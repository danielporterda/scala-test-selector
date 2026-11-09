//! Native compiler/JVM binding discovery over exact captured classpath bytes.
//! A compiler overload suffix is never interpreted as a JVM method-list index.
use flate2::read::MultiGzDecoder;
use rayon::prelude::*;
use selector_facts::FactSnapshot;
use selector_models::binary::{
    self, CapturedClasspath, ClassLookup, ClasspathEntry, EntryKind, Limits,
};
use selector_types::*;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::io::Read;
use std::path::{Component, Path, PathBuf};
#[cfg(test)]
#[path = "binary_capture_registration_tests.rs"]
mod registration_tests;
#[path = "binary_capture_source_types.rs"]
mod source_types;

#[derive(Clone, Debug)]
pub struct CaptureOptions {
    pub workers: usize,
    pub max_manifest_bytes: u64,
    pub max_inventory_names: usize,
    pub max_bindings: usize,
    pub platform: Option<crate::binary_platform::PlatformOptions>,
}
impl Default for CaptureOptions {
    fn default() -> Self {
        Self {
            workers: 4,
            max_manifest_bytes: 64 * 1024 * 1024,
            max_inventory_names: 2_000_000,
            max_bindings: 200_000,
            platform: None,
        }
    }
}
#[derive(Debug, Serialize)]
pub struct EntryReceipt {
    pub captured_path: String,
    pub physical_path: PathBuf,
    pub expected_sha256: String,
    pub classes: usize,
    pub admitted: bool,
    pub reason: Option<String>,
}
#[derive(Debug, Serialize)]
pub struct MappingReceipt {
    pub schema: &'static str,
    pub requested: usize,
    pub bound_methods: usize,
    pub bound_types: usize,
    pub skipped_source_recipes: usize,
    pub unresolved: BTreeMap<String, usize>,
    pub entries: Vec<EntryReceipt>,
}
pub struct Generated {
    pub manifest: Value,
    pub receipt: MappingReceipt,
}
#[derive(Deserialize)]
struct Capture {
    schema_version: String,
    revision: String,
    source_root: PathBuf,
    #[serde(default)]
    errors: Vec<Value>,
    contexts: Vec<Context>,
    input_objects: Vec<Object>,
    java_runtime: Option<JavaRuntime>,
}
#[derive(Deserialize)]
struct JavaRuntime {
    java_version: String,
}
#[derive(Deserialize)]
struct Context {
    context_id: String,
    full_classpath: Vec<Input>,
    #[serde(default)]
    java_options: Vec<String>,
    java_home: Option<PathBuf>,
    #[serde(default)]
    exported_products: Vec<Product>,
}
#[derive(Deserialize)]
struct Product {
    path: String,
    sha256: Option<String>,
}
#[derive(Deserialize)]
struct Origin {
    context_id: String,
}
#[derive(Deserialize)]
struct Input {
    index: usize,
    path: String,
    input_object: Option<String>,
    sha256: Option<String>,
    #[serde(default)]
    project_output_origins: Vec<Origin>,
}
#[derive(Deserialize)]
struct Object {
    path: String,
    kind: String,
    sha256: String,
    files: Option<u64>,
    bytes: u64,
}
struct Snapshot {
    entry: ClasspathEntry,
    names: Option<Vec<String>>,
    receipt: EntryReceipt,
}
struct Demand {
    symbol: SymbolId,
    context: usize,
    owner: SymbolId,
    jvm_owner: String,
    name: String,
    initializer: bool,
    module: Option<crate::binary_inputs::source_modules::Candidate>,
}
fn error(e: impl std::fmt::Display) -> Error {
    Error::Message(e.to_string())
}
fn reason(receipt: &mut MappingReceipt, why: impl Into<String>) {
    *receipt.unresolved.entry(why.into()).or_default() += 1;
}

pub fn generate(
    facts: &FactSnapshot,
    contexts_manifest: &Path,
    relocated_root: &Path,
    options: &CaptureOptions,
) -> Result<Generated, Error> {
    if options.workers == 0 || options.max_bindings == 0 {
        return Err(Error::Invalid("binary capture limits"));
    }
    let file = std::fs::File::open(contexts_manifest)?;
    let reader: Box<dyn Read> = if contexts_manifest.extension().is_some_and(|s| s == "gz") {
        Box::new(MultiGzDecoder::new(file))
    } else {
        Box::new(file)
    };
    let mut bytes = Vec::new();
    reader
        .take(options.max_manifest_bytes + 1)
        .read_to_end(&mut bytes)?;
    if bytes.len() as u64 > options.max_manifest_bytes {
        return Err(Error::Limit("binary capture manifest bytes"));
    }
    let capture: Capture = serde_json::from_slice(&bytes).map_err(error)?;
    let platform = options
        .platform
        .as_ref()
        .map(|options| {
            if options.contexts != contexts_manifest {
                return Err(Error::Invalid("platform context manifest path"));
            }
            crate::binary_platform::admit(options)
        })
        .transpose()?;
    if capture.schema_version != "sbt-compiler-context/v1"
        || !capture.errors.is_empty()
        || capture.revision != facts.text(facts.revision)
        || !capture.source_root.is_absolute()
    {
        return Err(Error::Invalid("binary capture revision/schema"));
    }
    let root = std::fs::canonicalize(relocated_root)?;
    let java_feature = capture
        .java_runtime
        .as_ref()
        .and_then(|runtime| java_feature(&runtime.java_version));
    if capture.contexts.iter().any(|context| {
        context.java_home.is_some()
            || context.java_options.iter().any(|option| {
                option.starts_with("-Djdk.util.jar.version")
                    || option.starts_with("-Djdk.util.jar.enableMultiRelease")
            })
    }) {
        return Err(Error::Invalid(
            "unsupported captured multi-release Java override",
        ));
    }
    let objects: HashMap<_, _> = capture
        .input_objects
        .iter()
        .map(|o| (o.path.as_str(), o))
        .collect();
    if objects.len() != capture.input_objects.len() {
        return Err(Error::Invalid("duplicate binary capture object"));
    }
    let mut unique = BTreeMap::new();
    for context in &capture.contexts {
        for (index, input) in context.full_classpath.iter().enumerate() {
            if input.index != index {
                return Err(Error::Invalid("binary capture classpath order"));
            }
            let key = input.input_object.as_deref().unwrap_or(&input.path);
            let object = objects
                .get(key)
                .copied()
                .ok_or(Error::Invalid("binary capture object absent"))?;
            if input.sha256.as_deref() != Some(object.sha256.as_str()) {
                return Err(Error::Invalid("binary capture object hash binding"));
            }
            unique.insert(key, object);
        }
    }
    let jobs: Vec<_> = unique
        .into_iter()
        .map(|(key, object)| {
            let path = if let Ok(relative) = Path::new(key).strip_prefix(&capture.source_root) {
                if relative
                    .components()
                    .any(|c| !matches!(c, Component::Normal(_)))
                {
                    return Err(Error::Invalid("binary capture relative path"));
                }
                root.join(relative)
            } else {
                PathBuf::from(key)
            };
            let kind = match object.kind.as_str() {
                "file" if path.extension().is_some_and(|e| e == "jar") => EntryKind::Jar,
                "directory" => EntryKind::Directory {
                    files: object
                        .files
                        .ok_or(Error::Invalid("binary capture directory count"))?,
                    bytes: object.bytes,
                },
                "absent_empty_project_output" => EntryKind::AbsentEmptyOutput,
                _ => EntryKind::Unavailable,
            };
            Ok((
                key,
                ClasspathEntry {
                    path,
                    sha256: ContentHash::from_hex(&object.sha256)?,
                    kind,
                },
            ))
        })
        .collect::<Result<_, Error>>()?;
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(options.workers)
        .build()
        .map_err(error)?;
    let mut snapshots: Vec<_> = pool.install(|| {
        jobs.par_iter()
            .map(|(captured, entry)| {
                let result = CapturedClasspath::new(vec![entry.clone()], Limits::default())
                    .and_then(|cp| cp.with_java_feature(java_feature))
                    .and_then(|mut cp| cp.class_names(0));
                let (names, why) = match result {
                    Ok(names) => (Some(names), None),
                    Err(e) => (None, Some(format!("{:?}", e.kind))),
                };
                Snapshot {
                    entry: entry.clone(),
                    receipt: EntryReceipt {
                        captured_path: (*captured).to_owned(),
                        physical_path: entry.path.clone(),
                        expected_sha256: entry.sha256.to_string(),
                        classes: names.as_ref().map_or(0, Vec::len),
                        admitted: names.is_some(),
                        reason: why,
                    },
                    names,
                }
            })
            .collect()
    });
    let platform_index = platform.as_ref().map(|platform| {
        let index = snapshots.len();
        snapshots.push(Snapshot {
            entry: platform.entry.clone(),
            names: Some(platform.owners.clone()),
            receipt: EntryReceipt {
                captured_path: "declared-runtime:jrt:/java.base".into(),
                physical_path: platform.entry.path.clone(),
                expected_sha256: platform.entry.sha256.to_string(),
                classes: platform.owners.len(),
                admitted: true,
                reason: None,
            },
        });
        index
    });
    if snapshots.iter().map(|s| s.receipt.classes).sum::<usize>() > options.max_inventory_names {
        return Err(Error::Limit("binary capture class inventories"));
    }
    let index: HashMap<_, _> = jobs
        .iter()
        .enumerate()
        .map(|(i, (key, _))| (*key, i))
        .collect();
    let mut classpaths = Vec::new();
    let mut context_index = HashMap::new();
    let fact_contexts: HashSet<_> = facts
        .symbols
        .iter()
        .map(|s| facts.text(s.context))
        .collect();
    let mut output_contexts = Vec::new();
    for context in &capture.contexts {
        if !fact_contexts.contains(context.context_id.as_str()) {
            continue;
        }
        if context_index
            .insert(context.context_id.as_str(), classpaths.len())
            .is_some()
        {
            return Err(Error::Invalid("duplicate binary compiler context"));
        }
        let mut entries: Vec<_> = context
            .full_classpath
            .iter()
            .map(|e| index[e.input_object.as_deref().unwrap_or(&e.path)])
            .collect();
        if platform
            .as_ref()
            .is_some_and(|p| p.contains_context(&context.context_id))
        {
            entries.insert(0, platform_index.unwrap());
        }
        let rows: Vec<_> = entries
            .iter()
            .map(|&i| {
                let snapshot = &snapshots[i];
                let entry = &snapshot.entry;
                let (kind, files, bytes) = if snapshot.names.is_none() {
                    ("unavailable", None, None)
                } else {
                    match entry.kind {
                        EntryKind::Jar => ("jar", None, None),
                        EntryKind::Directory { files, bytes } => {
                            ("directory", Some(files), Some(bytes))
                        }
                        EntryKind::AbsentEmptyOutput => ("absent_empty_output", None, None),
                        EntryKind::Unavailable => ("unavailable", None, None),
                    }
                };
                let mut row =
                    json!({"path":entry.path,"sha256":entry.sha256.to_string(),"kind":kind});
                if let Some(files) = files {
                    row["files"] = json!(files);
                }
                if let Some(bytes) = bytes {
                    row["bytes"] = json!(bytes);
                }
                row
            })
            .collect();
        output_contexts.push(json!({"id":context.context_id,"entries":rows}));
        classpaths.push(entries);
    }
    let mut receipt = MappingReceipt {
        schema: "captured-native-binary-map/v1",
        requested: 0,
        bound_methods: 0,
        bound_types: 0,
        skipped_source_recipes: 0,
        unresolved: BTreeMap::new(),
        entries: Vec::new(),
    };
    let mut seen = vec![false; facts.symbols.len()];
    let mut bodies = vec![false; facts.symbols.len()];
    for body in &facts.bodies {
        bodies[body.symbol.index()] = true;
    }
    let mut demands = Vec::new();
    let module_candidates: Vec<_> = crate::binary_inputs::source_modules::candidates(facts)
        .into_iter()
        .filter(|candidate| !candidate.global)
        .collect();
    for operation in &facts.operations {
        let symbol = operation.target;
        if symbol.is_none()
            || seen[symbol.index()]
            || !matches!(
                operation.opcode,
                Opcode::Call
                    | Opcode::VirtualCall
                    | Opcode::RegisterTest
                    | Opcode::Initialize
                    | Opcode::Allocate
            )
        {
            continue;
        }
        // The compiler term also serves as the runtime module class facet.
        // Never let another source opcode bind its native accessor to that
        // identity before the exact module bridge declares a separate member.
        if module_candidates
            .binary_search_by_key(&symbol, |module| module.symbol)
            .is_ok()
        {
            continue;
        }
        seen[symbol.index()] = true;
        if bodies[symbol.index()] {
            receipt.skipped_source_recipes += 1;
            continue;
        }
        let record = facts.symbols[symbol.index()];
        if !record.file.is_none()
            && record.span.start < record.span.end
            && facts.files[record.file.index()].flags & SOURCE_VERIFIED != 0
        {
            receipt.skipped_source_recipes += 1;
            continue;
        }
        receipt.requested += 1;
        let Some(&context) = context_index.get(facts.text(record.context)) else {
            reason(&mut receipt, "missing_or_multiple_compiler_context");
            continue;
        };
        let compiler = facts.symbol_name(symbol);
        let initializer = !compiler.ends_with(").")
            && matches!(operation.opcode, Opcode::Initialize | Opcode::Allocate);
        let owner = if initializer { symbol } else { record.owner };
        if owner.is_none() {
            reason(&mut receipt, "missing_compiler_owner");
            continue;
        }
        let Some(jvm_owner) = selector_types::symbol::jvm_owner(facts.symbol_name(owner)) else {
            reason(&mut receipt, "unsupported_owner_abi");
            continue;
        };
        let name = if initializer {
            "<init>".to_owned()
        } else {
            let Some(name) = selector_types::symbol::member_name(compiler) else {
                reason(&mut receipt, "unsupported_method_descriptor");
                continue;
            };
            if name == "<init>" {
                name.to_owned()
            } else {
                let Some(name) = selector_types::symbol::jvm_name(name) else {
                    reason(&mut receipt, "unsupported_member_abi");
                    continue;
                };
                name
            }
        };
        demands.push(Demand {
            symbol,
            context,
            owner,
            jvm_owner,
            name,
            initializer,
            module: None,
        });
    }
    for module in module_candidates {
        if seen[module.symbol.index()] || bodies[module.symbol.index()] {
            continue;
        }
        let record = facts.symbols[module.symbol.index()];
        let Some(&context) = context_index.get(facts.text(record.context)) else {
            continue;
        };
        seen[module.symbol.index()] = true;
        receipt.requested += 1;
        demands.push(Demand {
            symbol: module.symbol,
            context,
            owner: module.owner,
            jvm_owner: module.jvm_owner.clone(),
            name: module.name.clone(),
            initializer: false,
            module: Some(module),
        });
    }
    // Group demands by selected immutable archive/class. Each selected archive
    // is reopened once; all earlier absence decisions used complete inventories.
    let mut selected: BTreeMap<(usize, String), Vec<usize>> = BTreeMap::new();
    for (i, demand) in demands.iter().enumerate() {
        let mut found = false;
        for &entry in &classpaths[demand.context] {
            let snapshot = &snapshots[entry];
            let Some(names) = &snapshot.names else {
                reason(&mut receipt, "unavailable_preceding_classpath_input");
                found = true;
                break;
            };
            if names.binary_search(&demand.jvm_owner).is_err() {
                continue;
            }
            selected
                .entry((entry, demand.jvm_owner.clone()))
                .or_default()
                .push(i);
            found = true;
            break;
        }
        if !found {
            reason(&mut receipt, "class_absent_from_complete_classpath");
        }
    }
    let mut method_rows: BTreeMap<(usize, String, String, String), Value> = BTreeMap::new();
    let mut type_rows: BTreeMap<(usize, String), SymbolId> = BTreeMap::new();
    let mut abstract_owners = Vec::new();
    let mut header_owners = HashSet::new();
    let mut native_header_parents = Vec::new();
    let mut blocked_methods = HashSet::new();
    let mut blocked_types = HashSet::new();
    let signature_demands: HashSet<_> = demands
        .iter()
        .filter(|d| !facts.symbols[d.symbol.index()].signature.is_none())
        .map(|d| d.symbol)
        .collect();
    let mut parameters: HashMap<SymbolId, Vec<SymbolId>> = HashMap::new();
    for (i, symbol) in facts.symbols.iter().enumerate() {
        if signature_demands.contains(&symbol.owner) {
            parameters
                .entry(symbol.owner)
                .or_default()
                .push(SymbolId(i as u32));
        }
    }
    let mut active = None;
    let mut loader = None;
    for ((entry, owner), indices) in selected {
        if active != Some(entry) {
            active = Some(entry);
            loader = Some(
                CapturedClasspath::new(vec![snapshots[entry].entry.clone()], Limits::default())
                    .and_then(|cp| cp.with_java_feature(java_feature))
                    .map_err(error)?,
            );
        }
        let (bytes, class_hash) = match loader.as_mut().unwrap().lookup(&owner) {
            Ok(ClassLookup::Found(class)) => (class.bytes, class.proof.class_hash),
            Ok(ClassLookup::Absent(_)) => {
                return Err(Error::Invalid("binary inventory class disappeared"));
            }
            Err(e) => return Err(error(e)),
        };
        let class = binary::parse_class(&bytes, Limits::default()).map_err(error)?;
        for index in indices {
            let demand = &demands[index];
            if let Some(module) = &demand.module {
                // Prove the returned module independently in captured order.
                // A same-named class in an earlier entry or an opaque prefix
                // cannot be bypassed by the enclosing owner's archive.
                let selected_module = classpaths[demand.context].iter().find_map(|&input| {
                    match &snapshots[input].names {
                        None => Some(None),
                        Some(names) if names.binary_search(&module.module_owner).is_ok() => {
                            Some(Some(input))
                        }
                        _ => None,
                    }
                });
                if selected_module != Some(Some(entry)) {
                    reason(&mut receipt, "module_provider_unavailable_or_distinct");
                    continue;
                }
                let module_class = match loader.as_mut().unwrap().lookup(&module.module_owner) {
                    Ok(ClassLookup::Found(module_class)) => module_class,
                    Ok(ClassLookup::Absent(_)) => {
                        reason(&mut receipt, "module_header_unavailable");
                        continue;
                    }
                    Err(error) => return Err(self::error(error)),
                };
                let module_header =
                    binary::parse_class(&module_class.bytes, Limits::default()).map_err(error)?;
                if !crate::binary_inputs::source_modules::getter_rows(
                    class.name,
                    class.fields.iter().map(|f| f.name),
                    class
                        .methods
                        .iter()
                        .map(|m| (m.name, m.descriptor, m.flags)),
                    module,
                ) || !crate::binary_inputs::source_modules::module_rows(
                    module_header.name,
                    module_header.flags,
                    module_header.fields.iter().map(|f| f.name),
                    module_header
                        .methods
                        .iter()
                        .map(|m| (m.name, m.descriptor, m.flags)),
                    module,
                ) {
                    reason(&mut receipt, "module_accessor_abi_not_proven");
                    continue;
                }
            }
            let descriptor = compiler_descriptor(facts, demand.symbol, &parameters);
            let descriptor = demand
                .module
                .as_ref()
                .map(|m| m.descriptor.as_str())
                .or(descriptor.as_deref());
            // A pinned ABI may fill an absent external declaration, never
            // override a supplied but unsupported/conflicting compiler signature.
            let descriptor = descriptor.or_else(|| {
                if facts.symbols[demand.symbol.index()].signature.is_none()
                    && facts.symbols[demand.symbol.index()].flags & SYMBOL_DEFINED == 0
                    && facts.symbols[demand.owner.index()].flags & SYMBOL_DEFINED == 0
                    && snapshots[entry].entry.kind == EntryKind::Jar
                {
                    class_hash.and_then(|hash| {
                        selector_framework::native_abi::admitted_method_descriptor(
                            facts.symbol_name(demand.symbol),
                            &demand.jvm_owner,
                            &demand.name,
                            snapshots[entry].entry.sha256,
                            hash,
                        )
                    })
                } else {
                    None
                }
            });
            let trait_init = if demand.initializer {
                class.methods.iter().find(|m| {
                    m.name == "$init$" && m.descriptor == format!("(L{};)V", demand.jvm_owner)
                })
            } else {
                None
            };
            let method = if let Some(method) = trait_init {
                Ok(method)
            } else {
                class.method(&demand.name, descriptor)
            };
            let method = match method {
                Ok(m) => m,
                Err(e) => {
                    reason(&mut receipt, format!("method_{:?}", e.kind));
                    continue;
                }
            };
            if method.flags & 0x0400 != 0 && method.flags & (0x0002 | 0x0008) == 0 {
                abstract_owners.push(demand.owner);
            }
            let key = (demand.context, demand.jvm_owner.clone());
            if blocked_types.contains(&key) {
                continue;
            }
            if type_rows.get(&key).is_some_and(|old| *old != demand.owner) {
                type_rows.remove(&key);
                blocked_types.insert(key);
                reason(&mut receipt, "conflicting_compiler_type_abi");
                continue;
            }
            type_rows.insert(key, demand.owner);
            if facts.symbols[demand.owner.index()].flags & SYMBOL_DEFINED == 0
                && header_owners.insert((demand.context, demand.owner))
            {
                native_header_parents.extend(
                    class
                        .parent
                        .into_iter()
                        .chain(class.interfaces.iter().copied())
                        .map(|parent| (demand.context, demand.owner, parent.to_owned())),
                );
            }

            let context = &output_contexts[demand.context]["id"];
            let compiler_symbol = demand
                .module
                .is_none()
                .then(|| facts.symbol_name(demand.symbol));
            let mut row = json!({"context":context,"compiler_symbol":compiler_symbol,
                "jvm_owner":demand.jvm_owner,"jvm_name":method.name,"descriptor":method.descriptor});
            if trait_init.is_some() {
                row["receiver_parameter"] = json!(0);
            }
            let key = (
                demand.context,
                demand.jvm_owner.clone(),
                method.name.to_owned(),
                method.descriptor.to_owned(),
            );
            if blocked_methods.contains(&key) {
                continue;
            }
            if let Some(previous) = method_rows.get(&key) {
                if previous["compiler_symbol"] != row["compiler_symbol"] {
                    method_rows.remove(&key);
                    blocked_methods.insert(key);
                    reason(&mut receipt, "multiple_compiler_symbols_for_one_jvm_method");
                }
                continue;
            }
            method_rows.insert(key, row);
            if method_rows.len() > options.max_bindings {
                return Err(Error::Limit("automatic binary bindings"));
            }
        }
    }
    let bound_types: HashSet<_> = type_rows.values().copied().collect();
    let native_parents: Vec<_> = native_header_parents
        .into_iter()
        .filter_map(|(context, source, owner)| {
            let target = type_rows.get(&(context, owner)).copied()?;
            bound_types.contains(&source).then_some((source, target))
        })
        .collect();
    drop(bound_types);
    drop(header_owners);
    source_types::add(
        source_types::Inputs {
            facts,
            native_parents: &native_parents,
            contexts: &capture.contexts,
            context_index: &context_index,
            snapshots: &snapshots,
            classpaths: &classpaths,
            java_feature,
            max_bindings: options.max_bindings,
        },
        &abstract_owners,
        &mut type_rows,
        &mut blocked_types,
        &mut receipt,
    )?;
    method_rows
        .retain(|(context, owner, _, _), _| !blocked_types.contains(&(*context, owner.clone())));
    let types:Vec<_>=type_rows.into_iter().map(|((context,owner),symbol)| json!({
        "context":output_contexts[context]["id"],"compiler_symbol":facts.symbol_name(symbol),"jvm_owner":owner})).collect();
    receipt.bound_methods = method_rows.len();
    receipt.bound_types = types.len();
    receipt.entries = snapshots.drain(..).map(|s| s.receipt).collect();
    let mut manifest = json!({"version":1,"revision":capture.revision,"facts_identity":facts.identity.to_string(),"java_feature":java_feature,
        "contexts":output_contexts,"types":types,"methods":method_rows.into_values().collect::<Vec<_>>()});
    if let Some(platform) = platform {
        manifest["declared_platform"] = serde_json::to_value(platform.binding).map_err(error)?;
    }
    Ok(Generated { manifest, receipt })
}
fn java_feature(version: &str) -> Option<u16> {
    let version = version.strip_prefix("1.").unwrap_or(version);
    let feature = version.split(['.', '-', '+']).next()?.parse().ok()?;
    (feature > 0 && feature <= 255).then_some(feature)
}

fn compiler_descriptor(
    facts: &FactSnapshot,
    symbol: SymbolId,
    parameters: &HashMap<SymbolId, Vec<SymbolId>>,
) -> Option<String> {
    let signature = facts.symbols[symbol.index()].signature;
    if signature.is_none() {
        return None;
    }
    let value: Value = serde_json::from_str(facts.text(signature)).ok()?;
    let method = value.get("method_signature")?;
    let mut descriptor = "(".to_owned();
    for clause in method.get("parameter_lists")?.as_array()? {
        for name in clause.get("symlinks")?.as_array()? {
            let name = name.as_str()?;
            let parameter = parameters
                .get(&symbol)?
                .iter()
                .map(|p| &facts.symbols[p.index()])
                .find(|s| facts.text(s.name) == name)?;
            if parameter.signature.is_none() {
                return None;
            }
            let signature: Value = serde_json::from_str(facts.text(parameter.signature)).ok()?;
            descriptor.push_str(&erased_type(
                signature.pointer("/value_signature/tpe")?,
                false,
            )?);
        }
    }
    descriptor.push(')');
    descriptor.push_str(&erased_type(method.get("return_type")?, true)?);
    Some(descriptor)
}
fn erased_type(tpe: &Value, result: bool) -> Option<String> {
    if tpe.get("by_name_type").is_some() {
        return Some("Lscala/Function0;".into());
    }
    if let Some(reference) = tpe.get("type_ref") {
        let symbol = reference.get("symbol")?.as_str()?;
        let primitive = match symbol {
            "scala/Boolean#" => "Z",
            "scala/Byte#" => "B",
            "scala/Char#" => "C",
            "scala/Short#" => "S",
            "scala/Int#" => "I",
            "scala/Long#" => "J",
            "scala/Float#" => "F",
            "scala/Double#" => "D",
            "scala/Unit#" if result => "V",
            _ => "",
        };
        if !primitive.is_empty() {
            return Some(primitive.into());
        }
        if symbol == "scala/Array#" {
            return Some(format!(
                "[{}",
                erased_type(reference.get("type_arguments")?.as_array()?.first()?, false)?
            ));
        }
        if matches!(symbol, "scala/Any#" | "scala/AnyRef#" | "java/lang/Object#") {
            return Some("Ljava/lang/Object;".into());
        }
        // Scala aliases, generic parameters and structural wrappers need the
        // compiler's erasure authority; they cannot acquire guessed descriptors.
        if !symbol.starts_with("java/") {
            return None;
        }
        return Some(format!("L{};", selector_types::symbol::jvm_owner(symbol)?));
    }
    for key in ["annotated_type", "existential_type"] {
        if let Some(inner) = tpe.get(key).and_then(|v| v.get("tpe")) {
            return erased_type(inner, result);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use selector_facts::*;
    fn fixture() -> FactSnapshot {
        let mut builder = FactBuilder::new();
        builder.facts.revision = builder.intern("r").unwrap();
        let context = builder.intern("a").unwrap();
        let path = builder.intern("Use.scala").unwrap();
        let source = builder.intern("x").unwrap();
        builder.facts.files.push(FileRecord {
            path,
            source,
            revision: builder.facts.revision,
            context,
            source_hash: ContentHash::default(),
            flags: SOURCE_VERIFIED,
        });
        let owner = builder.ensure_symbol("fixture/Probe#", FileId(0)).unwrap();
        let caller = builder.ensure_symbol("p/Use#run().", FileId(0)).unwrap();
        builder.facts.symbols[caller.index()].file = FileId(0);
        builder.facts.symbols[caller.index()].span = Span { start: 0, end: 1 };
        let unique = builder
            .ensure_symbol("fixture/Probe#forward().", FileId(0))
            .unwrap();
        let ambiguous = builder
            .ensure_symbol("fixture/Probe#over(+27).", FileId(0))
            .unwrap();
        let exact = builder
            .ensure_symbol("fixture/Probe#over(+99).", FileId(0))
            .unwrap();
        let param = builder
            .ensure_symbol("fixture/Probe#over(+99).(x)", FileId(0))
            .unwrap();
        builder.facts.symbols[param.index()].owner = exact;
        builder.facts.symbols[param.index()].kind = 8;
        builder.facts.symbols[param.index()].signature = builder
            .intern(r#"{"value_signature":{"tpe":{"type_ref":{"symbol":"scala/Int#"}}}}"#)
            .unwrap();
        builder.facts.symbols[exact.index()].signature=builder.intern(r#"{"method_signature":{"parameter_lists":[{"symlinks":["fixture/Probe#over(+99).(x)"]}],"return_type":{"type_ref":{"symbol":"java/lang/Object#"}}}}"#).unwrap();
        for target in [unique, ambiguous, exact] {
            builder.facts.symbols[target.index()].owner = owner;
            builder.facts.operations.push(OperationRecord {
                body: BodyId(0),
                opcode: Opcode::Call,
                target,
                dest: ValueId(1),
                a: ValueId(0),
                b: ValueId::NONE,
                arguments: IdRange::default(),
                span: Span { start: 0, end: 1 },
                flags: 0,
            });
        }
        builder.facts.bodies.push(BodyRecord {
            symbol: caller,
            file: FileId(0),
            span: Span { start: 0, end: 1 },
            name_span: Span { start: 0, end: 1 },
            operations: IdRange { start: 0, len: 3 },
            parameters: IdRange::default(),
            body_hash: ContentHash::default(),
            flags: 0,
        });
        builder.finish().unwrap()
    }
    fn captured(directory: &Path, unavailable_prefix: bool) -> PathBuf {
        let jar = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../fixtures/binary/fixture-deflated.jar")
            .canonicalize()
            .unwrap();
        let manifest: Value =
            serde_json::from_str(include_str!("../../../fixtures/binary/manifest.json")).unwrap();
        let hash = manifest["outputs"]
            .as_array()
            .unwrap()
            .iter()
            .find(|o| o["path"] == "fixture-deflated.jar")
            .unwrap()["sha256"]
            .as_str()
            .unwrap();
        let mut objects = vec![
            json!({"path":jar,"kind":"file","sha256":hash,"bytes":std::fs::metadata(&jar).unwrap().len()}),
        ];
        let mut entries = vec![json!({"index":0,"path":jar,"sha256":hash})];
        if unavailable_prefix {
            let missing = directory.join("missing.jar");
            objects.insert(0,json!({"path":missing,"kind":"file","sha256":ContentHash([9;32]).to_string(),"bytes":1}));
            entries[0]["index"] = json!(1);
            entries.insert(
                0,
                json!({"index":0,"path":missing,"sha256":ContentHash([9;32]).to_string()}),
            );
        }
        let path = directory.join("contexts.json");
        std::fs::write(&path,json!({"schema_version":"sbt-compiler-context/v1","revision":"r",
            "source_root":"/old/root","errors":[],"contexts":[{"context_id":"a","full_classpath":entries}],
            "input_objects":objects}).to_string()).unwrap();
        path
    }
    #[test]
    fn genuine_classfiles_bind_unique_or_exact_descriptors_and_never_guess_overload_order() {
        let directory = tempfile::tempdir().unwrap();
        let mut facts = fixture();
        let capture = captured(directory.path(), false);
        let generated = generate(
            &facts,
            &capture,
            directory.path(),
            &CaptureOptions::default(),
        )
        .unwrap();
        assert_eq!(generated.receipt.bound_methods, 2);
        assert_eq!(
            generated.receipt.unresolved.get("method_AmbiguousMethod"),
            Some(&1)
        );
        let methods = generated.manifest["methods"].as_array().unwrap();
        assert!(
            methods
                .iter()
                .any(|m| m["compiler_symbol"] == "fixture/Probe#forward()."
                    && m["descriptor"] == "(Ljava/lang/Object;)Ljava/lang/Object;")
        );
        assert!(
            methods
                .iter()
                .any(|m| m["compiler_symbol"] == "fixture/Probe#over(+99)."
                    && m["descriptor"] == "(I)Ljava/lang/Object;")
        );
        assert!(
            !methods
                .iter()
                .any(|m| m["compiler_symbol"] == "fixture/Probe#over(+27).")
        );
        let map = directory.path().join("binary.json");
        std::fs::write(&map, generated.manifest.to_string()).unwrap();
        let mut admitted = crate::binary_inputs::load_binary_manifest(&map, &facts).unwrap();
        let serial = crate::binary_inputs::load_binary_manifest_with_options(
            &map,
            &facts,
            &crate::binary_inputs::BinaryInputOptions {
                workers: 1,
                ..Default::default()
            },
        )
        .unwrap();
        assert_eq!(admitted.identity, serial.identity);
        assert_eq!(
            admitted.retained_input_bytes(),
            serial.retained_input_bytes()
        );
        assert!(admitted.retained_input_bytes() > 0);
        assert!(matches!(
            crate::binary_inputs::load_binary_manifest_with_options(
                &map,
                &facts,
                &crate::binary_inputs::BinaryInputOptions {
                    workers: 2,
                    max_retained_bytes: 1
                }
            ),
            Err(Error::Limit("shared binary input bytes"))
        ));
        crate::binary_inputs::augment_binary_facts(&mut facts, &mut admitted).unwrap();
        assert!(facts.bodies.iter().any(|b| facts.symbol_name(b.symbol)
            == "fixture/Probe#forward()."
            && b.flags & BODY_BINARY_RECIPE != 0));
    }
    #[test]
    fn unavailable_earlier_input_blocks_later_exact_jar_and_publication_is_deterministic() {
        let directory = tempfile::tempdir().unwrap();
        let facts = fixture();
        let capture = captured(directory.path(), true);
        let serial = generate(
            &facts,
            &capture,
            directory.path(),
            &CaptureOptions {
                workers: 1,
                ..Default::default()
            },
        )
        .unwrap();
        let parallel = generate(
            &facts,
            &capture,
            directory.path(),
            &CaptureOptions {
                workers: 4,
                ..Default::default()
            },
        )
        .unwrap();
        assert_eq!(serial.manifest, parallel.manifest);
        assert_eq!(serial.receipt.bound_methods, 0);
        assert_eq!(
            serial
                .receipt
                .unresolved
                .get("unavailable_preceding_classpath_input"),
            Some(&3)
        );
        assert_eq!(
            serial.manifest["contexts"][0]["entries"][0]["kind"],
            "unavailable"
        );
    }
    #[test]
    fn verified_project_classes_bind_missing_bodies_and_placeholder_initializers() {
        let directory = tempfile::tempdir().unwrap();
        let mut facts = fixture();
        // SemanticDB object identities also name module accessor methods on
        // their enclosing class. Kind10 alone must not replace the exact ABI
        // owner binding with the returned object's own type identity.
        let accessor = facts.operations[0].target;
        let name = "fixture/Probe#forward.";
        facts.symbols[accessor.index()].name = StrId(facts.strings.entries.len() as u32);
        facts.strings.entries.push(TextRange {
            start: facts.strings.bytes.len() as u64,
            len: name.len() as u32,
        });
        facts.strings.bytes.extend_from_slice(name.as_bytes());
        facts.symbols[accessor.index()].kind = 10;
        let owner = facts
            .symbols
            .iter()
            .position(|s| facts.text(s.name) == "fixture/Probe#")
            .unwrap();
        assert_eq!(facts.symbols[owner].kind, 0);
        facts.operations.push(OperationRecord {
            target: SymbolId(owner as u32),
            opcode: Opcode::Initialize,
            ..facts.operations[0]
        });
        facts.bodies[0].operations.len += 1;
        let capture = captured(directory.path(), false);
        let mut value: Value = serde_json::from_slice(&std::fs::read(&capture).unwrap()).unwrap();
        let classes = directory.path().join("classes");
        std::fs::create_dir_all(classes.join("fixture")).unwrap();
        let bytes = include_bytes!("../../../fixtures/binary/classes/fixture/Probe.class");
        std::fs::write(classes.join("fixture/Probe.class"), bytes).unwrap();
        use sha2::{Digest, Sha256};
        let file_hash = ContentHash(Sha256::digest(bytes).into());
        let canonical = format!(
            "[{{\"bytes\":{},\"path\":\"fixture/Probe.class\",\"sha256\":\"{}\"}}]",
            bytes.len(),
            file_hash
        );
        let hash = ContentHash(Sha256::digest(canonical.as_bytes()).into()).to_string();
        value["input_objects"] = json!([{"path":classes,"kind":"directory","sha256":hash,"files":1,"bytes":bytes.len()}]);
        value["contexts"][0]["full_classpath"] = json!([{"index":0,"path":classes,"sha256":hash}]);
        std::fs::write(&capture, value.to_string()).unwrap();
        let generated = generate(
            &facts,
            &capture,
            directory.path(),
            &CaptureOptions::default(),
        )
        .unwrap();
        assert_eq!(generated.receipt.bound_methods, 3);
        assert!(
            generated.manifest["methods"]
                .as_array()
                .unwrap()
                .iter()
                .any(|m| m["compiler_symbol"] == "fixture/Probe#" && m["jvm_name"] == "<init>")
        );
        let map = directory.path().join("binary.json");
        std::fs::write(&map, generated.manifest.to_string()).unwrap();
        let mut admitted = crate::binary_inputs::load_binary_manifest(&map, &facts).unwrap();
        crate::binary_inputs::augment_binary_facts(&mut facts, &mut admitted).unwrap();
        assert!(
            facts
                .bodies
                .iter()
                .any(|b| b.symbol == SymbolId(owner as u32) && b.flags & BODY_BINARY_RECIPE != 0)
        );
    }
    fn framework_fixture() -> FactSnapshot {
        let mut builder = FactBuilder::new();
        builder.facts.revision = builder.intern("r").unwrap();
        let context = builder.intern("a").unwrap();
        let path = builder.intern("Use.scala").unwrap();
        let source = builder.intern("x").unwrap();
        builder.facts.files.push(FileRecord {
            path,
            source,
            context,
            revision: builder.facts.revision,
            source_hash: ContentHash::default(),
            flags: SOURCE_VERIFIED,
        });
        let caller = builder.ensure_symbol("p/Use#run().", FileId(0)).unwrap();
        builder.facts.symbols[caller.index()].file = FileId(0);
        builder.facts.symbols[caller.index()].span = Span { start: 0, end: 1 };
        let target = builder
            .ensure_symbol(
                selector_framework::native_abi::SHOULD_SCOPE_SYMBOL,
                FileId(0),
            )
            .unwrap();
        let owner = builder
            .ensure_symbol(
                selector_types::symbol::global_owner(
                    selector_framework::native_abi::SHOULD_SCOPE_SYMBOL,
                )
                .unwrap(),
                FileId(0),
            )
            .unwrap();
        builder.facts.symbols[target.index()].owner = owner;
        builder.facts.operations.push(OperationRecord {
            body: BodyId(0),
            opcode: Opcode::Call,
            target,
            dest: ValueId(1),
            a: ValueId(0),
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span { start: 0, end: 1 },
            flags: 0,
        });
        builder.facts.bodies.push(BodyRecord {
            symbol: caller,
            file: FileId(0),
            span: Span { start: 0, end: 1 },
            name_span: Span { start: 0, end: 1 },
            operations: IdRange { start: 0, len: 1 },
            parameters: IdRange::default(),
            body_hash: ContentHash::default(),
            flags: 0,
        });
        builder.finish().unwrap()
    }
    fn framework_capture(directory: &Path, prefix: Option<(&Path, ContentHash)>) -> PathBuf {
        let receipt: Value = serde_json::from_str(include_str!(
            "../../../fixtures/binary/framework/manifest.json"
        ))
        .unwrap();
        let jar = Path::new(receipt["archive"]["path"].as_str().unwrap());
        let hash = selector_framework::native_abi::SCALATEST_CORE_3_2_19;
        let mut entries = Vec::new();
        let mut objects = Vec::new();
        for (path, hash) in prefix.into_iter().chain(std::iter::once((jar, hash))) {
            entries.push(json!({"index":entries.len(),"path":path,"sha256":hash.to_string()}));
            objects.push(json!({"path":path,"kind":"file","sha256":hash.to_string(),"bytes":std::fs::metadata(path).unwrap().len()}));
        }
        let path = directory.join("framework-contexts.json");
        std::fs::write(&path, json!({"schema_version":"sbt-compiler-context/v1","revision":"r",
            "source_root":"/old/root","errors":[],"contexts":[{"context_id":"a","full_classpath":entries}],
            "input_objects":objects}).to_string()).unwrap();
        path
    }
    #[test]
    fn genuine_pinned_framework_overload_binds_exact_descriptor_and_lowers_real_effects() {
        use selector_framework::native_abi::*;
        use sha2::{Digest, Sha256};
        let bytes =
            include_bytes!("../../../fixtures/binary/framework/StringShouldWrapperForVerb.class");
        assert_eq!(
            ContentHash(Sha256::digest(bytes).into()),
            SHOULD_WRAPPER_CLASS
        );
        let class = binary::parse_class(bytes, Limits::default()).unwrap();
        assert!(
            class.method("should", None).is_err(),
            "overload order remains unavailable"
        );
        let method = class
            .method("should", Some(SHOULD_SCOPE_DESCRIPTOR))
            .unwrap();
        assert!(
            method.code.is_some(),
            "the reviewed scope method has executable effects"
        );
        assert!(
            class
                .method("should", Some("(Lscala/Function0;)V"))
                .is_err()
        );
        let directory = tempfile::tempdir().unwrap();
        let mut facts = framework_fixture();
        let capture = framework_capture(directory.path(), None);
        let options = CaptureOptions {
            workers: 1,
            ..Default::default()
        };
        let generated = generate(&facts, &capture, directory.path(), &options).unwrap();
        assert_eq!(generated.receipt.bound_methods, 1);
        assert_eq!(
            generated.manifest["methods"][0]["descriptor"],
            SHOULD_SCOPE_DESCRIPTOR
        );
        assert_eq!(
            generated.manifest["methods"][0]["compiler_symbol"],
            SHOULD_SCOPE_SYMBOL
        );
        let map = directory.path().join("framework-map.json");
        std::fs::write(&map, generated.manifest.to_string()).unwrap();
        let mut inputs = crate::binary_inputs::load_binary_manifest(&map, &facts).unwrap();
        crate::binary_inputs::augment_binary_facts(&mut facts, &mut inputs).unwrap();
        let target = facts.find_symbol(SHOULD_SCOPE_SYMBOL).unwrap();
        let body = facts.bodies.iter().find(|b| b.symbol == target).unwrap();
        assert_ne!(body.flags & BODY_BINARY_RECIPE, 0);
        let ops = &facts.operations[body.operations.range()];
        for member in ["leftSideString", "pos", "apply"] {
            assert!(
                ops.iter()
                    .any(|op| matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
                        && (selector_types::symbol::member_name(facts.symbol_name(op.target))
                            == Some(member)
                            || facts
                                .symbol_name(op.target)
                                .contains(&format!("{}:{member}", member.len())))),
                "normal native effects retain {member}"
            );
        }
        assert_eq!(
            ops.iter()
                .filter(|op| op.opcode == Opcode::Parameter)
                .count(),
            2
        );
    }
    #[test]
    fn pinned_framework_binding_rejects_earlier_archive_shadow_and_supplied_signature_conflict() {
        use sha2::{Digest, Sha256};
        let directory = tempfile::tempdir().unwrap();
        let facts = framework_fixture();
        let capture = framework_capture(directory.path(), None);
        let original: Value = serde_json::from_slice(&std::fs::read(&capture).unwrap()).unwrap();
        let jar = Path::new(original["input_objects"][0]["path"].as_str().unwrap());
        // Same real class and descriptors in a distinct valid archive. The
        // release hash is mandatory and a later pinned archive cannot rescue it.
        let mut bytes = std::fs::read(jar).unwrap();
        let eocd = bytes.windows(4).rposition(|w| w == b"PK\x05\x06").unwrap();
        let count = u16::from_le_bytes(bytes[eocd + 20..eocd + 22].try_into().unwrap());
        bytes[eocd + 20..eocd + 22].copy_from_slice(&(count + 1).to_le_bytes());
        bytes.push(b'x');
        let shadow = directory.path().join("shadow-core.jar");
        let hash = ContentHash(Sha256::digest(&bytes).into());
        std::fs::write(&shadow, bytes).unwrap();
        let capture = framework_capture(directory.path(), Some((&shadow, hash)));
        let options = CaptureOptions {
            workers: 1,
            ..Default::default()
        };
        let shadowed = generate(&facts, &capture, directory.path(), &options).unwrap();
        assert_eq!(shadowed.receipt.bound_methods, 0);
        assert_eq!(
            shadowed.receipt.unresolved.get("method_AmbiguousMethod"),
            Some(&1)
        );
        let capture = framework_capture(directory.path(), None);
        for shadow_owner in [false, true] {
            let mut facts = framework_fixture();
            let target = facts
                .find_symbol(selector_framework::native_abi::SHOULD_SCOPE_SYMBOL)
                .unwrap();
            let id = if shadow_owner {
                facts.symbols[target.index()].owner
            } else {
                target
            };
            facts.symbols[id.index()].flags |= SYMBOL_DEFINED;
            let rejected = generate(&facts, &capture, directory.path(), &options).unwrap();
            assert_eq!(
                rejected.receipt.bound_methods, 0,
                "source definitions cannot borrow a pinned library ABI"
            );
        }
        let mut wrong_hash: Value =
            serde_json::from_slice(&std::fs::read(&capture).unwrap()).unwrap();
        wrong_hash["input_objects"][0]["sha256"] = ContentHash::default().to_string().into();
        wrong_hash["contexts"][0]["full_classpath"][0]["sha256"] =
            ContentHash::default().to_string().into();
        std::fs::write(&capture, wrong_hash.to_string()).unwrap();
        let rejected = generate(&facts, &capture, directory.path(), &options).unwrap();
        assert_eq!(rejected.receipt.bound_methods, 0);
        assert_eq!(
            rejected
                .receipt
                .unresolved
                .get("unavailable_preceding_classpath_input"),
            Some(&1)
        );
        let capture = framework_capture(directory.path(), None);
        for signature in [
            r#"{"method_signature":{"parameter_lists":[],"return_type":{"type_ref":{"symbol":"scala/Unit#"}}}}"#,
            "{}",
        ] {
            let mut facts = framework_fixture();
            let target = facts
                .find_symbol(selector_framework::native_abi::SHOULD_SCOPE_SYMBOL)
                .unwrap();
            let id = StrId(facts.strings.entries.len() as u32);
            facts.strings.entries.push(selector_facts::TextRange {
                start: facts.strings.bytes.len() as u64,
                len: signature.len() as u32,
            });
            facts.strings.bytes.extend_from_slice(signature.as_bytes());
            facts.symbols[target.index()].signature = id;
            let rejected = generate(&facts, &capture, directory.path(), &options).unwrap();
            assert_eq!(
                rejected.receipt.bound_methods, 0,
                "a supplied signature is never overridden by the ABI fallback"
            );
        }
    }
}
