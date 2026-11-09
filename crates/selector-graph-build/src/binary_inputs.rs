//! Explicit compiler/JVM bindings and an owned, hash-verified enrichment stage.
//! A native declaration uses the @jvm namespace; JVM names never invent Scala
//! symbols. Derived facts are sealed separately from the captured source facts.
use rayon::prelude::*;
use selector_facts::*;
use selector_models::binary::{
    self, AdmittedEntry, CapturedClasspath, ClassLookup, ClasspathEntry, EntryKind, Limits,
    MemberRef,
};
use selector_types::*;
use serde::Deserialize;
use sha2::{Digest, Sha256};
use std::collections::{HashMap, HashSet, VecDeque};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, Weak};

#[path = "binary_accessors.rs"]
mod accessors;
#[path = "binary_admission.rs"]
mod admission;
#[path = "binary_scalatest.rs"]
mod scalatest;
pub use admission::NativeAdmissionLimits;
use admission::{
    Admission, DeferredReason, guarded_class, guarded_hierarchy_class, optional_effect,
    optional_phase,
};
#[path = "binary_generated_members.rs"]
mod generated_members;
#[path = "binary_hierarchy.rs"]
mod hierarchy;
#[path = "binary_lambdas.rs"]
mod lambdas;
#[path = "binary_macro.rs"]
mod macro_expansions;
#[path = "binary_native_result_bounds.rs"]
mod native_result_bounds;
#[path = "binary_overrides.rs"]
mod overrides;
#[path = "binary_parameter_apply.rs"]
mod parameter_apply;
#[path = "binary_sequence.rs"]
mod sequence;
#[path = "binary_source_modules.rs"]
pub(super) mod source_modules;
#[path = "binary_static_namespace.rs"]
mod static_namespace;
#[path = "binary_trusted_scala.rs"]
mod trusted_scala;

const MAX_MANIFEST_BYTES: u64 = 64 * 1024 * 1024;
const MAX_METHODS: usize = 200_000;
const MAX_CLASSES: usize = 8192;
const MAX_CLASS_BYTES: usize = 256 * 1024 * 1024;
const MAX_SHARED_METADATA_ENTRIES: usize = 32_768;
type SharedMetadata = Arc<Mutex<HashMap<ContentHash, Weak<binary::ClassMetadata>>>>;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
    version: u32,
    revision: Option<String>,
    facts_identity: Option<String>,
    contexts: Vec<Context>,
    #[serde(default)]
    types: Vec<TypeBinding>,
    methods: Vec<MethodBinding>,
    java_feature: Option<u16>,
    declared_platform: Option<crate::binary_platform::PlatformBinding>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Context {
    id: String,
    entries: Vec<Entry>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Entry {
    path: PathBuf,
    sha256: Option<String>,
    kind: String,
    files: Option<u64>,
    bytes: Option<u64>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct TypeBinding {
    context: String,
    compiler_symbol: String,
    jvm_owner: String,
}
#[derive(Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct MethodBinding {
    context: String,
    compiler_symbol: Option<String>,
    jvm_owner: String,
    jvm_name: String,
    descriptor: String,
    receiver_parameter: Option<u16>,
}

// Stage-local index: binary producer hashing never depends on graph construction helpers.
struct BinaryAdjacency {
    offsets: Vec<usize>,
    values: Vec<SymbolId>,
}
impl BinaryAdjacency {
    fn new(facts: &FactSnapshot, kind: RelationKind, reverse: bool) -> Self {
        let mut offsets = vec![0; facts.symbols.len() + 1];
        for r in &facts.relations {
            if r.kind == kind {
                offsets[if reverse {
                    r.target.index()
                } else {
                    r.source.index()
                } + 1] += 1;
            }
        }
        for i in 1..offsets.len() {
            offsets[i] += offsets[i - 1];
        }
        let mut values = vec![SymbolId::NONE; *offsets.last().unwrap()];
        let mut cursor = offsets[..facts.symbols.len()].to_vec();
        for r in &facts.relations {
            if r.kind == kind {
                let (source, target) = if reverse {
                    (r.target, r.source)
                } else {
                    (r.source, r.target)
                };
                values[cursor[source.index()]] = target;
                cursor[source.index()] += 1;
            }
        }
        Self { offsets, values }
    }
    fn get(&self, symbol: SymbolId) -> &[SymbolId] {
        &self.values[self.offsets[symbol.index()]..self.offsets[symbol.index() + 1]]
    }
}

struct ClassBytes {
    bytes: Arc<[u8]>,
    hash: ContentHash,
    origin: String,
    metadata: Arc<binary::ClassMetadata>,
}
enum CachedClass {
    Found(Arc<ClassBytes>),
    Unknown(binary::ErrorKind),
}
#[derive(Default)]
struct ClassCacheMetrics {
    found: usize,
    unknown: usize,
    retained_bytes: usize,
    metadata_bytes: usize,
    requests: u64,
    trusted_runtime_models: usize,
    trusted_runtime_model_fallbacks: usize,
}
struct AdmittedContext {
    id: StrId,
    name: String,
    cache_metrics: ClassCacheMetrics,
    phase: &'static str,
    active_method: SymbolId,
    active_file: FileId,
    pending_methods: usize,
    admission: Admission,
    entries: Vec<ClasspathEntry>,
    classes: HashMap<String, CachedClass>,
    shared_metadata: SharedMetadata,
    java_feature: Option<u16>,
    entries_at: Vec<usize>,
}
struct BoundMethod {
    context: usize,
    symbol: Option<SymbolId>,
    owner: String,
    name: String,
    descriptor: String,
    receiver_parameter: Option<u16>,
}
struct BoundTypeAlias {
    context: usize,
    owner: String,
    symbol: SymbolId,
    canonical: SymbolId,
}
pub struct OwnedBinaryInputs {
    pub identity: ContentHash,
    raw_identity: ContentHash,
    contexts: Vec<AdmittedContext>,
    types: HashMap<(usize, String), SymbolId>,
    type_aliases: Vec<BoundTypeAlias>,
    methods: Vec<BoundMethod>,
    admitted: Vec<AdmittedEntry>,
    envelope_cache: binary::EnvelopeCache,
    platform_inputs: Vec<PathBuf>,
    platform_contexts: HashSet<StrId>,
}
#[derive(Clone, Copy, Debug)]
pub struct BinaryContextMetrics<'a> {
    pub context: &'a str,
    pub found: usize,
    pub unknown: usize,
    pub retained_bytes: usize,
    pub requests: u64,
    pub phase: &'static str,
    pub active_method: SymbolId,
    pub pending_methods: usize,
    pub deferred_admissions: u64,
    pub derived_methods: usize,
    /// Unused first-round reservation reclaimed in the one redistribution.
    pub method_slots_released: usize,
    /// Additional second-round allowance (not necessarily all consumed).
    pub method_slots_received: usize,
    pub retried_callers: usize,
    /// Retained typed execution guard rows after node dedup; not callsites.
    pub method_guard_rows: usize,
    /// Retained receiver/contract dispatch frontiers; not unconditional guards.
    pub scoped_dispatch_rows: usize,
    /// Receiver-only dispatch uncertainty after bounded contract bookkeeping.
    pub receiver_dispatch_rows: usize,
    /// Final published semantic recipes, excluding retries.
    pub trusted_runtime_models: usize,
    /// Recognized API contracts kept on original recipes due missing authority.
    pub trusted_runtime_model_fallbacks: usize,
}
#[derive(Clone, Debug)]
pub struct BinaryInputOptions {
    pub workers: usize,
    /// Shared immutable archive bytes, member tables and directory inventories.
    pub max_retained_bytes: usize,
}
impl Default for BinaryInputOptions {
    fn default() -> Self {
        Self {
            workers: 4,
            max_retained_bytes: 768 * 1024 * 1024,
        }
    }
}
impl OwnedBinaryInputs {
    /// Exact declaration/image/archive files required by a native replay receipt.
    pub fn platform_input_files(&self) -> &[PathBuf] {
        &self.platform_inputs
    }
    pub fn context_metrics(&self) -> impl Iterator<Item = BinaryContextMetrics<'_>> {
        self.contexts.iter().map(|context| BinaryContextMetrics {
            context: &context.name,
            found: context.cache_metrics.found,
            unknown: context.cache_metrics.unknown,
            retained_bytes: context.cache_metrics.retained_bytes,
            requests: context.cache_metrics.requests,
            phase: context.phase,
            active_method: context.active_method,
            pending_methods: context.pending_methods,
            deferred_admissions: context.admission.deferred,
            derived_methods: context.admission.methods,
            method_slots_released: context.admission.method_slots_released,
            method_slots_received: context.admission.method_slots_received,
            retried_callers: context.admission.retried_callers,
            method_guard_rows: context.admission.method_guard_rows,
            scoped_dispatch_rows: context.admission.scoped_dispatch_rows,
            receiver_dispatch_rows: context.admission.receiver_dispatch_rows,
            trusted_runtime_models: context.cache_metrics.trusted_runtime_models,
            trusted_runtime_model_fallbacks: context.cache_metrics.trusted_runtime_model_fallbacks,
        })
    }
    pub fn envelope_metrics(&self) -> binary::EnvelopeMetrics {
        self.envelope_cache.metrics()
    }
    pub fn retained_input_bytes(&self) -> usize {
        self.admitted
            .iter()
            .map(AdmittedEntry::retained_bytes)
            .sum()
    }
}
fn context_loader(
    context: &AdmittedContext,
    admitted: &[AdmittedEntry],
) -> Result<CapturedClasspath, Error> {
    let entries: Vec<_> = context.entries_at.iter().map(|&i| &admitted[i]).collect();
    CapturedClasspath::from_admitted(
        context.entries.clone(),
        &entries,
        Limits::default(),
        context.java_feature,
    )
    .map_err(convert_error)
}
fn convert_error(error: binary::BinaryError) -> Error {
    Error::Message(error.to_string())
}
fn provenance_failure(kind: binary::ErrorKind) -> bool {
    matches!(
        kind,
        binary::ErrorKind::HashMismatch
            | binary::ErrorKind::DirectoryFingerprintMismatch
            | binary::ErrorKind::Io
            | binary::ErrorKind::BadCrc
            | binary::ErrorKind::InvalidZip
            | binary::ErrorKind::SymlinkInput
    )
}
struct Endpoints<'a>(HashMap<(StrId, &'a str), Option<SymbolId>>);
impl<'a> Endpoints<'a> {
    fn new(facts: &'a FactSnapshot, names: &HashSet<&str>) -> Self {
        let mut index = HashMap::new();
        for (i, symbol) in facts.symbols.iter().enumerate() {
            let name = facts.text(symbol.name);
            if names.contains(name) {
                index
                    .entry((symbol.context, name))
                    .and_modify(|old| *old = None)
                    .or_insert(Some(SymbolId(i as u32)));
            }
        }
        Self(index)
    }
    fn get(&self, name: &str, context: StrId) -> Result<SymbolId, Error> {
        self.0
            .get(&(context, name))
            .ok_or_else(|| Error::Message(format!("missing compiler binary binding: {name}")))?
            .ok_or(Error::Invalid("ambiguous compiler binary binding"))
    }
}
fn cache_class(
    context: &mut AdmittedContext,
    loader: &mut CapturedClasspath,
    owner: &str,
) -> Result<Option<Arc<ClassBytes>>, Error> {
    context.cache_metrics.requests += 1;
    if let Some(cached) = context.classes.get(owner) {
        return Ok(match cached {
            CachedClass::Found(bytes) => Some(bytes.clone()),
            CachedClass::Unknown(_) => None,
        });
    }
    if context.classes.len() >= context.admission.limits.classes_per_context {
        if context.admission.derived {
            return Err(DeferredReason::Classes.error());
        }
        let mut unknown_reasons = std::collections::BTreeMap::<String, usize>::new();
        for cached in context.classes.values() {
            if let CachedClass::Unknown(reason) = cached {
                *unknown_reasons.entry(format!("{reason:?}")).or_default() += 1;
            }
        }
        return Err(Error::Message(format!(
            "resource limit: binary class count: {}",
            serde_json::json!({
                "context": context.name, "requested_owner": owner, "phase": context.phase,
                "active_method": context.active_method.0, "pending_methods": context.pending_methods,
                "found": context.cache_metrics.found, "unknown": context.cache_metrics.unknown,
                "retained_bytes": context.cache_metrics.retained_bytes,
                "requests": context.cache_metrics.requests, "unknown_reasons": unknown_reasons,
            })
        )));
    }
    let found = match loader.lookup(owner) {
        Ok(ClassLookup::Found(class)) => {
            if context
                .cache_metrics
                .retained_bytes
                .saturating_add(class.bytes.len())
                > context.admission.limits.bytes_per_context
            {
                if context.admission.derived {
                    return Err(DeferredReason::Bytes.error());
                }
                return Err(Error::Limit("binary class snapshot bytes"));
            }
            let hash = class
                .proof
                .class_hash
                .ok_or(Error::Invalid("binary class receipt"))?;
            let index = class
                .proof
                .selected_entry
                .ok_or(Error::Invalid("binary selected classpath entry"))?;
            // Provider selection and all preceding absence proofs have already
            // been verified in this context. Only immutable content metadata is
            // shared: origins, compiler IDs and resolution decisions stay local.
            let cached = context
                .shared_metadata
                .lock()
                .map_err(|_| Error::Invalid("binary metadata cache lock"))?
                .get(&hash)
                .and_then(Weak::upgrade);
            let metadata = if let Some(metadata) = cached {
                metadata
            } else {
                let metadata = Arc::new(
                    binary::ClassMetadata::new(Arc::from(class.bytes), Limits::default())
                        .map_err(convert_error)?,
                );
                if metadata.hash() != hash {
                    return Err(Error::Invalid("binary metadata content identity"));
                }
                let mut shared = context
                    .shared_metadata
                    .lock()
                    .map_err(|_| Error::Invalid("binary metadata cache lock"))?;
                if shared.len() < MAX_SHARED_METADATA_ENTRIES {
                    shared.insert(hash, Arc::downgrade(&metadata));
                }
                metadata
            };
            if metadata.name() != owner {
                return Err(Error::Invalid("binary class header owner"));
            }
            if context
                .cache_metrics
                .retained_bytes
                .saturating_add(context.cache_metrics.metadata_bytes)
                .saturating_add(metadata.owned_bytes())
                > context.admission.limits.bytes_per_context
            {
                if context.admission.derived {
                    return Err(DeferredReason::Bytes.error());
                }
                return Err(Error::Limit("binary class snapshot bytes"));
            }
            let bytes = Arc::new(ClassBytes {
                bytes: metadata.bytes().clone(),
                hash,
                origin: format!("{}!/{owner}.class", context.entries[index].path.display()),
                metadata,
            });
            context.cache_metrics.found += 1;
            context.cache_metrics.retained_bytes += bytes.bytes.len();
            context.cache_metrics.metadata_bytes += bytes.metadata.metadata_bytes();
            context
                .classes
                .insert(owner.to_owned(), CachedClass::Found(bytes.clone()));
            Some(bytes)
        }
        Ok(ClassLookup::Absent(_)) => {
            context.cache_metrics.unknown += 1;
            context.classes.insert(
                owner.to_owned(),
                CachedClass::Unknown(binary::ErrorKind::ClassNotFound),
            );
            None
        }
        Err(error) => {
            if provenance_failure(error.kind) {
                return Err(convert_error(error));
            }
            context.cache_metrics.unknown += 1;
            context
                .classes
                .insert(owner.to_owned(), CachedClass::Unknown(error.kind));
            None
        }
    };
    Ok(found)
}
pub fn load_binary_manifest(path: &Path, facts: &FactSnapshot) -> Result<OwnedBinaryInputs, Error> {
    load_binary_manifest_with_options(path, facts, &BinaryInputOptions::default())
}
pub fn load_binary_manifest_with_options(
    path: &Path,
    facts: &FactSnapshot,
    options: &BinaryInputOptions,
) -> Result<OwnedBinaryInputs, Error> {
    load_binary_manifest_with_platform(path, facts, options, None)
}
pub fn load_binary_manifest_with_platform(
    path: &Path,
    facts: &FactSnapshot,
    options: &BinaryInputOptions,
    platform: Option<&crate::binary_platform::PlatformOptions>,
) -> Result<OwnedBinaryInputs, Error> {
    use std::io::Read;
    if options.workers == 0 || options.max_retained_bytes == 0 {
        return Err(Error::Invalid("binary admission limits"));
    }
    let file = std::fs::File::open(path)?;
    if file.metadata()?.len() > MAX_MANIFEST_BYTES {
        return Err(Error::Limit("binary manifest bytes"));
    }
    let mut bytes = Vec::new();
    file.take(MAX_MANIFEST_BYTES + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 > MAX_MANIFEST_BYTES {
        return Err(Error::Limit("binary manifest bytes"));
    }
    let manifest: Manifest = serde_json::from_slice(&bytes)
        .map_err(|e| Error::Message(format!("binary manifest JSON: {e}")))?;
    let platform = platform.map(crate::binary_platform::admit).transpose()?;
    if manifest.declared_platform.as_ref() != platform.as_ref().map(|p| &p.binding)
        || platform
            .as_ref()
            .is_some_and(|p| manifest.java_feature != Some(p.java_feature))
    {
        return Err(Error::Invalid(
            "explicit declared platform/native map binding",
        ));
    }
    if manifest.version != 1 || manifest.revision.is_none() && manifest.facts_identity.is_none() {
        return Err(Error::Invalid("binary manifest version or fact binding"));
    }
    if manifest
        .revision
        .as_deref()
        .is_some_and(|r| r.is_empty() || r != facts.text(facts.revision))
    {
        return Err(Error::Invalid("binary manifest revision"));
    }
    if manifest
        .facts_identity
        .as_deref()
        .map(ContentHash::from_hex)
        .transpose()?
        .is_some_and(|id| id != facts.identity)
    {
        return Err(Error::Invalid("binary manifest facts identity"));
    }
    if manifest.methods.len() > MAX_METHODS || manifest.contexts.len() > 1024 {
        return Err(Error::Limit("binary manifest bindings"));
    }
    // One sparse scan, independent of binding count. Names/contexts borrow the
    // immutable facts; do not rescan a million symbols for each manifest row.
    let requested: HashSet<_> = manifest
        .types
        .iter()
        .map(|b| b.compiler_symbol.as_str())
        .chain(
            manifest
                .methods
                .iter()
                .filter_map(|b| b.compiler_symbol.as_deref()),
        )
        .collect();
    let endpoints = Endpoints::new(facts, &requested);
    drop(requested);
    let base = path.parent().unwrap_or(Path::new("."));
    let mut context_ids = HashMap::new();
    let shared_metadata = SharedMetadata::default();
    let mut contexts = Vec::new();
    let mut platform_contexts = HashSet::new();
    for context in manifest.contexts {
        if context_ids.contains_key(&context.id) {
            return Err(Error::Invalid("duplicate binary context"));
        }
        let id = facts
            .symbols
            .iter()
            .map(|s| s.context)
            .chain(facts.files.iter().map(|f| f.context))
            .find(|id| facts.text(*id) == context.id)
            .ok_or(Error::Invalid(
                "binary context is not a captured compiler context",
            ))?;
        let mut entries = Vec::with_capacity(context.entries.len());
        for entry in context.entries {
            let kind = match entry.kind.as_str() {
                "jar" => EntryKind::Jar,
                "directory" => EntryKind::Directory {
                    files: entry
                        .files
                        .ok_or(Error::Invalid("binary directory file count"))?,
                    bytes: entry
                        .bytes
                        .ok_or(Error::Invalid("binary directory byte count"))?,
                },
                "absent_empty_output" => EntryKind::AbsentEmptyOutput,
                "unavailable" => EntryKind::Unavailable,
                _ => return Err(Error::Invalid("binary classpath entry kind")),
            };
            let sha256 = entry
                .sha256
                .as_deref()
                .map(ContentHash::from_hex)
                .transpose()?
                .unwrap_or_default();
            if entry.sha256.is_none() && !matches!(kind, EntryKind::Unavailable) {
                return Err(Error::Invalid("binary classpath digest"));
            }
            entries.push(ClasspathEntry {
                path: if entry.path.is_absolute() {
                    entry.path
                } else {
                    base.join(entry.path)
                },
                sha256,
                kind,
            });
        }
        if platform
            .as_ref()
            .is_some_and(|p| p.contains_context(&context.id))
        {
            let platform = platform.as_ref().unwrap();
            if entries.first() != Some(&platform.entry)
                || entries.iter().skip(1).any(|entry| entry == &platform.entry)
            {
                return Err(Error::Invalid("declared platform bootstrap order"));
            }
            platform_contexts.insert(id);
        } else if platform
            .as_ref()
            .is_some_and(|p| entries.iter().any(|e| e == &p.entry))
        {
            return Err(Error::Invalid("declared platform foreign context"));
        }
        context_ids.insert(context.id.clone(), contexts.len());
        contexts.push(AdmittedContext {
            id,
            name: context.id,
            cache_metrics: ClassCacheMetrics::default(),
            phase: "explicit",
            active_method: SymbolId::NONE,
            active_file: FileId::NONE,
            pending_methods: 0,
            admission: Admission::default(),
            entries,
            classes: HashMap::new(),
            shared_metadata: shared_metadata.clone(),
            java_feature: manifest.java_feature,
            entries_at: Vec::new(),
        });
    }
    if platform.is_some() && platform_contexts.is_empty() {
        return Err(Error::Invalid("declared platform has no native context"));
    }
    let mut types = HashMap::new();
    let mut type_aliases = Vec::new();
    let mut type_symbols = HashSet::new();
    for binding in manifest.types {
        let context = *context_ids
            .get(&binding.context)
            .ok_or(Error::Invalid("binary type context"))?;
        let symbol = endpoints.get(&binding.compiler_symbol, contexts[context].id)?;
        if !type_symbols.insert(symbol) {
            return Err(Error::Invalid("duplicate binary compiler type binding"));
        }
        let key = (context, binding.jvm_owner);
        if let Some(&canonical) = types.get(&key) {
            type_aliases.push(BoundTypeAlias {
                context,
                owner: key.1,
                symbol,
                canonical,
            });
        } else {
            types.insert(key, symbol);
        }
    }
    let mut methods = Vec::with_capacity(manifest.methods.len());
    let mut method_keys = HashSet::new();
    let mut compiler_keys = HashSet::new();
    for binding in manifest.methods {
        let context = *context_ids
            .get(&binding.context)
            .ok_or(Error::Invalid("binary method context"))?;
        let descriptor = binary::method_descriptor(&binding.descriptor).map_err(convert_error)?;
        if binding
            .receiver_parameter
            .is_some_and(|i| i as usize >= descriptor.parameter_count)
        {
            return Err(Error::Invalid("binary receiver parameter"));
        }
        if !method_keys.insert((
            context,
            binding.jvm_owner.clone(),
            binding.jvm_name.clone(),
            binding.descriptor.clone(),
        )) {
            return Err(Error::Invalid("duplicate binary method descriptor"));
        }
        let symbol = binding
            .compiler_symbol
            .as_deref()
            .map(|name| endpoints.get(name, contexts[context].id))
            .transpose()?;
        if let Some(symbol) = symbol {
            if !compiler_keys.insert(symbol) {
                return Err(Error::Invalid(
                    "compiler symbol has multiple binary method bindings",
                ));
            }
            let record = &facts.symbols[symbol.index()];
            let trait_initializer = binding.jvm_name == "$init$"
                && binding.receiver_parameter == Some(0)
                && facts.symbol_name(symbol).ends_with('#')
                && descriptor.return_type == "V"
                && descriptor.parameters().next()
                    == Some(format!("L{};", binding.jvm_owner).as_str());
            let explicit_type = types.get(&(context, binding.jvm_owner.clone())).copied();
            let owner = if let Some(owner) = explicit_type {
                // An object identity also names its enclosing class's module
                // accessor. The explicit class ABI binding distinguishes that
                // executable method from the object's own initializer.
                if owner != symbol && owner != record.owner {
                    return Err(Error::Invalid("conflicting explicit compiler method owner"));
                }
                owner
            } else if matches!(record.kind, 10 | 13 | 14) || trait_initializer {
                symbol
            } else {
                record.owner
            };
            if !owner.is_none() {
                let key = (context, binding.jvm_owner.clone());
                if let Some(old) = types.insert(key, owner) {
                    if old != owner {
                        return Err(Error::Message(format!(
                            "conflicting binary compiler owner binding for {} in {}: {} has owner {}, explicit {}",
                            binding.jvm_owner,
                            facts.text(contexts[context].id),
                            facts.symbol_name(symbol),
                            facts.symbol_name(owner),
                            facts.symbol_name(old)
                        )));
                    }
                }
            }
        }
        methods.push(BoundMethod {
            context,
            symbol,
            owner: binding.jvm_owner,
            name: binding.jvm_name,
            descriptor: binding.descriptor,
            receiver_parameter: binding.receiver_parameter,
        });
    }
    let mut hash = Sha256::new();
    hash.update(b"binary-input-manifest/2");
    hash.update(&bytes);
    let mut unique = HashMap::new();
    let mut entries = Vec::new();
    for context in &mut contexts {
        for entry in &context.entries {
            let index = if let Some(&index) = unique.get(entry) {
                index
            } else {
                let index = entries.len();
                unique.insert(entry.clone(), index);
                entries.push(entry.clone());
                index
            };
            context.entries_at.push(index);
        }
    }
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(options.workers)
        .build()
        .map_err(|e| Error::Message(e.to_string()))?;
    let charged = std::sync::atomic::AtomicUsize::new(0);
    let admitted: Vec<_> = pool.install(|| {
        entries
            .into_par_iter()
            .map(|entry| {
                let mut limits = Limits::default();
                let (reservation, max_archive_bytes) =
                    AdmittedEntry::reservation_bytes(&entry, limits).map_err(convert_error)?;
                charged
                    .fetch_update(
                        std::sync::atomic::Ordering::Relaxed,
                        std::sync::atomic::Ordering::Relaxed,
                        |total| {
                            total
                                .checked_add(reservation)
                                .filter(|total| *total <= options.max_retained_bytes)
                        },
                    )
                    .map_err(|_| Error::Limit("shared binary input bytes"))?;
                limits.max_retained_bytes = reservation;
                limits.max_archive_bytes = max_archive_bytes;
                let admitted = AdmittedEntry::admit(entry, limits, manifest.java_feature)
                    .map_err(convert_error)?;
                charged.fetch_sub(
                    reservation - admitted.retained_bytes(),
                    std::sync::atomic::Ordering::Relaxed,
                );
                Ok(admitted)
            })
            .collect::<Result<_, Error>>()
    })?;
    let retained = admitted.iter().try_fold(0usize, |total, entry| {
        total
            .checked_add(entry.retained_bytes())
            .ok_or(Error::Limit("shared binary input bytes"))
    })?;
    if retained > options.max_retained_bytes {
        return Err(Error::Limit("shared binary input bytes"));
    }
    for entry in &admitted {
        if let Some(error) = entry.error() {
            if provenance_failure(error.kind) {
                return Err(convert_error(error));
            }
            hash.update(format!("{:?}", error.kind));
        }
    }
    for (index, context) in contexts.iter_mut().enumerate() {
        let mut loader = context_loader(context, &admitted)?;
        for method in methods.iter().filter(|m| m.context == index) {
            cache_class(context, &mut loader, &method.owner)?;
        }
        let mut classes: Vec<_> = context.classes.iter().collect();
        classes.sort_unstable_by_key(|(owner, _)| *owner);
        for (owner, class) in classes {
            hash.update(owner);
            match class {
                CachedClass::Found(bytes) => hash.update(bytes.hash.0),
                CachedClass::Unknown(kind) => hash.update(format!("{kind:?}")),
            }
        }
    }
    Ok(OwnedBinaryInputs {
        identity: ContentHash(hash.finalize().into()),
        raw_identity: facts.identity,
        contexts,
        types,
        type_aliases,
        methods,
        admitted,
        envelope_cache: binary::EnvelopeCache::new(
            options
                .max_retained_bytes
                .saturating_sub(retained)
                .min(8 * 1024 * 1024),
        ),
        platform_inputs: platform
            .as_ref()
            .map_or_else(Vec::new, |p| p.input_files().to_vec()),
        platform_contexts,
    })
}

fn append_text(facts: &mut FactSnapshot, text: &str) -> Result<StrId, Error> {
    let id = StrId::checked(facts.strings.entries.len())?;
    let len = u32::try_from(text.len()).map_err(|_| Error::Limit("binary metadata string"))?;
    facts.strings.entries.push(TextRange {
        start: facts.strings.bytes.len() as u64,
        len,
    });
    facts.strings.bytes.extend_from_slice(text.as_bytes());
    Ok(id)
}
fn native_name(owner: &str, name: &str, descriptor: &str) -> String {
    format!(
        "@jvm/{}:{owner}{}:{name}{}:{descriptor}",
        owner.len(),
        name.len(),
        descriptor.len()
    )
}
fn declare(
    facts: &mut FactSnapshot,
    context: StrId,
    owner: SymbolId,
    name: &str,
    kind: u32,
    file: FileId,
    flags: u16,
) -> Result<SymbolId, Error> {
    let id = SymbolId::checked(facts.symbols.len())?;
    let name = append_text(facts, name)?;
    facts.symbols.push(SymbolRecord {
        name,
        display: StrId::NONE,
        owner,
        file,
        context,
        kind,
        properties: if flags & 0x0400 != 0 { 4 } else { 0 },
        signature: StrId::NONE,
        span: Span::default(),
        flags: SYMBOL_NATIVE_BINARY,
    });
    Ok(id)
}
fn add_issue(facts: &mut FactSnapshot, symbol: SymbolId, file: FileId, kind: IssueKind) {
    facts.issues.push(IssueRecord {
        kind,
        file,
        symbol,
        detail: StrId::NONE,
    });
}

#[derive(Clone, Hash, PartialEq, Eq)]
struct MethodKey {
    context: usize,
    owner: String,
    name: String,
    descriptor: String,
}
#[derive(Clone)]
struct MethodData {
    symbol: SymbolId,
    owner: SymbolId,
    flags: u16,
    receiver_parameter: Option<u16>,
}
/// Successful declarations awaiting the stage-local discovery indexes. Borrow
/// names/descriptors from verified metadata rather than cloning every key.
struct MethodEvent {
    context: usize,
    class: Arc<ClassBytes>,
    ordinal: usize,
    data: MethodData,
}
use crate::binary_lower::Initialization;

struct Registry {
    types: HashMap<(usize, String), SymbolId>,
    methods: HashMap<MethodKey, MethodData>,
    method_events: Vec<MethodEvent>,
    synthetic_methods: usize,
    fields: HashMap<MethodKey, SymbolId>,
    accessors: accessors::State,
    files: HashMap<(usize, String), FileId>,
    empty: StrId,
    initialized: HashSet<SymbolId>,
    static_phases: HashMap<(usize, String), Initialization>,
    static_active: HashSet<(usize, String)>,
    bootstrap: HashMap<StrId, BootstrapObject>,
}
enum BootstrapObject {
    Compiler(SymbolId),
    /// Exact declared image bytes must use ordinary member/static lowering.
    DeclaredPlatform,
}
impl Registry {
    fn file(
        &mut self,
        facts: &mut FactSnapshot,
        context: usize,
        context_id: StrId,
        owner: &str,
        class: &ClassBytes,
    ) -> Result<FileId, Error> {
        let key = (context, owner.to_owned());
        if let Some(file) = self.files.get(&key) {
            return Ok(*file);
        }
        let path = append_text(facts, &class.origin)?;
        let file = FileId::checked(facts.files.len())?;
        facts.files.push(FileRecord {
            path,
            source: self.empty,
            revision: facts.revision,
            context: context_id,
            source_hash: class.hash,
            flags: FILE_BINARY_SOURCE,
        });
        self.files.insert(key, file);
        Ok(file)
    }
    fn class(
        &mut self,
        facts: &mut FactSnapshot,
        context: usize,
        context_id: StrId,
        owner: &str,
        file: FileId,
        bytes: &ClassBytes,
    ) -> Result<SymbolId, Error> {
        let key = (context, owner.to_owned());
        let symbol = if let Some(symbol) = self.types.get(&key) {
            *symbol
        } else {
            let symbol = declare(
                facts,
                context_id,
                SymbolId::NONE,
                &native_name(owner, "<type>", ""),
                13,
                file,
                0,
            )?;
            self.types.insert(key, symbol);
            symbol
        };
        if self.initialized.insert(symbol) {
            let class = bytes.metadata.as_ref();
            if class.name() != owner {
                return Err(Error::Invalid("binary class header owner"));
            }
            let nominal = facts.symbol_name(symbol).ends_with('#');
            admit_header_authority(&mut facts.symbols[symbol.index()], nominal, class.flags());
            if facts.symbols[symbol.index()].flags & SYMBOL_DEFINED == 0
                && !class
                    .methods()
                    .any(|m| matches!(m.name, "<clinit>" | "$init$"))
            {
                facts.bodies.push(BodyRecord {
                    symbol,
                    file,
                    span: Span::default(),
                    name_span: Span::default(),
                    operations: IdRange {
                        start: u32::try_from(facts.operations.len())
                            .map_err(|_| Error::Limit("binary initialization operations"))?,
                        len: 0,
                    },
                    parameters: IdRange::default(),
                    body_hash: bytes.hash,
                    flags: BODY_BINARY_RECIPE | BODY_INITIALIZER | BODY_STATIC_INITIALIZER,
                });
            }
        }
        Ok(symbol)
    }
    fn method(
        &mut self,
        facts: &mut FactSnapshot,
        context: usize,
        ctx: &mut AdmittedContext,
        loader: &mut CapturedClasspath,
        member: MemberRef<'_>,
        explicit: Option<SymbolId>,
        receiver_parameter: Option<u16>,
        pending: &mut VecDeque<MethodKey>,
    ) -> Result<SymbolId, Error> {
        // The JVM bootstrap Object constructor has a specified empty effect.
        // Bind the existing compiler bootstrap identity; do not manufacture a
        // fake classfile/native declaration when JRT is outside the capture.
        if member.owner == "java/lang/Object"
            && member.name == "<init>"
            && member.descriptor == "()V"
        {
            if let Some(BootstrapObject::Compiler(symbol)) = self.bootstrap.get(&ctx.id) {
                return Ok(*symbol);
            }
        }
        let key = MethodKey {
            context,
            owner: member.owner.to_owned(),
            name: member.name.to_owned(),
            descriptor: member.descriptor.to_owned(),
        };
        if let Some(data) = self.methods.get(&key) {
            return Ok(data.symbol);
        }
        ctx.admission
            .check_method(self.methods.len().saturating_add(self.synthetic_methods))?;
        let Some(bytes) = cache_class(ctx, loader, member.owner)? else {
            return Ok(SymbolId::NONE);
        };
        let class = bytes.metadata.as_ref();
        let Ok(ordinal) = class.method_index(member.name, Some(member.descriptor)) else {
            return Ok(SymbolId::NONE);
        };
        let method = class.methods().nth(ordinal).unwrap();
        if receiver_parameter.is_some() && method.flags & 8 == 0 {
            return Err(Error::Invalid(
                "binary receiver parameter on instance method",
            ));
        }
        let file = self.file(facts, context, ctx.id, member.owner, &bytes)?;
        let owner = self.class(facts, context, ctx.id, member.owner, file, &bytes)?;
        if facts.symbols[owner.index()].kind == 0 {
            facts.symbols[owner.index()].kind = if class.flags() & 0x0200 != 0 { 14 } else { 13 };
        }
        let symbol = if let Some(symbol) = explicit {
            symbol
        } else {
            declare(
                facts,
                ctx.id,
                owner,
                &native_name(member.owner, member.name, member.descriptor),
                if member.name == "<init>" { 21 } else { 3 },
                file,
                method.flags,
            )?
        };
        if facts.symbols[symbol.index()].flags & SYMBOL_DEFINED == 0 {
            facts.symbols[symbol.index()].properties = (facts.symbols[symbol.index()].properties
                & !4)
                | if method.flags & 0x0400 != 0 { 4 } else { 0 };
        }
        let data = MethodData {
            symbol,
            owner,
            flags: method.flags,
            receiver_parameter,
        };
        self.method_events.push(MethodEvent {
            context,
            class: bytes.clone(),
            ordinal,
            data: data.clone(),
        });
        self.methods.insert(key.clone(), data);
        ctx.admission.admitted_method();
        pending.push_back(key);
        // invokestatic triggers initialization of the actual declaring class,
        // independently of whether the called body touches a static field.
        if method.flags & 0x0008 != 0
            && member.name != "<clinit>"
            && class
                .methods()
                .any(|method| method.name == "<clinit>" && method.descriptor == "()V")
        {
            let result = self.method(
                facts,
                context,
                ctx,
                loader,
                MemberRef {
                    owner: member.owner,
                    name: "<clinit>",
                    descriptor: "()V",
                },
                None,
                None,
                pending,
            );
            optional_effect(
                facts,
                ctx,
                ctx.active_method,
                ctx.active_file,
                result,
                SymbolId::NONE,
            )?;
        }
        Ok(symbol)
    }
    fn call(
        &mut self,
        facts: &mut FactSnapshot,
        context: usize,
        ctx: &mut AdmittedContext,
        loader: &mut CapturedClasspath,
        member: MemberRef<'_>,
        kind: binary::InvokeKind,
        caller: &str,
        pending: &mut VecDeque<MethodKey>,
    ) -> Result<(SymbolId, Initialization), Error> {
        if member.owner == "java/lang/Object"
            && member.name == "<init>"
            && member.descriptor == "()V"
        {
            return Ok((
                self.method(facts, context, ctx, loader, member, None, None, pending)?,
                Initialization::KnownEmpty,
            ));
        }
        match crate::binary_resolve::resolve_method_metadata(member, kind, Some(caller), |owner| {
            Ok(cache_class(ctx, loader, owner)?.map(|class| class.metadata.clone()))
        })? {
            crate::binary_resolve::Resolution::Found(resolved) => {
                let symbol = self.method(
                    facts,
                    context,
                    ctx,
                    loader,
                    MemberRef {
                        owner: &resolved.declared_owner,
                        name: member.name,
                        descriptor: member.descriptor,
                    },
                    None,
                    None,
                    pending,
                )?;
                let phase = if kind == binary::InvokeKind::Static && member.name != "<clinit>" {
                    let result = self.static_phase(
                        facts,
                        context,
                        ctx,
                        loader,
                        &resolved.declared_owner,
                        pending,
                    );
                    optional_phase(facts, ctx, result)?
                } else {
                    Initialization::KnownEmpty
                };
                Ok((symbol, phase))
            }
            crate::binary_resolve::Resolution::Unknown(_) => {
                Ok((SymbolId::NONE, Initialization::Unknown))
            }
        }
    }
    fn field(
        &mut self,
        facts: &mut FactSnapshot,
        context: usize,
        ctx: &mut AdmittedContext,
        loader: &mut CapturedClasspath,
        member: MemberRef<'_>,
        is_static: bool,
        pending: &mut VecDeque<MethodKey>,
    ) -> Result<(SymbolId, Initialization), Error> {
        match crate::binary_resolve::resolve_field_metadata(member, is_static, |owner| {
            Ok(cache_class(ctx, loader, owner)?.map(|class| class.metadata.clone()))
        })? {
            crate::binary_resolve::Resolution::Found(resolved) => {
                let symbol = self.declared_field(
                    facts,
                    context,
                    ctx,
                    loader,
                    MemberRef {
                        owner: &resolved.declared_owner,
                        name: member.name,
                        descriptor: member.descriptor,
                    },
                    pending,
                )?;
                let phase = if is_static {
                    let result = self.static_phase(
                        facts,
                        context,
                        ctx,
                        loader,
                        &resolved.declared_owner,
                        pending,
                    );
                    optional_phase(facts, ctx, result)?
                } else {
                    Initialization::KnownEmpty
                };
                Ok((symbol, phase))
            }
            crate::binary_resolve::Resolution::Unknown(_) => {
                Ok((SymbolId::NONE, Initialization::Unknown))
            }
        }
    }
    /// JVM class initialization is separate from Scala instance/trait recipes.
    /// Preparation defaults precede superclass/default-interface initialization,
    /// followed by this class's own exact <clinit>. Interfaces do not initialize
    /// their superinterfaces. Every absence used here is class-hash verified.
    fn static_phase(
        &mut self,
        facts: &mut FactSnapshot,
        context: usize,
        ctx: &mut AdmittedContext,
        loader: &mut CapturedClasspath,
        owner: &str,
        pending: &mut VecDeque<MethodKey>,
    ) -> Result<Initialization, Error> {
        // A phase may publish and memoize preparation/effect recipes before
        // the caller is lowered. Keep its real guards even while that caller
        // probes method quota; a later retry must not pretend the cached phase
        // is complete merely because more declaration slots became available.
        let probing = std::mem::replace(&mut ctx.admission.probe_method_quota, false);
        let result = self.static_phase_inner(facts, context, ctx, loader, owner, pending);
        ctx.admission.probe_method_quota = probing;
        result
    }
    fn static_phase_inner(
        &mut self,
        facts: &mut FactSnapshot,
        context: usize,
        ctx: &mut AdmittedContext,
        loader: &mut CapturedClasspath,
        owner: &str,
        pending: &mut VecDeque<MethodKey>,
    ) -> Result<Initialization, Error> {
        if owner == "java/lang/Object"
            && !matches!(
                self.bootstrap.get(&ctx.id),
                Some(BootstrapObject::DeclaredPlatform)
            )
        {
            return Ok(Initialization::KnownEmpty);
        }
        let key = (context, owner.to_owned());
        if let Some(phase) = self.static_phases.get(&key) {
            return Ok(*phase);
        }
        if self.static_active.len() >= 128 || !self.static_active.insert(key.clone()) {
            return Ok(Initialization::Unknown);
        }
        let Some(bytes) = cache_class(ctx, loader, owner)? else {
            self.static_active.remove(&key);
            return Ok(Initialization::Unknown);
        };
        let class = bytes.metadata.as_ref();
        let file = self.file(facts, context, ctx.id, owner, &bytes)?;
        let class_symbol = self.class(facts, context, ctx.id, owner, file, &bytes)?;
        let mut operations: Vec<(Opcode, SymbolId)> = Vec::new();
        // JVM preparation makes every declared static slot zero/null before
        // superclass initialization can recursively observe this class.
        for field in class.fields().filter(|field| field.flags & 0x0008 != 0) {
            let symbol = self.declared_field(
                facts,
                context,
                ctx,
                loader,
                MemberRef {
                    owner,
                    name: field.name,
                    descriptor: field.descriptor,
                },
                pending,
            )?;
            operations.push((Opcode::Constant, SymbolId::NONE));
            operations.push((Opcode::StoreField, symbol));
        }
        let mut add_phase = |phase: Initialization| match phase {
            Initialization::KnownEmpty => {}
            Initialization::Target(symbol) => operations.push((Opcode::Initialize, symbol)),
            Initialization::Unknown => operations.push((Opcode::Unknown, SymbolId::NONE)),
        };
        if class.flags() & 0x0200 == 0 {
            if let Some(parent) = class.parent() {
                let result = self.static_phase(facts, context, ctx, loader, parent, pending);
                add_phase(optional_phase(facts, ctx, result)?);
            }
            // Enumerate superinterfaces in classfile order, parents before
            // children, retaining only interfaces which declare a default.
            let mut interfaces: Vec<_> = class
                .interfaces()
                .rev()
                .map(|owner| (owner.to_owned(), false))
                .collect();
            let mut seen = HashSet::new();
            while let Some((interface, expanded)) = interfaces.pop() {
                if interfaces.len() > MAX_CLASSES || seen.len() > MAX_CLASSES {
                    if ctx.admission.derived {
                        optional_effect(
                            facts,
                            ctx,
                            ctx.active_method,
                            ctx.active_file,
                            Err(DeferredReason::Classes.error()),
                            (),
                        )?;
                        add_phase(Initialization::Unknown);
                        break;
                    }
                    return Err(Error::Limit("static interface closure"));
                }
                let Some(interface_bytes) = guarded_class(
                    facts,
                    ctx,
                    loader,
                    &interface,
                    ctx.active_method,
                    ctx.active_file,
                )?
                else {
                    add_phase(Initialization::Unknown);
                    continue;
                };
                let info = interface_bytes.metadata.as_ref();
                if info.flags() & 0x0200 == 0 {
                    add_phase(Initialization::Unknown);
                    continue;
                }
                if !expanded {
                    if !seen.insert(interface.clone()) {
                        continue;
                    }
                    interfaces.push((interface, true));
                    interfaces.extend(
                        info.interfaces()
                            .rev()
                            .map(|owner| (owner.to_owned(), false)),
                    );
                } else if info.methods().any(|method| {
                    method.flags & (0x0008 | 0x0400 | 0x0002) == 0
                        && !matches!(method.name, "<init>" | "<clinit>")
                }) {
                    let result =
                        self.static_phase(facts, context, ctx, loader, &interface, pending);
                    add_phase(optional_phase(facts, ctx, result)?);
                }
            }
        }
        if class
            .methods()
            .any(|method| method.name == "<clinit>" && method.descriptor == "()V")
        {
            let result = self.method(
                facts,
                context,
                ctx,
                loader,
                MemberRef {
                    owner,
                    name: "<clinit>",
                    descriptor: "()V",
                },
                None,
                None,
                pending,
            );
            let initializer = optional_effect(
                facts,
                ctx,
                ctx.active_method,
                ctx.active_file,
                result,
                SymbolId::NONE,
            )?;
            operations.push(if initializer.is_none() {
                (Opcode::Unknown, SymbolId::NONE)
            } else {
                (Opcode::Initialize, initializer)
            });
        }
        let result = if operations.is_empty() {
            Initialization::KnownEmpty
        } else {
            let symbol = declare(
                facts,
                ctx.id,
                class_symbol,
                &native_name(owner, "<class-init>", "()V"),
                3,
                file,
                0x0008,
            )?;
            let body = BodyId::checked(facts.bodies.len())?;
            let start = u32::try_from(facts.operations.len())
                .map_err(|_| Error::Limit("static phase operations"))?;
            for &(opcode, target) in &operations {
                facts.operations.push(OperationRecord {
                    body,
                    opcode,
                    target,
                    dest: if opcode == Opcode::Constant {
                        ValueId(1)
                    } else {
                        ValueId::NONE
                    },
                    a: ValueId::NONE,
                    b: if opcode == Opcode::StoreField {
                        ValueId(1)
                    } else {
                        ValueId::NONE
                    },
                    arguments: IdRange::default(),
                    span: Span::default(),
                    flags: if opcode == Opcode::StoreField {
                        OP_STATIC_FIELD
                    } else {
                        0
                    },
                });
            }
            facts.bodies.push(BodyRecord {
                symbol,
                file,
                span: Span::default(),
                name_span: Span::default(),
                operations: IdRange {
                    start,
                    len: u32::try_from(operations.len())
                        .map_err(|_| Error::Limit("static phase length"))?,
                },
                parameters: IdRange::default(),
                body_hash: bytes.hash,
                flags: BODY_BINARY_RECIPE | BODY_STATIC_INITIALIZER,
            });
            Initialization::Target(symbol)
        };
        self.static_active.remove(&key);
        self.static_phases.insert(key, result);
        Ok(result)
    }
    fn declared_field(
        &mut self,
        facts: &mut FactSnapshot,
        context: usize,
        ctx: &mut AdmittedContext,
        loader: &mut CapturedClasspath,
        member: MemberRef<'_>,
        _pending: &mut VecDeque<MethodKey>,
    ) -> Result<SymbolId, Error> {
        let key = MethodKey {
            context,
            owner: member.owner.to_owned(),
            name: member.name.to_owned(),
            descriptor: member.descriptor.to_owned(),
        };
        if let Some(symbol) = self.fields.get(&key) {
            return Ok(*symbol);
        }
        let Some(bytes) = cache_class(ctx, loader, member.owner)? else {
            return Ok(SymbolId::NONE);
        };
        let class = bytes.metadata.as_ref();
        let Some(field) = class
            .field(member.name, member.descriptor)
            .map_err(convert_error)?
        else {
            return Ok(SymbolId::NONE);
        };
        if let Some(symbol) =
            accessors::backing_field(facts, self, context, ctx, loader, member, field.flags)?
        {
            self.fields.insert(key, symbol);
            return Ok(symbol);
        }
        let file = self.file(facts, context, ctx.id, member.owner, &bytes)?;
        let owner = self.class(facts, context, ctx.id, member.owner, file, &bytes)?;
        let symbol = declare(
            facts,
            ctx.id,
            owner,
            &native_name(member.owner, member.name, member.descriptor),
            20,
            file,
            field.flags,
        )?;
        self.fields.insert(key, symbol);
        Ok(symbol)
    }
}

pub fn augment_binary_facts(
    facts: &mut FactSnapshot,
    inputs: &mut OwnedBinaryInputs,
) -> Result<(), Error> {
    augment_binary_facts_with_limits(facts, inputs, NativeAdmissionLimits::default())
}
pub fn augment_binary_facts_with_limits(
    facts: &mut FactSnapshot,
    inputs: &mut OwnedBinaryInputs,
    limits: NativeAdmissionLimits,
) -> Result<(), Error> {
    limits.validate()?;
    for context in &mut inputs.contexts {
        if context.classes.len() > limits.classes_per_context
            || context
                .cache_metrics
                .retained_bytes
                .saturating_add(context.cache_metrics.metadata_bytes)
                > limits.bytes_per_context
        {
            return Err(Error::Limit(
                "mandatory binary class inventory exceeds admission limits",
            ));
        }
        context.admission.limits = limits;
    }
    facts.validate()?;
    if facts.identity != inputs.raw_identity {
        return Err(Error::Invalid(
            "binary enrichment requires original captured facts",
        ));
    }
    let value_accessors = crate::source_recipes::augment_eager_val_accessors(facts)?;
    if value_accessors != 0 {
        eprintln!(
            "{}",
            serde_json::json!({"stage":"source_val_accessors","materialized":value_accessors})
        );
    }
    // Keep compiler namespace authority before native class facets are projected.
    let source_module_candidates = source_modules::candidates(facts);
    let bootstrap = {
        let names = [
            "java/lang/Object#`<init>`().",
            "java/lang/Object#<init>().",
            "java/lang/Object#",
            "scala/AnyRef#",
        ];
        let endpoints = Endpoints::new(facts, &names.into_iter().collect());
        inputs
            .contexts
            .iter()
            .filter_map(|context| {
                if inputs.platform_contexts.contains(&context.id) {
                    return Some((context.id, BootstrapObject::DeclaredPlatform));
                }
                names
                    .iter()
                    .find_map(|name| endpoints.get(name, context.id).ok())
                    .map(|symbol| (context.id, BootstrapObject::Compiler(symbol)))
            })
            .collect()
    };
    let empty = append_text(facts, "")?;
    let mut registry = Registry {
        types: inputs.types.clone(),
        methods: HashMap::new(),
        method_events: Vec::new(),
        synthetic_methods: 0,
        fields: HashMap::new(),
        accessors: accessors::State::default(),
        files: HashMap::new(),
        empty,
        initialized: HashSet::new(),
        static_phases: HashMap::new(),
        static_active: HashSet::new(),
        bootstrap,
    };
    let mut pending = VecDeque::new();
    let mut done = HashSet::new();
    let mut existing: HashSet<_> = facts.bodies.iter().map(|b| b.symbol).collect();
    // One exact classfile may be bound explicitly to several compiler type
    // identities (for example a Scala alias and its Java nominal endpoint).
    // Keep the first endpoint canonical for JVM member resolution. Additional
    // aliases only receive an instance-header recipe when actual interface
    // bytes prove no Scala trait initializer exists. Static <clinit> remains a
    // separate phase and is never executed by implementing an interface.
    for alias in &inputs.type_aliases {
        let context = &mut inputs.contexts[alias.context];
        let mut loader = context_loader(context, &inputs.admitted)?;
        let Some(bytes) = cache_class(context, &mut loader, &alias.owner)? else {
            add_issue(facts, alias.symbol, FileId::NONE, IssueKind::MissingBinary);
            continue;
        };
        let class = bytes.metadata.as_ref();
        let file = registry.file(facts, alias.context, context.id, &alias.owner, &bytes)?;
        let canonical =
            registry.class(facts, alias.context, context.id, &alias.owner, file, &bytes)?;
        if canonical != alias.canonical {
            return Err(Error::Invalid("binary alias canonical endpoint"));
        }
        if class.name() != alias.owner {
            return Err(Error::Invalid("binary alias class header owner"));
        }
        let nominal = facts.symbol_name(alias.symbol).ends_with('#');
        if class.flags() & 0x0200 != 0 {
            admit_header_authority(
                &mut facts.symbols[alias.symbol.index()],
                nominal,
                class.flags(),
            );
        }
        if existing.contains(&alias.symbol) {
            continue;
        }
        let declaration = facts.symbols[alias.symbol.index()];
        if class.flags() & 0x0200 == 0
            || class.methods().any(|method| method.name == "$init$")
            || declaration.flags & SYMBOL_DEFINED != 0
            || !matches!(declaration.kind, 0 | 7 | 14)
        {
            add_issue(facts, alias.symbol, file, IssueKind::UnsupportedModel);
            continue;
        }
        if declaration.kind == 0 {
            facts.symbols[alias.symbol.index()].kind = 14;
        }
        let mut hash = Sha256::new();
        hash.update(b"verified-jvm-interface-instance-header/1");
        hash.update(bytes.hash.0);
        facts.bodies.push(BodyRecord {
            symbol: alias.symbol,
            file,
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange {
                start: u32::try_from(facts.operations.len())
                    .map_err(|_| Error::Limit("binary alias operations"))?,
                len: 0,
            },
            parameters: IdRange::default(),
            body_hash: ContentHash(hash.finalize().into()),
            flags: BODY_BINARY_RECIPE | BODY_INITIALIZER,
        });
        existing.insert(alias.symbol);
    }
    // Native methods are declared only after an exact classfile method match.
    // Declare all explicit maps first so later runtime calls reuse their IDs.
    macro_expansions::augment(facts, inputs, &mut registry, &mut pending)?;
    for (context_index, context) in inputs.contexts.iter_mut().enumerate() {
        let mut loader = context_loader(context, &inputs.admitted)?;
        for method in inputs.methods.iter().filter(|m| m.context == context_index) {
            let symbol = registry.method(
                facts,
                context_index,
                context,
                &mut loader,
                MemberRef {
                    owner: &method.owner,
                    name: &method.name,
                    descriptor: &method.descriptor,
                },
                method.symbol,
                method.receiver_parameter,
                &mut pending,
            )?;
            if symbol.is_none() {
                if let Some(symbol) = method.symbol {
                    add_issue(facts, symbol, FileId::NONE, IssueKind::MissingBinary);
                }
            }
        }
    }
    accessors::declare(facts, inputs, &mut registry, &mut pending, &mut existing)?;
    // All mandatory declarations exist before optional derived work. Reserve a
    // fair share of the remaining global method budget for each context so an
    // early inventory cannot consume every later context's body frontier.
    let remaining = limits.methods.saturating_sub(
        registry
            .methods
            .len()
            .saturating_add(registry.synthetic_methods),
    );
    let contexts = inputs.contexts.len().max(1);
    for (index, context) in inputs.contexts.iter_mut().enumerate() {
        context.admission.derived = true;
        context.admission.method_allowance =
            remaining / contexts + usize::from(index < remaining % contexts);
    }
    let global_module_reads = source_modules::declare_globals(
        facts,
        inputs,
        &mut registry,
        &source_module_candidates,
        &mut pending,
    )?;
    let mut generated_members = generated_members::Discovery::new(facts, inputs);
    // Parent publication belongs to a class, not each lowered method. Reuse
    // this one contextual pair set through the final hierarchy closure; source
    // parent rows retain their compiler order and are never rewritten here.
    let mut parents: HashSet<_> = facts
        .relations
        .iter()
        .filter(|relation| relation.kind == RelationKind::Parent)
        .map(|relation| (relation.source, relation.target))
        .collect();
    let mut roots = pending;
    // Exact compiler THIS calls are required declarations, ahead of the bulk
    // mandatory-body dependency closure. Their method/header/own-product proof
    // and fair/global charges are identical to ordinary generated discovery.
    while generated_members.admit_requested(facts, inputs, &mut registry, &mut roots)? {}
    // Deferred callers retain their exact key and all already admitted targets.
    // One final round reuses the same class cache/registry; source facts are
    // never decoded again and method declarations are charged only on insertion.
    let mut quota_blocked = VecDeque::new();
    let mut final_round = false;
    // A single-method discovery unit must not rebuild every context's admitted
    // classpath. Loaders contain shared admitted entries, not new byte copies.
    let scalatest_conflicts = scalatest::Conflicts::new(facts);
    let mut body_loaders: Vec<Option<CapturedClasspath>> =
        (0..inputs.contexts.len()).map(|_| None).collect();
    loop {
        let mut dependencies = VecDeque::new();
        for context_index in 0..inputs.contexts.len() {
            let mut pending: VecDeque<_> = roots
                .iter()
                .filter(|key| key.context == context_index)
                .cloned()
                .collect();
            if pending.is_empty() {
                continue;
            }
            let context = &mut inputs.contexts[context_index];
            context.phase = "native-body";
            if body_loaders[context_index].is_none() {
                body_loaders[context_index] = Some(context_loader(context, &inputs.admitted)?);
            }
            let loader = body_loaders[context_index].as_mut().unwrap();
            while let Some(key) = pending.pop_front() {
                context.admission.probe_method_quota = false;
                if !done.insert(key.clone()) {
                    continue;
                }
                let data = registry.methods[&key].clone();
                context.active_method = data.symbol;
                context.pending_methods = pending.len();
                if existing.contains(&data.symbol) {
                    continue;
                }
                if accessors::materialize(
                    facts,
                    &mut registry,
                    key.context,
                    context,
                    loader,
                    &key,
                    &data,
                    &existing,
                )? {
                    existing.insert(data.symbol);
                    continue;
                }
                let Some(bytes) = cache_class(context, loader, &key.owner)? else {
                    add_issue(facts, data.symbol, FileId::NONE, IssueKind::MissingBinary);
                    continue;
                };
                let parsed =
                    binary::parse_class(&bytes.bytes, Limits::default()).map_err(convert_error)?;
                let method = parsed
                    .method(&key.name, Some(&key.descriptor))
                    .map_err(convert_error)?;
                let class = bytes.metadata.as_ref();
                let file = registry.file(facts, key.context, context.id, &key.owner, &bytes)?;
                context.active_file = file;
                let declared_platform = inputs.platform_contexts.contains(&context.id);
                let scala_model = trusted_scala::model(
                    context,
                    loader,
                    &parsed,
                    method,
                    &bytes,
                    declared_platform,
                )?;
                let jdk_model = if scala_model.is_none()
                    && declared_platform
                    && trusted_scala::declared_class(context, &key.owner, &bytes)
                {
                    selector_models::binary_jdk::model(
                        &parsed,
                        method,
                        bytes.hash,
                        Limits::default(),
                    )
                } else {
                    None
                };
                let scalatest_model = if scala_model.is_none() && jdk_model.is_none() {
                    scalatest::model(
                        facts,
                        &scalatest_conflicts,
                        context,
                        loader,
                        &data,
                        &bytes,
                        &parsed,
                        method,
                    )?
                } else {
                    None
                };
                let scalatest_model_applied = scalatest_model.is_some();
                let model_applied =
                    scala_model.is_some() || jdk_model.is_some() || scalatest_model_applied;
                let model_candidate =
                    trusted_scala::candidate(&key.owner, &key.name, &key.descriptor)
                        || selector_models::binary_jdk::candidate(
                            &key.owner,
                            &key.name,
                            &key.descriptor,
                        )
                        || scalatest::candidate(&key.owner, &key.name, &key.descriptor);
                let (summary, model_initializers, primitive_reads, body_hash) =
                    if let Some(model) = scala_model {
                        (
                            model.summary,
                            model.additional_initialization_owners,
                            &[][..],
                            trusted_scala::body_hash(bytes.hash, &[model.memory_effect as u8]),
                        )
                    } else if let Some(model) = jdk_model {
                        (
                            model.summary,
                            model.additional_initialization_owners,
                            model.primitive_read_arguments,
                            trusted_scala::body_hash(
                                bytes.hash,
                                selector_models::binary_jdk::VERSION.as_bytes(),
                            ),
                        )
                    } else if let Some(model) = scalatest_model {
                        (model.summary, &[][..], &[][..], model.body_hash)
                    } else {
                        (
                            inputs.envelope_cache.summarize(
                                &parsed,
                                method,
                                bytes.hash,
                                Limits::default(),
                            ),
                            &[][..],
                            &[][..],
                            bytes.hash,
                        )
                    };
                // Lambda declaration publishes synthetic bodies immediately;
                // keep that existing bounded path single-pass. Ordinary callers
                // can delay publication safely while their targets are probed.
                let retryable = !final_round && summary.lambdas.is_empty();
                let refusals_before = context.admission.method_refusals;
                context.admission.probe_method_quota = retryable;
                let mut lambda_targets = Vec::with_capacity(summary.lambdas.len());
                for lambda in &summary.lambdas {
                    let result = lambdas::declare(
                        facts,
                        &mut registry,
                        key.context,
                        context,
                        loader,
                        &key,
                        data.owner,
                        file,
                        bytes.hash,
                        lambda,
                        &mut dependencies,
                    );
                    lambda_targets.push(optional_effect(
                        facts,
                        context,
                        data.symbol,
                        file,
                        result,
                        SymbolId::NONE,
                    )?);
                }
                let mut call_targets = Vec::with_capacity(summary.calls.len());
                let mut call_initializers = Vec::with_capacity(summary.calls.len());
                for call in &summary.calls {
                    let result = registry.call(
                        facts,
                        key.context,
                        context,
                        loader,
                        call.member,
                        call.kind,
                        &key.owner,
                        &mut dependencies,
                    );
                    let (target, phase) = optional_effect(
                        facts,
                        context,
                        data.symbol,
                        file,
                        result,
                        (SymbolId::NONE, Initialization::Unknown),
                    )?;
                    call_targets.push(target);
                    call_initializers.push(phase);
                }
                let mut allocation_classes = vec![SymbolId::NONE; summary.values.len()];
                let mut field_targets = vec![SymbolId::NONE; summary.values.len()];
                let mut value_initializers = vec![Initialization::KnownEmpty; summary.values.len()];
                for (i, value) in summary.values.iter().enumerate() {
                    match value {
                        binary::Value::Allocation { class, .. }
                        | binary::Value::MayAllocation { class, .. } => {
                            let constructor = match value {
                                binary::Value::Allocation { constructor, .. } => *constructor,
                                _ => None,
                            };
                            let result = registry.static_phase(
                                facts,
                                key.context,
                                context,
                                loader,
                                class,
                                &mut dependencies,
                            );
                            value_initializers[i] = optional_effect(
                                facts,
                                context,
                                data.symbol,
                                file,
                                result,
                                Initialization::Unknown,
                            )?;
                            if let Some(bytes) =
                                guarded_class(facts, context, loader, class, data.symbol, file)?
                            {
                                let file =
                                    registry.file(facts, key.context, context.id, class, &bytes)?;
                                allocation_classes[i] = registry.class(
                                    facts,
                                    key.context,
                                    context.id,
                                    class,
                                    file,
                                    &bytes,
                                )?;
                                if constructor.is_some_and(|call| {
                                    call_targets
                                        .get(call as usize)
                                        .is_some_and(|target| !target.is_none())
                                }) {
                                    generated_members.allocation(
                                        facts,
                                        key.context,
                                        class,
                                        allocation_classes[i],
                                    );
                                }
                            }
                        }
                        binary::Value::Field { member, .. }
                        | binary::Value::StaticField(member) => {
                            let modeled_field = if scalatest_model_applied {
                                scalatest::field(
                                    facts,
                                    &mut registry,
                                    key.context,
                                    context.id,
                                    file,
                                    *member,
                                )?
                            } else {
                                None
                            };
                            let result = if let Some(target) = modeled_field {
                                Ok((target, Initialization::KnownEmpty))
                            } else {
                                registry.field(
                                    facts,
                                    key.context,
                                    context,
                                    loader,
                                    *member,
                                    matches!(value, binary::Value::StaticField(_)),
                                    &mut dependencies,
                                )
                            };
                            let (target, phase) = optional_effect(
                                facts,
                                context,
                                data.symbol,
                                file,
                                result,
                                (SymbolId::NONE, Initialization::Unknown),
                            )?;
                            field_targets[i] = target;
                            value_initializers[i] = phase;
                        }
                        _ => {}
                    }
                }
                let mut write_targets = Vec::with_capacity(summary.field_writes.len());
                let mut write_initializers = Vec::with_capacity(summary.field_writes.len());
                for write in &summary.field_writes {
                    let modeled_field = if scalatest_model_applied {
                        scalatest::field(
                            facts,
                            &mut registry,
                            key.context,
                            context.id,
                            file,
                            write.member,
                        )?
                    } else {
                        None
                    };
                    let result = if let Some(target) = modeled_field {
                        Ok((target, Initialization::KnownEmpty))
                    } else {
                        registry.field(
                            facts,
                            key.context,
                            context,
                            loader,
                            write.member,
                            write.receiver.is_none(),
                            &mut dependencies,
                        )
                    };
                    let (target, phase) = optional_effect(
                        facts,
                        context,
                        data.symbol,
                        file,
                        result,
                        (SymbolId::NONE, Initialization::Unknown),
                    )?;
                    write_targets.push(target);
                    write_initializers.push(phase);
                }
                let flags = recipe_flags(
                    &key.name,
                    data.receiver_parameter,
                    facts.symbols[data.symbol.index()].kind,
                );
                // Source calls can enter an explicitly mapped static method
                // directly, without a bytecode caller's call-initializer metadata.
                // Reserve its entry operation before lowering so initialization
                // precedes all effects without inserting into a growing op arena.
                let entry_phase = if data.flags & 0x0008 != 0 && key.name != "<clinit>" {
                    let result = registry.static_phase(
                        facts,
                        key.context,
                        context,
                        loader,
                        &key.owner,
                        &mut dependencies,
                    );
                    optional_effect(
                        facts,
                        context,
                        data.symbol,
                        file,
                        result,
                        Initialization::Unknown,
                    )?
                } else {
                    Initialization::KnownEmpty
                };
                let mut model_phases = Vec::with_capacity(model_initializers.len());
                for owner in model_initializers {
                    let result = registry.static_phase(
                        facts,
                        key.context,
                        context,
                        loader,
                        owner,
                        &mut dependencies,
                    );
                    model_phases.push(optional_effect(
                        facts,
                        context,
                        data.symbol,
                        file,
                        result,
                        Initialization::Unknown,
                    )?);
                }
                context.admission.probe_method_quota = false;
                if retryable && context.admission.method_refusals != refusals_before {
                    quota_blocked.push_back(key);
                    continue;
                }
                let prefix_start = facts.operations.len();
                for phase in std::iter::once(entry_phase).chain(model_phases) {
                    let (opcode, target) = match phase {
                        Initialization::KnownEmpty => continue,
                        Initialization::Target(symbol) => (Opcode::Initialize, symbol),
                        Initialization::Unknown => (Opcode::Unknown, SymbolId::NONE),
                    };
                    facts.operations.push(OperationRecord {
                        body: BodyId::checked(facts.bodies.len())?,
                        opcode,
                        target,
                        dest: ValueId::NONE,
                        a: ValueId::NONE,
                        b: ValueId::NONE,
                        arguments: IdRange::default(),
                        span: Span::default(),
                        flags: 0,
                    });
                }
                let prefix_len = u32::try_from(facts.operations.len() - prefix_start)
                    .map_err(|_| Error::Limit("trusted model initialization"))?;
                let lowered = crate::binary_lower::lower_summary(
                    facts,
                    data.symbol,
                    file,
                    &summary,
                    &crate::binary_lower::Targets {
                        call_targets: &call_targets,
                        allocation_classes: &allocation_classes,
                        field_targets: &field_targets,
                        write_targets: &write_targets,
                        lambda_targets: &lambda_targets,
                        call_initializers: &call_initializers,
                        value_initializers: &value_initializers,
                        write_initializers: &write_initializers,
                        receiver_parameter: data.receiver_parameter,
                    },
                    body_hash,
                    flags,
                )?;
                facts.bodies[lowered.index()].operations.start -= prefix_len;
                facts.bodies[lowered.index()].operations.len += prefix_len;
                for &argument in primitive_reads {
                    facts.operations.push(OperationRecord {
                        body: lowered,
                        opcode: Opcode::ReadElements,
                        target: SymbolId::NONE,
                        dest: ValueId::NONE,
                        a: ValueId(u32::from(argument) + 1),
                        b: ValueId::NONE,
                        arguments: IdRange::default(),
                        span: Span::default(),
                        flags: OP_TRUSTED_PRIMITIVE_READ,
                    });
                    facts.bodies[lowered.index()].operations.len += 1;
                }
                if model_applied {
                    context.cache_metrics.trusted_runtime_models += 1;
                } else if model_candidate {
                    context.cache_metrics.trusted_runtime_model_fallbacks += 1;
                }
                existing.insert(data.symbol);
                // A generated JVM member may belong to a source class. Keep its
                // compiler-ordered parent list authoritative; bytecode erasure must
                // not append Java Object or reorder Scala trait linearization.
                if facts.symbols[data.owner.index()].flags & SYMBOL_DEFINED != 0 {
                    continue;
                }
                // Verified JVM hierarchy is a typed relation, independent of source
                // spelling. Supplied compiler owner bindings preserve cross-layer IDs.
                for parent in class.parent().into_iter().chain(class.interfaces()) {
                    let deferred_before = context.admission.deferred;
                    let parent_id = if let Some(bytes) =
                        guarded_hierarchy_class(facts, context, loader, parent, data.symbol, file)?
                    {
                        let file = registry.file(facts, key.context, context.id, parent, &bytes)?;
                        registry.class(facts, key.context, context.id, parent, file, &bytes)?
                    } else if let Some(id) = registry.types.get(&(key.context, parent.to_owned())) {
                        if context.admission.deferred == deferred_before
                            && parent != "java/lang/Object"
                            && facts.symbols[id.index()].flags & SYMBOL_DEFINED == 0
                        {
                            add_issue(facts, data.symbol, file, IssueKind::IncompleteHierarchy);
                        }
                        *id
                    } else {
                        if context.admission.deferred == deferred_before
                            && parent != "java/lang/Object"
                        {
                            add_issue(facts, data.symbol, file, IssueKind::IncompleteHierarchy);
                        }
                        continue;
                    };
                    if parents.insert((data.owner, parent_id)) {
                        facts.relations.push(RelationRecord {
                            source: data.owner,
                            target: parent_id,
                            kind: RelationKind::Parent,
                            file,
                        });
                    }
                }
            }
            context.admission.probe_method_quota = false;
        }
        // Drain exact local-summary dependencies before another speculative
        // implementation spends a declaration slot. Discovery yields after one
        // new implementation, keeping its helper/constructor chain ahead of the
        // next unrelated receiver/contract candidate.
        if dependencies.is_empty() {
            generated_members.admit(facts, inputs, &mut registry, &mut dependencies)?;
        }
        if dependencies.is_empty() {
            if final_round || quota_blocked.is_empty() {
                break;
            }
            let remaining = limits.methods.saturating_sub(
                registry
                    .methods
                    .len()
                    .saturating_add(registry.synthetic_methods),
            );
            let mut blocked = vec![false; inputs.contexts.len()];
            for key in &quota_blocked {
                blocked[key.context] = true;
                inputs.contexts[key.context].admission.retried_callers += 1;
                done.remove(key);
            }
            admission::redistribute_methods(&mut inputs.contexts, &blocked, remaining);
            final_round = true;
            roots = std::mem::take(&mut quota_blocked);
        } else {
            roots = dependencies;
        }
    }
    // Resolution may demand an intermediate class without finding a method
    // body there. Publish its verified hierarchy independently of the summary
    // queue, or an inherited call could lose the receiver's Leaf -> Mid -> Base
    // proof. Native relations never replace ordered Scala source parent facts.
    for (context_index, context) in inputs.contexts.iter_mut().enumerate() {
        context.phase = "hierarchy";
        context.active_method = SymbolId::NONE;
        context.active_file = FileId::NONE;
        context.pending_methods = 0;
        let mut loader = context_loader(context, &inputs.admitted)?;
        let mut initial: Vec<_> = context
            .classes
            .iter()
            .filter_map(|(owner, class)| {
                matches!(class, CachedClass::Found(_)).then_some(owner.clone())
            })
            .collect();
        initial.sort_unstable();
        let mut pending: VecDeque<_> = initial.into();
        let mut done = HashSet::new();
        while let Some(owner) = pending.pop_front() {
            if !done.insert(owner.clone()) {
                continue;
            }
            let Some(bytes) = cache_class(context, &mut loader, &owner)? else {
                continue;
            };
            let class = bytes.metadata.as_ref();
            let file = registry.file(facts, context_index, context.id, &owner, &bytes)?;
            let source = registry.class(facts, context_index, context.id, &owner, file, &bytes)?;
            // A source owner's ordered edges stay authoritative, but its
            // admitted JVM header still demands the ancestors' own metadata.
            // This traversal must not depend on generated member discovery.
            let source_owned = facts.symbols[source.index()].flags & SYMBOL_DEFINED != 0;
            for parent in class.parent().into_iter().chain(class.interfaces()) {
                let deferred_before = context.admission.deferred;
                let target = if let Some(bytes) =
                    guarded_hierarchy_class(facts, context, &mut loader, parent, source, file)?
                {
                    let file = registry.file(facts, context_index, context.id, parent, &bytes)?;
                    pending.push_back(parent.to_owned());
                    registry.class(facts, context_index, context.id, parent, file, &bytes)?
                } else if let Some(target) = registry.types.get(&(context_index, parent.to_owned()))
                {
                    if context.admission.deferred == deferred_before
                        && parent != "java/lang/Object"
                        && facts.symbols[target.index()].flags & SYMBOL_DEFINED == 0
                    {
                        add_issue(facts, source, file, IssueKind::IncompleteHierarchy);
                    }
                    *target
                } else if parent == "java/lang/Object" {
                    hierarchy::object_endpoint(facts, &mut registry, context_index, context.id)?
                } else {
                    if context.admission.deferred == deferred_before && parent != "java/lang/Object"
                    {
                        add_issue(facts, source, file, IssueKind::IncompleteHierarchy);
                    }
                    continue;
                };
                if !source_owned && parents.insert((source, target)) {
                    facts.relations.push(RelationRecord {
                        source,
                        target,
                        kind: RelationKind::Parent,
                        file,
                    });
                }
            }
        }
    }
    hierarchy::seal(facts, inputs, &registry, &parents);
    // Hierarchy admission can project a compiler namespace/type facet. Publish
    // callable frontiers only after those final symbol kinds/owners are known.
    generated_members.finish(facts, inputs, &mut registry, &existing)?;
    // Exact JVM descriptors and verified ancestry; each owner walks once.
    overrides::augment(facts, &registry);
    parameter_apply::augment(facts, &registry)?;
    generated_members::repair_dispatch(facts, &registry)?;
    source_modules::augment(
        facts,
        &registry,
        inputs,
        &source_module_candidates,
        &global_module_reads,
    )?;
    static_namespace::augment(facts, &registry, inputs)?;
    sequence::augment(facts, &registry, inputs)?;
    native_result_bounds::publish(facts, inputs, &registry)?;
    facts.identity =
        enriched_identity_with_limits(inputs.raw_identity, inputs.identity, facts, limits);
    facts.validate()?;
    Ok(())
}

#[cfg(test)]
#[path = "binary_parent_publication_tests.rs"]
mod parent_publication_tests;
// Class hashes remain the captured binary body/change provenance. The derived
// program identity additionally binds the actual lowered recipes, so a producer
// improvement cannot reuse an old prefix-only program with identical classes.
#[cfg(test)]
fn enriched_identity(raw: ContentHash, input: ContentHash, facts: &FactSnapshot) -> ContentHash {
    enriched_identity_with_limits(raw, input, facts, NativeAdmissionLimits::default())
}
fn enriched_identity_with_limits(
    raw: ContentHash,
    input: ContentHash,
    facts: &FactSnapshot,
    limits: NativeAdmissionLimits,
) -> ContentHash {
    let mut hash = Sha256::new();
    limits.hash(&mut hash);
    hash.update(b"binary-enriched-facts/2\0");
    hash.update(SelectionContract::VERSION);
    hash.update(SelectionContract::CURRENT_BASE_BITS.to_le_bytes());
    hash.update(raw.0);
    hash.update(input.0);
    hash.update(facts.revision.0.to_le_bytes());
    hash.update((facts.strings.bytes.len() as u64).to_le_bytes());
    hash.update(&facts.strings.bytes);
    hash.update((facts.strings.entries.len() as u64).to_le_bytes());
    for text in &facts.strings.entries {
        hash.update(text.start.to_le_bytes());
        hash.update(text.len.to_le_bytes());
    }
    hash.update((facts.files.len() as u64).to_le_bytes());
    for file in &facts.files {
        for word in [
            file.path.0,
            file.source.0,
            file.revision.0,
            file.context.0,
            file.flags,
        ] {
            hash.update(word.to_le_bytes());
        }
        hash.update(file.source_hash.0);
    }
    hash.update((facts.symbols.len() as u64).to_le_bytes());
    for symbol in &facts.symbols {
        for word in [
            symbol.name.0,
            symbol.display.0,
            symbol.owner.0,
            symbol.file.0,
            symbol.context.0,
            symbol.kind,
            symbol.signature.0,
            symbol.span.start,
            symbol.span.end,
            symbol.flags,
        ] {
            hash.update(word.to_le_bytes());
        }
        hash.update(symbol.properties.to_le_bytes());
    }
    hash.update((facts.occurrences.len() as u64).to_le_bytes());
    for occurrence in &facts.occurrences {
        for word in [
            occurrence.file.0,
            occurrence.symbol.0,
            occurrence.span.start,
            occurrence.span.end,
            occurrence.role,
            occurrence.ordinal,
        ] {
            hash.update(word.to_le_bytes());
        }
    }
    hash.update((facts.relations.len() as u64).to_le_bytes());
    for relation in &facts.relations {
        for word in [
            relation.source.0,
            relation.target.0,
            relation.kind as u32,
            relation.file.0,
        ] {
            hash.update(word.to_le_bytes());
        }
    }
    hash.update((facts.bodies.len() as u64).to_le_bytes());
    for body in &facts.bodies {
        hash.update(body.body_hash.0);
        for word in [
            body.symbol.0,
            body.file.0,
            body.flags,
            body.operations.start,
            body.operations.len,
            body.parameters.start,
            body.parameters.len,
            body.span.start,
            body.span.end,
            body.name_span.start,
            body.name_span.end,
        ] {
            hash.update(word.to_le_bytes());
        }
    }
    hash.update((facts.operations.len() as u64).to_le_bytes());
    for operation in &facts.operations {
        for word in [
            operation.body.0,
            operation.opcode as u32,
            operation.target.0,
            operation.dest.0,
            operation.a.0,
            operation.b.0,
            operation.flags,
            operation.arguments.start,
            operation.arguments.len,
            operation.span.start,
            operation.span.end,
        ] {
            hash.update(word.to_le_bytes());
        }
    }
    hash.update((facts.operands.len() as u64).to_le_bytes());
    for operand in &facts.operands {
        hash.update(operand.0.to_le_bytes());
    }
    hash.update((facts.result_bounds.len() as u64).to_le_bytes());
    for bound in &facts.result_bounds {
        for word in [
            bound.symbol.0,
            bound.operation.0,
            bound.classes.start,
            bound.classes.len,
        ] {
            hash.update(word.to_le_bytes());
        }
    }
    hash.update((facts.bound_classes.len() as u64).to_le_bytes());
    for class in &facts.bound_classes {
        hash.update(class.0.to_le_bytes());
    }
    hash.update((facts.suites.len() as u64).to_le_bytes());
    for suite in &facts.suites {
        for word in [suite.name.0, suite.symbol.0, suite.file.0, suite.flags] {
            hash.update(word.to_le_bytes());
        }
    }
    hash.update((facts.issues.len() as u64).to_le_bytes());
    for issue in &facts.issues {
        for word in [
            issue.kind as u32,
            issue.file.0,
            issue.symbol.0,
            issue.detail.0,
        ] {
            hash.update(word.to_le_bytes());
        }
    }
    ContentHash(hash.finalize().into())
}
fn recipe_flags(jvm_name: &str, receiver_parameter: Option<u16>, compiler_kind: u32) -> u32 {
    let mut flags = BODY_BINARY_RECIPE;
    if jvm_name == "<clinit>" {
        flags |= BODY_STATIC_INITIALIZER | BODY_INITIALIZER;
    } else if (jvm_name == "$init$" && receiver_parameter.is_some())
        || (jvm_name == "<init>" && compiler_kind == 10)
    {
        // A JVM constructor explicitly bound to the compiler object symbol is
        // that object's instance initializer. Ordinary constructor overloads
        // keep callable entry identities and never become owner-wide fanout.
        flags |= BODY_INITIALIZER;
    }
    flags
}

fn admit_header_authority(record: &mut SymbolRecord, nominal: bool, jvm_flags: u16) {
    if record.flags & SYMBOL_DEFINED != 0 {
        return;
    }
    let native_class = record.flags & SYMBOL_NATIVE_BINARY != 0 && matches!(record.kind, 13 | 14);
    if !nominal && !native_class {
        return;
    }
    let kind = if jvm_flags & 0x0200 != 0 { 14 } else { 13 };
    if record.kind == 0 || native_class {
        record.kind = kind;
    }
    if record.kind == kind {
        record.flags |= SYMBOL_JVM_CLASS_HEADER_VERIFIED;
        // JVM ACC_FINAL certifies that a native result bound has no runtime
        // subclasses. Source definitions retain their compiler properties.
        if kind == 13 && jvm_flags & 0x0010 != 0 {
            record.properties |= 8;
        }
    }
}

#[cfg(test)]
mod entry_tests {
    use super::*;
    #[test]
    fn exact_native_final_header_projects_finality_without_rewriting_source_properties() {
        let bytes = include_bytes!("../../../fixtures/jdk-primitive-models/java/lang/String.class");
        let class = binary::parse_class(bytes, Limits::default()).unwrap();
        assert_eq!(class.name, "java/lang/String");
        assert_ne!(class.flags & 0x0010, 0);
        let mut builder = FactBuilder::new();
        let symbol = builder
            .ensure_symbol("java/lang/String#", FileId::NONE)
            .unwrap();
        let original = builder.facts.symbols[symbol.index()];
        let mut record = original;
        admit_header_authority(&mut record, true, class.flags);
        assert_eq!(record.kind, 13);
        assert_ne!(record.flags & SYMBOL_JVM_CLASS_HEADER_VERIFIED, 0);
        assert_ne!(record.properties & 8, 0);
        for (nominal, flags, defined) in [
            (true, class.flags & !0x0010, false),
            (false, class.flags, false),
            (true, class.flags, true),
        ] {
            let mut record = original;
            if defined {
                record.flags = SYMBOL_DEFINED;
            }
            admit_header_authority(&mut record, nominal, flags);
            assert_eq!(
                record.properties & 8,
                0,
                "source or unsupported header must not gain finality"
            );
        }
    }
    #[test]
    fn no_platform_keeps_the_original_native_input_hash_domain_and_bytes() {
        let mut builder = FactBuilder::new();
        let context = builder.intern("legacy-context").unwrap();
        builder
            .ensure_global_symbol("legacy/Caller#", context)
            .unwrap();
        let facts = builder.finish().unwrap();
        let bytes = serde_json::to_vec(&serde_json::json!({
            "version":1,"facts_identity":facts.identity.to_string(),
            "contexts":[{"id":"legacy-context","entries":[]}],"methods":[]
        }))
        .unwrap();
        let temporary = tempfile::tempdir().unwrap();
        let path = temporary.path().join("binary.json");
        std::fs::write(&path, &bytes).unwrap();
        let mut hash = Sha256::new();
        hash.update(b"binary-input-manifest/2");
        hash.update(&bytes);
        let previous = ContentHash(hash.finalize().into());
        let legacy = load_binary_manifest(&path, &facts).unwrap();
        let explicit_none =
            load_binary_manifest_with_platform(&path, &facts, &BinaryInputOptions::default(), None)
                .unwrap();
        assert_eq!(legacy.identity, previous);
        assert_eq!(explicit_none.identity, previous);
        assert!(legacy.platform_input_files().is_empty());
        assert!(legacy.platform_contexts.is_empty());
    }
    #[test]
    fn derived_metadata_hierarchy_and_bounds_are_part_of_enriched_identity() {
        let mut builder = FactBuilder::new();
        let symbol = builder.ensure_symbol("p/A#", FileId::NONE).unwrap();
        let mut facts = builder.finish().unwrap();
        let raw = ContentHash([1; 32]);
        let input = ContentHash([2; 32]);
        let mut prior = enriched_identity(raw, input, &facts);
        facts.symbols[symbol.index()].flags |= SYMBOL_JVM_CLASS_HEADER_VERIFIED;
        let next = enriched_identity(raw, input, &facts);
        assert_ne!(prior, next);
        prior = next;
        facts.relations.push(RelationRecord {
            source: symbol,
            target: symbol,
            kind: RelationKind::Override,
            file: FileId::NONE,
        });
        let next = enriched_identity(raw, input, &facts);
        assert_ne!(prior, next);
        prior = next;
        facts.result_bounds.push(ResultBoundRecord {
            symbol,
            operation: OperationId::NONE,
            classes: IdRange { start: 0, len: 1 },
        });
        facts.bound_classes.push(symbol);
        let next = enriched_identity(raw, input, &facts);
        assert_ne!(prior, next);
        prior = next;
        facts.issues.push(IssueRecord {
            kind: IssueKind::UnknownExecution,
            file: FileId::NONE,
            symbol,
            detail: StrId::NONE,
        });
        assert_ne!(prior, enriched_identity(raw, input, &facts));
    }
    #[test]
    fn identical_class_hashes_do_not_hide_lowered_recipe_changes() {
        let mut facts = FactSnapshot::default();
        facts.operations.push(OperationRecord {
            body: BodyId(0),
            opcode: Opcode::Unknown,
            target: SymbolId::NONE,
            dest: ValueId(1),
            a: ValueId::NONE,
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span::default(),
            flags: 0,
        });
        facts.bodies.push(BodyRecord {
            symbol: SymbolId(0),
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange { start: 0, len: 1 },
            parameters: IdRange::default(),
            body_hash: ContentHash([17; 32]),
            flags: BODY_BINARY_RECIPE,
        });
        let raw = ContentHash([1; 32]);
        let input = ContentHash([2; 32]);
        let prefix = enriched_identity(raw, input, &facts);
        facts.operations[0].opcode = Opcode::Assign;
        let complete_data = enriched_identity(raw, input, &facts);
        assert_ne!(prefix, complete_data);
        assert_eq!(facts.bodies[0].body_hash, ContentHash([17; 32]));
        assert_eq!(complete_data, enriched_identity(raw, input, &facts));
        facts.operations[0].a = ValueId(0);
        assert_ne!(complete_data, enriched_identity(raw, input, &facts));
    }
    #[test]
    fn exact_object_constructor_mapping_is_an_initializer_without_promoting_class_overloads() {
        assert_eq!(
            recipe_flags("<init>", None, 10),
            BODY_BINARY_RECIPE | BODY_INITIALIZER
        );
        for kind in [0, 3, 13, 14, 21] {
            assert_eq!(recipe_flags("<init>", None, kind), BODY_BINARY_RECIPE);
        }
        assert_eq!(
            recipe_flags("$init$", Some(0), 14),
            BODY_BINARY_RECIPE | BODY_INITIALIZER
        );
        assert_eq!(recipe_flags("$init$", None, 3), BODY_BINARY_RECIPE);
        assert_eq!(
            recipe_flags("<clinit>", None, 3),
            BODY_BINARY_RECIPE | BODY_INITIALIZER | BODY_STATIC_INITIALIZER
        );
    }
}
