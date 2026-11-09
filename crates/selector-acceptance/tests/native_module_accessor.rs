//! Existing genuine caller-only capture plus separately admitted Scala signatures.
//! Native admission additionally sees the pinned emitted caller product; that
//! explicit output view is distinct from the original metadata-provider classpath.
use selector_extract::external_metadata::{
    ExternalMetadataLimits, MetadataProviderAuthority, MetadataRequestLimits, ProviderResolution,
    admit,
};
use selector_extract::{ExtractOptions, finish_capture, prepare_capture};
use selector_facts::FactSnapshot;
use selector_models::binary::{CapturedClasspath, ClassLookup, ClasspathEntry, EntryKind, Limits};
use selector_types::*;
use serde_json::{Value, json};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

const CONTEXT: &str = "project:external-metadata/configuration:test";
const MODULE: &str = "selectedexternal/Configuration#PatienceConfig.";
const APPLY: &str = "selectedexternal/Configuration#PatienceConfig.apply(+1).";
const CALLS: &str = "selectedexternal/Calls#";
fn directory() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/external-metadata")
}
fn read_json(path: &Path) -> Value {
    serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap()
}
fn manifest() -> Value {
    read_json(&directory().join("manifest.json"))
}
fn hash(value: &Value) -> ContentHash {
    ContentHash::from_hex(value.as_str().unwrap()).unwrap()
}
fn options() -> ExtractOptions {
    ExtractOptions {
        workers: 2,
        compiler_contexts: Some(directory().join("compiler-contexts.json")),
        ..Default::default()
    }
}
fn prepared() -> selector_extract::PreparedCapture {
    prepare_capture(
        &directory().join("documents.jsonl"),
        Some(&directory().join("syntax.jsonl")),
        &options(),
    )
    .unwrap()
}
struct Authority {
    identity: ContentHash,
    contexts: ContentHash,
    classpath_identity: ContentHash,
    classpath: Mutex<CapturedClasspath>,
}
impl Authority {
    fn new() -> Self {
        let manifest = manifest();
        let entries = manifest["ordered_actual_compiler_classpath"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| ClasspathEntry {
                path: PathBuf::from(row["path"].as_str().unwrap()),
                sha256: hash(&row["sha256"]),
                kind: EntryKind::Jar,
            })
            .collect();
        Self {
            identity: hash(&manifest["authority_sha256"]),
            contexts: hash(&manifest["context_manifest_sha256"]),
            classpath_identity: hash(&manifest["classpath_sha256"]),
            classpath: Mutex::new(
                CapturedClasspath::new(entries, Limits::default())
                    .unwrap()
                    .with_java_feature(Some(21))
                    .unwrap(),
            ),
        }
    }
}
impl MetadataProviderAuthority for Authority {
    fn identity(&self) -> ContentHash {
        self.identity
    }
    fn contexts_identity(&self) -> ContentHash {
        self.contexts
    }
    fn resolve(
        &self,
        context: &str,
        outer_class: &str,
    ) -> Result<Option<ProviderResolution>, Error> {
        if context != CONTEXT {
            return Ok(None);
        }
        let mut classpath = self.classpath.lock().unwrap();
        let found = match classpath
            .lookup(outer_class)
            .map_err(|error| Error::Message(error.to_string()))?
        {
            ClassLookup::Found(found) => found,
            ClassLookup::Absent(_) => return Ok(None),
        };
        let provider_index = found.proof.selected_entry.unwrap();
        Ok(Some(ProviderResolution {
            classpath_identity: self.classpath_identity,
            provider_index: provider_index as u32,
            provider_sha256: classpath.entries[provider_index].sha256,
            class_bytes: Arc::from(found.bytes),
        }))
    }
}
fn metadata(
    prepared: &selector_extract::PreparedCapture,
) -> Arc<selector_extract::external_metadata::AdmittedExternalMetadata> {
    let requests = prepared
        .metadata_requests(&MetadataRequestLimits::default())
        .unwrap();
    assert_eq!(
        requests.contexts_identity(),
        Some(hash(&manifest()["context_manifest_sha256"]))
    );
    for root in read_json(&directory().join("admission.json"))["bindings"][0]["roots"]
        .as_array()
        .unwrap()
    {
        assert!(
            requests
                .iter()
                .any(|request| request.context == CONTEXT
                    && request.symbol == root.as_str().unwrap())
        );
    }
    Arc::new(
        admit(
            &directory().join("admission.json"),
            &requests,
            &Authority::new(),
            hash(&manifest()["producer_sha256"]),
            &ExternalMetadataLimits::default(),
        )
        .unwrap(),
    )
}
fn enhanced() -> FactSnapshot {
    let owner = prepared();
    let admitted = metadata(&owner);
    finish_capture(owner, Some(admitted)).unwrap()
}

fn source_operation(facts: &FactSnapshot) -> (usize, selector_facts::OperationRecord) {
    let method = facts
        .find_symbol("selectedexternal/Calls#inherited().")
        .unwrap();
    let rows: Vec<_> = facts
        .operations
        .iter()
        .copied()
        .enumerate()
        .filter(|(_, op)| {
            facts.bodies[op.body.index()].symbol == method
                && !op.target.is_none()
                && facts.symbol_name(op.target) == MODULE
        })
        .collect();
    assert_eq!(
        rows.len(),
        1,
        "one actual compiler-owned companion receiver"
    );
    rows[0]
}
fn native_view(facts: &FactSnapshot, temporary: &Path) -> PathBuf {
    let pinned = manifest();
    let caller = directory().join("caller.jar");
    let expected = pinned["files"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["path"] == "caller.jar")
        .unwrap();
    let mut entries = vec![json!({"index":0,"path":caller,
        "sha256":expected["sha256"],"project_output_origins":[{"context_id":CONTEXT}]})];
    let mut objects = vec![json!({"path":caller,"kind":"file",
        "sha256":expected["sha256"],"bytes":expected["bytes"]})];
    for row in pinned["ordered_actual_compiler_classpath"]
        .as_array()
        .unwrap()
    {
        let path = PathBuf::from(row["path"].as_str().unwrap());
        entries.push(json!({"index":entries.len(),"path":path,"sha256":row["sha256"]}));
        objects.push(json!({"path":path,"kind":"file","sha256":row["sha256"],
            "bytes":std::fs::metadata(&path).unwrap().len()}));
    }
    let view = temporary.join("native-output-view.json");
    std::fs::write(
        &view,
        serde_json::to_vec(&json!({
            "schema_version":"sbt-compiler-context/v1",
            "capture_kind":"checked_fixture_native_view_with_exact_emitted_product",
            "revision":facts.text(facts.revision),"source_root":directory(),"errors":[],
            "contexts":[{"context_id":CONTEXT,"full_classpath":entries,
                "exported_products":[{"path":caller,"sha256":expected["sha256"]}]}],
            "input_objects":objects
        }))
        .unwrap(),
    )
    .unwrap();
    view
}
fn enriched(
    metadata: bool,
    unavailable_prefix: bool,
) -> (FactSnapshot, FactSnapshot, FactSnapshot, Value) {
    let mut original = if metadata {
        enhanced()
    } else {
        finish_capture(prepared(), None).unwrap()
    };
    let temporary = tempfile::tempdir().unwrap();
    let saved = temporary.path().join("source-facts.bin");
    original.identity = selector_facts::codec::write(&saved, &original).unwrap();
    let mut facts = selector_facts::codec::read(&saved).unwrap();
    let view = native_view(&original, temporary.path());
    if unavailable_prefix {
        // Deliberate normalized authority-negative: an unavailable earlier
        // provider blocks lookup. It is not claimed as the original compiler CP.
        let mut input = read_json(&view);
        let opaque = temporary.path().join("unavailable-earlier.jar");
        let digest = ContentHash([1; 32]).to_string();
        let entries = input["contexts"][0]["full_classpath"]
            .as_array_mut()
            .unwrap();
        entries.insert(0, json!({"path":opaque,"sha256":digest}));
        for (index, row) in entries.iter_mut().enumerate() {
            row["index"] = json!(index);
        }
        input["input_objects"].as_array_mut().unwrap().push(json!({
            "path":opaque,"kind":"unavailable","sha256":digest,"bytes":0}));
        std::fs::write(&view, serde_json::to_vec(&input).unwrap()).unwrap();
    }

    let generated = selector_graph_build::binary_capture::generate(
        &original,
        &view,
        &directory(),
        &selector_graph_build::binary_capture::CaptureOptions {
            workers: 2,
            ..Default::default()
        },
    )
    .unwrap();
    let mapping = temporary.path().join("binary.json");
    std::fs::write(&mapping, serde_json::to_vec(&generated.manifest).unwrap()).unwrap();
    let mut inputs =
        selector_graph_build::binary_inputs::load_binary_manifest(&mapping, &facts).unwrap();
    selector_graph_build::binary_inputs::augment_binary_facts(&mut facts, &mut inputs).unwrap();
    // Matched ordinary-enrichment control: preserve every runtime-class mapping
    // and existing method root, removing only the newly synthesized accessor
    // demand. This isolates the callable endpoint from the old class facet.
    let mut ordinary_manifest = generated.manifest.clone();
    ordinary_manifest["methods"]
        .as_array_mut()
        .unwrap()
        .retain(|row| {
            !(row["jvm_owner"] == "selectedexternal/Configuration"
                && row["jvm_name"] == "PatienceConfig"
                && row["descriptor"] == "()Lselectedexternal/Configuration$PatienceConfig$;")
        });
    let ordinary_path = temporary.path().join("ordinary-binary.json");
    std::fs::write(
        &ordinary_path,
        serde_json::to_vec(&ordinary_manifest).unwrap(),
    )
    .unwrap();
    let mut ordinary = selector_facts::codec::read(&saved).unwrap();
    let mut ordinary_inputs =
        selector_graph_build::binary_inputs::load_binary_manifest(&ordinary_path, &ordinary)
            .unwrap();
    selector_graph_build::binary_inputs::augment_binary_facts(&mut ordinary, &mut ordinary_inputs)
        .unwrap();
    (original, facts, ordinary, generated.manifest)
}

#[test]
fn genuine_inherited_companion_load_uses_the_exact_native_getter_without_globalizing_its_receiver()
{
    let (before, after, ordinary, mappings) = enriched(true, false);
    let module = before.find_symbol(MODULE).unwrap();
    assert_eq!(before.symbols[module.index()].kind, 0);
    assert_eq!(before.symbols[module.index()].flags & SYMBOL_DEFINED, 0);
    let (index, source) = source_operation(&before);
    assert_eq!(source.opcode, Opcode::LoadField);
    assert_eq!(source.a, ValueId(0));
    let rewritten = after.operations[index];
    assert_eq!(
        rewritten.opcode,
        Opcode::VirtualCall,
        "module before={:?}, after={:?}; admitted method states={:?}",
        before.symbols[module.index()],
        after.symbols[module.index()],
        after
            .symbols
            .iter()
            .enumerate()
            .filter(|(_, symbol)| symbol.owner == module)
            .map(|(i, symbol)| (
                after.symbol_name(SymbolId(i as u32)),
                symbol.kind,
                symbol.file,
                symbol.flags,
                !symbol.signature.is_none()
            ))
            .collect::<Vec<_>>()
    );
    assert_eq!(
        rewritten.a, source.a,
        "the getter receives the actual enclosing instance"
    );
    assert_eq!(rewritten.dest, source.dest);
    assert_eq!(rewritten.span, source.span);
    assert_eq!(rewritten.body, source.body);
    assert_eq!(rewritten.arguments.len, 0);
    assert_eq!(
        after.symbols[module.index()].kind,
        ordinary.symbols[module.index()].kind,
        "the accessor must preserve the pre-existing runtime-class facet projection"
    );
    assert_eq!(
        after.symbols[module.index()].properties,
        ordinary.symbols[module.index()].properties,
        "the pre-existing class-facet properties are unchanged"
    );
    let getter = rewritten.target;
    assert_ne!(
        getter, module,
        "a callable accessor needs its own native endpoint"
    );
    assert!(after.symbol_name(getter).starts_with("@jvm/"));
    assert!(
        mappings["methods"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| row["jvm_owner"] == "selectedexternal/Configuration"
                && row["jvm_name"] == "PatienceConfig"
                && row["descriptor"] == "()Lselectedexternal/Configuration$PatienceConfig$;"
                && row.get("compiler_symbol").is_none_or(Value::is_null))
    );
    let concrete: Vec<_> = after
        .relations
        .iter()
        .filter(|relation| relation.kind == RelationKind::Override && relation.target == getter)
        .map(|relation| relation.source)
        .collect();
    let owner = after.find_symbol(CALLS).unwrap();
    let implementation = concrete
        .into_iter()
        .find(|symbol| after.symbols[symbol.index()].owner == owner)
        .expect("the exact emitted Calls getter implements its inherited native contract");
    let body = after
        .bodies
        .iter()
        .find(|body| body.symbol == implementation)
        .unwrap();
    assert_ne!(body.flags & BODY_BINARY_RECIPE, 0);
    let loads: Vec<_> = after.operations[body.operations.range()]
        .iter()
        .filter(|op| {
            op.opcode == Opcode::LoadField
                && !op.target.is_none()
                && after.symbols[op.target.index()].owner == owner
        })
        .collect();
    assert!(
        !loads.is_empty(),
        "the real lazy accessor retains its receiver backing-field read"
    );
    assert!(
        loads.iter().all(|op| !op.a.is_none()),
        "never replace per-instance storage with a global module"
    );
    let fields: Vec<_> = loads.iter().map(|op| op.target).collect();
    assert!(
        after
            .operations
            .iter()
            .any(|op| op.opcode == Opcode::StoreField && fields.contains(&op.target)),
        "the actual lazy computation's backing-field write is retained"
    );
    let lazy = after
        .bodies
        .iter()
        .find(|body| {
            after
                .symbol_name(body.symbol)
                .contains("PatienceConfig$lzycompute$1")
                && after.symbols[body.symbol.index()].owner == owner
        })
        .expect(
            "the actual lazy-compute body is admitted, rather than replaced by a pure getter model",
        );
    assert!(
        after.operations[lazy.operations.range()]
            .iter()
            .any(|op| op.opcode == Opcode::StoreField && fields.contains(&op.target)),
        "the same receiver backing field is written by its real lazy-compute body"
    );
    assert!(
        after.operations[lazy.operations.range()]
            .iter()
            .any(|op| op.opcode == Opcode::Unknown)
            || after
                .issues
                .iter()
                .any(|issue| issue.symbol == lazy.symbol
                    && issue.kind == IssueKind::UnknownExecution),
        "the genuine monitor/native-effect uncertainty must survive accessor recovery"
    );
    let apply = after.find_symbol(APPLY).unwrap();
    let method = before
        .find_symbol("selectedexternal/Calls#inherited().")
        .unwrap();
    let selected = after
        .operations
        .iter()
        .find(|op| {
            after.bodies[op.body.index()].symbol == method
                && matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
                && op.target == apply
        })
        .unwrap();
    assert_eq!(
        selected.a, rewritten.dest,
        "selected apply consumes the exact getter result"
    );
    assert_eq!(
        std::fs::read_to_string(directory().join("jvm-inherited.stdout")).unwrap(),
        "inherited:interval,timeout:1:2\n"
    );
}

#[test]
fn absent_external_scala_method_witness_does_not_turn_an_untyped_field_into_a_module_call() {
    let (before, after, _, _) = enriched(false, false);
    let (index, source) = source_operation(&before);
    assert_eq!(source.opcode, Opcode::LoadField);
    let unchanged = after.operations[index];
    assert_eq!(
        (
            unchanged.opcode,
            unchanged.target,
            unchanged.dest,
            unchanged.a,
            unchanged.b,
            unchanged.arguments,
            unchanged.span,
            unchanged.body,
            unchanged.flags
        ),
        (
            source.opcode,
            source.target,
            source.dest,
            source.a,
            source.b,
            source.arguments,
            source.span,
            source.body,
            source.flags
        )
    );
    assert!(
        before
            .issues
            .iter()
            .any(|issue| issue.kind == IssueKind::UnknownExecution
                && before.text(issue.detail).contains("argument signature")),
        "the missing compiler contract remains explicit"
    );
}

#[test]
fn unavailable_earlier_provider_blocks_the_real_module_getter_even_with_admitted_signatures() {
    let (before, after, _, mappings) = enriched(true, true);
    assert!(
        !mappings["methods"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| row["jvm_owner"] == "selectedexternal/Configuration"
                && row["jvm_name"] == "PatienceConfig")
    );
    assert_eq!(mappings["contexts"][0]["entries"][0]["kind"], "unavailable");
    let (index, source) = source_operation(&before);
    assert_eq!(
        format!("{:?}", after.operations[index]),
        format!("{source:?}"),
        "exact metadata cannot bypass an opaque earlier provider or authorize a getter on its own"
    );
}
