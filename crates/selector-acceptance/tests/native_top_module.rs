//! Signature-only compiler metadata plus genuine class bytes. The adapter is
//! explicit synthetic execution, never a purity contract for a Scala object.
use selector_extract::external_metadata::{
    ExternalMetadataLimits, MetadataProviderAuthority, MetadataRequestLimits, ProviderResolution,
    admit,
};
use selector_extract::{ExtractOptions, finish_capture, prepare_capture};
use selector_facts::FactSnapshot;
use selector_models::binary::{CapturedClasspath, ClassLookup, ClasspathEntry, EntryKind, Limits};
use selector_solve::{ExecutionRoot, QuerySession, SolveOptions, SolverRuntime};
use selector_types::*;
use serde_json::{Value, json};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

const CONTEXT: &str = "project:external-metadata/configuration:test";
const MODULE: &str = "selectedexternal/Effects.";
const NOTE: &str = "selectedexternal/Effects.note().";
fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/top-module-metadata")
}
fn caller() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/external-metadata")
}
fn json(path: &Path) -> Value {
    serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap()
}
fn hash(v: &Value) -> ContentHash {
    ContentHash::from_hex(v.as_str().unwrap()).unwrap()
}
struct Authority {
    manifest: Value,
    classpath: Mutex<CapturedClasspath>,
}
impl Authority {
    fn new() -> Self {
        let manifest = json(&fixture().join("manifest.json"));
        let contexts = json(&fixture().join("native-contexts.json"));
        let entries = contexts["contexts"][0]["full_classpath"]
            .as_array()
            .unwrap()
            .iter()
            .map(|entry| ClasspathEntry {
                path: PathBuf::from(entry["path"].as_str().unwrap()),
                sha256: hash(&entry["sha256"]),
                kind: EntryKind::Jar,
            })
            .collect();
        Self {
            manifest,
            classpath: Mutex::new(CapturedClasspath::new(entries, Limits::default()).unwrap()),
        }
    }
}
impl MetadataProviderAuthority for Authority {
    fn identity(&self) -> ContentHash {
        hash(&self.manifest["authority_sha256"])
    }
    fn contexts_identity(&self) -> ContentHash {
        hash(&self.manifest["contexts_sha256"])
    }
    fn resolve(
        &self,
        context: &str,
        outer_class: &str,
    ) -> Result<Option<ProviderResolution>, Error> {
        if context != CONTEXT {
            return Ok(None);
        }
        let mut cp = self.classpath.lock().unwrap();
        let found = match cp
            .lookup(outer_class)
            .map_err(|e| Error::Message(e.to_string()))?
        {
            ClassLookup::Found(found) => found,
            ClassLookup::Absent(_) => return Ok(None),
        };
        let index = found.proof.selected_entry.unwrap();
        Ok(Some(ProviderResolution {
            classpath_identity: hash(
                &self.manifest["bindings"][0]["projections"][0]["classpath_sha256"],
            ),
            provider_index: index as u32,
            provider_sha256: cp.entries[index].sha256,
            class_bytes: Arc::from(found.bytes),
        }))
    }
}
fn source(with_metadata: bool) -> FactSnapshot {
    let prepared = prepare_capture(
        &caller().join("documents.jsonl"),
        Some(&caller().join("syntax.jsonl")),
        &ExtractOptions {
            workers: 1,
            compiler_contexts: Some(fixture().join("native-contexts.json")),
            ..Default::default()
        },
    )
    .unwrap();
    let admitted = if with_metadata {
        let requests = prepared
            .metadata_requests(&MetadataRequestLimits::default())
            .unwrap();
        assert!(
            requests
                .iter()
                .any(|r| r.context == CONTEXT && r.symbol == NOTE)
        );
        let manifest = json(&fixture().join("manifest.json"));
        Some(Arc::new(
            admit(
                &fixture().join("manifest.json"),
                &requests,
                &Authority::new(),
                hash(&manifest["producer_sha256"]),
                &ExternalMetadataLimits::default(),
            )
            .unwrap(),
        ))
    } else {
        None
    };
    finish_capture(prepared, admitted).unwrap()
}
fn enrich(with_metadata: bool, unavailable_prefix: bool) -> (FactSnapshot, FactSnapshot) {
    let mut before = source(with_metadata);
    let temporary = tempfile::tempdir().unwrap();
    let saved = temporary.path().join("source.bin");
    before.identity = selector_facts::codec::write(&saved, &before).unwrap();
    let mut after = selector_facts::codec::read(&saved).unwrap();
    let view = temporary.path().join("contexts.json");
    let mut contexts = json(&fixture().join("native-contexts.json"));
    if unavailable_prefix {
        // Deliberate normalized negative, not a claim about the compiler's CP.
        let path = temporary.path().join("unavailable-earlier.jar");
        let digest = ContentHash([1; 32]).to_string();
        let entries = contexts["contexts"][0]["full_classpath"]
            .as_array_mut()
            .unwrap();
        entries.insert(0, json!({"path":path,"sha256":digest}));
        for (index, entry) in entries.iter_mut().enumerate() {
            entry["index"] = json!(index);
        }
        contexts["input_objects"]
            .as_array_mut()
            .unwrap()
            .push(json!({
            "path":path,"kind":"unavailable","sha256":digest,"bytes":0}));
    }
    std::fs::write(&view, serde_json::to_vec(&contexts).unwrap()).unwrap();
    let generated = selector_graph_build::binary_capture::generate(
        &before,
        &view,
        &caller(),
        &selector_graph_build::binary_capture::CaptureOptions {
            workers: 2,
            ..Default::default()
        },
    )
    .unwrap();
    let mapping = temporary.path().join("binary.json");
    std::fs::write(&mapping, serde_json::to_vec(&generated.manifest).unwrap()).unwrap();
    let mut inputs =
        selector_graph_build::binary_inputs::load_binary_manifest(&mapping, &after).unwrap();
    selector_graph_build::binary_inputs::augment_binary_facts(&mut after, &mut inputs).unwrap();
    (before, after)
}
fn source_read(facts: &FactSnapshot) -> (usize, selector_facts::OperationRecord) {
    let method = facts
        .find_symbol("selectedexternal/Calls#interval().")
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
    assert_eq!(rows.len(), 1);
    rows[0]
}
fn adapter<'a>(facts: &'a FactSnapshot, symbol: SymbolId) -> &'a [selector_facts::OperationRecord] {
    let body = facts.bodies.iter().find(|b| b.symbol == symbol).unwrap();
    assert_eq!(body.flags & BODY_BINARY_RECIPE, BODY_BINARY_RECIPE);
    assert_ne!(
        facts.files[body.file.index()].source_hash,
        ContentHash::default()
    );
    &facts.operations[body.operations.range()]
}

#[test]
fn genuine_global_module_read_retains_normal_initialization_and_the_real_static_slot() {
    let (before, after) = enrich(true, false);
    let (index, read) = source_read(&before);
    assert_eq!(read.opcode, Opcode::LoadField);
    let call = after.operations[index];
    assert_eq!(call.opcode, Opcode::Call);
    assert!(
        after
            .symbol_name(call.target)
            .starts_with("@jvm-module-read/")
    );
    assert_ne!(call.target, read.target);
    assert_eq!(
        (
            call.a,
            call.dest,
            call.span,
            call.body,
            call.arguments,
            call.flags
        ),
        (
            read.a,
            read.dest,
            read.span,
            read.body,
            read.arguments,
            read.flags
        )
    );
    let operations = adapter(&after, call.target);
    assert_eq!(operations.len(), 3);
    assert_eq!(operations[0].opcode, Opcode::Initialize);
    assert!(
        after
            .symbol_name(operations[0].target)
            .contains("class-init")
    );
    assert_eq!(operations[1].opcode, Opcode::LoadField);
    assert_eq!(operations[1].flags, OP_STATIC_FIELD);
    assert!(operations[1].a.is_none());
    assert!(after.symbol_name(operations[1].target).contains("MODULE$"));
    assert_eq!(operations[2].opcode, Opcode::Return);
    assert_eq!(operations[2].a, operations[1].dest);
    let module = after.symbols[operations[1].target.index()].owner;
    assert!(
        after
            .operations
            .iter()
            .any(|op| op.opcode == Opcode::StoreField && op.target == operations[1].target),
        "actual MODULE$ publication remains"
    );
    assert!(
        after
            .operations
            .iter()
            .any(|op| op.opcode == Opcode::StoreField
                && !op.target.is_none()
                && after.symbols[op.target.index()].owner == module
                && after.symbol_name(op.target).contains("trace")),
        "actual object-constructor effects remain"
    );
    let note = after.find_symbol(NOTE).unwrap();
    let source_body = &after.bodies[read.body.index()];
    assert!(
        after.operations[source_body.operations.range()]
            .iter()
            .any(|op| matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
                && op.target == note
                && op.a == call.dest)
    );
    assert_eq!(
        std::fs::read_to_string(caller().join("jvm-inherited.stdout")).unwrap(),
        "inherited:interval,timeout:1:2\n"
    );
}

#[test]
fn module_adapter_is_executed_by_the_active_provider_but_not_dormant_closure_creation() {
    let (before, mut facts) = enrich(true, false);
    let (index, _) = source_read(&before);
    let temporary = tempfile::tempdir().unwrap();
    facts.identity =
        selector_facts::codec::write(&temporary.path().join("facts.bin"), &facts).unwrap();
    let graph = selector_graph_build::build(&facts, &Default::default()).unwrap();
    let active = graph
        .node_for_symbol(
            facts
                .find_symbol("selectedexternal/Calls#interval().")
                .unwrap(),
        )
        .unwrap();
    let dormant = graph
        .node_for_symbol(
            facts
                .find_symbol("selectedexternal/Calls#dormant().")
                .unwrap(),
        )
        .unwrap();
    let receiver = facts.find_symbol("selectedexternal/Calls#").unwrap();
    let seed = graph
        .node_for_symbol(facts.operations[index].target)
        .unwrap();
    let options = SolveOptions {
        workers: 1,
        max_contexts: 10_000,
        max_steps: 1_000_000,
        memory_budget_bytes: 64 * 1024 * 1024,
        execution_roots: Some(
            vec![
                ExecutionRoot {
                    node: active,
                    receiver,
                },
                ExecutionRoot {
                    node: dormant,
                    receiver,
                },
            ]
            .into(),
        ),
        ..Default::default()
    };
    let runtime = SolverRuntime::new(&options).unwrap();
    let mut session = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
    let result = session.analyze(&[seed]).unwrap();
    assert_ne!(result.completion, Completion::ResourceLimited);
    assert!(result.affected.contains(&active));
    assert!(!result.affected.contains(&dormant));
    assert_eq!(
        std::fs::read_to_string(caller().join("jvm-dormant.stdout")).unwrap(),
        "dormant:\n"
    );
}

#[test]
fn missing_compiler_witness_does_not_globalize_an_untyped_source_read() {
    let (before, after) = enrich(false, false);
    let (index, read) = source_read(&before);
    assert_eq!(read.opcode, Opcode::LoadField);
    assert_eq!(
        format!("{:?}", after.operations[index]),
        format!("{read:?}")
    );
    assert!(
        !after
            .symbols
            .iter()
            .any(|s| after.text(s.name).starts_with("@jvm-module-read/"))
    );
}

#[test]
fn unavailable_earlier_provider_blocks_top_level_read_recovery() {
    let (before, after) = enrich(true, true);
    let (index, read) = source_read(&before);
    assert_eq!(
        format!("{:?}", after.operations[index]),
        format!("{read:?}")
    );
    assert!(
        !after
            .symbols
            .iter()
            .any(|s| after.text(s.name).starts_with("@jvm-module-read/"))
    );
}
