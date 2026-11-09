//! Genuine compiler OBJECT header admission is separate from executable authority.
//! All malformed variants below are explicitly labeled wire/manifest perturbations.
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
const MODULE: &str = "selectedexternal/Effects.";
const NOTE: &str = "selectedexternal/Effects.note().";
fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/external-module-header")
}
fn contexts_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../fixtures/top-module-metadata/native-contexts.json")
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
        let contexts = json(&contexts_path());
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
                &self.manifest["module_headers"][0]["projections"][0]["classpath_sha256"],
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
            compiler_contexts: Some(contexts_path()),
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
                .any(|r| r.context == CONTEXT && r.symbol == MODULE)
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
    let mut contexts = json(&contexts_path());
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
                && matches!(op.opcode, Opcode::LoadField | Opcode::Allocate)
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

fn prepared() -> selector_extract::PreparedCapture {
    prepare_capture(
        &caller().join("documents.jsonl"),
        Some(&caller().join("syntax.jsonl")),
        &ExtractOptions {
            workers: 1,
            compiler_contexts: Some(contexts_path()),
            ..Default::default()
        },
    )
    .unwrap()
}
fn rejected(change: impl FnOnce(&mut Value)) {
    let owner = prepared();
    let requests = owner.metadata_requests(&Default::default()).unwrap();
    assert!(
        requests
            .iter()
            .any(|r| r.context == CONTEXT && r.symbol == MODULE)
    );
    let mut manifest = json(&fixture().join("manifest.json"));
    for payload in manifest["payloads"].as_array_mut().unwrap() {
        payload["path"] = json!(fixture().join(payload["path"].as_str().unwrap()));
    }
    change(&mut manifest);
    let temporary = tempfile::tempdir().unwrap();
    let path = temporary.path().join("manifest.json");
    std::fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    assert!(
        admit(
            &path,
            &requests,
            &Authority::new(),
            hash(&json(&fixture().join("manifest.json"))["producer_sha256"]),
            &Default::default()
        )
        .is_err()
    );
}

#[test]
fn genuine_object_header_supplies_only_exact_contextual_identity() {
    let owner = prepared();
    let requests = owner.metadata_requests(&Default::default()).unwrap();
    assert!(
        requests
            .iter()
            .any(|r| r.context == CONTEXT && r.symbol == MODULE)
    );
    let manifest = json(&fixture().join("manifest.json"));
    let admitted = admit(
        &fixture().join("manifest.json"),
        &requests,
        &Authority::new(),
        hash(&manifest["producer_sha256"]),
        &Default::default(),
    )
    .unwrap();
    assert_eq!(admitted.methods(), 0);
    let facts = finish_capture(owner, Some(Arc::new(admitted))).unwrap();
    let module = facts.find_symbol(MODULE).unwrap();
    let record = facts.symbols[module.index()];
    assert_eq!(record.kind, 10);
    assert_eq!(record.flags, 0);
    assert_eq!(record.properties, 0);
    assert!(record.file.is_none());
    assert!(record.signature.is_none());
    assert_eq!(facts.text(record.context), CONTEXT);
    assert_eq!(facts.symbol_name(record.owner), "selectedexternal/");
    assert!(
        !facts
            .relations
            .iter()
            .any(|r| r.kind == RelationKind::Parent && r.source == module)
    );
    assert!(!facts.bodies.iter().any(|b| b.symbol == module));
    let note = facts.find_symbol(NOTE).unwrap();
    assert!(
        facts.symbols[note.index()].signature.is_none(),
        "header cannot smuggle member signatures"
    );
    // Executable uncertainty is a runtime boundary, not a fact issue keyed to
    // the callee: check the actual public solver instead of inventing an issue.
    let graph = selector_graph_build::build(&facts, &Default::default()).unwrap();
    let node = graph.node_for_symbol(note).unwrap();
    let options = selector_solve::SolveOptions {
        workers: 1,
        max_contexts: 1000,
        max_steps: 10_000,
        memory_budget_bytes: 64 * 1024 * 1024,
        execution_roots: Some(
            vec![selector_solve::ExecutionRoot {
                node,
                receiver: module,
            }]
            .into(),
        ),
        ..Default::default()
    };
    let mut session = selector_solve::QuerySession::new(&facts, &graph, &options).unwrap();
    let result = session.analyze(&[]).unwrap();
    assert_ne!(result.completion, Completion::ResourceLimited);
    assert!(result.guarded_roots.contains(&node));
    assert!(
        session
            .first_runtime_issue_sites()
            .any(|(_, at, site)| at == node
                && site.reason == selector_issue::RuntimeIssueReason::MissingExecutableBody),
        "module identity cannot discharge its member's missing runtime body"
    );
    assert_eq!(source_read(&facts).1.opcode, Opcode::Allocate);
}

#[test]
fn optional_none_is_byte_identical_and_header_does_not_rewrite_unrelated_constants() {
    let options = ExtractOptions {
        workers: 1,
        compiler_contexts: Some(contexts_path()),
        ..Default::default()
    };
    let direct = selector_extract::import_capture(
        &caller().join("documents.jsonl"),
        Some(&caller().join("syntax.jsonl")),
        &options,
    )
    .unwrap();
    let none = finish_capture(prepared(), None).unwrap();
    let temporary = tempfile::tempdir().unwrap();
    selector_facts::codec::write(&temporary.path().join("direct.bin"), &direct).unwrap();
    selector_facts::codec::write(&temporary.path().join("none.bin"), &none).unwrap();
    assert_eq!(
        std::fs::read(temporary.path().join("direct.bin")).unwrap(),
        std::fs::read(temporary.path().join("none.bin")).unwrap()
    );
    let header = source(true);
    let constants = |facts: &FactSnapshot| {
        facts
            .operations
            .iter()
            .filter(|op| op.opcode == Opcode::Constant)
            .map(|op| {
                format!(
                    "{}:{:?}",
                    facts.symbol_name(facts.bodies[op.body.index()].symbol),
                    op
                )
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(
        constants(&none),
        constants(&header),
        "OBJECT identity cannot classify scalar literals or opaque data as modules"
    );
}

#[test]
fn header_only_reference_uses_real_module_slot_and_retains_initialization_effects() {
    let (before, after) = enrich(true, false);
    let (index, read) = source_read(&before);
    assert_eq!(read.opcode, Opcode::Allocate);
    let call = after.operations[index];
    assert_eq!(call.opcode, Opcode::Call);
    assert!(
        after
            .symbol_name(call.target)
            .starts_with("@jvm-module-read/")
    );
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
    let ops = adapter(&after, call.target);
    assert_eq!(ops.len(), 3);
    assert_eq!(ops[0].opcode, Opcode::Initialize);
    assert_eq!(ops[1].opcode, Opcode::LoadField);
    assert_eq!(ops[1].flags, OP_STATIC_FIELD);
    assert!(after.symbol_name(ops[1].target).contains("MODULE$"));
    assert_eq!(ops[2].opcode, Opcode::Return);
    assert_eq!(ops[2].a, ops[1].dest);
    assert!(
        after
            .operations
            .iter()
            .any(|op| op.opcode == Opcode::StoreField && op.target == ops[1].target)
    );
    let module = after.symbols[ops[1].target.index()].owner;
    assert!(
        after
            .operations
            .iter()
            .any(|op| op.opcode == Opcode::StoreField
                && !op.target.is_none()
                && after.symbols[op.target.index()].owner == module
                && after.symbol_name(op.target).contains("trace"))
    );
    assert_eq!(
        std::fs::read_to_string(caller().join("jvm-inherited.stdout")).unwrap(),
        "inherited:interval,timeout:1:2\n"
    );
    let (missing, opaque) = enrich(true, true);
    let (index, read) = source_read(&missing);
    assert_eq!(
        format!("{:?}", opaque.operations[index]),
        format!("{read:?}"),
        "compiler header cannot bypass an unavailable earlier provider"
    );
}

#[test]
fn wrong_context_kind_or_duplicate_header_conflict_is_rejected() {
    rejected(|m| m["module_headers"][0]["context"] = json!("foreign-context"));
    rejected(|m| m["module_headers"][0]["projections"][0]["context"] = json!("foreign-context"));
    rejected(|m| {
        let duplicate = m["module_headers"][0].clone();
        m["module_headers"].as_array_mut().unwrap().push(duplicate);
    });
    let pins = json(&fixture().join("fixture.json"));
    for name in [
        "wrong-kind",
        "defined-property",
        "signature",
        "overridden-symbol",
        "java-language",
        "unrequested-member",
        "source-text",
    ] {
        let suffix = format!("/negative/{name}.semanticdb");
        let row = pins["files"]
            .as_array()
            .unwrap()
            .iter()
            .find(|r| r["path"].as_str().unwrap().ends_with(&suffix))
            .unwrap();
        rejected(|m| {
            m["payloads"][0]["path"] = json!(
                PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                    .join("../..")
                    .join(row["path"].as_str().unwrap())
            );
            m["payloads"][0]["sha256"] = row["sha256"].clone();
        });
    }
}
