//! NORMALIZED TWO-CONTEXT SEAM over genuine compiler/native bytes.
//! This does not claim two independently captured compiler invocations.
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
const OTHER: &str = "normalized:other-compiler-context";
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

fn pool(facts: &mut FactSnapshot, text: &str) -> StrId {
    if let Some(i) = (0..facts.strings.len()).find(|&i| facts.text(StrId(i as u32)) == text) {
        return StrId(i as u32);
    }
    let id = StrId(facts.strings.len() as u32);
    facts.strings.entries.push(selector_facts::TextRange {
        start: facts.strings.bytes.len() as u64,
        len: text.len() as u32,
    });
    facts.strings.bytes.extend_from_slice(text.as_bytes());
    id
}
#[derive(Clone, Copy)]
enum Negative {
    None,
    ChangedHeader,
    OpaqueProvider,
    SourceOverlay,
    WrongDescriptor,
}
fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/cross-context-native-getter")
}
fn run(
    negative: Negative,
) -> (
    FactSnapshot,
    Option<SymbolId>,
    Vec<SymbolId>,
    Vec<selector_facts::RelationRecord>,
) {
    let mut original = enhanced();
    let other = pool(&mut original, OTHER);
    // Normalized native demand context; no source/definition/header authority.
    // The manifest cannot introduce a wholly absent compiler context itself.
    let name = pool(&mut original, "selectedexternal/Configuration#");
    original.symbols.push(selector_facts::SymbolRecord {
        name,
        display: StrId::NONE,
        owner: SymbolId::NONE,
        file: FileId::NONE,
        context: other,
        kind: 0,
        properties: 0,
        signature: StrId::NONE,
        span: Span::default(),
        flags: 0,
    });
    let calls = original.find_symbol(CALLS).unwrap();
    if matches!(negative, Negative::SourceOverlay) {
        // Normalized precedence-negative, not a newly compiled declaration.
        // A source-owned same-name declaration wins even with unknown signature.
        let name = pool(&mut original, "selectedexternal/Calls#PatienceConfig().");
        let display = pool(&mut original, "PatienceConfig");
        let owner = original.symbols[calls.index()];
        original.symbols.push(selector_facts::SymbolRecord {
            name,
            display,
            owner: calls,
            file: owner.file,
            context: owner.context,
            kind: 3,
            properties: 0,
            signature: StrId::NONE,
            span: owner.span,
            flags: SYMBOL_DEFINED,
        });
    }
    let original_parents: Vec<_> = original
        .relations
        .iter()
        .copied()
        .filter(|r| r.kind == RelationKind::Parent && r.source == calls)
        .collect();
    let temporary = tempfile::tempdir().unwrap();
    let source = temporary.path().join("source.bin");
    original.identity = selector_facts::codec::write(&source, &original).unwrap();
    let mut facts = selector_facts::codec::read(&source).unwrap();
    let view = native_view(&original, temporary.path());
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
    let mut manifest = generated.manifest;
    let mut context = manifest["contexts"][0].clone();
    context["id"] = json!(OTHER);
    let descriptor = if matches!(negative, Negative::WrongDescriptor) {
        "(I)Lselectedexternal/Configuration$PatienceConfig$;"
    } else {
        "()Lselectedexternal/Configuration$PatienceConfig$;"
    };
    if matches!(negative, Negative::ChangedHeader) {
        let pins = read_json(&fixture().join("fixture.json"));
        for entry in context["entries"].as_array_mut().unwrap() {
            if entry["path"]
                .as_str()
                .unwrap()
                .ends_with("/selected-external-apply/library.jar")
            {
                entry["path"] = json!(fixture().join("changed-contract-header.jar"));
                entry["sha256"] = pins["files"][0]["sha256"].clone();
            }
        }
    }
    if matches!(negative, Negative::OpaqueProvider) {
        context["entries"].as_array_mut().unwrap().insert(
            0,
            json!({"path":temporary.path().join("unavailable.jar"),
            "sha256":ContentHash([1;32]).to_string(),"kind":"unavailable"}),
        );
    }
    manifest["contexts"].as_array_mut().unwrap().push(context);
    manifest["methods"].as_array_mut().unwrap().push(json!({"compiler_symbol":null,"context":OTHER,
        "jvm_owner":"selectedexternal/Configuration","jvm_name":"PatienceConfig","descriptor":descriptor}));
    let path = temporary.path().join("manifest.json");
    std::fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    let mut inputs =
        selector_graph_build::binary_inputs::load_binary_manifest(&path, &facts).unwrap();
    selector_graph_build::binary_inputs::augment_binary_facts(&mut facts, &mut inputs).unwrap();
    let contract = facts.symbols.iter().enumerate().find_map(|(i, s)| {
        (facts.text(s.context) == OTHER
            && s.kind == 3
            && facts.symbol_name(SymbolId(i as u32)).starts_with("@jvm/")
            && facts
                .symbol_name(SymbolId(i as u32))
                .contains("14:PatienceConfig"))
        .then_some(SymbolId(i as u32))
    });
    let implementations = contract
        .map(|target| {
            facts
                .relations
                .iter()
                .filter(|r| r.kind == RelationKind::Override && r.target == target)
                .map(|r| r.source)
                .filter(|&id| facts.symbols[id.index()].owner == calls)
                .collect()
        })
        .unwrap_or_default();
    (facts, contract, implementations, original_parents)
}
#[test]
fn same_verified_abstract_contract_bridges_only_real_getter_execution_across_contexts() {
    let (facts, contract, implementations, parents) = run(Negative::None);
    let contract = contract.expect("actual admitted abstract getter in normalized contextA");
    assert_eq!(
        implementations.len(),
        1,
        "real native getterB must implement exact abstract contractA"
    );
    let implementation = implementations[0];
    assert_eq!(facts.text(facts.symbols[contract.index()].context), OTHER);
    assert_eq!(
        facts.text(facts.symbols[implementation.index()].context),
        CONTEXT
    );
    assert_ne!(
        facts.symbols[implementation.index()].owner,
        facts.symbols[contract.index()].owner
    );
    let body = facts
        .bodies
        .iter()
        .find(|b| b.symbol == implementation)
        .unwrap();
    assert_ne!(body.flags & BODY_BINARY_RECIPE, 0);
    let loads: Vec<_> = facts.operations[body.operations.range()]
        .iter()
        .filter(|op| op.opcode == Opcode::LoadField)
        .collect();
    assert!(!loads.is_empty());
    assert!(loads.iter().all(|op| !op.a.is_none()));
    let fields: Vec<_> = loads.iter().map(|op| op.target).collect();
    assert!(
        facts
            .operations
            .iter()
            .any(|op| op.opcode == Opcode::StoreField && fields.contains(&op.target)),
        "real lazy backing-field writes remain"
    );
    assert!(
        fields
            .iter()
            .all(|&id| facts.text(facts.symbols[id.index()].context) == CONTEXT),
        "no field context merge"
    );
    let calls = facts.find_symbol(CALLS).unwrap();
    let after: Vec<_> = facts
        .relations
        .iter()
        .copied()
        .filter(|r| r.kind == RelationKind::Parent && r.source == calls)
        .collect();
    assert_eq!(
        format!("{parents:?}"),
        format!("{after:?}"),
        "compiler parent rows unchanged"
    );
    assert_eq!(
        std::fs::read_to_string(directory().join("jvm-inherited.stdout")).unwrap(),
        "inherited:interval,timeout:1:2\n"
    );
}
#[test]
fn changed_declaring_header_or_opaque_provider_cannot_authorize_a_cross_context_override() {
    for negative in [
        Negative::ChangedHeader,
        Negative::OpaqueProvider,
        Negative::WrongDescriptor,
    ] {
        let (_, _, implementations, _) = run(negative);
        assert!(implementations.is_empty());
    }
}
#[test]
fn normalized_source_owned_same_name_member_wins_over_synthetic_native_discovery() {
    let (facts, _, implementations, _) = run(Negative::SourceOverlay);
    assert!(implementations.is_empty());
    let own = facts
        .find_symbol("selectedexternal/Calls#PatienceConfig().")
        .unwrap();
    assert_ne!(facts.symbols[own.index()].flags & SYMBOL_DEFINED, 0);
    assert!(facts.symbols[own.index()].signature.is_none());
    assert!(
        !facts
            .bodies
            .iter()
            .any(|b| b.symbol == own && b.flags & BODY_BINARY_RECIPE != 0)
    );
}

#[test]
fn normalized_foreign_target_callsite_dispatches_the_real_receiver_with_full_worker_proof() {
    let (mut facts, contract, implementations, _) = run(Negative::None);
    let contract = contract.unwrap();
    let implementation = implementations[0];
    let caller = facts
        .find_symbol("selectedexternal/Calls#inherited().")
        .unwrap();
    let receiver = facts.find_symbol(CALLS).unwrap();
    // Normalized callsite seam, not a claim about this compiler's original
    // target context: preserve the genuine caller body, receiver, operands and
    // effects, changing only its equivalent abstract native target to contextA.
    let rows: Vec<_> = facts
        .operations
        .iter()
        .enumerate()
        .filter(|(_, op)| {
            facts.bodies[op.body.index()].symbol == caller
                && op.opcode == Opcode::VirtualCall
                && !op.target.is_none()
                && facts.symbol_name(op.target).starts_with("@jvm/")
                && facts.symbol_name(op.target).contains("14:PatienceConfig")
        })
        .map(|(i, _)| i)
        .collect();
    assert_eq!(rows.len(), 1);
    let index = rows[0];
    facts.operations[index].target = contract;
    let body = facts.operations[index].body;
    facts.bodies[body.index()].body_hash = ContentHash([77; 32]);
    let temporary = tempfile::tempdir().unwrap();
    facts.identity =
        selector_facts::codec::write(&temporary.path().join("normalized-callsite.bin"), &facts)
            .unwrap();
    let graph = selector_graph_build::build(&facts, &Default::default()).unwrap();
    let root = graph.node_for_symbol(caller).unwrap();
    let changed = graph.node_for_symbol(implementation).unwrap();
    let mut baseline = None;
    for workers in [1, 4] {
        let options = selector_solve::SolveOptions {
            workers,
            max_contexts: 10_000,
            max_steps: 1_000_000,
            memory_budget_bytes: 128 * 1024 * 1024,
            execution_roots: Some(
                vec![selector_solve::ExecutionRoot {
                    node: root,
                    receiver,
                }]
                .into(),
            ),
            ..Default::default()
        };
        let mut session = selector_solve::QuerySession::new(&facts, &graph, &options).unwrap();
        let mut result = session.analyze(&[changed]).unwrap();
        assert_ne!(result.completion, Completion::ResourceLimited);
        assert!(
            result.contains(root),
            "foreign contract must dispatch the actual receiverB; guards {:?}",
            result.guarded_roots
        );
        let actual_edges: Vec<_> = graph
            .edges
            .iter()
            .enumerate()
            .filter(|(_, e)| {
                e.source == root && e.target == changed && e.operation == OperationId(index as u32)
            })
            .map(|(i, _)| EdgeId(i as u32))
            .chain(
                result
                    .derived_edges
                    .iter()
                    .enumerate()
                    .filter(|(_, e)| {
                        e.source == root
                            && e.target == changed
                            && e.operation == OperationId(index as u32)
                    })
                    .map(|(i, _)| EdgeId((graph.edges.len() + i) as u32)),
            )
            .collect();
        assert!(
            result
                .witnesses
                .iter()
                .any(|w| w.node == root && w.next == changed && actual_edges.contains(&w.edge)),
            "impact needs the actual callsite dispatch witness, static or derived"
        );
        assert!(
            result.guarded_roots.contains(&root),
            "native lazy-getter/effect guards remain"
        );
        result.metrics = selector_result::AnalysisMetrics::default();
        let proof = format!("{result:?}");
        if let Some(previous) = &baseline {
            assert_eq!(
                &proof, previous,
                "full proof except metrics is worker deterministic"
            );
        }
        baseline = Some(proof);
    }
}
