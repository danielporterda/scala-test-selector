//! Missing hierarchy metadata is not a missing executable initializer. Real
//! default-interface/superclass phases and missing callees remain conservative.
use selector_facts::{FactBuilder, FactSnapshot, OperationRecord};
use selector_graph_build::binary_inputs::{augment_binary_facts, load_binary_manifest};
use selector_solve::{ExecutionRoot, SolveOptions};
use selector_types::*;
use std::path::PathBuf;

const CHILD: &str = "metadatacase/Probe$Child";
const DEFAULT: &str = "metadatacase/Probe$DefaultChild";
const SUPER: &str = "metadatacase/Probe$SuperChild";
const EFFECTS: &str = "metadatacase/Probe$Effects";
fn directory() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/incomplete-hierarchy")
}
fn endpoint(owner: &str, name: &str, descriptor: &str) -> String {
    format!(
        "@jvm/{}:{owner}{}:{name}{}:{descriptor}",
        owner.len(),
        name.len(),
        descriptor.len()
    )
}
fn admitted(mode: &str) -> FactSnapshot {
    let mut builder = FactBuilder::new();
    let context = builder.intern("fixture:incomplete-hierarchy").unwrap();
    builder.facts.revision = builder.intern("genuine-incomplete-hierarchy-v1").unwrap();
    let owners = [CHILD, DEFAULT, SUPER, EFFECTS];
    let mut classes = std::collections::HashMap::new();
    for owner in owners {
        let id = builder
            .ensure_symbol(&endpoint(owner, "<type>", ""), FileId::NONE)
            .unwrap();
        let row = &mut builder.facts.symbols[id.index()];
        row.kind = if owner == CHILD { 14 } else { 13 };
        row.context = context;
        // Opaque native endpoint identity only; verified headers and all parent
        // completeness flags come from ordinary admitted class bytes.
        row.flags = SYMBOL_NATIVE_BINARY;
        classes.insert(owner, id);
    }
    let mut methods = Vec::new();
    for (owner, name, descriptor) in [
        (CHILD, "ping", "()I"),
        (CHILD, "opaque", "()I"),
        (DEFAULT, "ping", "()I"),
        (SUPER, "ping", "()I"),
        (SUPER, "<init>", "()V"),
        (EFFECTS, "changed", "()I"),
        (EFFECTS, "note", "(I)I"),
    ] {
        let identity = endpoint(owner, name, descriptor);
        let id = builder.ensure_symbol(&identity, FileId::NONE).unwrap();
        let row = &mut builder.facts.symbols[id.index()];
        row.context = context;
        row.owner = classes[owner];
        row.kind = 3;
        row.flags = SYMBOL_NATIVE_BINARY;
        methods.push(
            serde_json::json!({"context":"fixture:incomplete-hierarchy","compiler_symbol":identity,
            "jvm_owner":owner,"jvm_name":name,"descriptor":descriptor}),
        );
    }
    let mut facts = builder.finish().unwrap();
    let receipt: serde_json::Value =
        serde_json::from_slice(&std::fs::read(directory().join("manifest.json")).unwrap()).unwrap();
    let jar_name = if mode == "full" {
        "bytecode.jar"
    } else {
        "retained.jar"
    };
    let jar = receipt["files"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["path"] == jar_name)
        .unwrap();
    let mut entries = Vec::new();
    if mode == "opaque-prefix" {
        entries.push(serde_json::json!({"path":directory().join("unavailable-earlier-provider.jar"),"kind":"unavailable"}));
    }
    entries.push(
        serde_json::json!({"path":directory().join(jar_name),"sha256":jar["sha256"],"kind":"jar"}),
    );
    let bootstrap = &receipt["bootstrap_input"];
    entries.push(
        serde_json::json!({"path":bootstrap["path"],"sha256":bootstrap["sha256"],"kind":"jar"}),
    );
    let manifest = serde_json::json!({"version":1,"revision":facts.text(facts.revision),"java_feature":21,
        "contexts":[{"id":"fixture:incomplete-hierarchy","entries":entries}],
        "types":owners.into_iter().map(|owner|serde_json::json!({"context":"fixture:incomplete-hierarchy",
            "compiler_symbol":endpoint(owner,"<type>",""),"jvm_owner":owner})).collect::<Vec<_>>(),"methods":methods});
    let temp = tempfile::tempdir().unwrap();
    let path = temp.path().join("binary.json");
    std::fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    let mut inputs = load_binary_manifest(&path, &facts).unwrap();
    augment_binary_facts(&mut facts, &mut inputs).unwrap();
    facts
}
fn operations<'a>(
    facts: &'a FactSnapshot,
    owner: &str,
    name: &str,
    descriptor: &str,
) -> &'a [OperationRecord] {
    let symbol = facts
        .find_symbol(&endpoint(owner, name, descriptor))
        .unwrap();
    let body = facts
        .bodies
        .iter()
        .find(|body| body.symbol == symbol)
        .unwrap();
    &facts.operations
        [body.operations.start as usize..(body.operations.start + body.operations.len) as usize]
}
fn analyze(
    facts: &FactSnapshot,
    owner: &str,
    name: &str,
    descriptor: &str,
) -> (
    selector_result::AnalysisResult,
    selector_graph::ProgramGraph,
    NodeId,
) {
    let graph = selector_graph_build::build(
        facts,
        &selector_graph_build::BuildOptions {
            workers: 2,
            include_models: false,
        },
    )
    .unwrap();
    let node = |owner, name, descriptor| {
        graph
            .node_for_symbol(
                facts
                    .find_symbol(&endpoint(owner, name, descriptor))
                    .unwrap(),
            )
            .unwrap()
    };
    let root = node(owner, name, descriptor);
    let changed = node(EFFECTS, "changed", "()I");
    let options = SolveOptions {
        workers: 2,
        memory_budget_bytes: 32 * 1024 * 1024,
        max_contexts: 4096,
        max_steps: 100_000,
        execution_roots: Some(
            vec![ExecutionRoot {
                node: root,
                receiver: SymbolId::NONE,
            }]
            .into(),
        ),
        ..Default::default()
    };
    let result = selector_solve::analyze(facts, &graph, &[changed], &options).unwrap();
    assert_ne!(result.completion, Completion::ResourceLimited);
    (result, graph, root)
}
#[test]
fn frozen_jvm_observations_distinguish_interface_default_and_superclass_initialization() {
    for (mode, expected) in [
        ("child", "child:2:2:7\n"),
        ("default", "default:12:2:7\n"),
        ("super-static", "super-static:48:2:7\n"),
        ("super-constructor", "super-constructor:112:1:0\n"),
        ("missing", "missing:2:1:11\n"),
    ] {
        assert_eq!(
            std::fs::read_to_string(directory().join(format!("{mode}.log"))).unwrap(),
            expected
        );
    }
}
#[test]
fn interface_missing_marker_metadata_keeps_actual_initializer_and_impact_without_runtime_guard() {
    let facts = admitted("missing");
    let child = facts.find_symbol(&endpoint(CHILD, "<type>", "")).unwrap();
    assert_eq!(
        facts.symbols[child.index()].flags & SYMBOL_JVM_PARENTS_COMPLETE,
        0
    );
    assert!(
        facts
            .issues
            .iter()
            .any(|issue| issue.symbol == child && issue.kind == IssueKind::IncompleteHierarchy)
    );
    let (result, graph, root) = analyze(&facts, CHILD, "ping", "()I");
    assert!(result.contains(root), "actual changed call remains reached");
    let clinit = graph
        .node_for_symbol(
            facts
                .find_symbol(&endpoint(CHILD, "<clinit>", "()V"))
                .unwrap(),
        )
        .unwrap();
    assert!(
        result.contains(clinit),
        "changed call in genuine interface initializer remains reached"
    );
    assert!(
        !graph
            .issues
            .iter()
            .any(|issue| issue.kind == IssueKind::IncompleteHierarchy),
        "metadata diagnostics are not executable graph issues"
    );
    assert!(
        result.guarded_roots.is_empty(),
        "metadata-only marker does not create an executable root guard: {:?}",
        result.evidence.guard_causes
    );
    assert_eq!(result.completion, Completion::Complete);
    let marker = "metadatacase/Probe$Marker";
    assert!(
        !operations(&facts, CHILD, "<class-init>", "()V")
            .iter()
            .any(|op| !op.target.is_none() && facts.symbol_name(op.target).contains(marker)),
        "static interface initialization must not invent superinterface initialization"
    );
}
#[test]
fn missing_default_interface_and_superclass_keep_real_executable_frontiers() {
    let facts = admitted("missing");
    let full = admitted("full");
    for (owner, name, descriptor) in [
        (DEFAULT, "ping", "()I"),
        (SUPER, "ping", "()I"),
        (SUPER, "<init>", "()V"),
    ] {
        let (complete, _, _) = analyze(&full, owner, name, descriptor);
        assert_eq!(complete.completion, Completion::Complete);
        assert!(
            complete.guarded_roots.is_empty(),
            "{owner}.{name} is closed with the actual parent bytes"
        );
        let (result, _, root) = analyze(&facts, owner, name, descriptor);
        // A direct constructor context has no allocation caller to request its
        // class static phase; the invokespecial parent body is still required.
        if name != "<init>" {
            assert!(
                result.contains(root),
                "{owner}.{name}: admitted own initializer's changed call survives missing parent"
            );
        }
        assert!(
            result.guarded_roots.contains(&root),
            "{owner}.{name} has an actual unresolved executable phase"
        );
    }
    for owner in [DEFAULT, SUPER] {
        assert!(
            operations(&facts, owner, "<class-init>", "()V")
                .iter()
                .any(|op| op.opcode == Opcode::Unknown)
        );
    }
    assert!(
        operations(&facts, SUPER, "<init>", "()V")
            .iter()
            .any(|op| op.opcode == Opcode::Call),
        "real invokespecial superclass constructor is not erased"
    );
}
#[test]
fn missing_callee_and_unavailable_earlier_provider_are_not_metadata_only() {
    let facts = admitted("missing");
    let (result, _, root) = analyze(&facts, CHILD, "opaque", "()I");
    assert!(
        result.guarded_roots.contains(&root),
        "actual missing method body remains guarded"
    );
    let hidden = admitted("opaque-prefix");
    let (result, _, root) = analyze(&hidden, CHILD, "ping", "()I");
    assert!(
        result.guarded_roots.contains(&root),
        "unavailable provider prevents later exact bytes from authorizing execution"
    );
    assert!(
        !hidden
            .symbols
            .iter()
            .any(|row| row.flags & SYMBOL_JVM_CLASS_HEADER_VERIFIED != 0)
    );
}
