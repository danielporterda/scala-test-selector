//! Genuine bytecode recipes through ordinary native admission and IR lowering.
//! Callable roots are engine controls, not discovered CI suite registrations.
use selector_facts::{FactBuilder, FactSnapshot};
use selector_graph_build::binary_inputs::{augment_binary_facts, load_binary_manifest};
use selector_types::*;
use serde_json::{Value, json};
use std::path::PathBuf;
const OWNER: &str = "aliascase/Probe";
fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/native-branch-alias")
}
fn identity(name: &str, desc: &str) -> String {
    format!(
        "@jvm/{}:{OWNER}{}:{name}{}:{desc}",
        OWNER.len(),
        name.len(),
        desc.len()
    )
}
fn admitted() -> FactSnapshot {
    let mut builder = FactBuilder::new();
    builder.facts.revision = builder.intern("genuine-native-branch-alias").unwrap();
    let context = builder.intern("fixture:native-branch-alias").unwrap();
    let class = builder
        .ensure_global_symbol(&identity("<type>", ""), context)
        .unwrap();
    builder.facts.symbols[class.index()].kind = 13;
    let facts = builder.finish().unwrap();
    let pin: Value =
        serde_json::from_slice(&std::fs::read(fixture().join("manifest.json")).unwrap()).unwrap();
    let jar = pin["files"]
        .as_array()
        .unwrap()
        .iter()
        .find(|r| r["path"] == "bytecode.jar")
        .unwrap();
    let methods:Vec<_>=[("lazy","()Ljava/lang/Object;"),("initialize","()V"),
        ("mergedField","(ZLaliascase/Probe;Laliascase/Probe;)Ljava/lang/Object;"),
        ("mergedCall","(ZLaliascase/Probe;Laliascase/Probe;)Ljava/lang/Object;"),
        ("mergedStore","(ZLjava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;"),
        ("mixed","(Z)Ljava/lang/Object;"),("opaque","()Ljava/lang/Object;"),
        ("reflecting","(Z)Ljava/lang/Object;")].into_iter().map(|(name,desc)|json!({
            "context":"fixture:native-branch-alias","jvm_owner":OWNER,"jvm_name":name,"descriptor":desc})).collect();
    let manifest = json!({"version":1,"revision":facts.text(facts.revision),"java_feature":21,
        "contexts":[{"id":"fixture:native-branch-alias","entries":[{"path":fixture().join("bytecode.jar"),"sha256":jar["sha256"],"kind":"jar"}]}],
        "types":[{"context":"fixture:native-branch-alias","compiler_symbol":identity("<type>",""),"jvm_owner":OWNER}],"methods":methods});
    let temp = tempfile::tempdir().unwrap();
    let path = temp.path().join("manifest.json");
    std::fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    let mut facts = facts;
    let mut inputs = load_binary_manifest(&path, &facts).unwrap();
    augment_binary_facts(&mut facts, &mut inputs).unwrap();
    facts
}
fn operations<'a>(
    facts: &'a FactSnapshot,
    name: &str,
    desc: &str,
) -> &'a [selector_facts::OperationRecord] {
    let symbol = facts.find_symbol(&identity(name, desc)).unwrap();
    let body = facts.bodies.iter().find(|b| b.symbol == symbol).unwrap();
    assert_ne!(body.flags & BODY_BINARY_RECIPE, 0);
    &facts.operations[body.operations.range()]
}
#[test]
fn ordinary_lowering_returns_the_actual_lazy_field_and_preserves_initialize_effects() {
    let facts = admitted();
    let ops = operations(&facts, "lazy", "()Ljava/lang/Object;");
    let loads: Vec<_> = ops
        .iter()
        .filter(|op| op.opcode == Opcode::LoadField)
        .collect();
    assert_eq!(loads.len(), 2);
    assert!(loads.iter().all(|op| op.a == ValueId(0)));
    assert_eq!(loads[0].target, loads[1].target);
    assert!(ops.iter().any(|op| op.opcode == Opcode::VirtualCall
        && op.a == ValueId(0)
        && facts.symbol_name(op.target) == identity("initialize", "()V")));
    assert!(
        ops.iter()
            .any(|op| op.opcode == Opcode::Return && op.a == loads[1].dest)
    );
    let effects = operations(&facts, "initialize", "()V");
    assert!(effects.iter().any(|op| op.opcode == Opcode::StoreField));
    assert_eq!(
        std::fs::read_to_string(fixture().join("execution.stdout")).unwrap(),
        "lazy:true,branches:true,field:true,call:true,store:true,throw:true,catch:true,literal:true\n"
    );
}
#[test]
fn merged_alias_join_is_evaluated_before_its_field_call_and_write_consumers() {
    let facts = admitted();
    for (name, desc, consumer) in [
        (
            "mergedField",
            "(ZLaliascase/Probe;Laliascase/Probe;)Ljava/lang/Object;",
            Opcode::LoadField,
        ),
        (
            "mergedCall",
            "(ZLaliascase/Probe;Laliascase/Probe;)Ljava/lang/Object;",
            Opcode::VirtualCall,
        ),
        (
            "mergedStore",
            "(ZLjava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;",
            Opcode::StoreField,
        ),
    ] {
        let ops = operations(&facts, name, desc);
        let (position, join) = ops
            .iter()
            .enumerate()
            .find(|(_, op)| op.opcode == Opcode::Join)
            .unwrap();
        assert_eq!(
            &facts.operands[join.arguments.range()],
            [ValueId(2), ValueId(3)]
        );
        let (at, op) = ops
            .iter()
            .enumerate()
            .find(|(_, op)| {
                op.opcode == consumer
                    && (if consumer == Opcode::StoreField {
                        op.b
                    } else {
                        op.a
                    }) == join.dest
            })
            .unwrap();
        assert!(
            position < at,
            "join is available before native consumer {name}"
        );
        if consumer == Opcode::LoadField {
            assert!(
                ops.iter()
                    .any(|r| r.opcode == Opcode::Return && r.a == op.dest)
            );
        }
    }
}
#[test]
fn unresolved_native_branch_and_reflective_effects_remain_guarded_at_the_actual_callee() {
    let mut facts = admitted();
    let temp = tempfile::tempdir().unwrap();
    facts.identity = selector_facts::codec::write(&temp.path().join("facts.bin"), &facts).unwrap();
    let graph = selector_graph_build::build(&facts, &Default::default()).unwrap();
    let mixed = facts
        .find_symbol(&identity("mixed", "(Z)Ljava/lang/Object;"))
        .unwrap();
    let opaque = facts
        .find_symbol(&identity("opaque", "()Ljava/lang/Object;"))
        .unwrap();
    let root = graph.node_for_symbol(mixed).unwrap();
    let missing = graph.node_for_symbol(opaque).unwrap();
    let options = selector_solve::SolveOptions {
        workers: 1,
        max_contexts: 1000,
        max_steps: 100_000,
        memory_budget_bytes: 64 * 1024 * 1024,
        execution_roots: Some(
            vec![selector_solve::ExecutionRoot {
                node: root,
                receiver: facts.find_symbol(&identity("<type>", "")).unwrap(),
            }]
            .into(),
        ),
        ..Default::default()
    };
    let mut session = selector_solve::QuerySession::new(&facts, &graph, &options).unwrap();
    let result = session.analyze(&[]).unwrap();
    assert_ne!(result.completion, Completion::ResourceLimited);
    assert!(result.guarded_roots.contains(&root));
    assert!(
        session
            .first_runtime_issue_sites()
            .any(|(_, node, _)| node == missing),
        "opaque branch must retain its own runtime guard"
    );
    let reflective = operations(&facts, "reflecting", "(Z)Ljava/lang/Object;");
    assert!(reflective.iter().any(|op| op.opcode == Opcode::Unknown));
    assert!(reflective.iter().any(|op| op.opcode == Opcode::StoreField));
}
