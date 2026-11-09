//! The genuine repeated-callback compiler fixture exercises the guarded native
//! indexed view. This proves callback flow, not complete collection execution.
use selector_facts::FactSnapshot;
use selector_solve::{ExecutionRoot, QuerySession, SolveOptions};
use selector_types::*;
use serde_json::json;
use std::path::PathBuf;
use std::sync::Arc;

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/repeated-callbacks")
}
fn facts() -> FactSnapshot {
    selector_extract::import_capture(
        &fixture().join("all-documents.jsonl"),
        Some(&fixture().join("all-syntax.jsonl")),
        &Default::default(),
    )
    .unwrap()
}
fn analyze(native: bool) -> (bool, bool, bool) {
    let mut facts = facts();
    let seq = facts
        .find_symbol("scala/collection/SeqOps#apply().")
        .unwrap();
    let context = facts.text(facts.symbols[seq.index()].context).to_owned();
    let directory = tempfile::tempdir().unwrap();
    if native {
        let manifest: serde_json::Value =
            serde_json::from_slice(&std::fs::read(fixture().join("manifest.json")).unwrap())
                .unwrap();
        let library = manifest["jars"]
            .as_array()
            .unwrap()
            .iter()
            .find(|jar| jar["path"].as_str().unwrap().contains("/scala-library/"))
            .unwrap();
        let map = json!({"version":1,"revision":facts.text(facts.revision),"java_feature":null,
            "contexts":[{"id":context,"entries":[{"path":library["path"],"kind":"jar","sha256":library["sha256"]}]}],
            "types":[{"context":context,"compiler_symbol":"scala/collection/SeqOps#","jvm_owner":"scala/collection/SeqOps"}],
            "methods":[{"context":context,"compiler_symbol":"scala/collection/SeqOps#apply().","jvm_owner":"scala/collection/SeqOps","jvm_name":"apply","descriptor":"(I)Ljava/lang/Object;"}]});
        let path = directory.path().join("binary.json");
        std::fs::write(&path, serde_json::to_vec(&map).unwrap()).unwrap();
        let mut binary =
            selector_graph_build::binary_inputs::load_binary_manifest(&path, &facts).unwrap();
        selector_graph_build::binary_inputs::augment_binary_facts(&mut facts, &mut binary).unwrap();
    }
    let provider = facts
        .find_symbol("repeatedcallbacks/Calls#provider().")
        .unwrap();
    let provider_body = facts
        .bodies
        .iter()
        .find(|body| body.symbol == provider)
        .unwrap();
    let callback = facts.operations[provider_body.operations.range()]
        .iter()
        .find(|op| op.opcode == Opcode::BindCallback)
        .unwrap()
        .target;
    // Seeding the deferred body itself cannot be satisfied by calling its
    // provider factory; it requires actual callback activation in the engine.
    assert_ne!(provider, callback);
    let graph = selector_graph_build::build(
        &facts,
        &selector_graph_build::BuildOptions {
            include_models: false,
            ..Default::default()
        },
    )
    .unwrap();
    let receiver = facts.find_symbol("repeatedcallbacks/Calls#").unwrap();
    let roots = ["flat", "captured", "dormant"].map(|name| ExecutionRoot {
        node: graph
            .node_for_symbol(
                facts
                    .find_symbol(&format!("repeatedcallbacks/Calls#{name}()."))
                    .unwrap(),
            )
            .unwrap(),
        receiver,
    });
    let options = SolveOptions {
        workers: 1,
        execution_roots: Some(Arc::from(roots)),
        max_contexts: 10_000,
        max_steps: 1_000_000,
        ..Default::default()
    };
    let mut session = QuerySession::new(&facts, &graph, &options).unwrap();
    session.execute(&roots).unwrap();
    let result = session
        .analyze(&[graph.node_for_symbol(callback).unwrap()])
        .unwrap();
    assert_ne!(result.completion, Completion::ResourceLimited);
    assert!(
        result.guarded_roots.contains(&roots[0].node),
        "native/backend uncertainty remains explicit"
    );
    let aggregate = facts
        .find_symbol("repeatedcallbacks/Api#aggregate().")
        .unwrap();
    let aggregate = facts
        .bodies
        .iter()
        .find(|body| body.symbol == aggregate)
        .unwrap();
    assert_eq!(
        facts.operations[aggregate.operations.range()]
            .iter()
            .filter(|op| op.flags & OP_SEQUENCE_ELEMENT_VIEW != 0)
            .count(),
        if native { 2 } else { 0 },
        "{:?}",
        facts.operations[aggregate.operations.range()]
            .iter()
            .map(|op| (
                op.opcode,
                if op.target.is_none() {
                    ""
                } else {
                    facts.symbol_name(op.target)
                },
                op.a,
                op.arguments.len,
                op.flags
            ))
            .collect::<Vec<_>>()
    );
    (
        result.contains(roots[0].node),
        result.contains(roots[1].node),
        result.contains(roots[2].node),
    )
}

#[test]
fn exact_selected_seqops_view_activates_flat_elements_and_keeps_creation_deferred() {
    assert_eq!(
        analyze(false),
        (false, false, false),
        "without native authority no element view is invented"
    );
    assert_eq!(
        analyze(true),
        (true, false, false),
        "guarded native view retains callbacks without eagerly invoking returned packs"
    );
}
