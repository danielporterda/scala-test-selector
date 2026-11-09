//! Genuine nested Future lowering: callback ownership is checked against source
//! events and independent JVM order, without declaring opaque library work pure.
use selector_extract::{ExtractOptions, import_capture};
use selector_facts::FactSnapshot;
use selector_types::*;
use std::path::PathBuf;

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/for-comprehension")
}
fn captured() -> FactSnapshot {
    import_capture(
        &fixture().join("documents.jsonl"),
        Some(&fixture().join("syntax.jsonl")),
        &ExtractOptions {
            workers: 2,
            ..Default::default()
        },
    )
    .unwrap()
}

fn with_future_arity() -> FactSnapshot {
    let mut facts = captured();
    let future_call = |op: &selector_facts::OperationRecord, facts: &FactSnapshot| {
        matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
            && matches!(
                facts.symbol_name(op.target),
                "scala/concurrent/Future#map()." | "scala/concurrent/Future#flatMap()."
            )
    };
    assert!(
        facts
            .operations
            .iter()
            .any(|op| future_call(op, &facts) && op.arguments.len == 1)
    );
    assert!(
        facts
            .operations
            .iter()
            .any(|op| op.flags == OP_SYNTHETIC_PARAMETER_APPLY)
    );
    // The caller capture deliberately omits external MethodSignature rows.
    // Admit the actual pinned library before folding its compiler-created
    // Apply-over-Apply stages; source-only prefixes must stay guarded.
    let pins: serde_json::Value =
        serde_json::from_slice(&std::fs::read(fixture().join("manifest.json")).unwrap()).unwrap();
    let library = pins["jars"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| {
            row["path"]
                .as_str()
                .unwrap()
                .ends_with("/scala-library-2.13.18.jar")
        })
        .unwrap();
    let context = facts.text(facts.files[0].context);
    let methods: Vec<_> = ["map", "flatMap"].into_iter().map(|name| serde_json::json!({
        "context": context,
        "compiler_symbol": format!("scala/concurrent/Future#{name}()."),
        "jvm_owner": "scala/concurrent/Future", "jvm_name": name,
        "descriptor": "(Lscala/Function1;Lscala/concurrent/ExecutionContext;)Lscala/concurrent/Future;"
    })).collect();
    let manifest = serde_json::json!({
        "version": 1, "revision": pins["revision"], "java_feature": 21,
        "contexts": [{"id": context, "entries": [{"path": library["path"],
            "sha256": library["sha256"], "kind": "jar"}]}],
        "types": [{"context": context, "compiler_symbol":"scala/concurrent/Future#",
            "jvm_owner":"scala/concurrent/Future"}], "methods": methods,
    });
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("binary.json");
    std::fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    let mut inputs =
        selector_graph_build::binary_inputs::load_binary_manifest(&path, &facts).unwrap();
    selector_graph_build::binary_inputs::augment_binary_facts(&mut facts, &mut inputs).unwrap();
    assert!(facts.operations.iter().any(|op| future_call(op, &facts)
        && op.arguments.len == 2
        && callback_argument_slot(op.flags) == Some(0)
        && op.flags & OP_SYNTHETIC_PARAMETER_APPLY == 0));
    facts
}
fn source_method(facts: &FactSnapshot, name: &str) -> BodyId {
    let symbol = facts
        .find_symbol(&format!("forcase/Pipeline#{name}()."))
        .unwrap();
    BodyId(
        facts
            .bodies
            .iter()
            .position(|body| body.symbol == symbol && body.flags & BODY_DEFERRED == 0)
            .unwrap() as u32,
    )
}
fn owned_call(facts: &FactSnapshot, method: BodyId, target: &str) -> usize {
    let source = facts.bodies[method.index()].span;
    let calls: Vec<_> = facts
        .operations
        .iter()
        .enumerate()
        .filter(|(_, op)| {
            facts.symbol_name(op.target) == format!("forcase/Pipeline#{target}().")
                && matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
                && source.start <= op.span.start
                && op.span.end <= source.end
        })
        .map(|(i, _)| i)
        .collect();
    assert_eq!(calls.len(), 1, "one actual {target} call in {source:?}");
    calls[0]
}

#[test]
fn real_value_enumerator_and_suffix_sentinels_preserve_the_continuation_chain() {
    let facts = captured();
    let flat_map = facts
        .find_symbol("scala/concurrent/Future#flatMap().")
        .unwrap();
    for method in [
        source_method(&facts, "execute"),
        source_method(&facts, "dormant"),
    ] {
        let check = owned_call(&facts, method, "check");
        let save = owned_call(&facts, method, "save");
        let after = owned_call(&facts, method, "after");
        assert!(facts.operations[check].span.start < facts.operations[save].span.start);
        assert!(facts.operations[save].span.start < facts.operations[after].span.start);
        assert_ne!(facts.operations[save].body, method);
        assert_ne!(facts.operations[after].body, method);
        assert_ne!(facts.operations[save].body, facts.operations[after].body);
        for call in [check, save, after] {
            assert_ne!(
                facts.bodies[facts.operations[call].body.index()].flags & BODY_DEFERRED,
                0
            );
        }
        let continuation = facts.bodies[facts.operations[after].body.index()];
        // Ownership may be discontiguous even when a compiler FunctionTree's
        // enclosing source span overlaps its already-evaluated qualifier.
        let binding = facts
            .operations
            .iter()
            .find(|op| {
                op.opcode == Opcode::BindCallback
                    && op.target == continuation.symbol
                    && op.body == facts.operations[save].body
            })
            .expect("save's enclosing callback binds the next continuation");
        assert!(
            facts.operations.iter().any(|op| op.body == binding.body
                && op.target == flat_map
                && op.a == facts.operations[save].dest
                && facts.operands[op.arguments.range()].contains(&binding.dest)),
            "the real save result is flatMapped into the distinct after callback"
        );
    }
}

#[test]
fn actual_jvm_order_and_dormant_closure_observations_are_frozen() {
    let expected = [
        "dormant-before:0",
        "active:first,clue:guard,load:3,check:3,save:3,after:3,finish",
        "dormant-invoked:clue:dormant,load:99,check:99,save:99,after:99",
    ];
    assert_eq!(
        std::fs::read_to_string(fixture().join("execution.log"))
            .unwrap()
            .lines()
            .collect::<Vec<_>>(),
        expected
    );
    let row: serde_json::Value =
        serde_json::from_slice(&std::fs::read(fixture().join("documents.jsonl")).unwrap()).unwrap();
    assert_eq!(row["document"]["synthetics"].as_array().unwrap().len(), 22);
    let log = std::fs::read_to_string(fixture().join("scalatest.log")).unwrap();
    assert!(log.contains("Suites: completed 2, aborted 0"));
    assert!(log.contains("Tests: succeeded 0, failed 0"));
}

#[test]
fn possible_future_work_proves_active_impact_with_guards_without_eager_dormant_execution() {
    let facts = with_future_arity();
    let graph = selector_graph_build::build(&facts, &Default::default()).unwrap();
    let class = |name| facts.find_symbol(&format!("forcase/{name}#")).unwrap();
    let active = graph.node_for_symbol(class("ActiveSuite")).unwrap();
    let dormant = graph.node_for_symbol(class("DormantSuite")).unwrap();
    let roots = [
        selector_solve::ExecutionRoot {
            node: active,
            receiver: class("ActiveSuite"),
        },
        selector_solve::ExecutionRoot {
            node: dormant,
            receiver: class("DormantSuite"),
        },
    ];
    // Known map/flatMap may execute their certified callback, while scheduling
    // and Future results remain explicitly incomplete. Dormant work stays inert.
    let options = selector_solve::SolveOptions {
        workers: 2,
        memory_budget_bytes: 64 * 1024 * 1024,
        max_contexts: 10_000,
        max_steps: 1_000_000,
        execution_roots: Some(roots.into()),
        ..Default::default()
    };
    for target in ["save", "after"] {
        let changed = graph
            .node_for_symbol(
                facts
                    .find_symbol(&format!("forcase/Pipeline#{target}()."))
                    .unwrap(),
            )
            .unwrap();
        let mut baseline: Option<selector_result::AnalysisResult> = None;
        for workers in [1, 4] {
            let result = selector_solve::analyze(
                &facts,
                &graph,
                &[changed],
                &selector_solve::SolveOptions {
                    workers,
                    ..options.clone()
                },
            )
            .unwrap();
            assert_ne!(result.completion, Completion::ResourceLimited);
            assert!(
                result.contains(active),
                "inherited {target} work must have an actual impact proof; guards {:?}",
                result.guarded_roots
            );
            assert!(result.guarded_roots.contains(&active));
            assert!(
                result
                    .evidence
                    .guard_causes
                    .iter()
                    .any(|cause| cause.root == active),
                "possible callback activation must keep an explicit incomplete boundary"
            );
            assert!(
                !result.contains(dormant),
                "stored dormant comprehension is not an execution proof"
            );
            if let Some(previous) = &baseline {
                assert_eq!(result.affected, previous.affected);
                assert_eq!(result.witnesses, previous.witnesses);
                assert_eq!(result.derived_edges, previous.derived_edges);
                assert_eq!(result.guarded_roots, previous.guarded_roots);
                assert_eq!(result.obligations, previous.obligations);
                assert_eq!(result.evidence.guard_causes, previous.evidence.guard_causes);
            }
            baseline = Some(result);
        }
    }
}
