//! Genuine lexical callback shapes are independent even after a four-variant
//! argument budget. Captured data and opaque actuals remain conservative.
use selector_solve::{
    AnalysisSeeds, ContextPolicy, ExecutionRoot, QuerySession, SolveOptions, SolverRuntime,
};
use selector_types::*;
use std::path::PathBuf;
#[path = "support/reduction_fixture.rs"]
mod fixture;
fn directory() -> PathBuf {
    fixture::root().join("fixtures/callback-variants")
}

#[test]
fn independent_jvm_mutation_changes_only_the_sixth_lexical_and_captured_callbacks() {
    for (side, value) in [("base", 41), ("head", 42)] {
        assert_eq!(
            std::fs::read_to_string(directory().join(side).join("execution.log")).unwrap(),
            format!("values:1,2,3,4,5,{value},10,20,30,40,50,{value},99\n")
        );
        let runner = std::fs::read_to_string(directory().join(side).join("scalatest.log")).unwrap();
        assert!(runner.contains("Suites: completed 13, aborted 0"));
        assert!(runner.contains("Tests: succeeded 0, failed 0"));
    }
    // The oracle is real construction order and values, not analysis output.
    for name in ["Shared.scala", "Suites.scala"] {
        assert_eq!(
            std::fs::read(directory().join("base/src/callbackcase").join(name)).unwrap(),
            std::fs::read(directory().join("head/src/callbackcase").join(name)).unwrap()
        );
    }
}

fn selected(workers: usize, policy: ContextPolicy, cohort: &str) -> (serde_json::Value, u64) {
    let snapshot = |side: &str| {
        let (mut facts, _) = fixture::snapshot(&directory().join(side), workers);
        // Explicit runnable cohorts isolate each mechanism. All compiler bodies
        // remain admitted; other suite declarations are dormant in this query.
        facts.suites.retain(|suite| {
            facts
                .strings
                .get(suite.name)
                .starts_with(&format!("callbackcase.{cohort}"))
        });
        let saved = tempfile::tempdir().unwrap();
        let path = saved.path().join("facts.bin");
        selector_facts::codec::write(&path, &facts).unwrap();
        let facts = selector_facts::codec::read(&path).unwrap();
        let graph = selector_graph_build::build(
            &facts,
            &selector_graph_build::BuildOptions {
                workers,
                include_models: true,
            },
        )
        .unwrap();
        (facts, graph)
    };
    let (base, bg) = snapshot("base");
    let (head, hg) = snapshot("head");
    let seeds =
        selector_select::changed_seeds(&base, &bg, &head, &hg, &["src/callbackcase/Changed.scala"])
            .unwrap();
    assert!(!seeds.conservative);
    let bp = selector_plan::plan(
        &base,
        &bg,
        selector_plan::PlanSeeds {
            execution: &seeds.base,
            declarations: &seeds.base_compile,
            unscoped: false,
        },
    )
    .unwrap();
    let hp = selector_plan::plan(
        &head,
        &hg,
        selector_plan::PlanSeeds {
            execution: &seeds.head,
            declarations: &seeds.head_compile,
            unscoped: false,
        },
    )
    .unwrap();
    let options = SolveOptions {
        workers,
        memory_budget_bytes: 128 * 1024 * 1024,
        max_contexts: 20_000,
        max_steps: 2_000_000,
        context_policy: policy,
        ..Default::default()
    };
    let runtime = SolverRuntime::new(&options).unwrap();
    let analyze = |facts: &selector_facts::FactSnapshot,
                   graph: &selector_graph::ProgramGraph,
                   plan: &selector_plan::CandidatePlan,
                   execution: &[NodeId],
                   declarations: &[NodeId]| {
        let mut options = options.clone();
        options.execution_roots = Some(
            plan.roots
                .iter()
                .map(|root| ExecutionRoot {
                    node: root.node,
                    receiver: root.receiver,
                })
                .collect::<Vec<_>>()
                .into(),
        );
        let mut session = QuerySession::with_runtime(facts, graph, &options, &runtime).unwrap();
        let result = session
            .analyze_typed(AnalysisSeeds {
                execution,
                declarations,
            })
            .unwrap();
        assert_ne!(result.completion, Completion::ResourceLimited);
        (result, session.work_counters().widened_contexts)
    };
    let (before, bw) = analyze(&base, &bg, &bp, &seeds.base, &seeds.base_compile);
    let (after, hw) = analyze(&head, &hg, &hp, &seeds.head, &seeds.head_compile);
    let result = selector_select::select_with_plan(
        &base,
        &bg,
        &head,
        &hg,
        seeds,
        Some(before),
        after,
        Some(&bp),
        &hp,
    )
    .unwrap();
    let mut bytes = Vec::new();
    selector_report::write_json(
        &mut bytes,
        &selector_report::ReportSnapshots {
            base_facts: &base,
            base_graph: &bg,
            head_facts: &head,
            head_graph: &hg,
        },
        &result,
    )
    .unwrap();
    let mut report: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    for side in ["base", "head"] {
        report[side].as_object_mut().unwrap().remove("metrics");
    }
    (report, bw + hw)
}
fn decision<'a>(report: &'a serde_json::Value, name: &str) -> &'a serde_json::Value {
    report["suites"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["name"] == name)
        .unwrap()
}
#[test]
fn bounded_four_keeps_six_distinct_callback_codes_separate_with_unknown_and_capture_safety() {
    let (one, _) = selected(
        1,
        ContextPolicy::BoundedArguments {
            max_variants_per_receiver: 4,
        },
        "Lexical",
    );
    let (four, _) = selected(
        4,
        ContextPolicy::BoundedArguments {
            max_variants_per_receiver: 4,
        },
        "Lexical",
    );
    assert_eq!(
        one, four,
        "all native proof/context/capture/heap-origin fields except metrics agree across workers"
    );
    let selected_names: Vec<_> = one["suites"]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| row["name"].as_str().unwrap())
        .collect();
    assert_eq!(
        selected_names,
        ["callbackcase.Lexical6Suite"],
        "six distinct callback codes must not cross a four-variant argument budget"
    );
    let (captured, widened) = selected(
        1,
        ContextPolicy::BoundedArguments {
            max_variants_per_receiver: 4,
        },
        "Captured",
    );
    assert!(
        captured["suites"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| row["name"] == "callbackcase.Captured6Suite"),
        "same-code capture widening may not lose the changed actual"
    );
    assert!(
        widened > 0,
        "six same-code/different-capture frames exercise bounded data joining"
    );
    let (unknown, _) = selected(
        1,
        ContextPolicy::BoundedArguments {
            max_variants_per_receiver: 4,
        },
        "Unknown",
    );
    assert!(
        decision(&unknown, "callbackcase.UnknownSuite")["guarded"]
            .as_bool()
            .unwrap(),
        "an actually opaque callback stays guarded"
    );
}
