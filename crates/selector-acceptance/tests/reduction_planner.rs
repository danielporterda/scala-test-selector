//! Potential-root planning must preserve the actual compiler-backed impact proof.
//! Unknown callback/heap frontiers may retain work; never count those as pruning.
#[path = "support/reduction_fixture.rs"]
mod fixture;
use fixture::{root, snapshot};
use selector_facts::FactSnapshot;
use selector_graph::ProgramGraph;
use selector_plan::{PlanSeeds, plan};
use selector_solve::{
    AnalysisSeeds, ExecutionRoot, SolveOptions, SolverRuntime, analyze_typed_with_runtime,
};
use selector_types::Completion;

fn run(
    base: &(FactSnapshot, ProgramGraph),
    head: &(FactSnapshot, ProgramGraph),
    path: &str,
    workers: usize,
    planned: bool,
) -> serde_json::Value {
    let seeds =
        selector_select::changed_seeds(&base.0, &base.1, &head.0, &head.1, &[path]).unwrap();
    let base_plan = plan(
        &base.0,
        &base.1,
        PlanSeeds {
            execution: &seeds.base,
            declarations: &seeds.base_compile,
            unscoped: seeds.conservative,
        },
    )
    .unwrap();
    let head_plan = plan(
        &head.0,
        &head.1,
        PlanSeeds {
            execution: &seeds.head,
            declarations: &seeds.head_compile,
            unscoped: seeds.conservative,
        },
    )
    .unwrap();
    for (plan, facts, graph) in [
        (&base_plan, &base.0, &base.1),
        (&head_plan, &head.0, &head.1),
    ] {
        assert_eq!(
            plan.roots.len() + plan.excluded_roots().len(),
            facts.suites.len()
        );
        for node in plan.excluded_roots() {
            assert!(!plan.roots.iter().any(|root| root.node == *node));
            assert!(plan.cert_identity(*node).is_some());
            assert_eq!(plan.snapshot(), graph.identity);
            assert_eq!(plan.facts_identity(), facts.identity);
        }
    }
    let options = SolveOptions {
        workers,
        max_steps: 1_000_000,
        max_contexts: 10_000,
        memory_budget_bytes: 64 * 1024 * 1024,
        ..Default::default()
    };
    let runtime = SolverRuntime::new(&options).unwrap();
    let analyze = |facts: &FactSnapshot,
                   graph: &ProgramGraph,
                   execution: &[_],
                   declarations: &[_],
                   plan: &selector_plan::CandidatePlan| {
        let mut options = options.clone();
        if planned {
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
        }
        analyze_typed_with_runtime(
            facts,
            graph,
            AnalysisSeeds {
                execution,
                declarations,
            },
            &options,
            &runtime,
        )
        .unwrap()
    };
    let before = analyze(
        &base.0,
        &base.1,
        &seeds.base,
        &seeds.base_compile,
        &base_plan,
    );
    let after = analyze(
        &head.0,
        &head.1,
        &seeds.head,
        &seeds.head_compile,
        &head_plan,
    );
    let result = if planned {
        selector_select::select_with_plan(
            &base.0,
            &base.1,
            &head.0,
            &head.1,
            seeds,
            Some(before),
            after,
            Some(&base_plan),
            &head_plan,
        )
    } else {
        selector_select::select(
            &base.0,
            &base.1,
            &head.0,
            &head.1,
            seeds,
            Some(before),
            after,
        )
    }
    .unwrap();
    assert_eq!(result.completion, Completion::Complete);
    let mut bytes = Vec::new();
    selector_report::write_json(
        &mut bytes,
        &selector_report::ReportSnapshots {
            base_facts: &base.0,
            base_graph: &base.1,
            head_facts: &head.0,
            head_graph: &head.1,
        },
        &result,
    )
    .unwrap();
    let mut report: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    for side in ["base", "head"] {
        report[side].as_object_mut().unwrap().remove("metrics");
        // The admitted root frontier intentionally differs. Every actual retained
        // context/atom/capture/witness/compilation proof remains in the comparison.
        report[side]["evidence"]
            .as_object_mut()
            .unwrap()
            .remove("requested_roots");
    }
    report
}

#[test]
fn genuine_planned_and_all_root_fixed_points_have_the_same_complete_impact_evidence() {
    for workers in [1, 4] {
        let base = snapshot(&root().join("fixtures/execution-smoke/base"), workers);
        for (directory, path, expectations) in [
            (
                "fixtures/execution-smoke/head",
                "src/executioncase/Changed.scala",
                "tools/dev-cases/execution-body-expected.json",
            ),
            (
                "fixtures/reduction-heldout/head",
                "src/executioncase/Unchanged.scala",
                "tools/dev-cases/heldout-helper-expected.json",
            ),
        ] {
            let head = snapshot(&root().join(directory), workers);
            let all = run(&base, &head, path, workers, false);
            let planned = run(&base, &head, path, workers, true);
            assert_eq!(planned["suites"], all["suites"]);
            let expected: serde_json::Value =
                serde_json::from_slice(&std::fs::read(root().join(expectations)).unwrap()).unwrap();
            let mut required: Vec<_> = expected["required"]
                .as_array()
                .unwrap()
                .iter()
                .map(|row| row.as_str().unwrap())
                .collect();
            let mut selected: Vec<_> = planned["suites"]
                .as_array()
                .unwrap()
                .iter()
                .map(|row| row["name"].as_str().unwrap())
                .collect();
            required.sort_unstable();
            selected.sort_unstable();
            assert_eq!(selected, required);
            for side in ["base", "head"] {
                assert_eq!(
                    planned[side], all[side],
                    "{directory}, {workers}workers, {side}"
                );
            }
        }
    }
}
