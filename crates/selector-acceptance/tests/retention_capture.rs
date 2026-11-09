//! Static retention is a diagnostic about immutable guards, not test exclusion
//! authority. These are explicit genuine callable roots, not a CI catalogue.
use selector_extract::{ExtractOptions, import_capture};
use selector_plan::PlannedRoot;
use selector_plan::retention::{RetentionLimits, precheck};
use selector_solve::{ExecutionRoot, QuerySession, SolveOptions, SolverRuntime};
use selector_types::*;
use std::path::PathBuf;

#[test]
fn genuine_eager_source_guards_have_valid_paths_without_changing_query_outcomes() {
    let fixture =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/anonymous-construction");
    let temporary = tempfile::tempdir().unwrap();
    let mut facts = import_capture(
        &fixture.join("documents.jsonl"),
        Some(&fixture.join("syntax.jsonl")),
        &ExtractOptions {
            workers: 1,
            ..Default::default()
        },
    )
    .unwrap();
    facts.identity =
        selector_facts::codec::write(&temporary.path().join("facts.bin"), &facts).unwrap();
    let mut graph = selector_graph_build::build(&facts, &Default::default()).unwrap();
    graph.identity =
        selector_graph::codec::write(&temporary.path().join("graph.bin"), &graph).unwrap();
    let roots: Vec<_> = ["ClassActive", "BodyActive", "Dormant"]
        .into_iter()
        .map(|name| {
            let receiver = facts
                .find_symbol(&format!("anonymouscase/{name}#"))
                .unwrap();
            PlannedRoot {
                node: graph.node_for_symbol(receiver).unwrap(),
                receiver,
            }
        })
        .collect();
    let options = SolveOptions {
        workers: 1,
        memory_budget_bytes: 64 * 1024 * 1024,
        max_contexts: 10_000,
        max_steps: 1_000_000,
        execution_roots: Some(
            roots
                .iter()
                .map(|root| ExecutionRoot {
                    node: root.node,
                    receiver: root.receiver,
                })
                .collect::<Vec<_>>()
                .into(),
        ),
        ..Default::default()
    };
    let runtime = SolverRuntime::new(&options).unwrap();
    let mut session = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
    let seed = graph
        .node_for_symbol(facts.find_symbol("anonymouscase/Effects.note().").unwrap())
        .unwrap();
    let mut before = session.analyze(&[seed]).unwrap();
    assert_ne!(before.completion, Completion::ResourceLimited);
    let counters = session.work_counters();
    let contexts = session.context_count();
    let owned = session.owned_bytes();
    let history: Vec<_> = session.first_runtime_issue_sites().collect();
    let certificate = precheck(&facts, &graph, &roots, &RetentionLimits::default()).unwrap();
    certificate.validate(&facts, &graph).unwrap();
    assert_eq!(certificate.roots().len(), roots.len());
    for row in &certificate.roots()[..2] {
        let guard = row
            .guard
            .expect("the actual eager unsupported anonymous body has a static source guard");
        let issue = &graph.issues[guard.issue as usize];
        assert_eq!(issue.kind, IssueKind::UnknownExecution);
        assert!(
            facts.text(issue.detail).contains(
                "anonymous construction lacks a complete compiler-owned initializer recipe"
            )
        );
        let path = certificate.path(row).unwrap();
        assert!(
            !path.is_empty(),
            "the class reaches its exact eager member recipe"
        );
        assert!(
            path.iter()
                .all(|edge| graph.edges[edge.index()].kind == EdgeKind::Initialize)
        );
        assert!(before.guarded_roots.contains(&row.root.node));
    }
    assert!(
        certificate.roots()[2].guard.is_none(),
        "the diagnostic must not follow dormant callback construction into its deferred body"
    );
    assert_eq!(certificate.eligible_roots(), 2);
    assert!(!certificate.all_roots_known_kept());
    assert_eq!(session.work_counters(), counters);
    assert_eq!(session.context_count(), contexts);
    assert_eq!(session.owned_bytes(), owned);
    assert_eq!(
        session.first_runtime_issue_sites().collect::<Vec<_>>(),
        history
    );
    let mut after = session.analyze(&[seed]).unwrap();
    // Normalize only the documented timing/work metrics; retain every affected
    // node, guard, obligation, detached context/capture and witness field.
    before.metrics = selector_result::AnalysisMetrics::default();
    after.metrics = selector_result::AnalysisMetrics::default();
    assert_eq!(format!("{before:?}"), format!("{after:?}"));
}
