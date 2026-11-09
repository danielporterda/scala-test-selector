//! Current-local diagnostics do not replace historical conservative selection.
//! Reuses an immutable genuine compiler/JVM fixture; no new execution oracle.
use selector_solve::{
    ContextPolicy, ExecutionRoot, QuerySession, SolveOptions, SolverRuntime,
    finalization::CurrentAuditOptions,
};
#[path = "support/reduction_fixture.rs"]
mod fixture;

#[test]
fn current_local_audit_of_genuine_opaque_callback_is_bounded_and_read_only() {
    let (facts, graph) =
        fixture::snapshot(&fixture::root().join("fixtures/callback-variants/head"), 1);
    let symbol = facts.find_symbol("callbackcase/UnknownSuite#").unwrap();
    let node = graph.node_for_symbol(symbol).unwrap();
    let options = SolveOptions {
        workers: 1,
        memory_budget_bytes: 128 * 1024 * 1024,
        max_contexts: 20_000,
        max_steps: 2_000_000,
        context_policy: ContextPolicy::BoundedArguments {
            max_variants_per_receiver: 4,
        },
        execution_roots: Some(
            vec![ExecutionRoot {
                node,
                receiver: symbol,
            }]
            .into(),
        ),
        ..Default::default()
    };
    let runtime = SolverRuntime::new(&options).unwrap();
    let mut session = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
    let result = session.analyze(&[]).unwrap();
    assert!(
        result.guarded_roots.contains(&node),
        "the actual opaque callback remains conservative"
    );
    let counters = session.work_counters();
    let contexts = session.context_count();
    let owned = session.owned_bytes();
    let history: Vec<_> = session.first_runtime_issue_sites().collect();
    assert!(!history.is_empty());
    let census = session.finalization_census(&result).unwrap();
    assert!(census.fixed_point_reached);
    assert_eq!(census.requested_root_nodes, 1);
    assert_eq!(census.reported_guarded_requested_root_nodes, 1);
    assert_eq!(census.guard_free_fixed_point_requested_root_nodes, Some(0));
    assert_eq!(census.retained_contexts, contexts);
    assert_eq!(census.historical_first_runtime_sites, history.len());
    assert!(!census.current_transfer_failures_reconstructed);
    let audit = session
        .audit_current_local_transfers(CurrentAuditOptions::default())
        .unwrap();
    assert!(
        audit.complete,
        "genuine fixture fits the explicit small diagnostic budget"
    );
    assert_eq!(audit.audited_contexts, contexts);
    assert_eq!(
        audit.contexts_with_current_local_issues + audit.contexts_without_current_local_issues,
        contexts
    );
    assert!(audit.contexts_with_current_local_issues > 0);
    assert!(!audit.first_current_issue_by_reason.is_empty());
    assert!(!audit.selection_authority && !audit.root_path_proof);
    assert_eq!(session.work_counters(), counters);
    assert_eq!(session.context_count(), contexts);
    assert_eq!(session.owned_bytes(), owned);
    assert_eq!(
        session.first_runtime_issue_sites().collect::<Vec<_>>(),
        history
    );
    let skipped = session
        .audit_current_local_transfers(CurrentAuditOptions {
            max_contexts: 0,
            ..Default::default()
        })
        .unwrap();
    assert!(!skipped.complete);
    assert_eq!(skipped.audited_contexts, 0);
    assert!(!skipped.selection_authority && !skipped.root_path_proof);
    assert_eq!(session.work_counters(), counters);
    assert_eq!(session.owned_bytes(), owned);
    assert!(result.guarded_roots.contains(&node));
}
