//! Resume genuine compiler/bytecode input across worker counts. Compare all
//! retained proof fields; fixture expectations remain outside graph admission.
#[path = "support/reduction_fixture.rs"]
mod fixture;
use fixture::{root, snapshot};
use selector_result::AnalysisResult;
use selector_solve::{
    CensusOptions, QuerySession, SolveControl, SolveOptions, SolverRuntime, StopReason,
};
use selector_types::{Completion, ContentHash};
use std::sync::Arc;

fn proof(
    facts: &selector_facts::FactSnapshot,
    graph: &selector_graph::ProgramGraph,
    seed: selector_types::NodeId,
    analysis: AnalysisResult,
) -> serde_json::Value {
    assert_eq!(analysis.completion, Completion::Complete);
    assert!(!analysis.unscoped_uncertainty);
    let result = selector_select::select(
        facts,
        graph,
        facts,
        graph,
        selector_select::ChangeSeeds {
            head: vec![seed],
            ..Default::default()
        },
        None,
        analysis,
    )
    .unwrap();
    let mut bytes = Vec::new();
    selector_report::write_json(
        &mut bytes,
        &selector_report::ReportSnapshots {
            base_facts: facts,
            base_graph: graph,
            head_facts: facts,
            head_graph: graph,
        },
        &result,
    )
    .unwrap();
    let mut json: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    json["head"].as_object_mut().unwrap().remove("metrics");
    assert_eq!(json["suites"].as_array().unwrap().len(), 1);
    assert_eq!(json["suites"][0]["name"], "executioncase.AffectedSuite");
    assert_eq!(json["suites"][0]["guarded"], false);
    json
}

#[test]
fn genuine_paused_and_cancelled_queries_resume_with_identical_cross_worker_full_proofs() {
    let (facts, graph) = snapshot(&root().join("fixtures/execution-smoke/head"), 1);
    let seed = graph
        .node_for_symbol(facts.find_symbol("executioncase/Changed.value().").unwrap())
        .unwrap();
    let producer = ContentHash([0x73; 32]);
    let options = SolveOptions {
        workers: 1,
        memory_budget_bytes: 64 * 1024 * 1024,
        max_contexts: 10_000,
        max_steps: 1_000_000,
        census: CensusOptions {
            capacity: 4,
            evaluation_stride: 1,
        },
        ..Default::default()
    };
    let mut uninterrupted = QuerySession::new(&facts, &graph, &options).unwrap();
    let baseline = proof(
        &facts,
        &graph,
        seed,
        uninterrupted.analyze(&[seed]).unwrap(),
    );
    drop(uninterrupted);
    for (write_workers, read_workers, cancel) in [(1, 4, false), (4, 1, false), (1, 4, true)] {
        let control = Arc::new(SolveControl::default());
        if cancel {
            control.cancel();
        } else {
            control.checkpoint_after_round(2);
        }
        let paused_options = SolveOptions {
            workers: write_workers,
            shard_count: write_workers,
            control: Some(control),
            ..options.clone()
        };
        let mut paused = QuerySession::new(&facts, &graph, &paused_options).unwrap();
        let partial = paused.analyze(&[seed]).unwrap();
        drop(partial);
        assert_eq!(
            paused.stop_reason(),
            Some(if cancel {
                StopReason::Cancelled
            } else {
                StopReason::CheckpointRequested
            })
        );
        assert!(paused.work_census().len() <= 4);
        if !cancel {
            assert!(paused.context_count() > 0);
        }
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("query.continuation");
        paused.save_checkpoint(&path, producer).unwrap();
        drop(paused);
        let resumed_options = SolveOptions {
            workers: read_workers,
            shard_count: read_workers,
            ..options.clone()
        };
        let runtime = SolverRuntime::new(&resumed_options).unwrap();
        let mut resumed = QuerySession::from_checkpoint(
            &facts,
            &graph,
            &resumed_options,
            &runtime,
            &path,
            producer,
        )
        .unwrap();
        resumed.resume().unwrap();
        assert_eq!(resumed.stop_reason(), None);
        assert_eq!(
            proof(&facts, &graph, seed, resumed.analyze(&[seed]).unwrap()),
            baseline,
            "{write_workers} -> {read_workers}, cancelled={cancel}"
        );
        assert!(
            QuerySession::from_checkpoint(
                &facts,
                &graph,
                &resumed_options,
                &runtime,
                &path,
                ContentHash([0x74; 32])
            )
            .is_err(),
            "producer mismatch must reject before admission"
        );
        let mut bytes = std::fs::read(&path).unwrap();
        *bytes.last_mut().unwrap() ^= 1;
        let corrupt_path = directory.path().join("corrupt.continuation");
        std::fs::write(&corrupt_path, bytes).unwrap();
        assert!(
            QuerySession::from_checkpoint(
                &facts,
                &graph,
                &resumed_options,
                &runtime,
                &corrupt_path,
                producer
            )
            .is_err(),
            "corrupt continuation must not become runnable"
        );
    }
}
