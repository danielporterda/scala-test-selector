//! The exact v623 unstable occurrence and genuine, independently run consumers.
//! The retained failure was an evidence classification difference, not a saved
//! final-suite oracle. The two-suite oracle below comes from JVM observations.
use selector_extract::{ExtractOptions, import_capture};
use selector_facts::FactSnapshot;
use selector_graph::ProgramGraph;
use selector_types::*;
use serde_json::Value;
use std::path::{Path, PathBuf};

const ANNOTATION: &str = "java/lang/SuppressWarnings#";
const RETAINED_URI: &str = "canton/community/ledger/ledger-json-api/src/main/scala/com/digitalasset/canton/http/json/v2/JsIdentityProviderService.scala";

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/source-annotations")
}

fn imported(directory: &Path, workers: usize, suites: bool) -> FactSnapshot {
    import_capture(
        &directory.join("documents.jsonl"),
        Some(&directory.join("syntax.jsonl")),
        &ExtractOptions {
            workers,
            catalogue: suites.then(|| directory.join("catalogue.json")),
            ..Default::default()
        },
    )
    .unwrap()
}

fn assert_head_is_metadata(facts: &FactSnapshot, graph: &ProgramGraph) {
    let annotation = facts.find_symbol(ANNOTATION).unwrap();
    assert!(
        facts
            .occurrences
            .iter()
            .any(|row| row.symbol == annotation && row.role == 1)
    );
    assert!(
        facts
            .relations
            .iter()
            .any(|row| row.target == annotation && row.kind == RelationKind::Annotation)
    );
    assert!(
        facts.operations.iter().all(|row| row.target != annotation),
        "a SOURCE annotation head cannot become an initializer/call operation"
    );
    if let Some(node) = graph.node_for_symbol(annotation) {
        assert!(
            graph
                .edges
                .iter()
                .all(|edge| edge.target != node || !edge.kind.is_execution()),
            "metadata must not create an execution witness"
        );
    }
}

#[test]
fn exact_v623_occurrence_118_stays_metadata_across_repeat_and_parallel_imports() {
    let directory = fixture().join("v623");
    let expected: Value =
        serde_json::from_slice(&std::fs::read(fixture().join("manifest.json")).unwrap()).unwrap();
    assert_eq!(expected["retained_v623"]["occurrence"], 118);
    assert_eq!(expected["retained_v623"]["symbol"], ANNOTATION);
    let saved = tempfile::tempdir().unwrap();
    let mut baseline = None;
    for (repeat, workers) in [1, 4, 1, 4].into_iter().enumerate() {
        let facts = imported(&directory, workers, false);
        assert_eq!(facts.files.len(), 1);
        let file = facts.files[0];
        assert_eq!(facts.text(file.path), RETAINED_URI);
        assert_eq!(
            file.flags & (SOURCE_VERIFIED | SYNTAX_VERIFIED),
            SOURCE_VERIFIED | SYNTAX_VERIFIED
        );
        assert_eq!(
            file.source_hash.to_string(),
            expected["retained_v623"]["source_sha256"].as_str().unwrap()
        );
        let source = facts.text(file.source);
        let line_start = source
            .split_inclusive('\n')
            .take(24)
            .map(str::len)
            .sum::<usize>();
        let span = Span {
            start: (line_start + 1) as u32,
            end: (line_start + 17) as u32,
        };
        assert_eq!(
            &source[span.start as usize..span.end as usize],
            "SuppressWarnings"
        );
        let symbol = facts.find_symbol(ANNOTATION).unwrap();
        assert_eq!(
            facts
                .occurrences
                .iter()
                .filter(|row| row.symbol == symbol && row.role == 1 && row.span == span)
                .count(),
            1,
            "the exact real compiler occurrence, rather than a fabricated metadata row, must survive"
        );
        let graph = selector_graph_build::build(
            &facts,
            &selector_graph_build::BuildOptions {
                workers,
                include_models: false,
            },
        )
        .unwrap();
        assert_head_is_metadata(&facts, &graph);
        let fact_id =
            selector_facts::codec::write(&saved.path().join(format!("facts-{repeat}.bin")), &facts)
                .unwrap();
        let graph_id =
            selector_graph::codec::write(&saved.path().join(format!("graph-{repeat}.bin")), &graph)
                .unwrap();
        if let Some(previous) = baseline {
            assert_eq!(
                (fact_id, graph_id),
                previous,
                "classification/evidence changed after repeated import with {workers} workers"
            );
        } else {
            baseline = Some((fact_id, graph_id));
        }
    }
}

fn enriched(directory: &Path, workers: usize) -> (FactSnapshot, ProgramGraph) {
    enrich_facts(imported(directory, workers, true), directory, workers)
}

fn enrich_facts(
    mut facts: FactSnapshot,
    directory: &Path,
    workers: usize,
) -> (FactSnapshot, ProgramGraph) {
    selector_graph_build::source_recipes::augment_source_recipes(&mut facts).unwrap();
    let mut binary = selector_graph_build::binary_inputs::load_binary_manifest(
        &directory.join("binary.json"),
        &facts,
    )
    .unwrap();
    selector_graph_build::binary_inputs::augment_binary_facts(&mut facts, &mut binary).unwrap();
    let saved = tempfile::tempdir().unwrap();
    let fact_path = saved.path().join("facts.bin");
    selector_facts::codec::write(&fact_path, &facts).unwrap();
    let facts = selector_facts::codec::read(&fact_path).unwrap();
    let graph = selector_graph_build::build(
        &facts,
        &selector_graph_build::BuildOptions {
            workers,
            include_models: true,
        },
    )
    .unwrap();
    let graph_path = saved.path().join("graph.bin");
    selector_graph::codec::write(&graph_path, &graph).unwrap();
    let graph = selector_graph::codec::read(&graph_path).unwrap();
    assert_head_is_metadata(&facts, &graph);
    (facts, graph)
}

#[test]
fn source_annotated_service_change_selects_actual_affected_suite_and_excludes_independent_suite() {
    let expected: Value =
        serde_json::from_slice(&std::fs::read(fixture().join("expected.json")).unwrap()).unwrap();
    // These observations were generated by an independent JVM program, before
    // querying Rust. Both constructors also completed under ScalaTest Runner.
    for side in ["base", "head"] {
        let values = expected["independent_observed_values"][side]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| v.as_i64().unwrap().to_string())
            .collect::<Vec<_>>()
            .join(",");
        let observed = std::fs::read_to_string(fixture().join(side).join("execution.log")).unwrap();
        assert_eq!(
            observed.lines().next(),
            Some(format!("observed:{values}").as_str())
        );
        assert!(
            std::fs::read_to_string(fixture().join(side).join("scalatest.log"))
                .unwrap()
                .contains("Suites: completed 2, aborted 0")
        );
    }
    let mut baseline = None;
    for workers in [1, 4] {
        let (base_facts, base_graph) = enriched(&fixture().join("base"), workers);
        let (head_facts, head_graph) = enriched(&fixture().join("head"), workers);
        let seeds = selector_select::changed_seeds(
            &base_facts,
            &base_graph,
            &head_facts,
            &head_graph,
            &["src/annotationcase/Service.scala"],
        )
        .unwrap();
        assert!(!seeds.conservative);
        let options = selector_solve::SolveOptions {
            workers,
            ..Default::default()
        };
        let runtime = selector_solve::SolverRuntime::new(&options).unwrap();
        let base = selector_solve::analyze_typed_with_runtime(
            &base_facts,
            &base_graph,
            selector_solve::AnalysisSeeds {
                execution: &seeds.base,
                declarations: &seeds.base_compile,
            },
            &options,
            &runtime,
        )
        .unwrap();
        let head = selector_solve::analyze_typed_with_runtime(
            &head_facts,
            &head_graph,
            selector_solve::AnalysisSeeds {
                execution: &seeds.head,
                declarations: &seeds.head_compile,
            },
            &options,
            &runtime,
        )
        .unwrap();
        let selected = selector_select::select(
            &base_facts,
            &base_graph,
            &head_facts,
            &head_graph,
            seeds,
            Some(base),
            head,
        )
        .unwrap();
        let mut bytes = Vec::new();
        selector_report::write_json(
            &mut bytes,
            &selector_report::ReportSnapshots {
                base_facts: &base_facts,
                base_graph: &base_graph,
                head_facts: &head_facts,
                head_graph: &head_graph,
            },
            &selected,
        )
        .unwrap();
        let mut report: Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(report["completion"], expected["completion"], "{report:#}");
        let names: Vec<_> = report["suites"]
            .as_array()
            .unwrap()
            .iter()
            .map(|s| s["name"].as_str().unwrap())
            .collect();
        assert_eq!(names, ["annotationcase.AffectedSuite"]);
        assert!(!names.contains(&"annotationcase.UnaffectedSuite"));
        assert!(
            report["suites"]
                .as_array()
                .unwrap()
                .iter()
                .all(|s| s["guarded"] == false)
        );
        assert!(report["obligations"].as_array().unwrap().is_empty());
        for side in ["base", "head"] {
            let contexts = report[side]["evidence"]["contexts"].as_array().unwrap();
            assert!(
                contexts
                    .iter()
                    .any(|c| c["symbol"] == "annotationcase/Service#value().")
            );
            assert!(contexts.iter().all(|c| c["symbol"] != ANNOTATION));
            assert!(report[side]["guarded_roots"].as_array().unwrap().is_empty());
            report[side].as_object_mut().unwrap().remove("metrics");
        }
        if let Some(previous) = &baseline {
            assert_eq!(
                &report, previous,
                "full retained evidence differs with {workers} workers"
            );
        } else {
            baseline = Some(report);
        }
    }
}

#[test]
fn source_annotation_only_edit_keeps_compile_metadata_and_excludes_both_execution_suites() {
    let directory = fixture();
    assert_eq!(
        std::fs::read(directory.join("base/service-bytecode.log")).unwrap(),
        std::fs::read(directory.join("annotation-only/service-bytecode.log")).unwrap(),
        "actual javap instructions are unchanged by the SOURCE argument edit"
    );
    assert_ne!(
        std::fs::read(directory.join("base/bytecode.jar")).unwrap(),
        std::fs::read(directory.join("annotation-only/bytecode.jar")).unwrap(),
        "ScalaSignature metadata still changes; whole classfiles are not interchangeable"
    );
    let observed =
        std::fs::read_to_string(directory.join("annotation-only/execution.log")).unwrap();
    assert_eq!(observed.lines().next(), Some("observed:41,7"));
    let mut baseline = None;
    for workers in [1, 4] {
        let (base_facts, base_graph) = enriched(&directory.join("base"), workers);
        let (head_facts, head_graph) = enriched(&directory.join("annotation-only"), workers);
        let seeds = selector_select::changed_seeds(
            &base_facts,
            &base_graph,
            &head_facts,
            &head_graph,
            &["src/annotationcase/Service.scala"],
        )
        .unwrap();
        assert!(!seeds.conservative);
        assert!(
            seeds.base.is_empty() && seeds.head.is_empty(),
            "metadata-only edit cannot become an executable initializer seed"
        );
        let options = selector_solve::SolveOptions {
            workers,
            ..Default::default()
        };
        let runtime = selector_solve::SolverRuntime::new(&options).unwrap();
        let base = selector_solve::analyze_typed_with_runtime(
            &base_facts,
            &base_graph,
            selector_solve::AnalysisSeeds {
                execution: &seeds.base,
                declarations: &seeds.base_compile,
            },
            &options,
            &runtime,
        )
        .unwrap();
        let head = selector_solve::analyze_typed_with_runtime(
            &head_facts,
            &head_graph,
            selector_solve::AnalysisSeeds {
                execution: &seeds.head,
                declarations: &seeds.head_compile,
            },
            &options,
            &runtime,
        )
        .unwrap();
        let selected = selector_select::select(
            &base_facts,
            &base_graph,
            &head_facts,
            &head_graph,
            seeds,
            Some(base),
            head,
        )
        .unwrap();
        let mut bytes = Vec::new();
        selector_report::write_json(
            &mut bytes,
            &selector_report::ReportSnapshots {
                base_facts: &base_facts,
                base_graph: &base_graph,
                head_facts: &head_facts,
                head_graph: &head_graph,
            },
            &selected,
        )
        .unwrap();
        let mut report: Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(report["completion"], "complete", "{report:#}");
        assert!(
            report["suites"].as_array().unwrap().is_empty(),
            "{report:#}"
        );
        assert!(report["obligations"].as_array().unwrap().is_empty());
        for side in ["base", "head"] {
            assert!(report[side]["guarded_roots"].as_array().unwrap().is_empty());
            assert!(
                report[side]["evidence"]["contexts"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .all(|context| context["symbol"] != ANNOTATION)
            );
            report[side].as_object_mut().unwrap().remove("metrics");
        }
        if let Some(previous) = &baseline {
            assert_eq!(&report, previous);
        } else {
            baseline = Some(report);
        }
    }
}

#[test]
fn source_annotation_positive_and_exclusion_proofs_survive_fresh_runtime_cache_reopens() {
    let mut baseline = None;
    for workers in [1, 4] {
        let (base_facts, base_graph) = enriched(&fixture().join("base"), workers);
        let (head_facts, head_graph) = enriched(&fixture().join("head"), workers);
        let cache = tempfile::tempdir().unwrap();
        let options = selector_solve::SolveOptions {
            workers,
            ..Default::default()
        };
        for repeat in 0..3 {
            // A fresh owner for every repeat cannot borrow the old query's heap,
            // subscriptions, mutable result vectors or worker scratch.
            let runtime = selector_solve::SolverRuntime::with_cache_directory(
                &options,
                cache.path(),
                ContentHash([143; 32]),
            )
            .unwrap();
            let seeds = selector_select::changed_seeds(
                &base_facts,
                &base_graph,
                &head_facts,
                &head_graph,
                &["src/annotationcase/Service.scala"],
            )
            .unwrap();
            let analyze = |facts: &FactSnapshot,
                           graph: &ProgramGraph,
                           execution: &[NodeId],
                           declarations: &[NodeId]| {
                let mut query =
                    selector_solve::QuerySession::with_runtime(facts, graph, &options, &runtime)
                        .unwrap();
                let reuse = query.reuse_metrics();
                if repeat > 0 {
                    assert!(
                        reuse.same_snapshot && reuse.loaded_contexts > 0,
                        "repeat must consume the actual persisted family, not silently recompute: {reuse:?}"
                    );
                }
                let result = query
                    .analyze_typed(selector_solve::AnalysisSeeds {
                        execution,
                        declarations,
                    })
                    .unwrap();
                if repeat > 0 {
                    assert_eq!(
                        result.metrics.edge_visits, 0,
                        "complete unchanged family must not be re-evaluated"
                    );
                }
                query.persist_completed().unwrap();
                result
            };
            let base = analyze(&base_facts, &base_graph, &seeds.base, &seeds.base_compile);
            let head = analyze(&head_facts, &head_graph, &seeds.head, &seeds.head_compile);
            let selected = selector_select::select(
                &base_facts,
                &base_graph,
                &head_facts,
                &head_graph,
                seeds,
                Some(base),
                head,
            )
            .unwrap();
            let mut bytes = Vec::new();
            selector_report::write_json(
                &mut bytes,
                &selector_report::ReportSnapshots {
                    base_facts: &base_facts,
                    base_graph: &base_graph,
                    head_facts: &head_facts,
                    head_graph: &head_graph,
                },
                &selected,
            )
            .unwrap();
            let mut report: Value = serde_json::from_slice(&bytes).unwrap();
            assert_eq!(report["completion"], "complete");
            assert_eq!(
                report["suites"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|suite| suite["name"].as_str().unwrap())
                    .collect::<Vec<_>>(),
                ["annotationcase.AffectedSuite"]
            );
            assert!(report["obligations"].as_array().unwrap().is_empty());
            for side in ["base", "head"] {
                assert!(report[side]["guarded_roots"].as_array().unwrap().is_empty());
                assert!(
                    report[side]["evidence"]["contexts"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .all(|context| context["symbol"] != ANNOTATION)
                );
                report[side].as_object_mut().unwrap().remove("metrics");
            }
            if let Some(previous) = &baseline {
                assert_eq!(
                    &report, previous,
                    "full proof changed after runtime reopen {repeat}, workers={workers}"
                );
            } else {
                baseline = Some(report);
            }
        }
    }
}

#[test]
fn absent_empty_and_stale_source_syntax_cannot_claim_the_annotation_exclusion() {
    let directory = fixture().join("annotation-only");
    for mode in ["absent", "empty", "stale"] {
        let temporary = tempfile::tempdir().unwrap();
        let broken_syntax = temporary.path().join("syntax.jsonl");
        let mut rows: Vec<Value> = std::fs::read_to_string(directory.join("syntax.jsonl"))
            .unwrap()
            .lines()
            .map(|line| serde_json::from_str(line).unwrap())
            .collect();
        let service = rows
            .iter_mut()
            .find(|row| row["path"] == "src/annotationcase/Service.scala")
            .unwrap();
        if mode == "empty" {
            service["ast"] = serde_json::json!({});
        } else if mode == "stale" {
            service["source_sha256"] = Value::String("0".repeat(64));
        }
        std::fs::write(
            &broken_syntax,
            rows.iter()
                .map(|row| serde_json::to_string(row).unwrap() + "\n")
                .collect::<String>(),
        )
        .unwrap();
        let head_facts = import_capture(
            &directory.join("documents.jsonl"),
            (mode != "absent").then_some(broken_syntax.as_path()),
            &ExtractOptions {
                workers: 1,
                catalogue: Some(directory.join("catalogue.json")),
                ..Default::default()
            },
        )
        .unwrap();
        let (head_facts, head_graph) = enrich_facts(head_facts, &directory, 1);
        let (base_facts, base_graph) = enriched(&fixture().join("base"), 1);
        let seeds = selector_select::changed_seeds(
            &base_facts,
            &base_graph,
            &head_facts,
            &head_graph,
            &["src/annotationcase/Service.scala"],
        )
        .unwrap();
        let options = selector_solve::SolveOptions::default();
        let runtime = selector_solve::SolverRuntime::new(&options).unwrap();
        let base = selector_solve::analyze_typed_with_runtime(
            &base_facts,
            &base_graph,
            selector_solve::AnalysisSeeds {
                execution: &seeds.base,
                declarations: &seeds.base_compile,
            },
            &options,
            &runtime,
        )
        .unwrap();
        let head = selector_solve::analyze_typed_with_runtime(
            &head_facts,
            &head_graph,
            selector_solve::AnalysisSeeds {
                execution: &seeds.head,
                declarations: &seeds.head_compile,
            },
            &options,
            &runtime,
        )
        .unwrap();
        let result = selector_select::select(
            &base_facts,
            &base_graph,
            &head_facts,
            &head_graph,
            seeds,
            Some(base),
            head,
        )
        .unwrap();
        assert_eq!(result.completion, Completion::Conservative, "{mode}");
        assert!(
            result.suites.iter().any(|selected| {
                head_facts.text(head_facts.suites[selected.suite.index()].name)
                    == "annotationcase.AffectedSuite"
                    && selected.guarded
            }),
            "missing source-positive authority cannot exclude the actual consumer: {mode}"
        );
        assert!(
            !result.obligations.is_empty()
                || !result.head.obligations.is_empty()
                || result
                    .base
                    .as_ref()
                    .is_some_and(|base| !base.obligations.is_empty()),
            "unsupported source must stay explainable: {mode}"
        );
    }
}
