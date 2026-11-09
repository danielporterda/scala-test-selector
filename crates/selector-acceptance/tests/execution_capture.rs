//! Fresh compiler input and independent JVM observations; no graph oracle input.
use selector_extract::{ExtractOptions, import_capture};
use selector_facts::FactSnapshot;
use selector_types::*;
use serde_json::Value;
use std::path::{Path, PathBuf};

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/execution-smoke")
}
fn captured(side: &Path, reference: bool) -> FactSnapshot {
    let options = ExtractOptions {
        workers: 2,
        catalogue: Some(side.join("catalogue.json")),
        ..ExtractOptions::default()
    };
    import_capture(
        &side.join(if reference {
            "reference-documents.jsonl"
        } else {
            "documents.jsonl"
        }),
        Some(&side.join("syntax.jsonl")),
        &options,
    )
    .unwrap()
}

#[test]
fn genuine_compiler_native_and_reference_inputs_admit_the_same_execution_records() {
    for side in ["base", "head"] {
        let directory = fixture().join(side);
        let native = captured(&directory, false);
        let reference = captured(&directory, true);
        assert_eq!(native.files.len(), 4);
        assert!(native.issues.is_empty(), "{:?}", native.issues);
        assert!(
            native
                .files
                .iter()
                .all(|file| file.flags & (SOURCE_VERIFIED | SYNTAX_VERIFIED)
                    == SOURCE_VERIFIED | SYNTAX_VERIFIED)
        );
        assert_eq!(native.symbols.len(), reference.symbols.len());
        assert_eq!(native.occurrences.len(), reference.occurrences.len());
        assert_eq!(native.operations.len(), reference.operations.len());
        for (a, b) in native.symbols.iter().zip(&reference.symbols) {
            assert_eq!(
                (native.text(a.name), a.kind, a.properties, a.flags, a.span),
                (
                    reference.text(b.name),
                    b.kind,
                    b.properties,
                    b.flags,
                    b.span
                )
            );
        }
        for (a, b) in native.operations.iter().zip(&reference.operations) {
            assert_eq!(
                (
                    a.body,
                    a.opcode as u32,
                    native.symbol_name(a.target),
                    a.dest,
                    a.a,
                    a.b,
                    a.arguments,
                    a.span
                ),
                (
                    b.body,
                    b.opcode as u32,
                    reference.symbol_name(b.target),
                    b.dest,
                    b.a,
                    b.b,
                    b.arguments,
                    b.span
                )
            );
        }
        let suites: Vec<_> = native
            .suites
            .iter()
            .map(|suite| native.text(suite.name))
            .collect();
        assert_eq!(
            suites,
            [
                "executioncase.AffectedSuite",
                "executioncase.UnaffectedSuite",
                "executioncase.DormantSuite"
            ]
        );
    }
}

#[test]
fn independent_jvm_observations_and_only_changed_source_are_frozen() {
    let expected: Value =
        serde_json::from_slice(&std::fs::read(fixture().join("expected.json")).unwrap()).unwrap();
    let base = captured(&fixture().join("base"), false);
    let head = captured(&fixture().join("head"), false);
    let changed: Vec<_> = head
        .files
        .iter()
        .filter_map(|file| {
            let path = head.text(file.path);
            let old = base
                .files
                .iter()
                .find(|old| base.text(old.path) == path)
                .unwrap();
            (old.source_hash != file.source_hash).then_some(path)
        })
        .collect();
    assert_eq!(changed, ["src/executioncase/Changed.scala"]);
    for side in ["base", "head"] {
        let values = expected["independent_observed_values"][side]
            .as_array()
            .unwrap()
            .iter()
            .map(|n| n.as_i64().unwrap().to_string())
            .collect::<Vec<_>>()
            .join(",");
        let observed = std::fs::read_to_string(fixture().join(side).join("execution.log")).unwrap();
        assert_eq!(
            observed.lines().next(),
            Some(format!("observed:{values}").as_str())
        );
        let runner = std::fs::read_to_string(fixture().join(side).join("scalatest.log")).unwrap();
        assert!(runner.contains("Suites: completed 3, aborted 0"));
    }
}

#[test]
fn compiler_typed_returned_callbacks_remain_deferred_and_parameter_headers_are_not_unknown() {
    let facts = captured(&fixture().join("head"), false);
    for package in ["org/", "org/scalatest/"] {
        assert!(
            facts
                .operations
                .iter()
                .all(|operation| facts.symbol_name(operation.target) != package),
            "qualified parent type namespace {package} must not become an executable operation"
        );
    }
    assert_eq!(
        facts
            .operations
            .iter()
            .filter(|operation| operation.opcode == Opcode::Initialize
                && facts.symbol_name(operation.target) == "org/scalatest/Suite#")
            .count(),
        3,
        "all three genuine constructors still initialize the actual compiler parent type"
    );
    let factory = facts.find_symbol("executioncase/Factory.make().").unwrap();
    let body = facts
        .bodies
        .iter()
        .find(|body| body.symbol == factory)
        .unwrap();
    let operations = &facts.operations[body.operations.range()];
    let parameter = operations
        .iter()
        .find(|op| op.opcode == Opcode::Parameter)
        .unwrap();
    assert!(
        !body.span.contains(parameter.span),
        "real parameter declaration belongs to the header"
    );
    let binding = operations
        .iter()
        .find(|op| op.opcode == Opcode::BindCallback)
        .unwrap();
    assert!(
        operations
            .iter()
            .any(|op| op.opcode == Opcode::Return && op.a == binding.dest)
    );
    let deferred = facts
        .bodies
        .iter()
        .find(|body| body.symbol == binding.target)
        .unwrap();
    assert_ne!(deferred.flags & BODY_DEFERRED, 0);
    assert!(
        facts.operations[deferred.operations.range()]
            .iter()
            .any(|op| op.opcode == Opcode::InvokeCallback)
    );
    let graph = selector_graph_build::build(
        &facts,
        &selector_graph_build::BuildOptions {
            workers: 2,
            include_models: true,
        },
    )
    .unwrap();
    assert!(
        !graph
            .issues
            .iter()
            .any(|issue| issue.symbol == factory && issue.kind == IssueKind::UnknownExecution)
    );
    let factory_node = graph.node_for_symbol(factory).unwrap();
    let closure_node = graph.node_for_symbol(binding.target).unwrap();
    assert!(
        !graph
            .successors(factory_node)
            .any(|(_, edge)| edge.target == closure_node && edge.kind.is_execution()),
        "constructing a returned closure must not invoke it"
    );
    let dormant = facts
        .find_symbol("executioncase/DormantSuite#dormantFactory().")
        .unwrap();
    let suite = facts.find_symbol("executioncase/DormantSuite#").unwrap();
    let suite_node = graph.node_for_symbol(suite).unwrap();
    let dormant_node = graph.node_for_symbol(dormant).unwrap();
    assert!(
        !graph
            .successors(suite_node)
            .any(|(_, edge)| edge.target == dormant_node && edge.kind.is_execution()),
        "constructing a suite must not call an ordinary dormant member"
    );
}

fn enriched(side: &Path, workers: usize) -> (FactSnapshot, selector_graph::ProgramGraph) {
    let mut facts = import_capture(
        &side.join("documents.jsonl"),
        Some(&side.join("syntax.jsonl")),
        &ExtractOptions {
            workers,
            catalogue: Some(side.join("catalogue.json")),
            ..ExtractOptions::default()
        },
    )
    .unwrap();
    let mut binary = selector_graph_build::binary_inputs::load_binary_manifest(
        &side.join("binary.json"),
        &facts,
    )
    .unwrap();
    selector_graph_build::binary_inputs::augment_binary_facts(&mut facts, &mut binary).unwrap();
    // Exercise the actual encoded admission boundary used by the native CLI.
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
}

#[test]
fn genuine_compiler_and_verified_bytecode_select_only_independently_observed_affected_suite() {
    let expected: Value =
        serde_json::from_slice(&std::fs::read(fixture().join("expected.json")).unwrap()).unwrap();
    let mut baseline = None;
    for workers in [1, 2, 4, 8, 16] {
        let (base_facts, base_graph) = enriched(&fixture().join("base"), workers);
        let (head_facts, head_graph) = enriched(&fixture().join("head"), workers);
        let paths: Vec<_> = expected["changed_paths"]
            .as_array()
            .unwrap()
            .iter()
            .map(|path| path.as_str().unwrap())
            .collect();
        let seeds = selector_select::changed_seeds(
            &base_facts,
            &base_graph,
            &head_facts,
            &head_graph,
            &paths,
        )
        .unwrap();
        assert!(
            !seeds.conservative,
            "source-complete changed path must be admitted"
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
        let snapshots = selector_report::ReportSnapshots {
            base_facts: &base_facts,
            base_graph: &base_graph,
            head_facts: &head_facts,
            head_graph: &head_graph,
        };
        let mut bytes = Vec::new();
        selector_report::write_json(&mut bytes, &snapshots, &result).unwrap();
        let mut report: Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(report["completion"], expected["completion"], "{report:#}");
        let selected: Vec<_> = report["suites"]
            .as_array()
            .unwrap()
            .iter()
            .map(|suite| suite["name"].as_str().unwrap())
            .collect();
        let names: Vec<_> = expected["selected_suites"]
            .as_array()
            .unwrap()
            .iter()
            .map(|name| name.as_str().unwrap())
            .collect();
        assert_eq!(selected, names);
        assert!(
            report["suites"]
                .as_array()
                .unwrap()
                .iter()
                .all(|suite| suite["guarded"] == false)
        );
        assert!(report["obligations"].as_array().unwrap().is_empty());
        for side in ["base", "head"] {
            let analysis = &report[side];
            assert!(analysis["metrics"]["states"].as_u64().unwrap() > 0);
            assert!(analysis["guarded_roots"].as_array().unwrap().is_empty());
            assert_eq!(analysis["unscoped_uncertainty"], false);
            let evidence = &analysis["evidence"];
            let contexts = evidence["contexts"].as_array().unwrap();
            for symbol in expected["required_executed_symbols"].as_array().unwrap() {
                assert!(
                    contexts.iter().any(|context| context["symbol"] == *symbol),
                    "missing actual retained context {symbol}: {evidence:#}"
                );
            }
            assert!(
                !evidence["captures"].as_array().unwrap().is_empty(),
                "returned callback must retain independently bound captures"
            );
            assert!(
                evidence["witnesses"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|witness| !witness["binding"].is_null()),
                "callback execution proof must include a concrete binding"
            );
            assert!(
                contexts.iter().all(|context| {
                    let symbol = context["symbol"].as_str().unwrap();
                    !symbol.contains("dormantFactory") && !symbol.contains("#dormant().")
                }),
                "ordinary deferred member must not be eagerly executed"
            );
            report[side].as_object_mut().unwrap().remove("metrics");
        }
        if let Some(previous) = &baseline {
            assert_eq!(
                &report, previous,
                "full evidence differs for {workers} workers"
            );
        } else {
            baseline = Some(report);
        }
    }
}

#[test]
fn captured_framework_bytes_are_verified_before_native_recipe_admission() {
    let side = fixture().join("head");
    let facts = captured(&side, false);
    let mut manifest: Value =
        serde_json::from_slice(&std::fs::read(side.join("binary.json")).unwrap()).unwrap();
    let directory = tempfile::tempdir().unwrap();
    let archive = directory.path().join("framework-prefix.jar");
    std::fs::copy(fixture().join("framework-prefix.jar"), &archive).unwrap();
    manifest["contexts"][0]["entries"][0]["path"] =
        Value::String(side.join("bytecode.jar").to_string_lossy().into_owned());
    manifest["contexts"][0]["entries"][1]["path"] =
        Value::String(archive.to_string_lossy().into_owned());
    let mapping = directory.path().join("binary.json");
    std::fs::write(&mapping, serde_json::to_vec(&manifest).unwrap()).unwrap();
    selector_graph_build::binary_inputs::load_binary_manifest(&mapping, &facts).unwrap();
    let mut bytes = std::fs::read(&archive).unwrap();
    bytes[40] ^= 1;
    std::fs::write(&archive, bytes).unwrap();
    let error = selector_graph_build::binary_inputs::load_binary_manifest(&mapping, &facts)
        .err()
        .expect("changed framework bytes must reject even after a successful admission");
    assert!(error.to_string().contains("HashMismatch"), "{error}");
}
