//! Independent JVM observations distinguish omitted defaults, explicit arguments,
//! receiver-dependent copy defaults and primary/secondary constructors.
use selector_extract::{ExtractOptions, import_capture};
use selector_facts::FactSnapshot;
use selector_graph::ProgramGraph;
use serde_json::Value;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/constructor-forms")
}

fn debug_source_recipes(facts: &FactSnapshot, stage: &str) {
    let Some(path) = std::env::var_os("SELECTOR_CONSTRUCTOR_REPORT") else {
        return;
    };
    let records: Vec<_> = facts.bodies.iter().filter(|body| {
        let name = facts.symbol_name(body.symbol);
        name.starts_with("constructorforms/Value") || name.starts_with("constructorforms/Secondary")
    }).map(|body| serde_json::json!({
        "symbol": facts.symbol_name(body.symbol), "flags": body.flags,
        "body_span": [body.span.start, body.span.end], "parameters": facts.operands[body.parameters.range()].iter().map(|id|id.0).collect::<Vec<_>>(),
        "operations": facts.operations[body.operations.range()].iter().map(|op| serde_json::json!({
            "opcode": format!("{:?}",op.opcode), "target": facts.symbol_name(op.target),
            "target_info": (!op.target.is_none()).then(|| format!("{:?}",facts.symbols[op.target.index()])),
            "dest": op.dest.0, "a": op.a.0, "b": op.b.0, "flags": op.flags,
            "span": [op.span.start,op.span.end], "arguments": facts.operands[op.arguments.range()].iter().map(|id|id.0).collect::<Vec<_>>(),
        })).collect::<Vec<_>>()
    })).collect();
    let mut path = path.to_string_lossy().into_owned();
    path.push_str(&format!(".{stage}.json"));
    std::fs::write(path, serde_json::to_vec_pretty(&records).unwrap()).unwrap();
}

fn enriched(directory: &Path, workers: usize) -> (FactSnapshot, ProgramGraph) {
    let mut facts = import_capture(
        &directory.join("documents.jsonl"),
        Some(&directory.join("syntax.jsonl")),
        &ExtractOptions {
            workers,
            catalogue: Some(directory.join("catalogue.json")),
            ..Default::default()
        },
    )
    .unwrap();
    debug_source_recipes(&facts, "before-source-recipes");
    let stats = selector_graph_build::source_recipes::augment_source_recipes(&mut facts).unwrap();
    if std::env::var_os("SELECTOR_CONSTRUCTOR_REPORT").is_some() {
        eprintln!("SourceRecipeStats: {stats:?}");
    }
    debug_source_recipes(&facts, "after-source-recipes");
    let mut binary = selector_graph_build::binary_inputs::load_binary_manifest(
        &directory.join("binary.json"),
        &facts,
    )
    .unwrap();
    selector_graph_build::binary_inputs::augment_binary_facts(&mut facts, &mut binary).unwrap();
    debug_source_recipes(&facts, "after-binary-recipes");
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
    let path = saved.path().join("graph.bin");
    selector_graph::codec::write(&path, &graph).unwrap();
    (facts, selector_graph::codec::read(&path).unwrap())
}

#[test]
fn genuine_ordinary_default_getter_is_a_source_owned_recipe_and_only_omitted_argument_calls_it() {
    let directory = fixture().join("head");
    let mut facts = import_capture(
        &directory.join("documents.jsonl"),
        Some(&directory.join("syntax.jsonl")),
        &ExtractOptions {
            workers: 1,
            catalogue: Some(directory.join("catalogue.json")),
            ..Default::default()
        },
    )
    .unwrap();
    selector_graph_build::source_recipes::augment_source_recipes(&mut facts).unwrap();
    let getter = facts
        .find_symbol("constructorforms/Defaults.run$default$1().")
        .unwrap();
    let changed = facts
        .find_symbol("constructorforms/Effects.changed().")
        .unwrap();
    let body = facts
        .bodies
        .iter()
        .find(|body| body.symbol == getter)
        .expect("compiler-bound default getter source body");
    assert_ne!(body.flags & selector_types::BODY_DEFERRED, 0);
    assert_eq!(
        facts.files[body.file.index()].flags & selector_types::FILE_BINARY_SOURCE,
        0,
        "binary fallback must not supply the source default getter in this gate"
    );
    assert!(
        facts.operations[body.operations.range()]
            .iter()
            .any(|operation| operation.target == changed)
    );
    for (class, expected) in [("MethodDefaultSuite", true), ("MethodExplicitSuite", false)] {
        let caller = facts
            .find_symbol(&format!("constructorforms/{class}#observed."))
            .unwrap();
        let body = facts
            .bodies
            .iter()
            .find(|body| body.symbol == caller)
            .unwrap();
        assert_eq!(
            facts.operations[body.operations.range()]
                .iter()
                .any(|operation| operation.target == getter),
            expected,
            "provided argument must not activate its default getter: {class}"
        );
    }
}

#[test]
fn independent_jvm_default_copy_and_secondary_constructor_observations_are_retained() {
    let expected: Value =
        serde_json::from_slice(&std::fs::read(fixture().join("expected.json")).unwrap()).unwrap();
    for side in ["base", "head"] {
        let directory = fixture().join(side);
        let observed = std::fs::read_to_string(directory.join("execution.log")).unwrap();
        let values = expected["independent_observed_values"][side]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| v.as_i64().unwrap().to_string())
            .collect::<Vec<_>>()
            .join(",");
        assert!(
            observed
                .lines()
                .any(|line| line == format!("observed:{values}"))
        );
        assert_eq!(
            observed
                .lines()
                .filter(|line| line.starts_with("suite:"))
                .count(),
            expected["selected_suites"].as_array().unwrap().len()
                + expected["excluded_suites"].as_array().unwrap().len()
        );
        assert!(
            std::fs::read_to_string(directory.join("scalatest.log"))
                .unwrap()
                .contains(&format!(
                    "Suites: completed {}, aborted 0",
                    expected["selected_suites"].as_array().unwrap().len()
                        + expected["excluded_suites"].as_array().unwrap().len()
                ))
        );
        let bytecode = std::fs::read_to_string(directory.join("constructor-bytecode.log")).unwrap();
        for method in [
            "apply$default$1",
            "$lessinit$greater$default$1",
            "copy$default$1",
            "constructorforms.Secondary();",
        ] {
            assert!(
                bytecode.contains(method),
                "real compiler did not emit {method}"
            );
        }
    }
}

#[test]
fn real_omitted_defaults_copy_receivers_and_secondary_constructors_select_only_observed_changes() {
    let expected: Value =
        serde_json::from_slice(&std::fs::read(fixture().join("expected.json")).unwrap()).unwrap();
    let mut baseline = None;
    for workers in [1, 4] {
        let (base_facts, base_graph) = enriched(&fixture().join("base"), workers);
        let (head_facts, head_graph) = enriched(&fixture().join("head"), workers);
        assert_eq!(
            head_facts.suites.len(),
            expected["selected_suites"].as_array().unwrap().len()
                + expected["excluded_suites"].as_array().unwrap().len()
        );
        let seeds = selector_select::changed_seeds(
            &base_facts,
            &base_graph,
            &head_facts,
            &head_graph,
            &["src/constructorforms/Effects.scala"],
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
        if let Some(path) = std::env::var_os("SELECTOR_CONSTRUCTOR_REPORT") {
            std::fs::write(path, serde_json::to_vec_pretty(&report).unwrap()).unwrap();
        }
        let diagnostics = serde_json::json!({
            "completion": report["completion"],
            "suites": report["suites"],
            "head_obligations": report["head"]["obligations"],
        });
        let names = report["suites"]
            .as_array()
            .unwrap()
            .iter()
            .map(|s| s["name"].as_str().unwrap())
            .collect::<BTreeSet<_>>();
        let expected_names = expected["selected_suites"]
            .as_array()
            .unwrap()
            .iter()
            .map(|s| s.as_str().unwrap())
            .collect::<BTreeSet<_>>();
        assert_eq!(
            report["completion"], expected["completion"],
            "{diagnostics:#}"
        );
        assert_eq!(names, expected_names, "{diagnostics:#}");
        for excluded in expected["excluded_suites"].as_array().unwrap() {
            assert!(!names.contains(excluded.as_str().unwrap()));
        }
        assert!(
            report["suites"]
                .as_array()
                .unwrap()
                .iter()
                .all(|s| s["guarded"] == false)
        );
        assert!(report["obligations"].as_array().unwrap().is_empty());
        for side in ["base", "head"] {
            assert!(report[side]["guarded_roots"].as_array().unwrap().is_empty());
            assert!(
                report[side]["evidence"]["contexts"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|context| context["symbol"] == "constructorforms/Effects.changed().")
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
