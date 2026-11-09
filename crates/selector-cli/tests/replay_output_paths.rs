//! Actual CLI reruns must preserve the evidence pinned by the source receipt.
// Reuse the receipt codec to resign a stale solver binding; this test exercises
// process-level output handling rather than defining another wire encoder.
#[allow(dead_code)]
#[path = "../src/external_metadata.rs"]
mod external_metadata;
#[allow(dead_code)]
#[path = "../src/metadata_stage.rs"]
mod metadata_stage;
#[allow(dead_code)]
#[path = "../src/replay.rs"]
mod protocol;

use protocol::Result;

use selector_facts::{BodyRecord, FactBuilder, FileRecord, SuiteRecord};
use selector_types::*;
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn digest(bytes: &[u8]) -> ContentHash {
    ContentHash(Sha256::digest(bytes).into())
}
fn snapshot(root: &Path) -> (PathBuf, PathBuf, NodeId) {
    let mut b = FactBuilder::new();
    b.facts.revision = b.intern("output-path-fixture").unwrap();
    let source = "class Tiny\n";
    let path = b.intern("Tiny.scala").unwrap();
    let text = b.intern(source).unwrap();
    let context = b.intern("fixture/test").unwrap();
    b.facts.files.push(FileRecord {
        path,
        source: text,
        revision: b.facts.revision,
        context,
        source_hash: digest(source.as_bytes()),
        flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
    });
    let symbol = b.ensure_symbol("fixture/Tiny#", FileId(0)).unwrap();
    let span = Span {
        start: 0,
        end: source.len() as u32,
    };
    // Global references are file-less until their compiler definition is bound.
    // This fixture declares Tiny in the verified source rather than leaving a
    // reference-only symbol that correctly triggers NoDeclarations.
    b.facts.symbols[symbol.index()].file = FileId(0);
    b.facts.symbols[symbol.index()].kind = 13;
    b.facts.symbols[symbol.index()].flags = SYMBOL_DEFINED | SYMBOL_SCALA_PARENTS_COMPLETE;
    b.facts.symbols[symbol.index()].span = span;
    b.facts.bodies.push(BodyRecord {
        symbol,
        file: FileId(0),
        span,
        name_span: span,
        operations: IdRange::default(),
        parameters: IdRange::default(),
        body_hash: digest(source.as_bytes()),
        flags: BODY_INITIALIZER,
    });
    let name = b.intern("fixture.Tiny").unwrap();
    b.facts.suites.push(SuiteRecord {
        name,
        symbol,
        file: FileId(0),
        flags: 0,
    });
    let mut facts = b.finish().unwrap();
    let fact_path = root.join("facts.bin");
    facts.identity = selector_facts::codec::write(&fact_path, &facts).unwrap();
    let graph = selector_graph_build::build(
        &facts,
        &selector_graph_build::BuildOptions {
            workers: 1,
            include_models: false,
        },
    )
    .unwrap();
    let node = graph.node_for_symbol(symbol).unwrap();
    let graph_path = root.join("graph.bin");
    selector_graph::codec::write(&graph_path, &graph).unwrap();
    (fact_path, graph_path, node)
}
fn run(command: &mut Command) -> Output {
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    output
}
fn tree(path: &Path) -> BTreeMap<PathBuf, ContentHash> {
    fn visit(base: &Path, path: &Path, files: &mut BTreeMap<PathBuf, ContentHash>) {
        if path.is_dir() {
            for entry in std::fs::read_dir(path).unwrap() {
                visit(base, &entry.unwrap().path(), files);
            }
        } else {
            files.insert(
                path.strip_prefix(base).unwrap().to_owned(),
                digest(&std::fs::read(path).unwrap()),
            );
        }
    }
    let mut files = BTreeMap::new();
    visit(path, path, &mut files);
    files
}
#[test]
fn stale_solver_rerun_to_new_output_preserves_original_receipt_report_and_all_auxiliary_outputs() {
    let directory = tempfile::tempdir().unwrap();
    let root = directory.path();
    let (facts, graph, node) = snapshot(root);
    let original = root.join("original");
    std::fs::create_dir(&original).unwrap();
    let report = original.join("report.json");
    let progress = original.join("progress.jsonl");
    let evidence = original.join("evidence.json");
    let checkpoints = original.join("checkpoints");
    let bundle = original.join("replay");
    let receipt_path = original.join("receipt.json");
    run(Command::new(env!("CARGO_BIN_EXE_selector"))
        .arg("query")
        .arg("--assume-independent-suites")
        .args(["--retain-suite", "fixture.Tiny"])
        .arg("--head-facts")
        .arg(&facts)
        .arg("--head-graph")
        .arg(&graph)
        .args(["--changed", "Tiny.scala", "--all-roots", "--workers", "1"])
        .arg("--output")
        .arg(&report)
        .arg("--progress-jsonl")
        .arg(&progress)
        .arg("--full-evidence")
        .arg(&evidence)
        .arg("--checkpoint-dir")
        .arg(&checkpoints)
        .arg("--replay-bundle")
        .arg(&bundle)
        .arg("--replay-node")
        .arg(node.0.to_string())
        .arg("--receipt")
        .arg(&receipt_path));
    assert!(report.is_file() && progress.is_file() && evidence.is_file());
    let selection: Value = serde_json::from_slice(&std::fs::read(&report).unwrap()).unwrap();
    assert_eq!(selection["suite_semantics"], "independent_suites");
    assert_eq!(selection["selection_contract"]["bits"], 496);
    assert_ne!(selection["decisions"][0]["status"], "excluded");
    let events: Vec<Value> = std::fs::read_to_string(&progress)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    for phase in [
        "query_input_receipt",
        "query_prepare",
        "query_plan",
        "query_session_admission",
    ] {
        let begin = events
            .iter()
            .position(|event| event["stage"] == "stage_begin" && event["phase"] == phase)
            .unwrap();
        let end = events
            .iter()
            .position(|event| event["stage"] == "stage_end" && event["phase"] == phase)
            .unwrap();
        assert!(begin < end, "{phase} must report its bounded lifetime");
        assert!(events[end]["elapsed_ns"].is_u64());
    }
    assert!(checkpoints.join("head.bin").is_file());
    assert!(bundle.join("metadata.json").is_file());
    let mut receipt =
        protocol::load_receipt(&receipt_path, &protocol::ReplayLimits::default()).unwrap();
    assert!(
        receipt
            .arguments
            .iter()
            .any(|argument| argument == "--assume-independent-suites")
    );
    assert!(
        receipt
            .arguments
            .windows(2)
            .any(|pair| pair == ["--retain-suite", "fixture.Tiny"])
    );
    let solve = receipt
        .stages
        .iter_mut()
        .find(|stage| stage.id == "query.solve")
        .unwrap();
    solve.producer = "00".repeat(32);
    solve.seal();
    protocol::write_receipt(&receipt_path, &receipt).unwrap();
    let frozen = tree(&original);
    let new_report = root.join("rerun.json");
    let output = run(Command::new(env!("CARGO_BIN_EXE_selector"))
        .arg("replay")
        .arg("--receipt")
        .arg(&receipt_path)
        .arg("--output")
        .arg(&new_report));
    assert_eq!(
        tree(&original),
        frozen,
        "recorded report, receipt, progress, evidence, checkpoint and transfer bundle must stay immutable"
    );
    assert!(new_report.is_file());
    let replayed: Value = serde_json::from_slice(&std::fs::read(&new_report).unwrap()).unwrap();
    assert_eq!(replayed["suite_semantics"], "independent_suites");
    assert_ne!(replayed["decisions"][0]["status"], "excluded");
    assert_eq!(replayed["selection_contract"]["bits"], 496);
    assert!(root.join("rerun.json.progress.jsonl").is_file());
    assert!(root.join("rerun.json.full-evidence.json").is_file());
    assert!(root.join("rerun.json.checkpoints/head.bin").is_file());
    assert!(root.join("rerun.json.replay/metadata.json").is_file());
    let events = String::from_utf8(output.stderr).unwrap();
    assert!(
        events
            .lines()
            .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
            .any(|event| event["stage"] == "native_replay"
                && event["earliest_invalidation"] == "query.solve")
    );
    let explicit_report = root.join("explicit.json");
    let explicit_progress = root.join("explicit-events.jsonl");
    run(Command::new(env!("CARGO_BIN_EXE_selector"))
        .arg("replay")
        .arg("--receipt")
        .arg(&receipt_path)
        .arg("--output")
        .arg(&explicit_report)
        .arg("--progress-jsonl")
        .arg(&explicit_progress));
    assert!(explicit_progress.is_file());
    assert!(!root.join("explicit.json.progress.jsonl").exists());
    assert_eq!(tree(&original), frozen);
}

#[test]
fn paired_plan_only_uses_the_same_explicit_suite_contract_on_both_sides_and_workers() {
    let directory = tempfile::tempdir().unwrap();
    let (facts, graph, _) = snapshot(directory.path());
    for workers in ["1", "4"] {
        for independent in [false, true] {
            let mut command = Command::new(env!("CARGO_BIN_EXE_selector"));
            command
                .arg("query")
                .arg("--head-facts")
                .arg(&facts)
                .arg("--head-graph")
                .arg(&graph)
                .arg("--base-facts")
                .arg(&facts)
                .arg("--base-graph")
                .arg(&graph)
                .args([
                    "--changed",
                    "Tiny.scala",
                    "--plan-only",
                    "--workers",
                    workers,
                ]);
            if independent {
                command.arg("--assume-independent-suites");
            }
            let output = run(&mut command);
            let plan: Value = serde_json::from_slice(&output.stdout).unwrap();
            let mode = if independent {
                "independent_suites"
            } else {
                "shared_state"
            };
            for row in [&plan, &plan["base"], &plan["head"]] {
                assert_eq!(row["suite_semantics"], mode);
                assert_eq!(
                    row["selection_contract"]["version"],
                    SelectionContract::VERSION
                );
                assert_eq!(
                    row["selection_contract"]["bits"],
                    if independent { 496 } else { 480 }
                );
                assert_eq!(row["assume_independent_suites"], independent);
                assert_eq!(
                    row["suite_semantics_assumption_bit"],
                    if independent { 16 } else { 0 }
                );
            }
        }
    }
}

#[test]
fn switching_only_suite_policy_reuses_captured_source_and_graph_cache_entries() {
    let directory = tempfile::tempdir().unwrap();
    let root = directory.path();
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/execution-smoke");
    let cache = root.join("cache");
    let invoke = |independent: bool, output: &Path| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_selector"));
        command
            .arg("run")
            .arg("--head")
            .arg(fixture.join("head/documents.jsonl"))
            .arg("--head-syntax")
            .arg(fixture.join("head/syntax.jsonl"))
            .arg("--base")
            .arg(fixture.join("base/documents.jsonl"))
            .arg("--base-syntax")
            .arg(fixture.join("base/syntax.jsonl"))
            .arg("--catalogue-input")
            .arg(fixture.join("head/catalogue.json"))
            .arg("--base-catalogue-input")
            .arg(fixture.join("base/catalogue.json"))
            .arg("--artifacts")
            .arg(&cache)
            .arg("--output")
            .arg(output)
            .args([
                "--changed",
                "src/executioncase/Changed.scala",
                "--workers",
                "1",
            ]);
        if independent {
            command
                .arg("--assume-independent-suites")
                .args(["--retain-suite", "executioncase.UnaffectedSuite"]);
        }
        run(&mut command)
    };
    let prepared = || {
        std::fs::read_dir(&cache)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.extension().is_some_and(|extension| extension == "bin"))
            .map(|path| {
                (
                    path.file_name().unwrap().to_owned(),
                    digest(&std::fs::read(&path).unwrap()),
                )
            })
            .collect::<BTreeMap<_, _>>()
    };
    let shared = root.join("shared.json");
    invoke(false, &shared);
    let before = prepared();
    assert!(!before.is_empty());
    let independent = root.join("independent.json");
    let output = invoke(true, &independent);
    assert_eq!(
        prepared(),
        before,
        "query-only policy must not invalidate extraction or graph artifacts"
    );
    for (path, mode) in [
        (&shared, "shared_state"),
        (&independent, "independent_suites"),
    ] {
        let report: Value = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
        assert_eq!(report["suite_semantics"], mode);
    }
    let events: Vec<Value> = String::from_utf8(output.stderr)
        .unwrap()
        .lines()
        .filter_map(|line| serde_json::from_str(line).ok())
        .collect();
    for stage in ["extract", "build"] {
        assert_eq!(
            events
                .iter()
                .filter(|event| event["stage"] == stage && event["cache_hit"] == true)
                .count(),
            2
        );
    }
}

#[test]
fn exact_suite_retention_prevents_exclusion_in_both_selection_paths_and_paired_plans() {
    let directory = tempfile::tempdir().unwrap();
    let (facts, graph, _) = snapshot(directory.path());
    let invoke = |retained: Option<&str>, all_roots: bool, plan_only: bool| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_selector"));
        command
            .arg("query")
            .arg("--head-facts")
            .arg(&facts)
            .arg("--head-graph")
            .arg(&graph)
            .arg("--base-facts")
            .arg(&facts)
            .arg("--base-graph")
            .arg(&graph)
            .args([
                "--changed",
                "Tiny.scala",
                "--assume-independent-suites",
                "--workers",
                "1",
            ]);
        if let Some(name) = retained {
            command.args(["--retain-suite", name]);
        }
        if all_roots {
            command.arg("--all-roots");
        }
        if plan_only {
            command.arg("--plan-only");
        }
        command.output().unwrap()
    };
    for all_roots in [false, true] {
        let baseline = invoke(None, all_roots, false);
        assert!(
            baseline.status.success(),
            "{}",
            String::from_utf8_lossy(&baseline.stderr)
        );
        let baseline: Value = serde_json::from_slice(&baseline.stdout).unwrap();
        assert_eq!(baseline["decisions"][0]["status"], "excluded");
        let retained = invoke(Some("fixture.Tiny"), all_roots, false);
        assert!(
            retained.status.success(),
            "{}",
            String::from_utf8_lossy(&retained.stderr)
        );
        let retained: Value = serde_json::from_slice(&retained.stdout).unwrap();
        assert_eq!(retained["decisions"][0]["status"], "unknown");
        assert_eq!(retained["decisions"][0]["guarded"], true);
        let causes = retained["guard_causes"].as_array().unwrap();
        assert_eq!(causes.len(), 2);
        for cause in causes {
            assert_eq!(cause["external"]["reason"], "explicit_suite_retention");
            assert_eq!(cause["external"]["suite_name"], "fixture.Tiny");
        }
    }
    let plan = invoke(Some("fixture.Tiny"), false, true);
    assert!(
        plan.status.success(),
        "{}",
        String::from_utf8_lossy(&plan.stderr)
    );
    let plan: Value = serde_json::from_slice(&plan.stdout).unwrap();
    assert_eq!(plan["retained_suites"], serde_json::json!(["fixture.Tiny"]));
    for side in ["base", "head"] {
        assert_eq!(plan[side]["metrics"]["excluded"], 0);
        assert_eq!(plan[side]["metrics"]["candidates"], 1);
    }
    let unmatched = invoke(Some("fixture.tiny"), false, false);
    assert!(!unmatched.status.success());
    assert!(
        String::from_utf8_lossy(&unmatched.stderr).contains("no exact current catalogue match")
    );
    assert!(unmatched.stdout.is_empty());
}
