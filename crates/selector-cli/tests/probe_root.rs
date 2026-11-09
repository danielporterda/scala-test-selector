use selector_facts::{BodyRecord, FactBuilder, FileRecord, OperationRecord, SuiteRecord};
use selector_types::*;
use sha2::{Digest, Sha256};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

struct Fixture {
    facts: selector_facts::FactSnapshot,
    graph: selector_graph::ProgramGraph,
    fact_path: PathBuf,
    graph_path: PathBuf,
    root: NodeId,
    helper: NodeId,
    quiet: NodeId,
}
fn fixture(directory: &Path, ambiguous: bool) -> Fixture {
    std::fs::create_dir_all(directory).unwrap();
    let mut b = FactBuilder::new();
    b.facts.revision = b.intern("probe-fixture").unwrap();
    let context = b.intern("fixture/test").unwrap();
    let source = "class Guarded { callback() }\nclass Quiet\n";
    let path = b.intern("Probe.scala").unwrap();
    let text = b.intern(source).unwrap();
    b.facts.files.push(FileRecord {
        path,
        source: text,
        context,
        revision: b.facts.revision,
        source_hash: ContentHash(Sha256::digest(source.as_bytes()).into()),
        flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
    });
    let root = b.ensure_symbol("fixture/Guarded#", FileId(0)).unwrap();
    let helper = b
        .ensure_symbol("fixture/Guarded#callback().", FileId(0))
        .unwrap();
    let quiet = b.ensure_symbol("fixture/Quiet#", FileId(0)).unwrap();
    let span = Span {
        start: 0,
        end: source.len() as u32,
    };
    for symbol in [root, quiet] {
        b.facts.symbols[symbol.index()].kind = 13;
        b.facts.symbols[symbol.index()].flags = SYMBOL_DEFINED | SYMBOL_SCALA_PARENTS_COMPLETE;
        b.facts.symbols[symbol.index()].span = span;
    }
    b.facts.symbols[helper.index()].kind = 3;
    b.facts.symbols[helper.index()].flags = SYMBOL_DEFINED;
    b.facts.symbols[helper.index()].owner = root;
    b.facts.symbols[helper.index()].span = span;
    b.facts.operands.push(ValueId(1));
    let op = |body, opcode, target, a| OperationRecord {
        body,
        opcode,
        target,
        a,
        dest: ValueId::NONE,
        b: ValueId::NONE,
        arguments: IdRange::default(),
        span: Span { start: 16, end: 24 },
        flags: 0,
    };
    b.facts
        .operations
        .push(op(BodyId(0), Opcode::Call, helper, ValueId(0)));
    b.facts.operations.push(op(
        BodyId(1),
        Opcode::InvokeCallback,
        SymbolId::NONE,
        ValueId(1),
    ));
    for (index, symbol) in [root, helper, quiet].into_iter().enumerate() {
        b.facts.bodies.push(BodyRecord {
            symbol,
            file: FileId(0),
            span,
            name_span: span,
            operations: IdRange {
                start: index.min(2) as u32,
                len: u32::from(index < 2),
            },
            parameters: if symbol == helper {
                IdRange { start: 0, len: 1 }
            } else {
                IdRange::default()
            },
            body_hash: ContentHash([index as u8 + 1; 32]),
            flags: if symbol == helper {
                0
            } else {
                BODY_INITIALIZER
            },
        });
    }
    for (symbol, name) in [(root, "fixture.Guarded"), (quiet, "fixture.Quiet")] {
        let name = b.intern(name).unwrap();
        b.facts.suites.push(SuiteRecord {
            name,
            symbol,
            file: FileId(0),
            flags: 0,
        });
    }
    if ambiguous {
        b.facts.symbols.push(b.facts.symbols[root.index()]);
    }
    let mut facts = b.finish().unwrap();
    let fact_path = directory.join("facts.bin");
    facts.identity = selector_facts::codec::write(&fact_path, &facts).unwrap();
    let mut graph = selector_graph_build::build(
        &facts,
        &selector_graph_build::BuildOptions {
            workers: 1,
            include_models: false,
        },
    )
    .unwrap();
    let root_node = graph.node_for_symbol(root).unwrap();
    let helper_node = graph.node_for_symbol(helper).unwrap();
    let quiet_node = graph.node_for_symbol(quiet).unwrap();
    let graph_path = directory.join("graph.bin");
    graph.identity = selector_graph::codec::write(&graph_path, &graph).unwrap();
    Fixture {
        facts,
        graph,
        fact_path,
        graph_path,
        root: root_node,
        helper: helper_node,
        quiet: quiet_node,
    }
}
fn base_command(f: &Fixture, output: &Path) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_selector"));
    command
        .arg("probe-root")
        .arg("--facts")
        .arg(&f.fact_path)
        .arg("--graph")
        .arg(&f.graph_path)
        .arg("--output")
        .arg(output);
    command
}
fn command(f: &Fixture, root: NodeId, output: &Path) -> Command {
    let mut command = base_command(f, output);
    command.arg("--root-node").arg(root.0.to_string());
    command
}
fn symbol_command(f: &Fixture, symbol: &str, context: Option<&str>, output: &Path) -> Command {
    let mut command = base_command(f, output);
    command.args(["--root-symbol", symbol]);
    if let Some(context) = context {
        command.args(["--root-context", context]);
    }
    command
}
fn pooled_text(facts: &mut selector_facts::FactSnapshot, text: &str) -> StrId {
    let id = StrId::checked(facts.strings.entries.len()).unwrap();
    facts.strings.entries.push(selector_facts::TextRange {
        start: facts.strings.bytes.len() as u64,
        len: text.len() as u32,
    });
    facts.strings.bytes.extend_from_slice(text.as_bytes());
    id
}
fn additional_root_context(mut f: Fixture, context: &str) -> (Fixture, NodeId) {
    let root_symbol = f.graph.nodes[f.root.index()].symbol;
    let helper_symbol = f.graph.nodes[f.helper.index()].symbol;
    let quiet_symbol = f.graph.nodes[f.quiet.index()].symbol;
    let context = pooled_text(&mut f.facts, context);
    let file = FileId::checked(f.facts.files.len()).unwrap();
    f.facts.files.push(FileRecord {
        context,
        ..f.facts.files[0]
    });
    let symbol = SymbolId::checked(f.facts.symbols.len()).unwrap();
    f.facts.symbols.push(selector_facts::SymbolRecord {
        context,
        file,
        ..f.facts.symbols[root_symbol.index()]
    });
    let body = f.facts.bodies[f.graph.nodes[f.root.index()].body.index()];
    f.facts.bodies.push(BodyRecord {
        symbol,
        file,
        operations: IdRange {
            start: f.facts.operations.len() as u32,
            len: 0,
        },
        ..body
    });
    f.facts.suites.push(SuiteRecord {
        symbol,
        file,
        ..f.facts.suites[0]
    });
    f.fact_path = f.fact_path.with_file_name("context-facts.bin");
    f.graph_path = f.graph_path.with_file_name("context-graph.bin");
    f.facts.identity = selector_facts::codec::write(&f.fact_path, &f.facts).unwrap();
    f.graph = selector_graph_build::build(
        &f.facts,
        &selector_graph_build::BuildOptions {
            workers: 1,
            include_models: false,
        },
    )
    .unwrap();
    f.graph.identity = selector_graph::codec::write(&f.graph_path, &f.graph).unwrap();
    f.root = f.graph.node_for_symbol(root_symbol).unwrap();
    f.helper = f.graph.node_for_symbol(helper_symbol).unwrap();
    f.quiet = f.graph.node_for_symbol(quiet_symbol).unwrap();
    let added = f.graph.node_for_symbol(symbol).unwrap();
    (f, added)
}
fn success(command: &mut Command) -> Output {
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    output
}
fn json(path: &Path) -> serde_json::Value {
    serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap()
}
fn failure(command: &mut Command, expected: &str) {
    let output = command.output().unwrap();
    assert!(!output.status.success());
    let error = String::from_utf8_lossy(&output.stderr);
    assert!(error.contains(expected), "{error}");
}

#[test]
fn probe_matches_full_solver_actual_boundary_without_catalogue_or_exclusion_claims() {
    let directory = tempfile::tempdir().unwrap();
    let f = fixture(directory.path(), false);
    let output = directory.path().join("probe.json");
    success(&mut command(&f, f.root, &output));
    let probe = json(&output);
    assert_eq!(probe["report_kind"], "root_execution_probe");
    assert_eq!(probe["diagnostic_only"], true);
    assert_eq!(probe["omission_authority"], false);
    assert_eq!(probe["scope"]["requested_roots"], 1);
    assert_eq!(probe["scope"]["unrequested_roots"], "not_analyzed");
    assert!(probe.get("decisions").is_none() && probe.get("suites").is_none());
    assert_eq!(probe["root"]["receiver_symbol"], "fixture/Guarded#");
    assert_eq!(probe["root"]["receiver_source"], "runnable_suite_symbol");
    assert_eq!(probe["limits"]["query_owned_bytes"], 64 * 1024 * 1024);
    let options = selector_solve::SolveOptions {
        workers: 1,
        retain_context_evidence: false,
        ..Default::default()
    };
    let mut full = selector_solve::QuerySession::new(&f.facts, &f.graph, &options).unwrap();
    let result = full.analyze(&[]).unwrap();
    assert_eq!(
        probe["guard_census"]["total"],
        result.obligations.len() as u64
    );
    assert_eq!(probe["guard_census"]["all_reported_rows_counted"], true);
    assert_eq!(probe["guard_census"]["fixed_point_reached"], true);
    assert_eq!(probe["finalization_census"]["fixed_point_reached"], true);
    assert_eq!(probe["finalization_census"]["requested_root_nodes"], 1);
    assert_eq!(
        probe["finalization_census"]["reported_guarded_requested_root_nodes"],
        1
    );
    assert_eq!(
        probe["finalization_census"]["guard_free_fixed_point_requested_root_nodes"],
        0
    );
    assert_eq!(
        probe["finalization_census"]["current_transfer_failures_reconstructed"],
        false
    );
    assert!(
        probe["current_local_transfer_audit"].is_null(),
        "fresh transfer audit is opt in"
    );
    let first_sites = &probe["runtime_first_site_census"];
    assert_eq!(first_sites["saved_first_sites"], 1);
    assert_eq!(first_sites["all_saved_first_sites_counted"], true);
    assert_eq!(
        first_sites["total_retained_contexts"],
        probe["metrics"]["contexts"]
    );
    assert_eq!(
        first_sites["evaluation_events"],
        probe["metrics"]["evaluations"]
    );
    assert_eq!(
        first_sites["reevaluation_events"],
        probe["metrics"]["reevaluations"]
    );
    assert_eq!(
        first_sites["unique_evaluated_contexts"],
        serde_json::Value::Null
    );
    assert_eq!(first_sites["is_current_failure_census"], false);
    assert_eq!(first_sites["is_current_root_cause_census"], false);
    assert_eq!(
        first_sites["by_reason"][0]["reason"],
        "unknown_callback_value"
    );
    assert_eq!(
        first_sites["by_reason"][0]["exemplar"]["operation"]["id"],
        1
    );
    assert_eq!(
        probe["guard_census"]["runtime_reasons"]["basis"],
        "root_guard_exemplars"
    );
    assert_eq!(
        probe["guard_census"]["runtime_reasons"]["all_context_first_sites_available"],
        false
    );
    let cause = result
        .evidence
        .guard_causes
        .iter()
        .find(|cause| cause.root == f.root)
        .unwrap();
    let site = cause.runtime.unwrap();
    let boundary = &probe["boundaries"][0];
    assert_eq!(boundary["runtime"]["reason"], site.reason.as_str());
    assert_eq!(boundary["runtime"]["operation"]["id"], site.operation.0);
    assert_eq!(boundary["runtime"]["operation"]["opcode"], "InvokeCallback");
    assert_eq!(boundary["runtime"]["operation"]["path"], "Probe.scala");
    assert_eq!(
        boundary["runtime"]["operation"]["span"],
        serde_json::json!({"start":16,"end":24})
    );
    assert!(probe["metrics"]["states"].as_u64().unwrap() < result.metrics.states);
    success(&mut command(&f, f.helper, &output));
    assert_eq!(json(&output)["root"]["receiver_source"], "none");
    success(command(&f, f.helper, &output).args(["--receiver-symbol", "fixture/Guarded#"]));
    assert_eq!(
        json(&output)["root"]["receiver_source"],
        "explicit_exact_symbol"
    );
}

#[test]
fn probe_budget_checkpoint_resume_and_replay_keep_exact_root_binding() {
    let directory = tempfile::tempdir().unwrap();
    let f = fixture(directory.path(), false);
    let stopped = directory.path().join("stopped.json");
    let checkpoints = directory.path().join("checkpoints");
    success(
        command(&f, f.root, &stopped)
            .args(["--max-steps", "1"])
            .arg("--checkpoint-dir")
            .arg(&checkpoints),
    );
    let partial = json(&stopped);
    assert_eq!(partial["completion"], "ResourceLimited");
    assert_eq!(partial["stop"], "StepLimit");
    assert_eq!(partial["stop_detail"]["resource"], "operations");
    assert_eq!(partial["stop_detail"]["limit"], 1);
    assert_eq!(partial["fixed_point_complete"], false);
    assert_eq!(partial["omission_authority"], false);
    assert_eq!(partial["guard_census"]["fixed_point_reached"], false);
    assert_eq!(partial["guard_census"]["all_reported_rows_counted"], true);
    assert_eq!(partial["finalization_census"]["fixed_point_reached"], false);
    assert!(
        partial["finalization_census"]["guard_free_fixed_point_requested_root_nodes"].is_null()
    );
    assert_eq!(partial["runtime_first_site_census"]["partial"], true);
    assert_eq!(
        partial["runtime_first_site_census"]["fixed_point_reached"],
        false
    );
    assert_eq!(
        partial["runtime_first_site_census"]["all_saved_first_sites_counted"],
        true
    );
    let output = directory.path().join("resumed.json");
    let bundle = directory.path().join("bundle");
    success(
        symbol_command(&f, "fixture/Guarded#", Some("fixture/test"), &output)
            .arg("--resume-dir")
            .arg(&checkpoints)
            .arg("--replay-bundle")
            .arg(&bundle)
            .arg("--replay-node")
            .arg(f.root.0.to_string()),
    );
    assert_eq!(json(&output)["completion"], "Conservative");
    assert!(bundle.join("metadata.json").is_file());
    success(
        Command::new(env!("CARGO_BIN_EXE_selector"))
            .arg("transfer-replay")
            .arg("--bundle")
            .arg(&bundle)
            .arg("--output")
            .arg(directory.path().join("replayed.json")),
    );
    failure(
        command(&f, f.quiet, &output)
            .arg("--resume-dir")
            .arg(&checkpoints),
        "checkpoint",
    );
    failure(
        command(&f, f.root, &output)
            .arg("--replay-bundle")
            .arg(directory.path().join("not-executed"))
            .arg("--replay-node")
            .arg(f.quiet.0.to_string()),
        "replay",
    );
}

#[test]
fn opt_in_current_local_audit_is_bounded_and_has_no_root_proof_authority() {
    let directory = tempfile::tempdir().unwrap();
    let f = fixture(directory.path(), false);
    let output = directory.path().join("audit.json");
    success(command(&f, f.root, &output).arg("--current-local-audit"));
    let probe = json(&output);
    let audit = &probe["current_local_transfer_audit"];
    assert_eq!(audit["complete"], true);
    assert_eq!(audit["status"], "complete");
    assert_eq!(audit["audited_contexts"], probe["metrics"]["contexts"]);
    assert_eq!(audit["contexts_with_current_local_issues"], 1);
    assert_eq!(
        audit["first_current_issue_by_reason"][0]["reason"],
        "unknown_callback_value"
    );
    assert_eq!(audit["root_path_proof"], false);
    assert_eq!(audit["selection_authority"], false);
    let ranking = &audit["first_current_site_ranking"];
    assert_eq!(ranking["audit_complete"], true);
    assert_eq!(ranking["sampling"], false);
    assert_eq!(ranking["total_contexts"], 1);
    assert_eq!(ranking["reported_contexts"], 1);
    assert_eq!(ranking["other_contexts"], 0);
    assert_eq!(ranking["top"][0]["contexts"], 1);
    assert_eq!(
        ranking["top"][0]["definition"]["symbol"],
        "fixture/Guarded#callback()."
    );
    assert_eq!(
        ranking["top"][0]["operation_detail"]["opcode"],
        "InvokeCallback"
    );
    assert_eq!(
        ranking["top"][0]["operation_detail"]["span"],
        serde_json::json!({"start":16,"end":24})
    );
    assert_eq!(probe["guarded"], true);
    assert_eq!(
        probe["runtime_first_site_census"]["is_current_failure_census"],
        false
    );
    success(command(&f, f.quiet, &output).arg("--current-local-audit"));
    let quiet = json(&output);
    assert_eq!(
        quiet["current_local_transfer_audit"]["contexts_with_current_local_issues"],
        0
    );
    assert_eq!(
        quiet["finalization_census"]["guard_free_fixed_point_requested_root_nodes"],
        1
    );
    success(command(&f, f.root, &output).args([
        "--current-local-audit",
        "--audit-max-contexts",
        "1",
    ]));
    let skipped = json(&output);
    assert_eq!(skipped["current_local_transfer_audit"]["complete"], false);
    assert_eq!(
        skipped["current_local_transfer_audit"]["status"],
        "not_run_context_limit"
    );
    assert_eq!(
        skipped["current_local_transfer_audit"]["audited_contexts"],
        0
    );
    assert_eq!(skipped["guarded"], true);
    failure(
        command(&f, f.root, &output).args(["--audit-max-contexts", "1"]),
        "require --current-local-audit",
    );
}

#[test]
fn current_audit_ranking_text_is_bounded_at_utf8_boundaries() {
    let directory = tempfile::tempdir().unwrap();
    let mut f = fixture(directory.path(), false);
    let name = format!("fixture/Guarded#{}().", "é".repeat(400));
    let name = pooled_text(&mut f.facts, &name);
    let helper_symbol = f.graph.nodes[f.helper.index()].symbol;
    f.facts.symbols[helper_symbol.index()].name = name;
    f.fact_path = directory.path().join("long-facts.bin");
    f.graph_path = directory.path().join("long-graph.bin");
    f.facts.identity = selector_facts::codec::write(&f.fact_path, &f.facts).unwrap();
    f.graph.facts_identity = f.facts.identity;
    f.graph.identity = selector_graph::codec::write(&f.graph_path, &f.graph).unwrap();
    let output = directory.path().join("long-audit.json");
    success(command(&f, f.root, &output).arg("--current-local-audit"));
    let value = json(&output);
    let definition = &value["current_local_transfer_audit"]["first_current_site_ranking"]["top"][0]
        ["definition"];
    assert_eq!(definition["text_truncated"], true);
    let clipped = definition["symbol"].as_str().unwrap();
    assert!(clipped.len() <= 512 && clipped.ends_with('é'));
    assert!(clipped.starts_with("fixture/Guarded#"));
}

#[test]
fn census_counts_all_obligations_beyond_bounded_examples_without_runtime_inference() {
    let directory = tempfile::tempdir().unwrap();
    let mut f = fixture(directory.path(), false);
    let symbol = f.graph.nodes[f.root.index()].symbol;
    for index in (0..40).rev() {
        let detail = pooled_text(&mut f.facts, &format!("static detail {index:02}"));
        f.facts.issues.push(selector_facts::IssueRecord {
            kind: IssueKind::UnknownExecution,
            file: FileId(0),
            symbol,
            detail,
        });
    }
    f.fact_path = directory.path().join("census-facts.bin");
    f.graph_path = directory.path().join("census-graph.bin");
    f.facts.identity = selector_facts::codec::write(&f.fact_path, &f.facts).unwrap();
    f.graph = selector_graph_build::build(
        &f.facts,
        &selector_graph_build::BuildOptions {
            workers: 1,
            include_models: false,
        },
    )
    .unwrap();
    f.graph.identity = selector_graph::codec::write(&f.graph_path, &f.graph).unwrap();
    f.root = f.graph.node_for_symbol(symbol).unwrap();
    let output = directory.path().join("census-probe.json");
    success(&mut command(&f, f.root, &output));
    let result = json(&output);
    assert_eq!(result["obligations_total"], 41);
    assert_eq!(result["obligations_truncated"], true);
    assert_eq!(result["obligations"].as_array().unwrap().len(), 32);
    let census = &result["guard_census"];
    assert_eq!(census["total"], 41);
    assert_eq!(census["by_kind"][0]["kind"], "UnknownExecution");
    assert_eq!(census["by_kind"][0]["count"], 41);
    assert_eq!(census["detail_groups"]["total_groups"], 40);
    assert_eq!(census["detail_groups"]["reported_groups"], 16);
    assert_eq!(census["detail_groups"]["reported_rows"], 16);
    assert_eq!(census["detail_groups"]["other_rows"], 24);
    assert_eq!(census["detail_groups"]["null_detail_rows"], 1);
    assert_eq!(census["detail_groups"]["empty_detail_rows"], 0);
    assert_eq!(census["detail_groups"]["truncated"], true);
    assert_eq!(
        census["detail_groups"]["top"][0]["detail"],
        "static detail 00"
    );
    assert_eq!(
        census["detail_groups"]["top"][15]["detail"],
        "static detail 15"
    );
    assert_eq!(result["boundaries"][0]["runtime"], serde_json::Value::Null);
    assert_eq!(census["runtime_reasons"]["without_runtime_site"], 1);
    assert_eq!(census["runtime_reasons"]["with_runtime_site"], 0);
    assert_eq!(
        census["runtime_reasons"]["by_reason"],
        serde_json::json!([])
    );
    assert_eq!(
        census["runtime_reasons"]["all_context_first_sites_available"],
        false
    );
    assert_eq!(
        census["runtime_reasons"]["all_runtime_occurrences_counted"],
        false
    );
    // The static first root guard does not hide the helper's retained runtime
    // first site, and the wider history is not relabeled as a root-path cause.
    let first_sites = &result["runtime_first_site_census"];
    assert_eq!(first_sites["saved_first_sites"], 1);
    assert_eq!(
        first_sites["by_reason"][0]["reason"],
        "unknown_callback_value"
    );
    assert_eq!(first_sites["by_reason"][0]["count"], 1);
    assert_eq!(
        first_sites["by_reason"][0]["exemplar"]["operation"]["opcode"],
        "InvokeCallback"
    );
    assert_eq!(first_sites["is_current_root_cause_census"], false);
    assert_eq!(result["diagnostic_only"], true);
    assert_eq!(result["omission_authority"], false);
}

#[test]
fn stable_compiler_symbol_lookup_requires_exact_context_when_ambiguous() {
    let directory = tempfile::tempdir().unwrap();
    let (f, other) =
        additional_root_context(fixture(directory.path(), false), "fixture/other-test");
    let output = directory.path().join("symbol.json");
    failure(
        &mut symbol_command(&f, "fixture/Guarded#", None, &output),
        "ambiguous",
    );
    assert!(!output.exists());
    for (context, node) in [("fixture/test", f.root), ("fixture/other-test", other)] {
        success(&mut symbol_command(
            &f,
            "fixture/Guarded#",
            Some(context),
            &output,
        ));
        let probe = json(&output);
        assert_eq!(probe["root"]["binding"]["node"], node.0);
        assert_eq!(probe["root"]["binding"]["symbol"], "fixture/Guarded#");
        assert_eq!(probe["root"]["binding"]["context"], context);
        assert_eq!(probe["root"]["receiver_symbol"], "fixture/Guarded#");
        assert_eq!(probe["root"]["receiver_source"], "runnable_suite_symbol");
        assert_eq!(probe["diagnostic_only"], true);
        assert_eq!(probe["omission_authority"], false);
        assert_eq!(probe["limits"]["query_owned_bytes"], 64 * 1024 * 1024);
    }
    let previous = std::fs::read(&output).unwrap();
    failure(
        &mut symbol_command(&f, "fixture/Guarded#", Some("fixture/missing"), &output),
        "no exact match",
    );
    assert_eq!(std::fs::read(&output).unwrap(), previous);
    failure(
        &mut symbol_command(&f, "fixture.Missing", Some("fixture/test"), &output),
        "no exact match",
    );
    let duplicate = fixture(&directory.path().join("same-context-duplicate"), true);
    failure(
        &mut symbol_command(
            &duplicate,
            "fixture/Guarded#",
            Some("fixture/test"),
            &output,
        ),
        "ambiguous",
    );
}

#[test]
fn stable_root_selector_rejects_invalid_combinations_and_unbound_symbols() {
    let directory = tempfile::tempdir().unwrap();
    let mut f = fixture(directory.path(), false);
    let output = directory.path().join("invalid.json");
    failure(
        &mut base_command(&f, &output),
        "one of --root-node or --root-symbol is required",
    );
    failure(
        command(&f, f.root, &output).args(["--root-symbol", "fixture/Guarded#"]),
        "mutually exclusive",
    );
    failure(
        command(&f, f.root, &output).args(["--root-context", "fixture/test"]),
        "requires --root-symbol",
    );
    failure(
        &mut symbol_command(&f, "", None, &output),
        "cannot be empty",
    );
    failure(
        &mut symbol_command(&f, "fixture/Missing#", None, &output),
        "no exact match",
    );
    assert!(!output.exists());
    success(&mut symbol_command(&f, "fixture/Guarded#", None, &output));
    assert_eq!(json(&output)["root"]["binding"]["node"], f.root.0);
    success(
        symbol_command(&f, "fixture/Guarded#callback().", None, &output)
            .args(["--receiver-symbol", "fixture/Guarded#"]),
    );
    assert_eq!(
        json(&output)["root"]["receiver_source"],
        "explicit_exact_symbol"
    );
    let name = pooled_text(&mut f.facts, "fixture/Unbound#");
    let root = f.facts.symbols[f.graph.nodes[f.root.index()].symbol.index()];
    f.facts
        .symbols
        .push(selector_facts::SymbolRecord { name, ..root });
    f.graph.symbol_nodes.push(NodeId::NONE);
    f.fact_path = f.fact_path.with_file_name("unbound-facts.bin");
    f.graph_path = f.graph_path.with_file_name("unbound-graph.bin");
    f.facts.identity = selector_facts::codec::write(&f.fact_path, &f.facts).unwrap();
    f.graph.facts_identity = f.facts.identity;
    f.graph.identity = selector_graph::codec::write(&f.graph_path, &f.graph).unwrap();
    failure(
        &mut symbol_command(&f, "fixture/Unbound#", Some("fixture/test"), &output),
        "no bound graph node",
    );
}

#[test]
fn probe_rejects_wrong_node_identity_ambiguous_receiver_and_selection_flags() {
    let directory = tempfile::tempdir().unwrap();
    let f = fixture(&directory.path().join("normal"), false);
    let output = directory.path().join("failure.json");
    failure(
        &mut command(&f, NodeId(9999), &output),
        "outside graph inventory",
    );
    failure(
        command(&f, f.root, &output).args(["--receiver-symbol", "fixture/Missing#"]),
        "no exact match",
    );
    for flag in ["--all-roots", "--plan-only", "--full-report"] {
        failure(command(&f, f.root, &output).arg(flag), "does not accept");
    }
    failure(
        command(&f, f.root, &output)
            .arg("--receipt")
            .arg(directory.path().join("receipt.json")),
        "does not accept",
    );
    assert!(!output.exists());
    let ambiguous = fixture(&directory.path().join("ambiguous"), true);
    failure(
        command(&ambiguous, ambiguous.root, &output)
            .args(["--receiver-symbol", "fixture/Guarded#"]),
        "ambiguous",
    );
    // Rebuild a command with the other snapshot's facts to avoid duplicate options.
    let mut wrong = Command::new(env!("CARGO_BIN_EXE_selector"));
    wrong
        .arg("probe-root")
        .arg("--facts")
        .arg(&ambiguous.fact_path)
        .arg("--graph")
        .arg(&f.graph_path)
        .arg("--root-node")
        .arg(f.root.0.to_string())
        .arg("--output")
        .arg(&output);
    failure(&mut wrong, "graph fact identity binding");
}
