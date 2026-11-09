use selector_facts::{BodyRecord, FactBuilder, FileRecord, OperationRecord, SuiteRecord};
use selector_graph::{EdgeRecord, GraphIssue, NodeRecord, ProgramGraph};
use selector_types::*;
use std::{
    path::PathBuf,
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

static SEQUENCE: AtomicU64 = AtomicU64::new(0);
struct Temp(PathBuf);
impl Temp {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "selector-retention-{}-{}",
            std::process::id(),
            SEQUENCE.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for Temp {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn inputs(temp: &Temp, kind: EdgeKind, second_root: bool) -> (PathBuf, PathBuf) {
    let mut b = FactBuilder::new();
    let path = b.intern("Root.scala").unwrap();
    let source = b.intern("class Root").unwrap();
    b.facts.files.push(FileRecord {
        path,
        source,
        revision: StrId::NONE,
        context: StrId::NONE,
        source_hash: ContentHash([1; 32]),
        flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
    });
    let root = b.ensure_symbol("p/Root#", FileId(0)).unwrap();
    let helper = b.ensure_symbol("p/helper().", FileId(0)).unwrap();
    b.facts.symbols[root.index()].kind = 13;
    b.facts.symbols[root.index()].flags = SYMBOL_DEFINED;
    let name = b.intern("p.Root").unwrap();
    b.facts.suites.push(SuiteRecord {
        name,
        symbol: root,
        file: FileId(0),
        flags: 0,
    });
    if second_root {
        let name = b.intern("p.Helper").unwrap();
        b.facts.suites.push(SuiteRecord {
            name,
            symbol: helper,
            file: FileId(0),
            flags: 0,
        });
    }
    b.facts.operations.push(OperationRecord {
        body: BodyId(0),
        opcode: if kind == EdgeKind::Call {
            Opcode::Call
        } else {
            Opcode::VirtualCall
        },
        target: helper,
        dest: ValueId(1),
        a: ValueId(0),
        b: ValueId::NONE,
        arguments: IdRange::default(),
        span: Span::default(),
        flags: 0,
    });
    b.facts.bodies.push(BodyRecord {
        symbol: root,
        file: FileId(0),
        span: Span::default(),
        name_span: Span::default(),
        operations: IdRange { start: 0, len: 1 },
        parameters: IdRange::default(),
        body_hash: ContentHash([2; 32]),
        flags: 0,
    });
    let facts = b.finish().unwrap();
    let facts_path = temp.0.join("facts.bin");
    let identity = selector_facts::codec::write(&facts_path, &facts).unwrap();
    let mut graph = ProgramGraph {
        facts_identity: identity,
        nodes: vec![
            NodeRecord {
                symbol: root,
                file: FileId(0),
                body: BodyId(0),
                flags: 0,
            },
            NodeRecord {
                symbol: helper,
                file: FileId(0),
                body: BodyId::NONE,
                flags: 0,
            },
        ],
        symbol_nodes: vec![NodeId(0), NodeId(1)],
        edges: vec![EdgeRecord {
            source: NodeId(0),
            target: NodeId(1),
            kind,
            operation: OperationId(0),
            occurrence: OccurrenceId::NONE,
            receiver: SymbolId::NONE,
            flags: 0,
        }],
        issues: vec![GraphIssue {
            kind: IssueKind::UnknownExecution,
            node: NodeId(1),
            file: FileId(0),
            symbol: helper,
            detail: StrId::NONE,
        }],
        ..Default::default()
    };
    graph.index().unwrap();
    let graph_path = temp.0.join("graph.bin");
    selector_graph::codec::write(&graph_path, &graph).unwrap();
    (facts_path, graph_path)
}
fn run(temp: &Temp, kind: EdgeKind, rows: &str) -> serde_json::Value {
    let (facts, graph) = inputs(temp, kind, rows == "1");
    let out = temp.0.join("diagnostic.json");
    let result = Command::new(env!("CARGO_BIN_EXE_selector"))
        .arg("retention-precheck")
        .arg("--facts")
        .arg(facts)
        .arg("--graph")
        .arg(graph)
        .arg("--output")
        .arg(&out)
        .arg("--inventory-rows")
        .arg(rows)
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    serde_json::from_slice(&std::fs::read(out).unwrap()).unwrap()
}
#[test]
fn explicit_command_reports_certified_paths_without_execution_or_selection() {
    let temp = Temp::new();
    let value = run(&temp, EdgeKind::Call, "32");
    assert_eq!(value["report_kind"], "retention_precheck");
    for name in [
        "analysis_not_performed",
        "diagnostic_only",
        "all_roots_known_kept",
        "complete",
    ] {
        assert_eq!(value[name], true, "{name}");
    }
    for name in ["fixed_point_complete", "omission_authority"] {
        assert_eq!(value[name], false, "{name}");
    }
    assert_eq!(value["counts"]["eligible"], 1);
    assert_eq!(value["counts"]["unproved"], 0);
    assert_eq!(value["roots"][0]["path"][0]["kind"], "Call");
    assert_eq!(value["metrics"]["transfer_evaluations"], 0);
    assert!(value.get("decisions").is_none());
    assert!(value.get("completion").is_none());
    assert_eq!(std::fs::read_dir(&temp.0).unwrap().count(), 3);
}
#[test]
fn potential_virtual_target_stays_unproved_and_truncated_rows_keep_full_counts() {
    let a = Temp::new();
    let value = run(&a, EdgeKind::VirtualCall, "32");
    assert_eq!(value["all_roots_known_kept"], false);
    assert_eq!(value["counts"]["unproved"], 1);
    let b = Temp::new();
    let value = run(&b, EdgeKind::Call, "1");
    assert_eq!(value["all_roots_known_kept"], true);
    assert_eq!(value["rows_complete"], false);
    assert_eq!(value["counts"]["eligible"], 2);
    assert_eq!(value["roots"].as_array().unwrap().len(), 1);
}
#[test]
fn execution_options_are_rejected_before_output_or_cache_creation() {
    let temp = Temp::new();
    let result = Command::new(env!("CARGO_BIN_EXE_selector"))
        .args([
            "retention-precheck",
            "--facts",
            "missing",
            "--graph",
            "missing",
            "--summary-cache",
        ])
        .arg(temp.0.join("cache"))
        .arg("--output")
        .arg(temp.0.join("out.json"))
        .output()
        .unwrap();
    assert!(!result.status.success());
    assert!(std::fs::read_dir(&temp.0).unwrap().next().is_none());
}
