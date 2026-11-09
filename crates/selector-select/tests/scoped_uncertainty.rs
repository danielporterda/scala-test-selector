//! Exercise change admission, actual context solving, and final selection together.
use selector_facts::{
    BodyRecord, FactBuilder, FactSnapshot, FileRecord, IssueRecord, OperationRecord, SuiteRecord,
};
use selector_graph::{EdgeRecord, GraphIssue, NodeRecord, ProgramGraph};
use selector_result::{AnalysisResult, SelectionResult};
use selector_select::{ChangeSeeds, changed_seeds, select};
use selector_solve::{AnalysisSeeds, QuerySession, SolveOptions};
use selector_types::*;

fn snapshot(
    issue_symbol: SymbolId,
    kind: IssueKind,
    changed_body: bool,
    represented: bool,
) -> (FactSnapshot, ProgramGraph) {
    let mut b = FactBuilder::new();
    let path = b.intern("Suites.scala").unwrap();
    let source = b
        .intern("class ActiveSuite; class OtherSuite; def called = (); def dormant = ()")
        .unwrap();
    b.facts.files.push(FileRecord {
        path,
        source,
        revision: StrId::NONE,
        context: StrId::NONE,
        source_hash: ContentHash([if changed_body { 2 } else { 1 }; 32]),
        flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
    });
    for (i, name) in [
        "p/ActiveSuite#",
        "p/OtherSuite#",
        "p/ActiveSuite#called().",
        "p/ActiveSuite#dormant().",
        "external/Passive#",
    ]
    .iter()
    .enumerate()
    {
        let id = b.ensure_symbol(name, FileId(0)).unwrap();
        let symbol = &mut b.facts.symbols[id.index()];
        symbol.kind = if i < 2 { 13 } else { 3 };
        if i < 4 {
            symbol.file = FileId(0);
            symbol.flags = SYMBOL_DEFINED;
        }
        if matches!(i, 2 | 3) {
            symbol.owner = SymbolId(0);
        }
    }
    for symbol in 0..4 {
        let start = b.facts.operations.len() as u32;
        if symbol == 0 || SymbolId(symbol) == issue_symbol {
            b.facts.operations.push(OperationRecord {
                body: BodyId(symbol),
                opcode: if symbol == 0 {
                    Opcode::Call
                } else {
                    Opcode::Unknown
                },
                target: if symbol == 0 {
                    SymbolId(2)
                } else {
                    SymbolId::NONE
                },
                dest: ValueId::NONE,
                a: ValueId::NONE,
                b: ValueId::NONE,
                arguments: IdRange::default(),
                span: Span::default(),
                flags: 0,
            });
        }
        b.facts.bodies.push(BodyRecord {
            symbol: SymbolId(symbol),
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange {
                start,
                len: b.facts.operations.len() as u32 - start,
            },
            parameters: IdRange::default(),
            body_hash: ContentHash(
                [if changed_body && SymbolId(symbol) == issue_symbol {
                    2
                } else {
                    1
                }; 32],
            ),
            flags: if symbol < 2 {
                BODY_INITIALIZER
            } else {
                BODY_DEFERRED
            },
        });
    }
    for (symbol, name) in [(0, "p.ActiveSuite"), (1, "p.OtherSuite")] {
        let name = b.intern(name).unwrap();
        b.facts.suites.push(SuiteRecord {
            name,
            symbol: SymbolId(symbol),
            file: FileId(0),
            flags: 0,
        });
    }
    let detail = b.intern("exact incomplete executable recipe").unwrap();
    b.facts.issues.push(IssueRecord {
        kind,
        file: FileId(0),
        symbol: issue_symbol,
        detail,
    });
    let facts = b.finish().unwrap();
    let mut graph = ProgramGraph {
        facts_identity: facts.identity,
        ..Default::default()
    };
    for i in 0..5 {
        graph.nodes.push(NodeRecord {
            symbol: SymbolId(i),
            file: FileId(0),
            body: if i < 4 { BodyId(i) } else { BodyId::NONE },
            flags: 0,
        });
        graph.symbol_nodes.push(NodeId(i));
    }
    graph.edges.push(EdgeRecord {
        source: NodeId(0),
        target: NodeId(2),
        kind: EdgeKind::Call,
        operation: OperationId(0),
        occurrence: OccurrenceId::NONE,
        receiver: SymbolId::NONE,
        flags: 0,
    });
    if represented {
        graph.issues.push(GraphIssue {
            kind,
            node: if issue_symbol.is_none() {
                NodeId::NONE
            } else {
                NodeId(issue_symbol.0)
            },
            file: FileId(0),
            symbol: issue_symbol,
            detail,
        });
    }
    graph.index().unwrap();
    (facts, graph)
}

fn solve(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    execution: &[NodeId],
    declarations: &[NodeId],
    workers: usize,
) -> AnalysisResult {
    let mut session = QuerySession::new(
        facts,
        graph,
        &SolveOptions {
            workers,
            ..Default::default()
        },
    )
    .unwrap();
    session
        .analyze_typed(AnalysisSeeds {
            execution,
            declarations,
        })
        .unwrap()
}

fn selected(
    base: &FactSnapshot,
    bg: &ProgramGraph,
    head: &FactSnapshot,
    hg: &ProgramGraph,
    seeds: ChangeSeeds,
    workers: usize,
) -> SelectionResult {
    let b = solve(base, bg, &seeds.base, &seeds.base_compile, workers);
    let h = solve(head, hg, &seeds.head, &seeds.head_compile, workers);
    select(base, bg, head, hg, seeds, Some(b), h).unwrap()
}

#[test]
fn changed_dormant_recipe_preserves_obligations_without_guarding_other_roots() {
    for kind in [IssueKind::UnknownExecution, IssueKind::ContextConflict] {
        let (base, bg) = snapshot(SymbolId(3), kind, false, true);
        let (head, hg) = snapshot(SymbolId(3), kind, true, true);
        let seeds = changed_seeds(&base, &bg, &head, &hg, &["Suites.scala"]).unwrap();
        assert!(!seeds.conservative);
        assert_eq!(seeds.base, vec![NodeId(3)]);
        assert_eq!(seeds.head, vec![NodeId(3)]);
        assert_eq!(seeds.head_obligations.len(), 1);
        let result = selected(&base, &bg, &head, &hg, seeds, 2);
        assert_eq!(result.completion, Completion::Complete);
        assert!(result.suites.is_empty());
        assert!(result.head.guarded_roots.is_empty());
        assert!(!result.head.unscoped_uncertainty);
        assert!(
            result
                .head
                .obligations
                .iter()
                .any(|o| o.symbol == SymbolId(3) && o.kind == kind)
        );
    }
}

#[test]
fn changed_reached_recipe_guards_only_the_executing_suite() {
    let (base, bg) = snapshot(SymbolId(2), IssueKind::UnknownExecution, false, true);
    let (head, hg) = snapshot(SymbolId(2), IssueKind::UnknownExecution, true, true);
    for workers in [1, 4] {
        let seeds = changed_seeds(&base, &bg, &head, &hg, &["Suites.scala"]).unwrap();
        assert!(!seeds.conservative);
        let result = selected(&base, &bg, &head, &hg, seeds, workers);
        assert_eq!(result.completion, Completion::Conservative);
        assert_eq!(result.suites.len(), 1);
        assert_eq!(result.suites[0].suite, SuiteId(0));
        assert!(result.suites[0].guarded);
        assert_eq!(result.head.guarded_roots, vec![NodeId(0)]);
        assert!(result.head.contains(NodeId(0)));
        assert!(!result.head.unscoped_uncertainty);
    }
}

#[test]
fn missing_graph_boundary_or_passive_conflict_cannot_claim_execution_scope() {
    for (symbol, kind, represented) in [
        (SymbolId(3), IssueKind::UnknownExecution, false),
        (SymbolId(4), IssueKind::ContextConflict, true),
        (SymbolId::NONE, IssueKind::UnknownExecution, true),
    ] {
        let (base, bg) = snapshot(symbol, kind, false, represented);
        let (head, hg) = snapshot(symbol, kind, true, represented);
        let seeds = changed_seeds(&base, &bg, &head, &hg, &["Suites.scala"]).unwrap();
        assert!(seeds.conservative);
        let result = selected(&base, &bg, &head, &hg, seeds, 2);
        assert_eq!(result.suites.len(), 2);
        assert!(result.suites.iter().all(|suite| suite.guarded));
    }
}

#[test]
fn malformed_and_incomplete_source_admission_remains_global() {
    for kind in [
        IssueKind::InvalidInput,
        IssueKind::MissingSyntax,
        IssueKind::MissingSource,
        IssueKind::StaleSource,
        IssueKind::UnsupportedSchema,
        IssueKind::ResourceLimit,
    ] {
        let (base, bg) = snapshot(SymbolId(3), kind, false, true);
        let (head, hg) = snapshot(SymbolId(3), kind, true, true);
        let seeds = changed_seeds(&base, &bg, &head, &hg, &["Suites.scala"]).unwrap();
        assert!(seeds.conservative, "{kind:?}");
        assert_eq!(selected(&base, &bg, &head, &hg, seeds, 1).suites.len(), 2);
    }
    let (base, bg) = snapshot(SymbolId(3), IssueKind::UnknownExecution, false, true);
    let (mut head, hg) = snapshot(SymbolId(3), IssueKind::UnknownExecution, true, true);
    head.files[0].flags = SOURCE_VERIFIED;
    assert!(
        changed_seeds(&base, &bg, &head, &hg, &["Suites.scala"])
            .unwrap()
            .conservative
    );
}

#[test]
fn graph_boundary_requires_exact_detail_and_source_owner_identity() {
    let (base, bg) = snapshot(SymbolId(3), IssueKind::UnknownExecution, false, true);
    let (head, mut hg) = snapshot(SymbolId(3), IssueKind::UnknownExecution, true, true);
    hg.issues[0].detail = StrId::NONE;
    assert!(
        changed_seeds(&base, &bg, &head, &hg, &["Suites.scala"])
            .unwrap()
            .conservative
    );
    let (mut head, hg) = snapshot(SymbolId(3), IssueKind::UnknownExecution, true, true);
    head.symbols[3].file = FileId::NONE;
    assert!(
        changed_seeds(&base, &bg, &head, &hg, &["Suites.scala"])
            .unwrap()
            .conservative
    );
}
