use super::*;
use selector_facts::{BodyRecord, FactBuilder, FileRecord, OperationRecord};
use selector_graph::{EdgeRecord, GraphIssue, NodeRecord};

fn fixture(
    opcode: Option<Opcode>,
    edge_kind: EdgeKind,
) -> (FactSnapshot, ProgramGraph, Vec<PlannedRoot>) {
    let mut b = FactBuilder::new();
    for name in ["Root.scala", "Other.scala"] {
        let path = b.intern(name).unwrap();
        let source = b.intern("class Root").unwrap();
        b.facts.files.push(FileRecord {
            path,
            source,
            revision: StrId::NONE,
            context: StrId::NONE,
            source_hash: ContentHash([1; 32]),
            flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
        });
    }
    let root = b.ensure_symbol("p/Root#", FileId(0)).unwrap();
    let helper = b.ensure_symbol("p/helper().", FileId(1)).unwrap();
    b.facts.symbols[root.index()].kind = 13;
    for symbol in [root, helper] {
        b.facts.symbols[symbol.index()].flags = SYMBOL_DEFINED;
    }
    if let Some(opcode) = opcode {
        b.facts.operations.push(OperationRecord {
            body: BodyId(0),
            opcode,
            target: helper,
            dest: ValueId(1),
            a: ValueId(0),
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span::default(),
            flags: 0,
        });
    }
    b.facts.bodies.push(BodyRecord {
        symbol: root,
        file: FileId(0),
        span: Span::default(),
        name_span: Span::default(),
        operations: IdRange {
            start: 0,
            len: u32::from(opcode.is_some()),
        },
        parameters: IdRange::default(),
        body_hash: ContentHash([3; 32]),
        flags: 0,
    });
    b.facts.identity = ContentHash([1; 32]);
    let facts = b.finish().unwrap();
    let mut graph = ProgramGraph {
        identity: ContentHash([2; 32]),
        facts_identity: facts.identity,
        nodes: vec![
            NodeRecord {
                symbol: root,
                file: FileId(0),
                body: BodyId(0),
                flags: 0,
            },
            NodeRecord {
                symbol: helper,
                file: FileId(1),
                body: BodyId::NONE,
                flags: 0,
            },
        ],
        symbol_nodes: vec![NodeId(0), NodeId(1)],
        edges: vec![EdgeRecord {
            source: NodeId(0),
            target: NodeId(1),
            kind: edge_kind,
            occurrence: OccurrenceId::NONE,
            operation: if opcode.is_some() {
                OperationId(0)
            } else {
                OperationId::NONE
            },
            receiver: SymbolId::NONE,
            flags: 0,
        }],
        issues: vec![GraphIssue {
            kind: IssueKind::UnknownExecution,
            node: NodeId(1),
            file: FileId(1),
            symbol: helper,
            detail: StrId::NONE,
        }],
        ..Default::default()
    };
    graph.index().unwrap();
    (
        facts,
        graph,
        vec![PlannedRoot {
            node: NodeId(0),
            receiver: root,
        }],
    )
}
#[test]
fn exact_call_and_initializer_paths_carry_real_issue_and_edge_ids() {
    for (opcode, kind) in [
        (Opcode::Call, EdgeKind::Call),
        (Opcode::Initialize, EdgeKind::Initialize),
    ] {
        let (facts, graph, roots) = fixture(Some(opcode), kind);
        let result = precheck(&facts, &graph, &roots, &RetentionLimits::default()).unwrap();
        assert!(result.all_roots_known_kept());
        assert_eq!(result.path(&result.roots()[0]).unwrap(), [EdgeId(0)]);
        assert_eq!(
            result.roots()[0].guard,
            Some(GuardReference {
                issue: 0,
                node: NodeId(1)
            })
        );
        result.validate(&facts, &graph).unwrap();
    }
}
#[test]
fn potential_virtual_callback_compile_and_reference_edges_are_not_guard_authority() {
    for kind in [
        EdgeKind::VirtualCall,
        EdgeKind::Callback,
        EdgeKind::Compile,
        EdgeKind::Field,
        EdgeKind::Return,
        EdgeKind::Guard,
    ] {
        let (facts, graph, roots) = fixture(None, kind);
        let result = precheck(&facts, &graph, &roots, &RetentionLimits::default()).unwrap();
        assert_eq!(result.eligible_roots(), 0, "{kind:?}");
        assert!(!result.all_roots_known_kept());
    }
    for (opcode, kind) in [
        (Opcode::VirtualCall, EdgeKind::Call),
        (Opcode::Call, EdgeKind::VirtualCall),
        (Opcode::BindCallback, EdgeKind::Call),
    ] {
        let (facts, graph, roots) = fixture(Some(opcode), kind);
        assert_eq!(
            precheck(&facts, &graph, &roots, &RetentionLimits::default())
                .unwrap()
                .eligible_roots(),
            0
        );
    }
}
#[test]
fn unrelated_file_hierarchy_and_malformed_scopes_never_certify() {
    let (facts, mut graph, roots) = fixture(None, EdgeKind::Compile);
    graph.issues[0].node = NodeId::NONE;
    assert_eq!(
        precheck(&facts, &graph, &roots, &RetentionLimits::default())
            .unwrap()
            .eligible_roots(),
        0
    );
    graph.issues[0].kind = IssueKind::IncompleteHierarchy;
    assert!(precheck(&facts, &graph, &roots, &RetentionLimits::default()).is_err());
    graph.issues[0].kind = IssueKind::UnknownExecution;
    graph.issues[0].file = FileId(999);
    assert!(precheck(&facts, &graph, &roots, &RetentionLimits::default()).is_err());
    graph.issues[0].file = FileId::NONE;
    graph.issues[0].symbol = SymbolId::NONE;
    let result = precheck(&facts, &graph, &roots, &RetentionLimits::default()).unwrap();
    assert!(result.all_roots_known_kept());
    assert_eq!(result.roots()[0].guard.unwrap().node, NodeId::NONE);
    result.validate(&facts, &graph).unwrap();
}
#[test]
fn resealed_virtual_path_and_wrong_issue_scope_are_rejected() {
    let (facts, mut graph, roots) = fixture(Some(Opcode::Call), EdgeKind::Call);
    graph.edges.push(EdgeRecord {
        kind: EdgeKind::VirtualCall,
        ..graph.edges[0]
    });
    graph.index().unwrap();
    let mut result = precheck(&facts, &graph, &roots, &RetentionLimits::default()).unwrap();
    let virtual_id = graph
        .edges
        .iter()
        .position(|edge| edge.kind == EdgeKind::VirtualCall)
        .unwrap();
    result.edges[0] = EdgeId(virtual_id as u32);
    result.identity = seal(&result);
    assert!(result.validate(&facts, &graph).is_err());
    let mut result = precheck(&facts, &graph, &roots, &RetentionLimits::default()).unwrap();
    result.roots[0].guard.as_mut().unwrap().node = NodeId(0);
    result.identity = seal(&result);
    assert!(result.validate(&facts, &graph).is_err());
}
#[test]
fn exact_target_and_no_body_complete_contract_are_checked() {
    let (mut facts, graph, roots) = fixture(Some(Opcode::Call), EdgeKind::Call);
    facts.operations[0].target = SymbolId(0);
    assert_eq!(
        precheck(&facts, &graph, &roots, &RetentionLimits::default())
            .unwrap()
            .eligible_roots(),
        0
    );
    let (facts, mut graph, roots) = fixture(None, EdgeKind::Initialize);
    graph.nodes[0].body = BodyId::NONE;
    graph.nodes[0].flags = NODE_EFFECTS_COMPLETE;
    assert_eq!(
        precheck(&facts, &graph, &roots, &RetentionLimits::default())
            .unwrap()
            .eligible_roots(),
        0
    );
    graph.edges[0].target = NodeId::NONE;
    assert!(precheck(&facts, &graph, &roots, &RetentionLimits::default()).is_err());
}
#[test]
fn mixed_missing_and_bounded_roots_stay_explicitly_unproved() {
    let (facts, graph, mut roots) = fixture(None, EdgeKind::Initialize);
    roots.push(PlannedRoot {
        node: NodeId::NONE,
        receiver: SymbolId(0),
    });
    let result = precheck(&facts, &graph, &roots, &RetentionLimits::default()).unwrap();
    assert_eq!(result.eligible_roots(), 1);
    assert!(!result.all_roots_known_kept());
    assert_eq!(
        result.roots()[1].unproved,
        Some(UnprovedReason::MissingRoot)
    );
    let limits = RetentionLimits {
        max_path_edges: 0,
        ..RetentionLimits::default()
    };
    assert_eq!(
        precheck(&facts, &graph, &roots, &limits)
            .unwrap()
            .eligible_roots(),
        0
    );
    let limits = RetentionLimits {
        memory_budget_bytes: 1,
        ..RetentionLimits::default()
    };
    assert!(matches!(
        precheck(&facts, &graph, &roots, &limits),
        Err(Error::Limit(_))
    ));
}
