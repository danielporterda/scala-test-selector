use super::*;

struct CompleteSummaries(ValuePool);
impl World for CompleteSummaries {
    fn values(&self) -> &ValuePool {
        &self.0
    }
    fn summary(
        &self,
        _: NodeId,
        _: Value,
        _: &[Value],
        _: &ValuePool,
        _: &mut Vec<Value>,
    ) -> SummaryRead {
        SummaryRead {
            context: None,
            value: Value::EMPTY,
            version: 1,
            present: true,
        }
    }
    fn slot(&self, _: Slot) -> (Value, u64, bool) {
        panic!("no heap access")
    }
    fn capture(&self, _: u32) -> Option<(Value, &[Value], u64)> {
        panic!("captures are local")
    }
    fn binding(
        &self,
        _: OperationId,
        _: Value,
        _: &[Value],
        _: &ValuePool,
        _: &mut Vec<Atom>,
        _: &mut Vec<Value>,
    ) -> Option<u32> {
        None
    }
}

fn fixture(flags: u32) -> (FactSnapshot, ProgramGraph) {
    fixture_for(flags, "external/framework#scope().")
}

pub(super) fn fixture_for(flags: u32, external_name: &str) -> (FactSnapshot, ProgramGraph) {
    let mut b = FactBuilder::new();
    let path = b.intern("Model.scala").unwrap();
    let source = b.intern(&" ".repeat(64)).unwrap();
    b.facts.files.push(FileRecord {
        path,
        source,
        revision: StrId::NONE,
        context: StrId::NONE,
        source_hash: ContentHash([1; 32]),
        flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
    });
    let root = b.ensure_symbol("p/root().", FileId(0)).unwrap();
    let external = b.ensure_symbol(external_name, FileId::NONE).unwrap();
    let callback = b.ensure_symbol("p/root().callback().", FileId(0)).unwrap();
    for id in [root, callback] {
        b.facts.symbols[id.index()].kind = 3;
        b.facts.symbols[id.index()].flags = SYMBOL_DEFINED;
    }
    b.facts
        .operands
        .extend([ValueId(2), ValueId(1), ValueId(2)]);
    b.facts.operations = vec![
        OperationRecord {
            body: BodyId(0),
            opcode: Opcode::Parameter,
            target: SymbolId::NONE,
            dest: ValueId(2),
            a: ValueId::NONE,
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span::default(),
            flags: 0,
        },
        OperationRecord {
            body: BodyId(0),
            opcode: Opcode::BindCallback,
            target: callback,
            dest: ValueId(1),
            a: ValueId::NONE,
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span::default(),
            flags: 0,
        },
        OperationRecord {
            body: BodyId(0),
            opcode: Opcode::Call,
            target: external,
            dest: ValueId(3),
            a: ValueId::NONE,
            b: ValueId::NONE,
            arguments: IdRange { start: 1, len: 2 },
            span: Span::default(),
            flags: 0,
        },
    ];
    for (symbol, operations, parameters) in [
        (
            root,
            IdRange { start: 0, len: 3 },
            IdRange { start: 0, len: 1 },
        ),
        (callback, IdRange { start: 3, len: 0 }, IdRange::default()),
    ] {
        b.facts.bodies.push(BodyRecord {
            symbol,
            file: FileId(0),
            span: Span { start: 0, end: 64 },
            name_span: Span::default(),
            operations,
            parameters,
            body_hash: ContentHash([2; 32]),
            flags: 0,
        });
    }
    let facts = b.finish().unwrap();
    let mut graph = ProgramGraph {
        facts_identity: facts.identity,
        ..Default::default()
    };
    graph.symbol_nodes = vec![NodeId(0), NodeId(1), NodeId(2)];
    graph.nodes = vec![
        NodeRecord {
            symbol: root,
            file: FileId(0),
            body: BodyId(0),
            flags: SYMBOL_DEFINED,
        },
        NodeRecord {
            symbol: external,
            file: FileId::NONE,
            body: BodyId::NONE,
            flags: 0,
        },
        NodeRecord {
            symbol: callback,
            file: FileId(0),
            body: BodyId(1),
            flags: SYMBOL_DEFINED,
        },
    ];
    graph.edges.push(EdgeRecord {
        source: NodeId(0),
        target: NodeId(1),
        kind: EdgeKind::Call,
        occurrence: OccurrenceId::NONE,
        operation: OperationId(2),
        receiver: SymbolId::NONE,
        flags,
    });
    graph.index().unwrap();
    (facts, graph)
}

fn run(flags: u32) -> Evaluation {
    let (facts, graph) = fixture(flags);
    let types = TypeIndex::new(&facts);
    let world = CompleteSummaries(ValuePool::new(16));
    let mut scratch = Scratch::new(16);
    let mut out = Evaluation::default();
    evaluate(
        &facts,
        &graph,
        &types,
        &world,
        NodeId(0),
        Value::EMPTY,
        &[Value::TOP],
        &mut scratch,
        &mut out,
    )
    .unwrap();
    out
}

#[test]
fn certified_actual_callback_executes_without_zero_invoking_unknown_implicit_carrier() {
    for model in [EDGE_CALLBACK_IMMEDIATE, EDGE_TEST_REGISTRATION] {
        let out = run(model | encode_callback_argument(0).unwrap());
        assert!(out.issues.is_empty(), "{:?}", out.first_issue);
        assert!(
            out.calls
                .iter()
                .any(|call| call.kind == EdgeKind::Callback && call.target == NodeId(2))
        );
        assert!(
            out.calls
                .iter()
                .any(|call| call.kind == EdgeKind::Call && call.target == NodeId(1))
        );
    }
}

#[test]
fn unknown_value_in_the_certified_callback_slot_still_guards() {
    let out = run(EDGE_TEST_REGISTRATION | encode_callback_argument(1).unwrap());
    assert!(out.issues.contains(&IssueKind::UnknownExecution));
    assert_eq!(
        out.first_issue.unwrap().reason,
        RuntimeIssueReason::UnknownCallbackValue
    );
    assert!(!out.calls.iter().any(|call| call.kind == EdgeKind::Callback));
}

#[test]
fn malformed_or_missing_certificates_keep_the_conservative_callback_scan() {
    for encoding in [
        0,
        encode_callback_argument(2).unwrap(),
        1 << CALLBACK_ARGUMENT_SHIFT,
    ] {
        let out = run(EDGE_TEST_REGISTRATION | encoding);
        assert!(out.issues.contains(&IssueKind::UnknownExecution));
        assert_eq!(
            out.first_issue.unwrap().reason,
            RuntimeIssueReason::UnknownCallbackValue
        );
        assert!(
            out.calls
                .iter()
                .any(|call| call.kind == EdgeKind::Callback && call.target == NodeId(2))
        );
    }
}

#[test]
fn ordinary_calls_ignore_callback_slot_bits() {
    let out = run(encode_callback_argument(0).unwrap());
    assert!(out.issues.is_empty());
    assert_eq!(out.calls.len(), 1);
    assert_eq!(out.calls[0].kind, EdgeKind::Call);
}

#[test]
fn a_slot_certificate_with_no_actual_arguments_must_guard() {
    let (mut facts, graph) = fixture(EDGE_TEST_REGISTRATION | encode_callback_argument(0).unwrap());
    facts.operations[2].arguments.len = 0;
    let types = TypeIndex::new(&facts);
    let world = CompleteSummaries(ValuePool::new(16));
    let mut scratch = Scratch::new(16);
    let mut out = Evaluation::default();
    evaluate(
        &facts,
        &graph,
        &types,
        &world,
        NodeId(0),
        Value::EMPTY,
        &[Value::TOP],
        &mut scratch,
        &mut out,
    )
    .unwrap();
    assert_eq!(
        out.first_issue.unwrap().reason,
        RuntimeIssueReason::UnknownCallbackValue
    );
    assert_eq!(out.calls.len(), 1);
}

#[test]
fn certified_slot_does_not_declare_the_external_callee_effects_complete() {
    let (facts, graph) = fixture(EDGE_TEST_REGISTRATION | encode_callback_argument(0).unwrap());
    assert_eq!(graph.edges[0].flags & EDGE_EFFECTS_COMPLETE, 0);
    let types = TypeIndex::new(&facts);
    let world = CompleteSummaries(ValuePool::new(16));
    let mut scratch = Scratch::new(16);
    let mut out = Evaluation::default();
    evaluate(
        &facts,
        &graph,
        &types,
        &world,
        NodeId(1),
        Value::EMPTY,
        &[],
        &mut scratch,
        &mut out,
    )
    .unwrap();
    assert_eq!(
        out.first_issue.unwrap().reason,
        RuntimeIssueReason::MissingExecutableBody
    );
}

#[test]
fn a_certified_noncallable_empty_value_cannot_silently_prove_no_effects() {
    let (mut facts, graph) = fixture(EDGE_TEST_REGISTRATION | encode_callback_argument(0).unwrap());
    facts.operations[1].opcode = Opcode::Constant;
    facts.operations[1].target = SymbolId::NONE;
    let types = TypeIndex::new(&facts);
    let world = CompleteSummaries(ValuePool::new(16));
    let mut scratch = Scratch::new(16);
    let mut out = Evaluation::default();
    evaluate(
        &facts,
        &graph,
        &types,
        &world,
        NodeId(0),
        Value::EMPTY,
        &[Value::TOP],
        &mut scratch,
        &mut out,
    )
    .unwrap();
    assert_eq!(
        out.first_issue.unwrap().reason,
        RuntimeIssueReason::UnknownCallbackValue
    );
}
