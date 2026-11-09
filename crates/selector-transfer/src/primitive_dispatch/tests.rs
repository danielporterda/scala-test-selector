use super::*;

struct TestWorld(ValuePool);
impl World for TestWorld {
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
            value: Value::TOP,
            version: 0,
            present: false,
        }
    }
    fn slot(&self, _: Slot) -> (Value, u64, bool) {
        (Value::TOP, 0, false)
    }
    fn capture(&self, _: u32) -> Option<(Value, &[Value], u64)> {
        None
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

fn fixture(producer: Opcode) -> (FactSnapshot, ProgramGraph) {
    let mut b = FactBuilder::new();
    let path = b.intern("PrimitiveReceiver.scala").unwrap();
    let text = b.intern("").unwrap();
    let context = b.intern("project:typed/configuration:compile").unwrap();
    b.facts.files.push(FileRecord {
        path,
        source: text,
        revision: StrId::NONE,
        context,
        source_hash: ContentHash([1; 32]),
        flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
    });
    for (i, name) in [
        "p/Example#call().",
        "p/Example#currentMigrationId.",
        ANY_TO_STRING,
        "p/BuildInfo.toString.",
        "p/BuildInfo.",
        "java/lang/Long#toString().",
        "java/lang/Long#",
        "@jvm/14:java/lang/Long12:<class-init>3:()V",
    ]
    .into_iter()
    .enumerate()
    {
        let id = b.ensure_symbol(name, FileId(0)).unwrap();
        assert_eq!(id, SymbolId(i as u32));
        b.facts.symbols[i].context = context;
        b.facts.symbols[i].file = FileId(0);
        b.facts.symbols[i].kind = match i {
            1 if producer == Opcode::Parameter => 8,
            4 => 10,
            6 => 13,
            _ => 3,
        };
        b.facts.symbols[i].flags = SYMBOL_DEFINED;
    }
    b.facts.symbols[1].owner = SymbolId(0);
    b.facts.symbols[1].signature = b
        .intern(if producer == Opcode::Parameter {
            r#"{"value_signature":{"tpe":{"type_ref":{"symbol":"scala/Long#"}}}}"#
        } else {
            r#"{"method_signature":{"type_parameters":{},"return_type":{"type_ref":{"symbol":"scala/Long#"}}}}"#
        })
        .unwrap();
    b.facts.symbols[3].owner = SymbolId(4);
    b.facts.symbols[5].owner = SymbolId(6);
    b.facts.operands.push(ValueId(1));
    b.facts.bodies.push(BodyRecord {
        symbol: SymbolId(0),
        file: FileId(0),
        span: Span::default(),
        name_span: Span::default(),
        operations: IdRange { start: 0, len: 3 },
        parameters: IdRange {
            start: 0,
            len: u32::from(producer == Opcode::Parameter),
        },
        body_hash: ContentHash([1; 32]),
        flags: 0,
    });
    let call = OperationRecord {
        body: BodyId(0),
        opcode: Opcode::VirtualCall,
        target: SymbolId(2),
        dest: ValueId(2),
        a: ValueId(1),
        b: ValueId::NONE,
        arguments: IdRange::default(),
        span: Span::default(),
        flags: 0,
    };
    b.facts.operations.extend([
        OperationRecord {
            opcode: producer,
            target: SymbolId(1),
            dest: ValueId(1),
            a: ValueId::NONE,
            ..call
        },
        call,
        OperationRecord {
            opcode: Opcode::Return,
            target: SymbolId::NONE,
            dest: ValueId::NONE,
            a: ValueId(2),
            ..call
        },
    ]);
    let facts = b.finish().unwrap();
    let mut graph = ProgramGraph {
        facts_identity: facts.identity,
        ..Default::default()
    };
    for i in 0..facts.symbols.len() {
        graph.symbol_nodes.push(NodeId(i as u32));
        graph.nodes.push(NodeRecord {
            symbol: SymbolId(i as u32),
            file: FileId(0),
            body: if i == 0 { BodyId(0) } else { BodyId::NONE },
            flags: 0,
        });
    }
    let edge = |target, receiver, operation, kind| EdgeRecord {
        source: NodeId(0),
        target: NodeId(target),
        kind,
        occurrence: OccurrenceId::NONE,
        operation: OperationId(operation),
        receiver,
        flags: 0,
    };
    graph.edges.extend([
        edge(2, SymbolId::NONE, 1, EdgeKind::VirtualCall),
        edge(3, SymbolId(4), 1, EdgeKind::VirtualCall),
        edge(5, SymbolId(6), 1, EdgeKind::VirtualCall),
        edge(7, SymbolId::NONE, 1, EdgeKind::Initialize),
    ]);
    if producer != Opcode::Parameter {
        graph.edges.push(edge(1, SymbolId::NONE, 0, EdgeKind::Call));
    }
    graph.index().unwrap();
    graph.validate().unwrap();
    (facts, graph)
}

fn run(facts: &FactSnapshot, graph: &ProgramGraph) -> Evaluation {
    let mut out = Evaluation::default();
    evaluate(
        facts,
        graph,
        &TypeIndex::new(facts),
        &TestWorld(ValuePool::new(16)),
        NodeId(0),
        Value::TOP,
        &[],
        &mut Scratch::new(16),
        &mut out,
    )
    .unwrap();
    out
}

#[test]
fn direct_long_parameter_or_accessor_cannot_dispatch_to_application_object() {
    for producer in [Opcode::Parameter, Opcode::Call, Opcode::VirtualCall] {
        let (facts, graph) = fixture(producer);
        assert_eq!(sites(&facts), [(OperationId(1), SymbolId(1))]);
        let out = run(&facts, &graph);
        assert!(!out.calls.iter().any(|c| c.target == NodeId(3)));
        for target in [2, 5, 7] {
            assert!(out.calls.iter().any(|c| c.target == NodeId(target)));
        }
        if producer != Opcode::Parameter {
            assert!(out.calls.iter().any(|c| c.target == NodeId(1)));
        }
        assert!(out.effects_open && out.value.is_unknown());
        let first = out.first_issue.unwrap();
        assert_eq!(first.reason, RuntimeIssueReason::IncompleteVirtualDispatch);
        assert_eq!(
            first.operation,
            OperationId(u32::from(producer != Opcode::VirtualCall))
        );
    }
}

#[test]
fn unverified_conflicted_or_reused_receivers_keep_application_dispatch() {
    for variant in 0..5 {
        let (mut facts, graph) = fixture(Opcode::Parameter);
        match variant {
            0 => facts.files[0].flags &= !SYNTAX_VERIFIED,
            1 => facts.symbols[1].signature = StrId::NONE,
            2 => facts.issues.push(IssueRecord {
                kind: IssueKind::ContextConflict,
                file: FileId(0),
                symbol: SymbolId(1),
                detail: StrId::NONE,
            }),
            3 => facts.operations[2].dest = ValueId(1),
            4 => facts.bodies[0].flags |= BODY_BINARY_RECIPE,
            _ => unreachable!(),
        }
        assert!(sites(&facts).is_empty());
        assert!(
            run(&facts, &graph)
                .calls
                .iter()
                .any(|c| c.target == NodeId(3))
        );
    }
}
