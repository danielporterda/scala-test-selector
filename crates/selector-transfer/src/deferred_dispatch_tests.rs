use super::*;

struct ClosedWorld(ValuePool);
impl World for ClosedWorld {
    fn values(&self) -> &ValuePool {
        &self.0
    }
    fn summary(
        &self,
        target: NodeId,
        _: Value,
        _: &[Value],
        _: &ValuePool,
        _: &mut Vec<Value>,
    ) -> SummaryRead {
        assert_eq!(target, NodeId(5), "the frontier is never a call target");
        SummaryRead {
            context: Some(ContextId(0)),
            value: Value::EMPTY,
            version: 1,
            present: true,
        }
    }
    fn slot(&self, _: Slot) -> (Value, u64, bool) {
        panic!("no field read")
    }
    fn capture(&self, _: u32) -> Option<(Value, &[Value], u64)> {
        Some((Value::EMPTY, &[], 1))
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

fn fixture(opcode: Opcode) -> (FactSnapshot, ProgramGraph) {
    let mut b = FactBuilder::new();
    let path = b.intern("scoped.scala").unwrap();
    b.facts.files.push(FileRecord {
        path,
        source: StrId::NONE,
        revision: StrId::NONE,
        context: StrId::NONE,
        source_hash: ContentHash::default(),
        flags: 0,
    });
    for (i, name) in [
        "p/Root#run().",
        "p/Base#",
        "p/Deferred#",
        "p/Sibling#",
        "p/Grandchild#",
        "p/Base#method().",
        "p/Base#other().",
        "p/childBound().",
        "p/siblingBound().",
    ]
    .into_iter()
    .enumerate()
    {
        assert_eq!(
            b.ensure_symbol(name, FileId(0)).unwrap(),
            SymbolId(i as u32)
        );
        b.facts.symbols[i].kind = if (1..=4).contains(&i) { 13 } else { 3 };
        b.facts.symbols[i].flags = SYMBOL_DEFINED | SYMBOL_SCALA_PARENTS_COMPLETE;
    }
    b.facts.symbols[5].owner = SymbolId(1);
    b.facts.symbols[6].owner = SymbolId(1);
    for (child, parent) in [(2, 1), (3, 1), (4, 2)] {
        b.facts.relations.push(RelationRecord {
            source: SymbolId(child),
            target: SymbolId(parent),
            kind: RelationKind::Parent,
            file: FileId(0),
        });
    }
    b.facts.relations.push(RelationRecord {
        source: SymbolId(2),
        target: SymbolId(5),
        kind: RelationKind::DeferredDispatch,
        file: FileId(0),
    });
    for (producer, class) in [(7, 2), (8, 3)] {
        let start = b.facts.bound_classes.len() as u32;
        b.facts.bound_classes.push(SymbolId(class));
        b.facts.result_bounds.push(ResultBoundRecord {
            symbol: SymbolId(producer),
            operation: OperationId::NONE,
            classes: IdRange { start, len: 1 },
        });
    }
    b.facts.bodies.push(BodyRecord {
        symbol: SymbolId(0),
        file: FileId(0),
        span: Span::default(),
        name_span: Span::default(),
        operations: IdRange { start: 0, len: 2 },
        parameters: IdRange::default(),
        body_hash: ContentHash::default(),
        flags: 0,
    });
    let op = OperationRecord {
        body: BodyId(0),
        opcode,
        target: SymbolId(5),
        dest: ValueId(1),
        a: ValueId(0),
        b: ValueId::NONE,
        arguments: IdRange::default(),
        span: Span::default(),
        flags: 0,
    };
    b.facts.operations.extend([
        op,
        OperationRecord {
            opcode: Opcode::Return,
            target: SymbolId::NONE,
            dest: ValueId::NONE,
            a: ValueId(1),
            ..op
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
    let candidate = EdgeRecord {
        source: NodeId(0),
        target: NodeId(5),
        kind: if opcode == Opcode::InvokeCallback {
            EdgeKind::Callback
        } else {
            EdgeKind::VirtualCall
        },
        occurrence: OccurrenceId::NONE,
        operation: OperationId(0),
        receiver: SymbolId(1),
        flags: 0,
    };
    graph.edges.extend([
        candidate,
        EdgeRecord {
            kind: EdgeKind::Guard,
            receiver: SymbolId(2),
            flags: EDGE_UNKNOWN | EDGE_DEFERRED_DISPATCH,
            ..candidate
        },
    ]);
    graph.index().unwrap();
    graph.validate().unwrap();
    (facts, graph)
}

fn object(world: &mut ClosedWorld, symbol: u32) -> Value {
    world
        .0
        .singleton(Atom {
            kind: AtomKind::Object,
            site: OperationId::NONE,
            symbol: SymbolId(symbol),
            binding: 0,
        })
        .unwrap()
}

fn run(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    world: &ClosedWorld,
    receiver: Value,
) -> Evaluation {
    let mut scratch = Scratch::new(16);
    let mut out = Evaluation::default();
    evaluate(
        facts,
        graph,
        &TypeIndex::new(facts),
        world,
        NodeId(0),
        receiver,
        &[],
        &mut scratch,
        &mut out,
    )
    .unwrap();
    out
}

#[test]
fn missing_child_override_cannot_close_an_inherited_target_or_poison_a_sibling() {
    for opcode in [
        Opcode::Call,
        Opcode::VirtualCall,
        Opcode::DefaultArgument,
        Opcode::RegisterTest,
        Opcode::InvokeCallback,
    ] {
        let (facts, graph) = fixture(opcode);
        for (receiver, guarded) in [(1, false), (2, true), (3, false), (4, true)] {
            let mut world = ClosedWorld(ValuePool::new(16));
            let value = object(&mut world, receiver);
            let out = run(&facts, &graph, &world, value);
            assert_eq!(out.value.is_unknown(), guarded, "{opcode:?}/{receiver}");
            assert_eq!(out.issues.is_empty(), !guarded, "{opcode:?}/{receiver}");
            assert_eq!(
                out.calls.len(),
                1,
                "known inherited effects remain possible"
            );
            assert_eq!(out.calls[0].target, NodeId(5));
            if guarded {
                assert_eq!(out.first_issue.unwrap().operation, OperationId(0));
                assert_eq!(
                    out.first_issue.unwrap().reason,
                    if opcode == Opcode::InvokeCallback {
                        RuntimeIssueReason::IncompleteCallbackDispatch
                    } else {
                        RuntimeIssueReason::IncompleteVirtualDispatch
                    }
                );
            }
        }
    }
}

#[test]
fn private_trait_this_call_keeps_callee_effects_even_with_unknown_receiver() {
    let (mut facts, graph) = fixture(Opcode::VirtualCall);
    facts.files[0].source_hash = ContentHash([1; 32]);
    facts.symbols[1].kind = 14;
    for id in [0, 1, 5] {
        facts.symbols[id].file = FileId(0);
    }
    facts.symbols[0].owner = SymbolId(1);
    facts.symbols[5].flags |= SYMBOL_SCALA_PRIVATE_METHOD;
    let world = ClosedWorld(ValuePool::new(16));
    let out = run(&facts, &graph, &world, Value::TOP);
    assert!(out.issues.is_empty());
    assert!(!out.effects_open);
    assert_eq!(out.calls.len(), 1);
    assert_eq!(out.calls[0].target, NodeId(5));
    assert_eq!(out.calls[0].receiver, Value::TOP);
    assert!(out.calls[0].observe_return);
    facts.symbols[0].owner = SymbolId(3);
    assert!(run(&facts, &graph, &world, Value::TOP).effects_open);
}

#[test]
fn unknown_and_incomplete_ancestry_remain_guarded_but_complete_bounds_can_exclude_scope() {
    let (mut facts, graph) = fixture(Opcode::VirtualCall);
    let mut world = ClosedWorld(ValuePool::new(16));
    assert!(run(&facts, &graph, &world, Value::TOP).value.is_unknown());
    let types = TypeIndex::new(&facts);
    let mut edges = OperationEdges::default();
    edges
        .build(&graph, NodeId(0), IdRange { start: 0, len: 2 })
        .unwrap();
    for (class, expected) in [(2, true), (3, false)] {
        let atom = types
            .canonical_bound_for_classes(&facts, &[SymbolId(class)])
            .unwrap();
        let value = world
            .0
            .intern(&[atom], UNKNOWN_VALUE | UNKNOWN_TYPED)
            .unwrap();
        assert_eq!(
            scoped_dispatch_possible(
                &facts,
                &graph,
                &types,
                &world.0,
                value,
                OperationId(0),
                &edges,
                &mut Vec::new(),
                &mut LinearizationScratch::default()
            )
            .unwrap(),
            expected
        );
    }
    let sibling = object(&mut world, 3);
    facts.symbols[3].flags = SYMBOL_NATIVE_BINARY;
    assert!(run(&facts, &graph, &world, sibling).value.is_unknown());
    facts.symbols[3].flags = SYMBOL_DEFINED | SYMBOL_SCALA_PARENTS_COMPLETE;
    facts.relations.push(RelationRecord {
        source: SymbolId(3),
        target: SymbolId(3),
        kind: RelationKind::Parent,
        file: FileId(0),
    });
    assert!(run(&facts, &graph, &world, sibling).value.is_unknown());
}

#[test]
fn literal_callback_identity_is_not_the_deferred_native_function_object() {
    let (facts, graph) = fixture(Opcode::InvokeCallback);
    let mut world = ClosedWorld(ValuePool::new(16));
    let callback = world
        .0
        .singleton(Atom {
            kind: AtomKind::Callback,
            site: OperationId::NONE,
            symbol: SymbolId(5),
            binding: 0,
        })
        .unwrap();
    let known = run(&facts, &graph, &world, callback);
    assert!(known.issues.is_empty());
    assert_eq!(known.calls.len(), 1);
    assert_eq!(known.value, Value::EMPTY);
    let unknown = run(&facts, &graph, &world, Value::TOP);
    assert!(unknown.value.is_unknown());
    assert_eq!(
        unknown.first_issue.unwrap().reason,
        RuntimeIssueReason::UnknownCallbackValue
    );
}

#[test]
fn malformed_scoped_frontiers_are_rejected_instead_of_silently_skipped() {
    for case in 0..10 {
        let (mut facts, mut graph) = fixture(Opcode::VirtualCall);
        match case {
            0 => graph.edges[1].flags = EDGE_DEFERRED_DISPATCH,
            1 => graph.edges[1].kind = EdgeKind::Call,
            2 => graph.edges[1].operation = OperationId::NONE,
            3 => graph.edges[1].receiver = SymbolId::NONE,
            4 => graph.edges[1].receiver = SymbolId(5),
            5 => facts.operations[0].opcode = Opcode::Constant,
            6 => facts.operations[0].flags = OP_SUPER,
            7 => facts.operations[0].target = SymbolId::NONE,
            8 => graph.nodes[0].body = BodyId::NONE,
            9 => graph.edges[1].target = NodeId(1),
            _ => unreachable!(),
        }
        assert!(
            validate_scoped_dispatch_edge(&facts, &graph, &graph.edges[1]).is_err(),
            "case{case}"
        );
    }
}
