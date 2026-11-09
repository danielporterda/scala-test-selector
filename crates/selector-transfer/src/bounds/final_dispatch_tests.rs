use super::*;

struct ClosedWorld(ValuePool);
impl World for ClosedWorld {
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
            context: Some(ContextId(7)),
            value: Value::TOP,
            version: 1,
            present: true,
        }
    }
    fn slot(&self, slot: Slot) -> (Value, u64, bool) {
        assert_eq!(slot.kind, SlotKind::StaticField);
        (Value::TOP, 9, true)
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
fn fixture() -> (FactSnapshot, ProgramGraph) {
    let mut b = FactBuilder::new();
    let path = b.intern("exact-native.class").unwrap();
    b.facts.files.push(FileRecord {
        path,
        source: StrId::NONE,
        revision: StrId::NONE,
        context: StrId::NONE,
        source_hash: ContentHash([19; 32]),
        flags: FILE_BINARY_SOURCE,
    });
    for (i, name) in [
        "root().",
        "j/Final#",
        "j/Parent#",
        "j/Other#",
        "j/Final#method().",
        "j/Parent#method().",
        "returnsFinal().",
        "returnsOther().",
    ]
    .into_iter()
    .enumerate()
    {
        b.ensure_symbol(name, FileId(0)).unwrap();
        b.facts.symbols[i].kind = if (1..=3).contains(&i) { 13 } else { 3 };
        b.facts.symbols[i].flags = if (1..=3).contains(&i) {
            SYMBOL_JVM_CLASS_HEADER_VERIFIED | SYMBOL_JVM_PARENTS_COMPLETE
        } else {
            SYMBOL_NATIVE_BINARY
        };
    }
    b.facts.symbols[1].properties = 8;
    b.facts.symbols[4].owner = SymbolId(1);
    b.facts.symbols[5].owner = SymbolId(2);
    b.facts.relations.push(RelationRecord {
        source: SymbolId(1),
        target: SymbolId(2),
        kind: RelationKind::Parent,
        file: FileId(0),
    });
    for (symbol, class) in [(6, 1), (7, 3)] {
        let start = b.facts.bound_classes.len() as u32;
        b.facts.bound_classes.push(SymbolId(class));
        b.facts.result_bounds.push(ResultBoundRecord {
            symbol: SymbolId(symbol),
            operation: OperationId::NONE,
            classes: IdRange { start, len: 1 },
        });
    }
    let op = OperationRecord {
        body: BodyId(0),
        opcode: Opcode::VirtualCall,
        target: SymbolId(4),
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
            opcode: Opcode::Constant,
            target: SymbolId::NONE,
            dest: ValueId::NONE,
            a: ValueId::NONE,
            ..op
        },
        OperationRecord {
            opcode: Opcode::Return,
            target: SymbolId::NONE,
            dest: ValueId::NONE,
            a: ValueId(1),
            ..op
        },
        OperationRecord {
            body: BodyId(1),
            opcode: Opcode::Return,
            target: SymbolId::NONE,
            dest: ValueId::NONE,
            a: ValueId(0),
            ..op
        },
        OperationRecord {
            body: BodyId(2),
            opcode: Opcode::Return,
            target: SymbolId::NONE,
            dest: ValueId::NONE,
            a: ValueId(0),
            ..op
        },
    ]);
    for (symbol, start, len) in [(0, 0, 3), (4, 3, 1), (5, 4, 1)] {
        b.facts.bodies.push(BodyRecord {
            symbol: SymbolId(symbol),
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange { start, len },
            parameters: IdRange::default(),
            body_hash: ContentHash([19; 32]),
            flags: BODY_BINARY_RECIPE,
        });
    }
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
            body: match i {
                0 => BodyId(0),
                4 => BodyId(1),
                5 => BodyId(2),
                _ => BodyId::NONE,
            },
            flags: 0,
        });
    }
    graph.edges.push(EdgeRecord {
        source: NodeId(0),
        target: NodeId(4),
        kind: EdgeKind::VirtualCall,
        occurrence: OccurrenceId::NONE,
        operation: OperationId(0),
        receiver: SymbolId(1),
        flags: 0,
    });
    graph.index().unwrap();
    (facts, graph)
}
fn upper(facts: &FactSnapshot, world: &mut ClosedWorld, class: u32) -> Value {
    let atom = TypeIndex::new(facts)
        .canonical_bound_for_classes(facts, &[SymbolId(class)])
        .unwrap();
    world
        .0
        .intern(&[atom], UNKNOWN_VALUE | UNKNOWN_TYPED)
        .unwrap()
}
fn proof(facts: &FactSnapshot, graph: &ProgramGraph, world: &ClosedWorld, value: Value) -> bool {
    let targets = graph
        .edges
        .iter()
        .enumerate()
        .filter(|(_, e)| e.kind == EdgeKind::VirtualCall)
        .map(|(i, e)| (e.target, EdgeId(i as u32), e.receiver))
        .collect::<Vec<_>>();
    final_dispatch_complete(
        facts,
        graph,
        &TypeIndex::new(facts),
        &world.0,
        value,
        OperationId(0),
        &targets,
        &mut Vec::new(),
        &mut LinearizationScratch::default(),
    )
}
fn run(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    world: &ClosedWorld,
    value: Value,
) -> (Evaluation, Scratch) {
    let mut scratch = Scratch::new(16);
    let mut out = Evaluation::default();
    evaluate(
        facts,
        graph,
        &TypeIndex::new(facts),
        world,
        NodeId(0),
        value,
        &[],
        &mut scratch,
        &mut out,
    )
    .unwrap();
    (out, scratch)
}

#[test]
fn final_native_bound_closes_dispatch_only_and_keeps_unknown_alias_and_call_witness() {
    let (facts, graph) = fixture();
    let mut world = ClosedWorld(ValuePool::new(16));
    let receiver = upper(&facts, &mut world, 1);
    assert!(proof(&facts, &graph, &world, receiver));
    let (out, scratch) = run(&facts, &graph, &world, receiver);
    assert!(out.issues.is_empty());
    assert!(out.value.is_unknown());
    assert!(!out.effects_open);
    assert_eq!(out.calls.len(), 1);
    assert_eq!(out.calls[0].target, NodeId(4));
    assert_eq!(out.calls[0].summary, Some(ContextId(7)));
    assert_eq!(out.calls[0].receiver.unknown, receiver.unknown);
    assert_eq!(scratch.pool.members(out.calls[0].receiver).len(), 1);
    assert_eq!(
        scratch.pool.members(out.calls[0].receiver)[0].kind,
        AtomKind::UpperBound,
        "no fake allocation/object identity"
    );
}

#[test]
fn typed_static_field_preserves_heap_read_and_drops_disjoint_virtual_candidate() {
    let (mut facts, mut graph) = fixture();
    let call = facts.operations[0];
    let field = SymbolId(6);
    facts.symbols[field.index()].kind = 20;
    facts.operations[0] = OperationRecord {
        opcode: Opcode::LoadField,
        target: field,
        dest: ValueId(2),
        a: ValueId::NONE,
        flags: OP_STATIC_FIELD,
        ..call
    };
    facts.operations[1] = OperationRecord {
        a: ValueId(2),
        ..call
    };
    facts.symbols[5].owner = SymbolId(3);
    graph.edges[0].operation = OperationId(1);
    graph.edges.push(EdgeRecord {
        target: NodeId(5),
        receiver: SymbolId(3),
        ..graph.edges[0]
    });
    graph.index().unwrap();
    let bound = facts.result_bounds.remove(0);
    let world = ClosedWorld(ValuePool::new(16));
    let (baseline, _) = run(&facts, &graph, &world, Value::TOP);
    assert_eq!(baseline.calls.len(), 2);
    facts.result_bounds.insert(
        0,
        ResultBoundRecord {
            operation: OperationId(0),
            ..bound
        },
    );
    facts.validate().unwrap();
    let (bounded, _) = run(&facts, &graph, &world, Value::TOP);
    assert_eq!(bounded.calls.len(), 1);
    assert_eq!(bounded.calls[0].target, NodeId(4));
    let slot = Slot {
        kind: SlotKind::StaticField,
        owner: field.0,
        member: 0,
    };
    for evaluation in [baseline, bounded] {
        assert!(
            evaluation
                .reads
                .iter()
                .any(|read| read.slot == slot && read.version == 9 && read.present)
        );
    }
}

#[test]
fn all_unknown_clauses_need_final_header_complete_ancestry_and_actual_admitted_body() {
    for case in 0..12 {
        let (mut facts, mut graph) = fixture();
        let mut world = ClosedWorld(ValuePool::new(16));
        let receiver = upper(&facts, &mut world, 1);
        match case {
            0 => facts.symbols[1].properties = 0,
            1 => facts.symbols[1].flags &= !SYMBOL_JVM_CLASS_HEADER_VERIFIED,
            2 => facts.symbols[2].flags &= !SYMBOL_JVM_PARENTS_COMPLETE,
            3 => graph.nodes[4].body = BodyId::NONE,
            4 => facts.bodies[1].flags = 0,
            5 => facts.files[0].flags = 0,
            6 => facts.bodies[1].body_hash = ContentHash([1; 32]),
            7 => facts.symbols[4].properties |= 4,
            8 => {
                graph.edges.clear();
                graph.index().unwrap();
            }
            9 => {
                facts.operations[0].flags |= OP_SUPER;
            }
            10 => {
                facts.symbols[4].context = facts.files[0].path;
                facts.files[0].context = facts.files[0].path;
            }
            11 => facts.operations[0].target = SymbolId::NONE,
            _ => unreachable!(),
        }
        assert!(!proof(&facts, &graph, &world, receiver), "case{case}");
    }
    let (facts, graph) = fixture();
    let mut world = ClosedWorld(ValuePool::new(16));
    let first = upper(&facts, &mut world, 1);
    let other = upper(&facts, &mut world, 3);
    let joined = world.0.join(first, other).unwrap();
    assert!(!proof(&facts, &graph, &world, joined));
    assert!(!proof(&facts, &graph, &world, Value::TOP));
    let mut malformed = world.0.members(first)[0];
    malformed.binding = 1;
    let malformed = world
        .0
        .intern(&[malformed], UNKNOWN_VALUE | UNKNOWN_TYPED)
        .unwrap();
    assert!(!proof(&facts, &graph, &world, malformed));
}

#[test]
fn inherited_body_requires_exact_full_lookup_and_ambiguity_remains_open() {
    let (mut facts, mut graph) = fixture();
    facts.operations[0].target = SymbolId(5);
    graph.edges[0].target = NodeId(5);
    graph.edges[0].receiver = SymbolId(2);
    graph.index().unwrap();
    let mut world = ClosedWorld(ValuePool::new(16));
    let receiver = upper(&facts, &mut world, 1);
    assert!(!proof(&facts, &graph, &world, receiver));
    facts.relations.push(RelationRecord {
        source: SymbolId(1),
        target: SymbolId(5),
        kind: RelationKind::KnownReceiverDispatch,
        file: FileId(0),
    });
    assert!(proof(&facts, &graph, &world, receiver));
    facts.relations.last_mut().unwrap().target = SymbolId(4);
    assert!(!proof(&facts, &graph, &world, receiver));
    facts.operations[0].target = SymbolId(4);
    graph.edges[0].target = NodeId(4);
    graph.edges[0].receiver = SymbolId(1);
    let mut duplicate = graph.edges[0];
    duplicate.target = NodeId(5);
    graph.edges.push(duplicate);
    graph.index().unwrap();
    assert!(!proof(&facts, &graph, &world, receiver));
}

#[test]
fn explicit_body_scoped_and_receiver_guards_still_win_over_final_lookup() {
    for case in 0..4 {
        let (mut facts, mut graph) = fixture();
        match case {
            0 => facts.operations[1].opcode = Opcode::Unknown,
            1 => {
                graph.edges.push(EdgeRecord {
                    source: NodeId(0),
                    target: NodeId(0),
                    kind: EdgeKind::Guard,
                    occurrence: OccurrenceId::NONE,
                    operation: OperationId(0),
                    receiver: SymbolId::NONE,
                    flags: EDGE_UNKNOWN,
                });
                graph.index().unwrap();
            }
            2 => facts.relations.push(RelationRecord {
                source: SymbolId(1),
                target: SymbolId(1),
                kind: RelationKind::DeferredReceiverDispatch,
                file: FileId(0),
            }),
            3 => {
                graph.edges.push(EdgeRecord {
                    source: NodeId(0),
                    target: NodeId(4),
                    kind: EdgeKind::Guard,
                    occurrence: OccurrenceId::NONE,
                    operation: OperationId(0),
                    receiver: SymbolId(1),
                    flags: EDGE_UNKNOWN | EDGE_DEFERRED_DISPATCH,
                });
                graph.index().unwrap();
            }
            _ => unreachable!(),
        }
        let mut world = ClosedWorld(ValuePool::new(16));
        let receiver = upper(&facts, &mut world, 1);
        assert!(proof(&facts, &graph, &world, receiver));
        let (out, _) = run(&facts, &graph, &world, receiver);
        assert!(out.effects_open);
        assert!(!out.issues.is_empty());
        assert!(!out.calls.is_empty());
    }
}
