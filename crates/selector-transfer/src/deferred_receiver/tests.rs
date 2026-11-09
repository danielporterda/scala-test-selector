use super::*;

struct ClosedWorld(ValuePool);
impl World for ClosedWorld {
    fn values(&self) -> &ValuePool {
        &self.0
    }
    fn summary(
        &self,
        node: NodeId,
        _: Value,
        _: &[Value],
        _: &ValuePool,
        _: &mut Vec<Value>,
    ) -> SummaryRead {
        assert_eq!(node, NodeId(5));
        SummaryRead {
            context: Some(ContextId(0)),
            value: Value::EMPTY,
            version: 1,
            present: true,
        }
    }
    fn slot(&self, _: Slot) -> (Value, u64, bool) {
        panic!("no heap read")
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
    let path = b.intern("receiver.scala").unwrap();
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
        "p/deferredBound().",
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
        target: SymbolId(2),
        kind: RelationKind::DeferredReceiverDispatch,
        file: FileId(0),
    });
    for (producer, class) in [(6, 2), (7, 3)] {
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
    graph.edges.push(EdgeRecord {
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
    });
    graph.index().unwrap();
    graph.validate().unwrap();
    (facts, graph)
}

fn value(world: &mut ClosedWorld, kind: AtomKind, symbol: u32) -> Value {
    world
        .0
        .singleton(Atom {
            kind,
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
    let mut out = Evaluation::default();
    evaluate(
        facts,
        graph,
        &TypeIndex::new(facts),
        world,
        NodeId(0),
        receiver,
        &[],
        &mut Scratch::new(16),
        &mut out,
    )
    .unwrap();
    out
}

#[test]
fn receiver_frontier_guards_actual_instance_calls_and_preserves_inherited_effects() {
    for opcode in [
        Opcode::Call,
        Opcode::VirtualCall,
        Opcode::DefaultArgument,
        Opcode::RegisterTest,
        Opcode::InvokeCallback,
    ] {
        let (facts, graph) = fixture(opcode);
        for (class, guarded) in [(1, false), (2, true), (3, false), (4, true)] {
            let mut world = ClosedWorld(ValuePool::new(16));
            let receiver = value(&mut world, AtomKind::Object, class);
            let out = run(&facts, &graph, &world, receiver);
            assert_eq!(out.value.is_unknown(), guarded, "{opcode:?}/{class}");
            assert_eq!(out.effects_open, guarded);
            assert_eq!(out.issues.is_empty(), !guarded);
            assert_eq!(out.calls.len(), 1, "known inherited effects stay present");
            assert_eq!(out.calls[0].target, NodeId(5));
            if guarded {
                assert_eq!(out.first_issue.unwrap().operation, OperationId(0));
            }
        }
    }
}

#[test]
fn unknown_bounds_incomplete_and_cyclic_ancestry_fail_closed() {
    let (mut facts, graph) = fixture(Opcode::VirtualCall);
    let mut world = ClosedWorld(ValuePool::new(16));
    let types = TypeIndex::new(&facts);
    assert!(run(&facts, &graph, &world, Value::TOP).effects_open);
    for (class, expected) in [(2, true), (3, false)] {
        let atom = types
            .canonical_bound_for_classes(&facts, &[SymbolId(class)])
            .unwrap();
        let receiver = world
            .0
            .intern(&[atom], UNKNOWN_VALUE | UNKNOWN_TYPED)
            .unwrap();
        assert_eq!(
            possible(
                &facts,
                &types,
                &world.0,
                receiver,
                OperationId(0),
                &mut Vec::new(),
                &mut LinearizationScratch::default()
            ),
            expected
        );
    }
    let sibling = value(&mut world, AtomKind::Object, 3);
    facts.symbols[3].flags = SYMBOL_NATIVE_BINARY;
    assert!(run(&facts, &graph, &world, sibling).effects_open);
    facts.symbols[3].flags = SYMBOL_DEFINED | SYMBOL_SCALA_PARENTS_COMPLETE;
    facts.relations.push(RelationRecord {
        source: SymbolId(3),
        target: SymbolId(3),
        kind: RelationKind::Parent,
        file: FileId(0),
    });
    assert!(run(&facts, &graph, &world, sibling).effects_open);
}

#[test]
fn literal_callbacks_and_exact_nonvirtual_operations_do_not_inherit_the_marker() {
    let (mut facts, graph) = fixture(Opcode::InvokeCallback);
    let mut world = ClosedWorld(ValuePool::new(16));
    let callback = value(&mut world, AtomKind::Callback, 5);
    let out = run(&facts, &graph, &world, callback);
    assert!(out.issues.is_empty());
    assert_eq!(out.calls.len(), 1);
    let receiver = value(&mut world, AtomKind::Object, 2);
    for flags in [OP_SUPER, OP_QUALIFIED_SUPER] {
        facts.operations[0].opcode = Opcode::Call;
        facts.operations[0].flags = flags;
        assert!(!possible(
            &facts,
            &TypeIndex::new(&facts),
            &world.0,
            receiver,
            OperationId(0),
            &mut Vec::new(),
            &mut LinearizationScratch::default()
        ));
    }
    facts.operations[0].flags = 0;
    facts.symbols[5].kind = 21;
    assert!(!possible(
        &facts,
        &TypeIndex::new(&facts),
        &world.0,
        receiver,
        OperationId(0),
        &mut Vec::new(),
        &mut LinearizationScratch::default()
    ));
    facts.symbols[5].kind = 3;
    assert!(
        !possible(
            &facts,
            &TypeIndex::new(&facts),
            &world.0,
            Value::EMPTY,
            OperationId(0),
            &mut Vec::new(),
            &mut LinearizationScratch::default()
        ),
        "explicit empty static receiver does not intersect"
    );
}

#[test]
fn sparse_inventory_is_deduplicated_owned_and_warm_match_reuses_scratch() {
    let (mut facts, _) = fixture(Opcode::Call);
    let marker = *facts.relations.last().unwrap();
    facts.relations.push(marker);
    let types = TypeIndex::new(&facts);
    assert_eq!(types.deferred_receivers(), &[SymbolId(2)]);
    let mut world = ClosedWorld(ValuePool::new(16));
    let receiver = value(&mut world, AtomKind::Object, 4);
    let mut work = Vec::new();
    let mut chain = LinearizationScratch::default();
    assert!(possible(
        &facts,
        &types,
        &world.0,
        receiver,
        OperationId(0),
        &mut work,
        &mut chain
    ));
    let capacities = (work.capacity(), chain.owned_bytes(), types.owned_bytes());
    for _ in 0..1000 {
        assert!(possible(
            &facts,
            &types,
            &world.0,
            receiver,
            OperationId(0),
            &mut work,
            &mut chain
        ));
    }
    assert_eq!(
        (work.capacity(), chain.owned_bytes(), types.owned_bytes()),
        capacities
    );
    facts
        .relations
        .retain(|r| r.kind != RelationKind::DeferredReceiverDispatch);
    assert!(types.owned_bytes() > TypeIndex::new(&facts).owned_bytes());
}

#[test]
fn admitted_full_lookup_closes_only_its_exact_receiver_and_contract() {
    let (mut facts, graph) = fixture(Opcode::VirtualCall);
    facts.relations.push(RelationRecord {
        source: SymbolId(2),
        target: SymbolId(5),
        kind: RelationKind::KnownReceiverDispatch,
        file: FileId(0),
    });
    let mut world = ClosedWorld(ValuePool::new(16));
    let exact = value(&mut world, AtomKind::Object, 2);
    let out = run(&facts, &graph, &world, exact);
    assert!(out.issues.is_empty());
    assert_eq!(out.calls.len(), 1, "the inherited body still executes");
    let child = value(&mut world, AtomKind::Object, 4);
    assert!(
        run(&facts, &graph, &world, child).effects_open,
        "C's lookup does not cover D's possible override"
    );
    assert!(run(&facts, &graph, &world, Value::TOP).effects_open);
    let types = TypeIndex::new(&facts);
    let atom = types
        .canonical_bound_for_classes(&facts, &[SymbolId(2)])
        .unwrap();
    let upper = world
        .0
        .intern(&[atom], UNKNOWN_VALUE | UNKNOWN_TYPED)
        .unwrap();
    assert!(
        run(&facts, &graph, &world, upper).effects_open,
        "a C upper bound may be D"
    );
    facts.relations.last_mut().unwrap().target = SymbolId(6);
    assert!(
        run(&facts, &graph, &world, exact).effects_open,
        "unrelated covered contracts do not close this call"
    );
    facts.relations.push(RelationRecord {
        source: SymbolId(4),
        target: SymbolId(5),
        kind: RelationKind::KnownReceiverDispatch,
        file: FileId(0),
    });
    assert!(
        !run(&facts, &graph, &world, child).effects_open,
        "D's own full lookup covers inherited C frontier"
    );
}

#[test]
fn nonvirtual_flag_requires_exact_native_call_recipe_and_preserves_effects() {
    for (opcode, binary_body, binary_file, guarded) in [
        (Opcode::Call, true, true, false),
        (Opcode::Call, false, true, true),
        (Opcode::Call, true, false, true),
        (Opcode::Call, false, false, true),
        (Opcode::VirtualCall, true, true, true),
        (Opcode::InvokeCallback, true, true, true),
    ] {
        let (mut facts, graph) = fixture(opcode);
        facts.operations[0].flags |= OP_JVM_NONVIRTUAL;
        if opcode == Opcode::Call {
            facts.operations[0].a = ValueId::NONE;
        }
        if binary_body {
            facts.bodies[0].flags |= BODY_BINARY_RECIPE;
        }
        if binary_file {
            facts.files[0].flags |= FILE_BINARY_SOURCE;
        }
        let mut world = ClosedWorld(ValuePool::new(16));
        let receiver = value(&mut world, AtomKind::Object, 2);
        let out = run(&facts, &graph, &world, receiver);
        assert_eq!(
            out.effects_open, guarded,
            "{opcode:?}/{binary_body}/{binary_file}"
        );
        assert_eq!(out.calls.len(), 1, "the exact callee still executes");
        assert_eq!(out.calls[0].target, NodeId(5));
    }
}
