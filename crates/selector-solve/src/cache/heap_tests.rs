//! Small semantic fixtures for heap cache closure and aggregate rehydration.
use super::*;

struct Fixture {
    facts: FactSnapshot,
    graph: ProgramGraph,
}

fn op(opcode: Opcode) -> OperationRecord {
    OperationRecord {
        body: BodyId::NONE,
        opcode,
        target: SymbolId::NONE,
        dest: ValueId::NONE,
        a: ValueId::NONE,
        b: ValueId::NONE,
        arguments: IdRange::default(),
        span: Span::default(),
        flags: 0,
    }
}

impl Fixture {
    fn new(names: &[&str]) -> Self {
        let mut builder = FactBuilder::new();
        for name in names {
            builder.ensure_symbol(name, FileId::NONE).unwrap();
        }
        let path = builder.intern("heap-cache.scala").unwrap();
        let source = builder.intern("").unwrap();
        builder.facts.files.push(FileRecord {
            path,
            source,
            revision: StrId::NONE,
            context: StrId::NONE,
            source_hash: ContentHash::default(),
            flags: SOURCE_VERIFIED,
        });
        let facts = builder.finish().unwrap();
        let mut graph = ProgramGraph {
            facts_identity: facts.identity,
            ..Default::default()
        };
        for index in 0..names.len() {
            graph.symbol_nodes.push(NodeId(index as u32));
            graph.nodes.push(NodeRecord {
                symbol: SymbolId(index as u32),
                file: FileId(0),
                body: BodyId::NONE,
                flags: 0,
            });
        }
        Self { facts, graph }
    }

    fn args(&mut self, ids: &[u32]) -> IdRange {
        let start = self.facts.operands.len() as u32;
        self.facts.operands.extend(ids.iter().copied().map(ValueId));
        IdRange {
            start,
            len: ids.len() as u32,
        }
    }

    fn body(&mut self, node: u32, params: &[u32], mut operations: Vec<OperationRecord>) {
        let id = BodyId(self.facts.bodies.len() as u32);
        let parameters = self.args(params);
        let start = self.facts.operations.len() as u32;
        for operation in &mut operations {
            operation.body = id;
        }
        self.facts.bodies.push(BodyRecord {
            symbol: SymbolId(node),
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange {
                start,
                len: operations.len() as u32,
            },
            parameters,
            body_hash: ContentHash::default(),
            flags: 0,
        });
        self.facts.operations.extend(operations);
        self.graph.nodes[node as usize].body = id;
    }

    fn seal(&mut self, revision: u8) {
        self.graph.edges.clear();
        for (index, operation) in self.facts.operations.iter().enumerate() {
            let kind = match operation.opcode {
                Opcode::Call => EdgeKind::Call,
                Opcode::Allocate => EdgeKind::Construct,
                _ => continue,
            };
            if operation.target.is_none() {
                continue;
            }
            self.graph.edges.push(EdgeRecord {
                source: NodeId(self.facts.bodies[operation.body.index()].symbol.0),
                target: NodeId(operation.target.0),
                kind,
                occurrence: OccurrenceId::NONE,
                operation: OperationId(index as u32),
                receiver: SymbolId::NONE,
                flags: 0,
            });
        }
        self.graph.index().unwrap();
        self.facts.identity = ContentHash([revision; 32]);
        self.graph.facts_identity = self.facts.identity;
        self.graph.identity = ContentHash([revision + 1; 32]);
    }

    fn allocation(&self) -> OperationId {
        OperationId(
            self.facts
                .operations
                .iter()
                .position(|op| op.opcode == Opcode::Allocate)
                .unwrap() as u32,
        )
    }
}

fn call(target: u32, receiver: u32, dest: u32) -> OperationRecord {
    OperationRecord {
        target: SymbolId(target),
        a: ValueId(receiver),
        dest: ValueId(dest),
        ..op(Opcode::Call)
    }
}

fn bind(target: u32, dest: u32) -> OperationRecord {
    OperationRecord {
        target: SymbolId(target),
        dest: ValueId(dest),
        ..op(Opcode::BindCallback)
    }
}

fn store(member: u32, object: u32, value: u32) -> OperationRecord {
    OperationRecord {
        target: SymbolId(member),
        a: ValueId(object),
        b: ValueId(value),
        ..op(Opcode::StoreField)
    }
}

fn load(member: u32, object: u32, dest: u32) -> OperationRecord {
    OperationRecord {
        target: SymbolId(member),
        a: ValueId(object),
        dest: ValueId(dest),
        ..op(Opcode::LoadField)
    }
}

fn roots(coarse: bool) -> Vec<ExecutionRoot> {
    let mut roots = vec![
        ExecutionRoot {
            node: NodeId(0),
            receiver: SymbolId(0),
        },
        ExecutionRoot {
            node: NodeId(1),
            receiver: SymbolId(1),
        },
    ];
    if coarse {
        roots.push(ExecutionRoot {
            node: NodeId(10),
            receiver: SymbolId::NONE,
        });
    }
    roots
}

/// The two roots allocate Carrier at the same factory operation. Its outer
/// field retains the receiver origin through the constructor and callback read.
fn carrier_fixture(revision: u8, callback_b: Option<u32>) -> Fixture {
    let mut f = Fixture::new(&[
        "ownerA#",
        "ownerB#",
        "factory",
        "Carrier#",
        "$outer",
        "ownerCallback",
        "carrierRun",
        "callbackA",
        "callbackB",
        "callbackReplacement",
        "coarseRoot",
    ]);
    for index in [0, 1, 3] {
        f.facts.symbols[index].kind = 13;
        f.facts.symbols[index].flags = SYMBOL_DEFINED;
    }
    for root in 0..2 {
        let mut operations = Vec::new();
        let callback = if root == 0 { Some(7) } else { callback_b };
        if let Some(callback) = callback {
            operations.extend([bind(callback, 1), store(5, 0, 1)]);
        }
        let arguments = f.args(&[0]);
        operations.push(OperationRecord {
            arguments,
            ..call(2, 0, 2)
        });
        f.body(root, &[], operations);
    }
    let arguments = f.args(&[1]);
    f.body(
        2,
        &[1],
        vec![
            OperationRecord {
                target: SymbolId(3),
                dest: ValueId(2),
                arguments,
                ..op(Opcode::Allocate)
            },
            call(6, 2, 3),
            OperationRecord {
                a: ValueId(2),
                ..op(Opcode::Return)
            },
        ],
    );
    f.body(3, &[1], vec![store(4, 0, 1)]);
    f.body(
        6,
        &[],
        vec![
            load(4, 0, 1),
            load(5, 1, 2),
            OperationRecord {
                a: ValueId(2),
                ..op(Opcode::InvokeCallback)
            },
        ],
    );
    for node in [4, 5, 7, 8, 9] {
        f.body(node, &[], vec![]);
    }
    // A scalar outer argument contributes bottom, without introducing an
    // unknown outer value, while receiver NONE makes the allocation coarse.
    let arguments = f.args(&[1]);
    f.body(
        10,
        &[],
        vec![
            OperationRecord {
                dest: ValueId(1),
                ..op(Opcode::Constant)
            },
            OperationRecord {
                arguments,
                ..call(2, 0, 2)
            },
            call(6, 2, 3),
        ],
    );
    f.seal(revision);
    f
}

fn group_for_root(session: &QuerySession<'_>, root: NodeId) -> usize {
    let context = session
        .roots
        .iter()
        .find(|id| session.contexts[id.index()].key.node == root)
        .unwrap();
    family_groups(session)
        .0
        .iter()
        .position(|group| group.contains(context))
        .unwrap()
}

fn proof(mut result: AnalysisResult) -> String {
    result.metrics = AnalysisMetrics::default();
    format!("{result:?}")
}

/// A direct callback cell also makes contributor removal visible in ALL.
fn callback_fixture(revision: u8, callback_b: Option<u32>, constructor_writes: bool) -> Fixture {
    let mut fixture = carrier_fixture(revision, callback_b);
    fixture.facts.operations.clear();
    fixture.facts.operands.clear();
    fixture.facts.bodies.clear();
    for node in &mut fixture.graph.nodes {
        node.body = BodyId::NONE;
    }
    for root in 0..2 {
        let callback = if root == 0 { Some(7) } else { callback_b };
        let mut operations = Vec::new();
        if let Some(callback) = callback {
            let arguments = fixture.args(&[1]);
            operations.extend([
                bind(callback, 1),
                OperationRecord {
                    arguments,
                    ..call(2, 0, 2)
                },
            ]);
        }
        fixture.body(root, &[], operations);
    }
    let arguments = fixture.args(&[1]);
    fixture.body(
        2,
        &[1],
        vec![
            OperationRecord {
                target: SymbolId(3),
                dest: ValueId(2),
                arguments,
                ..op(Opcode::Allocate)
            },
            call(6, 2, 3),
            OperationRecord {
                a: ValueId(2),
                ..op(Opcode::Return)
            },
        ],
    );
    fixture.body(
        3,
        &[1],
        if constructor_writes {
            vec![store(5, 0, 1)]
        } else {
            vec![]
        },
    );
    fixture.body(
        6,
        &[],
        vec![
            load(5, 0, 1),
            OperationRecord {
                a: ValueId(1),
                ..op(Opcode::InvokeCallback)
            },
        ],
    );
    for node in [4, 5, 7, 8, 9] {
        fixture.body(node, &[], vec![]);
    }
    let arguments = fixture.args(&[1]);
    fixture.body(
        10,
        &[],
        vec![
            OperationRecord {
                dest: ValueId(1),
                ..op(Opcode::Constant)
            },
            OperationRecord {
                arguments,
                ..call(2, 0, 2)
            },
            call(6, 2, 3),
        ],
    );
    fixture.seal(revision);
    fixture
}

fn coarse_consumer(session: &mut QuerySession<'_>, allocation: OperationId) -> ContextId {
    let receiver = session
        .pool
        .singleton(Atom {
            kind: AtomKind::Object,
            site: allocation,
            symbol: SymbolId(3),
            binding: 0,
        })
        .unwrap();
    let id = session
        .context(ContextKey {
            node: NodeId(6),
            receiver,
            arguments: FrameId(0),
        })
        .unwrap();
    session.roots.push(id);
    id
}

#[test]
fn exact_receiver_origin_writers_remain_independent_without_a_coarse_reader() {
    let fixture = carrier_fixture(101, Some(8));
    for workers in [1, 4] {
        let options = SolveOptions {
            workers,
            ..Default::default()
        };
        let mut session = QuerySession::new(&fixture.facts, &fixture.graph, &options).unwrap();
        session.execute(&roots(false)).unwrap();
        let result = session.analyze(&[NodeId(7)]).unwrap();
        assert_eq!(result.completion, Completion::Complete);
        assert!(result.contains(NodeId(0)));
        assert!(
            !result.contains(NodeId(1)),
            "shared factory allocation must preserve the receiver origin"
        );
        assert!(result.guarded_roots.is_empty());
        assert_ne!(
            group_for_root(&session, NodeId(0)),
            group_for_root(&session, NodeId(1))
        );
        assert_eq!(family_groups(&session).0.len(), 2);
        assert!(
            !session
                .dependencies
                .active_reads()
                .any(|(_, read)| read.slot.kind == SlotKind::FieldAll)
        );
        assert!(
            session
                .dependencies
                .active_reads()
                .any(|(_, read)| read.slot.kind == SlotKind::FieldWildcard)
        );
        assert!(
            session
                .writes
                .iter()
                .all(|(_, slot)| !matches!(slot.kind, SlotKind::FieldAll | SlotKind::FieldMissing))
        );
    }
}

#[test]
fn actual_coarse_reader_joins_all_contributing_origin_families() {
    let fixture = carrier_fixture(103, Some(8));
    let options = SolveOptions {
        workers: 4,
        ..Default::default()
    };
    let mut session = QuerySession::new(&fixture.facts, &fixture.graph, &options).unwrap();
    session.execute(&roots(true)).unwrap();
    assert!(
        session
            .dependencies
            .active_reads()
            .any(|(_, read)| read.slot.kind == SlotKind::FieldAll)
    );
    assert_eq!(family_groups(&session).0.len(), 1);
    for seed in [7, 8] {
        let result = session.analyze(&[NodeId(seed)]).unwrap();
        assert!(result.contains(NodeId(if seed == 7 { 0 } else { 1 })));
        assert!(!result.contains(NodeId(if seed == 7 { 1 } else { 0 })));
        assert!(
            result.contains(NodeId(10)),
            "coarse consumer sees every actual contributor"
        );
        assert!(result.guarded_roots.is_empty());
    }
}

#[test]
fn restore_rebuilds_unobserved_all_from_admitted_primary_writers() {
    let fixture = carrier_fixture(105, Some(8));
    let options = SolveOptions {
        workers: 2,
        ..Default::default()
    };
    let directory = tempfile::tempdir().unwrap();
    let runtime =
        SolverRuntime::with_cache_directory(&options, directory.path(), ContentHash([109; 32]))
            .unwrap();
    {
        let mut session =
            QuerySession::with_runtime(&fixture.facts, &fixture.graph, &options, &runtime).unwrap();
        session.execute(&roots(false)).unwrap();
        assert_eq!(family_groups(&session).0.len(), 2);
        session.persist_completed().unwrap();
    }
    let mut restored =
        QuerySession::with_runtime(&fixture.facts, &fixture.graph, &options, &runtime).unwrap();
    assert_eq!(restored.reuse_metrics().loaded_families, 2);
    let all = Slot {
        kind: SlotKind::FieldAll,
        owner: fixture.allocation().0,
        member: 4,
    };
    let outer = restored
        .slots
        .get(&all)
        .expect("unobserved derived ALL is rebuilt");
    let mut origins: Vec<_> = restored
        .pool
        .members(outer.value)
        .iter()
        .filter(|atom| atom.kind == AtomKind::Object)
        .map(|atom| atom.symbol)
        .collect();
    origins.sort_unstable();
    assert_eq!(origins, [SymbolId(0), SymbolId(1)]);
    restored.execute(&roots(true)).unwrap();
    let mut fresh = QuerySession::new(&fixture.facts, &fixture.graph, &options).unwrap();
    fresh.execute(&roots(true)).unwrap();
    for seed in [7, 8] {
        let actual = restored.analyze(&[NodeId(seed)]).unwrap();
        assert!(actual.contains(NodeId(10)));
        assert_eq!(
            proof(actual),
            proof(fresh.analyze(&[NodeId(seed)]).unwrap())
        );
    }
}

#[test]
fn missing_all_read_wakes_when_a_later_constructor_publishes_and_roundtrips_full_proof() {
    let fixture = callback_fixture(111, Some(8), true);
    let control = Arc::new(SolveControl::default());
    control.checkpoint_after_round(1);
    let options = SolveOptions {
        workers: 2,
        control: Some(control.clone()),
        ..Default::default()
    };
    let directory = tempfile::tempdir().unwrap();
    let runtime =
        SolverRuntime::with_cache_directory(&options, directory.path(), ContentHash([113; 32]))
            .unwrap();
    let expected;
    {
        let mut session =
            QuerySession::with_runtime(&fixture.facts, &fixture.graph, &options, &runtime).unwrap();
        let consumer = coarse_consumer(&mut session, fixture.allocation());
        session.execute(&roots(false)).unwrap();
        assert_eq!(session.stop_reason(), Some(StopReason::CheckpointRequested));
        let all = Slot {
            kind: SlotKind::FieldAll,
            owner: fixture.allocation().0,
            member: 5,
        };
        assert!(
            session
                .dependencies
                .active_reads()
                .any(|(query, read)| query == consumer
                    && read.slot == all
                    && !read.present
                    && read.version == 0)
        );
        assert!(
            !session.slots.contains_key(&all),
            "consumer really observed the absent aggregate before its constructor writer"
        );
        control.reset();
        session.resume().unwrap();
        let result = session.analyze(&[NodeId(7)]).unwrap();
        assert_eq!(result.completion, Completion::Complete);
        assert!(result.contains(NodeId(6)) && result.contains(NodeId(0)));
        assert!(!result.contains(NodeId(1)));
        assert!(result.guarded_roots.is_empty());
        assert!(
            session
                .dependencies
                .active_reads()
                .any(|(query, read)| query == consumer
                    && read.slot == all
                    && read.present
                    && read.version > 0)
        );
        assert!(session.metrics.invalidations > 0);
        expected = proof(result);
        session.persist_completed().unwrap();
    }
    let mut restored =
        QuerySession::with_runtime(&fixture.facts, &fixture.graph, &options, &runtime).unwrap();
    assert_eq!(restored.reuse_metrics().loaded_families, 1);
    assert_eq!(proof(restored.analyze(&[NodeId(7)]).unwrap()), expected);
    let mut fresh = QuerySession::new(&fixture.facts, &fixture.graph, &options).unwrap();
    coarse_consumer(&mut fresh, fixture.allocation());
    fresh.execute(&roots(false)).unwrap();
    assert_eq!(proof(fresh.analyze(&[NodeId(7)]).unwrap()), expected);
}

#[test]
fn changing_or_removing_a_contributor_rejects_the_old_family_and_aggregate() {
    for callback_b in [Some(9), None] {
        let base = callback_fixture(115, Some(8), true);
        let head = callback_fixture(117, callback_b, true);
        let options = SolveOptions {
            workers: 2,
            ..Default::default()
        };
        let directory = tempfile::tempdir().unwrap();
        let runtime =
            SolverRuntime::with_cache_directory(&options, directory.path(), ContentHash([119; 32]))
                .unwrap();
        {
            let mut session =
                QuerySession::with_runtime(&base.facts, &base.graph, &options, &runtime).unwrap();
            session.execute(&roots(true)).unwrap();
            assert_eq!(family_groups(&session).0.len(), 1);
            session.persist_completed().unwrap();
        }
        let mut restored =
            QuerySession::with_runtime(&head.facts, &head.graph, &options, &runtime).unwrap();
        assert_eq!(restored.reuse_metrics().loaded_families, 0);
        assert_eq!(restored.reuse_metrics().rejected_families, 1);
        assert!(
            restored.slots.is_empty(),
            "a rejected aggregate cannot survive as an independent cache cell"
        );
        restored.execute(&roots(true)).unwrap();
        let all = Slot {
            kind: SlotKind::FieldAll,
            owner: head.allocation().0,
            member: 5,
        };
        let value = restored.slots.get(&all).unwrap().value;
        let mut callbacks: Vec<_> = restored
            .pool
            .members(value)
            .iter()
            .filter(|atom| atom.kind == AtomKind::Callback)
            .map(|atom| atom.symbol)
            .collect();
        callbacks.sort_unstable();
        assert_eq!(
            callbacks,
            if callback_b.is_some() {
                vec![SymbolId(7), SymbolId(9)]
            } else {
                vec![SymbolId(7)]
            }
        );
        let mut fresh = QuerySession::new(&head.facts, &head.graph, &options).unwrap();
        fresh.execute(&roots(true)).unwrap();
        for seed in [7, 8, 9] {
            assert_eq!(
                proof(restored.analyze(&[NodeId(seed)]).unwrap()),
                proof(fresh.analyze(&[NodeId(seed)]).unwrap())
            );
        }
        let stale = restored.analyze(&[NodeId(8)]).unwrap();
        assert!(
            !stale.contains(NodeId(0)) && !stale.contains(NodeId(1)) && !stale.contains(NodeId(10))
        );
    }
}

#[test]
fn partial_rebase_rebuilds_unobserved_all_only_from_admitted_contributors() {
    for callback_b in [Some(9), None] {
        let base = callback_fixture(129, Some(8), true);
        let head = callback_fixture(131, callback_b, true);
        let options = SolveOptions {
            workers: 2,
            ..Default::default()
        };
        let directory = tempfile::tempdir().unwrap();
        let runtime =
            SolverRuntime::with_cache_directory(&options, directory.path(), ContentHash([133; 32]))
                .unwrap();
        {
            let mut session =
                QuerySession::with_runtime(&base.facts, &base.graph, &options, &runtime).unwrap();
            session.execute(&roots(false)).unwrap();
            assert_eq!(family_groups(&session).0.len(), 2);
            session.persist_completed().unwrap();
        }
        let mut restored =
            QuerySession::with_runtime(&head.facts, &head.graph, &options, &runtime).unwrap();
        assert_eq!(restored.reuse_metrics().loaded_families, 1);
        assert_eq!(restored.reuse_metrics().rejected_families, 1);
        let all = Slot {
            kind: SlotKind::FieldAll,
            owner: head.allocation().0,
            member: 5,
        };
        let value = restored.slots.get(&all).unwrap().value;
        let callbacks: Vec<_> = restored
            .pool
            .members(value)
            .iter()
            .filter(|atom| atom.kind == AtomKind::Callback)
            .map(|atom| atom.symbol)
            .collect();
        assert_eq!(
            callbacks,
            [SymbolId(7)],
            "the rejected contributor cannot leak through its former derived ALL cell"
        );
        restored.execute(&roots(true)).unwrap();
        let mut fresh = QuerySession::new(&head.facts, &head.graph, &options).unwrap();
        fresh.execute(&roots(true)).unwrap();
        for seed in [7, 8, 9] {
            assert_eq!(
                proof(restored.analyze(&[NodeId(seed)]).unwrap()),
                proof(fresh.analyze(&[NodeId(seed)]).unwrap())
            );
        }
        restored.persist_completed().unwrap();
        let mut repeated =
            QuerySession::with_runtime(&head.facts, &head.graph, &options, &runtime).unwrap();
        assert!(repeated.reuse_metrics().loaded_families > 0);
        assert_eq!(repeated.reuse_metrics().rejected_families, 0);
        assert_eq!(
            proof(repeated.analyze(&[NodeId(7)]).unwrap()),
            proof(fresh.analyze(&[NodeId(7)]).unwrap())
        );
    }
}

#[test]
fn optional_and_finalized_negative_subscribers_stay_independent_and_reject_authority_changes() {
    let base = callback_fixture(121, Some(8), false);
    let mut head = callback_fixture(123, Some(8), false);
    // An unexecuted recipe can introduce a new writer in a future execution.
    // Its authority change must revoke both independently finalized absences.
    let unrelated = head.graph.nodes[4].body;
    head.facts.bodies[unrelated.index()].body_hash = ContentHash([125; 32]);
    let mut execution = roots(false);
    execution.push(ExecutionRoot {
        node: NodeId(9),
        receiver: SymbolId::NONE,
    });
    let options = SolveOptions {
        workers: 2,
        execution_roots: Some(Arc::from(execution.clone())),
        ..Default::default()
    };
    let directory = tempfile::tempdir().unwrap();
    let runtime =
        SolverRuntime::with_cache_directory(&options, directory.path(), ContentHash([127; 32]))
            .unwrap();
    {
        let mut session =
            QuerySession::with_runtime(&base.facts, &base.graph, &options, &runtime).unwrap();
        session.execute(&execution).unwrap();
        assert_eq!(family_groups(&session).0.len(), 3);
        assert_ne!(
            group_for_root(&session, NodeId(0)),
            group_for_root(&session, NodeId(1))
        );
        let wildcard = Slot {
            kind: SlotKind::FieldWildcard,
            owner: base.allocation().0,
            member: 5,
        };
        assert_eq!(
            session
                .dependencies
                .active_reads()
                .filter(|(_, read)| read.slot == wildcard)
                .count(),
            2
        );
        assert!(!session.slots.contains_key(&wildcard));
        assert_eq!(
            session
                .slots
                .iter()
                .filter(|(slot, value)| slot.kind == SlotKind::FieldMissing
                    && value.value.unknown & UNKNOWN_FIELD != 0)
                .count(),
            2
        );
        // Even a shared writer-free negative certificate must never become a
        // synthetic owner connecting consumers merely because both read it.
        let shared = Slot {
            kind: SlotKind::FieldMissing,
            owner: u32::MAX,
            member: 5,
        };
        let root_contexts: Vec<_> = session
            .roots
            .iter()
            .copied()
            .filter(|id| session.contexts[id.index()].key.node.0 < 2)
            .collect();
        for query in root_contexts {
            session
                .dependencies
                .subscribe(
                    query,
                    Read {
                        slot: shared,
                        version: 0,
                        present: false,
                    },
                )
                .unwrap();
        }
        assert_eq!(family_groups(&session).0.len(), 3);
        let result = session.analyze(&[NodeId(7)]).unwrap();
        assert_eq!(result.guarded_roots, [NodeId(0), NodeId(1)]);
        session.persist_completed().unwrap();
    }
    let exact = QuerySession::with_runtime(&base.facts, &base.graph, &options, &runtime).unwrap();
    assert_eq!(exact.reuse_metrics().loaded_families, 3);
    drop(exact);
    let mut restored =
        QuerySession::with_runtime(&head.facts, &head.graph, &options, &runtime).unwrap();
    assert_eq!(
        restored.reuse_metrics().loaded_families,
        1,
        "the unrelated positive root remains reusable"
    );
    assert_eq!(
        restored.reuse_metrics().rejected_families,
        2,
        "each negative consumer must re-establish global absence authority"
    );
    restored.execute(&execution).unwrap();
    let mut fresh = QuerySession::new(&head.facts, &head.graph, &options).unwrap();
    fresh.execute(&execution).unwrap();
    assert_eq!(
        proof(restored.analyze(&[NodeId(7)]).unwrap()),
        proof(fresh.analyze(&[NodeId(7)]).unwrap())
    );
}

#[test]
fn symbol_reorder_rebinds_object_origin_tokens_and_exact_heap_owner_roots() {
    let base = carrier_fixture(135, Some(8));
    let mut head = carrier_fixture(137, Some(8));
    let remap = |symbol: SymbolId| match symbol.0 {
        0 => SymbolId(1),
        1 => SymbolId(0),
        _ => symbol,
    };
    head.facts.symbols.swap(0, 1);
    for symbol in &mut head.facts.symbols {
        symbol.owner = remap(symbol.owner);
    }
    for occurrence in &mut head.facts.occurrences {
        occurrence.symbol = remap(occurrence.symbol);
    }
    for relation in &mut head.facts.relations {
        relation.source = remap(relation.source);
        relation.target = remap(relation.target);
    }
    for body in &mut head.facts.bodies {
        body.symbol = remap(body.symbol);
    }
    for operation in &mut head.facts.operations {
        operation.target = remap(operation.target);
    }
    for row in &mut head.facts.result_bounds {
        row.symbol = remap(row.symbol);
    }
    for class in &mut head.facts.bound_classes {
        *class = remap(*class);
    }
    for suite in &mut head.facts.suites {
        suite.symbol = remap(suite.symbol);
    }
    for issue in &mut head.facts.issues {
        issue.symbol = remap(issue.symbol);
    }
    head.graph.symbol_nodes.fill(NodeId::NONE);
    for (index, node) in head.graph.nodes.iter_mut().enumerate() {
        node.symbol = remap(node.symbol);
        head.graph.symbol_nodes[node.symbol.index()] = NodeId(index as u32);
    }
    for edge in &mut head.graph.edges {
        edge.receiver = remap(edge.receiver);
    }
    for issue in &mut head.graph.issues {
        issue.symbol = remap(issue.symbol);
    }
    for diagnostic in &mut head.graph.diagnostics {
        diagnostic.symbol = remap(diagnostic.symbol);
    }
    head.graph.index().unwrap();
    assert_eq!(head.facts.symbol_name(SymbolId(1)), "ownerA#");
    assert_eq!(head.graph.node_for_symbol(SymbolId(1)), Some(NodeId(0)));
    let options = SolveOptions {
        workers: 2,
        ..Default::default()
    };
    let directory = tempfile::tempdir().unwrap();
    let runtime =
        SolverRuntime::with_cache_directory(&options, directory.path(), ContentHash([139; 32]))
            .unwrap();
    {
        let mut session =
            QuerySession::with_runtime(&base.facts, &base.graph, &options, &runtime).unwrap();
        session.execute(&roots(false)).unwrap();
        assert_eq!(family_groups(&session).0.len(), 2);
        session.persist_completed().unwrap();
    }
    let mut restored =
        QuerySession::with_runtime(&head.facts, &head.graph, &options, &runtime).unwrap();
    assert_eq!(restored.reuse_metrics().loaded_families, 2);
    assert_eq!(restored.reuse_metrics().rejected_families, 0);
    assert!(!restored.reuse_metrics().same_snapshot);
    let groups = family_groups(&restored).0;
    for root in [NodeId(0), NodeId(1)] {
        let symbol = head.graph.nodes[root.index()].symbol;
        let owner = restored
            .heap_owners
            .lookup(HeapOwnerKey {
                site: head.allocation(),
                root: symbol,
            })
            .unwrap();
        let slot = Slot {
            kind: SlotKind::Field,
            owner,
            member: 4,
        };
        let outer = restored.slots.get(&slot).unwrap().value;
        assert_eq!(
            restored.pool.members(outer),
            [Atom {
                kind: AtomKind::Object,
                site: OperationId::NONE,
                symbol,
                binding: 0
            }]
        );
        let group = &groups[group_for_root(&restored, root)];
        let constructor = group
            .iter()
            .find(|id| restored.contexts[id.index()].key.node == NodeId(3))
            .unwrap();
        let receiver = restored.contexts[constructor.index()].key.receiver;
        assert_eq!(
            restored.pool.members(receiver),
            [Atom {
                kind: AtomKind::Object,
                site: head.allocation(),
                symbol: SymbolId(3),
                binding: symbol.0 + 1
            }],
            "allocation origins use the current compiler symbol ID plus one"
        );
    }
    let mut execution = roots(false);
    for root in &mut execution {
        root.receiver = remap(root.receiver);
    }
    restored.execute(&execution).unwrap();
    let mut fresh = QuerySession::new(&head.facts, &head.graph, &options).unwrap();
    fresh.execute(&execution).unwrap();
    for seed in [7, 8] {
        let actual = restored.analyze(&[NodeId(seed)]).unwrap();
        assert!(actual.contains(NodeId(if seed == 7 { 0 } else { 1 })));
        assert!(!actual.contains(NodeId(if seed == 7 { 1 } else { 0 })));
        assert!(actual.guarded_roots.is_empty());
        assert_eq!(
            proof(actual),
            proof(fresh.analyze(&[NodeId(seed)]).unwrap())
        );
    }
}

#[test]
fn cached_object_identity_requires_an_allocation_and_an_in_range_origin() {
    let fixture = carrier_fixture(141, Some(8));
    let types = TypeIndex::new(&fixture.facts);
    assert!(
        validate_cached_object(&fixture.facts, &types, fixture.allocation(), SymbolId(3), 1)
            .is_ok()
    );
    assert!(
        validate_cached_object(&fixture.facts, &types, fixture.allocation(), SymbolId(3), 0)
            .is_ok()
    );
    assert!(
        validate_cached_object(&fixture.facts, &types, OperationId::NONE, SymbolId(0), 0).is_ok()
    );
    for (site, symbol, binding) in [
        (OperationId::NONE, SymbolId(0), 1),
        (OperationId(0), SymbolId(3), 1),
        (
            OperationId(fixture.facts.operations.len() as u32),
            SymbolId(3),
            1,
        ),
        (fixture.allocation(), SymbolId::NONE, 1),
        (
            fixture.allocation(),
            SymbolId(3),
            fixture.facts.symbols.len() as u32 + 1,
        ),
    ] {
        assert!(matches!(
            validate_cached_object(&fixture.facts, &types, site, symbol, binding),
            Err(Error::Invalid("cached object identity"))
        ));
    }
    let mut module = Fixture::new(&["p/Module."]);
    module.facts.symbols[0].kind = 10;
    let mut allocation = op(Opcode::Allocate);
    allocation.target = SymbolId(0);
    allocation.dest = ValueId(0);
    module.body(0, &[], vec![allocation]);
    let types = TypeIndex::new(&module.facts);
    assert_eq!(types.global_module_owner(SymbolId(0)), Some(SymbolId(0)));
    for binding in [0, 1] {
        assert!(matches!(
            validate_cached_object(&module.facts, &types, OperationId(0), SymbolId(0), binding),
            Err(Error::Invalid("cached object identity"))
        ));
    }
}

#[test]
fn cached_aggregate_validation_rejects_missing_contributors_stale_values_and_wrong_sites() {
    let fixture = callback_fixture(143, Some(8), true);
    let options = SolveOptions {
        workers: 1,
        ..Default::default()
    };
    for corruption in [0, 1, 2] {
        let mut session = QuerySession::new(&fixture.facts, &fixture.graph, &options).unwrap();
        session.execute(&roots(false)).unwrap();
        restore_heap_aggregates(&mut session).unwrap();
        let all = Slot {
            kind: SlotKind::FieldAll,
            owner: fixture.allocation().0,
            member: 5,
        };
        match corruption {
            0 => {
                let owner = session
                    .heap_owners
                    .lookup(HeapOwnerKey {
                        site: fixture.allocation(),
                        root: SymbolId(1),
                    })
                    .unwrap();
                assert!(
                    session
                        .slots
                        .remove(&Slot {
                            kind: SlotKind::Field,
                            owner,
                            member: 5
                        })
                        .is_some()
                );
            }
            1 => {
                session.slots.get_mut(&all).unwrap().value = Value::EMPTY;
            }
            _ => {
                let value = session.slots.remove(&all).unwrap();
                session.slots.insert(Slot { owner: 0, ..all }, value);
            }
        }
        let error = restore_heap_aggregates(&mut session).unwrap_err();
        let expected = if corruption == 2 {
            "cached aggregate allocation authority"
        } else {
            "cached aggregate contributor closure"
        };
        assert!(matches!(error, Error::Invalid(actual) if actual == expected));
    }
}

fn shape_fixture(revision: u8, rebase: bool) -> Fixture {
    let names = if rebase {
        [
            "factory",
            "consumer",
            "callbackB",
            "callbackA",
            "changed",
            "dormant",
        ]
    } else {
        [
            "factory",
            "consumer",
            "callbackA",
            "callbackB",
            "changed",
            "dormant",
        ]
    };
    let mut f = Fixture::new(&names);
    if rebase {
        f.body(5, &[], vec![op(Opcode::Constant)]);
    }
    let callbacks = if rebase { [3, 2] } else { [2, 3] };
    f.body(0, &[], vec![bind(callbacks[0], 1), bind(callbacks[1], 2)]);
    let mut invoke = op(Opcode::InvokeCallback);
    invoke.a = ValueId(1);
    invoke.dest = ValueId(2);
    let mut ret = op(Opcode::Return);
    ret.a = ValueId(2);
    f.body(1, &[1], vec![invoke, ret]);
    for callback in callbacks {
        let mut change = op(Opcode::Call);
        change.target = SymbolId(4);
        f.body(callback, &[], vec![change]);
    }
    f.body(4, &[], vec![]);
    if !rebase {
        f.body(5, &[], vec![]);
    }
    f.seal(revision);
    f
}
fn shape_options(workers: usize) -> SolveOptions {
    SolveOptions {
        workers,
        max_set_members: 1,
        context_policy: ContextPolicy::BoundedArguments {
            max_variants_per_receiver: 1,
        },
        ..Default::default()
    }
}
fn seed_shape_contexts(session: &mut QuerySession<'_>) {
    let symbol = |name: &str| {
        SymbolId(
            session
                .facts
                .symbols
                .iter()
                .position(|s| session.facts.text(s.name) == name)
                .unwrap() as u32,
        )
    };
    let callbacks = [symbol("callbackA"), symbol("callbackB")];
    let receivers = [callbacks[0], callbacks[1], symbol("changed")];
    let sites = callbacks.map(|symbol| {
        OperationId(
            session
                .facts
                .operations
                .iter()
                .position(|o| o.opcode == Opcode::BindCallback && o.target == symbol)
                .unwrap() as u32,
        )
    });
    // Seed valid published capture identities, then execute their real factory
    // contexts so cache closure has actual Capture writer provenance. Context
    // admission itself performs the argument widening under test.
    for (code, site) in sites.into_iter().enumerate() {
        for (variant, receiver) in receivers.into_iter().enumerate() {
            let binding = (code * 3 + variant) as u32;
            let receiver = session
                .pool
                .singleton(Atom {
                    kind: AtomKind::Object,
                    site: OperationId::NONE,
                    symbol: receiver,
                    binding: 0,
                })
                .unwrap();
            session.closure_families.insert(
                ClosureFamily {
                    site,
                    receiver,
                    arguments: FrameId(0),
                    origins: Value::EMPTY,
                },
                binding,
            );
            session.captures.insert(
                binding,
                Capture {
                    receiver,
                    arguments: FrameId(0),
                    version: 1,
                },
            );
            let callback = session
                .pool
                .singleton(Atom {
                    kind: AtomKind::Callback,
                    site,
                    symbol: callbacks[code],
                    binding,
                })
                .unwrap();
            let arguments = session.frames.intern(&[callback]).unwrap();
            let id = session
                .context(ContextKey {
                    node: NodeId(1),
                    receiver: Value::EMPTY,
                    arguments,
                })
                .unwrap();
            if !session.roots.contains(&id) {
                session.roots.push(id);
            }
        }
    }
    for receiver in receivers {
        let receiver = session
            .pool
            .singleton(Atom {
                kind: AtomKind::Object,
                site: OperationId::NONE,
                symbol: receiver,
                binding: 0,
            })
            .unwrap();
        let id = session
            .context(ContextKey {
                node: NodeId(0),
                receiver,
                arguments: FrameId(0),
            })
            .unwrap();
        session.roots.push(id);
    }
}
fn assert_separate_shape_overflows(session: &QuerySession<'_>) {
    let rows: Vec<_> = session
        .contexts
        .iter()
        .filter(|c| c.key.node == NodeId(1) && c.widened)
        .collect();
    assert_eq!(rows.len(), 2);
    assert_eq!(
        rows[0].key, rows[1].key,
        "both payloads widened to the same current frame"
    );
    assert_ne!(rows[0].callback_shape, rows[1].callback_shape);
    for row in rows {
        let payload = session.frames.get(row.key.arguments)[0];
        assert!(session.pool.members(payload).is_empty());
        assert_ne!(payload.unknown & WIDENED_VALUE, 0);
        let shape = session.callback_shapes.get(row.callback_shape);
        assert_eq!(shape.arity, 1);
        assert_eq!(shape.atoms.len(), 1);
        assert!(!shape.atoms[0].site.is_none());
    }
}
#[test]
fn callback_creation_shapes_survive_payload_widening_exact_restore_and_symbol_operation_rebase() {
    for rebase in [false, true] {
        let old = shape_fixture(151, false);
        let current = shape_fixture(if rebase { 153 } else { 151 }, rebase);
        let directory = tempfile::tempdir().unwrap();
        let options = shape_options(1);
        let producer = ContentHash([151; 32]);
        let runtime =
            SolverRuntime::with_cache_directory(&options, directory.path(), producer).unwrap();
        let original_contexts;
        {
            let mut session =
                QuerySession::with_runtime(&old.facts, &old.graph, &options, &runtime).unwrap();
            seed_shape_contexts(&mut session);
            assert_separate_shape_overflows(&session);
            session.resume().unwrap();
            assert_separate_shape_overflows(&session);
            let replay_path = directory.path().join("portable-family");
            let limits = crate::replay::ReplayLimits::default();
            let report = session
                .export_replay_family(NodeId(1), None, &replay_path, &limits, 64)
                .unwrap();
            assert_eq!(report.inventory.total_variants, 4);
            let portable = crate::replay::ReplayFamily::read(&replay_path, &limits).unwrap();
            let outcomes = portable
                .replay(&crate::replay::ReplayOptions::default())
                .unwrap();
            assert_eq!(outcomes.len(), 4);
            for context in session
                .contexts
                .iter()
                .enumerate()
                .filter(|(_, c)| c.key.node == NodeId(1) && c.widened)
            {
                assert!(
                    outcomes
                        .iter()
                        .any(|outcome| outcome.context == context.0 as u32)
                );
            }
            let reduction = portable
                .minimize(
                    &crate::replay::MinimizeOptions::default(),
                    &crate::replay::ReplayFamilyPredicate::default(),
                )
                .unwrap();
            assert_eq!(reduction.outcomes.len(), 4);
            assert_eq!(reduction.outcomes, outcomes);
            session.persist_completed().unwrap();
            original_contexts = session.contexts.len() as u64;
        }
        let next = shape_options(4);
        let runtime =
            SolverRuntime::with_cache_directory(&next, directory.path(), producer).unwrap();
        let mut restored =
            QuerySession::with_runtime(&current.facts, &current.graph, &next, &runtime).unwrap();
        assert_eq!(restored.reuse_metrics().loaded_contexts, original_contexts);
        assert_eq!(restored.reuse_metrics().same_snapshot, !rebase);
        assert_separate_shape_overflows(&restored);
        for context in &restored.contexts {
            for atom in restored.callback_shapes.get(context.callback_shape).atoms {
                if !atom.site.is_none() {
                    let operation = &current.facts.operations[atom.site.index()];
                    assert_eq!(operation.opcode, Opcode::BindCallback);
                    assert_eq!(operation.target, atom.symbol);
                }
            }
        }
        let mut fresh = QuerySession::new(&current.facts, &current.graph, &next).unwrap();
        seed_shape_contexts(&mut fresh);
        fresh.resume().unwrap();
        assert_eq!(
            proof(restored.analyze(&[NodeId(4)]).unwrap()),
            proof(fresh.analyze(&[NodeId(4)]).unwrap())
        );
    }
}

fn shape_group_range(bytes: &[u8], offset: usize) -> (usize, usize, usize) {
    const HEADER: usize = 3 * 4 + 6 * 32;
    assert_eq!(u32::from_le_bytes(bytes[..4].try_into().unwrap()), VERSION);
    let mut cursor = HEADER;
    while cursor < bytes.len() {
        let length = u64::from_le_bytes(bytes[cursor..cursor + 8].try_into().unwrap()) as usize;
        let start = cursor + 8;
        let end = start + length;
        if (start..end).contains(&offset) {
            return (cursor, start, end);
        }
        cursor = end;
    }
    panic!("shape row is not inside a family");
}
#[test]
fn malformed_cached_creation_shapes_and_unfingerprinted_code_fail_before_session_admission() {
    let f = shape_fixture(155, false);
    let schema = Schema::new(&f.facts, &f.graph, false).unwrap();
    let mut encoded = Writer(Vec::new());
    encoded.n(1); // arity
    encoded.n(1); // rows
    encoded.n(0); // argument
    encoded.operation(&schema, OperationId(0)).unwrap();
    encoded.symbol(&schema, SymbolId(2));
    let pattern = encoded.0;
    for corruption in 0..8 {
        let directory = tempfile::tempdir().unwrap();
        let options = shape_options(1);
        let runtime =
            SolverRuntime::with_cache_directory(&options, directory.path(), ContentHash([155; 32]))
                .unwrap();
        let config = runtime.inner.cache.as_ref().unwrap();
        {
            let mut session =
                QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
            seed_shape_contexts(&mut session);
            session.resume().unwrap();
            session.persist_completed().unwrap();
        }
        super::tests::rewrite(config, &f.graph, &options, |bytes| {
            let start = bytes
                .windows(pattern.len())
                .position(|row| row == pattern)
                .unwrap();
            let (length_offset, family_start, family_end) = shape_group_range(bytes, start);
            match corruption {
                0 => bytes[start..start + 4].copy_from_slice(&0u32.to_le_bytes()),
                1 => bytes[start + 8..start + 12].copy_from_slice(&1u32.to_le_bytes()),
                2 => {
                    let mut null = Writer(Vec::new());
                    null.operation(&schema, OperationId::NONE).unwrap();
                    bytes[start + 12..start + 48].copy_from_slice(&null.0);
                }
                3 => {
                    let mut wrong = Writer(Vec::new());
                    wrong.operation(&schema, OperationId(2)).unwrap();
                    bytes[start + 12..start + 48].copy_from_slice(&wrong.0);
                }
                4 => {
                    let mut wrong = Writer(Vec::new());
                    wrong.symbol(&schema, SymbolId(3));
                    bytes[start + 48..start + 84].copy_from_slice(&wrong.0);
                }
                5 => {
                    let row = bytes[start + 8..start + 84].to_vec();
                    bytes[start + 4..start + 8].copy_from_slice(&2u32.to_le_bytes());
                    bytes.splice(start + 84..start + 84, row);
                    let length = (family_end - family_start + 76) as u64;
                    bytes[length_offset..length_offset + 8].copy_from_slice(&length.to_le_bytes());
                }
                6 => {
                    let mut node = Writer(Vec::new());
                    node.node(&schema, NodeId(1));
                    let offset = start
                        + pattern.len()
                        + bytes[start + pattern.len()..family_end]
                            .windows(node.0.len())
                            .position(|row| row == node.0)
                            .unwrap();
                    bytes[offset + 56..offset + 60].copy_from_slice(&u32::MAX.to_le_bytes());
                }
                _ => {
                    let mut old = Writer(Vec::new());
                    old.node(&schema, NodeId(0));
                    old.key(schema.fingerprints[0]);
                    let mut replacement = Writer(Vec::new());
                    replacement.node(&schema, NodeId(5));
                    replacement.key(schema.fingerprints[5]);
                    let offset = family_start
                        + bytes[family_start..start]
                            .windows(old.0.len())
                            .position(|row| row == old.0)
                            .unwrap();
                    bytes[offset..offset + old.0.len()].copy_from_slice(&replacement.0);
                }
            }
        });
        assert!(
            QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).is_err(),
            "bad callback creation shape {corruption}"
        );
    }
}
#[test]
fn shape_only_overflow_authority_is_invalidated_when_its_creation_recipe_changes() {
    let original = shape_fixture(157, false);
    let mut changed = shape_fixture(159, false);
    changed.facts.bodies[changed.graph.nodes[0].body.index()].body_hash = ContentHash([159; 32]);
    let options = shape_options(1);
    let directory = tempfile::tempdir().unwrap();
    let runtime =
        SolverRuntime::with_cache_directory(&options, directory.path(), ContentHash([157; 32]))
            .unwrap();
    {
        let mut session =
            QuerySession::with_runtime(&original.facts, &original.graph, &options, &runtime)
                .unwrap();
        seed_shape_contexts(&mut session);
        session.resume().unwrap();
        assert_separate_shape_overflows(&session);
        session.persist_completed().unwrap();
    }
    let restored =
        QuerySession::with_runtime(&changed.facts, &changed.graph, &options, &runtime).unwrap();
    assert!(restored.reuse_metrics().rejected_families > 0);
    assert!(
        restored
            .contexts
            .iter()
            .all(|context| context.key.node != NodeId(1)),
        "lost callback payload must not drop its creation-recipe admission dependency"
    );
}
