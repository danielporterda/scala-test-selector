//! Discarding a return must discard only its summary subscription, never work.
use selector_domain::{Atom, Read, Slot, SlotKind, Value, ValuePool};
use selector_facts::*;
use selector_graph::*;
use selector_result::AnalysisResult;
use selector_solve::*;
use selector_transfer::{Evaluation, Scratch, SummaryRead, TypeIndex, World};
use selector_types::*;
use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};

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
fn call(target: u32, dest: ValueId) -> OperationRecord {
    OperationRecord {
        target: SymbolId(target),
        dest,
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
fn invoke(value: u32, dest: ValueId) -> OperationRecord {
    OperationRecord {
        a: ValueId(value),
        dest,
        ..op(Opcode::InvokeCallback)
    }
}
fn fixture(guarded: bool) -> (FactSnapshot, ProgramGraph) {
    let mut b = FactBuilder::new();
    let path = b.intern("effect-only-calls.scala").unwrap();
    let source = b.intern("").unwrap();
    b.facts.files.push(FileRecord {
        path,
        source,
        context: StrId::NONE,
        revision: StrId::NONE,
        source_hash: ContentHash([191; 32]),
        flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
    });
    for name in [
        "unused_direct",
        "unused_callback",
        "used_direct",
        "used_callback",
        "publisher",
        "captured_work",
        "changed",
        "reader",
        "shared_field",
        "external",
        "unrelated",
        "lifecycle",
        "explicit_initialize",
        "modeled_callback",
        "model_callee",
        "bodyless_model",
        "bodyless_consumer",
    ] {
        let id = b.ensure_symbol(name, FileId(0)).unwrap();
        let symbol = &mut b.facts.symbols[id.index()];
        symbol.kind = 3;
        symbol.flags = SYMBOL_DEFINED;
    }
    for root in [0, 1, 2, 3, 7, 10, 11, 12, 13, 16] {
        let symbol = &mut b.facts.symbols[root];
        symbol.kind = 13;
        symbol.flags |= SYMBOL_SCALA_PARENTS_COMPLETE;
        symbol.properties = 8;
    }
    b.facts.symbols[8].properties = 1024;
    b.facts.symbols[4].owner = SymbolId(0);
    b.facts.symbols[4].properties = 8;
    let captured = IdRange { start: 0, len: 1 };
    let parameter = IdRange { start: 1, len: 1 };
    let modeled = IdRange { start: 2, len: 1 };
    b.facts
        .operands
        .extend([ValueId(1), ValueId(1), ValueId(1)]);
    let mut publisher = vec![
        bind(6, 1),
        OperationRecord {
            arguments: captured,
            ..bind(5, 2)
        },
        OperationRecord {
            target: SymbolId(8),
            b: ValueId(2),
            flags: OP_STATIC_FIELD,
            ..op(Opcode::StoreField)
        },
        OperationRecord {
            a: ValueId(2),
            ..op(Opcode::Return)
        },
    ];
    if guarded {
        publisher.push(call(9, ValueId::NONE));
    }
    let operations = [
        vec![call(4, ValueId::NONE)],
        vec![bind(4, 1), invoke(1, ValueId::NONE)],
        vec![call(4, ValueId(1)), invoke(1, ValueId::NONE)],
        vec![bind(4, 1), invoke(1, ValueId(2)), invoke(2, ValueId::NONE)],
        publisher,
        vec![
            OperationRecord {
                dest: ValueId(1),
                flags: 1,
                ..op(Opcode::Parameter)
            },
            invoke(1, ValueId::NONE),
        ],
        vec![],
        vec![
            OperationRecord {
                target: SymbolId(8),
                dest: ValueId(1),
                flags: OP_STATIC_FIELD,
                ..op(Opcode::LoadField)
            },
            invoke(1, ValueId::NONE),
        ],
        vec![],
        vec![],
        vec![],
        vec![],
        vec![OperationRecord {
            opcode: Opcode::Initialize,
            ..call(4, ValueId::NONE)
        }],
        vec![
            bind(4, 1),
            OperationRecord {
                arguments: modeled,
                ..call(14, ValueId::NONE)
            },
        ],
        vec![],
        vec![],
        vec![call(15, ValueId(1)), invoke(1, ValueId::NONE)],
    ];
    let mut bodies = vec![BodyId::NONE; operations.len()];
    for (symbol, mut operations) in operations.into_iter().enumerate() {
        if matches!(symbol, 9 | 15) {
            continue;
        } // The adverse callee really lacks a recipe.
        let body = BodyId(b.facts.bodies.len() as u32);
        bodies[symbol] = body;
        for operation in &mut operations {
            operation.body = body;
        }
        b.facts.bodies.push(BodyRecord {
            symbol: SymbolId(symbol as u32),
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            body_hash: ContentHash([symbol as u8; 32]),
            flags: 0,
            parameters: if symbol == 5 {
                parameter
            } else {
                IdRange::default()
            },
            operations: IdRange {
                start: b.facts.operations.len() as u32,
                len: operations.len() as u32,
            },
        });
        b.facts.operations.extend(operations);
    }
    let mut facts = b.finish().unwrap();
    facts.identity = ContentHash([192 + u8::from(guarded); 32]);
    let mut graph = ProgramGraph {
        identity: ContentHash([194 + u8::from(guarded); 32]),
        facts_identity: facts.identity,
        ..Default::default()
    };
    for (symbol, body) in bodies.into_iter().enumerate() {
        graph.symbol_nodes.push(NodeId(symbol as u32));
        graph.nodes.push(NodeRecord {
            symbol: SymbolId(symbol as u32),
            file: FileId(0),
            body,
            flags: 0,
        });
    }
    for (index, operation) in facts.operations.iter().enumerate() {
        let kind = match operation.opcode {
            Opcode::Call => EdgeKind::Call,
            Opcode::Initialize => EdgeKind::Initialize,
            _ => continue,
        };
        let source = facts.bodies[operation.body.index()].symbol.0;
        graph.edges.push(EdgeRecord {
            source: NodeId(source),
            target: NodeId(operation.target.0),
            kind,
            operation: OperationId(index as u32),
            occurrence: OccurrenceId::NONE,
            receiver: SymbolId::NONE,
            flags: if source == 13 {
                EDGE_CALLBACK_IMMEDIATE | encode_callback_argument(0).unwrap()
            } else {
                0
            },
        });
    }
    graph.edges.push(EdgeRecord {
        source: NodeId(11),
        target: NodeId(4),
        kind: EdgeKind::Call,
        occurrence: OccurrenceId::NONE,
        operation: OperationId::NONE,
        receiver: SymbolId::NONE,
        flags: 0,
    });
    // Unlike body-owned lifecycle edges, this body's structural calls define
    // the model's returned value and still need their summary dependency.
    graph.edges.push(EdgeRecord {
        source: NodeId(15),
        target: NodeId(4),
        kind: EdgeKind::Call,
        occurrence: OccurrenceId::NONE,
        operation: OperationId::NONE,
        receiver: SymbolId::NONE,
        flags: 0,
    });
    graph.index().unwrap();
    facts.validate().unwrap();
    graph.validate().unwrap();
    (facts, graph)
}
fn roots() -> Vec<ExecutionRoot> {
    [0, 1, 2, 3, 7, 10, 11, 12, 13, 16]
        .into_iter()
        .map(|node| ExecutionRoot {
            node: NodeId(node),
            receiver: SymbolId(node),
        })
        .collect()
}
fn options(workers: usize) -> SolveOptions {
    SolveOptions {
        workers,
        execution_roots: Some(Arc::from(roots())),
        census: CensusOptions {
            capacity: 32,
            evaluation_stride: 1,
        },
        ..Default::default()
    }
}
fn proof(mut result: AnalysisResult) -> String {
    result.metrics = Default::default();
    format!("{result:?}")
}

struct EmptyWorld {
    values: ValuePool,
    summary_reads: AtomicUsize,
}
impl World for EmptyWorld {
    fn values(&self) -> &ValuePool {
        &self.values
    }
    fn summary(
        &self,
        _: NodeId,
        _: Value,
        _: &[Value],
        _: &ValuePool,
        _: &mut Vec<Value>,
    ) -> SummaryRead {
        self.summary_reads.fetch_add(1, Ordering::Relaxed);
        SummaryRead {
            context: None,
            value: Value::EMPTY,
            version: 0,
            present: false,
        }
    }
    fn slot(&self, _: Slot) -> (Value, u64, bool) {
        (Value::EMPTY, 0, false)
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

#[test]
fn discarded_direct_callback_model_and_lifecycle_results_never_read_summaries() {
    let (facts, graph) = fixture(false);
    let types = TypeIndex::new(&facts);
    let world = EmptyWorld {
        values: ValuePool::new(64),
        summary_reads: AtomicUsize::new(0),
    };
    let mut scratch = Scratch::new(64);
    let mut output = Evaluation::default();
    for node in [0, 1, 11, 12, 13] {
        let before = world.summary_reads.load(Ordering::Relaxed);
        selector_transfer::evaluate(
            &facts,
            &graph,
            &types,
            &world,
            NodeId(node),
            Value::EMPTY,
            &[],
            &mut scratch,
            &mut output,
        )
        .unwrap();
        assert!(
            !output.calls.is_empty(),
            "node {node} must still call its callee"
        );
        assert!(
            output.calls.iter().all(|call| !call.observe_return),
            "node {node}"
        );
        assert!(
            output
                .reads
                .iter()
                .all(|read: &Read| read.slot.kind != SlotKind::Summary)
        );
        assert_eq!(
            world.summary_reads.load(Ordering::Relaxed),
            before,
            "node {node}"
        );
    }
    for node in [2, 3, 15] {
        let before = world.summary_reads.load(Ordering::Relaxed);
        selector_transfer::evaluate(
            &facts,
            &graph,
            &types,
            &world,
            NodeId(node),
            Value::EMPTY,
            &[],
            &mut scratch,
            &mut output,
        )
        .unwrap();
        assert!(output.calls.iter().any(|call| call.observe_return));
        assert!(world.summary_reads.load(Ordering::Relaxed) > before);
    }
}

#[test]
fn effects_guards_captures_and_used_return_wakeups_survive_workers_and_cache() {
    for guarded in [false, true] {
        let (facts, graph) = fixture(guarded);
        let mut expected = None;
        for workers in [1, 4] {
            let options = options(workers);
            let directory = tempfile::tempdir().unwrap();
            let runtime = SolverRuntime::with_cache_directory(
                &options,
                directory.path(),
                ContentHash([196; 32]),
            )
            .unwrap();
            let answer = {
                let mut session =
                    QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
                session.execute(&roots()).unwrap();
                assert_eq!(session.stop_reason(), None);
                for node in [0, 1, 11, 12, 13] {
                    let row = session
                        .work_census()
                        .iter()
                        .find(|row| row.node == NodeId(node))
                        .unwrap();
                    assert_eq!(row.evaluations, 1, "discarded-return node {node}");
                }
                for node in [2, 3, 7, 16] {
                    let row = session
                        .work_census()
                        .iter()
                        .find(|row| row.node == NodeId(node))
                        .unwrap();
                    assert!(
                        row.reevaluations > 0,
                        "used return/negative field must resume: {node}"
                    );
                }
                let answer = session.analyze(&[NodeId(6)]).unwrap();
                for node in [2, 3, 7, 16] {
                    assert!(
                        answer.contains(NodeId(node)),
                        "callback execution node {node}"
                    );
                }
                assert!(!answer.evidence.captures.is_empty());
                assert!(
                    answer
                        .evidence
                        .witnesses
                        .iter()
                        .any(|witness| witness.binding != u32::MAX)
                );
                for node in [0, 1, 2, 3, 11, 12, 13, 16] {
                    assert_eq!(
                        answer.guarded_roots.contains(&NodeId(node)),
                        guarded,
                        "transitive callee guard at {node}"
                    );
                }
                assert!(!answer.guarded_roots.contains(&NodeId(10)));
                let called = session.analyze(&[NodeId(4)]).unwrap();
                for node in [0, 1, 2, 3, 11, 12, 13, 16] {
                    assert!(
                        called.contains(NodeId(node)),
                        "effect-only execution edge at {node}"
                    );
                }
                session.persist_completed().unwrap();
                proof(answer)
            };
            let mut warm = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
            warm.execute(&roots()).unwrap();
            let restored = warm.analyze(&[NodeId(6)]).unwrap();
            assert_eq!(restored.metrics.edge_visits, 0);
            assert_eq!(
                proof(restored),
                answer,
                "warm worker{workers} guarded{guarded}"
            );
            if let Some(expected) = &expected {
                assert_eq!(&answer, expected, "worker determinism");
            } else {
                expected = Some(answer);
            }
        }
    }
}

#[test]
fn effect_only_calls_resume_from_a_checkpoint_without_losing_effects() {
    let (facts, graph) = fixture(true);
    let mut limited = options(1);
    limited.max_steps = 1;
    let mut paused = QuerySession::new(&facts, &graph, &limited).unwrap();
    paused.execute(&roots()).unwrap();
    assert_eq!(paused.stop_reason(), Some(StopReason::StepLimit));
    let directory = tempfile::tempdir().unwrap();
    let checkpoint = directory.path().join("effect-only.bin");
    let producer = ContentHash([197; 32]);
    paused.save_checkpoint(&checkpoint, producer).unwrap();
    drop(paused);
    let options = options(4);
    let runtime = SolverRuntime::new(&options).unwrap();
    let mut resumed =
        QuerySession::from_checkpoint(&facts, &graph, &options, &runtime, &checkpoint, producer)
            .unwrap();
    resumed.resume().unwrap();
    assert_eq!(resumed.stop_reason(), None);
    let actual = resumed.analyze(&[NodeId(6)]).unwrap();
    let mut fresh = QuerySession::new(&facts, &graph, &options).unwrap();
    fresh.execute(&roots()).unwrap();
    assert_eq!(proof(actual), proof(fresh.analyze(&[NodeId(6)]).unwrap()));
}
