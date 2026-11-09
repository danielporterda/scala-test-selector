//! A type-clause representative is not the producer of a cached value.
use selector_facts::*;
use selector_graph::*;
use selector_result::AnalysisResult;
use selector_solve::*;
use selector_types::*;

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
fn call(target: u32) -> OperationRecord {
    OperationRecord {
        target: SymbolId(target),
        ..op(Opcode::Call)
    }
}
fn fixture(
    representative: Option<u32>,
    actual: Option<u32>,
    revision: u8,
    representative_body_edit: bool,
) -> (FactSnapshot, ProgramGraph) {
    let mut builder = FactBuilder::new();
    let path = builder.intern("bound-cache.scala").unwrap();
    let source = builder.intern("").unwrap();
    builder.facts.files.push(FileRecord {
        path,
        source,
        revision: StrId::NONE,
        context: StrId::NONE,
        source_hash: ContentHash::default(),
        flags: SOURCE_VERIFIED,
    });
    for name in [
        "representative",
        "actual",
        "provider",
        "Base",
        "Narrow",
        "Allowed",
        "Sibling",
        "Base.work",
        "Allowed.work",
        "Sibling.work",
        "changed",
        "pure",
    ] {
        let id = builder.ensure_symbol(name, FileId(0)).unwrap();
        builder.facts.symbols[id.index()].flags = SYMBOL_DEFINED;
    }
    for id in 3..=6 {
        let symbol = &mut builder.facts.symbols[id];
        symbol.kind = if id <= 4 { 14 } else { 13 };
        symbol.flags |= SYMBOL_SCALA_PARENTS_COMPLETE;
        if id >= 5 {
            symbol.properties |= 8;
        }
    }
    for (child, parent) in [(4, 3), (5, 4), (6, 3)] {
        builder.facts.relations.push(RelationRecord {
            source: SymbolId(child),
            target: SymbolId(parent),
            kind: RelationKind::Parent,
            file: FileId(0),
        });
    }
    for (method, owner) in [(7, 3), (8, 5), (9, 6)] {
        builder.facts.symbols[method].owner = SymbolId(owner);
    }
    for symbol in 0..12 {
        let mut operations = match symbol {
            0 => vec![OperationRecord {
                dest: ValueId(1),
                ..call(2)
            }],
            1 => vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..call(2)
                },
                OperationRecord {
                    target: SymbolId(7),
                    a: ValueId(1),
                    ..op(Opcode::VirtualCall)
                },
            ],
            2 => vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..op(Opcode::Unknown)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::Return)
                },
            ],
            9 => vec![call(10)],
            _ => vec![],
        };
        let body = BodyId(builder.facts.bodies.len() as u32);
        let start = builder.facts.operations.len() as u32;
        for operation in &mut operations {
            operation.body = body;
        }
        builder.facts.bodies.push(BodyRecord {
            symbol: SymbolId(symbol),
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange {
                start,
                len: operations.len() as u32,
            },
            parameters: IdRange::default(),
            body_hash: if symbol == 0 && representative_body_edit {
                ContentHash([91; 32])
            } else {
                ContentHash::default()
            },
            flags: 0,
        });
        builder.facts.operations.extend(operations);
    }
    for (operation, clause) in [(0, representative), (1, actual)] {
        if let Some(class) = clause {
            let start = builder.facts.bound_classes.len() as u32;
            builder.facts.bound_classes.push(SymbolId(class));
            builder.facts.result_bounds.push(ResultBoundRecord {
                symbol: SymbolId(2),
                operation: OperationId(operation),
                classes: IdRange { start, len: 1 },
            });
        }
    }
    let mut facts = builder.finish().unwrap();
    facts.identity = ContentHash([revision; 32]);
    let mut graph = ProgramGraph {
        facts_identity: facts.identity,
        identity: ContentHash([revision + 1; 32]),
        ..Default::default()
    };
    for id in 0..12 {
        graph.nodes.push(NodeRecord {
            symbol: SymbolId(id),
            file: FileId(0),
            body: BodyId(id),
            flags: 0,
        });
        graph.symbol_nodes.push(NodeId(id));
    }
    for (id, operation) in facts.operations.iter().enumerate() {
        if operation.opcode == Opcode::Call {
            graph.edges.push(EdgeRecord {
                source: NodeId(operation.body.0),
                target: NodeId(operation.target.0),
                kind: EdgeKind::Call,
                occurrence: OccurrenceId::NONE,
                operation: OperationId(id as u32),
                receiver: SymbolId::NONE,
                flags: 0,
            });
        }
    }
    for (method, owner) in [(8, 5), (9, 6)] {
        graph.edges.push(EdgeRecord {
            source: NodeId(1),
            target: NodeId(method),
            kind: EdgeKind::VirtualCall,
            occurrence: OccurrenceId::NONE,
            operation: OperationId(2),
            receiver: SymbolId(owner),
            flags: 0,
        });
    }
    graph.index().unwrap();
    facts.validate().unwrap();
    graph.validate().unwrap();
    (facts, graph)
}
fn roots() -> [ExecutionRoot; 2] {
    [1, 11].map(|node| ExecutionRoot {
        node: NodeId(node),
        receiver: SymbolId::NONE,
    })
}
fn proof(mut result: AnalysisResult) -> String {
    result.metrics = Default::default();
    format!("{result:?}")
}

#[test]
fn actual_operation_changes_cannot_hide_behind_an_unchanged_semantic_representative() {
    for workers in [1, 3] {
        for actual in [Some(3), None] {
            let (base_facts, base_graph) = fixture(Some(4), Some(4), 181, false);
            let options = SolveOptions {
                workers,
                ..Default::default()
            };
            let directory = tempfile::tempdir().unwrap();
            let runtime = SolverRuntime::with_cache_directory(
                &options,
                directory.path(),
                ContentHash([183; 32]),
            )
            .unwrap();
            {
                let mut base =
                    QuerySession::with_runtime(&base_facts, &base_graph, &options, &runtime)
                        .unwrap();
                base.execute(&roots()).unwrap();
                assert!(!base.analyze(&[NodeId(10)]).unwrap().contains(NodeId(1)));
                base.persist_completed().unwrap();
            }
            let (facts, graph) = fixture(Some(4), actual, 183, false);
            let mut fresh = QuerySession::new(&facts, &graph, &options).unwrap();
            fresh.execute(&roots()).unwrap();
            let expected = fresh.analyze(&[NodeId(10)]).unwrap();
            assert!(
                expected.contains(NodeId(1)),
                "broader/missing actual constraint must admit sibling work"
            );
            let mut cached =
                QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
            assert_eq!(
                cached.reuse_metrics().loaded_families,
                1,
                "unrelated pure family is reusable"
            );
            assert_eq!(
                cached.reuse_metrics().rejected_families,
                1,
                "actual producer recipe must invalidate its family"
            );
            cached.execute(&roots()).unwrap();
            assert_eq!(
                proof(cached.analyze(&[NodeId(10)]).unwrap()),
                proof(expected)
            );
            assert!(cached.metrics().edge_visits > 0);
        }
    }
}

#[test]
fn representative_changes_rebind_exact_classes_without_reinterpreting_or_invalidating_callers() {
    for workers in [1, 3] {
        for (representative, body_edit) in [(Some(3), false), (None, false), (Some(4), true)] {
            let (base_facts, base_graph) = fixture(Some(4), Some(4), 185, false);
            let options = SolveOptions {
                workers,
                ..Default::default()
            };
            let directory = tempfile::tempdir().unwrap();
            let runtime = SolverRuntime::with_cache_directory(
                &options,
                directory.path(),
                ContentHash([187; 32]),
            )
            .unwrap();
            {
                let mut base =
                    QuerySession::with_runtime(&base_facts, &base_graph, &options, &runtime)
                        .unwrap();
                base.execute(&roots()).unwrap();
                base.persist_completed().unwrap();
            }
            let (facts, graph) = fixture(representative, Some(4), 187, body_edit);
            let mut fresh = QuerySession::new(&facts, &graph, &options).unwrap();
            fresh.execute(&roots()).unwrap();
            let expected = fresh.analyze(&[NodeId(10)]).unwrap();
            assert!(!expected.contains(NodeId(1)));
            let mut cached =
                QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
            assert_eq!(
                cached.reuse_metrics().loaded_families,
                2,
                "same exact semantic clause must remain reusable"
            );
            assert_eq!(cached.reuse_metrics().rejected_families, 0);
            cached.execute(&roots()).unwrap();
            assert_eq!(
                proof(cached.analyze(&[NodeId(10)]).unwrap()),
                proof(expected)
            );
            assert_eq!(
                cached.metrics().edge_visits,
                0,
                "representative is not a causal body dependency"
            );
        }
    }
}
