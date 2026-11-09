//! Counterexamples exercising state shared by previously independent roots.
use selector_facts::*;
use selector_graph::*;
use selector_solve::*;
use selector_types::*;

fn operation(opcode: Opcode) -> OperationRecord {
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
fn call(target: u32, dest: u32) -> OperationRecord {
    OperationRecord {
        target: SymbolId(target),
        dest: ValueId(dest),
        ..operation(Opcode::Call)
    }
}
fn fixture(writer_added: bool, revision: u8) -> (FactSnapshot, ProgramGraph) {
    let mut b = FactBuilder::new();
    let path = b.intern("cache-audit.scala").unwrap();
    let source = b.intern("").unwrap();
    b.facts.files.push(FileRecord {
        path,
        source,
        revision: StrId::NONE,
        context: StrId::NONE,
        source_hash: ContentHash::default(),
        flags: SOURCE_VERIFIED,
    });
    for name in [
        "reader", "writer", "provider", "class", "closure", "changed", "field", "pure",
    ] {
        let id = b.ensure_symbol(name, FileId(0)).unwrap();
        b.facts.symbols[id.index()].file = FileId(0);
    }
    b.facts.symbols[3].kind = 13;
    let reader = vec![
        call(2, 1),
        OperationRecord {
            target: SymbolId(6),
            a: ValueId(1),
            dest: ValueId(2),
            ..operation(Opcode::LoadField)
        },
        OperationRecord {
            a: ValueId(2),
            ..operation(Opcode::InvokeCallback)
        },
    ];
    let writer = if writer_added {
        vec![
            call(2, 1),
            OperationRecord {
                target: SymbolId(4),
                dest: ValueId(2),
                ..operation(Opcode::BindCallback)
            },
            OperationRecord {
                target: SymbolId(6),
                a: ValueId(1),
                b: ValueId(2),
                ..operation(Opcode::StoreField)
            },
        ]
    } else {
        vec![]
    };
    let provider = vec![
        OperationRecord {
            target: SymbolId(3),
            dest: ValueId(1),
            ..operation(Opcode::Allocate)
        },
        OperationRecord {
            a: ValueId(1),
            ..operation(Opcode::Return)
        },
    ];
    for (symbol, mut ops) in [
        reader,
        writer,
        provider,
        vec![],
        vec![call(5, u32::MAX)],
        vec![],
        vec![],
        vec![],
    ]
    .into_iter()
    .enumerate()
    {
        let body = BodyId(b.facts.bodies.len() as u32);
        let start = b.facts.operations.len() as u32;
        for op in &mut ops {
            op.body = body;
        }
        b.facts.bodies.push(BodyRecord {
            symbol: SymbolId(symbol as u32),
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange {
                start,
                len: ops.len() as u32,
            },
            parameters: IdRange::default(),
            body_hash: ContentHash::default(),
            flags: 0,
        });
        b.facts.operations.extend(ops);
    }
    let mut facts = b.finish().unwrap();
    facts.identity = ContentHash([revision; 32]);
    let mut graph = ProgramGraph {
        identity: ContentHash([revision + 1; 32]),
        facts_identity: facts.identity,
        ..Default::default()
    };
    for i in 0..facts.symbols.len() {
        graph.nodes.push(NodeRecord {
            symbol: SymbolId(i as u32),
            file: FileId(0),
            body: BodyId(i as u32),
            flags: 0,
        });
        graph.symbol_nodes.push(NodeId(i as u32));
    }
    for (index, op) in facts.operations.iter().enumerate() {
        let kind = match op.opcode {
            Opcode::Call => EdgeKind::Call,
            Opcode::Allocate => EdgeKind::Construct,
            _ => continue,
        };
        graph.edges.push(EdgeRecord {
            source: NodeId(op.body.0),
            target: NodeId(op.target.0),
            kind,
            occurrence: OccurrenceId::NONE,
            operation: OperationId(index as u32),
            receiver: SymbolId::NONE,
            flags: 0,
        });
    }
    graph.index().unwrap();
    graph.validate().unwrap();
    (facts, graph)
}
fn roots() -> [ExecutionRoot; 3] {
    [0, 1, 7].map(|node| ExecutionRoot {
        node: NodeId(node),
        receiver: SymbolId::NONE,
    })
}

#[test]
fn new_writer_in_previous_independent_family_does_not_retain_sealed_field_absence() {
    for workers in [1, 3] {
        let options = SolveOptions {
            workers,
            ..Default::default()
        };
        let dir = tempfile::tempdir().unwrap();
        let runtime =
            SolverRuntime::with_cache_directory(&options, dir.path(), ContentHash([31; 32]))
                .unwrap();
        let (base_facts, base_graph) = fixture(false, 1);
        {
            let mut base =
                QuerySession::with_runtime(&base_facts, &base_graph, &options, &runtime).unwrap();
            base.execute(&roots()).unwrap();
            assert!(base
                .analyze(&[NodeId(5)])
                .unwrap()
                .guarded_roots
                .contains(&NodeId(0)));
            base.persist_completed().unwrap();
        }
        let (head_facts, head_graph) = fixture(true, 3);
        let mut fresh = QuerySession::new(&head_facts, &head_graph, &options).unwrap();
        fresh.execute(&roots()).unwrap();
        let fresh = fresh.analyze(&[NodeId(5)]).unwrap();
        let mut restored =
            QuerySession::with_runtime(&head_facts, &head_graph, &options, &runtime).unwrap();
        assert_eq!(
            restored.reuse_metrics().loaded_families,
            1,
            "unrelated pure family remains reusable"
        );
        assert_eq!(restored.reuse_metrics().loaded_contexts, 1);
        assert_eq!(restored.reuse_metrics().rejected_families, 2);
        restored.execute(&roots()).unwrap();
        let reused = restored.analyze(&[NodeId(5)]).unwrap();
        assert!(fresh.contains(NodeId(0)));
        assert!(!fresh.guarded_roots.contains(&NodeId(0)));
        assert_eq!(reused.affected, fresh.affected, "workers={workers}");
        assert_eq!(
            reused.guarded_roots, fresh.guarded_roots,
            "workers={workers}"
        );
        assert_eq!(reused.completion, fresh.completion, "workers={workers}");
    }
}

#[test]
fn positive_shared_heap_and_capture_family_survives_an_unrelated_body_edit() {
    for workers in [1, 3] {
        let options = SolveOptions {
            workers,
            ..Default::default()
        };
        let dir = tempfile::tempdir().unwrap();
        let runtime =
            SolverRuntime::with_cache_directory(&options, dir.path(), ContentHash([32; 32]))
                .unwrap();
        let (base_facts, base_graph) = fixture(true, 1);
        {
            let mut base =
                QuerySession::with_runtime(&base_facts, &base_graph, &options, &runtime).unwrap();
            base.execute(&roots()).unwrap();
            base.persist_completed().unwrap();
        }
        let (mut head_facts, head_graph) = fixture(true, 3);
        head_facts.bodies[7].body_hash = ContentHash([91; 32]);
        let mut restored =
            QuerySession::with_runtime(&head_facts, &head_graph, &options, &runtime).unwrap();
        assert_eq!(restored.reuse_metrics().loaded_families, 1);
        assert_eq!(restored.reuse_metrics().rejected_families, 1);
        assert!(restored.reuse_metrics().loaded_contexts >= 6);
        restored.execute(&roots()).unwrap();
        let reused = restored.analyze(&[NodeId(5)]).unwrap();
        let mut fresh = QuerySession::new(&head_facts, &head_graph, &options).unwrap();
        fresh.execute(&roots()).unwrap();
        let fresh = fresh.analyze(&[NodeId(5)]).unwrap();
        assert_eq!(reused.affected, fresh.affected, "workers={workers}");
        assert_eq!(
            reused.guarded_roots, fresh.guarded_roots,
            "workers={workers}"
        );
        assert_eq!(
            reused.derived_edges, fresh.derived_edges,
            "workers={workers}"
        );
        assert_eq!(reused.completion, fresh.completion, "workers={workers}");
        assert_eq!(
            reused.evidence.captures.len(),
            fresh.evidence.captures.len()
        );
    }
}

#[test]
fn malformed_persisted_families_and_references_fail_without_exposing_a_session() {
    use selector_artifacts::{ArtifactKind, Section};
    for corruption in 0..7 {
        let options = SolveOptions {
            workers: 1,
            memory_budget_bytes: 1024 * 1024,
            ..Default::default()
        };
        let directory = tempfile::tempdir().unwrap();
        let (facts, graph) = fixture(true, 1);
        let runtime =
            SolverRuntime::with_cache_directory(&options, directory.path(), ContentHash([33; 32]))
                .unwrap();
        {
            let mut session =
                QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
            session.execute(&roots()).unwrap();
            session.persist_completed().unwrap();
        }
        let refs: Vec<_> = std::fs::read_dir(directory.path())
            .unwrap()
            .map(|e| e.unwrap().path())
            .filter(|p| p.extension().is_some_and(|x| x == "ref"))
            .collect();
        let name = std::fs::read_to_string(&refs[0]).unwrap();
        let path = directory.path().join(&name);
        let artifact = selector_artifacts::open(&path, ArtifactKind::Summaries).unwrap();
        let original = std::fs::read(&path).unwrap();
        let replacement = match corruption {
            0 => "a".repeat(129),
            1 => format!("aé{}.rsel", "a".repeat(61)),
            2 => {
                let fake = format!("{}.rsel", "0".repeat(64));
                std::fs::copy(&path, directory.path().join(&fake)).unwrap();
                fake
            }
            3..=5 => {
                let mut bytes = artifact.section(1).unwrap().to_vec();
                let mut count = artifact.count(1).unwrap();
                if corruption == 3 {
                    // Version, max-set size and family count are u32; producer,
                    // policy, schema, facts, graph and content seal are keys.
                    const HEADER_BYTES: usize = 3 * size_of::<u32>() + 6 * 32;
                    // The capture-origin format preserves this header framing;
                    // corrupt the actual first family length, not a version tag.
                    assert_eq!(u32::from_le_bytes(bytes[..4].try_into().unwrap()), 15);
                    assert!(
                        u32::from_le_bytes(
                            bytes[HEADER_BYTES - 4..HEADER_BYTES].try_into().unwrap()
                        ) > 0
                    );
                    let length = HEADER_BYTES..HEADER_BYTES + size_of::<u64>();
                    let old_length = u64::from_le_bytes(bytes[length.clone()].try_into().unwrap());
                    assert!(old_length > 0 && old_length <= (bytes.len() - length.end) as u64);
                    bytes[length].copy_from_slice(&u64::MAX.to_le_bytes());
                }
                if corruption == 4 {
                    count += 1;
                }
                let mut sections = vec![Section {
                    id: 1,
                    count,
                    bytes: &bytes,
                }];
                if corruption == 5 {
                    sections.push(Section {
                        id: 2,
                        count: 0,
                        bytes: &[],
                    });
                }
                selector_artifacts::publish(directory.path(), ArtifactKind::Summaries, &sections)
                    .unwrap()
                    .path
                    .file_name()
                    .unwrap()
                    .to_str()
                    .unwrap()
                    .to_owned()
            }
            _ => {
                let mut bytes = original;
                *bytes.last_mut().unwrap() ^= 1;
                std::fs::remove_file(&path).unwrap();
                std::fs::write(&path, bytes).unwrap();
                name.clone()
            }
        };
        for reference in &refs {
            std::fs::write(reference, &replacement).unwrap();
        }
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            QuerySession::with_runtime(&facts, &graph, &options, &runtime)
        }));
        assert!(result.is_ok(), "cache corruption {corruption} panicked");
        assert!(
            result.unwrap().is_err(),
            "cache corruption {corruption} exposed a session"
        );
    }
}

fn root_field_fixture(
    order: &[&'static str],
    dormant_ops: usize,
    revision: u8,
) -> (
    FactSnapshot,
    ProgramGraph,
    std::collections::HashMap<&'static str, SymbolId>,
) {
    let mut builder = FactBuilder::new();
    let path = builder.intern("root-cell.scala").unwrap();
    let source = builder.intern("").unwrap();
    builder.facts.files.push(FileRecord {
        path,
        source,
        revision: StrId::NONE,
        context: StrId::NONE,
        source_hash: ContentHash::default(),
        flags: SOURCE_VERIFIED,
    });
    let names: std::collections::HashMap<_, _> = order
        .iter()
        .map(|name| (*name, builder.ensure_symbol(name, FileId(0)).unwrap()))
        .collect();
    let class = names["class"];
    let field = names["field"];
    builder.facts.symbols[class.index()].kind = 13;
    builder.facts.symbols[field.index()].owner = class;
    for &name in order {
        let mut ops = match name {
            "reader" | "late_reader" => vec![
                OperationRecord {
                    target: field,
                    a: ValueId(0),
                    dest: ValueId(1),
                    ..operation(Opcode::LoadField)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..operation(Opcode::InvokeCallback)
                },
            ],
            "writer" => vec![
                OperationRecord {
                    target: names["closure"],
                    dest: ValueId(1),
                    ..operation(Opcode::BindCallback)
                },
                OperationRecord {
                    target: field,
                    a: ValueId(0),
                    b: ValueId(1),
                    ..operation(Opcode::StoreField)
                },
            ],
            "closure" => vec![call(names["changed"].0, u32::MAX)],
            "dormant" => (0..dormant_ops)
                .map(|_| OperationRecord {
                    dest: ValueId(1),
                    ..operation(Opcode::Constant)
                })
                .collect(),
            _ => Vec::new(),
        };
        let body = BodyId(builder.facts.bodies.len() as u32);
        let start = builder.facts.operations.len() as u32;
        for op in &mut ops {
            op.body = body;
        }
        builder.facts.bodies.push(BodyRecord {
            symbol: names[name],
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange {
                start,
                len: ops.len() as u32,
            },
            parameters: IdRange::default(),
            body_hash: ContentHash::default(),
            flags: 0,
        });
        builder.facts.operations.extend(ops);
    }
    let mut facts = builder.finish().unwrap();
    facts.identity = ContentHash([revision; 32]);
    let mut graph = ProgramGraph {
        identity: ContentHash([revision + 1; 32]),
        facts_identity: facts.identity,
        ..Default::default()
    };
    for i in 0..facts.symbols.len() {
        graph.nodes.push(NodeRecord {
            symbol: SymbolId(i as u32),
            file: FileId(0),
            body: BodyId(i as u32),
            flags: 0,
        });
        graph.symbol_nodes.push(NodeId(i as u32));
    }
    for (index, op) in facts.operations.iter().enumerate() {
        if op.opcode == Opcode::Call {
            graph.edges.push(EdgeRecord {
                source: NodeId(facts.bodies[op.body.index()].symbol.0),
                target: NodeId(op.target.0),
                kind: EdgeKind::Call,
                occurrence: OccurrenceId::NONE,
                operation: OperationId(index as u32),
                receiver: SymbolId::NONE,
                flags: 0,
            });
        }
    }
    graph.index().unwrap();
    (facts, graph, names)
}

#[test]
fn root_field_heap_rebases_with_changed_operation_count_and_reordered_symbols() {
    for workers in [1, 3] {
        let options = SolveOptions {
            workers,
            ..Default::default()
        };
        let directory = tempfile::tempdir().unwrap();
        let runtime =
            SolverRuntime::with_cache_directory(&options, directory.path(), ContentHash([34; 32]))
                .unwrap();
        let (base_facts, base_graph, base_names) = root_field_fixture(
            &[
                "reader",
                "writer",
                "class",
                "closure",
                "changed",
                "field",
                "dormant",
                "late_reader",
            ],
            1,
            1,
        );
        let base_roots = ["reader", "writer"].map(|name| ExecutionRoot {
            node: NodeId(base_names[name].0),
            receiver: base_names["class"],
        });
        {
            let mut base =
                QuerySession::with_runtime(&base_facts, &base_graph, &options, &runtime).unwrap();
            base.execute(&base_roots).unwrap();
            let result = base.analyze(&[NodeId(base_names["changed"].0)]).unwrap();
            assert!(result.guarded_roots.is_empty());
            base.persist_completed().unwrap();
        }
        let (head_facts, head_graph, names) = root_field_fixture(
            &[
                "late_reader",
                "dormant",
                "field",
                "changed",
                "closure",
                "class",
                "writer",
                "reader",
            ],
            4,
            3,
        );
        assert_ne!(base_facts.operations.len(), head_facts.operations.len());
        assert_ne!(base_names["class"], names["class"]);
        let roots = ["reader", "writer", "late_reader"].map(|name| ExecutionRoot {
            node: NodeId(names[name].0),
            receiver: names["class"],
        });
        let mut restored =
            QuerySession::with_runtime(&head_facts, &head_graph, &options, &runtime).unwrap();
        assert_eq!(restored.reuse_metrics().loaded_families, 1);
        assert!(restored.reuse_metrics().loaded_contexts >= 4);
        restored.execute(&roots).unwrap();
        let reused = restored.analyze(&[NodeId(names["changed"].0)]).unwrap();
        let mut fresh = QuerySession::new(&head_facts, &head_graph, &options).unwrap();
        fresh.execute(&roots).unwrap();
        let fresh = fresh.analyze(&[NodeId(names["changed"].0)]).unwrap();
        assert!(
            reused.contains(NodeId(names["late_reader"].0)),
            "new root must read the restored root-cell heap using current namespace"
        );
        assert!(fresh.guarded_roots.is_empty());
        assert_eq!(reused.affected, fresh.affected, "workers={workers}");
        assert_eq!(
            reused.guarded_roots, fresh.guarded_roots,
            "workers={workers}"
        );
        assert_eq!(
            reused.derived_edges, fresh.derived_edges,
            "workers={workers}"
        );
        assert_eq!(reused.completion, fresh.completion, "workers={workers}");
    }
}
