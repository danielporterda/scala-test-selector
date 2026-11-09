//! Public-engine controls for explicit carriers, separate from compiler/backend
//! admission. The genuine compiler repeated-callbacks fixture checks lowering.
use selector_facts::*;
use selector_graph::ProgramGraph;
use selector_solve::{ExecutionRoot, QuerySession, SolveOptions, SolverRuntime};
use selector_types::*;
use std::sync::Arc;

fn op(opcode: Opcode, target: SymbolId, dest: u32, a: u32, args: IdRange) -> OperationRecord {
    OperationRecord {
        body: BodyId::NONE,
        opcode,
        target,
        dest: ValueId(dest),
        a: ValueId(a),
        b: ValueId::NONE,
        arguments: args,
        span: Span::default(),
        flags: 0,
    }
}
fn fixture() -> (FactSnapshot, ProgramGraph, [ExecutionRoot; 2], NodeId) {
    let mut b = FactBuilder::new();
    b.facts.revision = b.intern("carrier-core").unwrap();
    let context = b.intern("carrier/test").unwrap();
    let path = b.intern("carrier-core.class").unwrap();
    b.facts.files.push(FileRecord {
        path,
        source: StrId::NONE,
        revision: b.facts.revision,
        context,
        source_hash: ContentHash([1; 32]),
        flags: FILE_BINARY_SOURCE,
    });
    let names = [
        "p/Active#",
        "p/Dormant#",
        "p/Callbacks#changed().",
        "p/Callbacks#other().",
        "p/Consumer#run().",
        SEQUENCE_ELEMENTS_SYMBOL,
    ];
    let mut ids = Vec::new();
    for (index, name) in names.iter().enumerate() {
        let id = b.ensure_global_symbol(name, context).unwrap();
        ids.push(id);
        if index < 5 {
            let row = &mut b.facts.symbols[id.index()];
            row.file = FileId(0);
            row.flags = SYMBOL_DEFINED;
            row.kind = if index < 2 { 13 } else { 3 };
        }
    }
    let mut add =
        |symbol: SymbolId, mut ops: Vec<OperationRecord>, operands: &[u32], flags: u32| {
            let body = BodyId(b.facts.bodies.len() as u32);
            let start = b.facts.operations.len() as u32;
            let base = b.facts.operands.len() as u32;
            b.facts
                .operands
                .extend(operands.iter().copied().map(ValueId));
            for row in &mut ops {
                row.body = body;
                row.arguments.start += base;
            }
            b.facts.bodies.push(BodyRecord {
                symbol,
                file: FileId(0),
                span: Span::default(),
                name_span: Span::default(),
                operations: IdRange {
                    start,
                    len: ops.len() as u32,
                },
                parameters: IdRange::default(),
                body_hash: ContentHash([body.0 as u8 + 1; 32]),
                flags: BODY_BINARY_RECIPE | flags,
            });
            b.facts.operations.extend(ops);
        };
    let n = u32::MAX;
    add(
        ids[0],
        vec![
            op(Opcode::BindCallback, ids[2], 1, 0, IdRange::default()),
            op(Opcode::BindCallback, ids[3], 2, 0, IdRange::default()),
            op(
                Opcode::PackSequence,
                ids[5],
                3,
                n,
                IdRange { start: 0, len: 2 },
            ),
            op(Opcode::Call, ids[4], 4, 0, IdRange { start: 2, len: 1 }),
        ],
        &[1, 2, 3],
        BODY_INITIALIZER,
    );
    add(
        ids[1],
        vec![
            op(Opcode::BindCallback, ids[2], 1, 0, IdRange::default()),
            op(
                Opcode::PackSequence,
                ids[5],
                2,
                n,
                IdRange { start: 0, len: 1 },
            ),
            op(Opcode::Return, SymbolId::NONE, n, 2, IdRange::default()),
        ],
        &[1],
        BODY_INITIALIZER,
    );
    for symbol in &ids[2..4] {
        add(
            *symbol,
            vec![
                op(Opcode::Constant, SymbolId::NONE, 1, n, IdRange::default()),
                op(Opcode::Return, SymbolId::NONE, n, 1, IdRange::default()),
            ],
            &[],
            BODY_DEFERRED,
        );
    }
    add(
        ids[4],
        vec![
            op(Opcode::Parameter, SymbolId::NONE, 1, n, IdRange::default()),
            op(
                Opcode::ReadElements,
                SymbolId::NONE,
                2,
                1,
                IdRange::default(),
            ),
            op(
                Opcode::InvokeCallback,
                SymbolId::NONE,
                3,
                2,
                IdRange::default(),
            ),
        ],
        &[],
        0,
    );
    let parameters = IdRange {
        start: b.facts.operands.len() as u32,
        len: 1,
    };
    b.facts.operands.push(ValueId(1));
    b.facts.bodies.last_mut().unwrap().parameters = parameters;
    for (symbol, name) in [(ids[0], "Active"), (ids[1], "Dormant")] {
        let name = b.intern(name).unwrap();
        b.facts.suites.push(SuiteRecord {
            name,
            symbol,
            file: FileId(0),
            flags: 0,
        });
    }
    let mut facts = b.finish().unwrap();
    facts.identity = ContentHash([9; 32]);
    let graph = selector_graph_build::build(
        &facts,
        &selector_graph_build::BuildOptions {
            include_models: false,
            ..Default::default()
        },
    )
    .unwrap();
    let roots = [
        ExecutionRoot {
            node: graph.node_for_symbol(ids[0]).unwrap(),
            receiver: ids[0],
        },
        ExecutionRoot {
            node: graph.node_for_symbol(ids[1]).unwrap(),
            receiver: ids[1],
        },
    ];
    let seed = graph.node_for_symbol(ids[2]).unwrap();
    (facts, graph, roots, seed)
}
fn options(roots: &[ExecutionRoot]) -> SolveOptions {
    SolveOptions {
        workers: 1,
        retain_context_evidence: true,
        execution_roots: Some(Arc::from(roots)),
        ..Default::default()
    }
}

#[test]
fn carrier_keeps_callback_payloads_and_does_not_activate_dormant_elements() {
    let (facts, graph, roots, seed) = fixture();
    let options = options(&roots);
    let mut session = QuerySession::new(&facts, &graph, &options).unwrap();
    session.execute(&roots).unwrap();
    let result = session.analyze(&[seed]).unwrap();
    assert!(result.contains(roots[0].node));
    assert!(!result.contains(roots[1].node));
    assert!(result.evidence.atoms.iter().any(|atom| atom.kind == 4));
    assert_eq!(result.evidence.requested_roots.len(), 2);
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("facts.bin");
    selector_facts::codec::write(&path, &facts).unwrap();
    assert!(
        selector_facts::codec::read(&path)
            .unwrap()
            .operations
            .iter()
            .any(|op| op.opcode == Opcode::PackSequence)
    );
    let snapshots = selector_report::ReportSnapshots {
        base_facts: &facts,
        base_graph: &graph,
        head_facts: &facts,
        head_graph: &graph,
    };
    let mut selected = selector_select::select(
        &facts,
        &graph,
        &facts,
        &graph,
        selector_select::ChangeSeeds {
            head: vec![seed],
            ..Default::default()
        },
        None,
        result,
    )
    .unwrap();
    let mut json = Vec::new();
    selector_report::write_json(&mut json, &snapshots, &selected).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
    let carrier = json["head"]["evidence"]["atoms"]
        .as_array()
        .unwrap()
        .iter()
        .find(|a| a["kind"] == 4)
        .unwrap();
    assert_eq!(carrier["carrier"], "sequence_elements");
    assert_eq!(carrier["identity"], "pack_site_and_receiver_root");
    selected
        .head
        .evidence
        .atoms
        .iter_mut()
        .find(|a| a.kind == 4)
        .unwrap()
        .site = OperationId::NONE;
    assert!(selector_report::write_json(&mut Vec::new(), &snapshots, &selected).is_err());
}

#[test]
fn carrier_dependencies_survive_completed_cache_checkpoint_and_sealed_replay() {
    let (facts, graph, roots, seed) = fixture();
    let options = options(&roots);
    let temp = tempfile::tempdir().unwrap();
    let producer = ContentHash([42; 32]);
    let runtime =
        SolverRuntime::with_cache_directory(&options, &temp.path().join("cache"), producer)
            .unwrap();
    let mut cold = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
    cold.execute(&roots).unwrap();
    let original = cold.analyze(&[seed]).unwrap();
    cold.persist_completed().unwrap();
    let checkpoint = temp.path().join("checkpoint.bin");
    cold.save_checkpoint(&checkpoint, producer).unwrap();
    let replay_dir = temp.path().join("replay");
    cold.export_replay(roots[0].node, None, &replay_dir, &Default::default())
        .unwrap();
    assert!(
        selector_solve::replay::ReplayBundle::read(&replay_dir, &Default::default())
            .unwrap()
            .compare(&Default::default())
            .unwrap()
            .equal
    );
    let restored_runtime = SolverRuntime::new(&options).unwrap();
    let mut restored = QuerySession::from_checkpoint(
        &facts,
        &graph,
        &options,
        &restored_runtime,
        &checkpoint,
        producer,
    )
    .unwrap();
    let result = restored.analyze(&[seed]).unwrap();
    assert_eq!(result.affected, original.affected);
    assert_eq!(result.evidence.atoms, original.evidence.atoms);
    let runtime =
        SolverRuntime::with_cache_directory(&options, &temp.path().join("cache"), producer)
            .unwrap();
    let mut warm = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
    warm.execute(&roots).unwrap();
    let result = warm.analyze(&[seed]).unwrap();
    assert_eq!(result.affected, original.affected);
    assert_eq!(result.evidence.atoms, original.evidence.atoms);
    assert_eq!(warm.work_counters().operations, 0);
}

#[test]
fn malformed_pack_tag_is_rejected_and_container_is_never_a_concrete_object() {
    let (mut facts, graph, roots, seed) = fixture();
    let pack = facts
        .operations
        .iter_mut()
        .find(|op| op.opcode == Opcode::PackSequence)
        .unwrap();
    pack.target = graph.nodes[seed.index()].symbol;
    assert!(facts.validate().is_err());
    let (facts, graph, _, _) = fixture();
    let mut session = QuerySession::new(&facts, &graph, &options(&roots)).unwrap();
    session.execute(&roots).unwrap();
    let result = session.analyze(&[]).unwrap();
    for atom in result.evidence.atoms.iter().filter(|atom| atom.kind == 4) {
        assert_eq!(facts.symbol_name(atom.symbol), SEQUENCE_ELEMENTS_SYMBOL);
        assert_eq!(
            facts.operations[atom.site.index()].opcode,
            Opcode::PackSequence
        );
    }
}

#[test]
fn noncarrier_element_read_is_scoped_unknown_and_never_invents_callback_proof() {
    let (mut facts, _, roots, seed) = fixture();
    facts
        .operations
        .iter_mut()
        .find(|op| op.opcode == Opcode::ReadElements)
        .unwrap()
        .a = ValueId(0);
    facts.identity = ContentHash([10; 32]);
    let graph = selector_graph_build::build(
        &facts,
        &selector_graph_build::BuildOptions {
            include_models: false,
            ..Default::default()
        },
    )
    .unwrap();
    let mut session = QuerySession::new(&facts, &graph, &options(&roots)).unwrap();
    session.execute(&roots).unwrap();
    let result = session.analyze(&[seed]).unwrap();
    assert!(result.guarded_roots.contains(&roots[0].node));
    assert!(!result.contains(roots[0].node));
    assert!(!result.guarded_roots.contains(&roots[1].node));
    assert!(
        result
            .evidence
            .guard_causes
            .iter()
            .any(|cause| cause.root == roots[0].node
                && cause.runtime.is_some_and(
                    |site| site.reason == selector_issue::RuntimeIssueReason::UnknownFieldValue
                ))
    );
}

#[test]
fn ordinary_field_access_on_a_carrier_is_an_explicit_scoped_boundary() {
    for opcode in [Opcode::LoadField, Opcode::StoreField] {
        let (mut facts, _, _, _) = fixture();
        let consumer = facts.find_symbol("p/Consumer#run().").unwrap();
        let elements = facts.find_symbol(SEQUENCE_ELEMENTS_SYMBOL).unwrap();
        let body = facts
            .bodies
            .iter()
            .find(|body| body.symbol == consumer)
            .unwrap();
        let start = body.operations.start as usize;
        facts.operations[start + 1].opcode = opcode;
        facts.operations[start + 1].target = elements;
        if opcode == Opcode::StoreField {
            facts.operations[start + 1].b = ValueId(1);
            facts.operations[start + 1].dest = ValueId::NONE;
        }
        facts.operations[start + 2].opcode = Opcode::Constant;
        facts.operations[start + 2].a = ValueId::NONE;
        facts.validate().unwrap();
        let graph = selector_graph_build::build(
            &facts,
            &selector_graph_build::BuildOptions {
                include_models: false,
                ..Default::default()
            },
        )
        .unwrap();
        let active = graph
            .node_for_symbol(facts.find_symbol("p/Active#").unwrap())
            .unwrap();
        let dormant = graph
            .node_for_symbol(facts.find_symbol("p/Dormant#").unwrap())
            .unwrap();
        let roots = [
            ExecutionRoot {
                node: active,
                receiver: facts.find_symbol("p/Active#").unwrap(),
            },
            ExecutionRoot {
                node: dormant,
                receiver: facts.find_symbol("p/Dormant#").unwrap(),
            },
        ];
        let solve = options(&roots);
        let mut session = QuerySession::new(&facts, &graph, &solve).unwrap();
        session.execute(&roots).unwrap();
        let result = session.analyze(&[]).unwrap();
        assert!(result.guarded_roots.contains(&active), "{opcode:?}");
        assert!(!result.guarded_roots.contains(&dormant), "{opcode:?}");
        assert!(
            session
                .first_runtime_issue_sites()
                .any(
                    |(_, _, site)| site.operation == OperationId((start + 1) as u32)
                        && site.reason
                            == if opcode == Opcode::LoadField {
                                selector_issue::RuntimeIssueReason::UnknownFieldValue
                            } else {
                                selector_issue::RuntimeIssueReason::UnknownOperation
                            }
                )
        );
    }
}

#[test]
fn admitted_native_element_view_adds_callback_flow_without_dropping_native_effects_or_unknowns() {
    fn symbol(facts: &mut FactSnapshot, name: &str) -> SymbolId {
        let text = StrId(facts.strings.entries.len() as u32);
        facts.strings.entries.push(TextRange {
            start: facts.strings.bytes.len() as u64,
            len: name.len() as u32,
        });
        facts.strings.bytes.extend_from_slice(name.as_bytes());
        let id = SymbolId(facts.symbols.len() as u32);
        facts.symbols.push(SymbolRecord {
            name: text,
            display: text,
            owner: SymbolId::NONE,
            file: FileId(0),
            context: facts.files[0].context,
            kind: 3,
            properties: 0,
            signature: StrId::NONE,
            span: Span::default(),
            flags: SYMBOL_DEFINED,
        });
        id
    }
    for certified in [false, true] {
        let (mut facts, _, _, _) = fixture();
        let native = symbol(&mut facts, "scala/collection/SeqOps#apply().");
        let effect = symbol(&mut facts, "p/NativeEffect#called().");
        let consumer = facts.find_symbol("p/Consumer#run().").unwrap();
        let index = facts
            .bodies
            .iter()
            .position(|body| body.symbol == consumer)
            .unwrap();
        let consumer_body = BodyId(index as u32);
        let start = facts.bodies[index].operations.start as usize;
        let invoke = facts.operations.pop().unwrap();
        let _read = facts.operations.pop().unwrap();
        // A real index operand has no callback/alias information. Element view
        // conservatively unions all packed elements, without index precision.
        let mut constant = op(
            Opcode::Constant,
            SymbolId::NONE,
            4,
            u32::MAX,
            IdRange::default(),
        );
        constant.body = consumer_body;
        facts.operations.push(constant);
        let arguments = IdRange {
            start: facts.operands.len() as u32,
            len: 1,
        };
        facts.operands.push(ValueId(4));
        let mut call = op(Opcode::Call, native, 2, 1, arguments);
        call.body = consumer_body;
        if certified {
            call.flags = OP_SEQUENCE_ELEMENT_VIEW;
        }
        facts.operations.extend([call, invoke]);
        facts.bodies[index].operations.len = 4;
        let native_body = BodyId(facts.bodies.len() as u32);
        let native_start = facts.operations.len() as u32;
        let parameters = IdRange {
            start: facts.operands.len() as u32,
            len: 1,
        };
        facts.operands.push(ValueId(1));
        let mut native_ops = [
            op(
                Opcode::Parameter,
                SymbolId::NONE,
                1,
                u32::MAX,
                IdRange::default(),
            ),
            op(Opcode::Call, effect, 2, 0, IdRange::default()),
            op(
                Opcode::Unknown,
                SymbolId::NONE,
                3,
                u32::MAX,
                IdRange::default(),
            ),
            op(
                Opcode::Return,
                SymbolId::NONE,
                u32::MAX,
                3,
                IdRange::default(),
            ),
        ];
        for row in &mut native_ops {
            row.body = native_body;
        }
        facts.operations.extend(native_ops);
        facts.bodies.push(BodyRecord {
            symbol: native,
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange {
                start: native_start,
                len: 4,
            },
            parameters,
            body_hash: ContentHash([23; 32]),
            flags: BODY_BINARY_RECIPE,
        });
        let effect_body = BodyId(facts.bodies.len() as u32);
        facts.bodies.push(BodyRecord {
            symbol: effect,
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange {
                start: facts.operations.len() as u32,
                len: 0,
            },
            parameters: IdRange::default(),
            body_hash: ContentHash([24; 32]),
            flags: BODY_BINARY_RECIPE,
        });
        assert_eq!(effect_body.index(), facts.bodies.len() - 1);
        facts.validate().unwrap();
        if certified {
            let original = facts.operations[start + 2];
            for control in 0..6 {
                facts.operations[start + 2] = original;
                let row = &mut facts.operations[start + 2];
                match control {
                    0 => row.opcode = Opcode::ReadElements,
                    1 => row.target = effect,
                    2 => row.a = ValueId::NONE,
                    3 => row.dest = ValueId::NONE,
                    4 => row.arguments.len = 0,
                    5 => row.flags |= OP_SYNTHETIC_PARAMETER_APPLY,
                    _ => unreachable!(),
                }
                assert!(
                    facts.validate().is_err(),
                    "malformed view control {control}"
                );
            }
            facts.operations[start + 2] = original;
        }
        let graph = selector_graph_build::build(
            &facts,
            &selector_graph_build::BuildOptions {
                include_models: false,
                ..Default::default()
            },
        )
        .unwrap();
        let active = facts.find_symbol("p/Active#").unwrap();
        let dormant = facts.find_symbol("p/Dormant#").unwrap();
        let roots = [
            ExecutionRoot {
                node: graph.node_for_symbol(active).unwrap(),
                receiver: active,
            },
            ExecutionRoot {
                node: graph.node_for_symbol(dormant).unwrap(),
                receiver: dormant,
            },
        ];
        let solve = options(&roots);
        let mut session = QuerySession::new(&facts, &graph, &solve).unwrap();
        session.execute(&roots).unwrap();
        let changed = graph
            .node_for_symbol(facts.find_symbol("p/Callbacks#changed().").unwrap())
            .unwrap();
        let callback = session.analyze(&[changed]).unwrap();
        assert_eq!(
            callback.contains(roots[0].node),
            certified,
            "only certified carrier read grants callback evidence"
        );
        assert!(!callback.contains(roots[1].node));
        assert!(
            callback.guarded_roots.contains(&roots[0].node),
            "native unknown remains"
        );
        let native_effect = session
            .analyze(&[graph.node_for_symbol(effect).unwrap()])
            .unwrap();
        assert!(
            native_effect.contains(roots[0].node),
            "original native call effect survives"
        );
        assert!(native_effect.guarded_roots.contains(&roots[0].node));
        assert!(!native_effect.guarded_roots.contains(&roots[1].node));
        if certified {
            assert!(
                session
                    .first_runtime_issue_sites()
                    .any(
                        |(_, node, site)| node == graph.node_for_symbol(consumer).unwrap()
                            && site.operation == OperationId((start + 2) as u32)
                    )
            );
        }
    }
}
