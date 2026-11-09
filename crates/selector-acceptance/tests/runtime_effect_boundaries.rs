//! Adverse effect-closure consumers over an explicitly normalized test program.
//! These are engine controls, not a captured CI runtime/loader closure. A TOP
//! value may be data locally while its later consumers open real effect paths.
use selector_facts::{
    BodyRecord, FactBuilder, FactSnapshot, FileRecord, OperationRecord, SuiteRecord,
};
use selector_graph::{EdgeRecord, NodeRecord, ProgramGraph};
use selector_plan::{CandidatePlan, PlanSeeds, plan};
use selector_result::{AnalysisResult, EffectClosure, SuiteDecisionStatus};
use selector_select::{ChangeSeeds, select_with_plan};
use selector_solve::{ExecutionRoot, QuerySession, SolveOptions, SolverRuntime};
use selector_types::*;

const READER: u32 = 0;
const SUBJECT: u32 = 1;
const SCALAR: u32 = 2;
const INITIALIZER: u32 = 3;
const CHANGED: u32 = 4;
const SAFE: u32 = 5;
const SHARED: u32 = 6;
const MISSING_DATA: u32 = 7;
const OWNER: u32 = 8;
const LEAF: u32 = 9;
const INSTANCE_FIELD: u32 = 10;
const CAPTURED: u32 = 11;
const OMITTED: u32 = 12;

#[derive(Clone, Copy, Debug)]
#[repr(u8)]
enum Mode {
    Discard,
    Callback,
    Virtual,
    UnknownReceiverWrite,
    UnknownMemberWrite,
    UnknownMemberWriteOnly,
    Elements,
    InitializeSideEdge,
    AllocateThenInitialize,
    CapturedEscape,
    MissingCallee,
    CompleteMarkerWithGuard,
}
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
fn edge(source: u32, target: u32, kind: EdgeKind, operation: OperationId) -> EdgeRecord {
    EdgeRecord {
        source: NodeId(source),
        target: NodeId(target),
        kind,
        operation,
        occurrence: OccurrenceId::NONE,
        receiver: if kind == EdgeKind::VirtualCall {
            SymbolId(OWNER)
        } else {
            SymbolId::NONE
        },
        flags: 0,
    }
}
fn body(
    b: &mut FactBuilder,
    graph: &mut ProgramGraph,
    node: u32,
    parameters: &[ValueId],
    rows: Vec<(OperationRecord, Vec<ValueId>)>,
) {
    let id = BodyId(b.facts.bodies.len() as u32);
    let parameter_start = b.facts.operands.len() as u32;
    b.facts.operands.extend_from_slice(parameters);
    let start = b.facts.operations.len() as u32;
    for (mut operation, arguments) in rows {
        operation.body = id;
        operation.arguments = IdRange {
            start: b.facts.operands.len() as u32,
            len: arguments.len() as u32,
        };
        b.facts.operands.extend(arguments);
        let kind = match operation.opcode {
            Opcode::Call => Some(EdgeKind::Call),
            Opcode::VirtualCall => Some(EdgeKind::VirtualCall),
            Opcode::Allocate => Some(EdgeKind::Construct),
            _ => None,
        };
        if let Some(kind) = kind.filter(|_| !operation.target.is_none()) {
            graph.edges.push(edge(
                node,
                operation.target.0,
                kind,
                OperationId(b.facts.operations.len() as u32),
            ));
        }
        b.facts.operations.push(operation);
    }
    b.facts.bodies.push(BodyRecord {
        symbol: SymbolId(node),
        file: FileId(0),
        span: Span::default(),
        name_span: Span::default(),
        operations: IdRange {
            start,
            len: b.facts.operations.len() as u32 - start,
        },
        parameters: IdRange {
            start: parameter_start,
            len: parameters.len() as u32,
        },
        // Keep this constant across controls: cache admission must inspect IR,
        // not assume a producer/model changed only when raw body bytes change.
        body_hash: ContentHash([42; 32]),
        flags: if node <= INITIALIZER {
            BODY_INITIALIZER
        } else {
            0
        },
    });
    graph.nodes[node as usize].body = id;
}
fn fixture(mode: Mode) -> Fixture {
    fixture_with_opaque_catalogue_root(mode, false)
}
fn fixture_with_opaque_catalogue_root(mode: Mode, extra_opaque: bool) -> Fixture {
    let mut b = FactBuilder::new();
    let path = b.intern("RuntimeEffectControls.scala").unwrap();
    let source = b.intern(&" ".repeat(128)).unwrap();
    b.facts.files.push(FileRecord {
        path,
        source,
        context: StrId::NONE,
        revision: StrId::NONE,
        source_hash: ContentHash([1; 32]),
        flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
    });
    b.facts.identity = ContentHash([mode as u8 + 1; 32]);
    let mut graph = ProgramGraph {
        facts_identity: b.facts.identity,
        identity: ContentHash([mode as u8 + 32 + u8::from(extra_opaque) * 16; 32]),
        ..Default::default()
    };
    for (i, name) in [
        "p/Reader#",
        "p/Subject#",
        "p/Scalar#",
        "p/Initializer#",
        "p/changed().",
        "p/safe().",
        "p/Owner#shared.",
        "p/Owner#missing.",
        "p/Owner#",
        "external/opaque().",
        "p/Owner#instance.",
        "p/captured().",
        "p/OmittedOpaque#",
    ]
    .into_iter()
    .enumerate()
    {
        let external = i == LEAF as usize && !matches!(mode, Mode::Virtual);
        let file = if external { FileId::NONE } else { FileId(0) };
        let id = b.ensure_symbol(name, file).unwrap();
        assert_eq!(id.0, i as u32);
        let symbol = &mut b.facts.symbols[i];
        symbol.flags = if external { 0 } else { SYMBOL_DEFINED };
        symbol.kind = if i <= INITIALIZER as usize || i == OWNER as usize || i == OMITTED as usize {
            13
        } else if matches!(i as u32, SHARED | MISSING_DATA | INSTANCE_FIELD) {
            7
        } else {
            3
        };
        if matches!(i as u32, SHARED | MISSING_DATA | INSTANCE_FIELD | LEAF) {
            symbol.owner = SymbolId(OWNER);
        }
        if matches!(i as u32, SHARED | MISSING_DATA | INSTANCE_FIELD) {
            symbol.properties = 1024;
        }
        graph.nodes.push(NodeRecord {
            symbol: id,
            file,
            body: BodyId::NONE,
            flags: 0,
        });
        graph.symbol_nodes.push(NodeId(i as u32));
    }
    let mut reader = vec![(
        OperationRecord {
            target: SymbolId(SHARED),
            dest: ValueId(1),
            flags: OP_STATIC_FIELD,
            ..op(Opcode::LoadField)
        },
        vec![],
    )];
    reader.push((
        OperationRecord {
            a: ValueId(1),
            ..op(if matches!(mode, Mode::CapturedEscape) {
                Opcode::InvokeCallback
            } else {
                Opcode::Return
            })
        },
        vec![],
    ));
    if matches!(mode, Mode::UnknownMemberWriteOnly) {
        reader[0].0 = OperationRecord {
            dest: ValueId(1),
            flags: OP_TRUSTED_PRIMITIVE_READ,
            ..op(Opcode::ReadElements)
        };
    }
    body(&mut b, &mut graph, READER, &[], reader);
    if matches!(mode, Mode::UnknownMemberWriteOnly) {
        let mut native_file = b.facts.files[0];
        native_file.path = b.intern("TrustedPrimitiveReader.class").unwrap();
        native_file.flags = FILE_BINARY_SOURCE;
        let file = FileId(b.facts.files.len() as u32);
        b.facts.files.push(native_file);
        let native_body = &mut b.facts.bodies[graph.nodes[READER as usize].body.index()];
        native_body.flags |= BODY_BINARY_RECIPE;
        native_body.file = file;
        b.facts.symbols[READER as usize].file = file;
        graph.nodes[READER as usize].file = file;
    }
    let mut subject = vec![
        (
            OperationRecord {
                target: SymbolId(MISSING_DATA),
                dest: ValueId(1),
                flags: OP_STATIC_FIELD,
                ..op(Opcode::LoadField)
            },
            vec![],
        ),
        (
            OperationRecord {
                target: SymbolId(SAFE),
                dest: ValueId(2),
                ..op(Opcode::BindCallback)
            },
            vec![],
        ),
        // This known callback is a potential planner frontier but closes at
        // runtime. It ensures the independent reader has real HEAP exposure.
        (
            OperationRecord {
                a: ValueId(2),
                dest: ValueId(3),
                ..op(Opcode::InvokeCallback)
            },
            vec![],
        ),
    ];
    if matches!(mode, Mode::UnknownMemberWriteOnly) {
        // Isolate the unknown store: no callback frontier can accidentally
        // supply the shared-heap protection this control is checking.
        subject.truncate(1);
    }
    match mode {
        Mode::Discard | Mode::InitializeSideEdge => (),
        Mode::Callback => subject.push((
            OperationRecord {
                a: ValueId(1),
                ..op(Opcode::InvokeCallback)
            },
            vec![],
        )),
        Mode::Virtual => subject.push((
            OperationRecord {
                target: SymbolId(LEAF),
                a: ValueId(1),
                dest: ValueId(4),
                ..op(Opcode::VirtualCall)
            },
            vec![],
        )),
        Mode::UnknownReceiverWrite => subject.push((
            OperationRecord {
                target: SymbolId(INSTANCE_FIELD),
                a: ValueId(1),
                b: ValueId(2),
                ..op(Opcode::StoreField)
            },
            vec![],
        )),
        Mode::UnknownMemberWrite | Mode::UnknownMemberWriteOnly => subject.push((
            OperationRecord {
                a: ValueId(0),
                b: ValueId(2),
                ..op(Opcode::StoreField)
            },
            vec![],
        )),
        Mode::Elements => subject.push((
            OperationRecord {
                a: ValueId(1),
                dest: ValueId(4),
                ..op(Opcode::ReadElements)
            },
            vec![],
        )),
        Mode::AllocateThenInitialize => subject.push((
            OperationRecord {
                target: SymbolId(OWNER),
                dest: ValueId(4),
                ..op(Opcode::Allocate)
            },
            vec![],
        )),
        Mode::CapturedEscape => {
            subject.push((
                OperationRecord {
                    target: SymbolId(CAPTURED),
                    dest: ValueId(4),
                    ..op(Opcode::BindCallback)
                },
                vec![ValueId(1)],
            ));
            subject.push((
                OperationRecord {
                    target: SymbolId(SHARED),
                    b: ValueId(4),
                    flags: OP_STATIC_FIELD,
                    ..op(Opcode::StoreField)
                },
                vec![],
            ));
        }
        Mode::MissingCallee => subject.push((op(Opcode::Call), vec![])),
        Mode::CompleteMarkerWithGuard => subject.push((
            OperationRecord {
                target: SymbolId(LEAF),
                ..op(Opcode::Call)
            },
            vec![],
        )),
    }
    body(&mut b, &mut graph, SUBJECT, &[], subject);
    for node in [SCALAR, CHANGED, SAFE, OWNER] {
        body(&mut b, &mut graph, node, &[], vec![]);
    }
    if matches!(mode, Mode::Virtual) {
        body(&mut b, &mut graph, LEAF, &[], vec![]);
    }
    body(
        &mut b,
        &mut graph,
        CAPTURED,
        &[ValueId(1)],
        vec![
            (
                OperationRecord {
                    dest: ValueId(1),
                    ..op(Opcode::Parameter)
                },
                vec![],
            ),
            (
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::InvokeCallback)
                },
                vec![],
            ),
        ],
    );
    body(
        &mut b,
        &mut graph,
        INITIALIZER,
        &[],
        vec![
            (
                OperationRecord {
                    target: SymbolId(SAFE),
                    dest: ValueId(1),
                    ..op(Opcode::BindCallback)
                },
                vec![],
            ),
            (
                OperationRecord {
                    target: SymbolId(SHARED),
                    b: ValueId(1),
                    flags: OP_STATIC_FIELD,
                    ..op(Opcode::StoreField)
                },
                vec![],
            ),
        ],
    );
    if matches!(mode, Mode::CompleteMarkerWithGuard) {
        // An explicit execution frontier outranks a contradictory empty-effect
        // marker; model completeness must not hide the outgoing guard.
        graph.nodes[LEAF as usize].flags |= NODE_EFFECTS_COMPLETE;
        let mut guard = edge(LEAF, CHANGED, EdgeKind::Guard, OperationId::NONE);
        guard.flags = EDGE_UNKNOWN;
        graph.edges.push(guard);
    }
    match mode {
        Mode::InitializeSideEdge => {
            graph
                .edges
                .push(edge(SUBJECT, LEAF, EdgeKind::Initialize, OperationId::NONE))
        }
        Mode::AllocateThenInitialize => {
            graph
                .edges
                .push(edge(OWNER, LEAF, EdgeKind::Initialize, OperationId::NONE))
        }
        _ => (),
    }
    for (node, name) in [
        (READER, "p.Reader"),
        (SUBJECT, "p.Subject"),
        (SCALAR, "p.Scalar"),
        (INITIALIZER, "p.Initializer"),
    ] {
        let name = b.intern(name).unwrap();
        b.facts.suites.push(SuiteRecord {
            name,
            symbol: SymbolId(node),
            file: b.facts.symbols[node as usize].file,
            flags: 0,
        });
    }
    body(
        &mut b,
        &mut graph,
        OMITTED,
        &[],
        if extra_opaque {
            vec![(
                OperationRecord {
                    target: SymbolId(LEAF),
                    ..op(Opcode::Call)
                },
                vec![],
            )]
        } else {
            vec![]
        },
    );
    if extra_opaque {
        let name = b.intern("p.OmittedOpaque").unwrap();
        b.facts.suites.push(SuiteRecord {
            name,
            symbol: SymbolId(OMITTED),
            file: FileId(0),
            flags: 0,
        });
    }
    let facts = b.finish().unwrap();
    graph.index().unwrap();
    Fixture { facts, graph }
}
fn options(f: &Fixture, workers: usize, max_contexts: usize) -> SolveOptions {
    SolveOptions {
        workers,
        max_steps: 20_000,
        max_contexts,
        memory_budget_bytes: 16 * 1024 * 1024,
        execution_roots: Some(
            f.facts
                .suites
                .iter()
                .map(|s| ExecutionRoot {
                    node: f.graph.node_for_symbol(s.symbol).unwrap(),
                    receiver: s.symbol,
                })
                .collect(),
        ),
        ..Default::default()
    }
}
fn run(
    f: &Fixture,
    workers: usize,
    max_contexts: usize,
    cache: Option<&std::path::Path>,
) -> AnalysisResult {
    let options = options(f, workers, max_contexts);
    let runtime = match cache {
        Some(path) => {
            SolverRuntime::with_cache_directory(&options, path, ContentHash([77; 32])).unwrap()
        }
        None => SolverRuntime::new(&options).unwrap(),
    };
    let mut session = QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
    session
        .execute(&[ExecutionRoot {
            node: NodeId(INITIALIZER),
            receiver: SymbolId(INITIALIZER),
        }])
        .unwrap();
    session.analyze(&[NodeId(CHANGED)]).unwrap()
}
fn candidate_plan(f: &Fixture) -> CandidatePlan {
    plan(
        &f.facts,
        &f.graph,
        PlanSeeds {
            execution: &[NodeId(CHANGED)],
            declarations: &[],
            unscoped: false,
        },
    )
    .unwrap()
}
fn selection(
    f: &Fixture,
    base: AnalysisResult,
    head: AnalysisResult,
) -> selector_result::SelectionResult {
    let plan = candidate_plan(f);
    select_with_plan(
        &f.facts,
        &f.graph,
        &f.facts,
        &f.graph,
        ChangeSeeds {
            base: vec![NodeId(CHANGED)],
            head: vec![NodeId(CHANGED)],
            ..Default::default()
        },
        Some(base),
        head,
        Some(&plan),
        &plan,
    )
    .unwrap()
}

#[test]
fn unknown_writer_alone_protects_a_trusted_primitive_reader_in_shared_mode() {
    for workers in [1, 2] {
        let f = fixture(Mode::UnknownMemberWriteOnly);
        let subject = &f.facts.bodies[f.graph.nodes[SUBJECT as usize].body.index()];
        assert!(
            !f.facts.operations[subject.operations.range()]
                .iter()
                .any(|op| op.opcode == Opcode::InvokeCallback)
        );
        let observed = run(&f, workers, 100, None);
        assert!(!observed.guarded_roots.contains(&NodeId(READER)));
        assert!(observed.guarded_roots.contains(&NodeId(SUBJECT)));
        for mode in [SuiteSemantics::SharedState, SuiteSemantics::Independent] {
            let plan = selector_plan::plan_guarded_with_semantics(
                &f.facts,
                &f.graph,
                PlanSeeds {
                    execution: &[NodeId(CHANGED)],
                    declarations: &[],
                    unscoped: false,
                },
                &[],
                mode,
            )
            .unwrap();
            assert_eq!(
                plan.shared_heap_guarded_roots().contains(&NodeId(READER)),
                mode == SuiteSemantics::SharedState
            );
            let seeds = || ChangeSeeds {
                base: vec![NodeId(CHANGED)],
                head: vec![NodeId(CHANGED)],
                ..Default::default()
            };
            let expected = if mode == SuiteSemantics::SharedState {
                SuiteDecisionStatus::Unknown
            } else {
                SuiteDecisionStatus::Excluded
            };
            let planned = select_with_plan(
                &f.facts,
                &f.graph,
                &f.facts,
                &f.graph,
                seeds(),
                Some(run(&f, workers, 100, None)),
                run(&f, workers, 100, None),
                Some(&plan),
                &plan,
            )
            .unwrap();
            let all = selector_select::select_with_semantics(
                &f.facts,
                &f.graph,
                &f.facts,
                &f.graph,
                seeds(),
                Some(run(&f, workers, 100, None)),
                run(&f, workers, 100, None),
                mode,
            )
            .unwrap();
            for selected in [planned, all] {
                assert_eq!(selected.decisions[0].status, expected);
                assert_eq!(
                    selected.decisions[0].guarded,
                    mode == SuiteSemantics::SharedState
                );
                assert_eq!(selected.decisions[1].status, SuiteDecisionStatus::Unknown);
            }
        }
    }
}

#[test]
fn locally_unknown_data_does_not_open_effects_until_a_real_consumer_uses_it() {
    for workers in [1, 2] {
        let f = fixture(Mode::Discard);
        let plan = candidate_plan(&f);
        assert!(plan.shared_heap_guarded_roots().contains(&NodeId(READER)));
        let result = run(&f, workers, 100, None);
        assert!(result.guarded_roots.contains(&NodeId(SUBJECT)));
        assert!(!result.guarded_roots.contains(&NodeId(READER)));
        assert_eq!(
            result.validate_execution_effects().unwrap(),
            EffectClosure::Closed
        );
        let selected = selection(&f, run(&f, workers, 100, None), result);
        assert_eq!(selected.decisions[0].status, SuiteDecisionStatus::Excluded);
        assert_eq!(selected.decisions[1].status, SuiteDecisionStatus::Unknown);
    }
}
#[test]
fn independent_suite_contract_excludes_only_the_unrelated_reader() {
    for workers in [1, 2] {
        for mode in [Mode::Callback, Mode::MissingCallee] {
            let f = fixture(mode);
            let plan = selector_plan::plan_guarded_with_semantics(
                &f.facts,
                &f.graph,
                PlanSeeds {
                    execution: &[NodeId(CHANGED)],
                    declarations: &[],
                    unscoped: false,
                },
                &[],
                SuiteSemantics::Independent,
            )
            .unwrap();
            let seeds = || ChangeSeeds {
                base: vec![NodeId(CHANGED)],
                head: vec![NodeId(CHANGED)],
                ..Default::default()
            };
            let head = run(&f, workers, 100, None);
            assert!(!head.guarded_roots.contains(&NodeId(READER)), "{mode:?}");
            assert!(head.guarded_roots.contains(&NodeId(SUBJECT)), "{mode:?}");
            let selected = select_with_plan(
                &f.facts,
                &f.graph,
                &f.facts,
                &f.graph,
                seeds(),
                Some(run(&f, workers, 100, None)),
                head,
                Some(&plan),
                &plan,
            )
            .unwrap();
            assert_eq!(selected.suite_semantics, SuiteSemantics::Independent);
            assert_eq!(
                selected.decisions[0].status,
                SuiteDecisionStatus::Excluded,
                "{mode:?}"
            );
            assert_eq!(
                selected.decisions[1].status,
                SuiteDecisionStatus::Unknown,
                "{mode:?}"
            );
            assert!(selected.decisions[1].guarded);
            assert!(selected.decisions[0].head_exclusion.is_some());
            let all_roots = selector_select::select_with_semantics(
                &f.facts,
                &f.graph,
                &f.facts,
                &f.graph,
                seeds(),
                Some(run(&f, workers, 100, None)),
                run(&f, workers, 100, None),
                SuiteSemantics::Independent,
            )
            .unwrap();
            assert_eq!(all_roots.suite_semantics, SuiteSemantics::Independent);
            assert_eq!(all_roots.decisions[0].status, SuiteDecisionStatus::Excluded);
            assert_eq!(all_roots.decisions[1].status, SuiteDecisionStatus::Unknown);
        }
    }
}

#[test]
fn data_first_then_dynamic_or_opaque_effect_never_grants_shared_reader_exclusion() {
    for mode in [
        Mode::Callback,
        Mode::Virtual,
        Mode::UnknownReceiverWrite,
        Mode::UnknownMemberWrite,
        Mode::Elements,
        Mode::InitializeSideEdge,
        Mode::AllocateThenInitialize,
        Mode::MissingCallee,
        Mode::CompleteMarkerWithGuard,
    ] {
        let f = fixture(mode);
        let result = run(&f, 1, 100, None);
        assert_eq!(
            result.validate_execution_effects().unwrap(),
            EffectClosure::Open,
            "{mode:?}"
        );
        let selected = selection(&f, run(&f, 1, 100, None), result);
        assert_eq!(
            selected.decisions[0].status,
            SuiteDecisionStatus::Unknown,
            "{mode:?}"
        );
    }
}
#[test]
fn top_capture_escaping_through_a_static_slot_reopens_effects_when_invoked() {
    let f = fixture(Mode::CapturedEscape);
    let result = run(&f, 2, 100, None);
    assert_eq!(
        result.validate_execution_effects().unwrap(),
        EffectClosure::Open
    );
    assert!(result.guarded_roots.contains(&NodeId(READER)));
    let selected = selection(&f, run(&f, 2, 100, None), result);
    assert_eq!(selected.decisions[0].status, SuiteDecisionStatus::Unknown);
}
#[test]
fn stopped_context_admission_never_claims_whole_universe_effect_closure() {
    let f = fixture(Mode::Discard);
    let result = run(&f, 1, 1, None);
    assert_eq!(result.completion, Completion::ResourceLimited);
    assert_ne!(
        result.validate_execution_effects().unwrap(),
        EffectClosure::Closed
    );
    assert!(result.unscoped_uncertainty);
}
#[test]
fn changed_consumer_cannot_inherit_closed_authority_from_a_completed_cache() {
    let directory = tempfile::tempdir().unwrap();
    let closed = fixture(Mode::Discard);
    for workers in [1, 2] {
        let result = run(&closed, workers, 100, Some(directory.path()));
        assert_eq!(
            result.validate_execution_effects().unwrap(),
            EffectClosure::Closed
        );
    }
    let open = fixture(Mode::Callback);
    let result = run(&open, 2, 100, Some(directory.path()));
    assert_eq!(
        result.validate_execution_effects().unwrap(),
        EffectClosure::Open
    );
    let selected = selection(&open, run(&open, 1, 100, None), result);
    assert_eq!(selected.decisions[0].status, SuiteDecisionStatus::Unknown);
}
#[test]
fn closure_tokens_reject_swapped_frontiers_and_mutated_completion() {
    let closed_fixture = fixture(Mode::Discard);
    let open_fixture = fixture(Mode::Callback);
    let mut closed = run(&closed_fixture, 1, 100, None);
    let mut open = run(&open_fixture, 1, 100, None);
    open.evidence.execution_effects = std::mem::take(&mut closed.evidence.execution_effects);
    assert!(open.validate_execution_effects().is_err());
    let mut closed = run(&closed_fixture, 1, 100, None);
    closed.evidence.requested_roots.pop();
    assert!(closed.validate_execution_effects().is_err());
    let mut closed = run(&closed_fixture, 1, 100, None);
    closed.completion = Completion::ResourceLimited;
    assert!(closed.validate_execution_effects().is_err());
}

#[test]
fn a_closed_requested_subset_cannot_certify_an_unexecuted_opaque_catalogue_root() {
    let f = fixture_with_opaque_catalogue_root(Mode::Discard, true);
    let full = run(&f, 1, 100, None);
    assert_eq!(
        full.validate_execution_effects().unwrap(),
        EffectClosure::Open
    );
    let subset = || {
        let mut opts = options(&f, 1, 100);
        opts.execution_roots = Some(
            opts.execution_roots
                .as_ref()
                .unwrap()
                .iter()
                .copied()
                .filter(|root| root.node != NodeId(OMITTED))
                .collect(),
        );
        let mut session = QuerySession::new(&f.facts, &f.graph, &opts).unwrap();
        session
            .execute(&[ExecutionRoot {
                node: NodeId(INITIALIZER),
                receiver: SymbolId(INITIALIZER),
            }])
            .unwrap();
        session.analyze(&[NodeId(CHANGED)]).unwrap()
    };
    let result = subset();
    assert!(
        !result
            .evidence
            .requested_roots
            .iter()
            .any(|r| r.node == NodeId(OMITTED))
    );
    // Strict rejection and conservative Unknown are both sound APIs. A local
    // closure proof is never authority to ignore omitted opaque effects.
    if let Ok(selected) = selector_select::select(
        &f.facts,
        &f.graph,
        &f.facts,
        &f.graph,
        ChangeSeeds {
            base: vec![NodeId(CHANGED)],
            head: vec![NodeId(CHANGED)],
            ..Default::default()
        },
        Some(subset()),
        result,
    ) {
        assert_ne!(selected.decisions[0].status, SuiteDecisionStatus::Excluded);
        assert_ne!(selected.decisions[4].status, SuiteDecisionStatus::Excluded);
    }
}

#[test]
fn paused_contexts_acquire_only_newly_verified_effect_authority_after_resume() {
    for mode in [Mode::Discard, Mode::Callback] {
        let f = fixture(mode);
        let directory = tempfile::tempdir().unwrap();
        let checkpoint = directory.path().join("paused.bin");
        let producer = ContentHash([88; 32]);
        {
            let opts = options(&f, 1, 1);
            let mut session = QuerySession::new(&f.facts, &f.graph, &opts).unwrap();
            session
                .execute(&[ExecutionRoot {
                    node: NodeId(INITIALIZER),
                    receiver: SymbolId(INITIALIZER),
                }])
                .unwrap();
            let result = session.analyze(&[NodeId(CHANGED)]).unwrap();
            assert_eq!(result.completion, Completion::ResourceLimited);
            assert_ne!(
                result.validate_execution_effects().unwrap(),
                EffectClosure::Closed
            );
            session.save_checkpoint(&checkpoint, producer).unwrap();
        }
        let opts = options(&f, 2, 100);
        let runtime = SolverRuntime::new(&opts).unwrap();
        let mut resumed = QuerySession::from_checkpoint(
            &f.facts,
            &f.graph,
            &opts,
            &runtime,
            &checkpoint,
            producer,
        )
        .unwrap();
        resumed.resume().unwrap();
        let result = resumed.analyze(&[NodeId(CHANGED)]).unwrap();
        let expected = if matches!(mode, Mode::Discard) {
            EffectClosure::Closed
        } else {
            EffectClosure::Open
        };
        assert_eq!(
            result.validate_execution_effects().unwrap(),
            expected,
            "{mode:?}"
        );
    }
}

#[test]
fn local_transfer_replay_does_not_claim_its_opaque_callee_effects_are_closed() {
    use selector_solve::replay::{ReplayBundle, ReplayLimits, ReplayOptions};
    let f = fixture(Mode::InitializeSideEdge);
    let opts = options(&f, 1, 100);
    let mut session = QuerySession::new(&f.facts, &f.graph, &opts).unwrap();
    session
        .execute(&[ExecutionRoot {
            node: NodeId(INITIALIZER),
            receiver: SymbolId(INITIALIZER),
        }])
        .unwrap();
    let result = session.analyze(&[NodeId(CHANGED)]).unwrap();
    assert_eq!(
        result.validate_execution_effects().unwrap(),
        EffectClosure::Open
    );
    let directory = tempfile::tempdir().unwrap();
    let limits = ReplayLimits {
        max_bytes: 2 * 1024 * 1024,
        max_records: 4096,
        scratch_bytes: 2 * 1024 * 1024,
        ..Default::default()
    };
    session
        .export_replay(NodeId(SUBJECT), None, directory.path(), &limits)
        .unwrap();
    let bundle = ReplayBundle::read(directory.path(), &limits).unwrap();
    let local = bundle
        .replay(&ReplayOptions {
            scratch_bytes: limits.scratch_bytes,
            verify_expected: true,
        })
        .unwrap();
    // The local transfer emits the Initialize call, whose child is opaque. Its
    // own data-only read is locally closed; only the full fixed point may attest
    // global effects, and that full result above is Open.
    assert!(!local.effects_open);
    let json = serde_json::to_value(&local).unwrap();
    assert!(json.get("execution_effects").is_none());
}
