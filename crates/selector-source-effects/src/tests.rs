use crate::*;
use selector_effects as e;
use selector_facts::*;
use selector_graph::*;
use selector_types::*;

struct Fixture {
    builder: FactBuilder,
    graph: ProgramGraph,
    file: FileId,
    root: SymbolId,
    callback: SymbolId,
    field: SymbolId,
}
impl Fixture {
    fn new() -> Self {
        let mut b = FactBuilder::new();
        let path = b.intern("Source.scala").unwrap();
        let source = b.intern("abcdefghijklmnopqrstuvwxyz").unwrap();
        let context = b.intern("compiler:source").unwrap();
        b.facts.identity = ContentHash([1; 32]);
        b.facts.files.push(FileRecord {
            path,
            source,
            revision: StrId::NONE,
            context,
            source_hash: ContentHash([2; 32]),
            flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
        });
        let file = FileId(0);
        let root = b.ensure_symbol("p/Source#run().", file).unwrap();
        let callback = b.ensure_symbol("p/Source#callback().", file).unwrap();
        let field = b.ensure_symbol("p/Source#value.", file).unwrap();
        for id in [root, callback, field] {
            let r = &mut b.facts.symbols[id.index()];
            r.file = file;
            r.flags = SYMBOL_DEFINED;
            r.kind = 3;
        }
        let mut graph = ProgramGraph {
            identity: ContentHash([3; 32]),
            facts_identity: b.facts.identity,
            ..Default::default()
        };
        for id in [root, callback, field] {
            graph.nodes.push(NodeRecord {
                symbol: id,
                file,
                body: BodyId::NONE,
                flags: 0,
            });
            graph.symbol_nodes.push(NodeId(id.0));
        }
        Self {
            builder: b,
            graph,
            file,
            root,
            callback,
            field,
        }
    }
    fn body(&mut self, symbol: SymbolId, mut ops: Vec<OperationRecord>, flags: u32) {
        let body = BodyId(self.builder.facts.bodies.len() as u32);
        let start = self.builder.facts.operations.len() as u32;
        let pstart = self.builder.facts.operands.len() as u32;
        for op in &ops {
            if op.opcode == Opcode::Parameter {
                self.builder.facts.operands.push(op.dest);
            }
        }
        let plen = self.builder.facts.operands.len() as u32 - pstart;
        for op in &mut ops {
            op.body = body;
        }
        let len = ops.len() as u32;
        self.builder.facts.operations.extend(ops);
        self.builder.facts.bodies.push(BodyRecord {
            symbol,
            file: self.file,
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange { start, len },
            parameters: IdRange {
                start: pstart,
                len: plen,
            },
            body_hash: ContentHash([5; 32]),
            flags,
        });
        self.graph.nodes[symbol.index()].body = body;
    }
    fn ready(mut self) -> (FactSnapshot, ProgramGraph) {
        self.graph.index().unwrap();
        (self.builder.finish().unwrap(), self.graph)
    }
}
fn op(code: Opcode, target: SymbolId, dest: u32, a: u32, b: u32) -> OperationRecord {
    OperationRecord {
        body: BodyId::NONE,
        opcode: code,
        target,
        dest: ValueId(dest),
        a: ValueId(a),
        b: ValueId(b),
        arguments: IdRange::default(),
        span: Span::default(),
        flags: 0,
    }
}
fn project(facts: &FactSnapshot, graph: &ProgramGraph) -> SourceProjection {
    let index = SourceIndex::new(facts, graph, &IndexLimits::default()).unwrap();
    project_source(
        &index,
        &FactMembers {
            symbols: facts.symbols.len() as u32,
        },
        0,
        1,
        ProjectionLimits::default(),
    )
    .unwrap()
}

#[test]
fn empty_missing_native_and_orphan_recipes_stay_distinct() {
    let mut f = Fixture::new();
    f.body(
        f.root,
        vec![op(
            Opcode::Return,
            SymbolId::NONE,
            u32::MAX,
            u32::MAX,
            u32::MAX,
        )],
        0,
    );
    let (facts, graph) = f.ready();
    let out = project(&facts, &graph);
    assert!(out.data.methods[0].top.is_empty());
    assert_eq!(out.data.methods[1].top, e::TopMask::ALL);
    assert_eq!(out.data.methods[2].top, e::TopMask::ALL);
    assert_eq!(
        out.pending
            .iter()
            .filter(|p| p.kind == PendingKind::MissingRecipe)
            .count(),
        2
    );
    let index = SourceIndex::new(&facts, &graph, &IndexLimits::default()).unwrap();
    assert!(index.body(NodeId::NONE).is_err());
    assert!(index.operations(NodeId::NONE).is_err());
    let mut graph = graph;
    graph.nodes[0].body = BodyId::NONE;
    assert!(SourceIndex::new(&facts, &graph, &IndexLimits::default()).is_err());
}
#[test]
fn tuple_signature_and_input_unknowns_never_become_data_only() {
    let mut f = Fixture::new();
    f.body(
        f.root,
        vec![op(Opcode::Unknown, SymbolId::NONE, 1, u32::MAX, u32::MAX)],
        0,
    );
    f.builder
        .issue(
            IssueKind::UnknownExecution,
            f.file,
            f.root,
            "unsupported_result_expression:Term.Tuple",
        )
        .unwrap();
    f.builder
        .issue(
            IssueKind::UnknownExecution,
            f.file,
            f.root,
            "compiler-selected method has no authoritative source argument signature",
        )
        .unwrap();
    let (mut facts, graph) = f.ready();
    let index = SourceIndex::new(&facts, &graph, &IndexLimits::default()).unwrap();
    assert_eq!(
        index
            .guards
            .iter()
            .filter(|g| g.node == NodeId(0) && g.execution)
            .count(),
        3
    );
    let out = project(&facts, &graph);
    assert_eq!(out.data.methods[0].top, e::TopMask::ALL);
    assert!(out.compiled_coverage_unadmitted);
    facts.issues.clear();
    facts.operations[0].opcode = Opcode::Constant;
    facts.files[0].flags = SOURCE_VERIFIED;
    assert_eq!(project(&facts, &graph).data.methods[0].top, e::TopMask::ALL);
}
#[test]
fn metadata_diagnostics_remain_independent_from_runtime_guards() {
    let mut f = Fixture::new();
    f.body(f.root, vec![], 0);
    let native_path = f.builder.intern("lib.jar!/p/Header.class").unwrap();
    let context = f.builder.facts.files[0].context;
    f.builder.facts.files.push(FileRecord {
        path: native_path,
        source: StrId::NONE,
        revision: StrId::NONE,
        context,
        source_hash: ContentHash([9; 32]),
        flags: FILE_BINARY_SOURCE,
    });
    f.builder
        .issue(
            IssueKind::IncompleteHierarchy,
            FileId(1),
            f.root,
            "missing parent header",
        )
        .unwrap();
    let (facts, mut graph) = f.ready();
    let index = SourceIndex::new(&facts, &graph, &IndexLimits::default()).unwrap();
    assert!(!index.guards[0].execution);
    assert!(project(&facts, &graph).data.methods[0].top.is_empty());
    graph.issues.push(GraphIssue {
        kind: IssueKind::UnknownExecution,
        node: NodeId(0),
        file: FileId(0),
        symbol: SymbolId(0),
        detail: StrId::NONE,
    });
    assert_eq!(project(&facts, &graph).data.methods[0].top, e::TopMask::ALL);
}
#[test]
fn dormant_binding_is_code_observation_not_eager_execution() {
    let mut f = Fixture::new();
    f.body(
        f.root,
        vec![
            op(Opcode::BindCallback, f.callback, 1, 0, u32::MAX),
            op(Opcode::Return, SymbolId::NONE, u32::MAX, u32::MAX, u32::MAX),
        ],
        0,
    );
    f.body(
        f.callback,
        vec![op(Opcode::Unknown, SymbolId::NONE, 1, u32::MAX, u32::MAX)],
        BODY_DEFERRED,
    );
    let (facts, graph) = f.ready();
    let out = project(&facts, &graph);
    assert!(out.data.methods[0].top.is_empty());
    assert_eq!(out.data.methods[0].calls.len, 0);
    assert_eq!(out.data.methods[0].code_observations.len, 1);
    assert_eq!(out.closures.len(), 1);
    assert_eq!(out.data.methods[1].top, e::TopMask::ALL);
}
#[test]
fn invocation_and_escaping_closure_keep_target_and_capture_obligations() {
    let mut f = Fixture::new();
    f.body(
        f.root,
        vec![
            op(Opcode::BindCallback, f.callback, 1, 0, u32::MAX),
            op(Opcode::InvokeCallback, SymbolId::NONE, 2, 1, u32::MAX),
            op(Opcode::Return, SymbolId::NONE, u32::MAX, 1, u32::MAX),
        ],
        0,
    );
    f.body(f.callback, vec![], BODY_DEFERRED);
    let (facts, graph) = f.ready();
    let out = project(&facts, &graph);
    let row = out.data.methods[0];
    assert_eq!(row.calls.len, 1);
    assert_eq!(
        out.data.calls[row.calls.start as usize].kind,
        e::CallKind::Callback
    );
    assert_eq!(
        out.data.calls[row.calls.start as usize].target,
        e::CallTarget::Callable {
            value: e::ValueRef::local(1),
            sam: e::NONE
        }
    );
    assert!(row.top.contains(e::Channel::Escapes));
    assert!(row.top.contains(e::Channel::Flows));
    assert!(
        out.pending
            .iter()
            .any(|p| p.kind == PendingKind::CaptureEscape)
    );
}
struct Absent;
impl MemberKeys for Absent {
    fn count(&self) -> u32 {
        0
    }
    fn field(&self, _: SymbolId, _: bool) -> Option<MemberBinding> {
        None
    }
}
#[test]
fn unresolved_store_keeps_capture_escape_and_overwritten_load_kills_old_binding() {
    let mut f = Fixture::new();
    f.body(
        f.root,
        vec![
            op(Opcode::BindCallback, f.callback, 1, 0, u32::MAX),
            op(Opcode::StoreField, f.field, u32::MAX, 0, 1),
            op(Opcode::LoadField, f.field, 1, 0, u32::MAX),
            op(Opcode::InvokeCallback, SymbolId::NONE, 2, 1, u32::MAX),
        ],
        0,
    );
    f.body(f.callback, vec![], BODY_DEFERRED);
    let (facts, graph) = f.ready();
    let idx = SourceIndex::new(&facts, &graph, &IndexLimits::default()).unwrap();
    let out = project_source(&idx, &Absent, 0, 1, ProjectionLimits::default()).unwrap();
    let row = out.data.methods[0];
    assert_eq!(row.calls.len, 1);
    assert_eq!(
        out.data.calls[row.calls.start as usize].target,
        e::CallTarget::Callable {
            value: e::ValueRef::UNKNOWN,
            sam: e::NONE
        }
    );
    assert!(row.top.contains(e::Channel::Calls));
    assert!(row.top.contains(e::Channel::Writes));
    assert!(row.top.contains(e::Channel::Escapes));
    assert!(row.top.contains(e::Channel::Flows));
    assert!(
        out.data
            .escapes
            .iter()
            .any(|e| e.sink == e::EscapeSink::Unknown)
    );
    assert!(out.pending.iter().any(|p| p.kind == PendingKind::Callback));
}
#[test]
fn finite_source_member_keys_do_not_claim_native_alias_canonicality() {
    let mut f = Fixture::new();
    f.body(
        f.root,
        vec![
            op(Opcode::Parameter, SymbolId::NONE, 1, u32::MAX, u32::MAX),
            op(Opcode::StoreField, f.field, u32::MAX, 0, 1),
            op(Opcode::LoadField, f.field, 2, 0, u32::MAX),
        ],
        0,
    );
    let (facts, graph) = f.ready();
    let out = project(&facts, &graph);
    let row = out.data.methods[0];
    assert_eq!(row.reads.len, 1);
    assert_eq!(row.writes.len, 1);
    assert_eq!(out.data.writes[0].base, e::Origin::RECEIVER);
    assert_eq!(out.data.escapes[0].origin, e::Origin::argument(0));
    assert!(row.top.contains(e::Channel::Reads));
    assert!(row.top.contains(e::Channel::Writes));
    assert!(row.top.contains(e::Channel::Synchronizes));
}
#[test]
fn preflight_rejects_small_budgets_before_output_and_wrong_worlds() {
    let mut f = Fixture::new();
    f.body(
        f.root,
        vec![op(Opcode::Constant, SymbolId::NONE, 20, u32::MAX, u32::MAX)],
        0,
    );
    let (facts, mut graph) = f.ready();
    let idx = SourceIndex::new(&facts, &graph, &IndexLimits::default()).unwrap();
    assert!(
        project_source(
            &idx,
            &FactMembers { symbols: 3 },
            0,
            1,
            ProjectionLimits {
                max_value_ids: 2,
                ..Default::default()
            }
        )
        .is_err()
    );
    assert!(
        project_source(
            &idx,
            &FactMembers { symbols: 3 },
            0,
            1,
            ProjectionLimits {
                max_bytes: 1,
                ..Default::default()
            }
        )
        .is_err()
    );
    assert!(
        SourceIndex::new(
            &facts,
            &graph,
            &IndexLimits {
                max_bytes: 1,
                ..Default::default()
            }
        )
        .is_err()
    );
    graph.facts_identity = ContentHash([9; 32]);
    assert!(SourceIndex::new(&facts, &graph, &IndexLimits::default()).is_err());
}

#[test]
fn lifecycle_edge_without_actuals_cannot_close_parameterized_target() {
    let mut f = Fixture::new();
    f.body(f.root, vec![], 0);
    f.body(
        f.callback,
        vec![op(Opcode::Parameter, SymbolId::NONE, 1, u32::MAX, u32::MAX)],
        0,
    );
    f.graph.edges.push(EdgeRecord {
        source: NodeId(0),
        target: NodeId(1),
        kind: EdgeKind::Fixture,
        occurrence: OccurrenceId::NONE,
        operation: OperationId::NONE,
        receiver: SymbolId::NONE,
        flags: 0,
    });
    let (facts, graph) = f.ready();
    let out = project(&facts, &graph);
    assert_eq!(out.data.methods[0].calls.len, 1);
    assert_eq!(out.data.methods[0].top, e::TopMask::ALL);
    assert!(out.pending.iter().any(|p| p.caller == e::MethodId(0)
        && p.operation.is_none()
        && p.kind == PendingKind::Target));
}

#[test]
fn constructor_actuals_are_not_duplicated_as_a_zero_argument_class_phase() {
    let mut f = Fixture::new();
    f.builder.facts.symbols[f.callback.index()].kind = 21;
    f.builder.facts.symbols[f.callback.index()].owner = f.field;
    f.builder.facts.symbols[f.field.index()].kind = 13;
    f.builder.facts.operands.push(ValueId(1));
    let mut construct = op(Opcode::Allocate, f.callback, 2, u32::MAX, u32::MAX);
    construct.arguments = IdRange { start: 0, len: 1 };
    f.body(
        f.root,
        vec![
            op(Opcode::Parameter, SymbolId::NONE, 1, u32::MAX, u32::MAX),
            construct,
        ],
        0,
    );
    f.body(
        f.callback,
        vec![op(Opcode::Parameter, SymbolId::NONE, 1, u32::MAX, u32::MAX)],
        BODY_INITIALIZER,
    );
    let (facts, graph) = f.ready();
    let out = project(&facts, &graph);
    let row = out.data.methods[0];
    assert_eq!(row.calls.len, 1);
    assert_eq!(row.initializes.len, 0);
    assert!(row.top.contains(e::Channel::Initializes));
    let call = out.data.calls[row.calls.start as usize];
    assert_eq!(call.arguments.len, 1);
    assert_eq!(
        out.data.origins[call.arguments.start as usize],
        e::Origin::argument(0)
    );
    assert_eq!(call.receiver, e::Origin::fresh(0));
}

/// Synthetic admitted-key stand-in tests table plumbing, not a compiler/JVM SAM
/// certificate. Real consumers supply provider-bound keys through this seam.
struct UnitSam;
impl SamKeys for UnitSam {
    fn arities(&self) -> &[u32] {
        &[0]
    }
    fn creation(&self, _: SitePin, _: NodeId) -> Option<u32> {
        Some(0)
    }
    fn invocation(&self, _: SitePin) -> Option<u32> {
        Some(0)
    }
}
#[test]
fn parametric_argument_invocation_retains_callable_value_and_unadmitted_control() {
    let mut f = Fixture::new();
    f.body(
        f.root,
        vec![
            op(Opcode::Parameter, SymbolId::NONE, 1, u32::MAX, u32::MAX),
            op(Opcode::InvokeCallback, SymbolId::NONE, 2, 1, u32::MAX),
        ],
        0,
    );
    let (facts, graph) = f.ready();
    let idx = SourceIndex::new(&facts, &graph, &IndexLimits::default()).unwrap();
    let members = FactMembers {
        symbols: facts.symbols.len() as u32,
    };
    let known =
        project_source_with_sams(&idx, &members, &UnitSam, 0, 1, ProjectionLimits::default())
            .unwrap();
    let call = known.data.calls[0];
    assert_eq!(
        call.target,
        e::CallTarget::Callable {
            value: e::ValueRef::argument(0),
            sam: 0
        }
    );
    assert_eq!(call.result, 2);
    assert!(!known.data.methods[0].top.contains(e::Channel::Calls));
    let unknown = project_source(&idx, &members, 0, 1, ProjectionLimits::default()).unwrap();
    assert!(unknown.data.methods[0].top.contains(e::Channel::Calls));
    assert_eq!(
        unknown.data.calls[0].target,
        e::CallTarget::Callable {
            value: e::ValueRef::argument(0),
            sam: e::NONE
        }
    );
}
#[test]
fn returned_closure_creation_keeps_capture_values_without_eager_call() {
    let mut f = Fixture::new();
    f.builder.facts.operands.push(ValueId(1));
    let args = IdRange { start: 0, len: 1 };
    let mut bind = op(Opcode::BindCallback, f.callback, 2, 0, u32::MAX);
    bind.arguments = args;
    f.body(
        f.root,
        vec![
            op(Opcode::Parameter, SymbolId::NONE, 1, u32::MAX, u32::MAX),
            bind,
            op(Opcode::Return, SymbolId::NONE, u32::MAX, 2, u32::MAX),
        ],
        0,
    );
    let mut capture = op(Opcode::Parameter, SymbolId::NONE, 1, u32::MAX, u32::MAX);
    capture.flags = 1;
    f.body(f.callback, vec![capture], BODY_DEFERRED);
    let (facts, graph) = f.ready();
    let idx = SourceIndex::new(&facts, &graph, &IndexLimits::default()).unwrap();
    let out = project_source_with_sams(
        &idx,
        &FactMembers {
            symbols: facts.symbols.len() as u32,
        },
        &UnitSam,
        0,
        1,
        ProjectionLimits::default(),
    )
    .unwrap();
    let row = out.data.methods[0];
    assert_eq!(row.calls.len, 0);
    assert_eq!(row.creations.len, 1);
    let c = out.data.creations[row.creations.start as usize];
    assert_eq!(c.implementation, e::MethodId(1));
    assert_eq!(c.sam, 0);
    assert_eq!(
        out.data.callable_values[c.captures.start as usize],
        e::ValueRef::argument(0)
    );
    assert!(
        out.data.value_flows[row.value_flows.checked(out.data.value_flows.len()).unwrap()]
            .iter()
            .any(|f| f.kind == e::ValueFlowKind::Return && f.value == e::ValueRef::local(2))
    );
    assert_eq!(out.data.origins.len(), out.data.callable_values.len());
    assert!(row.top.contains(e::Channel::Escapes));
}
#[test]
fn ordinary_call_result_is_a_callable_cell_not_guessed_implementation() {
    let mut f = Fixture::new();
    f.body(
        f.root,
        vec![
            op(Opcode::Call, f.callback, 1, 0, u32::MAX),
            op(Opcode::InvokeCallback, SymbolId::NONE, 2, 1, u32::MAX),
        ],
        0,
    );
    f.body(f.callback, vec![], 0);
    let (facts, graph) = f.ready();
    let out = project(&facts, &graph);
    assert_eq!(out.data.calls.len(), 2);
    assert_eq!(
        out.data.calls[0].target,
        e::CallTarget::Direct(e::MethodId(1))
    );
    assert_eq!(out.data.calls[0].result, 1);
    assert_eq!(
        out.data.calls[1].target,
        e::CallTarget::Callable {
            value: e::ValueRef::local(1),
            sam: e::NONE
        }
    );
    assert!(out.data.methods[0].top.contains(e::Channel::Calls));
}

#[test]
fn cross_artifact_graph_ids_fail_checked_without_panicking() {
    for mutation in 0..5 {
        let mut f = Fixture::new();
        f.body(
            f.root,
            vec![op(
                Opcode::Return,
                SymbolId::NONE,
                u32::MAX,
                u32::MAX,
                u32::MAX,
            )],
            0,
        );
        let (facts, mut graph) = f.ready();
        match mutation {
            0 => graph.nodes[0].body = BodyId(99),
            1 => graph.nodes[0].file = FileId(99),
            2 => graph.issues.push(GraphIssue {
                kind: IssueKind::UnknownExecution,
                node: NodeId(0),
                file: FileId(99),
                symbol: SymbolId(0),
                detail: StrId(0),
            }),
            3 | 4 => {
                if mutation == 4 {
                    graph.symbol_nodes.resize(100, NodeId::NONE);
                }
                graph.edges.push(EdgeRecord {
                    source: NodeId(0),
                    target: NodeId(1),
                    kind: EdgeKind::Call,
                    occurrence: OccurrenceId::NONE,
                    operation: if mutation == 3 {
                        OperationId(99)
                    } else {
                        OperationId::NONE
                    },
                    receiver: if mutation == 4 {
                        SymbolId(99)
                    } else {
                        SymbolId::NONE
                    },
                    flags: 0,
                });
                graph.index().unwrap();
            }
            _ => unreachable!(),
        }
        graph.validate().unwrap(); // local graph geometry cannot see fact bounds
        let checked =
            std::panic::catch_unwind(|| SourceIndex::new(&facts, &graph, &IndexLimits::default()));
        assert!(
            checked.is_ok(),
            "cross-artifact mutation {mutation} panicked"
        );
        assert!(
            checked.unwrap().is_err(),
            "cross-artifact mutation {mutation} accepted"
        );
    }
}
