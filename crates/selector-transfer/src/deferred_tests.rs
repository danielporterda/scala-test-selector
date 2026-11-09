use super::*;

struct NativeSummary {
    values: ValuePool,
    returned: Value,
}
impl NativeSummary {
    fn new() -> Self {
        let mut values = ValuePool::new(16);
        let returned = values
            .singleton(Atom {
                kind: AtomKind::Object,
                site: OperationId(2),
                symbol: SymbolId(1),
                binding: 0,
            })
            .unwrap();
        Self { values, returned }
    }
}
impl World for NativeSummary {
    fn values(&self) -> &ValuePool {
        &self.values
    }
    fn summary(
        &self,
        node: NodeId,
        _: Value,
        _: &[Value],
        _: &ValuePool,
        _: &mut Vec<Value>,
    ) -> SummaryRead {
        // Possible callback activation must schedule effects without reading
        // its return as an alternative to the Future result.
        assert_eq!(node, NodeId(1));
        SummaryRead {
            context: Some(ContextId(0)),
            value: self.returned,
            version: 1,
            present: true,
        }
    }
    fn slot(&self, _: Slot) -> (Value, u64, bool) {
        panic!("no heap access")
    }
    fn capture(&self, _: u32) -> Option<(Value, &[Value], u64)> {
        panic!("local captures")
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

fn fixture(name: &str, flags: u32) -> (FactSnapshot, ProgramGraph) {
    let (mut facts, graph) = callback_model_tests::fixture_for(flags, name);
    facts.operations.push(OperationRecord {
        opcode: Opcode::Return,
        a: ValueId(3),
        ..facts.operations[0]
    });
    facts.bodies[0].operations.len = 4;
    facts.bodies[1].operations.start = 4;
    (facts, graph)
}

fn run(facts: &FactSnapshot, graph: &ProgramGraph) -> (Evaluation, Scratch, NativeSummary) {
    let types = TypeIndex::new(facts);
    let world = NativeSummary::new();
    let mut scratch = Scratch::new(16);
    let mut out = Evaluation::default();
    evaluate(
        facts,
        graph,
        &types,
        &world,
        NodeId(0),
        Value::EMPTY,
        &[Value::TOP],
        &mut scratch,
        &mut out,
    )
    .unwrap();
    (out, scratch, world)
}

#[test]
fn reached_future_map_and_flat_map_add_possible_execution_without_replacing_native_return() {
    for name in [
        "scala/concurrent/Future#map().",
        "scala/concurrent/Future#flatMap().",
    ] {
        let (facts, graph) = fixture(
            name,
            EDGE_CALLBACK_DEFERRED | encode_callback_argument(0).unwrap(),
        );
        let (out, scratch, world) = run(&facts, &graph);
        assert_eq!(
            out.first_issue,
            Some(RuntimeIssueSite {
                kind: IssueKind::UnknownExecution,
                operation: OperationId(2),
                reason: RuntimeIssueReason::IncompleteDeferredCallback,
            })
        );
        assert_eq!(out.issues, [IssueKind::UnknownExecution]);
        assert_eq!(out.calls.len(), 2);
        let native = &out.calls[0];
        assert_eq!(native.target, NodeId(1));
        assert!(native.observe_return);
        assert_eq!(native.summary, Some(ContextId(0)));
        assert_eq!(native.arguments.len, 2, "all native arguments remain");
        let callback = &out.calls[1];
        assert_eq!(callback.target, NodeId(2));
        assert_eq!(callback.kind, EdgeKind::Callback);
        assert!(!callback.observe_return);
        assert_eq!(callback.summary, None);
        assert_eq!(&out.arguments[callback.arguments.range()], &[Value::TOP]);
        assert_eq!(
            scratch.pool.members(out.value),
            world.values.members(world.returned)
        );
        assert_eq!(out.value.unknown, world.returned.unknown);
        assert_eq!(out.reads.len(), 1, "only the native return is observed");
    }
}

#[test]
fn possible_callback_keeps_lexical_captures_after_its_one_unknown_payload() {
    let (mut facts, mut graph) = fixture(
        "scala/concurrent/Future#map().",
        EDGE_CALLBACK_DEFERRED | encode_callback_argument(0).unwrap(),
    );
    facts.operations[1].arguments = IdRange { start: 0, len: 1 };
    facts.operations[1].a = ValueId(2);
    // A missing callback recipe cannot certify that its receiver is unused.
    graph.nodes[2].body = BodyId::NONE;
    let (out, _, _) = run(&facts, &graph);
    let callback = out
        .calls
        .iter()
        .find(|c| c.kind == EdgeKind::Callback)
        .unwrap();
    assert_eq!(
        &out.arguments[callback.arguments.range()],
        &[Value::TOP, Value::TOP]
    );
    assert_eq!(callback.receiver, Value::TOP);
    assert_eq!(callback.binding, LOCAL_BINDING);
}

#[test]
fn missing_malformed_unknown_or_empty_callback_slots_remain_guarded() {
    for encoding in [
        0,
        encode_callback_argument(2).unwrap(),
        1 << CALLBACK_ARGUMENT_SHIFT,
        encode_callback_argument(1).unwrap(),
    ] {
        let (facts, graph) = fixture(
            "scala/concurrent/Future#flatMap().",
            EDGE_CALLBACK_DEFERRED | encoding,
        );
        let (out, _, _) = run(&facts, &graph);
        assert_eq!(
            out.first_issue.unwrap().reason,
            RuntimeIssueReason::UnknownCallbackValue
        );
        assert!(!out.calls.iter().any(|c| c.kind == EdgeKind::Callback));
        assert_eq!(out.calls[0].target, NodeId(1), "native effects remain");
    }
    let (mut facts, graph) = fixture(
        "scala/concurrent/Future#map().",
        EDGE_CALLBACK_DEFERRED | encode_callback_argument(0).unwrap(),
    );
    facts.operations[1].opcode = Opcode::Constant;
    facts.operations[1].target = SymbolId::NONE;
    let (out, _, _) = run(&facts, &graph);
    assert_eq!(
        out.first_issue.unwrap().reason,
        RuntimeIssueReason::UnknownCallbackValue
    );
    assert!(!out.calls.iter().any(|c| c.kind == EdgeKind::Callback));
}

#[test]
fn policy_requires_the_exact_external_future_target_and_deferred_contract() {
    for name in [
        "p/Future#map().",
        "scala/concurrent/Future#foreach().",
        "scala/concurrent/Future#map(+1).",
    ] {
        let (facts, graph) = fixture(
            name,
            EDGE_CALLBACK_DEFERRED | encode_callback_argument(0).unwrap(),
        );
        let (out, _, _) = run(&facts, &graph);
        assert!(out.issues.is_empty());
        assert_eq!(out.calls.len(), 1);
    }
    let (mut facts, graph) = fixture(
        "scala/concurrent/Future#map().",
        EDGE_CALLBACK_DEFERRED | encode_callback_argument(0).unwrap(),
    );
    facts.symbols[1].flags |= SYMBOL_DEFINED;
    let (out, _, _) = run(&facts, &graph);
    assert!(out.issues.is_empty());
    assert_eq!(out.calls.len(), 1);
    facts.symbols[1].flags &= !SYMBOL_DEFINED;
    let mut graph = graph;
    graph.edges[0].flags &= !EDGE_CALLBACK_DEFERRED;
    let (out, _, _) = run(&facts, &graph);
    assert!(out.issues.is_empty());
    assert_eq!(out.calls.len(), 1);
}

#[test]
fn storing_a_dormant_callback_does_not_activate_its_future_work() {
    let (mut facts, graph) = fixture(
        "scala/concurrent/Future#flatMap().",
        EDGE_CALLBACK_DEFERRED | encode_callback_argument(0).unwrap(),
    );
    facts.bodies[0].operations.len = 2;
    let (out, _, _) = run(&facts, &graph);
    assert_eq!(out.captures.len(), 1);
    assert!(out.calls.is_empty());
    assert!(out.issues.is_empty());
}

#[test]
fn unresolved_compiler_apply_prefix_cannot_activate_a_callback_before_native_arity_repair() {
    let (mut facts, graph) = fixture(
        "scala/concurrent/Future#flatMap().",
        EDGE_CALLBACK_DEFERRED | encode_callback_argument(0).unwrap(),
    );
    facts.operations[2].flags |= OP_SYNTHETIC_PARAMETER_APPLY;
    let (out, _, _) = run(&facts, &graph);
    assert_eq!(out.calls.len(), 1, "prefix must not activate the callback");
    assert_eq!(
        out.first_issue.unwrap().reason,
        RuntimeIssueReason::IncompleteDeferredCallback
    );
    facts.operations[2].flags &= !OP_SYNTHETIC_PARAMETER_APPLY;
    let (out, _, _) = run(&facts, &graph);
    assert!(out.calls.iter().any(|call| call.kind == EdgeKind::Callback));
}

#[test]
fn one_argument_prefix_and_noncanonical_callback_slot_cannot_activate() {
    let (mut facts, mut graph) = fixture(
        "scala/concurrent/Future#map().",
        EDGE_CALLBACK_DEFERRED | encode_callback_argument(0).unwrap(),
    );
    facts.operations[2].arguments.len = 1;
    let (out, _, _) = run(&facts, &graph);
    assert_eq!(out.calls.len(), 1);
    assert_eq!(
        out.first_issue.unwrap().reason,
        RuntimeIssueReason::IncompleteDeferredCallback
    );
    facts.operations[2].arguments.len = 2;
    // A syntactically valid slot encoding cannot redefine this exact ABI.
    // Slot1 is also a known callback in this admission-negative frame.
    facts.operands[2] = ValueId(1);
    graph.edges[0].flags = EDGE_CALLBACK_DEFERRED | encode_callback_argument(1).unwrap();
    let (out, _, _) = run(&facts, &graph);
    assert_eq!(out.calls.len(), 1);
    assert_eq!(
        out.first_issue.unwrap().reason,
        RuntimeIssueReason::UnknownCallbackValue
    );
}
