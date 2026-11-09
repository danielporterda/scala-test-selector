use super::*;
use selector_facts::{BodyRecord, FactBuilder, FileRecord, OperationRecord, SuiteRecord};
use selector_graph::{EdgeRecord, GraphIssue, NodeRecord};

struct Fixture {
    b: FactBuilder,
    graph: ProgramGraph,
}
impl Fixture {
    fn new() -> Self {
        let mut b = FactBuilder::new();
        let path = b.intern("Root.scala").unwrap();
        let source = b.intern(&" ".repeat(256)).unwrap();
        b.facts.files.push(FileRecord {
            path,
            source,
            revision: StrId::NONE,
            context: StrId::NONE,
            source_hash: ContentHash([1; 32]),
            flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
        });
        b.facts.identity = ContentHash([1; 32]);
        Self {
            b,
            graph: ProgramGraph {
                identity: ContentHash([2; 32]),
                facts_identity: ContentHash([1; 32]),
                ..Default::default()
            },
        }
    }
    fn symbol(&mut self, name: &str, kind: u32, owner: SymbolId) -> SymbolId {
        let id = self.b.ensure_symbol(name, FileId(0)).unwrap();
        let row = &mut self.b.facts.symbols[id.index()];
        row.kind = kind;
        row.owner = owner;
        row.file = FileId(0);
        row.flags = SYMBOL_DEFINED;
        self.graph.symbol_nodes.push(NodeId(id.0));
        self.graph.nodes.push(NodeRecord {
            symbol: id,
            file: FileId(0),
            body: BodyId::NONE,
            flags: SYMBOL_DEFINED,
        });
        id
    }
    fn method(&mut self, name: &str) -> SymbolId {
        self.symbol(name, 3, SymbolId::NONE)
    }
    fn root(&mut self, name: &str) -> SymbolId {
        let id = self.symbol(name, 13, SymbolId::NONE);
        self.b.facts.suites.push(SuiteRecord {
            name: self.b.facts.symbols[id.index()].name,
            symbol: id,
            file: FileId(0),
            flags: 0,
        });
        id
    }
    fn field(&mut self, name: &str, foreign: bool) -> SymbolId {
        let id = self.symbol(name, if foreign { 20 } else { 3 }, SymbolId::NONE);
        self.b.facts.symbols[id.index()].properties = 1024;
        if foreign {
            self.b.facts.symbols[id.index()].flags = SYMBOL_NATIVE_BINARY;
        }
        self.body(id, &[]);
        id
    }
    fn body(&mut self, symbol: SymbolId, ops: &[(Opcode, SymbolId)]) {
        let body = BodyId(self.b.facts.bodies.len() as u32);
        let start = self.b.facts.operations.len() as u32;
        self.graph.nodes[symbol.index()].body = body;
        for &(opcode, target) in ops {
            self.b.facts.operations.push(OperationRecord {
                body,
                opcode,
                target,
                dest: ValueId(1),
                a: ValueId(0),
                b: ValueId(1),
                arguments: IdRange::default(),
                span: Span::default(),
                flags: 0,
            });
        }
        self.b.facts.bodies.push(BodyRecord {
            symbol,
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange {
                start,
                len: ops.len() as u32,
            },
            parameters: IdRange::default(),
            body_hash: ContentHash([3; 32]),
            flags: 0,
        });
    }
    fn edge(&mut self, source: SymbolId, target: SymbolId, kind: EdgeKind) {
        self.graph.edges.push(EdgeRecord {
            source: NodeId(source.0),
            target: NodeId(target.0),
            kind,
            occurrence: OccurrenceId::NONE,
            operation: OperationId::NONE,
            receiver: SymbolId::NONE,
            flags: 0,
        });
    }
    fn finish(mut self) -> (FactSnapshot, ProgramGraph) {
        self.graph.index().unwrap();
        (self.b.finish().unwrap(), self.graph)
    }
}
fn run(facts: &FactSnapshot, graph: &ProgramGraph, changed: &[SymbolId]) -> CandidatePlan {
    run_semantics(facts, graph, changed, SuiteSemantics::SharedState)
}
fn run_semantics(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    changed: &[SymbolId],
    semantics: SuiteSemantics,
) -> CandidatePlan {
    let changed: Vec<_> = changed
        .iter()
        .map(|s| graph.symbol_nodes[s.index()])
        .collect();
    plan_guarded_with_semantics(
        facts,
        graph,
        PlanSeeds {
            execution: &changed,
            declarations: &[],
            unscoped: false,
        },
        &[],
        semantics,
    )
    .unwrap()
}

// This protocol fixture supplies admitted class/contract identities, not native
// lookup authority. The producer's separate pinned-byte tests establish which
// receiver/contract pairs may be published as KnownReceiverDispatch.
fn sparse_receiver_fixture() -> (Fixture, [SymbolId; 7]) {
    let mut f = Fixture::new();
    let root = f.root("p/Root#");
    let base = f.symbol("p/Base#", 13, SymbolId::NONE);
    let marked = f.symbol("p/Marked#", 13, SymbolId::NONE);
    let sibling = f.symbol("p/Sibling#", 13, SymbolId::NONE);
    let child = f.symbol("p/Child#", 13, SymbolId::NONE);
    for class in [base, marked, sibling, child] {
        f.b.facts.symbols[class.index()].flags |= SYMBOL_SCALA_PARENTS_COMPLETE;
        f.body(class, &[]);
    }
    for (source, target) in [(marked, base), (sibling, base), (child, marked)] {
        f.b.facts.relations.push(selector_facts::RelationRecord {
            source,
            target,
            kind: RelationKind::Parent,
            file: FileId(0),
        });
    }
    f.b.facts.relations.push(selector_facts::RelationRecord {
        source: marked,
        target: marked,
        kind: RelationKind::DeferredReceiverDispatch,
        file: FileId(0),
    });
    let contract = f.symbol("p/Base#method().", 3, base);
    let other = f.symbol("p/Base#other().", 3, base);
    f.body(contract, &[]);
    f.body(other, &[]);
    (f, [root, base, marked, sibling, child, contract, other])
}
fn receiver_lookup(f: &mut Fixture, receiver: SymbolId, contract: SymbolId) {
    f.b.facts.relations.push(selector_facts::RelationRecord {
        source: receiver,
        target: contract,
        kind: RelationKind::KnownReceiverDispatch,
        file: FileId(0),
    });
}
fn allocated_dispatch(f: &mut Fixture, root: SymbolId, class: SymbolId, contract: SymbolId) {
    f.body(root, &[(Opcode::Allocate, class), (Opcode::Call, contract)]);
    let start = f.b.facts.bodies.last().unwrap().operations.start as usize;
    f.b.facts.operations[start + 1].a = ValueId(1);
    f.b.facts.operations[start + 1].dest = ValueId(2);
}
fn dispatch_reason(plan: &CandidatePlan, root: SymbolId) -> u32 {
    plan.frontiers()
        .iter()
        .find(|row| row.node == NodeId(root.0))
        .map_or(0, |row| row.reasons)
}

#[test]
fn sparse_receiver_frontiers_are_local_to_actual_possible_receiver_calls() {
    for (receiver, expected_open) in [(2, true), (3, false), (4, true)] {
        let (mut f, ids) = sparse_receiver_fixture();
        let [root, _, _, _, _, contract, _] = ids;
        allocated_dispatch(&mut f, root, ids[receiver], contract);
        let (facts, graph) = f.finish();
        let plan = run(&facts, &graph, &[]);
        assert_eq!(
            dispatch_reason(&plan, root) & OPEN_DISPATCH != 0,
            expected_open
        );
        assert_eq!(plan.certifies_unaffected(NodeId(root.0)), !expected_open);
        // A wildcard is not an initializer guard or an expanded graph edge.
        assert!(graph.edges.is_empty());
        assert_eq!(dispatch_reason(&plan, ids[2]), 0);
        plan.validate_seal().unwrap();
    }
    let (mut f, [root, _, _, _, _, _, _]) = sparse_receiver_fixture();
    f.body(root, &[]);
    let (facts, graph) = f.finish();
    assert!(run(&facts, &graph, &[]).certifies_unaffected(NodeId(root.0)));
}

#[test]
fn exact_receiver_lookup_covers_only_its_own_class_and_requested_contract() {
    for (receiver, coverage_receiver, coverage_contract, expected_open) in [
        (2, 2, 5, false),
        (4, 2, 5, true),
        (4, 4, 5, false),
        (2, 2, 6, true),
    ] {
        let (mut f, ids) = sparse_receiver_fixture();
        let root = ids[0];
        receiver_lookup(&mut f, ids[coverage_receiver], ids[coverage_contract]);
        allocated_dispatch(&mut f, root, ids[receiver], ids[5]);
        let (facts, graph) = f.finish();
        let plan = run(&facts, &graph, &[]);
        assert_eq!(
            dispatch_reason(&plan, root) & OPEN_DISPATCH != 0,
            expected_open
        );
        assert_eq!(plan.certifies_unaffected(NodeId(root.0)), !expected_open);
    }
}

#[test]
fn exact_lookup_does_not_erase_body_effects_or_unknown_lexical_receiver() {
    for opaque_body in [false, true] {
        let (mut f, [root, _, marked, _, _, contract, _]) = sparse_receiver_fixture();
        receiver_lookup(&mut f, marked, contract);
        if opaque_body {
            allocated_dispatch(&mut f, root, marked, contract);
            let body = f.graph.nodes[contract.index()].body;
            let start = f.b.facts.operations.len() as u32;
            f.b.facts.bodies[body.index()].operations = IdRange { start, len: 1 };
            f.b.facts.operations.push(OperationRecord {
                body,
                opcode: Opcode::Unknown,
                target: SymbolId::NONE,
                dest: ValueId::NONE,
                a: ValueId::NONE,
                b: ValueId::NONE,
                arguments: IdRange::default(),
                span: Span::default(),
                flags: 0,
            });
        } else {
            // Declaring/lexical this is not an exact runtime class certificate.
            f.body(root, &[(Opcode::Call, contract)]);
        }
        let (facts, graph) = f.finish();
        let plan = run(&facts, &graph, &[]);
        assert!(!plan.certifies_unaffected(NodeId(root.0)));
        assert_eq!(
            dispatch_reason(&plan, root) & OPEN_DISPATCH != 0,
            !opaque_body
        );
    }
}

#[test]
fn incomplete_or_cyclic_receiver_ancestry_cannot_use_a_lookup_certificate() {
    for cycle in [false, true] {
        let (mut f, [root, base, marked, _, child, contract, _]) = sparse_receiver_fixture();
        receiver_lookup(&mut f, marked, contract);
        allocated_dispatch(&mut f, root, marked, contract);
        if cycle {
            f.b.facts.relations.push(selector_facts::RelationRecord {
                source: base,
                target: child,
                kind: RelationKind::Parent,
                file: FileId(0),
            });
        } else {
            f.b.facts.symbols[base.index()].flags &= !SYMBOL_SCALA_PARENTS_COMPLETE;
        }
        let (facts, graph) = f.finish();
        let plan = run(&facts, &graph, &[]);
        assert_ne!(dispatch_reason(&plan, root) & OPEN_DISPATCH, 0);
        assert!(!plan.certifies_unaffected(NodeId(root.0)));
    }
}

#[test]
fn proven_static_scalar_literal_callback_constructor_and_super_do_not_match_wildcards() {
    for mode in 0..5 {
        let (mut f, [root, _, marked, _, _, contract, _]) = sparse_receiver_fixture();
        match mode {
            0 => {
                f.body(
                    root,
                    &[(Opcode::Constant, SymbolId::NONE), (Opcode::Call, contract)],
                );
                f.b.facts.operations.last_mut().unwrap().a = ValueId(1);
            }
            1 => {
                f.body(
                    root,
                    &[
                        (Opcode::BindCallback, contract),
                        (Opcode::InvokeCallback, SymbolId::NONE),
                    ],
                );
                f.b.facts.operations.last_mut().unwrap().a = ValueId(1);
            }
            2 => {
                let ctor = f.symbol("p/Marked#<init>().", 21, marked);
                f.body(ctor, &[]);
                f.body(root, &[(Opcode::Call, ctor)]);
            }
            _ => {
                f.body(root, &[(Opcode::Call, contract)]);
                f.b.facts.operations.last_mut().unwrap().flags = if mode == 3 {
                    OP_SUPER
                } else {
                    OP_QUALIFIED_SUPER
                };
            }
        }
        let (facts, graph) = f.finish();
        let plan = run(&facts, &graph, &[]);
        assert_eq!(dispatch_reason(&plan, root) & OPEN_DISPATCH, 0);
        // Literal callback execution still has the ordinary callback frontier.
        assert_eq!(plan.certifies_unaffected(NodeId(root.0)), mode != 1);
        if mode == 1 {
            assert_ne!(dispatch_reason(&plan, root) & OPEN_CALLBACK, 0);
        }
    }
}

#[test]
fn exact_local_receiver_proof_survives_assign_and_join_but_not_an_unknown_write() {
    for unknown in [false, true] {
        let (mut f, [root, _, _, sibling, _, contract, _]) = sparse_receiver_fixture();
        f.body(
            root,
            &[
                (Opcode::Allocate, sibling),
                (Opcode::Assign, SymbolId::NONE),
                (Opcode::Join, SymbolId::NONE),
                (
                    if unknown {
                        Opcode::Parameter
                    } else {
                        Opcode::Assign
                    },
                    SymbolId::NONE,
                ),
                (Opcode::DefaultArgument, contract),
            ],
        );
        let start = f.b.facts.bodies.last().unwrap().operations.start as usize;
        for (offset, a, b, dest) in [(1, 1, 0, 2), (2, 1, 2, 3), (3, 3, 0, 4), (4, 4, 0, 5)] {
            let op = &mut f.b.facts.operations[start + offset];
            op.a = ValueId(a);
            op.b = ValueId(b);
            op.dest = ValueId(dest);
        }
        let (facts, graph) = f.finish();
        let plan = run(&facts, &graph, &[]);
        assert_eq!(dispatch_reason(&plan, root) & OPEN_DISPATCH != 0, unknown);
        assert_eq!(plan.certifies_unaffected(NodeId(root.0)), !unknown);
    }
}

#[test]
fn nonvirtual_receiver_certificate_requires_native_call_body_and_file() {
    for mode in 0..6 {
        let (mut f, [root, _, _, _, _, contract, _]) = sparse_receiver_fixture();
        f.body(
            root,
            &[(
                if mode == 4 {
                    Opcode::VirtualCall
                } else {
                    Opcode::Call
                },
                contract,
            )],
        );
        let root_body = f.graph.nodes[root.index()].body;
        if !matches!(mode, 1 | 3) {
            f.b.facts.files[0].flags = FILE_BINARY_SOURCE;
            for body in &mut f.b.facts.bodies {
                body.flags |= BODY_BINARY_RECIPE;
            }
        }
        if mode == 2 {
            f.b.facts.bodies[root_body.index()].flags &= !BODY_BINARY_RECIPE;
        } else if mode == 3 {
            f.b.facts.bodies[root_body.index()].flags |= BODY_BINARY_RECIPE;
        }
        let operation = f.b.facts.bodies[root_body.index()].operations.start as usize;
        if mode != 5 {
            f.b.facts.operations[operation].flags |= OP_JVM_NONVIRTUAL;
        }
        let (facts, graph) = f.finish();
        assert_eq!(
            receiver_dispatch_operation(&facts, &facts.operations[operation]),
            mode != 0
        );
        let plan = run(&facts, &graph, &[]);
        assert_eq!(dispatch_reason(&plan, root) & OPEN_DISPATCH != 0, mode != 0);
        assert_eq!(plan.certifies_unaffected(NodeId(root.0)), mode == 0);
    }
}

#[test]
fn nonvirtual_certificate_preserves_unknown_targets_body_effects_and_initialization() {
    for boundary in [Opcode::Call, Opcode::Unknown, Opcode::Initialize] {
        let (mut f, [root, _, _, _, _, contract, _]) = sparse_receiver_fixture();
        f.body(
            root,
            &[(Opcode::Call, contract), (boundary, SymbolId::NONE)],
        );
        f.b.facts.files[0].flags = FILE_BINARY_SOURCE;
        for body in &mut f.b.facts.bodies {
            body.flags |= BODY_BINARY_RECIPE;
        }
        let body = f.b.facts.bodies.last().unwrap();
        for op in &mut f.b.facts.operations[body.operations.range()] {
            op.flags |= OP_JVM_NONVIRTUAL;
        }
        let (facts, graph) = f.finish();
        let plan = run(&facts, &graph, &[]);
        assert_eq!(dispatch_reason(&plan, root) & OPEN_DISPATCH, 0);
        assert_ne!(dispatch_reason(&plan, root) & UNKNOWN_RECIPE, 0);
        assert!(!plan.certifies_unaffected(NodeId(root.0)));
    }
}

#[test]
fn suite_independence_removes_only_other_roots_hidden_shared_heap_exposure() {
    let mut f = Fixture::new();
    let opaque = f.root("p/Opaque#");
    let reader = f.root("p/Reader#");
    let pure = f.root("p/Pure#");
    let changed = f.method("other/changed().");
    let field = f.field("p/State.value.", false);
    f.body(opaque, &[(Opcode::Unknown, SymbolId::NONE)]);
    f.body(reader, &[(Opcode::LoadField, field)]);
    f.body(pure, &[]);
    f.body(changed, &[]);
    let (facts, graph) = f.finish();
    let shared = run(&facts, &graph, &[changed]);
    let independent = run_semantics(&facts, &graph, &[changed], SuiteSemantics::Independent);
    assert!(!shared.certifies_unaffected(NodeId(reader.0)));
    assert_eq!(shared.shared_heap_guarded_roots(), [NodeId(reader.0)]);
    assert!(independent.certifies_unaffected(NodeId(reader.0)));
    assert!(independent.shared_heap_guarded_roots().is_empty());
    for p in [&shared, &independent] {
        assert!(!p.certifies_unaffected(NodeId(opaque.0)));
        assert!(p.certifies_unaffected(NodeId(pure.0)));
        p.validate_seal().unwrap();
    }
    assert_eq!(shared.suite_semantics(), SuiteSemantics::SharedState);
    assert_eq!(independent.suite_semantics(), SuiteSemantics::Independent);
    assert_eq!(
        shared.assumptions(),
        15 | SelectionContract::CURRENT_BASE_BITS
    );
    assert_eq!(
        independent.assumptions(),
        15 | SelectionContract::current(SuiteSemantics::Independent).bits()
    );
    // Recognizing an opt-in premise does not enable it for ordinary plans.
    assert_eq!(
        independent.assumptions() & SelectionContract::OWNING_TEST_CLASSPATH,
        0
    );
    assert_eq!(
        ASSUMED_SUITE_INDEPENDENCE,
        SelectionContract::SUITE_INDEPENDENCE
    );
    // The established wrappers retain shared-state behavior and exact content.
    let default = plan(
        &facts,
        &graph,
        PlanSeeds {
            execution: &[NodeId(changed.0)],
            declarations: &[],
            unscoped: false,
        },
    )
    .unwrap();
    assert_eq!(default.identity(), shared.identity());
}

#[test]
fn suite_independence_preserves_matching_known_and_foreign_potential_writers() {
    for foreign_writer in [false, true] {
        let mut f = Fixture::new();
        let reader = f.root("p/Reader#");
        let writer = f.root("p/Writer#");
        let pure = f.root("p/Pure#");
        let source = f.field("p/State.value.", false);
        let target = if foreign_writer {
            f.field("@jvm/State/value", true)
        } else {
            source
        };
        f.body(reader, &[(Opcode::LoadField, source)]);
        f.body(writer, &[(Opcode::StoreField, target)]);
        f.body(pure, &[]);
        let (facts, graph) = f.finish();
        let p = run_semantics(&facts, &graph, &[writer], SuiteSemantics::Independent);
        assert!(!p.certifies_unaffected(NodeId(reader.0)));
        assert!(!p.certifies_unaffected(NodeId(writer.0)));
        assert!(p.certifies_unaffected(NodeId(pure.0)));
    }
}

#[test]
fn suite_independence_preserves_within_root_frontiers_and_input_guards() {
    let mut f = Fixture::new();
    let callback = f.root("p/Callback#");
    let dispatch = f.root("p/Dispatch#");
    let reflection = f.root("p/Reflection#");
    let unknown_heap = f.root("p/UnknownHeap#");
    let elements = f.root("p/Elements#");
    let guarded = f.root("p/Guarded#");
    let input = f.root("p/Input#");
    let pure = f.root("p/Pure#");
    let method = f.method("p/Receiver#invoke().");
    let reflective = f.method("java/lang/Class#forName().");
    let field = f.field("p/State.value.", false);
    f.body(callback, &[(Opcode::InvokeCallback, SymbolId::NONE)]);
    f.body(dispatch, &[(Opcode::VirtualCall, method)]);
    f.body(reflection, &[(Opcode::Call, reflective)]);
    f.body(unknown_heap, &[(Opcode::LoadField, SymbolId::NONE)]);
    f.body(elements, &[(Opcode::ReadElements, field)]);
    f.body(guarded, &[]);
    f.body(input, &[]);
    f.body(pure, &[]);
    f.body(method, &[]);
    f.b.facts.issues.push(selector_facts::IssueRecord {
        kind: IssueKind::UnknownExecution,
        file: FileId::NONE,
        symbol: input,
        detail: StrId::NONE,
    });
    let (facts, graph) = f.finish();
    let p = plan_guarded_with_semantics(
        &facts,
        &graph,
        PlanSeeds {
            execution: &[],
            declarations: &[],
            unscoped: false,
        },
        &[NodeId(guarded.0)],
        SuiteSemantics::Independent,
    )
    .unwrap();
    for root in [
        callback,
        dispatch,
        reflection,
        unknown_heap,
        elements,
        guarded,
        input,
    ] {
        assert!(!p.certifies_unaffected(NodeId(root.0)));
    }
    assert!(p.certifies_unaffected(NodeId(pure.0)));
    let unscoped = plan_guarded_with_semantics(
        &facts,
        &graph,
        PlanSeeds {
            execution: &[],
            declarations: &[],
            unscoped: true,
        },
        &[],
        SuiteSemantics::Independent,
    )
    .unwrap();
    assert!(unscoped.excluded_roots().is_empty());
}

#[test]
fn suite_independence_keeps_declarations_and_class_initialization_dependencies() {
    let mut f = Fixture::new();
    let uses_declaration = f.root("p/DeclarationUser#");
    let uses_initializer = f.root("p/InitializerUser#");
    let pure = f.root("p/Pure#");
    let declaration = f.symbol("p/ChangedType#", 13, SymbolId::NONE);
    let initializer = f.symbol("p/ChangedInitializer#", 13, SymbolId::NONE);
    f.body(uses_declaration, &[]);
    f.body(uses_initializer, &[(Opcode::Initialize, initializer)]);
    f.body(pure, &[]);
    f.body(initializer, &[]);
    f.edge(uses_declaration, declaration, EdgeKind::Compile);
    f.edge(uses_initializer, initializer, EdgeKind::Initialize);
    let (facts, graph) = f.finish();
    let p = plan_guarded_with_semantics(
        &facts,
        &graph,
        PlanSeeds {
            execution: &[NodeId(initializer.0)],
            declarations: &[NodeId(declaration.0)],
            unscoped: false,
        },
        &[],
        SuiteSemantics::Independent,
    )
    .unwrap();
    assert!(!p.certifies_unaffected(NodeId(uses_declaration.0)));
    assert!(!p.certifies_unaffected(NodeId(uses_initializer.0)));
    assert!(p.certifies_unaffected(NodeId(pure.0)));
}

#[test]
fn suite_semantics_are_private_and_bound_to_plan_and_root_certificates() {
    let mut f = Fixture::new();
    let pure = f.root("p/Pure#");
    f.body(pure, &[]);
    let (facts, graph) = f.finish();
    let shared = run(&facts, &graph, &[]);
    let mut independent = run_semantics(&facts, &graph, &[], SuiteSemantics::Independent);
    assert!(shared.certifies_unaffected(NodeId(pure.0)));
    assert!(independent.certifies_unaffected(NodeId(pure.0)));
    assert_ne!(shared.identity(), independent.identity());
    assert_eq!(shared.assumptions() & 15, 15);
    assert_eq!(independent.assumptions() & 15, 15);
    for premise in [
        SelectionContract::FUNCTIONAL_BEHAVIOR,
        SelectionContract::CLOSED_APPLICATION_CLASSPATH,
        SelectionContract::TRUSTED_RUNTIME_CONTRACTS,
        SelectionContract::STABLE_EXTERNAL_INPUTS,
    ] {
        assert_eq!(shared.assumptions() & premise, premise);
        assert_eq!(independent.assumptions() & premise, premise);
    }
    assert_ne!(
        shared.cert_identity(NodeId(pure.0)),
        independent.cert_identity(NodeId(pure.0))
    );
    independent.suite_semantics = SuiteSemantics::SharedState;
    assert!(independent.validate_seal().is_err());
}

#[test]
fn current_model_contract_is_bound_even_without_any_exclusions() {
    let mut f = Fixture::new();
    let root = f.root("p/Open#");
    f.body(root, &[(Opcode::Unknown, SymbolId::NONE)]);
    let (facts, graph) = f.finish();
    let shared = run(&facts, &graph, &[]);
    let independent = run_semantics(&facts, &graph, &[], SuiteSemantics::Independent);
    for p in [&shared, &independent] {
        assert!(p.excluded_roots().is_empty());
        assert_eq!(
            p.assumptions() & SelectionContract::CURRENT_BASE_BITS,
            SelectionContract::CURRENT_BASE_BITS
        );
        p.validate_seal().unwrap();
    }
    assert_ne!(shared.identity(), independent.identity());
}

#[test]
fn unknown_member_writes_expose_primitive_readers_without_an_extra_callback() {
    let mut f = Fixture::new();
    let writer = f.root("p/UnknownWriter#");
    let reader = f.root("p/PrimitiveReader#");
    let pure = f.root("p/Pure#");
    f.body(writer, &[(Opcode::StoreField, SymbolId::NONE)]);
    f.body(reader, &[(Opcode::ReadElements, SymbolId::NONE)]);
    f.body(pure, &[]);
    let body = f.graph.nodes[reader.index()].body;
    f.b.facts.bodies[body.index()].flags |= BODY_BINARY_RECIPE;
    let operation = f.b.facts.bodies[body.index()].operations.start as usize;
    f.b.facts.operations[operation].flags |= OP_TRUSTED_PRIMITIVE_READ;
    let (facts, graph) = f.finish();
    let shared = run(&facts, &graph, &[writer]);
    let independent = run_semantics(&facts, &graph, &[writer], SuiteSemantics::Independent);
    assert_eq!(shared.shared_heap_guarded_roots(), [NodeId(reader.0)]);
    assert!(independent.shared_heap_guarded_roots().is_empty());
    assert!(shared.frontiers().iter().any(|frontier| {
        frontier.node == NodeId(writer.0)
            && frontier.reasons & (UNKNOWN_RECIPE | UNKNOWN_HEAP) == (UNKNOWN_RECIPE | UNKNOWN_HEAP)
    }));
    for p in [&shared, &independent] {
        assert!(!p.certifies_unaffected(NodeId(writer.0)));
        // Primitive value uncertainty is still a within-root frontier. The
        // independent selector may later finish this candidate without a guard.
        assert!(!p.certifies_unaffected(NodeId(reader.0)));
        assert!(p.certifies_unaffected(NodeId(pure.0)));
    }
}

#[test]
fn closed_effect_top_data_certifies_disjointness_but_not_open_consumers() {
    let mut f = Fixture::new();
    let scalar = f.root("p/Scalar#");
    let hidden = f.root("p/Hidden#");
    let incomplete = f.root("p/Incomplete#");
    let callback = f.root("p/Callback#");
    let alias = f.root("p/Alias#");
    let dispatch = f.root("p/Dispatch#");
    let changed = f.method("p/changed().");
    let scalar_method = f.method("p/scalar().");
    let owner = f.symbol("p/Open#", 13, SymbolId::NONE);
    let virtual_method = f.symbol("p/Open#m().", 3, owner);
    let field = f.field("p/Cell#value.", false);
    f.body(changed, &[]);
    f.body(virtual_method, &[]);
    f.body(scalar_method, &[(Opcode::Assign, SymbolId::NONE)]);
    f.b.facts.operations.last_mut().unwrap().a = ValueId::NONE;
    f.body(scalar, &[(Opcode::Call, scalar_method)]);
    f.body(hidden, &[(Opcode::Call, changed)]);
    f.body(incomplete, &[(Opcode::Unknown, SymbolId::NONE)]);
    f.body(callback, &[(Opcode::InvokeCallback, SymbolId::NONE)]);
    f.body(alias, &[(Opcode::LoadField, field)]);
    f.body(dispatch, &[(Opcode::VirtualCall, virtual_method)]);
    let (facts, graph) = f.finish();
    let planned = run(&facts, &graph, &[changed]);
    assert!(planned.certifies_unaffected(NodeId(scalar.0)));
    for root in [hidden, incomplete, callback, alias, dispatch] {
        assert!(
            !planned.certifies_unaffected(NodeId(root.0)),
            "TOP data cannot close an effect/alias frontier: {root:?}"
        );
    }
    // A changed scalar callee is still a potential execution dependency even
    // when its recipe has no externally visible side effects.
    assert!(!run(&facts, &graph, &[scalar_method]).certifies_unaffected(NodeId(scalar.0)));
}

#[test]
fn unrelated_closed_execution_region_is_certified_without_a_solver_run() {
    let mut f = Fixture::new();
    let a = f.root("one/A#");
    let b = f.root("two/B#");
    let changed = f.method("one/changed().");
    let stable = f.method("two/stable().");
    f.body(changed, &[]);
    f.body(stable, &[]);
    f.body(a, &[(Opcode::Call, changed)]);
    f.body(b, &[(Opcode::Call, stable)]);
    let (facts, graph) = f.finish();
    let p = run(&facts, &graph, &[changed]);
    assert_eq!(
        p.roots,
        [PlannedRoot {
            node: NodeId(a.0),
            receiver: a
        }]
    );
    assert!(p.certifies_unaffected(NodeId(b.0)));
    assert!(p.cert_identity(NodeId(b.0)).is_some());
    assert!(p.cert_identity(NodeId(a.0)).is_none());
    assert_eq!(
        (p.metrics.roots, p.metrics.candidates, p.metrics.excluded),
        (2, 1, 1)
    );
}

#[test]
fn callback_bindings_and_open_invocations_cannot_hide_a_changed_closure() {
    let mut f = Fixture::new();
    let binding = f.root("p/Binding#");
    let invoke = f.root("p/Invoke#");
    let untouched = f.root("p/Pure#");
    let closure = f.method("@closure/changed");
    let other = f.method("p/other().");
    f.body(closure, &[]);
    f.body(other, &[]);
    f.body(binding, &[(Opcode::BindCallback, closure)]);
    f.body(invoke, &[(Opcode::InvokeCallback, SymbolId::NONE)]);
    f.body(untouched, &[]);
    let (facts, graph) = f.finish();
    let p = run(&facts, &graph, &[closure]);
    assert!(p.roots.iter().any(|r| r.node == NodeId(binding.0)));
    assert!(p.roots.iter().any(|r| r.node == NodeId(invoke.0)));
    assert!(p.certifies_unaffected(NodeId(untouched.0)));
    let unrelated = run(&facts, &graph, &[other]);
    assert!(!unrelated.certifies_unaffected(NodeId(invoke.0)));
}

#[test]
fn open_virtual_dispatch_stays_candidate_and_verified_final_owner_can_close_it() {
    for final_owner in [false, true] {
        let mut f = Fixture::new();
        let root = f.root("p/Suite#");
        let owner = f.symbol("p/Base#", 13, SymbolId::NONE);
        let method = f.symbol("p/Base#m().", 3, owner);
        let changed = f.method("other/changed().");
        if final_owner {
            f.b.facts.symbols[owner.index()].properties |= 8;
        }
        f.body(method, &[]);
        f.body(changed, &[]);
        f.body(root, &[(Opcode::VirtualCall, method)]);
        let (facts, graph) = f.finish();
        let p = run(&facts, &graph, &[changed]);
        assert_eq!(p.certifies_unaffected(NodeId(root.0)), final_owner);
    }
}

#[test]
fn shared_field_reads_depend_on_all_potential_writers_even_in_other_roots() {
    let mut f = Fixture::new();
    let reader = f.root("p/Read#");
    let writer = f.root("p/Write#");
    let separate = f.root("p/Separate#");
    let field = f.field("p/Cell#value.", false);
    f.body(reader, &[(Opcode::LoadField, field)]);
    f.body(writer, &[(Opcode::StoreField, field)]);
    f.body(separate, &[]);
    let (facts, graph) = f.finish();
    let p = run(&facts, &graph, &[writer]);
    assert!(!p.certifies_unaffected(NodeId(reader.0)));
    assert!(!p.certifies_unaffected(NodeId(writer.0)));
    assert!(p.certifies_unaffected(NodeId(separate.0)));
}

#[test]
fn native_and_source_field_namespaces_do_not_prove_disjoint_heap_slots() {
    for native_reader in [false, true] {
        let mut f = Fixture::new();
        let reader = f.root("p/Read#");
        let writer = f.root("p/Write#");
        let source = f.field("p/Cell#value.", false);
        let native = f.field("@jvm/field", true);
        f.body(
            reader,
            &[(
                Opcode::LoadField,
                if native_reader { native } else { source },
            )],
        );
        f.body(
            writer,
            &[(
                Opcode::StoreField,
                if native_reader { source } else { native },
            )],
        );
        let (facts, graph) = f.finish();
        let p = run(&facts, &graph, &[writer]);
        assert!(!p.certifies_unaffected(NodeId(reader.0)));
    }
}

#[test]
fn opaque_runnable_frontier_keeps_heap_readers_but_not_a_disjoint_pure_region() {
    let mut f = Fixture::new();
    let opaque = f.root("p/Opaque#");
    let heap = f.root("p/Heap#");
    let pure = f.root("p/Pure#");
    let changed = f.method("elsewhere/changed().");
    let field = f.field("p/Cell#value.", false);
    f.body(opaque, &[(Opcode::Unknown, SymbolId::NONE)]);
    f.body(
        heap,
        &[(Opcode::StoreField, field), (Opcode::LoadField, field)],
    );
    f.body(pure, &[]);
    f.body(changed, &[]);
    let (facts, graph) = f.finish();
    let p = run(&facts, &graph, &[changed]);
    assert!(!p.certifies_unaffected(NodeId(opaque.0)));
    assert!(!p.certifies_unaffected(NodeId(heap.0)));
    assert!(p.certifies_unaffected(NodeId(pure.0)));
    assert_eq!(p.shared_heap_guarded_roots(), [NodeId(heap.0)]);
    p.validate_seal().unwrap();
    // The scalar read is retained through shared-state exposure, rather than
    // being misclassified as an execution hole of its own.
    assert_eq!(p.metrics.unknown_roots, 1);
    assert_eq!(p.metrics.heap_roots, 1);
    // Existing unresolved effects stay visible even on an unchanged query.
    let no_changes = run(&facts, &graph, &[]);
    assert!(!no_changes.certifies_unaffected(NodeId(opaque.0)));
    assert_eq!(no_changes.shared_heap_guarded_roots(), [NodeId(heap.0)]);
}

#[test]
fn shared_heap_exposure_is_private_sealed_and_owned_capacity_is_charged() {
    let mut f = Fixture::new();
    let opaque = f.root("p/Opaque#");
    let reader = f.root("p/Reader#");
    let pure = f.root("p/Pure#");
    let field = f.field("p/State.value.", false);
    f.body(opaque, &[(Opcode::Unknown, SymbolId::NONE)]);
    f.body(reader, &[(Opcode::LoadField, field)]);
    f.body(pure, &[]);
    let (facts, graph) = f.finish();
    let mut planned = run(&facts, &graph, &[]);
    assert_eq!(planned.shared_heap_guarded_roots(), [NodeId(reader.0)]);
    assert!(planned.certifies_unaffected(NodeId(pure.0)));
    assert_eq!(
        planned.metrics().owned_bytes,
        planned.roots.capacity() * std::mem::size_of::<PlannedRoot>()
            + (planned.excluded.capacity()
                + planned.shared_heap_guarded.capacity()
                + planned.execution.capacity()
                + planned.declarations.capacity()
                + planned.guards.capacity())
                * 4
            + planned.frontiers.capacity() * std::mem::size_of::<Frontier>()
            + planned.potential.offsets.capacity() * std::mem::size_of::<usize>()
            + planned.potential.sources.capacity() * 4
    );
    planned.validate_seal().unwrap();
    planned.shared_heap_guarded.clear();
    assert!(
        planned.validate_seal().is_err(),
        "heap exposure must participate in identity"
    );
    let mut planned = run(&facts, &graph, &[]);
    planned.roots.retain(|root| root.node != NodeId(reader.0));
    assert!(
        planned.validate_seal().is_err(),
        "removing a public candidate invalidates its seal"
    );
    let mut planned = run(&facts, &graph, &[]);
    planned.roots[0].receiver = SymbolId::NONE;
    assert!(
        planned.validate_seal().is_err(),
        "receiver changes invalidate the sealed content"
    );
}

#[test]
fn declaration_changes_and_query_guards_have_bound_separate_coverage() {
    let mut f = Fixture::new();
    let a = f.root("p/A#");
    let b = f.root("p/B#");
    let method = f.method("p/api().");
    let declaration = f.symbol("p/Type#", 13, SymbolId::NONE);
    f.body(a, &[(Opcode::Call, method)]);
    f.body(b, &[]);
    f.body(method, &[]);
    f.edge(method, declaration, EdgeKind::Compile);
    let (facts, graph) = f.finish();
    let seeds = [NodeId(declaration.0)];
    let p = plan(
        &facts,
        &graph,
        PlanSeeds {
            execution: &[],
            declarations: &seeds,
            unscoped: false,
        },
    )
    .unwrap();
    assert!(!p.certifies_unaffected(NodeId(a.0)));
    assert!(p.certifies_unaffected(NodeId(b.0)));
    let guarded = plan_guarded(
        &facts,
        &graph,
        PlanSeeds {
            execution: &[],
            declarations: &[],
            unscoped: false,
        },
        &[NodeId(method.0)],
    )
    .unwrap();
    assert!(!guarded.certifies_unaffected(NodeId(a.0)));
    assert!(guarded.certifies_unaffected(NodeId(b.0)));
    assert_ne!(guarded.identity(), p.identity());
    assert_eq!(guarded.guard_nodes(), [NodeId(method.0)]);
}

#[test]
fn file_only_unknowns_cover_every_body_and_unscoped_inputs_forbid_certificates() {
    let mut f = Fixture::new();
    let a = f.root("p/A#");
    let b = f.root("p/B#");
    f.body(a, &[]);
    f.body(b, &[]);
    f.graph.issues.push(GraphIssue {
        kind: IssueKind::UnknownExecution,
        node: NodeId::NONE,
        file: FileId(0),
        symbol: SymbolId::NONE,
        detail: StrId::NONE,
    });
    let (facts, graph) = f.finish();
    let p = run(&facts, &graph, &[]);
    assert!(p.excluded_roots().is_empty());
    let mut f = Fixture::new();
    let a = f.root("p/A#");
    f.body(a, &[]);
    let (facts, graph) = f.finish();
    let p = plan(
        &facts,
        &graph,
        PlanSeeds {
            execution: &[],
            declarations: &[],
            unscoped: true,
        },
    )
    .unwrap();
    assert!(p.excluded_roots().is_empty());
}

#[test]
fn metadata_ancestry_does_not_poison_execution_coverage_but_real_guards_still_do() {
    let mut f = Fixture::new();
    let root = f.root("p/Root#");
    let initializer = f.symbol("p/LibraryTrait#", 14, SymbolId::NONE);
    f.body(root, &[(Opcode::Initialize, initializer)]);
    f.body(initializer, &[]);
    f.edge(root, initializer, EdgeKind::Initialize);
    let path = f.b.intern("admitted.jar!/p/LibraryTrait.class").unwrap();
    let native_file = FileId(f.b.facts.files.len() as u32);
    f.b.facts.files.push(FileRecord {
        path,
        source: StrId::NONE,
        revision: StrId::NONE,
        context: StrId::NONE,
        source_hash: ContentHash([9; 32]),
        flags: FILE_BINARY_SOURCE,
    });
    f.b.facts.symbols[initializer.index()].flags = SYMBOL_JVM_CLASS_HEADER_VERIFIED;
    f.b.facts.symbols[initializer.index()].file = FileId::NONE;
    f.graph.nodes[initializer.index()].flags = SYMBOL_JVM_CLASS_HEADER_VERIFIED;
    f.graph.nodes[initializer.index()].file = native_file;
    let body = f.graph.nodes[initializer.index()].body;
    f.b.facts.bodies[body.index()].file = native_file;
    f.b.facts.bodies[body.index()].flags = BODY_BINARY_RECIPE | BODY_INITIALIZER;
    f.b.facts.issues.push(selector_facts::IssueRecord {
        kind: IssueKind::IncompleteHierarchy,
        file: native_file,
        symbol: initializer,
        detail: StrId::NONE,
    });
    let (mut facts, graph) = f.finish();
    let plan = run(&facts, &graph, &[]);
    assert!(plan.certifies_unaffected(NodeId(root.0)));
    facts.issues[0].kind = IssueKind::UnknownExecution;
    let guarded = run(&facts, &graph, &[]);
    assert!(!guarded.certifies_unaffected(NodeId(root.0)));
    assert_ne!(plan.identity(), guarded.identity());
}

#[test]
fn certificates_bind_snapshot_and_canonical_seed_sets_independently_on_each_side() {
    let mut f = Fixture::new();
    let root = f.root("p/Root#");
    let a = f.method("p/A().");
    let b = f.method("p/B().");
    f.body(root, &[]);
    f.body(a, &[]);
    f.body(b, &[]);
    let (facts, mut graph) = f.finish();
    let p = run(&facts, &graph, &[a, b, a]);
    let reordered = run(&facts, &graph, &[b, a]);
    assert_eq!(p.identity(), reordered.identity());
    assert_eq!(
        p.cert_identity(NodeId(root.0)),
        reordered.cert_identity(NodeId(root.0))
    );
    graph.identity = ContentHash([9; 32]);
    let head = run(&facts, &graph, &[a, b]);
    assert_ne!(p.identity(), head.identity());
    assert_ne!(
        p.cert_identity(NodeId(root.0)),
        head.cert_identity(NodeId(root.0))
    );
}

#[test]
fn known_field_noninterference_does_not_require_a_must_execute_initializer() {
    let mut f = Fixture::new();
    let root = f.root("p/Read#");
    let pure = f.root("p/Pure#");
    let writer = f.method("p/dormantWriter().");
    let unrelated = f.method("other/changed().");
    let field = f.field("p/Cell#value.", false);
    f.body(root, &[(Opcode::LoadField, field)]);
    f.body(pure, &[]);
    f.body(writer, &[(Opcode::StoreField, field)]);
    f.body(unrelated, &[]);
    let (facts, graph) = f.finish();
    let p = run(&facts, &graph, &[unrelated]);
    assert!(p.certifies_unaffected(NodeId(root.0)));
    assert!(
        p.frontiers()
            .iter()
            .all(|row| row.node != NodeId(root.0) || row.reasons & UNKNOWN_HEAP == 0)
    );
    assert!(p.certifies_unaffected(NodeId(pure.0)));
    // A store need not run or establish an initial value to carry a change.
    // Its potential effect is sufficient to retain every matching reader.
    let changed_writer = run(&facts, &graph, &[writer]);
    assert!(!changed_writer.certifies_unaffected(NodeId(root.0)));
    assert!(changed_writer.certifies_unaffected(NodeId(pure.0)));
}

#[test]
fn unknown_field_values_do_not_close_indirect_execution_or_unidentified_reads() {
    let mut f = Fixture::new();
    let scalar = f.root("p/Scalar#");
    let callback = f.root("p/Callback#");
    let dispatch = f.root("p/Dispatch#");
    let unidentified = f.root("p/Unidentified#");
    let elements = f.root("p/Elements#");
    let field = f.field("p/Cell#value.", false);
    let method = f.method("p/Receiver#invoke().");
    let unrelated = f.method("other/changed().");
    f.body(scalar, &[(Opcode::LoadField, field)]);
    f.body(
        callback,
        &[
            (Opcode::LoadField, field),
            (Opcode::InvokeCallback, SymbolId::NONE),
        ],
    );
    f.body(
        dispatch,
        &[(Opcode::LoadField, field), (Opcode::VirtualCall, method)],
    );
    f.body(unidentified, &[(Opcode::LoadField, SymbolId::NONE)]);
    f.body(elements, &[(Opcode::ReadElements, field)]);
    f.body(method, &[]);
    f.body(unrelated, &[]);
    let (facts, graph) = f.finish();
    let p = run(&facts, &graph, &[unrelated]);
    for root in [callback, dispatch, unidentified, elements] {
        assert!(!p.certifies_unaffected(NodeId(root.0)));
    }
    // The callback and open dispatch can mutate shared state. Even a plain
    // scalar reader cannot use its known field ID to escape that exposure.
    assert!(!p.certifies_unaffected(NodeId(scalar.0)));
    assert!(p.shared_heap_guarded_roots().contains(&NodeId(scalar.0)));
}

#[test]
fn unresolved_named_catalogue_suites_are_not_invented_or_certified() {
    let mut f = Fixture::new();
    let pure = f.root("p/Pure#");
    let heap = f.root("p/Heap#");
    let field = f.field("p/Cell#value.", false);
    f.body(pure, &[]);
    f.body(
        heap,
        &[(Opcode::StoreField, field), (Opcode::LoadField, field)],
    );
    let name = f.b.intern("missing.ExternalSuite").unwrap();
    f.b.facts.suites.push(SuiteRecord {
        name,
        symbol: SymbolId::NONE,
        file: FileId::NONE,
        flags: 0,
    });
    let (facts, graph) = f.finish();
    let p = run(&facts, &graph, &[]);
    assert_eq!(p.metrics().unresolved_roots, 1);
    assert!(!p.certifies_unaffected(NodeId::NONE));
    assert!(p.certifies_unaffected(NodeId(pure.0)));
    assert!(!p.certifies_unaffected(NodeId(heap.0)));
    assert!(
        p.roots
            .iter()
            .all(|root| !root.node.is_none() && !root.receiver.is_none())
    );
}

#[test]
fn observations_refute_certificates_through_potential_and_derived_dependencies() {
    let mut f = Fixture::new();
    let heap = f.root("p/Heap#");
    let pure = f.root("p/Pure#");
    let caller = f.root("p/Caller#");
    let field = f.field("p/Cell#value.", false);
    let writer = f.method("p/write().");
    let helper = f.method("p/helper().");
    let changed = f.method("other/changed().");
    f.body(heap, &[(Opcode::Call, writer)]);
    f.body(pure, &[]);
    f.body(caller, &[(Opcode::Call, helper)]);
    f.body(writer, &[(Opcode::StoreField, field)]);
    f.body(helper, &[]);
    f.body(changed, &[]);
    let (facts, graph) = f.finish();
    let p = run(&facts, &graph, &[changed]);
    assert!(p.certifies_unaffected(NodeId(heap.0)));
    assert!(p.certifies_unaffected(NodeId(caller.0)));
    assert_eq!(
        p.refuted_roots(&facts, &graph, &[NodeId(writer.0)], &[])
            .unwrap(),
        [NodeId(heap.0)]
    );
    assert_eq!(
        p.refuted_roots(
            &facts,
            &graph,
            &[NodeId(changed.0)],
            &[(NodeId(helper.0), NodeId(changed.0))]
        )
        .unwrap(),
        [NodeId(caller.0)]
    );
    assert!(p.certifies_unaffected(NodeId(pure.0))); // Refutation never mutates or creates proof.
    assert!(
        p.refuted_roots(&facts, &graph, &[NodeId::NONE], &[])
            .is_err()
    );
}

#[test]
fn a_conflicted_final_owner_does_not_close_virtual_dispatch() {
    let mut f = Fixture::new();
    let root = f.root("p/Root#");
    let owner = f.symbol("p/Final#", 13, SymbolId::NONE);
    f.b.facts.symbols[owner.index()].properties = 8;
    let method = f.symbol("p/Final#m().", 3, owner);
    let changed = f.method("other/changed().");
    f.body(root, &[(Opcode::VirtualCall, method)]);
    f.body(method, &[]);
    f.body(changed, &[]);
    f.b.facts.issues.push(selector_facts::IssueRecord {
        kind: IssueKind::ContextConflict,
        file: FileId(0),
        symbol: owner,
        detail: StrId::NONE,
    });
    let (facts, graph) = f.finish();
    let p = run(&facts, &graph, &[changed]);
    assert!(!p.certifies_unaffected(NodeId(root.0)));
    assert!(
        p.frontiers()
            .iter()
            .any(|row| row.node == NodeId(root.0) && row.reasons & OPEN_DISPATCH != 0)
    );
}

#[test]
fn unsealed_inputs_never_issue_exclusion_certificates() {
    let mut f = Fixture::new();
    let root = f.root("p/Root#");
    f.body(root, &[]);
    let (mut facts, mut graph) = f.finish();
    facts.identity = ContentHash::default();
    graph.facts_identity = facts.identity;
    let p = run(&facts, &graph, &[]);
    assert!(!p.certifies_unaffected(NodeId(root.0)));
    assert!(p.frontiers().iter().any(|f| f.node.is_none()));
}
