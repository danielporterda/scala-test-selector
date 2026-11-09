//! Genuine compiler identities, anonymous initialization, and independent JVM
//! order. Unsupported constructor shapes retain explicit uncertainty.
use selector_extract::{ExtractOptions, import_capture};
use selector_facts::{FactSnapshot, OperationRecord};
use selector_types::*;
use std::path::PathBuf;

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/anonymous-construction")
}
fn captured() -> FactSnapshot {
    import_capture(
        &fixture().join("documents.jsonl"),
        Some(&fixture().join("syntax.jsonl")),
        &ExtractOptions {
            workers: 2,
            ..Default::default()
        },
    )
    .unwrap()
}
fn source(facts: &FactSnapshot) -> &str {
    facts.text(facts.files[0].source)
}
fn written(facts: &FactSnapshot, text: &str, last: bool) -> Span {
    let start = if last {
        source(facts).rfind(text)
    } else {
        source(facts).find(text)
    }
    .unwrap() as u32;
    Span {
        start,
        end: start + text.len() as u32,
    }
}
fn operations(facts: &FactSnapshot, body: BodyId) -> &[OperationRecord] {
    &facts.operations[facts.bodies[body.index()].operations.range()]
}
fn class_initializer(facts: &FactSnapshot, name: &str) -> BodyId {
    let class = facts
        .find_symbol(&format!("anonymouscase/{name}#"))
        .unwrap();
    BodyId(
        facts
            .bodies
            .iter()
            .position(|row| row.symbol == class && row.flags & BODY_INITIALIZER != 0)
            .unwrap() as u32,
    )
}
fn member_initializer(facts: &FactSnapshot, owner: &str, name: &str) -> BodyId {
    let symbol = facts
        .find_symbol(&format!("anonymouscase/{owner}#{name}."))
        .unwrap();
    BodyId(
        facts
            .bodies
            .iter()
            .position(|body| body.symbol == symbol && body.flags & BODY_INITIALIZER != 0)
            .unwrap() as u32,
    )
}
fn allocation_at(facts: &FactSnapshot, span: Span) -> &OperationRecord {
    let rows: Vec<_> = facts
        .operations
        .iter()
        .filter(|op| op.span == span && op.opcode == Opcode::Allocate)
        .collect();
    assert_eq!(rows.len(), 1, "exactly one actual allocation at {span:?}");
    rows[0]
}

#[test]
fn actual_jvm_distinguishes_constructor_and_deferred_method_effects() {
    assert_eq!(
        std::fs::read_to_string(fixture().join("execution.log"))
            .unwrap()
            .lines()
            .collect::<Vec<_>>(),
        [
            "active:trait-init",
            "class-active:argument,class:7",
            "body-active:trait-init,body",
            "dormant-created:",
            "dormant-invoked:trait-init",
            "override-created:trait-init",
            "override-invoked:override"
        ]
    );
}

#[test]
fn empty_anonymous_trait_uses_exact_compiler_local_class_and_ordered_initializers() {
    let facts = captured();
    let active = written(&facts, "new Parent {}", false);
    let allocation = allocation_at(&facts, active);
    assert_eq!(
        allocation.body,
        member_initializer(&facts, "Active", "allocated")
    );
    // Eager field recipes attach to their compiler owner in graph building;
    // they need not also appear as an explicit source Initialize operation.
    let owner = facts.find_symbol("anonymouscase/Active#").unwrap();
    let member = facts.bodies[allocation.body.index()].symbol;
    assert_eq!(facts.symbols[member.index()].owner, owner);
    let graph = selector_graph_build::build(&facts, &Default::default()).unwrap();
    let owner_node = graph.node_for_symbol(owner).unwrap();
    let member_node = graph.node_for_symbol(member).unwrap();
    assert_eq!(
        graph
            .edges
            .iter()
            .filter(|edge| edge.source == owner_node
                && edge.target == member_node
                && edge.kind == EdgeKind::Initialize)
            .count(),
        1,
        "the actual class initializer must activate the exact eager field recipe once"
    );
    let class = &facts.symbols[allocation.target.index()];
    assert!(selector_types::symbol::is_local(
        facts.symbol_name(allocation.target)
    ));
    assert_eq!(class.kind, 13);
    let definitions: Vec<_> = facts
        .occurrences
        .iter()
        .filter(|occurrence| occurrence.symbol == allocation.target && occurrence.role == 2)
        .collect();
    assert_eq!(definitions.len(), 1, "exact compiler definition identity");
    assert_eq!(
        definitions[0].span,
        Span {
            start: active.start + 4,
            end: active.start + 4
        }
    );
    assert_eq!(
        class.flags & (SYMBOL_DEFINED | SYMBOL_SCALA_PARENTS_COMPLETE),
        SYMBOL_DEFINED | SYMBOL_SCALA_PARENTS_COMPLETE
    );
    let initializer = BodyId(
        facts
            .bodies
            .iter()
            .position(|b| b.symbol == allocation.target && b.flags & BODY_INITIALIZER != 0)
            .unwrap() as u32,
    );
    assert_eq!(
        facts.bodies[initializer.index()].flags & BODY_SOURCE_RECIPE,
        BODY_SOURCE_RECIPE
    );
    let parents: Vec<_> = operations(&facts, initializer)
        .iter()
        .map(|op| (op.opcode, facts.symbol_name(op.target)))
        .collect();
    assert_eq!(
        parents,
        [
            (Opcode::Initialize, "java/lang/Object#`<init>`()."),
            (Opcode::Initialize, "anonymouscase/Parent#")
        ]
    );
    assert!(
        operations(&facts, initializer)
            .iter()
            .all(|op| op.a == ValueId(0))
    );
    assert!(
        !operations(&facts, allocation.body)
            .iter()
            .any(|op| op.opcode == Opcode::Unknown && op.span == active)
    );
}

#[test]
fn dormant_anonymous_initialization_is_owned_only_by_the_deferred_callback() {
    let facts = captured();
    let span = written(&facts, "new Parent {}", true);
    let allocation = allocation_at(&facts, span);
    assert_ne!(allocation.body, class_initializer(&facts, "Dormant"));
    assert_ne!(
        facts.bodies[allocation.body.index()].flags & BODY_DEFERRED,
        0
    );
    let dormant = operations(&facts, member_initializer(&facts, "Dormant", "later"));
    assert!(
        !dormant
            .iter()
            .any(|op| op.opcode == Opcode::Allocate && op.span == span)
    );
    assert!(dormant.iter().any(|op| op.opcode == Opcode::BindCallback
        && op.target == facts.bodies[allocation.body.index()].symbol));
}

#[test]
fn parameterized_or_nonempty_anonymous_bodies_cannot_be_claimed_empty() {
    let facts = captured();
    for (name, text) in [
        ("ClassActive", "new WithCtor(effectArg()) {}"),
        ("BodyActive", "new Parent { Effects.note(\"body\") }"),
        (
            "OverrideActive",
            "new Parent { override def work(): Unit = Effects.note(\"override\") }",
        ),
    ] {
        let span = written(&facts, text, false);
        assert!(
            !facts
                .operations
                .iter()
                .any(|op| op.opcode == Opcode::Allocate && op.span == span),
            "unsupported {name} not an empty recipe"
        );
        assert!(
            operations(&facts, member_initializer(&facts, name, "allocated"))
                .iter()
                .any(|op| op.opcode == Opcode::Unknown && op.span == span),
            "unsupported {name} stays explicit"
        );
    }
    let argument = facts
        .find_symbol("anonymouscase/ClassActive#effectArg().")
        .unwrap();
    assert!(
        operations(
            &facts,
            member_initializer(&facts, "ClassActive", "allocated")
        )
        .iter()
        .any(|op| matches!(op.opcode, Opcode::Call | Opcode::VirtualCall) && op.target == argument),
        "actual constructor argument side effect must remain visible"
    );
    let override_note = written(&facts, "Effects.note(\"override\")", false);
    assert!(
        !operations(
            &facts,
            member_initializer(&facts, "OverrideActive", "allocated")
        )
        .iter()
        .any(|op| matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
            && op.span == override_note),
        "overridden method body is not constructor-time execution"
    );
}

#[test]
fn executable_trait_effect_has_an_active_proof_and_no_dormant_creation_proof() {
    let facts = captured();
    let graph = selector_graph_build::build(&facts, &Default::default()).unwrap();
    let node = |name: &str| {
        graph
            .node_for_symbol(facts.find_symbol(name).unwrap())
            .unwrap()
    };
    let active = node("anonymouscase/Active#");
    let dormant = node("anonymouscase/Dormant#");
    let options = selector_solve::SolveOptions {
        workers: 2,
        memory_budget_bytes: 64 * 1024 * 1024,
        max_contexts: 10_000,
        max_steps: 1_000_000,
        execution_roots: Some(
            [
                "Active",
                "Dormant",
                "ClassActive",
                "BodyActive",
                "OverrideActive",
            ]
            .into_iter()
            .map(|name| {
                let receiver = facts
                    .find_symbol(&format!("anonymouscase/{name}#"))
                    .unwrap();
                selector_solve::ExecutionRoot {
                    node: graph.node_for_symbol(receiver).unwrap(),
                    receiver,
                }
            })
            .collect::<Vec<_>>()
            .into(),
        ),
        ..Default::default()
    };
    let result = selector_solve::analyze(
        &facts,
        &graph,
        &[node("anonymouscase/Effects.note().")],
        &options,
    )
    .unwrap();
    assert_ne!(result.completion, Completion::ResourceLimited);
    assert!(
        result.contains(active),
        "real trait initializer executes its written effect"
    );
    assert!(
        !result.contains(dormant),
        "creating the closure does not execute its anonymous initializer"
    );
    for name in ["ClassActive", "BodyActive", "OverrideActive"] {
        assert!(
            result
                .guarded_roots
                .contains(&node(&format!("anonymouscase/{name}#"))),
            "unsupported anonymous {name} retains its runtime guard"
        );
    }
    // Opaque library effects in Effects.note remain guarded. This assertion is
    // impact reachability, not an empty-effect or whole-program precision claim.
}
