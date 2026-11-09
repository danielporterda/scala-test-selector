//! Real compiler-generated Position actuals complete registration before its
//! effect, while the registered body stays a deferred callback. No JVM rerun.
use selector_extract::{ExtractOptions, import_capture};
use selector_facts::FactSnapshot;
use selector_types::*;
use std::path::PathBuf;

const REGISTRATION: &str = "org/scalatest/funsuite/AnyFunSuiteLike#test().";
const POSITION: &str = "org/scalactic/source/Position.here().";
fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/position-macro")
}
fn capture(workers: usize) -> FactSnapshot {
    import_capture(
        &fixture().join("documents.jsonl"),
        Some(&fixture().join("syntax.jsonl")),
        &ExtractOptions {
            workers,
            ..Default::default()
        },
    )
    .unwrap()
}

#[test]
fn genuine_registration_consumes_its_position_after_written_providers_before_registering() {
    let facts = capture(1);
    let registrations: Vec<_> = facts
        .operations
        .iter()
        .enumerate()
        .filter(|(_, op)| op.opcode == Opcode::RegisterTest)
        .collect();
    assert_eq!(registrations.len(), 3);
    for (index, registration) in registrations {
        assert_eq!(facts.symbol_name(registration.target), REGISTRATION);
        let arguments = &facts.operands[registration.arguments.range()];
        let slot = callback_argument_slot(registration.flags).expect("exact callback certificate");
        assert!(slot < arguments.len());
        let body = &facts.bodies[registration.body.index()];
        let providers: Vec<_> = facts.operations[body.operations.range()]
            .iter()
            .enumerate()
            .filter(|(_, op)| {
                op.opcode == Opcode::Unknown
                    && op.target != SymbolId::NONE
                    && facts.symbol_name(op.target) == POSITION
                    && op.span == registration.span
                    && op.flags & OP_MACRO_EXPANSION != 0
            })
            .map(|(offset, op)| (body.operations.start as usize + offset, op))
            .collect();
        assert_eq!(
            providers.len(),
            1,
            "one genuine implicit provider for this full written call"
        );
        let (provider_index, provider) = providers[0];
        assert!(
            provider_index < index,
            "implicit provider must execute before registration"
        );
        assert_eq!(arguments.last(), Some(&provider.dest));
        assert_eq!(
            arguments
                .iter()
                .filter(|&&value| value == provider.dest)
                .count(),
            1
        );
        let (callback_index, callback) = facts.operations[body.operations.range()]
            .iter()
            .enumerate()
            .find(|(_, op)| op.opcode == Opcode::BindCallback && op.dest == arguments[slot])
            .map(|(offset, op)| (body.operations.start as usize + offset, op))
            .unwrap();
        assert!(
            callback_index < provider_index,
            "written callback creation precedes its later implicit clause"
        );
        assert!(
            facts
                .bodies
                .iter()
                .any(|body| body.symbol == callback.target && body.flags & BODY_DEFERRED != 0),
            "completing the registration does not eagerly execute its test body"
        );
        let (label_index, label) = facts.operations[body.operations.range()]
            .iter()
            .enumerate()
            .find(|(_, op)| op.opcode == Opcode::Constant && op.dest == arguments[0])
            .map(|(offset, op)| (body.operations.start as usize + offset, op))
            .unwrap();
        assert!(registration.span.contains(label.span));
        assert!(
            label_index < callback_index
                && callback_index < provider_index
                && provider_index < index
        );
        assert_eq!(
            provider.opcode,
            Opcode::Unknown,
            "scheduling does not discharge the Position macro's native provider authority"
        );
    }
    let log = std::fs::read_to_string(fixture().join("scalatest.log")).unwrap();
    assert!(log.contains("Total number of tests run: 3"));
    assert!(log.contains("Tests: succeeded 3, failed 0"));
}

#[test]
fn registration_completion_keeps_opaque_macro_effects_and_is_worker_deterministic() {
    let one = capture(1);
    let four = capture(4);
    let temp = tempfile::tempdir().unwrap();
    let first = temp.path().join("one.bin");
    let second = temp.path().join("four.bin");
    selector_facts::codec::write(&first, &one).unwrap();
    selector_facts::codec::write(&second, &four).unwrap();
    assert_eq!(
        std::fs::read(first).unwrap(),
        std::fs::read(second).unwrap()
    );
    // This compiler capture does not emit a MacroExpansionTree for the user
    // macro. Its exact ordinary call must remain, with the real callee boundary.
    let opaque = one
        .find_symbol("positioncase/UserMacros.effect().")
        .unwrap();
    assert!(
        one.operations.iter().any(
            |op| matches!(op.opcode, Opcode::Call | Opcode::VirtualCall) && op.target == opaque
        )
    );
    let graph = selector_graph_build::build(&one, &Default::default()).unwrap();
    let opaque_node = graph.node_for_symbol(opaque).unwrap();
    let options = selector_solve::SolveOptions {
        workers: 1,
        memory_budget_bytes: 64 * 1024 * 1024,
        max_contexts: 1000,
        max_steps: 10_000,
        execution_roots: Some(
            vec![selector_solve::ExecutionRoot {
                node: opaque_node,
                receiver: one.symbols[opaque.index()].owner,
            }]
            .into(),
        ),
        ..Default::default()
    };
    let mut session = selector_solve::QuerySession::new(&one, &graph, &options).unwrap();
    let result = session.analyze(&[]).unwrap();
    assert_ne!(result.completion, Completion::ResourceLimited);
    assert!(result.guarded_roots.contains(&opaque_node));
    assert!(
        session
            .first_runtime_issue_sites()
            .any(|(_, node, site)| node == opaque_node
                && site.reason == selector_issue::RuntimeIssueReason::MissingExecutableBody),
        "the actual source macro call has no admitted runtime expansion body"
    );
    assert!(
        one.issues
            .iter()
            .any(|issue| issue.kind == IssueKind::UnknownExecution
                && one.text(issue.detail)
                    == "compiler macro expansion runtime effects require explicit model")
    );
    let log = std::fs::read_to_string(fixture().join("execution.log")).unwrap();
    assert!(log.contains("position-effects:0:0"));
    assert!(log.contains("user-macro-effects:0:1"));
    assert!(log.contains("assertion-argument-effects:1:11"));
}
