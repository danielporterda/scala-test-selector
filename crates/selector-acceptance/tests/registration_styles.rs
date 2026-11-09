//! Actual ScalaTest 3.2.19 async/fixture/tagged/flat registration overloads.
use selector_extract::{ExtractOptions, import_capture};
use selector_facts::FactSnapshot;
use selector_types::*;
use std::path::PathBuf;
fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/registration-styles")
}
fn captured() -> FactSnapshot {
    import_capture(
        &fixture().join("documents.jsonl"),
        Some(&fixture().join("syntax.jsonl")),
        &ExtractOptions {
            workers: 2,
            catalogue: Some(fixture().join("catalogue.json")),
            ..Default::default()
        },
    )
    .unwrap()
}
#[test]
fn all_genuine_async_fixture_tagged_and_flat_registrations_reach_their_source_body() {
    let facts = captured();
    assert_eq!(facts.suites.len(), 9);
    let graph = selector_graph_build::build(
        &facts,
        &selector_graph_build::BuildOptions {
            workers: 2,
            include_models: true,
        },
    )
    .unwrap();
    let changed = graph
        .node_for_symbol(
            facts
                .find_symbol("registrationcase/Effects.changed().")
                .unwrap(),
        )
        .unwrap();
    let result = selector_solve::analyze(
        &facts,
        &graph,
        &[changed],
        &selector_solve::SolveOptions {
            workers: 2,
            ..Default::default()
        },
    )
    .unwrap();
    let missing: Vec<_> = facts
        .suites
        .iter()
        .filter_map(|suite| {
            let node = graph.node_for_symbol(suite.symbol).unwrap();
            (!result.contains(node)).then(|| facts.text(suite.name))
        })
        .collect();
    assert!(
        missing.is_empty(),
        "missing registered source bodies: {missing:?}"
    );
    assert!(
        !result.obligations.is_empty(),
        "external framework effects remain explicitly unadmitted"
    );
}
#[test]
fn fixture_function_factory_remains_eager_while_the_registered_function_is_deferred() {
    let facts = captured();
    let suite = facts
        .find_symbol("registrationcase/FixtureFunctionSuite#")
        .unwrap();
    let factory = facts
        .find_symbol("registrationcase/FixtureFunctionSuite#make().")
        .unwrap();
    let constructor = facts
        .bodies
        .iter()
        .find(|body| body.symbol == suite && body.flags & BODY_INITIALIZER != 0)
        .unwrap();
    let operations = &facts.operations[constructor.operations.range()];
    let factory_call = operations
        .iter()
        .find(|op| op.target == factory)
        .expect("fixture Function1 factory is evaluated at registration");
    let registration = operations
        .iter()
        .find(|op| op.opcode == Opcode::RegisterTest)
        .expect("registration is an explicit compiler-bound effect");
    assert_eq!(
        facts.operands[registration.arguments.range()][0],
        factory_call.dest
    );
    assert!(
        !facts.bodies.iter().any(|body| facts
            .symbol_name(body.symbol)
            .starts_with("@framework-byname:")
            && facts.symbols[body.symbol.index()].owner == suite),
        "a Function1 argument must not acquire an extra by-name wrapper"
    );
    let factory_body = facts
        .bodies
        .iter()
        .find(|body| body.symbol == factory)
        .unwrap();
    assert_eq!(factory_body.flags & BODY_DEFERRED, 0);
    let callback = facts.operations[factory_body.operations.range()]
        .iter()
        .find(|op| op.opcode == Opcode::BindCallback)
        .unwrap();
    assert_ne!(
        facts
            .bodies
            .iter()
            .find(|body| body.symbol == callback.target)
            .unwrap()
            .flags
            & BODY_DEFERRED,
        0
    );
}
#[test]
fn independent_jvm_run_proves_factory_evaluation_and_nine_registered_tests() {
    let log = std::fs::read_to_string(fixture().join("execution.log")).unwrap();
    let receipt: serde_json::Value =
        serde_json::from_slice(&std::fs::read(fixture().join("manifest.json")).unwrap()).unwrap();
    assert_eq!(receipt["jvm_witness"].as_str(), Some(log.as_str()));
    assert_eq!(
        log.lines().next(),
        Some("factory:FixtureFunctionSuite:made=7:observed=0")
    );
    let suites: Vec<_> = log
        .lines()
        .filter(|line| line.starts_with("suite:"))
        .collect();
    assert_eq!(suites.len(), 9);
    assert!(
        suites
            .iter()
            .all(|line| line.ends_with(":tests=1:observed=41"))
    );
}
