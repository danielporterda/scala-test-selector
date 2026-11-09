//! Genuine ScalaTest registration/lifecycle fixtures, compared with independently
//! executed JVM observations and the named legacy semantic regression families.
use selector_extract::{ExtractOptions, import_capture};
use selector_facts::FactSnapshot;
use selector_graph::ProgramGraph;
use selector_types::*;
use std::path::PathBuf;

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/registration-smoke")
}
fn captured(workers: usize) -> FactSnapshot {
    import_capture(
        &fixture().join("documents.jsonl"),
        Some(&fixture().join("syntax.jsonl")),
        &ExtractOptions {
            workers,
            catalogue: Some(fixture().join("catalogue.json")),
            ..Default::default()
        },
    )
    .unwrap()
}
fn source_owner(facts: &FactSnapshot, mut symbol: SymbolId) -> &str {
    for _ in 0..128 {
        let record = facts.symbols[symbol.index()];
        if matches!(record.kind, 10 | 13 | 14) || record.owner.is_none() {
            return facts.symbol_name(symbol);
        }
        symbol = record.owner;
    }
    panic!("cyclic owner")
}
fn graph(facts: &FactSnapshot, workers: usize) -> ProgramGraph {
    selector_graph_build::build(
        facts,
        &selector_graph_build::BuildOptions {
            workers,
            include_models: true,
        },
    )
    .unwrap()
}

#[test]
fn real_registration_arguments_are_deferred_recipes_and_nested_callbacks_are_distinct() {
    let facts = captured(2);
    assert_eq!(facts.suites.len(), 11);
    let changed = facts
        .find_symbol("registrationcase/Effects.changed().")
        .unwrap();
    for class in [
        "DirectSuite",
        "StoredSuite",
        "InvokedSuite",
        "OpaqueSuite",
        "WordSuite",
        "NestedWordSuite",
    ] {
        let owner = format!("registrationcase/{class}#");
        let calls: Vec<_> = facts
            .operations
            .iter()
            .filter(|op| {
                op.target == changed
                    && source_owner(&facts, facts.bodies[op.body.index()].symbol) == owner
            })
            .collect();
        assert_eq!(calls.len(), 1, "{class}: {calls:?}");
        assert_ne!(
            facts.bodies[calls[0].body.index()].flags & BODY_DEFERRED,
            0,
            "registered executable work must not belong to eager construction: {class}"
        );
    }
    let stored = facts
        .bodies
        .iter()
        .find(|body| {
            facts
                .symbol_name(body.symbol)
                .starts_with("@framework-byname:")
                && source_owner(&facts, body.symbol) == "registrationcase/StoredSuite#"
        })
        .expect("outer registration recipe");
    let binding = facts
        .operations
        .iter()
        .find(|op| {
            op.opcode == Opcode::BindCallback
                && source_owner(&facts, facts.bodies[op.body.index()].symbol)
                    == "registrationcase/StoredSuite#"
                && !facts
                    .symbol_name(op.target)
                    .starts_with("@framework-byname:")
        })
        .expect("stored nested callback retains a separate binding");
    assert_ne!(binding.target, stored.symbol);
    assert!(
        !facts.operations[stored.operations.range()]
            .iter()
            .any(|op| op.target == changed),
        "stored closure body must not be flattened into the registered body"
    );
}

#[test]
fn registered_and_lifecycle_work_respects_concrete_suite_receivers_and_dormant_callbacks() {
    let facts = captured(2);
    let graph = graph(&facts, 2);
    let changed = facts
        .find_symbol("registrationcase/Effects.changed().")
        .unwrap();
    let changed = graph.node_for_symbol(changed).unwrap();
    let options = selector_solve::SolveOptions {
        workers: 2,
        ..Default::default()
    };
    let result = selector_solve::analyze(&facts, &graph, &[changed], &options).unwrap();
    let candidate: Vec<_> = facts
        .suites
        .iter()
        .filter_map(|suite| {
            let node = graph.node_for_symbol(suite.symbol).unwrap();
            result
                .contains(node)
                .then(|| facts.text(suite.name).to_owned())
        })
        .collect();
    assert_eq!(
        candidate,
        [
            "DirectSuite",
            "InvokedSuite",
            "InheritedSuite",
            "HookSuite",
            "FixtureSuite",
            "WordSuite",
            "NestedWordSuite"
        ]
        .map(|name| format!("registrationcase.{name}")),
        "guarded roots: {:?}",
        result.guarded_roots
    );
    let opaque = facts.find_symbol("registrationcase/OpaqueSuite#").unwrap();
    assert!(
        result
            .guarded_roots
            .contains(&graph.node_for_symbol(opaque).unwrap()),
        "opaque callback sink remains guarded"
    );
}

#[test]
fn explicit_compiler_parameter_modes_override_external_framework_fallback() {
    let rows: Vec<serde_json::Value> = std::fs::read_to_string(fixture().join("documents.jsonl"))
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    for by_name in [false, true] {
        // Named synthetic metadata control: only the external declarations are
        // added; source, original occurrences and source-bound syntax are exact.
        let mut rows = rows.clone();
        let row = rows
            .iter_mut()
            .find(|row| row["path"] == "src/registrationcase/Suites.scala")
            .unwrap();
        let symbols = row["document"]["symbols"].as_array_mut().unwrap();
        let method = "org/scalatest/funsuite/AnyFunSuiteLike#test().";
        symbols.extend([
            serde_json::json!({"symbol":method,"kind":3,"signature":{"method_signature":{
                "parameter_lists":[{"symlinks":[format!("{method}(name)")]},{"symlinks":[format!("{method}(body)")]}],
                "return_type":{"type_ref":{"symbol":"scala/Unit#"}}
            }}}),
            serde_json::json!({"symbol":format!("{method}(name)"),"kind":8,"signature":{"value_signature":{"tpe":{"type_ref":{"symbol":"java/lang/String#"}}}}}),
            serde_json::json!({"symbol":format!("{method}(body)"),"kind":8,"signature":{"value_signature":{"tpe": if by_name {
                serde_json::json!({"by_name_type":{"tpe":{"type_ref":{"symbol":"scala/Any#"}}}})
            } else { serde_json::json!({"type_ref":{"symbol":"scala/Any#"}}) }}}}),
        ]);
        let directory = tempfile::tempdir().unwrap();
        let input = directory.path().join("documents.jsonl");
        let bytes = rows
            .iter()
            .map(|row| serde_json::to_string(row).unwrap() + "\n")
            .collect::<String>();
        std::fs::write(&input, bytes).unwrap();
        let facts = import_capture(
            &input,
            Some(&fixture().join("syntax.jsonl")),
            &ExtractOptions {
                workers: 1,
                ..Default::default()
            },
        )
        .unwrap();
        let changed = facts
            .find_symbol("registrationcase/Effects.changed().")
            .unwrap();
        let call = facts
            .operations
            .iter()
            .find(|op| {
                op.target == changed
                    && source_owner(&facts, facts.bodies[op.body.index()].symbol)
                        == "registrationcase/DirectSuite#"
            })
            .unwrap();
        let body = facts.bodies[call.body.index()];
        assert_eq!(body.flags & BODY_DEFERRED != 0, by_name);
        assert!(
            !facts
                .symbol_name(body.symbol)
                .starts_with("@framework-byname:"),
            "declared mode must not use fallback evidence"
        );
    }
}

#[test]
fn independently_run_jvm_witness_contains_eleven_deferred_single_test_suites() {
    let receipt: serde_json::Value =
        serde_json::from_slice(&std::fs::read(fixture().join("manifest.json")).unwrap()).unwrap();
    let log = std::fs::read_to_string(fixture().join("execution.log")).unwrap();
    assert_eq!(receipt["jvm_witness"].as_str(), Some(log.as_str()));
    assert_eq!(log.lines().count(), 11);
    for (class, observed) in [
        ("DirectSuite", 41),
        ("StoredSuite", 7),
        ("InvokedSuite", 41),
        ("OpaqueSuite", 7),
        ("InheritedSuite", 41),
        ("InheritedSibling", 7),
        ("HookSuite", 41),
        ("HookSibling", 7),
        ("FixtureSuite", 41),
        ("WordSuite", 41),
        ("NestedWordSuite", 41),
    ] {
        assert!(
            log.lines().any(|line| line
                == format!("suite:registrationcase.{class}:tests=1:observed={observed}"))
        );
    }
    assert_eq!(
        receipt["framework_bodies_admitted"], false,
        "this source behavior fixture must retain unresolved external framework obligations"
    );
}
