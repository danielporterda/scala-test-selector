//! Actual Scala compiler and JVM evidence for ordered same-instance super calls.
use selector_extract::{ExtractOptions, import_capture};
use selector_types::*;
use serde_json::Value;
use std::path::PathBuf;

#[test]
fn genuine_compiler_super_calls_preserve_receiver_qualifier_and_parent_order() {
    let fixture = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/trait-super");
    let expected: Value =
        serde_json::from_slice(&std::fs::read(fixture.join("expected.json")).unwrap()).unwrap();
    assert_eq!(
        std::fs::read_to_string(fixture.join("execution.log"))
            .unwrap()
            .trim(),
        "plain:2,qualified:1"
    );
    let facts = import_capture(
        &fixture.join("documents.jsonl"),
        Some(&fixture.join("syntax.jsonl")),
        &ExtractOptions {
            workers: 2,
            ..Default::default()
        },
    )
    .unwrap();
    for case in expected["calls"].as_array().unwrap() {
        let owner = facts.find_symbol(case["owner"].as_str().unwrap()).unwrap();
        let body = facts
            .bodies
            .iter()
            .find(|body| body.symbol == owner)
            .unwrap();
        let operations = &facts.operations[body.operations.range()];
        let calls: Vec<_> = operations
            .iter()
            .filter(|op| op.flags & OP_SUPER != 0)
            .collect();
        assert_eq!(calls.len(), 1, "one actual super call in {}", case["owner"]);
        let call = calls[0];
        assert!(matches!(call.opcode, Opcode::Call | Opcode::VirtualCall));
        assert_eq!(
            facts.symbol_name(call.target),
            case["target"].as_str().unwrap()
        );
        assert_eq!(call.a, ValueId(0), "super preserves the current instance");
        assert_eq!(
            call.flags & OP_QUALIFIED_SUPER != 0,
            case["qualified"].as_bool().unwrap()
        );
        assert!(
            !operations
                .iter()
                .any(|operation| operation.opcode == Opcode::Unknown),
            "compiler-bound super receiver must not become an unknown value"
        );
    }
    for (name, parents) in expected["ordered_parents"].as_object().unwrap() {
        let class = facts.find_symbol(name).unwrap();
        let record = &facts.symbols[class.index()];
        assert_ne!(record.flags & SYMBOL_SCALA_PARENTS_COMPLETE, 0);
        let signature: Value = serde_json::from_str(facts.text(record.signature)).unwrap();
        let actual = signature["class_signature"]["parents"]
            .as_array()
            .unwrap()
            .iter()
            .map(|parent| parent["type_ref"]["symbol"].clone())
            .collect::<Vec<_>>();
        assert_eq!(
            &Value::Array(actual),
            parents,
            "compiler parent order must remain intact"
        );
    }
}
