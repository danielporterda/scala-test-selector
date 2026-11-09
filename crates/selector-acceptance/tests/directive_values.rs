//! Genuine nullary getter / implicit conversion / returned Function1 modes.
//! All-source input has actual library source bodies; caller-only input does
//! not acquire that executable authority from signature-only metadata.
use selector_extract::{ExtractOptions, import_capture};
use selector_facts::{BodyRecord, FactSnapshot, OperationRecord};
use selector_types::*;
use std::path::PathBuf;

fn directory() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/directive-values")
}
fn captured(all: bool) -> FactSnapshot {
    let prefix = if all { "all" } else { "caller" };
    import_capture(
        &directory().join(format!("{prefix}-documents.jsonl")),
        Some(&directory().join(format!("{prefix}-syntax.jsonl"))),
        &ExtractOptions {
            workers: 2,
            ..Default::default()
        },
    )
    .unwrap()
}
fn body<'a>(facts: &'a FactSnapshot, name: &str) -> &'a BodyRecord {
    let symbol = facts
        .find_symbol(&format!("directivevalues/Calls#{name}()."))
        .unwrap();
    facts
        .bodies
        .iter()
        .find(|body| body.symbol == symbol)
        .unwrap()
}
fn ops<'a>(facts: &'a FactSnapshot, body: &BodyRecord) -> &'a [OperationRecord] {
    &facts.operations[body.operations.range()]
}
fn target<'a>(
    facts: &'a FactSnapshot,
    body: &BodyRecord,
    name: &str,
) -> (usize, &'a OperationRecord) {
    let symbol = format!("directivevalues/Api#{name}().");
    let matches: Vec<_> = ops(facts, body)
        .iter()
        .enumerate()
        .filter(|(_, op)| {
            matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
                && facts.symbol_name(op.target) == symbol
        })
        .collect();
    assert_eq!(
        matches.len(),
        1,
        "{symbol}: {:?}",
        ops(facts, body)
            .iter()
            .map(|op| (
                op.opcode,
                facts.symbol_name(op.target),
                op.dest,
                op.a,
                op.arguments.len
            ))
            .collect::<Vec<_>>()
    );
    matches[0]
}
fn bound<'a>(
    facts: &'a FactSnapshot,
    operations: &[OperationRecord],
    value: ValueId,
) -> &'a BodyRecord {
    let binding = operations
        .iter()
        .find(|op| op.opcode == Opcode::BindCallback && op.dest == value)
        .unwrap();
    facts
        .bodies
        .iter()
        .find(|body| body.symbol == binding.target)
        .unwrap()
}

#[test]
fn independent_jvm_proves_strict_byname_getter_and_deferred_function_order() {
    for (mode, expected) in [
        ("active", "active:get,convert,invoke,run,inner:42\n"),
        (
            "strict",
            "strict:strict-get,strict-convert,strict-inner,strict-invoke,strict-run:43\n",
        ),
        (
            "deferred",
            "deferred:deferred-convert,deferred-invoke,deferred-get,deferred-run,deferred-inner:44\n",
        ),
        (
            "constructed",
            "created:get,convert\ninvoked:get,convert,invoke,run,supplied:46\n",
        ),
        (
            "dormant",
            "dormant-created:\ndormant-invoked:get,convert,invoke,run,dormant-inner:45\n",
        ),
    ] {
        assert_eq!(
            std::fs::read_to_string(directory().join(format!("jvm-{mode}.stdout"))).unwrap(),
            expected
        );
    }
}

#[test]
fn compiler_scala_metadata_distinguishes_nullary_strict_and_byname_modes() {
    let data: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(directory().join("external-signatures.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(data["jdk_object_in_index"], false);
    let methods = data["methods"].as_array().unwrap();
    let method = |name: &str| {
        methods
            .iter()
            .find(|m| m["symbol"] == format!("directivevalues/Api#{name}()."))
            .unwrap()
    };
    assert!(method("get")["formals"].as_array().unwrap().is_empty());
    assert_eq!(method("convert")["formals"][0]["by_name"], false);
    assert_eq!(method("deferredConvert")["formals"][0]["by_name"], true);
    let raw = std::fs::read_to_string(directory().join("external-signatures.textproto")).unwrap();
    assert!(raw.contains("language: SCALA"));
    assert!(raw.contains("symbol: \"scala/Function1#\""));
    assert!(raw.contains("by_name_type {"));
    let library: serde_json::Value =
        std::fs::read_to_string(directory().join("all-documents.jsonl"))
            .unwrap()
            .lines()
            .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
            .find(|row| row["path"] == "definitions/directivevalues/Library.scala")
            .unwrap();
    let signature = |name: &str| {
        library["document"]["symbols"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["symbol"] == format!("directivevalues/Api#{name}()."))
            .unwrap()["signature"]["method_signature"]
            .clone()
    };
    assert!(
        signature("get")["parameter_lists"]
            .as_array()
            .is_none_or(|clauses| clauses.is_empty())
    );
    for (name, deferred) in [
        ("convert", true),
        ("strictConvert", false),
        ("deferredConvert", true),
    ] {
        let signature = signature(name);
        let returned = &signature["return_type"]["type_ref"];
        assert_eq!(returned["symbol"], "scala/Function1#");
        assert_eq!(
            returned["type_arguments"][0].get("by_name_type").is_some(),
            deferred
        );
    }
    let caller: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(directory().join("caller-documents.jsonl")).unwrap(),
    )
    .unwrap();
    assert!(
        !caller["document"]["symbols"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| row["symbol"]
                .as_str()
                .unwrap()
                .starts_with("directivevalues/Api#"))
    );
}

#[test]
fn nullary_getter_is_evaluated_once_before_conversion_and_deferred_inner() {
    let facts = captured(true);
    let active = body(&facts, "active");
    let (get_index, get) = target(&facts, active, "get");
    let (conversion_index, conversion) = target(&facts, active, "convert");
    assert!(get_index < conversion_index);
    assert_eq!(get.arguments.len, 0);
    assert_eq!(&facts.operands[conversion.arguments.range()], &[get.dest]);
    let operations = ops(&facts, active);
    let invoke = operations
        .iter()
        .find(|op| op.opcode == Opcode::InvokeCallback && op.a == conversion.dest)
        .unwrap();
    assert_eq!(invoke.arguments.len, 1);
    let callback = bound(
        &facts,
        operations,
        facts.operands[invoke.arguments.start as usize],
    );
    assert_ne!(callback.flags & BODY_DEFERRED, 0);
    assert!(
        ops(&facts, callback)
            .iter()
            .any(|op| facts.symbol_name(op.target) == "directivevalues/Effects.note().")
    );
    assert!(
        !operations
            .iter()
            .any(|op| facts.symbol_name(op.target) == "directivevalues/Effects.note().")
    );
}

#[test]
fn strict_function_argument_is_evaluated_in_the_caller_before_invocation() {
    let facts = captured(true);
    let strict = body(&facts, "strict");
    let operations = ops(&facts, strict);
    let (get_index, _) = target(&facts, strict, "strictGet");
    let (convert_index, conversion) = target(&facts, strict, "strictConvert");
    let inner = operations
        .iter()
        .position(|op| facts.symbol_name(op.target) == "directivevalues/Effects.note().")
        .unwrap();
    let invoke = operations
        .iter()
        .position(|op| op.opcode == Opcode::InvokeCallback && op.a == conversion.dest)
        .unwrap();
    assert!(
        get_index < convert_index && convert_index < inner && inner < invoke,
        "strict prefix/provider order: {:?}",
        operations
            .iter()
            .map(|op| (op.opcode, facts.symbol_name(op.target), op.dest, op.a))
            .collect::<Vec<_>>()
    );
    assert!(
        !operations
            .iter()
            .any(|op| op.opcode == Opcode::BindCallback)
    );
}

#[test]
fn byname_conversion_formal_defers_the_getter_without_reclassifying_the_inner() {
    let facts = captured(true);
    let parent = body(&facts, "deferredGetter");
    let operations = ops(&facts, parent);
    let (_, conversion) = target(&facts, parent, "deferredConvert");
    assert_eq!(conversion.arguments.len, 1);
    let getter = bound(
        &facts,
        operations,
        facts.operands[conversion.arguments.start as usize],
    );
    target(&facts, getter, "deferredGet");
    assert!(
        !operations
            .iter()
            .any(|op| facts.symbol_name(op.target) == "directivevalues/Api#deferredGet().")
    );
    let invoke = operations
        .iter()
        .find(|op| op.opcode == Opcode::InvokeCallback && op.a == conversion.dest)
        .unwrap();
    let inner = bound(
        &facts,
        operations,
        facts.operands[invoke.arguments.start as usize],
    );
    assert_ne!(getter.symbol, inner.symbol);
}

#[test]
fn dormant_function_creation_does_not_eagerly_execute_the_getter_or_inner() {
    let facts = captured(true);
    let parent = body(&facts, "dormant");
    let operations = ops(&facts, parent);
    assert!(!operations.iter().any(|op| matches!(
        op.opcode,
        Opcode::Call | Opcode::VirtualCall | Opcode::InvokeCallback
    )));
    let callback = operations
        .iter()
        .find(|op| op.opcode == Opcode::BindCallback)
        .unwrap();
    let deferred = facts
        .bodies
        .iter()
        .find(|body| body.symbol == callback.target)
        .unwrap();
    target(&facts, deferred, "get");
    target(&facts, deferred, "convert");
}

#[test]
fn caller_only_missing_mode_authority_retains_a_scoped_execution_guard() {
    let facts = captured(false);
    let parent = body(&facts, "active");
    assert!(
        facts
            .issues
            .iter()
            .any(|issue| issue.file == parent.file && issue.kind == IssueKind::UnknownExecution)
    );
    assert!(
        !facts
            .bodies
            .iter()
            .any(|body| facts.symbol_name(body.symbol) == "directivevalues/Api#convert().")
    );
}

#[test]
fn duplicate_same_prefix_ast_claim_cannot_certify_a_callable_value_mode() {
    // A normalized malformed-AST control, not compiler-emitted positive data.
    let mut rows: Vec<serde_json::Value> =
        std::fs::read_to_string(directory().join("all-syntax.jsonl"))
            .unwrap()
            .lines()
            .map(|line| serde_json::from_str(line).unwrap())
            .collect();
    let source =
        std::fs::read_to_string(directory().join("src/directivevalues/Calls.scala")).unwrap();
    let start = source.find("get {").unwrap() as u64;
    let row = rows
        .iter_mut()
        .find(|row| row["path"] == "src/directivevalues/Calls.scala")
        .unwrap();
    let values = row["ast"]["value_expressions"].as_array_mut().unwrap();
    let value = values
        .iter()
        .find(|value| {
            value["start"] == start && value["end"] == start + 3 && value["kind"] == "reference"
        })
        .unwrap()
        .clone();
    values.push(value);
    let temporary = tempfile::tempdir().unwrap();
    let path = temporary.path().join("duplicate-claim.jsonl");
    std::fs::write(
        &path,
        rows.iter()
            .map(|row| serde_json::to_string(row).unwrap() + "\n")
            .collect::<String>(),
    )
    .unwrap();
    let facts = import_capture(
        &directory().join("all-documents.jsonl"),
        Some(&path),
        &ExtractOptions::default(),
    )
    .unwrap();
    let parent = body(&facts, "active");
    assert!(
        facts
            .issues
            .iter()
            .any(|issue| issue.symbol == parent.symbol
                && issue.file == parent.file
                && issue.kind == IssueKind::UnknownExecution
                && facts.text(issue.detail).contains(
                    "callable value conversion lacks unique compiler parameter evaluation metadata"
                )),
        "a duplicate prefix claim must not be resolved by insertion order"
    );
}
