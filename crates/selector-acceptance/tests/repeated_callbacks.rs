//! Genuine repeated callback ABI packing and explicitly marked sequence spread.
//! Sequence element reads are may-values; these controls do not claim index
//! precision, collection traversal completeness or an external purity contract.
use selector_extract::{ExtractOptions, import_capture};
use selector_facts::{BodyRecord, FactSnapshot, OperationRecord};
use selector_types::*;
use std::path::{Path, PathBuf};

fn directory() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/repeated-callbacks")
}
fn captured_from(syntax: &Path) -> FactSnapshot {
    import_capture(
        &directory().join("all-documents.jsonl"),
        Some(syntax),
        &ExtractOptions {
            workers: 2,
            ..Default::default()
        },
    )
    .unwrap()
}
fn captured() -> FactSnapshot {
    captured_from(&directory().join("all-syntax.jsonl"))
}
fn body<'a>(facts: &'a FactSnapshot, symbol: &str) -> &'a BodyRecord {
    let symbol = facts.find_symbol(symbol).unwrap();
    facts
        .bodies
        .iter()
        .find(|body| body.symbol == symbol)
        .unwrap()
}
fn ops<'a>(facts: &'a FactSnapshot, body: &BodyRecord) -> &'a [OperationRecord] {
    &facts.operations[body.operations.range()]
}
fn call<'a>(facts: &'a FactSnapshot, body: &BodyRecord, name: &str) -> &'a OperationRecord {
    let matching: Vec<_> = ops(facts, body)
        .iter()
        .filter(|op| {
            matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
                && facts.symbol_name(op.target) == name
        })
        .collect();
    assert_eq!(
        matching.len(),
        1,
        "{name}: {:?}",
        ops(facts, body)
            .iter()
            .map(|op| (
                op.opcode,
                facts.symbol_name(op.target),
                op.dest,
                op.arguments.len
            ))
            .collect::<Vec<_>>()
    );
    matching[0]
}

#[test]
fn independent_jvm_proves_provider_order_spread_and_deferred_pack_capture() {
    for (mode, expected) in [
        (
            "flat",
            "flat:provider:a,provider:b,aggregate,call:a,call:b:3\n",
        ),
        ("empty", "empty-created:\n"),
        (
            "spread",
            "spread:provider:a,provider:b,aggregate,call:a,call:b:3\n",
        ),
        (
            "mixed",
            "mixed:provider:a,provider:b,mixed,call:a,call:b,prefix:10\n",
        ),
        (
            "captured",
            "captured-created:provider:a,provider:b\ncaptured-invoked:provider:a,provider:b,aggregate,call:a,call:b:3\n",
        ),
        (
            "dormant",
            "dormant-created:\ndormant-invoked:provider:dormant-a,provider:dormant-b,aggregate,call:dormant-a,call:dormant-b:9\n",
        ),
    ] {
        assert_eq!(
            std::fs::read_to_string(directory().join(format!("jvm-{mode}.stdout"))).unwrap(),
            expected
        );
    }
}

#[test]
fn actual_compiler_signature_declares_one_repeated_formal_and_ast_marks_only_spread() {
    let metadata: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(directory().join("external-signatures.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(metadata["jdk_object_in_index"], false);
    for method in metadata["methods"].as_array().unwrap() {
        let formals = method["formals"].as_array().unwrap();
        if method["symbol"] == "repeatedcallbacks/Api#mixed()." {
            assert_eq!(formals.len(), 2);
            assert_eq!(formals[0]["by_name"], true);
            assert_eq!(formals[0]["repeated"], false);
        } else {
            assert_eq!(formals.len(), 1);
        }
        let last = formals.last().unwrap();
        assert_eq!(last["repeated"], true);
        assert_eq!(last["by_name"], false);
    }
    let syntax: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(directory().join("caller-syntax.jsonl")).unwrap(),
    )
    .unwrap();
    let spread: Vec<_> = syntax["ast"]["call_sites"]
        .as_array()
        .unwrap()
        .iter()
        .flat_map(|site| site["arguments"].as_array().unwrap())
        .filter(|argument| argument["repeated_spread"] == true)
        .collect();
    assert_eq!(spread.len(), 1);
    assert!(spread[0]["expression_end"].as_u64().unwrap() < spread[0]["end"].as_u64().unwrap());
    assert_eq!(spread[0]["expression_form"], "reference");
}

#[test]
fn flat_actuals_are_one_ordered_pack_before_the_single_repeated_formal_call() {
    let facts = captured();
    let parent = body(&facts, "repeatedcallbacks/Calls#flat().");
    let operations = ops(&facts, parent);
    let providers: Vec<_> = operations
        .iter()
        .filter(|op| {
            matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
                && facts.symbol_name(op.target) == "repeatedcallbacks/Calls#provider()."
        })
        .collect();
    assert_eq!(providers.len(), 2);
    let target = call(&facts, parent, "repeatedcallbacks/Api#aggregate().");
    assert_eq!(
        target.arguments.len, 1,
        "repeated ABI has one sequence argument"
    );
    let packed = facts.operands[target.arguments.start as usize];
    let pack = operations
        .iter()
        .find(|op| op.opcode == Opcode::PackSequence && op.dest == packed)
        .unwrap();
    assert_eq!(
        &facts.operands[pack.arguments.range()],
        &[providers[0].dest, providers[1].dest]
    );
    let index = |op: &OperationRecord| {
        operations
            .iter()
            .position(|row| std::ptr::eq(row, op))
            .unwrap()
    };
    assert!(
        index(providers[0]) < index(providers[1])
            && index(providers[1]) < index(pack)
            && index(pack) < index(target)
    );
    assert!(
        facts.issues.iter().any(|issue| issue.file == parent.file
            && issue.symbol == parent.symbol
            && issue.kind == IssueKind::UnknownExecution
            && facts.text(issue.detail)
                == "repeated argument container backend effects remain unverified"),
        "source ABI packing alone cannot assert runtime-wrapper effect completeness"
    );
}

#[test]
fn mixed_byname_formal_stays_a_thunk_while_repeated_providers_are_strict() {
    let facts = captured();
    let parent = body(&facts, "repeatedcallbacks/Calls#mixedCall().");
    let operations = ops(&facts, parent);
    let target = call(&facts, parent, "repeatedcallbacks/Api#mixed().");
    assert_eq!(target.arguments.len, 2);
    let arguments = &facts.operands[target.arguments.range()];
    let deferred = operations
        .iter()
        .find(|op| op.opcode == Opcode::BindCallback && op.dest == arguments[0])
        .unwrap();
    let thunk = body(&facts, facts.symbol_name(deferred.target));
    call(&facts, thunk, "repeatedcallbacks/Calls#prefix().");
    assert!(
        !operations
            .iter()
            .any(|op| facts.symbol_name(op.target) == "repeatedcallbacks/Calls#prefix().")
    );
    let pack = operations
        .iter()
        .find(|op| op.opcode == Opcode::PackSequence && op.dest == arguments[1])
        .unwrap();
    assert_eq!(pack.arguments.len, 2);
    let providers: Vec<_> = operations
        .iter()
        .filter(|op| {
            matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
                && facts.symbol_name(op.target) == "repeatedcallbacks/Calls#provider()."
        })
        .collect();
    assert_eq!(providers.len(), 2);
    assert_eq!(
        &facts.operands[pack.arguments.range()],
        &[providers[0].dest, providers[1].dest]
    );
}

#[test]
fn repeated_pack_is_captured_as_one_value_and_empty_pack_is_not_top() {
    let facts = captured();
    for (name, length) in [("captured", 2), ("empty", 0)] {
        let parent = body(&facts, &format!("repeatedcallbacks/Calls#{name}()."));
        let target = call(&facts, parent, "repeatedcallbacks/Api#store().");
        assert_eq!(target.arguments.len, 1);
        let pack = ops(&facts, parent)
            .iter()
            .find(|op| {
                op.opcode == Opcode::PackSequence
                    && op.dest == facts.operands[target.arguments.start as usize]
            })
            .unwrap();
        assert_eq!(pack.arguments.len, length);
        assert!(
            !ops(&facts, parent)
                .iter()
                .any(|op| op.opcode == Opcode::InvokeCallback)
        );
    }
    let store = body(&facts, "repeatedcallbacks/Api#store().");
    let parameter = ops(&facts, store)
        .iter()
        .find(|op| op.opcode == Opcode::Parameter && op.flags & 1 == 0)
        .unwrap();
    let callback = ops(&facts, store)
        .iter()
        .find(|op| op.opcode == Opcode::BindCallback)
        .unwrap();
    assert!(facts.operands[callback.arguments.range()].contains(&parameter.dest));
    let deferred = body(&facts, facts.symbol_name(callback.target));
    let aggregate = call(&facts, deferred, "repeatedcallbacks/Api#aggregate().");
    assert_eq!(aggregate.arguments.len, 1);
    assert!(
        !ops(&facts, deferred)
            .iter()
            .any(|op| op.opcode == Opcode::PackSequence),
        "spread forwards the captured sequence rather than nesting it"
    );
}

#[test]
fn legacy_missing_spread_proof_cannot_silently_reinterpret_sequence_as_one_element() {
    // Labeled normalized AST perturbation, not an alternative compiler result.
    let mut rows: Vec<serde_json::Value> =
        std::fs::read_to_string(directory().join("all-syntax.jsonl"))
            .unwrap()
            .lines()
            .map(|line| serde_json::from_str(line).unwrap())
            .collect();
    let mut removed = 0;
    for row in &mut rows {
        for site in row["ast"]["call_sites"].as_array_mut().unwrap() {
            for argument in site["arguments"].as_array_mut().unwrap() {
                if argument["repeated_spread"] == true {
                    argument.as_object_mut().unwrap().remove("repeated_spread");
                    removed += 1;
                }
            }
        }
    }
    assert!(
        removed >= 2,
        "caller and library captured spreads are explicit"
    );
    let temporary = tempfile::tempdir().unwrap();
    let syntax = temporary.path().join("legacy-syntax.jsonl");
    std::fs::write(
        &syntax,
        rows.into_iter()
            .map(|row| serde_json::to_string(&row).unwrap() + "\n")
            .collect::<String>(),
    )
    .unwrap();
    let facts = captured_from(&syntax);
    let spread = body(&facts, "repeatedcallbacks/Calls#spread().");
    assert!(
        facts
            .issues
            .iter()
            .any(|issue| issue.file == spread.file && issue.symbol == spread.symbol
                && issue.kind == IssueKind::UnknownExecution
                && facts.text(issue.detail).contains("repeated actual evaluations are retained without an exact argument-container recipe")),
        "the missing spread proof itself must remain a scoped execution frontier"
    );
}
