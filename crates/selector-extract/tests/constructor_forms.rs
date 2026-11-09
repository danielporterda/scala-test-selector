use selector_extract::{ExtractOptions, import_capture};
use selector_facts::{FactSnapshot, OperationRecord};
use selector_types::*;
use sha2::{Digest, Sha256};
use std::path::Path;

fn facts() -> FactSnapshot {
    let fixture =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/constructor-forms/base");
    import_capture(
        &fixture.join("documents.jsonl"),
        Some(&fixture.join("syntax.jsonl")),
        &ExtractOptions::default(),
    )
    .unwrap()
}
fn ops<'a>(facts: &'a FactSnapshot, symbol: &str) -> &'a [OperationRecord] {
    let body = facts
        .bodies
        .iter()
        .find(|body| facts.symbol_name(body.symbol) == symbol)
        .unwrap();
    &facts.operations[body.operations.range()]
}

#[test]
fn frozen_constructor_compiler_receipt_matches_every_retained_input() {
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/constructor-forms");
    let manifest: serde_json::Value =
        serde_json::from_slice(&std::fs::read(fixture.join("manifest.json")).unwrap()).unwrap();
    assert_eq!(manifest["compiler"], "Scala 2.13.18");
    assert_eq!(manifest["plugin"], "SemanticDB 4.15.2");
    for row in manifest["files"].as_array().unwrap() {
        let bytes = std::fs::read(fixture.join(row["path"].as_str().unwrap())).unwrap();
        assert_eq!(row["bytes"].as_u64().unwrap(), bytes.len() as u64);
        assert_eq!(
            row["sha256"].as_str().unwrap(),
            ContentHash(Sha256::digest(bytes).into()).to_string()
        );
    }
    for (key, path) in [
        (
            "generator_sha256",
            "../../tools/prepare_constructor_forms.py",
        ),
        (
            "capture_helper_sha256",
            "../../tools/prepare_source_annotations.py",
        ),
    ] {
        assert_eq!(
            manifest[key].as_str().unwrap(),
            ContentHash(Sha256::digest(std::fs::read(fixture.join(path)).unwrap()).into())
                .to_string()
        );
    }
}

#[test]
fn exact_zero_width_constructor_references_and_primary_entries_are_executable() {
    let facts = facts();
    let secondary = ops(&facts, "constructorforms/Secondary#`<init>`(+1).");
    assert!(secondary.iter().any(|op| op.opcode == Opcode::Call
        && facts.symbol_name(op.target) == "constructorforms/Secondary#`<init>`()."));
    assert!(!secondary.iter().any(|op| op.opcode == Opcode::Unknown));
    let primary = ops(&facts, "constructorforms/Secondary#`<init>`().");
    let initialize = primary
        .iter()
        .find(|op| op.opcode == Opcode::Initialize)
        .unwrap();
    assert_eq!(
        facts.symbol_name(initialize.target),
        "constructorforms/Secondary#"
    );
    assert_eq!(initialize.arguments.len, 1);
    // Declaring an overload never invokes it while the class initializes.
    assert!(
        !ops(&facts, "constructorforms/Secondary#").iter().any(|op| {
            matches!(op.opcode, Opcode::Call | Opcode::Initialize)
                && facts.symbol_name(op.target) == "constructorforms/Secondary#`<init>`(+1)."
        })
    );
}

#[test]
fn compiler_apply_and_default_getters_fill_only_omitted_slots() {
    let facts = facts();
    for (caller, getter) in [
        (
            "constructorforms/ApplyDefaultSuite#observed.",
            "constructorforms/Value.apply$default$1().",
        ),
        (
            "constructorforms/NewDefaultSuite#observed.",
            "constructorforms/Value.`<init>$default$1`().",
        ),
        (
            "constructorforms/CopyDefaultSuite#observed.",
            "constructorforms/Value#copy$default$1().",
        ),
    ] {
        let ops = ops(&facts, caller);
        assert!(
            ops.iter()
                .any(|op| op.opcode == Opcode::DefaultArgument
                    && facts.symbol_name(op.target) == getter),
            "{caller}"
        );
        assert!(
            !ops.iter().any(|op| op.opcode == Opcode::Unknown),
            "{caller}"
        );
    }
    for caller in [
        "constructorforms/ApplyExplicitSuite#observed.",
        "constructorforms/NewExplicitSuite#observed.",
        "constructorforms/CopyExplicitSuite#observed.",
    ] {
        assert!(
            !ops(&facts, caller)
                .iter()
                .any(|op| op.opcode == Opcode::DefaultArgument)
        );
    }
    let apply = ops(&facts, "constructorforms/ApplyExplicitSuite#observed.");
    assert!(apply.iter().any(|op| op.opcode == Opcode::Call
        && facts.symbol_name(op.target) == "constructorforms/Value.apply()."));
}

#[test]
fn class_initializer_retains_source_bound_parameter_accessors() {
    let facts = facts();
    let initial = ops(&facts, "constructorforms/Value#");
    let parameter = initial
        .iter()
        .find(|op| op.opcode == Opcode::Parameter)
        .unwrap();
    assert_eq!(
        facts.symbol_name(parameter.target),
        "constructorforms/Value#value."
    );
    let symbol = facts.symbols[parameter.target.index()];
    assert_eq!(symbol.properties & 1024, 1024);
    assert_eq!(symbol.flags & SYMBOL_DEFINED, SYMBOL_DEFINED);
    assert_eq!(facts.symbol_name(symbol.owner), "constructorforms/Value#");
}

#[test]
fn by_name_defaults_are_thunks_and_only_formal_reads_invoke_them() {
    let facts = facts();
    for (caller, getter) in [
        (
            "constructorforms/ByNameDefaultUsedSuite#observed.",
            "constructorforms/Defaults.force$default$1().",
        ),
        (
            "constructorforms/ByNameDefaultIgnoredSuite#observed.",
            "constructorforms/Defaults.ignore$default$1().",
        ),
    ] {
        let caller = ops(&facts, caller);
        assert!(
            caller
                .iter()
                .any(|op| op.opcode == Opcode::BindCallback
                    && facts.symbol_name(op.target) == getter)
        );
        assert!(!caller.iter().any(
            |op| op.opcode == Opcode::DefaultArgument && facts.symbol_name(op.target) == getter
        ));
    }
    assert!(
        ops(&facts, "constructorforms/Defaults.force().")
            .iter()
            .any(|op| op.opcode == Opcode::InvokeCallback)
    );
    assert!(
        !ops(&facts, "constructorforms/Defaults.ignore().")
            .iter()
            .any(|op| op.opcode == Opcode::InvokeCallback)
    );
}

#[test]
fn default_getter_receives_exact_preceding_clause_arguments() {
    let facts = facts();
    let body = ops(&facts, "constructorforms/Defaults.dependent$default$2().");
    let parameter = body
        .iter()
        .find(|op| op.opcode == Opcode::Parameter)
        .unwrap();
    assert!(
        body.iter()
            .any(|op| op.opcode == Opcode::Return && op.a == parameter.dest)
    );
    assert!(!body.iter().any(|op| op.opcode == Opcode::Unknown));
    let caller = ops(&facts, "constructorforms/DependentDefaultSuite#observed.");
    let prefix = caller
        .iter()
        .find(|op| facts.symbol_name(op.target) == "constructorforms/Effects.changed().")
        .unwrap();
    let default = caller
        .iter()
        .find(|op| op.opcode == Opcode::DefaultArgument)
        .unwrap();
    assert_eq!(&facts.operands[default.arguments.range()], &[prefix.dest]);
}

#[test]
fn missing_constructor_and_default_getter_proofs_remain_explicit_unknowns() {
    let fixture =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/constructor-forms/base");
    for remove_constructor in [true, false] {
        let temporary = tempfile::tempdir().unwrap();
        let mut rows = Vec::new();
        for line in std::fs::read_to_string(fixture.join("documents.jsonl"))
            .unwrap()
            .lines()
        {
            let mut row: serde_json::Value = serde_json::from_str(line).unwrap();
            if remove_constructor {
                row["document"]["occurrences"]
                    .as_array_mut()
                    .unwrap()
                    .retain(|occurrence| {
                        occurrence["role"] != 1
                            || !occurrence["symbol"].as_str().unwrap().contains("`<init>`")
                    });
            } else {
                row["document"]["symbols"]
                    .as_array_mut()
                    .unwrap()
                    .retain(|symbol| !symbol["symbol"].as_str().unwrap().contains("$default$"));
            }
            rows.push(serde_json::to_string(&row).unwrap());
        }
        let capture = temporary.path().join("documents.jsonl");
        std::fs::write(&capture, rows.join("\n") + "\n").unwrap();
        let facts = import_capture(
            &capture,
            Some(&fixture.join("syntax.jsonl")),
            &ExtractOptions::default(),
        )
        .unwrap();
        let caller = if remove_constructor {
            "constructorforms/NewExplicitSuite#observed."
        } else {
            "constructorforms/ApplyDefaultSuite#observed."
        };
        assert!(facts.issues.iter().any(|issue| {
            facts.symbol_name(issue.symbol) == caller
                && matches!(
                    issue.kind,
                    IssueKind::UnresolvedSymbol | IssueKind::UnknownExecution
                )
        }));
    }
}

#[test]
fn getter_name_without_complete_compiler_formal_proof_is_not_admitted() {
    let fixture =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/constructor-forms/base");
    for missing in ["default_property", "evaluation_mode"] {
        let temporary = tempfile::tempdir().unwrap();
        let mut rows = Vec::new();
        for line in std::fs::read_to_string(fixture.join("documents.jsonl"))
            .unwrap()
            .lines()
        {
            let mut row: serde_json::Value = serde_json::from_str(line).unwrap();
            for symbol in row["document"]["symbols"].as_array_mut().unwrap() {
                if symbol["symbol"] == "constructorforms/Value.apply().(value)" {
                    if missing == "default_property" {
                        symbol["properties"] =
                            serde_json::json!(symbol["properties"].as_u64().unwrap_or(0) & !32768);
                    } else {
                        symbol.as_object_mut().unwrap().remove("signature");
                    }
                }
            }
            rows.push(serde_json::to_string(&row).unwrap());
        }
        let capture = temporary.path().join("documents.jsonl");
        std::fs::write(&capture, rows.join("\n") + "\n").unwrap();
        let facts = import_capture(
            &capture,
            Some(&fixture.join("syntax.jsonl")),
            &ExtractOptions::default(),
        )
        .unwrap();
        let caller = ops(&facts, "constructorforms/ApplyDefaultSuite#observed.");
        assert!(
            caller.iter().any(|op| op.opcode == Opcode::Unknown),
            "{missing}"
        );
        assert!(
            !caller.iter().any(|op| op.opcode == Opcode::DefaultArgument),
            "{missing}"
        );
    }
}
