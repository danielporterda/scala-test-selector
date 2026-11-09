//! Exact compiler selections distinguish same-arity external Java constructors.
//! Type-argument wrappers do not execute a generic call prefix a second time.
use selector_extract::{ExtractOptions, import_capture};
use selector_facts::{BodyRecord, FactSnapshot, OperationRecord};
use selector_types::*;
use std::path::{Path, PathBuf};

const STRING: &str = "externalprefix/Native#`<init>`().";
const INT: &str = "externalprefix/Native#`<init>`(+1).";
fn directory() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/external-constructor-prefix")
}
fn imported(documents: &Path, syntax: &Path) -> FactSnapshot {
    import_capture(
        documents,
        Some(syntax),
        &ExtractOptions {
            workers: 2,
            ..Default::default()
        },
    )
    .unwrap()
}
fn facts() -> FactSnapshot {
    imported(
        &directory().join("documents.jsonl"),
        &directory().join("syntax.jsonl"),
    )
}
fn body<'a>(facts: &'a FactSnapshot, name: &str) -> &'a BodyRecord {
    let symbol = facts
        .find_symbol(&format!("externalprefix/Calls#{name}()."))
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
fn calls<'a>(
    facts: &'a FactSnapshot,
    body: &BodyRecord,
    symbol: &str,
) -> Vec<(usize, &'a OperationRecord)> {
    ops(facts, body)
        .iter()
        .enumerate()
        .filter(|(_, op)| {
            matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
                && facts.symbol_name(op.target) == symbol
        })
        .collect()
}

#[test]
fn genuine_jvm_distinguishes_overloaded_constructors_and_deferred_generic_chain() {
    for (mode, expected) in [
        ("string", "string:text,ctor-string:x:1\n"),
        ("int", "int:number,ctor-int:7:7\n"),
        (
            "dormant",
            "dormant-created:\ndormant-invoked:text,ctor-string:x:1\n",
        ),
        ("class", "class:\n"),
        ("chain", "chain:box,map,map-body,flatMap,flat-body:3\n"),
        (
            "deferred-chain",
            "chain-created:\nchain-invoked:box,map,map-body,flatMap,flat-body:3\n",
        ),
        ("eta", "eta-created:\neta-invoked:generic:8\n"),
    ] {
        assert_eq!(
            std::fs::read_to_string(directory().join(format!("jvm-{mode}.stdout"))).unwrap(),
            expected
        );
    }
}

#[test]
fn real_external_selections_are_zero_width_role_one_without_java_declaration_rows() {
    let document: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(directory().join("documents.jsonl")).unwrap(),
    )
    .unwrap();
    assert!(
        !document["document"]["symbols"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| row["symbol"]
                .as_str()
                .unwrap()
                .starts_with("externalprefix/Native#"))
    );
    for name in [STRING, INT] {
        let matching: Vec<_> = document["document"]["occurrences"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|row| row["symbol"] == name)
            .collect();
        assert!(!matching.is_empty());
        for row in matching {
            let range = &row["range"];
            assert_eq!(row["role"], 1);
            assert_eq!(range["start_line"], range["end_line"]);
            assert_eq!(range["start_character"], range["end_character"]);
        }
    }
    let javap = std::fs::read_to_string(directory().join("javap.stdout")).unwrap();
    assert!(javap.contains("(Ljava/lang/String;)V") && javap.contains("(I)V"));
}

#[test]
fn exact_compiler_id_selects_the_same_arity_overload_after_its_provider_once() {
    let facts = facts();
    for (name, selected, provider) in [
        ("stringConstructor", STRING, "text"),
        ("intConstructor", INT, "number"),
    ] {
        let body = body(&facts, name);
        let operations = ops(&facts, body);
        let constructor: Vec<_> = operations
            .iter()
            .enumerate()
            .filter(|(_, op)| {
                op.opcode == Opcode::Allocate && facts.symbol_name(op.target) == selected
            })
            .collect();
        assert_eq!(
            constructor.len(),
            1,
            "selected compiler overload is preserved"
        );
        let providers = calls(&facts, body, &format!("externalprefix/Calls#{provider}()."));
        assert_eq!(providers.len(), 1);
        assert!(providers[0].0 < constructor[0].0);
        assert_eq!(
            &facts.operands[constructor[0].1.arguments.range()],
            &[providers[0].1.dest]
        );
        let record = facts.symbols[constructor[0].1.target.index()];
        assert_eq!(record.kind, 0);
        assert!(record.signature.is_none());
        assert_eq!(
            record.flags
                & (SYMBOL_DEFINED | SYMBOL_NATIVE_BINARY | SYMBOL_JVM_CLASS_HEADER_VERIFIED),
            0
        );
        assert!(
            facts.issues.iter().any(|issue| issue.symbol == body.symbol
                && issue.kind == IssueKind::UnknownExecution
                && facts
                    .text(issue.detail)
                    .contains("constructor has no authoritative source argument signature")),
            "identity alone grants neither Java argument metadata nor effect completeness"
        );
        assert!(!facts.issues.iter().any(|issue| issue.symbol == body.symbol
            && issue.kind == IssueKind::UnresolvedSymbol
            && facts.text(issue.detail).contains("constructor overload")));
    }
}

#[test]
fn constructor_identity_perturbations_remain_unresolved_without_arity_guessing() {
    let original: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(directory().join("documents.jsonl")).unwrap(),
    )
    .unwrap();
    for control in [
        "missing",
        "ambiguous",
        "wrong-owner",
        "wrong-kind",
        "declaration-role",
        "nonzero-anchor",
    ] {
        // Clearly labeled normalized compiler-record corruptions, not positive
        // Java metadata or alternate compiler observations.
        let mut changed = original.clone();
        let occurrences = changed["document"]["occurrences"].as_array_mut().unwrap();
        let position = occurrences
            .iter()
            .position(|row| row["symbol"] == STRING)
            .unwrap();
        let row = occurrences[position].clone();
        match control {
            "missing" => {
                occurrences.remove(position);
            }
            "ambiguous" => {
                let mut other = row;
                other["symbol"] = INT.into();
                occurrences.push(other);
            }
            "wrong-owner" => {
                occurrences[position]["symbol"] = "externalprefix/Other#`<init>`().".into()
            }
            "declaration-role" => occurrences[position]["role"] = 2.into(),
            "nonzero-anchor" => {
                let start = occurrences[position]["range"]["start_character"]
                    .as_u64()
                    .unwrap();
                occurrences[position]["range"]["start_character"] = (start - 1).into();
            }
            "wrong-kind" => changed["document"]["symbols"]
                .as_array_mut()
                .unwrap()
                .push(serde_json::json!({"symbol":STRING,"kind":3})),
            _ => unreachable!(),
        }
        let temporary = tempfile::tempdir().unwrap();
        let path = temporary.path().join("perturbed.jsonl");
        std::fs::write(&path, serde_json::to_vec(&changed).unwrap()).unwrap();
        let facts = imported(&path, &directory().join("syntax.jsonl"));
        let body = body(&facts, "stringConstructor");
        assert!(
            !ops(&facts, body)
                .iter()
                .any(|op| op.opcode == Opcode::Allocate && facts.symbol_name(op.target) == STRING),
            "{control}"
        );
        assert!(
            facts.issues.iter().any(|issue| issue.symbol == body.symbol
                && issue.kind == IssueKind::UnresolvedSymbol
                && facts
                    .text(issue.detail)
                    .contains("constructor overload has no exact compiler occurrence")),
            "{control}"
        );
        assert_eq!(
            calls(&facts, body, "externalprefix/Calls#text().").len(),
            1,
            "written provider effects remain: {control}"
        );
    }
}

#[test]
fn generic_type_only_prefixes_do_not_duplicate_calls_or_manufacture_runtime_unknowns() {
    let facts = facts();
    let parent = body(&facts, "chain");
    for method in [
        "externalprefix/Calls#box().",
        "externalprefix/Box#map().",
        "externalprefix/Box#flatMap().",
    ] {
        assert_eq!(calls(&facts, parent, method).len(), 1, "{method}");
    }
    assert!(
        !ops(&facts, parent)
            .iter()
            .any(|op| op.opcode == Opcode::Unknown),
        "a type-only wrapper is not a second executable prefix: {:?}",
        ops(&facts, parent)
            .iter()
            .map(|op| (op.opcode, facts.symbol_name(op.target), op.span))
            .collect::<Vec<_>>()
    );
    assert!(!facts.issues.iter().any(|issue| issue.symbol == parent.symbol && issue.kind == IssueKind::UnknownExecution));
}

#[test]
fn dormant_constructor_chain_and_eta_creation_do_not_run_their_bodies() {
    let facts = facts();
    for name in ["dormantConstructor", "dormantChain", "eta"] {
        let parent = body(&facts, name);
        assert!(
            ops(&facts, parent)
                .iter()
                .any(|op| op.opcode == Opcode::BindCallback)
        );
        assert!(!ops(&facts, parent).iter().any(|op| matches!(
            op.opcode,
            Opcode::Call | Opcode::VirtualCall | Opcode::InvokeCallback | Opcode::Allocate
        )));
    }
    assert!(!ops(&facts, body(&facts, "classLiteral")).iter().any(|op| {
        op.opcode == Opcode::Allocate
            && facts
                .symbol_name(op.target)
                .starts_with("externalprefix/Native#")
    }));
}

#[test]
fn duplicate_generic_prefix_application_claim_keeps_an_explicit_guard() {
    // Structural AST corruption only: the real compiler input above contains
    // one complete application for each type-only prefix.
    let source =
        std::fs::read_to_string(directory().join("src/externalprefix/Calls.scala")).unwrap();
    let start = source.find("box().map").unwrap() as u64;
    let mut syntax: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(directory().join("syntax.jsonl")).unwrap())
            .unwrap();
    let sites = syntax["ast"]["call_sites"].as_array_mut().unwrap();
    let row = sites
        .iter()
        .find(|row| {
            row["start"] == start && row["kind"] == "apply" && row["function_end"] == start + 9
        })
        .unwrap()
        .clone();
    sites.push(row);
    let temporary = tempfile::tempdir().unwrap();
    let path = temporary.path().join("duplicate-application.jsonl");
    std::fs::write(&path, serde_json::to_vec(&syntax).unwrap()).unwrap();
    let facts = imported(&directory().join("documents.jsonl"), &path);
    let parent = body(&facts, "chain");
    assert!(facts.issues.iter().any(|issue| {
        issue.symbol == parent.symbol
            && issue.kind == IssueKind::UnknownExecution
            && facts
                .text(issue.detail)
                .contains("type-only function prefix has no unique same-body complete application")
    }));
    assert_eq!(
        calls(&facts, parent, "externalprefix/Calls#box().").len(),
        1,
        "receiver provider remains evaluated once"
    );
}
