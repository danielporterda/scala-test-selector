//! Separately compiled inherited case-class companion: compiler selections,
//! named provider scheduling and strict external metadata remain distinct.
use selector_extract::{ExtractOptions, import_capture};
use selector_facts::{BodyRecord, FactSnapshot, OperationRecord};
use selector_types::*;
use std::path::PathBuf;

const OWNER: &str = "selectedexternal/Configuration#PatienceConfig.";
const APPLY: &str = "selectedexternal/Configuration#PatienceConfig.apply(+1).";
const OVERLOAD: &str = "selectedexternal/Configuration#PatienceConfig.apply().";
fn directory() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/selected-external-apply")
}
fn facts() -> FactSnapshot {
    import_capture(
        &directory().join("documents.jsonl"),
        Some(&directory().join("syntax.jsonl")),
        &ExtractOptions {
            workers: 2,
            ..Default::default()
        },
    )
    .unwrap()
}
fn body<'a>(facts: &'a FactSnapshot, name: &str) -> &'a BodyRecord {
    let symbol = facts
        .find_symbol(&format!("selectedexternal/Calls#{name}()."))
        .unwrap();
    facts
        .bodies
        .iter()
        .find(|body| body.symbol == symbol)
        .unwrap()
}
fn operations<'a>(facts: &'a FactSnapshot, body: &BodyRecord) -> &'a [OperationRecord] {
    &facts.operations[body.operations.range()]
}
fn calls<'a>(
    facts: &'a FactSnapshot,
    body: &BodyRecord,
    symbol: &str,
) -> Vec<(usize, &'a OperationRecord)> {
    operations(facts, body)
        .iter()
        .enumerate()
        .filter(|(_, op)| {
            matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
                && facts.symbol_name(op.target) == symbol
        })
        .collect()
}

#[test]
fn independent_jvm_observes_qualifier_named_order_overload_and_deferred_calls() {
    for (name, expected) in [
        ("inherited", "inherited:interval,timeout:1:2\n"),
        ("qualified", "qualified:qualifier,interval,timeout\n"),
        ("positional", "positional:qualifier,timeout,interval\n"),
        ("overloaded", "overloaded:qualifier,label,overload:x\n"),
        (
            "eta",
            "eta-created:qualifier\neta-invoked:qualifier,timeout,interval\n",
        ),
        (
            "returned",
            "returned-created:qualifier,timeout,factory\nreturned-invoked:qualifier,timeout,factory,returned-body\n",
        ),
        (
            "applied-returned",
            "applied-returned:qualifier,timeout,factory,interval,returned-body\n",
        ),
        ("dormant", "dormant:\n"),
    ] {
        assert_eq!(
            std::fs::read_to_string(directory().join(format!("jvm-{name}.stdout"))).unwrap(),
            expected
        );
    }
}

#[test]
fn exact_external_scala_metadata_is_separate_from_the_caller_source_capture() {
    let fixture = directory();
    let source: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(fixture.join("documents.jsonl")).unwrap())
            .unwrap();
    assert_eq!(source["path"], "src/selectedexternal/Calls.scala");
    assert!(
        !source["document"]["symbols"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| {
                row["symbol"]
                    .as_str()
                    .is_some_and(|s| s.starts_with("selectedexternal/Configuration#"))
            }),
        "separately compiled external declarations are absent from caller-only source rows"
    );
    let metadata: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(fixture.join("external-signatures.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(metadata["jdk_object_in_index"], false);
    let pair = metadata["methods"]
        .as_array()
        .unwrap()
        .iter()
        .find(|m| m["symbol"] == APPLY)
        .unwrap();
    let formals = pair["formals"].as_array().unwrap();
    assert_eq!(formals.len(), 2);
    for (ordinal, name) in ["timeout", "interval"].into_iter().enumerate() {
        assert_eq!(formals[ordinal]["symbol"], format!("{APPLY}({name})"));
        assert_eq!(formals[ordinal]["clause"], 0);
        assert_eq!(formals[ordinal]["ordinal"], ordinal);
        assert_eq!(formals[ordinal]["default"], true);
        assert!(
            source["document"]["occurrences"]
                .as_array()
                .unwrap()
                .iter()
                .any(|row| row["symbol"] == formals[ordinal]["symbol"]),
            "external formal identities exactly match genuine compiler-bound named labels"
        );
        for flag in ["by_name", "repeated", "implicit"] {
            assert_eq!(formals[ordinal][flag], false);
        }
    }
    assert!(
        metadata["methods"]
            .as_array()
            .unwrap()
            .iter()
            .any(|m| m["symbol"] == OVERLOAD && m["formals"].as_array().unwrap().len() == 1)
    );
    let facts = facts();
    let selected = facts.find_symbol(APPLY).unwrap();
    assert_eq!(facts.symbols[selected.index()].flags & SYMBOL_DEFINED, 0);
    assert!(facts.symbols[selected.index()].signature.is_none());
    assert!(
        !facts.bodies.iter().any(|b| b.symbol == selected),
        "metadata is never admitted as an executable source definition"
    );
}

#[test]
fn compiler_selected_inherited_apply_runs_once_after_each_written_provider() {
    let facts = facts();
    let body = body(&facts, "inherited");
    let interval = calls(&facts, body, "selectedexternal/Calls#interval().");
    let timeout = calls(&facts, body, "selectedexternal/Calls#timeout().");
    let selected = calls(&facts, body, APPLY);
    assert_eq!((interval.len(), timeout.len(), selected.len()), (1, 1, 1));
    assert!(
        interval[0].0 < timeout[0].0 && timeout[0].0 < selected[0].0,
        "providers execute in written order even when formal order is the reverse"
    );
    assert_eq!(selected[0].1.arguments.len, 2);
    assert!(
        selected[0].1.span.contains(interval[0].1.span)
            && selected[0].1.span.contains(timeout[0].1.span),
        "one selected call owns the complete written Apply span"
    );
    let receiver: Vec<_> = operations(&facts, body)
        .iter()
        .enumerate()
        .filter(|(_, op)| !op.target.is_none() && facts.symbol_name(op.target) == OWNER)
        .collect();
    assert_eq!(
        receiver.len(),
        1,
        "the actual companion receiver is evaluated once"
    );
    assert!(receiver[0].0 < interval[0].0);
    assert_eq!(selected[0].1.a, receiver[0].1.dest);
    assert!(
        calls(&facts, body, OVERLOAD).is_empty(),
        "the other declaration does not select an overload"
    );
}

#[test]
fn absent_signature_retains_a_scoped_guard_instead_of_claiming_formal_order() {
    let facts = facts();
    let body = body(&facts, "inherited");
    assert!(
        facts
            .issues
            .iter()
            .any(|issue| issue.kind == IssueKind::UnknownExecution
                && issue.symbol == body.symbol
                && facts.text(issue.detail).contains("argument signature")),
        "caller capture alone has selected identity and labels, but no authoritative formal signature: {:?}",
        facts
            .issues
            .iter()
            .map(|i| (facts.symbol_name(i.symbol), facts.text(i.detail)))
            .collect::<Vec<_>>()
    );
    let graph = selector_graph_build::build(
        &facts,
        &selector_graph_build::BuildOptions {
            workers: 1,
            include_models: false,
        },
    )
    .unwrap();
    let node = graph.node_for_symbol(body.symbol).unwrap();
    assert!(
        graph
            .issues
            .iter()
            .any(|issue| issue.kind == IssueKind::UnknownExecution
                && issue.node == node
                && issue.symbol == body.symbol
                && facts.text(issue.detail).contains("argument signature")),
        "the scoped source-argument guard survives immutable graph admission"
    );
}

#[test]
fn real_eta_and_dormant_bodies_keep_written_provider_calls_deferred() {
    let facts = facts();
    for name in ["eta", "dormant"] {
        let outer = body(&facts, name);
        assert!(calls(&facts, outer, "selectedexternal/Calls#interval().").is_empty());
        assert!(calls(&facts, outer, "selectedexternal/Calls#timeout().").is_empty());
        assert!(
            calls(&facts, outer, APPLY).is_empty(),
            "eta/lambda creation must not execute selected apply"
        );
        assert!(
            facts.bodies.iter().any(|inner| inner.symbol != outer.symbol
                && inner.flags & BODY_DEFERRED != 0
                && outer.span.contains(inner.span)),
            "genuine compiler callback body is retained"
        );
    }
}

#[test]
fn explicit_qualified_compiler_selections_keep_qualifier_before_all_providers() {
    let facts = facts();
    for (name, target, providers) in [
        ("positional", APPLY, vec!["timeout", "interval"]),
        ("overloaded", OVERLOAD, vec!["label"]),
    ] {
        let owner = body(&facts, name);
        let qualifier = calls(&facts, owner, "selectedexternal/Calls#qualifier().");
        assert_eq!(qualifier.len(), 1, "{name}: qualifier once");
        let selected = calls(&facts, owner, target);
        assert_eq!(
            selected.len(),
            1,
            "{name}: exact selected compiler target once"
        );
        assert_eq!(selected[0].1.arguments.len as usize, providers.len());
        let mut previous = qualifier[0].0;
        for provider in providers {
            let actuals = calls(
                &facts,
                owner,
                &format!("selectedexternal/Calls#{provider}()."),
            );
            assert_eq!(actuals.len(), 1, "{name}: {provider} once");
            assert!(
                previous < actuals[0].0 && actuals[0].0 < selected[0].0,
                "{name}: qualifier and providers keep JVM-observed source ordering"
            );
            previous = actuals[0].0;
            assert!(selected[0].1.span.contains(actuals[0].1.span));
        }
        assert!(selected[0].1.span.contains(qualifier[0].1.span));
        assert!(
            !selected[0].1.a.is_none(),
            "actual companion receiver is explicit"
        );
    }
}

#[test]
fn compiler_missing_select_tree_does_not_license_named_target_inference() {
    let facts = facts();
    let owner = body(&facts, "qualified");
    let qualifier = calls(&facts, owner, "selectedexternal/Calls#qualifier().");
    let interval = calls(&facts, owner, "selectedexternal/Calls#interval().");
    let timeout = calls(&facts, owner, "selectedexternal/Calls#timeout().");
    assert_eq!((qualifier.len(), interval.len(), timeout.len()), (1, 1, 1));
    assert!(qualifier[0].0 < interval[0].0 && interval[0].0 < timeout[0].0);
    assert!(
        calls(&facts, owner, APPLY).is_empty(),
        "compiler-bound labels alone do not recover a missing method-selection tree"
    );
    assert!(
        facts
            .issues
            .iter()
            .any(|issue| issue.kind == IssueKind::UnknownExecution && issue.symbol == owner.symbol),
        "compiler named-temporary rewrite with no selection witness stays scoped unknown"
    );
}
