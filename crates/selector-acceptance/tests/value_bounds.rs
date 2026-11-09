//! Actual compiler identities distinguish known allocation flow, universal
//! static result constraints, and disjunctive unknown alternatives.
use selector_extract::{ExtractOptions, import_capture};
use selector_facts::FactSnapshot;
use selector_graph::ProgramGraph;
use selector_result::AnalysisResult;
use selector_solve::{ExecutionRoot, QuerySession, SolveOptions};
use selector_types::*;
use std::path::{Path, PathBuf};

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/value-bounds")
}
fn imported(workers: usize) -> (FactSnapshot, ProgramGraph) {
    let directory = fixture().join("head");
    imported_capture(&directory.join("documents.jsonl"), workers)
}
fn imported_capture(input: &Path, workers: usize) -> (FactSnapshot, ProgramGraph) {
    let directory = fixture().join("head");
    let facts = import_capture(
        input,
        Some(&directory.join("syntax.jsonl")),
        &ExtractOptions {
            workers,
            ..Default::default()
        },
    )
    .unwrap();
    let graph = selector_graph_build::build(
        &facts,
        &selector_graph_build::BuildOptions {
            workers,
            include_models: true,
        },
    )
    .unwrap();
    (facts, graph)
}

#[test]
fn synthetic_missing_or_nonruntime_bound_declarations_never_exclude_a_final_implementation() {
    // Explicit synthetic negative controls derived from the genuine capture.
    // Source bytes, source occurrences and parent relationships are retained;
    // only the Narrow declaration metadata is removed or made unverified.
    for control in ["missing-runtime-declaration", "unverified-type-parameter"] {
        let original = std::fs::read_to_string(fixture().join("head/documents.jsonl")).unwrap();
        let mut rows: Vec<serde_json::Value> = original
            .lines()
            .map(|line| serde_json::from_str(line).unwrap())
            .collect();
        for row in &mut rows {
            let symbols = row["document"]["symbols"].as_array_mut().unwrap();
            if control == "missing-runtime-declaration" {
                symbols.retain(|symbol| symbol["symbol"] != "valuebounds/Narrow#");
            } else {
                for symbol in symbols
                    .iter_mut()
                    .filter(|symbol| symbol["symbol"] == "valuebounds/Narrow#")
                {
                    symbol["kind"] = serde_json::json!(9);
                    symbol["signature"] = serde_json::json!({});
                }
            }
        }
        let directory = tempfile::tempdir().unwrap();
        let input = directory.path().join("synthetic-documents.jsonl");
        std::fs::write(
            &input,
            rows.iter()
                .map(|row| serde_json::to_string(row).unwrap() + "\n")
                .collect::<String>(),
        )
        .unwrap();
        let (facts, graph) = imported_capture(&input, 2);
        let narrow = facts.find_symbol("valuebounds/Narrow#").unwrap();
        assert!(!matches!(facts.symbols[narrow.index()].kind, 13 | 14));
        for method in ["narrowed", "alias", "generic"] {
            let root = node(&facts, &graph, &format!("valuebounds/Cases.{method}()."));
            let result = analyze(&facts, &graph, method, "outsider", 2);
            assert!(
                result.contains(root),
                "{control}/{method}: incomplete bounds cannot prove final Sibling disjoint"
            );
            assert!(
                result.guarded_roots.contains(&root),
                "{control}/{method}: uncertainty remains explicit"
            );
        }
    }
}
fn node(facts: &FactSnapshot, graph: &ProgramGraph, symbol: &str) -> NodeId {
    graph
        .node_for_symbol(facts.find_symbol(symbol).unwrap())
        .unwrap()
}
fn analyze(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    method: &str,
    effect: &str,
    workers: usize,
) -> AnalysisResult {
    let root = node(facts, graph, &format!("valuebounds/Cases.{method}()."));
    let mut query = QuerySession::new(
        facts,
        graph,
        &SolveOptions {
            workers,
            ..Default::default()
        },
    )
    .unwrap();
    query
        .execute(&[ExecutionRoot {
            node: root,
            receiver: facts.find_symbol("valuebounds/Cases.").unwrap(),
        }])
        .unwrap();
    query
        .analyze(&[node(
            facts,
            graph,
            &format!("valuebounds/Effects.{effect}()."),
        )])
        .unwrap()
}

#[test]
fn compiler_and_jvm_witnesses_preserve_the_static_bound_forms() {
    let receipt: serde_json::Value =
        serde_json::from_slice(&std::fs::read(fixture().join("manifest.json")).unwrap()).unwrap();
    assert_eq!(receipt["opaque_library_bodies_admitted"], false);
    for (side, expected) in [
        ("base", "observed:41,41,41,41,41,41,41,41,41,99\n"),
        ("head", "observed:42,42,42,42,42,42,42,42,42,99\n"),
    ] {
        let actual = std::fs::read_to_string(fixture().join(side).join("execution.log")).unwrap();
        assert_eq!(actual, expected);
        assert_eq!(
            receipt["sides"][side]["jvm_witness"].as_str(),
            Some(expected)
        );
    }
    let (facts, _) = imported(2);
    let signature = |name: &str| -> serde_json::Value {
        let symbol = facts.find_symbol(name).unwrap();
        serde_json::from_str(facts.text(facts.symbols[symbol.index()].signature)).unwrap()
    };
    assert_eq!(
        signature("valuebounds/Factories.narrow().")["method_signature"]["return_type"]["type_ref"]
            ["symbol"],
        "valuebounds/Narrow#"
    );
    assert_eq!(
        signature("valuebounds/Factories.known().")["method_signature"]["return_type"]["type_ref"]
            ["symbol"],
        "valuebounds/Base#"
    );
    assert_eq!(
        signature("valuebounds/Factories.Alias#")["type_signature"]["upper_bound"]["type_ref"]["symbol"],
        "valuebounds/Narrow#"
    );
    assert_eq!(
        signature("valuebounds/Factories.generic().[T]")["type_signature"]["upper_bound"]["type_ref"]
            ["symbol"],
        "valuebounds/Narrow#"
    );
    let intersection = signature("valuebounds/Factories.intersection().");
    let return_type = &intersection["method_signature"]["return_type"]["structural_type"]["tpe"];
    assert!(
        return_type.get("with_type").is_some() || return_type.get("intersection_type").is_some(),
        "{return_type}"
    );
}

#[test]
fn a_known_allocation_survives_a_wider_declared_return_without_adding_sibling_execution() {
    for workers in [1, 4] {
        let (facts, graph) = imported(workers);
        for method in ["exact", "wider"] {
            let root = node(&facts, &graph, &format!("valuebounds/Cases.{method}()."));
            let positive = analyze(&facts, &graph, method, "affected", workers);
            assert!(
                positive.contains(root),
                "{method} must preserve Allowed allocation flow"
            );
            for effect in ["outsider", "unmarked"] {
                let negative = analyze(&facts, &graph, method, effect, workers);
                assert!(
                    !negative.contains(root),
                    "{method}: unrelated {effect} implementation must stay inactive"
                );
            }
        }
    }
}

#[test]
fn a_declared_bound_restricts_unknown_alternatives_without_fabricating_allocations() {
    let mut violations = Vec::new();
    for workers in [1, 4] {
        let (facts, graph) = imported(workers);
        for method in ["narrowed", "alias", "generic", "intersection"] {
            let root = node(&facts, &graph, &format!("valuebounds/Cases.{method}()."));
            let positive = analyze(&facts, &graph, method, "affected", workers);
            assert!(
                positive.contains(root),
                "{method}: Allowed remains feasible under the compiler bound"
            );
            assert!(
                positive.guarded_roots.contains(&root),
                "{method}: opaque effects must remain guarded"
            );
            assert!(
                !positive.evidence.atoms.iter().any(|atom| atom.kind == 1
                    && [
                        "valuebounds/Allowed#",
                        "valuebounds/Narrow#",
                        "valuebounds/Marker#"
                    ]
                    .contains(&facts.symbol_name(atom.symbol))),
                "{method}: a type constraint is not an allocation witness"
            );
            let outside = analyze(&facts, &graph, method, "outsider", workers);
            if outside.contains(root) {
                violations.push(format!("workers={workers} {method}: verified Narrow bound did not exclude unrelated Sibling"));
            }
            assert!(
                outside.guarded_roots.contains(&root),
                "{method}: narrowing must retain the opaque guard"
            );
            if method != "intersection" {
                assert!(
                    analyze(&facts, &graph, method, "unmarked", workers).contains(root),
                    "{method}: Narrow permits the separate NoMarker subclass"
                );
            }
        }
        let root = node(&facts, &graph, "valuebounds/Cases.intersection().");
        let unmarked = analyze(&facts, &graph, "intersection", "unmarked", workers);
        if unmarked.contains(root) {
            violations.push(format!(
                "workers={workers} intersection: Narrow with Marker did not exclude NoMarker"
            ));
        }
    }
    assert!(violations.is_empty(), "{}", violations.join("\n"));
}

#[test]
fn a_separate_broad_unknown_branch_does_not_borrow_the_known_branch_identity() {
    for workers in [1, 4] {
        let (facts, graph) = imported(workers);
        let root = node(&facts, &graph, "valuebounds/Cases.mixed().");
        for effect in ["affected", "outsider", "unmarked"] {
            let result = analyze(&facts, &graph, "mixed", effect, workers);
            assert!(
                result.contains(root),
                "the separate Base alternative permits {effect}"
            );
            assert!(result.guarded_roots.contains(&root));
        }
        let result = analyze(&facts, &graph, "mixed", "affected", workers);
        assert!(
            result
                .evidence
                .atoms
                .iter()
                .any(|atom| atom.kind == 1
                    && facts.symbol_name(atom.symbol) == "valuebounds/Allowed#"),
            "the exact branch allocation must remain in detached evidence beside the unknown alternative"
        );
        let branches = node(&facts, &graph, "valuebounds/Cases.branches().");
        assert!(analyze(&facts, &graph, "branches", "affected", workers).contains(branches));
        assert!(analyze(&facts, &graph, "branches", "outsider", workers).contains(branches));
        assert!(!analyze(&facts, &graph, "branches", "unmarked", workers).contains(branches));
    }
}
