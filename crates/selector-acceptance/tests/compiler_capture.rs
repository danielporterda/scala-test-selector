//! Compiler identities + source-reviewed expectations are independent inputs.
//! `expected.json` is read only by assertions, never passed into extraction/build.
use selector_extract::{ExtractOptions, SourceCoordinates, import_capture};
use selector_facts::FactSnapshot;
use selector_types::*;
use serde_json::Value;
use std::path::PathBuf;

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/compiler-smoke")
}
fn extract(workers: usize) -> FactSnapshot {
    let directory = fixture();
    let options = ExtractOptions {
        workers,
        ..ExtractOptions::default()
    };
    import_capture(
        &directory.join("documents.jsonl"),
        Some(&directory.join("syntax.jsonl")),
        &options,
    )
    .unwrap()
}
fn expected() -> Value {
    serde_json::from_slice(&std::fs::read(fixture().join("expected.json")).unwrap()).unwrap()
}
fn symbol_in_file(facts: &FactSnapshot, name: &str, path: &str) -> SymbolId {
    facts
        .symbols
        .iter()
        .enumerate()
        .find(|(_, record)| facts.text(record.name) == name && facts.path(record.file) == path)
        .map(|(index, _)| SymbolId(index as u32))
        .unwrap_or_else(|| panic!("missing compiler declaration {name} in {path}"))
}

#[test]
fn reviewed_declarations_keep_exact_compiler_identities_and_overrides() {
    let facts = extract(2);
    let assertions = expected();
    for declaration in assertions["declarations"].as_array().unwrap() {
        let name = declaration["symbol"].as_str().unwrap();
        let path = declaration["path"].as_str().unwrap();
        let id = symbol_in_file(&facts, name, path);
        let symbol = facts.symbols[id.index()];
        assert_eq!(
            symbol.kind as u64,
            declaration["kind"].as_u64().unwrap(),
            "{name}"
        );
        assert_ne!(symbol.flags & SYMBOL_DEFINED, 0, "{name}");
        if let Some(overrides) = declaration["overridden_symbols"].as_array() {
            for target in overrides {
                assert!(
                    facts.relations.iter().any(|relation| relation.source == id
                        && relation.kind == RelationKind::Override
                        && facts.symbol_name(relation.target) == target.as_str().unwrap()),
                    "compiler override missing for {name}"
                );
            }
        }
    }
}

#[test]
fn reviewed_body_spans_and_targets_come_from_validated_syntax_and_occurrences() {
    let facts = extract(2);
    let assertions = expected();
    for call in assertions["body_calls"].as_array().unwrap() {
        let owner = symbol_in_file(
            &facts,
            call["from_symbol"].as_str().unwrap(),
            call["path"].as_str().unwrap(),
        );
        let symbol = facts.symbols[owner.index()];
        let source = facts.text(facts.files[symbol.file.index()].source);
        let coords = SourceCoordinates::new(source).unwrap();
        let range = &call["body_range"];
        let span = coords
            .semantic_span([
                range["start_line"].as_i64().unwrap(),
                range["start_character"].as_i64().unwrap(),
                range["end_line"].as_i64().unwrap(),
                range["end_character"].as_i64().unwrap(),
            ])
            .unwrap();
        assert_eq!(
            &source[span.start as usize..span.end as usize],
            call["body_source"].as_str().unwrap()
        );
        let body = facts
            .bodies
            .iter()
            .find(|body| body.symbol == owner && body.span == span)
            .unwrap_or_else(|| {
                panic!(
                    "no captured executable body span for {}",
                    call["from_symbol"]
                )
            });
        assert!(
            facts.operations[body.operations.range()]
                .iter()
                .any(|operation| {
                    matches!(operation.opcode, Opcode::Call | Opcode::VirtualCall)
                        && facts.symbol_name(operation.target)
                            == call["to_symbol"].as_str().unwrap()
                }),
            "reviewed direct call target missing for {}",
            call["from_symbol"]
        );
    }
}

#[test]
fn missing_syntax_stays_explicit_and_parallel_extraction_is_deterministic() {
    let serial = extract(1);
    let parallel = extract(4);
    assert_eq!(serial.identity, parallel.identity);
    assert_eq!(serial.strings.bytes, parallel.strings.bytes);
    assert_eq!(serial.symbols.len(), parallel.symbols.len());
    assert_eq!(serial.occurrences.len(), parallel.occurrences.len());
    assert_eq!(serial.operations.len(), parallel.operations.len());
    for (left, right) in serial.operations.iter().zip(&parallel.operations) {
        assert_eq!(
            (left.body, left.opcode as u32, left.target, left.span),
            (right.body, right.opcode as u32, right.target, right.span)
        );
    }
    // Deliberately withhold the available syntax sidecar for the admission control.
    let without_syntax = import_capture(
        &fixture().join("documents.jsonl"),
        None,
        &ExtractOptions {
            workers: 2,
            ..ExtractOptions::default()
        },
    )
    .unwrap();
    let path = "apps/app/src/main/scala/org/lfdecentralizedtrust/splice/SpliceApp.scala";
    let file = without_syntax
        .files
        .iter()
        .enumerate()
        .find(|(_, file)| without_syntax.text(file.path) == path)
        .map(|(index, _)| FileId(index as u32))
        .unwrap();
    assert!(
        without_syntax
            .issues
            .iter()
            .any(|issue| issue.file == file && issue.kind == IssueKind::MissingSyntax)
    );
    assert!(
        !without_syntax.bodies.iter().any(|body| body.file == file),
        "compiler name-token positions must not invent executable spans"
    );
}
