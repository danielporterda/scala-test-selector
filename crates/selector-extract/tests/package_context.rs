//! Original PR7646 compiler records: a package-clause definition without a
//! SymbolInformation record must not become a cross-project class provider.
use selector_extract::{ExtractOptions, import_capture};
use selector_types::*;
use sha2::{Digest, Sha256};

#[test]
fn genuine_package_clause_without_symbol_information_is_a_namespace_across_contexts() {
    let bytes = include_bytes!("../../../fixtures/package-context/documents.jsonl");
    let manifest: serde_json::Value = serde_json::from_str(include_str!(
        "../../../fixtures/package-context/manifest.json"
    ))
    .unwrap();
    assert_eq!(
        ContentHash(Sha256::digest(bytes).into()).to_string(),
        manifest["documents_sha256"].as_str().unwrap()
    );
    let package = manifest["package_symbol"].as_str().unwrap();
    let rows: Vec<serde_json::Value> = bytes
        .split_inclusive(|&byte| byte == b'\n')
        .filter(|line| !line.is_empty())
        .enumerate()
        .map(|(index, line)| {
            assert_eq!(
                ContentHash(Sha256::digest(line).into()).to_string(),
                manifest["documents"][index]["capture_row_sha256"]
                    .as_str()
                    .unwrap()
            );
            let row: serde_json::Value = serde_json::from_slice(line).unwrap();
            assert!(
                row["document"]["symbols"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .all(|symbol| symbol["symbol"] != package)
            );
            row
        })
        .collect();
    assert_eq!(rows.len(), 2);
    let roles: Vec<_> = rows
        .iter()
        .flat_map(|row| row["document"]["occurrences"].as_array().unwrap())
        .filter(|occurrence| occurrence["symbol"] == package)
        .map(|occurrence| occurrence["role"].as_u64().unwrap())
        .collect();
    assert_eq!(roles, [2, 1]);
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("documents.jsonl");
    std::fs::write(&input, bytes).unwrap();
    let mut fingerprints = Vec::new();
    for workers in [1, 4] {
        let facts = import_capture(
            &input,
            None,
            &ExtractOptions {
                workers,
                ..Default::default()
            },
        )
        .unwrap();
        assert_eq!(facts.files.len(), 2);
        let package_symbols: Vec<_> = facts
            .symbols
            .iter()
            .enumerate()
            .filter(|(_, symbol)| facts.text(symbol.name) == package)
            .collect();
        assert_eq!(package_symbols.len(), 2);
        assert_ne!(package_symbols[0].1.context, package_symbols[1].1.context);
        assert!(package_symbols.iter().all(|(_, symbol)| symbol.kind == 0));
        assert_eq!(
            package_symbols
                .iter()
                .filter(|(_, symbol)| symbol.flags & SYMBOL_DEFINED != 0)
                .count(),
            1
        );
        assert!(facts.issues.iter().all(|issue| {
            !matches!(
                issue.kind,
                IssueKind::ContextConflict | IssueKind::UnresolvedSymbol
            ) || issue.symbol.is_none()
                || facts.symbol_name(issue.symbol) != package
        }));
        // No syntax was supplied. This fixture proves namespace admission,
        // rather than claiming executable-body completeness.
        assert!(
            facts
                .issues
                .iter()
                .any(|issue| issue.kind == IssueKind::MissingSyntax)
        );
        fingerprints.push(facts.identity);
    }
    assert_eq!(fingerprints[0], fingerprints[1]);
}
