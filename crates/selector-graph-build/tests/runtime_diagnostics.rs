use selector_facts::FactBuilder;
use selector_graph_build::{BuildOptions, build_with_runtime};
use selector_models::runtime::{RuntimeInputs, RuntimeSource};
use selector_types::*;

#[test]
fn runtime_diagnostic_reasons_and_metadata_survive_canonical_build_and_persistence() {
    let facts = FactBuilder::new().finish().unwrap();
    let mut inputs = RuntimeInputs {
        sources: vec![
            RuntimeSource {
                path: "z/ui.ts",
                text: "const z = 1",
            },
            RuntimeSource {
                path: "a/métadata.ts",
                text: "const a = 1",
            },
        ],
        ..Default::default()
    };
    let graph = build_with_runtime(
        &facts,
        &BuildOptions {
            workers: 1,
            include_models: true,
        },
        &inputs,
    )
    .unwrap();
    assert_eq!(graph.diagnostics.len(), 2);
    assert_eq!(
        graph.issues.len(),
        1,
        "equal uncertainty scopes may deduplicate independently of their provenance"
    );
    for diagnostic in &graph.diagnostics {
        assert_eq!(diagnostic.kind, IssueKind::UnsupportedModel);
        assert!(diagnostic.node.is_none());
        assert_eq!(
            graph.diagnostic_text(diagnostic.reason),
            "frontend_string_selector_runtime_join_not_supported"
        );
    }
    assert_eq!(
        graph.diagnostics[0].reason, graph.diagnostics[1].reason,
        "reason text interned once"
    );
    let paths: Vec<_> = graph
        .diagnostics
        .iter()
        .map(|d| graph.diagnostic_text(d.metadata_path))
        .collect();
    assert_eq!(paths, ["a/métadata.ts", "z/ui.ts"]);
    assert_eq!(
        graph.diagnostic_bytes.len(),
        "frontend_string_selector_runtime_join_not_supported".len()
            + "a/métadata.ts".len()
            + "z/ui.ts".len()
    );
    inputs.sources.reverse();
    let parallel = build_with_runtime(
        &facts,
        &BuildOptions {
            workers: 4,
            include_models: true,
        },
        &inputs,
    )
    .unwrap();
    assert_eq!(graph.identity, parallel.identity);
    assert_eq!(graph.diagnostics, parallel.diagnostics);
    assert_eq!(graph.diagnostic_bytes, parallel.diagnostic_bytes);
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("graph.rsel");
    let identity = selector_graph::codec::write(&path, &graph).unwrap();
    let loaded = selector_graph::codec::read_bound(&path, facts.identity).unwrap();
    assert_eq!(identity, loaded.identity);
    assert_eq!(loaded.diagnostics, graph.diagnostics);
    assert_eq!(loaded.diagnostic_bytes, graph.diagnostic_bytes);
    assert_eq!(std::mem::size_of::<selector_graph::GraphDiagnostic>(), 32);
}

#[test]
fn overlay_obligations_preserve_reason_when_metadata_path_is_unavailable() {
    let facts = FactBuilder::new().finish().unwrap();
    let overlay = r#"{"schema_version":"compiler-runtime-bridges/v1","edge_direction":"caller_or_producer_to_callee_or_callback","edges":[{"from_symbol":"missing/a().","to_symbol":"missing/b().","effect":"execution","status":"resolved"}]}"#;
    let inputs = RuntimeInputs {
        overlay_json: Some(overlay),
        ..Default::default()
    };
    let graph = build_with_runtime(
        &facts,
        &BuildOptions {
            workers: 1,
            include_models: true,
        },
        &inputs,
    )
    .unwrap();
    assert_eq!(graph.diagnostics.len(), 1);
    let diagnostic = graph.diagnostics[0];
    assert_eq!(diagnostic.kind, IssueKind::UnresolvedSymbol);
    assert_eq!(
        graph.diagnostic_text(diagnostic.reason),
        "unresolved_or_ambiguous_overlay_endpoint"
    );
    assert_eq!(graph.diagnostic_text(diagnostic.metadata_path), "");
}
