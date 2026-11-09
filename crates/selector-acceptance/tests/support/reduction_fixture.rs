use selector_extract::{ExtractOptions, import_capture};
use selector_facts::FactSnapshot;
use selector_graph::ProgramGraph;
use std::path::{Path, PathBuf};

pub fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

pub fn snapshot(directory: &Path, workers: usize) -> (FactSnapshot, ProgramGraph) {
    let mut facts = import_capture(
        &directory.join("documents.jsonl"),
        Some(&directory.join("syntax.jsonl")),
        &ExtractOptions {
            workers,
            catalogue: Some(directory.join("catalogue.json")),
            ..Default::default()
        },
    )
    .unwrap();
    let mut binary = selector_graph_build::binary_inputs::load_binary_manifest(
        &directory.join("binary.json"),
        &facts,
    )
    .unwrap();
    selector_graph_build::binary_inputs::augment_binary_facts(&mut facts, &mut binary).unwrap();
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
