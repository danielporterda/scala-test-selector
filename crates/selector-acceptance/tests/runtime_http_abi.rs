//! ABI projection regression only: this historical fixture explicitly omits
//! references/synthetics. Its bridge output is not full selector soundness proof.
use selector_extract::{ExtractOptions, import_capture};
use selector_models::runtime::{RuntimeInputs, RuntimeSource, contribute};
use selector_types::*;
use serde_json::Value;
use std::io::Write;
use std::path::PathBuf;

#[test]
fn frozen_compiler_http_abi_projection_preserves_real_generated_runtime_joins() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../fixtures/runtime-http-abi/original.json.gz");
    let reader = flate2::read::GzDecoder::new(std::fs::File::open(path).unwrap());
    let fixture: Value = serde_json::from_reader(reader).unwrap();
    let sources = fixture["sources"].as_object().unwrap();
    let directory = tempfile::tempdir().unwrap();
    let capture = directory.path().join("documents.jsonl");
    let mut output = std::io::BufWriter::new(std::fs::File::create(&capture).unwrap());
    for record in fixture["documents"].as_array().unwrap() {
        let mut row = record.clone();
        let path = row["path"].as_str().unwrap().to_owned();
        row["revision"] = fixture["revision"].clone();
        row["source_text"] = sources[&path].clone();
        row["source_md5"] = row["document"]["md5"].clone();
        row["source_md5_matches"] = Value::Bool(true);
        // Leave absent original context metadata absent, rather than inventing
        // a target context that the frozen ABI projection did not capture.
        serde_json::to_writer(&mut output, &row).unwrap();
        writeln!(output).unwrap();
    }
    output.flush().unwrap();
    let facts = import_capture(
        &capture,
        None,
        &ExtractOptions {
            workers: 2,
            ..ExtractOptions::default()
        },
    )
    .unwrap();
    let inputs = RuntimeInputs {
        sources: sources
            .iter()
            .map(|(path, text)| RuntimeSource {
                path,
                text: text.as_str().unwrap(),
            })
            .collect(),
        ..RuntimeInputs::default()
    };
    let nodes = (0..facts.symbols.len())
        .map(|index| NodeId(index as u32))
        .collect::<Vec<_>>();
    let runtime = contribute(&facts, &nodes, &inputs).unwrap();
    assert_eq!(
        runtime.model.edges.len(),
        55,
        "native ABI joins differ from frozen projection"
    );
    assert_eq!(
        runtime.diagnostics.len(),
        2,
        "unresolved endpoints must stay explicit"
    );
    assert!(
        runtime
            .model
            .edges
            .iter()
            .all(|edge| edge.kind == EdgeKind::RuntimeBridge)
    );
    let graph = selector_graph_build::build_with_runtime(
        &facts,
        &selector_graph_build::BuildOptions {
            workers: 4,
            include_models: true,
        },
        &inputs,
    )
    .unwrap();
    assert_eq!(
        graph
            .edges
            .iter()
            .filter(|edge| edge.kind == EdgeKind::RuntimeBridge)
            .count(),
        55
    );
}
