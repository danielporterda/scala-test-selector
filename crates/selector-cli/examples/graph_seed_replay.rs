//! Rebuild retained graphs in memory and compare source seeds without solving.
//!
//! Input directories must each contain enriched.bin, graph.bin and runtime.json.
//! The change list contains only source paths; no output graph is written and
//! this audit grants no suite exclusion authority.
use selector_facts::FactSnapshot;
use selector_graph::ProgramGraph;
use selector_graph_build::{BuildOptions, build_with_runtime, runtime_inputs};
use selector_types::NodeId;
use std::path::Path;

fn execution_edges_match(saved: &ProgramGraph, rebuilt: &ProgramGraph) -> bool {
    fn edges(graph: &ProgramGraph) -> impl Iterator<Item = &selector_graph::EdgeRecord> {
        graph.edges.iter().filter(|edge| edge.kind.is_execution())
    }
    edges(saved).eq(edges(rebuilt))
}

fn compile_incidence(graph: &ProgramGraph) -> Vec<(u32, u32)> {
    let mut rows: Vec<_> = graph
        .edges
        .iter()
        .filter(|edge| !edge.kind.is_execution() && !edge.occurrence.is_none())
        .map(|edge| (edge.occurrence.0, edge.target.0))
        .collect();
    rows.sort_unstable();
    rows
}

fn unmatched(source: &[(u32, u32)], target: &[(u32, u32)]) -> usize {
    let mut candidates = target.iter().peekable();
    let mut missing = 0;
    for row in source {
        while candidates.next_if(|candidate| *candidate < row).is_some() {}
        if candidates.next_if(|candidate| *candidate == row).is_none() {
            missing += 1;
        }
    }
    missing
}

fn entries(facts: &FactSnapshot, graph: &ProgramGraph, ids: &[NodeId]) -> Vec<serde_json::Value> {
    ids.iter()
        .map(|id| {
            let node = graph.nodes[id.index()];
            let symbol = facts.symbols[node.symbol.index()];
            let file = facts.files.get(node.file.index());
            let body = facts.bodies.get(node.body.index());
            serde_json::json!({
                "node": id.0,
                "symbol": facts.text(symbol.name),
                "context": facts.text(symbol.context),
                "graph_path": file.map(|file| facts.text(file.path)),
                "graph_file_hash": file.map(|file| file.source_hash.to_string()),
                "graph_file_flags": file.map(|file| file.flags),
                "declaration_path": facts.files.get(symbol.file.index()).map(|file| facts.text(file.path)),
                "body_hash": body.map(|body| body.body_hash.to_string()),
                "body_flags": body.map(|body| body.flags),
            })
        })
        .collect()
}

fn rebuild(
    directory: &Path,
    facts: &FactSnapshot,
    saved: &ProgramGraph,
) -> Result<(ProgramGraph, serde_json::Value), Box<dyn std::error::Error>> {
    let runtime = runtime_inputs::load_runtime_manifest(&directory.join("runtime.json"), facts)?;
    let rebuilt = build_with_runtime(
        facts,
        &BuildOptions {
            workers: 2,
            include_models: true,
        },
        &runtime.borrow(),
    )?;
    let saved_compile = compile_incidence(saved);
    let rebuilt_compile = compile_incidence(&rebuilt);
    let comparison = serde_json::json!({
        "facts": facts.identity.to_string(),
        "saved_graph": saved.identity.to_string(),
        "rebuilt_in_memory_graph": rebuilt.identity.to_string(),
        "saved_edge_count": saved.edges.len(),
        "rebuilt_edge_count": rebuilt.edges.len(),
        "execution_edge_incidence_unchanged": execution_edges_match(saved, &rebuilt),
        "lost_compile_occurrence_target_incidences": unmatched(&saved_compile, &rebuilt_compile),
        "added_compile_occurrence_target_incidences": unmatched(&rebuilt_compile, &saved_compile),
        "runtime_identity_unchanged": saved.runtime_identity == rebuilt.runtime_identity,
    });
    Ok((rebuilt, comparison))
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    let [base, head, changed] = args.as_slice() else {
        return Err("usage: graph_seed_replay BASE_DIR HEAD_DIR CHANGED_SOURCE_LIST".into());
    };
    let (base, head) = (Path::new(base), Path::new(head));
    let changed = std::fs::read_to_string(changed)?;
    let paths: Vec<_> = changed
        .lines()
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .collect();
    if paths.is_empty() {
        return Err("expected requested source paths".into());
    }
    let read = |directory: &Path| -> Result<_, selector_types::Error> {
        let facts = selector_facts::codec::read(&directory.join("enriched.bin"))?;
        let graph =
            selector_graph::codec::read_bound(&directory.join("graph.bin"), facts.identity)?;
        Ok((facts, graph))
    };
    let (base_facts, base_saved) = read(base)?;
    let (head_facts, head_saved) = read(head)?;
    let saved =
        selector_select::changed_seeds(&base_facts, &base_saved, &head_facts, &head_saved, &paths)?;
    let (base_rebuilt, base_comparison) = rebuild(base, &base_facts, &base_saved)?;
    drop(base_saved);
    let (head_rebuilt, head_comparison) = rebuild(head, &head_facts, &head_saved)?;
    drop(head_saved);
    let rebuilt = selector_select::changed_seeds(
        &base_facts,
        &base_rebuilt,
        &head_facts,
        &head_rebuilt,
        &paths,
    )?;
    let counts = |seeds: &selector_select::ChangeSeeds| {
        serde_json::json!({
            "execution": {"base": seeds.base.len(), "head": seeds.head.len()},
            "compilation": {"base": seeds.base_compile.len(), "head": seeds.head_compile.len()},
            "conservative": seeds.conservative,
        })
    };
    serde_json::to_writer_pretty(
        std::io::stdout().lock(),
        &serde_json::json!({
            "schema": "selector-in-memory-graph-seed-replay/v1",
            "qualification": "Source seed comparison only; changed runtime inputs, solver and suite omission authority are outside this audit.",
            "paths": paths,
            "base": base_comparison,
            "head": head_comparison,
            "saved_graph_seeds": counts(&saved),
            "rebuilt_graph_seeds": counts(&rebuilt),
            "rebuilt_seed_inventory": {
                "base": {
                    "execution": entries(&base_facts, &base_rebuilt, &rebuilt.base),
                    "compilation": entries(&base_facts, &base_rebuilt, &rebuilt.base_compile),
                },
                "head": {
                    "execution": entries(&head_facts, &head_rebuilt, &rebuilt.head),
                    "compilation": entries(&head_facts, &head_rebuilt, &rebuilt.head_compile),
                },
            },
        }),
    )?;
    println!();
    Ok(())
}
