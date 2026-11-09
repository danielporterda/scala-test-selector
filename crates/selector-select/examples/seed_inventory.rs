//! Inspect the exact source-seed inputs to a paired query without running it.
//!
//! The list must contain only requested source paths. Auxiliary runtime seeds,
//! suite selection and exclusion authority are intentionally outside this tool.
use std::io::{self, Write};
use std::path::Path;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let paths: Vec<_> = std::env::args_os().skip(1).collect();
    let [base_facts, base_graph, head_facts, head_graph, changed] = paths.as_slice() else {
        return Err(
            "usage: seed_inventory BASE_FACTS BASE_GRAPH HEAD_FACTS HEAD_GRAPH CHANGED_LIST".into(),
        );
    };
    let before = selector_facts::codec::read(Path::new(base_facts))?;
    let after = selector_facts::codec::read(Path::new(head_facts))?;
    let before_graph = selector_graph::codec::read_bound(Path::new(base_graph), before.identity)?;
    let after_graph = selector_graph::codec::read_bound(Path::new(head_graph), after.identity)?;
    let changed = std::fs::read_to_string(changed)?;
    let changed: Vec<_> = changed
        .lines()
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .collect();
    if changed.is_empty() {
        return Err("expected at least one requested source path".into());
    }
    let seeds =
        selector_select::changed_seeds(&before, &before_graph, &after, &after_graph, &changed)?;
    let mut out = io::BufWriter::new(io::stdout().lock());
    writeln!(
        out,
        "# requested_source_only; conservative={}; base={}; head={}",
        seeds.conservative, before_graph.identity, after_graph.identity
    )?;
    for (side, facts, graph, execution, compilation) in [
        (
            "base",
            &before,
            &before_graph,
            seeds.base,
            seeds.base_compile,
        ),
        ("head", &after, &after_graph, seeds.head, seeds.head_compile),
    ] {
        for (kind, ids) in [("execution", execution), ("compilation", compilation)] {
            for node in ids {
                let record = graph.nodes[node.index()];
                let symbol = facts.symbols[record.symbol.index()];
                let file = if record.file.is_none() {
                    ""
                } else {
                    facts.path(record.file)
                };
                writeln!(
                    out,
                    "{side}\t{kind}\t{}\t{:?}\t{:?}\t{:?}",
                    node.0,
                    facts.text(symbol.name),
                    facts.text(symbol.context),
                    file
                )?;
            }
        }
    }
    Ok(())
}
