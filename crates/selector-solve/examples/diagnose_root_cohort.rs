//! Replay a small mixed cohort from a saved snapshot without rerunning facts
//! or graph production. Only root impact and uncertainty diagnostics come out.
//!
//! Usage: diagnose_root_cohort FACTS GRAPH CONTEXT_LIMIT ROOT_IDS SEED_IDS
//! The last two arguments are comma-separated node IDs from this snapshot.
use selector_solve::{ContextPolicy, ExecutionRoot, SolveOptions, provider_scope};
use selector_types::NodeId;
use std::path::Path;

fn node_ids(input: &str) -> Result<Vec<NodeId>, Box<dyn std::error::Error>> {
    let mut nodes = input
        .split(',')
        .map(|field| field.parse::<u32>().map(NodeId))
        .collect::<Result<Vec<_>, _>>()?;
    nodes.sort_unstable();
    if nodes.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err("duplicate node ID".into());
    }
    Ok(nodes)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    let [facts_path, graph_path, limit, roots, seeds] = args.as_slice() else {
        return Err(
            "usage: diagnose_root_cohort FACTS GRAPH CONTEXT_LIMIT ROOT_IDS SEED_IDS".into(),
        );
    };
    let facts = selector_facts::codec::read(Path::new(facts_path))?;
    let graph = selector_graph::codec::read_bound(Path::new(graph_path), facts.identity)?;
    let roots = node_ids(roots)?
        .into_iter()
        .map(|node| {
            let mut suites = facts
                .suites
                .iter()
                .filter(|suite| graph.node_for_symbol(suite.symbol) == Some(node));
            let suite = suites.next().ok_or("node is not a captured suite root")?;
            if suites.next().is_some() {
                return Err("node has ambiguous suite ownership");
            }
            Ok(ExecutionRoot {
                node,
                receiver: suite.symbol,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let seeds = node_ids(seeds)?;
    let options = SolveOptions {
        workers: 1,
        memory_budget_bytes: 4 * 1024 * 1024 * 1024,
        max_contexts: limit.parse()?,
        context_policy: ContextPolicy::BoundedArguments {
            max_variants_per_receiver: 4,
        },
        ..Default::default()
    };
    let result =
        provider_scope::diagnose(&facts, &graph, &options, roots.clone().into(), &[], &seeds)?;
    let decisions: Vec<_> = roots.iter().map(|root| {
        serde_json::json!({
            "node":root.node.0,
            "receiver":root.receiver.0,
            "observed_impact":result.root_impacts.iter().any(|impact| impact.node==root.node && impact.receiver==root.receiver),
            "scoped_guard":result.guarded_roots.binary_search(&root.node).is_ok(),
        })
    }).collect();
    println!(
        "{}",
        serde_json::json!({
            "schema":"selector-root-cohort-diagnostic/v1",
            "graph":result.graph.to_string(),
            "seeds":seeds.iter().map(|node|node.0).collect::<Vec<_>>(),
            "completion":format!("{:?}",result.completion),
            "stop":format!("{:?}",result.stop),
            "unscoped_uncertainty":result.unscoped_uncertainty,
            "contexts":result.counters.contexts,
            "operations":result.counters.operations,
            "pending":result.counters.pending,
            "roots":decisions,
            "exclusion_authority":false,
        })
    );
    Ok(())
}
