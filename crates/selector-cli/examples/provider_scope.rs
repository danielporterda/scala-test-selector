//! Run one owning test classpath as an isolated diagnostic session.
//! A pinned classpath request and suite catalogue supply the physical evidence.
use selector_facts::{FactSnapshot, codec as facts_codec};
use selector_graph::{ProgramGraph, codec as graph_codec};
use selector_native_effects::{classpath_absence as issuer, provider::VerifiedProvider};
use selector_solve::{ContextPolicy, ExecutionRoot, SolveOptions, provider_scope};
use selector_types::*;
use serde_json::{Value, json};
use std::{path::Path, sync::Arc, time::Instant};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

fn render(
    result: provider_scope::Diagnostic,
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    elapsed_ns: u128,
) -> Value {
    let node = |id: NodeId| {
        let row = &graph.nodes[id.index()];
        json!({
            "node": id.0,
            "symbol": facts.symbol_name(row.symbol),
            "path": if row.file.is_none() { "" } else { facts.path(row.file) },
        })
    };
    let first = result.first_blocked_call.map(|call| {
        json!({
            "source": node(call.source),
            "target": node(call.target),
            "kind": format!("{:?}", call.kind),
            "operation": (!call.operation.is_none()).then_some(call.operation.0),
        })
    });
    json!({
        "graph": result.graph.to_string(),
        "completion": format!("{:?}", result.completion),
        "stop": result.stop.map(|r| format!("{r:?}")),
        "root_impacts": result.root_impacts.into_iter().map(|r| node(r.node)).collect::<Vec<_>>(),
        "guarded_roots": result.guarded_roots.into_iter().map(node).collect::<Vec<_>>(),
        "unscoped_uncertainty": result.unscoped_uncertainty,
        "blocked_nodes": result.blocked_nodes,
        "blocked_calls": result.blocked_calls,
        "blocked_callbacks": result.blocked_callbacks,
        "first_blocked_call": first,
        "contexts": result.counters.contexts,
        "operations": result.counters.operations,
        "pending": result.counters.pending,
        "owned_bytes": result.counters.owned_bytes,
        "elapsed_ns": elapsed_ns,
    })
}

fn main() -> Result<()> {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let prove_only = args.last().is_some_and(|s| s == "--prove-only");
    if prove_only {
        args.pop();
    }
    let [
        facts_path,
        graph_path,
        request,
        side,
        owner,
        source,
        paired,
        contexts,
        workers,
        ..,
    ] = args.as_slice()
    else {
        return Err("provider_scope FACTS GRAPH REQUEST BASE|HEAD OWNER SOURCE PAIRED_REPORT MAX_CONTEXTS WORKERS [VARIANTS] [--prove-only]".into());
    };
    if args.len() > 10 {
        return Err("unexpected argument".into());
    }
    let side = side.to_ascii_lowercase();
    let facts = facts_codec::read(Path::new(facts_path))?;
    let graph = graph_codec::read_bound(Path::new(graph_path), facts.identity)?;
    let report: Value = serde_json::from_reader(std::fs::File::open(paired)?)?;
    if report[format!("{side}_snapshot")].as_str() != Some(&graph.identity.to_string())
        || report[format!("{side}_facts")].as_str() != Some(&facts.identity.to_string())
    {
        return Err("paired seed report does not bind the exact snapshot".into());
    }
    let seeds = report["execution_seeds"][&side]
        .as_array()
        .ok_or("missing execution seeds")?
        .iter()
        .map(|id| {
            let n = id.as_u64().ok_or("bad seed")?;
            Ok(NodeId::checked(n.try_into()?)?)
        })
        .collect::<Result<Vec<_>>>()?;
    let request = issuer::read_request(Path::new(request))?;
    let (options, catalogue) = match side.as_str() {
        "base" => (&request.base, &request.base_catalogue),
        "head" => (&request.head, &request.head_catalogue),
        _ => return Err("side must be base or head".into()),
    };
    let sources: Vec<_> = (0..facts.files.len())
        .map(|i| FileId(i as u32))
        .filter(|&id| facts.path(id) == source)
        .collect();
    if sources.is_empty() {
        return Err("no exact source path in facts".into());
    }
    let suites: Vec<_> = facts
        .suites
        .iter()
        .enumerate()
        .filter(|(_, s)| facts.text(facts.symbols[s.symbol.index()].context) == owner)
        .map(|(i, _)| SuiteId(i as u32))
        .collect();
    if suites.is_empty() {
        return Err("no exact suite classpath owner in facts".into());
    }
    let start = Instant::now();
    let mut provider = VerifiedProvider::admit_inventory(options)?;
    let issued = issuer::issue_runtime_scope(
        issuer::Side {
            facts: &facts,
            provider: &mut provider,
            catalogue,
            source_files: &sources,
            suites: &suites,
        },
        SelectionContract::owning_test_classpath(),
        issuer::Limits::default(),
    )?;
    drop(provider);
    if issued.suites().len() != suites.len() {
        let mut reasons = std::collections::BTreeMap::new();
        for row in issued.denials() {
            *reasons.entry(format!("{:?}", row.reason)).or_insert(0usize) += 1;
        }
        return Err(format!(
            "scope proven for {} of {} roots; denied: {reasons:?}",
            issued.suites().len(),
            suites.len(),
        )
        .into());
    }
    let absent = issued
        .sources()
        .iter()
        .map(|s| s.file)
        .chain(issued.product_files().iter().map(|f| f.file))
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let roots: Arc<[ExecutionRoot]> = suites
        .iter()
        .map(|id| {
            let suite = &facts.suites[id.index()];
            let node = graph
                .node_for_symbol(suite.symbol)
                .ok_or("suite missing from graph")?;
            Ok(ExecutionRoot {
                node,
                receiver: suite.symbol,
            })
        })
        .collect::<Result<Vec<_>>>()?
        .into();
    let proof_ns = start.elapsed().as_nanos();
    let absent_graph_nodes = graph
        .nodes
        .iter()
        .filter(|node| absent.binary_search(&node.file).is_ok())
        .count();
    let mut options = SolveOptions {
        workers: workers.parse()?,
        max_contexts: contexts.parse()?,
        memory_budget_bytes: 8 * 1024 * 1024 * 1024,
        ..SolveOptions::default()
    };
    if let Some(variants) = args.get(9) {
        options.context_policy = ContextPolicy::BoundedArguments {
            max_variants_per_receiver: variants.parse()?,
        };
    }
    let run = |absent: &[FileId]| {
        let start = Instant::now();
        let diagnostic =
            provider_scope::diagnose(&facts, &graph, &options, roots.clone(), absent, &seeds)?;
        Ok::<_, Error>(render(
            diagnostic,
            &facts,
            &graph,
            start.elapsed().as_nanos(),
        ))
    };
    let (same_frontier_unfiltered, same_frontier_filtered) = if prove_only {
        (None, None)
    } else {
        eprintln!(
            "verified {} roots; running identical frontier with and without provider mask",
            roots.len()
        );
        let unfiltered = run(&[])?;
        eprintln!("unfiltered frontier complete; running provider mask");
        (Some(unfiltered), Some(run(&absent)?))
    };
    issued.revalidate()?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema": "selector-provider-scope-diagnostic/v1",
            "authority": "diagnostic_only",
            "side": side,
            "owner": owner,
            "source": source,
            "facts": facts.identity.to_string(),
            "graph": graph.identity.to_string(),
            "issuer": issued.identity().to_string(),
            "request": request.identity.to_string(),
            "absent_files": absent.into_iter().map(|f| facts.path(f)).collect::<Vec<_>>(),
            "absent_graph_nodes": absent_graph_nodes,
            "proof_elapsed_ns": proof_ns,
            "roots": suites.iter().map(|id| facts.text(facts.suites[id.index()].name)).collect::<Vec<_>>(),
            "seeds": seeds.iter().map(|id| id.0).collect::<Vec<_>>(),
            "same_frontier_unfiltered": same_frontier_unfiltered,
            "same_frontier_filtered": same_frontier_filtered,
        }))?
    );
    Ok(())
}
