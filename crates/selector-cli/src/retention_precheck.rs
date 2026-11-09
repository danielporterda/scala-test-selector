//! Separate static diagnostic; this never constructs a solver or selection.
use super::*;
use selector_plan::retention::{self, RetentionLimits, UnprovedReason};
use std::mem::size_of;

const MAX_ROWS: usize = 4096;
const TEXT_LIMIT: usize = 512;

pub(super) fn validate(args: &Args) -> Result<()> {
    for key in args.values.keys() {
        if ![
            "facts",
            "graph",
            "output",
            "memory-budget",
            "inventory-rows",
            "progress-jsonl",
            "help",
        ]
        .contains(&key.as_str())
        {
            return Err(format!(
                "retention-precheck does not accept --{key}; it performs no execution or selection"
            )
            .into());
        }
    }
    args.required("facts")?;
    args.required("graph")?;
    args.required("output")?;
    if args.number(
        "memory-budget",
        RetentionLimits::default().memory_budget_bytes,
    )? == 0
        || args.number("inventory-rows", 32)? > MAX_ROWS
    {
        return Err(
            "retention-precheck requires a positive memory budget and at most4096 inventory rows"
                .into(),
        );
    }
    Ok(())
}

fn pin(path: &Path) -> Result<serde_json::Value> {
    let mut file = fs::File::open(path)?;
    let mut h = Sha256::new();
    let mut buffer = [0u8; 64 * 1024];
    let mut bytes = 0u64;
    loop {
        let n = file.read(&mut buffer)?;
        if n == 0 {
            break;
        }
        h.update(&buffer[..n]);
        bytes += n as u64;
    }
    Ok(
        serde_json::json!({"path":path.canonicalize()?,"bytes":bytes,"sha256":ContentHash(h.finalize().into()).to_string()}),
    )
}
fn text(value: &str) -> &str {
    let mut end = value.len().min(TEXT_LIMIT);
    while !value.is_char_boundary(end) {
        end -= 1;
    }
    &value[..end]
}
fn node_json(facts: &FactSnapshot, graph: &ProgramGraph, node: NodeId) -> serde_json::Value {
    if node.is_none() {
        return serde_json::Value::Null;
    }
    let record = graph.nodes[node.index()];
    let symbol = facts.symbols[record.symbol.index()];
    let name = facts.text(symbol.name);
    let context = facts.text(symbol.context);
    let path = if record.file.is_none() {
        ""
    } else {
        facts.path(record.file)
    };
    serde_json::json!({"node":node.0,"symbol_id":record.symbol.0,"symbol":text(name),"context":text(context),"path":text(path),
        "text_truncated":name.len()>TEXT_LIMIT||context.len()>TEXT_LIMIT||path.len()>TEXT_LIMIT})
}

pub(super) fn execute(args: &Args) -> Result<()> {
    validate(args)?;
    let facts_path = args.required("facts")?;
    let graph_path = args.required("graph")?;
    let input_facts = pin(&facts_path)?;
    let input_graph = pin(&graph_path)?;
    let (facts, graph) = read_revision(args, "retention_precheck", &facts_path, &graph_path)?;
    let rows = args.number("inventory-rows", 32)?;
    let total_budget = args.number(
        "memory-budget",
        RetentionLimits::default().memory_budget_bytes,
    )?;
    let defaults = RetentionLimits::default();
    // JSON row metadata is bounded independently of graph size. Reserve its
    // conservative allowance before allocating the library's work arrays.
    let render_bytes = rows
        .checked_mul(4096 + defaults.max_path_edges * 2048)
        .and_then(|n| n.checked_add(facts.suites.len() * size_of::<selector_plan::PlannedRoot>()))
        .ok_or("retention display budget overflow")?;
    let memory = total_budget
        .checked_sub(render_bytes)
        .ok_or("retention display exceeds memory budget")?;
    let limits = RetentionLimits {
        memory_budget_bytes: memory,
        ..defaults
    };
    let roots = retention::catalogue_roots(&facts, &graph)?;
    let started = Instant::now();
    let _progress = stage_progress(args, "retention_precheck", "request");
    let result = retention::precheck(&facts, &graph, &roots, &limits)?;
    result.validate(&facts, &graph)?;
    let elapsed_ns = started.elapsed().as_nanos();
    let eligible = result.eligible_roots();
    let mut displayed = Vec::with_capacity(rows.min(result.roots().len()));
    for (suite, row) in result.roots().iter().enumerate().take(rows) {
        let mut path = Vec::with_capacity(row.path.len as usize);
        for &id in result.path(row).ok_or("retention display path range")? {
            let edge = graph.edges[id.index()];
            let operation = if edge.operation.is_none() {
                serde_json::Value::Null
            } else {
                let op = facts.operations[edge.operation.index()];
                serde_json::json!({"id":edge.operation.0,"opcode":format!("{:?}",op.opcode),"target_symbol_id":op.target.0,
                    "target_symbol":text(facts.symbol_name(op.target)),"span":{"start":op.span.start,"end":op.span.end}})
            };
            path.push(serde_json::json!({"edge":id.0,"source":edge.source.0,"target":edge.target.0,"kind":format!("{:?}",edge.kind),
                "basis":if edge.operation.is_none(){"unconditional_structural_edge"}else{"exact_nonvirtual_operation"},"operation":operation}));
        }
        let guard=row.guard.map(|guard| {
            let issue=graph.issues[guard.issue as usize];
            let detail=if issue.detail.is_none(){""}else{facts.text(issue.detail)};
            serde_json::json!({"issue_id":guard.issue,"kind":format!("{:?}",issue.kind),"scope":if !issue.node.is_none(){"node"}else if !issue.file.is_none(){"file"}else{"global"},
                "boundary":node_json(&facts,&graph,guard.node),"file_id":(!issue.file.is_none()).then_some(issue.file.0),
                "symbol_id":(!issue.symbol.is_none()).then_some(issue.symbol.0),"detail":text(detail),"detail_truncated":detail.len()>TEXT_LIMIT})
        });
        let unproved = row.unproved.map(|reason| match reason {
            UnprovedReason::MissingRoot => "missing_root",
            UnprovedReason::NoStaticGuardPath => "no_static_guard_path_within_limits",
            UnprovedReason::PathBound => "total_path_bound",
        });
        displayed.push(serde_json::json!({"suite_id":suite,"root":node_json(&facts,&graph,row.root.node),"receiver_symbol_id":row.root.receiver.0,
            "static_guard_certified":row.guard.is_some(),"unproved_reason":unproved,"guard":guard,"path":path}));
    }
    if pin(&facts_path)? != input_facts || pin(&graph_path)? != input_graph {
        return Err("retention input changed during diagnostic".into());
    }
    publish_output(args, |out| {
        serde_json::to_writer_pretty(
            out,
            &serde_json::json!({
                "schema_version":1,"report_kind":"retention_precheck","complete":true,"diagnostic_only":true,
                "analysis_not_performed":true,"fixed_point_complete":false,"omission_authority":false,
                "all_roots_known_kept":result.all_roots_known_kept(),
                "scope":{"universe":"admitted_suite_catalogue_only","requested_roots":roots.len(),"changed_seed_analysis_performed":false},
                "counts":{"roots":roots.len(),"eligible":eligible,"unproved":roots.len()-eligible,"rows":displayed.len()},
                "rows_complete":displayed.len()==roots.len(),"paths_bounded":true,
                "limits":{"diagnostic_memory_bytes":total_budget,"borrowed_input_bytes_excluded":true,"max_path_edges":limits.max_path_edges,"max_total_path_edges":limits.max_total_path_edges,"inventory_rows":rows,"text_bytes_per_field":TEXT_LIMIT},
                "metrics":{"elapsed_ns":elapsed_ns,"peak_library_storage_bytes":result.scratch_bytes(),"retained_certificate_bytes":result.owned_bytes(),"reserved_render_bytes":render_bytes,"execution_contexts":0,"transfer_evaluations":0},
                "pins":{"facts":facts.identity.to_string(),"graph":graph.identity.to_string(),"runtime_models":graph.runtime_identity.to_string(),"physical_facts":input_facts,"physical_graph":input_graph,"operators":producers(),"certificate":result.identity().to_string(),"certificate_policy":retention::VERSION},
                "qualification":"Static retention under the current conservative guard policy only. Exact rooted issue paths are not concrete runtime must-execution, changed-code impact, Required status, a solved fixed point or suite exclusion authority. Unproved roots remain unproved. No guarded writers may be removed from a later query using this diagnostic.",
                "roots":displayed
            }),
        )?;
        Ok(())
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn rejects_execution_selection_and_cache_flags() {
        let mut args = Args::default();
        for (key, value) in [("facts", "f"), ("graph", "g"), ("output", "o")] {
            args.values.insert(key.into(), vec![value.into()]);
        }
        validate(&args).unwrap();
        for key in [
            "summary-cache",
            "checkpoint-dir",
            "resume-dir",
            "changed",
            "max-contexts",
            "all-roots",
        ] {
            let mut bad = args.clone();
            bad.values.insert(key.into(), vec!["1".into()]);
            assert!(validate(&bad).is_err(), "{key}");
        }
        args.values
            .insert("inventory-rows".into(), vec!["4097".into()]);
        assert!(validate(&args).is_err());
    }
    #[test]
    fn text_is_bounded_on_utf8_boundary() {
        let long = "é".repeat(300);
        assert!(text(&long).len() <= TEXT_LIMIT);
        assert_eq!(text(&long).chars().count(), 256);
    }
}
