//! A single execution frontier is diagnostic evidence, never selection authority.
mod census;

use super::*;
use selector_solve::{SolveEvent, SolveObserver};
use std::sync::Mutex;

const ROW_LIMIT: usize = 32;

pub(super) fn validate(args: &Args) -> Result<()> {
    const ALLOWED: &[&str] = &[
        "facts",
        "graph",
        "root-node",
        "root-symbol",
        "root-context",
        "receiver-symbol",
        "output",
        "workers",
        "memory-budget",
        "max-contexts",
        "max-context-variants",
        "max-steps",
        "progress-jsonl",
        "stop-after-round",
        "checkpoint-dir",
        "resume-dir",
        "summary-cache",
        "replay-bundle",
        "replay-node",
        "replay-context",
        "replay-family",
        "replay-family-contexts",
        "census-capacity",
        "census-stride",
        "current-local-audit",
        "audit-max-contexts",
        "audit-max-steps",
        "audit-memory-budget",
        "help",
    ];
    for name in args.values.keys() {
        if !ALLOWED.contains(&name.as_str()) {
            return Err(format!("probe-root does not accept --{name}; diagnostic execution has no selection authority").into());
        }
    }
    args.required("facts")?;
    args.required("graph")?;
    match (args.value("root-node"), args.value("root-symbol")) {
        (Some(_), Some(_)) => {
            return Err("--root-node and --root-symbol are mutually exclusive".into());
        }
        (None, None) => return Err("one of --root-node or --root-symbol is required".into()),
        (Some(node), None) => {
            node.parse::<u32>()?;
        }
        (None, Some("")) => return Err("--root-symbol cannot be empty".into()),
        (None, Some(_)) => {}
    }
    if args.value("root-context").is_some() && args.value("root-symbol").is_none() {
        return Err("--root-context requires --root-symbol".into());
    }
    args.solve_options()?;
    if !args.flag("current-local-audit")
        && [
            "audit-max-contexts",
            "audit-max-steps",
            "audit-memory-budget",
        ]
        .iter()
        .any(|name| args.flag(name))
    {
        return Err("--audit-* limits require --current-local-audit".into());
    }
    current_audit_options(args)?;
    Ok(())
}

fn current_audit_options(
    args: &Args,
) -> Result<Option<selector_solve::finalization::CurrentAuditOptions>> {
    if !args.flag("current-local-audit") {
        return Ok(None);
    }
    let defaults = selector_solve::finalization::CurrentAuditOptions::default();
    Ok(Some(selector_solve::finalization::CurrentAuditOptions {
        max_contexts: args.number("audit-max-contexts", defaults.max_contexts)?,
        max_operations: u64::try_from(
            args.number("audit-max-steps", defaults.max_operations as usize)?,
        )?,
        scratch_budget_bytes: args.number("audit-memory-budget", defaults.scratch_budget_bytes)?,
    }))
}

fn resolve_root(args: &Args, facts: &FactSnapshot, graph: &ProgramGraph) -> Result<NodeId> {
    if let Some(raw) = args.value("root-node") {
        let node = NodeId(raw.parse()?);
        graph
            .nodes
            .get(node.index())
            .ok_or("--root-node is outside graph inventory")?;
        return Ok(node);
    }
    let name = args
        .value("root-symbol")
        .ok_or("--root-symbol is required")?;
    let context = args.value("root-context");
    let mut matches = facts.symbols.iter().enumerate().filter(|(_, symbol)| {
        facts.text(symbol.name) == name
            && context.is_none_or(|context| facts.text(symbol.context) == context)
    });
    let (index, symbol) = matches
        .next()
        .ok_or("--root-symbol has no exact match in the admitted compiler context")?;
    if matches.next().is_some() {
        return Err("--root-symbol is ambiguous; pass an exact --root-context identifying one admitted compiler symbol".into());
    }
    let node = graph
        .node_for_symbol(SymbolId::checked(index)?)
        .ok_or("--root-symbol has no bound graph node")?;
    let bound = graph
        .nodes
        .get(node.index())
        .and_then(|node| facts.symbols.get(node.symbol.index()))
        .ok_or("--root-symbol has an invalid graph binding")?;
    if facts.text(bound.name) != name || facts.text(bound.context) != facts.text(symbol.context) {
        return Err(
            "--root-symbol graph binding does not preserve the exact compiler identity".into(),
        );
    }
    Ok(node)
}

#[derive(Debug)]
struct Observer {
    progress: diagnostics::Observer,
    last: Mutex<Option<SolveEvent>>,
}
impl SolveObserver for Observer {
    fn observe(&self, event: SolveEvent) {
        *self.last.lock().expect("probe observer lock") = Some(event);
        self.progress.observe(event);
    }
    fn work_row_with_origin(
        &self,
        row: selector_solve::WorkRow,
        origin: selector_solve::WorkOrigin<'_>,
    ) {
        self.progress.work_row_with_origin(row, origin);
    }
}

fn receiver(
    args: &Args,
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    node: NodeId,
) -> Result<(SymbolId, &'static str)> {
    let root = graph
        .nodes
        .get(node.index())
        .ok_or("--root-node is outside graph inventory")?;
    let owner = facts
        .symbols
        .get(root.symbol.index())
        .ok_or("probe root symbol binding")?;
    if let Some(name) = args.value("receiver-symbol") {
        let mut matches = facts.symbols.iter().enumerate().filter(|(_, symbol)| {
            symbol.context == owner.context && facts.text(symbol.name) == name
        });
        let (index, symbol) = matches
            .next()
            .ok_or("--receiver-symbol has no exact match in the root compiler context")?;
        if matches.next().is_some() {
            return Err("--receiver-symbol is ambiguous in the root compiler context".into());
        }
        if !matches!(symbol.kind, 10..=14) {
            return Err(
                "--receiver-symbol must identify an admitted class, trait or object".into(),
            );
        }
        return Ok((SymbolId::checked(index)?, "explicit_exact_symbol"));
    }
    if matches!(owner.kind, 10..=14) && facts.suites.iter().any(|suite| suite.symbol == root.symbol)
    {
        Ok((root.symbol, "runnable_suite_symbol"))
    } else {
        Ok((SymbolId::NONE, "none"))
    }
}

fn node_json(facts: &FactSnapshot, graph: &ProgramGraph, node: NodeId) -> serde_json::Value {
    let record = graph.nodes[node.index()];
    let symbol = &facts.symbols[record.symbol.index()];
    serde_json::json!({"node":node.0,"symbol_id":record.symbol.0,
        "symbol":facts.symbol_name(record.symbol),
        "context":(!symbol.context.is_none()).then(||facts.text(symbol.context)),
        "path":(!record.file.is_none()).then(||facts.path(record.file))})
}

fn bounded_audit_text(text: &str) -> (&str, bool) {
    const MAX_BYTES: usize = 512;
    if text.len() <= MAX_BYTES {
        return (text, false);
    }
    let mut end = MAX_BYTES;
    while !text.is_char_boundary(end) {
        end -= 1;
    }
    (&text[..end], true)
}

fn current_audit_json(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    audit: selector_solve::finalization::CurrentLocalTransferAudit,
) -> std::result::Result<serde_json::Value, Error> {
    let mut json =
        serde_json::to_value(&audit).map_err(|_| Error::Invalid("current audit serialization"))?;
    let rows = json["first_current_site_ranking"]["top"]
        .as_array_mut()
        .ok_or(Error::Invalid("current audit ranking"))?;
    for (value, row) in rows.iter_mut().zip(&audit.first_current_site_ranking.top) {
        let node = graph
            .nodes
            .get(row.node as usize)
            .ok_or(Error::Invalid("current audit node"))?;
        let symbol = facts
            .symbols
            .get(node.symbol.index())
            .ok_or(Error::Invalid("current audit symbol"))?;
        let (name, a) = bounded_audit_text(facts.symbol_name(node.symbol));
        let (context, b) = bounded_audit_text(facts.text(symbol.context));
        let (path, c) = bounded_audit_text(if node.file.is_none() {
            ""
        } else {
            facts.path(node.file)
        });
        let native =
            !node.body.is_none() && facts.bodies[node.body.index()].flags & BODY_BINARY_RECIPE != 0;
        value["definition"] = serde_json::json!({"symbol_id":node.symbol.0,"symbol":name,
            "context":context,"path":path,"text_truncated":a||b||c,
            "recipe_ownership":if node.body.is_none(){"none"}else if native{"native_binary"}else{"source_or_compiler"}});
        value["operation_detail"] = if let Some(id) = row.operation {
            let op = facts
                .operations
                .get(id as usize)
                .ok_or(Error::Invalid("current audit operation"))?;
            if op.body != node.body
                || !facts.bodies[node.body.index()]
                    .operations
                    .range()
                    .contains(&(id as usize))
            {
                return Err(Error::Invalid("current audit operation owner"));
            }
            let (target, truncated) = bounded_audit_text(if op.target.is_none() {
                ""
            } else {
                facts.symbol_name(op.target)
            });
            serde_json::json!({"id":id,"opcode":format!("{:?}",op.opcode),
                "span":{"start":op.span.start,"end":op.span.end},
                "target_symbol_id":(!op.target.is_none()).then_some(op.target.0),
                "target_symbol":target,"text_truncated":truncated})
        } else {
            serde_json::Value::Null
        };
    }
    Ok(json)
}

fn boundary_json(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    cause: &selector_result::RootGuardEvidence,
) -> Result<serde_json::Value> {
    let operation = if let Some(site) = cause.runtime {
        site.validate()?;
        if site.kind != cause.kind {
            return Err("probe runtime issue kind".into());
        }
        if site.operation.is_none() {
            None
        } else {
            let op = facts
                .operations
                .get(site.operation.index())
                .ok_or("probe runtime operation")?;
            let node = &graph.nodes[cause.node.index()];
            if node.body != op.body || !site.reason.accepts_opcode(op.opcode) {
                return Err("probe runtime operation ownership".into());
            }
            let body = &facts.bodies[op.body.index()];
            Some(
                serde_json::json!({"id":site.operation.0,"opcode":format!("{:?}",op.opcode),
                "path":(!body.file.is_none()).then(||facts.path(body.file)),
                "span":{"start":op.span.start,"end":op.span.end}}),
            )
        }
    } else {
        None
    };
    Ok(
        serde_json::json!({"boundary":node_json(facts,graph,cause.node),
        "kind":format!("{:?}",cause.kind),
        "detail":(!cause.detail.is_none()).then(||facts.text(cause.detail)),
        "runtime":cause.runtime.map(|site|serde_json::json!({"reason":site.reason.as_str(),
            "operation":operation})),"exemplar_only":true}),
    )
}

pub(super) fn execute(args: &Args) -> Result<Completion> {
    let (facts, graph) = read_revision(
        args,
        "probe",
        &args.required("facts")?,
        &args.required("graph")?,
    )?;
    verify_binding(&facts, &graph)?;
    let node = resolve_root(args, &facts, &graph)?;
    let (receiver, receiver_source) = receiver(args, &facts, &graph, node)?;
    let mut options = args.solve_options()?;
    if !args.flag("workers") {
        options.workers = 1;
    }
    if !args.flag("memory-budget") {
        options.memory_budget_bytes = 64 * 1024 * 1024;
    }
    if !args.flag("max-contexts") {
        options.max_contexts = 10_000;
    }
    if !args.flag("max-steps") {
        options.max_steps = 1_000_000;
    }
    options.retain_context_evidence = false;
    options.execution_roots = Some(Arc::from([selector_solve::ExecutionRoot {
        node,
        receiver,
    }]));
    let control = Arc::new(selector_solve::SolveControl::default());
    let _signals = diagnostics::SignalGuard::install()?;
    if let Some(round) = args.value("stop-after-round") {
        control.checkpoint_after_round(round.parse()?);
    }
    let observer = Arc::new(Observer {
        progress: diagnostics::Observer::new(
            "probe",
            args.events.clone().unwrap_or_default(),
            control.clone(),
            &options,
        ),
        last: Mutex::new(None),
    });
    options.control = Some(control);
    options.observer = Some(observer.clone());
    let runtime = if let Some(directory) = args.path("summary-cache") {
        selector_solve::SolverRuntime::with_cache_directory(
            &options,
            &directory,
            ContentHash::from_hex(env!("SELECTOR_SOLVE_PRODUCER"))?,
        )?
    } else {
        selector_solve::SolverRuntime::new(&options)?
    };
    let audit_limits = current_audit_options(args)?;
    let (result, (runtime_first_sites, finalization_census, current_local_audit)) =
        analyze_revision_with_inspection(
            args,
            "head",
            &facts,
            &graph,
            selector_solve::AnalysisSeeds {
                execution: &[],
                declarations: &[],
            },
            &[],
            &options,
            &runtime,
            |session, result| {
                let first_sites = census::first_runtime_sites(
                    &facts,
                    &graph,
                    session.first_runtime_issue_sites(),
                    session.context_count(),
                    session.work_counters().evaluations,
                    session.work_counters().reevaluations,
                    result.completion != Completion::ResourceLimited,
                )?;
                let finalization = session.finalization_census(result)?;
                let audit = if let Some(limits) = audit_limits {
                    let _progress = stage_progress(args, "current_local_transfer_audit", "probe");
                    Some(current_audit_json(
                        &facts,
                        &graph,
                        session.audit_current_local_transfers(limits)?,
                    )?)
                } else {
                    None
                };
                Ok((first_sites, finalization, audit))
            },
        )?;
    if result.evidence.requested_roots != [selector_result::AnalyzedRoot { node, receiver }] {
        return Err("probe result changed the exact requested execution frontier".into());
    }
    let last = observer
        .last
        .lock()
        .map_err(|_| "probe observer lock")?
        .ok_or("probe has no solver event")?;
    let counters = last.counters;
    let boundaries = result
        .evidence
        .guard_causes
        .iter()
        .take(ROW_LIMIT)
        .map(|cause| boundary_json(&facts, &graph, cause))
        .collect::<Result<Vec<_>>>()?;
    let obligations = result
        .obligations
        .iter()
        .take(ROW_LIMIT)
        .map(|row| {
            serde_json::json!({
        "kind":format!("{:?}",row.kind),"symbol":facts.symbol_name(row.symbol),
        "path":(!row.file.is_none()).then(||facts.path(row.file)),
        "detail":(!row.detail.is_none()).then(||facts.text(row.detail))})
        })
        .collect::<Vec<_>>();
    let metadata = graph
        .diagnostics
        .iter()
        .filter(|row| {
            result
                .evidence
                .guard_causes
                .iter()
                .any(|cause| cause.node == row.node)
        })
        .take(ROW_LIMIT + 1)
        .collect::<Vec<_>>();
    let stop_detail = last.stop.map(|reason| {
        let (resource, observed, limit) = match reason {
            selector_solve::StopReason::ContextLimit =>
                (Some("contexts"), Some(counters.contexts), Some(options.max_contexts as u64)),
            selector_solve::StopReason::StepLimit =>
                (Some("operations"), Some(counters.operations), Some(options.max_steps)),
            selector_solve::StopReason::MemoryLimit =>
                (Some("query_owned_bytes"), Some(counters.owned_bytes), Some(options.memory_budget_bytes as u64)),
            _ => (None, None, None),
        };
        serde_json::json!({"reason":format!("{reason:?}"),"resource":resource,"observed":observed,"limit":limit})
    });
    let guard_census = census::build(
        &facts,
        &result.obligations,
        &result.evidence.guard_causes,
        result.completion != Completion::ResourceLimited,
    )?;
    let metrics = result.metrics;
    let completion = result.completion;
    publish_output(args, |out| {
        serde_json::to_writer_pretty(
            out,
            &serde_json::json!({
            "schema_version":1,"report_kind":"root_execution_probe","diagnostic_only":true,
            "omission_authority":false,"fixed_point_complete":completion!=Completion::ResourceLimited,
            "root":{"binding":node_json(&facts,&graph,node),"receiver_symbol_id":(!receiver.is_none()).then_some(receiver.0),
                "receiver_symbol":(!receiver.is_none()).then(||facts.symbol_name(receiver)),"receiver_source":receiver_source},
            "scope":{"requested_roots":1,"catalogue_evaluated":false,"unrequested_roots":"not_analyzed"},
            "pins":{"facts":facts.identity.to_string(),"graph":graph.identity.to_string(),"runtime_models":graph.runtime_identity.to_string(),
                "revision":facts.text(facts.revision),"operators":producers(),
                "probe_source":ContentHash(Sha256::digest(include_bytes!("probe.rs")).into()).to_string(),
                "guard_census_source":ContentHash(Sha256::digest(include_bytes!("probe/census.rs")).into()).to_string()},
            "limits":{"query_owned_bytes":options.memory_budget_bytes,"contexts":options.max_contexts,"operations":options.max_steps,
                "workers":runtime.workers(),"input_snapshot_bytes_excluded":true},
            "completion":format!("{completion:?}"),"stop":last.stop.map(|stop|format!("{stop:?}")),"stop_detail":stop_detail,
            "guarded":result.guarded_roots.contains(&node),"unscoped_uncertainty":result.unscoped_uncertainty,
            "metrics":{"states":metrics.states,"operations":metrics.edge_visits,"owned_bytes":metrics.owned_bytes,
                "elapsed_ns":metrics.elapsed_ns,"contexts":counters.contexts,"evaluations":counters.evaluations,
                "reevaluations":counters.reevaluations,"dispatch_targets":counters.dispatch_targets,"callback_targets":counters.callback_targets,
                "pending":counters.pending,"widened_contexts":counters.widened_contexts,"round":last.round},
            "boundaries":boundaries,"boundaries_truncated":result.evidence.guard_causes.len()>ROW_LIMIT,
            "obligations":obligations,"obligations_total":result.obligations.len(),"obligations_truncated":result.obligations.len()>ROW_LIMIT,
            "guard_census":guard_census,
            "runtime_first_site_census":runtime_first_sites,
            "finalization_census":finalization_census,
            "current_local_transfer_audit":current_local_audit,
            "static_metadata":metadata.iter().take(ROW_LIMIT).map(|row|serde_json::json!({"node":row.node.0,
                "kind":format!("{:?}",row.kind),"reason":graph.diagnostic_text(row.reason),"metadata_path":graph.diagnostic_text(row.metadata_path)})).collect::<Vec<_>>(),
            "static_metadata_truncated":metadata.len()>ROW_LIMIT}),
        )?;
        Ok(())
    })?;
    Ok(completion)
}
