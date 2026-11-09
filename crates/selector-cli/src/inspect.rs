//! Read-only checkpoint diagnostics cannot resume or publish analysis results.
use super::*;
use selector_solve::continuation::inspection::{CheckpointView, InspectionLimits};

pub(super) fn execute(args: &Args) -> Result<()> {
    let (facts, graph) = read_revision(
        args,
        "checkpoint",
        &args.required("facts")?,
        &args.required("graph")?,
    )?;
    let mut limits = InspectionLimits::default();
    limits.memory_budget_bytes = args.number("memory-budget", limits.memory_budget_bytes)?;
    limits.max_artifact_bytes = args.number(
        "max-checkpoint-bytes",
        usize::try_from(limits.max_artifact_bytes)?,
    )? as u64;
    limits.max_contexts = args.number("max-contexts", limits.max_contexts)?;
    let top_rows = args.number("inventory-rows", 32)?;
    let _progress = stage_progress(args, "checkpoint_inspection", "checkpoint");
    let view = CheckpointView::open(&facts, &graph, &args.required("checkpoint")?, &limits)?;
    if let Some(node) = args.value("root-node") {
        if args.path("replay-bundle").is_some() {
            return Err(
                "root frontier inspection and replay export are separate operations".into(),
            );
        }
        let target = args
            .value("target-node")
            .map(str::parse)
            .transpose()?
            .map(NodeId);
        let frontier = view.root_frontier(NodeId(node.parse()?), target, top_rows)?;
        let header = view.header();
        #[derive(serde::Serialize)]
        struct Report<'a> {
            schema_version: u32,
            report_kind: &'static str,
            mode: &'static str,
            selection_authority: bool,
            basis: &'static str,
            checkpoint: serde_json::Value,
            frontier: selector_solve::continuation::inspection::RootFrontier<'a>,
        }
        let report = Report {
            schema_version: 1,
            report_kind: "checkpoint_root_frontier",
            mode: "inspection_only",
            selection_authority: false,
            basis: "Reachability through retained abstract context calls; recorded runtime sites are the first saved issue per context, not a current audit. Missing paths do not prove absence.",
            checkpoint: serde_json::json!({
                "artifact": header.artifact.to_string(),
                "producer": header.producer.to_string(),
                "facts": header.facts.to_string(),
                "graph": header.graph.to_string(),
                "version": header.version,
                "recorded_completion": format!("{:?}", header.completion),
                "recorded_stop": header.stop.map(|stop| format!("{stop:?}")),
            }),
            frontier,
        };
        return publish_output(args, |out| {
            serde_json::to_writer_pretty(out, &report)?;
            Ok(())
        });
    }
    if args.value("target-node").is_some() {
        return Err("--target-node requires --root-node for checkpoint inspection".into());
    }
    let mut rows = Vec::new();
    let summary=view.visit_inventory(top_rows,|row,origin| {
        rows.push(serde_json::json!({"node":row.node.0,"symbol":origin.symbol,"context":origin.context,"path":origin.path,
            "contexts":row.contexts,"receiver_variants":row.receiver_variants,
            "max_argument_frames_per_receiver":row.max_argument_frames_per_receiver,
            "largest_receiver_context":row.largest_receiver_context.0,"largest_receiver_variants":row.largest_receiver_variants,
            "evaluated_contexts":row.evaluated_contexts,"widened_contexts":row.widened_contexts,
            "publication_versions":row.publication_versions}));
    })?;
    let header = view.header();
    let context_policy = match header.context_policy {
        selector_solve::ContextPolicy::Exact => serde_json::json!({"kind":"exact"}),
        selector_solve::ContextPolicy::BoundedArguments {
            max_variants_per_receiver,
        } => {
            serde_json::json!({"kind":"bounded_arguments","max_variants_per_receiver":max_variants_per_receiver})
        }
    };
    if let Some(directory) = args.path("replay-bundle") {
        let node = NodeId(
            args.value("replay-node")
                .ok_or("--replay-node is required with --replay-bundle")?
                .parse()?,
        );
        let context = args
            .value("replay-context")
            .map(|value| value.parse::<u32>().map(ContextId))
            .transpose()?;
        if args.flag("replay-family") {
            let report = view.export_replay_family(
                node,
                context,
                &directory,
                &selector_solve::replay::ReplayLimits::default(),
                args.number("replay-family-contexts", 64)?,
            )?;
            eprintln!(
                "{}",
                serde_json::json!({"stage":"transfer_replay_family_export","mode":"checkpoint_inspection",
                "recorded_producer":header.producer.to_string(),"operator_producer":env!("SELECTOR_SOLVE_PRODUCER"),"directory":directory,"bundle":report})
            );
        } else {
            let report = view.export_replay(
                node,
                context,
                &directory,
                &selector_solve::replay::ReplayLimits::default(),
            )?;
            eprintln!(
                "{}",
                serde_json::json!({"stage":"transfer_replay_export","mode":"checkpoint_inspection",
                "recorded_producer":header.producer.to_string(),"operator_producer":env!("SELECTOR_SOLVE_PRODUCER"),"directory":directory,"bundle":report})
            );
        }
    }
    publish_output(args, |out| {
        serde_json::to_writer_pretty(
            out,
            &serde_json::json!({"schema_version":1,"report_kind":"checkpoint_inventory","mode":"inspection_only",
            "checkpoint":{"version":header.version,"artifact":header.artifact.to_string(),"producer":header.producer.to_string(),
                "facts":header.facts.to_string(),"graph":header.graph.to_string(),"content_seal":header.content_seal.to_string(),
                "execution_roots":header.execution_roots.to_string(),"max_set_members":header.max_set_members,"quantum":header.quantum,
                "contexts":header.contexts,"frames":header.frames,"value_sets":header.value_sets,"context_policy":context_policy,
                "rounds":header.rounds,"recorded_completion":format!("{:?}",header.completion),"recorded_stop":header.stop.map(|stop|format!("{stop:?}"))},
            "inventory":{"contexts":summary.contexts,"nodes":summary.nodes,"rows":summary.rows,
                "retained_bytes":summary.retained_bytes,"scratch_bytes":summary.scratch_bytes,"query_owned_bytes":view.owned_bytes(),
                "publication_versions_are_evaluation_counts":false},"nodes":rows}),
        )?;
        Ok(())
    })
}

pub(super) fn replay_family(args: &Args) -> Result<()> {
    let family = selector_solve::replay::ReplayFamily::read(
        &args.required("bundle")?,
        &selector_solve::replay::ReplayLimits::default(),
    )?;
    if let Some(directory) = args.path("minimized-output") {
        let explicit = args.value("min-calls").is_some()
            || args.value("min-reads").is_some()
            || args.value("target-node").is_some();
        let context = args
            .value("replay-context")
            .map(str::parse::<u32>)
            .transpose()?;
        let predicate = selector_solve::replay::ReplayFamilyPredicate {
            condition: selector_solve::replay::ReplayPredicate {
                min_calls: args
                    .value("min-calls")
                    .map(str::parse)
                    .transpose()?
                    .unwrap_or(0),
                min_reads: args
                    .value("min-reads")
                    .map(str::parse)
                    .transpose()?
                    .unwrap_or(0),
                target: args
                    .value("target-node")
                    .map(|value| value.parse::<u32>().map(NodeId))
                    .transpose()?,
                preserve_exact_output: !explicit,
                ..Default::default()
            },
            context,
            match_all: context.is_none(),
        };
        let minimized = family.minimize(
            &selector_solve::replay::MinimizeOptions {
                max_evaluations: args.number("max-minimize-evaluations", 256)?,
                ..Default::default()
            },
            &predicate,
        )?;
        family.write_minimized(&directory, &minimized)?;
        publish_output(args, |out| {
            serde_json::to_writer_pretty(out, &minimized)?;
            Ok(())
        })
    } else if args.flag("compare") {
        let comparison = family.compare(&selector_solve::replay::ReplayOptions::default())?;
        publish_output(args, |out| {
            serde_json::to_writer_pretty(out, &comparison)?;
            Ok(())
        })
    } else {
        let result = family.replay(&selector_solve::replay::ReplayOptions::default())?;
        publish_output(args, |out| {
            serde_json::to_writer_pretty(out, &result)?;
            Ok(())
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn old_checkpoint_inventory_and_receiver_family_run_without_resuming() {
        let fixture =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/execution-smoke/head");
        let mut facts = selector_extract::import_capture(
            &fixture.join("documents.jsonl"),
            Some(&fixture.join("syntax.jsonl")),
            &selector_extract::ExtractOptions {
                workers: 1,
                ..Default::default()
            },
        )
        .unwrap();
        let directory = tempfile::tempdir().unwrap();
        let facts_path = directory.path().join("facts.bin");
        facts.identity = selector_facts::codec::write(&facts_path, &facts).unwrap();
        let mut graph = selector_graph_build::build(
            &facts,
            &selector_graph_build::BuildOptions {
                workers: 1,
                include_models: true,
            },
        )
        .unwrap();
        let graph_path = directory.path().join("graph.bin");
        graph.identity = selector_graph::codec::write(&graph_path, &graph).unwrap();
        let node = NodeId(
            graph
                .nodes
                .iter()
                .position(|node| !node.body.is_none())
                .unwrap() as u32,
        );
        let options = selector_solve::SolveOptions {
            workers: 1,
            execution_roots: Some(Arc::from([selector_solve::ExecutionRoot {
                node,
                receiver: SymbolId::NONE,
            }])),
            ..Default::default()
        };
        let mut session = selector_solve::QuerySession::new(&facts, &graph, &options).unwrap();
        session.analyze(&[node]).unwrap();
        let checkpoint = directory.path().join("query.bin");
        let old_producer = ContentHash([93; 32]);
        session.save_checkpoint(&checkpoint, old_producer).unwrap();
        let original = fs::read(&checkpoint).unwrap();
        drop(session);
        let frontier_output = directory.path().join("frontier.json");
        let frontier_args = Args::parse([
            "inspect-checkpoint".to_owned(),
            "--facts".into(),
            facts_path.display().to_string(),
            "--graph".into(),
            graph_path.display().to_string(),
            "--checkpoint".into(),
            checkpoint.display().to_string(),
            "--output".into(),
            frontier_output.display().to_string(),
            "--root-node".into(),
            node.0.to_string(),
            "--target-node".into(),
            node.0.to_string(),
        ])
        .unwrap();
        frontier_args.validate().unwrap();
        execute(&frontier_args).unwrap();
        let frontier: serde_json::Value =
            serde_json::from_slice(&fs::read(frontier_output).unwrap()).unwrap();
        assert_eq!(frontier["report_kind"], "checkpoint_root_frontier");
        assert_eq!(frontier["selection_authority"], false);
        assert_eq!(frontier["frontier"]["root"]["node"], node.0);
        assert_eq!(
            frontier["frontier"]["target"]["calls"],
            serde_json::json!([])
        );
        assert_eq!(fs::read(&checkpoint).unwrap(), original);
        let output = directory.path().join("inventory.json");
        let bundle = directory.path().join("family");
        let args = Args::parse([
            "inspect-checkpoint".to_owned(),
            "--facts".into(),
            facts_path.display().to_string(),
            "--graph".into(),
            graph_path.display().to_string(),
            "--checkpoint".into(),
            checkpoint.display().to_string(),
            "--output".into(),
            output.display().to_string(),
            "--replay-bundle".into(),
            bundle.display().to_string(),
            "--replay-node".into(),
            node.0.to_string(),
            "--replay-family".into(),
        ])
        .unwrap();
        args.validate().unwrap();
        execute(&args).unwrap();
        let inventory: serde_json::Value =
            serde_json::from_slice(&fs::read(output).unwrap()).unwrap();
        assert_eq!(inventory["mode"], "inspection_only");
        assert_eq!(
            inventory["checkpoint"]["producer"],
            old_producer.to_string()
        );
        assert!(inventory["inventory"]["contexts"].as_u64().unwrap() > 0);
        assert_eq!(fs::read(checkpoint).unwrap(), original);
        let replay_output = directory.path().join("comparison.json");
        let args = Args::parse([
            "transfer-replay".to_owned(),
            "--bundle".into(),
            bundle.display().to_string(),
            "--compare".into(),
            "--output".into(),
            replay_output.display().to_string(),
        ])
        .unwrap();
        replay_family(&args).unwrap();
        let comparison: Vec<serde_json::Value> =
            serde_json::from_slice(&fs::read(replay_output).unwrap()).unwrap();
        assert!(!comparison.is_empty());
        assert!(comparison.iter().all(|row| row["equal"] == true));
    }
}
