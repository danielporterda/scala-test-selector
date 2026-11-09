//! Explicit conditional selection by paired owning-test classpath absence.
use super::*;
use selector_plan::classpath_absence::{Plan, SourceScope};

/// Convert the selector's exact requested-path scope without upgrading legacy,
/// whole-snapshot or unknown input scopes. Exact execution-recipe issues in
/// requested source files remain diagnostics: their unavailable products cannot
/// execute in a certified suite. Additional effective input uncertainty blocks.
pub fn classpath_absence_scope(
    base_facts: &FactSnapshot,
    base_graph: &ProgramGraph,
    head_facts: &FactSnapshot,
    head_graph: &ProgramGraph,
    seeds: &ChangeSeeds,
) -> Result<SourceScope, Error> {
    if seeds.conservative || seeds.guard_causes.iter().any(|cause| !is_retention(cause)) {
        return Err(Error::Invalid(
            "classpath absence has additional changed-input guards",
        ));
    }
    let scope = seeds
        .change_scope
        .as_ref()
        .filter(|scope| scope.mode == SourceChangeMode::RequestedPaths)
        .ok_or(Error::Invalid(
            "classpath absence requires explicit requested source scope",
        ))?;
    for (facts, graph, obligations) in [
        (base_facts, base_graph, &seeds.base_obligations),
        (head_facts, head_graph, &seeds.head_obligations),
    ] {
        if obligations.is_empty() {
            continue;
        }
        admitted(facts, graph)?;
        let dirty: HashSet<_> = facts
            .files
            .iter()
            .enumerate()
            .filter_map(|(i, file)| {
                let id = FileId(i as u32);
                (file.flags & (SOURCE_VERIFIED | SYNTAX_VERIFIED | FILE_BINARY_SOURCE)
                    == SOURCE_VERIFIED | SYNTAX_VERIFIED
                    && scope
                        .requested_paths
                        .binary_search_by(|path| path.as_str().cmp(facts.path(id)))
                        .is_ok())
                .then_some((facts.path(id), facts.text(file.context)))
            })
            .collect();
        let recipes = scoped_recipe_issues(facts, graph, &dirty);
        let actual: HashSet<_> = facts
            .issues
            .iter()
            .filter_map(|issue| {
                let key = (issue.kind as u32, issue.file, issue.symbol, issue.detail);
                recipes.contains(&key).then_some(key)
            })
            .collect();
        for issue in obligations {
            let file = facts.files.get(issue.file.index());
            let symbol = facts.symbols.get(issue.symbol.index());
            if !actual.contains(&(issue.kind as u32, issue.file, issue.symbol, issue.detail))
                || file.zip(symbol).is_none_or(|(file, symbol)| {
                    symbol.context != file.context || symbol.file != issue.file
                })
            {
                return Err(Error::Invalid(
                    "classpath absence obligation is not an exact requested source recipe issue",
                ));
            }
        }
    }
    Ok(SourceScope {
        requested_paths: scope.requested_paths.clone(),
        outside_count: scope.outside_count,
        outside: scope
            .outside
            .iter()
            .map(|row| (row.base_file, row.head_file))
            .collect(),
    })
}

/// Apply a separately issued paired classpath certificate under its explicit
/// opt-in contract. Observed Required always wins. Kernel uncertainty, resource
/// completion and effect evidence remain untouched; this proof establishes only
/// that this requested source scope cannot be loaded by the owning test task.
/// Strict selection/planner defaults do not call this function.
pub fn select_with_classpath_absence(
    base_facts: &FactSnapshot,
    base_graph: &ProgramGraph,
    head_facts: &FactSnapshot,
    head_graph: &ProgramGraph,
    seeds: ChangeSeeds,
    base: Option<AnalysisResult>,
    head: AnalysisResult,
    plan: &Plan,
) -> Result<SelectionResult, Error> {
    let scope = classpath_absence_scope(base_facts, base_graph, head_facts, head_graph, &seeds)?;
    if base.is_none() {
        return Err(Error::Invalid(
            "classpath absence requires paired observed results",
        ));
    }
    plan.validate(
        base_facts,
        base_graph,
        head_facts,
        head_graph,
        selector_plan::PlanSeeds {
            execution: &seeds.base,
            declarations: &seeds.base_compile,
            unscoped: seeds.conservative,
        },
        selector_plan::PlanSeeds {
            execution: &seeds.head,
            declarations: &seeds.head_compile,
            unscoped: seeds.conservative,
        },
        &scope,
    )?;
    for cause in &seeds.guard_causes {
        let facts = match cause.side {
            SnapshotSide::Base => base_facts,
            SnapshotSide::Head => head_facts,
        };
        let name = cause
            .external
            .as_ref()
            .and_then(|detail| detail.suite_name.as_deref())
            .unwrap_or("");
        if !facts.suites.iter().any(|suite| {
            suite.symbol == cause.symbol
                && suite.file == cause.file
                && facts.text(suite.name) == name
        }) {
            return Err(Error::Invalid(
                "classpath absence explicit retention binding",
            ));
        }
    }
    let mut result = select_observed(
        base_facts, base_graph, head_facts, head_graph, seeds, base, head,
    )?;
    result.suite_semantics = SuiteSemantics::Independent;
    result.selection_contract = plan.contract();
    // Base catalogue positions can differ between revisions. Match the same
    // exact suite identity used by observed selection, never display name alone.
    let base_suites: HashMap<_, _> = base_facts
        .suites
        .iter()
        .enumerate()
        .map(|(i, suite)| {
            (
                (
                    base_facts.text(suite.name),
                    symbol_key(base_facts, suite.symbol),
                ),
                SuiteId(i as u32),
            )
        })
        .collect();
    for decision in &mut result.decisions {
        if decision.status == SuiteDecisionStatus::Required
            || decision.node.is_none()
            || decision.base_node.is_none()
        {
            continue;
        }
        let suite = &head_facts.suites[decision.suite.index()];
        if result.guard_causes.iter().any(|cause| {
            cause.external.as_ref().is_some_and(|detail| {
                detail.suite_name.as_deref() == Some(head_facts.text(suite.name))
            })
        }) {
            decision.status = SuiteDecisionStatus::Unknown;
            decision.guarded = true;
            decision.reasons = (decision.reasons
                & !(DECISION_COMPLETE_UNAFFECTED | DECISION_CERTIFIED_EXCLUSION))
                | DECISION_CHANGED_INPUT_GUARD;
            continue;
        }
        let Some(&base_suite) = base_suites.get(&(
            head_facts.text(suite.name),
            symbol_key(head_facts, suite.symbol),
        )) else {
            continue;
        };
        let Some(head_certificate) = plan.certificate(true, decision.suite, decision.node) else {
            continue;
        };
        let Some(base_certificate) = plan.certificate(false, base_suite, decision.base_node) else {
            continue;
        };
        decision.status = SuiteDecisionStatus::Excluded;
        decision.guarded = false;
        // Keep the actual execution diagnostics visible. They are not refuted
        // by a source-product absence certificate, nor needed to establish it.
        decision.reasons = (decision.reasons
            & !(DECISION_COMPLETE_UNAFFECTED | DECISION_CERTIFIED_EXCLUSION))
            | DECISION_CLASSPATH_ABSENCE;
        decision.head_exclusion = Some(RootExclusion {
            snapshot: head_graph.identity,
            root: decision.node,
            certificate: head_certificate,
            assumptions: plan.contract().bits(),
        });
        decision.base_exclusion = Some(RootExclusion {
            snapshot: base_graph.identity,
            root: decision.base_node,
            certificate: base_certificate,
            assumptions: plan.contract().bits(),
        });
    }
    // This entry point does not consume ordinary CandidatePlan certificates.
    // If its caller pruned a root, an absent observed hit is not an omission
    // proof for that root. Only the paired classpath proof may override this.
    for decision in &mut result.decisions {
        if decision.status != SuiteDecisionStatus::Excluded
            || decision.reasons & DECISION_CLASSPATH_ABSENCE != 0
        {
            continue;
        }
        let head_suite = &head_facts.suites[decision.suite.index()];
        let head_requested = result
            .head
            .evidence
            .requested_roots
            .binary_search(&AnalyzedRoot {
                node: decision.node,
                receiver: head_suite.symbol,
            })
            .is_ok();
        let base_requested = result.base.as_ref().is_some_and(|base| {
            let symbol = base_graph
                .nodes
                .get(decision.base_node.index())
                .map(|node| node.symbol)
                .unwrap_or(SymbolId::NONE);
            base.evidence
                .requested_roots
                .binary_search(&AnalyzedRoot {
                    node: decision.base_node,
                    receiver: symbol,
                })
                .is_ok()
        });
        if !head_requested || !base_requested {
            decision.status = SuiteDecisionStatus::Unknown;
            decision.guarded = true;
            decision.reasons =
                (decision.reasons & !DECISION_COMPLETE_UNAFFECTED) | DECISION_MISSING_ROOT;
            result.completion = merge_completion(result.completion, Completion::Conservative);
        }
    }
    result.suites = selected_decisions(&result.decisions);
    Ok(result)
}

fn is_retention(cause: &ChangeGuardCause) -> bool {
    cause.reason == ChangeGuardReason::ExternalInput
        && cause.kind == IssueKind::UnsupportedModel
        && !cause.file.is_none()
        && !cause.symbol.is_none()
        && cause.detail.is_none()
        && cause.path.is_none()
        && cause.external.as_ref().is_some_and(|detail| {
            detail.reason == "explicit_suite_retention"
                && detail
                    .suite_name
                    .as_deref()
                    .is_some_and(|name| !name.is_empty())
                && detail.schema_path.is_none()
                && detail.operation_path.is_none()
                && detail.verb.is_none()
        })
}

#[cfg(test)]
mod tests;
