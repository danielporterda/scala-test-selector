//! Read-only diagnostics after publication. Historical obligations stay historical.
use super::*;
use serde::Serialize;

#[derive(Debug, Serialize)]
pub struct FinalizationCensus {
    pub schema_version: u32,
    pub basis: &'static str,
    pub fixed_point_reached: bool,
    pub retained_contexts: usize,
    pub evaluated_retained_contexts: usize,
    pub unevaluated_retained_contexts: usize,
    pub invalidated_retained_contexts: usize,
    pub ready_frontier_rows: usize,
    pub pending_root_rows: usize,
    pub requested_root_bindings: usize,
    pub requested_root_nodes: usize,
    pub admitted_root_contexts: usize,
    pub reported_guarded_requested_root_nodes: usize,
    /// None means that residual work or global uncertainty prevents this claim.
    pub guard_free_fixed_point_requested_root_nodes: Option<usize>,
    pub reported_unscoped_uncertainty: bool,
    pub monotone_issue_contexts: usize,
    pub monotone_published_obligation_rows: usize,
    pub reported_obligation_rows: usize,
    pub historical_first_runtime_sites: usize,
    pub current_transfer_failures_reconstructed: bool,
    pub coverage: &'static str,
}

/// A separate diagnostic allowance, never an execution option or selection proof.
#[derive(Clone, Copy, Debug)]
pub struct CurrentAuditOptions {
    pub max_contexts: usize,
    pub max_operations: u64,
    pub scratch_budget_bytes: usize,
}
impl Default for CurrentAuditOptions {
    fn default() -> Self {
        Self {
            max_contexts: 4096,
            max_operations: 1_000_000,
            scratch_budget_bytes: 256 * 1024 * 1024,
        }
    }
}

#[derive(Debug, Serialize)]
pub struct CurrentReasonCount {
    pub reason: &'static str,
    pub contexts: u64,
    pub exemplar_context: u32,
    pub exemplar_node: u32,
    pub exemplar_operation: Option<u32>,
}
#[derive(Debug, Serialize)]
pub struct CurrentKindCount {
    pub kind: &'static str,
    pub contexts: u64,
}

pub const CURRENT_SITE_LIMIT: usize = 16;

#[derive(Debug, Serialize)]
pub struct CurrentSiteCount {
    pub reason: &'static str,
    #[serde(skip)]
    reason_id: u32,
    pub contexts: u64,
    pub node: u32,
    pub operation: Option<u32>,
    pub exemplar_context: u32,
}

/// Exact grouped counts over the audit's first CURRENT site per context.
#[derive(Debug, Serialize)]
pub struct CurrentSiteRanking {
    pub basis: &'static str,
    pub audit_complete: bool,
    pub sampling: bool,
    pub all_runtime_occurrences_counted: bool,
    pub limit: usize,
    pub total_contexts: u64,
    pub total_groups: usize,
    pub reported_contexts: u64,
    pub reported_groups: usize,
    pub other_contexts: u64,
    pub other_groups: usize,
    pub top: Vec<CurrentSiteCount>,
}
impl Default for CurrentSiteRanking {
    fn default() -> Self {
        Self {
            basis: "exact_first_current_issue_per_successfully_audited_context",
            audit_complete: false,
            sampling: false,
            all_runtime_occurrences_counted: false,
            limit: CURRENT_SITE_LIMIT,
            total_contexts: 0,
            total_groups: 0,
            reported_contexts: 0,
            reported_groups: 0,
            other_contexts: 0,
            other_groups: 0,
            top: Vec::new(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct CurrentSiteRow {
    reason: u32,
    node: u32,
    operation: u32,
    context: u32,
}
impl CurrentSiteRow {
    fn key(self) -> (u32, u32, u32) {
        (self.reason, self.node, self.operation)
    }
}

fn rank_sites(rows: &mut [CurrentSiteRow], ranking: &mut CurrentSiteRanking) -> Result<(), Error> {
    // Unstable sort needs no allocation; ContextId is only an exemplar tie-break.
    rows.sort_unstable();
    ranking.total_contexts = rows.len() as u64;
    let mut start = 0;
    while start < rows.len() {
        let row = rows[start];
        let mut end = start + 1;
        while end < rows.len() && rows[end].key() == row.key() {
            end += 1;
        }
        ranking.total_groups += 1;
        let count = (end - start) as u64;
        let reason = RuntimeIssueReason::decode(row.reason)?.as_str();
        // Frequency first, then the numeric typed reason/node/operation key.
        // String comparison and insertion order never decide the ranking.
        let position = ranking.top.partition_point(|old| {
            old.contexts > count
                || (old.contexts == count
                    && (old.reason_id, old.node, old.operation.unwrap_or(u32::MAX))
                        < (row.reason, row.node, row.operation))
        });
        if position < CURRENT_SITE_LIMIT {
            if ranking.top.len() == CURRENT_SITE_LIMIT {
                ranking.top.pop();
            }
            ranking.top.insert(
                position,
                CurrentSiteCount {
                    reason,
                    reason_id: row.reason,
                    contexts: count,
                    node: row.node,
                    operation: (row.operation != u32::MAX).then_some(row.operation),
                    exemplar_context: row.context,
                },
            );
        }
        start = end;
    }
    ranking.reported_groups = ranking.top.len();
    ranking.reported_contexts = ranking.top.iter().map(|row| row.contexts).sum();
    ranking.other_contexts = ranking.total_contexts - ranking.reported_contexts;
    ranking.other_groups = ranking.total_groups - ranking.reported_groups;
    Ok(())
}
#[derive(Debug, Serialize)]
pub struct CurrentLocalTransferAudit {
    pub schema_version: u32,
    pub basis: &'static str,
    pub complete: bool,
    pub status: &'static str,
    pub fixed_point_reached: bool,
    pub retained_contexts: usize,
    pub attempted_contexts: usize,
    pub audited_contexts: usize,
    pub contexts_with_current_local_issues: usize,
    pub contexts_without_current_local_issues: usize,
    pub first_current_issue_by_reason: Vec<CurrentReasonCount>,
    pub first_current_site_ranking: CurrentSiteRanking,
    pub current_local_issue_kinds: Vec<CurrentKindCount>,
    pub operations: u64,
    pub emitted_calls: u64,
    pub calls_without_published_return_summary: u64,
    pub elapsed_ns: u64,
    pub estimated_scratch_bytes: usize,
    pub peak_retained_scratch_bytes: usize,
    pub ranking_storage_bytes: usize,
    pub context_limit: usize,
    pub operation_limit: u64,
    pub scratch_budget_bytes: usize,
    pub budget_semantics: &'static str,
    pub selection_authority: bool,
    pub root_path_proof: bool,
    pub all_runtime_occurrences_counted: bool,
    pub coverage: &'static str,
}

fn finish_audit(
    mut report: CurrentLocalTransferAudit,
    start: Instant,
) -> CurrentLocalTransferAudit {
    report.elapsed_ns = start.elapsed().as_nanos().min(u64::MAX as u128) as u64;
    report
}

fn ranking_bytes(capacity: usize, report: &CurrentLocalTransferAudit) -> usize {
    capacity * std::mem::size_of::<CurrentSiteRow>()
        + report.first_current_site_ranking.top.capacity() * std::mem::size_of::<CurrentSiteCount>()
        + report.first_current_issue_by_reason.capacity()
            * std::mem::size_of::<CurrentReasonCount>()
        + report.current_local_issue_kinds.capacity() * std::mem::size_of::<CurrentKindCount>()
}

fn kind_name(kind: IssueKind) -> &'static str {
    match kind {
        IssueKind::MissingSource => "MissingSource",
        IssueKind::StaleSource => "StaleSource",
        IssueKind::UnsupportedSchema => "UnsupportedSchema",
        IssueKind::MissingSyntax => "MissingSyntax",
        IssueKind::UnresolvedSymbol => "UnresolvedSymbol",
        IssueKind::UnknownExecution => "UnknownExecution",
        IssueKind::MissingBinary => "MissingBinary",
        IssueKind::UnsupportedModel => "UnsupportedModel",
        IssueKind::ContextConflict => "ContextConflict",
        IssueKind::ResourceLimit => "ResourceLimit",
        IssueKind::InvalidInput => "InvalidInput",
        IssueKind::IncompleteHierarchy => "IncompleteHierarchy",
    }
}

impl QuerySession<'_> {
    /// Counts immutable retained state and conservative reported guards. This
    /// never treats a previously published issue as a current transfer failure.
    pub fn finalization_census(
        &self,
        result: &AnalysisResult,
    ) -> Result<FinalizationCensus, Error> {
        if result.snapshot != self.graph.identity {
            return Err(Error::Invalid("finalization snapshot"));
        }
        let mut requested = Vec::new();
        self.requested_root_evidence(&mut requested);
        if requested != result.evidence.requested_roots {
            return Err(Error::Invalid("finalization requested frontier"));
        }
        let root_nodes: HashSet<_> = requested.iter().map(|root| root.node).collect();
        let guarded: HashSet<_> = result.guarded_roots.iter().copied().collect();
        let reported_guarded = root_nodes.intersection(&guarded).count();
        let evaluated = self.contexts.iter().filter(|c| c.evaluated).count();
        let invalidated = self
            .dependencies
            .snapshot_contexts()
            .filter(|(_, invalid)| *invalid)
            .count();
        let fixed = self.sealed
            && self.stop_reason.is_none()
            && self.ready.is_empty()
            && self.pending_roots.is_empty()
            && evaluated == self.contexts.len()
            && invalidated == 0;
        Ok(FinalizationCensus {
            schema_version: 1,
            basis: "final_published_session_state_and_conservative_analysis_result",
            fixed_point_reached: fixed,
            retained_contexts: self.contexts.len(),
            evaluated_retained_contexts: evaluated,
            unevaluated_retained_contexts: self.contexts.len() - evaluated,
            invalidated_retained_contexts: invalidated,
            ready_frontier_rows: self.ready.len(),
            pending_root_rows: self.pending_roots.len(),
            requested_root_bindings: requested.len(),
            requested_root_nodes: root_nodes.len(),
            admitted_root_contexts: self.roots.len(),
            reported_guarded_requested_root_nodes: reported_guarded,
            guard_free_fixed_point_requested_root_nodes: (fixed && !result.unscoped_uncertainty)
                .then_some(root_nodes.len() - reported_guarded),
            reported_unscoped_uncertainty: result.unscoped_uncertainty,
            monotone_issue_contexts: self.issue_contexts.len(),
            monotone_published_obligation_rows: self.issues.len(),
            reported_obligation_rows: result.obligations.len(),
            historical_first_runtime_sites: self.runtime_issue_sites.len(),
            current_transfer_failures_reconstructed: false,
            coverage: "Guard-free counts use the conservative reported root-node proof only after a drained publication fixed point and no global uncertainty. They are not suite exclusions. Published issues/calls and saved FIRST EVER sites are monotone histories, not current failures. Root-node counts collapse receiver bindings; evaluated counts inspect retained summary-published flags, not evaluation-event subtraction or fully committed attempts after a resource stop.",
        })
    }

    /// Re-evaluates local kernels against one immutable final World. No delta is
    /// committed: contexts, interning owners, dependencies, guards, work counters,
    /// selection and caches remain untouched. This does not rebuild root paths.
    pub fn audit_current_local_transfers(
        &self,
        limits: CurrentAuditOptions,
    ) -> Result<CurrentLocalTransferAudit, Error> {
        let start = Instant::now();
        let fixed = self.sealed
            && self.stop_reason.is_none()
            && self.ready.is_empty()
            && self.pending_roots.is_empty()
            && self.contexts.iter().all(|c| c.evaluated)
            && self
                .dependencies
                .snapshot_contexts()
                .all(|(_, invalid)| !invalid);
        let mut report = CurrentLocalTransferAudit {
            schema_version: 1,
            basis: "one_fresh_local_transfer_per_retained_context_against_immutable_final_world",
            complete: false,
            status: "not_run_not_fixed_point",
            fixed_point_reached: fixed,
            retained_contexts: self.contexts.len(),
            attempted_contexts: 0,
            audited_contexts: 0,
            contexts_with_current_local_issues: 0,
            contexts_without_current_local_issues: 0,
            first_current_issue_by_reason: Vec::new(),
            first_current_site_ranking: CurrentSiteRanking::default(),
            current_local_issue_kinds: Vec::new(),
            operations: 0,
            emitted_calls: 0,
            calls_without_published_return_summary: 0,
            elapsed_ns: 0,
            estimated_scratch_bytes: 0,
            peak_retained_scratch_bytes: 0,
            ranking_storage_bytes: 0,
            context_limit: limits.max_contexts,
            operation_limit: limits.max_operations,
            scratch_budget_bytes: limits.scratch_budget_bytes,
            budget_semantics: "Conservative recipe-based admission estimate, then actual retained scratch checked after each transfer; limits are diagnostic publication-boundary checks, not a hard allocator ceiling. Operation cap can overshoot by one transfer. No state is committed.",
            selection_authority: false,
            root_path_proof: false,
            all_runtime_occurrences_counted: false,
            coverage: "Current local issue kinds and first CURRENT issue reason per audited context; excludes static graph/file/auxiliary guards and does not reconstruct current call paths or global effects. All retained contexts, including restored/unrequested contexts, may be included. The current abstract World can itself retain earlier joined unknown alternatives; these are not concrete runtime failures. Historical guards are not cleared. Partial or skipped results cannot establish absence of uncertainty.",
        };
        if !fixed {
            return Ok(finish_audit(report, start));
        }
        if self.contexts.len() > limits.max_contexts {
            report.status = "not_run_context_limit";
            return Ok(finish_audit(report, start));
        }
        let members = self.options.max_set_members.saturating_add(1);
        let mut work = 0u64;
        let mut estimated = 0usize;
        // Scratch is reused across the audit. Include whole-type traversal
        // scratch plus local SSA storage and generously amplified candidate /
        // abstract-set publications. This is admission, not an allocator guard.
        for context in &self.contexts {
            let record = self.graph.nodes[context.key.node.index()];
            let edges = self.graph.successors(context.key.node).count();
            let mut max_value = 0usize;
            let mut actuals = 0usize;
            let mut operations = 0usize;
            if !record.body.is_none() {
                let body = self.facts.bodies[record.body.index()];
                operations = body.operations.len as usize;
                for id in &self.facts.operands[body.parameters.range()] {
                    if !id.is_none() {
                        max_value = max_value.max(id.index().saturating_add(1));
                    }
                }
                for op in &self.facts.operations[body.operations.range()] {
                    for id in [op.dest, op.a, op.b] {
                        if !id.is_none() {
                            max_value = max_value.max(id.index().saturating_add(1));
                        }
                    }
                    actuals = actuals.saturating_add(op.arguments.len as usize);
                    for id in &self.facts.operands[op.arguments.range()] {
                        if !id.is_none() {
                            max_value = max_value.max(id.index().saturating_add(1));
                        }
                    }
                }
            }
            work = work.saturating_add((operations + edges) as u64);
            let estimate = self
                .facts
                .symbols
                .len()
                .saturating_mul(64)
                .saturating_add(max_value.saturating_mul(16))
                .saturating_add(
                    operations
                        .saturating_add(actuals)
                        .saturating_mul(members)
                        .saturating_mul(128),
                )
                .saturating_add(edges.saturating_mul(members).saturating_mul(256));
            estimated = estimated.max(estimate);
        }
        let planned_ranking_bytes = self
            .contexts
            .len()
            .checked_mul(std::mem::size_of::<CurrentSiteRow>())
            .and_then(|n| {
                n.checked_add(CURRENT_SITE_LIMIT * std::mem::size_of::<CurrentSiteCount>())
            })
            .and_then(|n| n.checked_add(13 * std::mem::size_of::<CurrentReasonCount>()))
            .and_then(|n| n.checked_add(12 * std::mem::size_of::<CurrentKindCount>()))
            .ok_or(Error::Limit("current audit ranking bytes"))?;
        report.estimated_scratch_bytes = estimated.saturating_add(planned_ranking_bytes);
        if work > limits.max_operations {
            report.status = "not_run_operation_estimate";
            return Ok(finish_audit(report, start));
        }
        if report.estimated_scratch_bytes > limits.scratch_budget_bytes {
            report.status = "not_run_scratch_estimate";
            return Ok(finish_audit(report, start));
        }
        // Charge every table before reserving; no per-context table growth is
        // permitted during evaluation. These are diagnostic-owned, not World.
        let mut site_rows = Vec::new();
        if site_rows.try_reserve_exact(self.contexts.len()).is_err()
            || report
                .first_current_site_ranking
                .top
                .try_reserve_exact(CURRENT_SITE_LIMIT)
                .is_err()
            || report
                .first_current_issue_by_reason
                .try_reserve_exact(13)
                .is_err()
            || report
                .current_local_issue_kinds
                .try_reserve_exact(12)
                .is_err()
        {
            report.ranking_storage_bytes = ranking_bytes(site_rows.capacity(), &report);
            report.peak_retained_scratch_bytes = report.ranking_storage_bytes;
            report.status = "partial_allocation_limit";
            return Ok(finish_audit(report, start));
        }
        report.ranking_storage_bytes = ranking_bytes(site_rows.capacity(), &report);
        report.peak_retained_scratch_bytes = report.ranking_storage_bytes;
        if estimated.saturating_add(report.ranking_storage_bytes) > limits.scratch_budget_bytes {
            report.status = "not_run_scratch_estimate";
            return Ok(finish_audit(report, start));
        }
        let world = ReadWorld {
            facts: self.facts,
            graph: self.graph,
            types: &self.types,
            pool: &self.pool,
            frames: &self.frames,
            contexts: &self.contexts,
            index: &self.index,
            callback_shapes: &self.callback_shapes,
            slots: &self.slots,
            heap_owners: &self.heap_owners,
            captures: &self.captures,
            families: &self.closure_families,
            capture_origins: &self.capture_origins,
            context_policy: self.options.context_policy,
            provider_scope: self.provider_scope.as_ref(),
        };
        let mut scratch = Scratch::new(self.options.max_set_members);
        let mut output = Evaluation::default();
        let mut reasons = [0u64; 13];
        let mut exemplars = [None; 13];
        let mut kinds = [0u64; 12];
        report.status = "complete";
        for (i, context) in self.contexts.iter().enumerate() {
            report.attempted_contexts += 1;
            if let Err(error) = evaluate(
                self.facts,
                self.graph,
                &self.types,
                &world,
                context.key.node,
                context.key.receiver,
                self.frames.get(context.key.arguments),
                &mut scratch,
                &mut output,
            ) {
                if matches!(error, Error::Limit(_)) {
                    report.operations = report
                        .operations
                        .saturating_add(output.operation_visits + output.edges.len() as u64);
                    report.peak_retained_scratch_bytes = report.peak_retained_scratch_bytes.max(
                        scratch
                            .owned_bytes()
                            .saturating_add(evaluation_bytes(&output))
                            .saturating_add(report.ranking_storage_bytes),
                    );
                    report.status = "partial_allocation_limit";
                    break;
                }
                return Err(error);
            }
            report.audited_contexts += 1;
            report.emitted_calls += output.calls.len() as u64;
            report.calls_without_published_return_summary += output
                .calls
                .iter()
                .filter(|call| call.observe_return && call.summary.is_none())
                .count() as u64;
            report.operations = report
                .operations
                .saturating_add(output.operation_visits + output.edges.len() as u64);
            report.peak_retained_scratch_bytes = report.peak_retained_scratch_bytes.max(
                scratch
                    .owned_bytes()
                    .saturating_add(evaluation_bytes(&output))
                    .saturating_add(report.ranking_storage_bytes),
            );
            report.contexts_with_current_local_issues += usize::from(!output.issues.is_empty());
            report.contexts_without_current_local_issues += usize::from(output.issues.is_empty());
            for kind in &output.issues {
                kinds[*kind as usize - 1] += 1;
            }
            if let Some(site) = output.first_issue {
                self.validate_runtime_issue_site(context.key.node, site)?;
                let reason = site.reason as usize - 1;
                reasons[reason] += 1;
                site_rows.push(CurrentSiteRow {
                    reason: site.reason as u32,
                    node: context.key.node.0,
                    operation: site.operation.0,
                    context: i as u32,
                });
                let candidate = (context.key.node, site.operation, ContextId(i as u32));
                if exemplars[reason].is_none_or(|old| candidate < old) {
                    exemplars[reason] = Some(candidate);
                }
            }
            if report.operations > limits.max_operations {
                report.status = "partial_operation_limit";
                break;
            }
            if report.peak_retained_scratch_bytes > limits.scratch_budget_bytes {
                report.status = "partial_scratch_limit";
                break;
            }
        }
        for (i, count) in reasons.into_iter().enumerate() {
            if let Some((node, operation, context)) = exemplars[i] {
                report
                    .first_current_issue_by_reason
                    .push(CurrentReasonCount {
                        reason: RuntimeIssueReason::decode(i as u32 + 1)?.as_str(),
                        contexts: count,
                        exemplar_context: context.0,
                        exemplar_node: node.0,
                        exemplar_operation: (!operation.is_none()).then_some(operation.0),
                    });
            }
        }
        for (i, count) in kinds
            .into_iter()
            .enumerate()
            .filter(|(_, count)| *count != 0)
        {
            report.current_local_issue_kinds.push(CurrentKindCount {
                kind: kind_name(IssueKind::decode(i as u32 + 1)?),
                contexts: count,
            });
        }
        report.complete =
            report.status == "complete" && report.audited_contexts == self.contexts.len();
        rank_sites(&mut site_rows, &mut report.first_current_site_ranking)?;
        report.first_current_site_ranking.audit_complete = report.complete;
        Ok(finish_audit(report, start))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn current_site_ranking_counts_all_groups_and_exposes_the_remainder() {
        assert_eq!(std::mem::size_of::<CurrentSiteRow>(), 16);
        let mut rows = Vec::new();
        for node in 0..20 {
            for occurrence in 0..=node {
                rows.push(CurrentSiteRow {
                    reason: 12,
                    node,
                    operation: node + 50,
                    context: 1000 + node * 20 + occurrence,
                });
            }
        }
        let mut ranking = CurrentSiteRanking::default();
        ranking.top.reserve_exact(CURRENT_SITE_LIMIT);
        let capacity = ranking.top.capacity();
        let mut reversed = rows.clone();
        reversed.reverse();
        rank_sites(&mut rows, &mut ranking).unwrap();
        assert_eq!(ranking.total_contexts, 210);
        assert_eq!(ranking.total_groups, 20);
        assert_eq!(ranking.reported_groups, 16);
        assert_eq!(ranking.reported_contexts, 200);
        assert_eq!(ranking.other_contexts, 10);
        assert_eq!(ranking.other_groups, 4);
        assert_eq!(
            ranking.top[0].node, 19,
            "frequency beats the rare lowest node"
        );
        assert_eq!(ranking.top[0].contexts, 20);
        assert_eq!(ranking.top.last().unwrap().node, 4);
        assert_eq!(ranking.top.capacity(), capacity);
        let mut other = CurrentSiteRanking::default();
        other.top.reserve_exact(CURRENT_SITE_LIMIT);
        rank_sites(&mut reversed, &mut other).unwrap();
        let keys = |r: &CurrentSiteRanking| {
            r.top
                .iter()
                .map(|x| {
                    (
                        x.reason,
                        x.node,
                        x.operation,
                        x.contexts,
                        x.exemplar_context,
                    )
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(keys(&ranking), keys(&other));
    }

    #[test]
    fn current_site_ranking_ties_use_typed_keys_and_preserve_operation_none() {
        let mut rows = [
            CurrentSiteRow {
                reason: 4,
                node: 2,
                operation: u32::MAX,
                context: 9,
            },
            CurrentSiteRow {
                reason: 1,
                node: 3,
                operation: 7,
                context: 8,
            },
            CurrentSiteRow {
                reason: 4,
                node: 2,
                operation: u32::MAX,
                context: 4,
            },
            CurrentSiteRow {
                reason: 1,
                node: 3,
                operation: 7,
                context: 1,
            },
        ];
        let mut ranking = CurrentSiteRanking::default();
        ranking.top.reserve_exact(CURRENT_SITE_LIMIT);
        rank_sites(&mut rows, &mut ranking).unwrap();
        assert_eq!(ranking.total_contexts, 4);
        assert_eq!(ranking.top[0].reason, "missing_callback_target");
        assert_eq!(ranking.top[0].exemplar_context, 1);
        assert_eq!(ranking.top[1].operation, None);
        assert_eq!(ranking.top[1].exemplar_context, 4);
        assert_eq!(ranking.other_contexts, 0);
    }
}
