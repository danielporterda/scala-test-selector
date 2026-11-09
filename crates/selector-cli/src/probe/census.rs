//! Count all reported obligations without mistaking bounded examples for a census
//! of runtime contexts, issue occurrences, or guarded-root paths.
use selector_facts::FactSnapshot;
use selector_graph::ProgramGraph;
use selector_issue::{RuntimeIssueReason, RuntimeIssueSite};
use selector_result::{Obligation, RootGuardEvidence};
use selector_types::{
    ContextId, EDGE_UNKNOWN, EdgeKind, Error, IssueKind, NODE_EFFECTS_COMPLETE, NodeId,
};
use serde::Serialize;
use std::cmp::Ordering;

const DETAIL_LIMIT: usize = 16;
const KINDS: [IssueKind; 12] = [
    IssueKind::MissingSource,
    IssueKind::StaleSource,
    IssueKind::UnsupportedSchema,
    IssueKind::MissingSyntax,
    IssueKind::UnresolvedSymbol,
    IssueKind::UnknownExecution,
    IssueKind::MissingBinary,
    IssueKind::UnsupportedModel,
    IssueKind::ContextConflict,
    IssueKind::ResourceLimit,
    IssueKind::InvalidInput,
    IssueKind::IncompleteHierarchy,
];
const REASONS: [RuntimeIssueReason; 13] = [
    RuntimeIssueReason::MissingCallbackTarget,
    RuntimeIssueReason::UnknownCallbackValue,
    RuntimeIssueReason::IncompleteCallbackDispatch,
    RuntimeIssueReason::ExecutionGuard,
    RuntimeIssueReason::MissingExecutableBody,
    RuntimeIssueReason::UnboundCallbackTarget,
    RuntimeIssueReason::MissingFieldTarget,
    RuntimeIssueReason::UnknownFieldValue,
    RuntimeIssueReason::UnknownSuperOwner,
    RuntimeIssueReason::IncompleteVirtualDispatch,
    RuntimeIssueReason::MissingCallTarget,
    RuntimeIssueReason::UnknownOperation,
    RuntimeIssueReason::IncompleteDeferredCallback,
];

// Exhaustive matches make a future typed variant require a counter update,
// rather than indexing a fixed array with an unchecked persisted integer.
fn kind_index(kind: IssueKind) -> usize {
    match kind {
        IssueKind::MissingSource => 0,
        IssueKind::StaleSource => 1,
        IssueKind::UnsupportedSchema => 2,
        IssueKind::MissingSyntax => 3,
        IssueKind::UnresolvedSymbol => 4,
        IssueKind::UnknownExecution => 5,
        IssueKind::MissingBinary => 6,
        IssueKind::UnsupportedModel => 7,
        IssueKind::ContextConflict => 8,
        IssueKind::ResourceLimit => 9,
        IssueKind::InvalidInput => 10,
        IssueKind::IncompleteHierarchy => 11,
    }
}
fn reason_index(reason: RuntimeIssueReason) -> usize {
    match reason {
        RuntimeIssueReason::MissingCallbackTarget => 0,
        RuntimeIssueReason::UnknownCallbackValue => 1,
        RuntimeIssueReason::IncompleteCallbackDispatch => 2,
        RuntimeIssueReason::ExecutionGuard => 3,
        RuntimeIssueReason::MissingExecutableBody => 4,
        RuntimeIssueReason::UnboundCallbackTarget => 5,
        RuntimeIssueReason::MissingFieldTarget => 6,
        RuntimeIssueReason::UnknownFieldValue => 7,
        RuntimeIssueReason::UnknownSuperOwner => 8,
        RuntimeIssueReason::IncompleteVirtualDispatch => 9,
        RuntimeIssueReason::MissingCallTarget => 10,
        RuntimeIssueReason::UnknownOperation => 11,
        RuntimeIssueReason::IncompleteDeferredCallback => 12,
    }
}

#[derive(Serialize)]
pub(super) struct GuardCensus<'a> {
    basis: &'static str,
    total: u64,
    all_reported_rows_counted: bool,
    fixed_point_reached: bool,
    counts_are_runtime_occurrences: bool,
    counts_are_guard_paths: bool,
    by_kind: Vec<KindCount<'a>>,
    detail_groups: DetailGroups<'a>,
    runtime_reasons: RuntimeReasons,
}

#[derive(Clone, Copy, Serialize)]
struct Exemplar<'a> {
    symbol_id: Option<u32>,
    symbol: Option<&'a str>,
    context: Option<&'a str>,
    context_source: Option<&'static str>,
    file_id: Option<u32>,
    path: Option<&'a str>,
}
#[derive(Serialize)]
struct KindCount<'a> {
    kind: String,
    count: u64,
    with_nonempty_detail: u64,
    without_nonempty_detail: u64,
    exemplar: Exemplar<'a>,
}
#[derive(Serialize)]
struct DetailGroup<'a> {
    kind: String,
    count: u64,
    detail: &'a str,
    exemplar: Exemplar<'a>,
}
#[derive(Serialize)]
struct DetailGroups<'a> {
    basis: &'static str,
    limit: usize,
    total_groups: u64,
    reported_groups: usize,
    other_groups: u64,
    truncated: bool,
    nonempty_detail_rows: u64,
    null_detail_rows: u64,
    empty_detail_rows: u64,
    reported_rows: u64,
    other_rows: u64,
    top: Vec<DetailGroup<'a>>,
}
#[derive(Serialize)]
struct RuntimeReasonCount {
    reason: &'static str,
    kind: String,
    count: u64,
}
#[derive(Serialize)]
struct RuntimeReasons {
    basis: &'static str,
    guard_exemplars: u64,
    with_runtime_site: u64,
    without_runtime_site: u64,
    counts_complete_for_basis: bool,
    all_context_first_sites_available: bool,
    all_runtime_occurrences_counted: bool,
    coverage: &'static str,
    by_reason: Vec<RuntimeReasonCount>,
}

#[derive(Clone, Copy, Default)]
struct KindAccumulator {
    count: u64,
    nonempty: u64,
    exemplar: Option<usize>,
}
#[derive(Clone, Copy)]
struct Group {
    first: usize,
    count: u64,
}

fn validate_row(facts: &FactSnapshot, row: Obligation) -> Result<(), Error> {
    if (!row.file.is_none() && row.file.index() >= facts.files.len())
        || (!row.symbol.is_none() && row.symbol.index() >= facts.symbols.len())
        || (!row.detail.is_none() && row.detail.index() >= facts.strings.len())
    {
        return Err(Error::Invalid("probe guard census obligation reference"));
    }
    Ok(())
}

fn exemplar(facts: &FactSnapshot, row: Obligation) -> Exemplar<'_> {
    let symbol = (!row.symbol.is_none()).then(|| &facts.symbols[row.symbol.index()]);
    let file = (!row.file.is_none()).then(|| &facts.files[row.file.index()]);
    let (context, context_source) = match symbol {
        Some(symbol) if !symbol.context.is_none() => {
            (Some(facts.text(symbol.context)), Some("symbol"))
        }
        _ => match file {
            Some(file) if !file.context.is_none() => (Some(facts.text(file.context)), Some("file")),
            _ => (None, None),
        },
    };
    Exemplar {
        symbol_id: symbol.map(|_| row.symbol.0),
        symbol: symbol.map(|symbol| facts.text(symbol.name)),
        context,
        context_source,
        file_id: file.map(|_| row.file.0),
        path: file.map(|file| facts.text(file.path)),
    }
}

fn exemplar_key(
    facts: &FactSnapshot,
    row: Obligation,
) -> (
    bool,
    bool,
    Option<&str>,
    Option<&str>,
    Option<&str>,
    u32,
    u32,
) {
    let value = exemplar(facts, row);
    (
        value.symbol.is_none(),
        value.path.is_none(),
        value.context,
        value.symbol,
        value.path,
        row.symbol.0,
        row.file.0,
    )
}

pub(super) fn build<'a>(
    facts: &'a FactSnapshot,
    obligations: &[Obligation],
    guard_causes: &[RootGuardEvidence],
    fixed_point_reached: bool,
) -> Result<GuardCensus<'a>, Error> {
    u32::try_from(obligations.len()).map_err(|_| Error::Limit("probe guard census rows"))?;
    let mut kinds = [KindAccumulator::default(); KINDS.len()];
    let mut indices = Vec::<u32>::new();
    indices
        .try_reserve_exact(obligations.len())
        .map_err(|_| Error::Limit("probe guard census scratch"))?;
    let (mut null_rows, mut empty_rows) = (0u64, 0u64);
    for (index, row) in obligations.iter().copied().enumerate() {
        validate_row(facts, row)?;
        let bucket = &mut kinds[kind_index(row.kind)];
        bucket.count += 1;
        if bucket
            .exemplar
            .is_none_or(|old| exemplar_key(facts, row) < exemplar_key(facts, obligations[old]))
        {
            bucket.exemplar = Some(index);
        }
        if row.detail.is_none() {
            null_rows += 1;
        } else if facts.text(row.detail).is_empty() {
            empty_rows += 1;
        } else {
            bucket.nonempty += 1;
            indices.push(index as u32);
        }
    }
    indices.sort_unstable_by(|left, right| {
        let (left, right) = (obligations[*left as usize], obligations[*right as usize]);
        (left.kind as u32)
            .cmp(&(right.kind as u32))
            .then_with(|| facts.text(left.detail).cmp(facts.text(right.detail)))
            .then_with(|| exemplar_key(facts, left).cmp(&exemplar_key(facts, right)))
    });
    let compare_groups = |left: Group, right: Group| {
        let left_row = obligations[indices[left.first] as usize];
        let right_row = obligations[indices[right.first] as usize];
        right
            .count
            .cmp(&left.count)
            .then_with(|| (left_row.kind as u32).cmp(&(right_row.kind as u32)))
            .then_with(|| {
                facts
                    .text(left_row.detail)
                    .cmp(facts.text(right_row.detail))
            })
    };
    let mut best = [None::<Group>; DETAIL_LIMIT];
    let (mut groups, mut first, mut retained) = (0u64, 0usize, 0usize);
    while first < indices.len() {
        let row = obligations[indices[first] as usize];
        let mut end = first + 1;
        while end < indices.len() {
            let next = obligations[indices[end] as usize];
            if next.kind != row.kind || facts.text(next.detail) != facts.text(row.detail) {
                break;
            }
            end += 1;
        }
        groups += 1;
        let group = Group {
            first,
            count: (end - first) as u64,
        };
        let position = best[..retained]
            .iter()
            .position(|old| old.is_some_and(|old| compare_groups(group, old) == Ordering::Less))
            .unwrap_or(retained);
        if position < DETAIL_LIMIT {
            for index in (position + 1..=retained.min(DETAIL_LIMIT - 1)).rev() {
                best[index] = best[index - 1];
            }
            best[position] = Some(group);
            retained = (retained + 1).min(DETAIL_LIMIT);
        }
        first = end;
    }
    let top: Vec<_> = best
        .into_iter()
        .flatten()
        .map(|group| {
            let row = obligations[indices[group.first] as usize];
            DetailGroup {
                kind: format!("{:?}", row.kind),
                count: group.count,
                detail: facts.text(row.detail),
                exemplar: exemplar(facts, row),
            }
        })
        .collect();
    let reported_rows = top.iter().map(|row| row.count).sum::<u64>();
    let by_kind = KINDS
        .into_iter()
        .zip(kinds)
        .filter_map(|(kind, bucket)| {
            bucket.exemplar.map(|index| KindCount {
                kind: format!("{kind:?}"),
                count: bucket.count,
                with_nonempty_detail: bucket.nonempty,
                without_nonempty_detail: bucket.count - bucket.nonempty,
                exemplar: exemplar(facts, obligations[index]),
            })
        })
        .collect();
    let mut reasons = [0u64; REASONS.len()];
    let mut with_runtime_site = 0u64;
    for cause in guard_causes {
        if let Some(site) = cause.runtime {
            site.validate()?;
            if site.kind != cause.kind {
                return Err(Error::Invalid("probe guard census runtime kind"));
            }
            reasons[reason_index(site.reason)] += 1;
            with_runtime_site += 1;
        }
    }
    Ok(GuardCensus {
        basis: "reported_obligation_rows",
        total: obligations.len() as u64,
        all_reported_rows_counted: true,
        fixed_point_reached,
        counts_are_runtime_occurrences: false,
        counts_are_guard_paths: false,
        by_kind,
        detail_groups: DetailGroups {
            basis: "nonempty_exact_detail_text_and_issue_kind",
            limit: DETAIL_LIMIT,
            total_groups: groups,
            reported_groups: top.len(),
            other_groups: groups - top.len() as u64,
            truncated: groups > top.len() as u64,
            nonempty_detail_rows: indices.len() as u64,
            null_detail_rows: null_rows,
            empty_detail_rows: empty_rows,
            reported_rows,
            other_rows: indices.len() as u64 - reported_rows,
            top,
        },
        runtime_reasons: RuntimeReasons {
            basis: "root_guard_exemplars",
            guard_exemplars: guard_causes.len() as u64,
            with_runtime_site,
            without_runtime_site: guard_causes.len() as u64 - with_runtime_site,
            counts_complete_for_basis: true,
            all_context_first_sites_available: false,
            all_runtime_occurrences_counted: false,
            coverage: "Only saved guarded-root boundary exemplars; other context/runtime causes are unavailable.",
            by_reason: REASONS
                .into_iter()
                .zip(reasons)
                .filter(|(_, count)| *count != 0)
                .map(|(reason, count)| RuntimeReasonCount {
                    reason: reason.as_str(),
                    kind: format!("{:?}", reason.kind()),
                    count,
                })
                .collect(),
        },
    })
}

#[derive(Serialize)]
pub(super) struct FirstSiteCensus<'a> {
    basis: &'static str,
    scope: &'static str,
    total_retained_contexts: u64,
    unique_evaluated_contexts: Option<u64>,
    unique_evaluated_context_count_available: bool,
    evaluation_events: u64,
    reevaluation_events: u64,
    evaluation_event_scope: &'static str,
    saved_first_sites: u64,
    retained_contexts_without_saved_site: u64,
    all_saved_first_sites_counted: bool,
    fixed_point_reached: bool,
    partial: bool,
    is_current_failure_census: bool,
    is_current_root_cause_census: bool,
    all_runtime_occurrences_counted: bool,
    issue_context_provenance_coverage: &'static str,
    context_id_scope: &'static str,
    coverage: &'static str,
    reason_limit: usize,
    histogram_truncated: bool,
    exemplars_per_reason: usize,
    by_reason: Vec<FirstSiteReason<'a>>,
}
#[derive(Serialize)]
struct FirstSiteReason<'a> {
    reason: &'static str,
    kind: String,
    count: u64,
    exemplar: FirstSiteExemplar<'a>,
}
#[derive(Serialize)]
struct FirstSiteExemplar<'a> {
    retained_context_id: u32,
    node: u32,
    definition: Exemplar<'a>,
    operation: Option<FirstSiteOperation<'a>>,
}
#[derive(Serialize)]
struct FirstSiteOperation<'a> {
    id: u32,
    opcode: String,
    path: Option<&'a str>,
    span: OperationSpan,
}
#[derive(Serialize)]
struct OperationSpan {
    start: u32,
    end: u32,
}
#[derive(Clone, Copy)]
struct FirstSite {
    context: ContextId,
    node: NodeId,
    site: RuntimeIssueSite,
}

fn validate_first_site(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    retained_contexts: usize,
    row: FirstSite,
) -> Result<(), Error> {
    row.site.validate()?;
    if row.context.is_none() || row.context.index() >= retained_contexts {
        return Err(Error::Invalid("probe first runtime site context"));
    }
    let node = graph
        .nodes
        .get(row.node.index())
        .ok_or(Error::Invalid("probe first runtime site node"))?;
    validate_row(
        facts,
        Obligation {
            kind: row.site.kind,
            symbol: node.symbol,
            file: node.file,
            detail: selector_types::StrId::NONE,
        },
    )?;
    if node.symbol.is_none() {
        return Err(Error::Invalid("probe first runtime site symbol"));
    }
    if row.site.reason == RuntimeIssueReason::ExecutionGuard
        && !graph.successors(row.node).any(|(_, edge)| {
            edge.operation == row.site.operation
                && (edge.kind == EdgeKind::Guard || edge.flags & EDGE_UNKNOWN != 0)
        })
    {
        return Err(Error::Invalid("probe first runtime execution guard"));
    }
    if row.site.operation.is_none() {
        if row.site.reason == RuntimeIssueReason::MissingExecutableBody
            && (!node.body.is_none() || node.flags & NODE_EFFECTS_COMPLETE != 0)
        {
            return Err(Error::Invalid("probe first runtime missing body"));
        }
        return Ok(());
    }
    let body = facts
        .bodies
        .get(node.body.index())
        .ok_or(Error::Invalid("probe first runtime site body"))?;
    let operation = facts
        .operations
        .get(row.site.operation.index())
        .ok_or(Error::Invalid("probe first runtime site operation"))?;
    if body.symbol != node.symbol
        || operation.body != node.body
        || !body
            .operations
            .range()
            .contains(&row.site.operation.index())
        || (!body.file.is_none() && body.file.index() >= facts.files.len())
        || !row.site.reason.accepts_opcode(operation.opcode)
    {
        return Err(Error::Invalid(
            "probe first runtime site operation ownership",
        ));
    }
    Ok(())
}

fn first_site_key<'a>(
    facts: &'a FactSnapshot,
    graph: &ProgramGraph,
    row: FirstSite,
) -> (
    Option<&'a str>,
    Option<&'a str>,
    Option<&'a str>,
    bool,
    u32,
    u32,
    u32,
    u32,
    u32,
    u32,
) {
    let node = graph.nodes[row.node.index()];
    let definition = exemplar(
        facts,
        Obligation {
            kind: row.site.kind,
            symbol: node.symbol,
            file: node.file,
            detail: selector_types::StrId::NONE,
        },
    );
    let operation =
        (!row.site.operation.is_none()).then(|| &facts.operations[row.site.operation.index()]);
    (
        definition.context,
        definition.symbol,
        definition.path,
        operation.is_none(),
        operation.map_or(u32::MAX, |op| op.span.start),
        operation.map_or(u32::MAX, |op| op.span.end),
        operation.map_or(u32::MAX, |op| op.opcode as u32),
        row.site.operation.0,
        row.node.0,
        row.context.0,
    )
}

/// The session accessor guarantees one row per retained context. Count that
/// sparse history in one pass; retain only one actual site per known reason.
pub(super) fn first_runtime_sites<'a>(
    facts: &'a FactSnapshot,
    graph: &ProgramGraph,
    sites: impl ExactSizeIterator<Item = (ContextId, NodeId, RuntimeIssueSite)>,
    retained_contexts: usize,
    evaluation_events: u64,
    reevaluation_events: u64,
    fixed_point_reached: bool,
) -> Result<FirstSiteCensus<'a>, Error> {
    let expected_sites = sites.len();
    if expected_sites > retained_contexts || reevaluation_events > evaluation_events {
        return Err(Error::Invalid("probe first runtime site census totals"));
    }
    let mut counts = [0u64; REASONS.len()];
    let mut examples = [None::<FirstSite>; REASONS.len()];
    let mut scanned = 0usize;
    for (context, node, site) in sites {
        let row = FirstSite {
            context,
            node,
            site,
        };
        validate_first_site(facts, graph, retained_contexts, row)?;
        let index = reason_index(site.reason);
        counts[index] += 1;
        if examples[index]
            .is_none_or(|old| first_site_key(facts, graph, row) < first_site_key(facts, graph, old))
        {
            examples[index] = Some(row);
        }
        scanned += 1;
    }
    if scanned != expected_sites {
        return Err(Error::Invalid("probe first runtime site iterator length"));
    }
    let by_reason = REASONS
        .into_iter()
        .zip(counts)
        .zip(examples)
        .filter_map(|((reason, count), example)| {
            example.map(|row| {
                let node = graph.nodes[row.node.index()];
                let operation = (!row.site.operation.is_none()).then(|| {
                    let op = &facts.operations[row.site.operation.index()];
                    let body = &facts.bodies[op.body.index()];
                    FirstSiteOperation {
                        id: row.site.operation.0,
                        opcode: format!("{:?}", op.opcode),
                        path: (!body.file.is_none()).then(|| facts.path(body.file)),
                        span: OperationSpan {
                            start: op.span.start,
                            end: op.span.end,
                        },
                    }
                });
                FirstSiteReason {
                    reason: reason.as_str(),
                    kind: format!("{:?}", reason.kind()),
                    count,
                    exemplar: FirstSiteExemplar {
                        retained_context_id: row.context.0,
                        node: row.node.0,
                        definition: exemplar(
                            facts,
                            Obligation {
                                kind: row.site.kind,
                                symbol: node.symbol,
                                file: node.file,
                                detail: selector_types::StrId::NONE,
                            },
                        ),
                        operation,
                    },
                }
            })
        })
        .collect();
    Ok(FirstSiteCensus {
        basis: "first_ever_recorded_runtime_site_per_retained_context",
        scope: "all_retained_session_contexts",
        total_retained_contexts: retained_contexts as u64,
        unique_evaluated_contexts: None,
        unique_evaluated_context_count_available: false,
        evaluation_events,
        reevaluation_events,
        evaluation_event_scope: "session_counters_as_retained_or_restored",
        saved_first_sites: scanned as u64,
        retained_contexts_without_saved_site: (retained_contexts - scanned) as u64,
        all_saved_first_sites_counted: true,
        fixed_point_reached,
        partial: !fixed_point_reached,
        is_current_failure_census: false,
        is_current_root_cause_census: false,
        all_runtime_occurrences_counted: false,
        issue_context_provenance_coverage: "not_available",
        context_id_scope: "retained_session_only",
        coverage: "First ever recorded site, retained even if later evaluation resolves it. Retained state may include cache/restored or unrequested contexts. Counts are not final failures or current root-path causes.",
        reason_limit: REASONS.len(),
        histogram_truncated: false,
        exemplars_per_reason: 1,
        by_reason,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use selector_facts::{BodyRecord, FactBuilder, FileRecord, OperationRecord};
    use selector_graph::{EdgeRecord, NodeRecord};
    use selector_types::*;

    fn fixture() -> (FactBuilder, SymbolId) {
        let mut builder = FactBuilder::new();
        let path = builder.intern("Census.scala").unwrap();
        let context = builder.intern("fixture/test").unwrap();
        builder.facts.files.push(FileRecord {
            path,
            context,
            source: StrId::NONE,
            revision: StrId::NONE,
            source_hash: ContentHash::default(),
            flags: 0,
        });
        let symbol = builder.ensure_symbol("fixture/Census#", FileId(0)).unwrap();
        (builder, symbol)
    }
    fn row(kind: IssueKind, symbol: SymbolId, detail: StrId) -> Obligation {
        Obligation {
            kind,
            symbol,
            file: FileId(0),
            detail,
        }
    }
    fn json(facts: &FactSnapshot, rows: &[Obligation]) -> serde_json::Value {
        serde_json::to_value(build(facts, rows, &[], true).unwrap()).unwrap()
    }
    fn cause(symbol: SymbolId, runtime: Option<RuntimeIssueSite>) -> RootGuardEvidence {
        RootGuardEvidence {
            root: NodeId(0),
            node: NodeId(1),
            kind: IssueKind::UnknownExecution,
            file: FileId(0),
            symbol,
            detail: StrId::NONE,
            runtime,
        }
    }
    fn site_fixture() -> (FactBuilder, ProgramGraph) {
        let (mut builder, first) = fixture();
        let second = builder.ensure_symbol("fixture/Zeta#", FileId(0)).unwrap();
        let mut graph = ProgramGraph::default();
        for (index, symbol) in [first, second].into_iter().enumerate() {
            builder.facts.bodies.push(BodyRecord {
                symbol,
                file: FileId(0),
                span: Span { start: 0, end: 30 },
                name_span: Span { start: 0, end: 1 },
                operations: IdRange {
                    start: index as u32,
                    len: 1,
                },
                parameters: IdRange::default(),
                body_hash: ContentHash::default(),
                flags: 0,
            });
            builder.facts.operations.push(OperationRecord {
                body: BodyId(index as u32),
                opcode: Opcode::LoadField,
                target: symbol,
                dest: ValueId(1),
                a: ValueId(0),
                b: ValueId::NONE,
                arguments: IdRange::default(),
                span: Span { start: 10, end: 20 },
                flags: 0,
            });
            graph.nodes.push(NodeRecord {
                symbol,
                file: FileId(0),
                body: BodyId(index as u32),
                flags: 0,
            });
        }
        graph.index().unwrap();
        (builder, graph)
    }
    fn field_site(operation: u32) -> RuntimeIssueSite {
        RuntimeIssueSite {
            kind: IssueKind::UnknownExecution,
            operation: OperationId(operation),
            reason: RuntimeIssueReason::UnknownFieldValue,
        }
    }

    #[test]
    fn all_saved_first_sites_counted_with_order_independent_actual_exemplar() {
        let (builder, graph) = site_fixture();
        let mut rows = vec![
            (ContextId(0), NodeId(1), field_site(1)),
            (ContextId(1), NodeId(0), field_site(0)),
            (ContextId(2), NodeId(1), field_site(1)),
        ];
        let first = serde_json::to_value(
            first_runtime_sites(
                &builder.facts,
                &graph,
                rows.clone().into_iter(),
                4,
                7,
                4,
                true,
            )
            .unwrap(),
        )
        .unwrap();
        rows.reverse();
        assert_eq!(
            first,
            serde_json::to_value(
                first_runtime_sites(&builder.facts, &graph, rows.into_iter(), 4, 7, 4, true)
                    .unwrap()
            )
            .unwrap()
        );
        assert_eq!(first["saved_first_sites"], 3);
        assert_eq!(first["total_retained_contexts"], 4);
        assert_eq!(first["retained_contexts_without_saved_site"], 1);
        assert_eq!(first["all_saved_first_sites_counted"], true);
        assert_eq!(first["by_reason"][0]["count"], 3);
        let example = &first["by_reason"][0]["exemplar"];
        assert_eq!(example["retained_context_id"], 1);
        assert_eq!(example["definition"]["symbol"], "fixture/Census#");
        assert_eq!(example["operation"]["id"], 0);
        assert_eq!(example["operation"]["opcode"], "LoadField");
        assert_eq!(example["operation"]["path"], "Census.scala");
        assert_eq!(
            example["operation"]["span"],
            serde_json::json!({"start":10,"end":20})
        );
    }

    #[test]
    fn first_site_history_never_claims_unique_evaluated_contexts_or_current_failures() {
        let (builder, graph) = site_fixture();
        // Failed commit/retry can produce more first-evaluation events than
        // unique contexts. Restored evaluated contexts can produce zero events.
        for (evaluations, reevaluations) in [(4, 0), (0, 0)] {
            let result = serde_json::to_value(
                first_runtime_sites(
                    &builder.facts,
                    &graph,
                    [(ContextId(0), NodeId(0), field_site(0))].into_iter(),
                    3,
                    evaluations,
                    reevaluations,
                    false,
                )
                .unwrap(),
            )
            .unwrap();
            assert_eq!(result["unique_evaluated_contexts"], serde_json::Value::Null);
            assert_eq!(result["unique_evaluated_context_count_available"], false);
            assert_eq!(result["evaluation_events"], evaluations);
            assert_eq!(result["reevaluation_events"], reevaluations);
            assert_eq!(result["partial"], true);
            assert_eq!(result["fixed_point_reached"], false);
            assert_eq!(result["is_current_failure_census"], false);
            assert_eq!(result["is_current_root_cause_census"], false);
            assert_eq!(result["all_runtime_occurrences_counted"], false);
            assert_eq!(result["issue_context_provenance_coverage"], "not_available");
        }
    }

    #[test]
    fn every_first_site_is_validated_even_when_it_cannot_win_an_exemplar() {
        let (builder, graph) = site_fixture();
        let rows = [
            (ContextId(0), NodeId(0), field_site(0)),
            (ContextId(1), NodeId(1), field_site(0)), // operation belongs to node0
        ];
        assert!(
            first_runtime_sites(&builder.facts, &graph, rows.into_iter(), 2, 2, 0, true).is_err()
        );
        for row in [
            (ContextId::NONE, NodeId(0), field_site(0)),
            (ContextId(9), NodeId(0), field_site(0)),
            (ContextId(0), NodeId(99), field_site(0)),
            (
                ContextId(0),
                NodeId(0),
                RuntimeIssueSite {
                    kind: IssueKind::UnresolvedSymbol,
                    operation: OperationId(0),
                    reason: RuntimeIssueReason::MissingCallTarget,
                },
            ),
        ] {
            assert!(
                first_runtime_sites(&builder.facts, &graph, [row].into_iter(), 1, 1, 0, true)
                    .is_err()
            );
        }
        assert!(
            first_runtime_sites(
                &builder.facts,
                &graph,
                [(ContextId(0), NodeId(0), field_site(0))].into_iter(),
                0,
                1,
                0,
                true
            )
            .is_err()
        );
    }

    #[test]
    fn nonoperation_first_sites_remain_null_and_require_the_actual_missing_body_or_guard() {
        let (builder, mut graph) = site_fixture();
        graph.nodes[0].body = BodyId::NONE;
        let missing = RuntimeIssueSite {
            kind: IssueKind::UnknownExecution,
            operation: OperationId::NONE,
            reason: RuntimeIssueReason::MissingExecutableBody,
        };
        let result = serde_json::to_value(
            first_runtime_sites(
                &builder.facts,
                &graph,
                [(ContextId(0), NodeId(0), missing)].into_iter(),
                1,
                1,
                0,
                true,
            )
            .unwrap(),
        )
        .unwrap();
        assert_eq!(
            result["by_reason"][0]["exemplar"]["operation"],
            serde_json::Value::Null
        );
        graph.nodes[0].flags |= NODE_EFFECTS_COMPLETE;
        assert!(
            first_runtime_sites(
                &builder.facts,
                &graph,
                [(ContextId(0), NodeId(0), missing)].into_iter(),
                1,
                1,
                0,
                true
            )
            .is_err()
        );
        graph.nodes[0].flags = 0;
        let guard = RuntimeIssueSite {
            reason: RuntimeIssueReason::ExecutionGuard,
            ..missing
        };
        assert!(
            first_runtime_sites(
                &builder.facts,
                &graph,
                [(ContextId(0), NodeId(0), guard)].into_iter(),
                1,
                1,
                0,
                true
            )
            .is_err()
        );
        graph.edges.push(EdgeRecord {
            source: NodeId(0),
            target: NodeId(0),
            kind: EdgeKind::Guard,
            operation: OperationId::NONE,
            occurrence: OccurrenceId::NONE,
            receiver: SymbolId::NONE,
            flags: EDGE_UNKNOWN,
        });
        graph.index().unwrap();
        assert!(
            first_runtime_sites(
                &builder.facts,
                &graph,
                [(ContextId(0), NodeId(0), guard)].into_iter(),
                1,
                1,
                0,
                true
            )
            .is_ok()
        );
    }

    #[test]
    fn empty_first_site_history_has_exact_zero_totals_without_an_absence_claim() {
        let (builder, graph) = site_fixture();
        let result = serde_json::to_value(
            first_runtime_sites(&builder.facts, &graph, std::iter::empty(), 2, 2, 0, true).unwrap(),
        )
        .unwrap();
        assert_eq!(result["saved_first_sites"], 0);
        assert_eq!(result["retained_contexts_without_saved_site"], 2);
        assert_eq!(result["by_reason"], serde_json::json!([]));
        assert_eq!(result["histogram_truncated"], false);
        assert_eq!(result["is_current_failure_census"], false);
        assert_eq!(result["all_runtime_occurrences_counted"], false);
    }

    #[test]
    fn exact_text_groups_duplicate_pool_ids_but_preserves_kind_and_missing_detail() {
        let (mut builder, symbol) = fixture();
        let detail = builder.intern("same exact diagnostic").unwrap();
        let empty = builder.intern("").unwrap();
        let duplicate = StrId::checked(builder.facts.strings.entries.len()).unwrap();
        let entry = builder.facts.strings.entries[detail.index()];
        builder.facts.strings.entries.push(entry);
        let rows = [
            row(IssueKind::UnknownExecution, symbol, detail),
            row(IssueKind::UnknownExecution, symbol, duplicate),
            row(IssueKind::MissingSyntax, symbol, detail),
            row(IssueKind::MissingSyntax, symbol, StrId::NONE),
            row(IssueKind::MissingSyntax, symbol, empty),
            row(IssueKind::IncompleteHierarchy, symbol, StrId::NONE),
        ];
        let result = json(&builder.facts, &rows);
        assert_eq!(result["total"], 6);
        assert_eq!(result["detail_groups"]["total_groups"], 2);
        assert_eq!(result["detail_groups"]["top"][0]["count"], 2);
        assert_eq!(
            result["detail_groups"]["top"][0]["kind"],
            "UnknownExecution"
        );
        assert_eq!(result["detail_groups"]["null_detail_rows"], 2);
        assert_eq!(result["detail_groups"]["empty_detail_rows"], 1);
        assert_eq!(result["detail_groups"]["nonempty_detail_rows"], 3);
        assert_eq!(result["by_kind"][2]["kind"], "IncompleteHierarchy");
        assert_eq!(result["by_kind"][2]["count"], 1);
        let sum: u64 = result["by_kind"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| row["count"].as_u64().unwrap())
            .sum();
        assert_eq!(sum, 6);
    }

    #[test]
    fn top_sixteen_groups_and_exemplars_are_stable_under_input_permutation() {
        let (mut builder, symbol) = fixture();
        let earlier_symbol = builder.ensure_symbol("fixture/AAA#", FileId(0)).unwrap();
        let mut rows = Vec::new();
        for index in (0..32).rev() {
            let detail = builder.intern(&format!("detail-{index:02}")).unwrap();
            rows.push(row(IssueKind::UnknownExecution, symbol, detail));
            rows.push(row(IssueKind::UnknownExecution, earlier_symbol, detail));
        }
        let first = json(&builder.facts, &rows);
        rows.reverse();
        rows.rotate_left(7);
        assert_eq!(first, json(&builder.facts, &rows));
        assert_eq!(first["detail_groups"]["total_groups"], 32);
        assert_eq!(first["detail_groups"]["reported_groups"], 16);
        assert_eq!(first["detail_groups"]["other_groups"], 16);
        assert_eq!(first["detail_groups"]["reported_rows"], 32);
        assert_eq!(first["detail_groups"]["other_rows"], 32);
        assert_eq!(first["detail_groups"]["truncated"], true);
        assert_eq!(first["detail_groups"]["top"][0]["detail"], "detail-00");
        assert_eq!(first["detail_groups"]["top"][15]["detail"], "detail-15");
        assert_eq!(
            first["detail_groups"]["top"][0]["exemplar"]["symbol"],
            "fixture/AAA#"
        );
    }

    #[test]
    fn counts_rank_before_kind_and_detail_ties() {
        let (mut builder, symbol) = fixture();
        let alpha = builder.intern("alpha").unwrap();
        let zeta = builder.intern("zeta").unwrap();
        let rows = [
            row(IssueKind::MissingSource, symbol, alpha),
            row(IssueKind::UnknownExecution, symbol, zeta),
            row(IssueKind::UnknownExecution, symbol, zeta),
            row(IssueKind::MissingSyntax, symbol, zeta),
        ];
        let result = json(&builder.facts, &rows);
        assert_eq!(result["detail_groups"]["top"][0]["detail"], "zeta");
        assert_eq!(result["detail_groups"]["top"][0]["count"], 2);
        assert_eq!(result["detail_groups"]["top"][1]["kind"], "MissingSource");
        assert_eq!(result["detail_groups"]["top"][2]["kind"], "MissingSyntax");
    }

    #[test]
    fn empty_runtime_exemplar_histogram_never_claims_all_context_coverage() {
        let (builder, symbol) = fixture();
        let rows = [row(IssueKind::UnknownExecution, symbol, StrId::NONE)];
        let result = serde_json::to_value(
            build(&builder.facts, &rows, &[cause(symbol, None)], true).unwrap(),
        )
        .unwrap();
        assert_eq!(result["runtime_reasons"]["guard_exemplars"], 1);
        assert_eq!(result["runtime_reasons"]["without_runtime_site"], 1);
        assert_eq!(result["runtime_reasons"]["with_runtime_site"], 0);
        assert_eq!(
            result["runtime_reasons"]["by_reason"],
            serde_json::json!([])
        );
        assert_eq!(
            result["runtime_reasons"]["all_context_first_sites_available"],
            false
        );
        assert_eq!(
            result["runtime_reasons"]["all_runtime_occurrences_counted"],
            false
        );
        assert_eq!(result["counts_are_runtime_occurrences"], false);
        assert_eq!(result["counts_are_guard_paths"], false);
    }

    #[test]
    fn runtime_counts_only_actual_exemplar_sites_and_rejects_kind_mismatch() {
        let (builder, symbol) = fixture();
        let site = RuntimeIssueSite {
            kind: IssueKind::UnknownExecution,
            operation: OperationId(0),
            reason: RuntimeIssueReason::UnknownFieldValue,
        };
        let mut guard = cause(symbol, Some(site));
        let result =
            serde_json::to_value(build(&builder.facts, &[], &[guard], true).unwrap()).unwrap();
        assert_eq!(
            result["runtime_reasons"]["by_reason"][0]["reason"],
            "unknown_field_value"
        );
        assert_eq!(result["runtime_reasons"]["by_reason"][0]["count"], 1);
        assert_eq!(
            result["runtime_reasons"]["all_context_first_sites_available"],
            false
        );
        guard.kind = IssueKind::MissingBinary;
        assert!(build(&builder.facts, &[], &[guard], true).is_err());
    }

    #[test]
    fn partial_results_count_all_reported_rows_without_claiming_a_fixed_point() {
        let (builder, _) = fixture();
        let rows = [Obligation {
            kind: IssueKind::ResourceLimit,
            file: FileId::NONE,
            symbol: SymbolId::NONE,
            detail: StrId::NONE,
        }];
        let result =
            serde_json::to_value(build(&builder.facts, &rows, &[], false).unwrap()).unwrap();
        assert_eq!(result["total"], 1);
        assert_eq!(result["all_reported_rows_counted"], true);
        assert_eq!(result["fixed_point_reached"], false);
        assert_eq!(
            result["by_kind"][0]["exemplar"]["symbol"],
            serde_json::Value::Null
        );
        assert_eq!(
            result["by_kind"][0]["exemplar"]["path"],
            serde_json::Value::Null
        );
        assert_eq!(result["detail_groups"]["null_detail_rows"], 1);
    }

    #[test]
    fn invalid_row_references_fail_before_sorting_or_rendering() {
        let (builder, symbol) = fixture();
        for invalid in [
            Obligation {
                file: FileId(99),
                ..row(IssueKind::MissingSyntax, symbol, StrId::NONE)
            },
            row(IssueKind::MissingSyntax, SymbolId(99), StrId::NONE),
            row(IssueKind::MissingSyntax, symbol, StrId(999)),
        ] {
            assert!(build(&builder.facts, &[invalid], &[], true).is_err());
        }
    }
}
