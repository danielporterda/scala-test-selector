//! Inspect the contexts reachable from one recorded root through saved calls.
//! No transfer evaluation, invented edges, or selection certificates.
use super::*;
use serde::Serialize;
use std::mem::size_of;

const NONE: u32 = u32::MAX;
const ROOT: u32 = u32::MAX - 1;
const PATH_CALLS: usize = 96;

#[derive(Debug, Serialize)]
pub struct RootFrontier<'a> {
    root: ContextLocation<'a>,
    reachable_contexts: usize,
    reachable_calls: usize,
    reachable_effects_open_contexts: usize,
    reachable_pending_contexts: usize,
    reachable_issue_contexts: usize,
    reachable_runtime_site_contexts: usize,
    runtime_site_groups: usize,
    reachable_graph_issue_contexts: usize,
    checkpoint_global_graph_issues: usize,
    checkpoint_pending_roots: usize,
    scratch_budget_bytes: usize,
    top_runtime_sites: Vec<RuntimeSite<'a>>,
    nearest_pending: Option<Witness<'a>>,
    nearest_graph_issue: Option<GraphBoundary<'a>>,
    requested_target_node: Option<u32>,
    target: Option<Witness<'a>>,
}

#[derive(Debug, Serialize)]
struct ContextLocation<'a> {
    context_id: u32,
    node: u32,
    symbol: &'a str,
    compiler_context: &'a str,
    path: &'a str,
    receiver_set: u32,
    receiver_unknown: u32,
    argument_frame: u32,
    evaluated: bool,
    widened: bool,
    effects_open: bool,
}

#[derive(Debug, Serialize)]
struct OperationLocation<'a> {
    id: u32,
    opcode: String,
    target_symbol: Option<&'a str>,
    span: [u32; 2],
}

#[derive(Debug, Serialize)]
struct SavedCall<'a> {
    from: ContextLocation<'a>,
    to: ContextLocation<'a>,
    operation: Option<OperationLocation<'a>>,
    kind: String,
    graph_edge: Option<u32>,
    capture_binding: Option<u32>,
}

#[derive(Debug, Serialize)]
struct Witness<'a> {
    terminal: ContextLocation<'a>,
    omitted_prefix_calls: usize,
    calls: Vec<SavedCall<'a>>,
}

#[derive(Debug, Serialize)]
struct RuntimeSite<'a> {
    contexts: usize,
    reason: &'static str,
    operation: Option<OperationLocation<'a>>,
    witness: Witness<'a>,
}

#[derive(Debug, Serialize)]
struct GraphBoundary<'a> {
    issue_index: usize,
    kind: String,
    detail: &'a str,
    witness: Witness<'a>,
}

// Sorted once by exact node and site, then the BFS position gives a shortest
// representative (stable across repeated inspections of this checkpoint).
type Observation = (u32, u32, u32, u32);
// Count first for top-K ranking; prefer a nearer representative for ties.
type RankedSite = (usize, Reverse<u32>);

fn allocate<T>(capacity: usize) -> Result<Vec<T>, Error> {
    let mut v = Vec::new();
    v.try_reserve_exact(capacity)
        .map_err(|_| Error::Limit("root frontier allocation"))?;
    Ok(v)
}

impl<'a> CheckpointView<'a> {
    /// Inspect one unambiguous admitted root, not an arbitrary occurrence of
    /// its node as a callee. Paths are exact within the saved abstract graph;
    /// the graph itself can contain spurious calls and can be incomplete.
    pub fn root_frontier(
        &self,
        root_node: NodeId,
        target_node: Option<NodeId>,
        top_rows: usize,
    ) -> Result<RootFrontier<'a>, Error> {
        let s = &self.session;
        if root_node.index() >= s.graph.nodes.len()
            || target_node.is_some_and(|n| n.index() >= s.graph.nodes.len())
        {
            return Err(Error::Invalid("root frontier node"));
        }
        let mut roots = s
            .roots
            .iter()
            .filter(|id| s.contexts[id.index()].key.node == root_node)
            .copied();
        let root = roots.next().ok_or(Error::Invalid(
            "root frontier node was not admitted as a root",
        ))?;
        if roots.any(|id| id != root) {
            return Err(Error::Invalid("ambiguous saved root node"));
        }

        let n = s.contexts.len();
        let m = s.calls.len();
        if n >= ROOT as usize || m >= ROOT as usize || top_rows > self.limits.max_rows {
            return Err(Error::Limit("root frontier rows"));
        }
        let max_sites = n.min(s.runtime_issue_sites.len());
        let scratch_budget_bytes = [
            (n, 3 * size_of::<u32>() + size_of::<bool>()), // offsets, cursor/parent, queue, pending
            (1, size_of::<u32>()),
            (m, size_of::<u32>()),
            (max_sites, size_of::<Observation>()),
            (
                top_rows,
                size_of::<Reverse<RankedSite>>() + size_of::<RuntimeSite<'_>>(),
            ),
            (top_rows + 3, PATH_CALLS * (size_of::<SavedCall<'_>>() + 96)),
        ]
        .into_iter()
        .try_fold(0usize, |sum, (count, width)| {
            count.checked_mul(width).and_then(|n| sum.checked_add(n))
        })
        .ok_or(Error::Limit("root frontier memory"))?;
        if self
            .owned_bytes()
            .checked_add(scratch_budget_bytes)
            .is_none_or(|bytes| bytes > self.limits.memory_budget_bytes)
        {
            return Err(Error::Limit("root frontier memory"));
        }
        let mut offsets = allocate(n + 1)?;
        offsets.resize(n + 1, 0u32);
        for call in &s.calls {
            offsets[call.source.index() + 1] += 1;
        }
        for i in 1..=n {
            offsets[i] += offsets[i - 1];
        }
        let mut parent = allocate(n)?;
        parent.extend_from_slice(&offsets[..n]);
        let mut outgoing = allocate(m)?;
        outgoing.resize(m, 0u32);
        for (i, call) in s.calls.iter().enumerate() {
            let at = &mut parent[call.source.index()];
            outgoing[*at as usize] = i as u32;
            *at += 1;
        }
        parent.fill(NONE);
        parent[root.index()] = ROOT;
        let mut queue = allocate(n)?;
        queue.push(root.0);
        let mut pending = allocate(n)?;
        pending.resize(n, false);
        for id in &s.ready {
            pending[id.index()] = true;
        }

        let mut head = 0;
        let mut reachable_calls = 0;
        let mut reachable_pending_contexts = 0;
        let mut reachable_issue_contexts = 0;
        let mut reachable_effects_open_contexts = 0;
        let mut reachable_graph_issue_contexts = 0;
        let mut nearest_pending = None;
        let mut nearest_graph_issue = None;
        let mut target = None;
        let mut sites = allocate(max_sites)?;
        while head < queue.len() {
            let id = ContextId(queue[head]);
            let context = s.contexts[id.index()];
            if Some(context.key.node) == target_node {
                target.get_or_insert(id);
            }
            if pending[id.index()] || !context.evaluated {
                nearest_pending.get_or_insert(id);
                reachable_pending_contexts += 1;
            }
            reachable_effects_open_contexts += usize::from(context.effects_open);
            reachable_issue_contexts += usize::from(s.issue_contexts.contains(&id));
            let file = s.graph.nodes[context.key.node.index()].file;
            if let Some(&issue) = s
                .issue_postings
                .nodes(context.key.node)
                .first()
                .or_else(|| s.issue_postings.files(file).first())
            {
                nearest_graph_issue.get_or_insert((issue, id));
                reachable_graph_issue_contexts += 1;
            }
            if let Some(site) = s.runtime_issue_sites.get(&id) {
                sites.push((
                    context.key.node.0,
                    site.reason as u32,
                    site.operation.0,
                    head as u32,
                ));
            }
            let links = &outgoing[offsets[id.index()] as usize..offsets[id.index() + 1] as usize];
            reachable_calls += links.len();
            for &call in links {
                let target = s.calls[call as usize].target;
                if parent[target.index()] == NONE {
                    parent[target.index()] = call;
                    queue.push(target.0);
                }
            }
            head += 1;
        }

        let mut top = BinaryHeap::<Reverse<RankedSite>>::new();
        top.try_reserve_exact(top_rows)
            .map_err(|_| Error::Limit("root frontier allocation"))?;
        sites.sort_unstable();
        let mut at = 0;
        let mut groups = 0;
        while at < sites.len() {
            let (node, reason, operation, first) = sites[at];
            let start = at;
            while at < sites.len()
                && (sites[at].0, sites[at].1, sites[at].2) == (node, reason, operation)
            {
                at += 1;
            }
            let rank = (at - start, Reverse(first));
            if top.len() < top_rows {
                top.push(Reverse(rank));
            } else if top.peek().is_some_and(|smallest| rank > smallest.0) {
                *top.peek_mut().unwrap() = Reverse(rank);
            }
            groups += 1;
        }
        let mut top_runtime_sites = allocate(top.len())?;
        for Reverse((count, Reverse(first))) in top.into_sorted_vec() {
            let id = ContextId(queue[first as usize]);
            let site = s.runtime_issue_sites[&id];
            top_runtime_sites.push(RuntimeSite {
                contexts: count,
                reason: site.reason.as_str(),
                operation: operation_location(s.facts, site.operation),
                witness: witness(s, &parent, id)?,
            });
        }

        Ok(RootFrontier {
            root: context_location(s, root),
            reachable_contexts: queue.len(),
            reachable_calls,
            reachable_effects_open_contexts,
            reachable_pending_contexts,
            reachable_issue_contexts,
            reachable_runtime_site_contexts: sites.len(),
            runtime_site_groups: groups,
            reachable_graph_issue_contexts,
            checkpoint_global_graph_issues: s.issue_postings.global.len(),
            checkpoint_pending_roots: s.pending_roots.len(),
            scratch_budget_bytes,
            top_runtime_sites,
            nearest_pending: nearest_pending
                .map(|id| witness(s, &parent, id))
                .transpose()?,
            nearest_graph_issue: nearest_graph_issue
                .map(|(issue_index, id)| -> Result<_, Error> {
                    let issue = s.graph.issues[issue_index];
                    Ok(GraphBoundary {
                        issue_index,
                        kind: format!("{:?}", issue.kind),
                        detail: s.facts.text(issue.detail),
                        witness: witness(s, &parent, id)?,
                    })
                })
                .transpose()?,
            requested_target_node: target_node.map(|n| n.0),
            target: target.map(|id| witness(s, &parent, id)).transpose()?,
        })
    }
}

fn context_location<'a>(s: &QuerySession<'a>, id: ContextId) -> ContextLocation<'a> {
    let c = s.contexts[id.index()];
    let node = s.graph.nodes[c.key.node.index()];
    let symbol = s.facts.symbols[node.symbol.index()];
    ContextLocation {
        context_id: id.0,
        node: c.key.node.0,
        symbol: s.facts.symbol_name(node.symbol),
        compiler_context: s.facts.text(symbol.context),
        path: s.facts.path(node.file),
        receiver_set: c.key.receiver.set.0,
        receiver_unknown: c.key.receiver.unknown,
        argument_frame: c.key.arguments.0,
        evaluated: c.evaluated,
        widened: c.widened,
        effects_open: c.effects_open,
    }
}

fn operation_location(facts: &FactSnapshot, id: OperationId) -> Option<OperationLocation<'_>> {
    if id.is_none() {
        return None;
    }
    let op = facts.operations[id.index()];
    Some(OperationLocation {
        id: id.0,
        opcode: format!("{:?}", op.opcode),
        target_symbol: (!op.target.is_none()).then(|| facts.symbol_name(op.target)),
        span: [op.span.start, op.span.end],
    })
}

fn witness<'a>(
    s: &QuerySession<'a>,
    parent: &[u32],
    terminal: ContextId,
) -> Result<Witness<'a>, Error> {
    let mut indices = [0; PATH_CALLS];
    let mut depth = 0;
    let mut current = terminal;
    while parent[current.index()] != ROOT {
        let index = parent[current.index()];
        if depth < PATH_CALLS {
            indices[depth] = index;
        }
        current = s.calls[index as usize].source;
        depth += 1;
    }
    let count = depth.min(PATH_CALLS);
    let mut calls = allocate(count)?;
    for &index in indices[..count].iter().rev() {
        let call = s.calls[index as usize];
        calls.push(SavedCall {
            from: context_location(s, call.source),
            to: context_location(s, call.target),
            operation: operation_location(s.facts, call.operation),
            kind: format!("{:?}", call.kind),
            graph_edge: (!call.edge.is_none()).then_some(call.edge.0),
            capture_binding: (call.binding != NONE).then_some(call.binding),
        });
    }
    Ok(Witness {
        terminal: context_location(s, terminal),
        omitted_prefix_calls: depth - count,
        calls,
    })
}
