//! Static retention diagnostics, independent of observed execution or selection.
//!
//! A certificate says the current conservative kernel would attach an immutable
//! graph issue to an admitted root. It is not a concrete must-execute claim,
//! affected-code proof, fixed point, or permission to omit a suite. In particular,
//! these diagnostics must not remove guarded writers from a subsequent query.
use crate::PlannedRoot;
use selector_facts::FactSnapshot;
use selector_graph::ProgramGraph;
use selector_types::*;
use sha2::{Digest, Sha256};
use std::mem::size_of;

pub const VERSION: &str = "selector-static-retention/1";

#[derive(Clone, Copy, Debug)]
pub struct RetentionLimits {
    /// Diagnostic storage only; borrowed immutable program inputs are separate.
    pub memory_budget_bytes: usize,
    pub max_path_edges: usize,
    pub max_total_path_edges: usize,
}
impl Default for RetentionLimits {
    fn default() -> Self {
        Self {
            memory_budget_bytes: 128 * 1024 * 1024,
            max_path_edges: 64,
            max_total_path_edges: 65_536,
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnprovedReason {
    MissingRoot,
    NoStaticGuardPath,
    PathBound,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GuardReference {
    pub issue: u32,
    /// NONE means a globally scoped immutable graph issue.
    pub node: NodeId,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RootRetention {
    pub root: PlannedRoot,
    pub guard: Option<GuardReference>,
    pub path: IdRange,
    pub unproved: Option<UnprovedReason>,
}
#[derive(Debug)]
pub struct RetentionPrecheck {
    facts: ContentHash,
    graph: ContentHash,
    identity: ContentHash,
    roots: Vec<RootRetention>,
    edges: Vec<EdgeId>,
    scratch_bytes: usize,
}
impl RetentionPrecheck {
    pub fn roots(&self) -> &[RootRetention] {
        &self.roots
    }
    pub fn path(&self, root: &RootRetention) -> Option<&[EdgeId]> {
        self.edges.get(root.path.range())
    }
    pub fn identity(&self) -> ContentHash {
        self.identity
    }
    pub fn eligible_roots(&self) -> usize {
        self.roots
            .iter()
            .filter(|root| root.guard.is_some())
            .count()
    }
    pub fn all_roots_known_kept(&self) -> bool {
        !self.roots.is_empty() && self.eligible_roots() == self.roots.len()
    }
    pub fn scratch_bytes(&self) -> usize {
        self.scratch_bytes
    }
    pub fn owned_bytes(&self) -> usize {
        self.roots.capacity() * size_of::<RootRetention>()
            + self.edges.capacity() * size_of::<EdgeId>()
    }
    /// Recheck both the seal and each actual issue/path predicate. Even a
    /// recomputed seal cannot turn a virtual or unrelated edge into authority.
    pub fn validate(&self, facts: &FactSnapshot, graph: &ProgramGraph) -> Result<(), Error> {
        validate_inputs(facts, graph)?;
        if self.facts != facts.identity
            || self.graph != graph.identity
            || self.identity != seal(self)
        {
            return Err(Error::Invalid("retention certificate binding/seal"));
        }
        let mut end = 0usize;
        for row in &self.roots {
            validate_root(facts, graph, row.root)?;
            if row.path.start as usize != end || row.path.range().end > self.edges.len() {
                return Err(Error::Invalid("retention path range"));
            }
            end = row.path.range().end;
            let Some(guard) = row.guard else {
                if row.unproved.is_none() || row.path.len != 0 {
                    return Err(Error::Invalid("unproved retention row"));
                }
                continue;
            };
            if row.root.node.is_none() || row.unproved.is_some() {
                return Err(Error::Invalid("retention root guard"));
            }
            let issue = graph
                .issues
                .get(guard.issue as usize)
                .ok_or(Error::Invalid("retention issue"))?;
            let mut node = row.root.node;
            for &edge in self
                .path(row)
                .ok_or(Error::Invalid("retention path range"))?
            {
                let record = graph
                    .edges
                    .get(edge.index())
                    .ok_or(Error::Invalid("retention edge"))?;
                if record.source != node || !allowed_edge(facts, graph, record)? {
                    return Err(Error::Invalid("retention path predicate"));
                }
                node = record.target;
            }
            if guard.node.is_none() {
                if !issue.node.is_none() || !issue.file.is_none() || row.path.len != 0 {
                    return Err(Error::Invalid("retention global scope"));
                }
            } else if node != guard.node || !matches_scope(graph, issue, node) {
                return Err(Error::Invalid("retention issue scope"));
            }
        }
        if end != self.edges.len() {
            return Err(Error::Invalid("retention unused path rows"));
        }
        Ok(())
    }
}

/// Includes missing catalogue roots as explicit unproved rows. No catalogue
/// entry is lost merely because its graph mapping is absent.
pub fn catalogue_roots(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
) -> Result<Vec<PlannedRoot>, Error> {
    validate_inputs(facts, graph)?;
    Ok(facts
        .suites
        .iter()
        .map(|suite| PlannedRoot {
            node: graph.node_for_symbol(suite.symbol).unwrap_or(NodeId::NONE),
            receiver: suite.symbol,
        })
        .collect())
}

pub fn precheck(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    roots: &[PlannedRoot],
    limits: &RetentionLimits,
) -> Result<RetentionPrecheck, Error> {
    if limits.max_path_edges > u32::MAX as usize || limits.max_total_path_edges > u32::MAX as usize
    {
        return Err(Error::Limit("retention path limits"));
    }
    let n = graph.nodes.len();
    let path_capacity = roots
        .len()
        .checked_mul(limits.max_path_edges)
        .ok_or(Error::Limit("retention path capacity"))?
        .min(limits.max_total_path_edges);
    let retained_estimate = roots
        .len()
        .checked_mul(size_of::<RootRetention>())
        .and_then(|bytes| {
            path_capacity
                .checked_mul(4)
                .and_then(|p| bytes.checked_add(p))
        })
        .ok_or(Error::Limit("retention storage"))?;
    let working_estimate = n
        .checked_mul(16)
        .and_then(|bytes| {
            facts
                .files
                .len()
                .checked_mul(4)
                .and_then(|f| bytes.checked_add(f))
        })
        .and_then(|bytes| bytes.checked_add(retained_estimate))
        .ok_or(Error::Limit("retention scratch"))?;
    let admission_estimate = graph
        .edges
        .len()
        .checked_add(63)
        .and_then(|edges| (edges / 64).checked_mul(8))
        .ok_or(Error::Limit("retention admission scratch"))?;
    if working_estimate.max(admission_estimate) > limits.memory_budget_bytes {
        return Err(Error::Limit("retention memory budget"));
    }
    validate_inputs(facts, graph)?;
    for &root in roots {
        validate_root(facts, graph, root)?;
    }
    let mut causes = filled(n, u32::MAX)?;
    let mut files = filled(facts.files.len(), u32::MAX)?;
    let mut global = None;
    for (i, issue) in graph.issues.iter().enumerate() {
        let index = i as u32;
        if !issue.node.is_none() {
            causes[issue.node.index()] = causes[issue.node.index()].min(index);
        } else if !issue.file.is_none() {
            files[issue.file.index()] = files[issue.file.index()].min(index);
        } else {
            global = global.or(Some(index));
        }
    }
    for (i, node) in graph.nodes.iter().enumerate() {
        if !node.file.is_none() {
            causes[i] = causes[i].min(files[node.file.index()]);
        }
    }
    let mut next = filled(n, EdgeId::NONE)?;
    let mut depth = filled(n, u32::MAX)?;
    let mut queue = Vec::new();
    queue
        .try_reserve_exact(n)
        .map_err(|_| Error::Limit("retention queue"))?;
    for (i, &cause) in causes.iter().enumerate() {
        if cause != u32::MAX {
            depth[i] = 0;
            queue.push(NodeId(i as u32));
        }
    }
    let mut cursor = 0;
    while cursor < queue.len() {
        let target = queue[cursor];
        cursor += 1;
        if depth[target.index()] as usize >= limits.max_path_edges {
            continue;
        }
        for (id, edge) in graph.predecessors(target) {
            if causes[edge.source.index()] == u32::MAX && allowed_edge(facts, graph, edge)? {
                causes[edge.source.index()] = causes[target.index()];
                depth[edge.source.index()] = depth[target.index()] + 1;
                next[edge.source.index()] = id;
                queue.push(edge.source);
            }
        }
    }
    let mut rows = Vec::new();
    rows.try_reserve_exact(roots.len())
        .map_err(|_| Error::Limit("retention root rows"))?;
    let mut paths = Vec::new();
    paths
        .try_reserve_exact(path_capacity)
        .map_err(|_| Error::Limit("retention path rows"))?;
    for &root in roots {
        let start = u32::try_from(paths.len()).map_err(|_| Error::Limit("retention paths"))?;
        let mut row = RootRetention {
            root,
            guard: None,
            path: IdRange { start, len: 0 },
            unproved: Some(UnprovedReason::NoStaticGuardPath),
        };
        if root.node.is_none() {
            row.unproved = Some(UnprovedReason::MissingRoot);
        } else if let Some(issue) = global {
            row.guard = Some(GuardReference {
                issue,
                node: NodeId::NONE,
            });
            row.unproved = None;
        } else if causes[root.node.index()] != u32::MAX {
            let length = depth[root.node.index()] as usize;
            if paths
                .len()
                .checked_add(length)
                .is_some_and(|end| end <= path_capacity)
            {
                let mut node = root.node;
                while !next[node.index()].is_none() {
                    let edge = next[node.index()];
                    paths.push(edge);
                    node = graph.edges[edge.index()].target;
                }
                row.guard = Some(GuardReference {
                    issue: causes[root.node.index()],
                    node,
                });
                row.path.len = length as u32;
                row.unproved = None;
            } else {
                row.unproved = Some(UnprovedReason::PathBound);
            }
        }
        rows.push(row);
    }
    let actual = causes.capacity() * 4
        + files.capacity() * 4
        + next.capacity() * 4
        + depth.capacity() * 4
        + queue.capacity() * 4
        + rows.capacity() * size_of::<RootRetention>()
        + paths.capacity() * 4;
    if actual > limits.memory_budget_bytes {
        return Err(Error::Limit("retention actual storage"));
    }
    let mut result = RetentionPrecheck {
        facts: facts.identity,
        graph: graph.identity,
        identity: ContentHash::default(),
        roots: rows,
        edges: paths,
        scratch_bytes: actual,
    };
    result.identity = seal(&result);
    Ok(result)
}

fn filled<T: Clone>(n: usize, value: T) -> Result<Vec<T>, Error> {
    let mut out = Vec::new();
    out.try_reserve_exact(n)
        .map_err(|_| Error::Limit("retention arrays"))?;
    out.resize(n, value);
    Ok(out)
}

fn validate_root(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    root: PlannedRoot,
) -> Result<(), Error> {
    if (!root.node.is_none() && root.node.index() >= graph.nodes.len())
        || (!root.receiver.is_none() && root.receiver.index() >= facts.symbols.len())
        || (root.node.is_none() && root.receiver.is_none())
    {
        return Err(Error::Invalid("retention root binding"));
    }
    Ok(())
}
fn validate_inputs(facts: &FactSnapshot, graph: &ProgramGraph) -> Result<(), Error> {
    facts.validate()?;
    graph.validate()?;
    if facts.identity == ContentHash::default()
        || graph.identity == ContentHash::default()
        || graph.facts_identity != facts.identity
        || graph.symbol_nodes.len() != facts.symbols.len()
    {
        return Err(Error::Invalid("retention snapshot binding"));
    }
    for node in &graph.nodes {
        if node.symbol.index() >= facts.symbols.len()
            || (!node.file.is_none() && node.file.index() >= facts.files.len())
        {
            return Err(Error::Invalid("retention node binding"));
        }
        if !node.body.is_none() {
            let body = facts
                .bodies
                .get(node.body.index())
                .ok_or(Error::Invalid("retention body"))?;
            if body.symbol != node.symbol || body.file != node.file {
                return Err(Error::Invalid("retention body binding"));
            }
        }
    }
    for issue in &graph.issues {
        if (!issue.file.is_none() && issue.file.index() >= facts.files.len())
            || (!issue.symbol.is_none() && issue.symbol.index() >= facts.symbols.len())
            || (!issue.detail.is_none() && issue.detail.index() >= facts.strings.len())
        {
            return Err(Error::Invalid("retention issue fact reference"));
        }
    }
    for edge in &graph.edges {
        if !edge.operation.is_none() {
            let op = facts
                .operations
                .get(edge.operation.index())
                .ok_or(Error::Invalid("retention operation"))?;
            if graph.nodes[edge.source.index()].body != op.body {
                return Err(Error::Invalid("retention operation source"));
            }
        }
    }
    Ok(())
}
fn matches_scope(graph: &ProgramGraph, issue: &selector_graph::GraphIssue, node: NodeId) -> bool {
    if !issue.node.is_none() {
        issue.node == node
    } else {
        !issue.file.is_none() && graph.nodes[node.index()].file == issue.file
    }
}

/// The whitelist is intentionally narrower than the evaluator. In particular,
/// even structural VirtualCall/Callback edges are not used as authority here.
fn allowed_edge(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    edge: &selector_graph::EdgeRecord,
) -> Result<bool, Error> {
    let source = &graph.nodes[edge.source.index()];
    if source.body.is_none() && source.flags & NODE_EFFECTS_COMPLETE != 0 {
        return Ok(false);
    }
    if edge.operation.is_none() {
        return Ok(matches!(
            edge.kind,
            EdgeKind::Call | EdgeKind::Initialize | EdgeKind::Fixture | EdgeKind::RuntimeBridge
        ));
    }
    let op = facts
        .operations
        .get(edge.operation.index())
        .ok_or(Error::Invalid("retention edge operation"))?;
    if source.body != op.body
        || op.target.is_none()
        || graph.node_for_symbol(op.target) != Some(edge.target)
        || op.flags & (OP_SUPER | OP_QUALIFIED_SUPER | OP_SYNTHETIC_PARAMETER_APPLY) != 0
    {
        return Ok(false);
    }
    Ok(matches!(
        (op.opcode, edge.kind),
        (Opcode::Call, EdgeKind::Call) | (Opcode::Initialize, EdgeKind::Initialize)
    ))
}
fn seal(value: &RetentionPrecheck) -> ContentHash {
    let mut h = Sha256::new();
    h.update(VERSION);
    h.update(value.facts.0);
    h.update(value.graph.0);
    h.update((value.roots.len() as u64).to_le_bytes());
    for row in &value.roots {
        for number in [
            row.root.node.0,
            row.root.receiver.0,
            row.guard.map_or(u32::MAX, |g| g.issue),
            row.guard.map_or(u32::MAX, |g| g.node.0),
            row.path.start,
            row.path.len,
            row.unproved.map_or(0, |r| match r {
                UnprovedReason::MissingRoot => 1,
                UnprovedReason::NoStaticGuardPath => 2,
                UnprovedReason::PathBound => 3,
            }),
        ] {
            h.update(number.to_le_bytes());
        }
    }
    for edge in &value.edges {
        h.update(edge.0.to_le_bytes());
    }
    ContentHash(h.finalize().into())
}

#[cfg(test)]
mod tests;
