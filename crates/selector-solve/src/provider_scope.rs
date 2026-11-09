//! Replay a proven provider boundary without changing the shared graph.
//!
//! This interface only reports diagnostics. The caller must supply files that
//! are positively absent from every selected root's owning runtime scope.
//! A suppressed call remains an open effect, not an unaffectedness proof.
use super::*;

pub(crate) struct ProviderScope {
    blocked: Vec<NodeId>,
    blocked_calls: u64,
    blocked_callbacks: u64,
    first: Option<BlockedCall>,
}

#[derive(Clone, Copy, Debug)]
pub struct BlockedCall {
    pub source: NodeId,
    pub target: NodeId,
    pub operation: OperationId,
    pub kind: EdgeKind,
}

impl ProviderScope {
    fn new(graph: &ProgramGraph, absent: &[FileId]) -> Result<Self, Error> {
        let candidates = graph
            .nodes
            .iter()
            .enumerate()
            .filter(|(_, node)| absent.binary_search(&node.file).is_ok())
            .map(|(i, _)| NodeId(i as u32));
        let mut blocked = Vec::new();
        blocked
            .try_reserve_exact(candidates.clone().count())
            .map_err(|_| Error::Limit("provider scope node mask"))?;
        blocked.extend(candidates);
        Ok(Self {
            blocked,
            blocked_calls: 0,
            blocked_callbacks: 0,
            first: None,
        })
    }

    pub(crate) fn blocks(&self, node: NodeId) -> bool {
        self.blocked.binary_search(&node).is_ok()
    }

    pub(crate) fn owned_bytes(&self) -> usize {
        self.blocked.capacity() * std::mem::size_of::<NodeId>()
    }

    pub(crate) fn block(&mut self, source: NodeId, call: &CallEffect) -> bool {
        if !self.blocks(call.target) {
            return false;
        }
        self.blocked_calls = self.blocked_calls.saturating_add(1);
        if call.kind == EdgeKind::Callback {
            self.blocked_callbacks = self.blocked_callbacks.saturating_add(1);
        }
        self.first.get_or_insert(BlockedCall {
            source,
            target: call.target,
            operation: call.operation,
            kind: call.kind,
        });
        true
    }
}

#[derive(Debug)]
pub struct Diagnostic {
    pub graph: ContentHash,
    pub completion: Completion,
    pub stop: Option<StopReason>,
    pub root_impacts: Vec<AnalyzedRoot>,
    pub guarded_roots: Vec<NodeId>,
    pub unscoped_uncertainty: bool,
    pub blocked_nodes: usize,
    /// Suppressed call attempts, including repeated evaluations.
    pub blocked_calls: u64,
    pub blocked_callbacks: u64,
    pub first_blocked_call: Option<BlockedCall>,
    pub counters: WorkCounters,
}

/// Run a separate, fresh analysis session over the same facts and graph.
/// IDs in `absent_files` must be sorted and belong to this exact snapshot.
/// Unattributed graph nodes are never filtered. No checkpoint, cache or
/// selection result from this counterfactual session can escape this API.
pub fn diagnose(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    options: &SolveOptions,
    roots: Arc<[ExecutionRoot]>,
    absent_files: &[FileId],
    seeds: &[NodeId],
) -> Result<Diagnostic, Error> {
    if roots.is_empty()
        || absent_files.windows(2).any(|x| x[0] >= x[1])
        || absent_files.iter().any(|f| f.index() >= facts.files.len())
    {
        return Err(Error::Invalid("diagnostic provider scope"));
    }
    let mut options = options.clone();
    options.execution_roots = Some(roots.clone());
    options.retain_context_evidence = false;
    let mut session = QuerySession::new(facts, graph, &options)?;
    let scope = ProviderScope::new(graph, absent_files)?;
    if session.owned_bytes().saturating_add(scope.owned_bytes()) > options.memory_budget_bytes {
        return Err(Error::Limit("provider scope memory"));
    }
    if roots.iter().any(|r| scope.blocks(r.node)) {
        return Err(Error::Invalid("diagnostic scope blocks root"));
    }
    session.provider_scope = Some(scope);
    let result = session.analyze(seeds)?;
    let scope = session.provider_scope.as_ref().expect("scope retained");
    Ok(Diagnostic {
        graph: result.snapshot,
        completion: result.completion,
        stop: session.stop_reason(),
        root_impacts: result.root_impacts().unwrap_or_default().to_vec(),
        guarded_roots: result.guarded_roots,
        unscoped_uncertainty: result.unscoped_uncertainty,
        blocked_nodes: scope.blocked.len(),
        blocked_calls: scope.blocked_calls,
        blocked_callbacks: scope.blocked_callbacks,
        first_blocked_call: scope.first,
        counters: session.work_counters(),
    })
}
