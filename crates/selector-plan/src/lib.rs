//! Change-focused execution roots, with exclusions backed by potential rather
//! than observed dependencies. No solver or selector implementation is linked.
//!
//! Certificates assume admitted facts conservatively describe executable effects
//! and the supplied suite catalogue is the execution universe. Open callbacks,
//! dispatch, missing recipes and input coverage are explicit frontiers. A known
//! field read depends on every potential writer; it need not establish the
//! field's initial value or a must-execute store to prove noninterference.
//! Unidentified heap reads and opaque shared writers remain frontiers. An
//! explicit independent-suite assumption removes only the blanket exposure of
//! other suites' heap readers to a runnable opaque boundary; known dependencies
//! and all uncertainty reachable within a suite remain. A solver
//! result may refute a certificate but cannot establish one. Consuming a planner
//! exclusion for an existing suite requires compatible base/head certificates;
//! the selector separately checks complete, unguarded abstract execution proofs.
use selector_facts::FactSnapshot;
use selector_graph::ProgramGraph;
use selector_types::*;
use sha2::{Digest, Sha256};
pub mod classpath_absence;
pub mod retention;
#[cfg(test)]
mod tests;

pub const VERSION: &str = "selector-potential-plan/7";
pub const ADMITTED_RECIPES: u32 = 1;
pub const DECLARED_ROOT_UNIVERSE: u32 = 2;
pub const POTENTIAL_DEPENDENCIES: u32 = 4;
pub const UNKNOWN_FRONTIERS_RETAINED: u32 = 8;
pub const ASSUMED_SUITE_INDEPENDENCE: u32 = 16;

#[derive(Clone, Copy, Debug)]
pub struct PlanSeeds<'a> {
    pub execution: &'a [NodeId],
    pub declarations: &'a [NodeId],
    pub unscoped: bool,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PlannedRoot {
    pub node: NodeId,
    pub receiver: SymbolId,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Frontier {
    pub node: NodeId,
    pub reasons: u32,
}
pub const UNKNOWN_RECIPE: u32 = 1;
pub const OPEN_DISPATCH: u32 = 2;
pub const OPEN_CALLBACK: u32 = 4;
pub const UNKNOWN_HEAP: u32 = 8;
pub const INPUT_COVERAGE: u32 = 16;
pub const QUERY_GUARD: u32 = 32;
#[derive(Clone, Copy, Debug, Default)]
pub struct PlanMetrics {
    pub roots: usize,
    pub candidates: usize,
    pub excluded: usize,
    pub potential_edges: usize,
    pub unknown_frontiers: usize,
    pub unknown_roots: usize,
    pub heap_roots: usize,
    pub unresolved_roots: usize,
    pub owned_bytes: usize,
}
#[derive(Debug)]
pub struct CandidatePlan {
    pub roots: Vec<PlannedRoot>,
    snapshot: ContentHash,
    facts_identity: ContentHash,
    identity: ContentHash,
    execution: Vec<NodeId>,
    declarations: Vec<NodeId>,
    guards: Vec<NodeId>,
    unscoped: bool,
    suite_semantics: SuiteSemantics,
    excluded: Vec<NodeId>,
    shared_heap_guarded: Vec<NodeId>,
    frontiers: Vec<Frontier>,
    metrics: PlanMetrics,
    potential: Reverse,
}
impl CandidatePlan {
    pub fn snapshot(&self) -> ContentHash {
        self.snapshot
    }
    pub fn facts_identity(&self) -> ContentHash {
        self.facts_identity
    }
    pub fn identity(&self) -> ContentHash {
        self.identity
    }
    pub fn execution_seeds(&self) -> &[NodeId] {
        &self.execution
    }
    pub fn declaration_seeds(&self) -> &[NodeId] {
        &self.declarations
    }
    pub fn guard_nodes(&self) -> &[NodeId] {
        &self.guards
    }
    pub fn unscoped(&self) -> bool {
        self.unscoped
    }
    pub fn suite_semantics(&self) -> SuiteSemantics {
        self.suite_semantics
    }
    pub fn excluded_roots(&self) -> &[NodeId] {
        &self.excluded
    }
    /// Runnable roots exposed to opaque shared-state mutation, independently of
    /// whether a transfer happened to read a currently known slot value.
    pub fn shared_heap_guarded_roots(&self) -> &[NodeId] {
        &self.shared_heap_guarded
    }
    /// Check the sealed planner result before consuming public mutable roots or
    /// its private exclusion/shared-heap certificates. This allocates no buffer.
    pub fn validate_seal(&self) -> Result<(), Error> {
        if content_identity(self) != self.identity {
            return Err(Error::Invalid("planning content seal"));
        }
        Ok(())
    }
    pub fn frontiers(&self) -> &[Frontier] {
        &self.frontiers
    }
    pub fn metrics(&self) -> &PlanMetrics {
        &self.metrics
    }
    pub fn assumptions(&self) -> u32 {
        ADMITTED_RECIPES
            | DECLARED_ROOT_UNIVERSE
            | POTENTIAL_DEPENDENCIES
            | UNKNOWN_FRONTIERS_RETAINED
            | SelectionContract::current(self.suite_semantics).bits()
    }
    pub fn certifies_unaffected(&self, root: NodeId) -> bool {
        self.excluded.binary_search(&root).is_ok()
    }
    pub fn cert_identity(&self, root: NodeId) -> Option<ContentHash> {
        if !self.certifies_unaffected(root) {
            return None;
        }
        let mut hash = Sha256::new();
        hash.update(b"selector-root-exclusion/1");
        hash.update(self.identity.0);
        hash.update(root.0.to_le_bytes());
        Some(ContentHash(hash.finalize().into()))
    }
    /// Potential changed-state readers, independent of observed value deltas.
    /// This is retention authority, never an execution witness. The private
    /// potential index includes native/source field aliases and all writers.
    pub fn potential_changed_heap_read_roots(
        &self,
        facts: &FactSnapshot,
        graph: &ProgramGraph,
    ) -> Result<Vec<NodeId>, Error> {
        self.validate_seal()?;
        if self.snapshot != graph.identity
            || self.facts_identity != facts.identity
            || graph.facts_identity != facts.identity
        {
            return Err(Error::Invalid("planning changed heap snapshot"));
        }
        if self.potential.offsets.len() != graph.nodes.len() + 3 {
            return Err(Error::Invalid("planning changed heap index"));
        }
        let mut flags = vec![0u8; self.potential.offsets.len() - 1];
        let mut pending = Vec::new();
        for &node in self.execution.iter().chain(&self.declarations) {
            if flags[node.index()] == 0 {
                flags[node.index()] = 1;
                pending.push(node);
            }
        }
        // Including compile predecessors conservatively retains declaration
        // changes which can alter a writer/reader's implementation or aliases.
        while let Some(node) = pending.pop() {
            if node.index() < graph.nodes.len() {
                for (_, edge) in graph.predecessors(node) {
                    if flags[edge.source.index()] & 1 == 0 {
                        flags[edge.source.index()] |= 1;
                        pending.push(edge.source);
                    }
                }
            }
            for &source in self.potential.get(node) {
                if flags[source.index()] & 1 == 0 {
                    flags[source.index()] |= 1;
                    pending.push(source);
                }
            }
        }
        let mut readers = Vec::new();
        for (index, node) in graph.nodes.iter().enumerate() {
            if flags[index] & 1 == 0 || node.body.is_none() {
                continue;
            }
            let body = facts
                .bodies
                .get(node.body.index())
                .ok_or(Error::Invalid("planning changed heap body"))?;
            let operations = facts
                .operations
                .get(body.operations.range())
                .ok_or(Error::Invalid("planning changed heap operations"))?;
            if operations
                .iter()
                .any(|op| matches!(op.opcode, Opcode::LoadField | Opcode::ReadElements))
            {
                readers.push(NodeId(index as u32));
            }
        }
        reverse_potential(graph, &self.potential, &mut flags, readers, 2, &mut pending);
        let mut roots = self
            .roots
            .iter()
            .filter(|root| flags[root.node.index()] & 2 != 0)
            .map(|root| root.node)
            .collect::<Vec<_>>();
        roots.sort_unstable();
        roots.dedup();
        Ok(roots)
    }

    /// Positive observations may cancel exclusions, never establish absence.
    /// The compact potential index is reused rather than rebuilding facts.
    pub fn refuted_roots(
        &self,
        facts: &FactSnapshot,
        graph: &ProgramGraph,
        affected: &[NodeId],
        observed_edges: &[(NodeId, NodeId)],
    ) -> Result<Vec<NodeId>, Error> {
        if self.snapshot != graph.identity
            || self.facts_identity != facts.identity
            || graph.facts_identity != facts.identity
        {
            return Err(Error::Invalid("planning refutation snapshot"));
        }
        let n = graph.nodes.len();
        if affected.iter().any(|node| node.index() >= n)
            || observed_edges
                .iter()
                .any(|&(a, b)| a.index() >= n || b.index() >= n)
        {
            return Err(Error::Invalid("planning refutation node"));
        }
        let mut observed = observed_edges.to_vec();
        observed.sort_unstable_by_key(|&(source, target)| (target, source));
        observed.dedup();
        let mut seen = vec![false; self.potential.offsets.len() - 1];
        let mut pending = Vec::new();
        for &node in affected {
            if !seen[node.index()] {
                seen[node.index()] = true;
                pending.push(node);
            }
        }
        while let Some(node) = pending.pop() {
            if node.index() < n {
                for (_, edge) in graph.predecessors(node) {
                    if edge.kind != EdgeKind::Compile && !seen[edge.source.index()] {
                        seen[edge.source.index()] = true;
                        pending.push(edge.source);
                    }
                }
            }
            for &source in self.potential.get(node) {
                if !seen[source.index()] {
                    seen[source.index()] = true;
                    pending.push(source);
                }
            }
            let begin = observed.partition_point(|&(_, target)| target < node);
            let end = observed.partition_point(|&(_, target)| target <= node);
            for &(source, _) in &observed[begin..end] {
                if !seen[source.index()] {
                    seen[source.index()] = true;
                    pending.push(source);
                }
            }
        }
        Ok(self
            .excluded
            .iter()
            .copied()
            .filter(|node| seen[node.index()])
            .collect())
    }
}

pub fn plan(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    seeds: PlanSeeds<'_>,
) -> Result<CandidatePlan, Error> {
    plan_guarded(facts, graph, seeds, &[])
}
pub fn plan_guarded(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    seeds: PlanSeeds<'_>,
    guard_nodes: &[NodeId],
) -> Result<CandidatePlan, Error> {
    plan_guarded_with_semantics(
        facts,
        graph,
        seeds,
        guard_nodes,
        SuiteSemantics::SharedState,
    )
}
/// Plan under an explicit suite-state contract. Independent suites are an
/// analysis assumption, not a claim about processes or classloaders. It removes
/// only hidden cross-suite shared-heap exposure; within-suite uncertainty and
/// known potential dependencies are preserved.
pub fn plan_guarded_with_semantics(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    seeds: PlanSeeds<'_>,
    guard_nodes: &[NodeId],
    suite_semantics: SuiteSemantics,
) -> Result<CandidatePlan, Error> {
    facts.validate()?;
    graph.validate()?;
    if graph.facts_identity != facts.identity || graph.symbol_nodes.len() != facts.symbols.len() {
        return Err(Error::Invalid("planner graph binding"));
    }
    let canonical = |nodes: &[NodeId]| -> Result<Vec<NodeId>, Error> {
        let mut result = nodes.to_vec();
        if result.iter().any(|n| n.index() >= graph.nodes.len()) {
            return Err(Error::Invalid("planner seed node"));
        }
        result.sort_unstable();
        result.dedup();
        Ok(result)
    };
    let mut roots = Vec::with_capacity(facts.suites.len());
    let mut unresolved_roots = 0;
    for suite in &facts.suites {
        if let Some(node) = graph.node_for_symbol(suite.symbol) {
            roots.push(PlannedRoot {
                node,
                receiver: suite.symbol,
            });
        } else {
            unresolved_roots += 1;
        }
    }
    roots.sort_unstable();
    roots.dedup();
    let mut out = CandidatePlan {
        roots,
        snapshot: graph.identity,
        facts_identity: facts.identity,
        identity: ContentHash::default(),
        execution: canonical(seeds.execution)?,
        declarations: canonical(seeds.declarations)?,
        guards: canonical(guard_nodes)?,
        unscoped: seeds.unscoped,
        suite_semantics,
        excluded: Vec::new(),
        shared_heap_guarded: Vec::new(),
        frontiers: Vec::new(),
        metrics: PlanMetrics::default(),
        potential: Reverse {
            offsets: Vec::new(),
            sources: Vec::new(),
        },
    };
    out.metrics.unresolved_roots = unresolved_roots;
    classify(facts, graph, &mut out)?;
    seal(&mut out);
    Ok(out)
}
#[derive(Debug)]
struct Reverse {
    offsets: Vec<usize>,
    sources: Vec<NodeId>,
}
impl Reverse {
    fn new(nodes: usize, pairs: &[(NodeId, NodeId)]) -> Self {
        let mut offsets = vec![0; nodes + 1];
        for &(_, target) in pairs {
            offsets[target.index() + 1] += 1;
        }
        for i in 1..offsets.len() {
            offsets[i] += offsets[i - 1];
        }
        let mut sources = vec![NodeId::NONE; pairs.len()];
        let mut cursor = offsets[..nodes].to_vec();
        for &(source, target) in pairs {
            sources[cursor[target.index()]] = source;
            cursor[target.index()] += 1;
        }
        Self { offsets, sources }
    }
    fn get(&self, target: NodeId) -> &[NodeId] {
        &self.sources[self.offsets[target.index()]..self.offsets[target.index() + 1]]
    }
}

fn reverse_potential(
    graph: &ProgramGraph,
    extra: &Reverse,
    flags: &mut [u8],
    seeds: impl IntoIterator<Item = NodeId>,
    bit: u8,
    scratch: &mut Vec<NodeId>,
) {
    scratch.clear();
    for node in seeds {
        if flags[node.index()] & bit == 0 {
            flags[node.index()] |= bit;
            scratch.push(node);
        }
    }
    while let Some(node) = scratch.pop() {
        if node.index() < graph.nodes.len() {
            for (_, edge) in graph.predecessors(node) {
                if edge.kind != EdgeKind::Compile && flags[edge.source.index()] & bit == 0 {
                    flags[edge.source.index()] |= bit;
                    scratch.push(edge.source);
                }
            }
        }
        for &source in extra.get(node) {
            if flags[source.index()] & bit == 0 {
                flags[source.index()] |= bit;
                scratch.push(source);
            }
        }
    }
}

fn foreign_field(facts: &FactSnapshot, symbol: SymbolId) -> bool {
    let field = facts.symbols[symbol.index()];
    field.kind != 3
        || field.flags & SYMBOL_DEFINED == 0
        || field.flags & SYMBOL_NATIVE_BINARY != 0
        || field.properties & (1024 | 2048) == 0
}
fn declaring_type(facts: &FactSnapshot, mut symbol: SymbolId) -> SymbolId {
    for _ in 0..64 {
        if symbol.is_none() {
            return SymbolId::NONE;
        }
        let record = facts.symbols[symbol.index()];
        if matches!(record.kind, 10 | 13 | 14) {
            return symbol;
        }
        symbol = record.owner;
    }
    SymbolId::NONE
}

/// A deliberately small local value proof. Unknown includes bounded values and
/// lexical `this`: a shared base body need not run with its declaring class as
/// its exact receiver. No observed dispatch alternative establishes exactness.
#[derive(Clone, Copy, PartialEq, Eq)]
enum DispatchReceiver {
    Unknown,
    Empty,
    Callback,
    Exact(SymbolId),
}
impl DispatchReceiver {
    fn join(self, other: Self) -> Self {
        if self == other || other == Self::Empty {
            self
        } else if self == Self::Empty {
            other
        } else {
            Self::Unknown
        }
    }
}

fn receiver_dispatch_operation(facts: &FactSnapshot, op: &selector_facts::OperationRecord) -> bool {
    // Only the native producer's exact Static/Special instruction certificate
    // selects this route. A similarly flagged source or virtual operation has
    // no such authority, and the selected callee's effects remain independent.
    if op.opcode == Opcode::Call
        && op.flags & OP_JVM_NONVIRTUAL != 0
        && facts.bodies.get(op.body.index()).is_some_and(|body| {
            body.flags & BODY_BINARY_RECIPE != 0
                && facts
                    .files
                    .get(body.file.index())
                    .is_some_and(|file| file.flags & FILE_BINARY_SOURCE != 0)
        })
    {
        return false;
    }
    matches!(
        op.opcode,
        Opcode::Call
            | Opcode::VirtualCall
            | Opcode::DefaultArgument
            | Opcode::RegisterTest
            | Opcode::InvokeCallback
    ) && op.flags & (OP_SUPER | OP_QUALIFIED_SUPER) == 0
        && !facts
            .symbols
            .get(op.target.index())
            .is_some_and(|target| target.kind == 21)
}

/// Project sparse receiver-discovery uncertainty at its possible consumers,
/// without making a class initializer opaque or expanding operation×marker
/// edges. The flat ancestry pass and reusable local table are temporary.
fn receiver_dispatch_frontiers(
    facts: &FactSnapshot,
    body_nodes: &[NodeId],
    conflicts: &[bool],
    reasons: &mut [u32],
) {
    if !facts
        .relations
        .iter()
        .any(|row| row.kind == RelationKind::DeferredReceiverDispatch)
    {
        return;
    }
    let mut marked = vec![false; facts.symbols.len()];
    let mut known = Vec::new();
    for row in &facts.relations {
        if row.kind == RelationKind::DeferredReceiverDispatch {
            marked[row.source.index()] = true;
        } else if row.kind == RelationKind::KnownReceiverDispatch {
            known.push((row.source, row.target));
        }
    }
    known.sort_unstable();
    known.dedup();
    let mut offsets = vec![0usize; facts.symbols.len() + 1];
    for row in &facts.relations {
        if row.kind == RelationKind::Parent {
            offsets[row.source.index() + 1] += 1;
        }
    }
    for i in 1..offsets.len() {
        offsets[i] += offsets[i - 1];
    }
    let mut parents = vec![SymbolId::NONE; *offsets.last().unwrap()];
    let mut cursor = offsets[..facts.symbols.len()].to_vec();
    for row in &facts.relations {
        if row.kind == RelationKind::Parent {
            parents[cursor[row.source.index()]] = row.target;
            cursor[row.source.index()] += 1;
        }
    }
    drop(cursor);
    let inventory = |index: usize| {
        let symbol = facts.symbols[index];
        !conflicts[index]
            && (symbol.flags & SYMBOL_SCALA_PARENTS_COMPLETE != 0
                || (matches!(symbol.kind, 13 | 14)
                    && symbol.flags
                        & (SYMBOL_DEFINED
                            | SYMBOL_NATIVE_BINARY
                            | SYMBOL_JVM_CLASS_HEADER_VERIFIED)
                        != 0
                    && symbol.flags & SYMBOL_JVM_PARENTS_COMPLETE != 0)
                || matches!(
                    facts.symbol_name(SymbolId(index as u32)),
                    "scala/Any#" | "scala/AnyRef#" | "java/lang/Object#"
                ))
    };
    // State 2 proves complete transitive ancestry; cycles and missing local
    // inventories become state 3. `marked` accumulates ancestor exposure only
    // where that complete inventory can be proved.
    let mut states = vec![0u8; facts.symbols.len()];
    let mut stack = Vec::<(usize, usize, bool)>::new();
    for root in 0..facts.symbols.len() {
        if states[root] != 0 {
            continue;
        }
        states[root] = 1;
        stack.push((root, offsets[root], inventory(root)));
        while let Some(&(node, next, good)) = stack.last() {
            if !good || next == offsets[node + 1] {
                states[node] = if good { 2 } else { 3 };
                stack.pop();
                continue;
            }
            let parent = parents[next].index();
            if states[parent] == 0 {
                states[parent] = 1;
                stack.push((parent, offsets[parent], inventory(parent)));
            } else {
                let frame = stack.last_mut().unwrap();
                frame.1 += 1;
                frame.2 &= states[parent] == 2;
                marked[node] |= marked[parent];
            }
        }
    }
    let mut locals = Vec::<(ValueId, DispatchReceiver)>::new();
    for (body_id, body) in facts.bodies.iter().enumerate() {
        locals.clear();
        locals.push((ValueId(0), DispatchReceiver::Unknown));
        for op in &facts.operations[body.operations.range()] {
            if !op.dest.is_none() {
                locals.push((op.dest, DispatchReceiver::Unknown));
            }
        }
        locals.sort_unstable_by_key(|row| row.0);
        locals.dedup_by_key(|row| row.0);
        let get = |locals: &[(ValueId, DispatchReceiver)], value| {
            locals
                .binary_search_by_key(&value, |row| row.0)
                .map(|index| locals[index].1)
                .unwrap_or(DispatchReceiver::Unknown)
        };
        for op in &facts.operations[body.operations.range()] {
            if receiver_dispatch_operation(facts, op) {
                // Calls with no explicit receiver use the frame's receiver;
                // InvokeCallback uses its callable operand, never lexical this.
                let receiver = if op.a.is_none() && op.opcode != Opcode::InvokeCallback {
                    DispatchReceiver::Unknown
                } else {
                    get(&locals, op.a)
                };
                let possible = match receiver {
                    DispatchReceiver::Empty | DispatchReceiver::Callback => false,
                    DispatchReceiver::Unknown => true,
                    DispatchReceiver::Exact(class) => {
                        states[class.index()] != 2
                            || (known.binary_search(&(class, op.target)).is_err()
                                && marked[class.index()])
                    }
                };
                if possible {
                    reasons[body_nodes[body_id].index()] |= OPEN_DISPATCH;
                }
            }
            let value = match op.opcode {
                Opcode::Constant if op.flags & OP_MACRO_RESULT_TYPE == 0 => DispatchReceiver::Empty,
                Opcode::BindCallback if !op.target.is_none() => DispatchReceiver::Callback,
                Opcode::Allocate if !op.target.is_none() => {
                    let target = facts.symbols[op.target.index()];
                    DispatchReceiver::Exact(if target.kind == 21 && !target.owner.is_none() {
                        target.owner
                    } else {
                        op.target
                    })
                }
                Opcode::Assign => get(&locals, op.a),
                Opcode::Join => {
                    if op.arguments.len != 0 {
                        facts.operands[op.arguments.range()]
                            .iter()
                            .fold(DispatchReceiver::Empty, |value, &operand| {
                                value.join(get(&locals, operand))
                            })
                    } else {
                        get(&locals, op.a).join(get(&locals, op.b))
                    }
                }
                // Stores and returns do not define their nominal destination.
                Opcode::StoreField | Opcode::Return => continue,
                _ => DispatchReceiver::Unknown,
            };
            if let Ok(index) = locals.binary_search_by_key(&op.dest, |row| row.0) {
                locals[index].1 = value;
            }
        }
    }
}

fn classify(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    out: &mut CandidatePlan,
) -> Result<(), Error> {
    const CHANGED: u8 = 1;
    const OPEN: u8 = 2;
    const HEAP: u8 = 4;
    const OPAQUE: u8 = 8;
    let n = graph.nodes.len();
    let nodes = n.checked_add(2).ok_or(Error::Limit("planning nodes"))?;
    let all_writers = NodeId::checked(n)?;
    let foreign_writers = NodeId::checked(n + 1)?;
    let mut body_nodes = vec![NodeId::NONE; facts.bodies.len()];
    let mut reasons = vec![0u32; n];
    for (i, node) in graph.nodes.iter().enumerate() {
        if node.symbol.index() >= facts.symbols.len()
            || (!node.file.is_none() && node.file.index() >= facts.files.len())
        {
            return Err(Error::Invalid("planning node fact binding"));
        }
        if !node.body.is_none() {
            let body = facts
                .bodies
                .get(node.body.index())
                .ok_or(Error::Invalid("planning node body"))?;
            if body.symbol != node.symbol
                || body.file != node.file
                || !body_nodes[node.body.index()].is_none()
            {
                return Err(Error::Invalid("planning body identity"));
            }
            body_nodes[node.body.index()] = NodeId(i as u32);
            let file = facts.files[body.file.index()];
            if file.flags & (SOURCE_VERIFIED | SYNTAX_VERIFIED) != SOURCE_VERIFIED | SYNTAX_VERIFIED
                && !(file.flags & FILE_BINARY_SOURCE != 0 && body.flags & BODY_BINARY_RECIPE != 0)
            {
                reasons[i] |= INPUT_COVERAGE;
            }
        }
    }
    if body_nodes.iter().any(|n| n.is_none()) {
        return Err(Error::Invalid("planning missing body node"));
    }
    for (i, &node) in graph.symbol_nodes.iter().enumerate() {
        if node.is_none() || graph.nodes[node.index()].symbol != SymbolId(i as u32) {
            return Err(Error::Invalid("planning symbol node"));
        }
    }
    let empty_effects = |target: NodeId| {
        !graph.nodes[target.index()].body.is_none()
            || graph.nodes[target.index()].flags & NODE_EFFECTS_COMPLETE != 0
    };
    let mut contracts = vec![0u8; facts.operations.len()];
    for edge in &graph.edges {
        if edge.flags & EDGE_UNKNOWN != 0 {
            reasons[edge.source.index()] |= UNKNOWN_RECIPE;
        }
        if edge.flags & (EDGE_CALLBACK_IMMEDIATE | EDGE_CALLBACK_DEFERRED | EDGE_TEST_REGISTRATION)
            != 0
        {
            reasons[edge.source.index()] |= OPEN_CALLBACK;
        }
        if edge.kind != EdgeKind::Compile
            && edge.kind != EdgeKind::Field
            && edge.kind != EdgeKind::Guard
            && !empty_effects(edge.target)
            && edge.flags & EDGE_EFFECTS_COMPLETE == 0
        {
            reasons[edge.source.index()] |= UNKNOWN_RECIPE;
        }
        if !edge.operation.is_none() {
            let op = facts
                .operations
                .get(edge.operation.index())
                .ok_or(Error::Invalid("planning edge operation"))?;
            if graph.nodes[edge.source.index()].body != op.body {
                return Err(Error::Invalid("planning operation source"));
            }
            if !op.target.is_none()
                && graph.node_for_symbol(op.target) == Some(edge.target)
                && edge.flags & EDGE_EFFECTS_COMPLETE != 0
            {
                contracts[edge.operation.index()] |= 1;
            }
        }
    }
    let mut extra = Vec::new();
    let mut readers = Vec::new();
    let mut conflicts = vec![false; facts.symbols.len()];
    let mut conflicted_contexts = Vec::new();
    let mut global_conflict = false;
    for issue in &facts.issues {
        if issue.kind == IssueKind::ContextConflict {
            if !issue.symbol.is_none() {
                conflicts[issue.symbol.index()] = true;
            } else if !issue.file.is_none() {
                conflicted_contexts.push(facts.files[issue.file.index()].context);
            } else {
                global_conflict = true;
            }
        }
    }
    for issue in &graph.issues {
        if issue.kind == IssueKind::ContextConflict {
            if !issue.symbol.is_none() {
                if let Some(flag) = conflicts.get_mut(issue.symbol.index()) {
                    *flag = true;
                }
            } else if !issue.file.is_none() {
                let file = facts
                    .files
                    .get(issue.file.index())
                    .ok_or(Error::Invalid("planning issue binding"))?;
                conflicted_contexts.push(file.context);
            } else {
                global_conflict = true;
            }
        }
    }
    conflicted_contexts.sort_unstable();
    conflicted_contexts.dedup();
    for (i, symbol) in facts.symbols.iter().enumerate() {
        conflicts[i] |=
            global_conflict || conflicted_contexts.binary_search(&symbol.context).is_ok();
    }
    receiver_dispatch_frontiers(facts, &body_nodes, &conflicts, &mut reasons);
    for (i, op) in facts.operations.iter().enumerate() {
        let source = body_nodes[op.body.index()];
        if matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
            && op.flags & OP_SUPER != 0
            && op.flags & OP_QUALIFIED_SUPER == 0
        {
            let declaring = declaring_type(facts, facts.bodies[op.body.index()].symbol);
            if declaring.is_none() || facts.symbols[declaring.index()].kind == 14 {
                reasons[source.index()] |= OPEN_DISPATCH;
            }
        }
        match op.opcode {
            // A complete may-effect recipe can discard scalar/operand precision
            // using Assign(NONE)=TOP. Data imprecision is not an execution hole;
            // its call, heap and dispatch consumers below retain their frontiers.
            Opcode::Assign => {}
            Opcode::Unknown => reasons[source.index()] |= UNKNOWN_RECIPE,
            Opcode::InvokeCallback => reasons[source.index()] |= OPEN_CALLBACK,
            Opcode::VirtualCall => {
                let target = facts.symbols.get(op.target.index());
                let closed = target.is_some_and(|target| {
                    !conflicts[op.target.index()]
                        && !target.owner.is_none()
                        && !conflicts[target.owner.index()]
                        && ((target.flags & SYMBOL_DEFINED != 0 && target.properties & 8 != 0)
                            || (facts.symbols[target.owner.index()].flags & SYMBOL_DEFINED != 0
                                && facts.symbols[target.owner.index()].properties & 8 != 0))
                });
                if !closed && op.flags & (OP_SUPER | OP_QUALIFIED_SUPER) == 0 {
                    reasons[source.index()] |= OPEN_DISPATCH;
                }
            }
            Opcode::StoreField | Opcode::PackSequence => {
                extra.push((all_writers, source));
                if op.target.is_none() {
                    reasons[source.index()] |= UNKNOWN_HEAP;
                    if op.opcode == Opcode::StoreField {
                        // An unidentified write has no finite field boundary.
                        // It can mutate a reader's storage even when no call or
                        // callback frontier exists elsewhere in the root.
                        reasons[source.index()] |= UNKNOWN_RECIPE;
                    }
                    extra.push((foreign_writers, source));
                } else {
                    extra.push((graph.symbol_nodes[op.target.index()], source));
                    if foreign_field(facts, op.target) {
                        extra.push((foreign_writers, source));
                    }
                }
            }
            Opcode::LoadField | Opcode::ReadElements => {
                readers.push(source);
                // Value imprecision alone is not an execution hole. With the
                // same external inputs, a known field can change only through
                // one of its potential writers (including dormant/conditional
                // stores and the source/native alias bridge below). Indirect
                // uses of the value retain their own open call/callback guards.
                // Opaque runnable components still expose ALL readers to hidden
                // writes, independently of any known slot value or initializer.
                if op.opcode == Opcode::ReadElements || op.target.is_none() {
                    reasons[source.index()] |= UNKNOWN_HEAP;
                }
                if !op.target.is_none() {
                    extra.push((source, graph.symbol_nodes[op.target.index()]));
                    extra.push((
                        source,
                        if foreign_field(facts, op.target) {
                            all_writers
                        } else {
                            foreign_writers
                        },
                    ));
                }
            }
            _ => {}
        }
        if matches!(
            op.opcode,
            Opcode::Call
                | Opcode::VirtualCall
                | Opcode::Allocate
                | Opcode::Initialize
                | Opcode::DefaultArgument
                | Opcode::RegisterTest
                | Opcode::BindCallback
        ) {
            if op.target.is_none() {
                reasons[source.index()] |=
                    if matches!(op.opcode, Opcode::BindCallback | Opcode::RegisterTest) {
                        OPEN_CALLBACK
                    } else {
                        UNKNOWN_RECIPE
                    };
            } else {
                let target = graph.symbol_nodes[op.target.index()];
                extra.push((source, target));
                if !empty_effects(target) && contracts[i] == 0 {
                    reasons[source.index()] |= UNKNOWN_RECIPE;
                }
            }
        }
    }
    for root in &out.roots {
        if !empty_effects(root.node)
            || (!graph.nodes[root.node.index()].body.is_none()
                && facts.bodies[graph.nodes[root.node.index()].body.index()]
                    .parameters
                    .len
                    != 0)
        {
            reasons[root.node.index()] |= UNKNOWN_RECIPE;
        }
    }
    for &guard in &out.guards {
        reasons[guard.index()] |= QUERY_GUARD;
    }
    let mut global = out.unscoped
        || facts.identity == ContentHash::default()
        || graph.identity == ContentHash::default();
    // File-only diagnostics are expanded once over compact source postings.
    let mut uncertain_files = vec![false; facts.files.len()];
    let mut scope = |kind: IssueKind, node: NodeId, file: FileId, symbol: SymbolId| {
        if matches!(
            kind,
            IssueKind::InvalidInput
                | IssueKind::ResourceLimit
                | IssueKind::UnsupportedSchema
                | IssueKind::StaleSource
        ) {
            global = true;
        } else if !node.is_none() {
            reasons[node.index()] |= INPUT_COVERAGE;
        } else if !symbol.is_none() {
            reasons[graph.symbol_nodes[symbol.index()].index()] |= INPUT_COVERAGE;
        } else if !file.is_none() {
            uncertain_files[file.index()] = true;
        } else {
            global = true;
        }
    };
    for issue in &graph.issues {
        if (!issue.node.is_none() && issue.node.index() >= n)
            || (!issue.file.is_none() && issue.file.index() >= facts.files.len())
            || (!issue.symbol.is_none() && issue.symbol.index() >= facts.symbols.len())
        {
            return Err(Error::Invalid("planning issue binding"));
        }
        scope(issue.kind, issue.node, issue.file, issue.symbol);
    }
    for issue in &facts.issues {
        if issue.kind.is_execution_boundary() {
            scope(issue.kind, NodeId::NONE, issue.file, issue.symbol);
        }
    }
    let mut mapped_files = vec![false; facts.files.len()];
    for (i, node) in graph.nodes.iter().enumerate() {
        if !node.file.is_none() && uncertain_files[node.file.index()] {
            reasons[i] |= INPUT_COVERAGE;
            mapped_files[node.file.index()] = true;
        }
    }
    if uncertain_files
        .iter()
        .zip(&mapped_files)
        .any(|(&uncertain, &mapped)| uncertain && !mapped)
    {
        global = true;
    }
    extra.sort_unstable();
    extra.dedup();
    let potential_edges = graph
        .edges
        .iter()
        .filter(|e| e.kind != EdgeKind::Compile)
        .count()
        + extra.len();
    let reverse = Reverse::new(nodes, &extra);
    drop(extra);
    let mut flags = vec![0u8; nodes];
    let mut scratch = Vec::new();
    // Compilation dependencies influence declarations but never make dormant
    // declarations executable or attach their unknown effects to a live root.
    let mut compile = vec![false; n];
    for &seed in &out.declarations {
        if !compile[seed.index()] {
            compile[seed.index()] = true;
            scratch.push(seed);
        }
    }
    while let Some(node) = scratch.pop() {
        for (_, edge) in graph.predecessors(node) {
            if edge.kind == EdgeKind::Compile && !compile[edge.source.index()] {
                compile[edge.source.index()] = true;
                scratch.push(edge.source);
            }
        }
    }
    reverse_potential(
        graph,
        &reverse,
        &mut flags,
        out.execution.iter().copied().chain(
            compile
                .iter()
                .enumerate()
                .filter_map(|(i, &hit)| hit.then_some(NodeId(i as u32))),
        ),
        CHANGED,
        &mut scratch,
    );
    reverse_potential(
        graph,
        &reverse,
        &mut flags,
        reasons
            .iter()
            .enumerate()
            .filter_map(|(i, &reason)| (reason != 0).then_some(NodeId(i as u32))),
        OPEN,
        &mut scratch,
    );
    let unknown_roots = out
        .roots
        .iter()
        .filter(|r| flags[r.node.index()] & OPEN != 0)
        .count()
        + out.metrics.unresolved_roots;
    reverse_potential(
        graph,
        &reverse,
        &mut flags,
        reasons
            .iter()
            .enumerate()
            .filter_map(|(i, &reason)| (reason & !UNKNOWN_HEAP != 0).then_some(NodeId(i as u32))),
        OPAQUE,
        &mut scratch,
    );
    let opaque_roots = out
        .roots
        .iter()
        .filter(|root| flags[root.node.index()] & OPAQUE != 0)
        .count()
        + out.metrics.unresolved_roots;
    if opaque_roots != 0 && out.suite_semantics == SuiteSemantics::SharedState {
        // An opaque runnable boundary can invoke changed code and mutate shared
        // state without a compiler-visible field ID. Keep every potential heap
        // reader; a closed pure component still has a valid disjoint proof.
        reverse_potential(
            graph,
            &reverse,
            &mut flags,
            readers.iter().copied(),
            HEAP,
            &mut scratch,
        );
    }
    out.shared_heap_guarded.extend(
        out.roots
            .iter()
            .filter(|r| flags[r.node.index()] & HEAP != 0)
            .map(|root| root.node),
    );
    out.shared_heap_guarded.sort_unstable();
    out.shared_heap_guarded.dedup();
    let heap_roots = out.shared_heap_guarded.len();
    let total = out.roots.len();
    out.roots.retain(|root| {
        let keep = global || flags[root.node.index()] & (CHANGED | OPEN | HEAP) != 0;
        if !keep {
            out.excluded.push(root.node);
        }
        keep
    });
    out.excluded.sort_unstable();
    out.excluded.dedup();
    out.frontiers = reasons
        .into_iter()
        .enumerate()
        .filter_map(|(i, reasons)| {
            (reasons != 0).then_some(Frontier {
                node: NodeId(i as u32),
                reasons,
            })
        })
        .collect();
    if global {
        out.frontiers.push(Frontier {
            node: NodeId::NONE,
            reasons: INPUT_COVERAGE,
        });
    }
    if out.metrics.unresolved_roots != 0 {
        out.frontiers.push(Frontier {
            node: NodeId::NONE,
            reasons: INPUT_COVERAGE,
        });
    }
    out.metrics = PlanMetrics {
        roots: total,
        candidates: out.roots.len(),
        excluded: out.excluded.len(),
        potential_edges,
        unknown_frontiers: out.frontiers.len(),
        unknown_roots,
        heap_roots,
        unresolved_roots: out.metrics.unresolved_roots,
        owned_bytes: out.roots.capacity() * std::mem::size_of::<PlannedRoot>()
            + out.excluded.capacity() * 4
            + out.shared_heap_guarded.capacity() * 4
            + out.frontiers.capacity() * std::mem::size_of::<Frontier>()
            + (out.execution.capacity() + out.declarations.capacity() + out.guards.capacity()) * 4
            + reverse.offsets.capacity() * std::mem::size_of::<usize>()
            + reverse.sources.capacity() * 4,
    };
    out.potential = reverse;
    Ok(())
}
fn seal(out: &mut CandidatePlan) {
    out.identity = content_identity(out);
}
fn content_identity(out: &CandidatePlan) -> ContentHash {
    let mut hash = Sha256::new();
    hash.update(VERSION.as_bytes());
    hash.update(SelectionContract::VERSION.as_bytes());
    hash.update(out.snapshot.0);
    hash.update(out.facts_identity.0);
    hash.update(out.assumptions().to_le_bytes());
    hash.update([u8::from(out.unscoped)]);
    for nodes in [
        &out.execution,
        &out.declarations,
        &out.guards,
        &out.excluded,
        &out.shared_heap_guarded,
    ] {
        hash.update((nodes.len() as u64).to_le_bytes());
        for n in nodes {
            hash.update(n.0.to_le_bytes());
        }
    }
    hash.update((out.roots.len() as u64).to_le_bytes());
    for root in &out.roots {
        hash.update(root.node.0.to_le_bytes());
        hash.update(root.receiver.0.to_le_bytes());
    }
    hash.update((out.frontiers.len() as u64).to_le_bytes());
    for frontier in &out.frontiers {
        hash.update(frontier.node.0.to_le_bytes());
        hash.update(frontier.reasons.to_le_bytes());
    }
    ContentHash(hash.finalize().into())
}
