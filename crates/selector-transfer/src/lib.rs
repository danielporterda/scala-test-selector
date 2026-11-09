//! Operation semantics, independent of scheduling and summary ownership.
//!
//! One worker owns `Scratch`. Program data and completed summaries are borrowed;
//! writes are compact deltas applied by the owning shard after a batch completes.
use selector_domain::*;
use selector_facts::*;
use selector_graph::*;
use selector_issue::{RuntimeIssueReason, RuntimeIssueSite};
use selector_types::*;
use std::collections::HashMap;
mod bounds;
#[cfg(test)]
mod callback_model_tests;
mod containers;
mod deferred;
mod deferred_receiver;
pub use deferred_receiver::eligible as receiver_dispatch_operation;
#[cfg(test)]
mod deferred_tests;
mod primitive_dispatch;
pub use primitive_dispatch::sites as primitive_long_receiver_sites;

#[derive(Clone, Copy, Debug)]
pub struct SummaryRead {
    pub context: Option<ContextId>,
    pub value: Value,
    pub version: u64,
    pub present: bool,
}
pub trait World: Sync {
    fn values(&self) -> &ValuePool;
    fn summary(
        &self,
        node: NodeId,
        receiver: Value,
        args: &[Value],
        local: &ValuePool,
        scratch: &mut Vec<Value>,
    ) -> SummaryRead;
    fn slot(&self, slot: Slot) -> (Value, u64, bool);
    fn heap_owner(&self, _key: HeapOwnerKey) -> Option<u32> {
        None
    }
    fn capture(&self, binding: u32) -> Option<(Value, &[Value], u64)>;
    fn binding(
        &self,
        site: OperationId,
        receiver: Value,
        args: &[Value],
        local: &ValuePool,
        atoms: &mut Vec<Atom>,
        values: &mut Vec<Value>,
    ) -> Option<u32>;
}
#[derive(Clone, Copy, Debug)]
pub struct CallEffect {
    pub target: NodeId,
    pub receiver: Value,
    pub arguments: IdRange,
    pub operation: OperationId,
    pub kind: EdgeKind,
    pub edge: EdgeId,
    pub summary: Option<ContextId>,
    pub binding: u32,
    /// Execution/proof edges always remain. False only suppresses a dependency
    /// on a return value which the caller does not consume.
    pub observe_return: bool,
}
#[derive(Clone, Copy, Debug)]
pub struct StoreEffect {
    pub slot: Slot,
    pub value: Value,
}
#[derive(Clone, Copy, Debug)]
pub struct CaptureEffect {
    pub site: OperationId,
    pub receiver: Value,
    pub arguments: IdRange,
}
#[derive(Clone, Copy, Debug)]
pub struct ExecutionEdge {
    pub target: NodeId,
    pub operation: OperationId,
    pub kind: EdgeKind,
    pub edge: EdgeId,
    pub receiver: SymbolId,
}
#[derive(Debug, Default)]
pub struct Evaluation {
    pub value: Value,
    pub calls: Vec<CallEffect>,
    pub arguments: Vec<Value>,
    pub stores: Vec<StoreEffect>,
    pub captures: Vec<CaptureEffect>,
    pub reads: Vec<Read>,
    pub edges: Vec<ExecutionEdge>,
    pub issues: Vec<IssueKind>,
    /// First actual issue occurrence in this evaluation; no per-operation log.
    pub first_issue: Option<RuntimeIssueSite>,
    /// At least one operation may have execution or heap effects which this
    /// evaluation did not enumerate. This accumulates independently of the
    /// diagnostic first issue and is never cleared within an evaluation.
    pub effects_open: bool,
    pub operation_visits: u64,
    pub heap_owners: Vec<HeapOwnerKey>,
    pub field_reads: Vec<Slot>,
}
impl Evaluation {
    pub fn clear(&mut self) {
        self.value = Value::EMPTY;
        self.calls.clear();
        self.arguments.clear();
        self.stores.clear();
        self.captures.clear();
        self.reads.clear();
        self.edges.clear();
        self.issues.clear();
        self.first_issue = None;
        self.effects_open = false;
        self.operation_visits = 0;
        self.heap_owners.clear();
        self.field_reads.clear();
    }
}
#[derive(Debug)]
pub struct Scratch {
    pub pool: ValuePool,
    values: Vec<Value>,
    args: Vec<Value>,
    supplied_parameters: Vec<ValueId>,
    lookup: Vec<Value>,
    model_args: Vec<Value>,
    // Native actuals and callback-bound actuals coexist during modeled calls.
    bound_args: Vec<Value>,
    type_work: Vec<SymbolId>,
    linearization: LinearizationScratch,
    dispatch: Vec<ObjectDispatch>,
    receiver_atoms: Vec<Atom>,
    atoms: Vec<Atom>,
    targets: Vec<(NodeId, EdgeId, SymbolId)>,
    operation_edges: OperationEdges,
    heap_owners: HashMap<HeapOwnerKey, u32>,
}
/// Current-body postings only. Both vectors are reused by the owning worker;
/// all entries remain global graph EdgeIds, including duplicate graph records.
#[derive(Debug, Default)]
struct OperationEdges {
    operations: IdRange,
    offsets: Vec<usize>,
    ids: Vec<EdgeId>,
    #[cfg(test)]
    build_edge_visits: usize,
}
impl OperationEdges {
    fn clear(&mut self) {
        self.offsets.clear();
        self.ids.clear();
        self.operations = IdRange::default();
    }
    fn build(
        &mut self,
        graph: &ProgramGraph,
        node: NodeId,
        operations: IdRange,
    ) -> Result<(), Error> {
        self.operations = operations;
        let len = operations.len as usize + 1;
        self.offsets
            .try_reserve(len.saturating_sub(self.offsets.len()))
            .map_err(|_| Error::Limit("operation edge offsets"))?;
        self.offsets.resize(len, 0);
        self.offsets.fill(0);
        #[cfg(test)]
        {
            self.build_edge_visits = 0;
        }
        let start = graph.forward_offsets[node.index()] as usize;
        let end = graph.forward_offsets[node.index() + 1] as usize;
        let source = &graph.forward_edges[start..end];
        let local = |operation: OperationId| {
            operation
                .0
                .checked_sub(operations.start)
                .filter(|i| *i < operations.len)
                .map(|i| i as usize)
        };
        for id in source {
            #[cfg(test)]
            {
                self.build_edge_visits += 1;
            }
            if let Some(i) = local(graph.edges[id.index()].operation) {
                self.offsets[i] += 1;
            }
        }
        let mut total = 0;
        for offset in &mut self.offsets[..operations.len as usize] {
            total += *offset;
            *offset = total;
        }
        self.offsets[operations.len as usize] = total;
        self.ids
            .try_reserve(total.saturating_sub(self.ids.len()))
            .map_err(|_| Error::Limit("operation edge postings"))?;
        self.ids.resize(total, EdgeId::NONE);
        // Decrement end cursors in reverse graph order. The same offsets become
        // final starts, so a third positions vector is unnecessary.
        for id in source.iter().rev() {
            #[cfg(test)]
            {
                self.build_edge_visits += 1;
            }
            if let Some(i) = local(graph.edges[id.index()].operation) {
                self.offsets[i] -= 1;
                self.ids[self.offsets[i]] = *id;
            }
        }
        Ok(())
    }
    fn ids(&self, operation: OperationId) -> &[EdgeId] {
        let Some(i) = operation
            .0
            .checked_sub(self.operations.start)
            .filter(|i| *i < self.operations.len)
            .map(|i| i as usize)
        else {
            return &[];
        };
        &self.ids[self.offsets[i]..self.offsets[i + 1]]
    }
    fn iter<'a>(
        &'a self,
        graph: &'a ProgramGraph,
        operation: OperationId,
    ) -> impl Iterator<Item = (EdgeId, &'a EdgeRecord)> + 'a {
        self.ids(operation)
            .iter()
            .map(|id| (*id, &graph.edges[id.index()]))
    }
    fn owned_bytes(&self) -> usize {
        self.offsets.capacity() * std::mem::size_of::<usize>()
            + self.ids.capacity() * std::mem::size_of::<EdgeId>()
    }
}
impl Scratch {
    pub fn new(max_members: usize) -> Self {
        Self {
            pool: ValuePool::new(max_members),
            values: Vec::new(),
            args: Vec::new(),
            supplied_parameters: Vec::new(),
            lookup: Vec::new(),
            model_args: Vec::new(),
            bound_args: Vec::new(),
            type_work: Vec::new(),
            linearization: LinearizationScratch::default(),
            dispatch: Vec::new(),
            receiver_atoms: Vec::new(),
            atoms: Vec::new(),
            targets: Vec::new(),
            operation_edges: OperationEdges::default(),
            heap_owners: HashMap::new(),
        }
    }
    pub fn clear(&mut self) {
        self.pool.clear();
        self.values.clear();
        self.args.clear();
        self.supplied_parameters.clear();
        self.lookup.clear();
        self.model_args.clear();
        self.bound_args.clear();
        self.type_work.clear();
        self.linearization.clear();
        self.dispatch.clear();
        self.receiver_atoms.clear();
        self.atoms.clear();
        self.targets.clear();
        self.operation_edges.clear();
        self.heap_owners.clear();
    }
    pub fn owned_bytes(&self) -> usize {
        self.pool.owned_bytes()
            + (self.values.capacity()
                + self.args.capacity()
                + self.lookup.capacity()
                + self.model_args.capacity()
                + self.bound_args.capacity())
                * std::mem::size_of::<Value>()
            + (self.atoms.capacity() + self.receiver_atoms.capacity()) * std::mem::size_of::<Atom>()
            + self.type_work.capacity() * 4
            + self.supplied_parameters.capacity() * 4
            + self.linearization.owned_bytes()
            + self.dispatch.capacity() * std::mem::size_of::<ObjectDispatch>()
            + self.targets.capacity() * 16
            + self.operation_edges.owned_bytes()
            + self.heap_owners.capacity() * 24
    }
    fn get(&self, v: ValueId) -> Value {
        if v.is_none() {
            Value::TOP
        } else {
            self.values.get(v.index()).copied().unwrap_or(Value::TOP)
        }
    }
    fn put(&mut self, v: ValueId, value: Value) {
        if !v.is_none() {
            if self.values.len() <= v.index() {
                self.values.resize(v.index() + 1, Value::EMPTY);
            }
            self.values[v.index()] = value;
        }
    }
}
/// Flat direct-parent index. A bounded traversal avoids allocating a type-set for
/// each dispatch; malformed cyclic inheritance is handled by the visit bound.
#[derive(Debug)]
pub struct TypeIndex {
    offsets: Vec<usize>,
    parents: Vec<SymbolId>,
    body_locals: Vec<usize>,
    body_receiver_unused: Vec<bool>,
    ordered: Vec<bool>,
    bounds: bounds::BoundIndex,
    global_modules: Vec<SymbolId>,
    deferred_receivers: Vec<SymbolId>,
    known_receiver_dispatch: Vec<(SymbolId, SymbolId)>,
    primitive_dispatch: Vec<(OperationId, SymbolId)>,
}
#[derive(Clone, Copy, Debug)]
struct LinearizationFrame {
    symbol: SymbolId,
    next: usize,
    start: usize,
}
/// Bounded, worker-owned temporary storage. No hierarchy-sized vector is
/// allocated for every type or every worker.
#[derive(Debug, Default)]
pub struct LinearizationScratch {
    chain: Vec<SymbolId>,
    frames: Vec<LinearizationFrame>,
}
impl LinearizationScratch {
    fn clear(&mut self) {
        self.chain.clear();
        self.frames.clear();
    }
    fn owned_bytes(&self) -> usize {
        self.chain.capacity() * std::mem::size_of::<SymbolId>()
            + self.frames.capacity() * std::mem::size_of::<LinearizationFrame>()
    }
}
#[derive(Clone, Copy, Debug)]
struct ObjectDispatch {
    atom: Atom,
    // NONE retains conservative compatible alternatives. An exact target is
    // selected only by a complete Scala chain or unique most-specific owner.
    target: NodeId,
}
impl TypeIndex {
    pub fn new(facts: &FactSnapshot) -> Self {
        let mut offsets = vec![0; facts.symbols.len() + 1];
        for r in &facts.relations {
            if r.kind == RelationKind::Parent {
                offsets[r.source.index() + 1] += 1;
            }
        }
        for i in 1..offsets.len() {
            offsets[i] += offsets[i - 1];
        }
        let mut positions = offsets[..facts.symbols.len()].to_vec();
        let mut parents = vec![SymbolId::NONE; *offsets.last().unwrap_or(&0)];
        for r in &facts.relations {
            if r.kind == RelationKind::Parent {
                parents[positions[r.source.index()]] = r.target;
                positions[r.source.index()] += 1;
            }
        }
        let mut body_receiver_unused = Vec::with_capacity(facts.bodies.len());
        let body_locals = facts
            .bodies
            .iter()
            .map(|b| {
                let mut max = 0;
                let mut unused = b.flags & (BODY_INITIALIZER | BODY_STATIC_INITIALIZER) == 0;
                for o in &facts.operations[b.operations.range()] {
                    // Include implicit this, escaping/nested captures and all
                    // ordinary operands. Unknown/allocation/initialization
                    // recipes cannot certify a lexical receiver irrelevant.
                    unused &= ![o.a, o.b, o.dest].contains(&ValueId(0))
                        && !matches!(
                            o.opcode,
                            Opcode::Unknown | Opcode::Allocate | Opcode::Initialize
                        )
                        && !(o.a.is_none()
                            && matches!(
                                o.opcode,
                                Opcode::Call
                                    | Opcode::VirtualCall
                                    | Opcode::DefaultArgument
                                    | Opcode::RegisterTest
                                    | Opcode::BindCallback
                            ));
                    for v in [o.a, o.b, o.dest] {
                        if !v.is_none() {
                            max = max.max(v.index());
                        }
                    }
                    for v in &facts.operands[o.arguments.range()] {
                        unused &= *v != ValueId(0);
                        if !v.is_none() {
                            max = max.max(v.index());
                        }
                    }
                }
                for v in &facts.operands[b.parameters.range()] {
                    unused &= *v != ValueId(0);
                    if !v.is_none() {
                        max = max.max(v.index());
                    }
                }
                body_receiver_unused.push(unused);
                max + 1
            })
            .collect();
        let mut ordered: Vec<_> = facts
            .symbols
            .iter()
            .enumerate()
            .map(|(i, s)| {
                s.flags & SYMBOL_SCALA_PARENTS_COMPLETE != 0
                    || matches!(
                        facts.symbol_name(SymbolId(i as u32)),
                        "scala/Any#" | "scala/AnyRef#" | "java/lang/Object#"
                    )
            })
            .collect();
        for issue in &facts.issues {
            if issue.kind == IssueKind::ContextConflict && !issue.symbol.is_none() {
                ordered[issue.symbol.index()] = false;
            }
        }
        let bounds = bounds::BoundIndex::new(facts, &ordered, &offsets, &parents);
        let global_modules = global_module_owners(facts);
        let mut deferred_receivers: Vec<_> = facts
            .relations
            .iter()
            .filter(|row| row.kind == RelationKind::DeferredReceiverDispatch)
            .map(|row| row.source)
            .collect();
        deferred_receivers.sort_unstable();
        deferred_receivers.dedup();
        let mut known_receiver_dispatch: Vec<_> = facts
            .relations
            .iter()
            .filter(|row| row.kind == RelationKind::KnownReceiverDispatch)
            .map(|row| (row.source, row.target))
            .collect();
        known_receiver_dispatch.sort_unstable();
        known_receiver_dispatch.dedup();
        Self {
            offsets,
            parents,
            body_locals,
            body_receiver_unused,
            ordered,
            bounds,
            global_modules,
            deferred_receivers,
            known_receiver_dispatch,
            primitive_dispatch: primitive_dispatch::sites(facts),
        }
    }
    /// Scala L(C) = C, L(last parent) + ... + L(first parent), replacing
    /// duplicate left occurrences with occurrences from the right operand.
    /// Unknown/JVM-only parents, cycles and excessive hierarchy depth return
    /// None; none of those conditions proves an empty parent suffix.
    pub fn linearization<'a>(
        &self,
        child: SymbolId,
        scratch: &'a mut LinearizationScratch,
    ) -> Option<&'a [SymbolId]> {
        const MAX_ITEMS: usize = 4096;
        const MAX_STEPS: usize = 65536;
        scratch.clear();
        if child.is_none() || !self.ordered[child.index()] {
            return None;
        }
        scratch.chain.push(child);
        scratch.frames.push(LinearizationFrame {
            symbol: child,
            next: self.offsets[child.index() + 1],
            start: 0,
        });
        let mut steps = 0;
        while let Some(frame) = scratch.frames.last().copied() {
            steps += 1;
            if steps > MAX_STEPS {
                return None;
            }
            if frame.next > self.offsets[frame.symbol.index()] {
                let parent = self.parents[frame.next - 1];
                scratch.frames.last_mut().unwrap().next -= 1;
                if !self.ordered[parent.index()]
                    || scratch.frames.iter().any(|f| f.symbol == parent)
                    || scratch.chain.len() >= MAX_ITEMS
                    || scratch.frames.len() >= MAX_ITEMS
                {
                    return None;
                }
                let start = scratch.chain.len();
                scratch.chain.push(parent);
                scratch.frames.push(LinearizationFrame {
                    symbol: parent,
                    next: self.offsets[parent.index() + 1],
                    start,
                });
            } else {
                scratch.frames.pop();
                if let Some(parent) = scratch.frames.last() {
                    let end = scratch.chain.len();
                    let mut write = parent.start + 1;
                    for read in parent.start + 1..frame.start {
                        let item = scratch.chain[read];
                        if !scratch.chain[frame.start..end].contains(&item) {
                            scratch.chain[write] = item;
                            write += 1;
                        }
                    }
                    scratch.chain.copy_within(frame.start..end, write);
                    scratch.chain.truncate(write + end - frame.start);
                }
            }
        }
        Some(&scratch.chain)
    }
    pub fn subtype(&self, child: SymbolId, parent: SymbolId, scratch: &mut Vec<SymbolId>) -> bool {
        if child == parent {
            return true;
        }
        if child.is_none() || parent.is_none() {
            return false;
        }
        scratch.clear();
        scratch.push(child);
        let mut at = 0;
        while at < scratch.len() {
            let current = scratch[at];
            at += 1;
            for candidate in
                &self.parents[self.offsets[current.index()]..self.offsets[current.index() + 1]]
            {
                if *candidate == parent {
                    return true;
                }
                if !scratch.contains(candidate) {
                    scratch.push(*candidate);
                }
            }
        }
        false
    }
    /// Exact ordered parent inventory for bounded diagnostic replay capture.
    pub fn direct_parents(&self, symbol: SymbolId) -> Option<&[SymbolId]> {
        let start = *self.offsets.get(symbol.index())?;
        let end = *self.offsets.get(symbol.index().checked_add(1)?)?;
        self.parents.get(start..end)
    }
    /// Complete sparse receiver-frontier inventory for portable replay.
    pub fn deferred_receivers(&self) -> &[SymbolId] {
        &self.deferred_receivers
    }
    /// Exact receiver/contract lookups admitted by the native producer. A
    /// superclass receiver certificate never certifies a descendant lookup.
    pub fn known_receiver_dispatch(&self) -> &[(SymbolId, SymbolId)] {
        &self.known_receiver_dispatch
    }
    /// Exact globally stable Scala module owning this execution symbol. An
    /// instance-owned object, local object or missing owner proof returns None.
    pub fn global_module_owner(&self, symbol: SymbolId) -> Option<SymbolId> {
        self.global_modules
            .get(symbol.index())
            .copied()
            .filter(|s| !s.is_none())
    }
    /// A callback can erase its lexical receiver only when its complete recipe
    /// does not read, pass or capture it. Keep modules, absent recipes, unknown
    /// edges and structural lifecycle effects receiver-specific. This changes
    /// neither ordinary formal arguments nor captured argument values.
    pub fn callback_receiver_unused(&self, graph: &ProgramGraph, symbol: SymbolId) -> bool {
        if self.global_module_owner(symbol).is_some() {
            return false;
        }
        let Some(node) = graph.node_for_symbol(symbol) else {
            return false;
        };
        let body = graph.nodes[node.index()].body;
        !body.is_none()
            && self.body_receiver_unused.get(body.index()).copied() == Some(true)
            && !graph.successors(node).any(|(_, edge)| {
                edge.kind == EdgeKind::Guard
                    || edge.flags & EDGE_UNKNOWN != 0
                    || (edge.kind.is_execution() && edge.operation.is_none())
            })
    }
    pub fn primitive_long_receiver_producer(&self, operation: OperationId) -> Option<SymbolId> {
        self.primitive_dispatch
            .binary_search_by_key(&operation, |(site, _)| *site)
            .ok()
            .map(|at| self.primitive_dispatch[at].1)
    }
    pub fn owned_bytes(&self) -> usize {
        self.offsets.capacity() * std::mem::size_of::<usize>()
            + self.parents.capacity() * 4
            + self.body_locals.capacity() * std::mem::size_of::<usize>()
            + self.body_receiver_unused.capacity()
            + self.ordered.capacity()
            + self.bounds.owned_bytes()
            + self.global_modules.capacity() * std::mem::size_of::<SymbolId>()
            + self.deferred_receivers.capacity() * std::mem::size_of::<SymbolId>()
            + self.known_receiver_dispatch.capacity() * std::mem::size_of::<(SymbolId, SymbolId)>()
            + self.primitive_dispatch.capacity() * std::mem::size_of::<(OperationId, SymbolId)>()
    }
}
fn global_module_owners(facts: &FactSnapshot) -> Vec<SymbolId> {
    if !facts.symbols.iter().any(|s| s.kind == 10) {
        return Vec::new();
    }
    let mut conflicts = vec![false; facts.symbols.len()];
    for issue in &facts.issues {
        if issue.kind == IssueKind::ContextConflict && !issue.symbol.is_none() {
            conflicts[issue.symbol.index()] = true;
        }
    }
    let mut owners = vec![SymbolId::NONE; facts.symbols.len()];
    for (i, symbol) in facts.symbols.iter().enumerate() {
        if symbol.kind != 10 {
            continue;
        }
        let mut current = SymbolId(i as u32);
        let mut stable = false;
        for _ in 0..64 {
            if conflicts[current.index()] {
                break;
            }
            let record = facts.symbols[current.index()];
            let name = facts.symbol_name(current);
            if record.kind != 10
                || !name.ends_with('.')
                || name.starts_with('@')
                || selector_types::symbol::is_local(name)
            {
                break;
            }
            let descriptor_owner = selector_types::symbol::global_owner(name);
            if record.owner.is_none() {
                stable = descriptor_owner.is_none_or(|owner| owner.ends_with('/'));
                break;
            }
            if conflicts[record.owner.index()] {
                break;
            }
            let parent = facts.symbols[record.owner.index()];
            let parent_name = facts.symbol_name(record.owner);
            if descriptor_owner != Some(parent_name) {
                break;
            }
            if parent.kind == 11 || parent_name.ends_with('/') {
                stable = true;
                break;
            }
            if parent.kind != 10 {
                break;
            }
            current = record.owner;
        }
        if stable {
            owners[i] = SymbolId(i as u32);
        }
    }
    for (i, symbol) in facts.symbols.iter().enumerate() {
        if matches!(symbol.kind, 10 | 13 | 14 | 21) || conflicts[i] {
            continue;
        }
        let mut current = symbol.owner;
        for _ in 0..64 {
            if current.is_none() || conflicts[current.index()] {
                break;
            }
            let record = facts.symbols[current.index()];
            if record.kind == 10 {
                owners[i] = owners[current.index()];
                break;
            }
            if matches!(record.kind, 11 | 13 | 14 | 21) {
                break;
            }
            current = record.owner;
        }
    }
    owners
}
fn object_class(facts: &FactSnapshot, symbol: SymbolId) -> SymbolId {
    if symbol.is_none() {
        return symbol;
    }
    let s = facts.symbols[symbol.index()];
    if s.kind == 21 && !s.owner.is_none() {
        s.owner
    } else {
        symbol
    }
}
fn add_issue(
    out: &mut Evaluation,
    issue: IssueKind,
    operation: OperationId,
    reason: RuntimeIssueReason,
) {
    out.effects_open = true;
    record_issue(out, issue, operation, reason);
}
// Only an explicit read-only operation envelope may use this path. The caller
// must establish the field and every receiver alternative, independently of the
// issue reason. A later operation can still open effects in the same evaluation.
fn record_issue(
    out: &mut Evaluation,
    issue: IssueKind,
    operation: OperationId,
    reason: RuntimeIssueReason,
) {
    let site = RuntimeIssueSite {
        kind: issue,
        operation,
        reason,
    };
    debug_assert!(site.validate().is_ok());
    if out.first_issue.is_none() {
        out.first_issue = Some(site);
    }
    if !out.issues.contains(&issue) {
        out.issues.push(issue);
    }
}
fn issue_read(out: &mut Evaluation, slot: Slot, version: u64, present: bool) {
    let read = Read {
        slot,
        version,
        present,
    };
    if !out.reads.iter().any(|r| r.slot == slot) {
        out.reads.push(read);
    }
}
/// Bind a scoped frontier to its actual invocation. Graph-only validation
/// checks IDs and flags; portable replays must also retain this operation's
/// recipe and the receiver/contract endpoints.
pub fn validate_scoped_dispatch_edge(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    edge: &EdgeRecord,
) -> Result<(), Error> {
    if edge.flags & EDGE_DEFERRED_DISPATCH == 0 {
        return Ok(());
    }
    let valid = (|| {
        let node = graph.nodes.get(edge.source.index())?;
        let body = facts.bodies.get(node.body.index())?;
        let op = facts.operations.get(edge.operation.index())?;
        let receiver = facts.symbols.get(edge.receiver.index())?;
        let target = graph.nodes.get(edge.target.index())?;
        let contract = facts.symbols.get(target.symbol.index())?;
        Some(
            edge.kind == EdgeKind::Guard
                && edge.flags == (EDGE_UNKNOWN | EDGE_DEFERRED_DISPATCH)
                && op.body == node.body
                && body.operations.range().contains(&edge.operation.index())
                && matches!(
                    op.opcode,
                    Opcode::Call
                        | Opcode::VirtualCall
                        | Opcode::DefaultArgument
                        | Opcode::RegisterTest
                        | Opcode::InvokeCallback
                )
                && !op.target.is_none()
                && op.flags & (OP_SUPER | OP_QUALIFIED_SUPER) == 0
                && matches!(receiver.kind, 10 | 13)
                && matches!(contract.kind, 0 | 3 | 6),
        )
    })()
    .unwrap_or(false);
    if !valid {
        return Err(Error::Invalid("scoped dispatch frontier invocation"));
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn scoped_dispatch_possible(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    types: &TypeIndex,
    pool: &ValuePool,
    receiver: Value,
    operation: OperationId,
    operation_edges: &OperationEdges,
    work: &mut Vec<SymbolId>,
    linearization: &mut LinearizationScratch,
) -> Result<bool, Error> {
    for (_, edge) in operation_edges.iter(graph, operation) {
        if edge.flags & EDGE_DEFERRED_DISPATCH == 0 {
            continue;
        }
        validate_scoped_dispatch_edge(facts, graph, edge)?;
        if types.unknown_possible(facts, pool, receiver, edge.receiver, work) {
            return Ok(true);
        }
        for atom in pool.members(receiver) {
            if atom.kind == AtomKind::Object
                && (types.subtype(atom.symbol, edge.receiver, work)
                    || !types.exact_ancestry_complete(atom.symbol, linearization))
            {
                return Ok(true);
            }
        }
    }
    Ok(false)
}
fn heap_field<W: World>(
    world: &W,
    s: &mut Scratch,
    out: &mut Evaluation,
    atom: Atom,
    member: SymbolId,
    operations: usize,
) -> Result<Slot, Error> {
    if atom.site.is_none() {
        return Ok(Slot {
            kind: SlotKind::Field,
            owner: object_owner(atom, operations)?,
            member: member.0,
        });
    }
    let Some(root) = binding_root(atom.binding) else {
        return Ok(Slot {
            kind: SlotKind::FieldAll,
            owner: atom.site.0,
            member: member.0,
        });
    };
    let key = HeapOwnerKey {
        site: atom.site,
        root,
    };
    let owner = if let Some(owner) = world.heap_owner(key) {
        owner
    } else if let Some(owner) = s.heap_owners.get(&key) {
        *owner
    } else {
        let index =
            u32::try_from(out.heap_owners.len()).map_err(|_| Error::Limit("local heap owners"))?;
        if index >= LOCAL_HEAP_OWNER - 1 {
            return Err(Error::Limit("local heap owners"));
        }
        let owner = LOCAL_HEAP_OWNER | index;
        s.heap_owners
            .try_reserve(1)
            .map_err(|_| Error::Limit("local heap owner index"))?;
        out.heap_owners
            .try_reserve(1)
            .map_err(|_| Error::Limit("local heap owner rows"))?;
        out.heap_owners.push(key);
        s.heap_owners.insert(key, owner);
        owner
    };
    Ok(Slot {
        kind: SlotKind::Field,
        owner,
        member: member.0,
    })
}

/// Choose independently for each finite receiver. The exact runtime object is
/// retained when entering a parent implementation, so virtual calls inside it
/// still dispatch on the original subclass.
#[allow(clippy::too_many_arguments)]
fn plan_dispatch(
    types: &TypeIndex,
    pool: &ValuePool,
    receiver: Value,
    targets: &[(NodeId, EdgeId, SymbolId)],
    after: Option<SymbolId>,
    unknown_dispatch_complete: bool,
    work: &mut Vec<SymbolId>,
    linearization: &mut LinearizationScratch,
    decisions: &mut Vec<ObjectDispatch>,
) -> bool {
    decisions.clear();
    let mut uncertain = receiver.is_unknown() && !unknown_dispatch_complete;
    for atom in pool.members(receiver) {
        if atom.kind != AtomKind::Object {
            continue;
        }
        let mut selected = NodeId::NONE;
        let mut ambiguous = false;
        if let Some(chain) = types.linearization(atom.symbol, linearization) {
            let start = if let Some(after) = after {
                if let Some(i) = chain.iter().position(|s| *s == after) {
                    i + 1
                } else {
                    uncertain = true;
                    decisions.push(ObjectDispatch {
                        atom: *atom,
                        target: NodeId::NONE,
                    });
                    continue;
                }
            } else {
                0
            };
            for owner in &chain[start..] {
                for (target, _, candidate_owner) in targets {
                    if candidate_owner == owner {
                        if !selected.is_none() && selected != *target {
                            ambiguous = true;
                        }
                        selected = *target;
                    }
                }
                if !selected.is_none() {
                    break;
                }
            }
        } else if after.is_some() {
            // A plain trait super call cannot be narrowed using unordered JVM
            // ancestry. Keep compatible predecessor implementations guarded.
            uncertain = true;
        } else {
            // An ordinary virtual call with a unique most-specific owner can
            // still be resolved without proving relative mixin order.
            for (target, _, owner) in targets {
                if owner.is_none() || !types.subtype(atom.symbol, *owner, work) {
                    continue;
                }
                let shadowed = targets.iter().any(|(_, _, other)| {
                    *other != *owner
                        && !other.is_none()
                        && types.subtype(atom.symbol, *other, work)
                        && types.subtype(*other, *owner, work)
                });
                if !shadowed {
                    if !selected.is_none() && selected != *target {
                        ambiguous = true;
                    }
                    selected = *target;
                }
            }
        }
        if selected.is_none() && after.is_none() {
            for (target, _, owner) in targets {
                if owner.is_none() {
                    if !selected.is_none() && selected != *target {
                        ambiguous = true;
                    }
                    selected = *target;
                }
            }
        }
        uncertain |= ambiguous || selected.is_none();
        decisions.push(ObjectDispatch {
            atom: *atom,
            target: if ambiguous { NodeId::NONE } else { selected },
        });
    }
    uncertain
}

fn compatible_dispatch(
    types: &TypeIndex,
    decision: ObjectDispatch,
    target: NodeId,
    owner: SymbolId,
    targets: &[(NodeId, EdgeId, SymbolId)],
    after: Option<SymbolId>,
    work: &mut Vec<SymbolId>,
) -> bool {
    if !decision.target.is_none() {
        return decision.target == target;
    }
    if owner.is_none() || !types.subtype(decision.atom.symbol, owner, work) {
        return false;
    }
    if let Some(after) = after {
        return !types.subtype(owner, after, work);
    }
    !targets.iter().any(|(_, _, other)| {
        *other != owner
            && !other.is_none()
            && types.subtype(decision.atom.symbol, *other, work)
            && types.subtype(*other, owner, work)
    })
}

fn declaring_type(facts: &FactSnapshot, mut symbol: SymbolId) -> SymbolId {
    // A local method/callback may be nested below its enclosing class method.
    for _ in 0..facts.symbols.len().min(256) {
        if symbol.is_none() {
            break;
        }
        let record = facts.symbols[symbol.index()];
        if matches!(record.kind, 10..=14) {
            return symbol;
        }
        symbol = record.owner;
    }
    SymbolId::NONE
}

#[allow(clippy::too_many_arguments)]
fn emit_call<W: World>(
    world: &W,
    s: &mut Scratch,
    out: &mut Evaluation,
    target: NodeId,
    receiver: Value,
    args: &[Value],
    operation: OperationId,
    kind: EdgeKind,
    edge: EdgeId,
    observe_return: bool,
) -> Result<Value, Error> {
    let found = if observe_return {
        world.summary(target, receiver, args, &s.pool, &mut s.lookup)
    } else {
        SummaryRead {
            context: None,
            value: Value::EMPTY,
            version: 0,
            present: false,
        }
    };
    let start = u32::try_from(out.arguments.len()).map_err(|_| Error::Limit("call arguments"))?;
    out.arguments.extend_from_slice(args);
    out.calls.push(CallEffect {
        target,
        receiver,
        arguments: IdRange {
            start,
            len: args.len() as u32,
        },
        operation,
        kind,
        edge,
        summary: found.context,
        binding: u32::MAX,
        observe_return,
    });
    if let Some(id) = found.context {
        issue_read(
            out,
            Slot {
                kind: SlotKind::Summary,
                owner: id.0,
                member: 0,
            },
            found.version,
            found.present,
        );
    }
    out.edges.push(ExecutionEdge {
        target,
        operation,
        kind,
        edge,
        receiver: SymbolId::NONE,
    });
    s.pool.import(world.values(), found.value)
}

#[allow(clippy::too_many_arguments)]
fn invoke_callable<W: World>(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    types: &TypeIndex,
    world: &W,
    s: &mut Scratch,
    out: &mut Evaluation,
    _node: NodeId,
    operation: OperationId,
    callable: Value,
    args: &[Value],
    observe_return: bool,
) -> Result<Value, Error> {
    // The list is bounded by the value-domain cardinality; copying compact atoms
    // avoids holding a pool borrow across result interning.
    let mut atoms = std::mem::take(&mut s.atoms);
    atoms.clear();
    atoms.extend_from_slice(s.pool.members(callable));
    let mut result = Value::EMPTY;
    for atom in &atoms {
        if atom.kind != AtomKind::Callback {
            continue;
        }
        let Some(target) = graph.node_for_symbol(atom.symbol) else {
            add_issue(
                out,
                IssueKind::UnresolvedSymbol,
                operation,
                RuntimeIssueReason::MissingCallbackTarget,
            );
            continue;
        };
        let mut bound = std::mem::take(&mut s.bound_args);
        bound.clear();
        bound.extend_from_slice(args);
        let recv = if atom.binding & LOCAL_BINDING != 0 {
            let capture = out
                .captures
                .get((atom.binding & !LOCAL_BINDING) as usize)
                .copied()
                .ok_or(Error::Invalid("local capture"))?;
            bound.extend_from_slice(&out.arguments[capture.arguments.range()]);
            capture.receiver
        } else {
            let capture_slot = Slot {
                kind: SlotKind::Capture,
                owner: atom.binding,
                member: 0,
            };
            let (capture_recv, captured, version) =
                if let Some((r, a, v)) = world.capture(atom.binding) {
                    (r, a, v)
                } else {
                    (Value::EMPTY, &[][..], 0)
                };
            issue_read(out, capture_slot, version, version != 0);
            for value in captured {
                bound.push(s.pool.import(world.values(), *value)?);
            }
            s.pool.import(world.values(), capture_recv)?
        };
        let edge = s
            .operation_edges
            .iter(graph, operation)
            .find(|(_, e)| {
                e.kind == EdgeKind::Callback && e.target == target && e.operation == operation
            })
            .map(|(id, _)| id)
            .unwrap_or(EdgeId::NONE);
        let at = out.calls.len();
        let value = emit_call(
            world,
            s,
            out,
            target,
            recv,
            &bound,
            operation,
            EdgeKind::Callback,
            edge,
            observe_return,
        )?;
        out.calls[at].binding = atom.binding;
        result = s.pool.join(result, value)?;
        bound.clear();
        s.bound_args = bound;
    }
    if callable.is_unknown() {
        result = s.pool.join(
            result,
            Value {
                set: SetId(0),
                unknown: UNKNOWN_CALLBACK,
            },
        )?;
        add_issue(
            out,
            IssueKind::UnknownExecution,
            operation,
            RuntimeIssueReason::UnknownCallbackValue,
        );
    }
    // Native function objects use the same ordered Scala dispatch rules as
    // ordinary virtual calls, including inherited FunctionN.apply.
    let mut targets = std::mem::take(&mut s.targets);
    targets.clear();
    let mut deferred_dispatch = false;
    for (edge, candidate) in s.operation_edges.iter(graph, operation) {
        deferred_dispatch |= candidate.flags & EDGE_DEFERRED_DISPATCH != 0;
        if candidate.flags & EDGE_DEFERRED_DISPATCH == 0
            && candidate.operation == operation
            && candidate.kind == EdgeKind::Callback
        {
            targets.push((candidate.target, edge, candidate.receiver));
        }
    }
    let mut dispatch = std::mem::take(&mut s.dispatch);
    if deferred_receiver::possible(
        facts,
        types,
        &s.pool,
        callable,
        operation,
        &mut s.type_work,
        &mut s.linearization,
    ) || (deferred_dispatch
        && facts
            .operations
            .get(operation.index())
            .is_some_and(|op| op.opcode == Opcode::InvokeCallback)
        && scoped_dispatch_possible(
            facts,
            graph,
            types,
            &s.pool,
            callable,
            operation,
            &s.operation_edges,
            &mut s.type_work,
            &mut s.linearization,
        )?)
    {
        result = s.pool.join(result, Value::TOP)?;
        add_issue(
            out,
            IssueKind::UnknownExecution,
            operation,
            RuntimeIssueReason::IncompleteCallbackDispatch,
        );
    }
    if plan_dispatch(
        types,
        &s.pool,
        callable,
        &targets,
        None,
        false,
        &mut s.type_work,
        &mut s.linearization,
        &mut dispatch,
    ) {
        result = s.pool.join(result, Value::TOP)?;
        add_issue(
            out,
            IssueKind::UnknownExecution,
            operation,
            RuntimeIssueReason::IncompleteCallbackDispatch,
        );
    }
    for (target, edge, owner) in &targets {
        s.receiver_atoms.clear();
        let unknown = types.unknown_possible(facts, &s.pool, callable, *owner, &mut s.type_work);
        if unknown {
            for atom in s.pool.members(callable) {
                if atom.kind == AtomKind::UpperBound
                    && types.clause_possible(facts, *atom, *owner, &mut s.type_work)
                {
                    s.receiver_atoms.push(*atom);
                }
            }
        }
        for decision in &dispatch {
            if owner.is_none()
                || compatible_dispatch(
                    types,
                    *decision,
                    *target,
                    *owner,
                    &targets,
                    None,
                    &mut s.type_work,
                )
            {
                s.receiver_atoms.push(decision.atom);
            }
        }
        if !s.receiver_atoms.is_empty() || unknown {
            s.receiver_atoms.sort_unstable();
            let receiver = s.pool.intern(
                &s.receiver_atoms,
                if unknown { callable.unknown } else { 0 },
            )?;
            let value = emit_call(
                world,
                s,
                out,
                *target,
                receiver,
                args,
                operation,
                EdgeKind::Callback,
                *edge,
                observe_return,
            )?;
            result = s.pool.join(result, value)?;
        }
    }
    targets.clear();
    s.targets = targets;
    dispatch.clear();
    s.dispatch = dispatch;
    atoms.clear();
    s.atoms = atoms;
    let _ = facts;
    Ok(result)
}

/// A trusted native primitive-array model keeps its input heap dependency in
/// ReadElements, but primitive elements cannot execute application callbacks.
/// This is data TOP, not element absence or generic-container purity. The
/// planner still sees the read and its potential shared writers.
fn trusted_primitive_read(facts: &FactSnapshot, body: &BodyRecord, op: &OperationRecord) -> bool {
    op.opcode == Opcode::ReadElements
        && op.flags & OP_TRUSTED_PRIMITIVE_READ != 0
        && body.flags & BODY_BINARY_RECIPE != 0
        && facts
            .files
            .get(body.file.index())
            .is_some_and(|file| file.flags & FILE_BINARY_SOURCE != 0)
}

pub fn evaluate<W: World>(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    types: &TypeIndex,
    world: &W,
    node: NodeId,
    receiver: Value,
    args: &[Value],
    s: &mut Scratch,
    out: &mut Evaluation,
) -> Result<(), Error> {
    out.clear();
    s.values.clear();
    s.args.clear();
    s.supplied_parameters.clear();
    s.heap_owners.clear();
    let record = graph.nodes[node.index()];
    let receiver = if !record.body.is_none()
        && facts.bodies[record.body.index()].flags & BODY_STATIC_INITIALIZER != 0
    {
        Value::EMPTY
    } else if let Some(module) = types.global_module_owner(record.symbol) {
        s.pool.singleton(Atom {
            kind: AtomKind::Object,
            site: OperationId::NONE,
            symbol: module,
            binding: 0,
        })?
    } else {
        s.pool.import(world.values(), receiver)?
    };
    s.put(ValueId(0), receiver);
    if record.body.is_none() {
        if graph
            .successors(node)
            .any(|(_, edge)| edge.flags & EDGE_DEFERRED_DISPATCH != 0)
        {
            return Err(Error::Invalid("scoped dispatch frontier without recipe"));
        }
        if record.flags & NODE_EFFECTS_COMPLETE != 0
            && !graph
                .successors(node)
                .any(|(_, e)| e.kind == EdgeKind::Guard || e.flags & EDGE_UNKNOWN != 0)
        {
            out.value = Value::EMPTY;
            return Ok(());
        }
        // Explicit structural/model edges can be evaluated without a source body.
        // An unresolved binary leaf must remain an unknown return value.
        for (edge, e) in graph.successors(node) {
            if e.kind == EdgeKind::Guard || e.flags & EDGE_UNKNOWN != 0 {
                out.value = s.pool.join(out.value, Value::TOP)?;
                add_issue(
                    out,
                    IssueKind::UnknownExecution,
                    e.operation,
                    RuntimeIssueReason::ExecutionGuard,
                );
                continue;
            }
            if e.kind.is_execution() {
                let value = emit_call(
                    world,
                    s,
                    out,
                    e.target,
                    receiver,
                    &[],
                    OperationId::NONE,
                    e.kind,
                    edge,
                    e.kind != EdgeKind::Initialize,
                )?;
                out.value = s.pool.join(out.value, value)?;
            }
        }
        if out.calls.is_empty() && record.flags & NODE_EFFECTS_COMPLETE == 0 {
            out.value = Value::TOP;
            add_issue(
                out,
                IssueKind::UnknownExecution,
                OperationId::NONE,
                RuntimeIssueReason::MissingExecutableBody,
            );
        }
        out.value =
            bounds::constrain_result(facts, types, s, out.value, record.symbol, OperationId::NONE)?;
        return Ok(());
    }
    let body = facts.bodies[record.body.index()];
    let locals = types.body_locals[record.body.index()];
    if locals > 16 * 1024 * 1024 {
        return Err(Error::Limit("body local values"));
    }
    s.operation_edges.build(graph, node, body.operations)?;
    s.values
        .try_reserve(locals)
        .map_err(|_| Error::Limit("local value allocation"))?;
    // Missing actuals are unknown. An actual which is bottom is different:
    // its producer's summary may still be pending, or it may be a known Unit
    // value carrying no object/callback facts. Preserve it until publication.
    for id in &facts.operands[body.parameters.range()] {
        s.put(*id, Value::TOP);
    }
    s.supplied_parameters
        .try_reserve(args.len())
        .map_err(|_| Error::Limit("parameter binding allocation"))?;
    for (i, v) in args.iter().enumerate() {
        let value = s.pool.import(world.values(), *v)?;
        let id = facts.operands[body.parameters.range()]
            .get(i)
            .copied()
            .unwrap_or(ValueId(i as u32 + 1));
        s.put(id, value);
        s.supplied_parameters.push(id);
    }
    s.supplied_parameters.sort_unstable();
    for (ordinal, op) in facts.operations[body.operations.range()].iter().enumerate() {
        let operation = OperationId(body.operations.start + ordinal as u32);
        out.operation_visits += 1;
        match op.opcode {
            Opcode::Parameter => {
                if s.supplied_parameters.binary_search(&op.dest).is_err() {
                    s.put(op.dest, Value::TOP);
                }
                let value = bounds::constrain_result(
                    facts,
                    types,
                    s,
                    s.get(op.dest),
                    op.target,
                    OperationId::NONE,
                )?;
                s.put(op.dest, value);
            }
            Opcode::Constant => s.put(
                op.dest,
                if op.flags & OP_MACRO_RESULT_TYPE != 0 {
                    // Compile-time type evidence is neither a scalar literal
                    // nor proof that a macro produced no runtime value.
                    Value::TOP
                } else {
                    Value::EMPTY
                },
            ),
            Opcode::PackSequence => {
                let value = containers::pack(world, facts, s, out, operation, op)?;
                s.put(op.dest, value);
            }
            Opcode::ReadElements => {
                let value = if trusted_primitive_read(facts, &body, op) {
                    Value::TOP
                } else {
                    containers::read(world, facts, s, out, operation, s.get(op.a))?
                };
                s.put(op.dest, value);
            }
            Opcode::Assign => {
                let v = s.get(op.a);
                s.put(op.dest, v);
            }
            Opcode::Join => {
                let mut v = Value::EMPTY;
                if op.arguments.len > 0 {
                    for id in &facts.operands[op.arguments.range()] {
                        v = s.pool.join(v, s.get(*id))?;
                    }
                } else {
                    v = s.pool.join(s.get(op.a), s.get(op.b))?;
                }
                s.put(op.dest, v);
            }
            Opcode::Allocate => {
                let v = if op.target.is_none() {
                    Value::TOP
                } else {
                    let class = object_class(facts, op.target);
                    if types.global_module_owner(class) == Some(class) {
                        s.pool.singleton(Atom {
                            kind: AtomKind::Object,
                            site: OperationId::NONE,
                            symbol: class,
                            binding: 0,
                        })?
                    } else {
                        let receiver = s.get(ValueId(0));
                        s.atoms.clear();
                        s.atoms.extend_from_slice(s.pool.members(receiver));
                        s.receiver_atoms.clear();
                        for atom in &s.atoms {
                            if atom.kind != AtomKind::Object {
                                continue;
                            }
                            let binding = if atom.binding != 0 {
                                atom.binding
                            } else if atom.site.is_none()
                                && types.global_module_owner(atom.symbol).is_none()
                            {
                                root_binding(atom.symbol)?
                            } else {
                                0
                            };
                            s.receiver_atoms.push(Atom {
                                kind: AtomKind::Object,
                                site: operation,
                                symbol: class,
                                binding,
                            });
                        }
                        if receiver.is_unknown() || s.receiver_atoms.is_empty() {
                            s.receiver_atoms.push(Atom {
                                kind: AtomKind::Object,
                                site: operation,
                                symbol: class,
                                binding: 0,
                            });
                        }
                        s.receiver_atoms.sort_unstable();
                        s.receiver_atoms.dedup();
                        s.pool.intern(&s.receiver_atoms, 0)?
                    }
                };
                s.put(op.dest, v);
                if let Some(target) = graph.node_for_symbol(op.target) {
                    s.args.clear();
                    for id in &facts.operands[op.arguments.range()] {
                        s.args.push(s.get(*id));
                    }
                    let args = std::mem::take(&mut s.args);
                    let edge = s
                        .operation_edges
                        .iter(graph, operation)
                        .find(|(_, e)| e.target == target && e.operation == operation)
                        .map(|(id, _)| id)
                        .unwrap_or(EdgeId::NONE);
                    emit_call(
                        world,
                        s,
                        out,
                        target,
                        v,
                        &args,
                        operation,
                        EdgeKind::Construct,
                        edge,
                        false,
                    )?;
                    s.args = args;
                }
            }
            Opcode::BindCallback => {
                if op.target.is_none() {
                    s.put(op.dest, Value::TOP);
                    add_issue(
                        out,
                        IssueKind::UnknownExecution,
                        operation,
                        RuntimeIssueReason::UnboundCallbackTarget,
                    );
                    continue;
                }
                let start = out.arguments.len() as u32;
                for id in &facts.operands[op.arguments.range()] {
                    out.arguments.push(s.get(*id));
                }
                let receiver = if types.callback_receiver_unused(graph, op.target) {
                    Value::EMPTY
                } else if op.a.is_none() {
                    receiver
                } else {
                    s.get(op.a)
                };
                let binding = world
                    .binding(
                        operation,
                        receiver,
                        &out.arguments[start as usize..],
                        &s.pool,
                        &mut s.atoms,
                        &mut s.lookup,
                    )
                    .unwrap_or(
                        LOCAL_BINDING
                            | u32::try_from(out.captures.len())
                                .map_err(|_| Error::Limit("local captures"))?,
                    );
                let v = s.pool.singleton(Atom {
                    kind: AtomKind::Callback,
                    site: operation,
                    symbol: op.target,
                    binding,
                })?;
                s.put(op.dest, v);
                out.captures.push(CaptureEffect {
                    site: operation,
                    receiver,
                    arguments: IdRange {
                        start,
                        len: op.arguments.len,
                    },
                });
            }
            Opcode::Return => {
                out.value = s.pool.join(out.value, s.get(op.a))?;
            }
            Opcode::StoreField => {
                if op.target.is_none() {
                    out.effects_open = true;
                }
                if op.flags & OP_STATIC_FIELD != 0 {
                    if op.target.is_none() {
                        add_issue(
                            out,
                            IssueKind::UnresolvedSymbol,
                            operation,
                            RuntimeIssueReason::MissingFieldTarget,
                        );
                        continue;
                    }
                    out.stores.push(StoreEffect {
                        slot: Slot {
                            kind: SlotKind::StaticField,
                            owner: op.target.0,
                            member: 0,
                        },
                        value: s.get(op.b),
                    });
                    continue;
                }
                let objects = s.get(op.a);
                let value = s.get(op.b);
                out.effects_open |= objects.is_unknown()
                    || s.pool
                        .members(objects)
                        .iter()
                        .any(|a| a.kind != AtomKind::Object);
                s.atoms.clear();
                s.atoms.extend_from_slice(s.pool.members(objects));
                for i in 0..s.atoms.len() {
                    let atom = s.atoms[i];
                    if atom.kind == AtomKind::Object {
                        let mut slot =
                            heap_field(world, s, out, atom, op.target, facts.operations.len())?;
                        if slot.kind == SlotKind::FieldAll {
                            slot.kind = SlotKind::FieldWildcard;
                        }
                        out.stores.push(StoreEffect { slot, value });
                    }
                }
                let carrier_receiver = s.atoms.iter().any(|atom| atom.kind == AtomKind::Container);
                if carrier_receiver {
                    // A carrier is not a concrete runtime object. Ordinary
                    // field mutation cannot silently disappear on this value.
                    add_issue(
                        out,
                        IssueKind::UnknownExecution,
                        operation,
                        RuntimeIssueReason::UnknownOperation,
                    );
                }
                if objects.is_unknown() || carrier_receiver {
                    out.stores.push(StoreEffect {
                        slot: Slot {
                            kind: SlotKind::Field,
                            owner: u32::MAX,
                            member: op.target.0,
                        },
                        value,
                    });
                }
            }
            Opcode::LoadField => {
                if op.flags & OP_STATIC_FIELD != 0 {
                    if op.target.is_none() {
                        s.put(op.dest, Value::TOP);
                        add_issue(
                            out,
                            IssueKind::UnresolvedSymbol,
                            operation,
                            RuntimeIssueReason::MissingFieldTarget,
                        );
                        continue;
                    }
                    let slot = Slot {
                        kind: SlotKind::StaticField,
                        owner: op.target.0,
                        member: 0,
                    };
                    let (value, version, present) = world.slot(slot);
                    issue_read(out, slot, version, present);
                    let value = s.pool.import(world.values(), value)?;
                    if value.unknown & UNKNOWN_FIELD != 0 {
                        record_issue(
                            out,
                            IssueKind::UnknownExecution,
                            operation,
                            RuntimeIssueReason::UnknownFieldValue,
                        );
                    }
                    let value =
                        bounds::constrain_result(facts, types, s, value, op.target, operation)?;
                    s.put(op.dest, value);
                    continue;
                }
                let objects = s.get(op.a);
                let unidentified = objects.is_unknown()
                    || s.pool
                        .members(objects)
                        .iter()
                        .any(|a| a.kind != AtomKind::Object);
                let exact_read =
                    !op.target.is_none() && !unidentified && !s.pool.members(objects).is_empty();
                // Unknown field identity/receiver is not covered by the narrow
                // data-only envelope, even if a known wildcard store supplies
                // a concrete value and no runtime issue is emitted.
                out.effects_open |= op.target.is_none() || unidentified;
                let mut value = Value::EMPTY;
                s.atoms.clear();
                s.atoms.extend_from_slice(s.pool.members(objects));
                for i in 0..s.atoms.len() {
                    let atom = s.atoms[i];
                    if atom.kind != AtomKind::Object {
                        continue;
                    }
                    let slot = heap_field(world, s, out, atom, op.target, facts.operations.len())?;
                    if !out.field_reads.contains(&slot) {
                        out.field_reads.push(slot);
                    }
                    let (v, version, present) = world.slot(slot);
                    issue_read(out, slot, version, present);
                    let v = s.pool.import(world.values(), v)?;
                    value = s.pool.join(value, v)?;
                    let mut any_present = present;
                    if slot.kind == SlotKind::Field && !atom.site.is_none() {
                        let wildcard = Slot {
                            kind: SlotKind::FieldWildcard,
                            owner: atom.site.0,
                            member: op.target.0,
                        };
                        let (v, version, present) = world.slot(wildcard);
                        issue_read(out, wildcard, version, present);
                        any_present |= present;
                        let v = s.pool.import(world.values(), v)?;
                        value = s.pool.join(value, v)?;
                    }
                    if !any_present {
                        let missing = Slot {
                            kind: SlotKind::FieldMissing,
                            ..slot
                        };
                        let (v, version, present) = world.slot(missing);
                        issue_read(out, missing, version, present);
                        let v = s.pool.import(world.values(), v)?;
                        value = s.pool.join(value, v)?;
                    }
                }
                let slot = Slot {
                    kind: SlotKind::Field,
                    owner: u32::MAX,
                    member: op.target.0,
                };
                let (v, version, present) = world.slot(slot);
                issue_read(out, slot, version, present);
                let v = s.pool.import(world.values(), v)?;
                value = s.pool.join(value, v)?;
                if objects.is_unknown()
                    || s.atoms.iter().any(|atom| atom.kind == AtomKind::Container)
                {
                    value = s.pool.join(
                        value,
                        Value {
                            set: SetId(0),
                            unknown: UNKNOWN_FIELD,
                        },
                    )?;
                }
                if value.unknown & UNKNOWN_FIELD != 0 {
                    // An exact field read is data uncertainty only. Unknown
                    // receivers or carrier/non-object alternatives do not have
                    // that authority, even when this is the first issue.
                    if !exact_read {
                        out.effects_open = true;
                    }
                    record_issue(
                        out,
                        IssueKind::UnknownExecution,
                        operation,
                        RuntimeIssueReason::UnknownFieldValue,
                    );
                }
                let value = bounds::constrain_result(facts, types, s, value, op.target, operation)?;
                s.put(op.dest, value);
            }
            Opcode::Call
            | Opcode::VirtualCall
            | Opcode::Initialize
            | Opcode::DefaultArgument
            | Opcode::RegisterTest => {
                let compiler_private = facts.compiler_private_dispatch(op);
                let primitive = op.opcode == Opcode::VirtualCall
                    && op.arguments.len == 0
                    && !types.primitive_dispatch.is_empty()
                    && facts.symbol_name(op.target) == primitive_dispatch::ANY_TO_STRING
                    && types.primitive_long_receiver_producer(operation).is_some();
                let recv = if primitive {
                    // A joined reference atom is not a runtime inhabitant of
                    // a compiler-proven primitive operand. Keep unknown data
                    // and the platform/boxing boundary, not that atom.
                    Value::TOP
                } else if op.a.is_none() {
                    receiver
                } else {
                    s.get(op.a)
                };
                s.args.clear();
                for id in &facts.operands[op.arguments.range()] {
                    s.args.push(s.get(*id));
                }
                s.targets.clear();
                let mut deferred_dispatch = false;
                for (id, e) in s.operation_edges.iter(graph, operation) {
                    deferred_dispatch |= e.flags & EDGE_DEFERRED_DISPATCH != 0;
                    if e.flags & EDGE_DEFERRED_DISPATCH == 0
                        && e.kind.is_execution()
                        && e.operation == operation
                        && (!compiler_private
                            || !matches!(e.kind, EdgeKind::Call | EdgeKind::VirtualCall)
                            || graph.node_for_symbol(op.target) == Some(e.target))
                        && (e.kind != EdgeKind::VirtualCall
                            || !primitive
                            || primitive_dispatch::possible_virtual_target(
                                facts.symbol_name(graph.nodes[e.target.index()].symbol),
                            ))
                    {
                        s.targets.push((e.target, id, e.receiver));
                    }
                }
                if s.targets.is_empty() {
                    if let Some(target) = graph.node_for_symbol(op.target) {
                        s.targets.push((target, EdgeId::NONE, SymbolId::NONE));
                    }
                }
                let targets = std::mem::take(&mut s.targets);
                let declaring = if op.flags & OP_SUPER != 0 {
                    declaring_type(facts, record.symbol)
                } else {
                    SymbolId::NONE
                };
                let trait_super = op.flags & OP_SUPER != 0
                    && op.flags & OP_QUALIFIED_SUPER == 0
                    && !declaring.is_none()
                    && facts.symbols[declaring.index()].kind == 14;
                let after = trait_super.then_some(declaring);
                let virtual_dispatch = (op.opcode == Opcode::VirtualCall
                    && !compiler_private
                    && op.flags & (OP_SUPER | OP_QUALIFIED_SUPER) == 0)
                    || trait_super;
                let mut dispatch = std::mem::take(&mut s.dispatch);
                let call_args = std::mem::take(&mut s.args);
                let mut result = Value::EMPTY;
                if primitive {
                    // We only ruled out application override candidates; we
                    // did not bind this compiler call to an emitted platform
                    // implementation, or prove that implementation closed.
                    result = Value::TOP;
                    add_issue(
                        out,
                        IssueKind::UnknownExecution,
                        operation,
                        RuntimeIssueReason::IncompleteVirtualDispatch,
                    );
                }
                if !compiler_private
                    && (deferred_receiver::possible(
                        facts,
                        types,
                        &s.pool,
                        recv,
                        operation,
                        &mut s.type_work,
                        &mut s.linearization,
                    ) || (deferred_dispatch
                        && scoped_dispatch_possible(
                            facts,
                            graph,
                            types,
                            &s.pool,
                            recv,
                            operation,
                            &s.operation_edges,
                            &mut s.type_work,
                            &mut s.linearization,
                        )?))
                {
                    result = Value::TOP;
                    add_issue(
                        out,
                        IssueKind::UnknownExecution,
                        operation,
                        RuntimeIssueReason::IncompleteVirtualDispatch,
                    );
                }
                if op.flags & OP_SUPER != 0 && declaring.is_none() {
                    result = Value::TOP;
                    add_issue(
                        out,
                        IssueKind::UnknownExecution,
                        operation,
                        RuntimeIssueReason::UnknownSuperOwner,
                    );
                }
                if virtual_dispatch
                    && plan_dispatch(
                        types,
                        &s.pool,
                        recv,
                        &targets,
                        after,
                        after.is_none()
                            && bounds::final_dispatch_complete(
                                facts,
                                graph,
                                types,
                                &s.pool,
                                recv,
                                operation,
                                &targets,
                                &mut s.type_work,
                                &mut s.linearization,
                            ),
                        &mut s.type_work,
                        &mut s.linearization,
                        &mut dispatch,
                    )
                {
                    result = Value::TOP;
                    add_issue(
                        out,
                        IssueKind::UnknownExecution,
                        operation,
                        RuntimeIssueReason::IncompleteVirtualDispatch,
                    );
                }
                for (target, edge, owner) in targets.iter().copied() {
                    // Explicit class/qualified super stays compiler-bound even
                    // if potential override edges were retained by a producer.
                    if op.flags & (OP_SUPER | OP_QUALIFIED_SUPER) != 0
                        && !trait_super
                        && graph.node_for_symbol(op.target) != Some(target)
                    {
                        continue;
                    }
                    let eligible = after.is_none_or(|after| {
                        !owner.is_none() && !types.subtype(owner, after, &mut s.type_work)
                    });
                    let unknown = eligible
                        && types.unknown_possible(facts, &s.pool, recv, owner, &mut s.type_work);
                    let mut allowed = !virtual_dispatch || owner.is_none() || unknown;
                    s.receiver_atoms.clear();
                    if unknown {
                        for atom in s.pool.members(recv) {
                            if atom.kind == AtomKind::UpperBound
                                && types.clause_possible(facts, *atom, owner, &mut s.type_work)
                            {
                                s.receiver_atoms.push(*atom);
                            }
                        }
                    }
                    for decision in &dispatch {
                        if compatible_dispatch(
                            types,
                            *decision,
                            target,
                            owner,
                            &targets,
                            after,
                            &mut s.type_work,
                        ) {
                            allowed = true;
                            s.receiver_atoms.push(decision.atom);
                        }
                    }
                    if allowed {
                        let recv = if virtual_dispatch && !owner.is_none() {
                            s.receiver_atoms.sort_unstable();
                            s.pool
                                .intern(&s.receiver_atoms, if unknown { recv.unknown } else { 0 })?
                        } else {
                            recv
                        };
                        let kind = if !edge.is_none() {
                            graph.edges[edge.index()].kind
                        } else {
                            match op.opcode {
                                Opcode::VirtualCall if !compiler_private => EdgeKind::VirtualCall,
                                Opcode::Initialize => EdgeKind::Initialize,
                                Opcode::DefaultArgument => EdgeKind::Default,
                                _ => EdgeKind::Call,
                            }
                        };
                        let v = emit_call(
                            world,
                            s,
                            out,
                            target,
                            recv,
                            &call_args,
                            operation,
                            kind,
                            edge,
                            // The callee and its effects remain observable when
                            // a source/native statement discards its return.
                            // Only a real destination needs a summary read and
                            // a wakeup when that return is later published.
                            !op.dest.is_none()
                                && (kind != EdgeKind::Initialize
                                    || op.opcode == Opcode::Initialize),
                        )?;
                        // Class/module initialization is an execution effect,
                        // never an alternative return value of the written call.
                        if kind != EdgeKind::Initialize || op.opcode == Opcode::Initialize {
                            result = s.pool.join(result, v)?;
                        }
                        let flags = if edge.is_none() {
                            0
                        } else {
                            graph.edges[edge.index()].flags
                        };
                        if deferred::possible_future_callback(
                            facts, graph, op.target, target, flags,
                        ) {
                            // This adds possible execution only. The native callee
                            // remains above, and its return abstraction is unchanged.
                            // An unresolved compiler Apply prefix is not an
                            // actual invocation until native arity repair.
                            // Future's exact ABI has Function1 followed by its
                            // ExecutionContext. An unrepaired synthetic prefix
                            // may carry only the first clause and no flag here.
                            let complete = op.flags & OP_SYNTHETIC_PARAMETER_APPLY == 0
                                && call_args.len() == 2;
                            let slot = callback_argument_slot(flags).filter(|&slot| slot == 0);
                            if let Some(slot) = slot.filter(|_| complete) {
                                let callable = call_args[slot];
                                if !callable.is_unknown()
                                    && !s.pool.members(callable).iter().any(|atom| {
                                        matches!(atom.kind, AtomKind::Callback | AtomKind::Object)
                                    })
                                {
                                    add_issue(
                                        out,
                                        IssueKind::UnknownExecution,
                                        operation,
                                        RuntimeIssueReason::UnknownCallbackValue,
                                    );
                                }
                                invoke_callable(
                                    facts,
                                    graph,
                                    types,
                                    world,
                                    s,
                                    out,
                                    node,
                                    operation,
                                    callable,
                                    &[Value::TOP],
                                    false,
                                )?;
                            } else if complete {
                                // No broad argument scan: only an exact slot
                                // certificate can activate this partial policy.
                                add_issue(
                                    out,
                                    IssueKind::UnknownExecution,
                                    operation,
                                    RuntimeIssueReason::UnknownCallbackValue,
                                );
                            }
                            add_issue(
                                out,
                                IssueKind::UnknownExecution,
                                operation,
                                RuntimeIssueReason::IncompleteDeferredCallback,
                            );
                        }
                        if flags & (EDGE_CALLBACK_IMMEDIATE | EDGE_TEST_REGISTRATION) != 0 {
                            let certified_slot = callback_argument_slot(flags);
                            let certified = certified_slot.filter(|&slot| slot < call_args.len());
                            if (certified_slot.is_some() && certified.is_none())
                                || (certified_slot.is_none() && flags & CALLBACK_ARGUMENT_MASK != 0)
                            {
                                // A broken certificate cannot suppress a real
                                // callback or silently certify no invocation.
                                add_issue(
                                    out,
                                    IssueKind::UnknownExecution,
                                    operation,
                                    RuntimeIssueReason::UnknownCallbackValue,
                                );
                            }
                            let callbacks = if let Some(slot) = certified {
                                &call_args[slot..slot + 1]
                            } else {
                                &call_args[..]
                            };
                            for callable in callbacks {
                                if certified.is_some()
                                    && !callable.is_unknown()
                                    && !s.pool.members(*callable).iter().any(|atom| {
                                        matches!(atom.kind, AtomKind::Callback | AtomKind::Object)
                                    })
                                {
                                    add_issue(
                                        out,
                                        IssueKind::UnknownExecution,
                                        operation,
                                        RuntimeIssueReason::UnknownCallbackValue,
                                    );
                                }
                                if certified.is_some()
                                    || s.pool
                                        .members(*callable)
                                        .iter()
                                        .any(|a| a.kind == AtomKind::Callback)
                                    || callable.is_unknown()
                                {
                                    // External collections/providers may supply values
                                    // unavailable to source lowering; unknown arguments
                                    // conservatively bind non-capture callback formals.
                                    let mut callback_args = std::mem::take(&mut s.model_args);
                                    callback_args.clear();
                                    let atom = s
                                        .pool
                                        .members(*callable)
                                        .iter()
                                        .find(|a| a.kind == AtomKind::Callback)
                                        .copied();
                                    if let Some(atom) = atom {
                                        if let Some(callback_node) =
                                            graph.node_for_symbol(atom.symbol)
                                        {
                                            let body = graph.nodes[callback_node.index()].body;
                                            if !body.is_none() {
                                                let b = facts.bodies[body.index()];
                                                let formals = facts.operations
                                                    [b.operations.range()]
                                                .iter()
                                                .filter(|o| {
                                                    o.opcode == Opcode::Parameter
                                                        && o.flags & 1 == 0
                                                })
                                                .count();
                                                callback_args.resize(formals, Value::TOP);
                                            }
                                        }
                                    }
                                    invoke_callable(
                                        facts,
                                        graph,
                                        types,
                                        world,
                                        s,
                                        out,
                                        node,
                                        operation,
                                        *callable,
                                        &callback_args,
                                        !op.dest.is_none(),
                                    )?;
                                    callback_args.clear();
                                    s.model_args = callback_args;
                                }
                            }
                        }
                    }
                }
                if targets.is_empty() {
                    result = Value::TOP;
                    add_issue(
                        out,
                        IssueKind::UnresolvedSymbol,
                        operation,
                        RuntimeIssueReason::MissingCallTarget,
                    );
                }
                s.targets = targets;
                dispatch.clear();
                s.dispatch = dispatch;
                s.args = call_args;
                if op.flags & OP_SEQUENCE_ELEMENT_VIEW != 0
                    && facts.symbol_name(op.target) == "scala/collection/SeqOps#apply()."
                    && op.arguments.len == 1
                    && s.pool
                        .members(recv)
                        .iter()
                        .any(|atom| atom.kind == AtomKind::Container)
                {
                    // An exact admitted ABI grants only a possible value view.
                    // Keep native calls/results/unknown flags above, and retain
                    // a guard because a carrier grants no concrete Seq runtime.
                    let elements = containers::read(world, facts, s, out, operation, recv)?;
                    result = s.pool.join(result, elements)?;
                    add_issue(
                        out,
                        IssueKind::UnknownExecution,
                        operation,
                        RuntimeIssueReason::UnknownOperation,
                    );
                }
                let result =
                    bounds::constrain_result(facts, types, s, result, op.target, operation)?;
                s.put(op.dest, result);
            }
            Opcode::InvokeCallback => {
                let callable = s.get(op.a);
                s.args.clear();
                for id in &facts.operands[op.arguments.range()] {
                    s.args.push(s.get(*id));
                }
                let args = std::mem::take(&mut s.args);
                let result = invoke_callable(
                    facts,
                    graph,
                    types,
                    world,
                    s,
                    out,
                    node,
                    operation,
                    callable,
                    &args,
                    !op.dest.is_none(),
                )?;
                s.args = args;
                s.put(op.dest, result);
            }
            Opcode::Unknown => {
                s.put(op.dest, Value::TOP);
                add_issue(
                    out,
                    IssueKind::UnknownExecution,
                    operation,
                    RuntimeIssueReason::UnknownOperation,
                );
            }
        }
    }
    // Framework/lifecycle edges have no source operation and are unconditional.
    for (edge, e) in graph.successors(node) {
        if e.flags & EDGE_DEFERRED_DISPATCH != 0 {
            validate_scoped_dispatch_edge(facts, graph, e)?;
            continue;
        }
        if e.kind == EdgeKind::Guard || e.flags & EDGE_UNKNOWN != 0 {
            out.value = s.pool.join(out.value, Value::TOP)?;
            add_issue(
                out,
                IssueKind::UnknownExecution,
                e.operation,
                RuntimeIssueReason::ExecutionGuard,
            );
            continue;
        }
        if e.kind.is_execution() && e.operation.is_none() {
            emit_call(
                world,
                s,
                out,
                e.target,
                receiver,
                &[],
                OperationId::NONE,
                e.kind,
                edge,
                // Body-owned lifecycle/model edges have no return destination.
                // Their call, capture and heap effects are still published.
                false,
            )?;
        }
    }
    out.value =
        bounds::constrain_result(facts, types, s, out.value, record.symbol, OperationId::NONE)?;
    Ok(())
}

#[cfg(test)]
mod deferred_dispatch_tests;

#[cfg(test)]
mod tests {
    use super::*;
    fn primitive_read_control(
        native_body: bool,
        native_file: bool,
        flag: bool,
        later: Option<Opcode>,
    ) -> Evaluation {
        struct NoOpaqueCalls(ValuePool);
        impl World for NoOpaqueCalls {
            fn values(&self) -> &ValuePool {
                &self.0
            }
            fn summary(
                &self,
                _: NodeId,
                _: Value,
                _: &[Value],
                _: &ValuePool,
                _: &mut Vec<Value>,
            ) -> SummaryRead {
                panic!("no admitted callees")
            }
            fn slot(&self, _: Slot) -> (Value, u64, bool) {
                panic!("primitive scalar value remains TOP")
            }
            fn capture(&self, _: u32) -> Option<(Value, &[Value], u64)> {
                None
            }
            fn binding(
                &self,
                _: OperationId,
                _: Value,
                _: &[Value],
                _: &ValuePool,
                _: &mut Vec<Atom>,
                _: &mut Vec<Value>,
            ) -> Option<u32> {
                None
            }
        }
        let mut builder = FactBuilder::new();
        let path = builder.intern("java/lang/PrimitiveFixture.class").unwrap();
        builder.facts.files.push(FileRecord {
            path,
            source: StrId::NONE,
            revision: StrId::NONE,
            context: StrId::NONE,
            source_hash: ContentHash([1; 32]),
            flags: if native_file { FILE_BINARY_SOURCE } else { 0 },
        });
        let symbol = builder
            .ensure_symbol("primitive/Fixture#read().", FileId(0))
            .unwrap();
        builder.facts.symbols[symbol.index()].kind = 3;
        builder.facts.symbols[symbol.index()].flags = SYMBOL_NATIVE_BINARY;
        builder.facts.operands.push(ValueId(1));
        let op = |opcode, dest, a, flags| OperationRecord {
            body: BodyId(0),
            opcode,
            target: SymbolId::NONE,
            dest,
            a,
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span::default(),
            flags,
        };
        builder.facts.operations.extend([
            op(Opcode::Parameter, ValueId(1), ValueId::NONE, 0),
            op(
                Opcode::ReadElements,
                ValueId(2),
                ValueId(1),
                if flag { OP_TRUSTED_PRIMITIVE_READ } else { 0 },
            ),
        ]);
        if let Some(opcode) = later {
            builder
                .facts
                .operations
                .push(op(opcode, ValueId(3), ValueId(2), 0));
        }
        builder
            .facts
            .operations
            .push(op(Opcode::Return, ValueId::NONE, ValueId(2), 0));
        builder.facts.bodies.push(BodyRecord {
            symbol,
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange {
                start: 0,
                len: builder.facts.operations.len() as u32,
            },
            parameters: IdRange { start: 0, len: 1 },
            body_hash: ContentHash([2; 32]),
            flags: if native_body { BODY_BINARY_RECIPE } else { 0 },
        });
        let facts = builder.finish().unwrap();
        let mut graph = ProgramGraph::default();
        graph.nodes.push(NodeRecord {
            symbol,
            file: FileId(0),
            body: BodyId(0),
            flags: 0,
        });
        graph.symbol_nodes.push(NodeId(0));
        graph.index().unwrap();
        let types = TypeIndex::new(&facts);
        let world = NoOpaqueCalls(ValuePool::new(16));
        let mut scratch = Scratch::new(16);
        let mut out = Evaluation::default();
        evaluate(
            &facts,
            &graph,
            &types,
            &world,
            NodeId(0),
            Value::EMPTY,
            &[Value::TOP],
            &mut scratch,
            &mut out,
        )
        .unwrap();
        out
    }
    #[test]
    fn trusted_native_primitive_read_keeps_top_data_without_inventing_empty_or_execution() {
        let out = primitive_read_control(true, true, true, None);
        assert_eq!(out.value, Value::TOP);
        assert!(out.issues.is_empty() && !out.effects_open);
        assert!(out.calls.is_empty() && out.stores.is_empty());
    }
    #[test]
    fn primitive_read_flag_cannot_waive_source_generic_or_nonbinary_reads() {
        for (body, file, flag) in [
            (false, true, true),
            (true, false, true),
            (true, true, false),
        ] {
            let out = primitive_read_control(body, file, flag, None);
            assert!(out.value.is_unknown());
            assert!(out.effects_open);
            assert_eq!(
                out.first_issue.unwrap().reason,
                RuntimeIssueReason::UnknownFieldValue
            );
        }
    }
    #[test]
    fn primitive_data_contract_does_not_close_later_callbacks_writes_or_unknown_execution() {
        for later in [Opcode::InvokeCallback, Opcode::StoreField, Opcode::Unknown] {
            let out = primitive_read_control(true, true, true, Some(later));
            assert!(out.effects_open);
            if later == Opcode::StoreField {
                // An unidentified write is retained as a wildcard store and
                // independently opens effects, even without a diagnostic site.
                assert!(out.stores.iter().any(|store| {
                    store.slot.kind == SlotKind::Field
                        && store.slot.owner == u32::MAX
                        && store.slot.member == SymbolId::NONE.0
                        && store.value == Value::TOP
                }));
            } else {
                assert!(!out.issues.is_empty());
                assert_eq!(out.first_issue.unwrap().operation, OperationId(2));
            }
        }
    }
    #[test]
    fn runtime_site_keeps_first_actual_operation_without_dropping_issue_kinds() {
        struct EmptyWorld(ValuePool);
        impl World for EmptyWorld {
            fn values(&self) -> &ValuePool {
                &self.0
            }
            fn summary(
                &self,
                _: NodeId,
                _: Value,
                _: &[Value],
                _: &ValuePool,
                _: &mut Vec<Value>,
            ) -> SummaryRead {
                panic!("no resolved calls")
            }
            fn slot(&self, _: Slot) -> (Value, u64, bool) {
                panic!("no field reads")
            }
            fn capture(&self, _: u32) -> Option<(Value, &[Value], u64)> {
                panic!("no captures")
            }
            fn binding(
                &self,
                _: OperationId,
                _: Value,
                _: &[Value],
                _: &ValuePool,
                _: &mut Vec<Atom>,
                _: &mut Vec<Value>,
            ) -> Option<u32> {
                panic!("no bindings")
            }
        }
        let mut builder = FactBuilder::new();
        let path = builder.intern("p/Owner.class").unwrap();
        builder.facts.files.push(FileRecord {
            path,
            source: StrId::NONE,
            revision: StrId::NONE,
            context: StrId::NONE,
            source_hash: ContentHash::default(),
            flags: FILE_BINARY_SOURCE,
        });
        let symbol = builder.ensure_symbol("p/Owner#run().", FileId(0)).unwrap();
        builder.facts.symbols[symbol.index()].kind = 3;
        builder.facts.symbols[symbol.index()].flags = SYMBOL_NATIVE_BINARY;
        builder.facts.bodies.push(BodyRecord {
            symbol,
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange { start: 0, len: 3 },
            parameters: IdRange::default(),
            body_hash: ContentHash::default(),
            flags: BODY_BINARY_RECIPE,
        });
        for (i, opcode) in [Opcode::Unknown, Opcode::Call, Opcode::Unknown]
            .into_iter()
            .enumerate()
        {
            builder.facts.operations.push(OperationRecord {
                body: BodyId(0),
                opcode,
                target: SymbolId::NONE,
                dest: ValueId(i as u32 + 1),
                a: ValueId::NONE,
                b: ValueId::NONE,
                arguments: IdRange::default(),
                span: Span::default(),
                flags: 0,
            });
        }
        let mut facts = builder.finish().unwrap();
        let mut graph = ProgramGraph::default();
        graph.nodes.push(NodeRecord {
            symbol,
            file: FileId(0),
            body: BodyId(0),
            flags: 0,
        });
        graph.symbol_nodes.push(NodeId(0));
        graph.index().unwrap();
        let types = TypeIndex::new(&facts);
        let world = EmptyWorld(ValuePool::new(16));
        let mut scratch = Scratch::new(16);
        let mut out = Evaluation::default();
        evaluate(
            &facts,
            &graph,
            &types,
            &world,
            NodeId(0),
            Value::EMPTY,
            &[],
            &mut scratch,
            &mut out,
        )
        .unwrap();
        assert_eq!(
            out.issues,
            [IssueKind::UnknownExecution, IssueKind::UnresolvedSymbol]
        );
        assert_eq!(
            out.first_issue,
            Some(RuntimeIssueSite {
                kind: IssueKind::UnknownExecution,
                operation: OperationId(0),
                reason: RuntimeIssueReason::UnknownOperation
            })
        );
        out.clear();
        assert!(out.first_issue.is_none());
        assert!(out.issues.is_empty());
        facts.operations[0].opcode = Opcode::InvokeCallback;
        evaluate(
            &facts,
            &graph,
            &types,
            &world,
            NodeId(0),
            Value::EMPTY,
            &[],
            &mut scratch,
            &mut out,
        )
        .unwrap();
        assert_eq!(
            out.issues,
            [IssueKind::UnknownExecution, IssueKind::UnresolvedSymbol]
        );
        assert_eq!(
            out.first_issue,
            Some(RuntimeIssueSite {
                kind: IssueKind::UnknownExecution,
                operation: OperationId(0),
                reason: RuntimeIssueReason::UnknownCallbackValue
            })
        );
    }
    #[test]
    fn global_modules_require_a_verified_package_or_module_owner_chain() {
        let mut b = FactBuilder::new();
        for name in [
            "p/",
            "p/Global.",
            "p/Global.Nested.",
            "p/Outer#",
            "p/Outer#Inner.",
            "p/Global.worker().",
            "p/Outer#member().",
        ] {
            b.ensure_symbol(name, FileId::NONE).unwrap();
        }
        for (i, (kind, owner)) in [
            (11, SymbolId::NONE),
            (10, SymbolId(0)),
            (10, SymbolId(1)),
            (13, SymbolId(0)),
            (10, SymbolId(3)),
            (3, SymbolId(1)),
            (3, SymbolId(3)),
        ]
        .into_iter()
        .enumerate()
        {
            b.facts.symbols[i].kind = kind;
            b.facts.symbols[i].owner = owner;
        }
        let mut f = b.finish().unwrap();
        let t = TypeIndex::new(&f);
        assert_eq!(t.global_module_owner(SymbolId(1)), Some(SymbolId(1)));
        assert_eq!(t.global_module_owner(SymbolId(2)), Some(SymbolId(2)));
        assert_eq!(t.global_module_owner(SymbolId(5)), Some(SymbolId(1)));
        for id in [0, 3, 4, 6] {
            assert_eq!(t.global_module_owner(SymbolId(id)), None);
        }
        f.issues.push(IssueRecord {
            kind: IssueKind::ContextConflict,
            file: FileId::NONE,
            symbol: SymbolId(1),
            detail: StrId::NONE,
        });
        let t = TypeIndex::new(&f);
        for id in [1, 2, 5] {
            assert_eq!(t.global_module_owner(SymbolId(id)), None);
        }
        f.issues.clear();
        f.symbols[1].kind = 0;
        let t = TypeIndex::new(&f);
        assert_eq!(t.global_module_owner(SymbolId(2)), None);
    }
    #[test]
    fn operation_postings_bound_work_to_two_source_scans_and_exact_edges() {
        const N: u32 = 2048;
        let mut graph = ProgramGraph::default();
        graph.nodes = (0..2)
            .map(|i| NodeRecord {
                symbol: SymbolId(i),
                file: FileId::NONE,
                body: BodyId::NONE,
                flags: 0,
            })
            .collect();
        graph.symbol_nodes = vec![NodeId(0), NodeId(1)];
        let edge = EdgeRecord {
            source: NodeId(0),
            target: NodeId(1),
            kind: EdgeKind::Call,
            operation: OperationId::NONE,
            receiver: SymbolId::NONE,
            occurrence: OccurrenceId::NONE,
            flags: 0,
        };
        for i in (0..N).rev() {
            let e = EdgeRecord {
                operation: OperationId(100 + i),
                ..edge
            };
            graph.edges.extend([e, e]);
        }
        graph.edges.extend([
            edge,
            EdgeRecord {
                operation: OperationId(99),
                ..edge
            },
            EdgeRecord {
                source: NodeId(1),
                operation: OperationId(100),
                ..edge
            },
        ]);
        graph.index().unwrap();
        let mut index = OperationEdges::default();
        let operations = IdRange { start: 100, len: N };
        index.build(&graph, NodeId(0), operations).unwrap();
        assert_eq!(index.build_edge_visits, 2 * (2 * N as usize + 2));
        let mut examined = 0;
        for i in 0..N {
            let ids = index.ids(OperationId(100 + i));
            let first = 2 * (N - 1 - i);
            assert_eq!(
                ids,
                &[EdgeId(first), EdgeId(first + 1)],
                "duplicates retain global edge IDs and source order"
            );
            examined += ids.len();
        }
        assert_eq!(
            examined,
            2 * N as usize,
            "no scan of other operations at lookup"
        );
        assert!(index.ids(OperationId::NONE).is_empty());
        assert!(index.ids(OperationId(99)).is_empty());
        let bytes = index.owned_bytes();
        index.clear();
        index.build(&graph, NodeId(0), operations).unwrap();
        assert_eq!(
            index.owned_bytes(),
            bytes,
            "warm current-body tables reuse capacity"
        );
    }
    fn hierarchy(parents: &[&[u32]]) -> FactSnapshot {
        let mut b = FactBuilder::new();
        for i in 0..parents.len() {
            b.ensure_symbol(&format!("T{i}#"), FileId::NONE).unwrap();
            b.facts.symbols[i].kind = 13;
            b.facts.symbols[i].flags = SYMBOL_SCALA_PARENTS_COMPLETE;
        }
        for (child, parents) in parents.iter().enumerate() {
            for parent in *parents {
                b.facts.relations.push(RelationRecord {
                    source: SymbolId(child as u32),
                    target: SymbolId(*parent),
                    kind: RelationKind::Parent,
                    file: FileId::NONE,
                });
            }
        }
        b.finish().unwrap()
    }
    #[test]
    fn scala_linearization_keeps_shared_base_as_suffix_and_parent_order() {
        let f = hierarchy(&[&[], &[0], &[1], &[1], &[2, 3], &[3, 2]]);
        let t = TypeIndex::new(&f);
        let mut s = LinearizationScratch::default();
        assert_eq!(
            t.linearization(SymbolId(4), &mut s).unwrap(),
            &[
                SymbolId(4),
                SymbolId(3),
                SymbolId(2),
                SymbolId(1),
                SymbolId(0)
            ]
        );
        assert_eq!(
            t.linearization(SymbolId(5), &mut s).unwrap(),
            &[
                SymbolId(5),
                SymbolId(2),
                SymbolId(3),
                SymbolId(1),
                SymbolId(0)
            ]
        );
    }
    #[test]
    fn missing_unordered_conflicting_and_cyclic_parents_never_prove_a_chain() {
        let mut f = hierarchy(&[&[], &[0], &[1]]);
        f.symbols[1].flags = SYMBOL_NATIVE_BINARY;
        assert!(
            TypeIndex::new(&f)
                .linearization(SymbolId(2), &mut LinearizationScratch::default())
                .is_none()
        );
        f.symbols[1].flags = SYMBOL_SCALA_PARENTS_COMPLETE;
        f.issues.push(IssueRecord {
            kind: IssueKind::ContextConflict,
            file: FileId::NONE,
            symbol: SymbolId(0),
            detail: StrId::NONE,
        });
        assert!(
            TypeIndex::new(&f)
                .linearization(SymbolId(2), &mut LinearizationScratch::default())
                .is_none()
        );
        f.issues.clear();
        f.relations.push(RelationRecord {
            source: SymbolId(0),
            target: SymbolId(2),
            kind: RelationKind::Parent,
            file: FileId::NONE,
        });
        assert!(
            TypeIndex::new(&f)
                .linearization(SymbolId(2), &mut LinearizationScratch::default())
                .is_none()
        );
    }
}
