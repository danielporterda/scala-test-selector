//! Bounded static callable instantiation. Frame/payload IDs are analysis
//! provenance, never runtime object or isolation identities.
use super::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) struct SymbolicEdge {
    pub root: u32,
    pub caller: MethodId,
    pub call: u32,
    pub target: MethodId,
}
pub(crate) struct Resolution {
    pub edges: Vec<SymbolicEdge>,
    pub top: Vec<TopMask>,
}
impl Resolution {
    pub fn targets(&self, root: u32, caller: MethodId, call: u32) -> &[SymbolicEdge] {
        let key = (root, caller, call);
        let start = self
            .edges
            .partition_point(|e| (e.root, e.caller, e.call) < key);
        let end = self
            .edges
            .partition_point(|e| (e.root, e.caller, e.call) <= key);
        &self.edges[start..end]
    }
}
#[derive(Clone, Copy)]
struct FrameRow {
    root: u32,
    method: MethodId,
    start: u32,
    ret: CellId,
    payloads: Range,
}
#[derive(Clone, Copy)]
struct Payload {
    template: u32,
    owner: u32,
    /// A bridge receives this exact original closure, not the union of values
    /// at an invocation site and not its creator's lexical receiver.
    singleton: CellId,
    receiver: CellValue,
    captures: Range,
}
#[derive(Clone, Copy)]
struct Lookup {
    root: u32,
    method: u32,
    frame: u32,
}
#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
struct HeapKey {
    kind: StorageKind,
    member: u32,
}
#[derive(Clone, Copy)]
struct HeapRow {
    key: HeapKey,
    cell: CellId,
}

struct Engine<'a> {
    world: World<'a>,
    bank: CallableCells,
    frames: Vec<FrameRow>,
    lookup: Vec<Lookup>,
    payloads: Vec<Payload>,
    capture_values: Vec<CellValue>,
    heap: Vec<HeapRow>,
    wildcard: CellId,
    all_stores: CellId,
    scratch: Vec<u32>,
    definition_offsets: Vec<u32>,
    defined: Vec<bool>,
    returns: Vec<bool>,
}
fn cell_value(frame: FrameRow, row: MethodRow, value: ValueRef) -> Result<CellValue, Error> {
    let slot = match value.kind {
        ValueKind::Unknown => return Ok(CellValue::Unknown),
        ValueKind::Constant => return Ok(CellValue::NonCallable),
        ValueKind::Receiver => 0,
        ValueKind::Argument => 1 + value.index,
        ValueKind::Capture => 1 + row.arity + value.index,
        ValueKind::Local => 1 + row.arity + row.captures + value.index,
    };
    Ok(CellValue::Cell(CellId(
        frame.start.checked_add(slot).ok_or(Error::Overflow)?,
    )))
}
fn local(frame: FrameRow, row: MethodRow, index: u32) -> CellId {
    CellId(frame.start + 1 + row.arity + row.captures + index)
}
fn hash(root: u32, method: u32) -> usize {
    let mut x = ((root as u64) << 32) | method as u64;
    x ^= x >> 30;
    x = x.wrapping_mul(0xbf58476d1ce4e5b9);
    x ^= x >> 27;
    x = x.wrapping_mul(0x94d049bb133111eb);
    (x ^ (x >> 31)) as usize
}
impl<'a> Engine<'a> {
    fn new(world: World<'a>, budget: &mut Budget) -> Result<Self, Error> {
        let limits = budget.limits;
        let lookup_len = limits
            .max_callable_frames
            .checked_mul(2)
            .and_then(|n| n.max(4).checked_next_power_of_two())
            .ok_or(Error::Overflow)?;
        let lookup = budget.filled(
            lookup_len,
            Lookup {
                root: NONE,
                method: NONE,
                frame: NONE,
            },
        )?;
        let d = world.capsules.data();
        let mut definition_offsets = budget.filled(d.methods.len() + 1, 0u32)?;
        for (i, m) in d.methods.iter().enumerate() {
            definition_offsets[i + 1] = definition_offsets[i]
                .checked_add(m.locals)
                .ok_or(Error::Overflow)?;
        }
        if definition_offsets[d.methods.len()] as usize > budget.limits.max_origin_slots {
            return Err(Error::Budget);
        }
        let mut defined = budget.filled(definition_offsets[d.methods.len()] as usize, false)?;
        let mut returns = budget.filled(d.methods.len(), false)?;
        for (i, m) in d.methods.iter().enumerate() {
            if m.top.contains(Channel::Flows) {
                continue;
            }
            let start = definition_offsets[i] as usize;
            for ci in m.creations.checked(d.creations.len())? {
                defined[start + d.creations[ci].destination as usize] = true;
            }
            for ci in m.calls.checked(d.calls.len())? {
                if d.calls[ci].result != NONE {
                    defined[start + d.calls[ci].result as usize] = true;
                }
            }
            for vi in m.value_flows.checked(d.value_flows.len())? {
                let f = d.value_flows[vi];
                match f.kind {
                    ValueFlowKind::Copy => defined[start + f.index as usize] = true,
                    ValueFlowKind::Load => defined[start + f.value.index as usize] = true,
                    ValueFlowKind::Return => returns[i] = true,
                    ValueFlowKind::Store => (),
                }
            }
        }
        let mut bank = CallableCells::default();
        bank.reserve(
            limits.max_callable_cells,
            limits.max_callable_members,
            limits.max_callable_targets,
            budget.limits.max_bytes.saturating_sub(budget.bytes),
        )?;
        budget.bytes = budget
            .bytes
            .checked_add(bank.owned_bytes())
            .ok_or(Error::Overflow)?;
        if budget.bytes > budget.limits.max_bytes {
            return Err(Error::Budget);
        }
        let wildcard = bank.push_seed(CellSeed::Unknown)?;
        let all_stores = bank.push_seed(CellSeed::Unknown)?;
        let mut keys = Vec::new();
        for s in world
            .capsules
            .data()
            .reads
            .iter()
            .chain(&world.capsules.data().writes)
        {
            budget.push(
                &mut keys,
                HeapKey {
                    kind: s.kind,
                    member: s.member,
                },
            )?;
        }
        keys.sort_unstable();
        keys.dedup();
        let mut heap = Vec::new();
        budget.reserve(&mut heap, keys.len())?;
        // A potential store is not must-initialization. Unknown initial values
        // survive while known stored payload alternatives remain available.
        for key in keys {
            heap.push(HeapRow {
                key,
                cell: bank.push_seed(CellSeed::Unknown)?,
            });
        }
        Ok(Self {
            world,
            bank,
            frames: Vec::new(),
            lookup,
            payloads: Vec::new(),
            capture_values: Vec::new(),
            heap,
            wildcard,
            all_stores,
            scratch: Vec::new(),
            definition_offsets,
            defined,
            returns,
        })
    }
    fn find(&self, root: u32, method: MethodId) -> usize {
        let mask = self.lookup.len() - 1;
        let mut slot = hash(root, method.0) & mask;
        loop {
            let e = self.lookup[slot];
            if e.frame == NONE || (e.root == root && e.method == method.0) {
                return slot;
            }
            slot = (slot + 1) & mask;
        }
    }
    fn ensure(
        &mut self,
        root: u32,
        method: MethodId,
        is_root: bool,
        budget: &mut Budget,
    ) -> Result<(u32, bool), Error> {
        let slot = self.find(root, method);
        if self.lookup[slot].frame != NONE {
            return Ok((self.lookup[slot].frame, false));
        }
        if self.frames.len() >= budget.limits.max_callable_frames {
            return Err(Error::Budget);
        }
        let row = self.world.capsules.view(method)?.row;
        let d = self.world.capsules.data();
        let start = u32::try_from(self.bank.len()).map_err(|_| Error::Overflow)?;
        for _ in 0..1 + row.arity + row.captures {
            self.bank.push_seed(if is_root {
                CellSeed::Unknown
            } else {
                CellSeed::Pending
            })?;
        }
        for index in 0..row.locals {
            let defined =
                self.defined[(self.definition_offsets[method.0 as usize] + index) as usize];
            self.bank.push_seed(if defined {
                CellSeed::Pending
            } else {
                CellSeed::Unknown
            })?;
        }
        let has_return = self.returns[method.0 as usize];
        let ret = self.bank.push_seed(if has_return {
            CellSeed::Pending
        } else {
            CellSeed::Unknown
        })?;
        let fi = u32::try_from(self.frames.len()).map_err(|_| Error::Overflow)?;
        budget.push(
            &mut self.frames,
            FrameRow {
                root,
                method,
                start,
                ret,
                payloads: Range::EMPTY,
            },
        )?;
        self.lookup[slot] = Lookup {
            root,
            method: method.0,
            frame: fi,
        };
        let begin = self.payloads.len();
        for template in row.creations.checked(d.creations.len())? {
            if self.payloads.len() >= budget.limits.max_callable_payloads {
                return Err(Error::Budget);
            }
            let creation = d.creations[template];
            let frame = self.frames[fi as usize];
            let payload = u32::try_from(self.payloads.len()).map_err(|_| Error::Overflow)?;
            let singleton = self.bank.push_seed(CellSeed::Pending)?;
            self.bank.add_payload(singleton, payload)?;
            let cap_start =
                u32::try_from(self.capture_values.len()).map_err(|_| Error::Overflow)?;
            for i in creation.captures.checked(d.callable_values.len())? {
                budget.push(
                    &mut self.capture_values,
                    cell_value(frame, row, d.callable_values[i])?,
                )?;
            }
            budget.push(
                &mut self.payloads,
                Payload {
                    template: template as u32,
                    owner: fi,
                    singleton,
                    receiver: cell_value(frame, row, creation.receiver_value)?,
                    captures: Range {
                        start: cap_start,
                        len: creation.captures.len,
                    },
                },
            )?;
        }
        self.frames[fi as usize].payloads = Range {
            start: u32::try_from(begin).map_err(|_| Error::Overflow)?,
            len: u32::try_from(self.payloads.len() - begin).map_err(|_| Error::Overflow)?,
        };
        Ok((fi, true))
    }
    fn canonical(&self, s: StorageRef) -> bool {
        s.kind == StorageKind::ArrayElements
            || (s.kind != StorageKind::RuntimeState
                && self.world.canonical_members[s.member as usize])
    }
    fn heap_cell(&self, s: StorageRef) -> Option<CellId> {
        self.heap
            .binary_search_by_key(
                &HeapKey {
                    kind: s.kind,
                    member: s.member,
                },
                |h| h.key,
            )
            .ok()
            .map(|i| self.heap[i].cell)
    }
    fn bind(
        &mut self,
        caller: u32,
        call: CallRow,
        target: MethodId,
        payload: Option<(u32, InvocationRoute)>,
        budget: &mut Budget,
    ) -> Result<bool, Error> {
        let cf = self.frames[caller as usize];
        let cr = self.world.capsules.view(cf.method)?.row;
        let tr = self.world.capsules.view(target)?.row;
        let d = self.world.capsules.data();
        if call.arguments.len != tr.arity {
            return Err(Error::Capsule(selector_effects::Error::Arity));
        }
        if payload.is_none() && call.captures.len != tr.captures {
            return Err(Error::Capsule(selector_effects::Error::Arity));
        }
        let (tf, mut changed) = self.ensure(cf.root, target, false, budget)?;
        let tf = self.frames[tf as usize];
        let receiver = if let Some((p, route)) = payload {
            let p = self.payloads[p as usize];
            match route {
                InvocationRoute::Implementation => p.receiver,
                InvocationRoute::DefaultBridge => CellValue::Cell(p.singleton),
            }
        } else {
            cell_value(cf, cr, call.receiver_value)?
        };
        changed |= self.bank.join_value(CellId(tf.start), receiver)?;
        for (ordinal, i) in call.arguments.checked(d.callable_values.len())?.enumerate() {
            changed |= self.bank.join_value(
                CellId(tf.start + 1 + ordinal as u32),
                cell_value(cf, cr, d.callable_values[i])?,
            )?;
        }
        if let Some((p, route)) = payload {
            let p = self.payloads[p as usize];
            match route {
                InvocationRoute::Implementation => {
                    if p.captures.len != tr.captures {
                        return Err(Error::Capsule(selector_effects::Error::Arity));
                    }
                    for (ordinal, i) in p.captures.checked(self.capture_values.len())?.enumerate() {
                        changed |= self.bank.join_value(
                            CellId(tf.start + 1 + tr.arity + ordinal as u32),
                            self.capture_values[i],
                        )?;
                    }
                }
                InvocationRoute::DefaultBridge => {
                    if tr.captures != 0 {
                        return Err(Error::Capsule(selector_effects::Error::Arity));
                    }
                }
            }
        } else {
            for (ordinal, i) in call.captures.checked(d.callable_values.len())?.enumerate() {
                changed |= self.bank.join_value(
                    CellId(tf.start + 1 + tr.arity + ordinal as u32),
                    cell_value(cf, cr, d.callable_values[i])?,
                )?;
            }
        }
        if call.result != NONE {
            changed |= self.bank.join(local(cf, cr, call.result), tf.ret)?;
        }
        Ok(changed)
    }
    fn payloads_for(
        &mut self,
        frame: FrameRow,
        row: MethodRow,
        value: ValueRef,
        budget: &mut Budget,
    ) -> Result<(bool, usize), Error> {
        self.scratch.clear();
        let complete = match cell_value(frame, row, value)? {
            CellValue::Cell(id) => {
                for p in self.bank.payloads(id)? {
                    budget.push(&mut self.scratch, p)?;
                }
                self.bank.is_complete_callable(id)?
            }
            _ => false,
        };
        self.scratch.sort_unstable();
        self.scratch.dedup();
        Ok((complete, self.scratch.len()))
    }
    fn compatible(&self, payload: u32, sam: u32) -> Result<Option<CallableInvocation>, Error> {
        let p = *self.payloads.get(payload as usize).ok_or(Error::Bounds)?;
        // owner is retained even when a different root loaded this payload.
        if p.owner as usize >= self.frames.len() {
            return Err(Error::Bounds);
        }
        Ok(self
            .world
            .capsules
            .resolve_callable_invocation(p.template, sam)?)
    }
    fn round(&mut self, budget: &mut Budget) -> Result<bool, Error> {
        let mut changed = false;
        let mut cursor = 0;
        while cursor < self.frames.len() {
            let fi = cursor as u32;
            let frame = self.frames[cursor];
            cursor += 1;
            let view = self.world.capsules.view(frame.method)?;
            let row = view.row;
            let d = self.world.capsules.data();
            budget.tick(view.calls.len() + view.value_flows.len() + view.creations.len() + 1)?;
            for (ordinal, creation) in view.creations.iter().enumerate() {
                changed |= self.bank.add_payload(
                    local(frame, row, creation.destination),
                    frame.payloads.start + ordinal as u32,
                )?;
            }
            for f in view.value_flows {
                match f.kind {
                    ValueFlowKind::Copy => {
                        changed |= self.bank.join_value(
                            local(frame, row, f.index),
                            cell_value(frame, row, f.value)?,
                        )?
                    }
                    ValueFlowKind::Return => {
                        changed |= self
                            .bank
                            .join_value(frame.ret, cell_value(frame, row, f.value)?)?
                    }
                    ValueFlowKind::Store => {
                        let storage = view.writes[f.index as usize];
                        let value = cell_value(frame, row, f.value)?;
                        changed |= self.bank.join_value(self.all_stores, value)?;
                        let cell = if self.canonical(storage) {
                            self.heap_cell(storage).ok_or(Error::Bounds)?
                        } else {
                            self.wildcard
                        };
                        changed |= self.bank.join_value(cell, value)?;
                    }
                    ValueFlowKind::Load => {
                        let storage = view.reads[f.index as usize];
                        let target = local(frame, row, f.value.index);
                        if self.canonical(storage) {
                            changed |= self
                                .bank
                                .join(target, self.heap_cell(storage).ok_or(Error::Bounds)?)?;
                            changed |= self.bank.join(target, self.wildcard)?;
                        } else {
                            changed |= self.bank.join(target, self.all_stores)?;
                        }
                    }
                }
            }
            for call in view.calls {
                match call.target {
                    CallTarget::Direct(target) => {
                        changed |= self.bind(fi, *call, target, None, budget)?
                    }
                    CallTarget::Callable { value, sam } => {
                        let (_, n) = self.payloads_for(frame, row, value, budget)?;
                        for i in 0..n {
                            let payload = self.scratch[i];
                            if let Some(invocation) = self.compatible(payload, sam)? {
                                changed |= self.bind(
                                    fi,
                                    *call,
                                    invocation.implementation,
                                    Some((payload, invocation.route)),
                                    budget,
                                )?;
                            }
                        }
                    }
                }
            }
            for &target in view.initializes {
                let tr = self.world.capsules.view(target)?.row;
                if tr.arity != 0 || tr.captures != 0 {
                    return Err(Error::Capsule(selector_effects::Error::Arity));
                }
                let (_, created) = self.ensure(frame.root, target, false, budget)?;
                changed |= created;
            }
            // Unmodeled field writes may store arbitrary callables. Initial
            // cells are already Unknown; preserve known alternatives as well.
            if row.top.contains(Channel::Writes) {
                changed |= self.bank.set_unknown(self.wildcard)?;
            }
            let _ = d;
        }
        Ok(changed)
    }
}

pub(crate) fn resolve(world: World<'_>, budget: &mut Budget) -> Result<Resolution, Error> {
    let d = world.capsules.data();
    let top = budget.filled(world.roots.len(), TopMask::NONE)?;
    if d.creations.is_empty()
        && d.value_flows.is_empty()
        && d.calls
            .iter()
            .all(|c| matches!(c.target, CallTarget::Direct(_)))
    {
        return Ok(Resolution {
            edges: Vec::new(),
            top,
        });
    }
    let mut engine = Engine::new(world, budget)?;
    for (root, r) in world.roots.iter().enumerate() {
        engine.ensure(root as u32, r.method, true, budget)?;
    }
    let mut fixed = false;
    for _ in 0..budget.limits.max_callable_rounds {
        if !engine.round(budget)? {
            fixed = true;
            break;
        }
    }
    if !fixed {
        return Err(Error::Budget);
    }
    let mut result = Resolution {
        edges: Vec::new(),
        top,
    };
    for i in 0..engine.frames.len() {
        let f = engine.frames[i];
        let view = world.capsules.view(f.method)?;
        for (ordinal, call) in view.calls.iter().enumerate() {
            if let CallTarget::Callable { value, sam } = call.target {
                let (mut complete, n) = engine.payloads_for(f, view.row, value, budget)?;
                for j in 0..n {
                    let payload = engine.scratch[j];
                    if let Some(invocation) = engine.compatible(payload, sam)? {
                        if result.edges.len() >= budget.limits.max_refs {
                            return Err(Error::Budget);
                        }
                        budget.push(
                            &mut result.edges,
                            SymbolicEdge {
                                root: f.root,
                                caller: f.method,
                                call: ordinal as u32,
                                target: invocation.implementation,
                            },
                        )?;
                    } else {
                        complete = false;
                    }
                }
                if !complete {
                    result.top[f.root as usize].insert(Channel::Calls);
                }
            }
        }
    }
    result.edges.sort_unstable();
    result.edges.dedup();
    Ok(result)
}
