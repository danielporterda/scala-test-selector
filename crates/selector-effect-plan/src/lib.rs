//! Input-bound static effect planning. A cryptographic seal binds reviewed
//! inputs; it does not turn an untrusted capsule producer into semantic
//! authority. This crate is not activated by query selection.
//!
//! The algorithm uses a flat SCC graph and root bit matrix, then one reusable
//! origin environment for each catalogue root. Change influence is deliberately
//! coarse: a changed dependency taints the enclosing root's possible effects.
//! This loses invocation precision but does not confuse direct stores with a
//! complete influence proof. Every finite call/initialization is composed.

use selector_effects::*;
use sha2::{Digest, Sha256};
use std::{fmt, mem::size_of};
mod callables;

pub type Identity = [u8; 32];
const DOMAIN: &[u8] = b"selector-effect-plan/3\0";
const ANY: u64 = u64::MAX;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WorldBinding {
    pub producer: Identity,
    pub facts: Identity,
    pub graph: Identity,
    pub runtime: Identity,
    pub inputs: Identity,
    pub catalogue: Identity,
    pub contracts: Identity,
    pub member_authority: Identity,
    /// Verified transport/artifact identity, not the canonical DTO scalar hash.
    pub capsules: Identity,
    pub root_count: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Root {
    /// Exact compiler identity, context and receiver binding, supplied by a
    /// verified catalogue. Local MethodIds are not cross-snapshot identities.
    pub key: Identity,
    pub method: MethodId,
}

#[derive(Clone, Debug, Default)]
pub struct Changes {
    /// Complete body/declaration/class-initializer dependency seeds, sorted.
    pub methods: Vec<MethodId>,
    pub classes: Vec<u32>,
}

#[derive(Clone, Copy)]
pub struct World<'a> {
    pub capsules: &'a Capsules,
    pub binding: WorldBinding,
    pub roots: &'a [Root],
    pub changes: &'a Changes,
    /// True only for globally linked declaring-field/runtime identities. A
    /// source SymbolId or constant-pool owner alone does not prove this.
    pub canonical_members: &'a [bool],
    pub ambient: AmbientCoverage,
    /// Retained verified transport/key-table ownership, in addition to the
    /// decoded DTO capacities. Zero only for a directly producer-owned DTO.
    pub transport_bytes: usize,
}

/// A suite catalogue does not prove the absence of background/bootstrap/user
/// entrypoints. This prototype has no producer for the reviewed contract below.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum AmbientCoverage {
    #[default]
    Unverified,
    NoAdditionalRunnableEntries {
        contract: Identity,
    },
}

#[derive(Clone, Copy, Debug)]
pub struct PlanLimits {
    pub max_methods: usize,
    pub max_refs: usize,
    pub max_roots: usize,
    pub max_origin_slots: usize,
    pub max_output_rows: usize,
    pub max_bytes: usize,
    pub max_work: u64,
    pub max_callable_frames: usize,
    pub max_callable_cells: usize,
    pub max_callable_payloads: usize,
    pub max_callable_members: usize,
    pub max_callable_targets: u32,
    pub max_callable_rounds: usize,
}
impl Default for PlanLimits {
    fn default() -> Self {
        Self {
            max_methods: 1_000_000,
            max_refs: 2_000_000,
            max_roots: 1024,
            max_origin_slots: 4_000_000,
            max_output_rows: 2_000_000,
            max_bytes: 512 << 20,
            max_work: 200_000_000,
            max_callable_frames: 500_000,
            max_callable_cells: 2_000_000,
            max_callable_payloads: 500_000,
            max_callable_members: 4_000_000,
            max_callable_targets: 32,
            max_callable_rounds: 64,
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Error {
    Capsule(selector_effects::Error),
    Bounds,
    Binding,
    Catalogue,
    Order,
    Budget,
    Overflow,
    Seal,
}
impl From<selector_effects::Error> for Error {
    fn from(e: selector_effects::Error) -> Self {
        Self::Capsule(e)
    }
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "effect plan {self:?}")
    }
}
impl std::error::Error for Error {}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Decision {
    Retained,
    Excluded,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Reason {
    ChangedDependency,
    OpenRoot,
    ChangedSharedStorage,
    ChangedExternal,
    ChangedControl,
    OpenUniverse,
    UnchangedClosedRegion,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RootDecision {
    pub key: Identity,
    pub decision: Decision,
    pub reason: Reason,
    pub top: TopMask,
    pub reachable_methods: u32,
    pub reads: u32,
    pub writes: u32,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Metrics {
    pub methods: u32,
    pub refs: u32,
    pub components: u32,
    pub catalogue_roots: u32,
    pub root_matrix_bytes: u64,
    pub work: u64,
    /// Conservative cumulative charged capacities, including reusable scratch.
    pub charged_bytes: u64,
}

/// Fields are private. Validation also binds the caller's current inputs, so a
/// valid proof cannot be transplanted to another snapshot/root set/change set.
pub struct Plan {
    binding: WorldBinding,
    input: Identity,
    decisions: Vec<RootDecision>,
    metrics: Metrics,
    seal: Identity,
}
impl Plan {
    pub fn decisions(&self) -> &[RootDecision] {
        &self.decisions
    }
    pub fn metrics(&self) -> Metrics {
        self.metrics
    }
    pub fn identity(&self) -> Identity {
        self.seal
    }
    pub fn validate(&self, world: World<'_>) -> Result<(), Error> {
        validate_world(world)?;
        if self.binding != world.binding
            || self.input != input_identity(world)?
            || self.seal != seal(self)
        {
            return Err(Error::Seal);
        }
        Ok(())
    }
    pub fn decision(&self, key: Identity) -> Option<RootDecision> {
        self.decisions
            .binary_search_by_key(&key, |d| d.key)
            .ok()
            .map(|i| self.decisions[i])
    }
}

pub struct PairedPlan {
    base: Identity,
    head: Identity,
    decisions: Vec<RootDecision>,
    seal: Identity,
}
impl PairedPlan {
    pub fn decisions(&self) -> &[RootDecision] {
        &self.decisions
    }
    pub fn identity(&self) -> Identity {
        self.seal
    }
    pub fn validate(
        &self,
        base: &Plan,
        bw: World<'_>,
        head: &Plan,
        hw: World<'_>,
    ) -> Result<(), Error> {
        base.validate(bw)?;
        head.validate(hw)?;
        if self.base != base.identity()
            || self.head != head.identity()
            || self.seal != pair_seal(self)
        {
            return Err(Error::Seal);
        }
        Ok(())
    }
}

/// Both snapshots and the exact complete stable root catalogue are mandatory.
/// New/removed/ambiguous roots require another authority and are rejected here.
pub fn paired(base: &Plan, bw: World<'_>, head: &Plan, hw: World<'_>) -> Result<PairedPlan, Error> {
    base.validate(bw)?;
    head.validate(hw)?;
    if base.decisions.len() != head.decisions.len() {
        return Err(Error::Catalogue);
    }
    let mut decisions = Vec::new();
    decisions
        .try_reserve_exact(base.decisions.len())
        .map_err(|_| Error::Budget)?;
    for (b, h) in base.decisions.iter().zip(&head.decisions) {
        if b.key != h.key {
            return Err(Error::Catalogue);
        }
        let mut d = *h;
        if b.decision != Decision::Excluded {
            d.decision = Decision::Retained;
            d.reason = b.reason;
        }
        decisions.push(d);
    }
    let mut pair = PairedPlan {
        base: base.identity(),
        head: head.identity(),
        decisions,
        seal: [0; 32],
    };
    pair.seal = pair_seal(&pair);
    Ok(pair)
}

struct Budget {
    bytes: usize,
    work: u64,
    limits: PlanLimits,
}
impl Budget {
    fn new(limits: PlanLimits) -> Self {
        Self {
            bytes: 0,
            work: 0,
            limits,
        }
    }
    fn tick(&mut self, n: usize) -> Result<(), Error> {
        self.work = self.work.checked_add(n as u64).ok_or(Error::Overflow)?;
        if self.work > self.limits.max_work {
            Err(Error::Budget)
        } else {
            Ok(())
        }
    }
    fn reserve<T>(&mut self, v: &mut Vec<T>, count: usize) -> Result<(), Error> {
        if count <= v.capacity() {
            return Ok(());
        }
        let additional = count.checked_sub(v.capacity()).ok_or(Error::Overflow)?;
        let estimate = additional
            .checked_mul(size_of::<T>())
            .ok_or(Error::Overflow)?;
        if self.bytes.checked_add(estimate).ok_or(Error::Overflow)? > self.limits.max_bytes {
            return Err(Error::Budget);
        }
        let old = v.capacity();
        v.try_reserve_exact(count.saturating_sub(v.len()))
            .map_err(|_| Error::Budget)?;
        self.bytes = self
            .bytes
            .checked_add(
                (v.capacity() - old)
                    .checked_mul(size_of::<T>())
                    .ok_or(Error::Overflow)?,
            )
            .ok_or(Error::Overflow)?;
        if self.bytes > self.limits.max_bytes {
            return Err(Error::Budget);
        }
        Ok(())
    }
    fn push<T>(&mut self, v: &mut Vec<T>, x: T) -> Result<(), Error> {
        if v.len() == v.capacity() {
            let wanted = v
                .len()
                .checked_add(1)
                .ok_or(Error::Overflow)?
                .max(v.capacity().saturating_mul(2))
                .max(4);
            self.reserve(v, wanted)?;
        }
        v.push(x);
        Ok(())
    }
    fn filled<T: Clone>(&mut self, n: usize, value: T) -> Result<Vec<T>, Error> {
        let mut v = Vec::new();
        self.reserve(&mut v, n)?;
        v.resize(n, value);
        Ok(v)
    }
}

struct Csr {
    offsets: Vec<u32>,
    targets: Vec<u32>,
}
fn csr(n: usize, edges: &[(u32, u32)], reverse: bool, budget: &mut Budget) -> Result<Csr, Error> {
    let mut offsets = budget.filled(n + 1, 0u32)?;
    for &(a, b) in edges {
        let a = if reverse { b } else { a };
        offsets[a as usize + 1] = offsets[a as usize + 1]
            .checked_add(1)
            .ok_or(Error::Overflow)?;
    }
    for i in 1..offsets.len() {
        offsets[i] = offsets[i]
            .checked_add(offsets[i - 1])
            .ok_or(Error::Overflow)?;
    }
    let mut next = Vec::new();
    budget.reserve(&mut next, offsets.len())?;
    next.extend_from_slice(&offsets);
    let mut targets = budget.filled(edges.len(), 0u32)?;
    for &(a, b) in edges {
        let (a, b) = if reverse { (b, a) } else { (a, b) };
        let p = &mut next[a as usize];
        targets[*p as usize] = b;
        *p += 1;
    }
    Ok(Csr { offsets, targets })
}

struct Components {
    of: Vec<u32>,
    recursive: Vec<bool>,
    masks: Vec<u64>,
    words: usize,
    count: usize,
}
fn components(
    world: World<'_>,
    resolved: &callables::Resolution,
    budget: &mut Budget,
) -> Result<Components, Error> {
    let n = world.capsules.len();
    let d = world.capsules.data();
    let edge_count = d
        .calls
        .len()
        .checked_add(d.initializes.len())
        .and_then(|n| n.checked_add(resolved.edges.len()))
        .ok_or(Error::Overflow)?;
    if edge_count > budget.limits.max_refs {
        return Err(Error::Budget);
    }
    let mut edges = Vec::new();
    budget.reserve(&mut edges, edge_count)?;
    for (mi, m) in d.methods.iter().enumerate() {
        for i in m.calls.checked(d.calls.len())? {
            if let CallTarget::Direct(target) = d.calls[i].target {
                edges.push((mi as u32, target.0));
            }
        }
        for i in m.initializes.checked(d.initializes.len())? {
            edges.push((mi as u32, d.initializes[i].0));
        }
    }
    for edge in &resolved.edges {
        edges.push((edge.caller.0, edge.target.0));
    }
    if edges.len() > budget.limits.max_refs {
        return Err(Error::Budget);
    }
    edges.sort_unstable();
    edges.dedup();
    let graph = csr(n, &edges, false, budget)?;
    let reverse = csr(n, &edges, true, budget)?;
    let mut visited = budget.filled(n, false)?;
    let mut order = Vec::new();
    budget.reserve(&mut order, n)?;
    let mut stack = Vec::new();
    budget.reserve(&mut stack, n)?;
    for start in 0..n {
        if visited[start] {
            continue;
        }
        visited[start] = true;
        stack.push((start as u32, graph.offsets[start]));
        while let Some((node, cursor)) = stack.last_mut() {
            budget.tick(1)?;
            if *cursor < graph.offsets[*node as usize + 1] {
                let child = graph.targets[*cursor as usize] as usize;
                *cursor += 1;
                if !visited[child] {
                    visited[child] = true;
                    stack.push((child as u32, graph.offsets[child]));
                }
            } else {
                let (node, _) = stack.pop().unwrap();
                order.push(node);
            }
        }
    }
    let mut of = budget.filled(n, NONE)?;
    let mut sizes = Vec::new();
    budget.reserve(&mut sizes, n)?;
    let mut todo = Vec::new();
    budget.reserve(&mut todo, n)?;
    for &start in order.iter().rev() {
        if of[start as usize] != NONE {
            continue;
        }
        let c = u32::try_from(sizes.len()).map_err(|_| Error::Overflow)?;
        let mut size = 0u32;
        of[start as usize] = c;
        todo.push(start);
        while let Some(node) = todo.pop() {
            size += 1;
            budget.tick(1)?;
            for i in reverse.offsets[node as usize]..reverse.offsets[node as usize + 1] {
                let child = reverse.targets[i as usize];
                if of[child as usize] == NONE {
                    of[child as usize] = c;
                    todo.push(child);
                }
            }
        }
        sizes.push(size);
    }
    let count = sizes.len();
    let mut recursive = budget.filled(count, false)?;
    for (i, &s) in sizes.iter().enumerate() {
        recursive[i] = s > 1;
    }
    let mut condensed = Vec::new();
    budget.reserve(&mut condensed, edges.len())?;
    for &(a, b) in &edges {
        let (x, y) = (of[a as usize], of[b as usize]);
        if x == y {
            if a == b {
                recursive[x as usize] = true;
            }
        } else {
            condensed.push((x, y));
        }
    }
    condensed.sort_unstable();
    condensed.dedup();
    let dag = csr(count, &condensed, false, budget)?;
    let mut indegree = budget.filled(count, 0u32)?;
    for &(_, b) in &condensed {
        indegree[b as usize] += 1;
    }
    let words = (world.roots.len() + 63) / 64;
    let mut masks = budget.filled(count.checked_mul(words).ok_or(Error::Overflow)?, 0u64)?;
    for (ri, r) in world.roots.iter().enumerate() {
        masks[of[r.method.0 as usize] as usize * words + ri / 64] |= 1u64 << (ri % 64);
    }
    todo.clear();
    for (c, &degree) in indegree.iter().enumerate() {
        if degree == 0 {
            todo.push(c as u32);
        }
    }
    let mut cursor = 0;
    while cursor < todo.len() {
        let c = todo[cursor] as usize;
        cursor += 1;
        for i in dag.offsets[c]..dag.offsets[c + 1] {
            let child = dag.targets[i as usize] as usize;
            for w in 0..words {
                let value = masks[c * words + w];
                masks[child * words + w] |= value;
            }
            budget.tick(words + 1)?;
            indegree[child] -= 1;
            if indegree[child] == 0 {
                todo.push(child as u32);
            }
        }
    }
    if cursor != count {
        return Err(Error::Bounds);
    }
    Ok(Components {
        of,
        recursive,
        masks,
        words,
        count,
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct Region {
    kind: StorageKind,
    member: u32,
    base: u64,
}
#[derive(Clone, Copy)]
struct RootSummary {
    top: TopMask,
    reads: Range,
    writes: Range,
    external: Range,
    throws: bool,
    sync: bool,
    reached: u32,
    changed: bool,
}
struct Footprints {
    roots: Vec<RootSummary>,
    reads: Vec<Region>,
    writes: Vec<Region>,
    external: Vec<ExternalRef>,
}

fn append<T: Copy>(target: &mut Vec<T>, source: &[T], budget: &mut Budget) -> Result<Range, Error> {
    if target
        .len()
        .checked_add(source.len())
        .ok_or(Error::Overflow)?
        > budget.limits.max_output_rows
    {
        return Err(Error::Budget);
    }
    let r = Range {
        start: u32::try_from(target.len()).map_err(|_| Error::Overflow)?,
        len: u32::try_from(source.len()).map_err(|_| Error::Overflow)?,
    };
    let wanted = target.len() + source.len();
    budget.reserve(target, wanted)?;
    target.extend_from_slice(source);
    Ok(r)
}
fn mapped(
    origin: Origin,
    method: MethodId,
    root: MethodId,
    env: &[u64],
    offset: usize,
    row: MethodRow,
    recursive: bool,
) -> u64 {
    match origin.kind {
        OriginKind::Any => ANY,
        OriginKind::Receiver => env[offset],
        OriginKind::Argument => env[offset + 1 + origin.index as usize],
        OriginKind::Capture => env[offset + 1 + row.arity as usize + origin.index as usize],
        OriginKind::Fresh if method == root && !recursive => {
            ((root.0 as u64) << 32) | origin.index as u64
        }
        OriginKind::Fresh => ANY,
    }
}
fn queue_environment(
    target: MethodId,
    values: &[u64],
    offsets: &[u32],
    generation: u32,
    seen: &mut [u32],
    queued: &mut [u32],
    env: &mut [u64],
    todo: &mut Vec<MethodId>,
    reached: &mut Vec<MethodId>,
    budget: &mut Budget,
) -> Result<(), Error> {
    let mi = target.0 as usize;
    let start = offsets[mi] as usize;
    let end = offsets[mi + 1] as usize;
    if values.len() != end - start {
        return Err(Error::Capsule(selector_effects::Error::Arity));
    }
    let mut changed = false;
    if seen[mi] != generation {
        seen[mi] = generation;
        env[start..end].copy_from_slice(values);
        changed = true;
        budget.push(reached, target)?;
    } else {
        for (slot, &value) in env[start..end].iter_mut().zip(values) {
            if *slot != value && *slot != ANY {
                *slot = ANY;
                changed = true;
            }
        }
    }
    if changed && queued[mi] != generation {
        queued[mi] = generation;
        budget.push(todo, target)?;
    }
    Ok(())
}

fn footprints(
    world: World<'_>,
    comps: &Components,
    resolved: &callables::Resolution,
    budget: &mut Budget,
) -> Result<Footprints, Error> {
    let d = world.capsules.data();
    let n = d.methods.len();
    let mut offsets = budget.filled(n + 1, 0u32)?;
    let mut max_slots = 1usize;
    for (i, m) in d.methods.iter().enumerate() {
        let slots = 1usize
            .checked_add(m.arity as usize)
            .and_then(|v| v.checked_add(m.captures as usize))
            .ok_or(Error::Overflow)?;
        max_slots = max_slots.max(slots);
        offsets[i + 1] = offsets[i]
            .checked_add(u32::try_from(slots).map_err(|_| Error::Overflow)?)
            .ok_or(Error::Overflow)?;
    }
    if offsets[n] as usize > budget.limits.max_origin_slots {
        return Err(Error::Budget);
    }
    let mut env = budget.filled(offsets[n] as usize, ANY)?;
    let mut seen = budget.filled(n, 0u32)?;
    let mut queued = budget.filled(n, 0u32)?;
    let mut todo = Vec::new();
    let mut reached = Vec::new();
    budget.reserve(&mut todo, n)?;
    budget.reserve(&mut reached, n)?;
    let mut values = Vec::new();
    budget.reserve(&mut values, max_slots)?;
    let mut escaped = Vec::new();
    let mut reads = Vec::new();
    let mut writes = Vec::new();
    let mut external = Vec::new();
    let mut written_members = Vec::new();
    let mut unknown_captures = Vec::new();
    let mut out = Footprints {
        roots: Vec::new(),
        reads: Vec::new(),
        writes: Vec::new(),
        external: Vec::new(),
    };
    budget.reserve(&mut out.roots, world.roots.len())?;
    for (ri, root) in world.roots.iter().enumerate() {
        let generation = u32::try_from(ri + 1).map_err(|_| Error::Overflow)?;
        todo.clear();
        reached.clear();
        escaped.clear();
        reads.clear();
        writes.clear();
        external.clear();
        values.clear();
        values.resize(
            (offsets[root.method.0 as usize + 1] - offsets[root.method.0 as usize]) as usize,
            ANY,
        );
        queue_environment(
            root.method,
            &values,
            &offsets,
            generation,
            &mut seen,
            &mut queued,
            &mut env,
            &mut todo,
            &mut reached,
            budget,
        )?;
        let mut cursor = 0;
        while cursor < todo.len() {
            let id = todo[cursor];
            cursor += 1;
            queued[id.0 as usize] = 0;
            let view = world.capsules.view(id)?;
            let row = view.row;
            let offset = offsets[id.0 as usize] as usize;
            let recursive = comps.recursive[comps.of[id.0 as usize] as usize];
            for (ordinal, call) in view.calls.iter().enumerate() {
                budget.tick(1)?;
                let direct = match call.target {
                    CallTarget::Direct(target) => Some(target),
                    CallTarget::Callable { .. } => None,
                };
                for target_id in direct.into_iter().chain(
                    resolved
                        .targets(ri as u32, id, ordinal as u32)
                        .iter()
                        .map(|e| e.target),
                ) {
                    let target = world.capsules.view(target_id)?.row;
                    let args = &d.origins[call.arguments.checked(d.origins.len())?];
                    let captures = if direct.is_some() {
                        &d.origins[call.captures.checked(d.origins.len())?]
                    } else {
                        budget.reserve(&mut unknown_captures, target.captures as usize)?;
                        unknown_captures.clear();
                        unknown_captures.resize(target.captures as usize, Origin::ANY);
                        &unknown_captures
                    };
                    // Frame checks the exact finite ABI. An ALL-TOP target with
                    // unavailable shape is not silently treated as a closed call.
                    let receiver = if direct.is_some() {
                        call.receiver
                    } else {
                        Origin::ANY
                    };
                    Frame::new(target, row, receiver, args, captures, &[])?;
                    values.clear();
                    values.push(mapped(
                        receiver,
                        id,
                        root.method,
                        &env,
                        offset,
                        row,
                        recursive,
                    ));
                    for &o in args.iter().chain(captures) {
                        values.push(mapped(o, id, root.method, &env, offset, row, recursive));
                    }
                    queue_environment(
                        target_id,
                        &values,
                        &offsets,
                        generation,
                        &mut seen,
                        &mut queued,
                        &mut env,
                        &mut todo,
                        &mut reached,
                        budget,
                    )?;
                }
            }
            for &target in view.initializes {
                let row = world.capsules.view(target)?.row;
                if row.arity != 0 || row.captures != 0 {
                    return Err(Error::Capsule(selector_effects::Error::Arity));
                }
                values.clear();
                values.push(ANY);
                queue_environment(
                    target,
                    &values,
                    &offsets,
                    generation,
                    &mut seen,
                    &mut queued,
                    &mut env,
                    &mut todo,
                    &mut reached,
                    budget,
                )?;
            }
        }
        let mut top = resolved.top[ri];
        if top.contains(Channel::Calls) {
            top.join(TopMask::ALL);
        }
        let mut changed = false;
        let mut throws = false;
        let mut sync = false;
        let mut escape_all = false;
        for &id in &reached {
            let view = world.capsules.view(id)?;
            let offset = offsets[id.0 as usize] as usize;
            let recursive = comps.recursive[comps.of[id.0 as usize] as usize];
            budget.tick(
                view.reads.len() + view.writes.len() + view.calls.len() + view.flows.len() + 1,
            )?;
            top.join(view.row.top);
            if view.row.top.contains(Channel::Calls) || view.row.top.contains(Channel::Initializes)
                // No granular no-later-callbacks contract is admitted by this
                // prototype; an unknown escape can activate a callable later.
                || view.row.top.contains(Channel::Escapes)
            {
                top.join(TopMask::ALL);
            }
            if view.row.top.contains(Channel::Escapes) {
                escape_all = true;
            }
            changed |= world.changes.methods.binary_search(&id).is_ok();
            changed |= view.row.top.contains(Channel::CodeObservations)
                && (!world.changes.methods.is_empty() || !world.changes.classes.is_empty());
            for c in view.code_observations {
                changed |= match c.kind {
                    CodeKind::Method => world
                        .changes
                        .methods
                        .binary_search(&MethodId(c.index))
                        .is_ok(),
                    // The leaf DTO has no method→declaring-class coverage
                    // proof. A method delta may change a class resource even
                    // when a caller omitted that class from its seed list.
                    CodeKind::Class => {
                        world.changes.classes.binary_search(&c.index).is_ok()
                            || !world.changes.methods.is_empty()
                    }
                };
            }
            written_members.clear();
            for w in view.writes {
                budget.push(&mut written_members, w.member)?;
            }
            written_members.sort_unstable();
            written_members.dedup();
            for e in view.escapes {
                let base = mapped(e.origin, id, root.method, &env, offset, view.row, recursive);
                if base != ANY {
                    budget.push(&mut escaped, base)?;
                } else {
                    escape_all = true;
                }
                match e.sink {
                    EscapeSink::Unknown => top.join(TopMask::ALL),
                    EscapeSink::External => top.insert(Channel::External),
                    EscapeSink::Heap if written_members.binary_search(&e.index).is_err() => {
                        top.insert(Channel::Writes)
                    }
                    _ => (),
                }
            }
            for (source, target, channel) in [
                (view.reads, &mut reads, Channel::Reads),
                (view.writes, &mut writes, Channel::Writes),
            ] {
                for storage in source {
                    // A RuntimeState bucket is not a substitute for canonical
                    // ordinary fields (e.g. VM-mutated Throwable fields). This
                    // v1 DTO lacks the cross-kind alias proof, so keep TOP.
                    if storage.kind == StorageKind::RuntimeState
                        || (storage.kind != StorageKind::ArrayElements
                            && !world.canonical_members[storage.member as usize])
                    {
                        top.insert(channel);
                        continue;
                    }
                    budget.push(
                        target,
                        Region {
                            kind: storage.kind,
                            member: storage.member,
                            base: mapped(
                                storage.base,
                                id,
                                root.method,
                                &env,
                                offset,
                                view.row,
                                recursive,
                            ),
                        },
                    )?;
                }
            }
            for &e in view.external {
                budget.push(&mut external, e)?;
            }
            // A type-only Throws row has no exception-object origin or alias
            // identity. Until an explicit ordinary-Throwable storage contract
            // accompanies it, it cannot be a finite shared-state certificate.
            if !view.throws.is_empty() {
                top.insert(Channel::Writes);
                top.insert(Channel::Throws);
            }
            throws |= !view.throws.is_empty();
            sync |= !view.synchronizes.is_empty();
        }
        // Unknown calls/initialization/escape were promoted above. Their arbitrary
        // code observations can invoke changed code even with unchanged args.
        changed |= top.contains(Channel::CodeObservations)
            && (!world.changes.methods.is_empty() || !world.changes.classes.is_empty());
        // An escaping closure's captures require a producer sidecar. The core
        // has no capture-to-allocation proof; its Escapes TOP must remain TOP.
        escaped.sort_unstable();
        escaped.dedup();
        for r in reads.iter_mut().chain(&mut writes) {
            if escape_all || escaped.binary_search(&r.base).is_ok() {
                r.base = ANY;
            }
        }
        reads.sort_unstable();
        reads.dedup();
        writes.sort_unstable();
        writes.dedup();
        external.sort_unstable_by_key(|e| (e.kind as u32, e.key));
        external.dedup();
        let read_range = append(&mut out.reads, &reads, budget)?;
        let write_range = append(&mut out.writes, &writes, budget)?;
        let ext_range = append(&mut out.external, &external, budget)?;
        out.roots.push(RootSummary {
            top,
            reads: read_range,
            writes: write_range,
            external: ext_range,
            throws,
            sync,
            reached: u32::try_from(reached.len()).map_err(|_| Error::Overflow)?,
            changed,
        });
    }
    Ok(out)
}

fn alias(a: Region, b: Region) -> bool {
    a.kind == b.kind && a.member == b.member && (a.base == ANY || b.base == ANY || a.base == b.base)
}
fn storage_intersects(
    reads: &[Region],
    writes: &[Region],
    budget: &mut Budget,
) -> Result<bool, Error> {
    // Sorted member postings avoid a full read×write scan. Origins are compared
    // only inside equal canonical member/kind ranges; ANY is a wildcard.
    let mut i = 0;
    let mut j = 0;
    while i < reads.len() && j < writes.len() {
        budget.tick(1)?;
        let ak = (reads[i].kind, reads[i].member);
        let bk = (writes[j].kind, writes[j].member);
        if ak < bk {
            i += 1;
            continue;
        }
        if bk < ak {
            j += 1;
            continue;
        }
        let mut ie = i + 1;
        while ie < reads.len() && (reads[ie].kind, reads[ie].member) == ak {
            ie += 1;
        }
        let mut je = j + 1;
        while je < writes.len() && (writes[je].kind, writes[je].member) == bk {
            je += 1;
        }
        if reads[ie - 1].base == ANY || writes[je - 1].base == ANY {
            return Ok(true);
        }
        let (mut ai, mut bj) = (i, j);
        while ai < ie && bj < je {
            budget.tick(1)?;
            if alias(reads[ai], writes[bj]) {
                return Ok(true);
            }
            if reads[ai].base < writes[bj].base {
                ai += 1;
            } else {
                bj += 1;
            }
        }
        i = ie;
        j = je;
    }
    Ok(false)
}

fn external_intersects(
    reader: &[ExternalRef],
    writer: &[ExternalRef],
    budget: &mut Budget,
) -> Result<bool, Error> {
    let start = writer.partition_point(|e| (e.kind as u32) < ExternalKind::Write as u32);
    let end = writer.partition_point(|e| (e.kind as u32) <= ExternalKind::Write as u32);
    let writes = &writer[start..end];
    for r in reader {
        budget.tick(1 + writes.len().checked_ilog2().unwrap_or(0) as usize)?;
        if writes.binary_search_by_key(&r.key, |e| e.key).is_ok() {
            return Ok(true);
        }
    }
    Ok(false)
}

pub fn plan(world: World<'_>, limits: PlanLimits) -> Result<Plan, Error> {
    if world.capsules.len() > limits.max_methods || world.roots.len() > limits.max_roots {
        return Err(Error::Budget);
    }
    if world
        .capsules
        .data()
        .calls
        .len()
        .checked_add(world.capsules.data().initializes.len())
        .ok_or(Error::Overflow)?
        > limits.max_refs
    {
        return Err(Error::Budget);
    }
    validate_world(world)?;
    let mut budget = Budget::new(limits);
    // Input ownership is part of the budget, not an uncharged prerequisite.
    // The fixed allowance covers Vec headers and bounded stack bookkeeping.
    budget.bytes = world
        .capsules
        .owned_bytes()
        .checked_add(
            world
                .roots
                .len()
                .checked_mul(size_of::<Root>())
                .ok_or(Error::Overflow)?,
        )
        .and_then(|v| v.checked_add(world.canonical_members.len()))
        .and_then(|v| v.checked_add(world.transport_bytes))
        .and_then(|v| v.checked_add(world.changes.methods.capacity() * size_of::<MethodId>()))
        .and_then(|v| v.checked_add(world.changes.classes.capacity() * size_of::<u32>()))
        .and_then(|v| v.checked_add(4096))
        .ok_or(Error::Overflow)?;
    if budget.bytes > limits.max_bytes {
        return Err(Error::Budget);
    }
    let input = input_identity(world)?;
    let resolved = callables::resolve(world, &mut budget)?;
    let comps = components(world, &resolved, &mut budget)?;
    let fp = footprints(world, &comps, &resolved, &mut budget)?;
    let mut influenced = budget.filled(world.roots.len(), false)?;
    let mut reason = budget.filled(world.roots.len(), Reason::UnchangedClosedRegion)?;
    let mut todo = Vec::new();
    budget.reserve(&mut todo, world.roots.len())?;
    for (i, s) in fp.roots.iter().enumerate() {
        if s.changed {
            influenced[i] = true;
            reason[i] = Reason::ChangedDependency;
            todo.push(i as u32);
        }
    }
    // Missing ambient coverage is an arbitrary observing/control component,
    // not a finite writer dismissible by a field-key comparison.
    if world.ambient == AmbientCoverage::Unverified
        && (!world.changes.methods.is_empty() || !world.changes.classes.is_empty())
    {
        for i in 0..influenced.len() {
            if !influenced[i] {
                influenced[i] = true;
                reason[i] = Reason::OpenUniverse;
                todo.push(i as u32);
            }
        }
    }
    let mut cursor = 0;
    while cursor < todo.len() {
        let writer = todo[cursor] as usize;
        cursor += 1;
        let w = fp.roots[writer];
        let writes = &fp.writes[w.writes.checked(fp.writes.len())?];
        let ext = &fp.external[w.external.checked(fp.external.len())?];
        let global_control = w.top.contains(Channel::External)
            || w.top.contains(Channel::Throws)
            || w.top.contains(Channel::Synchronizes)
            || w.throws
            || w.sync
            || ext.iter().any(|e| e.kind == ExternalKind::Control);
        for (reader, r) in fp.roots.iter().enumerate() {
            budget.tick(1)?;
            if influenced[reader] {
                continue;
            }
            let reads = &fp.reads[r.reads.checked(fp.reads.len())?];
            let r_ext = &fp.external[r.external.checked(fp.external.len())?];
            let storage = (w.top.contains(Channel::Writes)
                && (!reads.is_empty() || r.top.contains(Channel::Reads)))
                || (r.top.contains(Channel::Reads)
                    && (!writes.is_empty() || w.top.contains(Channel::Writes)))
                || storage_intersects(reads, writes, &mut budget)?;
            let external = external_intersects(r_ext, ext, &mut budget)?
                || (r.top.contains(Channel::External) && !ext.is_empty());
            if global_control || storage || external {
                influenced[reader] = true;
                reason[reader] = if global_control {
                    Reason::ChangedControl
                } else if storage {
                    Reason::ChangedSharedStorage
                } else {
                    Reason::ChangedExternal
                };
                todo.push(reader as u32);
            }
        }
    }
    let mut decisions = Vec::new();
    budget.reserve(&mut decisions, world.roots.len())?;
    for (i, r) in world.roots.iter().enumerate() {
        let s = fp.roots[i];
        let decision = if influenced[i] || !s.top.is_empty() {
            Decision::Retained
        } else {
            Decision::Excluded
        };
        let why = if influenced[i] {
            reason[i]
        } else if !s.top.is_empty() {
            Reason::OpenRoot
        } else {
            Reason::UnchangedClosedRegion
        };
        decisions.push(RootDecision {
            key: r.key,
            decision,
            reason: why,
            top: s.top,
            reachable_methods: s.reached,
            reads: s.reads.len,
            writes: s.writes.len,
        });
    }
    let metrics = Metrics {
        methods: world.capsules.len() as u32,
        refs: (world.capsules.data().calls.len() + world.capsules.data().initializes.len()) as u32,
        components: comps.count as u32,
        catalogue_roots: world.roots.len() as u32,
        root_matrix_bytes: (comps.masks.len() * size_of::<u64>()) as u64,
        work: budget.work,
        charged_bytes: budget.bytes as u64,
    };
    debug_assert_eq!(comps.words, (world.roots.len() + 63) / 64);
    let mut result = Plan {
        binding: world.binding,
        input,
        decisions,
        metrics,
        seal: [0; 32],
    };
    result.seal = seal(&result);
    Ok(result)
}

fn sorted_unique<T: Ord>(values: &[T]) -> bool {
    values.windows(2).all(|w| w[0] < w[1])
}
fn validate_world(w: World<'_>) -> Result<(), Error> {
    let b = w.binding;
    if let AmbientCoverage::NoAdditionalRunnableEntries { contract } = w.ambient {
        if contract == [0; 32] {
            return Err(Error::Binding);
        }
    }
    if [
        b.producer,
        b.facts,
        b.graph,
        b.runtime,
        b.inputs,
        b.catalogue,
        b.contracts,
        b.member_authority,
        b.capsules,
    ]
    .contains(&[0; 32])
    {
        return Err(Error::Binding);
    }
    if w.roots.len() != b.root_count as usize || !w.roots.windows(2).all(|a| a[0].key < a[1].key) {
        return Err(Error::Catalogue);
    }
    if w.roots
        .iter()
        .any(|r| r.key == [0; 32] || r.method.0 as usize >= w.capsules.len())
    {
        return Err(Error::Catalogue);
    }
    if catalogue_identity(w.roots) != b.catalogue {
        return Err(Error::Catalogue);
    }
    if w.canonical_members.len() != w.capsules.bounds().members as usize {
        return Err(Error::Bounds);
    }
    if !sorted_unique(&w.changes.methods) || !sorted_unique(&w.changes.classes) {
        return Err(Error::Order);
    }
    if w.changes
        .methods
        .iter()
        .any(|m| m.0 as usize >= w.capsules.len())
        || w.changes
            .classes
            .iter()
            .any(|c| *c >= w.capsules.bounds().classes)
    {
        return Err(Error::Bounds);
    }
    // Canonical uniqueness is checked without an uncharged sorting allocation.
    // The verified codec imposes the same order. Never take the first of two
    // conflicting semantic subjects and silently prefer the narrower capsule.
    if !w.capsules.data().methods.windows(2).all(|m| {
        (m[0].subject.kind as u32, m[0].subject.index)
            < (m[1].subject.kind as u32, m[1].subject.index)
    }) {
        return Err(Error::Binding);
    }
    Ok(())
}

fn u32h(h: &mut Sha256, v: u32) {
    h.update(v.to_le_bytes());
}
fn u64h(h: &mut Sha256, v: u64) {
    h.update(v.to_le_bytes());
}
fn rangeh(h: &mut Sha256, r: Range) {
    u32h(h, r.start);
    u32h(h, r.len);
}
fn originh(h: &mut Sha256, o: Origin) {
    u32h(h, o.kind as u32);
    u32h(h, o.index);
}
fn valueh(h: &mut Sha256, v: ValueRef) {
    u32h(h, v.kind as u32);
    u32h(h, v.index);
}
fn storageh(h: &mut Sha256, s: StorageRef) {
    u32h(h, s.kind as u32);
    u32h(h, s.member);
    originh(h, s.base);
}
fn bindingh(h: &mut Sha256, b: WorldBinding) {
    for x in [
        b.producer,
        b.facts,
        b.graph,
        b.runtime,
        b.inputs,
        b.catalogue,
        b.contracts,
        b.member_authority,
        b.capsules,
    ] {
        h.update(x);
    }
    u32h(h, b.root_count);
}
pub fn catalogue_identity(roots: &[Root]) -> Identity {
    let mut h = Sha256::new();
    h.update(DOMAIN);
    h.update(b"catalogue\0");
    u64h(&mut h, roots.len() as u64);
    for r in roots {
        h.update(r.key);
        u32h(&mut h, r.method.0);
    }
    h.finalize().into()
}
fn input_identity(w: World<'_>) -> Result<Identity, Error> {
    let mut h = Sha256::new();
    h.update(DOMAIN);
    h.update(b"input\0");
    bindingh(&mut h, w.binding);
    u64h(&mut h, w.transport_bytes as u64);
    match w.ambient {
        AmbientCoverage::Unverified => u32h(&mut h, 0),
        AmbientCoverage::NoAdditionalRunnableEntries { contract } => {
            u32h(&mut h, 1);
            h.update(contract);
        }
    }
    let b = w.capsules.bounds();
    for x in [
        b.fact_nodes,
        b.foreign_methods,
        b.authorities,
        b.members,
        b.classes,
        b.exceptions,
        b.externals,
        b.sites,
        b.sams,
        b.adapters,
        b.bridge_proofs,
        b.phases,
    ] {
        u32h(&mut h, x);
    }
    let d = w.capsules.data();
    u64h(&mut h, d.methods.len() as u64);
    for m in &d.methods {
        for x in [
            m.subject.kind as u32,
            m.subject.index,
            m.authority,
            m.arity,
            m.captures,
            m.fresh_sites,
            m.locals,
            m.top.bits(),
        ] {
            u32h(&mut h, x);
        }
        for r in [
            m.calls,
            m.code_observations,
            m.reads,
            m.writes,
            m.escapes,
            m.initializes,
            m.throws,
            m.synchronizes,
            m.external,
            m.flows,
            m.creations,
            m.value_flows,
        ] {
            rangeh(&mut h, r);
        }
    }
    u64h(&mut h, d.calls.len() as u64);
    for c in &d.calls {
        u32h(&mut h, c.site);
        match c.target {
            CallTarget::Direct(target) => {
                u32h(&mut h, 0);
                u32h(&mut h, target.0);
            }
            CallTarget::Callable { value, sam } => {
                u32h(&mut h, 1);
                valueh(&mut h, value);
                u32h(&mut h, sam);
            }
        }
        u32h(&mut h, c.kind as u32);
        originh(&mut h, c.receiver);
        valueh(&mut h, c.receiver_value);
        u32h(&mut h, c.result);
        rangeh(&mut h, c.arguments);
        rangeh(&mut h, c.captures);
    }
    u64h(&mut h, d.origins.len() as u64);
    for &o in &d.origins {
        originh(&mut h, o);
    }
    u64h(&mut h, d.callable_values.len() as u64);
    for &v in &d.callable_values {
        valueh(&mut h, v);
    }
    u64h(&mut h, d.sam_arities.len() as u64);
    for &a in &d.sam_arities {
        u32h(&mut h, a);
    }
    u64h(&mut h, d.creations.len() as u64);
    for c in &d.creations {
        for v in [c.site, c.destination, c.implementation.0, c.sam] {
            u32h(&mut h, v);
        }
        originh(&mut h, c.receiver);
        valueh(&mut h, c.receiver_value);
        rangeh(&mut h, c.captures);
    }
    u64h(&mut h, d.callable_bridges.len() as u64);
    for b in &d.callable_bridges {
        for v in [b.creation, b.sam, b.implementation.0, b.proof] {
            u32h(&mut h, v);
        }
    }
    u64h(&mut h, d.value_flows.len() as u64);
    for f in &d.value_flows {
        u32h(&mut h, f.kind as u32);
        valueh(&mut h, f.value);
        u32h(&mut h, f.index);
    }
    u64h(&mut h, d.code_observations.len() as u64);
    for c in &d.code_observations {
        u32h(&mut h, c.kind as u32);
        u32h(&mut h, c.index);
    }
    u64h(&mut h, d.reads.len() as u64);
    for &s in &d.reads {
        storageh(&mut h, s);
    }
    u64h(&mut h, d.writes.len() as u64);
    for &s in &d.writes {
        storageh(&mut h, s);
    }
    u64h(&mut h, d.escapes.len() as u64);
    for e in &d.escapes {
        originh(&mut h, e.origin);
        u32h(&mut h, e.sink as u32);
        u32h(&mut h, e.index);
    }
    u64h(&mut h, d.initializes.len() as u64);
    for m in &d.initializes {
        u32h(&mut h, m.0);
    }
    u64h(&mut h, d.throws.len() as u64);
    for x in &d.throws {
        u32h(&mut h, *x);
    }
    u64h(&mut h, d.synchronizes.len() as u64);
    for s in &d.synchronizes {
        u32h(&mut h, s.kind as u32);
        originh(&mut h, s.base);
    }
    u64h(&mut h, d.external.len() as u64);
    for e in &d.external {
        u32h(&mut h, e.kind as u32);
        u32h(&mut h, e.key);
    }
    u64h(&mut h, d.flows.len() as u64);
    for f in &d.flows {
        originh(&mut h, f.source);
        u32h(&mut h, f.sink as u32);
        u32h(&mut h, f.via);
        u32h(&mut h, f.index);
    }
    u64h(&mut h, w.canonical_members.len() as u64);
    for c in w.canonical_members {
        h.update([u8::from(*c)]);
    }
    u64h(&mut h, w.changes.methods.len() as u64);
    for m in &w.changes.methods {
        u32h(&mut h, m.0);
    }
    u64h(&mut h, w.changes.classes.len() as u64);
    for c in &w.changes.classes {
        u32h(&mut h, *c);
    }
    Ok(h.finalize().into())
}
fn decisionsh(h: &mut Sha256, ds: &[RootDecision]) {
    u64h(h, ds.len() as u64);
    for d in ds {
        h.update(d.key);
        for x in [
            d.decision as u32,
            d.reason as u32,
            d.top.bits(),
            d.reachable_methods,
            d.reads,
            d.writes,
        ] {
            u32h(h, x);
        }
    }
}
fn seal(p: &Plan) -> Identity {
    let mut h = Sha256::new();
    h.update(DOMAIN);
    h.update(b"seal\0");
    bindingh(&mut h, p.binding);
    h.update(p.input);
    decisionsh(&mut h, &p.decisions);
    for x in [
        p.metrics.methods as u64,
        p.metrics.refs as u64,
        p.metrics.components as u64,
        p.metrics.catalogue_roots as u64,
        p.metrics.root_matrix_bytes,
        p.metrics.work,
        p.metrics.charged_bytes,
    ] {
        u64h(&mut h, x);
    }
    h.finalize().into()
}
fn pair_seal(p: &PairedPlan) -> Identity {
    let mut h = Sha256::new();
    h.update(DOMAIN);
    h.update(b"pair\0");
    h.update(p.base);
    h.update(p.head);
    decisionsh(&mut h, &p.decisions);
    h.finalize().into()
}

#[cfg(test)]
mod tests;
