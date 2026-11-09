//! Durable publication-barrier state, separate from completed-family reuse.
//!
//! Dense query IDs, versions and the runnable frontier survive exactly. Artifact
//! admission binds all logical program tables and semantic options. Worker count
//! and resource limits may change; a limit below the retained state is rejected.
pub mod inspection;
use super::*;
use selector_artifacts::{ArtifactKind, StreamingSection};
use sha2::{Digest, Sha256};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

const VERSION: u32 = 7;
const SECTION_COUNT: u32 = 26;
static NEXT_SAVE: AtomicU64 = AtomicU64::new(0);
const META_BYTES: usize = 424;
const WIDTHS: [usize; SECTION_COUNT as usize] = [
    META_BYTES, 4, 16, 4, 8, 40, 24, 28, 24, 20, 12, 16, 4, 4, 16, 4, 12, 28, 8, 16, 8, 4, 8, 12,
    4, 8,
];

fn section_count(version: u32) -> Option<u32> {
    match version {
        1 => Some(19),
        2 => Some(20),
        3 => Some(21),
        5 => Some(24),
        6 => Some(25),
        VERSION => Some(SECTION_COUNT),
        _ => None,
    }
}

fn artifact_error(error: selector_artifacts::Error) -> Error {
    Error::Message(error.to_string())
}
struct PublishedTemp(PathBuf);
impl Drop for PublishedTemp {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn section(id: u32, count: usize) -> Result<StreamingSection, Error> {
    let length = count
        .checked_mul(WIDTHS[id as usize - 1])
        .ok_or(Error::Limit("checkpoint section bytes"))?;
    Ok(StreamingSection {
        id,
        count: count as u64,
        length: length as u64,
    })
}

struct Encoder<'a>(&'a mut dyn Write);
impl Encoder<'_> {
    fn n(&mut self, n: u32) -> io::Result<()> {
        self.0.write_all(&n.to_le_bytes())
    }
    fn q(&mut self, n: u64) -> io::Result<()> {
        self.0.write_all(&n.to_le_bytes())
    }
    fn value(&mut self, value: Value) -> io::Result<()> {
        self.n(value.set.0)?;
        self.n(value.unknown)
    }
    fn slot(&mut self, slot: Slot) -> io::Result<()> {
        self.n(match slot.kind {
            SlotKind::Summary => 1,
            SlotKind::Field => 2,
            SlotKind::Capture => 3,
            SlotKind::Dispatch => 4,
            SlotKind::Body => 5,
            SlotKind::StaticField => 6,
            SlotKind::FieldWildcard => 7,
            SlotKind::FieldAll => 8,
            SlotKind::FieldMissing => 9,
        })?;
        self.n(slot.owner)?;
        self.n(slot.member)
    }
    fn atom(&mut self, atom: Atom) -> io::Result<()> {
        self.n(match atom.kind {
            AtomKind::Object => 1,
            AtomKind::Callback => 2,
            AtomKind::UpperBound => 3,
            AtomKind::Container => 4,
        })?;
        self.n(atom.site.0)?;
        self.n(atom.symbol.0)?;
        self.n(atom.binding)
    }
}

struct Decoder<'a> {
    bytes: &'a [u8],
    at: usize,
}
impl<'a> Decoder<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, at: 0 }
    }
    fn take<const N: usize>(&mut self) -> Result<[u8; N], Error> {
        let end = self
            .at
            .checked_add(N)
            .ok_or(Error::Invalid("checkpoint offset overflow"))?;
        let bytes = self
            .bytes
            .get(self.at..end)
            .ok_or(Error::Invalid("truncated checkpoint"))?;
        self.at = end;
        Ok(bytes.try_into().unwrap())
    }
    fn n(&mut self) -> Result<u32, Error> {
        Ok(u32::from_le_bytes(self.take()?))
    }
    fn q(&mut self) -> Result<u64, Error> {
        Ok(u64::from_le_bytes(self.take()?))
    }
    fn boolean(&mut self) -> Result<bool, Error> {
        match self.n()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(Error::Invalid("checkpoint boolean")),
        }
    }
    fn value(&mut self, pool: &ValuePool) -> Result<Value, Error> {
        let value = Value {
            set: SetId(self.n()?),
            unknown: self.n()?,
        };
        pool.validate_snapshot_value(value)?;
        Ok(value)
    }
    fn slot(&mut self, legacy: bool, operations: usize) -> Result<Slot, Error> {
        let kind = match self.n()? {
            1 => SlotKind::Summary,
            2 => SlotKind::Field,
            3 => SlotKind::Capture,
            4 => SlotKind::Dispatch,
            5 => SlotKind::Body,
            6 => SlotKind::StaticField,
            7 if !legacy => SlotKind::FieldWildcard,
            8 if !legacy => SlotKind::FieldAll,
            9 if !legacy => SlotKind::FieldMissing,
            _ => return Err(Error::Invalid("checkpoint slot kind")),
        };
        let mut slot = Slot {
            kind,
            owner: self.n()?,
            member: self.n()?,
        };
        // Legacy allocated fields merged every receiver at one site. The
        // read-only adapter preserves that coarse namespace explicitly.
        if legacy && slot.kind == SlotKind::Field && (slot.owner as usize) < operations {
            slot.kind = SlotKind::FieldAll;
        }
        Ok(slot)
    }
    fn done(&self) -> Result<(), Error> {
        if self.at == self.bytes.len() {
            Ok(())
        } else {
            Err(Error::Invalid("checkpoint trailing bytes"))
        }
    }
}

fn stop_tag(reason: Option<StopReason>) -> u32 {
    match reason {
        None => 0,
        Some(StopReason::ContextLimit) => 1,
        Some(StopReason::StepLimit) => 2,
        Some(StopReason::MemoryLimit) => 3,
        Some(StopReason::AllocationLimit) => 4,
        Some(StopReason::Cancelled) => 5,
        Some(StopReason::CheckpointRequested) => 6,
    }
}
fn read_stop(tag: u32) -> Result<Option<StopReason>, Error> {
    Ok(match tag {
        0 => None,
        1 => Some(StopReason::ContextLimit),
        2 => Some(StopReason::StepLimit),
        3 => Some(StopReason::MemoryLimit),
        4 => Some(StopReason::AllocationLimit),
        5 => Some(StopReason::Cancelled),
        6 => Some(StopReason::CheckpointRequested),
        _ => return Err(Error::Invalid("checkpoint stop reason")),
    })
}
fn policy(options: &SolveOptions) -> (u32, u64) {
    match options.context_policy {
        ContextPolicy::Exact => (0, 0),
        ContextPolicy::BoundedArguments {
            max_variants_per_receiver,
        } => (1, max_variants_per_receiver as u64),
    }
}
fn root_identity(options: &SolveOptions) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"selector-continuation-execution-roots/v1");
    match &options.execution_roots {
        None => h.update([0]),
        Some(roots) => {
            h.update([1]);
            h.update((roots.len() as u64).to_le_bytes());
            for root in roots.iter() {
                h.update(root.node.0.to_le_bytes());
                h.update(root.receiver.0.to_le_bytes());
            }
        }
    }
    h.finalize().into()
}

fn check_index(index: u32, len: usize, message: &'static str) -> Result<(), Error> {
    if index as usize >= len {
        Err(Error::Invalid(message))
    } else {
        Ok(())
    }
}
fn check_version(version: u64) -> Result<(), Error> {
    if version >= u64::MAX / 2 {
        Err(Error::Invalid("checkpoint version overflow"))
    } else {
        Ok(())
    }
}
fn check_slot(s: &QuerySession<'_>, slot: Slot, families: usize) -> Result<(), Error> {
    let member = slot.member == u32::MAX || (slot.member as usize) < s.facts.symbols.len();
    let root_or_exact = (slot.owner as usize) >= s.facts.operations.len()
        && (slot.owner < s.heap_owners.base() || s.heap_owners.key(slot.owner).is_some());
    let site = (slot.owner as usize) < s.facts.operations.len()
        && s.facts.operations[slot.owner as usize]
            .opcode
            .is_heap_site();
    let valid = match slot.kind {
        SlotKind::Summary => (slot.owner as usize) < s.contexts.len() && slot.member == 0,
        SlotKind::Capture => (slot.owner as usize) < families && slot.member == 0,
        SlotKind::Field => (slot.owner == u32::MAX || root_or_exact) && member,
        SlotKind::FieldWildcard | SlotKind::FieldAll => site && member,
        SlotKind::FieldMissing => (site || root_or_exact) && member,
        SlotKind::StaticField => (slot.owner as usize) < s.facts.symbols.len() && slot.member == 0,
        SlotKind::Body | SlotKind::Dispatch => {
            (slot.owner as usize) < s.graph.nodes.len() && slot.member == 0
        }
    };
    if valid {
        Ok(())
    } else {
        Err(Error::Invalid("checkpoint slot reference"))
    }
}
fn check_atom(
    s: &QuerySession<'_>,
    atom: Atom,
    families: usize,
    legacy: bool,
) -> Result<(), Error> {
    check_index(
        atom.symbol.0,
        s.facts.symbols.len(),
        "checkpoint atom symbol",
    )?;
    if !atom.site.is_none() {
        check_index(
            atom.site.0,
            s.facts.operations.len(),
            "checkpoint atom operation",
        )?;
    }
    match atom.kind {
        AtomKind::Object => {
            if atom.site.is_none() {
                return if atom.binding == 0 {
                    Ok(())
                } else {
                    Err(Error::Invalid("checkpoint root object origin"))
                };
            }
            if s.facts.operations[atom.site.index()].opcode != Opcode::Allocate {
                return Err(Error::Invalid("checkpoint object constructor operation"));
            }
            if s.types.global_module_owner(atom.symbol) == Some(atom.symbol)
                && !(legacy && atom.binding == 0)
            {
                return Err(Error::Invalid("checkpoint module object identity"));
            }
            if let Some(root) = binding_root(atom.binding) {
                check_index(
                    root.0,
                    s.facts.symbols.len(),
                    "checkpoint object root origin",
                )?;
            }
            Ok(())
        }
        AtomKind::Container => validate_container_atom(s.facts, atom),
        AtomKind::Callback if !atom.site.is_none() && (atom.binding as usize) < families => Ok(()),
        AtomKind::UpperBound
            if atom.binding == 0 && s.facts.result_bound(atom.symbol, atom.site).is_some() =>
        {
            Ok(())
        }
        _ => Err(Error::Invalid("checkpoint atom identity")),
    }
}
fn family_value(s: &QuerySession<'_>, value: Value) -> Result<(), Error> {
    if s.pool
        .members(value)
        .iter()
        .any(|atom| atom.kind == AtomKind::Callback && atom.binding != 0)
    {
        return Err(Error::Invalid("checkpoint normalized closure family"));
    }
    Ok(())
}

fn check_heap_aggregates(s: &mut QuerySession<'_>) -> Result<(), Error> {
    let mut contributions = Vec::<(Slot, Value)>::new();
    contributions
        .try_reserve_exact(s.slots.len())
        .map_err(|_| Error::Limit("checkpoint heap aggregate validation"))?;
    for (slot, value) in &s.slots {
        let site = match slot.kind {
            SlotKind::Field => s.heap_owners.key(slot.owner).map(|key| key.site),
            SlotKind::FieldWildcard => Some(OperationId(slot.owner)),
            SlotKind::FieldMissing => {
                if value.value
                    != (Value {
                        set: SetId(0),
                        unknown: UNKNOWN_FIELD,
                    })
                    || value.version != 1
                {
                    return Err(Error::Invalid("checkpoint missing field marker"));
                }
                None
            }
            _ => None,
        };
        if let Some(site) = site {
            let aggregate = Slot {
                kind: SlotKind::FieldAll,
                owner: site.0,
                member: slot.member,
            };
            contributions.push((aggregate, value.value));
        }
    }
    contributions.sort_unstable_by_key(|(slot, _)| *slot);
    let mut members = Vec::new();
    let mut at = 0;
    let mut aggregates = 0;
    while at < contributions.len() {
        let slot = contributions[at].0;
        let actual = s
            .slots
            .get(&slot)
            .ok_or(Error::Invalid("checkpoint missing heap aggregate"))?
            .value;
        members.clear();
        let mut unknown = 0;
        while at < contributions.len() && contributions[at].0 == slot {
            let value = contributions[at].1;
            let unbounded = unknown != 0 && unknown & UNKNOWN_TYPED == 0;
            unknown = (unknown | value.unknown) & !UNKNOWN_TYPED;
            if unknown != 0 && !unbounded && !value.is_unbounded() {
                unknown |= UNKNOWN_TYPED;
            }
            if unknown & WIDENED_VALUE != 0 {
                members.clear();
                unknown &= !UNKNOWN_TYPED;
            } else {
                let incoming = s.pool.members(value);
                members
                    .try_reserve(incoming.len())
                    .map_err(|_| Error::Limit("checkpoint heap aggregate validation"))?;
                members.extend_from_slice(incoming);
                members.sort_unstable();
                members.dedup();
                if members.len() > s.options.max_set_members {
                    members.clear();
                    unknown = (unknown | WIDENED_VALUE) & !UNKNOWN_TYPED;
                }
            }
            at += 1;
        }
        if actual.unknown != unknown || s.pool.members(actual) != members {
            return Err(Error::Invalid("checkpoint heap aggregate"));
        }
        aggregates += 1;
    }
    if aggregates
        != s.slots
            .keys()
            .filter(|slot| slot.kind == SlotKind::FieldAll)
            .count()
    {
        return Err(Error::Invalid("checkpoint extra heap aggregate"));
    }
    drop(members);
    drop(contributions);
    s.rebuild_heap_aggregates()
}

fn intern_checkpoint_shape(
    s: &mut QuerySession<'_>,
    arity: u32,
    atoms: &[CallbackShapeAtom],
    artifact_bytes: usize,
    scratch_bytes: usize,
) -> Result<CallbackShapeId, Error> {
    let other_owned = s
        .owned_bytes()
        .checked_sub(s.callback_shapes.owned_bytes())
        .and_then(|n| n.checked_add(artifact_bytes))
        .and_then(|n| n.checked_add(scratch_bytes))
        .ok_or(Error::Limit("checkpoint callback shape memory"))?;
    let allowance = s
        .options
        .memory_budget_bytes
        .checked_sub(other_owned)
        .ok_or(Error::Limit("checkpoint callback shape memory"))?;
    s.callback_shapes
        .intern_rows_bounded(arity, atoms, allowance)
}

impl<'a> QuerySession<'a> {
    /// Publish a durable checkpoint while the coordinator is at a barrier.
    /// Workers have joined before this shared borrow can be obtained. Encoding
    /// streams existing owners twice for length/digest validation, with no query
    /// clone, per-record allocation, or retained previous session.
    pub fn save_checkpoint(
        &self,
        path: &Path,
        producer: ContentHash,
    ) -> Result<ContentHash, Error> {
        if path.file_name().is_none() {
            return Err(Error::Invalid("checkpoint path"));
        }
        let parent = path
            .parent()
            .filter(|path| !path.as_os_str().is_empty())
            .unwrap_or(Path::new("."));
        let temp = parent.join(format!(
            ".selector-checkpoint-{}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos(),
            NEXT_SAVE.fetch_add(1, Ordering::Relaxed)
        ));
        let atoms = self
            .pool
            .snapshot_sets()
            .map(<[Atom]>::len)
            .try_fold(0usize, |n, x| n.checked_add(x))
            .ok_or(Error::Limit("checkpoint atoms"))?;
        let frame_values = self
            .frames
            .snapshot_frames()
            .map(<[Value]>::len)
            .try_fold(0usize, |n, x| n.checked_add(x))
            .ok_or(Error::Limit("checkpoint frame values"))?;
        let shape_atoms = self
            .callback_shapes
            .snapshot_shapes()
            .map(|shape| shape.atoms.len())
            .try_fold(0usize, |n, len| n.checked_add(len))
            .ok_or(Error::Limit("checkpoint callback shape atoms"))?;
        let counts = [
            1,
            self.pool.len(),
            atoms,
            self.frames.len(),
            frame_values,
            self.contexts.len(),
            self.calls.len(),
            self.slots.len(),
            self.captures.len(),
            self.closure_families.len(),
            self.field_reads.len(),
            self.writes.len(),
            self.ready.len(),
            self.roots.len(),
            self.issues.len(),
            self.issue_contexts.len(),
            self.dependencies.snapshot_contexts().len(),
            self.dependencies.snapshot_reads().count(),
            self.pending_roots.len(),
            self.runtime_issue_sites.len(),
            self.heap_owners.rows().len(),
            self.contexts.len(),
            self.callback_shapes.len(),
            shape_atoms,
            self.contexts.len(),
            self.closure_families.len(),
        ];
        let mut sections = Vec::with_capacity(counts.len());
        for (index, count) in counts.into_iter().enumerate() {
            sections.push(section(index as u32 + 1, count)?);
        }
        let seal = cache::continuation_content_seal(self.facts, self.graph);
        let identity = selector_artifacts::write_streaming(
            &temp,
            ArtifactKind::Continuation,
            &sections,
            |id, writer| {
                let mut w = Encoder(writer);
                match id {
                    1 => {
                        w.n(VERSION)?;
                        for hash in [
                            producer.0,
                            self.facts.identity.0,
                            self.graph.identity.0,
                            seal,
                        ] {
                            w.0.write_all(&hash)?;
                        }
                        w.q(self.options.max_set_members as u64)?;
                        w.q(self.options.quantum as u64)?;
                        let (tag, limit) = policy(&self.options);
                        w.n(tag)?;
                        w.q(limit)?;
                        w.0.write_all(&root_identity(&self.options))?;
                        w.n(match self.completion {
                            Completion::Complete => 0,
                            Completion::Conservative => 1,
                            Completion::ResourceLimited => 2,
                        })?;
                        w.n(u32::from(self.sealed))?;
                        w.n(stop_tag(self.stop_reason))?;
                        w.q(self.rounds)?;
                        w.q(self.dependencies.epoch())?;
                        let m = self.metrics;
                        for n in [
                            m.states,
                            m.edge_visits,
                            m.novel_facts,
                            m.repeated_facts,
                            m.summary_hits,
                            m.invalidations,
                            m.queued_peak,
                            m.owned_bytes,
                            m.workers as u64,
                            m.elapsed_ns,
                        ] {
                            w.q(n)?;
                        }
                        for n in [
                            self.reuse.loaded_families,
                            self.reuse.rejected_families,
                            self.reuse.loaded_contexts,
                        ] {
                            w.q(n)?;
                        }
                        w.n(u32::from(self.reuse.same_snapshot))?;
                        let c = self.counters;
                        for n in [
                            c.contexts,
                            c.context_hits,
                            c.evaluations,
                            c.reevaluations,
                            c.novel_publications,
                            c.repeated_publications,
                            c.dispatch_targets,
                            c.callback_targets,
                            c.operations,
                            c.pending,
                            c.owned_bytes,
                            c.widened_contexts,
                        ] {
                            w.q(n)?;
                        }
                    }
                    2 => {
                        for atoms in self.pool.snapshot_sets() {
                            w.n(atoms.len() as u32)?;
                        }
                    }
                    3 => {
                        for atoms in self.pool.snapshot_sets() {
                            for atom in atoms {
                                w.atom(*atom)?;
                            }
                        }
                    }
                    4 => {
                        for values in self.frames.snapshot_frames() {
                            w.n(values.len() as u32)?;
                        }
                    }
                    5 => {
                        for values in self.frames.snapshot_frames() {
                            for value in values {
                                w.value(*value)?;
                            }
                        }
                    }
                    6 => {
                        for c in &self.contexts {
                            w.n(c.key.node.0)?;
                            w.value(c.key.receiver)?;
                            w.n(c.key.arguments.0)?;
                            w.value(c.value)?;
                            w.q(c.version)?;
                            w.n(u32::from(c.evaluated))?;
                            w.n(u32::from(c.widened))?;
                        }
                    }
                    25 => {
                        for context in &self.contexts {
                            w.n(u32::from(context.effects_open))?;
                        }
                    }
                    7 => {
                        for c in &self.calls {
                            for n in [
                                c.source.0,
                                c.target.0,
                                c.operation.0,
                                c.kind as u32,
                                c.edge.0,
                                c.binding,
                            ] {
                                w.n(n)?;
                            }
                        }
                    }
                    8 => {
                        for (slot, value) in &self.slots {
                            w.slot(*slot)?;
                            w.value(value.value)?;
                            w.q(value.version)?;
                        }
                    }
                    9 => {
                        for (binding, capture) in &self.captures {
                            w.n(*binding)?;
                            w.value(capture.receiver)?;
                            w.n(capture.arguments.0)?;
                            w.q(capture.version)?;
                        }
                    }
                    10 => {
                        for (family, binding) in &self.closure_families {
                            w.n(family.site.0)?;
                            w.value(family.receiver)?;
                            w.n(family.arguments.0)?;
                            w.n(*binding)?;
                        }
                    }
                    11 => {
                        for slot in &self.field_reads {
                            w.slot(*slot)?;
                        }
                    }
                    12 => {
                        for (context, slot) in &self.writes {
                            w.n(context.0)?;
                            w.slot(*slot)?;
                        }
                    }
                    13 => {
                        for id in &self.ready {
                            w.n(id.0)?;
                        }
                    }
                    14 => {
                        for id in &self.roots {
                            w.n(id.0)?;
                        }
                    }
                    15 => {
                        for issue in &self.issues {
                            for n in [
                                issue.kind as u32,
                                issue.file.0,
                                issue.symbol.0,
                                issue.detail.0,
                            ] {
                                w.n(n)?;
                            }
                        }
                    }
                    16 => {
                        for context in &self.issue_contexts {
                            w.n(context.0)?;
                        }
                    }
                    17 => {
                        for (generation, invalid) in self.dependencies.snapshot_contexts() {
                            w.q(generation)?;
                            w.n(u32::from(invalid))?;
                        }
                    }
                    18 => {
                        for (context, read) in self.dependencies.snapshot_reads() {
                            w.n(context.0)?;
                            w.slot(read.slot)?;
                            w.q(read.version)?;
                            w.n(u32::from(read.present))?;
                        }
                    }
                    19 => {
                        for root in &self.pending_roots {
                            w.n(root.node.0)?;
                            w.n(root.receiver.0)?;
                        }
                    }
                    20 => {
                        for (context, site) in &self.runtime_issue_sites {
                            w.n(context.0)?;
                            w.n(site.kind as u32)?;
                            w.n(site.operation.0)?;
                            w.n(site.reason as u32)?;
                        }
                    }
                    21 => {
                        for owner in self.heap_owners.rows() {
                            w.n(owner.site.0)?;
                            w.n(owner.root.0)?;
                        }
                    }
                    22 => {
                        for context in &self.contexts {
                            w.n(context.callback_shape.0)?;
                        }
                    }
                    23 => {
                        for shape in self.callback_shapes.snapshot_shapes() {
                            w.n(shape.arity)?;
                            w.n(shape.atoms.len() as u32)?;
                        }
                    }
                    24 => {
                        for shape in self.callback_shapes.snapshot_shapes() {
                            for atom in shape.atoms {
                                w.n(atom.argument)?;
                                w.n(atom.site.0)?;
                                w.n(atom.symbol.0)?;
                            }
                        }
                    }
                    26 => {
                        // Same immutable iteration order as section 10.
                        for family in self.closure_families.keys() {
                            w.value(family.origins)?;
                        }
                    }
                    _ => {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidInput,
                            "checkpoint section",
                        ));
                    }
                }
                Ok(())
            },
        )
        .map_err(artifact_error)?;
        // Logical checkpoint names are mutable publication pointers, unlike
        // immutable cache artifact names. Replace their inode atomically, never
        // truncate bytes an in-flight owned reader may still be consuming.
        let published = PublishedTemp(temp);
        std::fs::rename(&published.0, path)?;
        std::fs::File::open(parent)?.sync_all()?;
        Ok(ContentHash(identity))
    }

    /// Restore exact paused state. This deliberately bypasses completed-family
    /// cache admission. Call `resume` to continue with the new resource limits.
    pub fn from_checkpoint(
        facts: &'a FactSnapshot,
        graph: &'a ProgramGraph,
        options: &SolveOptions,
        runtime: &SolverRuntime,
        path: &Path,
        producer: ContentHash,
    ) -> Result<Self, Error> {
        Self::restore_checkpoint(facts, graph, options, runtime, path, producer, None, None)
    }

    // The recorded-root override is confined to this module and its read-only
    // inspector. Public resumable admission always compares caller roots.
    fn restore_checkpoint(
        facts: &'a FactSnapshot,
        graph: &'a ProgramGraph,
        options: &SolveOptions,
        runtime: &SolverRuntime,
        path: &Path,
        producer: ContentHash,
        admitted_artifact: Option<selector_artifacts::Artifact>,
        inspection_roots: Option<[u8; 32]>,
    ) -> Result<Self, Error> {
        // Only the read-only child view may inspect the prior compatible
        // layout. It cannot expose this private session for resume or caching.
        let inspection = admitted_artifact.is_some() && inspection_roots.is_some();
        let mut s = Self::with_runtime_unrestored(facts, graph, options, runtime)?;
        let available = options
            .memory_budget_bytes
            .checked_sub(s.owned_bytes())
            .ok_or(Error::Limit("checkpoint admission memory"))?;
        let artifact = if let Some(artifact) = admitted_artifact {
            if artifact.byte_len() > available {
                return Err(Error::Limit("checkpoint admission memory"));
            }
            artifact
        } else {
            selector_artifacts::open_bounded(path, ArtifactKind::Continuation, available as u64)
                .map_err(artifact_error)?
        };
        let wire_version = Decoder::new(artifact.section(1).map_err(artifact_error)?).n()?;
        let legacy = inspection && matches!(wire_version, 1 | 2);
        let prior_shapes = inspection && wire_version == 3;
        let prior_effects = inspection && wire_version == 5;
        let prior_origins = inspection && wire_version == 6;
        let has_shapes = wire_version >= 5;
        let has_effects = wire_version >= 6;
        if wire_version != VERSION && !legacy && !prior_shapes && !prior_effects && !prior_origins {
            return Err(Error::Invalid("checkpoint version"));
        }
        let sections = section_count(wire_version).ok_or(Error::Invalid("checkpoint version"))?;
        if artifact.section_ids().ne(1..=sections) {
            return Err(Error::Invalid("checkpoint section inventory"));
        }
        let mut counts = [0usize; SECTION_COUNT as usize];
        for (i, width) in WIDTHS.into_iter().take(sections as usize).enumerate() {
            let id = i as u32 + 1;
            let count = usize::try_from(artifact.count(id).map_err(artifact_error)?)
                .map_err(|_| Error::Invalid("checkpoint count overflow"))?;
            if count.checked_mul(width) != Some(artifact.section(id).map_err(artifact_error)?.len())
            {
                return Err(Error::Invalid("checkpoint section count or width"));
            }
            counts[i] = count;
        }
        if counts[0] != 1
            || counts[1] == 0
            || counts[3] == 0
            || counts[16] > counts[5]
            || counts[19] > counts[15]
            || counts[9] >= LOCAL_BINDING as usize
            || (has_shapes && (counts[21] != counts[5] || counts[22] == 0))
            || (has_effects && counts[24] != counts[5])
            || (wire_version == VERSION && counts[25] != counts[9])
            || s.heap_owners
                .base()
                .checked_add(counts[20] as u32)
                .is_none_or(|end| end > LOCAL_HEAP_OWNER)
            || counts.iter().skip(1).any(|n| *n >= u32::MAX as usize)
        {
            return Err(Error::Invalid("checkpoint table inventory"));
        }
        if counts[5] > options.max_contexts {
            return Err(Error::Limit("checkpoint retained context limit"));
        }
        // Conservative peak charge includes decoded tables/hash indexes, the
        // verified byte owner, and one reused largest-row scratch buffer. This
        // precedes all input-sized reservations; actual ownership is checked too.
        let weights = [
            0usize, 80, 64, 80, 32, 256, 160, 160, 128, 128, 64, 64, 8, 32, 64, 32, 32, 256, 16,
            64, 64, 8, 80, 48, 8, 8,
        ];
        let mut peak = s
            .owned_bytes()
            .checked_add(artifact.byte_len())
            .ok_or(Error::Limit("checkpoint admission memory"))?;
        for (count, weight) in counts.into_iter().zip(weights) {
            peak = peak
                .checked_add(
                    count
                        .checked_mul(weight)
                        .ok_or(Error::Limit("checkpoint admission memory"))?,
                )
                .ok_or(Error::Limit("checkpoint admission memory"))?;
        }
        if peak > options.memory_budget_bytes {
            return Err(Error::Limit("checkpoint admission memory"));
        }
        let bytes = |id| artifact.section(id).map_err(artifact_error);
        let mut r = Decoder::new(bytes(1)?);
        if r.n()? != wire_version {
            return Err(Error::Invalid("checkpoint version"));
        }
        if r.take::<32>()? != producer.0 {
            return Err(Error::Invalid("checkpoint producer"));
        }
        if r.take::<32>()? != facts.identity.0 || r.take::<32>()? != graph.identity.0 {
            return Err(Error::Invalid("checkpoint snapshot identity"));
        }
        if r.take::<32>()? != cache::continuation_content_seal(facts, graph) {
            return Err(Error::Invalid("checkpoint snapshot content seal"));
        }
        let expected_policy = policy(options);
        if r.q()? != options.max_set_members as u64
            || r.q()? != options.quantum as u64
            || r.n()? != expected_policy.0
            || r.q()? != expected_policy.1
        {
            return Err(Error::Invalid("checkpoint semantic options"));
        }
        if r.take::<32>()? != inspection_roots.unwrap_or_else(|| root_identity(options)) {
            return Err(Error::Invalid("checkpoint execution roots"));
        }
        s.completion = match r.n()? {
            0 => Completion::Complete,
            1 => Completion::Conservative,
            2 => Completion::ResourceLimited,
            _ => return Err(Error::Invalid("checkpoint completion")),
        };
        s.sealed = r.boolean()?;
        s.stop_reason = read_stop(r.n()?)?;
        s.rounds = r.q()?;
        check_version(s.rounds)?;
        s.dependencies.restore_epoch(r.q()?)?;
        s.metrics = AnalysisMetrics {
            states: r.q()?,
            edge_visits: r.q()?,
            novel_facts: r.q()?,
            repeated_facts: r.q()?,
            summary_hits: r.q()?,
            invalidations: r.q()?,
            queued_peak: r.q()?,
            owned_bytes: r.q()?,
            workers: usize::try_from(r.q()?).map_err(|_| Error::Invalid("checkpoint workers"))?,
            elapsed_ns: r.q()?,
        };
        s.metrics.workers = runtime.workers();
        s.reuse = ReuseMetrics {
            loaded_families: r.q()?,
            rejected_families: r.q()?,
            loaded_contexts: r.q()?,
            same_snapshot: r.boolean()?,
        };
        s.counters = WorkCounters {
            contexts: r.q()?,
            context_hits: r.q()?,
            evaluations: r.q()?,
            reevaluations: r.q()?,
            novel_publications: r.q()?,
            repeated_publications: r.q()?,
            dispatch_targets: r.q()?,
            callback_targets: r.q()?,
            operations: r.q()?,
            pending: r.q()?,
            owned_bytes: r.q()?,
            widened_contexts: r.q()?,
        };
        for counter in [
            s.metrics.states,
            s.metrics.edge_visits,
            s.metrics.novel_facts,
            s.metrics.repeated_facts,
            s.metrics.summary_hits,
            s.metrics.invalidations,
            s.metrics.queued_peak,
            s.metrics.elapsed_ns,
            s.counters.evaluations,
            s.counters.reevaluations,
            s.counters.novel_publications,
            s.counters.repeated_publications,
            s.counters.dispatch_targets,
            s.counters.callback_targets,
            s.counters.widened_contexts,
        ] {
            check_version(counter)?;
        }
        r.done()?;

        macro_rules! reserve {
            ($field:ident, $count:expr) => {
                s.$field
                    .try_reserve($count)
                    .map_err(|_| Error::Limit("checkpoint table allocation"))?;
            };
        }
        reserve!(calls, counts[6]);
        reserve!(call_index, counts[6]);
        reserve!(slots, counts[7]);
        reserve!(captures, counts[8]);
        reserve!(closure_families, counts[9]);
        reserve!(field_reads, counts[10]);
        reserve!(writes, counts[11]);
        reserve!(ready, counts[12]);
        reserve!(roots, counts[13]);
        reserve!(issues, counts[14]);
        reserve!(issue_index, counts[14]);
        reserve!(issue_contexts, counts[15]);
        reserve!(pending_roots, counts[18]);
        reserve!(runtime_issue_sites, counts[19]);

        // Restore dense owner IDs before admitting atoms or slots referring to
        // them. Interning must append each distinct key in its recorded order.
        if !legacy {
            let mut r = Decoder::new(bytes(21)?);
            for id in 0..counts[20] {
                let key = HeapOwnerKey {
                    site: OperationId(r.n()?),
                    root: SymbolId(r.n()?),
                };
                check_index(
                    key.site.0,
                    facts.operations.len(),
                    "checkpoint heap owner operation",
                )?;
                check_index(
                    key.root.0,
                    facts.symbols.len(),
                    "checkpoint heap owner root",
                )?;
                if !facts.operations[key.site.index()].opcode.is_heap_site() {
                    return Err(Error::Invalid(
                        "checkpoint heap owner constructor operation",
                    ));
                }
                if s.heap_owners.intern(key)? != s.heap_owners.base() + id as u32 {
                    return Err(Error::Invalid("checkpoint duplicate heap owner"));
                }
            }
            r.done()?;
        }

        let mut lengths = Decoder::new(bytes(2)?);
        let mut records = Decoder::new(bytes(3)?);
        let mut atom_scratch = Vec::new();
        for id in 0..counts[1] {
            let len = lengths.n()? as usize;
            if len > options.max_set_members || len > counts[2] {
                return Err(Error::Invalid("checkpoint set length"));
            }
            atom_scratch.clear();
            atom_scratch
                .try_reserve(len)
                .map_err(|_| Error::Limit("checkpoint atom scratch"))?;
            for _ in 0..len {
                let kind = match records.n()? {
                    1 => AtomKind::Object,
                    2 => AtomKind::Callback,
                    3 => AtomKind::UpperBound,
                    4 if wire_version >= 5 => AtomKind::Container,
                    _ => return Err(Error::Invalid("checkpoint atom kind")),
                };
                let atom = Atom {
                    kind,
                    site: OperationId(records.n()?),
                    symbol: SymbolId(records.n()?),
                    binding: records.n()?,
                };
                if legacy && atom.kind == AtomKind::Object && atom.binding != 0 {
                    return Err(Error::Invalid("checkpoint legacy object origin"));
                }
                check_atom(&s, atom, counts[9], legacy)?;
                atom_scratch.push(atom);
            }
            s.pool.restore_set(SetId(id as u32), &atom_scratch)?;
        }
        lengths.done()?;
        records.done()?;
        drop(atom_scratch);
        let mut lengths = Decoder::new(bytes(4)?);
        let mut records = Decoder::new(bytes(5)?);
        let mut value_scratch = Vec::new();
        for id in 0..counts[3] {
            let len = lengths.n()? as usize;
            if len > counts[4] {
                return Err(Error::Invalid("checkpoint frame length"));
            }
            value_scratch.clear();
            value_scratch
                .try_reserve(len)
                .map_err(|_| Error::Limit("checkpoint frame scratch"))?;
            for _ in 0..len {
                value_scratch.push(records.value(&s.pool)?);
            }
            s.frames.restore_frame(FrameId(id as u32), &value_scratch)?;
        }
        lengths.done()?;
        records.done()?;
        drop(value_scratch);

        if has_shapes {
            let mut lengths = Decoder::new(bytes(23)?);
            let mut records = Decoder::new(bytes(24)?);
            let mut shape_scratch = Vec::new();
            for id in 0..counts[22] {
                let arity = lengths.n()?;
                let len = lengths.n()? as usize;
                if len > counts[23] {
                    return Err(Error::Invalid("checkpoint callback shape length"));
                }
                shape_scratch.clear();
                let scratch_bytes = shape_scratch
                    .capacity()
                    .max(len)
                    .checked_mul(std::mem::size_of::<CallbackShapeAtom>())
                    .and_then(|n| n.checked_add(artifact.byte_len()))
                    .and_then(|n| n.checked_add(s.owned_bytes()))
                    .ok_or(Error::Limit("checkpoint callback shape scratch memory"))?;
                if scratch_bytes > options.memory_budget_bytes {
                    return Err(Error::Limit("checkpoint callback shape scratch memory"));
                }
                shape_scratch
                    .try_reserve_exact(len)
                    .map_err(|_| Error::Limit("checkpoint callback shape scratch"))?;
                for _ in 0..len {
                    let atom = CallbackShapeAtom {
                        argument: records.n()?,
                        site: OperationId(records.n()?),
                        symbol: SymbolId(records.n()?),
                    };
                    if atom.argument >= arity || atom.site.is_none() != atom.symbol.is_none() {
                        return Err(Error::Invalid("checkpoint callback shape atom"));
                    }
                    if !atom.site.is_none() {
                        check_index(
                            atom.site.0,
                            facts.operations.len(),
                            "checkpoint callback shape operation",
                        )?;
                        check_index(
                            atom.symbol.0,
                            facts.symbols.len(),
                            "checkpoint callback shape symbol",
                        )?;
                        let operation = facts.operations[atom.site.index()];
                        if operation.opcode != Opcode::BindCallback
                            || operation.target != atom.symbol
                        {
                            return Err(Error::Invalid("checkpoint callback shape code"));
                        }
                    }
                    shape_scratch.push(atom);
                }
                if shape_scratch.windows(2).any(|pair| pair[0] >= pair[1]) {
                    return Err(Error::Invalid("checkpoint callback shape ordering"));
                }
                let scratch_bytes = shape_scratch
                    .capacity()
                    .checked_mul(std::mem::size_of::<CallbackShapeAtom>())
                    .ok_or(Error::Limit("checkpoint callback shape scratch memory"))?;
                if intern_checkpoint_shape(
                    &mut s,
                    arity,
                    &shape_scratch,
                    artifact.byte_len(),
                    scratch_bytes,
                )? != CallbackShapeId(id as u32)
                {
                    return Err(Error::Invalid("checkpoint duplicate callback shape"));
                }
            }
            lengths.done()?;
            records.done()?;
        }
        let mut context_shapes = if has_shapes {
            Some(Decoder::new(bytes(22)?))
        } else {
            None
        };
        let mut context_effects = if has_effects {
            Some(Decoder::new(bytes(25)?))
        } else {
            None
        };
        let mut r = Decoder::new(bytes(6)?);
        s.contexts
            .try_reserve_exact(counts[5])
            .map_err(|_| Error::Limit("checkpoint contexts"))?;
        s.index
            .try_reserve(counts[5])
            .map_err(|_| Error::Limit("checkpoint context index"))?;
        for id in 0..counts[5] {
            let node = NodeId(r.n()?);
            check_index(node.0, graph.nodes.len(), "checkpoint context node")?;
            let receiver = r.value(&s.pool)?;
            let arguments = FrameId(r.n()?);
            check_index(arguments.0, s.frames.len(), "checkpoint context frame")?;
            let value = r.value(&s.pool)?;
            let version = r.q()?;
            check_version(version)?;
            let evaluated = r.boolean()?;
            let widened = r.boolean()?;
            // Older read-only snapshots never certified executable effects.
            let effects_open = context_effects
                .as_mut()
                .map_or(Ok(true), Decoder::boolean)?;
            if evaluated != (version != 0) {
                return Err(Error::Invalid("checkpoint context evaluation version"));
            }
            let key = ContextKey {
                node,
                receiver,
                arguments,
            };
            // Prior read-only schemas have no immutable creation shape. Zero
            // is a descriptive placeholder, never an inferred resume identity.
            let callback_shape = if let Some(shapes) = &mut context_shapes {
                let shape = CallbackShapeId(shapes.n()?);
                check_index(
                    shape.0,
                    s.callback_shapes.len(),
                    "checkpoint context callback shape",
                )?;
                match options.context_policy {
                    ContextPolicy::Exact if shape != CallbackShapeId(0) => {
                        return Err(Error::Invalid("checkpoint exact context callback shape"));
                    }
                    ContextPolicy::BoundedArguments { .. } => {
                        let arguments = s.frames.get(arguments);
                        if s.callback_shapes.get(shape).arity as usize != arguments.len() {
                            return Err(Error::Invalid("checkpoint context callback shape arity"));
                        }
                        if !widened && s.callback_shapes.lookup(&s.pool, arguments) != Some(shape) {
                            return Err(Error::Invalid(
                                "checkpoint context callback shape identity",
                            ));
                        }
                    }
                    _ => {}
                }
                shape
            } else {
                CallbackShapeId(0)
            };
            let context = Context {
                key,
                callback_shape,
                value,
                version,
                evaluated,
                widened,
                effects_open,
            };
            if is_static_initializer(facts, graph, node)
                && (receiver != Value::EMPTY || arguments != FrameId(0))
            {
                return Err(Error::Invalid("checkpoint static initializer context"));
            }
            if s.index
                .insert(context_index_key(&context), ContextId(id as u32))
                .is_some()
            {
                return Err(Error::Invalid("checkpoint duplicate context"));
            }
            s.contexts.push(context);
        }
        r.done()?;
        if let Some(shapes) = context_shapes {
            shapes.done()?;
        }
        if let Some(effects) = context_effects {
            effects.done()?;
        }
        let mut r = Decoder::new(bytes(7)?);
        for _ in 0..counts[6] {
            let call = ContextCall {
                source: ContextId(r.n()?),
                target: ContextId(r.n()?),
                operation: OperationId(r.n()?),
                kind: EdgeKind::decode(r.n()?)?,
                edge: EdgeId(r.n()?),
                binding: r.n()?,
            };
            check_index(call.source.0, s.contexts.len(), "checkpoint call source")?;
            check_index(call.target.0, s.contexts.len(), "checkpoint call target")?;
            if !call.operation.is_none() {
                check_index(
                    call.operation.0,
                    facts.operations.len(),
                    "checkpoint call operation",
                )?;
            }
            if !call.edge.is_none() {
                check_index(call.edge.0, graph.edges.len(), "checkpoint call edge")?;
            }
            if !call.kind.is_execution()
                || (call.binding != u32::MAX && call.binding as usize >= counts[9])
                || !s.call_index.insert(call)
            {
                return Err(Error::Invalid("checkpoint call identity"));
            }
            s.calls.push(call);
        }
        r.done()?;
        let mut r = Decoder::new(bytes(8)?);
        for _ in 0..counts[7] {
            let slot = r.slot(legacy, facts.operations.len())?;
            check_slot(&s, slot, counts[9])?;
            let value = SlotValue {
                value: r.value(&s.pool)?,
                version: r.q()?,
            };
            check_version(value.version)?;
            if !matches!(
                slot.kind,
                SlotKind::Field
                    | SlotKind::FieldWildcard
                    | SlotKind::FieldAll
                    | SlotKind::FieldMissing
                    | SlotKind::StaticField
            ) || value.version == 0
                || s.slots.insert(slot, value).is_some()
            {
                return Err(Error::Invalid("checkpoint heap slot"));
            }
        }
        r.done()?;
        if !legacy {
            check_heap_aggregates(&mut s)?;
        }
        let mut r = Decoder::new(bytes(9)?);
        for _ in 0..counts[8] {
            let binding = r.n()?;
            check_index(binding, counts[9], "checkpoint capture binding")?;
            let capture = Capture {
                receiver: r.value(&s.pool)?,
                arguments: FrameId(r.n()?),
                version: r.q()?,
            };
            check_index(
                capture.arguments.0,
                s.frames.len(),
                "checkpoint capture frame",
            )?;
            check_version(capture.version)?;
            if capture.version == 0 || s.captures.insert(binding, capture).is_some() {
                return Err(Error::Invalid("checkpoint capture identity"));
            }
        }
        r.done()?;
        let mut r = Decoder::new(bytes(10)?);
        let mut origins = if wire_version == VERSION {
            Some(Decoder::new(bytes(26)?))
        } else {
            None
        };
        let mut bindings = Vec::new();
        bindings
            .try_reserve_exact(counts[9])
            .map_err(|_| Error::Limit("checkpoint binding validation"))?;
        bindings.resize(counts[9], false);
        for _ in 0..counts[9] {
            let family = ClosureFamily {
                site: OperationId(r.n()?),
                receiver: r.value(&s.pool)?,
                arguments: FrameId(r.n()?),
                origins: origins
                    .as_mut()
                    .map_or(Ok(Value::EMPTY), |r| r.value(&s.pool))?,
            };
            check_index(
                family.site.0,
                facts.operations.len(),
                "checkpoint closure operation",
            )?;
            check_index(
                family.arguments.0,
                s.frames.len(),
                "checkpoint closure frame",
            )?;
            family_value(&s, family.receiver)?;
            if wire_version == VERSION {
                capture_origins::validate(facts, &s.pool, &s.frames, family)?;
            }
            for value in s.frames.get(family.arguments) {
                family_value(&s, *value)?;
            }
            let binding = r.n()?;
            check_index(binding, bindings.len(), "checkpoint closure binding")?;
            if std::mem::replace(&mut bindings[binding as usize], true)
                || s.closure_families.insert(family, binding).is_some()
            {
                return Err(Error::Invalid("checkpoint duplicate closure identity"));
            }
        }
        r.done()?;
        if let Some(origins) = origins {
            origins.done()?;
        }
        drop(bindings);
        let mut r = Decoder::new(bytes(11)?);
        for _ in 0..counts[10] {
            let slot = r.slot(legacy, facts.operations.len())?;
            check_slot(&s, slot, counts[9])?;
            if !matches!(
                slot.kind,
                SlotKind::Field | SlotKind::FieldAll | SlotKind::StaticField
            ) || slot.owner == u32::MAX
                || !s.field_reads.insert(slot)
            {
                return Err(Error::Invalid("checkpoint field read"));
            }
        }
        r.done()?;
        let mut r = Decoder::new(bytes(12)?);
        for _ in 0..counts[11] {
            let context = ContextId(r.n()?);
            check_index(context.0, s.contexts.len(), "checkpoint writer context")?;
            let slot = r.slot(legacy, facts.operations.len())?;
            check_slot(&s, slot, counts[9])?;
            if !matches!(
                slot.kind,
                SlotKind::Field
                    | SlotKind::FieldWildcard
                    | SlotKind::StaticField
                    | SlotKind::Capture
            ) && !(legacy && slot.kind == SlotKind::FieldAll)
                || !s.writes.insert((context, slot))
            {
                return Err(Error::Invalid("checkpoint write identity"));
            }
        }
        r.done()?;
        let mut r = Decoder::new(bytes(13)?);
        for _ in 0..counts[12] {
            let id = ContextId(r.n()?);
            check_index(id.0, s.contexts.len(), "checkpoint ready context")?;
            s.ready.push(id);
        }
        r.done()?;
        let mut r = Decoder::new(bytes(14)?);
        let mut roots = HashSet::new();
        roots
            .try_reserve(counts[13])
            .map_err(|_| Error::Limit("checkpoint root validation"))?;
        for _ in 0..counts[13] {
            let id = ContextId(r.n()?);
            check_index(id.0, s.contexts.len(), "checkpoint root context")?;
            if !roots.insert(id) {
                return Err(Error::Invalid("checkpoint duplicate root"));
            }
            s.roots.push(id);
        }
        r.done()?;
        drop(roots);
        let mut r = Decoder::new(bytes(15)?);
        for _ in 0..counts[14] {
            let issue = Obligation {
                kind: IssueKind::decode(r.n()?)?,
                file: FileId(r.n()?),
                symbol: SymbolId(r.n()?),
                detail: StrId(r.n()?),
            };
            if !issue.kind.is_execution_boundary() {
                return Err(Error::Invalid(
                    "metadata issue in checkpoint execution obligations",
                ));
            }
            if !issue.file.is_none() {
                check_index(issue.file.0, facts.files.len(), "checkpoint issue file")?;
            }
            if !issue.symbol.is_none() {
                check_index(
                    issue.symbol.0,
                    facts.symbols.len(),
                    "checkpoint issue symbol",
                )?;
            }
            if !issue.detail.is_none() {
                check_index(
                    issue.detail.0,
                    facts.strings.len(),
                    "checkpoint issue detail",
                )?;
            }
            if !s.issue_index.insert(obligation_key(issue)) {
                return Err(Error::Invalid("checkpoint duplicate issue"));
            }
            s.issues.push(issue);
        }
        r.done()?;
        let mut r = Decoder::new(bytes(16)?);
        for _ in 0..counts[15] {
            let context = ContextId(r.n()?);
            check_index(context.0, s.contexts.len(), "checkpoint issue context")?;
            if !s.issue_contexts.insert(context) {
                return Err(Error::Invalid("checkpoint duplicate issue context"));
            }
        }
        r.done()?;
        let mut r = Decoder::new(bytes(17)?);
        for _ in 0..counts[16] {
            let generation = r.q()?;
            let invalid = r.boolean()?;
            s.dependencies.restore_context_state(generation, invalid)?;
        }
        r.done()?;
        let mut r = Decoder::new(bytes(18)?);
        for _ in 0..counts[17] {
            let context = ContextId(r.n()?);
            check_index(context.0, s.contexts.len(), "checkpoint dependency context")?;
            let read = Read {
                slot: r.slot(legacy, facts.operations.len())?,
                version: r.q()?,
                present: r.boolean()?,
            };
            check_slot(&s, read.slot, counts[9])?;
            check_version(read.version)?;
            let (current, present) = match read.slot.kind {
                SlotKind::Summary => {
                    let c = s.contexts[read.slot.owner as usize];
                    (c.version, c.evaluated)
                }
                SlotKind::Capture => s
                    .captures
                    .get(&read.slot.owner)
                    .map_or((0, false), |c| (c.version, true)),
                _ => s
                    .slots
                    .get(&read.slot)
                    .map_or((0, false), |v| (v.version, true)),
            };
            if read.version > current
                || (read.present && (!present || read.version == 0))
                || (!read.present && read.version != 0)
            {
                return Err(Error::Invalid("checkpoint dependency read version"));
            }
            if ((matches!(read.slot.kind, SlotKind::Field | SlotKind::FieldAll)
                && read.slot.owner != u32::MAX)
                || read.slot.kind == SlotKind::StaticField)
                && !s.field_reads.contains(&read.slot)
            {
                return Err(Error::Invalid("checkpoint missing field read subscription"));
            }
            if read.slot.kind == SlotKind::FieldMissing {
                let primary = Slot {
                    kind: if (read.slot.owner as usize) < facts.operations.len() {
                        SlotKind::FieldAll
                    } else {
                        SlotKind::Field
                    },
                    ..read.slot
                };
                if !s.field_reads.contains(&primary) {
                    return Err(Error::Invalid(
                        "checkpoint missing field marker subscription",
                    ));
                }
            }
            s.dependencies.restore_read(context, read)?;
        }
        r.done()?;
        let mut r = Decoder::new(bytes(19)?);
        for _ in 0..counts[18] {
            let root = ExecutionRoot {
                node: NodeId(r.n()?),
                receiver: SymbolId(r.n()?),
            };
            check_index(
                root.node.0,
                graph.nodes.len(),
                "checkpoint pending root node",
            )?;
            if !root.receiver.is_none() {
                check_index(
                    root.receiver.0,
                    facts.symbols.len(),
                    "checkpoint pending root receiver",
                )?;
            }
            s.pending_roots.push(root);
        }
        r.done()?;
        if wire_version >= 2 {
            let mut r = Decoder::new(bytes(20)?);
            for _ in 0..counts[19] {
                let context = ContextId(r.n()?);
                let site = RuntimeIssueSite {
                    kind: IssueKind::decode(r.n()?)?,
                    operation: OperationId(r.n()?),
                    reason: RuntimeIssueReason::decode(r.n()?)?,
                };
                if s.runtime_issue_sites.contains_key(&context) {
                    return Err(Error::Invalid("checkpoint duplicate runtime issue context"));
                }
                s.record_runtime_issue_site(context, site)?;
            }
            r.done()?;
        }
        if s.sealed
            && (!s.ready.is_empty()
                || !s.pending_roots.is_empty()
                || s.stop_reason.is_some()
                || s.completion == Completion::ResourceLimited)
        {
            return Err(Error::Invalid("checkpoint sealed frontier"));
        }
        if s.stop_reason.is_some() != (s.completion == Completion::ResourceLimited) {
            return Err(Error::Invalid("checkpoint stop completion"));
        }
        let mut queued = Vec::new();
        queued
            .try_reserve_exact(s.contexts.len())
            .map_err(|_| Error::Limit("checkpoint frontier validation"))?;
        queued.resize(s.contexts.len(), false);
        for id in &s.ready {
            queued[id.index()] = true;
        }
        if s.contexts
            .iter()
            .enumerate()
            .any(|(i, c)| !c.evaluated && !queued[i])
            || s.dependencies
                .snapshot_contexts()
                .enumerate()
                .any(|(i, (_, invalid))| invalid && !queued[i])
        {
            return Err(Error::Invalid("checkpoint omitted runnable context"));
        }
        drop(queued);
        if has_shapes {
            s.rebuild_context_policy()?;
        }
        s.validate_effect_states()?;
        if s.owned_bytes().saturating_add(artifact.byte_len()) > options.memory_budget_bytes {
            return Err(Error::Limit("checkpoint admission memory"));
        }
        s.metrics.owned_bytes = s.owned_bytes() as u64;
        Ok(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use selector_artifacts::Section;

    struct Fixture {
        facts: FactSnapshot,
        graph: ProgramGraph,
    }
    fn op(opcode: Opcode) -> OperationRecord {
        OperationRecord {
            body: BodyId::NONE,
            opcode,
            target: SymbolId::NONE,
            dest: ValueId::NONE,
            a: ValueId::NONE,
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span::default(),
            flags: 0,
        }
    }
    impl Fixture {
        fn new(names: &[&str]) -> Self {
            let mut builder = FactBuilder::new();
            for name in names {
                builder.ensure_symbol(name, FileId::NONE).unwrap();
            }
            let path = builder.intern("checkpoint.scala").unwrap();
            let source = builder.intern("").unwrap();
            builder.facts.files.push(FileRecord {
                path,
                source,
                revision: StrId::NONE,
                context: StrId::NONE,
                source_hash: ContentHash::default(),
                flags: SOURCE_VERIFIED,
            });
            let facts = builder.finish().unwrap();
            let mut graph = ProgramGraph {
                facts_identity: facts.identity,
                ..Default::default()
            };
            for id in 0..names.len() {
                graph.symbol_nodes.push(NodeId(id as u32));
                graph.nodes.push(NodeRecord {
                    symbol: SymbolId(id as u32),
                    file: FileId(0),
                    body: BodyId::NONE,
                    flags: 0,
                });
            }
            Self { facts, graph }
        }
        fn body(&mut self, node: u32, mut operations: Vec<OperationRecord>) {
            let body = BodyId(self.facts.bodies.len() as u32);
            let start = self.facts.operations.len() as u32;
            for operation in &mut operations {
                operation.body = body;
            }
            self.facts.bodies.push(BodyRecord {
                symbol: SymbolId(node),
                file: FileId(0),
                span: Span::default(),
                name_span: Span::default(),
                operations: IdRange {
                    start,
                    len: operations.len() as u32,
                },
                parameters: IdRange::default(),
                body_hash: ContentHash::default(),
                flags: 0,
            });
            self.facts.operations.extend(operations);
            self.graph.nodes[node as usize].body = body;
        }
        fn args(&mut self, ids: &[u32]) -> IdRange {
            let start = self.facts.operands.len() as u32;
            self.facts.operands.extend(ids.iter().copied().map(ValueId));
            IdRange {
                start,
                len: ids.len() as u32,
            }
        }
        fn seal(&mut self) {
            for (index, operation) in self.facts.operations.iter().enumerate() {
                if matches!(operation.opcode, Opcode::Call | Opcode::Allocate)
                    && !operation.target.is_none()
                {
                    self.graph.edges.push(EdgeRecord {
                        source: NodeId(self.facts.bodies[operation.body.index()].symbol.0),
                        target: NodeId(operation.target.0),
                        kind: if operation.opcode == Opcode::Call {
                            EdgeKind::Call
                        } else {
                            EdgeKind::Construct
                        },
                        occurrence: OccurrenceId::NONE,
                        operation: OperationId(index as u32),
                        receiver: SymbolId::NONE,
                        flags: 0,
                    });
                }
            }
            self.graph.index().unwrap();
        }
        fn heap() -> Self {
            let mut f = Self::new(&["root", "class", "closure", "changed", "field"]);
            f.facts.symbols[1].kind = 13;
            f.body(
                0,
                vec![
                    OperationRecord {
                        target: SymbolId(1),
                        dest: ValueId(1),
                        ..op(Opcode::Allocate)
                    },
                    OperationRecord {
                        target: SymbolId(2),
                        dest: ValueId(2),
                        ..op(Opcode::BindCallback)
                    },
                    OperationRecord {
                        target: SymbolId(4),
                        a: ValueId(1),
                        b: ValueId(2),
                        ..op(Opcode::StoreField)
                    },
                    OperationRecord {
                        target: SymbolId(4),
                        a: ValueId(1),
                        dest: ValueId(3),
                        ..op(Opcode::LoadField)
                    },
                    OperationRecord {
                        a: ValueId(3),
                        ..op(Opcode::InvokeCallback)
                    },
                ],
            );
            f.body(1, vec![]);
            f.body(
                2,
                vec![OperationRecord {
                    target: SymbolId(3),
                    ..op(Opcode::Call)
                }],
            );
            f.body(3, vec![]);
            f.body(4, vec![]);
            f.seal();
            f
        }
    }
    fn options(workers: usize) -> SolveOptions {
        SolveOptions {
            workers,
            quantum: 1,
            scratch_bytes_per_worker: 4096,
            memory_budget_bytes: 16 * 1024 * 1024,
            ..Default::default()
        }
    }
    fn root() -> ExecutionRoot {
        ExecutionRoot {
            node: NodeId(0),
            receiver: SymbolId::NONE,
        }
    }
    fn assert_answer(a: &AnalysisResult, b: &AnalysisResult) {
        assert_eq!(a.completion, b.completion);
        assert_eq!(a.affected, b.affected);
        assert_eq!(a.witnesses, b.witnesses);
        assert_eq!(a.derived_edges, b.derived_edges);
        assert_eq!(a.obligations, b.obligations);
        assert_eq!(a.guarded_roots, b.guarded_roots);
        assert_eq!(a.unscoped_uncertainty, b.unscoped_uncertainty);
        assert_eq!(format!("{:?}", a.evidence), format!("{:?}", b.evidence));
        assert_eq!(a.compilation.affected, b.compilation.affected);
        assert_eq!(a.compilation.witnesses, b.compilation.witnesses);
    }
    fn paused<'a>(f: &'a Fixture) -> QuerySession<'a> {
        let mut capped = options(1);
        capped.max_steps = 1;
        let mut session = QuerySession::new(&f.facts, &f.graph, &capped).unwrap();
        session.execute(&[root()]).unwrap();
        assert_eq!(session.stop_reason(), Some(StopReason::StepLimit));
        assert!(!session.ready.is_empty());
        assert!(!session.captures.is_empty());
        assert!(session.dependencies.active_reads().any(
            |(_, r)| !r.present && matches!(r.slot.kind, SlotKind::Field | SlotKind::FieldAll)
        ));
        session
    }

    fn origin_root() -> ExecutionRoot {
        ExecutionRoot {
            receiver: SymbolId(1),
            ..root()
        }
    }

    fn callback_shape_fixture() -> Fixture {
        let mut f = Fixture::new(&["factory", "consumer", "callbackA", "callbackB", "changed"]);
        f.body(
            0,
            vec![
                OperationRecord {
                    target: SymbolId(2),
                    dest: ValueId(1),
                    ..op(Opcode::BindCallback)
                },
                OperationRecord {
                    target: SymbolId(3),
                    dest: ValueId(2),
                    ..op(Opcode::BindCallback)
                },
            ],
        );
        f.body(
            1,
            vec![
                OperationRecord {
                    a: ValueId(1),
                    dest: ValueId(2),
                    ..op(Opcode::InvokeCallback)
                },
                OperationRecord {
                    a: ValueId(2),
                    ..op(Opcode::Return)
                },
            ],
        );
        let parameter = f.args(&[1]);
        f.facts.bodies[1].parameters = parameter;
        for node in [2, 3] {
            f.body(
                node,
                vec![OperationRecord {
                    target: SymbolId(4),
                    ..op(Opcode::Call)
                }],
            );
        }
        f.body(4, vec![]);
        f.seal();
        f
    }

    fn callback_shape_options(workers: usize) -> SolveOptions {
        SolveOptions {
            max_set_members: 1,
            context_policy: ContextPolicy::BoundedArguments {
                max_variants_per_receiver: 1,
            },
            ..options(workers)
        }
    }

    fn callback_shape_session<'a>(f: &'a Fixture, options: &SolveOptions) -> QuerySession<'a> {
        let mut session = QuerySession::new(&f.facts, &f.graph, options).unwrap();
        for binding in 0..6 {
            let site = OperationId(binding / 3);
            let receiver = session
                .pool
                .singleton(Atom {
                    kind: AtomKind::Object,
                    site: OperationId::NONE,
                    symbol: SymbolId(2 + binding % 3),
                    binding: 0,
                })
                .unwrap();
            session.closure_families.insert(
                ClosureFamily {
                    site,
                    receiver,
                    arguments: FrameId(0),
                    origins: Value::EMPTY,
                },
                binding,
            );
            session.captures.insert(
                binding,
                Capture {
                    receiver,
                    arguments: FrameId(0),
                    version: 1,
                },
            );
            let callback = session
                .pool
                .singleton(Atom {
                    kind: AtomKind::Callback,
                    site,
                    symbol: SymbolId(2 + binding / 3),
                    binding,
                })
                .unwrap();
            let arguments = session.frames.intern(&[callback]).unwrap();
            let id = session
                .context(ContextKey {
                    node: NodeId(1),
                    receiver: Value::EMPTY,
                    arguments,
                })
                .unwrap();
            if !session.roots.contains(&id) {
                session.roots.push(id);
            }
        }
        let arguments = session.frames.intern(&[Value::TOP]).unwrap();
        let id = session
            .context(ContextKey {
                node: NodeId(1),
                receiver: Value::EMPTY,
                arguments,
            })
            .unwrap();
        session.roots.push(id);
        session
    }

    #[test]
    fn immutable_callback_shapes_survive_identical_top_payloads_and_cross_worker_resume() {
        let f = callback_shape_fixture();
        let mut capped = callback_shape_options(1);
        capped.max_steps = 1;
        let mut original = callback_shape_session(&f, &capped);
        let overflows = original
            .contexts
            .iter()
            .filter(|c| c.widened)
            .copied()
            .collect::<Vec<_>>();
        assert_eq!(overflows.len(), 2);
        assert_eq!(overflows[0].key, overflows[1].key);
        assert_ne!(overflows[0].callback_shape, overflows[1].callback_shape);
        for context in &overflows {
            let value = original.frames.get(context.key.arguments)[0];
            assert!(original.pool.members(value).is_empty());
            assert_ne!(value.unknown & WIDENED_VALUE, 0);
            let shape = original.callback_shapes.get(context.callback_shape);
            assert_eq!(shape.arity, 1);
            assert_eq!(shape.atoms.len(), 1);
            assert!(!shape.atoms[0].site.is_none());
        }
        original.resume().unwrap();
        assert_eq!(original.stop_reason(), Some(StopReason::StepLimit));
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("callback-shapes.bin");
        let producer = ContentHash([84; 32]);
        original.save_checkpoint(&path, producer).unwrap();
        let next = callback_shape_options(4);
        let runtime = SolverRuntime::new(&next).unwrap();
        let mut loaded =
            QuerySession::from_checkpoint(&f.facts, &f.graph, &next, &runtime, &path, producer)
                .unwrap();
        let loaded_overflows = loaded
            .contexts
            .iter()
            .filter(|c| c.widened)
            .copied()
            .collect::<Vec<_>>();
        assert_eq!(loaded_overflows.len(), 2);
        for (expected, actual) in overflows.iter().zip(&loaded_overflows) {
            assert_eq!(actual.callback_shape, expected.callback_shape);
            assert_eq!(actual.key, expected.key);
        }
        assert_eq!(loaded.dependencies.epoch(), original.dependencies.epoch());
        assert!(loaded.callback_shapes.snapshot_shapes().any(|shape| {
            shape
                .atoms
                .iter()
                .any(|atom| atom.site.is_none() && atom.symbol.is_none())
        }));
        loaded.resume().unwrap();
        let mut expected = callback_shape_session(&f, &callback_shape_options(1));
        expected.resume().unwrap();
        assert_answer(
            &expected.analyze(&[NodeId(4)]).unwrap(),
            &loaded.analyze(&[NodeId(4)]).unwrap(),
        );
        assert_eq!(
            loaded.work_counters().evaluations,
            expected.work_counters().evaluations
        );
    }
    #[test]
    fn resealed_checkpoint_metadata_obligation_is_not_runtime_uncertainty() {
        let f = Fixture::heap();
        let session = paused(&f);
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("original.bin");
        let producer = ContentHash([172; 32]);
        session.save_checkpoint(&path, producer).unwrap();
        let next = options(1);
        let runtime = SolverRuntime::new(&next).unwrap();
        QuerySession::from_checkpoint(&f.facts, &f.graph, &next, &runtime, &path, producer)
            .unwrap();
        let artifact = selector_artifacts::open(&path, ArtifactKind::Continuation).unwrap();
        let mut issue_rows = artifact.section(15).unwrap().to_vec();
        assert!(!issue_rows.is_empty());
        let old_kind =
            IssueKind::decode(u32::from_le_bytes(issue_rows[..4].try_into().unwrap())).unwrap();
        assert!(old_kind.is_execution_boundary());
        issue_rows[..4].copy_from_slice(&(IssueKind::IncompleteHierarchy as u32).to_le_bytes());
        let sections: Vec<_> = (1..=SECTION_COUNT)
            .map(|id| Section {
                id,
                count: artifact.count(id).unwrap(),
                bytes: if id == 15 {
                    &issue_rows
                } else {
                    artifact.section(id).unwrap()
                },
            })
            .collect();
        let malformed = directory.path().join("metadata-obligation.bin");
        selector_artifacts::write(&malformed, ArtifactKind::Continuation, &sections).unwrap();
        assert!(matches!(
            QuerySession::from_checkpoint(
                &f.facts, &f.graph, &next, &runtime, &malformed, producer
            ),
            Err(Error::Invalid(
                "metadata issue in checkpoint execution obligations"
            ))
        ));
        assert!(matches!(
            inspection::CheckpointView::open(
                &f.facts,
                &f.graph,
                &malformed,
                &inspection::InspectionLimits::default()
            ),
            Err(Error::Invalid(
                "metadata issue in checkpoint execution obligations"
            ))
        ));
    }

    #[test]
    fn checkpoint_shape_growth_charges_live_artifact_and_decode_scratch_before_allocating() {
        let f = callback_shape_fixture();
        let mut session = callback_shape_session(&f, &callback_shape_options(1));
        let artifact = vec![0u8; 1024];
        let mut scratch = Vec::with_capacity(64);
        scratch.extend([
            CallbackShapeAtom {
                argument: 0,
                site: OperationId(0),
                symbol: SymbolId(2),
            },
            CallbackShapeAtom {
                argument: 1,
                site: OperationId(1),
                symbol: SymbolId(3),
            },
        ]);
        let scratch_bytes = scratch.capacity() * std::mem::size_of::<CallbackShapeAtom>();
        session.options.memory_budget_bytes =
            session.owned_bytes() + artifact.len() + scratch_bytes;
        let before = (
            session.callback_shapes.len(),
            session.callback_shapes.owned_bytes(),
        );
        assert!(matches!(
            intern_checkpoint_shape(&mut session, 2, &scratch, artifact.len(), scratch_bytes),
            Err(Error::Limit("callback shape memory"))
        ));
        assert_eq!(
            (
                session.callback_shapes.len(),
                session.callback_shapes.owned_bytes()
            ),
            before
        );
        session.options.memory_budget_bytes += 4096;
        assert!(
            intern_checkpoint_shape(&mut session, 2, &scratch, artifact.len(), scratch_bytes)
                .is_ok()
        );
        assert_eq!(session.callback_shapes.len(), before.0 + 1);
    }

    #[test]
    fn malformed_callback_shape_rows_context_ids_and_arities_fail_closed() {
        let f = callback_shape_fixture();
        let mut capped = callback_shape_options(1);
        capped.max_steps = 1;
        let mut original = callback_shape_session(&f, &capped);
        original.resume().unwrap();
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("shape-original.bin");
        let producer = ContentHash([85; 32]);
        original.save_checkpoint(&path, producer).unwrap();
        let artifact = selector_artifacts::open(&path, ArtifactKind::Continuation).unwrap();
        let next = callback_shape_options(4);
        let runtime = SolverRuntime::new(&next).unwrap();
        for case in 0..15 {
            let mut data = (1..=SECTION_COUNT)
                .map(|id| artifact.section(id).unwrap().to_vec())
                .collect::<Vec<_>>();
            let mut counts = (1..=SECTION_COUNT)
                .map(|id| artifact.count(id).unwrap())
                .collect::<Vec<_>>();
            match case {
                0 => data[21][..4].copy_from_slice(&u32::MAX.to_le_bytes()),
                1 => data[22][8..12].copy_from_slice(&0u32.to_le_bytes()),
                2 => data[23][..4].copy_from_slice(&1u32.to_le_bytes()),
                3 => data[23][4..8].copy_from_slice(&u32::MAX.to_le_bytes()),
                4 => data[23][8..12].copy_from_slice(&u32::MAX.to_le_bytes()),
                5 => {
                    data[23][4..8].copy_from_slice(&(f.facts.operations.len() as u32).to_le_bytes())
                }
                6 => data[23][8..12].copy_from_slice(&(f.facts.symbols.len() as u32).to_le_bytes()),
                7 => data[23][4..8].copy_from_slice(&2u32.to_le_bytes()),
                8 => data[23][8..12].copy_from_slice(&3u32.to_le_bytes()),
                9 => {
                    let token = data[23][..12].to_vec();
                    data[23].splice(12..12, token);
                    data[22][12..16].copy_from_slice(&2u32.to_le_bytes());
                    counts[23] += 1;
                }
                10 => data[23][4..12].fill(255),
                11 => data[21][..4].copy_from_slice(&2u32.to_le_bytes()),
                12 => {
                    let shape = data[22][8..16].to_vec();
                    let token = data[23][..12].to_vec();
                    data[22].extend_from_slice(&shape);
                    data[23].extend_from_slice(&token);
                    counts[22] += 1;
                    counts[23] += 1;
                }
                13 => data[22][8..12].copy_from_slice(&2u32.to_le_bytes()),
                14 => {
                    data[21].clear();
                    counts[21] = 0;
                }
                _ => unreachable!(),
            }
            let sections = data
                .iter()
                .zip(&counts)
                .enumerate()
                .map(|(i, (bytes, count))| Section {
                    id: i as u32 + 1,
                    count: *count,
                    bytes,
                })
                .collect::<Vec<_>>();
            let bad = directory.path().join(format!("malformed-shape-{case}.bin"));
            selector_artifacts::write(&bad, ArtifactKind::Continuation, &sections).unwrap();
            assert!(
                QuerySession::from_checkpoint(&f.facts, &f.graph, &next, &runtime, &bad, producer)
                    .is_err(),
                "case {case}"
            );
            assert!(
                inspection::CheckpointView::open(
                    &f.facts,
                    &f.graph,
                    &bad,
                    &inspection::InspectionLimits::default()
                )
                .is_err(),
                "inspection case {case}"
            );
        }
    }

    fn origin_paused(f: &Fixture) -> QuerySession<'_> {
        let mut capped = options(1);
        capped.max_steps = 1;
        let mut session = QuerySession::new(&f.facts, &f.graph, &capped).unwrap();
        session.execute(&[origin_root()]).unwrap();
        assert_eq!(session.stop_reason(), Some(StopReason::StepLimit));
        assert_eq!(
            session.heap_owners.rows(),
            &[HeapOwnerKey {
                site: OperationId(0),
                root: SymbolId(1)
            }]
        );
        session
    }

    #[test]
    fn receiver_origin_owner_ids_and_negative_reads_resume_across_worker_counts() {
        let f = Fixture::heap();
        let producer = ContentHash([81; 32]);
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("origins.bin");
        let stopped = origin_paused(&f);
        let owners = stopped.heap_owners.rows().to_vec();
        let atoms = stopped
            .pool
            .snapshot_sets()
            .flatten()
            .copied()
            .collect::<Vec<_>>();
        assert!(
            atoms
                .iter()
                .any(|a| a.kind == AtomKind::Object && a.site == OperationId(0) && a.binding == 2)
        );
        let reads = stopped.dependencies.snapshot_reads().collect::<Vec<_>>();
        assert!(
            reads
                .iter()
                .any(|(_, r)| !r.present && r.slot.kind == SlotKind::FieldMissing)
        );
        let epoch = stopped.dependencies.epoch();
        stopped.save_checkpoint(&path, producer).unwrap();
        let next = options(4);
        let runtime = SolverRuntime::new(&next).unwrap();
        let mut loaded =
            QuerySession::from_checkpoint(&f.facts, &f.graph, &next, &runtime, &path, producer)
                .unwrap();
        assert_eq!(loaded.heap_owners.rows(), owners);
        assert_eq!(
            loaded
                .pool
                .snapshot_sets()
                .flatten()
                .copied()
                .collect::<Vec<_>>(),
            atoms
        );
        assert_eq!(
            loaded.dependencies.snapshot_reads().collect::<Vec<_>>(),
            reads
        );
        assert_eq!(loaded.dependencies.epoch(), epoch);
        for (slot, value) in &stopped.slots {
            let restored = loaded.slots.get(slot).unwrap();
            assert_eq!(
                (restored.value, restored.version),
                (value.value, value.version)
            );
        }
        loaded.resume().unwrap();
        let mut expected = QuerySession::new(&f.facts, &f.graph, &options(1)).unwrap();
        expected.execute(&[origin_root()]).unwrap();
        assert_answer(
            &expected.analyze(&[NodeId(3)]).unwrap(),
            &loaded.analyze(&[NodeId(3)]).unwrap(),
        );
        assert_eq!(
            loaded.work_counters().evaluations,
            expected.work_counters().evaluations
        );
    }

    #[test]
    fn missing_markers_roundtrip_without_becoming_actual_field_stores() {
        let mut f = Fixture::heap();
        // Read an unwritten field on the root, independent of the allocated
        // object's stored callback. The drained frontier records its absence.
        let last = f.facts.bodies[0].operations.range().end;
        f.facts.operations.insert(
            last,
            OperationRecord {
                body: BodyId(0),
                target: SymbolId(4),
                a: ValueId(0),
                dest: ValueId(6),
                ..op(Opcode::LoadField)
            },
        );
        f.facts.bodies[0].operations.len += 1;
        for body in &mut f.facts.bodies[1..] {
            body.operations.start += 1;
        }
        f.graph.edges.clear();
        f.seal();
        let next = options(1);
        let runtime = SolverRuntime::new(&next).unwrap();
        let mut original = QuerySession::new(&f.facts, &f.graph, &next).unwrap();
        original.execute(&[origin_root()]).unwrap();
        let markers = original
            .slots
            .iter()
            .filter(|(s, _)| s.kind == SlotKind::FieldMissing)
            .map(|(s, v)| (*s, v.value, v.version))
            .collect::<Vec<_>>();
        assert!(!markers.is_empty());
        assert!(
            markers
                .iter()
                .all(|(slot, _, _)| !original.writes.iter().any(|(_, write)| write == slot))
        );
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("missing.bin");
        let producer = ContentHash([82; 32]);
        original.save_checkpoint(&path, producer).unwrap();
        let restored =
            QuerySession::from_checkpoint(&f.facts, &f.graph, &next, &runtime, &path, producer)
                .unwrap();
        for (slot, value, version) in markers {
            let actual = restored.slots.get(&slot).unwrap();
            assert_eq!((actual.value, actual.version), (value, version));
        }
        assert_eq!(restored.dependencies.epoch(), original.dependencies.epoch());
    }

    #[test]
    fn malformed_owner_origin_local_tags_and_derived_channels_fail_closed() {
        let f = Fixture::heap();
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("origin.bin");
        let producer = ContentHash([83; 32]);
        origin_paused(&f).save_checkpoint(&path, producer).unwrap();
        let artifact = selector_artifacts::open(&path, ArtifactKind::Continuation).unwrap();
        let next = options(1);
        let runtime = SolverRuntime::new(&next).unwrap();
        for case in 0..10 {
            let mut data = (1..=SECTION_COUNT)
                .map(|id| artifact.section(id).unwrap().to_vec())
                .collect::<Vec<_>>();
            let mut counts = (1..=SECTION_COUNT)
                .map(|id| artifact.count(id).unwrap())
                .collect::<Vec<_>>();
            match case {
                0 => data[20][4..8].copy_from_slice(&(f.facts.symbols.len() as u32).to_le_bytes()),
                1 => data[20][..4].copy_from_slice(&1u32.to_le_bytes()), // BindCallback is not a constructor.
                2 => data[20][..4].copy_from_slice(&LOCAL_HEAP_OWNER.to_le_bytes()),
                3 => {
                    let row = data[20].clone();
                    data[20].extend_from_slice(&row);
                    counts[20] += 1;
                }
                4 | 5 => {
                    let row = data[2]
                        .chunks_exact_mut(16)
                        .find(|row| {
                            u32::from_le_bytes(row[..4].try_into().unwrap()) == 1
                                && u32::from_le_bytes(row[4..8].try_into().unwrap()) == 0
                        })
                        .unwrap();
                    row[12..16].copy_from_slice(
                        &(if case == 4 {
                            f.facts.symbols.len() as u32 + 1
                        } else {
                            LOCAL_BINDING
                        })
                        .to_le_bytes(),
                    );
                }
                6 | 7 => {
                    let row = data[7]
                        .chunks_exact_mut(28)
                        .find(|row| u32::from_le_bytes(row[..4].try_into().unwrap()) == 2)
                        .unwrap();
                    row[4..8].copy_from_slice(
                        &(if case == 6 {
                            LOCAL_HEAP_OWNER
                        } else {
                            (f.facts.operations.len() + f.facts.symbols.len() + 1) as u32
                        })
                        .to_le_bytes(),
                    );
                }
                8 => {
                    let row = data[11]
                        .chunks_exact_mut(16)
                        .find(|row| u32::from_le_bytes(row[4..8].try_into().unwrap()) == 2)
                        .unwrap();
                    row[4..8].copy_from_slice(&8u32.to_le_bytes());
                    row[8..12].copy_from_slice(&0u32.to_le_bytes());
                }
                9 => {
                    let row = data[7]
                        .chunks_exact_mut(28)
                        .find(|row| u32::from_le_bytes(row[..4].try_into().unwrap()) == 8)
                        .unwrap();
                    row[12..16].copy_from_slice(&0u32.to_le_bytes()); // Lose the actual callback value.
                }
                _ => unreachable!(),
            }
            let sections = data
                .iter()
                .zip(&counts)
                .enumerate()
                .map(|(i, (bytes, count))| Section {
                    id: i as u32 + 1,
                    count: *count,
                    bytes,
                })
                .collect::<Vec<_>>();
            let bad = dir.path().join(format!("bad-{case}.bin"));
            selector_artifacts::write(&bad, ArtifactKind::Continuation, &sections).unwrap();
            assert!(
                QuerySession::from_checkpoint(&f.facts, &f.graph, &next, &runtime, &bad, producer)
                    .is_err(),
                "case {case}"
            );
            assert!(
                inspection::CheckpointView::open(
                    &f.facts,
                    &f.graph,
                    &bad,
                    &inspection::InspectionLimits::default()
                )
                .is_err(),
                "inspection case {case}"
            );
        }
    }

    #[test]
    fn capped_heap_capture_and_negative_read_resume_without_redoing_completed_work() {
        let f = Fixture::heap();
        let producer = ContentHash([71; 32]);
        let mut uninterrupted = QuerySession::new(&f.facts, &f.graph, &options(1)).unwrap();
        uninterrupted.execute(&[root()]).unwrap();
        let expected = uninterrupted.analyze(&[NodeId(3)]).unwrap();
        assert!(expected.contains(NodeId(0)));
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("query.bin");
        let mut stopped = paused(&f);
        let visits = stopped.metrics.edge_visits;
        let partial = stopped.analyze(&[NodeId(3)]).unwrap();
        assert_eq!(partial.completion, Completion::ResourceLimited);
        assert_eq!(
            stopped.metrics.edge_visits, visits,
            "reporting a stopped query must not resume it"
        );
        let epoch = stopped.dependencies.epoch();
        let before = stopped.work_counters();
        stopped.save_checkpoint(&path, producer).unwrap();
        drop(stopped);
        let resumed_options = options(4);
        let runtime = SolverRuntime::new(&resumed_options).unwrap();
        let mut resumed = QuerySession::from_checkpoint(
            &f.facts,
            &f.graph,
            &resumed_options,
            &runtime,
            &path,
            producer,
        )
        .unwrap();
        assert_eq!(resumed.metrics.edge_visits, visits);
        assert_eq!(resumed.dependencies.epoch(), epoch);
        assert_eq!(resumed.work_counters().evaluations, before.evaluations);
        resumed.resume().unwrap();
        let actual = resumed.analyze(&[NodeId(3)]).unwrap();
        assert_answer(&expected, &actual);
        assert_eq!(
            actual.metrics.edge_visits, expected.metrics.edge_visits,
            "barrier resume retains already evaluated work"
        );
        assert_eq!(
            resumed.work_counters().evaluations,
            uninterrupted.work_counters().evaluations
        );
        assert_eq!(actual.metrics.workers, 4);
    }

    #[test]
    fn cancellation_preserves_pending_roots_and_can_be_checkpointed_repeatedly() {
        let f = Fixture::heap();
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("cancelled.bin");
        let producer = ContentHash([72; 32]);
        let control = Arc::new(SolveControl::default());
        control.cancel();
        let mut initial = options(1);
        initial.control = Some(control);
        let mut stopped = QuerySession::new(&f.facts, &f.graph, &initial).unwrap();
        stopped.execute(&[root()]).unwrap();
        assert_eq!(stopped.stop_reason(), Some(StopReason::Cancelled));
        stopped.save_checkpoint(&path, producer).unwrap();
        let next = options(2);
        let runtime = SolverRuntime::new(&next).unwrap();
        let loaded =
            QuerySession::from_checkpoint(&f.facts, &f.graph, &next, &runtime, &path, producer)
                .unwrap();
        loaded.save_checkpoint(&path, producer).unwrap();
        drop(loaded);
        let mut loaded =
            QuerySession::from_checkpoint(&f.facts, &f.graph, &next, &runtime, &path, producer)
                .unwrap();
        loaded.resume().unwrap();
        let actual = loaded.analyze(&[NodeId(3)]).unwrap();
        let mut uninterrupted = QuerySession::new(&f.facts, &f.graph, &options(1)).unwrap();
        uninterrupted.execute(&[root()]).unwrap();
        let expected = uninterrupted.analyze(&[NodeId(3)]).unwrap();
        assert_answer(&expected, &actual);
    }

    #[test]
    fn context_cap_during_root_admission_retains_the_unadmitted_frontier() {
        let f = Fixture::heap();
        let roots = [
            root(),
            ExecutionRoot {
                node: NodeId(1),
                receiver: SymbolId::NONE,
            },
            ExecutionRoot {
                node: NodeId(2),
                receiver: SymbolId::NONE,
            },
        ];
        let mut capped = options(1);
        capped.max_contexts = 1;
        let mut stopped = QuerySession::new(&f.facts, &f.graph, &capped).unwrap();
        stopped.execute(&roots).unwrap();
        assert_eq!(stopped.stop_reason(), Some(StopReason::ContextLimit));
        assert_eq!(stopped.pending_roots.len(), 2);
        assert_eq!(stopped.metrics.edge_visits, 0);
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("roots.bin");
        let producer = ContentHash([76; 32]);
        stopped.save_checkpoint(&path, producer).unwrap();
        let next = options(4);
        let runtime = SolverRuntime::new(&next).unwrap();
        let mut restored =
            QuerySession::from_checkpoint(&f.facts, &f.graph, &next, &runtime, &path, producer)
                .unwrap();
        assert_eq!(restored.pending_roots.len(), 2);
        restored.resume().unwrap();
        let actual = restored.analyze(&[NodeId(3)]).unwrap();
        let mut uninterrupted = QuerySession::new(&f.facts, &f.graph, &options(1)).unwrap();
        uninterrupted.execute(&roots).unwrap();
        let expected = uninterrupted.analyze(&[NodeId(3)]).unwrap();
        assert_answer(&expected, &actual);
        assert_eq!(actual.metrics.edge_visits, expected.metrics.edge_visits);
    }

    #[test]
    fn unresolved_instance_field_member_is_a_valid_checkpoint_sentinel() {
        let mut f = Fixture::heap();
        f.facts.operations[2].target = SymbolId::NONE;
        f.facts.operations[3].target = SymbolId::NONE;
        let stopped = paused(&f);
        assert!(stopped.slots.keys().any(|slot| matches!(
            slot.kind,
            SlotKind::Field | SlotKind::FieldWildcard | SlotKind::FieldAll
        ) && slot.member == u32::MAX));
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("unresolved-field.bin");
        let producer = ContentHash([78; 32]);
        stopped.save_checkpoint(&path, producer).unwrap();
        let next = options(2);
        let runtime = SolverRuntime::new(&next).unwrap();
        let mut loaded =
            QuerySession::from_checkpoint(&f.facts, &f.graph, &next, &runtime, &path, producer)
                .unwrap();
        loaded.resume().unwrap();
        let actual = loaded.analyze(&[NodeId(3)]).unwrap();
        let mut baseline = QuerySession::new(&f.facts, &f.graph, &options(1)).unwrap();
        baseline.execute(&[root()]).unwrap();
        assert_answer(&baseline.analyze(&[NodeId(3)]).unwrap(), &actual);
    }

    #[test]
    fn certified_data_issue_keeps_closed_effects_through_cache_and_checkpoint() {
        let mut f = Fixture::new(&["Owner#root().", "Owner#field.", "Owner#"]);
        f.facts.symbols[2].kind = 13;
        f.facts.symbols[2].flags = SYMBOL_DEFINED | SYMBOL_SCALA_PARENTS_COMPLETE;
        f.body(
            0,
            vec![
                OperationRecord {
                    target: SymbolId(1),
                    a: ValueId(0),
                    dest: ValueId(1),
                    ..op(Opcode::LoadField)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::Return)
                },
            ],
        );
        f.seal();
        let execution_root = ExecutionRoot {
            node: NodeId(0),
            receiver: SymbolId(2),
        };
        let next = SolveOptions {
            execution_roots: Some(Arc::from([execution_root])),
            ..options(1)
        };
        let directory = tempfile::tempdir().unwrap();
        let runtime =
            SolverRuntime::with_cache_directory(&next, directory.path(), ContentHash([95; 32]))
                .unwrap();
        let mut original = QuerySession::with_runtime(&f.facts, &f.graph, &next, &runtime).unwrap();
        let owner = object_owner(
            Atom {
                kind: AtomKind::Object,
                site: OperationId::NONE,
                symbol: SymbolId(2),
                binding: 0,
            },
            f.facts.operations.len(),
        )
        .unwrap();
        original.slots.insert(
            Slot {
                kind: SlotKind::FieldMissing,
                owner,
                member: 1,
            },
            SlotValue {
                value: Value {
                    set: SetId(0),
                    unknown: UNKNOWN_FIELD,
                },
                version: 1,
            },
        );
        original.execute(&[execution_root]).unwrap();
        assert!(original.issue_contexts.contains(&ContextId(0)));
        assert_eq!(
            original.runtime_issue_sites[&ContextId(0)].reason,
            RuntimeIssueReason::UnknownFieldValue
        );
        assert!(!original.contexts[0].effects_open);
        original.persist_completed().unwrap();
        let cached = QuerySession::with_runtime(&f.facts, &f.graph, &next, &runtime).unwrap();
        assert_eq!(cached.reuse_metrics().loaded_contexts, 1);
        assert!(cached.issue_contexts.contains(&ContextId(0)));
        assert!(!cached.contexts[0].effects_open);
        let path = directory.path().join("data-issue.bin");
        original
            .save_checkpoint(&path, ContentHash([94; 32]))
            .unwrap();
        let restored = QuerySession::from_checkpoint(
            &f.facts,
            &f.graph,
            &next,
            &runtime,
            &path,
            ContentHash([94; 32]),
        )
        .unwrap();
        assert!(restored.issue_contexts.contains(&ContextId(0)));
        assert!(!restored.contexts[0].effects_open);
    }

    #[test]
    fn effects_closure_checkpoint_roundtrip_legacy_open_and_invalid_bits() {
        let mut f = Fixture::new(&["closed", "open"]);
        f.body(0, vec![op(Opcode::Constant)]);
        f.body(1, vec![op(Opcode::Unknown)]);
        f.seal();
        let next = options(4);
        let runtime = SolverRuntime::new(&next).unwrap();
        let mut original = QuerySession::new(&f.facts, &f.graph, &options(1)).unwrap();
        original
            .execute(&[
                root(),
                ExecutionRoot {
                    node: NodeId(1),
                    receiver: SymbolId::NONE,
                },
            ])
            .unwrap();
        assert_eq!(
            original
                .contexts
                .iter()
                .map(|c| c.effects_open)
                .collect::<Vec<_>>(),
            [false, true]
        );
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("effects.bin");
        let producer = ContentHash([96; 32]);
        original.save_checkpoint(&path, producer).unwrap();
        let restored =
            QuerySession::from_checkpoint(&f.facts, &f.graph, &next, &runtime, &path, producer)
                .unwrap();
        assert_eq!(
            restored
                .contexts
                .iter()
                .map(|c| c.effects_open)
                .collect::<Vec<_>>(),
            [false, true]
        );
        let artifact = selector_artifacts::open(&path, ArtifactKind::Continuation).unwrap();
        let mut data: Vec<_> = (1..=SECTION_COUNT)
            .map(|id| artifact.section(id).unwrap().to_vec())
            .collect();
        for (index, flag) in [(0, 2u32), (1, 0)] {
            data[24] = artifact.section(25).unwrap().to_vec();
            data[24][index * 4..index * 4 + 4].copy_from_slice(&flag.to_le_bytes());
            let sections: Vec<_> = data
                .iter()
                .enumerate()
                .map(|(i, bytes)| Section {
                    id: i as u32 + 1,
                    count: artifact.count(i as u32 + 1).unwrap(),
                    bytes,
                })
                .collect();
            let bad = directory.path().join(format!("bad-effects-{index}.bin"));
            selector_artifacts::write(&bad, ArtifactKind::Continuation, &sections).unwrap();
            assert!(
                QuerySession::from_checkpoint(&f.facts, &f.graph, &next, &runtime, &bad, producer)
                    .is_err()
            );
        }
        data.truncate(section_count(5).unwrap() as usize);
        data[0][..4].copy_from_slice(&5u32.to_le_bytes());
        let sections: Vec<_> = data
            .iter()
            .enumerate()
            .map(|(i, bytes)| Section {
                id: i as u32 + 1,
                count: artifact.count(i as u32 + 1).unwrap(),
                bytes,
            })
            .collect();
        let legacy = directory.path().join("legacy-effects.bin");
        selector_artifacts::write(&legacy, ArtifactKind::Continuation, &sections).unwrap();
        assert!(
            QuerySession::from_checkpoint(&f.facts, &f.graph, &next, &runtime, &legacy, producer)
                .is_err()
        );
        let view = inspection::CheckpointView::open(
            &f.facts,
            &f.graph,
            &legacy,
            &inspection::InspectionLimits::default(),
        )
        .unwrap();
        assert_eq!(view.header().effects_open_contexts, 2);
    }

    #[test]
    fn sparse_runtime_sites_roundtrip_and_reject_cross_body_or_missing_obligations() {
        let mut f = Fixture::new(&["root", "other"]);
        f.body(0, vec![op(Opcode::Constant), op(Opcode::Unknown)]);
        f.body(1, vec![op(Opcode::Unknown)]);
        f.seal();
        let next = options(1);
        let runtime = SolverRuntime::new(&next).unwrap();
        let mut original = QuerySession::with_runtime(&f.facts, &f.graph, &next, &runtime).unwrap();
        original
            .execute(&[
                root(),
                ExecutionRoot {
                    node: NodeId(1),
                    receiver: SymbolId::NONE,
                },
            ])
            .unwrap();
        assert_eq!(original.runtime_issue_sites.len(), 2);
        assert_eq!(
            original.runtime_issue_sites[&ContextId(0)].operation,
            OperationId(1)
        );
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("sites.bin");
        let producer = ContentHash([79; 32]);
        original.save_checkpoint(&path, producer).unwrap();
        let restored =
            QuerySession::from_checkpoint(&f.facts, &f.graph, &next, &runtime, &path, producer)
                .unwrap();
        assert_eq!(restored.runtime_issue_sites, original.runtime_issue_sites);
        let artifact = selector_artifacts::open(&path, ArtifactKind::Continuation).unwrap();
        for case in 0..5 {
            let mut data: Vec<Vec<u8>> = (1..=SECTION_COUNT)
                .map(|id| artifact.section(id).unwrap().to_vec())
                .collect();
            let mut counts: Vec<_> = (1..=SECTION_COUNT)
                .map(|id| artifact.count(id).unwrap())
                .collect();
            let context = u32::from_le_bytes(data[19][0..4].try_into().unwrap());
            match case {
                0 => data[19][8..12]
                    .copy_from_slice(&(if context == 0 { 2u32 } else { 1u32 }).to_le_bytes()),
                1 => data[19][12..16].copy_from_slice(&u32::MAX.to_le_bytes()),
                2 => {
                    let first = data[19][..16].to_vec();
                    data[19][16..32].copy_from_slice(&first);
                }
                3 => {
                    data[14].clear();
                    counts[14] = 0;
                }
                _ => {
                    data[15].clear();
                    counts[15] = 0;
                }
            }
            let sections: Vec<_> = data
                .iter()
                .enumerate()
                .map(|(i, bytes)| Section {
                    id: i as u32 + 1,
                    count: counts[i],
                    bytes,
                })
                .collect();
            let bad = dir.path().join(format!("bad-site-{case}.bin"));
            selector_artifacts::write(&bad, ArtifactKind::Continuation, &sections).unwrap();
            assert!(
                QuerySession::from_checkpoint(&f.facts, &f.graph, &next, &runtime, &bad, producer)
                    .is_err(),
                "case {case}"
            );
        }
    }

    #[test]
    fn legacy_layout_is_read_only_and_never_invents_runtime_sites() {
        let f = Fixture::heap();
        let dir = tempfile::tempdir().unwrap();
        let producer = ContentHash([80; 32]);
        let current = dir.path().join("current.bin");
        paused(&f).save_checkpoint(&current, producer).unwrap();
        let artifact = selector_artifacts::open(&current, ArtifactKind::Continuation).unwrap();
        let next = options(1);
        let runtime = SolverRuntime::new(&next).unwrap();
        for version in [1u32, 2] {
            let mut data = (1..=20)
                .map(|id| artifact.section(id).unwrap().to_vec())
                .collect::<Vec<_>>();
            let mut counts = (1..=20)
                .map(|id| artifact.count(id).unwrap())
                .collect::<Vec<_>>();
            data[0][..4].copy_from_slice(&version.to_le_bytes());
            // Encode the previous operator's merged allocation-site channel. Its
            // real coarse write becomes one legacy Field; derived unions and the
            // new separate no-store channel were absent from the old schema.
            for (id, width, offset) in [
                (8usize, 28usize, 0usize),
                (11, 12, 0),
                (12, 16, 4),
                (18, 28, 4),
            ] {
                let mut rows = Vec::new();
                for row in data[id - 1].chunks_exact(width) {
                    let tag = u32::from_le_bytes(row[offset..offset + 4].try_into().unwrap());
                    if (id == 8 && matches!(tag, 8 | 9)) || (id == 18 && matches!(tag, 7 | 9)) {
                        continue;
                    }
                    let start = rows.len();
                    rows.extend_from_slice(row);
                    if matches!(tag, 7 | 8) {
                        rows[start + offset..start + offset + 4]
                            .copy_from_slice(&2u32.to_le_bytes());
                    }
                }
                counts[id - 1] = (rows.len() / width) as u64;
                data[id - 1] = rows;
            }
            let sections = data
                .iter()
                .zip(&counts)
                .enumerate()
                .take(section_count(version).unwrap() as usize)
                .map(|(i, (bytes, count))| Section {
                    id: i as u32 + 1,
                    count: *count,
                    bytes,
                })
                .collect::<Vec<_>>();
            let legacy = dir.path().join(format!("legacy-{version}.bin"));
            selector_artifacts::write(&legacy, ArtifactKind::Continuation, &sections).unwrap();
            assert!(matches!(
                QuerySession::from_checkpoint(
                    &f.facts, &f.graph, &next, &runtime, &legacy, producer
                ),
                Err(Error::Invalid("checkpoint version"))
            ));
            let view = inspection::CheckpointView::open(
                &f.facts,
                &f.graph,
                &legacy,
                &inspection::InspectionLimits::default(),
            )
            .unwrap();
            assert_eq!(view.header().version, version);
            assert_eq!(view.header().runtime_issue_sites, 0);
            assert_eq!(view.header().heap_owners, 0);
            assert!(view.context_inventory(1).unwrap().summary.contexts > 0);
            assert!(matches!(
                view.export_replay(
                    NodeId(0),
                    None,
                    &dir.path().join("legacy-replay"),
                    &replay::ReplayLimits::default()
                ),
                Err(Error::Invalid(
                    "legacy checkpoint replay requires frozen legacy operator"
                ))
            ));
            let invalid = dir
                .path()
                .join(format!("legacy-{version}-with-new-section.bin"));
            let sections = data
                .iter()
                .zip(&counts)
                .enumerate()
                .map(|(i, (bytes, count))| Section {
                    id: i as u32 + 1,
                    count: *count,
                    bytes,
                })
                .chain(std::iter::once(Section {
                    id: 21,
                    count: 0,
                    bytes: &[],
                }))
                .collect::<Vec<_>>();
            selector_artifacts::write(&invalid, ArtifactKind::Continuation, &sections).unwrap();
            assert!(
                inspection::CheckpointView::open(
                    &f.facts,
                    &f.graph,
                    &invalid,
                    &inspection::InspectionLimits::default()
                )
                .is_err()
            );
            drop(sections);
            data[0][..4].copy_from_slice(&VERSION.to_le_bytes());
            let sections = data
                .iter()
                .zip(&counts)
                .enumerate()
                .map(|(i, (bytes, count))| Section {
                    id: i as u32 + 1,
                    count: *count,
                    bytes,
                })
                .collect::<Vec<_>>();
            let missing = dir.path().join(format!("new-with-v{version}-sections.bin"));
            selector_artifacts::write(&missing, ArtifactKind::Continuation, &sections).unwrap();
            assert!(
                inspection::CheckpointView::open(
                    &f.facts,
                    &f.graph,
                    &missing,
                    &inspection::InspectionLimits::default()
                )
                .is_err()
            );
        }
    }

    #[test]
    fn widened_argument_context_and_joined_frame_survive_checkpoint() {
        let mut f = Fixture::new(&["root", "A", "B", "C", "callee", "changed"]);
        let args = [f.args(&[1]), f.args(&[2]), f.args(&[3])];
        let mut operations = Vec::new();
        for class in 1..=3 {
            f.facts.symbols[class].kind = 13;
            operations.push(OperationRecord {
                target: SymbolId(class as u32),
                dest: ValueId(class as u32),
                ..op(Opcode::Allocate)
            });
        }
        for arguments in args {
            operations.push(OperationRecord {
                target: SymbolId(4),
                arguments,
                ..op(Opcode::Call)
            });
        }
        f.body(0, operations);
        for class in 1..=3 {
            f.body(class, vec![]);
        }
        f.body(
            4,
            vec![OperationRecord {
                target: SymbolId(5),
                ..op(Opcode::Call)
            }],
        );
        f.body(5, vec![]);
        f.seal();
        let mut next = options(1);
        next.context_policy = ContextPolicy::BoundedArguments {
            max_variants_per_receiver: 1,
        };
        let mut capped = next.clone();
        capped.max_steps = 1;
        let mut stopped = QuerySession::new(&f.facts, &f.graph, &capped).unwrap();
        stopped.execute(&[root()]).unwrap();
        assert_eq!(stopped.stop_reason(), Some(StopReason::StepLimit));
        assert_eq!(stopped.contexts.iter().filter(|c| c.widened).count(), 1);
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("widened.bin");
        let producer = ContentHash([77; 32]);
        stopped.save_checkpoint(&path, producer).unwrap();
        let mut uninterrupted = QuerySession::new(&f.facts, &f.graph, &next).unwrap();
        uninterrupted.execute(&[root()]).unwrap();
        let expected = uninterrupted.analyze(&[NodeId(5)]).unwrap();
        next.workers = 4;
        let runtime = SolverRuntime::new(&next).unwrap();
        let mut loaded =
            QuerySession::from_checkpoint(&f.facts, &f.graph, &next, &runtime, &path, producer)
                .unwrap();
        assert_eq!(loaded.contexts.iter().filter(|c| c.widened).count(), 1);
        loaded.resume().unwrap();
        let actual = loaded.analyze(&[NodeId(5)]).unwrap();
        assert_answer(&expected, &actual);
        assert_eq!(actual.metrics.edge_visits, expected.metrics.edge_visits);
    }

    #[test]
    fn stale_program_producer_and_semantic_options_fail_but_resource_changes_are_allowed() {
        let mut f = Fixture::heap();
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("state.bin");
        let producer = ContentHash([73; 32]);
        paused(&f).save_checkpoint(&path, producer).unwrap();
        let next = options(2);
        let runtime = SolverRuntime::new(&next).unwrap();
        assert!(
            QuerySession::from_checkpoint(
                &f.facts,
                &f.graph,
                &next,
                &runtime,
                &path,
                ContentHash([74; 32])
            )
            .is_err()
        );
        for changed in [
            SolveOptions {
                max_set_members: 3,
                ..next.clone()
            },
            SolveOptions {
                quantum: 3,
                ..next.clone()
            },
            SolveOptions {
                context_policy: ContextPolicy::BoundedArguments {
                    max_variants_per_receiver: 2,
                },
                ..next.clone()
            },
            SolveOptions {
                execution_roots: Some(Arc::from([])),
                ..next.clone()
            },
            SolveOptions {
                memory_budget_bytes: 1,
                ..next.clone()
            },
            SolveOptions {
                max_contexts: 1,
                ..next.clone()
            },
        ] {
            assert!(
                QuerySession::from_checkpoint(
                    &f.facts, &f.graph, &changed, &runtime, &path, producer
                )
                .is_err()
            );
        }
        f.facts.bodies[0].body_hash = ContentHash([5; 32]);
        assert!(matches!(
            QuerySession::from_checkpoint(&f.facts, &f.graph, &next, &runtime, &path, producer),
            Err(Error::Invalid("checkpoint snapshot content seal"))
        ));
    }

    #[test]
    fn malformed_sections_references_versions_and_full_checksum_fail_closed() {
        let f = Fixture::heap();
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("original.bin");
        let bad = directory.path().join("bad.bin");
        let producer = ContentHash([75; 32]);
        paused(&f).save_checkpoint(&path, producer).unwrap();
        let original = selector_artifacts::open(&path, ArtifactKind::Continuation).unwrap();
        let next = options(1);
        let runtime = SolverRuntime::new(&next).unwrap();
        for (case, (id, offset, replacement)) in [
            (6, 12, u32::MAX.to_le_bytes().to_vec()),
            (6, 24, u64::MAX.to_le_bytes().to_vec()),
            (8, 8, (f.facts.symbols.len() as u32).to_le_bytes().to_vec()),
            (10, 16, u32::MAX.to_le_bytes().to_vec()),
            (13, 0, u32::MAX.to_le_bytes().to_vec()),
            (17, 8, 2u32.to_le_bytes().to_vec()),
            (18, 0, u32::MAX.to_le_bytes().to_vec()),
            (18, 16, u64::MAX.to_le_bytes().to_vec()),
        ]
        .into_iter()
        .enumerate()
        {
            let bad = directory.path().join(format!("bad-{case}.bin"));
            let mut data: Vec<Vec<u8>> = (1..=SECTION_COUNT)
                .map(|i| original.section(i).unwrap().to_vec())
                .collect();
            assert!(
                offset + replacement.len() <= data[id - 1].len(),
                "fixture must exercise section {id}"
            );
            data[id - 1][offset..offset + replacement.len()].copy_from_slice(&replacement);
            let sections: Vec<_> = data
                .iter()
                .enumerate()
                .map(|(i, bytes)| Section {
                    id: i as u32 + 1,
                    count: original.count(i as u32 + 1).unwrap(),
                    bytes,
                })
                .collect();
            selector_artifacts::write(&bad, ArtifactKind::Continuation, &sections).unwrap();
            assert!(
                QuerySession::from_checkpoint(&f.facts, &f.graph, &next, &runtime, &bad, producer)
                    .is_err(),
                "section {id},offset {offset}"
            );
        }
        for (case, omitted) in [(0, 13), (1, 11)] {
            let data: Vec<Vec<u8>> = (1..=SECTION_COUNT)
                .map(|id| {
                    if id == omitted {
                        Vec::new()
                    } else {
                        original.section(id).unwrap().to_vec()
                    }
                })
                .collect();
            let sections: Vec<_> = data
                .iter()
                .enumerate()
                .map(|(i, bytes)| Section {
                    id: i as u32 + 1,
                    count: if i as u32 + 1 == omitted {
                        0
                    } else {
                        original.count(i as u32 + 1).unwrap()
                    },
                    bytes,
                })
                .collect();
            let malformed = directory.path().join(format!("omitted-{case}.bin"));
            selector_artifacts::write(&malformed, ArtifactKind::Continuation, &sections).unwrap();
            assert!(
                QuerySession::from_checkpoint(
                    &f.facts, &f.graph, &next, &runtime, &malformed, producer
                )
                .is_err()
            );
        }
        let data: Vec<_> = (1..=SECTION_COUNT)
            .map(|id| original.section(id).unwrap())
            .collect();
        let sections: Vec<_> = data
            .iter()
            .enumerate()
            .map(|(i, bytes)| Section {
                id: i as u32 + 1,
                count: original.count(i as u32 + 1).unwrap() + u64::from(i == 12),
                bytes,
            })
            .collect();
        let malformed = directory.path().join("count.bin");
        selector_artifacts::write(&malformed, ArtifactKind::Continuation, &sections).unwrap();
        assert!(
            QuerySession::from_checkpoint(
                &f.facts, &f.graph, &next, &runtime, &malformed, producer
            )
            .is_err()
        );
        let mut bytes = std::fs::read(&path).unwrap();
        let last = bytes.len() - 1;
        bytes[last] ^= 1;
        std::fs::write(&bad, bytes).unwrap();
        assert!(
            QuerySession::from_checkpoint(&f.facts, &f.graph, &next, &runtime, &bad, producer)
                .is_err()
        );
    }
}
