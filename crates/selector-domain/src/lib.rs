//! Finite abstract values and exact semantic dependencies.
//!
//! Pools own contiguous records. Contexts and workers carry copyable IDs, never
//! recursively owned environments. Allocation-site and lexical callback identity
//! are deliberately finite; dynamic call history is not an identity component.
mod heap;
pub mod snapshot;
pub use heap::*;
use selector_types::*;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

pub const UNKNOWN_VALUE: u32 = 1;
pub const WIDENED_VALUE: u32 = 2;
pub const UNKNOWN_FIELD: u32 = 4;
pub const UNKNOWN_CALLBACK: u32 = 8;
/// Every unknown alternative is covered by an UpperBound atom. This bit is
/// coverage evidence, not an additional alternative; an unbounded join clears it.
pub const UNKNOWN_TYPED: u32 = 16;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AtomKind {
    Object,
    Callback,
    /// One conjunctive compiler result constraint, referenced by declaration
    /// symbol and optional operation-specific specialization. Never an object.
    UpperBound,
    /// An explicit index-insensitive element carrier. Symbol is a synthetic
    /// element-channel tag, not a class; site is its PackSequence operation.
    Container,
}
pub const LOCAL_BINDING: u32 = 1 << 31;
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Atom {
    pub kind: AtomKind,
    pub site: OperationId,
    pub symbol: SymbolId,
    pub binding: u32,
}
/// Allocation sites and exact root classes occupy disjoint compact namespaces.
/// The final ID remains reserved for an unresolved instance receiver.
pub fn object_owner(atom: Atom, operation_count: usize) -> Result<u32, Error> {
    if atom.binding != 0 {
        return Err(Error::Invalid(
            "partitioned object requires heap owner lookup",
        ));
    }
    if !atom.site.is_none() {
        if atom.site.index() >= operation_count {
            return Err(Error::Invalid("object allocation site"));
        }
        return Ok(atom.site.0);
    }
    let owner = operation_count
        .checked_add(atom.symbol.index())
        .ok_or(Error::Limit("root object owners"))?;
    if owner >= u32::MAX as usize {
        return Err(Error::Limit("root object owners"));
    }
    Ok(owner as u32)
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Value {
    pub set: SetId,
    pub unknown: u32,
}
impl Value {
    pub const EMPTY: Self = Self {
        set: SetId(0),
        unknown: 0,
    };
    pub const TOP: Self = Self {
        set: SetId(0),
        unknown: UNKNOWN_VALUE,
    };
    pub fn is_bottom(self) -> bool {
        self.set == SetId(0) && self.unknown == 0
    }
    pub fn is_unknown(self) -> bool {
        self.unknown != 0
    }
    pub fn is_unbounded(self) -> bool {
        self.is_unknown() && self.unknown & UNKNOWN_TYPED == 0
    }
}
#[derive(Clone, Copy, Debug)]
struct SetEntry {
    start: u32,
    len: u32,
    next: SetId,
}
fn hash<T: Hash + ?Sized>(x: &T) -> u64 {
    let mut h = std::collections::hash_map::DefaultHasher::new();
    x.hash(&mut h);
    h.finish()
}

/// Interning indexes hash -> collision chain, without owning a duplicate set.
#[derive(Debug)]
pub struct ValuePool {
    atoms: Vec<Atom>,
    entries: Vec<SetEntry>,
    heads: HashMap<u64, SetId>,
    scratch: Vec<Atom>,
    max_members: usize,
}
impl ValuePool {
    pub fn new(max_members: usize) -> Self {
        Self {
            atoms: Vec::new(),
            entries: vec![SetEntry {
                start: 0,
                len: 0,
                next: SetId::NONE,
            }],
            heads: HashMap::new(),
            scratch: Vec::new(),
            max_members: max_members.max(1),
        }
    }
    pub fn clear(&mut self) {
        self.atoms.clear();
        self.entries.truncate(1);
        self.heads.clear();
        self.scratch.clear();
    }
    pub fn members(&self, v: Value) -> &[Atom] {
        let e = self.entries[v.set.index()];
        &self.atoms[e.start as usize..(e.start + e.len) as usize]
    }
    pub fn member_limit(&self) -> usize {
        self.max_members
    }
    pub fn lookup(&self, members: &[Atom], unknown: u32) -> Option<Value> {
        if members.is_empty() {
            return Some(Value {
                set: SetId(0),
                unknown,
            });
        }
        let mut id = self
            .heads
            .get(&hash(members))
            .copied()
            .unwrap_or(SetId::NONE);
        while !id.is_none() {
            let e = self.entries[id.index()];
            if self.atoms[e.start as usize..(e.start + e.len) as usize] == *members {
                return Some(Value { set: id, unknown });
            }
            id = e.next;
        }
        None
    }
    pub fn import(&mut self, source: &ValuePool, value: Value) -> Result<Value, Error> {
        self.intern(source.members(value), value.unknown)
    }
    pub fn import_bindings(
        &mut self,
        source: &ValuePool,
        value: Value,
        bindings: &[u32],
    ) -> Result<Value, Error> {
        if !source
            .members(value)
            .iter()
            .any(|a| a.kind == AtomKind::Callback && a.binding & LOCAL_BINDING != 0)
        {
            return self.import(source, value);
        }
        let mut scratch = std::mem::take(&mut self.scratch);
        scratch.clear();
        for atom in source.members(value) {
            let mut atom = *atom;
            if atom.kind == AtomKind::Callback && atom.binding & LOCAL_BINDING != 0 {
                atom.binding = *bindings
                    .get((atom.binding & !LOCAL_BINDING) as usize)
                    .ok_or(Error::Invalid("local closure binding"))?;
            }
            scratch.push(atom);
        }
        scratch.sort_unstable();
        scratch.dedup();
        let result = self.intern(&scratch, value.unknown);
        scratch.clear();
        self.scratch = scratch;
        result
    }
    /// Raw callback binding history is payload, never a family identity. Static allocation
    /// sites and finite receiver-root origins remain in object keys so closures
    /// do not immediately join independently partitioned heap receivers again.
    pub fn lookup_family(
        &self,
        source: &ValuePool,
        value: Value,
        scratch: &mut Vec<Atom>,
    ) -> Option<Value> {
        scratch.clear();
        for atom in source.members(value) {
            let mut atom = *atom;
            if atom.kind == AtomKind::Callback {
                atom.binding = 0;
            }
            scratch.push(atom);
        }
        scratch.sort_unstable();
        scratch.dedup();
        self.lookup(scratch, value.unknown)
    }
    pub fn family(&mut self, source: &ValuePool, value: Value) -> Result<Value, Error> {
        let mut scratch = std::mem::take(&mut self.scratch);
        scratch.clear();
        for atom in source.members(value) {
            let mut atom = *atom;
            if atom.kind == AtomKind::Callback {
                atom.binding = 0;
            }
            scratch.push(atom);
        }
        scratch.sort_unstable();
        scratch.dedup();
        let result = self.intern(&scratch, value.unknown);
        scratch.clear();
        self.scratch = scratch;
        result
    }
    pub fn singleton(&mut self, atom: Atom) -> Result<Value, Error> {
        self.intern(&[atom], 0)
    }
    /// `members` must be sorted and unique. Unknown alternatives are retained
    /// alongside known alternatives; they never masquerade as an exact set.
    pub fn intern(&mut self, members: &[Atom], unknown: u32) -> Result<Value, Error> {
        let bounded = members.iter().any(|a| a.kind == AtomKind::UpperBound);
        if (unknown & UNKNOWN_TYPED != 0 && !bounded) || (bounded && unknown & !UNKNOWN_TYPED == 0)
        {
            return Err(Error::Invalid("typed unknown coverage"));
        }
        if members.is_empty() {
            return Ok(Value {
                set: SetId(0),
                unknown,
            });
        }
        if members.len() > self.max_members {
            return Ok(Value {
                set: SetId(0),
                unknown: (unknown | WIDENED_VALUE) & !UNKNOWN_TYPED,
            });
        }
        let h = hash(members);
        let head = self.heads.get(&h).copied().unwrap_or(SetId::NONE);
        let mut id = head;
        while !id.is_none() {
            let e = self.entries[id.index()];
            if self.atoms[e.start as usize..(e.start + e.len) as usize] == *members {
                return Ok(Value { set: id, unknown });
            }
            id = e.next;
        }
        let id = SetId::checked(self.entries.len())?;
        let start = u32::try_from(self.atoms.len()).map_err(|_| Error::Limit("value pool"))?;
        self.atoms
            .try_reserve(members.len())
            .map_err(|_| Error::Limit("value pool allocation"))?;
        self.entries
            .try_reserve(1)
            .map_err(|_| Error::Limit("set allocation"))?;
        self.atoms.extend_from_slice(members);
        self.entries.push(SetEntry {
            start,
            len: members.len() as u32,
            next: head,
        });
        self.heads.insert(h, id);
        Ok(Value { set: id, unknown })
    }
    pub fn join(&mut self, a: Value, b: Value) -> Result<Value, Error> {
        if a == b {
            return Ok(a);
        }
        if a.is_bottom() {
            return Ok(b);
        }
        if b.is_bottom() {
            return Ok(a);
        }
        // Once widened, finite alternatives may be omitted without changing the
        // conservative meaning. Keeping this absorbing ensures termination.
        let mut unknown = (a.unknown | b.unknown) & !UNKNOWN_TYPED;
        if unknown != 0 && !a.is_unbounded() && !b.is_unbounded() {
            unknown |= UNKNOWN_TYPED;
        }
        if unknown & WIDENED_VALUE != 0 {
            return Ok(Value {
                set: SetId(0),
                unknown: unknown & !UNKNOWN_TYPED,
            });
        }
        if a.set == b.set {
            return Ok(Value {
                set: a.set,
                unknown,
            });
        }
        let mut scratch = std::mem::take(&mut self.scratch);
        scratch.clear();
        scratch.extend_from_slice(self.members(a));
        scratch.extend_from_slice(self.members(b));
        scratch.sort_unstable();
        scratch.dedup();
        let result = self.intern(&scratch, unknown);
        scratch.clear();
        self.scratch = scratch;
        result
    }
    pub fn owned_bytes(&self) -> usize {
        self.atoms.capacity() * std::mem::size_of::<Atom>()
            + self.entries.capacity() * std::mem::size_of::<SetEntry>()
            + self.heads.capacity() * 24
            + self.scratch.capacity() * std::mem::size_of::<Atom>()
    }
    pub fn len(&self) -> usize {
        self.entries.len()
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct FrameId(pub u32);
#[derive(Clone, Copy, Debug)]
struct FrameEntry {
    start: u32,
    len: u32,
    next: FrameId,
}
#[derive(Debug)]
pub struct FramePool {
    values: Vec<Value>,
    entries: Vec<FrameEntry>,
    heads: HashMap<u64, FrameId>,
}
impl Default for FramePool {
    fn default() -> Self {
        Self {
            values: Vec::new(),
            entries: vec![FrameEntry {
                start: 0,
                len: 0,
                next: FrameId(u32::MAX),
            }],
            heads: HashMap::new(),
        }
    }
}
impl FramePool {
    pub fn get(&self, id: FrameId) -> &[Value] {
        let e = self.entries[id.0 as usize];
        &self.values[e.start as usize..(e.start + e.len) as usize]
    }
    pub fn lookup(&self, values: &[Value]) -> Option<FrameId> {
        if values.is_empty() {
            return Some(FrameId(0));
        }
        let mut id = self
            .heads
            .get(&hash(values))
            .copied()
            .unwrap_or(FrameId(u32::MAX));
        while id.0 != u32::MAX {
            let e = self.entries[id.0 as usize];
            if self.get(id) == values {
                return Some(id);
            }
            id = e.next;
        }
        None
    }
    pub fn intern(&mut self, values: &[Value]) -> Result<FrameId, Error> {
        if values.is_empty() {
            return Ok(FrameId(0));
        }
        let h = hash(values);
        let head = self.heads.get(&h).copied().unwrap_or(FrameId(u32::MAX));
        let mut id = head;
        while id.0 != u32::MAX {
            let e = self.entries[id.0 as usize];
            if self.get(id) == values {
                return Ok(id);
            }
            id = e.next;
        }
        let id = FrameId(u32::try_from(self.entries.len()).map_err(|_| Error::Limit("frame IDs"))?);
        let start = u32::try_from(self.values.len()).map_err(|_| Error::Limit("frame values"))?;
        self.values
            .try_reserve(values.len())
            .map_err(|_| Error::Limit("frame allocation"))?;
        self.values.extend_from_slice(values);
        self.entries.push(FrameEntry {
            start,
            len: values.len() as u32,
            next: head,
        });
        self.heads.insert(h, id);
        Ok(id)
    }
    pub fn owned_bytes(&self) -> usize {
        self.values.capacity() * std::mem::size_of::<Value>()
            + self.entries.capacity() * std::mem::size_of::<FrameEntry>()
            + self.heads.capacity() * 24
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ContextKey {
    pub node: NodeId,
    pub receiver: Value,
    pub arguments: FrameId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SlotKind {
    Summary,
    Field,
    Capture,
    Dispatch,
    Body,
    /// A JVM/Scala static compiler field; owner is its SymbolId, member is zero.
    StaticField,
    /// Coarse writes at one allocation site, visible to every exact partition.
    FieldWildcard,
    /// Derived union of exact and coarse writes, read by coarse objects only.
    FieldAll,
    /// A drained-frontier no-store marker for one complete field lookup.
    FieldMissing,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Slot {
    pub kind: SlotKind,
    pub owner: u32,
    pub member: u32,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Read {
    pub slot: Slot,
    pub version: u64,
    pub present: bool,
}
#[derive(Clone, Copy, Debug)]
struct Dependency {
    query: ContextId,
    generation: u64,
    next: u32,
    read: Read,
}
/// Indexed read subscriptions include missing slots. Replacing/removing a slot
/// invalidates the same consumers as adding it. Unknown writers invalidate all.
#[derive(Default, Debug)]
pub struct Dependencies {
    heads: HashMap<Slot, u32>,
    members: HashMap<(ContextId, Slot), u32>,
    edges: Vec<Dependency>,
    generation: Vec<u64>,
    invalid: Vec<bool>,
    epoch: u64,
    #[cfg(test)]
    membership_probes: usize,
}
impl Dependencies {
    pub fn subscribe(&mut self, query: ContextId, read: Read) -> Result<(), Error> {
        let i = query.index();
        if self.generation.len() <= i {
            self.generation.resize(i + 1, 1);
            self.invalid.resize(i + 1, false);
        }
        let generation = self.generation[i];
        #[cfg(test)]
        {
            self.membership_probes += 1;
        }
        if let Some(edge) = self.members.get(&(query, read.slot)).copied() {
            let entry = &mut self.edges[edge as usize];
            entry.generation = generation;
            entry.read = read;
            return Ok(());
        }
        let next = self.heads.get(&read.slot).copied().unwrap_or(u32::MAX);
        let edge = EdgeId::checked(self.edges.len())?.0;
        self.edges.push(Dependency {
            query,
            generation,
            next,
            read,
        });
        self.heads.insert(read.slot, edge);
        self.members.insert((query, read.slot), edge);
        Ok(())
    }
    pub fn acknowledge(&mut self, query: ContextId) {
        if let Some(x) = self.invalid.get_mut(query.index()) {
            *x = false;
        }
    }
    pub fn replace(&mut self, query: ContextId, reads: &[Read]) -> Result<(), Error> {
        let i = query.index();
        if self.generation.len() <= i {
            self.generation.resize(i + 1, 0);
            self.invalid.resize(i + 1, false);
        }
        self.generation[i] = self.generation[i].wrapping_add(1);
        self.invalid[i] = false;
        for r in reads {
            self.subscribe(query, *r)?;
        }
        Ok(())
    }
    pub fn publish(&mut self, slots: &[Slot], before: u64, after: u64, out: &mut Vec<ContextId>) {
        if before != self.epoch {
            self.invalidate_all(out);
        } else {
            for slot in slots {
                let mut edge = self.heads.get(slot).copied().unwrap_or(u32::MAX);
                while edge != u32::MAX {
                    let e = self.edges[edge as usize];
                    let i = e.query.index();
                    if self.generation[i] == e.generation && !self.invalid[i] {
                        self.invalid[i] = true;
                        out.push(e.query);
                    }
                    edge = e.next;
                }
            }
        }
        self.epoch = after;
    }
    pub fn invalidate_all(&mut self, out: &mut Vec<ContextId>) {
        for i in 0..self.generation.len() {
            if !self.invalid[i] {
                self.invalid[i] = true;
                out.push(ContextId(i as u32));
            }
        }
    }
    pub fn active_reads(&self) -> impl Iterator<Item = (ContextId, Read)> + '_ {
        self.edges
            .iter()
            .filter(|e| self.generation[e.query.index()] == e.generation)
            .map(|e| (e.query, e.read))
    }
    pub fn epoch(&self) -> u64 {
        self.epoch
    }
    pub fn clear_edges(&mut self) {
        self.heads.clear();
        self.members.clear();
        self.edges.clear();
        self.generation.fill(0);
        self.invalid.fill(false);
    }
    pub fn owned_bytes(&self) -> usize {
        self.heads.capacity() * 32
            + self.members.capacity() * 32
            + self.edges.capacity() * std::mem::size_of::<Dependency>()
            + self.generation.capacity() * 8
            + self.invalid.capacity()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn obj(n: u32) -> Atom {
        Atom {
            kind: AtomKind::Object,
            site: OperationId(n),
            symbol: SymbolId(n),
            binding: 0,
        }
    }
    #[test]
    fn canonical_join_retains_unknown_and_is_idempotent() {
        let mut p = ValuePool::new(8);
        let a = p.singleton(obj(1)).unwrap();
        let b = p.singleton(obj(2)).unwrap();
        let ab = p.join(a, b).unwrap();
        assert_eq!(p.join(b, a).unwrap(), ab);
        assert_eq!(p.join(ab, a).unwrap(), ab);
        let mixed = p.join(ab, Value::TOP).unwrap();
        assert!(mixed.is_unknown());
        assert_eq!(p.members(mixed).len(), 2);
        let count = p.len();
        for _ in 0..1000 {
            assert_eq!(p.join(a, b).unwrap(), ab);
        }
        assert_eq!(p.len(), count);
    }
    #[test]
    fn finite_widening_absorbs_future_allocations() {
        let mut p = ValuePool::new(1);
        let a = p.singleton(obj(1)).unwrap();
        let b = p.singleton(obj(2)).unwrap();
        let top = p.join(a, b).unwrap();
        assert_eq!(top.unknown, WIDENED_VALUE);
        assert_eq!(p.join(top, a).unwrap(), top);
    }
    #[test]
    fn negative_reads_replacements_removal_and_unknown_writer() {
        let mut d = Dependencies::default();
        let slot = Slot {
            kind: SlotKind::Field,
            owner: 7,
            member: 9,
        };
        d.replace(
            ContextId(0),
            &[Read {
                slot,
                version: 0,
                present: false,
            }],
        )
        .unwrap();
        let mut out = Vec::new();
        d.publish(&[slot], 0, 1, &mut out);
        assert_eq!(out, vec![ContextId(0)]);
        d.replace(
            ContextId(0),
            &[Read {
                slot,
                version: 1,
                present: true,
            }],
        )
        .unwrap();
        out.clear();
        d.publish(&[slot], 1, 2, &mut out);
        assert_eq!(out, vec![ContextId(0)]);
        d.replace(ContextId(1), &[]).unwrap();
        out.clear();
        d.publish(&[], 99, 3, &mut out);
        assert_eq!(out, vec![ContextId(1)]);
    }
    #[test]
    fn high_fanout_admission_uses_one_membership_probe_and_reuses_generation_edges() {
        const N: usize = 16_384;
        let shared = Slot {
            kind: SlotKind::StaticField,
            owner: 7,
            member: 0,
        };
        let other = Slot {
            kind: SlotKind::Summary,
            owner: 9,
            member: 0,
        };
        let mut d = Dependencies::default();
        let read = Read {
            slot: shared,
            version: 0,
            present: false,
        };
        for i in 0..N {
            d.subscribe(ContextId(i as u32), read).unwrap();
        }
        assert_eq!(d.membership_probes, N);
        assert_eq!(d.edges.len(), N);
        assert_eq!(d.members.len(), N);
        let bytes = d.owned_bytes();
        // Repeated hits include the oldest subscriber in the slot's reverse
        // chain. Their work and retained allocation are independent of fanout.
        for _ in 0..2 {
            for i in 0..N {
                d.subscribe(
                    ContextId(i as u32),
                    Read {
                        version: 1,
                        present: true,
                        ..read
                    },
                )
                .unwrap();
            }
        }
        assert_eq!(d.membership_probes, 3 * N);
        assert_eq!(d.owned_bytes(), bytes);
        assert_eq!(d.edges.len(), N);
        for i in (0..N).step_by(2) {
            d.replace(
                ContextId(i as u32),
                &[Read {
                    slot: other,
                    version: 0,
                    present: false,
                }],
            )
            .unwrap();
        }
        let mut out = Vec::new();
        d.publish(&[shared], 0, 1, &mut out);
        assert_eq!(out.len(), N / 2);
        assert!(out.iter().all(|id| id.0 % 2 == 1));
        for i in (0..N).step_by(2) {
            d.replace(ContextId(i as u32), &[read, read]).unwrap();
        }
        assert_eq!(
            d.edges.len(),
            N + N / 2,
            "replace revives the existing pair once"
        );
        assert_eq!(d.active_reads().count(), N);
        out.clear();
        d.publish(&[other], 1, 2, &mut out);
        assert!(
            out.is_empty(),
            "removed reads cannot wake the new generation"
        );
        d.clear_edges();
        assert!(d.members.is_empty() && d.edges.is_empty());
        d.subscribe(ContextId(0), read).unwrap();
        out.clear();
        d.publish(&[shared], 2, 3, &mut out);
        assert_eq!(out, vec![ContextId(0)]);
    }
    #[test]
    fn typed_unknown_alternatives_do_not_cover_an_independent_unbounded_value() {
        let mut p = ValuePool::new(8);
        let clause = |symbol| Atom {
            kind: AtomKind::UpperBound,
            site: OperationId::NONE,
            symbol: SymbolId(symbol),
            binding: 0,
        };
        let narrow = p
            .intern(&[clause(1)], UNKNOWN_VALUE | UNKNOWN_TYPED)
            .unwrap();
        let other = p
            .intern(&[clause(2)], UNKNOWN_FIELD | UNKNOWN_TYPED)
            .unwrap();
        let alternatives = p.join(narrow, other).unwrap();
        assert!(!alternatives.is_unbounded());
        assert_eq!(p.members(alternatives), &[clause(1), clause(2)]);
        let exact = p.singleton(obj(7)).unwrap();
        let mixed = p.join(exact, narrow).unwrap();
        assert!(!mixed.is_unbounded());
        assert!(p.members(mixed).iter().any(|a| a.kind == AtomKind::Object));
        let missing = p.join(mixed, Value::TOP).unwrap();
        assert!(missing.is_unbounded());
        assert_eq!(missing.unknown & UNKNOWN_TYPED, 0);
        assert!(
            p.members(missing).contains(&clause(1)),
            "bounded branch remains explicit beside broad branch"
        );
        let mut tiny = ValuePool::new(1);
        let widened = tiny.import(&p, alternatives).unwrap();
        assert!(widened.is_unbounded());
        assert_eq!(widened.unknown & UNKNOWN_TYPED, 0);
    }
}
