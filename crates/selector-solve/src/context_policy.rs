//! Optional argument abstraction. Receiver identities remain separate.
use crate::{Context, SolveOptions};
use selector_domain::{
    AtomKind, ContextKey, FrameId, UNKNOWN_TYPED, Value, ValuePool, WIDENED_VALUE,
};
use selector_types::{Error, IdRange, OperationId, SymbolId};
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ContextPolicy {
    /// Preserve every distinct receiver and argument frame.
    #[default]
    Exact,
    /// Keep this many exact frames per (node, receiver, callback-code shape),
    /// then use one joined argument frame within that immutable shape. Callback
    /// code and argument positions remain separate; captures/data may join.
    /// Frames containing wrappers with nested callbacks remain exact.
    /// Joining never removes concrete receiver/callback choices;
    /// the existing finite-value limit explicitly widens oversized alternatives.
    BoundedArguments { max_variants_per_receiver: usize },
}

pub(crate) fn cache_policy_key(options: &SolveOptions) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"selector-context-policy-v3-callback-origins");
    h.update((options.quantum as u64).to_le_bytes());
    match options.context_policy {
        ContextPolicy::Exact => h.update([0]),
        ContextPolicy::BoundedArguments {
            max_variants_per_receiver,
        } => {
            h.update([1]);
            h.update((max_variants_per_receiver as u64).to_le_bytes());
        }
    }
    h.finalize().into()
}

/// Query-owned identity for an immutable callback-code signature. Zero is the
/// empty, zero-argument signature (and the unused exact-policy sentinel).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CallbackShapeId(pub u32);

/// One callback code at an argument position, independent of capture binding.
/// Both IDs NONE denotes an unknown alternative; known callbacks have both IDs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CallbackShapeAtom {
    pub argument: u32,
    pub site: OperationId,
    pub symbol: SymbolId,
}
#[derive(Clone, Copy, Debug)]
pub struct CallbackShape<'a> {
    pub arity: u32,
    pub atoms: &'a [CallbackShapeAtom],
}
#[derive(Clone, Copy)]
struct ShapeRow {
    arity: u32,
    atoms: IdRange,
    next: CallbackShapeId,
}
/// Flat owned rows, with one hash head per distinct hash. Lookup streams the
/// borrowed value pool: no temporary vector, per-record owner or worker bitmap.
#[derive(Default)]
pub struct CallbackShapes {
    atoms: Vec<CallbackShapeAtom>,
    rows: Vec<ShapeRow>,
    heads: HashMap<u64, CallbackShapeId>,
}
struct ShapeAtoms<'a> {
    pool: &'a ValuePool,
    args: &'a [Value],
    argument: usize,
    member: usize,
    previous: Option<(OperationId, SymbolId)>,
    unknown: bool,
}
impl<'a> ShapeAtoms<'a> {
    fn new(pool: &'a ValuePool, args: &'a [Value]) -> Self {
        Self {
            pool,
            args,
            argument: 0,
            member: 0,
            previous: None,
            unknown: false,
        }
    }
}
impl Iterator for ShapeAtoms<'_> {
    type Item = CallbackShapeAtom;
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(value) = self.args.get(self.argument) {
            let members = self.pool.members(*value);
            while let Some(atom) = members.get(self.member) {
                self.member += 1;
                if atom.kind != AtomKind::Callback {
                    continue;
                }
                let code = (atom.site, atom.symbol);
                if self.previous == Some(code) {
                    continue;
                }
                self.previous = Some(code);
                return Some(CallbackShapeAtom {
                    argument: self.argument as u32,
                    site: atom.site,
                    symbol: atom.symbol,
                });
            }
            if value.is_unknown() && !self.unknown {
                self.unknown = true;
                return Some(CallbackShapeAtom {
                    argument: self.argument as u32,
                    site: OperationId::NONE,
                    symbol: SymbolId::NONE,
                });
            }
            self.argument += 1;
            self.member = 0;
            self.previous = None;
            self.unknown = false;
        }
        None
    }
}
fn shape_hash(arity: u32, atoms: impl Iterator<Item = CallbackShapeAtom>) -> (u64, usize) {
    let mut hash = std::collections::hash_map::DefaultHasher::new();
    arity.hash(&mut hash);
    let mut count = 0;
    for atom in atoms {
        atom.hash(&mut hash);
        count += 1;
    }
    count.hash(&mut hash);
    (hash.finish(), count)
}
impl CallbackShapes {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn len(&self) -> usize {
        self.rows.len() + 1
    }
    pub fn get(&self, id: CallbackShapeId) -> CallbackShape<'_> {
        if id.0 == 0 {
            return CallbackShape {
                arity: 0,
                atoms: &[],
            };
        }
        let row = self.rows[id.0 as usize - 1];
        CallbackShape {
            arity: row.arity,
            atoms: &self.atoms[row.atoms.range()],
        }
    }
    pub fn snapshot_shapes(&self) -> impl ExactSizeIterator<Item = CallbackShape<'_>> {
        (0..self.len()).map(|id| self.get(CallbackShapeId(id as u32)))
    }
    fn find(
        &self,
        hash: u64,
        arity: u32,
        mut matches: impl FnMut(&[CallbackShapeAtom]) -> bool,
    ) -> Option<CallbackShapeId> {
        if arity == 0 {
            return Some(CallbackShapeId(0));
        }
        let mut id = *self.heads.get(&hash)?;
        loop {
            let row = self.rows[id.0 as usize - 1];
            if row.arity == arity && matches(&self.atoms[row.atoms.range()]) {
                return Some(id);
            }
            if row.next.0 == 0 {
                return None;
            }
            id = row.next;
        }
    }
    pub fn lookup(&self, pool: &ValuePool, args: &[Value]) -> Option<CallbackShapeId> {
        let arity = u32::try_from(args.len()).ok()?;
        let (hash, _) = shape_hash(arity, ShapeAtoms::new(pool, args));
        self.find(hash, arity, |atoms| {
            ShapeAtoms::new(pool, args).eq(atoms.iter().copied())
        })
    }
    pub fn intern(&mut self, pool: &ValuePool, args: &[Value]) -> Result<CallbackShapeId, Error> {
        self.intern_bounded(pool, args, usize::MAX)
    }
    pub(crate) fn intern_bounded(
        &mut self,
        pool: &ValuePool,
        args: &[Value],
        budget: usize,
    ) -> Result<CallbackShapeId, Error> {
        let arity = u32::try_from(args.len()).map_err(|_| Error::Limit("callback shape arity"))?;
        let (hash, count) = shape_hash(arity, ShapeAtoms::new(pool, args));
        if let Some(id) = self.find(hash, arity, |atoms| {
            ShapeAtoms::new(pool, args).eq(atoms.iter().copied())
        }) {
            return Ok(id);
        }
        self.reserve(count, budget)?;
        let range = IdRange {
            start: self.atoms.len() as u32,
            len: count as u32,
        };
        self.atoms.extend(ShapeAtoms::new(pool, args));
        Ok(self.append(hash, arity, range))
    }
    pub fn intern_rows(
        &mut self,
        arity: u32,
        atoms: &[CallbackShapeAtom],
    ) -> Result<CallbackShapeId, Error> {
        self.intern_rows_bounded(arity, atoms, usize::MAX)
    }
    pub(crate) fn intern_rows_bounded(
        &mut self,
        arity: u32,
        atoms: &[CallbackShapeAtom],
        budget: usize,
    ) -> Result<CallbackShapeId, Error> {
        if atoms
            .iter()
            .any(|a| a.argument >= arity || a.site.is_none() != a.symbol.is_none())
            || atoms.windows(2).any(|w| w[0] >= w[1])
        {
            return Err(Error::Invalid("callback shape rows"));
        }
        let (hash, _) = shape_hash(arity, atoms.iter().copied());
        if let Some(id) = self.find(hash, arity, |existing| existing == atoms) {
            return Ok(id);
        }
        self.reserve(atoms.len(), budget)?;
        let range = IdRange {
            start: self.atoms.len() as u32,
            len: atoms.len() as u32,
        };
        self.atoms.extend_from_slice(atoms);
        Ok(self.append(hash, arity, range))
    }
    fn reserve(&mut self, atoms: usize, budget: usize) -> Result<(), Error> {
        let next = self
            .atoms
            .len()
            .checked_add(atoms)
            .ok_or(Error::Limit("callback shape tokens"))?;
        if next >= u32::MAX as usize || self.rows.len() >= u32::MAX as usize - 1 {
            return Err(Error::Limit("callback shape IDs"));
        }
        // Vec's amortized growth and a conservative hash-table growth estimate
        // are charged before allocation. Repeated hits never reserve storage.
        let grow = |cap: usize, required: usize| {
            if required <= cap {
                cap
            } else {
                required.max(cap.saturating_mul(2)).max(4)
            }
        };
        // HashMap capacity is bucket-rounded (3 -> 7 -> 14), rather than Vec's
        // doubling of usable entries. Reserve a conservative power-of-two
        // bucket upper bound, including the small first allocation.
        let head_capacity = if self.heads.len() < self.heads.capacity() {
            self.heads.capacity()
        } else {
            self.heads
                .len()
                .checked_add(1)
                .and_then(usize::checked_next_power_of_two)
                .and_then(|n| n.checked_mul(2))
                .map(|n| n.max(4))
                .ok_or(Error::Limit("callback shape index bytes"))?
        };
        let estimate = grow(self.atoms.capacity(), next)
            .checked_mul(std::mem::size_of::<CallbackShapeAtom>())
            .and_then(|n| {
                n.checked_add(
                    grow(self.rows.capacity(), self.rows.len() + 1)
                        .checked_mul(std::mem::size_of::<ShapeRow>())?,
                )
            })
            .and_then(|n| n.checked_add(head_capacity.checked_mul(24)?))
            .ok_or(Error::Limit("callback shape bytes"))?;
        if estimate > budget {
            return Err(Error::Limit("callback shape memory"));
        }
        self.atoms
            .try_reserve(atoms)
            .map_err(|_| Error::Limit("callback shape tokens"))?;
        self.rows
            .try_reserve(1)
            .map_err(|_| Error::Limit("callback shape rows"))?;
        self.heads
            .try_reserve(1)
            .map_err(|_| Error::Limit("callback shape index"))?;
        Ok(())
    }
    fn append(&mut self, hash: u64, arity: u32, atoms: IdRange) -> CallbackShapeId {
        let id = CallbackShapeId(self.rows.len() as u32 + 1);
        let next = self.heads.insert(hash, id).unwrap_or_default();
        self.rows.push(ShapeRow { arity, atoms, next });
        id
    }
    pub fn owned_bytes(&self) -> usize {
        self.atoms.capacity() * std::mem::size_of::<CallbackShapeAtom>()
            + self.rows.capacity() * std::mem::size_of::<ShapeRow>()
            + self.heads.capacity() * 24
    }
}
/// Overflow data may lose finite alternatives only through explicit widening.
/// It may never acquire another creation shape's callback code or unknown bit.
pub(crate) fn shape_covers_payload(
    shape: CallbackShape<'_>,
    pool: &ValuePool,
    args: &[Value],
) -> bool {
    if shape.arity as usize != args.len() {
        return false;
    }
    for atom in ShapeAtoms::new(pool, args) {
        if shape.atoms.binary_search(&atom).is_err()
            && !(atom.site.is_none() && args[atom.argument as usize].unknown & WIDENED_VALUE != 0)
        {
            return false;
        }
    }
    for atom in shape.atoms {
        let value = args[atom.argument as usize];
        if atom.site.is_none() {
            if !value.is_unknown() {
                return false;
            }
        } else if value.unknown & WIDENED_VALUE == 0
            && !pool.members(value).iter().any(|actual| {
                actual.kind == AtomKind::Callback
                    && actual.site == atom.site
                    && actual.symbol == atom.symbol
            })
        {
            return false;
        }
    }
    true
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct PolicyContextKey {
    pub key: ContextKey,
    pub shape: CallbackShapeId,
}
// Overflow payloads can converge to TOP across code signatures. Their immutable
// creation shapes remain part of index identity, never reconstructed from TOP.
pub(crate) fn context_index_key(context: &Context) -> PolicyContextKey {
    let mut key = context.key;
    if context.widened {
        key.arguments = FrameId(u32::MAX);
    }
    PolicyContextKey {
        key,
        shape: context.callback_shape,
    }
}

pub(crate) fn arguments_subsumed(pool: &ValuePool, broad: &[Value], narrow: &[Value]) -> bool {
    let n = broad.len().max(narrow.len());
    (0..n).all(|i| {
        value_subsumed(
            pool,
            broad.get(i).copied().unwrap_or(Value::TOP),
            narrow.get(i).copied().unwrap_or(Value::TOP),
        )
    })
}
fn value_subsumed(pool: &ValuePool, broad: Value, narrow: Value) -> bool {
    if broad == narrow || narrow.is_bottom() {
        return true;
    }
    if broad.is_unbounded() || broad.unknown & WIDENED_VALUE != 0 {
        return true;
    }
    if narrow.is_unbounded() {
        return false;
    }
    if narrow.unknown != 0 && broad.unknown == 0 {
        return false;
    }
    if narrow.unknown & UNKNOWN_TYPED != 0 && broad.unknown & UNKNOWN_TYPED == 0 {
        return false;
    }
    let atoms = pool.members(broad);
    pool.members(narrow)
        .iter()
        .all(|a| atoms.binary_search(a).is_ok())
}

#[cfg(test)]
mod tests {
    use super::*;
    use selector_domain::{Atom, AtomKind, UNKNOWN_VALUE};
    use selector_types::{OperationId, SymbolId};
    fn callback(pool: &mut ValuePool, site: u32, symbol: u32, binding: u32) -> Value {
        pool.singleton(Atom {
            kind: AtomKind::Callback,
            site: OperationId(site),
            symbol: SymbolId(symbol),
            binding,
        })
        .unwrap()
    }
    #[test]
    fn shape_identity_preserves_code_position_arity_and_unknown_but_erases_capture_binding() {
        let mut p = ValuePool::new(64);
        let mut shapes = CallbackShapes::new();
        let a = callback(&mut p, 1, 1, 1);
        let a2 = callback(&mut p, 1, 1, 99);
        let b = callback(&mut p, 2, 2, 1);
        let aa = p.join(a, a2).unwrap();
        let known = shapes.intern(&p, &[a]).unwrap();
        assert_eq!(shapes.intern(&p, &[a2]).unwrap(), known);
        assert_eq!(shapes.intern(&p, &[aa]).unwrap(), known);
        assert_ne!(shapes.intern(&p, &[b]).unwrap(), known);
        assert_ne!(shapes.intern(&p, &[Value::EMPTY, a]).unwrap(), known);
        assert_ne!(shapes.intern(&p, &[a, Value::EMPTY]).unwrap(), known);
        assert_ne!(
            shapes.intern(&p, &[Value::EMPTY]).unwrap(),
            CallbackShapeId(0)
        );
        let mixed = p
            .intern(p.members(a).to_vec().as_slice(), UNKNOWN_VALUE)
            .unwrap();
        let mixed = shapes.intern(&p, &[mixed]).unwrap();
        let unknown = shapes.intern(&p, &[Value::TOP]).unwrap();
        assert_ne!(known, mixed);
        assert_ne!(unknown, mixed);
        assert_ne!(known, unknown);
        let before = shapes.owned_bytes();
        for _ in 0..100_000 {
            assert_eq!(shapes.lookup(&p, &[aa]), Some(known));
            assert_eq!(shapes.intern(&p, &[a2]).unwrap(), known);
        }
        assert_eq!(shapes.owned_bytes(), before);
        assert_eq!(std::mem::size_of::<CallbackShapeAtom>(), 12);
    }
    #[test]
    fn hash_bucket_growth_is_preflighted_before_any_shape_capacity_changes() {
        let mut p = ValuePool::new(64);
        let mut shapes = CallbackShapes::new();
        for site in 1..=3 {
            let value = callback(&mut p, site, site, 0);
            shapes.intern(&p, &[value]).unwrap();
        }
        assert_eq!(shapes.heads.len(), 3);
        assert_eq!(shapes.heads.capacity(), 3);
        let v = callback(&mut p, 4, 4, 0);
        let before = (
            shapes.atoms.capacity(),
            shapes.rows.capacity(),
            shapes.heads.capacity(),
            shapes.len(),
            shapes.owned_bytes(),
        );
        // The old Vec-like estimate allowed only 6 usable hash entries, while
        // reserve(1) actually grows to 7. Reject this threshold without growing
        // either flat vector or the index.
        let vec_bytes = shapes.atoms.capacity() * std::mem::size_of::<CallbackShapeAtom>()
            + shapes.rows.capacity() * std::mem::size_of::<ShapeRow>();
        assert!(shapes.intern_bounded(&p, &[v], vec_bytes + 6 * 24).is_err());
        assert_eq!(
            (
                shapes.atoms.capacity(),
                shapes.rows.capacity(),
                shapes.heads.capacity(),
                shapes.len(),
                shapes.owned_bytes()
            ),
            before
        );
        let id = shapes.intern_bounded(&p, &[v], vec_bytes + 8 * 24).unwrap();
        assert_eq!(shapes.lookup(&p, &[v]), Some(id));
        assert!(shapes.owned_bytes() <= vec_bytes + 8 * 24);
    }
    #[test]
    fn shape_admission_preflights_storage_and_validates_rows_and_overflow() {
        let mut p = ValuePool::new(2);
        let a = callback(&mut p, 1, 1, 1);
        let b = callback(&mut p, 2, 2, 1);
        let mut shapes = CallbackShapes::new();
        assert!(shapes.intern_bounded(&p, &[a], 0).is_err());
        assert_eq!(shapes.owned_bytes(), 0);
        assert_eq!(shapes.len(), 1);
        let id = shapes.intern(&p, &[a]).unwrap();
        let shape = shapes.get(id);
        assert!(shape_covers_payload(shape, &p, &[a]));
        assert!(!shape_covers_payload(shape, &p, &[b]));
        assert!(!shape_covers_payload(shape, &p, &[Value::TOP]));
        assert!(shape_covers_payload(
            shape,
            &p,
            &[Value {
                set: selector_types::SetId(0),
                unknown: UNKNOWN_VALUE | WIDENED_VALUE
            }]
        ));
        for rows in [
            vec![CallbackShapeAtom {
                argument: 1,
                site: OperationId(1),
                symbol: SymbolId(1),
            }],
            vec![CallbackShapeAtom {
                argument: 0,
                site: OperationId::NONE,
                symbol: SymbolId(1),
            }],
            vec![
                CallbackShapeAtom {
                    argument: 0,
                    site: OperationId(1),
                    symbol: SymbolId(1)
                };
                2
            ],
        ] {
            assert!(shapes.intern_rows(1, &rows).is_err());
        }
    }
    #[test]
    fn subsumption_respects_unknown_coverage_and_finite_callback_alternatives() {
        let mut p = ValuePool::new(8);
        let a = p
            .singleton(Atom {
                kind: AtomKind::Callback,
                site: OperationId(1),
                symbol: SymbolId(1),
                binding: 0,
            })
            .unwrap();
        let b = p
            .singleton(Atom {
                kind: AtomKind::Callback,
                site: OperationId(2),
                symbol: SymbolId(2),
                binding: 0,
            })
            .unwrap();
        let ab = p.join(a, b).unwrap();
        assert!(arguments_subsumed(&p, &[ab], &[a]));
        assert!(!arguments_subsumed(&p, &[a], &[ab]));
        assert!(!arguments_subsumed(&p, &[ab], &[Value::TOP]));
        assert!(arguments_subsumed(&p, &[Value::TOP], &[ab]));
        let typed = p
            .intern(
                &[Atom {
                    kind: AtomKind::UpperBound,
                    site: OperationId::NONE,
                    symbol: SymbolId(3),
                    binding: 0,
                }],
                UNKNOWN_VALUE | UNKNOWN_TYPED,
            )
            .unwrap();
        assert!(!arguments_subsumed(&p, &[typed], &[Value::TOP]));
        assert!(arguments_subsumed(&p, &[Value::TOP], &[typed]));
    }
}
