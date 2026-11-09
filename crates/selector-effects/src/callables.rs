//! Parametric callable identity is independent from heap allocation identity.
//! A creation identifies code and a finite capture-cell graph; it never invokes
//! that code. Consumers must retain unknown scheduling/escape effects.
use crate::*;
use std::mem::size_of;

#[repr(u32)]
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum ValueKind {
    Unknown = 0,
    Constant = 1,
    Receiver = 2,
    Argument = 3,
    Capture = 4,
    Local = 5,
}
impl ValueKind {
    pub const fn from_u32(n: u32) -> Option<Self> {
        match n {
            0 => Some(Self::Unknown),
            1 => Some(Self::Constant),
            2 => Some(Self::Receiver),
            3 => Some(Self::Argument),
            4 => Some(Self::Capture),
            5 => Some(Self::Local),
            _ => None,
        }
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ValueRef {
    pub kind: ValueKind,
    pub index: u32,
}
impl ValueRef {
    pub const UNKNOWN: Self = Self {
        kind: ValueKind::Unknown,
        index: 0,
    };
    /// A producer proved this value cannot be a callable. Not an opaque return.
    pub const CONSTANT: Self = Self {
        kind: ValueKind::Constant,
        index: 0,
    };
    pub const RECEIVER: Self = Self {
        kind: ValueKind::Receiver,
        index: 0,
    };
    pub const fn argument(index: u32) -> Self {
        Self {
            kind: ValueKind::Argument,
            index,
        }
    }
    pub const fn capture(index: u32) -> Self {
        Self {
            kind: ValueKind::Capture,
            index,
        }
    }
    pub const fn local(index: u32) -> Self {
        Self {
            kind: ValueKind::Local,
            index,
        }
    }
}
pub(crate) fn value_bound(v: ValueRef, m: MethodRow) -> Result<(), Error> {
    match v.kind {
        ValueKind::Unknown | ValueKind::Constant | ValueKind::Receiver if v.index == 0 => Ok(()),
        ValueKind::Argument => bound(v.index, m.arity),
        ValueKind::Capture => bound(v.index, m.captures),
        ValueKind::Local => bound(v.index, m.locals),
        _ => Err(Error::Malformed),
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CallTarget {
    Direct(MethodId),
    Callable { value: ValueRef, sam: u32 },
}
impl From<MethodId> for CallTarget {
    fn from(id: MethodId) -> Self {
        Self::Direct(id)
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CallableCreation {
    pub site: u32,
    pub destination: u32,
    /// A normalized callable body: SAM ordinary actuals, then capture formals.
    /// A raw BSM implementation needs a separately admitted adapter capsule.
    pub implementation: MethodId,
    /// NONE means unadmitted SAM; activation must remain unknown.
    pub sam: u32,
    pub receiver: Origin,
    pub receiver_value: ValueRef,
    /// Indexes both origins and the parallel callable_values table.
    pub captures: Range,
}
/// Compatibility belongs to one admitted creation, never to every object of a
/// SAM interface. The target is the actual default method, including its effects.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CallableBridge {
    pub creation: u32,
    pub sam: u32,
    pub implementation: MethodId,
    pub proof: u32,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InvocationRoute {
    Implementation,
    DefaultBridge,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CallableInvocation {
    pub creation: u32,
    pub implementation: MethodId,
    pub route: InvocationRoute,
}

impl Capsules {
    /// Allocation-free lookup in the immutable creation-specific compatibility
    /// table. A missing route stays unknown, even when signatures have equal
    /// arity. The caller must preserve the original payload/capture ownership.
    pub fn resolve_callable_invocation(
        &self,
        creation: u32,
        requested_sam: u32,
    ) -> Result<Option<CallableInvocation>, Error> {
        let row = self
            .data()
            .creations
            .get(creation as usize)
            .ok_or(Error::Bounds)?;
        if requested_sam == NONE || row.sam == NONE {
            return Ok(None);
        }
        bound(requested_sam, self.bounds().sams)?;
        if row.sam == requested_sam {
            return Ok(Some(CallableInvocation {
                creation,
                implementation: row.implementation,
                route: InvocationRoute::Implementation,
            }));
        }
        let key = (creation, requested_sam);
        let bridges = &self.data().callable_bridges;
        let Ok(index) = bridges.binary_search_by_key(&key, |bridge| (bridge.creation, bridge.sam))
        else {
            return Ok(None);
        };
        Ok(Some(CallableInvocation {
            creation,
            implementation: bridges[index].implementation,
            route: InvocationRoute::DefaultBridge,
        }))
    }
}
#[repr(u32)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ValueFlowKind {
    Copy = 0,
    Return = 1,
    Store = 2,
    Load = 3,
}
impl ValueFlowKind {
    pub const fn from_u32(n: u32) -> Option<Self> {
        match n {
            0 => Some(Self::Copy),
            1 => Some(Self::Return),
            2 => Some(Self::Store),
            3 => Some(Self::Load),
            _ => None,
        }
    }
}
/// All indices are method-local. Multiple Copy rows implement a may-join.
/// Load: value is the Local destination, index the read ordinal. Store: value
/// is the source, index the write ordinal. Return uses index zero.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ValueFlow {
    pub kind: ValueFlowKind,
    pub value: ValueRef,
    pub index: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CellId(pub u32);
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CellValue {
    Unknown,
    NonCallable,
    Cell(CellId),
}
/// Static coordinates must be resolved in their defining method, not an
/// invoking method with a coincidentally equal local ordinal.
pub struct ValueFrame<'a> {
    pub method: MethodId,
    pub receiver: CellValue,
    pub arguments: &'a [CellValue],
    pub captures: &'a [CellValue],
    pub locals: &'a [CellValue],
}
impl ValueFrame<'_> {
    pub fn resolve(&self, owner: MethodId, value: ValueRef) -> Result<CellValue, Error> {
        if owner != self.method {
            return Err(Error::Malformed);
        }
        match value.kind {
            ValueKind::Unknown if value.index == 0 => Ok(CellValue::Unknown),
            ValueKind::Constant if value.index == 0 => Ok(CellValue::NonCallable),
            ValueKind::Receiver if value.index == 0 => Ok(self.receiver),
            ValueKind::Argument => self
                .arguments
                .get(value.index as usize)
                .copied()
                .ok_or(Error::Bounds),
            ValueKind::Capture => self
                .captures
                .get(value.index as usize)
                .copied()
                .ok_or(Error::Bounds),
            ValueKind::Local => self
                .locals
                .get(value.index as usize)
                .copied()
                .ok_or(Error::Bounds),
            _ => Err(Error::Malformed),
        }
    }
}

/// Only admitted complete local definitions may start Pending. Unproduced
/// locals start Unknown. A Pending cycle with no value is unresolved on invoke.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CellSeed {
    Unknown,
    Pending,
    NonCallable,
}
#[derive(Clone, Copy)]
struct Cell {
    head: u32,
    count: u32,
    unknown: bool,
    non_callable: bool,
}
#[derive(Clone, Copy)]
struct Member {
    creation: u32,
    next: u32,
}
/// Flat append-only monotone payload-ID sets. Payload IDs are owned by the
/// consumer and retain their defining capture-frame coordinates. They are NOT
/// implicitly static creation-row indices. Captures are separately indexed cells, so
/// recursion creates finite graph cycles rather than recursive owned payloads.
#[derive(Default)]
pub struct CallableCells {
    cells: Vec<Cell>,
    members: Vec<Member>,
    max_cells: usize,
    max_members: usize,
    max_targets: u32,
}
impl CallableCells {
    pub fn owned_bytes(&self) -> usize {
        self.cells.capacity() * size_of::<Cell>() + self.members.capacity() * size_of::<Member>()
    }
    pub fn reserve(
        &mut self,
        cell_count: usize,
        max_members: usize,
        max_targets: u32,
        max_bytes: usize,
    ) -> Result<(), Error> {
        if cell_count >= NONE as usize || max_members >= NONE as usize || max_targets == NONE {
            return Err(Error::Overflow);
        }
        let c = growth(self.cells.capacity(), cell_count)?;
        let m = growth(self.members.capacity(), max_members)?;
        let bytes = c
            .checked_mul(size_of::<Cell>())
            .and_then(|v| {
                m.checked_mul(size_of::<Member>())
                    .and_then(|w| v.checked_add(w))
            })
            .ok_or(Error::Overflow)?;
        if bytes > max_bytes {
            return Err(Error::Budget);
        }
        if c > self.cells.capacity() {
            self.cells
                .try_reserve_exact(c - self.cells.len())
                .map_err(|_| Error::Budget)?;
        }
        if m > self.members.capacity() {
            self.members
                .try_reserve_exact(m - self.members.len())
                .map_err(|_| Error::Budget)?;
        }
        self.max_members = max_members;
        self.max_targets = max_targets;
        self.max_cells = cell_count;
        if self.owned_bytes() > max_bytes {
            return Err(Error::Budget);
        }
        Ok(())
    }
    pub fn reset(&mut self, seeds: &[CellSeed]) -> Result<(), Error> {
        if seeds.len() > self.max_cells || seeds.len() > self.cells.capacity() {
            return Err(Error::Capacity);
        }
        self.cells.clear();
        self.members.clear();
        for seed in seeds {
            self.cells.push(Cell {
                head: NONE,
                count: 0,
                unknown: *seed == CellSeed::Unknown,
                non_callable: *seed == CellSeed::NonCallable,
            });
        }
        Ok(())
    }
    pub fn len(&self) -> usize {
        self.cells.len()
    }
    pub fn is_empty(&self) -> bool {
        self.cells.is_empty()
    }
    /// Admit one sparse frame cell within the already charged capacity.
    pub fn push_seed(&mut self, seed: CellSeed) -> Result<CellId, Error> {
        if self.cells.len() >= self.max_cells || self.cells.len() == self.cells.capacity() {
            return Err(Error::Capacity);
        }
        let id = CellId(u32::try_from(self.cells.len()).map_err(|_| Error::Overflow)?);
        self.cells.push(Cell {
            head: NONE,
            count: 0,
            unknown: seed == CellSeed::Unknown,
            non_callable: seed == CellSeed::NonCallable,
        });
        Ok(id)
    }
    fn cell(&self, id: CellId) -> Result<Cell, Error> {
        self.cells.get(id.0 as usize).copied().ok_or(Error::Bounds)
    }
    pub fn set_unknown(&mut self, id: CellId) -> Result<bool, Error> {
        let c = self.cells.get_mut(id.0 as usize).ok_or(Error::Bounds)?;
        let changed = !c.unknown;
        c.unknown = true;
        Ok(changed)
    }
    pub fn add_payload(&mut self, id: CellId, creation: u32) -> Result<bool, Error> {
        if creation == NONE {
            return Err(Error::Bounds);
        }
        let cell = self.cell(id)?;
        let mut next = cell.head;
        while next != NONE {
            let m = self.members[next as usize];
            if m.creation == creation {
                return Ok(false);
            }
            next = m.next;
        }
        if cell.count >= self.max_targets
            || self.members.len() >= self.max_members
            || self.members.len() == self.members.capacity()
        {
            return self.set_unknown(id);
        }
        let next = u32::try_from(self.members.len()).map_err(|_| Error::Overflow)?;
        self.members.push(Member {
            creation,
            next: cell.head,
        });
        let c = &mut self.cells[id.0 as usize];
        c.head = next;
        c.count += 1;
        Ok(true)
    }
    pub fn join_value(&mut self, target: CellId, source: CellValue) -> Result<bool, Error> {
        match source {
            CellValue::Unknown => self.set_unknown(target),
            CellValue::NonCallable => {
                let c = self.cells.get_mut(target.0 as usize).ok_or(Error::Bounds)?;
                let changed = !c.non_callable;
                c.non_callable = true;
                Ok(changed)
            }
            CellValue::Cell(source) => self.join(target, source),
        }
    }
    pub fn join(&mut self, target: CellId, source: CellId) -> Result<bool, Error> {
        let src = self.cell(source)?;
        self.cell(target)?;
        let mut changed = if src.unknown {
            self.set_unknown(target)?
        } else {
            false
        };
        if src.non_callable {
            changed |= self.join_value(target, CellValue::NonCallable)?;
        }
        let mut next = src.head;
        while next != NONE {
            let m = self.members[next as usize];
            next = m.next;
            changed |= self.add_payload(target, m.creation)?;
        }
        Ok(changed)
    }
    pub fn is_unknown(&self, id: CellId) -> Result<bool, Error> {
        Ok(self.cell(id)?.unknown)
    }
    pub fn is_complete_callable(&self, id: CellId) -> Result<bool, Error> {
        let c = self.cell(id)?;
        Ok(!c.unknown && !c.non_callable && c.count > 0)
    }
    pub fn payloads(&self, id: CellId) -> Result<CreationIter<'_>, Error> {
        Ok(CreationIter {
            members: &self.members,
            next: self.cell(id)?.head,
        })
    }
    /// No field/local ordinal coincidence is a heap identity. A missing or
    /// unproved heap binding explicitly poisons the destination.
    pub fn load_heap(
        &mut self,
        target: CellId,
        canonical_source: Option<CellId>,
    ) -> Result<bool, Error> {
        match canonical_source {
            Some(source) => self.join(target, source),
            None => self.set_unknown(target),
        }
    }
    /// Visits known supported targets while returning false for any unknown,
    /// non-callable, missing or incompatible alternative. False must open Calls.
    pub fn visit_invocations(
        &self,
        id: CellId,
        sam: u32,
        program: &Capsules,
        mut resolve: impl FnMut(u32) -> Option<u32>,
        mut visit: impl FnMut(u32, CallableInvocation),
    ) -> Result<bool, Error> {
        let mut complete = self.is_complete_callable(id)?
            && sam != NONE
            && (sam as usize) < program.data().sam_arities.len();
        for payload in self.payloads(id)? {
            let Some(creation) = resolve(payload) else {
                complete = false;
                continue;
            };
            if creation as usize >= program.data().creations.len() {
                complete = false;
                continue;
            }
            if sam != NONE && sam as usize >= program.data().sam_arities.len() {
                complete = false;
                continue;
            }
            let Some(invocation) = program.resolve_callable_invocation(creation, sam)? else {
                complete = false;
                continue;
            };
            visit(payload, invocation);
        }
        Ok(complete)
    }
}
pub struct CreationIter<'a> {
    members: &'a [Member],
    next: u32,
}
impl Iterator for CreationIter<'_> {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        if self.next == NONE {
            return None;
        }
        let m = self.members[self.next as usize];
        self.next = m.next;
        Some(m.creation)
    }
}

#[cfg(test)]
mod tests;
