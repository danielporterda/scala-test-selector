//! Sealed, local transfer replays. A capture retains the complete candidate
//! universe of the source node and the transitive type/owner/bound closure.
//! Recorded world misses are data; an unrecorded request is an error.
use crate::validate_container_atom;
use selector_domain::*;
use selector_facts::*;
use selector_graph::*;
use selector_issue::{RuntimeIssueReason, RuntimeIssueSite};
use selector_transfer::{
    Evaluation, Scratch, SummaryRead, TypeIndex, World, evaluate, primitive_long_receiver_sites,
    receiver_dispatch_operation, validate_scoped_dispatch_edge,
};
use selector_types::*;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::hash::{Hash, Hasher};
use std::path::Path;
use std::sync::Mutex;

const VERSION: u32 = 5;
#[derive(Clone, Debug)]
pub struct ReplayLimits {
    pub max_bytes: usize,
    pub max_records: usize,
    pub max_set_members: usize,
    pub scratch_bytes: usize,
}
impl Default for ReplayLimits {
    fn default() -> Self {
        Self {
            max_bytes: 64 * 1024 * 1024,
            max_records: 200_000,
            max_set_members: 64,
            scratch_bytes: 16 * 1024 * 1024,
        }
    }
}
#[derive(Clone, Debug)]
pub struct ReplayOptions {
    pub scratch_bytes: usize,
    pub verify_expected: bool,
}
impl Default for ReplayOptions {
    fn default() -> Self {
        Self {
            scratch_bytes: 16 * 1024 * 1024,
            verify_expected: true,
        }
    }
}
#[derive(Clone, Debug, Default, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ReplayAtom {
    pub kind: u32,
    pub site: u32,
    pub symbol: u32,
    pub binding: u32,
}
#[derive(Clone, Debug, Default, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct ReplayValue {
    pub unknown: u32,
    pub atoms: Vec<ReplayAtom>,
}
impl ReplayValue {
    pub fn from_value(pool: &ValuePool, value: Value) -> Result<Self, Error> {
        Self::from(pool, value, None)
    }
    fn from(pool: &ValuePool, value: Value, map: Option<&Mapping>) -> Result<Self, Error> {
        let mut atoms = Vec::with_capacity(pool.members(value).len());
        for atom in pool.members(value) {
            atoms.push(ReplayAtom {
                kind: match atom.kind {
                    AtomKind::Object => 1,
                    AtomKind::Callback => 2,
                    AtomKind::UpperBound => 3,
                    AtomKind::Container => 4,
                },
                site: if let Some(map) = map {
                    map.original_op(atom.site)?
                } else {
                    atom.site.0
                },
                symbol: if let Some(map) = map {
                    map.original_symbol(atom.symbol)?
                } else {
                    atom.symbol.0
                },
                binding: if matches!(atom.kind, AtomKind::Object | AtomKind::Container)
                    && atom.binding != 0
                {
                    if let Some(map) = map {
                        map.original_symbol(binding_root(atom.binding).unwrap())?
                            .checked_add(1)
                            .ok_or(Error::Invalid("replay object root origin"))?
                    } else {
                        atom.binding
                    }
                } else {
                    atom.binding
                },
            });
        }
        atoms.sort_unstable();
        Ok(Self {
            unknown: value.unknown,
            atoms,
        })
    }
    fn load(&self, pool: &mut ValuePool, map: &Mapping) -> Result<Value, Error> {
        let atoms = self
            .atoms
            .iter()
            .map(|atom| {
                Ok(Atom {
                    kind: match atom.kind {
                        1 => AtomKind::Object,
                        2 => AtomKind::Callback,
                        3 => AtomKind::UpperBound,
                        4 => AtomKind::Container,
                        _ => return Err(Error::Invalid("replay atom kind")),
                    },
                    site: OperationId(map.compact_op(atom.site)?),
                    symbol: SymbolId(map.compact_symbol(atom.symbol)?),
                    binding: if matches!(atom.kind, 1 | 4) && atom.binding != 0 {
                        root_binding(SymbolId(map.compact_symbol(atom.binding - 1)?))?
                    } else {
                        atom.binding
                    },
                })
            })
            .collect::<Result<Vec<_>, Error>>()?;
        pool.intern(&atoms, self.unknown)
    }
}
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct ReplaySlot {
    pub kind: u32,
    pub owner: u32,
    pub member: u32,
    /// Exact allocation partitions use this stable key and canonical owner 0.
    /// Worker-local draft ordinals never become durable replay identities.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub heap_owner: Option<ReplayHeapKey>,
}
#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ReplayHeapKey {
    pub site: u32,
    pub root: u32,
}
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
struct ReplayHeapOwner {
    key: ReplayHeapKey,
    owner: Option<u32>,
}
impl ReplaySlot {
    fn from(slot: Slot, map: Option<&Mapping>, local: &[HeapOwnerKey]) -> Result<Self, Error> {
        let kind = match slot.kind {
            SlotKind::Summary => 0,
            SlotKind::Field => 1,
            SlotKind::Capture => 2,
            SlotKind::Dispatch => 3,
            SlotKind::Body => 4,
            SlotKind::StaticField => 5,
            SlotKind::FieldWildcard => 6,
            SlotKind::FieldAll => 7,
            SlotKind::FieldMissing => 8,
        };
        let (mut owner, mut member) = (slot.owner, slot.member);
        let mut heap_owner = None;
        if let Some(map) = map {
            match slot.kind {
                SlotKind::Field | SlotKind::FieldMissing => {
                    if owner != u32::MAX && owner >= map.compact_owner_base()? {
                        let key = if owner & LOCAL_HEAP_OWNER != 0 {
                            let key = local
                                .get((owner & !LOCAL_HEAP_OWNER) as usize)
                                .ok_or(Error::Invalid("replay local heap owner"))?;
                            ReplayHeapKey {
                                site: map.original_op(key.site)?,
                                root: map.original_symbol(key.root)?,
                            }
                        } else {
                            map.heap_owners
                                .get((owner - map.compact_owner_base()?) as usize)
                                .filter(|entry| entry.owner.is_some())
                                .ok_or(Error::Invalid("replay heap owner range"))?
                                .key
                        };
                        heap_owner = Some(key);
                        owner = 0;
                    } else {
                        owner = map.original_object_owner(owner)?;
                    }
                    member = map.original_symbol(SymbolId(member))?;
                }
                SlotKind::FieldWildcard | SlotKind::FieldAll => {
                    owner = map.original_op(OperationId(owner))?;
                    member = map.original_symbol(SymbolId(member))?;
                }
                SlotKind::StaticField => owner = map.original_symbol(SymbolId(owner))?,
                SlotKind::Summary | SlotKind::Capture => (),
                _ => return Err(Error::Invalid("unsupported replay slot namespace")),
            }
        }
        Ok(Self {
            kind,
            owner,
            member,
            heap_owner,
        })
    }
}
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
enum Request {
    Summary {
        node: u32,
        receiver: ReplayValue,
        arguments: Vec<ReplayValue>,
    },
    Slot(ReplaySlot),
    Capture(u32),
    Binding {
        site: u32,
        receiver: ReplayValue,
        arguments: Vec<ReplayValue>,
    },
    HeapOwner(ReplayHeapKey),
}
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
enum Response {
    Summary {
        context: Option<u32>,
        value: ReplayValue,
        version: u64,
        present: bool,
    },
    Slot {
        value: ReplayValue,
        version: u64,
        present: bool,
    },
    Capture(Option<(ReplayValue, Vec<ReplayValue>, u64)>),
    Binding(Option<u32>),
    HeapOwner(Option<u32>),
}
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
struct Event {
    request: Request,
    response: Response,
}
fn default_true() -> bool {
    true
}
fn is_true(value: &bool) -> bool {
    *value
}
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct ReplayCall {
    pub target: u32,
    pub receiver: ReplayValue,
    pub arguments: IdSlice,
    pub operation: u32,
    pub kind: u32,
    pub edge: u32,
    pub summary: Option<u32>,
    pub binding: u32,
    #[serde(default = "default_true", skip_serializing_if = "is_true")]
    pub observe_return: bool,
}
#[derive(Clone, Copy, Debug, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct IdSlice {
    pub start: u32,
    pub len: u32,
}
impl From<IdRange> for IdSlice {
    fn from(value: IdRange) -> Self {
        Self {
            start: value.start,
            len: value.len,
        }
    }
}
#[derive(Clone, Debug, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct ReplayIssueSite {
    pub kind: u32,
    pub operation: u32,
    pub reason: u32,
}
fn unverified_effects_open() -> bool {
    true
}
fn effects_are_open(value: &bool) -> bool {
    *value
}
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct ReplayOutcome {
    pub value: ReplayValue,
    pub calls: Vec<ReplayCall>,
    pub arguments: Vec<ReplayValue>,
    pub stores: Vec<(ReplaySlot, ReplayValue)>,
    pub captures: Vec<(u32, ReplayValue, IdSlice)>,
    pub reads: Vec<(ReplaySlot, u64, bool)>,
    pub heap_owners: Vec<ReplayHeapKey>,
    pub field_reads: Vec<ReplaySlot>,
    pub edges: Vec<(u32, u32, u32, u32, u32)>,
    pub issues: Vec<u32>,
    pub first_issue: Option<ReplayIssueSite>,
    pub operation_visits: u64,
    /// Missing legacy evidence is open. Omitting open values preserves the
    /// canonical seals of historical recordings without certifying closure.
    #[serde(
        default = "unverified_effects_open",
        skip_serializing_if = "effects_are_open"
    )]
    pub effects_open: bool,
}
impl Default for ReplayOutcome {
    fn default() -> Self {
        Self {
            value: ReplayValue::default(),
            calls: Vec::new(),
            arguments: Vec::new(),
            stores: Vec::new(),
            captures: Vec::new(),
            reads: Vec::new(),
            heap_owners: Vec::new(),
            field_reads: Vec::new(),
            edges: Vec::new(),
            issues: Vec::new(),
            first_issue: None,
            operation_visits: 0,
            effects_open: true,
        }
    }
}
impl ReplayOutcome {
    fn from(
        evaluation: &Evaluation,
        pool: &ValuePool,
        map: Option<&Mapping>,
    ) -> Result<Self, Error> {
        let node = |id: NodeId| {
            if let Some(map) = map {
                map.original_node(id)
            } else {
                Ok(id.0)
            }
        };
        let operation = |id: OperationId| {
            if let Some(map) = map {
                map.original_op(id)
            } else {
                Ok(id.0)
            }
        };
        let symbol = |id: SymbolId| {
            if let Some(map) = map {
                map.original_symbol(id)
            } else {
                Ok(id.0)
            }
        };
        let edge = |id: EdgeId| {
            if let Some(map) = map {
                map.original_edge(id)
            } else {
                Ok(id.0)
            }
        };
        Ok(Self {
            value: ReplayValue::from(pool, evaluation.value, map)?,
            calls: evaluation
                .calls
                .iter()
                .map(|call| {
                    Ok(ReplayCall {
                        target: node(call.target)?,
                        receiver: ReplayValue::from(pool, call.receiver, map)?,
                        arguments: call.arguments.into(),
                        operation: operation(call.operation)?,
                        kind: call.kind as u32,
                        edge: edge(call.edge)?,
                        summary: call.summary.map(|id| id.0),
                        binding: call.binding,
                        observe_return: call.observe_return,
                    })
                })
                .collect::<Result<_, Error>>()?,
            arguments: evaluation
                .arguments
                .iter()
                .map(|value| ReplayValue::from(pool, *value, map))
                .collect::<Result<_, _>>()?,
            stores: evaluation
                .stores
                .iter()
                .map(|store| {
                    Ok((
                        ReplaySlot::from(store.slot, map, &evaluation.heap_owners)?,
                        ReplayValue::from(pool, store.value, map)?,
                    ))
                })
                .collect::<Result<_, Error>>()?,
            captures: evaluation
                .captures
                .iter()
                .map(|capture| {
                    Ok((
                        operation(capture.site)?,
                        ReplayValue::from(pool, capture.receiver, map)?,
                        capture.arguments.into(),
                    ))
                })
                .collect::<Result<_, Error>>()?,
            reads: evaluation
                .reads
                .iter()
                .map(|read| {
                    Ok((
                        ReplaySlot::from(read.slot, map, &evaluation.heap_owners)?,
                        read.version,
                        read.present,
                    ))
                })
                .collect::<Result<_, Error>>()?,
            heap_owners: evaluation
                .heap_owners
                .iter()
                .map(|key| {
                    Ok(ReplayHeapKey {
                        site: operation(key.site)?,
                        root: symbol(key.root)?,
                    })
                })
                .collect::<Result<_, Error>>()?,
            field_reads: evaluation
                .field_reads
                .iter()
                .map(|slot| ReplaySlot::from(*slot, map, &evaluation.heap_owners))
                .collect::<Result<_, Error>>()?,
            edges: evaluation
                .edges
                .iter()
                .map(|e| {
                    Ok((
                        node(e.target)?,
                        operation(e.operation)?,
                        e.kind as u32,
                        edge(e.edge)?,
                        symbol(e.receiver)?,
                    ))
                })
                .collect::<Result<_, Error>>()?,
            issues: evaluation.issues.iter().map(|kind| *kind as u32).collect(),
            first_issue: evaluation
                .first_issue
                .map(|site| {
                    Ok::<_, Error>(ReplayIssueSite {
                        kind: site.kind as u32,
                        operation: operation(site.operation)?,
                        reason: site.reason as u32,
                    })
                })
                .transpose()?,
            operation_visits: evaluation.operation_visits,
            effects_open: evaluation.effects_open,
        })
    }
}
struct RecordingWorld<'a, W> {
    world: &'a W,
    events: Mutex<Vec<Event>>,
    max_events: usize,
    overflow: std::sync::atomic::AtomicBool,
}
impl<W> RecordingWorld<'_, W> {
    fn record(&self, build: impl FnOnce() -> Event) {
        let mut events = self.events.lock().unwrap();
        if events.len() >= self.max_events {
            self.overflow
                .store(true, std::sync::atomic::Ordering::Relaxed);
        } else {
            events.push(build());
        }
    }
}
impl<W: World> World for RecordingWorld<'_, W> {
    fn values(&self) -> &ValuePool {
        self.world.values()
    }
    fn heap_owner(&self, key: HeapOwnerKey) -> Option<u32> {
        let owner = self.world.heap_owner(key);
        self.record(|| Event {
            request: Request::HeapOwner(ReplayHeapKey {
                site: key.site.0,
                root: key.root.0,
            }),
            response: Response::HeapOwner(owner),
        });
        owner
    }
    fn summary(
        &self,
        node: NodeId,
        receiver: Value,
        args: &[Value],
        local: &ValuePool,
        scratch: &mut Vec<Value>,
    ) -> SummaryRead {
        let response = self.world.summary(node, receiver, args, local, scratch);
        self.record(|| Event {
            request: Request::Summary {
                node: node.0,
                receiver: ReplayValue::from(local, receiver, None).unwrap(),
                arguments: args
                    .iter()
                    .map(|value| ReplayValue::from(local, *value, None).unwrap())
                    .collect(),
            },
            response: Response::Summary {
                context: response.context.map(|id| id.0),
                value: ReplayValue::from(self.values(), response.value, None).unwrap(),
                version: response.version,
                present: response.present,
            },
        });
        response
    }
    fn slot(&self, slot: Slot) -> (Value, u64, bool) {
        let (value, version, present) = self.world.slot(slot);
        self.record(|| Event {
            request: Request::Slot(ReplaySlot::from(slot, None, &[]).unwrap()),
            response: Response::Slot {
                value: ReplayValue::from(self.values(), value, None).unwrap(),
                version,
                present,
            },
        });
        (value, version, present)
    }
    fn capture(&self, binding: u32) -> Option<(Value, &[Value], u64)> {
        let response = self.world.capture(binding);
        self.record(|| Event {
            request: Request::Capture(binding),
            response: Response::Capture(response.map(|(receiver, args, version)| {
                (
                    ReplayValue::from(self.values(), receiver, None).unwrap(),
                    args.iter()
                        .map(|value| ReplayValue::from(self.values(), *value, None).unwrap())
                        .collect(),
                    version,
                )
            })),
        });
        response
    }
    fn binding(
        &self,
        site: OperationId,
        receiver: Value,
        args: &[Value],
        local: &ValuePool,
        atoms: &mut Vec<Atom>,
        values: &mut Vec<Value>,
    ) -> Option<u32> {
        let response = self
            .world
            .binding(site, receiver, args, local, atoms, values);
        self.record(|| Event {
            request: Request::Binding {
                site: site.0,
                receiver: ReplayValue::from(local, receiver, None).unwrap(),
                arguments: args
                    .iter()
                    .map(|value| ReplayValue::from(local, *value, None).unwrap())
                    .collect(),
            },
            response: Response::Binding(response),
        });
        response
    }
}
#[derive(Clone, Debug, Serialize, Deserialize)]
struct Mapping {
    symbols: Vec<u32>,
    nodes: Vec<u32>,
    operations: Vec<u32>,
    edges: Vec<u32>,
    source_operations: u32,
    source_symbols: u32,
    heap_owners: Vec<ReplayHeapOwner>,
}
fn original(ids: &[u32], id: u32) -> Result<u32, Error> {
    if id == u32::MAX {
        Ok(id)
    } else {
        ids.get(id as usize)
            .copied()
            .ok_or(Error::Invalid("replay identity range"))
    }
}
fn compact(ids: &[u32], original: u32) -> Result<u32, Error> {
    if original == u32::MAX {
        Ok(original)
    } else {
        ids.iter()
            .position(|id| *id == original)
            .map(|index| index as u32)
            .ok_or(Error::Invalid("replay omitted identity frontier"))
    }
}
impl Mapping {
    fn heap_entry(&self, key: ReplayHeapKey) -> Option<&ReplayHeapOwner> {
        self.heap_owners
            .binary_search_by_key(&key, |entry| entry.key)
            .ok()
            .map(|index| &self.heap_owners[index])
    }
    fn compact_owner_base(&self) -> Result<u32, Error> {
        self.operations
            .len()
            .checked_add(self.symbols.len())
            .filter(|base| *base < LOCAL_HEAP_OWNER as usize)
            .map(|base| base as u32)
            .ok_or(Error::Limit("replay heap owner namespaces"))
    }
    fn source_owner_base(&self) -> Result<u32, Error> {
        self.source_operations
            .checked_add(self.source_symbols)
            .filter(|base| *base < LOCAL_HEAP_OWNER)
            .ok_or(Error::Invalid("replay source heap owner namespaces"))
    }
    fn validate_value(
        &self,
        value: &ReplayValue,
        facts: &FactSnapshot,
        allow_container: bool,
    ) -> Result<(), Error> {
        for atom in &value.atoms {
            if atom.kind == 4 && !allow_container {
                return Err(Error::Invalid("legacy replay container atom"));
            }
            if !matches!(atom.kind, 1..=4) {
                return Err(Error::Invalid("replay atom kind"));
            }
            self.compact_op(atom.site)?;
            self.compact_symbol(atom.symbol)?;
            if atom.kind == 4 {
                validate_container_atom(
                    facts,
                    Atom {
                        kind: AtomKind::Container,
                        site: OperationId(self.compact_op(atom.site)?),
                        symbol: SymbolId(self.compact_symbol(atom.symbol)?),
                        binding: if atom.binding == 0 {
                            0
                        } else {
                            root_binding(SymbolId(self.compact_symbol(atom.binding - 1)?))?
                        },
                    },
                )?;
            }
            if matches!(atom.kind, 1 | 4) && atom.binding != 0 {
                self.compact_symbol(atom.binding - 1)?;
            }
        }
        Ok(())
    }
    fn validate_slot(&self, slot: &ReplaySlot) -> Result<(), Error> {
        if let Some(key) = slot.heap_owner {
            if !matches!(slot.kind, 1 | 8) || slot.owner != 0 || self.heap_entry(key).is_none() {
                return Err(Error::Invalid("replay heap slot identity"));
            }
        } else if matches!(slot.kind, 1 | 8) {
            if slot.owner != u32::MAX {
                if slot.owner < self.source_operations {
                    if slot.kind == 1 {
                        return Err(Error::Invalid("replay unpartitioned allocation field"));
                    }
                    self.compact_op(slot.owner)?;
                } else if slot.owner < self.source_owner_base()? {
                    self.compact_symbol(slot.owner - self.source_operations)?;
                } else {
                    return Err(Error::Invalid("replay heap owner tag or frontier"));
                }
            }
        }
        match slot.kind {
            1 | 8 => {
                self.compact_symbol(slot.member)?;
            }
            6 | 7 => {
                if slot.owner == u32::MAX {
                    return Err(Error::Invalid("replay allocation channel site"));
                }
                self.compact_op(slot.owner)?;
                self.compact_symbol(slot.member)?;
            }
            5 => {
                self.compact_symbol(slot.owner)?;
            }
            0 | 2 => (),
            _ => return Err(Error::Invalid("unsupported replay slot namespace")),
        }
        Ok(())
    }
    fn original_symbol(&self, id: SymbolId) -> Result<u32, Error> {
        original(&self.symbols, id.0)
    }
    fn original_node(&self, id: NodeId) -> Result<u32, Error> {
        original(&self.nodes, id.0)
    }
    fn original_op(&self, id: OperationId) -> Result<u32, Error> {
        original(&self.operations, id.0)
    }
    fn original_edge(&self, id: EdgeId) -> Result<u32, Error> {
        original(&self.edges, id.0)
    }
    fn compact_symbol(&self, id: u32) -> Result<u32, Error> {
        compact(&self.symbols, id)
    }
    fn compact_node(&self, id: u32) -> Result<u32, Error> {
        compact(&self.nodes, id)
    }
    fn compact_op(&self, id: u32) -> Result<u32, Error> {
        compact(&self.operations, id)
    }
    fn original_object_owner(&self, owner: u32) -> Result<u32, Error> {
        if owner == u32::MAX {
            return Ok(owner);
        }
        if (owner as usize) < self.operations.len() {
            self.original_op(OperationId(owner))
        } else {
            self.source_operations
                .checked_add(self.original_symbol(SymbolId(owner - self.operations.len() as u32))?)
                .ok_or(Error::Limit("replay root owner"))
        }
    }
}

fn normalize_heap_slot(
    slot: &mut ReplaySlot,
    source_base: u32,
    owners: &[ReplayHeapOwner],
    local: &[HeapOwnerKey],
) -> Result<(), Error> {
    if matches!(slot.kind, 1 | 8) && slot.owner != u32::MAX && slot.owner >= source_base {
        let key = if slot.owner & LOCAL_HEAP_OWNER != 0 {
            let key = local
                .get((slot.owner & !LOCAL_HEAP_OWNER) as usize)
                .ok_or(Error::Invalid("replay local heap owner"))?;
            ReplayHeapKey {
                site: key.site.0,
                root: key.root.0,
            }
        } else {
            owners
                .iter()
                .find(|entry| entry.owner == Some(slot.owner))
                .ok_or(Error::Invalid("replay unrecorded heap owner"))?
                .key
        };
        slot.heap_owner = Some(key);
        slot.owner = 0;
    }
    Ok(())
}

struct Closure<'a> {
    facts: &'a FactSnapshot,
    graph: &'a ProgramGraph,
    types: &'a TypeIndex,
    symbols: BTreeSet<u32>,
    nodes: BTreeSet<u32>,
    bodies: BTreeSet<u32>,
    operations: BTreeSet<u32>,
    files: BTreeSet<u32>,
    symbol_work: Vec<u32>,
    node_work: Vec<u32>,
    body_work: Vec<u32>,
    op_work: Vec<u32>,
    main_body: BodyId,
    certificate_nodes: BTreeSet<u32>,
    certificate_bodies: BTreeSet<u32>,
}
impl<'a> Closure<'a> {
    fn new(
        facts: &'a FactSnapshot,
        graph: &'a ProgramGraph,
        types: &'a TypeIndex,
        node: NodeId,
    ) -> Self {
        Self {
            facts,
            graph,
            types,
            symbols: BTreeSet::new(),
            nodes: BTreeSet::new(),
            bodies: BTreeSet::new(),
            operations: BTreeSet::new(),
            files: BTreeSet::new(),
            symbol_work: Vec::new(),
            node_work: Vec::new(),
            body_work: Vec::new(),
            op_work: Vec::new(),
            main_body: graph.nodes[node.index()].body,
            certificate_nodes: BTreeSet::new(),
            certificate_bodies: BTreeSet::new(),
        }
    }
    fn symbol(&mut self, id: u32) {
        if id != u32::MAX && self.symbols.insert(id) {
            self.symbol_work.push(id);
        }
    }
    fn node(&mut self, id: u32) {
        if id != u32::MAX && self.nodes.insert(id) {
            self.node_work.push(id);
        }
    }
    fn body(&mut self, id: u32) {
        if id != u32::MAX && self.bodies.insert(id) {
            self.body_work.push(id);
        }
    }
    fn operation(&mut self, id: u32) {
        if id != u32::MAX && self.operations.insert(id) {
            self.op_work.push(id);
        }
    }
    fn callback_certificate(&mut self, target: SymbolId) {
        if let Some(node) = self.graph.node_for_symbol(target) {
            self.certificate_nodes.insert(node.0);
            let body = self.graph.nodes[node.index()].body;
            if !body.is_none() {
                self.certificate_bodies.insert(body.0);
            }
            self.node(node.0);
        }
    }
    fn value(&mut self, value: &ReplayValue) {
        for atom in &value.atoms {
            self.symbol(atom.symbol);
            self.operation(atom.site);
            if matches!(atom.kind, 1 | 4) && atom.binding != 0 {
                self.symbol(atom.binding - 1);
            }
            if atom.kind == 2 {
                if let Some(node) = self.graph.node_for_symbol(SymbolId(atom.symbol)) {
                    self.node(node.0);
                }
            }
        }
    }
    fn slot(&mut self, slot: &ReplaySlot) -> Result<(), Error> {
        match slot.kind {
            1 | 8 => {
                if let Some(key) = slot.heap_owner {
                    self.operation(key.site);
                    self.symbol(key.root);
                } else if slot.owner != u32::MAX {
                    if slot.owner < self.facts.operations.len() as u32 {
                        self.operation(slot.owner);
                    } else {
                        self.symbol(slot.owner - self.facts.operations.len() as u32);
                    }
                }
                self.symbol(slot.member);
            }
            6 | 7 => {
                self.operation(slot.owner);
                self.symbol(slot.member);
            }
            5 => self.symbol(slot.owner),
            0 | 2 => (),
            _ => return Err(Error::Invalid("unsupported replay slot namespace")),
        }
        Ok(())
    }
    fn event(&mut self, event: &Event) -> Result<(), Error> {
        match &event.request {
            Request::Summary {
                node,
                receiver,
                arguments,
            } => {
                self.node(*node);
                self.value(receiver);
                for value in arguments {
                    self.value(value);
                }
            }
            Request::Slot(slot) => self.slot(slot)?,
            Request::Capture(_) => (),
            Request::HeapOwner(key) => {
                self.operation(key.site);
                self.symbol(key.root);
            }
            Request::Binding {
                site,
                receiver,
                arguments,
            } => {
                self.operation(*site);
                self.value(receiver);
                for value in arguments {
                    self.value(value);
                }
            }
        }
        match &event.response {
            Response::Summary { value, .. } | Response::Slot { value, .. } => self.value(value),
            Response::Capture(Some((receiver, arguments, _))) => {
                self.value(receiver);
                for value in arguments {
                    self.value(value);
                }
            }
            _ => (),
        }
        Ok(())
    }
    fn close(&mut self, limits: &ReplayLimits) -> Result<(), Error> {
        loop {
            if self.symbols.len() + self.nodes.len() + self.bodies.len() + self.operations.len()
                > limits.max_records
            {
                return Err(Error::Limit("replay closure records"));
            }
            if let Some(id) = self.symbol_work.pop() {
                let record = *self
                    .facts
                    .symbols
                    .get(id as usize)
                    .ok_or(Error::Invalid("replay symbol frontier"))?;
                self.symbol(record.owner.0);
                if !record.file.is_none() {
                    self.files.insert(record.file.0);
                }
                for parent in self
                    .types
                    .direct_parents(SymbolId(id))
                    .ok_or(Error::Invalid("replay type frontier"))?
                {
                    self.symbol(parent.0);
                }
                if let Some(classes) = self.facts.result_bound(SymbolId(id), OperationId::NONE) {
                    for class in classes {
                        self.symbol(class.0);
                    }
                }
            } else if let Some(id) = self.node_work.pop() {
                let record = *self
                    .graph
                    .nodes
                    .get(id as usize)
                    .ok_or(Error::Invalid("replay node frontier"))?;
                self.symbol(record.symbol.0);
                // Additional initializer bodies may share a compiler symbol.
                // Preserve its canonical callable node rather than choosing a
                // convenient body from the compact subset.
                if let Some(canonical) = self.graph.node_for_symbol(record.symbol) {
                    self.node(canonical.0);
                }
                self.body(record.body.0);
                if !record.file.is_none() {
                    self.files.insert(record.file.0);
                }
            } else if let Some(id) = self.body_work.pop() {
                let body = *self
                    .facts
                    .bodies
                    .get(id as usize)
                    .ok_or(Error::Invalid("replay body frontier"))?;
                self.symbol(body.symbol.0);
                self.files.insert(body.file.0);
                let full = BodyId(id) == self.main_body || self.certificate_bodies.contains(&id);
                let added = body
                    .operations
                    .range()
                    .filter(|index| {
                        (full || self.facts.operations[*index].opcode == Opcode::Parameter)
                            && !self.operations.contains(&(*index as u32))
                    })
                    .count();
                if self
                    .symbols
                    .len()
                    .saturating_add(self.nodes.len())
                    .saturating_add(self.bodies.len())
                    .saturating_add(self.operations.len())
                    .saturating_add(added)
                    > limits.max_records
                {
                    return Err(Error::Limit("replay certificate recipe records"));
                }
                for index in body.operations.range() {
                    if full || self.facts.operations[index].opcode == Opcode::Parameter {
                        self.operation(index as u32);
                    }
                }
            } else if let Some(id) = self.op_work.pop() {
                let record = *self
                    .facts
                    .operations
                    .get(id as usize)
                    .ok_or(Error::Invalid("replay operation frontier"))?;
                self.body(record.body.0);
                self.symbol(record.target.0);
                if let Some(node) = self.graph.node_for_symbol(record.target) {
                    self.node(node.0);
                }
                if let Some(classes) = self.facts.result_bound(record.target, OperationId(id)) {
                    for class in classes {
                        self.symbol(class.0);
                    }
                }
            } else {
                return Ok(());
            }
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct CallbackAuthority {
    node: u32,
    operations: Vec<u32>,
    structural_edges: Vec<u32>,
}
fn certificate_edge(edge: &EdgeRecord) -> bool {
    edge.kind == EdgeKind::Guard
        || edge.flags & EDGE_UNKNOWN != 0
        || (edge.kind.is_execution() && edge.operation.is_none())
}
#[derive(Clone, Debug, Serialize, Deserialize)]
struct Metadata {
    version: u32,
    source_facts: String,
    source_graph: String,
    root: u32,
    max_members: usize,
    mapping: Mapping,
    receiver: ReplayValue,
    arguments: Vec<ReplayValue>,
    events: Vec<Event>,
    expected: ReplayOutcome,
    scope: String,
    parent_inventory: Vec<(u32, Vec<u32>)>,
    // Absent historical inventories mean no receiver-only frontiers. New
    // recordings retain the entire source inventory, including disjoint types.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    deferred_receiver_inventory: Vec<u32>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    known_receiver_inventory: Vec<(u32, u32)>,
    callback_authority: Vec<CallbackAuthority>,
    disabled: Vec<u32>,
    strict_events: bool,
    // Canonical codec identities are distinct from the semantic scope seal.
    artifacts: Option<(String, String)>,
    scratch_required: usize,
}
fn values_owned(values: &Vec<ReplayValue>) -> usize {
    values.capacity() * std::mem::size_of::<ReplayValue>()
        + values
            .iter()
            .map(|value| value.atoms.capacity() * std::mem::size_of::<ReplayAtom>())
            .sum::<usize>()
}
fn value_owned(value: &ReplayValue) -> usize {
    value.atoms.capacity() * std::mem::size_of::<ReplayAtom>()
}
impl Metadata {
    fn validate_heap_references(&self, facts: &FactSnapshot) -> Result<(), Error> {
        let map = &self.mapping;
        let allow_container = self.version >= 4;
        map.validate_value(&self.receiver, facts, allow_container)?;
        for value in &self.arguments {
            map.validate_value(value, facts, allow_container)?;
        }
        for event in &self.events {
            match &event.request {
                Request::Summary {
                    receiver,
                    arguments,
                    ..
                }
                | Request::Binding {
                    receiver,
                    arguments,
                    ..
                } => {
                    map.validate_value(receiver, facts, allow_container)?;
                    for value in arguments {
                        map.validate_value(value, facts, allow_container)?;
                    }
                }
                Request::Slot(slot) => map.validate_slot(slot)?,
                _ => (),
            }
            match &event.response {
                Response::Summary { value, .. } | Response::Slot { value, .. } => {
                    map.validate_value(value, facts, allow_container)?
                }
                Response::Capture(Some((receiver, arguments, _))) => {
                    map.validate_value(receiver, facts, allow_container)?;
                    for value in arguments {
                        map.validate_value(value, facts, allow_container)?;
                    }
                }
                _ => (),
            }
        }
        let out = &self.expected;
        map.validate_value(&out.value, facts, allow_container)?;
        for call in &out.calls {
            map.validate_value(&call.receiver, facts, allow_container)?;
        }
        for value in &out.arguments {
            map.validate_value(value, facts, allow_container)?;
        }
        for (slot, value) in &out.stores {
            map.validate_slot(slot)?;
            map.validate_value(value, facts, allow_container)?;
        }
        for (_, value, _) in &out.captures {
            map.validate_value(value, facts, allow_container)?;
        }
        for (slot, _, _) in &out.reads {
            map.validate_slot(slot)?;
        }
        for slot in &out.field_reads {
            map.validate_slot(slot)?;
        }
        let mut keys = BTreeSet::new();
        for key in &out.heap_owners {
            if !keys.insert(*key)
                || !map
                    .heap_entry(*key)
                    .is_some_and(|entry| entry.owner.is_none())
            {
                return Err(Error::Invalid("replay local heap owner outcome"));
            }
        }
        Ok(())
    }
    fn owned_bytes(&self) -> usize {
        let mut bytes = self.source_facts.capacity()
            + self.source_graph.capacity()
            + self.scope.capacity()
            + self.mapping.symbols.capacity() * 4
            + self.mapping.nodes.capacity() * 4
            + self.mapping.operations.capacity() * 4
            + self.mapping.edges.capacity() * 4
            + self.mapping.heap_owners.capacity() * std::mem::size_of::<ReplayHeapOwner>()
            + value_owned(&self.receiver)
            + values_owned(&self.arguments)
            + self.disabled.capacity() * 4
            + self.events.capacity() * std::mem::size_of::<Event>()
            + self.parent_inventory.capacity() * std::mem::size_of::<(u32, Vec<u32>)>();
        bytes += self.deferred_receiver_inventory.capacity() * 4;
        bytes += self.known_receiver_inventory.capacity() * 8;
        bytes += self.callback_authority.capacity() * std::mem::size_of::<CallbackAuthority>()
            + self
                .callback_authority
                .iter()
                .map(|entry| (entry.operations.capacity() + entry.structural_edges.capacity()) * 4)
                .sum::<usize>();
        if let Some((facts, graph)) = &self.artifacts {
            bytes += facts.capacity() + graph.capacity();
        }
        bytes += self
            .parent_inventory
            .iter()
            .map(|(_, parents)| parents.capacity() * 4)
            .sum::<usize>();
        for event in &self.events {
            bytes += match &event.request {
                Request::Summary {
                    receiver,
                    arguments,
                    ..
                }
                | Request::Binding {
                    receiver,
                    arguments,
                    ..
                } => value_owned(receiver) + values_owned(arguments),
                _ => 0,
            };
            bytes += match &event.response {
                Response::Summary { value, .. } | Response::Slot { value, .. } => {
                    value_owned(value)
                }
                Response::Capture(Some((receiver, arguments, _))) => {
                    value_owned(receiver) + values_owned(arguments)
                }
                _ => 0,
            };
        }
        let out = &self.expected;
        bytes
            + value_owned(&out.value)
            + values_owned(&out.arguments)
            + out.calls.capacity() * std::mem::size_of::<ReplayCall>()
            + out
                .calls
                .iter()
                .map(|call| value_owned(&call.receiver))
                .sum::<usize>()
            + out.stores.capacity() * std::mem::size_of::<(ReplaySlot, ReplayValue)>()
            + out
                .stores
                .iter()
                .map(|(_, value)| value_owned(value))
                .sum::<usize>()
            + out.captures.capacity() * std::mem::size_of::<(u32, ReplayValue, IdSlice)>()
            + out
                .captures
                .iter()
                .map(|(_, value, _)| value_owned(value))
                .sum::<usize>()
            + out.reads.capacity() * std::mem::size_of::<(ReplaySlot, u64, bool)>()
            + out.heap_owners.capacity() * std::mem::size_of::<ReplayHeapKey>()
            + out.field_reads.capacity() * std::mem::size_of::<ReplaySlot>()
            + out.edges.capacity() * std::mem::size_of::<(u32, u32, u32, u32, u32)>()
            + out.issues.capacity() * 4
    }
}
pub struct ReplayBundle {
    facts: FactSnapshot,
    graph: ProgramGraph,
    metadata: Metadata,
    recording_digest: ContentHash,
}
#[derive(Clone, Debug, Serialize)]
pub struct ReplayExportReport {
    pub node: u32,
    pub symbols: usize,
    pub nodes: usize,
    pub operations: usize,
    pub candidates: usize,
    pub events: usize,
    pub owned_bytes: usize,
}
fn digest(bytes: &[u8]) -> ContentHash {
    ContentHash(Sha256::digest(bytes).into())
}
fn json_error(error: serde_json::Error) -> Error {
    Error::Message(format!("replay metadata: {error}"))
}

#[allow(clippy::too_many_arguments)]
pub fn capture_context<W: World>(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    types: &TypeIndex,
    world: &W,
    node: NodeId,
    receiver: Value,
    arguments: &[Value],
    limits: &ReplayLimits,
) -> Result<ReplayBundle, Error> {
    if limits.scratch_bytes < 4096 || limits.max_set_members == 0 {
        return Err(Error::Limit("replay scratch budget"));
    }
    if graph.facts_identity != facts.identity {
        return Err(Error::Invalid("replay source graph binding"));
    }
    let record = graph
        .nodes
        .get(node.index())
        .ok_or(Error::Invalid("replay root"))?;
    if !record.body.is_none() {
        let body = facts
            .bodies
            .get(record.body.index())
            .ok_or(Error::Invalid("replay source body reference"))?;
        if body.operations.len as usize > limits.max_records {
            return Err(Error::Limit("replay source operations"));
        }
    }
    let recording = RecordingWorld {
        world,
        events: Mutex::new(Vec::new()),
        max_events: limits.max_records,
        overflow: std::sync::atomic::AtomicBool::new(false),
    };
    let mut scratch = Scratch::new(limits.max_set_members);
    let mut evaluated = Evaluation::default();
    evaluate(
        facts,
        graph,
        types,
        &recording,
        node,
        receiver,
        arguments,
        &mut scratch,
        &mut evaluated,
    )?;
    if scratch.owned_bytes() > limits.scratch_bytes {
        return Err(Error::Limit("replay scratch budget"));
    }
    let mut expected = ReplayOutcome::from(&evaluated, &scratch.pool, None)?;
    let receiver = ReplayValue::from(world.values(), receiver, None)?;
    let arguments = arguments
        .iter()
        .map(|value| ReplayValue::from(world.values(), *value, None))
        .collect::<Result<Vec<_>, _>>()?;
    if recording
        .overflow
        .load(std::sync::atomic::Ordering::Relaxed)
    {
        return Err(Error::Limit("replay events"));
    }
    let mut events = recording.events.into_inner().unwrap();
    if events.len() > limits.max_records {
        return Err(Error::Limit("replay events"));
    }
    let source_operations = u32::try_from(facts.operations.len())
        .map_err(|_| Error::Limit("replay source operations"))?;
    let source_symbols =
        u32::try_from(facts.symbols.len()).map_err(|_| Error::Limit("replay source symbols"))?;
    let source_base = source_operations
        .checked_add(source_symbols)
        .filter(|base| *base < LOCAL_HEAP_OWNER)
        .ok_or(Error::Limit("replay source heap owner namespaces"))?;
    let mut owner_inventory = BTreeMap::new();
    for event in &events {
        if let (Request::HeapOwner(key), Response::HeapOwner(owner)) =
            (&event.request, &event.response)
        {
            if let Some(previous) = owner_inventory.insert(*key, *owner) {
                if previous != *owner {
                    return Err(Error::Invalid("nonimmutable replay heap owner"));
                }
            }
        }
    }
    let heap_owners: Vec<_> = owner_inventory
        .into_iter()
        .map(|(key, owner)| ReplayHeapOwner { key, owner })
        .collect();
    for event in &mut events {
        if let Request::Slot(slot) = &mut event.request {
            normalize_heap_slot(slot, source_base, &heap_owners, &evaluated.heap_owners)?;
        }
    }
    for (slot, _) in &mut expected.stores {
        normalize_heap_slot(slot, source_base, &heap_owners, &evaluated.heap_owners)?;
    }
    for (slot, _, _) in &mut expected.reads {
        normalize_heap_slot(slot, source_base, &heap_owners, &evaluated.heap_owners)?;
    }
    for slot in &mut expected.field_reads {
        normalize_heap_slot(slot, source_base, &heap_owners, &evaluated.heap_owners)?;
    }
    // A World is one immutable publication snapshot. Repeated requests must
    // have the same response; otherwise a keyed reduction would be invalid.
    let mut seen = HashMap::with_capacity(events.len());
    for event in &events {
        if seen
            .insert(&event.request, &event.response)
            .is_some_and(|previous| previous != &event.response)
        {
            return Err(Error::Invalid("nonimmutable replay world"));
        }
    }
    drop(seen);
    let mut closure = Closure::new(facts, graph, types, node);
    for &symbol in types.deferred_receivers() {
        closure.symbol(symbol.0);
    }
    for &(receiver, contract) in types.known_receiver_dispatch() {
        closure.symbol(receiver.0);
        closure.symbol(contract.0);
    }
    for relation in &facts.relations {
        if matches!(
            relation.kind,
            RelationKind::DeferredReceiverDispatch | RelationKind::KnownReceiverDispatch
        ) && !relation.file.is_none()
        {
            closure.files.insert(relation.file.0);
        }
    }
    closure.node(node.0);
    if !record.body.is_none() {
        for op in &facts.operations[facts.bodies[record.body.index()].operations.range()] {
            if op.opcode == Opcode::BindCallback {
                closure.callback_certificate(op.target);
            }
        }
    }
    closure.value(&receiver);
    for value in &arguments {
        closure.value(value);
    }
    let mut source_edges: Vec<_> = graph
        .successors(node)
        .map(|(id, edge)| (id, *edge))
        .collect();
    let mut retained_edges: BTreeSet<_> = source_edges.iter().map(|(id, _)| id.0).collect();
    let mut callback_authority = Vec::with_capacity(closure.certificate_nodes.len());
    for &id in &closure.certificate_nodes {
        let record = graph.nodes[id as usize];
        let operations = if record.body.is_none() {
            Vec::new()
        } else {
            let body = facts.bodies[record.body.index()];
            if body.operations.len as usize > limits.max_records {
                return Err(Error::Limit("replay certificate recipe records"));
            }
            body.operations.range().map(|index| index as u32).collect()
        };
        let mut structural_edges = Vec::new();
        for (edge_id, edge) in graph
            .successors(NodeId(id))
            .filter(|(_, edge)| certificate_edge(edge))
        {
            structural_edges.push(edge_id.0);
            if retained_edges.insert(edge_id.0) {
                if source_edges.len() >= limits.max_records {
                    return Err(Error::Limit("replay certificate edges"));
                }
                source_edges.push((edge_id, *edge));
            }
        }
        callback_authority.push(CallbackAuthority {
            node: id,
            operations,
            structural_edges,
        });
    }
    for (_, edge) in &source_edges {
        closure.node(edge.target.0);
        closure.symbol(edge.receiver.0);
        closure.operation(edge.operation.0);
    }
    for event in &events {
        closure.event(event)?;
    }
    closure.value(&expected.value);
    for value in &expected.arguments {
        closure.value(value);
    }
    for (slot, value) in &expected.stores {
        closure.slot(slot)?;
        closure.value(value);
    }
    for (_, value, _) in &expected.captures {
        closure.value(value);
    }
    closure.close(limits)?;
    let mut mapping = Mapping {
        symbols: closure.symbols.iter().copied().collect(),
        nodes: closure.nodes.iter().copied().collect(),
        operations: Vec::new(),
        edges: source_edges.iter().map(|(id, _)| id.0).collect(),
        source_operations,
        source_symbols,
        heap_owners,
    };
    let mut builder = FactBuilder::new();
    let mut primitive_files = BTreeSet::new();
    let mut primitive_producers = BTreeSet::new();
    if !record.body.is_none() {
        let body = &facts.bodies[record.body.index()];
        for index in body.operations.range() {
            if let Some(producer) =
                types.primitive_long_receiver_producer(OperationId(index as u32))
            {
                primitive_files.insert(body.file.0);
                primitive_files.insert(facts.symbols[producer.index()].file.0);
                primitive_producers.insert(producer.0);
            }
        }
    }
    let mut primitive_source_bytes = 0usize;
    let mut file_map = HashMap::new();
    for &original in &closure.files {
        let file = *facts
            .files
            .get(original as usize)
            .ok_or(Error::Invalid("replay file frontier"))?;
        let id = FileId(builder.facts.files.len() as u32);
        file_map.insert(original, id);
        let path = builder.intern(facts.text(file.path))?;
        let revision = builder.intern(facts.text(file.revision))?;
        let context = builder.intern(facts.text(file.context))?;
        // Source spans are never needed. Retain source bytes and verification
        // only for the compiler receiver evidence used by this transfer.
        let (source, flags) = if primitive_files.contains(&original) {
            let source = facts.text(file.source);
            primitive_source_bytes = primitive_source_bytes
                .checked_add(source.len())
                .filter(|bytes| *bytes <= limits.max_bytes)
                .ok_or(Error::Limit("replay primitive receiver source bytes"))?;
            (builder.intern(source)?, file.flags)
        } else {
            (
                StrId::NONE,
                file.flags & !(SOURCE_VERIFIED | SYNTAX_VERIFIED),
            )
        };
        builder.facts.files.push(FileRecord {
            path,
            source,
            revision,
            context,
            source_hash: file.source_hash,
            flags,
        });
    }
    let file = |id: FileId| {
        if id.is_none() {
            FileId::NONE
        } else {
            file_map[&id.0]
        }
    };
    for &original in &mapping.symbols {
        let source = facts.symbols[original as usize];
        let name = builder.intern(facts.text(source.name))?;
        let context = builder.intern(facts.text(source.context))?;
        let signature = if primitive_producers.contains(&original) {
            builder.intern(facts.text(source.signature))?
        } else {
            StrId::NONE
        };
        builder.facts.symbols.push(SymbolRecord {
            name,
            display: StrId::NONE,
            owner: SymbolId(mapping.compact_symbol(source.owner.0)?),
            file: file(source.file),
            context,
            kind: source.kind,
            properties: source.properties,
            signature,
            span: Span::default(),
            flags: source.flags,
        });
    }
    let mut body_map = HashMap::new();
    for &original in &closure.bodies {
        let body = facts.bodies[original as usize];
        let id = BodyId(builder.facts.bodies.len() as u32);
        body_map.insert(original, id);
        let parameters = IdRange {
            start: builder.facts.operands.len() as u32,
            len: body.parameters.len,
        };
        builder
            .facts
            .operands
            .extend_from_slice(&facts.operands[body.parameters.range()]);
        let start = builder.facts.operations.len() as u32;
        for index in body
            .operations
            .range()
            .filter(|index| closure.operations.contains(&(*index as u32)))
        {
            let source = facts.operations[index];
            mapping.operations.push(index as u32);
            let arguments = IdRange {
                start: builder.facts.operands.len() as u32,
                len: source.arguments.len,
            };
            builder
                .facts
                .operands
                .extend_from_slice(&facts.operands[source.arguments.range()]);
            builder.facts.operations.push(OperationRecord {
                body: id,
                target: SymbolId(mapping.compact_symbol(source.target.0)?),
                arguments,
                span: Span::default(),
                ..source
            });
        }
        builder.facts.bodies.push(BodyRecord {
            symbol: SymbolId(mapping.compact_symbol(body.symbol.0)?),
            file: file(body.file),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange {
                start,
                len: builder.facts.operations.len() as u32 - start,
            },
            parameters,
            body_hash: body.body_hash,
            flags: body.flags,
        });
    }
    let mut parent_inventory = Vec::new();
    for &original in &mapping.symbols {
        let parents = types
            .direct_parents(SymbolId(original))
            .ok_or(Error::Invalid("replay type frontier"))?;
        parent_inventory.push((original, parents.iter().map(|id| id.0).collect()));
        for parent in parents {
            builder.facts.relations.push(RelationRecord {
                source: SymbolId(mapping.compact_symbol(original)?),
                target: SymbolId(mapping.compact_symbol(parent.0)?),
                kind: RelationKind::Parent,
                file: FileId::NONE,
            });
        }
    }
    for relation in &facts.relations {
        if matches!(
            relation.kind,
            RelationKind::DeferredReceiverDispatch | RelationKind::KnownReceiverDispatch
        ) {
            builder.facts.relations.push(RelationRecord {
                source: SymbolId(mapping.compact_symbol(relation.source.0)?),
                target: SymbolId(mapping.compact_symbol(relation.target.0)?),
                kind: relation.kind,
                file: file(relation.file),
            });
        }
    }
    for row in &facts.result_bounds {
        if !closure.symbols.contains(&row.symbol.0)
            || (!row.operation.is_none() && !closure.operations.contains(&row.operation.0))
        {
            continue;
        }
        let classes = IdRange {
            start: builder.facts.bound_classes.len() as u32,
            len: row.classes.len,
        };
        for class in &facts.bound_classes[row.classes.range()] {
            builder
                .facts
                .bound_classes
                .push(SymbolId(mapping.compact_symbol(class.0)?));
        }
        builder.facts.bound_classes[classes.range()].sort_unstable();
        builder.facts.result_bounds.push(ResultBoundRecord {
            symbol: SymbolId(mapping.compact_symbol(row.symbol.0)?),
            operation: OperationId(mapping.compact_op(row.operation.0)?),
            classes,
        });
    }
    builder
        .facts
        .result_bounds
        .sort_unstable_by_key(|row| (row.symbol, row.operation));
    for issue in &facts.issues {
        if !issue.symbol.is_none() && !closure.symbols.contains(&issue.symbol.0) {
            continue;
        }
        if !issue.file.is_none() && !closure.files.contains(&issue.file.0) {
            continue;
        }
        builder.facts.issues.push(IssueRecord {
            kind: issue.kind,
            file: file(issue.file),
            symbol: SymbolId(mapping.compact_symbol(issue.symbol.0)?),
            detail: StrId::NONE,
        });
    }
    let compact_facts = builder.finish()?;
    let mut compact_graph = ProgramGraph {
        symbol_nodes: vec![NodeId::NONE; mapping.symbols.len()],
        ..Default::default()
    };
    for (index, &original) in mapping.nodes.iter().enumerate() {
        let source = graph.nodes[original as usize];
        let symbol = SymbolId(mapping.compact_symbol(source.symbol.0)?);
        compact_graph.nodes.push(NodeRecord {
            symbol,
            file: file(source.file),
            body: if source.body.is_none() {
                BodyId::NONE
            } else {
                body_map[&source.body.0]
            },
            flags: source.flags,
        });
        if graph.node_for_symbol(source.symbol) == Some(NodeId(original)) {
            compact_graph.symbol_nodes[symbol.index()] = NodeId(index as u32);
        }
    }
    for (_, edge) in source_edges {
        compact_graph.edges.push(EdgeRecord {
            source: NodeId(mapping.compact_node(edge.source.0)?),
            target: NodeId(mapping.compact_node(edge.target.0)?),
            kind: edge.kind,
            occurrence: OccurrenceId::NONE,
            operation: OperationId(mapping.compact_op(edge.operation.0)?),
            receiver: SymbolId(mapping.compact_symbol(edge.receiver.0)?),
            flags: edge.flags,
        });
    }
    compact_graph.index()?;
    let metadata = Metadata {
        version: VERSION,
        source_facts: facts.identity.to_string(),
        source_graph: graph.identity.to_string(),
        root: node.0,
        max_members: limits.max_set_members,
        mapping,
        receiver,
        arguments,
        events,
        expected,
        scope: String::new(),
        parent_inventory,
        deferred_receiver_inventory: types.deferred_receivers().iter().map(|id| id.0).collect(),
        known_receiver_inventory: types
            .known_receiver_dispatch()
            .iter()
            .map(|(receiver, contract)| (receiver.0, contract.0))
            .collect(),
        callback_authority,
        disabled: Vec::new(),
        strict_events: true,
        artifacts: None,
        scratch_required: scratch.owned_bytes().max(4096),
    };
    let mut bundle = ReplayBundle {
        facts: compact_facts,
        graph: compact_graph,
        metadata,
        recording_digest: ContentHash::default(),
    };
    let scope = bundle.scope_digest()?;
    bundle.metadata.scope = scope.to_string();
    bundle.facts.identity = scope;
    bundle.graph.facts_identity = scope;
    bundle.graph.identity = digest(&[scope.0.as_slice(), graph.identity.0.as_slice()].concat());
    bundle.recording_digest = digest(&serde_json::to_vec(&bundle.metadata).map_err(json_error)?);
    bundle.replay(&ReplayOptions {
        scratch_bytes: limits.scratch_bytes,
        verify_expected: true,
    })?;
    Ok(bundle)
}

impl ReplayBundle {
    fn scope_digest(&self) -> Result<ContentHash, Error> {
        let map = &self.metadata.mapping;
        let mut hash = Sha256::new();
        hash.update(b"selector-transfer-replay-scope/v3\0");
        hash.update(map.source_operations.to_le_bytes());
        hash.update(map.source_symbols.to_le_bytes());
        hash.update((map.heap_owners.len() as u64).to_le_bytes());
        for entry in &map.heap_owners {
            hash.update(entry.key.site.to_le_bytes());
            hash.update(entry.key.root.to_le_bytes());
            hash.update(entry.owner.unwrap_or(u32::MAX).to_le_bytes());
        }
        self.scope_digest_seed(hash)
    }
    fn scope_digest_seed(&self, mut hash: Sha256) -> Result<ContentHash, Error> {
        let map = &self.metadata.mapping;
        if map.symbols.len() != self.facts.symbols.len()
            || map.nodes.len() != self.graph.nodes.len()
            || map.operations.len() != self.facts.operations.len()
            || map.edges.len() != self.graph.edges.len()
        {
            return Err(Error::Invalid("replay scope inventory"));
        }
        for ids in [&map.symbols, &map.nodes, &map.operations, &map.edges] {
            let mut sorted = ids.clone();
            sorted.sort_unstable();
            if sorted.last() == Some(&u32::MAX) || sorted.windows(2).any(|pair| pair[0] == pair[1])
            {
                return Err(Error::Invalid("replay duplicate identity"));
            }
        }
        if map.operations.iter().any(|id| *id >= map.source_operations)
            || map.symbols.iter().any(|id| *id >= map.source_symbols)
            || self.metadata.parent_inventory.len() != map.symbols.len()
            || self
                .metadata
                .parent_inventory
                .iter()
                .map(|(id, _)| *id)
                .ne(map.symbols.iter().copied())
        {
            return Err(Error::Invalid("replay type inventory"));
        }
        let source_base = map.source_owner_base()?;
        if map
            .heap_owners
            .windows(2)
            .any(|pair| pair[0].key >= pair[1].key)
        {
            return Err(Error::Invalid("replay heap owner ordering"));
        }
        map.compact_owner_base()?
            .checked_add(map.heap_owners.len() as u32)
            .filter(|end| *end < LOCAL_HEAP_OWNER)
            .ok_or(Error::Limit("replay compact heap owners"))?;
        let mut owner_ids = BTreeSet::new();
        let mut owner_keys = BTreeSet::new();
        for entry in &map.heap_owners {
            if entry.key.site == u32::MAX
                || entry.key.root == u32::MAX
                || !owner_keys.insert(entry.key)
                || entry.owner.is_some_and(|id| {
                    id < source_base || id >= LOCAL_HEAP_OWNER || !owner_ids.insert(id)
                })
            {
                return Err(Error::Invalid("replay heap owner inventory"));
            }
            let site = map.compact_op(entry.key.site)?;
            map.compact_symbol(entry.key.root)?;
            if !self.facts.operations[site as usize].opcode.is_heap_site() {
                return Err(Error::Invalid("replay heap owner allocation"));
            }
        }
        let mut requested_keys = BTreeSet::new();
        for event in &self.metadata.events {
            if let (Request::HeapOwner(key), Response::HeapOwner(owner)) =
                (&event.request, &event.response)
            {
                if !map
                    .heap_entry(*key)
                    .is_some_and(|entry| entry.owner == *owner)
                {
                    return Err(Error::Invalid("replay heap owner response"));
                }
                requested_keys.insert(*key);
            }
        }
        if owner_keys != requested_keys {
            return Err(Error::Invalid("replay heap owner frontier"));
        }
        let root = NodeId(map.compact_node(self.metadata.root)?);
        let mut required_authority = BTreeSet::new();
        let root_body = self.graph.nodes[root.index()].body;
        if !root_body.is_none() {
            let body = self
                .facts
                .bodies
                .get(root_body.index())
                .ok_or(Error::Invalid("replay node body reference"))?;
            let operations = self
                .facts
                .operations
                .get(body.operations.range())
                .ok_or(Error::Invalid("replay callback recipe operations"))?;
            for op in operations {
                if op.opcode == Opcode::BindCallback {
                    if let Some(node) = self.graph.node_for_symbol(op.target) {
                        required_authority.insert(map.original_node(node)?);
                    }
                }
            }
        }
        if self
            .metadata
            .callback_authority
            .iter()
            .map(|entry| entry.node)
            .ne(required_authority.iter().copied())
        {
            return Err(Error::Invalid("replay callback authority frontier"));
        }
        for entry in &self.metadata.callback_authority {
            let node = NodeId(map.compact_node(entry.node)?);
            let body = self.graph.nodes[node.index()].body;
            let operations = if body.is_none() {
                Vec::new()
            } else {
                self.facts
                    .bodies
                    .get(body.index())
                    .ok_or(Error::Invalid("replay node body reference"))?
                    .operations
                    .range()
                    .map(|i| map.original_op(OperationId(i as u32)))
                    .collect::<Result<Vec<_>, _>>()?
            };
            let edges = self
                .graph
                .successors(node)
                .filter(|(_, edge)| certificate_edge(edge))
                .map(|(id, _)| map.original_edge(id))
                .collect::<Result<Vec<_>, _>>()?;
            if operations != entry.operations
                || edges != entry.structural_edges
                || operations
                    .windows(2)
                    .any(|pair| pair[0].checked_add(1) != Some(pair[1]))
            {
                return Err(Error::Invalid("replay omitted callback recipe authority"));
            }
        }
        if self.graph.edges.iter().any(|edge| {
            edge.source != root
                && !(required_authority.contains(&map.nodes[edge.source.index()])
                    && certificate_edge(edge))
        }) {
            return Err(Error::Invalid("replay candidate frontier"));
        }
        for entry in &self.metadata.callback_authority {
            hash.update(entry.node.to_le_bytes());
            hash.update((entry.operations.len() as u64).to_le_bytes());
            for id in &entry.operations {
                hash.update(id.to_le_bytes());
            }
            hash.update((entry.structural_edges.len() as u64).to_le_bytes());
            for id in &entry.structural_edges {
                hash.update(id.to_le_bytes());
            }
        }
        for (index, symbol) in self.facts.symbols.iter().enumerate() {
            hash.update(map.symbols[index].to_le_bytes());
            for text in [
                self.facts.text(symbol.name),
                self.facts.text(symbol.context),
            ] {
                hash.update((text.len() as u64).to_le_bytes());
                hash.update(text.as_bytes());
            }
            for word in [
                map.original_symbol(symbol.owner)?,
                symbol.kind,
                symbol.flags,
            ] {
                hash.update(word.to_le_bytes());
            }
            hash.update(symbol.properties.to_le_bytes());
        }
        for &(original, ref expected) in &self.metadata.parent_inventory {
            let symbol = SymbolId(map.compact_symbol(original)?);
            let actual = self
                .facts
                .relations
                .iter()
                .filter(|relation| {
                    relation.kind == RelationKind::Parent && relation.source == symbol
                })
                .map(|relation| map.original_symbol(relation.target))
                .collect::<Result<Vec<_>, _>>()?;
            if &actual != expected {
                return Err(Error::Invalid(
                    "replay omitted or reordered parent frontier",
                ));
            }
            hash.update(original.to_le_bytes());
            hash.update((actual.len() as u64).to_le_bytes());
            for parent in actual {
                hash.update(parent.to_le_bytes());
            }
        }
        let mut actual_deferred = self
            .facts
            .relations
            .iter()
            .filter(|row| row.kind == RelationKind::DeferredReceiverDispatch)
            .map(|row| map.original_symbol(row.source))
            .collect::<Result<Vec<_>, _>>()?;
        actual_deferred.sort_unstable();
        actual_deferred.dedup();
        if actual_deferred != self.metadata.deferred_receiver_inventory {
            return Err(Error::Invalid("replay receiver dispatch inventory"));
        }
        let mut actual_known = self
            .facts
            .relations
            .iter()
            .filter(|row| row.kind == RelationKind::KnownReceiverDispatch)
            .map(|row| {
                Ok((
                    map.original_symbol(row.source)?,
                    map.original_symbol(row.target)?,
                ))
            })
            .collect::<Result<Vec<_>, Error>>()?;
        actual_known.sort_unstable();
        actual_known.dedup();
        if actual_known != self.metadata.known_receiver_inventory {
            return Err(Error::Invalid("replay known receiver dispatch inventory"));
        }
        // Keep historical marker-free scope seals byte compatible. The typed
        // nonempty inventory binds all marker identities independently of the
        // recorded result's first issue and the caller's reduction masks.
        if !actual_deferred.is_empty() {
            hash.update(b"deferred-receiver-dispatch/v1\0");
            hash.update((actual_deferred.len() as u64).to_le_bytes());
            for symbol in actual_deferred {
                hash.update(symbol.to_le_bytes());
            }
        }
        if !actual_known.is_empty() {
            hash.update(b"known-receiver-dispatch/v1\0");
            hash.update((actual_known.len() as u64).to_le_bytes());
            for (receiver, contract) in actual_known {
                hash.update(receiver.to_le_bytes());
                hash.update(contract.to_le_bytes());
            }
        }
        let primitive = primitive_long_receiver_sites(&self.facts);
        if !primitive.is_empty() {
            hash.update(b"primitive-long-receiver/v1\0");
            hash.update((primitive.len() as u64).to_le_bytes());
            for (operation, producer) in primitive {
                hash.update(map.original_op(operation)?.to_le_bytes());
                hash.update(map.original_symbol(producer)?.to_le_bytes());
            }
        }
        for body in &self.facts.bodies {
            hash.update(map.original_symbol(body.symbol)?.to_le_bytes());
            hash.update(body.flags.to_le_bytes());
            hash.update(body.parameters.len.to_le_bytes());
            for value in &self.facts.operands[body.parameters.range()] {
                hash.update(value.0.to_le_bytes());
            }
            hash.update(body.operations.len.to_le_bytes());
            for index in body.operations.range() {
                let op = self.facts.operations[index];
                for word in [
                    map.operations[index],
                    op.opcode as u32,
                    map.original_symbol(op.target)?,
                    op.dest.0,
                    op.a.0,
                    op.b.0,
                    op.flags,
                    op.arguments.len,
                ] {
                    hash.update(word.to_le_bytes());
                }
                for value in &self.facts.operands[op.arguments.range()] {
                    hash.update(value.0.to_le_bytes());
                }
            }
        }
        for node in &self.graph.nodes {
            for word in [map.original_symbol(node.symbol)?, node.body.0, node.flags] {
                hash.update(word.to_le_bytes());
            }
        }
        for node in &self.graph.symbol_nodes {
            hash.update(map.original_node(*node)?.to_le_bytes());
        }
        for edge in &self.graph.forward_edges {
            hash.update(map.original_edge(*edge)?.to_le_bytes());
        }
        for edge in &self.graph.edges {
            for word in [
                map.original_node(edge.source)?,
                map.original_node(edge.target)?,
                edge.kind as u32,
                map.original_op(edge.operation)?,
                map.original_symbol(edge.receiver)?,
                edge.flags,
            ] {
                hash.update(word.to_le_bytes());
            }
        }
        for row in &self.facts.result_bounds {
            for word in [
                map.original_symbol(row.symbol)?,
                map.original_op(row.operation)?,
                row.classes.len,
            ] {
                hash.update(word.to_le_bytes());
            }
            for class in &self.facts.bound_classes[row.classes.range()] {
                hash.update(map.original_symbol(*class)?.to_le_bytes());
            }
        }
        for issue in &self.facts.issues {
            hash.update((issue.kind as u32).to_le_bytes());
            hash.update(map.original_symbol(issue.symbol)?.to_le_bytes());
        }
        Ok(ContentHash(hash.finalize().into()))
    }
    fn validate(&self, limits: &ReplayLimits) -> Result<(), Error> {
        if !matches!(self.metadata.version, 3 | 4 | VERSION)
            || self.metadata.max_members == 0
            || self.metadata.max_members > 4096
        {
            return Err(Error::Invalid("replay version or set bound"));
        }
        if self.metadata.version < VERSION && !self.metadata.expected.effects_open {
            return Err(Error::Invalid("legacy replay effects closure"));
        }
        if self.facts.symbols.len()
            + self.facts.operations.len()
            + self.metadata.events.len()
            + self.metadata.mapping.heap_owners.len()
            > limits.max_records
        {
            return Err(Error::Limit("replay records"));
        }
        if self.metadata.version == 3
            && self
                .facts
                .operations
                .iter()
                .any(|op| matches!(op.opcode, Opcode::PackSequence | Opcode::ReadElements))
        {
            return Err(Error::Invalid("legacy replay sequence operation"));
        }
        self.facts.validate()?;
        self.graph.validate()?;
        let canonical_masks = self
            .metadata
            .disabled
            .windows(2)
            .all(|pair| pair[0] < pair[1]);
        for edge in &self.graph.edges {
            validate_scoped_dispatch_edge(&self.facts, &self.graph, edge)?;
            if edge.flags & EDGE_DEFERRED_DISPATCH != 0
                && (!canonical_masks
                    || self
                        .metadata
                        .disabled
                        .binary_search(&self.metadata.mapping.original_op(edge.operation)?)
                        .is_ok())
            {
                return Err(Error::Invalid(
                    "replay mask changes scoped dispatch authority",
                ));
            }
        }
        self.metadata.validate_heap_references(&self.facts)?;
        for raw in &self.metadata.expected.issues {
            if !IssueKind::decode(*raw)?.is_execution_boundary() {
                return Err(Error::Invalid(
                    "metadata issue in replay execution obligations",
                ));
            }
        }
        for node in &self.graph.nodes {
            if !node.body.is_none() && node.body.index() >= self.facts.bodies.len() {
                return Err(Error::Invalid("replay node body reference"));
            }
            if !node.file.is_none() && node.file.index() >= self.facts.files.len() {
                return Err(Error::Invalid("replay node file reference"));
            }
        }
        if let Some(recorded) = &self.metadata.expected.first_issue {
            let kind = IssueKind::decode(recorded.kind)?;
            let operation = OperationId(self.metadata.mapping.compact_op(recorded.operation)?);
            let reason = RuntimeIssueReason::decode(recorded.reason)?;
            let site = RuntimeIssueSite {
                kind,
                operation,
                reason,
            };
            site.validate()?;
            let root = NodeId(self.metadata.mapping.compact_node(self.metadata.root)?);
            let node = self.graph.nodes[root.index()];
            if !self.metadata.expected.issues.contains(&recorded.kind) {
                return Err(Error::Invalid("replay runtime issue obligation"));
            }
            if operation.is_none() {
                if reason == RuntimeIssueReason::MissingExecutableBody
                    && (!node.body.is_none() || node.flags & NODE_EFFECTS_COMPLETE != 0)
                {
                    return Err(Error::Invalid("replay missing executable body site"));
                }
            } else {
                let op = self
                    .facts
                    .operations
                    .get(operation.index())
                    .ok_or(Error::Invalid("replay runtime issue operation"))?;
                let body = self
                    .facts
                    .bodies
                    .get(node.body.index())
                    .ok_or(Error::Invalid("replay runtime issue body"))?;
                if op.body != node.body
                    || !body.operations.range().contains(&operation.index())
                    || !reason.accepts_opcode(op.opcode)
                {
                    return Err(Error::Invalid("replay runtime issue operation owner"));
                }
            }
            if reason == RuntimeIssueReason::ExecutionGuard
                && !self.graph.successors(root).any(|(_, edge)| {
                    (edge.kind == EdgeKind::Guard || edge.flags & EDGE_UNKNOWN != 0)
                        && edge.operation == operation
                })
            {
                return Err(Error::Invalid("replay runtime issue guard"));
            }
        }
        if self.metadata.events.iter().any(|event| {
            !matches!(
                (&event.request, &event.response),
                (Request::Summary { .. }, Response::Summary { .. })
                    | (Request::Slot(_), Response::Slot { .. })
                    | (Request::Capture(_), Response::Capture(_))
                    | (Request::Binding { .. }, Response::Binding(_))
                    | (Request::HeapOwner(_), Response::HeapOwner(_))
            )
        }) {
            return Err(Error::Invalid("replay response kind"));
        }
        let scope = self.scope_digest()?;
        if scope.to_string() != self.metadata.scope
            || self.facts.identity != scope
            || self.graph.facts_identity != scope
        {
            return Err(Error::Invalid("replay scope identity"));
        }
        let original_graph = ContentHash::from_hex(&self.metadata.source_graph)?;
        ContentHash::from_hex(&self.metadata.source_facts)?;
        if self.graph.identity
            != digest(&[scope.0.as_slice(), original_graph.0.as_slice()].concat())
        {
            return Err(Error::Invalid("replay graph identity"));
        }
        let bytes = serde_json::to_vec(&self.metadata).map_err(json_error)?;
        if bytes.len() > limits.max_bytes {
            return Err(Error::Limit("replay metadata bytes"));
        }
        if digest(&bytes) != self.recording_digest {
            return Err(Error::Invalid("replay omitted or corrupted recording"));
        }
        for &operation in &self.metadata.disabled {
            self.mask_operation(operation)?;
        }
        Ok(())
    }
    // Reduction masks change this one transfer evaluation. Callee recipes and
    // their structural edges remain immutable static authority for TypeIndex.
    // An invocation carrying a scoped dispatch certificate stays intact: its
    // edge is bound to the original opcode and cannot become an unconditional
    // guard or silently disappear when that opcode is masked.
    fn mask_operation(&self, original: u32) -> Result<usize, Error> {
        let operation = self.metadata.mapping.compact_op(original)? as usize;
        let node = self.metadata.mapping.compact_node(self.metadata.root)? as usize;
        let body = self.graph.nodes[node].body;
        if body.is_none()
            || !self.facts.bodies[body.index()]
                .operations
                .range()
                .contains(&operation)
        {
            return Err(Error::Invalid("replay mask outside evaluated body"));
        }
        // Both persisted masks and ReplayRuntime::run's transient masks enter
        // here before any operation is changed. Fact-only receiver frontiers
        // have no graph Guard edge whose validator could reject a masked call.
        if !self.metadata.deferred_receiver_inventory.is_empty()
            && receiver_dispatch_operation(&self.facts, OperationId(operation as u32))
        {
            return Err(Error::Invalid(
                "replay mask changes receiver dispatch authority",
            ));
        }
        Ok(operation)
    }
    // Reuse the existing operation list as a mask bitmap. Walking source edges
    // once avoids rescanning the candidate universe for every reduction mask.
    fn reduction_operations(&self) -> Result<(Vec<u32>, usize), Error> {
        let node = NodeId(self.metadata.mapping.compact_node(self.metadata.root)?);
        let body = self.graph.nodes[node.index()].body;
        if body.is_none() {
            return Ok((Vec::new(), 0));
        }
        let range = self.facts.bodies[body.index()].operations;
        let mut operations: Vec<_> = range
            .range()
            .map(|index| {
                if !self.metadata.deferred_receiver_inventory.is_empty()
                    && receiver_dispatch_operation(&self.facts, OperationId(index as u32))
                {
                    u32::MAX
                } else {
                    self.metadata.mapping.operations[index]
                }
            })
            .collect();
        for (_, edge) in self.graph.successors(node) {
            if edge.flags & EDGE_DEFERRED_DISPATCH != 0 {
                operations[(edge.operation.0 - range.start) as usize] = u32::MAX;
            }
        }
        operations.retain(|id| *id != u32::MAX);
        Ok((operations, range.len as usize))
    }
    pub fn report(&self) -> ReplayExportReport {
        ReplayExportReport {
            node: self.metadata.root,
            symbols: self.facts.symbols.len(),
            nodes: self.graph.nodes.len(),
            operations: self.facts.operations.len(),
            candidates: self.graph.edges.len(),
            events: self.metadata.events.len(),
            owned_bytes: self.facts.owned_bytes()
                + self.graph.owned_bytes()
                + self.metadata.owned_bytes(),
        }
    }
    pub fn write(&self, directory: &Path) -> Result<ReplayExportReport, Error> {
        self.validate(&ReplayLimits::default())?;
        std::fs::create_dir_all(directory)?;
        let facts_id = selector_facts::codec::write(&directory.join("facts.bin"), &self.facts)?;
        let graph_id = selector_graph::codec::write(&directory.join("graph.bin"), &self.graph)?;
        let mut metadata = self.metadata.clone();
        metadata.artifacts = Some((facts_id.to_string(), graph_id.to_string()));
        let bytes = serde_json::to_vec(&metadata).map_err(json_error)?;
        let seal = digest(&bytes);
        std::fs::write(directory.join("metadata.json"), bytes)?;
        // Publish the final seal only after all immutable components are written.
        std::fs::write(directory.join("recording.sha256"), seal.0)?;
        Ok(self.report())
    }
    pub fn read(directory: &Path, limits: &ReplayLimits) -> Result<Self, Error> {
        let mut total = 0u64;
        for name in [
            "facts.bin",
            "graph.bin",
            "metadata.json",
            "recording.sha256",
        ] {
            total = total
                .checked_add(std::fs::metadata(directory.join(name))?.len())
                .ok_or(Error::Limit("replay bundle bytes"))?;
        }
        if total > limits.max_bytes as u64 {
            return Err(Error::Limit("replay bundle bytes"));
        }
        let bytes = std::fs::read(directory.join("metadata.json"))?;
        let seal = std::fs::read(directory.join("recording.sha256"))?;
        if seal.len() != 32 || digest(&bytes).0.as_slice() != seal {
            return Err(Error::Invalid("replay recording digest"));
        }
        let metadata: Metadata = serde_json::from_slice(&bytes).map_err(json_error)?;
        let mut facts = selector_facts::codec::read(&directory.join("facts.bin"))?;
        let scope = ContentHash::from_hex(&metadata.scope)?;
        let mut graph = selector_graph::codec::read_bound(&directory.join("graph.bin"), scope)?;
        if metadata.artifacts.as_ref()
            != Some(&(facts.identity.to_string(), graph.identity.to_string()))
        {
            return Err(Error::Invalid("replay artifact identity"));
        }
        // Both full artifact hashes were checked above. Restore the in-memory
        // semantic identities used by capture and transfer comparison.
        facts.identity = scope;
        let source_graph = ContentHash::from_hex(&metadata.source_graph)?;
        graph.identity = digest(&[scope.0.as_slice(), source_graph.0.as_slice()].concat());
        let bundle = Self {
            facts,
            graph,
            metadata,
            recording_digest: digest(&bytes),
        };
        bundle.validate(limits)?;
        Ok(bundle)
    }
    pub fn replay(&self, options: &ReplayOptions) -> Result<ReplayOutcome, Error> {
        self.runtime(options)?
            .run(&self.metadata.disabled, options.verify_expected)
    }
    pub fn runtime(&self, options: &ReplayOptions) -> Result<ReplayRuntime<'_>, Error> {
        ReplayRuntime::new(self, options)
    }
}

fn request_hash(request: &Request) -> u64 {
    let mut hash = std::collections::hash_map::DefaultHasher::new();
    request.hash(&mut hash);
    hash.finish()
}
#[derive(Debug, Serialize)]
pub struct ReplayComparison {
    pub expected: ReplayOutcome,
    pub actual: ReplayOutcome,
    pub equal: bool,
}
impl ReplayBundle {
    /// Compare a changed kernel against recorded output. Known unused reads are
    /// allowed; new world requests always remain an explicit frontier error.
    pub fn compare(&self, options: &ReplayOptions) -> Result<ReplayComparison, Error> {
        let actual = self.replay(&ReplayOptions {
            scratch_bytes: options.scratch_bytes,
            verify_expected: false,
        })?;
        Ok(ReplayComparison {
            equal: actual == self.metadata.expected,
            expected: self.metadata.expected.clone(),
            actual,
        })
    }
}
enum LoadedResponse {
    Summary(SummaryRead),
    Slot(Value, u64, bool),
    Capture(Option<(Value, Vec<Value>, u64)>),
    Binding(Option<u32>),
    HeapOwner(Option<u32>),
}
#[derive(Default)]
struct ReplayState {
    cursor: usize,
    strict: bool,
    fault: Option<&'static str>,
    local_owners: Vec<HeapOwnerKey>,
}
struct ReplayWorld<'a> {
    bundle: &'a ReplayBundle,
    pool: ValuePool,
    responses: Vec<LoadedResponse>,
    request_heads: HashMap<u64, usize>,
    request_next: Vec<usize>,
    state: Mutex<ReplayState>,
}
impl<'a> ReplayWorld<'a> {
    fn new(bundle: &'a ReplayBundle) -> Result<Self, Error> {
        let mut pool = ValuePool::new(bundle.metadata.max_members);
        let map = &bundle.metadata.mapping;
        let compact_owner_base = map.compact_owner_base()?;
        let compact_owners: HashMap<_, _> = map
            .heap_owners
            .iter()
            .enumerate()
            .filter_map(|(index, entry)| {
                entry
                    .owner
                    .map(|owner| (owner, compact_owner_base + index as u32))
            })
            .collect();
        let mut responses = Vec::with_capacity(bundle.metadata.events.len());
        for event in &bundle.metadata.events {
            responses.push(match &event.response {
                Response::Summary {
                    context,
                    value,
                    version,
                    present,
                } => LoadedResponse::Summary(SummaryRead {
                    context: context.map(ContextId),
                    value: value.load(&mut pool, map)?,
                    version: *version,
                    present: *present,
                }),
                Response::Slot {
                    value,
                    version,
                    present,
                } => LoadedResponse::Slot(value.load(&mut pool, map)?, *version, *present),
                Response::Capture(value) => LoadedResponse::Capture(
                    value
                        .as_ref()
                        .map(|(receiver, args, version)| {
                            Ok::<_, Error>((
                                receiver.load(&mut pool, map)?,
                                args.iter()
                                    .map(|value| value.load(&mut pool, map))
                                    .collect::<Result<Vec<_>, Error>>()?,
                                *version,
                            ))
                        })
                        .transpose()?,
                ),
                Response::Binding(value) => LoadedResponse::Binding(*value),
                Response::HeapOwner(value) => {
                    let owner = value
                        .map(|owner| {
                            compact_owners
                                .get(&owner)
                                .copied()
                                .ok_or(Error::Invalid("replay heap owner response"))
                        })
                        .transpose()?;
                    LoadedResponse::HeapOwner(owner)
                }
            });
        }
        let mut request_heads = HashMap::with_capacity(bundle.metadata.events.len());
        let mut request_next = Vec::with_capacity(bundle.metadata.events.len());
        for (index, event) in bundle.metadata.events.iter().enumerate() {
            let key = request_hash(&event.request);
            request_next.push(request_heads.insert(key, index).unwrap_or(usize::MAX));
        }
        Ok(Self {
            bundle,
            pool,
            responses,
            request_heads,
            request_next,
            state: Mutex::new(ReplayState::default()),
        })
    }
    fn reset(&self, strict: bool) {
        let mut state = self.state.lock().unwrap();
        state.cursor = 0;
        state.strict = strict;
        state.fault = None;
        state.local_owners.clear();
    }
    fn find(&self, request: Result<Request, Error>) -> Option<usize> {
        let mut state = self.state.lock().unwrap();
        let Ok(request) = request else {
            state.fault = Some("replay request identity frontier");
            return None;
        };
        if state.strict {
            let index = state.cursor;
            state.cursor += 1;
            if self
                .bundle
                .metadata
                .events
                .get(index)
                .is_some_and(|event| event.request == request)
            {
                return Some(index);
            }
            state.fault = Some("replay unrecorded or reordered world request");
        }
        let mut next = self
            .request_heads
            .get(&request_hash(&request))
            .copied()
            .unwrap_or(usize::MAX);
        let mut found = None;
        while next != usize::MAX {
            if self.bundle.metadata.events[next].request == request {
                found = Some(next);
                break;
            }
            next = self.request_next[next];
        }
        if found.is_none() {
            state.fault = Some("replay unrecorded world frontier");
        }
        found
    }
    fn finish(&self) -> Result<(), Error> {
        let state = self.state.lock().unwrap();
        if let Some(message) = state.fault {
            return Err(Error::Invalid(message));
        }
        if state.strict && state.cursor != self.responses.len() {
            return Err(Error::Invalid("replay omitted world request"));
        }
        Ok(())
    }
}
impl World for ReplayWorld<'_> {
    fn values(&self) -> &ValuePool {
        &self.pool
    }
    fn heap_owner(&self, key: HeapOwnerKey) -> Option<u32> {
        let map = &self.bundle.metadata.mapping;
        let request = (|| {
            Ok(Request::HeapOwner(ReplayHeapKey {
                site: map.original_op(key.site)?,
                root: map.original_symbol(key.root)?,
            }))
        })();
        let index = self.find(request)?;
        if let LoadedResponse::HeapOwner(owner) = self.responses[index] {
            if owner.is_none() {
                let mut state = self.state.lock().unwrap();
                if !state.local_owners.contains(&key) {
                    state.local_owners.push(key);
                }
            }
            owner
        } else {
            None
        }
    }
    fn summary(
        &self,
        node: NodeId,
        receiver: Value,
        args: &[Value],
        local: &ValuePool,
        _scratch: &mut Vec<Value>,
    ) -> SummaryRead {
        let map = &self.bundle.metadata.mapping;
        let request = (|| {
            Ok(Request::Summary {
                node: map.original_node(node)?,
                receiver: ReplayValue::from(local, receiver, Some(map))?,
                arguments: args
                    .iter()
                    .map(|value| ReplayValue::from(local, *value, Some(map)))
                    .collect::<Result<_, _>>()?,
            })
        })();
        if let Some(index) = self.find(request) {
            if let LoadedResponse::Summary(value) = self.responses[index] {
                return value;
            }
        }
        SummaryRead {
            context: None,
            value: Value::TOP,
            version: 0,
            present: false,
        }
    }
    fn slot(&self, slot: Slot) -> (Value, u64, bool) {
        let request = ReplaySlot::from(
            slot,
            Some(&self.bundle.metadata.mapping),
            &self.state.lock().unwrap().local_owners,
        )
        .map(Request::Slot);
        if let Some(index) = self.find(request) {
            if let LoadedResponse::Slot(value, version, present) = self.responses[index] {
                return (value, version, present);
            }
        }
        (Value::TOP, 0, false)
    }
    fn capture(&self, binding: u32) -> Option<(Value, &[Value], u64)> {
        let index = self.find(Ok(Request::Capture(binding)))?;
        if let LoadedResponse::Capture(value) = &self.responses[index] {
            return value
                .as_ref()
                .map(|(receiver, args, version)| (*receiver, args.as_slice(), *version));
        }
        None
    }
    fn binding(
        &self,
        site: OperationId,
        receiver: Value,
        args: &[Value],
        local: &ValuePool,
        _atoms: &mut Vec<Atom>,
        _values: &mut Vec<Value>,
    ) -> Option<u32> {
        let map = &self.bundle.metadata.mapping;
        let request = (|| {
            Ok(Request::Binding {
                site: map.original_op(site)?,
                receiver: ReplayValue::from(local, receiver, Some(map))?,
                arguments: args
                    .iter()
                    .map(|value| ReplayValue::from(local, *value, Some(map)))
                    .collect::<Result<_, _>>()?,
            })
        })();
        let index = self.find(request)?;
        if let LoadedResponse::Binding(value) = self.responses[index] {
            value
        } else {
            None
        }
    }
}
pub struct ReplayRuntime<'a> {
    bundle: &'a ReplayBundle,
    world: ReplayWorld<'a>,
    facts: FactSnapshot,
    types: TypeIndex,
    scratch: Scratch,
    evaluation: Evaluation,
    receiver: Value,
    arguments: Vec<Value>,
    scratch_limit: usize,
}
fn clone_facts(source: &FactSnapshot) -> FactSnapshot {
    FactSnapshot {
        identity: source.identity,
        revision: source.revision,
        strings: StringPool {
            bytes: source.strings.bytes.clone(),
            entries: source.strings.entries.clone(),
        },
        files: source.files.clone(),
        symbols: source.symbols.clone(),
        occurrences: source.occurrences.clone(),
        relations: source.relations.clone(),
        bodies: source.bodies.clone(),
        operations: source.operations.clone(),
        operands: source.operands.clone(),
        suites: source.suites.clone(),
        issues: source.issues.clone(),
        result_bounds: source.result_bounds.clone(),
        bound_classes: source.bound_classes.clone(),
    }
}
impl<'a> ReplayRuntime<'a> {
    fn new(bundle: &'a ReplayBundle, options: &ReplayOptions) -> Result<Self, Error> {
        if options.scratch_bytes < bundle.metadata.scratch_required.max(4096) {
            return Err(Error::Limit("replay scratch budget"));
        }
        bundle.validate(&ReplayLimits::default())?;
        let mut world = ReplayWorld::new(bundle)?;
        let map = &bundle.metadata.mapping;
        let receiver = bundle.metadata.receiver.load(&mut world.pool, map)?;
        let arguments = bundle
            .metadata
            .arguments
            .iter()
            .map(|value| value.load(&mut world.pool, map))
            .collect::<Result<Vec<_>, _>>()?;
        let facts = clone_facts(&bundle.facts);
        let types = TypeIndex::new(&facts);
        let scratch = Scratch::new(bundle.metadata.max_members);
        Ok(Self {
            bundle,
            world,
            facts,
            types,
            scratch,
            evaluation: Evaluation::default(),
            receiver,
            arguments,
            scratch_limit: options.scratch_bytes,
        })
    }
    pub fn owned_bytes(&self) -> usize {
        self.facts.owned_bytes()
            + self.types.owned_bytes()
            + self.scratch.owned_bytes()
            + self.world.pool.owned_bytes()
            + self.world.responses.capacity() * std::mem::size_of::<LoadedResponse>()
            + self
                .world
                .responses
                .iter()
                .map(|response| match response {
                    LoadedResponse::Capture(Some((_, arguments, _))) => {
                        arguments.capacity() * std::mem::size_of::<Value>()
                    }
                    _ => 0,
                })
                .sum::<usize>()
            + self.world.request_heads.capacity() * (std::mem::size_of::<(u64, usize)>() + 1)
            + self.world.request_next.capacity() * std::mem::size_of::<usize>()
            + self.world.state.lock().unwrap().local_owners.capacity()
                * std::mem::size_of::<HeapOwnerKey>()
            + self.arguments.capacity() * std::mem::size_of::<Value>()
            + self.evaluation.calls.capacity()
                * std::mem::size_of::<selector_transfer::CallEffect>()
            + self.evaluation.arguments.capacity() * std::mem::size_of::<Value>()
            + self.evaluation.stores.capacity()
                * std::mem::size_of::<selector_transfer::StoreEffect>()
            + self.evaluation.captures.capacity()
                * std::mem::size_of::<selector_transfer::CaptureEffect>()
            + self.evaluation.reads.capacity() * std::mem::size_of::<Read>()
            + self.evaluation.edges.capacity()
                * std::mem::size_of::<selector_transfer::ExecutionEdge>()
            + self.evaluation.issues.capacity() * std::mem::size_of::<IssueKind>()
            + self.evaluation.heap_owners.capacity() * std::mem::size_of::<HeapOwnerKey>()
            + self.evaluation.field_reads.capacity() * std::mem::size_of::<Slot>()
    }
    pub fn run(&mut self, disabled: &[u32], verify_expected: bool) -> Result<ReplayOutcome, Error> {
        for &original in disabled {
            self.bundle.mask_operation(original)?;
        }
        self.facts
            .operations
            .copy_from_slice(&self.bundle.facts.operations);
        for original in disabled {
            let index = self.bundle.mask_operation(*original)?;
            let op = &mut self.facts.operations[index];
            op.opcode = Opcode::Constant;
            op.dest = ValueId::NONE;
            op.a = ValueId::NONE;
            op.b = ValueId::NONE;
            op.arguments = IdRange::default();
            op.flags = 0;
        }
        self.scratch.clear();
        self.world
            .reset(verify_expected && disabled.is_empty() && self.bundle.metadata.strict_events);
        let node = NodeId(
            self.bundle
                .metadata
                .mapping
                .compact_node(self.bundle.metadata.root)?,
        );
        evaluate(
            &self.facts,
            &self.bundle.graph,
            &self.types,
            &self.world,
            node,
            self.receiver,
            &self.arguments,
            &mut self.scratch,
            &mut self.evaluation,
        )?;
        self.world.finish()?;
        if self.scratch.owned_bytes() > self.scratch_limit {
            return Err(Error::Limit("replay scratch budget"));
        }
        let mut outcome = ReplayOutcome::from(
            &self.evaluation,
            &self.scratch.pool,
            Some(&self.bundle.metadata.mapping),
        )?;
        if self.bundle.metadata.version < VERSION {
            // Legacy recordings can still compare their original transfer
            // evidence, but cannot acquire a new closed-effects certificate.
            outcome.effects_open = true;
        }
        if verify_expected && outcome != self.bundle.metadata.expected {
            return Err(Error::Invalid("replay transfer outcome differs"));
        }
        Ok(outcome)
    }
}

#[derive(Clone, Debug)]
pub struct MinimizeOptions {
    pub max_evaluations: usize,
    pub scratch_bytes: usize,
}
impl Default for MinimizeOptions {
    fn default() -> Self {
        Self {
            max_evaluations: 256,
            scratch_bytes: 16 * 1024 * 1024,
        }
    }
}
#[derive(Clone, Debug)]
pub struct ReplayPredicate {
    pub issue: Option<IssueKind>,
    pub target: Option<NodeId>,
    pub min_calls: usize,
    pub min_reads: usize,
    pub preserve_exact_output: bool,
}
impl Default for ReplayPredicate {
    fn default() -> Self {
        Self {
            issue: None,
            target: None,
            min_calls: 0,
            min_reads: 0,
            preserve_exact_output: true,
        }
    }
}
impl ReplayPredicate {
    fn accepts(&self, outcome: &ReplayOutcome, expected: &ReplayOutcome) -> bool {
        (!self.preserve_exact_output || outcome == expected)
            && self
                .issue
                .is_none_or(|issue| outcome.issues.contains(&(issue as u32)))
            && outcome.calls.len() >= self.min_calls
            && outcome.reads.len() >= self.min_reads
            && self
                .target
                .is_none_or(|target| outcome.calls.iter().any(|call| call.target == target.0))
    }
}
#[derive(Debug, Serialize)]
pub struct MinimizedReplay {
    pub disabled_operations: Vec<u32>,
    pub evaluations: usize,
    pub active_operations: usize,
    pub outcome: ReplayOutcome,
}
impl ReplayBundle {
    pub fn minimize(
        &self,
        options: &MinimizeOptions,
        predicate: &ReplayPredicate,
    ) -> Result<MinimizedReplay, Error> {
        if options.max_evaluations == 0 {
            return Err(Error::Invalid("replay minimizer evaluations"));
        }
        let mut runtime = self.runtime(&ReplayOptions {
            scratch_bytes: options.scratch_bytes,
            verify_expected: true,
        })?;
        let baseline = runtime.run(&self.metadata.disabled, true)?;
        if !predicate.accepts(&baseline, &self.metadata.expected) {
            return Err(Error::Invalid("replay predicate does not hold"));
        }
        let (operations, total_operations) = self.reduction_operations()?;
        let mut disabled = self.metadata.disabled.clone();
        let mut outcome = baseline;
        let mut evaluations = 1;
        let mut chunk = operations.len().div_ceil(2).max(1);
        while evaluations < options.max_evaluations {
            let mut changed = false;
            for group in operations.chunks(chunk) {
                let mut candidate = disabled.clone();
                candidate.extend(group.iter().filter(|id| !disabled.contains(id)).copied());
                candidate.sort_unstable();
                candidate.dedup();
                if candidate == disabled {
                    continue;
                }
                evaluations += 1;
                if let Ok(result) = runtime.run(&candidate, false) {
                    if predicate.accepts(&result, &self.metadata.expected) {
                        disabled = candidate;
                        outcome = result;
                        changed = true;
                    }
                }
                if evaluations >= options.max_evaluations {
                    break;
                }
            }
            if chunk == 1 && !changed {
                break;
            }
            if !changed {
                chunk = chunk.div_ceil(2).max(1);
            }
        }
        Ok(MinimizedReplay {
            active_operations: total_operations
                - operations.iter().filter(|id| disabled.contains(id)).count(),
            disabled_operations: disabled,
            evaluations,
            outcome,
        })
    }
    pub fn write_minimized(
        &self,
        directory: &Path,
        reduction: &MinimizedReplay,
    ) -> Result<ReplayExportReport, Error> {
        let mut metadata = self.metadata.clone();
        metadata.disabled = reduction.disabled_operations.clone();
        metadata.expected = reduction.outcome.clone();
        metadata.strict_events = false;
        let recording_digest = digest(&serde_json::to_vec(&metadata).map_err(json_error)?);
        let reduced = Self {
            facts: clone_facts(&self.facts),
            graph: clone_graph(&self.graph),
            metadata,
            recording_digest,
        };
        reduced.replay(&ReplayOptions::default())?;
        reduced.write(directory)
    }
}
fn clone_graph(source: &ProgramGraph) -> ProgramGraph {
    ProgramGraph {
        identity: source.identity,
        facts_identity: source.facts_identity,
        runtime_identity: source.runtime_identity,
        nodes: source.nodes.clone(),
        edges: source.edges.clone(),
        forward_offsets: source.forward_offsets.clone(),
        forward_edges: source.forward_edges.clone(),
        reverse_offsets: source.reverse_offsets.clone(),
        reverse_edges: source.reverse_edges.clone(),
        symbol_nodes: source.symbol_nodes.clone(),
        issues: source.issues.clone(),
        diagnostic_bytes: source.diagnostic_bytes.clone(),
        diagnostics: source.diagnostics.clone(),
    }
}

/// Families include every admitted frame selected from one immutable session
/// view, including pending inputs. Each frame records one transfer evaluation.
pub const MAX_REPLAY_FAMILY_VARIANTS: usize = 64;
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ReplayFamilyScope {
    Method,
    ReceiverOf { context: u32, receiver: ReplayValue },
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ReplayFamilyInventory {
    pub node: u32,
    pub total_variants: usize,
    pub total_receivers: usize,
    pub selected_variants: usize,
    pub selected_evaluated: usize,
    pub scope: ReplayFamilyScope,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
struct FamilyEntry {
    context: u32,
    seal: String,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
struct FamilyManifest {
    version: u32,
    source_facts: String,
    source_graph: String,
    inventory: ReplayFamilyInventory,
    truncated: bool,
    entries: Vec<FamilyEntry>,
}
pub struct ReplayFamily {
    inventory: ReplayFamilyInventory,
    contexts: Vec<(ContextId, ReplayBundle)>,
}
#[derive(Clone, Debug, Serialize)]
pub struct ReplayFamilyReport {
    pub inventory: ReplayFamilyInventory,
    pub variants: usize,
    pub truncated: bool,
    pub owned_bytes: usize,
}
#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct ReplayFamilyOutcome {
    pub context: u32,
    pub outcome: ReplayOutcome,
}
#[derive(Debug, Serialize)]
pub struct ReplayFamilyComparison {
    pub context: u32,
    pub expected: ReplayOutcome,
    pub actual: ReplayOutcome,
    pub equal: bool,
}
fn family_shape(inventory: &ReplayFamilyInventory, count: usize) -> Result<(), Error> {
    if inventory.selected_variants > MAX_REPLAY_FAMILY_VARIANTS {
        return Err(Error::Limit(
            "replay family variants; select an explicit receiver family",
        ));
    }
    if count == 0
        || count != inventory.selected_variants
        || inventory.selected_evaluated > count
        || inventory.total_variants < count
        || inventory.total_receivers == 0
        || inventory.total_receivers > inventory.total_variants
    {
        return Err(Error::Invalid("replay incomplete family inventory"));
    }
    if matches!(inventory.scope, ReplayFamilyScope::Method) && count != inventory.total_variants {
        return Err(Error::Invalid("replay incomplete method family"));
    }
    Ok(())
}
impl ReplayFamily {
    pub fn from_contexts(
        inventory: ReplayFamilyInventory,
        mut contexts: Vec<(ContextId, ReplayBundle)>,
        limits: &ReplayLimits,
    ) -> Result<Self, Error> {
        family_shape(&inventory, contexts.len())?;
        contexts.sort_unstable_by_key(|(id, _)| *id);
        let first = &contexts[0].1.metadata;
        let mut responses = HashMap::new();
        let mut bytes = contexts.capacity() * std::mem::size_of::<(ContextId, ReplayBundle)>()
            + match &inventory.scope {
                ReplayFamilyScope::ReceiverOf { receiver, .. } => value_owned(receiver),
                _ => 0,
            };
        for (index, (id, bundle)) in contexts.iter().enumerate() {
            if id.is_none() || index > 0 && contexts[index - 1].0 == *id {
                return Err(Error::Invalid("replay duplicate family context"));
            }
            bundle.validate(limits)?;
            let meta = &bundle.metadata;
            if meta.root != inventory.node
                || meta.source_facts != first.source_facts
                || meta.source_graph != first.source_graph
                || meta.mapping.edges != first.mapping.edges
                || meta.max_members != first.max_members
                || meta.disabled != first.disabled
            {
                return Err(Error::Invalid(
                    "replay family program or candidate identity",
                ));
            }
            if let ReplayFamilyScope::ReceiverOf { receiver, .. } = &inventory.scope {
                if &meta.receiver != receiver {
                    return Err(Error::Invalid("replay receiver family identity"));
                }
            }
            // Distinct exact/overflow context namespaces can converge to the
            // same current frame after a monotone join. Retain both proofs.
            for event in &meta.events {
                if responses
                    .insert(&event.request, &event.response)
                    .is_some_and(|old| old != &event.response)
                {
                    return Err(Error::Invalid("replay inconsistent family world snapshot"));
                }
            }
            bytes = bytes
                .checked_add(bundle.report().owned_bytes)
                .ok_or(Error::Limit("replay family bytes"))?;
            if bytes > limits.max_bytes {
                return Err(Error::Limit("replay family bytes"));
            }
        }
        if let ReplayFamilyScope::ReceiverOf { context, .. } = inventory.scope {
            if !contexts.iter().any(|(id, _)| id.0 == context) {
                return Err(Error::Invalid("replay receiver anchor omitted"));
            }
        }
        if matches!(inventory.scope, ReplayFamilyScope::Method) {
            let mut receivers = std::collections::HashSet::new();
            for (_, bundle) in &contexts {
                receivers.insert(&bundle.metadata.receiver);
            }
            if receivers.len() != inventory.total_receivers {
                return Err(Error::Invalid("replay receiver inventory"));
            }
        }
        Ok(Self {
            inventory,
            contexts,
        })
    }
    pub fn compare(&self, options: &ReplayOptions) -> Result<Vec<ReplayFamilyComparison>, Error> {
        self.contexts
            .iter()
            .map(|(context, bundle)| {
                let compared = bundle.compare(options)?;
                Ok(ReplayFamilyComparison {
                    context: context.0,
                    expected: compared.expected,
                    actual: compared.actual,
                    equal: compared.equal,
                })
            })
            .collect()
    }
    pub fn inventory(&self) -> &ReplayFamilyInventory {
        &self.inventory
    }
    pub fn report(&self) -> ReplayFamilyReport {
        ReplayFamilyReport {
            inventory: self.inventory.clone(),
            variants: self.contexts.len(),
            truncated: false,
            owned_bytes: self.contexts.capacity()
                * std::mem::size_of::<(ContextId, ReplayBundle)>()
                + match &self.inventory.scope {
                    ReplayFamilyScope::ReceiverOf { receiver, .. } => value_owned(receiver),
                    _ => 0,
                }
                + self
                    .contexts
                    .iter()
                    .map(|(_, bundle)| bundle.report().owned_bytes)
                    .sum::<usize>(),
        }
    }
    pub fn write(&self, directory: &Path) -> Result<ReplayFamilyReport, Error> {
        family_shape(&self.inventory, self.contexts.len())?;
        std::fs::create_dir_all(directory)?;
        let first = &self.contexts[0].1.metadata;
        let mut manifest = FamilyManifest {
            version: VERSION,
            source_facts: first.source_facts.clone(),
            source_graph: first.source_graph.clone(),
            inventory: self.inventory.clone(),
            truncated: false,
            entries: Vec::with_capacity(self.contexts.len()),
        };
        for (id, bundle) in &self.contexts {
            let path = directory.join(format!("context-{}", id.0));
            bundle.write(&path)?;
            let seal = std::fs::read(path.join("recording.sha256"))?;
            manifest.entries.push(FamilyEntry {
                context: id.0,
                seal: ContentHash(
                    seal.try_into()
                        .map_err(|_| Error::Invalid("replay child seal"))?,
                )
                .to_string(),
            });
        }
        let bytes = serde_json::to_vec(&manifest).map_err(json_error)?;
        std::fs::write(directory.join("family.json"), &bytes)?;
        std::fs::write(directory.join("family.sha256"), digest(&bytes).0)?;
        Ok(self.report())
    }
    pub fn read(directory: &Path, limits: &ReplayLimits) -> Result<Self, Error> {
        if std::fs::metadata(directory.join("family.json"))?.len() > limits.max_bytes as u64 {
            return Err(Error::Limit("replay family manifest bytes"));
        }
        let bytes = std::fs::read(directory.join("family.json"))?;
        let seal = std::fs::read(directory.join("family.sha256"))?;
        if seal.len() != 32 || digest(&bytes).0.as_slice() != seal {
            return Err(Error::Invalid("replay family digest"));
        }
        let manifest: FamilyManifest = serde_json::from_slice(&bytes).map_err(json_error)?;
        family_shape(&manifest.inventory, manifest.entries.len())?;
        if manifest.version != VERSION || manifest.truncated {
            return Err(Error::Invalid("replay truncated family"));
        }
        let mut total = bytes.len() as u64 + 32;
        // Check the aggregate artifact size before retaining any child records.
        for entry in &manifest.entries {
            let path = directory.join(format!("context-{}", entry.context));
            for name in [
                "facts.bin",
                "graph.bin",
                "metadata.json",
                "recording.sha256",
            ] {
                total = total
                    .checked_add(std::fs::metadata(path.join(name))?.len())
                    .ok_or(Error::Limit("replay family bytes"))?;
            }
        }
        if total > limits.max_bytes as u64 {
            return Err(Error::Limit("replay family bytes"));
        }
        let mut contexts = Vec::with_capacity(manifest.entries.len());
        for entry in &manifest.entries {
            let bundle = ReplayBundle::read(
                &directory.join(format!("context-{}", entry.context)),
                limits,
            )?;
            if bundle.recording_digest.to_string() != entry.seal
                || bundle.metadata.source_facts != manifest.source_facts
                || bundle.metadata.source_graph != manifest.source_graph
            {
                return Err(Error::Invalid("replay family child identity"));
            }
            contexts.push((ContextId(entry.context), bundle));
        }
        Self::from_contexts(manifest.inventory, contexts, limits)
    }
    pub fn replay(&self, options: &ReplayOptions) -> Result<Vec<ReplayFamilyOutcome>, Error> {
        self.contexts
            .iter()
            .map(|(context, bundle)| {
                Ok(ReplayFamilyOutcome {
                    context: context.0,
                    outcome: bundle.replay(options)?,
                })
            })
            .collect()
    }
}

/// By default every frame keeps its complete observed output. Explicit scoped
/// predicates can preserve a counterexample in one frame or any family member;
/// every frame is still executed and every new world frontier rejects a mask.
#[derive(Clone, Debug)]
pub struct ReplayFamilyPredicate {
    pub condition: ReplayPredicate,
    pub context: Option<u32>,
    pub match_all: bool,
}
impl Default for ReplayFamilyPredicate {
    fn default() -> Self {
        Self {
            condition: ReplayPredicate::default(),
            context: None,
            match_all: true,
        }
    }
}
#[derive(Debug, Serialize)]
pub struct MinimizedFamilyReplay {
    pub disabled_operations: Vec<u32>,
    pub mask_evaluations: usize,
    pub transfer_evaluations: usize,
    pub active_operations: usize,
    pub outcomes: Vec<ReplayFamilyOutcome>,
}
impl ReplayFamily {
    fn accepts(&self, outcomes: &[ReplayFamilyOutcome], predicate: &ReplayFamilyPredicate) -> bool {
        if outcomes.len() != self.contexts.len() {
            return false;
        }
        let matches = |(entry, bundle): (&(ContextId, ReplayBundle), &ReplayFamilyOutcome)| {
            entry.0.0 == bundle.context
                && predicate
                    .condition
                    .accepts(&bundle.outcome, &entry.1.metadata.expected)
        };
        if let Some(context) = predicate.context {
            self.contexts
                .iter()
                .zip(outcomes)
                .find(|(entry, _)| entry.0.0 == context)
                .is_some_and(matches)
        } else if predicate.match_all {
            self.contexts.iter().zip(outcomes).all(matches)
        } else {
            self.contexts.iter().zip(outcomes).any(matches)
        }
    }
    pub fn minimize(
        &self,
        options: &MinimizeOptions,
        predicate: &ReplayFamilyPredicate,
    ) -> Result<MinimizedFamilyReplay, Error> {
        if options.max_evaluations == 0 {
            return Err(Error::Invalid("replay minimizer evaluations"));
        }
        let mut runtimes = Vec::with_capacity(self.contexts.len());
        let mut owned = 0usize;
        for (_, bundle) in &self.contexts {
            let runtime = bundle.runtime(&ReplayOptions {
                scratch_bytes: options.scratch_bytes,
                verify_expected: true,
            })?;
            owned = owned
                .checked_add(runtime.owned_bytes())
                .ok_or(Error::Limit("replay family workspace"))?;
            if owned > options.scratch_bytes {
                return Err(Error::Limit("replay family workspace"));
            }
            runtimes.push(runtime);
        }
        let run = |runtimes: &mut Vec<ReplayRuntime<'_>>,
                   disabled: &[u32],
                   verify: bool,
                   performed: &mut usize|
         -> Result<Vec<ReplayFamilyOutcome>, Error> {
            let mut outcomes = Vec::with_capacity(runtimes.len());
            let mut owned = 0usize;
            for (runtime, (context, _)) in runtimes.iter_mut().zip(&self.contexts) {
                *performed = performed
                    .checked_add(1)
                    .ok_or(Error::Limit("replay transfer evaluations"))?;
                outcomes.push(ReplayFamilyOutcome {
                    context: context.0,
                    outcome: runtime.run(disabled, verify)?,
                });
                owned = owned
                    .checked_add(runtime.owned_bytes())
                    .ok_or(Error::Limit("replay family workspace"))?;
                if owned > options.scratch_bytes {
                    return Err(Error::Limit("replay family workspace"));
                }
            }
            Ok(outcomes)
        };
        let first = &self.contexts[0].1;
        let mut disabled = first.metadata.disabled.clone();
        let mut transfer_evaluations = 0;
        let mut outcomes = run(&mut runtimes, &disabled, true, &mut transfer_evaluations)?;
        if !self.accepts(&outcomes, predicate) {
            return Err(Error::Invalid("replay family predicate does not hold"));
        }
        let (operations, total_operations) = first.reduction_operations()?;
        let mut evaluations = 1;
        let mut chunk = operations.len().div_ceil(2).max(1);
        while evaluations < options.max_evaluations {
            let mut changed = false;
            for group in operations.chunks(chunk) {
                let mut candidate = disabled.clone();
                candidate.extend(group.iter().filter(|id| !disabled.contains(id)).copied());
                candidate.sort_unstable();
                candidate.dedup();
                if candidate == disabled {
                    continue;
                }
                evaluations += 1;
                if let Ok(result) = run(&mut runtimes, &candidate, false, &mut transfer_evaluations)
                {
                    if self.accepts(&result, predicate) {
                        disabled = candidate;
                        outcomes = result;
                        changed = true;
                    }
                }
                if evaluations >= options.max_evaluations {
                    break;
                }
            }
            if chunk == 1 && !changed {
                break;
            }
            if !changed {
                chunk = chunk.div_ceil(2).max(1);
            }
        }
        Ok(MinimizedFamilyReplay {
            active_operations: total_operations
                - operations.iter().filter(|id| disabled.contains(id)).count(),
            disabled_operations: disabled,
            mask_evaluations: evaluations,
            transfer_evaluations,
            outcomes,
        })
    }
    pub fn write_minimized(
        &self,
        directory: &Path,
        reduction: &MinimizedFamilyReplay,
    ) -> Result<ReplayFamilyReport, Error> {
        if reduction.outcomes.len() != self.contexts.len() {
            return Err(Error::Invalid("replay incomplete family reduction"));
        }
        let mut contexts = Vec::with_capacity(self.contexts.len());
        for ((context, bundle), out) in self.contexts.iter().zip(&reduction.outcomes) {
            if context.0 != out.context {
                return Err(Error::Invalid("replay reduction context"));
            }
            let mut metadata = bundle.metadata.clone();
            metadata.disabled = reduction.disabled_operations.clone();
            metadata.expected = out.outcome.clone();
            metadata.strict_events = false;
            let recording_digest = digest(&serde_json::to_vec(&metadata).map_err(json_error)?);
            contexts.push((
                *context,
                ReplayBundle {
                    facts: clone_facts(&bundle.facts),
                    graph: clone_graph(&bundle.graph),
                    metadata,
                    recording_digest,
                },
            ));
        }
        let reduced =
            Self::from_contexts(self.inventory.clone(), contexts, &ReplayLimits::default())?;
        reduced.replay(&ReplayOptions::default())?;
        reduced.write(directory)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    // This adapter is intentionally confined to an ignored migration test. The
    // production reader admits only sealed v3 bundles.
    mod coarse_v2_migration {
        use super::*;

        const SOURCE_SYMBOLS: u32 = 1_098_659;
        const SOURCE_OPERATIONS: u32 = 2_658_360;
        const SOURCE_FACTS: &str =
            "737f0f4232074f05ba05af9f0e430f7334517e12da23849552d071528c1282b1";
        const SOURCE_GRAPH: &str =
            "0bf2d9be3f3f145824a6b59c39e47c57b2ba3eee306894449d023d3496f0389a";

        fn coarse_atoms(value: &serde_json::Value) -> Result<(), Error> {
            match value {
                serde_json::Value::Object(fields) => {
                    if fields.get("kind").and_then(|v| v.as_u64()) == Some(1)
                        && fields
                            .get("binding")
                            .and_then(|v| v.as_u64())
                            .is_some_and(|binding| binding != 0)
                    {
                        return Err(Error::Invalid(
                            "legacy migration cannot recover object origins",
                        ));
                    }
                    for value in fields.values() {
                        coarse_atoms(value)?;
                    }
                }
                serde_json::Value::Array(values) => {
                    for value in values {
                        coarse_atoms(value)?;
                    }
                }
                _ => (),
            }
            Ok(())
        }
        fn open_legacy(path: &Path) -> Result<(ReplayBundle, serde_json::Value), Error> {
            let directory = path.join("bundle");
            let portable: serde_json::Value =
                serde_json::from_slice(&std::fs::read(path.join("provenance.json"))?)
                    .map_err(json_error)?;
            for name in [
                "facts.bin",
                "graph.bin",
                "metadata.json",
                "recording.sha256",
            ] {
                let bytes = std::fs::read(directory.join(name))?;
                if portable["artifacts"][name]["sha256"].as_str()
                    != Some(&digest(&bytes).to_string())
                {
                    return Err(Error::Invalid("legacy replay provenance artifact digest"));
                }
            }
            let bytes = std::fs::read(directory.join("metadata.json"))?;
            let seal = std::fs::read(directory.join("recording.sha256"))?;
            if seal.len() != 32 || digest(&bytes).0.as_slice() != seal {
                return Err(Error::Invalid("legacy replay recording digest"));
            }
            let mut json: serde_json::Value = serde_json::from_slice(&bytes).map_err(json_error)?;
            if json["version"] != 2
                || json["source_facts"] != SOURCE_FACTS
                || json["source_graph"] != SOURCE_GRAPH
                || json["mapping"]["source_operations"] != SOURCE_OPERATIONS
                || portable["source_facts"] != SOURCE_FACTS
                || portable["source_graph"] != SOURCE_GRAPH
                || portable["scope"] != json["scope"]
            {
                return Err(Error::Invalid("legacy replay pinned input identity"));
            }
            coarse_atoms(&json)?;
            // The original enriched.bin section directory supplies these full
            // namespace counts. It has the pinned SOURCE_FACTS identity; the
            // compact v2 replay itself never recorded its source symbol count.
            json["mapping"]["source_symbols"] = SOURCE_SYMBOLS.into();
            json["mapping"]["heap_owners"] = serde_json::json!([]);
            json["expected"]["heap_owners"] = serde_json::json!([]);
            json["expected"]["field_reads"] = serde_json::json!([]);
            let metadata: Metadata = serde_json::from_value(json).map_err(json_error)?;
            if !metadata.disabled.is_empty() {
                return Err(Error::Invalid("legacy replay baseline is masked"));
            }
            let mut facts = selector_facts::codec::read(&directory.join("facts.bin"))?;
            let scope = ContentHash::from_hex(&metadata.scope)?;
            let mut graph = selector_graph::codec::read_bound(&directory.join("graph.bin"), scope)?;
            if metadata.artifacts.as_ref()
                != Some(&(facts.identity.to_string(), graph.identity.to_string()))
            {
                return Err(Error::Invalid("legacy replay artifact identity"));
            }
            facts.validate()?;
            graph.validate()?;
            facts.identity = scope;
            graph.identity = digest(
                &[
                    scope.0.as_slice(),
                    ContentHash::from_hex(SOURCE_GRAPH)?.0.as_slice(),
                ]
                .concat(),
            );
            let bundle = ReplayBundle {
                facts,
                graph,
                metadata,
                recording_digest: digest(&bytes),
            };
            let mut seed = Sha256::new();
            seed.update(b"selector-transfer-replay-scope/v2\0");
            if bundle.scope_digest_seed(seed)? != scope {
                return Err(Error::Invalid("legacy replay scope digest"));
            }
            Ok((bundle, portable))
        }

        struct CoarseWorld<'a> {
            replay: ReplayWorld<'a>,
            marker_responses: Mutex<Vec<ReplaySlot>>,
            unknown_markers: bool,
            new_summary_requests: Mutex<Vec<Request>>,
        }
        impl World for CoarseWorld<'_> {
            fn values(&self) -> &ValuePool {
                self.replay.values()
            }
            fn heap_owner(&self, _: HeapOwnerKey) -> Option<u32> {
                self.replay.state.lock().unwrap().fault =
                    Some("legacy migration invented an exact owner request");
                None
            }
            fn summary(
                &self,
                node: NodeId,
                receiver: Value,
                args: &[Value],
                local: &ValuePool,
                scratch: &mut Vec<Value>,
            ) -> SummaryRead {
                let map = &self.replay.bundle.metadata.mapping;
                let request = (|| {
                    Ok::<_, Error>(Request::Summary {
                        node: map.original_node(node)?,
                        receiver: ReplayValue::from(local, receiver, Some(map))?,
                        arguments: args
                            .iter()
                            .map(|value| ReplayValue::from(local, *value, Some(map)))
                            .collect::<Result<_, _>>()?,
                    })
                })();
                if let Ok(request) = request {
                    if !self
                        .replay
                        .bundle
                        .metadata
                        .events
                        .iter()
                        .any(|event| event.request == request)
                    {
                        self.new_summary_requests.lock().unwrap().push(request);
                    }
                }
                self.replay.summary(node, receiver, args, local, scratch)
            }
            fn slot(&self, slot: Slot) -> (Value, u64, bool) {
                if slot.kind != SlotKind::FieldMissing {
                    return self.replay.slot(slot);
                }
                let mut primary = slot;
                primary.kind = if slot.owner < self.replay.bundle.facts.operations.len() as u32 {
                    SlotKind::FieldAll
                } else {
                    SlotKind::Field
                };
                // Only an explicitly recorded absent primary can receive an
                // adapter marker. A StepLimit snapshot has no drained absence
                // certificate; its current in-flight marker remains bottom.
                let request =
                    ReplaySlot::from(primary, Some(&self.replay.bundle.metadata.mapping), &[])
                        .map(Request::Slot);
                let allowed = self.replay.find(request).is_some_and(|index| {
                    matches!(
                        self.replay.responses[index],
                        LoadedResponse::Slot(Value::EMPTY, 0, false)
                    )
                });
                if allowed {
                    self.marker_responses.lock().unwrap().push(
                        ReplaySlot::from(slot, Some(&self.replay.bundle.metadata.mapping), &[])
                            .unwrap(),
                    );
                } else {
                    self.replay.state.lock().unwrap().fault =
                        Some("legacy migration unrecorded marker primary");
                }
                (
                    Value {
                        unknown: if self.unknown_markers {
                            UNKNOWN_FIELD
                        } else {
                            0
                        },
                        ..Value::EMPTY
                    },
                    0,
                    false,
                )
            }
            fn capture(&self, binding: u32) -> Option<(Value, &[Value], u64)> {
                self.replay.capture(binding)
            }
            fn binding(
                &self,
                site: OperationId,
                receiver: Value,
                args: &[Value],
                local: &ValuePool,
                atoms: &mut Vec<Atom>,
                values: &mut Vec<Value>,
            ) -> Option<u32> {
                self.replay
                    .binding(site, receiver, args, local, atoms, values)
            }
        }

        fn run_adapter(
            legacy: &ReplayBundle,
            unknown_markers: bool,
        ) -> Result<(ReplayBundle, Vec<ReplaySlot>), (Error, Vec<Request>)> {
            let replay = ReplayWorld::new(legacy).map_err(|error| (error, Vec::new()))?;
            replay.reset(false);
            let mut world = CoarseWorld {
                replay,
                marker_responses: Mutex::new(Vec::new()),
                unknown_markers,
                new_summary_requests: Mutex::new(Vec::new()),
            };
            let captured = (|| {
                let receiver = legacy
                    .metadata
                    .receiver
                    .load(&mut world.replay.pool, &legacy.metadata.mapping)?;
                let arguments = legacy
                    .metadata
                    .arguments
                    .iter()
                    .map(|argument| argument.load(&mut world.replay.pool, &legacy.metadata.mapping))
                    .collect::<Result<Vec<_>, _>>()?;
                let root = NodeId(legacy.metadata.mapping.compact_node(legacy.metadata.root)?);
                let bundle = capture_context(
                    &legacy.facts,
                    &legacy.graph,
                    &TypeIndex::new(&legacy.facts),
                    &world,
                    root,
                    receiver,
                    &arguments,
                    &ReplayLimits::default(),
                )?;
                world.replay.finish()?;
                Ok(bundle)
            })();
            match captured {
                Ok(bundle) => Ok((bundle, world.marker_responses.into_inner().unwrap())),
                Err(error) => Err((error, world.new_summary_requests.into_inner().unwrap())),
            }
        }

        fn value(value: &mut ReplayValue, map: &Mapping) -> Result<(), Error> {
            for atom in &mut value.atoms {
                atom.site = map.original_op(OperationId(atom.site))?;
                atom.symbol = map.original_symbol(SymbolId(atom.symbol))?;
                if matches!(atom.kind, 1 | 4) && atom.binding != 0 {
                    return Err(Error::Invalid("legacy migration invented an object origin"));
                }
            }
            Ok(())
        }
        fn slot(slot: &mut ReplaySlot, map: &Mapping) -> Result<(), Error> {
            if slot.heap_owner.is_some() {
                return Err(Error::Invalid("legacy migration invented a heap partition"));
            }
            match slot.kind {
                1 | 8 => {
                    slot.owner = map.original_object_owner(slot.owner)?;
                    slot.member = map.original_symbol(SymbolId(slot.member))?;
                }
                6 | 7 => {
                    slot.owner = map.original_op(OperationId(slot.owner))?;
                    slot.member = map.original_symbol(SymbolId(slot.member))?;
                }
                5 => slot.owner = map.original_symbol(SymbolId(slot.owner))?,
                0 | 2 => (),
                _ => return Err(Error::Invalid("legacy migration slot namespace")),
            }
            Ok(())
        }
        fn original_ids(bundle: &mut ReplayBundle, legacy: &ReplayBundle) -> Result<(), Error> {
            let map = &legacy.metadata.mapping;
            let meta = &mut bundle.metadata;
            if !meta.mapping.heap_owners.is_empty() || !meta.expected.heap_owners.is_empty() {
                return Err(Error::Invalid("legacy migration invented owner metadata"));
            }
            meta.root = map.original_node(NodeId(meta.root))?;
            meta.source_facts = legacy.metadata.source_facts.clone();
            meta.source_graph = legacy.metadata.source_graph.clone();
            value(&mut meta.receiver, map)?;
            for argument in &mut meta.arguments {
                value(argument, map)?;
            }
            for event in &mut meta.events {
                match &mut event.request {
                    Request::Summary {
                        node,
                        receiver,
                        arguments,
                    } => {
                        *node = map.original_node(NodeId(*node))?;
                        value(receiver, map)?;
                        for argument in arguments {
                            value(argument, map)?;
                        }
                    }
                    Request::Slot(field) => slot(field, map)?,
                    Request::Binding {
                        site,
                        receiver,
                        arguments,
                    } => {
                        *site = map.original_op(OperationId(*site))?;
                        value(receiver, map)?;
                        for argument in arguments {
                            value(argument, map)?;
                        }
                    }
                    Request::Capture(_) => (),
                    Request::HeapOwner(_) => {
                        return Err(Error::Invalid("legacy migration invented owner event"));
                    }
                }
                match &mut event.response {
                    Response::Summary { value: v, .. } | Response::Slot { value: v, .. } => {
                        value(v, map)?
                    }
                    Response::Capture(Some((receiver, arguments, _))) => {
                        value(receiver, map)?;
                        for argument in arguments {
                            value(argument, map)?;
                        }
                    }
                    Response::HeapOwner(_) => {
                        return Err(Error::Invalid("legacy migration invented owner response"));
                    }
                    _ => (),
                }
            }
            let out = &mut meta.expected;
            value(&mut out.value, map)?;
            for call in &mut out.calls {
                call.target = map.original_node(NodeId(call.target))?;
                call.operation = map.original_op(OperationId(call.operation))?;
                call.edge = map.original_edge(EdgeId(call.edge))?;
                value(&mut call.receiver, map)?;
            }
            for argument in &mut out.arguments {
                value(argument, map)?;
            }
            for (field, v) in &mut out.stores {
                slot(field, map)?;
                value(v, map)?;
            }
            for (site, receiver, _) in &mut out.captures {
                *site = map.original_op(OperationId(*site))?;
                value(receiver, map)?;
            }
            for (field, _, _) in &mut out.reads {
                slot(field, map)?;
            }
            for field in &mut out.field_reads {
                slot(field, map)?;
            }
            for (node, operation, _, edge, receiver) in &mut out.edges {
                *node = map.original_node(NodeId(*node))?;
                *operation = map.original_op(OperationId(*operation))?;
                *edge = map.original_edge(EdgeId(*edge))?;
                *receiver = map.original_symbol(SymbolId(*receiver))?;
            }
            if let Some(issue) = &mut out.first_issue {
                issue.operation = map.original_op(OperationId(issue.operation))?;
            }
            for (symbol, parents) in &mut meta.parent_inventory {
                *symbol = map.original_symbol(SymbolId(*symbol))?;
                for parent in parents {
                    *parent = map.original_symbol(SymbolId(*parent))?;
                }
            }
            for authority in &mut meta.callback_authority {
                authority.node = map.original_node(NodeId(authority.node))?;
                for operation in &mut authority.operations {
                    *operation = map.original_op(OperationId(*operation))?;
                }
                for edge in &mut authority.structural_edges {
                    *edge = map.original_edge(EdgeId(*edge))?;
                }
            }
            for id in &mut meta.mapping.symbols {
                *id = map.original_symbol(SymbolId(*id))?;
            }
            for id in &mut meta.mapping.nodes {
                *id = map.original_node(NodeId(*id))?;
            }
            for id in &mut meta.mapping.operations {
                *id = map.original_op(OperationId(*id))?;
            }
            for id in &mut meta.mapping.edges {
                *id = map.original_edge(EdgeId(*id))?;
            }
            meta.mapping.source_operations = map.source_operations;
            meta.mapping.source_symbols = map.source_symbols;
            let scope = bundle.scope_digest()?;
            bundle.metadata.scope = scope.to_string();
            bundle.facts.identity = scope;
            bundle.graph.facts_identity = scope;
            bundle.graph.identity = digest(
                &[
                    scope.0.as_slice(),
                    ContentHash::from_hex(SOURCE_GRAPH)?.0.as_slice(),
                ]
                .concat(),
            );
            bundle.recording_digest =
                digest(&serde_json::to_vec(&bundle.metadata).map_err(json_error)?);
            bundle.replay(&ReplayOptions::default())?;
            Ok(())
        }

        #[test]
        #[ignore = "explicit coarse v2 input adapter; set SELECTOR_REPLAY_V3_OUTPUT under /private/tmp"]
        fn recapture_genuine_clue_with_current_kernel_and_coarse_adapter() -> Result<(), Error> {
            let output = std::path::PathBuf::from(
                std::env::var("SELECTOR_REPLAY_V3_OUTPUT")
                    .map_err(|_| Error::Invalid("SELECTOR_REPLAY_V3_OUTPUT is required"))?,
            );
            if !output.is_absolute() || !output.starts_with("/private/tmp") || output.exists() {
                return Err(Error::Invalid(
                    "migration output must be a new directory under /private/tmp",
                ));
            }
            let path = Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../fixtures/transfer-replay/pr7743-clue/history/v2");
            let (mut legacy, portable) = open_legacy(&path)?;
            let legacy_scope = legacy.metadata.scope.clone();
            let legacy_seal = legacy.recording_digest.to_string();
            let mut allocated_fields_mapped = 0usize;
            for event in &mut legacy.metadata.events {
                if let Request::Slot(field) = &mut event.request {
                    if field.kind == 1 && field.owner < legacy.metadata.mapping.source_operations {
                        let operation = legacy.metadata.mapping.compact_op(field.owner)?;
                        if legacy.facts.operations[operation as usize].opcode != Opcode::Allocate {
                            return Err(Error::Invalid("legacy field owner is not an allocation"));
                        }
                        field.kind = 7;
                        allocated_fields_mapped += 1;
                    }
                }
            }
            let unknown_extension = match run_adapter(&legacy, true) {
                Err((error, requests)) => serde_json::json!({
                    "status": "rejected", "policy": "UNKNOWN_FIELD/version0/presentfalse",
                    "error": error.to_string(), "new_summary_requests": requests,
                    "interpretation": "These summary frontiers have no recorded result; no extended transcript was published.",
                }),
                Ok(_) => {
                    serde_json::json!({ "status": "unselected", "policy": "UNKNOWN_FIELD/version0/presentfalse" })
                }
            };
            let (mut bundle, markers) =
                run_adapter(&legacy, false).map_err(|(error, requests)| {
                    Error::Message(format!(
                        "pending-bottom adapter failed: {error}; new summary requests: {requests:?}"
                    ))
                })?;
            original_ids(&mut bundle, &legacy)?;
            let frozen: serde_json::Value =
                serde_json::from_slice(&std::fs::read(path.join("reduction.json"))?)
                    .map_err(json_error)?;
            let predicate = ReplayPredicate {
                issue: Some(IssueKind::decode(
                    frozen["issue"]
                        .as_u64()
                        .ok_or(Error::Invalid("legacy reduction issue"))?
                        as u32,
                )?),
                target: Some(NodeId(
                    frozen["callback_target"]
                        .as_u64()
                        .ok_or(Error::Invalid("legacy reduction target"))?
                        as u32,
                )),
                min_calls: frozen["min_calls"]
                    .as_u64()
                    .ok_or(Error::Invalid("legacy reduction calls"))?
                    as usize,
                min_reads: frozen["min_reads"]
                    .as_u64()
                    .ok_or(Error::Invalid("legacy reduction reads"))?
                    as usize,
                preserve_exact_output: false,
            };
            let reduction = bundle.minimize(&MinimizeOptions::default(), &predicate)?;
            bundle.write(&output.join("bundle"))?;
            bundle.write_minimized(&output.join("minimized"), &reduction)?;
            let reduced = serde_json::json!({
                "root": bundle.metadata.root, "callback_target": predicate.target.unwrap().0,
                "callback_binding": frozen["callback_binding"], "issue": predicate.issue.unwrap() as u32,
                "min_calls": predicate.min_calls, "min_reads": predicate.min_reads,
                "disabled_operations": reduction.disabled_operations, "evaluations": reduction.evaluations,
                "active_operations": reduction.active_operations, "outcome": reduction.outcome,
            });
            std::fs::write(
                output.join("reduction.json"),
                serde_json::to_vec_pretty(&reduced).map_err(json_error)?,
            )?;
            let receipt = serde_json::json!({
                "schema": "selector-replay-coarse-current-kernel-migration/v1",
                "interpretation": "Current transfer re-evaluation of an explicitly adapted coarse v2 input; not the historical same proof, finalized state, resumed solver, or fixed point.",
                "source_facts": SOURCE_FACTS, "source_graph": SOURCE_GRAPH,
                "source_symbols": SOURCE_SYMBOLS, "source_operations": SOURCE_OPERATIONS,
                "namespace_evidence": "Full counts read from original enriched.bin directory sections 5/9 with the pinned source facts identity.",
                "legacy_scope": legacy_scope, "legacy_recording_sha256": legacy_seal,
                "legacy_provenance": portable,
                "legacy_allocated_field_requests_mapped_to_coarse_all": allocated_fields_mapped,
                "publication_status": "Adapter experiment only; independent actual ReadWorld control must substantiate marker responses before fixture publication.",
                "object_origins": "All historical Object.binding=0 remain coarse; no root origin or heap partition reconstructed.",
                "marker_policy": "Adapter-provided bottom/version0/presentfalse for recorded bottom/version0/presentfalse primary reads only; current unfinalized in-flight view of a StepLimit snapshot, not a finalized absence certificate or exact historical v3 marker state.",
                "rejected_unknown_extension": unknown_extension,
                "adapter_marker_response_count": markers.len(), "adapter_marker_responses": markers,
                "current_scope": bundle.metadata.scope, "current_outcome": bundle.metadata.expected,
                "report": bundle.report(),
            });
            std::fs::write(
                output.join("migration.json"),
                serde_json::to_vec_pretty(&receipt).map_err(json_error)?,
            )?;
            eprintln!(
                "coarse v2 current-kernel re-evaluation written to {}",
                output.display()
            );
            Ok(())
        }
    }

    struct FrozenWorld {
        pool: ValuePool,
        receiver: Value,
        argument: Value,
        captures: Vec<Value>,
        visits: AtomicUsize,
    }
    impl World for FrozenWorld {
        fn values(&self) -> &ValuePool {
            &self.pool
        }
        fn summary(
            &self,
            node: NodeId,
            _: Value,
            _: &[Value],
            _: &ValuePool,
            _: &mut Vec<Value>,
        ) -> SummaryRead {
            self.visits.fetch_add(1, Ordering::Relaxed);
            SummaryRead {
                context: Some(ContextId(100 + node.0)),
                value: if node == NodeId(4) {
                    Value::TOP
                } else {
                    Value::EMPTY
                },
                version: 11,
                present: true,
            }
        }
        fn slot(&self, _: Slot) -> (Value, u64, bool) {
            self.visits.fetch_add(1, Ordering::Relaxed);
            (Value::EMPTY, 0, false)
        }
        fn capture(&self, binding: u32) -> Option<(Value, &[Value], u64)> {
            self.visits.fetch_add(1, Ordering::Relaxed);
            (binding == 17).then_some((self.receiver, self.captures.as_slice(), 9))
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
            self.visits.fetch_add(1, Ordering::Relaxed);
            Some(17)
        }
    }
    fn fixture() -> (FactSnapshot, ProgramGraph, FrozenWorld) {
        let mut b = FactBuilder::new();
        let path = b.intern("Replay.scala").unwrap();
        b.facts.files.push(FileRecord {
            path,
            source: StrId::NONE,
            revision: StrId::NONE,
            context: StrId::NONE,
            source_hash: ContentHash([1; 32]),
            flags: 0,
        });
        for name in [
            "Unused#",
            "Root#",
            "Base#",
            "Left#",
            "Right#",
            "Root#main().",
            "Left#run().",
            "Right#run().",
            "Root#callback().",
            "Base#field.",
            "Root#provider().",
            "Root#callback().(x)",
        ] {
            b.ensure_symbol(name, FileId(0)).unwrap();
        }
        for i in 0..5 {
            b.facts.symbols[i].kind = 13;
            b.facts.symbols[i].flags = SYMBOL_DEFINED | SYMBOL_SCALA_PARENTS_COMPLETE;
        }
        for (member, owner) in [(5, 1), (6, 3), (7, 4), (8, 1), (9, 2), (10, 1), (11, 8)] {
            b.facts.symbols[member].kind = 3;
            b.facts.symbols[member].owner = SymbolId(owner);
            b.facts.symbols[member].flags = SYMBOL_DEFINED;
        }
        for child in [1, 3, 4] {
            b.facts.relations.push(RelationRecord {
                source: SymbolId(child),
                target: SymbolId(2),
                kind: RelationKind::Parent,
                file: FileId::NONE,
            });
        }
        b.facts.operands = vec![ValueId(1)];
        let op = |opcode, target, dest, a| OperationRecord {
            body: BodyId(0),
            opcode,
            target: SymbolId(target),
            dest: ValueId(dest),
            a: ValueId(a),
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span::default(),
            flags: 0,
        };
        let none = u32::MAX;
        b.facts.operations = vec![
            op(Opcode::Parameter, none, 1, none),
            op(Opcode::LoadField, 9, 2, 0),
            op(Opcode::VirtualCall, 6, 3, 0),
            op(Opcode::BindCallback, 8, 4, 0),
            op(Opcode::InvokeCallback, none, 5, 4),
            op(Opcode::InvokeCallback, none, 6, 1),
            op(Opcode::Call, 10, 7, none),
            op(Opcode::Unknown, none, 8, none),
            op(Opcode::Return, none, none, 7),
            op(Opcode::Constant, none, 9, none),
        ];
        b.facts.bodies.push(BodyRecord {
            symbol: SymbolId(5),
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange { start: 0, len: 10 },
            parameters: IdRange { start: 0, len: 1 },
            body_hash: ContentHash([2; 32]),
            flags: 0,
        });
        b.facts.operations.push(OperationRecord {
            body: BodyId(1),
            ..op(Opcode::Parameter, 11, 1, none)
        });
        b.facts.bodies.push(BodyRecord {
            symbol: SymbolId(8),
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange { start: 10, len: 1 },
            parameters: IdRange { start: 0, len: 1 },
            body_hash: ContentHash([3; 32]),
            flags: 0,
        });
        // A disconnected body makes global operation and symbol namespaces
        // differ from the compact replay namespaces.
        b.facts.operations.push(OperationRecord {
            body: BodyId(2),
            ..op(Opcode::Constant, none, 1, none)
        });
        b.facts.bodies.push(BodyRecord {
            symbol: SymbolId(0),
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange { start: 11, len: 1 },
            parameters: IdRange::default(),
            body_hash: ContentHash([8; 32]),
            flags: 0,
        });
        b.facts.bound_classes.push(SymbolId(2));
        b.facts.result_bounds.push(ResultBoundRecord {
            symbol: SymbolId(10),
            operation: OperationId::NONE,
            classes: IdRange { start: 0, len: 1 },
        });
        let mut facts = b.finish().unwrap();
        facts.identity = ContentHash([4; 32]);
        let mut graph = ProgramGraph {
            identity: ContentHash([5; 32]),
            facts_identity: facts.identity,
            symbol_nodes: vec![NodeId::NONE; 12],
            ..Default::default()
        };
        for (index, symbol) in [5, 6, 7, 8, 10].into_iter().enumerate() {
            graph.nodes.push(NodeRecord {
                symbol: SymbolId(symbol),
                file: FileId(0),
                body: match index {
                    0 => BodyId(0),
                    3 => BodyId(1),
                    _ => BodyId::NONE,
                },
                flags: 0,
            });
            graph.symbol_nodes[symbol as usize] = NodeId(index as u32);
        }
        for (target, operation, receiver, kind) in [
            (1, 2, 3, EdgeKind::VirtualCall),
            (2, 2, 4, EdgeKind::VirtualCall),
            (3, 4, none, EdgeKind::Callback),
            (3, 5, none, EdgeKind::Callback),
            (4, 6, none, EdgeKind::Call),
            (2, 9, 4, EdgeKind::Compile),
        ] {
            graph.edges.push(EdgeRecord {
                source: NodeId(0),
                target: NodeId(target),
                kind,
                occurrence: OccurrenceId::NONE,
                operation: OperationId(operation),
                receiver: SymbolId(receiver),
                flags: 0,
            });
        }
        graph.index().unwrap();
        graph.validate().unwrap();
        let mut pool = ValuePool::new(64);
        let receiver = pool
            .singleton(Atom {
                kind: AtomKind::Object,
                site: OperationId::NONE,
                symbol: SymbolId(3),
                binding: 0,
            })
            .unwrap();
        let argument = pool
            .singleton(Atom {
                kind: AtomKind::Callback,
                site: OperationId::NONE,
                symbol: SymbolId(8),
                binding: 17,
            })
            .unwrap();
        let world = FrozenWorld {
            pool,
            receiver,
            argument,
            captures: vec![Value::EMPTY],
            visits: AtomicUsize::new(0),
        };
        (facts, graph, world)
    }
    fn captured() -> ReplayBundle {
        let (facts, graph, world) = fixture();
        capture_context(
            &facts,
            &graph,
            &TypeIndex::new(&facts),
            &world,
            NodeId(0),
            world.receiver,
            &[world.argument],
            &ReplayLimits::default(),
        )
        .unwrap()
    }
    fn reseal(bundle: &mut ReplayBundle) {
        let scope = bundle.scope_digest().unwrap();
        bundle.metadata.scope = scope.to_string();
        bundle.facts.identity = scope;
        bundle.graph.facts_identity = scope;
        let source = ContentHash::from_hex(&bundle.metadata.source_graph).unwrap();
        bundle.graph.identity = digest(&[scope.0.as_slice(), source.0.as_slice()].concat());
        bundle.recording_digest = digest(&serde_json::to_vec(&bundle.metadata).unwrap());
    }

    struct HeapWorld {
        pool: ValuePool,
        owners: HeapOwners,
        missing: bool,
    }
    impl World for HeapWorld {
        fn values(&self) -> &ValuePool {
            &self.pool
        }
        fn heap_owner(&self, key: HeapOwnerKey) -> Option<u32> {
            self.owners.lookup(key)
        }
        fn summary(
            &self,
            _: NodeId,
            _: Value,
            _: &[Value],
            _: &ValuePool,
            _: &mut Vec<Value>,
        ) -> SummaryRead {
            panic!("heap replay fixture has no calls")
        }
        fn slot(&self, slot: Slot) -> (Value, u64, bool) {
            if self.missing && slot.kind == SlotKind::FieldMissing {
                (
                    Value {
                        unknown: UNKNOWN_FIELD,
                        ..Value::EMPTY
                    },
                    7,
                    true,
                )
            } else {
                (Value::EMPTY, 0, false)
            }
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
    fn heap_fixture(
        published: bool,
        coarse: bool,
    ) -> (FactSnapshot, ProgramGraph, HeapWorld, Value, Value) {
        let (mut facts, mut graph, old) = fixture();
        graph.edges.clear();
        graph.index().unwrap();
        let make = |opcode, target, dest, a, b| OperationRecord {
            body: BodyId(0),
            opcode,
            target: SymbolId(target),
            dest: ValueId(dest),
            a: ValueId(a),
            b: ValueId(b),
            arguments: IdRange::default(),
            span: Span::default(),
            flags: 0,
        };
        let none = u32::MAX;
        facts.operations[..10].copy_from_slice(&[
            make(Opcode::Parameter, none, 1, none, none),
            make(Opcode::Allocate, 3, 2, none, none),
            make(Opcode::StoreField, 9, none, 2, 1),
            make(Opcode::LoadField, 9, 3, 2, none),
            make(Opcode::Allocate, 3, 4, none, none),
            make(Opcode::StoreField, 9, none, 4, 1),
            make(Opcode::LoadField, 9, 5, 4, none),
            make(Opcode::Return, none, none, 5, none),
            make(Opcode::Constant, none, 6, none, none),
            make(Opcode::Constant, none, 7, none, none),
        ]);
        let mut pool = old.pool;
        let receiver = if coarse {
            facts.operations[11].opcode = Opcode::Allocate;
            facts.operations[11].target = SymbolId(3);
            pool.intern(
                &[
                    Atom {
                        kind: AtomKind::Object,
                        site: OperationId::NONE,
                        symbol: SymbolId(3),
                        binding: 0,
                    },
                    Atom {
                        kind: AtomKind::Object,
                        site: OperationId(11),
                        symbol: SymbolId(3),
                        binding: 0,
                    },
                ],
                0,
            )
            .unwrap()
        } else {
            old.receiver
        };
        let argument = pool
            .singleton(Atom {
                kind: AtomKind::Object,
                site: OperationId::NONE,
                symbol: SymbolId(4),
                binding: 0,
            })
            .unwrap();
        let mut owners = HeapOwners::new(facts.operations.len(), facts.symbols.len()).unwrap();
        if published {
            // An unrelated published partition proves compact replay IDs do
            // not depend on retaining the full query owner table.
            owners
                .intern(HeapOwnerKey {
                    site: OperationId(11),
                    root: SymbolId(4),
                })
                .unwrap();
            for site in [1, 4] {
                owners
                    .intern(HeapOwnerKey {
                        site: OperationId(site),
                        root: SymbolId(3),
                    })
                    .unwrap();
            }
        }
        (
            facts,
            graph,
            HeapWorld {
                pool,
                owners,
                missing: true,
            },
            receiver,
            argument,
        )
    }
    fn heap_bundle(published: bool, coarse: bool) -> ReplayBundle {
        let (facts, graph, world, receiver, argument) = heap_fixture(published, coarse);
        capture_context(
            &facts,
            &graph,
            &TypeIndex::new(&facts),
            &world,
            NodeId(0),
            receiver,
            &[argument],
            &ReplayLimits::default(),
        )
        .unwrap()
    }

    #[test]
    fn legacy_v3_rejects_carrier_values_even_in_recorded_world_responses() {
        for world_response in [false, true] {
            let mut bundle = heap_bundle(false, false);
            bundle.metadata.version = 3;
            bundle.metadata.expected.effects_open = true;
            let carrier = ReplayAtom {
                kind: 4,
                site: u32::MAX,
                symbol: u32::MAX,
                binding: 0,
            };
            if world_response {
                let value = bundle
                    .metadata
                    .events
                    .iter_mut()
                    .find_map(|event| match &mut event.response {
                        Response::Slot { value, .. } => Some(value),
                        _ => None,
                    })
                    .unwrap();
                value.atoms.push(carrier);
            } else {
                bundle.metadata.receiver.atoms.push(carrier);
            }
            assert!(
                bundle
                    .validate(&ReplayLimits::default())
                    .unwrap_err()
                    .to_string()
                    .contains("legacy replay container atom")
            );
        }
    }
    #[test]
    fn legacy_v3_rejects_sequence_ir_without_relabeling_historical_recordings() {
        for opcode in [Opcode::PackSequence, Opcode::ReadElements] {
            let mut bundle = heap_bundle(false, false);
            bundle.metadata.version = 3;
            bundle.metadata.expected.effects_open = true;
            bundle.facts.operations[0].opcode = opcode;
            assert!(
                bundle
                    .validate(&ReplayLimits::default())
                    .unwrap_err()
                    .to_string()
                    .contains("legacy replay sequence operation")
            );
        }
    }
    #[test]
    fn allocated_heap_misses_roundtrip_and_masked_replays_resolve_current_local_drafts() {
        let bundle = heap_bundle(false, false);
        assert_eq!(bundle.metadata.version, VERSION);
        assert!(
            bundle
                .metadata
                .mapping
                .heap_owners
                .iter()
                .all(|entry| entry.owner.is_none())
        );
        let baseline = bundle.replay(&ReplayOptions::default()).unwrap();
        assert_eq!(baseline.stores.len(), 2);
        assert_eq!(
            baseline.stores[0].0.heap_owner,
            Some(ReplayHeapKey { site: 1, root: 3 })
        );
        assert_eq!(
            baseline.stores[1].0.heap_owner,
            Some(ReplayHeapKey { site: 4, root: 3 })
        );
        assert!(baseline.value.unknown & UNKNOWN_FIELD != 0);
        assert!(
            baseline
                .reads
                .iter()
                .any(|(slot, version, present)| slot.kind == 8 && *version == 7 && *present)
        );
        assert!(
            baseline
                .reads
                .iter()
                .any(|(slot, _, present)| slot.kind == 6 && !present)
        );
        // Newly allocated field owners retain the original receiver class even
        // though that class has a different compact identity.
        assert_ne!(bundle.metadata.mapping.compact_symbol(3).unwrap(), 3);
        let mut runtime = bundle.runtime(&ReplayOptions::default()).unwrap();
        runtime.run(&[], true).unwrap();
        let bytes = runtime.owned_bytes();
        let reduced = runtime.run(&[1, 2, 3], false).unwrap();
        assert_eq!(reduced.stores.len(), 1);
        assert_eq!(
            reduced.stores[0].0.heap_owner,
            Some(ReplayHeapKey { site: 4, root: 3 })
        );
        for _ in 0..4 {
            assert_eq!(runtime.run(&[], true).unwrap(), baseline);
        }
        assert_eq!(runtime.owned_bytes(), bytes);
        let dir = tempfile::tempdir().unwrap();
        bundle.write(dir.path()).unwrap();
        let loaded = ReplayBundle::read(dir.path(), &ReplayLimits::default()).unwrap();
        assert_eq!(loaded.replay(&ReplayOptions::default()).unwrap(), baseline);
        assert!(
            loaded
                .metadata
                .expected
                .reads
                .iter()
                .all(|(slot, _, _)| slot.owner < LOCAL_HEAP_OWNER || slot.owner == u32::MAX)
        );
    }

    #[test]
    fn published_exact_and_coarse_allocation_alias_channels_survive_compaction() {
        let bundle = heap_bundle(true, true);
        let baseline = bundle.replay(&ReplayOptions::default()).unwrap();
        assert!(
            bundle
                .metadata
                .mapping
                .heap_owners
                .iter()
                .all(|entry| entry.owner.is_some())
        );
        assert_eq!(
            baseline
                .stores
                .iter()
                .filter(|(slot, _)| slot.heap_owner.is_some())
                .count(),
            2
        );
        assert_eq!(
            baseline
                .stores
                .iter()
                .filter(|(slot, _)| slot.kind == 6)
                .count(),
            2
        );
        for kind in [1, 6, 7, 8] {
            assert!(baseline.reads.iter().any(|(slot, _, _)| slot.kind == kind));
        }
        let dir = tempfile::tempdir().unwrap();
        bundle.write(dir.path()).unwrap();
        let loaded = ReplayBundle::read(dir.path(), &ReplayLimits::default()).unwrap();
        assert_eq!(loaded.replay(&ReplayOptions::default()).unwrap(), baseline);
    }

    #[test]
    fn allocated_object_root_origins_in_frames_and_outputs_are_symbol_references() {
        let (mut facts, graph, mut world, _, argument) = heap_fixture(false, false);
        facts.operations[11].opcode = Opcode::Allocate;
        facts.operations[11].target = SymbolId(3);
        facts.operations[7].a = ValueId(4);
        // A different receiver root reaches this allocation through a receiver
        // whose runtime class is Left. Only the finite original root is kept.
        facts.symbols[11].kind = 13;
        facts.symbols[11].owner = SymbolId::NONE;
        let receiver = world
            .pool
            .singleton(Atom {
                kind: AtomKind::Object,
                site: OperationId(11),
                symbol: SymbolId(3),
                binding: root_binding(SymbolId(11)).unwrap(),
            })
            .unwrap();
        let bundle = capture_context(
            &facts,
            &graph,
            &TypeIndex::new(&facts),
            &world,
            NodeId(0),
            receiver,
            &[argument],
            &ReplayLimits::default(),
        )
        .unwrap();
        assert_ne!(bundle.metadata.mapping.compact_symbol(11).unwrap(), 11);
        let outcome = bundle.replay(&ReplayOptions::default()).unwrap();
        assert_eq!(
            outcome.value.atoms,
            vec![ReplayAtom {
                kind: 1,
                site: 4,
                symbol: 3,
                binding: 12
            }]
        );
        assert!(
            outcome
                .stores
                .iter()
                .all(|(slot, _)| slot.heap_owner.unwrap().root == 11)
        );
        let dir = tempfile::tempdir().unwrap();
        bundle.write(dir.path()).unwrap();
        assert_eq!(
            ReplayBundle::read(dir.path(), &ReplayLimits::default())
                .unwrap()
                .replay(&ReplayOptions::default())
                .unwrap(),
            outcome
        );
    }

    #[test]
    fn heap_replay_families_keep_same_class_receivers_with_distinct_allocation_origins() {
        let (mut facts, graph, mut world, receiver, argument) = heap_fixture(false, false);
        facts.operations[11].opcode = Opcode::Allocate;
        facts.operations[11].target = SymbolId(3);
        let origins = [
            world
                .pool
                .singleton(Atom {
                    kind: AtomKind::Object,
                    site: OperationId(11),
                    symbol: SymbolId(3),
                    binding: 4,
                })
                .unwrap(),
            world
                .pool
                .singleton(Atom {
                    kind: AtomKind::Object,
                    site: OperationId(11),
                    symbol: SymbolId(3),
                    binding: 5,
                })
                .unwrap(),
        ];
        assert_ne!(receiver, origins[0]);
        let types = TypeIndex::new(&facts);
        let contexts = origins
            .into_iter()
            .enumerate()
            .map(|(index, receiver)| {
                (
                    ContextId(index as u32 + 10),
                    capture_context(
                        &facts,
                        &graph,
                        &types,
                        &world,
                        NodeId(0),
                        receiver,
                        &[argument],
                        &ReplayLimits::default(),
                    )
                    .unwrap(),
                )
            })
            .collect();
        let family = ReplayFamily::from_contexts(
            ReplayFamilyInventory {
                node: 0,
                total_variants: 2,
                total_receivers: 2,
                selected_variants: 2,
                selected_evaluated: 2,
                scope: ReplayFamilyScope::Method,
            },
            contexts,
            &ReplayLimits::default(),
        )
        .unwrap();
        let outcomes = family.replay(&ReplayOptions::default()).unwrap();
        assert_eq!(outcomes[0].outcome.stores[0].0.heap_owner.unwrap().root, 3);
        assert_eq!(outcomes[1].outcome.stores[0].0.heap_owner.unwrap().root, 4);
        let dir = tempfile::tempdir().unwrap();
        family.write(dir.path()).unwrap();
        assert_eq!(
            ReplayFamily::read(dir.path(), &ReplayLimits::default())
                .unwrap()
                .replay(&ReplayOptions::default())
                .unwrap(),
            outcomes
        );
    }

    #[test]
    fn heap_replay_rejects_local_tags_invalid_owners_origins_and_cross_scope_keys() {
        for case in 0..5 {
            let mut bundle = heap_bundle(true, false);
            match case {
                0 => bundle.metadata.mapping.heap_owners[0].owner = Some(LOCAL_HEAP_OWNER),
                1 => {
                    let id = bundle.metadata.mapping.heap_owners[0].owner;
                    bundle.metadata.mapping.heap_owners[1].owner = id;
                }
                2 => {
                    let slot = &mut bundle.metadata.expected.stores[0].0;
                    slot.heap_owner = None;
                    slot.owner = LOCAL_HEAP_OWNER;
                }
                3 => {
                    bundle.metadata.receiver.atoms[0].binding =
                        bundle.metadata.mapping.source_symbols + 1
                }
                _ => {
                    bundle.metadata.expected.stores[0]
                        .0
                        .heap_owner
                        .as_mut()
                        .unwrap()
                        .root = u32::MAX - 1
                }
            }
            bundle.recording_digest = digest(&serde_json::to_vec(&bundle.metadata).unwrap());
            assert!(
                bundle.replay(&ReplayOptions::default()).is_err(),
                "malformed heap case {case}"
            );
        }
        let mut bundle = heap_bundle(false, false);
        let event = bundle
            .metadata
            .events
            .iter_mut()
            .find(|event| matches!(event.request, Request::HeapOwner(_)))
            .unwrap();
        event.response = Response::HeapOwner(Some(LOCAL_HEAP_OWNER));
        bundle.recording_digest = digest(&serde_json::to_vec(&bundle.metadata).unwrap());
        assert!(bundle.replay(&ReplayOptions::default()).is_err());
    }

    #[test]
    fn callback_projection_recomputes_full_callee_recipes_and_structural_guards() {
        for case in 0..4 {
            let (mut facts, mut graph, world) = fixture();
            if case <= 2 {
                let opcode = match case {
                    0 => Opcode::Return,
                    1 => Opcode::Unknown,
                    _ => Opcode::Constant,
                };
                facts.operations.insert(
                    11,
                    OperationRecord {
                        body: BodyId(1),
                        opcode,
                        target: SymbolId::NONE,
                        dest: ValueId::NONE,
                        a: if case == 0 { ValueId(0) } else { ValueId::NONE },
                        b: ValueId::NONE,
                        arguments: IdRange::default(),
                        span: Span::default(),
                        flags: 0,
                    },
                );
                facts.bodies[1].operations.len = 2;
                facts.bodies[2].operations.start += 1;
            } else {
                graph.edges.push(EdgeRecord {
                    source: NodeId(3),
                    target: NodeId(3),
                    kind: EdgeKind::Guard,
                    occurrence: OccurrenceId::NONE,
                    operation: OperationId::NONE,
                    receiver: SymbolId::NONE,
                    flags: 0,
                });
                graph.index().unwrap();
            }
            let types = TypeIndex::new(&facts);
            assert_eq!(
                types.callback_receiver_unused(&graph, SymbolId(8)),
                case == 2
            );
            let mut bundle = capture_context(
                &facts,
                &graph,
                &types,
                &world,
                NodeId(0),
                world.receiver,
                &[world.argument],
                &ReplayLimits::default(),
            )
            .unwrap();
            assert_eq!(bundle.metadata.callback_authority.len(), 1);
            assert_eq!(bundle.metadata.callback_authority[0].node, 3);
            assert_eq!(
                bundle.metadata.callback_authority[0].operations.len(),
                if case <= 2 { 2 } else { 1 }
            );
            let compact = SymbolId(bundle.metadata.mapping.compact_symbol(8).unwrap());
            assert_eq!(
                TypeIndex::new(&bundle.facts).callback_receiver_unused(&bundle.graph, compact),
                case == 2
            );
            let expected = bundle.replay(&ReplayOptions::default()).unwrap();
            if case <= 2 {
                assert!(
                    bundle
                        .runtime(&ReplayOptions::default())
                        .unwrap()
                        .run(&[11], false)
                        .is_err(),
                    "callee authority cannot be masked as root execution"
                );
            }
            let dir = tempfile::tempdir().unwrap();
            bundle.write(dir.path()).unwrap();
            let loaded = ReplayBundle::read(dir.path(), &ReplayLimits::default()).unwrap();
            assert_eq!(loaded.replay(&ReplayOptions::default()).unwrap(), expected);
            if case == 0 {
                let operation = bundle.metadata.mapping.compact_op(11).unwrap() as usize;
                bundle.facts.operations[operation].opcode = Opcode::Constant;
                bundle.facts.operations[operation].a = ValueId::NONE;
                reseal(&mut bundle);
                assert!(
                    bundle.replay(&ReplayOptions::default()).is_err(),
                    "changed static receiver authority must change the World request, never reuse a trusted bool"
                );
            }
        }
    }

    #[test]
    fn effects_closure_replay_compares_flags_and_legacy_evidence_stays_open() {
        assert!(ReplayOutcome::default().effects_open);
        let mut forged = captured();
        forged.metadata.expected.effects_open = false;
        reseal(&mut forged);
        assert!(forged.replay(&ReplayOptions::default()).is_err());
        assert!(!forged.compare(&ReplayOptions::default()).unwrap().equal);
        let mut open = captured();
        assert!(open.metadata.expected.effects_open);
        open.metadata.version = 4;
        reseal(&mut open);
        assert!(open.replay(&ReplayOptions::default()).unwrap().effects_open);
        assert!(
            !serde_json::to_value(&open.metadata.expected)
                .unwrap()
                .as_object()
                .unwrap()
                .contains_key("effects_open")
        );
        open.metadata.expected.effects_open = false;
        reseal(&mut open);
        assert!(matches!(
            open.replay(&ReplayOptions::default()),
            Err(Error::Invalid("legacy replay effects closure"))
        ));

        let (mut facts, mut graph, world) = fixture();
        let body = graph.nodes[0].body;
        for operation in &mut facts.operations[facts.bodies[body.index()].operations.range()] {
            operation.opcode = Opcode::Constant;
            operation.dest = ValueId::NONE;
            operation.a = ValueId::NONE;
            operation.b = ValueId::NONE;
            operation.arguments = IdRange::default();
            operation.flags = 0;
        }
        graph.edges.clear();
        graph.index().unwrap();
        let mut closed = capture_context(
            &facts,
            &graph,
            &TypeIndex::new(&facts),
            &world,
            NodeId(0),
            world.receiver,
            &[world.argument],
            &ReplayLimits::default(),
        )
        .unwrap();
        assert!(!closed.metadata.expected.effects_open);
        assert_eq!(
            serde_json::to_value(&closed.metadata.expected).unwrap()["effects_open"],
            false
        );
        let directory = tempfile::tempdir().unwrap();
        closed.write(directory.path()).unwrap();
        let loaded = ReplayBundle::read(directory.path(), &ReplayLimits::default()).unwrap();
        assert!(
            !loaded
                .replay(&ReplayOptions::default())
                .unwrap()
                .effects_open
        );
        closed.metadata.version = 4;
        closed.metadata.expected.effects_open = true;
        reseal(&mut closed);
        assert!(
            closed
                .replay(&ReplayOptions::default())
                .unwrap()
                .effects_open
        );
        closed.metadata.version = VERSION;
        reseal(&mut closed);
        assert!(closed.replay(&ReplayOptions::default()).is_err());
        assert!(!closed.compare(&ReplayOptions::default()).unwrap().equal);

        let mut malformed = serde_json::to_value(&loaded.metadata.expected).unwrap();
        malformed["effects_open"] = serde_json::json!(2);
        assert!(serde_json::from_value::<ReplayOutcome>(malformed.clone()).is_err());
        malformed.as_object_mut().unwrap().remove("effects_open");
        assert!(
            serde_json::from_value::<ReplayOutcome>(malformed)
                .unwrap()
                .effects_open
        );
    }

    #[test]
    fn actual_issue_site_roundtrips_original_ids_and_rejects_wrong_body_kind_or_opcode() {
        let bundle = captured();
        let site = bundle.metadata.expected.first_issue.as_ref().unwrap();
        assert_eq!(site.operation, 7);
        assert_eq!(site.kind, IssueKind::UnknownExecution as u32);
        assert_eq!(site.reason, RuntimeIssueReason::UnknownOperation as u32);
        let dir = tempfile::tempdir().unwrap();
        bundle.write(dir.path()).unwrap();
        let loaded = ReplayBundle::read(dir.path(), &ReplayLimits::default()).unwrap();
        assert_eq!(
            loaded
                .replay(&ReplayOptions::default())
                .unwrap()
                .first_issue,
            Some(site.clone())
        );
        for case in 0..4 {
            let mut bad = captured();
            let recorded = bad.metadata.expected.first_issue.as_mut().unwrap();
            match case {
                0 => recorded.operation = 10,
                1 => recorded.operation = 0,
                2 => recorded.kind = IssueKind::UnresolvedSymbol as u32,
                _ => {
                    bad.metadata.expected.issues.clear();
                }
            }
            bad.recording_digest = digest(&serde_json::to_vec(&bad.metadata).unwrap());
            assert!(
                bad.replay(&ReplayOptions::default()).is_err(),
                "malformed issue case {case}"
            );
        }
    }
    #[test]
    fn compact_snapshot_roundtrip_preserves_negative_reads_callbacks_and_candidate_universe() {
        let bundle = captured();
        assert!(
            bundle.report().owned_bytes > bundle.facts.owned_bytes() + bundle.graph.owned_bytes()
        );
        assert_eq!(
            bundle.report().candidates,
            6,
            "includes filtered Right and compile candidates"
        );
        assert!(!bundle.metadata.mapping.symbols.contains(&0));
        let result = bundle.replay(&ReplayOptions::default()).unwrap();
        assert!(result.calls.iter().any(|call| call.target == 1));
        assert!(!result.calls.iter().any(|call| call.target == 2));
        assert_eq!(
            result
                .calls
                .iter()
                .filter(|call| call.kind == EdgeKind::Callback as u32)
                .count(),
            2
        );
        assert!(
            result
                .reads
                .iter()
                .any(|(slot, _, present)| slot.kind == 1 && slot.owner != u32::MAX && !present)
        );
        assert!(
            result
                .reads
                .iter()
                .any(|(slot, _, present)| slot.kind == 1 && slot.owner == u32::MAX && !present)
        );
        assert!(
            result
                .reads
                .iter()
                .any(|(slot, version, present)| slot.kind == 2 && *version == 9 && *present)
        );
        assert!(
            result
                .value
                .atoms
                .iter()
                .any(|atom| atom.kind == 3 && atom.symbol == 10)
        );
        let dir = tempfile::tempdir().unwrap();
        bundle.write(dir.path()).unwrap();
        drop(bundle);
        let reopened = ReplayBundle::read(dir.path(), &ReplayLimits::default()).unwrap();
        assert_eq!(reopened.replay(&ReplayOptions::default()).unwrap(), result);
    }
    fn scoped_dispatch_capture(receiver_class: u32) -> ReplayBundle {
        let (mut facts, mut graph, mut world) = fixture();
        let invocation = facts.operations[2];
        for op in &mut facts.operations[..10] {
            op.opcode = Opcode::Constant;
            op.target = SymbolId::NONE;
            op.dest = ValueId::NONE;
            op.a = ValueId::NONE;
            op.b = ValueId::NONE;
            op.arguments = IdRange::default();
            op.flags = 0;
        }
        facts.operations[2] = invocation;
        facts.operations[8].opcode = Opcode::Return;
        facts.operations[8].a = invocation.dest;
        graph.edges.retain(|edge| edge.operation == OperationId(2));
        graph.edges.push(EdgeRecord {
            source: NodeId(0),
            target: NodeId(1),
            kind: EdgeKind::Guard,
            occurrence: OccurrenceId::NONE,
            operation: OperationId(2),
            receiver: SymbolId(3),
            flags: EDGE_UNKNOWN | EDGE_DEFERRED_DISPATCH,
        });
        graph.index().unwrap();
        world.receiver = world
            .pool
            .singleton(Atom {
                kind: AtomKind::Object,
                site: OperationId::NONE,
                symbol: SymbolId(receiver_class),
                binding: 0,
            })
            .unwrap();
        capture_context(
            &facts,
            &graph,
            &TypeIndex::new(&facts),
            &world,
            NodeId(0),
            world.receiver,
            &[world.argument],
            &ReplayLimits::default(),
        )
        .unwrap()
    }
    fn receiver_dispatch_capture(receiver_class: u32, known: bool) -> ReplayBundle {
        let (mut facts, mut graph, mut world) = fixture();
        let invocation = facts.operations[2];
        for op in &mut facts.operations[..10] {
            op.opcode = Opcode::Constant;
            op.target = SymbolId::NONE;
            op.dest = ValueId::NONE;
            op.a = ValueId::NONE;
            op.b = ValueId::NONE;
            op.arguments = IdRange::default();
            op.flags = 0;
        }
        facts.operations[2] = invocation;
        facts.operations[8].opcode = Opcode::Return;
        facts.operations[8].a = invocation.dest;
        facts.relations.push(RelationRecord {
            source: SymbolId(3),
            target: SymbolId(3),
            kind: RelationKind::DeferredReceiverDispatch,
            file: FileId(0),
        });
        if known {
            facts.relations.push(RelationRecord {
                source: SymbolId(3),
                target: invocation.target,
                kind: RelationKind::KnownReceiverDispatch,
                file: FileId(0),
            });
        }
        graph.edges.retain(|edge| edge.operation == OperationId(2));
        graph.index().unwrap();
        world.receiver = world
            .pool
            .singleton(Atom {
                kind: AtomKind::Object,
                site: OperationId::NONE,
                symbol: SymbolId(receiver_class),
                binding: 0,
            })
            .unwrap();
        capture_context(
            &facts,
            &graph,
            &TypeIndex::new(&facts),
            &world,
            NodeId(0),
            world.receiver,
            &[world.argument],
            &ReplayLimits::default(),
        )
        .unwrap()
    }
    #[test]
    fn receiver_dispatch_replay_preserves_complete_sparse_inventory_and_known_lookup() {
        for (receiver, known, guarded) in [(3, false, true), (4, false, false), (3, true, false)] {
            let bundle = receiver_dispatch_capture(receiver, known);
            let expected = bundle.replay(&ReplayOptions::default()).unwrap();
            assert_eq!(expected.issues.is_empty(), !guarded);
            assert_eq!(bundle.metadata.deferred_receiver_inventory, vec![3]);
            assert_eq!(bundle.metadata.known_receiver_inventory.is_empty(), !known);
            assert_eq!(
                bundle.graph.edges.len(),
                2,
                "no marker/operation edge expansion"
            );
            let directory = tempfile::tempdir().unwrap();
            bundle.write(directory.path()).unwrap();
            let reopened = ReplayBundle::read(directory.path(), &ReplayLimits::default()).unwrap();
            assert_eq!(
                reopened.replay(&ReplayOptions::default()).unwrap(),
                expected
            );
            assert!(
                matches!(
                    reopened
                        .runtime(&ReplayOptions::default())
                        .unwrap()
                        .run(&[2], false),
                    Err(Error::Invalid(
                        "replay mask changes receiver dispatch authority"
                    ))
                ),
                "reduction cannot erase an operation bound to receiver authority"
            );
        }
    }
    #[test]
    fn receiver_dispatch_replay_rejects_stripped_rows_and_resealed_inventory_changes() {
        for kind in [
            RelationKind::DeferredReceiverDispatch,
            RelationKind::KnownReceiverDispatch,
        ] {
            let mut omitted = receiver_dispatch_capture(3, true);
            omitted.facts.relations.retain(|row| row.kind != kind);
            assert!(omitted.scope_digest().is_err(), "omitted {kind:?} rows");
            omitted.recording_digest = digest(&serde_json::to_vec(&omitted.metadata).unwrap());
            assert!(omitted.replay(&ReplayOptions::default()).is_err());
        }
        let mut omitted = receiver_dispatch_capture(3, false);
        omitted.metadata.deferred_receiver_inventory.clear();
        omitted.recording_digest = digest(&serde_json::to_vec(&omitted.metadata).unwrap());
        assert!(omitted.replay(&ReplayOptions::default()).is_err());
        let mut changed = receiver_dispatch_capture(3, true);
        changed.metadata.known_receiver_inventory[0].0 = 4;
        changed.recording_digest = digest(&serde_json::to_vec(&changed.metadata).unwrap());
        assert!(changed.replay(&ReplayOptions::default()).is_err());
    }
    #[test]
    fn scoped_dispatch_frontier_roundtrip_retains_receiver_scope_and_static_authority() {
        for (receiver, guarded) in [(3, true), (4, false)] {
            let bundle = scoped_dispatch_capture(receiver);
            let expected = bundle.replay(&ReplayOptions::default()).unwrap();
            assert_eq!(expected.issues.is_empty(), !guarded);
            if guarded {
                assert_eq!(expected.first_issue.as_ref().unwrap().operation, 2);
            }
            assert_eq!(
                bundle.graph.edges.len(),
                3,
                "includes the non-call frontier"
            );
            let directory = tempfile::tempdir().unwrap();
            bundle.write(directory.path()).unwrap();
            let reopened = ReplayBundle::read(directory.path(), &ReplayLimits::default()).unwrap();
            assert_eq!(
                reopened.replay(&ReplayOptions::default()).unwrap(),
                expected
            );
            assert!(
                reopened
                    .runtime(&ReplayOptions::default())
                    .unwrap()
                    .run(&[2], false)
                    .is_err(),
                "the opcode bound to the scoped certificate is immutable authority"
            );
            if guarded {
                let reduced = reopened
                    .minimize(
                        &MinimizeOptions {
                            max_evaluations: 32,
                            ..Default::default()
                        },
                        &ReplayPredicate {
                            issue: Some(IssueKind::UnknownExecution),
                            min_calls: 1,
                            preserve_exact_output: false,
                            ..Default::default()
                        },
                    )
                    .unwrap();
                assert!(!reduced.disabled_operations.contains(&2));
                assert_eq!(
                    reduced.active_operations,
                    10 - reduced.disabled_operations.len(),
                    "the retained invocation still counts as an active operation"
                );
                assert!(
                    reduced
                        .outcome
                        .issues
                        .contains(&(IssueKind::UnknownExecution as u32))
                );
            }
        }
        for case in 0..3 {
            let mut bad = scoped_dispatch_capture(3);
            let edge = bad
                .graph
                .edges
                .iter_mut()
                .find(|edge| edge.flags & EDGE_DEFERRED_DISPATCH != 0)
                .unwrap();
            match case {
                0 => edge.operation = OperationId::NONE,
                1 => edge.receiver = SymbolId::NONE,
                2 => edge.flags = EDGE_DEFERRED_DISPATCH,
                _ => unreachable!(),
            }
            assert!(
                bad.replay(&ReplayOptions::default()).is_err(),
                "malformed frontier{case}"
            );
        }
        let mut omitted = scoped_dispatch_capture(3);
        let index = omitted
            .graph
            .edges
            .iter()
            .position(|edge| edge.flags & EDGE_DEFERRED_DISPATCH != 0)
            .unwrap();
        omitted.graph.edges.remove(index);
        omitted.metadata.mapping.edges.remove(index);
        omitted.graph.index().unwrap();
        reseal(&mut omitted);
        assert!(
            omitted.replay(&ReplayOptions::default()).is_err(),
            "even a resealed omission must not match the recorded guarded transfer"
        );
    }
    #[test]
    fn omitted_record_or_candidate_and_corrupted_identity_fail_closed() {
        let mut bundle = captured();
        bundle.metadata.events.pop();
        assert!(bundle.replay(&ReplayOptions::default()).is_err());
        bundle.recording_digest = digest(&serde_json::to_vec(&bundle.metadata).unwrap());
        assert!(
            bundle.replay(&ReplayOptions::default()).is_err(),
            "resealed incomplete transcript is still a frontier"
        );
        let mut bundle = captured();
        bundle.graph.edges.pop();
        bundle.graph.index().unwrap();
        assert!(bundle.replay(&ReplayOptions::default()).is_err());
        let mut bundle = captured();
        bundle.graph.identity = ContentHash([99; 32]);
        assert!(bundle.replay(&ReplayOptions::default()).is_err());
        let mut bundle = captured();
        bundle.facts.relations.pop();
        assert!(bundle.replay(&ReplayOptions::default()).is_err());
        let mut bundle = captured();
        bundle.metadata.parent_inventory.pop();
        bundle.recording_digest = digest(&serde_json::to_vec(&bundle.metadata).unwrap());
        assert!(bundle.replay(&ReplayOptions::default()).is_err());
    }
    #[test]
    fn scratch_limits_are_explicit_and_repeated_runtime_retains_bounded_capacity() {
        let bundle = captured();
        for budget in [0, 1, 4095] {
            assert!(matches!(
                bundle.runtime(&ReplayOptions {
                    scratch_bytes: budget,
                    ..Default::default()
                }),
                Err(Error::Limit(_))
            ));
        }
        let mut runtime = bundle.runtime(&ReplayOptions::default()).unwrap();
        let expected = runtime.run(&[], true).unwrap();
        let bytes = runtime.owned_bytes();
        for _ in 0..20 {
            assert_eq!(runtime.run(&[], true).unwrap(), expected);
            assert_eq!(runtime.owned_bytes(), bytes);
        }
        let (facts, graph, world) = fixture();
        let limits = ReplayLimits {
            max_records: 1,
            ..Default::default()
        };
        assert!(
            capture_context(
                &facts,
                &graph,
                &TypeIndex::new(&facts),
                &world,
                NodeId(0),
                world.receiver,
                &[world.argument],
                &limits
            )
            .is_err()
        );
        assert_eq!(world.visits.load(Ordering::Relaxed), 0);
    }
    #[test]
    fn deterministic_minimizer_keeps_guard_and_target_and_saves_a_standalone_replay() {
        let bundle = captured();
        let predicate = ReplayPredicate {
            issue: Some(IssueKind::UnknownExecution),
            target: Some(NodeId(1)),
            min_calls: 1,
            preserve_exact_output: false,
            ..Default::default()
        };
        let first = bundle
            .minimize(&MinimizeOptions::default(), &predicate)
            .unwrap();
        let second = bundle
            .minimize(&MinimizeOptions::default(), &predicate)
            .unwrap();
        assert_eq!(first.disabled_operations, second.disabled_operations);
        assert_eq!(first.outcome, second.outcome);
        assert!(first.active_operations < 10);
        assert!(!first.disabled_operations.contains(&2), "dispatch kept");
        assert!(!first.disabled_operations.contains(&7), "guard kept");
        assert_eq!(
            bundle.graph.edges.len(),
            6,
            "all candidates retained while masking operations"
        );
        let dir = tempfile::tempdir().unwrap();
        bundle.write_minimized(dir.path(), &first).unwrap();
        let loaded = ReplayBundle::read(dir.path(), &ReplayLimits::default()).unwrap();
        assert_eq!(
            loaded.replay(&ReplayOptions::default()).unwrap(),
            first.outcome
        );
    }
    #[test]
    fn additional_bodies_do_not_replace_the_canonical_callable_node() {
        let (facts, mut graph, world) = fixture();
        graph.nodes.push(NodeRecord {
            symbol: SymbolId(8),
            file: FileId(0),
            body: BodyId::NONE,
            flags: NODE_EFFECTS_COMPLETE,
        });
        graph.edges.push(EdgeRecord {
            source: NodeId(0),
            target: NodeId(5),
            kind: EdgeKind::Compile,
            occurrence: OccurrenceId::NONE,
            operation: OperationId(9),
            receiver: SymbolId::NONE,
            flags: 0,
        });
        graph.index().unwrap();
        let bundle = capture_context(
            &facts,
            &graph,
            &TypeIndex::new(&facts),
            &world,
            NodeId(0),
            world.receiver,
            &[world.argument],
            &ReplayLimits::default(),
        )
        .unwrap();
        assert_eq!(bundle.report().candidates, 7);
        let result = bundle.replay(&ReplayOptions::default()).unwrap();
        assert_eq!(
            result.calls.iter().filter(|call| call.target == 3).count(),
            2
        );
        assert!(!result.calls.iter().any(|call| call.target == 5));
    }
    #[test]
    fn allocation_and_static_slot_namespaces_survive_compaction() {
        let (mut facts, graph, mut world) = fixture();
        facts.operations[11].opcode = Opcode::Allocate;
        facts.operations[11].target = SymbolId(3);
        world.receiver = world
            .pool
            .singleton(Atom {
                kind: AtomKind::Object,
                site: OperationId(11),
                symbol: SymbolId(3),
                binding: 0,
            })
            .unwrap();
        facts.operations[9].opcode = Opcode::LoadField;
        facts.operations[9].flags = OP_STATIC_FIELD;
        facts.operations[9].target = SymbolId(9);
        let bundle = capture_context(
            &facts,
            &graph,
            &TypeIndex::new(&facts),
            &world,
            NodeId(0),
            world.receiver,
            &[world.argument],
            &ReplayLimits::default(),
        )
        .unwrap();
        let result = bundle.replay(&ReplayOptions::default()).unwrap();
        assert!(
            result
                .reads
                .iter()
                .any(|(slot, _, present)| slot.kind == 7 && slot.owner == 11 && !present)
        );
        assert!(
            result
                .reads
                .iter()
                .any(|(slot, _, present)| slot.kind == 5 && slot.owner == 9 && !present)
        );
        assert_eq!(
            result.calls.iter().filter(|call| call.target == 1).count(),
            1
        );
    }
    #[test]
    fn resealed_invalid_cross_table_ids_and_response_variants_are_rejected_before_execution() {
        let mut bundle = captured();
        let root = bundle
            .metadata
            .mapping
            .compact_node(bundle.metadata.root)
            .unwrap() as usize;
        bundle.graph.nodes[root].body = BodyId(9999);
        // Scope construction rejects invalid authority references itself, and
        // admission reports this structural error before any identity mismatch.
        assert!(matches!(
            bundle.scope_digest(),
            Err(Error::Invalid("replay node body reference"))
        ));
        bundle.recording_digest = digest(&serde_json::to_vec(&bundle.metadata).unwrap());
        assert!(matches!(
            bundle.replay(&ReplayOptions::default()),
            Err(Error::Invalid("replay node body reference"))
        ));
        let mut bundle = captured();
        bundle.metadata.events[0].response = Response::Binding(None);
        bundle.recording_digest = digest(&serde_json::to_vec(&bundle.metadata).unwrap());
        assert!(matches!(
            bundle.replay(&ReplayOptions::default()),
            Err(Error::Invalid("replay response kind"))
        ));
    }
    #[test]
    fn resealed_metadata_issue_list_is_rejected_before_replay_execution() {
        let mut bundle = captured();
        let directory = tempfile::tempdir().unwrap();
        bundle.write(directory.path()).unwrap();
        bundle = ReplayBundle::read(directory.path(), &ReplayLimits::default()).unwrap();
        bundle.replay(&ReplayOptions::default()).unwrap();
        bundle.metadata.expected.first_issue = None;
        bundle
            .metadata
            .expected
            .issues
            .push(IssueKind::IncompleteHierarchy as u32);
        let bytes = serde_json::to_vec(&bundle.metadata).unwrap();
        std::fs::write(directory.path().join("metadata.json"), &bytes).unwrap();
        std::fs::write(directory.path().join("recording.sha256"), digest(&bytes).0).unwrap();
        assert!(matches!(
            ReplayBundle::read(directory.path(), &ReplayLimits::default()),
            Err(Error::Invalid(
                "metadata issue in replay execution obligations"
            ))
        ));
    }
    fn family_fixture(method: bool) -> ReplayFamily {
        let (facts, graph, world) = fixture();
        let types = TypeIndex::new(&facts);
        let first = capture_context(
            &facts,
            &graph,
            &types,
            &world,
            NodeId(0),
            world.receiver,
            &[world.argument],
            &ReplayLimits::default(),
        )
        .unwrap();
        let second = capture_context(
            &facts,
            &graph,
            &types,
            &world,
            NodeId(0),
            world.receiver,
            &[Value::TOP],
            &ReplayLimits::default(),
        )
        .unwrap();
        ReplayFamily::from_contexts(
            ReplayFamilyInventory {
                node: 0,
                total_variants: if method { 2 } else { 787 },
                total_receivers: if method { 1 } else { 104 },
                selected_variants: 2,
                selected_evaluated: 1,
                scope: if method {
                    ReplayFamilyScope::Method
                } else {
                    ReplayFamilyScope::ReceiverOf {
                        context: 10,
                        receiver: ReplayValue::from_value(&world.pool, world.receiver).unwrap(),
                    }
                },
            },
            vec![(ContextId(10), first), (ContextId(20), second)],
            &ReplayLimits::default(),
        )
        .unwrap()
    }
    #[test]
    fn complete_method_and_explicit_receiver_families_roundtrip_without_dropping_pending_frames() {
        for method in [false, true] {
            let family = family_fixture(method);
            let expected = family.replay(&ReplayOptions::default()).unwrap();
            let compared = family.compare(&ReplayOptions::default()).unwrap();
            assert_eq!(compared.len(), 2);
            assert!(compared.iter().all(|entry| entry.equal));
            assert_eq!(expected.len(), 2);
            assert_ne!(expected[0].outcome, expected[1].outcome);
            assert_eq!(family.inventory().selected_evaluated, 1);
            let dir = tempfile::tempdir().unwrap();
            family.write(dir.path()).unwrap();
            let loaded = ReplayFamily::read(dir.path(), &ReplayLimits::default()).unwrap();
            assert_eq!(loaded.replay(&ReplayOptions::default()).unwrap(), expected);
            assert!(!loaded.report().truncated);
        }
    }
    #[test]
    fn family_limits_and_omitted_variants_are_explicit_failures() {
        let family = family_fixture(false);
        let mut inventory = family.inventory.clone();
        inventory.scope = ReplayFamilyScope::Method;
        assert!(
            ReplayFamily::from_contexts(inventory, family.contexts, &ReplayLimits::default())
                .is_err()
        );
        let family = family_fixture(false);
        let mut inventory = family.inventory.clone();
        inventory.selected_variants = 65;
        assert!(matches!(
            ReplayFamily::from_contexts(inventory, family.contexts, &ReplayLimits::default()),
            Err(Error::Limit(_))
        ));
        let family = family_fixture(false);
        let dir = tempfile::tempdir().unwrap();
        family.write(dir.path()).unwrap();
        let mut manifest: FamilyManifest =
            serde_json::from_slice(&std::fs::read(dir.path().join("family.json")).unwrap())
                .unwrap();
        manifest.entries.pop();
        let bytes = serde_json::to_vec(&manifest).unwrap();
        std::fs::write(dir.path().join("family.json"), &bytes).unwrap();
        std::fs::write(dir.path().join("family.sha256"), digest(&bytes).0).unwrap();
        assert!(ReplayFamily::read(dir.path(), &ReplayLimits::default()).is_err());
    }
    #[test]
    fn real_pr7743_clue_snapshot_replays_and_reduces_with_callback_fanout_and_guard() {
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../fixtures/transfer-replay/pr7743-clue");
        let bundle = ReplayBundle::read(&path.join("bundle"), &ReplayLimits::default()).unwrap();
        let portable = serde_json::from_slice::<serde_json::Value>(
            &std::fs::read(path.join("provenance.json")).unwrap(),
        )
        .unwrap();
        for name in [
            "facts.bin",
            "graph.bin",
            "metadata.json",
            "recording.sha256",
        ] {
            let bytes = std::fs::read(path.join("bundle").join(name)).unwrap();
            assert_eq!(
                digest(&bytes).to_string(),
                portable["artifacts"][name]["sha256"].as_str().unwrap()
            );
        }
        assert_eq!(
            bundle.metadata.source_facts,
            portable["source_facts"].as_str().unwrap()
        );
        assert_eq!(
            bundle.metadata.source_graph,
            portable["source_graph"].as_str().unwrap()
        );
        assert_eq!(bundle.metadata.scope, portable["scope"].as_str().unwrap());
        assert_eq!(
            bundle.report().candidates as u64,
            portable["counts"]["static_candidates"].as_u64().unwrap()
        );
        assert_eq!(
            bundle.report().symbols as u64,
            portable["counts"]["symbols"].as_u64().unwrap()
        );
        let frozen: serde_json::Value =
            serde_json::from_slice(&std::fs::read(path.join("reduction.json")).unwrap()).unwrap();
        let callback_target = frozen["callback_target"].as_u64().unwrap() as u32;
        let callback_binding = frozen["callback_binding"].as_u64().unwrap() as u32;
        let baseline = bundle.replay(&ReplayOptions::default()).unwrap();
        assert!(baseline.first_issue.is_some(), "genuine runtime issue site");
        assert_eq!(baseline.calls.len(), bundle.metadata.expected.calls.len());
        assert!(
            baseline
                .calls
                .iter()
                .any(|call| call.target == callback_target
                    && call.kind == EdgeKind::Callback as u32
                    && call.binding == callback_binding)
        );
        let predicate = ReplayPredicate {
            issue: Some(IssueKind::decode(frozen["issue"].as_u64().unwrap() as u32).unwrap()),
            target: Some(NodeId(callback_target)),
            min_calls: frozen["min_calls"].as_u64().unwrap() as usize,
            min_reads: frozen["min_reads"].as_u64().unwrap() as usize,
            preserve_exact_output: false,
        };
        let reduction = bundle
            .minimize(&MinimizeOptions::default(), &predicate)
            .unwrap();
        assert_eq!(
            reduction.active_operations as u64,
            frozen["active_operations"].as_u64().unwrap()
        );
        assert_eq!(
            reduction.disabled_operations,
            serde_json::from_value::<Vec<u32>>(frozen["disabled_operations"].clone()).unwrap()
        );
        assert!(predicate.accepts(&reduction.outcome, &baseline));
        let mut runtime = bundle.runtime(&ReplayOptions::default()).unwrap();
        runtime.run(&[], true).unwrap();
        let bytes = runtime.owned_bytes();
        let start = std::time::Instant::now();
        for _ in 0..100 {
            assert_eq!(runtime.run(&[], true).unwrap(), baseline);
        }
        assert_eq!(runtime.owned_bytes(), bytes);
        eprintln!(
            "real_clue_replay_100_ns={} runtime_owned_bytes={bytes}",
            start.elapsed().as_nanos()
        );
    }
    #[test]
    fn family_minimization_applies_one_mask_to_every_frame_and_reopens_all_outcomes() {
        let family = family_fixture(false);
        let predicate = ReplayFamilyPredicate {
            condition: ReplayPredicate {
                issue: Some(IssueKind::UnknownExecution),
                target: Some(NodeId(3)),
                min_calls: 4,
                preserve_exact_output: false,
                ..Default::default()
            },
            context: Some(10),
            match_all: false,
        };
        let reduction = family
            .minimize(&MinimizeOptions::default(), &predicate)
            .unwrap();
        assert_eq!(reduction.outcomes.len(), 2);
        assert!(reduction.transfer_evaluations >= reduction.mask_evaluations + 1);
        assert!(reduction.transfer_evaluations <= reduction.mask_evaluations * 2);
        assert!(reduction.active_operations < 10);
        let dir = tempfile::tempdir().unwrap();
        family.write_minimized(dir.path(), &reduction).unwrap();
        let loaded = ReplayFamily::read(dir.path(), &ReplayLimits::default()).unwrap();
        assert_eq!(
            loaded.replay(&ReplayOptions::default()).unwrap(),
            reduction.outcomes
        );
        let limit = MinimizeOptions {
            scratch_bytes: 4096,
            ..Default::default()
        };
        assert!(matches!(
            family.minimize(&limit, &predicate),
            Err(Error::Limit(_))
        ));
    }
    #[test]
    fn family_rejects_inconsistent_shared_world_responses() {
        let mut family = family_fixture(false);
        family.contexts[1].1.metadata.events[0].response = Response::Slot {
            value: ReplayValue {
                unknown: 1,
                atoms: Vec::new(),
            },
            version: 0,
            present: false,
        };
        let meta = &family.contexts[1].1.metadata;
        family.contexts[1].1.recording_digest = digest(&serde_json::to_vec(meta).unwrap());
        assert!(matches!(
            ReplayFamily::from_contexts(
                family.inventory,
                family.contexts,
                &ReplayLimits::default()
            ),
            Err(Error::Invalid("replay inconsistent family world snapshot"))
        ));
    }
    #[test]
    fn effect_only_initializer_replay_records_execution_without_a_summary_read() {
        let (facts, mut graph, world) = fixture();
        graph.nodes[0].body = BodyId::NONE;
        for edge in &mut graph.edges {
            edge.kind = EdgeKind::Compile;
        }
        graph.edges[0].kind = EdgeKind::Initialize;
        graph.index().unwrap();
        let bundle = capture_context(
            &facts,
            &graph,
            &TypeIndex::new(&facts),
            &world,
            NodeId(0),
            world.receiver,
            &[],
            &ReplayLimits::default(),
        )
        .unwrap();
        let outcome = bundle.replay(&ReplayOptions::default()).unwrap();
        assert_eq!(outcome.calls.len(), 1);
        assert!(!outcome.calls[0].observe_return);
        assert_eq!(outcome.calls[0].summary, None);
        assert!(outcome.reads.is_empty());
        assert_eq!(world.visits.load(Ordering::Relaxed), 0);
        let dir = tempfile::tempdir().unwrap();
        bundle.write(dir.path()).unwrap();
        let loaded = ReplayBundle::read(dir.path(), &ReplayLimits::default()).unwrap();
        assert_eq!(loaded.replay(&ReplayOptions::default()).unwrap(), outcome);
    }
    #[test]
    fn comparison_allows_unused_known_records_but_rejects_new_world_frontiers() {
        let mut bundle = captured();
        bundle
            .metadata
            .events
            .push(bundle.metadata.events.last().unwrap().clone());
        bundle.recording_digest = digest(&serde_json::to_vec(&bundle.metadata).unwrap());
        assert!(bundle.replay(&ReplayOptions::default()).is_err());
        assert!(bundle.compare(&ReplayOptions::default()).unwrap().equal);
        let mut bundle = captured();
        bundle.metadata.events.remove(0);
        bundle.recording_digest = digest(&serde_json::to_vec(&bundle.metadata).unwrap());
        assert!(bundle.compare(&ReplayOptions::default()).is_err());
    }
    #[test]
    fn converged_exact_and_overflow_frames_keep_both_context_identities() {
        let inventory = ReplayFamilyInventory {
            node: 0,
            total_variants: 2,
            total_receivers: 1,
            selected_variants: 2,
            selected_evaluated: 2,
            scope: ReplayFamilyScope::Method,
        };
        let family = ReplayFamily::from_contexts(
            inventory.clone(),
            vec![(ContextId(10), captured()), (ContextId(20), captured())],
            &ReplayLimits::default(),
        )
        .unwrap();
        let outcomes = family.replay(&ReplayOptions::default()).unwrap();
        assert_eq!(
            outcomes
                .iter()
                .map(|entry| entry.context)
                .collect::<Vec<_>>(),
            vec![10, 20]
        );
        assert_eq!(outcomes[0].outcome, outcomes[1].outcome);
        assert!(
            ReplayFamily::from_contexts(
                inventory,
                vec![(ContextId(10), captured()), (ContextId(10), captured())],
                &ReplayLimits::default()
            )
            .is_err()
        );
    }
}
