//! Bounded structural DTOs for an effect-capsule prototype.
//!
//! This crate validates geometry and local namespaces, not bytecode semantics,
//! provider identity, a complete catalogue, or exclusion authority. A consumer
//! must verify those bindings separately. A finite list in an open channel is
//! only a lower bound. Missing evidence is represented by an explicit ALL-TOP
//! method, never by a complete empty method.

use std::fmt;
use std::mem::size_of;

mod callables;
pub use callables::*;

pub const NONE: u32 = u32::MAX;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct MethodId(pub u32);

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Range {
    pub start: u32,
    pub len: u32,
}

impl Range {
    pub const EMPTY: Self = Self { start: 0, len: 0 };
    pub fn checked(self, count: usize) -> Result<std::ops::Range<usize>, Error> {
        let start = self.start as usize;
        let end = start
            .checked_add(self.len as usize)
            .ok_or(Error::Overflow)?;
        if end > count {
            return Err(Error::Bounds);
        }
        Ok(start..end)
    }
}

macro_rules! numeric_enum {
    ($name:ident { $($variant:ident = $number:literal),+ $(,)? }) => {
        #[repr(u32)]
        #[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
        pub enum $name { $($variant = $number),+ }
        impl $name {
            pub const fn from_u32(value: u32) -> Option<Self> {
                match value { $($number => Some(Self::$variant),)+ _ => None }
            }
        }
    };
}

numeric_enum!(Channel {
    Calls = 0, CodeObservations = 1, Reads = 2, Writes = 3, Escapes = 4,
    Initializes = 5, Throws = 6, Synchronizes = 7, External = 8, Flows = 9,
});

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct TopMask(u32);

impl TopMask {
    pub const NONE: Self = Self(0);
    pub const ALL: Self = Self((1 << 10) - 1);
    pub const fn from_bits(bits: u32) -> Option<Self> {
        if bits & !Self::ALL.0 == 0 {
            Some(Self(bits))
        } else {
            None
        }
    }
    pub const fn bits(self) -> u32 {
        self.0
    }
    pub const fn contains(self, channel: Channel) -> bool {
        self.0 & (1 << channel as u32) != 0
    }
    pub fn insert(&mut self, channel: Channel) {
        self.0 |= 1 << channel as u32;
    }
    pub fn join(&mut self, other: Self) {
        self.0 |= other.0;
    }
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }
}

numeric_enum!(OriginKind { Any = 0, Receiver = 1, Argument = 2, Capture = 3, Fresh = 4 });
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Origin {
    pub kind: OriginKind,
    pub index: u32,
}
impl Origin {
    pub const ANY: Self = Self {
        kind: OriginKind::Any,
        index: 0,
    };
    pub const RECEIVER: Self = Self {
        kind: OriginKind::Receiver,
        index: 0,
    };
    pub const fn argument(index: u32) -> Self {
        Self {
            kind: OriginKind::Argument,
            index,
        }
    }
    pub const fn capture(index: u32) -> Self {
        Self {
            kind: OriginKind::Capture,
            index,
        }
    }
    pub const fn fresh(index: u32) -> Self {
        Self {
            kind: OriginKind::Fresh,
            index,
        }
    }
}

numeric_enum!(StorageKind { StaticField = 0, InstanceField = 1, ArrayElements = 2, RuntimeState = 3 });
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct StorageRef {
    pub kind: StorageKind,
    pub member: u32,
    pub base: Origin,
}
numeric_enum!(SubjectKind { FactNode = 0, ForeignMethod = 1, CallableAdapter = 2, RuntimePhase = 3 });
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SubjectRef {
    pub kind: SubjectKind,
    pub index: u32,
}
numeric_enum!(CallKind { Static = 0, Special = 1, Virtual = 2, Interface = 3, Callback = 4 });
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CallRow {
    pub site: u32,
    pub target: CallTarget,
    pub kind: CallKind,
    pub receiver: Origin,
    pub receiver_value: ValueRef,
    /// Method-local result cell; NONE means discarded, never no execution.
    pub result: u32,
    pub arguments: Range,
    pub captures: Range,
}
numeric_enum!(CodeKind { Method = 0, Class = 1 });
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct CodeRef {
    pub kind: CodeKind,
    pub index: u32,
}
numeric_enum!(EscapeSink { Return = 0, Heap = 1, Callback = 2, External = 3, Unknown = 4 });
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct EscapeRef {
    pub origin: Origin,
    pub sink: EscapeSink,
    pub index: u32,
}
numeric_enum!(SyncKind { AcquireFence = 0, ReleaseFence = 1, FullFence = 2, Monitor = 3, Volatile = 4 });
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SyncRef {
    pub kind: SyncKind,
    pub base: Origin,
}
numeric_enum!(ExternalKind { Read = 0, Write = 1, Control = 2 });
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ExternalRef {
    pub kind: ExternalKind,
    pub key: u32,
}
numeric_enum!(FlowSink {
    Return = 0, CallReceiver = 1, CallArgument = 2, CallCapture = 3,
    HeapWrite = 4, Throw = 5, External = 6, Control = 7,
});
/// `via` is a method-local call/write/external-row ordinal. Return, Throw and
/// Control use NONE. `index` is the call argument/capture or exception key.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FlowRef {
    pub source: Origin,
    pub sink: FlowSink,
    pub via: u32,
    pub index: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MethodRow {
    pub subject: SubjectRef,
    pub authority: u32,
    pub arity: u32,
    pub captures: u32,
    pub fresh_sites: u32,
    pub locals: u32,
    pub creations: Range,
    pub value_flows: Range,
    pub top: TopMask,
    pub calls: Range,
    pub code_observations: Range,
    pub reads: Range,
    pub writes: Range,
    pub escapes: Range,
    pub initializes: Range,
    pub throws: Range,
    pub synchronizes: Range,
    pub external: Range,
    pub flows: Range,
}

impl MethodRow {
    pub const fn unknown(
        subject: SubjectRef,
        authority: u32,
        arity: u32,
        captures: u32,
        fresh_sites: u32,
    ) -> Self {
        Self {
            subject,
            authority,
            arity,
            captures,
            fresh_sites,
            locals: 0,
            creations: Range::EMPTY,
            value_flows: Range::EMPTY,
            top: TopMask::ALL,
            calls: Range::EMPTY,
            code_observations: Range::EMPTY,
            reads: Range::EMPTY,
            writes: Range::EMPTY,
            escapes: Range::EMPTY,
            initializes: Range::EMPTY,
            throws: Range::EMPTY,
            synchronizes: Range::EMPTY,
            external: Range::EMPTY,
            flows: Range::EMPTY,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct CapsuleData {
    pub methods: Vec<MethodRow>,
    pub calls: Vec<CallRow>,
    pub origins: Vec<Origin>,
    /// Parallel to origins, including creation captures.
    pub callable_values: Vec<ValueRef>,
    pub sam_arities: Vec<u32>,
    pub creations: Vec<CallableCreation>,
    /// Canonical order is (creation, requested SAM). Proofs are admitted by the
    /// artifact layer; these rows never grant compatibility by arity alone.
    pub callable_bridges: Vec<CallableBridge>,
    pub value_flows: Vec<ValueFlow>,
    pub code_observations: Vec<CodeRef>,
    pub reads: Vec<StorageRef>,
    pub writes: Vec<StorageRef>,
    pub escapes: Vec<EscapeRef>,
    pub initializes: Vec<MethodId>,
    pub throws: Vec<u32>,
    pub synchronizes: Vec<SyncRef>,
    pub external: Vec<ExternalRef>,
    pub flows: Vec<FlowRef>,
}

/// A checked scalar reader also permits a codec to validate borrowed fixed-width
/// tables without allocating decoded row vectors. `None` is malformed, not empty.
macro_rules! table_view {
    ($(($count:ident, $get:ident, $field:ident, $row:ty)),+ $(,)?) => {
        pub trait TableView {
            $(fn $count(&self) -> usize;
              fn $get(&self, index: usize) -> Option<$row>;)+
        }
        impl TableView for CapsuleData {
            $(fn $count(&self) -> usize { self.$field.len() }
              fn $get(&self, index: usize) -> Option<$row> { self.$field.get(index).copied() })+
        }
    };
}
table_view!(
    (method_count, method, methods, MethodRow),
    (call_count, call, calls, CallRow),
    (origin_count, origin, origins, Origin),
    (
        callable_value_count,
        callable_value,
        callable_values,
        ValueRef
    ),
    (sam_count, sam_arity, sam_arities, u32),
    (creation_count, creation, creations, CallableCreation),
    (
        callable_bridge_count,
        callable_bridge,
        callable_bridges,
        CallableBridge
    ),
    (value_flow_count, value_flow, value_flows, ValueFlow),
    (
        code_observation_count,
        code_observation,
        code_observations,
        CodeRef
    ),
    (read_count, read, reads, StorageRef),
    (write_count, write, writes, StorageRef),
    (escape_count, escape, escapes, EscapeRef),
    (initialize_count, initialize, initializes, MethodId),
    (throw_count, r#throw, throws, u32),
    (synchronize_count, synchronize, synchronizes, SyncRef),
    (external_count, external, external, ExternalRef),
    (flow_count, flow, flows, FlowRef),
);

#[derive(Clone, Copy, Debug, Default)]
pub struct RefBounds {
    pub fact_nodes: u32,
    pub foreign_methods: u32,
    pub authorities: u32,
    pub members: u32,
    pub classes: u32,
    pub exceptions: u32,
    pub externals: u32,
    pub sites: u32,
    pub sams: u32,
    pub adapters: u32,
    pub bridge_proofs: u32,
    pub phases: u32,
}

#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub max_methods: usize,
    pub max_rows: usize,
    pub max_bytes: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            max_methods: 1_000_000,
            max_rows: 2_000_000,
            max_bytes: 256 << 20,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Error {
    Bounds,
    Malformed,
    Budget,
    Capacity,
    Overflow,
    Arity,
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "effect capsule {:?}", self)
    }
}
impl std::error::Error for Error {}

fn bound(index: u32, count: u32) -> Result<(), Error> {
    if index < count {
        Ok(())
    } else {
        Err(Error::Bounds)
    }
}
fn method_bound(index: MethodId, count: usize) -> Result<(), Error> {
    if (index.0 as usize) < count {
        Ok(())
    } else {
        Err(Error::Bounds)
    }
}
fn origin_bound(origin: Origin, method: MethodRow) -> Result<(), Error> {
    match origin.kind {
        OriginKind::Any | OriginKind::Receiver if origin.index == 0 => Ok(()),
        OriginKind::Argument => bound(origin.index, method.arity),
        OriginKind::Capture => bound(origin.index, method.captures),
        OriginKind::Fresh => bound(origin.index, method.fresh_sites),
        _ => Err(Error::Malformed),
    }
}
fn storage_bound(storage: StorageRef, method: MethodRow, bounds: RefBounds) -> Result<(), Error> {
    origin_bound(storage.base, method)?;
    match storage.kind {
        StorageKind::StaticField | StorageKind::RuntimeState => {
            bound(storage.member, bounds.members)?;
            if storage.base != Origin::ANY {
                return Err(Error::Malformed);
            }
        }
        StorageKind::InstanceField => bound(storage.member, bounds.members)?,
        StorageKind::ArrayElements if storage.member == NONE => (),
        StorageKind::ArrayElements => return Err(Error::Malformed),
    }
    Ok(())
}

fn table_size(t: &impl TableView) -> Result<(usize, usize), Error> {
    let mut rows = 0usize;
    let mut bytes = 0usize;
    for (count, width) in [
        (t.method_count(), size_of::<MethodRow>()),
        (t.call_count(), size_of::<CallRow>()),
        (t.origin_count(), size_of::<Origin>()),
        (t.callable_value_count(), size_of::<ValueRef>()),
        (t.sam_count(), size_of::<u32>()),
        (t.creation_count(), size_of::<CallableCreation>()),
        (t.callable_bridge_count(), size_of::<CallableBridge>()),
        (t.value_flow_count(), size_of::<ValueFlow>()),
        (t.code_observation_count(), size_of::<CodeRef>()),
        (t.read_count(), size_of::<StorageRef>()),
        (t.write_count(), size_of::<StorageRef>()),
        (t.escape_count(), size_of::<EscapeRef>()),
        (t.initialize_count(), size_of::<MethodId>()),
        (t.throw_count(), size_of::<u32>()),
        (t.synchronize_count(), size_of::<SyncRef>()),
        (t.external_count(), size_of::<ExternalRef>()),
        (t.flow_count(), size_of::<FlowRef>()),
    ] {
        if count >= NONE as usize {
            return Err(Error::Overflow);
        }
        rows = rows.checked_add(count).ok_or(Error::Overflow)?;
        bytes = bytes
            .checked_add(count.checked_mul(width).ok_or(Error::Overflow)?)
            .ok_or(Error::Overflow)?;
    }
    Ok((rows, bytes))
}

/// Allocation-free structural validation. Namespace counts must themselves come
/// from verified key tables; counts alone are not semantic authority.
pub fn validate_tables(t: &impl TableView, bounds: RefBounds, limits: Limits) -> Result<(), Error> {
    let (rows, bytes) = table_size(t)?;
    if t.method_count() > limits.max_methods || rows > limits.max_rows || bytes > limits.max_bytes {
        return Err(Error::Budget);
    }
    if t.callable_value_count() != t.origin_count() || t.sam_count() != bounds.sams as usize {
        return Err(Error::Malformed);
    }
    for i in 0..t.sam_count() {
        if t.sam_arity(i).ok_or(Error::Malformed)? == NONE {
            return Err(Error::Overflow);
        }
    }
    for mi in 0..t.method_count() {
        let m = t.method(mi).ok_or(Error::Malformed)?;
        bound(m.authority, bounds.authorities)?;
        match m.subject.kind {
            SubjectKind::FactNode => bound(m.subject.index, bounds.fact_nodes)?,
            SubjectKind::ForeignMethod => bound(m.subject.index, bounds.foreign_methods)?,
            SubjectKind::CallableAdapter => bound(m.subject.index, bounds.adapters)?,
            SubjectKind::RuntimePhase => {
                bound(m.subject.index, bounds.phases)?;
                // A phase is not a fabricated JVM method. Until a dedicated
                // phase contract is admitted, it remains opaque. Known code
                // and zero-actual initialization dependencies are lower bounds.
                if m.top != TopMask::ALL
                    || m.arity != 0
                    || m.captures != 0
                    || m.locals != 0
                    || m.fresh_sites != 0
                    || [
                        m.creations,
                        m.value_flows,
                        m.reads,
                        m.writes,
                        m.escapes,
                        m.throws,
                        m.synchronizes,
                        m.external,
                        m.flows,
                    ]
                    .iter()
                    .any(|range| range.len != 0)
                {
                    return Err(Error::Malformed);
                }
                for i in m.calls.checked(t.call_count())? {
                    let call = t.call(i).ok_or(Error::Malformed)?;
                    let CallTarget::Direct(target) = call.target else {
                        return Err(Error::Malformed);
                    };
                    let target = t.method(target.0 as usize).ok_or(Error::Bounds)?;
                    if call.arguments.len != 0
                        || call.captures.len != 0
                        || target.arity != 0
                        || target.captures != 0
                    {
                        return Err(Error::Arity);
                    }
                }
            }
        }
        if m.arity == NONE || m.captures == NONE || m.fresh_sites == NONE || m.locals == NONE {
            return Err(Error::Overflow);
        }
        for ci in m.calls.checked(t.call_count())? {
            let c = t.call(ci).ok_or(Error::Malformed)?;
            bound(c.site, bounds.sites)?;
            match c.target {
                CallTarget::Direct(id) => {
                    method_bound(id, t.method_count())?;
                    let target = t.method(id.0 as usize).ok_or(Error::Malformed)?;
                    if !m.top.contains(Channel::Calls)
                        && target.top != TopMask::ALL
                        && (c.arguments.len != target.arity || c.captures.len != target.captures)
                    {
                        return Err(Error::Arity);
                    }
                }
                CallTarget::Callable { value, sam } => {
                    value_bound(value, m)?;
                    if c.kind != CallKind::Callback || c.captures.len != 0 {
                        return Err(Error::Malformed);
                    }
                    if sam != NONE {
                        bound(sam, bounds.sams)?;
                        if c.arguments.len != t.sam_arity(sam as usize).ok_or(Error::Malformed)? {
                            return Err(Error::Arity);
                        }
                    }
                }
            }
            value_bound(c.receiver_value, m)?;
            if c.result != NONE {
                bound(c.result, m.locals)?;
            }
            origin_bound(c.receiver, m)?;
            if c.kind == CallKind::Static && c.receiver != Origin::ANY {
                return Err(Error::Malformed);
            }
            for oi in c
                .arguments
                .checked(t.origin_count())?
                .chain(c.captures.checked(t.origin_count())?)
            {
                origin_bound(t.origin(oi).ok_or(Error::Malformed)?, m)?;
                value_bound(t.callable_value(oi).ok_or(Error::Malformed)?, m)?;
            }
        }
        for i in m.creations.checked(t.creation_count())? {
            let c = t.creation(i).ok_or(Error::Malformed)?;
            bound(c.site, bounds.sites)?;
            bound(c.destination, m.locals)?;
            method_bound(c.implementation, t.method_count())?;
            origin_bound(c.receiver, m)?;
            value_bound(c.receiver_value, m)?;
            let implementation = t
                .method(c.implementation.0 as usize)
                .ok_or(Error::Malformed)?;
            if c.sam != NONE {
                bound(c.sam, bounds.sams)?;
                if implementation.top != TopMask::ALL
                    && implementation.arity
                        != t.sam_arity(c.sam as usize).ok_or(Error::Malformed)?
                {
                    return Err(Error::Arity);
                }
            }
            if implementation.top != TopMask::ALL && implementation.captures != c.captures.len {
                return Err(Error::Arity);
            }
            for oi in c.captures.checked(t.origin_count())? {
                origin_bound(t.origin(oi).ok_or(Error::Malformed)?, m)?;
                value_bound(t.callable_value(oi).ok_or(Error::Malformed)?, m)?;
            }
        }
        for i in m.value_flows.checked(t.value_flow_count())? {
            let flow = t.value_flow(i).ok_or(Error::Malformed)?;
            value_bound(flow.value, m)?;
            match flow.kind {
                ValueFlowKind::Copy => bound(flow.index, m.locals)?,
                ValueFlowKind::Return if flow.index == 0 => (),
                ValueFlowKind::Store => bound(flow.index, m.writes.len)?,
                ValueFlowKind::Load if flow.value.kind == ValueKind::Local => {
                    bound(flow.index, m.reads.len)?
                }
                _ => return Err(Error::Malformed),
            }
        }
        for i in m.code_observations.checked(t.code_observation_count())? {
            let c = t.code_observation(i).ok_or(Error::Malformed)?;
            match c.kind {
                CodeKind::Method => method_bound(MethodId(c.index), t.method_count())?,
                CodeKind::Class => bound(c.index, bounds.classes)?,
            }
        }
        for i in m.reads.checked(t.read_count())? {
            storage_bound(t.read(i).ok_or(Error::Malformed)?, m, bounds)?;
        }
        for i in m.writes.checked(t.write_count())? {
            storage_bound(t.write(i).ok_or(Error::Malformed)?, m, bounds)?;
        }
        for i in m.escapes.checked(t.escape_count())? {
            let e = t.escape(i).ok_or(Error::Malformed)?;
            origin_bound(e.origin, m)?;
            match e.sink {
                EscapeSink::Return if e.index == 0 => (),
                EscapeSink::Heap => bound(e.index, bounds.members)?,
                EscapeSink::Callback => bound(e.index, m.calls.len)?,
                EscapeSink::External => bound(e.index, bounds.externals)?,
                EscapeSink::Unknown if e.index == 0 && m.top.contains(Channel::Escapes) => (),
                _ => return Err(Error::Malformed),
            }
        }
        for i in m.initializes.checked(t.initialize_count())? {
            method_bound(t.initialize(i).ok_or(Error::Malformed)?, t.method_count())?;
        }
        for i in m.throws.checked(t.throw_count())? {
            bound(t.r#throw(i).ok_or(Error::Malformed)?, bounds.exceptions)?;
        }
        for i in m.synchronizes.checked(t.synchronize_count())? {
            let s = t.synchronize(i).ok_or(Error::Malformed)?;
            origin_bound(s.base, m)?;
            if matches!(
                s.kind,
                SyncKind::AcquireFence | SyncKind::ReleaseFence | SyncKind::FullFence
            ) && s.base != Origin::ANY
            {
                return Err(Error::Malformed);
            }
        }
        for i in m.external.checked(t.external_count())? {
            bound(t.external(i).ok_or(Error::Malformed)?.key, bounds.externals)?;
        }
        for i in m.flows.checked(t.flow_count())? {
            let flow = t.flow(i).ok_or(Error::Malformed)?;
            origin_bound(flow.source, m)?;
            match flow.sink {
                FlowSink::Return | FlowSink::Control if flow.via == NONE && flow.index == 0 => (),
                FlowSink::CallReceiver | FlowSink::CallArgument | FlowSink::CallCapture => {
                    bound(flow.via, m.calls.len)?;
                    let call = t
                        .call(m.calls.start as usize + flow.via as usize)
                        .ok_or(Error::Malformed)?;
                    match flow.sink {
                        FlowSink::CallReceiver if flow.index == 0 => (),
                        FlowSink::CallArgument => bound(flow.index, call.arguments.len)?,
                        FlowSink::CallCapture => bound(flow.index, call.captures.len)?,
                        _ => return Err(Error::Malformed),
                    }
                }
                FlowSink::HeapWrite if flow.index == 0 => bound(flow.via, m.writes.len)?,
                FlowSink::Throw if flow.via == NONE => bound(flow.index, bounds.exceptions)?,
                FlowSink::External if flow.index == 0 => bound(flow.via, m.external.len)?,
                _ => return Err(Error::Malformed),
            }
        }
    }
    let mut previous_bridge = None;
    for i in 0..t.callable_bridge_count() {
        let bridge = t.callable_bridge(i).ok_or(Error::Malformed)?;
        let key = (bridge.creation, bridge.sam);
        if previous_bridge.is_some_and(|previous| previous >= key) {
            return Err(Error::Malformed);
        }
        previous_bridge = Some(key);
        let creation = t.creation(bridge.creation as usize).ok_or(Error::Bounds)?;
        bound(bridge.sam, bounds.sams)?;
        bound(bridge.proof, bounds.bridge_proofs)?;
        if creation.sam == NONE || creation.sam == bridge.sam {
            return Err(Error::Malformed);
        }
        method_bound(bridge.implementation, t.method_count())?;
        let implementation = t
            .method(bridge.implementation.0 as usize)
            .ok_or(Error::Malformed)?;
        if implementation.subject.kind != SubjectKind::ForeignMethod {
            return Err(Error::Malformed);
        }
        // The real default bridge receives the callable object as its receiver,
        // not the creator implementation's lexical receiver/capture frame.
        if implementation.captures != 0
            || implementation.arity != t.sam_arity(bridge.sam as usize).ok_or(Error::Malformed)?
        {
            return Err(Error::Arity);
        }
    }
    Ok(())
}

pub fn validate(data: &CapsuleData, bounds: RefBounds, limits: Limits) -> Result<(), Error> {
    validate_tables(data, bounds, limits)
}

impl CapsuleData {
    pub fn owned_bytes(&self) -> Result<usize, Error> {
        let mut bytes = 0usize;
        macro_rules! charge { ($($field:ident : $ty:ty),+ $(,)?) => { $(bytes = bytes.checked_add(self.$field.capacity().checked_mul(size_of::<$ty>()).ok_or(Error::Overflow)?).ok_or(Error::Overflow)?;)+ }; }
        charge!(methods:MethodRow, calls:CallRow, origins:Origin, callable_values:ValueRef, sam_arities:u32, creations:CallableCreation, callable_bridges:CallableBridge, value_flows:ValueFlow, code_observations:CodeRef,
            reads:StorageRef, writes:StorageRef, escapes:EscapeRef, initializes:MethodId,
            throws:u32, synchronizes:SyncRef, external:ExternalRef, flows:FlowRef);
        Ok(bytes)
    }
}

/// Immutable structurally validated ownership. No method here issues a semantic
/// certificate or permits a mutable DTO to replace already checked rows.
pub struct Capsules {
    data: CapsuleData,
    bounds: RefBounds,
}
impl Capsules {
    pub fn new(data: CapsuleData, bounds: RefBounds, limits: Limits) -> Result<Self, Error> {
        if data.owned_bytes()? > limits.max_bytes {
            return Err(Error::Budget);
        }
        validate(&data, bounds, limits)?;
        Ok(Self { data, bounds })
    }
    pub fn data(&self) -> &CapsuleData {
        &self.data
    }
    pub fn bounds(&self) -> RefBounds {
        self.bounds
    }
    pub fn len(&self) -> usize {
        self.data.methods.len()
    }
    pub fn is_empty(&self) -> bool {
        self.data.methods.is_empty()
    }
    pub fn owned_bytes(&self) -> usize {
        self.data.owned_bytes().expect("validated capacities")
    }
    pub fn view(&self, id: MethodId) -> Result<MethodView<'_>, Error> {
        let row = *self.data.methods.get(id.0 as usize).ok_or(Error::Bounds)?;
        macro_rules! slice {
            ($field:ident) => {
                &self.data.$field[row.$field.checked(self.data.$field.len())?]
            };
        }
        Ok(MethodView {
            row,
            calls: slice!(calls),
            origins: &self.data.origins,
            callable_values: &self.data.callable_values,
            creations: slice!(creations),
            value_flows: slice!(value_flows),
            code_observations: slice!(code_observations),
            reads: slice!(reads),
            writes: slice!(writes),
            escapes: slice!(escapes),
            initializes: slice!(initializes),
            throws: slice!(throws),
            synchronizes: slice!(synchronizes),
            external: slice!(external),
            flows: slice!(flows),
        })
    }
}

#[derive(Clone, Copy)]
pub struct MethodView<'a> {
    pub row: MethodRow,
    pub calls: &'a [CallRow],
    pub origins: &'a [Origin],
    pub callable_values: &'a [ValueRef],
    pub creations: &'a [CallableCreation],
    pub value_flows: &'a [ValueFlow],
    pub code_observations: &'a [CodeRef],
    pub reads: &'a [StorageRef],
    pub writes: &'a [StorageRef],
    pub escapes: &'a [EscapeRef],
    pub initializes: &'a [MethodId],
    pub throws: &'a [u32],
    pub synchronizes: &'a [SyncRef],
    pub external: &'a [ExternalRef],
    pub flows: &'a [FlowRef],
}

/// Checked actual origins in the caller namespace. There is deliberately no
/// ContextId, ambient root, or recursive allocation history in an origin.
pub struct Frame<'a> {
    callee: MethodRow,
    receiver: Origin,
    arguments: &'a [Origin],
    captures: &'a [Origin],
    escaped_fresh: &'a [u32],
    caller: MethodRow,
}
impl<'a> Frame<'a> {
    pub fn new(
        callee: MethodRow,
        caller: MethodRow,
        receiver: Origin,
        arguments: &'a [Origin],
        captures: &'a [Origin],
        escaped_fresh: &'a [u32],
    ) -> Result<Self, Error> {
        if arguments.len() != callee.arity as usize || captures.len() != callee.captures as usize {
            return Err(Error::Arity);
        }
        origin_bound(receiver, caller)?;
        for origin in arguments.iter().chain(captures) {
            origin_bound(*origin, caller)?;
        }
        let mut previous = None;
        for index in escaped_fresh {
            bound(*index, caller.fresh_sites)?;
            if previous.is_some_and(|p| p >= *index) {
                return Err(Error::Malformed);
            }
            previous = Some(*index);
        }
        Ok(Self {
            callee,
            receiver,
            arguments,
            captures,
            escaped_fresh,
            caller,
        })
    }
    fn map(&self, origin: Origin) -> Result<Origin, Error> {
        match origin.kind {
            OriginKind::Any if origin.index == 0 => Ok(Origin::ANY),
            OriginKind::Receiver if origin.index == 0 => Ok(self.receiver),
            OriginKind::Argument => self
                .arguments
                .get(origin.index as usize)
                .copied()
                .ok_or(Error::Arity),
            OriginKind::Capture => self
                .captures
                .get(origin.index as usize)
                .copied()
                .ok_or(Error::Arity),
            // A callee-local fresh site is not a globally unique object. A later
            // producer may supply a checked fresh mapping; v1 widens it.
            OriginKind::Fresh => Ok(Origin::ANY),
            _ => Err(Error::Malformed),
        }
    }
    pub fn caller(&self) -> MethodRow {
        self.caller
    }
}

#[derive(Default)]
pub struct SubstitutionScratch {
    calls: Vec<CallRow>,
    origins: Vec<Origin>,
    reads: Vec<StorageRef>,
    writes: Vec<StorageRef>,
    escapes: Vec<EscapeRef>,
    synchronizes: Vec<SyncRef>,
    flows: Vec<FlowRef>,
    escaped_fresh: Vec<u32>,
}

#[derive(Clone, Copy)]
struct Needs {
    calls: usize,
    origins: usize,
    reads: usize,
    writes: usize,
    escapes: usize,
    synchronizes: usize,
    flows: usize,
    escaped_fresh: usize,
}
fn needs(view: MethodView<'_>, frame: &Frame<'_>) -> Result<Needs, Error> {
    let mut origins = 0usize;
    for call in view.calls {
        origins = origins
            .checked_add(call.arguments.len as usize)
            .and_then(|x| x.checked_add(call.captures.len as usize))
            .ok_or(Error::Overflow)?;
    }
    Ok(Needs {
        calls: view.calls.len(),
        origins,
        reads: view.reads.len(),
        writes: view.writes.len(),
        escapes: view.escapes.len(),
        synchronizes: view.synchronizes.len(),
        flows: view.flows.len(),
        escaped_fresh: frame
            .escaped_fresh
            .len()
            .checked_add(view.escapes.len())
            .ok_or(Error::Overflow)?,
    })
}
fn growth(capacity: usize, need: usize) -> Result<usize, Error> {
    if capacity >= need {
        Ok(capacity)
    } else {
        need.max(4)
            .checked_next_power_of_two()
            .ok_or(Error::Overflow)
    }
}
impl SubstitutionScratch {
    pub fn owned_bytes(&self) -> usize {
        self.calls.capacity() * size_of::<CallRow>()
            + self.origins.capacity() * size_of::<Origin>()
            + (self.reads.capacity() + self.writes.capacity()) * size_of::<StorageRef>()
            + self.escapes.capacity() * size_of::<EscapeRef>()
            + self.synchronizes.capacity() * size_of::<SyncRef>()
            + self.flows.capacity() * size_of::<FlowRef>()
            + self.escaped_fresh.capacity() * size_of::<u32>()
    }
    /// All capacity growth occurs here, after a conservative checked charge.
    /// `substitute_into` never reserves and errors if this was not called.
    pub fn reserve_for(
        &mut self,
        view: MethodView<'_>,
        frame: &Frame<'_>,
        limits: Limits,
    ) -> Result<(), Error> {
        let n = needs(view, frame)?;
        let mut bytes = 0usize;
        let mut rows = 0usize;
        macro_rules! estimate { ($($field:ident : $ty:ty),+ $(,)?) => { $(let count = growth(self.$field.capacity(), n.$field)?; rows=rows.checked_add(count).ok_or(Error::Overflow)?; bytes=bytes.checked_add(count.checked_mul(size_of::<$ty>()).ok_or(Error::Overflow)?).ok_or(Error::Overflow)?;)+ }; }
        estimate!(calls:CallRow,origins:Origin,reads:StorageRef,writes:StorageRef,escapes:EscapeRef,synchronizes:SyncRef,flows:FlowRef,escaped_fresh:u32);
        if rows > limits.max_rows || bytes > limits.max_bytes {
            return Err(Error::Budget);
        }
        macro_rules! reserve { ($($field:ident),+ $(,)?) => { $(let wanted=growth(self.$field.capacity(),n.$field)?; if wanted>self.$field.capacity() { self.$field.try_reserve_exact(wanted-self.$field.len()).map_err(|_|Error::Budget)?; })+ }; }
        reserve!(
            calls,
            origins,
            reads,
            writes,
            escapes,
            synchronizes,
            flows,
            escaped_fresh
        );
        if self.owned_bytes() > limits.max_bytes {
            return Err(Error::Budget);
        }
        Ok(())
    }
}

pub struct Substituted<'a> {
    pub top: TopMask,
    pub calls: &'a [CallRow],
    pub origins: &'a [Origin],
    pub code_observations: &'a [CodeRef],
    pub reads: &'a [StorageRef],
    pub writes: &'a [StorageRef],
    pub escapes: &'a [EscapeRef],
    pub initializes: &'a [MethodId],
    pub throws: &'a [u32],
    pub synchronizes: &'a [SyncRef],
    pub external: &'a [ExternalRef],
    pub flows: &'a [FlowRef],
}

/// Instantiate one method in caller coordinates. Every escape is considered
/// before any storage row, so row order cannot falsely preserve a fresh region.
/// Caller-reserved capacities make the warmed path allocation-free.
pub fn substitute_into<'a>(
    view: MethodView<'a>,
    frame: &Frame<'_>,
    scratch: &'a mut SubstitutionScratch,
) -> Result<Substituted<'a>, Error> {
    // Data-only compatibility helper cannot rebind method-local callable cells.
    // The v2 callable engine resolves those through a checked ValueFrame.
    if !view.creations.is_empty()
        || !view.value_flows.is_empty()
        || view.calls.iter().any(|c| {
            !matches!(c.target, CallTarget::Direct(_))
                || !matches!(
                    c.receiver_value.kind,
                    ValueKind::Unknown | ValueKind::Constant
                )
        })
    {
        return Err(Error::Malformed);
    }
    for call in view.calls {
        for index in call
            .arguments
            .checked(view.callable_values.len())?
            .chain(call.captures.checked(view.callable_values.len())?)
        {
            if !matches!(
                view.callable_values[index].kind,
                ValueKind::Unknown | ValueKind::Constant
            ) {
                return Err(Error::Malformed);
            }
        }
    }
    if frame.callee != view.row {
        return Err(Error::Malformed);
    }
    let n = needs(view, frame)?;
    macro_rules! capacity { ($($field:ident),+ $(,)?) => { $(if scratch.$field.capacity()<n.$field { return Err(Error::Capacity); })+ }; }
    capacity!(
        calls,
        origins,
        reads,
        writes,
        escapes,
        synchronizes,
        flows,
        escaped_fresh
    );
    scratch.calls.clear();
    scratch.origins.clear();
    scratch.reads.clear();
    scratch.writes.clear();
    scratch.escapes.clear();
    scratch.synchronizes.clear();
    scratch.flows.clear();
    scratch.escaped_fresh.clear();
    scratch.escaped_fresh.extend_from_slice(frame.escaped_fresh);
    let mut widen_all_fresh = view.row.top.contains(Channel::Escapes);
    for escape in view.escapes {
        let mapped = frame.map(escape.origin)?;
        if mapped.kind == OriginKind::Any {
            widen_all_fresh = true;
        }
        if mapped.kind == OriginKind::Fresh {
            scratch.escaped_fresh.push(mapped.index);
        }
    }
    scratch.escaped_fresh.sort_unstable();
    scratch.escaped_fresh.dedup();
    let map = |origin: Origin| -> Result<Origin, Error> {
        let mapped = frame.map(origin)?;
        if mapped.kind == OriginKind::Fresh
            && (widen_all_fresh || scratch.escaped_fresh.binary_search(&mapped.index).is_ok())
        {
            Ok(Origin::ANY)
        } else {
            Ok(mapped)
        }
    };
    for call in view.calls {
        let start = u32::try_from(scratch.origins.len()).map_err(|_| Error::Overflow)?;
        for i in call.arguments.checked(view.origins.len())? {
            scratch.origins.push(map(view.origins[i])?);
        }
        let arguments = Range {
            start,
            len: call.arguments.len,
        };
        let start = u32::try_from(scratch.origins.len()).map_err(|_| Error::Overflow)?;
        for i in call.captures.checked(view.origins.len())? {
            scratch.origins.push(map(view.origins[i])?);
        }
        scratch.calls.push(CallRow {
            receiver: map(call.receiver)?,
            arguments,
            captures: Range {
                start,
                len: call.captures.len,
            },
            ..*call
        });
    }
    for row in view.reads {
        scratch.reads.push(StorageRef {
            base: map(row.base)?,
            ..*row
        });
    }
    for row in view.writes {
        scratch.writes.push(StorageRef {
            base: map(row.base)?,
            ..*row
        });
    }
    for row in view.escapes {
        scratch.escapes.push(EscapeRef {
            origin: map(row.origin)?,
            ..*row
        });
    }
    for row in view.synchronizes {
        scratch.synchronizes.push(SyncRef {
            base: map(row.base)?,
            ..*row
        });
    }
    for row in view.flows {
        scratch.flows.push(FlowRef {
            source: map(row.source)?,
            ..*row
        });
    }
    Ok(Substituted {
        top: view.row.top,
        calls: &scratch.calls,
        origins: &scratch.origins,
        code_observations: view.code_observations,
        reads: &scratch.reads,
        writes: &scratch.writes,
        escapes: &scratch.escapes,
        initializes: view.initializes,
        throws: view.throws,
        synchronizes: &scratch.synchronizes,
        external: view.external,
        flows: &scratch.flows,
    })
}

/// A finite channel union. Overflow changes the channel to TOP instead of
/// retaining a truncated set that a consumer could mistake for exhaustive.
pub struct BoundedSet<T> {
    values: Vec<T>,
    top: bool,
    max_members: usize,
}
impl<T: Ord + Copy> BoundedSet<T> {
    pub fn new(max_members: usize) -> Self {
        Self {
            values: Vec::new(),
            top: false,
            max_members,
        }
    }
    pub fn reserve(&mut self, max_bytes: usize) -> Result<(), Error> {
        let capacity = growth(self.values.capacity(), self.max_members)?;
        if capacity
            .checked_mul(size_of::<T>())
            .ok_or(Error::Overflow)?
            > max_bytes
        {
            return Err(Error::Budget);
        }
        if capacity > self.values.capacity() {
            self.values
                .try_reserve_exact(capacity - self.values.len())
                .map_err(|_| Error::Budget)?;
        }
        Ok(())
    }
    pub fn is_top(&self) -> bool {
        self.top
    }
    pub fn values(&self) -> &[T] {
        &self.values
    }
    pub fn owned_bytes(&self) -> usize {
        self.values.capacity() * size_of::<T>()
    }
    pub fn set_top(&mut self) {
        self.top = true;
        self.values.clear();
    }
    pub fn insert(&mut self, value: T) -> Result<(), Error> {
        if self.top {
            return Ok(());
        }
        match self.values.binary_search(&value) {
            Ok(_) => Ok(()),
            Err(_) if self.values.len() >= self.max_members => {
                self.set_top();
                Ok(())
            }
            Err(_) if self.values.len() == self.values.capacity() => {
                self.set_top();
                Err(Error::Capacity)
            }
            Err(index) => {
                self.values.insert(index, value);
                Ok(())
            }
        }
    }
    pub fn join(&mut self, other: &Self) -> Result<(), Error> {
        if other.top {
            self.set_top();
            return Ok(());
        }
        for value in &other.values {
            self.insert(*value)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
