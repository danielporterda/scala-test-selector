use crate::{SourceIndex, SubjectState};
use selector_effects as e;
use selector_facts::OperationRecord;
use selector_types::*;

#[derive(Clone, Copy, Debug)]
pub struct MemberBinding {
    pub key: u32,
    pub canonical: bool,
}
/// Key counts and equality are supplied by the separately admitted linker. A
/// source compiler spelling is not a native field-alias proof.
pub trait MemberKeys {
    fn count(&self) -> u32;
    fn field(&self, symbol: SymbolId, static_field: bool) -> Option<MemberBinding>;
}
/// Artifact-local compiler IDs are retained as *noncanonical* keys by default.
pub struct FactMembers {
    pub symbols: u32,
}
impl MemberKeys for FactMembers {
    fn count(&self) -> u32 {
        self.symbols
    }
    fn field(&self, symbol: SymbolId, _: bool) -> Option<MemberBinding> {
        (symbol.0 < self.symbols).then_some(MemberBinding {
            key: symbol.0,
            canonical: false,
        })
    }
}
/// Exact SAM identities are supplied by the separately admitted linker. An
/// implementation's argument count alone never proves FunctionN/SAM identity.
pub trait SamKeys {
    fn arities(&self) -> &[u32];
    fn creation(&self, site: SitePin, implementation: NodeId) -> Option<u32>;
    fn invocation(&self, site: SitePin) -> Option<u32>;
}
pub struct NoSams;
impl SamKeys for NoSams {
    fn arities(&self) -> &[u32] {
        &[]
    }
    fn creation(&self, _: SitePin, _: NodeId) -> Option<u32> {
        None
    }
    fn invocation(&self, _: SitePin) -> Option<u32> {
        None
    }
}
#[derive(Clone, Copy, Debug)]
pub struct SourcePin {
    pub node: NodeId,
    pub body: BodyId,
    pub symbol: SymbolId,
    pub file: FileId,
    pub context: StrId,
    pub source_hash: ContentHash,
    pub body_hash: ContentHash,
    pub flags: u32,
}
#[derive(Clone, Copy, Debug)]
pub struct SitePin {
    pub node: NodeId,
    pub body: BodyId,
    pub operation: OperationId,
    pub span: Span,
    pub flags: u32,
    pub target: SymbolId,
    pub opcode: Opcode,
}
#[derive(Clone, Copy, Debug)]
pub struct ClosureBinding {
    pub method: e::MethodId,
    pub operation: OperationId,
    pub fresh: u32,
    pub target: Option<e::MethodId>,
    /// Stable creation-row index. Origin-column canonicalization can rebase
    /// creation captures without duplicating ranges in this sidecar.
    pub creation: Option<u32>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PendingKind {
    MissingRecipe,
    Target,
    VirtualDispatch,
    Callback,
    NoncanonicalMember,
    CaptureEscape,
}
#[derive(Clone, Copy, Debug)]
pub struct PendingRef {
    pub caller: e::MethodId,
    pub operation: OperationId,
    pub symbol: SymbolId,
    pub kind: PendingKind,
}
#[derive(Clone, Copy, Debug)]
pub struct ProjectionLimits {
    pub max_value_ids: usize,
    pub max_rows: usize,
    pub max_bytes: usize,
}
impl Default for ProjectionLimits {
    fn default() -> Self {
        Self {
            max_value_ids: 1_000_000,
            max_rows: 8_000_000,
            max_bytes: 512 << 20,
        }
    }
}
pub struct SourceProjection {
    pub data: e::CapsuleData,
    pub bounds: e::RefBounds,
    pub sources: Vec<SourcePin>,
    pub sites: Vec<SitePin>,
    pub closures: Vec<ClosureBinding>,
    pub pending: Vec<PendingRef>,
    /// True until an independent producer supplies a verified coverage token.
    /// This producer has no API that suppresses guards using debug attributes.
    pub compiled_coverage_unadmitted: bool,
}
#[derive(Clone, Copy)]
struct Cell {
    origin: e::Origin,
    value: e::ValueRef,
    closure: Option<u32>,
}
impl Cell {
    const ANY: Self = Self {
        origin: e::Origin::ANY,
        value: e::ValueRef::UNKNOWN,
        closure: None,
    };
}
#[derive(Default)]
struct Scratch {
    values: Vec<Cell>,
}
impl Scratch {
    fn clear(&mut self, count: usize) -> Result<(), Error> {
        self.values.clear();
        self.values
            .try_reserve(count)
            .map_err(|_| Error::Limit("source value origins"))?;
        self.values.resize(count, Cell::ANY);
        if !self.values.is_empty() {
            self.values[0].origin = e::Origin::RECEIVER;
            self.values[0].value = e::ValueRef::RECEIVER;
        }
        Ok(())
    }
    fn get(&self, value: ValueId) -> Cell {
        if value.is_none() {
            Cell::ANY
        } else {
            self.values.get(value.index()).copied().unwrap_or(Cell::ANY)
        }
    }
    fn put(&mut self, value: ValueId, cell: Cell) -> Result<(), Error> {
        if !value.is_none() {
            *self
                .values
                .get_mut(value.index())
                .ok_or(Error::Invalid("source local origin"))? = cell;
        }
        Ok(())
    }
}
fn number(n: usize) -> Result<u32, Error> {
    u32::try_from(n).map_err(|_| Error::Limit("source capsule IDs"))
}
fn tail(start: usize, end: usize) -> Result<e::Range, Error> {
    Ok(e::Range {
        start: number(start)?,
        len: number(end - start)?,
    })
}
fn append_origins(
    out: &mut SourceProjection,
    origins: impl IntoIterator<Item = Cell>,
) -> Result<e::Range, Error> {
    let start = out.data.origins.len();
    for cell in origins {
        out.data.origins.push(cell.origin);
        out.data.callable_values.push(cell.value);
    }
    tail(start, out.data.origins.len())
}
fn pending(
    out: &mut SourceProjection,
    method: e::MethodId,
    op: OperationId,
    symbol: SymbolId,
    kind: PendingKind,
) {
    out.pending.push(PendingRef {
        caller: method,
        operation: op,
        symbol,
        kind,
    });
}
fn target(index: &SourceIndex<'_>, symbol: SymbolId) -> Option<e::MethodId> {
    (!symbol.is_none())
        .then(|| index.graph.node_for_symbol(symbol))
        .flatten()
        .map(|id| e::MethodId(id.0))
}
fn observe(out: &mut SourceProjection, target: e::MethodId) {
    out.data.code_observations.push(e::CodeRef {
        kind: e::CodeKind::Method,
        index: target.0,
    });
}
fn flow(
    out: &mut SourceProjection,
    row: &mut e::MethodRow,
    origin: e::Origin,
    sink: e::FlowSink,
    via: u32,
    index: u32,
) {
    if origin.kind == e::OriginKind::Any {
        row.top.insert(e::Channel::Flows);
    }
    out.data.flows.push(e::FlowRef {
        source: origin,
        sink,
        via,
        index,
    });
}
fn capture_escape(
    out: &mut SourceProjection,
    row: &mut e::MethodRow,
    method: e::MethodId,
    operation: OperationId,
    cell: Cell,
) {
    if cell.closure.is_some() {
        // The binding is retained, but the core DTO does not yet express a
        // transitive capture graph or activation/lifetime authority.
        row.top.insert(e::Channel::Escapes);
        row.top.insert(e::Channel::Flows);
        pending(
            out,
            method,
            operation,
            SymbolId::NONE,
            PendingKind::CaptureEscape,
        );
    }
}
fn call(
    index: &SourceIndex<'_>,
    out: &mut SourceProjection,
    row: &mut e::MethodRow,
    scratch: &Scratch,
    method: e::MethodId,
    operation: OperationId,
    op: OperationRecord,
    target_method: Option<e::CallTarget>,
    kind: e::CallKind,
    receiver: e::Origin,
    receiver_value: e::ValueRef,
    captures: e::Range,
) -> Result<(), Error> {
    let Some(callee) = target_method else {
        row.top = e::TopMask::ALL;
        pending(out, method, operation, op.target, PendingKind::Target);
        return Ok(());
    };
    if kind != e::CallKind::Callback && !op.a.is_none() {
        capture_escape(out, row, method, operation, scratch.get(op.a));
    }
    let args = &index.facts.operands[op.arguments.range()];
    let arguments = append_origins(out, args.iter().map(|value| scratch.get(*value)))?;
    let ordinal = number(out.data.calls.len())? - row.calls.start;
    out.data.calls.push(e::CallRow {
        site: number(out.sites.len() - 1)?,
        target: callee,
        kind,
        receiver,
        receiver_value,
        result: if op.dest.is_none() {
            e::NONE
        } else {
            op.dest.0
        },
        arguments,
        captures,
    });
    if let e::CallTarget::Direct(id) = callee {
        observe(out, id);
    }
    flow(out, row, receiver, e::FlowSink::CallReceiver, ordinal, 0);
    for (i, value) in args.iter().enumerate() {
        let cell = scratch.get(*value);
        flow(
            out,
            row,
            cell.origin,
            e::FlowSink::CallArgument,
            ordinal,
            i as u32,
        );
        capture_escape(out, row, method, operation, cell);
    }
    for i in 0..captures.len {
        let origin = out.data.origins[(captures.start + i) as usize];
        flow(out, row, origin, e::FlowSink::CallCapture, ordinal, i);
    }
    if matches!(kind, e::CallKind::Virtual | e::CallKind::Interface) {
        // A compiler-selected contract is not a closed runtime target family.
        // The native/source linker must supply that family before this opens.
        row.top = e::TopMask::ALL;
        pending(
            out,
            method,
            operation,
            op.target,
            PendingKind::VirtualDispatch,
        );
    }
    row.top.insert(e::Channel::Throws); // Invocation/null/linkage behavior is not licensed here.
    Ok(())
}

/// Conservative default: no caller supplied an admitted SAM identity.
pub fn project_source(
    index: &SourceIndex<'_>,
    members: &impl MemberKeys,
    authority: u32,
    authorities: u32,
    limits: ProjectionLimits,
) -> Result<SourceProjection, Error> {
    project_source_with_sams(index, members, &NoSams, authority, authorities, limits)
}
fn copy_value(out: &mut SourceProjection, destination: ValueId, value: e::ValueRef) {
    if !destination.is_none() {
        out.data.value_flows.push(e::ValueFlow {
            kind: e::ValueFlowKind::Copy,
            value,
            index: destination.0,
        });
    }
}
fn local(value: ValueId) -> e::ValueRef {
    if value.is_none() {
        e::ValueRef::UNKNOWN
    } else {
        e::ValueRef::local(value.0)
    }
}
/// Enumerate local effects over an already validated complete node universe.
/// Finite rows coexist with TOP; this function never issues an omission proof.
pub fn project_source_with_sams(
    index: &SourceIndex<'_>,
    members: &impl MemberKeys,
    sams: &impl SamKeys,
    authority: u32,
    authorities: u32,
    limits: ProjectionLimits,
) -> Result<SourceProjection, Error> {
    if authority >= authorities {
        return Err(Error::Invalid("source capsule authority index"));
    }
    // Conservative preflight before allocating any output or value scratch.
    // This prototype may refuse a large but compressible recipe; it never
    // materializes one and truncates it into a falsely closed capsule.
    let mut upper_rows = index
        .subjects
        .len()
        .checked_add(sams.arities().len())
        .ok_or(Error::Limit("SAM rows"))?;
    let mut max_values = 1usize;
    for subject in &index.subjects {
        let ops = index.operations(subject.node)?;
        let captures = ops
            .iter()
            .filter(|o| o.opcode == Opcode::BindCallback)
            .map(|o| o.arguments.len as usize)
            .max()
            .unwrap_or(0);
        for op in ops {
            let extra = 30usize
                .checked_add(
                    (op.arguments.len as usize)
                        .checked_mul(6)
                        .ok_or(Error::Limit("source preflight operands"))?,
                )
                .and_then(|n| {
                    n.checked_add(if op.opcode == Opcode::InvokeCallback {
                        captures.checked_mul(2)?
                    } else {
                        0
                    })
                })
                .ok_or(Error::Limit("source preflight rows"))?;
            upper_rows = upper_rows
                .checked_add(extra)
                .ok_or(Error::Limit("source preflight rows"))?;
            for id in [op.dest, op.a, op.b]
                .into_iter()
                .chain(index.facts.operands[op.arguments.range()].iter().copied())
            {
                if !id.is_none() {
                    max_values = max_values.max(
                        id.index()
                            .checked_add(1)
                            .ok_or(Error::Limit("source preflight locals"))?,
                    );
                }
            }
        }
    }
    upper_rows = upper_rows
        .checked_add(
            index
                .graph
                .edges
                .len()
                .checked_mul(6)
                .ok_or(Error::Limit("source preflight lifecycle"))?,
        )
        .ok_or(Error::Limit("source preflight lifecycle"))?;
    let upper_bytes = upper_rows
        .checked_mul(std::mem::size_of::<e::MethodRow>())
        .and_then(|n| n.checked_mul(2)) // peak old+new Vec buffers during growth
        .and_then(|n| {
            n.checked_add(
                max_values
                    .checked_mul(std::mem::size_of::<Cell>())?
                    .checked_mul(2)?,
            )
        })
        .ok_or(Error::Limit("source preflight bytes"))?;
    if upper_rows > limits.max_rows
        || upper_bytes > limits.max_bytes
        || max_values > limits.max_value_ids
    {
        return Err(Error::Limit("source capsule preflight budget"));
    }
    let mut out = SourceProjection {
        data: e::CapsuleData::default(),
        bounds: e::RefBounds {
            fact_nodes: number(index.graph.nodes.len())?,
            authorities,
            members: members.count(),
            classes: number(index.facts.symbols.len())?,
            sams: number(sams.arities().len())?,
            ..Default::default()
        },
        sources: Vec::new(),
        sites: Vec::new(),
        closures: Vec::new(),
        pending: Vec::new(),
        compiled_coverage_unadmitted: true,
    };
    out.data.sam_arities.extend_from_slice(sams.arities());
    out.data
        .methods
        .try_reserve_exact(index.subjects.len())
        .map_err(|_| Error::Limit("source capsule methods"))?;
    for subject in &index.subjects {
        out.data.methods.push(e::MethodRow::unknown(
            e::SubjectRef {
                kind: e::SubjectKind::FactNode,
                index: subject.node.0,
            },
            authority,
            0,
            0,
            0,
        ));
    }
    let mut scratch = Scratch::default();
    for subject in index.subjects.iter().copied() {
        let method = e::MethodId(subject.node.0);
        let Some(body) = index.body(subject.node)? else {
            pending(
                &mut out,
                method,
                OperationId::NONE,
                index.graph.nodes[subject.node.index()].symbol,
                PendingKind::MissingRecipe,
            );
            continue;
        };
        let file = index.facts.files[body.file.index()];
        out.sources.push(SourcePin {
            node: subject.node,
            body: subject.body,
            symbol: body.symbol,
            file: body.file,
            context: file.context,
            source_hash: file.source_hash,
            body_hash: body.body_hash,
            flags: body.flags,
        });
        let ops = index.operations(subject.node)?;
        let mut max_value = 1usize;
        let mut ordinary = 0u32;
        let mut captured = 0u32;
        let mut fresh = 0u32;
        for op in ops {
            for id in [op.dest, op.a, op.b]
                .into_iter()
                .chain(index.facts.operands[op.arguments.range()].iter().copied())
            {
                if !id.is_none() {
                    max_value = max_value.max(
                        id.index()
                            .checked_add(1)
                            .ok_or(Error::Limit("source local IDs"))?,
                    );
                }
            }
            if op.opcode == Opcode::Parameter {
                if op.flags & 1 != 0 {
                    captured += 1;
                } else {
                    ordinary += 1;
                }
            }
            if matches!(
                op.opcode,
                Opcode::Allocate | Opcode::BindCallback | Opcode::PackSequence
            ) {
                fresh += 1;
            }
        }
        if max_value > limits.max_value_ids {
            return Err(Error::Limit("source local value count"));
        }
        scratch.clear(max_value)?;
        let mut row = out.data.methods[subject.node.index()];
        row.arity = ordinary;
        row.captures = captured;
        row.fresh_sites = fresh;
        row.locals = number(max_value)?;
        let creation_start = out.data.creations.len();
        let value_flow_start = out.data.value_flows.len();
        if subject.state == SubjectState::SourceRecipe && !subject.has_execution_guard {
            row.top = e::TopMask::NONE;
        }
        let starts = [
            out.data.calls.len(),
            out.data.code_observations.len(),
            out.data.reads.len(),
            out.data.writes.len(),
            out.data.escapes.len(),
            out.data.initializes.len(),
            out.data.throws.len(),
            out.data.synchronizes.len(),
            out.data.external.len(),
            out.data.flows.len(),
        ];
        row.calls.start = number(starts[0])?;
        let mut arg_index = 0;
        let mut capture_index = 0;
        let mut fresh_index = 0;
        for (offset, op) in ops.iter().copied().enumerate() {
            let operation = OperationId(body.operations.start + offset as u32);
            out.sites.push(SitePin {
                node: subject.node,
                body: subject.body,
                operation,
                span: op.span,
                flags: op.flags,
                target: op.target,
                opcode: op.opcode,
            });
            match op.opcode {
                Opcode::Parameter => {
                    let origin = if op.flags & 1 != 0 {
                        let value = e::Origin::capture(capture_index);
                        capture_index += 1;
                        value
                    } else {
                        let value = e::Origin::argument(arg_index);
                        arg_index += 1;
                        value
                    };
                    scratch.put(
                        op.dest,
                        Cell {
                            origin,
                            value: if op.flags & 1 != 0 {
                                e::ValueRef::capture(capture_index - 1)
                            } else {
                                e::ValueRef::argument(arg_index - 1)
                            },
                            closure: None,
                        },
                    )?;
                }
                Opcode::Constant => {
                    // Only an ordinary literal is proved noncallable. Opaque
                    // macro/result metadata stays unknown, even if scalar IR
                    // currently represents both with Constant.
                    let value = if op.flags == 0
                        && op.target.is_none()
                        && op.a.is_none()
                        && op.b.is_none()
                        && op.arguments.len == 0
                    {
                        e::ValueRef::CONSTANT
                    } else {
                        e::ValueRef::UNKNOWN
                    };
                    copy_value(&mut out, op.dest, value);
                    scratch.put(op.dest, Cell { value, ..Cell::ANY })?;
                }
                Opcode::Assign => {
                    let mut value = scratch.get(op.a);
                    copy_value(&mut out, op.dest, value.value);
                    value.value = local(op.dest);
                    scratch.put(op.dest, value)?;
                }
                Opcode::Join => {
                    let mut joined = false;
                    for v in [op.a, op.b]
                        .into_iter()
                        .filter(|v| !v.is_none())
                        .chain(index.facts.operands[op.arguments.range()].iter().copied())
                    {
                        joined = true;
                        copy_value(&mut out, op.dest, scratch.get(v).value);
                    }
                    if !joined {
                        copy_value(&mut out, op.dest, e::ValueRef::UNKNOWN);
                    }
                    let mut cells = [op.a, op.b]
                        .into_iter()
                        .filter(|v| !v.is_none())
                        .chain(index.facts.operands[op.arguments.range()].iter().copied())
                        .map(|id| scratch.get(id));
                    let first = cells.next().unwrap_or(Cell::ANY);
                    let value = if cells
                        .all(|cell| cell.origin == first.origin && cell.closure == first.closure)
                    {
                        first
                    } else {
                        Cell::ANY
                    };
                    if value.origin.kind == e::OriginKind::Any {
                        row.top.insert(e::Channel::Flows);
                    }
                    scratch.put(
                        op.dest,
                        Cell {
                            value: local(op.dest),
                            ..value
                        },
                    )?;
                }
                Opcode::Unknown => {
                    row.top = e::TopMask::ALL;
                    copy_value(&mut out, op.dest, e::ValueRef::UNKNOWN);
                    scratch.put(op.dest, Cell::ANY)?;
                }
                Opcode::BindCallback => {
                    let origin = e::Origin::fresh(fresh_index);
                    fresh_index += 1;
                    let callee = target(index, op.target);
                    let captures = if callee.is_some() && !op.dest.is_none() {
                        append_origins(
                            &mut out,
                            index.facts.operands[op.arguments.range()]
                                .iter()
                                .map(|v| scratch.get(*v)),
                        )?
                    } else {
                        e::Range::EMPTY
                    };
                    if let Some(callee) = callee {
                        observe(&mut out, callee);
                    } else {
                        row.top.insert(e::Channel::CodeObservations);
                    }
                    let receiver = if op.a.is_none() {
                        Cell {
                            origin: e::Origin::RECEIVER,
                            value: e::ValueRef::RECEIVER,
                            closure: None,
                        }
                    } else {
                        scratch.get(op.a)
                    };
                    let sam = callee
                        .and_then(|id| {
                            sams.creation(*out.sites.last().expect("site"), NodeId(id.0))
                        })
                        .unwrap_or(e::NONE);
                    let mut creation = None;
                    if let Some(implementation) = callee {
                        if !op.dest.is_none() {
                            creation = Some(number(out.data.creations.len())?);
                            out.data.creations.push(e::CallableCreation {
                                site: number(out.sites.len() - 1)?,
                                destination: op.dest.0,
                                implementation,
                                sam,
                                receiver: receiver.origin,
                                receiver_value: receiver.value,
                                captures,
                            });
                        }
                    } else {
                        copy_value(&mut out, op.dest, e::ValueRef::UNKNOWN);
                    }
                    let binding = number(out.closures.len())?;
                    out.closures.push(ClosureBinding {
                        method,
                        operation,
                        fresh: origin.index,
                        target: callee,
                        creation,
                    });
                    scratch.put(
                        op.dest,
                        Cell {
                            origin,
                            value: if callee.is_some() {
                                local(op.dest)
                            } else {
                                e::ValueRef::UNKNOWN
                            },
                            closure: Some(binding),
                        },
                    )?;
                }
                Opcode::InvokeCallback => {
                    let value = scratch.get(op.a);
                    let sam = sams
                        .invocation(*out.sites.last().expect("site"))
                        .unwrap_or(e::NONE);
                    if sam == e::NONE {
                        row.top.insert(e::Channel::Calls);
                        pending(
                            &mut out,
                            method,
                            operation,
                            op.target,
                            PendingKind::Callback,
                        );
                    }
                    call(
                        index,
                        &mut out,
                        &mut row,
                        &scratch,
                        method,
                        operation,
                        op,
                        Some(e::CallTarget::Callable {
                            value: value.value,
                            sam,
                        }),
                        e::CallKind::Callback,
                        value.origin,
                        value.value,
                        e::Range::EMPTY,
                    )?;
                    scratch.put(
                        op.dest,
                        Cell {
                            value: local(op.dest),
                            ..Cell::ANY
                        },
                    )?;
                }
                Opcode::Call
                | Opcode::VirtualCall
                | Opcode::DefaultArgument
                | Opcode::RegisterTest => {
                    let kind = if op.opcode == Opcode::VirtualCall && op.flags & OP_SUPER == 0 {
                        e::CallKind::Virtual
                    } else {
                        e::CallKind::Special
                    };
                    let receiver = if op.a.is_none() {
                        e::Origin::RECEIVER
                    } else {
                        scratch.get(op.a).origin
                    };
                    call(
                        index,
                        &mut out,
                        &mut row,
                        &scratch,
                        method,
                        operation,
                        op,
                        target(index, op.target).map(e::CallTarget::Direct),
                        kind,
                        receiver,
                        if op.a.is_none() {
                            e::ValueRef::RECEIVER
                        } else {
                            scratch.get(op.a).value
                        },
                        e::Range::EMPTY,
                    )?;
                    scratch.put(
                        op.dest,
                        Cell {
                            value: local(op.dest),
                            ..Cell::ANY
                        },
                    )?;
                }
                Opcode::Allocate | Opcode::Initialize => {
                    let receiver = if op.opcode == Opcode::Allocate {
                        let origin = e::Origin::fresh(fresh_index);
                        fresh_index += 1;
                        origin
                    } else if op.a.is_none() {
                        e::Origin::RECEIVER
                    } else {
                        scratch.get(op.a).origin
                    };
                    if target(index, op.target).is_some() {
                        // Source Allocate/Initialize targets constructors or
                        // Scala instance/trait initializers, not a proven
                        // zero-argument JVM class-init phase.
                        row.top.insert(e::Channel::Initializes);
                        pending(&mut out, method, operation, op.target, PendingKind::Target);
                    } else {
                        row.top = e::TopMask::ALL;
                        pending(&mut out, method, operation, op.target, PendingKind::Target);
                    }
                    if !op.target.is_none() {
                        let record = index.facts.symbols[op.target.index()];
                        let class = if record.kind == 21 {
                            record.owner
                        } else {
                            op.target
                        };
                        if !class.is_none() {
                            out.data.code_observations.push(e::CodeRef {
                                kind: e::CodeKind::Class,
                                index: class.0,
                            });
                        }
                    }
                    call(
                        index,
                        &mut out,
                        &mut row,
                        &scratch,
                        method,
                        operation,
                        op,
                        target(index, op.target).map(e::CallTarget::Direct),
                        e::CallKind::Special,
                        receiver,
                        if op.opcode == Opcode::Allocate {
                            e::ValueRef::UNKNOWN
                        } else if op.a.is_none() {
                            e::ValueRef::RECEIVER
                        } else {
                            scratch.get(op.a).value
                        },
                        e::Range::EMPTY,
                    )?;
                    scratch.put(
                        op.dest,
                        Cell {
                            origin: receiver,
                            // A constructed object may implement a callable interface;
                            // this producer has no closed hierarchy proof.
                            value: e::ValueRef::UNKNOWN,
                            closure: None,
                        },
                    )?;
                }
                Opcode::LoadField | Opcode::StoreField => {
                    let write = op.opcode == Opcode::StoreField;
                    let static_field = op.flags & OP_STATIC_FIELD != 0;
                    let base = if static_field {
                        e::Origin::ANY
                    } else {
                        scratch.get(op.a).origin
                    };
                    // Every load defines its destination, including an
                    // unresolved member: never reuse a stale closure/fresh ID.
                    if !write {
                        scratch.put(op.dest, Cell::ANY)?;
                    }
                    match members.field(op.target, static_field) {
                        Some(member) if member.key < members.count() => {
                            let storage = e::StorageRef {
                                kind: if static_field {
                                    e::StorageKind::StaticField
                                } else {
                                    e::StorageKind::InstanceField
                                },
                                member: member.key,
                                base,
                            };
                            if write {
                                let ordinal = number(out.data.writes.len() - starts[3])?;
                                out.data.writes.push(storage);
                                let value = scratch.get(op.b);
                                if member.canonical {
                                    out.data.value_flows.push(e::ValueFlow {
                                        kind: e::ValueFlowKind::Store,
                                        value: value.value,
                                        index: ordinal,
                                    });
                                }
                                flow(
                                    &mut out,
                                    &mut row,
                                    value.origin,
                                    e::FlowSink::HeapWrite,
                                    ordinal,
                                    0,
                                );
                                out.data.escapes.push(e::EscapeRef {
                                    origin: value.origin,
                                    sink: e::EscapeSink::Heap,
                                    index: member.key,
                                });
                                if value.origin.kind == e::OriginKind::Any {
                                    row.top.insert(e::Channel::Escapes);
                                }
                                capture_escape(&mut out, &mut row, method, operation, value);
                            } else {
                                let ordinal = number(out.data.reads.len() - starts[2])?;
                                out.data.reads.push(storage);
                                if member.canonical && !op.dest.is_none() {
                                    out.data.value_flows.push(e::ValueFlow {
                                        kind: e::ValueFlowKind::Load,
                                        value: local(op.dest),
                                        index: ordinal,
                                    });
                                    scratch.put(
                                        op.dest,
                                        Cell {
                                            value: local(op.dest),
                                            ..Cell::ANY
                                        },
                                    )?;
                                } else {
                                    copy_value(&mut out, op.dest, e::ValueRef::UNKNOWN);
                                    scratch.put(op.dest, Cell::ANY)?;
                                }
                            }
                            if !member.canonical {
                                row.top.insert(if write {
                                    e::Channel::Writes
                                } else {
                                    e::Channel::Reads
                                });
                                pending(
                                    &mut out,
                                    method,
                                    operation,
                                    op.target,
                                    PendingKind::NoncanonicalMember,
                                );
                            }
                        }
                        _ => {
                            if !write {
                                copy_value(&mut out, op.dest, e::ValueRef::UNKNOWN);
                            }
                            if write {
                                let value = scratch.get(op.b);
                                row.top.insert(e::Channel::Escapes);
                                row.top.insert(e::Channel::Flows);
                                out.data.escapes.push(e::EscapeRef {
                                    origin: value.origin,
                                    sink: e::EscapeSink::Unknown,
                                    index: 0,
                                });
                                capture_escape(&mut out, &mut row, method, operation, value);
                            }
                            row.top.insert(if write {
                                e::Channel::Writes
                            } else {
                                e::Channel::Reads
                            });
                            pending(
                                &mut out,
                                method,
                                operation,
                                op.target,
                                PendingKind::NoncanonicalMember,
                            );
                        }
                    }
                    // The current flat source record does not prove nonvolatile,
                    // nullness or exact static declaring-owner initialization.
                    row.top.insert(e::Channel::Synchronizes);
                    row.top.insert(e::Channel::Throws);
                    if static_field {
                        row.top.insert(e::Channel::Initializes);
                    }
                }
                Opcode::PackSequence => {
                    let origin = e::Origin::fresh(fresh_index);
                    fresh_index += 1;
                    let ordinal = number(out.data.writes.len() - starts[3])?;
                    out.data.writes.push(e::StorageRef {
                        kind: e::StorageKind::ArrayElements,
                        member: e::NONE,
                        base: origin,
                    });
                    for value in &index.facts.operands[op.arguments.range()] {
                        out.data.value_flows.push(e::ValueFlow {
                            kind: e::ValueFlowKind::Store,
                            value: scratch.get(*value).value,
                            index: ordinal,
                        });
                        flow(
                            &mut out,
                            &mut row,
                            scratch.get(*value).origin,
                            e::FlowSink::HeapWrite,
                            ordinal,
                            0,
                        );
                    }
                    row.top.insert(e::Channel::Escapes);
                    row.top.insert(e::Channel::Flows);
                    scratch.put(
                        op.dest,
                        Cell {
                            origin,
                            value: e::ValueRef::UNKNOWN,
                            closure: None,
                        },
                    )?;
                }
                Opcode::ReadElements => {
                    let read = number(out.data.reads.len() - starts[2])?;
                    out.data.reads.push(e::StorageRef {
                        kind: e::StorageKind::ArrayElements,
                        member: e::NONE,
                        base: scratch.get(op.a).origin,
                    });
                    row.top.insert(e::Channel::Flows);
                    row.top.insert(e::Channel::Throws);
                    if !op.dest.is_none() {
                        out.data.value_flows.push(e::ValueFlow {
                            kind: e::ValueFlowKind::Load,
                            value: local(op.dest),
                            index: read,
                        });
                    }
                    scratch.put(
                        op.dest,
                        Cell {
                            value: local(op.dest),
                            ..Cell::ANY
                        },
                    )?;
                }
                Opcode::Return => {
                    if op.a.is_none() {
                        continue;
                    }
                    let cell = scratch.get(op.a);
                    out.data.value_flows.push(e::ValueFlow {
                        kind: e::ValueFlowKind::Return,
                        value: cell.value,
                        index: 0,
                    });
                    out.data.escapes.push(e::EscapeRef {
                        origin: cell.origin,
                        sink: e::EscapeSink::Return,
                        index: 0,
                    });
                    if cell.origin.kind == e::OriginKind::Any {
                        row.top.insert(e::Channel::Escapes);
                    }
                    flow(
                        &mut out,
                        &mut row,
                        cell.origin,
                        e::FlowSink::Return,
                        e::NONE,
                        0,
                    );
                    capture_escape(&mut out, &mut row, method, operation, cell);
                }
            }
        }
        // Preserve unconditional model/lifecycle edges as finite calls. Their
        // original edge flags remain source graph provenance; no new activation
        // is inferred for operation-scoped dormant closure bindings.
        for (edge_id, edge) in index.graph.successors(subject.node) {
            if edge.operation.is_none()
                && edge.kind.is_execution()
                && edge.kind != EdgeKind::Guard
                && edge.flags & EDGE_UNKNOWN == 0
            {
                out.sites.push(SitePin {
                    node: subject.node,
                    body: subject.body,
                    operation: OperationId::NONE,
                    span: body.span,
                    flags: edge.flags,
                    target: index.graph.nodes[edge.target.index()].symbol,
                    opcode: Opcode::Call,
                });
                let callee = e::MethodId(edge.target.0);
                let target_body = index.graph.nodes[edge.target.index()].body;
                if !target_body.is_none()
                    && index.facts.bodies[target_body.index()].parameters.len != 0
                {
                    // The structural edge supplies no actual/capture operands.
                    // Preserve the edge but not a fabricated zero-argument call.
                    row.top = e::TopMask::ALL;
                    pending(
                        &mut out,
                        method,
                        OperationId::NONE,
                        index.graph.nodes[edge.target.index()].symbol,
                        PendingKind::Target,
                    );
                }
                observe(&mut out, callee);
                out.data.calls.push(e::CallRow {
                    site: number(out.sites.len() - 1)?,
                    target: e::CallTarget::Direct(callee),
                    kind: if edge.kind == EdgeKind::Callback {
                        e::CallKind::Callback
                    } else {
                        e::CallKind::Special
                    },
                    receiver: e::Origin::RECEIVER,
                    receiver_value: e::ValueRef::RECEIVER,
                    result: e::NONE,
                    arguments: e::Range::EMPTY,
                    captures: e::Range::EMPTY,
                });
                if edge.kind == EdgeKind::Initialize {
                    row.top.insert(e::Channel::Initializes);
                    pending(
                        &mut out,
                        method,
                        OperationId::NONE,
                        index.graph.nodes[edge.target.index()].symbol,
                        PendingKind::Target,
                    );
                }
                let _ = edge_id;
            }
        }
        row.creations = tail(creation_start, out.data.creations.len())?;
        row.value_flows = tail(value_flow_start, out.data.value_flows.len())?;
        row.calls = tail(starts[0], out.data.calls.len())?;
        row.code_observations = tail(starts[1], out.data.code_observations.len())?;
        row.reads = tail(starts[2], out.data.reads.len())?;
        row.writes = tail(starts[3], out.data.writes.len())?;
        row.escapes = tail(starts[4], out.data.escapes.len())?;
        row.initializes = tail(starts[5], out.data.initializes.len())?;
        row.throws = tail(starts[6], out.data.throws.len())?;
        row.synchronizes = tail(starts[7], out.data.synchronizes.len())?;
        row.external = tail(starts[8], out.data.external.len())?;
        row.flows = tail(starts[9], out.data.flows.len())?;
        out.data.methods[subject.node.index()] = row;
        let rows = out.sites.len()
            + out.closures.len()
            + out.pending.len()
            + out.sources.len()
            + out.data.methods.len()
            + out.data.calls.len()
            + out.data.origins.len()
            + out.data.callable_values.len()
            + out.data.creations.len()
            + out.data.value_flows.len()
            + out.data.sam_arities.len()
            + out.data.code_observations.len()
            + out.data.reads.len()
            + out.data.writes.len()
            + out.data.escapes.len()
            + out.data.initializes.len()
            + out.data.flows.len();
        if rows > limits.max_rows
            || out
                .data
                .owned_bytes()
                .map_err(|_| Error::Limit("source table bytes"))?
                > limits.max_bytes
        {
            return Err(Error::Limit("source capsule output"));
        }
    }
    out.bounds.sites = number(out.sites.len())?;
    e::validate(
        &out.data,
        out.bounds,
        e::Limits {
            max_methods: limits.max_rows,
            max_rows: limits.max_rows,
            max_bytes: limits.max_bytes,
        },
    )
    .map_err(|_| Error::Invalid("source capsule DTO validation"))?;
    Ok(out)
}
