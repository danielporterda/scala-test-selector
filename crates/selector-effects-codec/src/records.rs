//! Explicit scalar codecs; no Rust layout casts or per-record allocation.
use crate::keys::*;
use crate::wire::{Cursor, Row, row};
use selector_effects::*;
use std::io::{self, Write};

fn range(r: &mut Cursor<'_>) -> Range {
    Range {
        start: r.u32(),
        len: r.u32(),
    }
}
fn put_range<const N: usize>(r: &mut Row<N>, v: Range) {
    r.u32(v.start);
    r.u32(v.len);
}
fn origin(r: &mut Cursor<'_>) -> Option<Origin> {
    Some(Origin {
        kind: OriginKind::from_u32(r.u32())?,
        index: r.u32(),
    })
}
fn put_origin<const N: usize>(r: &mut Row<N>, v: Origin) {
    r.u32(v.kind as u32);
    r.u32(v.index);
}
fn subject(r: &mut Cursor<'_>) -> Option<SubjectRef> {
    Some(SubjectRef {
        kind: SubjectKind::from_u32(r.u32())?,
        index: r.u32(),
    })
}
fn put_subject<const N: usize>(r: &mut Row<N>, v: SubjectRef) {
    r.u32(v.kind as u32);
    r.u32(v.index);
}

pub(crate) fn decode_text_range(mut r: Cursor<'_>) -> Option<TextRange> {
    Some(TextRange {
        start: r.u32(),
        len: r.u32(),
    })
}
pub(crate) fn encode_text_range(out: &mut dyn Write, v: TextRange) -> io::Result<()> {
    row::<8>(out, |r| {
        r.u32(v.start);
        r.u32(v.len);
    })
}

pub(crate) fn decode_context(mut r: Cursor<'_>) -> Option<ContextKey> {
    Some(ContextKey {
        name: r.u32(),
        inputs: Hash(r.hash()),
    })
}
pub(crate) fn encode_context(out: &mut dyn Write, v: ContextKey) -> io::Result<()> {
    row::<36>(out, |r| {
        r.u32(v.name);
        r.hash(&v.inputs.0);
    })
}

pub(crate) fn decode_provider(mut r: Cursor<'_>) -> Option<ProviderKey> {
    Some(ProviderKey {
        context: r.u32(),
        ordinal: r.u32(),
        kind: ProviderKind::decode(r.u32()).ok()?,
        path: r.u32(),
        digest: Hash(r.hash()),
    })
}
pub(crate) fn encode_provider(out: &mut dyn Write, v: ProviderKey) -> io::Result<()> {
    row::<48>(out, |r| {
        r.u32(v.context);
        r.u32(v.ordinal);
        r.u32(v.kind as u32);
        r.u32(v.path);
        r.hash(&v.digest.0);
    })
}

pub(crate) fn decode_foreign_method(mut r: Cursor<'_>) -> Option<ForeignMethod> {
    Some(ForeignMethod {
        context: r.u32(),
        provider: r.u32(),
        class: Hash(r.hash()),
        owner: r.u32(),
        name: r.u32(),
        descriptor: r.u32(),
        node: r.u32(),
        method_flags: r.u32(),
        resolved: r.boolean().ok()?,
    })
}
pub(crate) fn encode_foreign_method(out: &mut dyn Write, v: ForeignMethod) -> io::Result<()> {
    row::<64>(out, |r| {
        r.u32(v.context);
        r.u32(v.provider);
        r.hash(&v.class.0);
        r.u32(v.owner);
        r.u32(v.name);
        r.u32(v.descriptor);
        r.u32(v.node);
        r.u32(v.method_flags);
        r.u32(v.resolved as u32);
    })
}

pub(crate) fn decode_member(mut r: Cursor<'_>) -> Option<MemberKey> {
    Some(MemberKey {
        identity: MemberIdentity::decode(r.u32()).ok()?,
        fact_symbol: r.u32(),
        context: r.u32(),
        provider: r.u32(),
        class: Hash(r.hash()),
        owner: r.u32(),
        name: r.u32(),
        descriptor: r.u32(),
        kind: MemberKind::decode(r.u32()).ok()?,
        canonical: r.boolean().ok()?,
    })
}
pub(crate) fn encode_member(out: &mut dyn Write, v: MemberKey) -> io::Result<()> {
    row::<68>(out, |r| {
        r.u32(v.identity as u32);
        r.u32(v.fact_symbol);
        r.u32(v.context);
        r.u32(v.provider);
        r.hash(&v.class.0);
        r.u32(v.owner);
        r.u32(v.name);
        r.u32(v.descriptor);
        r.u32(v.kind as u32);
        r.u32(v.canonical as u32);
    })
}

pub(crate) fn decode_class(mut r: Cursor<'_>) -> Option<ClassKey> {
    Some(ClassKey {
        identity: ClassIdentity::decode(r.u32()).ok()?,
        fact_symbol: r.u32(),
        context: r.u32(),
        provider: r.u32(),
        class: Hash(r.hash()),
        owner: r.u32(),
        node: r.u32(),
        resolved: r.boolean().ok()?,
    })
}
pub(crate) fn encode_class(out: &mut dyn Write, v: ClassKey) -> io::Result<()> {
    row::<60>(out, |r| {
        r.u32(v.identity as u32);
        r.u32(v.fact_symbol);
        r.u32(v.context);
        r.u32(v.provider);
        r.hash(&v.class.0);
        r.u32(v.owner);
        r.u32(v.node);
        r.u32(v.resolved as u32);
    })
}

pub(crate) fn decode_authority(mut r: Cursor<'_>) -> Option<AuthorityKey> {
    Some(AuthorityKey {
        producer: Hash(r.hash()),
        contract: Hash(r.hash()),
        kind: AuthorityKind::decode(r.u32()).ok()?,
        name: r.u32(),
    })
}
pub(crate) fn encode_authority(out: &mut dyn Write, v: AuthorityKey) -> io::Result<()> {
    row::<72>(out, |r| {
        r.hash(&v.producer.0);
        r.hash(&v.contract.0);
        r.u32(v.kind as u32);
        r.u32(v.name);
    })
}

pub(crate) fn decode_exception_key(mut r: Cursor<'_>) -> Option<ExceptionKey> {
    Some(ExceptionKey {
        class: r.u32(),
        known: r.boolean().ok()?,
    })
}
pub(crate) fn encode_exception_key(out: &mut dyn Write, v: ExceptionKey) -> io::Result<()> {
    row::<8>(out, |r| {
        r.u32(v.class);
        r.u32(v.known as u32);
    })
}

pub(crate) fn decode_external_key(mut r: Cursor<'_>) -> Option<ExternalKey> {
    Some(ExternalKey {
        context: r.u32(),
        kind: r.u32(),
        name: r.u32(),
        digest: Hash(r.hash()),
        canonical: r.boolean().ok()?,
    })
}
pub(crate) fn encode_external_key(out: &mut dyn Write, v: ExternalKey) -> io::Result<()> {
    row::<48>(out, |r| {
        r.u32(v.context);
        r.u32(v.kind);
        r.u32(v.name);
        r.hash(&v.digest.0);
        r.u32(v.canonical as u32);
    })
}

pub(crate) fn decode_site(mut r: Cursor<'_>) -> Option<SiteKey> {
    Some(SiteKey {
        method: r.u32(),
        offset: r.u32(),
        fact_operation: r.u32(),
        kind: SiteKind::decode(r.u32()).ok()?,
    })
}
pub(crate) fn encode_site(out: &mut dyn Write, v: SiteKey) -> io::Result<()> {
    row::<16>(out, |r| {
        r.u32(v.method);
        r.u32(v.offset);
        r.u32(v.fact_operation);
        r.u32(v.kind as u32);
    })
}

pub(crate) fn decode_method(mut r: Cursor<'_>) -> Option<MethodRow> {
    Some(MethodRow {
        subject: subject(&mut r)?,
        authority: r.u32(),
        arity: r.u32(),
        captures: r.u32(),
        fresh_sites: r.u32(),
        top: TopMask::from_bits(r.u32())?,
        calls: range(&mut r),
        code_observations: range(&mut r),
        reads: range(&mut r),
        writes: range(&mut r),
        escapes: range(&mut r),
        initializes: range(&mut r),
        throws: range(&mut r),
        synchronizes: range(&mut r),
        external: range(&mut r),
        flows: range(&mut r),
        locals: r.u32(),
        creations: range(&mut r),
        value_flows: range(&mut r),
    })
}
pub(crate) fn encode_method(out: &mut dyn Write, v: MethodRow) -> io::Result<()> {
    row::<128>(out, |r| {
        put_subject(r, v.subject);
        r.u32(v.authority);
        r.u32(v.arity);
        r.u32(v.captures);
        r.u32(v.fresh_sites);
        r.u32(v.top.bits());
        put_range(r, v.calls);
        put_range(r, v.code_observations);
        put_range(r, v.reads);
        put_range(r, v.writes);
        put_range(r, v.escapes);
        put_range(r, v.initializes);
        put_range(r, v.throws);
        put_range(r, v.synchronizes);
        put_range(r, v.external);
        put_range(r, v.flows);
        r.u32(v.locals);
        put_range(r, v.creations);
        put_range(r, v.value_flows);
    })
}

pub(crate) fn decode_call(mut r: Cursor<'_>) -> Option<CallRow> {
    let site = r.u32();
    let tag = r.u32();
    let a = r.u32();
    let b = r.u32();
    let c = r.u32();
    let target = match tag {
        0 if b == 0 && c == 0 => CallTarget::Direct(MethodId(a)),
        1 => CallTarget::Callable {
            value: ValueRef {
                kind: ValueKind::from_u32(a)?,
                index: b,
            },
            sam: c,
        },
        _ => return None,
    };
    Some(CallRow {
        site,
        target,
        kind: CallKind::from_u32(r.u32())?,
        receiver: origin(&mut r)?,
        arguments: range(&mut r),
        captures: range(&mut r),
        receiver_value: value(&mut r)?,
        result: r.u32(),
    })
}
pub(crate) fn encode_call(out: &mut dyn Write, v: CallRow) -> io::Result<()> {
    row::<60>(out, |r| {
        r.u32(v.site);
        match v.target {
            CallTarget::Direct(id) => {
                r.u32(0);
                r.u32(id.0);
                r.u32(0);
                r.u32(0);
            }
            CallTarget::Callable { value, sam } => {
                r.u32(1);
                r.u32(value.kind as u32);
                r.u32(value.index);
                r.u32(sam);
            }
        }
        r.u32(v.kind as u32);
        put_origin(r, v.receiver);
        put_range(r, v.arguments);
        put_range(r, v.captures);
        put_value(r, v.receiver_value);
        r.u32(v.result);
    })
}
fn value(r: &mut Cursor<'_>) -> Option<ValueRef> {
    Some(ValueRef {
        kind: ValueKind::from_u32(r.u32())?,
        index: r.u32(),
    })
}
fn put_value<const N: usize>(r: &mut Row<N>, v: ValueRef) {
    r.u32(v.kind as u32);
    r.u32(v.index);
}
pub(crate) fn decode_value(mut r: Cursor<'_>) -> Option<ValueRef> {
    value(&mut r)
}
pub(crate) fn encode_value(out: &mut dyn Write, v: ValueRef) -> io::Result<()> {
    row::<8>(out, |r| put_value(r, v))
}
pub(crate) fn decode_creation(mut r: Cursor<'_>) -> Option<CallableCreation> {
    Some(CallableCreation {
        site: r.u32(),
        destination: r.u32(),
        implementation: MethodId(r.u32()),
        sam: r.u32(),
        receiver: origin(&mut r)?,
        receiver_value: value(&mut r)?,
        captures: range(&mut r),
    })
}
pub(crate) fn encode_creation(out: &mut dyn Write, v: CallableCreation) -> io::Result<()> {
    row::<40>(out, |r| {
        r.u32(v.site);
        r.u32(v.destination);
        r.u32(v.implementation.0);
        r.u32(v.sam);
        put_origin(r, v.receiver);
        put_value(r, v.receiver_value);
        put_range(r, v.captures);
    })
}
pub(crate) fn decode_value_flow(mut r: Cursor<'_>) -> Option<ValueFlow> {
    Some(ValueFlow {
        kind: ValueFlowKind::from_u32(r.u32())?,
        value: value(&mut r)?,
        index: r.u32(),
    })
}
pub(crate) fn encode_value_flow(out: &mut dyn Write, v: ValueFlow) -> io::Result<()> {
    row::<16>(out, |r| {
        r.u32(v.kind as u32);
        put_value(r, v.value);
        r.u32(v.index);
    })
}

pub(crate) fn decode_origin(mut r: Cursor<'_>) -> Option<Origin> {
    Some(Origin {
        kind: OriginKind::from_u32(r.u32())?,
        index: r.u32(),
    })
}
pub(crate) fn encode_origin(out: &mut dyn Write, v: Origin) -> io::Result<()> {
    row::<8>(out, |r| {
        r.u32(v.kind as u32);
        r.u32(v.index);
    })
}

pub(crate) fn decode_code_observation(mut r: Cursor<'_>) -> Option<CodeRef> {
    Some(CodeRef {
        kind: CodeKind::from_u32(r.u32())?,
        index: r.u32(),
    })
}
pub(crate) fn encode_code_observation(out: &mut dyn Write, v: CodeRef) -> io::Result<()> {
    row::<8>(out, |r| {
        r.u32(v.kind as u32);
        r.u32(v.index);
    })
}

pub(crate) fn decode_storage(mut r: Cursor<'_>) -> Option<StorageRef> {
    Some(StorageRef {
        kind: StorageKind::from_u32(r.u32())?,
        member: r.u32(),
        base: origin(&mut r)?,
    })
}
pub(crate) fn encode_storage(out: &mut dyn Write, v: StorageRef) -> io::Result<()> {
    row::<16>(out, |r| {
        r.u32(v.kind as u32);
        r.u32(v.member);
        put_origin(r, v.base);
    })
}

pub(crate) fn decode_escape(mut r: Cursor<'_>) -> Option<EscapeRef> {
    Some(EscapeRef {
        origin: origin(&mut r)?,
        sink: EscapeSink::from_u32(r.u32())?,
        index: r.u32(),
    })
}
pub(crate) fn encode_escape(out: &mut dyn Write, v: EscapeRef) -> io::Result<()> {
    row::<16>(out, |r| {
        put_origin(r, v.origin);
        r.u32(v.sink as u32);
        r.u32(v.index);
    })
}

pub(crate) fn decode_synchronize(mut r: Cursor<'_>) -> Option<SyncRef> {
    Some(SyncRef {
        kind: SyncKind::from_u32(r.u32())?,
        base: origin(&mut r)?,
    })
}
pub(crate) fn encode_synchronize(out: &mut dyn Write, v: SyncRef) -> io::Result<()> {
    row::<12>(out, |r| {
        r.u32(v.kind as u32);
        put_origin(r, v.base);
    })
}

pub(crate) fn decode_external(mut r: Cursor<'_>) -> Option<ExternalRef> {
    Some(ExternalRef {
        kind: ExternalKind::from_u32(r.u32())?,
        key: r.u32(),
    })
}
pub(crate) fn encode_external(out: &mut dyn Write, v: ExternalRef) -> io::Result<()> {
    row::<8>(out, |r| {
        r.u32(v.kind as u32);
        r.u32(v.key);
    })
}

pub(crate) fn decode_flow(mut r: Cursor<'_>) -> Option<FlowRef> {
    Some(FlowRef {
        source: origin(&mut r)?,
        sink: FlowSink::from_u32(r.u32())?,
        via: r.u32(),
        index: r.u32(),
    })
}
pub(crate) fn encode_flow(out: &mut dyn Write, v: FlowRef) -> io::Result<()> {
    row::<20>(out, |r| {
        put_origin(r, v.source);
        r.u32(v.sink as u32);
        r.u32(v.via);
        r.u32(v.index);
    })
}

pub(crate) fn decode_sam_key(mut r: Cursor<'_>) -> Option<SamKey> {
    Some(SamKey {
        authority: r.u32(),
        context: r.u32(),
        provider: r.u32(),
        class: Hash(r.hash()),
        owner: r.u32(),
        name: r.u32(),
        descriptor: r.u32(),
        resolved: r.boolean().ok()?,
    })
}
pub(crate) fn encode_sam_key(out: &mut dyn Write, v: SamKey) -> io::Result<()> {
    row::<60>(out, |r| {
        r.u32(v.authority);
        r.u32(v.context);
        r.u32(v.provider);
        r.hash(&v.class.0);
        r.u32(v.owner);
        r.u32(v.name);
        r.u32(v.descriptor);
        r.u32(v.resolved as u32);
    })
}
pub(crate) fn decode_adapter(mut r: Cursor<'_>) -> Option<CallableAdapterKey> {
    Some(CallableAdapterKey {
        authority: r.u32(),
        enclosing_method: r.u32(),
        enclosing_foreign_method: r.u32(),
        site: r.u32(),
        bootstrap_foreign_method: r.u32(),
        bootstrap_handle_kind: r.u32(),
        bootstrap_arguments: Hash(r.hash()),
        implementation_foreign_method: r.u32(),
        implementation_handle_kind: r.u32(),
        sam: r.u32(),
        invoked_name: r.u32(),
        invoked_descriptor: r.u32(),
        instantiated_descriptor: r.u32(),
        adaptation: Hash(r.hash()),
        normalized_arity: r.u32(),
        normalized_captures: r.u32(),
        resolved: r.boolean().ok()?,
    })
}
pub(crate) fn encode_adapter(out: &mut dyn Write, v: CallableAdapterKey) -> io::Result<()> {
    row::<124>(out, |r| {
        r.u32(v.authority);
        r.u32(v.enclosing_method);
        r.u32(v.enclosing_foreign_method);
        r.u32(v.site);
        r.u32(v.bootstrap_foreign_method);
        r.u32(v.bootstrap_handle_kind);
        r.hash(&v.bootstrap_arguments.0);
        r.u32(v.implementation_foreign_method);
        r.u32(v.implementation_handle_kind);
        r.u32(v.sam);
        r.u32(v.invoked_name);
        r.u32(v.invoked_descriptor);
        r.u32(v.instantiated_descriptor);
        r.hash(&v.adaptation.0);
        r.u32(v.normalized_arity);
        r.u32(v.normalized_captures);
        r.u32(v.resolved as u32);
    })
}

pub(crate) fn decode_callable_bridge(mut r: Cursor<'_>) -> Option<CallableBridge> {
    Some(CallableBridge {
        creation: r.u32(),
        sam: r.u32(),
        implementation: MethodId(r.u32()),
        proof: r.u32(),
    })
}
pub(crate) fn encode_callable_bridge(out: &mut dyn Write, v: CallableBridge) -> io::Result<()> {
    row::<16>(out, |r| {
        r.u32(v.creation);
        r.u32(v.sam);
        r.u32(v.implementation.0);
        r.u32(v.proof);
    })
}
pub(crate) fn decode_bridge_proof(mut r: Cursor<'_>) -> Option<CallableBridgeProofKey> {
    Some(CallableBridgeProofKey {
        authority: r.u32(),
        creation: r.u32(),
        creator_adapter: r.u32(),
        from_sam: r.u32(),
        to_sam: r.u32(),
        default_foreign_method: r.u32(),
        generated_method_set: Hash(r.hash()),
        default_code: Hash(r.hash()),
        transport_policy: Hash(r.hash()),
        proof: Hash(r.hash()),
        no_override: r.boolean().ok()?,
        resolved: r.boolean().ok()?,
    })
}
pub(crate) fn encode_bridge_proof(
    out: &mut dyn Write,
    v: CallableBridgeProofKey,
) -> io::Result<()> {
    row::<160>(out, |r| {
        r.u32(v.authority);
        r.u32(v.creation);
        r.u32(v.creator_adapter);
        r.u32(v.from_sam);
        r.u32(v.to_sam);
        r.u32(v.default_foreign_method);
        r.hash(&v.generated_method_set.0);
        r.hash(&v.default_code.0);
        r.hash(&v.transport_policy.0);
        r.hash(&v.proof.0);
        r.u32(v.no_override as u32);
        r.u32(v.resolved as u32);
    })
}

pub(crate) fn decode_phase(mut r: Cursor<'_>) -> Option<PhaseKey> {
    Some(PhaseKey {
        class: r.u32(),
        authority: r.u32(),
        kind: PhaseKind::decode(r.u32()).ok()?,
    })
}
pub(crate) fn encode_phase(out: &mut dyn Write, v: PhaseKey) -> io::Result<()> {
    row::<12>(out, |r| {
        r.u32(v.class);
        r.u32(v.authority);
        r.u32(v.kind as u32);
    })
}
