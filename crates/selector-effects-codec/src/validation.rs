use crate::*;

fn need(value: bool, message: &'static str) -> Result<(), Error> {
    if value {
        Ok(())
    } else {
        Err(Error::Invalid(message))
    }
}
fn text(k: &impl ProvenanceView, index: u32) -> Result<&str, Error> {
    let value = k
        .text(index)
        .ok_or(Error::Invalid("text reference or UTF8"))?;
    need(
        !value.is_empty() && !value.contains('\0'),
        "empty or NUL identity text",
    )?;
    Ok(value)
}
fn context(k: &impl ProvenanceView, index: u32) -> Result<(), Error> {
    need((index as usize) < k.context_count(), "context reference")
}
fn provider(k: &impl ProvenanceView, index: u32, context: u32) -> Result<(), Error> {
    let value = k
        .provider(index as usize)
        .ok_or(Error::Invalid("provider reference"))?;
    need(value.context == context, "provider context transplant")
}
fn class_binding(
    k: &impl ProvenanceView,
    ctx: u32,
    provider_id: u32,
    class: Hash,
    resolved: bool,
) -> Result<(), Error> {
    context(k, ctx)?;
    if provider_id == NONE {
        need(class.is_zero() && !resolved, "class without provider")
    } else {
        provider(k, provider_id, ctx)?;
        need(!resolved || !class.is_zero(), "resolved class without hash")
    }
}
fn unique<T: Ord + Copy>(
    previous: &mut Option<T>,
    value: T,
    label: &'static str,
) -> Result<(), Error> {
    need(previous.is_none_or(|p| p < value), label)?;
    *previous = Some(value);
    Ok(())
}
fn owner(value: &str) -> bool {
    !value.is_empty()
        && value.split('/').all(|s| !s.is_empty())
        && !value.bytes().any(|b| matches!(b, b'.' | b';' | b'[' | 0))
}
fn value_type(bytes: &[u8], at: &mut usize, void: bool) -> bool {
    let Some(&tag) = bytes.get(*at) else {
        return false;
    };
    *at += 1;
    match tag {
        b'V' => void,
        b'B' | b'C' | b'D' | b'F' | b'I' | b'J' | b'S' | b'Z' => true,
        b'L' => {
            let start = *at;
            let Some(end) = bytes[start..].iter().position(|b| *b == b';') else {
                return false;
            };
            *at = start + end + 1;
            std::str::from_utf8(&bytes[start..start + end]).is_ok_and(owner)
        }
        b'[' => {
            let mut dimensions = 1usize;
            while bytes.get(*at) == Some(&b'[') {
                dimensions += 1;
                *at += 1;
            }
            dimensions <= 255 && value_type(bytes, at, false)
        }
        _ => false,
    }
}
fn descriptor(value: &str, method: bool) -> bool {
    let bytes = value.as_bytes();
    let mut at = 0usize;
    if method {
        if bytes.first() != Some(&b'(') {
            return false;
        }
        at = 1;
        let mut parameters = 0usize;
        while bytes.get(at) != Some(&b')') {
            if !value_type(bytes, &mut at, false) {
                return false;
            }
            parameters += 1;
            if parameters > 255 {
                return false;
            }
        }
        at += 1;
        value_type(bytes, &mut at, true) && at == bytes.len()
    } else {
        value_type(bytes, &mut at, false) && at == bytes.len()
    }
}
fn parameter_count(value: &str) -> Option<u32> {
    let bytes = value.as_bytes();
    if bytes.first() != Some(&b'(') {
        return None;
    }
    let mut at = 1;
    let mut count = 0u32;
    while bytes.get(at) != Some(&b')') {
        if !value_type(bytes, &mut at, false) {
            return None;
        }
        count = count.checked_add(1)?;
    }
    Some(count)
}
fn top(m: MethodRow, channel: Channel, message: &'static str) -> Result<(), Error> {
    need(m.top.contains(channel), message)
}
fn partition(range: Range, next: &mut u32) -> Result<(), Error> {
    // MethodRow::unknown uses Range::EMPTY regardless of earlier table rows.
    // Empty references carry no authority and may have any in-bounds start.
    if range.len == 0 {
        return Ok(());
    }
    need(range.start == *next, "overlapping or orphan effect row")?;
    *next = next
        .checked_add(range.len)
        .ok_or(Error::Limit("effect range end"))?;
    Ok(())
}
fn member(k: &impl ProvenanceView, id: u32) -> Result<MemberKey, Error> {
    k.member(id as usize)
        .ok_or(Error::Invalid("member reference"))
}
fn storage(
    k: &impl ProvenanceView,
    m: MethodRow,
    value: StorageRef,
    channel: Channel,
) -> Result<(), Error> {
    if value.kind == StorageKind::ArrayElements {
        return need(value.member == NONE, "array member namespace");
    }
    let key = member(k, value.member)?;
    let matches = matches!(
        (value.kind, key.kind),
        (StorageKind::StaticField, MemberKind::StaticField)
            | (StorageKind::InstanceField, MemberKind::InstanceField)
            | (StorageKind::RuntimeState, MemberKind::RuntimeState)
    );
    need(matches, "storage member kind alias")?;
    if !key.canonical {
        top(m, channel, "unproved member alias without channel TOP")?;
    }
    Ok(())
}

pub(crate) fn validate(
    k: &impl ProvenanceView,
    t: &impl TableView,
    binding: Binding,
    bounds: RefBounds,
    limits: Limits,
) -> Result<(), Error> {
    binding.validate()?;
    for n in [
        k.text_count(),
        k.context_count(),
        k.provider_count(),
        k.foreign_method_count(),
        k.member_count(),
        k.class_count(),
        k.authority_count(),
        k.exception_key_count(),
        k.external_key_count(),
        k.site_count(),
        k.sam_key_count(),
        k.adapter_count(),
        k.bridge_proof_count(),
        k.phase_key_count(),
    ] {
        need(
            n < NONE as usize && n <= limits.max_records as usize,
            "key table identifier budget",
        )?;
    }
    need(
        bounds.fact_nodes == binding.fact_nodes
            && bounds.foreign_methods as usize == k.foreign_method_count()
            && bounds.authorities as usize == k.authority_count()
            && bounds.members as usize == k.member_count()
            && bounds.classes as usize == k.class_count()
            && bounds.exceptions as usize == k.exception_key_count()
            && bounds.externals as usize == k.external_key_count()
            && bounds.sites as usize == k.site_count()
            && bounds.sams as usize == k.sam_key_count()
            && bounds.adapters as usize == k.adapter_count()
            && bounds.bridge_proofs as usize == k.bridge_proof_count()
            && bounds.phases as usize == k.phase_key_count()
            && t.sam_count() == k.sam_key_count(),
        "key namespace counts",
    )?;
    let mut previous = None;
    for i in 0..k.text_count() {
        let value = k
            .text(i as u32)
            .ok_or(Error::Invalid("text range or UTF8"))?;
        unique(&mut previous, value, "text table not sorted unique")?;
    }
    let mut previous = None;
    for i in 0..k.context_count() {
        let v = k.context(i).ok_or(Error::Invalid("context row"))?;
        text(k, v.name)?;
        need(!v.inputs.is_zero(), "unbound context inputs")?;
        unique(&mut previous, v.name, "duplicate context identity")?;
    }
    let mut previous = None;
    for i in 0..k.provider_count() {
        let v = k.provider(i).ok_or(Error::Invalid("provider row"))?;
        context(k, v.context)?;
        text(k, v.path)?;
        need(!v.digest.is_zero(), "unbound provider")?;
        unique(
            &mut previous,
            (v.context, v.ordinal),
            "duplicate provider ordinal",
        )?;
    }
    let mut previous = None;
    for i in 0..k.foreign_method_count() {
        let v = k
            .foreign_method(i)
            .ok_or(Error::Invalid("foreign method row"))?;
        class_binding(k, v.context, v.provider, v.class, v.resolved)?;
        need(owner(text(k, v.owner)?), "foreign owner ABI")?;
        let name = text(k, v.name)?;
        let abi = text(k, v.descriptor)?;
        need(descriptor(abi, true), "foreign method descriptor")?;
        need(
            !name
                .bytes()
                .any(|b| matches!(b, b'.' | b';' | b'[' | b'/' | 0))
                && (!name.contains(['<', '>']) || matches!(name, "<init>" | "<clinit>")),
            "foreign method name",
        )?;
        need(
            name != "<init>" || abi.ends_with(")V"),
            "constructor result ABI",
        )?;
        need(name != "<clinit>" || abi == "()V", "class initializer ABI")?;
        if v.resolved {
            need(
                name != "<init>" || v.method_flags & 8 == 0,
                "static constructor ABI",
            )?;
            need(
                name != "<clinit>" || v.method_flags & 8 != 0,
                "instance class initializer ABI",
            )?;
        }
        need(
            v.node == NONE || v.node < binding.fact_nodes,
            "foreign node hint",
        )?;
        need(v.method_flags <= u16::MAX as u32, "foreign method flags")?;
        unique(
            &mut previous,
            (v.context, v.owner, v.name, v.descriptor),
            "duplicate foreign ABI identity",
        )?;
    }
    let mut previous = None;
    let mut source_symbol = None;
    for i in 0..k.member_count() {
        let v = k.member(i).ok_or(Error::Invalid("member row"))?;
        context(k, v.context)?;
        match v.identity {
            MemberIdentity::FactSymbol => {
                need(
                    v.fact_symbol < binding.fact_symbols
                        && v.provider == NONE
                        && v.class.is_zero()
                        && v.owner == NONE
                        && v.name == NONE
                        && v.descriptor == NONE,
                    "source member identity namespace",
                )?;
                need(
                    source_symbol != Some(v.fact_symbol),
                    "duplicate source member symbol",
                )?;
                source_symbol = Some(v.fact_symbol);
                need(
                    matches!(v.kind, MemberKind::StaticField | MemberKind::InstanceField),
                    "source member storage kind",
                )?;
            }
            MemberIdentity::ForeignMember => {
                need(v.fact_symbol == NONE, "foreign member symbol alias")?;
                class_binding(k, v.context, v.provider, v.class, v.canonical)?;
                need(owner(text(k, v.owner)?), "foreign field owner ABI")?;
                need(
                    !text(k, v.name)?
                        .bytes()
                        .any(|b| matches!(b, b'.' | b';' | b'[' | b'/' | 0)),
                    "foreign field name",
                )?;
                need(
                    descriptor(text(k, v.descriptor)?, false),
                    "foreign field descriptor",
                )?;
                need(
                    matches!(v.kind, MemberKind::StaticField | MemberKind::InstanceField),
                    "foreign member storage kind",
                )?;
            }
            MemberIdentity::RuntimeKey | MemberIdentity::ArrayKey => {
                need(
                    v.fact_symbol == NONE && v.class.is_zero(),
                    "runtime member namespace",
                )?;
                provider(k, v.provider, v.context)?;
                text(k, v.owner)?;
                text(k, v.name)?;
                text(k, v.descriptor)?;
                need(
                    matches!(
                        (v.identity, v.kind),
                        (MemberIdentity::RuntimeKey, MemberKind::RuntimeState)
                            | (MemberIdentity::ArrayKey, MemberKind::ArrayElements)
                    ),
                    "runtime member storage kind",
                )?;
            }
        }
        unique(
            &mut previous,
            (
                v.identity as u32,
                v.fact_symbol,
                v.context,
                v.kind as u32,
                v.owner,
                v.name,
                v.descriptor,
            ),
            "duplicate or unordered member identity",
        )?;
    }
    let mut previous = None;
    let mut source_symbol = None;
    for i in 0..k.class_count() {
        let v = k.class(i).ok_or(Error::Invalid("class row"))?;
        context(k, v.context)?;
        need(
            v.node == NONE || v.node < binding.fact_nodes,
            "class node hint",
        )?;
        match v.identity {
            ClassIdentity::FactSymbol => {
                need(
                    v.fact_symbol < binding.fact_symbols
                        && v.provider == NONE
                        && v.class.is_zero()
                        && v.owner == NONE,
                    "source class identity namespace",
                )?;
                need(
                    source_symbol != Some(v.fact_symbol),
                    "duplicate source class symbol",
                )?;
                source_symbol = Some(v.fact_symbol);
            }
            ClassIdentity::ForeignClass => {
                need(v.fact_symbol == NONE, "foreign class symbol alias")?;
                class_binding(k, v.context, v.provider, v.class, v.resolved)?;
                need(owner(text(k, v.owner)?), "foreign class owner ABI")?;
            }
        }
        unique(
            &mut previous,
            (v.identity as u32, v.fact_symbol, v.context, v.owner),
            "duplicate or unordered class identity",
        )?;
    }
    let mut previous = None;
    for i in 0..k.authority_count() {
        let v = k.authority(i).ok_or(Error::Invalid("authority row"))?;
        need(!v.producer.is_zero(), "unbound authority producer")?;
        text(k, v.name)?;
        need(
            v.kind != AuthorityKind::ReviewedContract || !v.contract.is_zero(),
            "unbound reviewed contract",
        )?;
        unique(
            &mut previous,
            (v.producer.0, v.contract.0, v.kind as u32, v.name),
            "duplicate authority identity",
        )?;
    }
    let mut previous = None;
    for i in 0..k.exception_key_count() {
        let v = k
            .exception_key(i)
            .ok_or(Error::Invalid("exception key row"))?;
        need(
            (v.class as usize) < k.class_count() || (!v.known && v.class == NONE),
            "exception class reference",
        )?;
        unique(&mut previous, v.class, "duplicate exception class")?;
    }
    let mut previous = None;
    for i in 0..k.external_key_count() {
        let v = k
            .external_key(i)
            .ok_or(Error::Invalid("external key row"))?;
        context(k, v.context)?;
        text(k, v.name)?;
        need((1..=6).contains(&v.kind), "external key kind")?;
        need(!v.canonical || !v.digest.is_zero(), "unbound external key")?;
        unique(
            &mut previous,
            (v.context, v.kind, v.name),
            "duplicate external identity",
        )?;
    }
    let mut previous = None;
    for i in 0..k.site_count() {
        let v = k.site(i).ok_or(Error::Invalid("site row"))?;
        need(
            (v.method as usize) < t.method_count(),
            "site method reference",
        )?;
        match v.kind {
            SiteKind::FactOperation => need(
                v.fact_operation < binding.fact_operations && v.offset == 0,
                "source operation site namespace",
            )?,
            SiteKind::NativeBytecode => {
                need(v.fact_operation == NONE, "native PC source operation alias")?
            }
        }
        unique(
            &mut previous,
            (v.method, v.kind as u32, v.offset, v.fact_operation),
            "duplicate site identity",
        )?;
    }
    let mut previous = None;
    for i in 0..k.sam_key_count() {
        let v = k.sam_key(i).ok_or(Error::Invalid("SAM key"))?;
        need(
            (v.authority as usize) < k.authority_count(),
            "SAM authority",
        )?;
        class_binding(k, v.context, v.provider, v.class, v.resolved)?;
        need(owner(text(k, v.owner)?), "SAM owner ABI")?;
        let name = text(k, v.name)?;
        need(
            !name
                .bytes()
                .any(|b| matches!(b, b'.' | b';' | b'[' | b'/' | b'<' | b'>' | 0)),
            "SAM method name",
        )?;
        let abi = text(k, v.descriptor)?;
        need(descriptor(abi, true), "SAM method descriptor")?;
        need(
            parameter_count(abi) == t.sam_arity(i),
            "SAM arity contradicts descriptor",
        )?;
        unique(
            &mut previous,
            (v.context, v.owner, v.name, v.descriptor),
            "duplicate or unordered SAM identity",
        )?;
    }
    let mut previous = None;
    for i in 0..k.adapter_count() {
        let v = k.adapter(i).ok_or(Error::Invalid("callable adapter key"))?;
        need(
            (v.authority as usize) < k.authority_count(),
            "adapter authority",
        )?;
        let enclosing = k
            .foreign_method(v.enclosing_foreign_method as usize)
            .ok_or(Error::Invalid("adapter enclosing foreign method"))?;
        let bootstrap = k
            .foreign_method(v.bootstrap_foreign_method as usize)
            .ok_or(Error::Invalid("adapter bootstrap foreign method"))?;
        let implementation = k
            .foreign_method(v.implementation_foreign_method as usize)
            .ok_or(Error::Invalid("adapter implementation foreign method"))?;
        let sam = k
            .sam_key(v.sam as usize)
            .ok_or(Error::Invalid("adapter SAM key"))?;
        need(
            (v.enclosing_method as usize) < t.method_count()
                && k.site(v.site as usize)
                    .is_some_and(|s| s.method == v.enclosing_method),
            "adapter enclosing method/site",
        )?;
        need(
            enclosing.context == bootstrap.context
                && enclosing.context == implementation.context
                && enclosing.context == sam.context,
            "adapter context transplant",
        )?;
        need(
            matches!(v.bootstrap_handle_kind, 6 | 8)
                && (5..=9).contains(&v.implementation_handle_kind),
            "adapter method handle kind",
        )?;
        let enclosing_row = t
            .method(v.enclosing_method as usize)
            .ok_or(Error::Invalid("adapter enclosing row"))?;
        if v.resolved {
            need(
                enclosing_row.subject.kind == SubjectKind::ForeignMethod
                    && enclosing_row.subject.index == v.enclosing_foreign_method,
                "adapter enclosing foreign identity mismatch",
            )?;
        }
        need(
            (v.bootstrap_handle_kind == 8) == (text(k, bootstrap.name)? == "<init>")
                && text(k, bootstrap.name)? != "<clinit>",
            "adapter bootstrap handle constructor ABI",
        )?;
        need(
            (v.implementation_handle_kind == 8) == (text(k, implementation.name)? == "<init>")
                && text(k, implementation.name)? != "<clinit>",
            "adapter implementation handle constructor ABI",
        )?;
        text(k, v.invoked_name)?;
        need(
            descriptor(text(k, v.invoked_descriptor)?, true)
                && descriptor(text(k, v.instantiated_descriptor)?, true),
            "adapter invocation descriptors",
        )?;
        need(
            v.normalized_arity
                == t.sam_arity(v.sam as usize)
                    .ok_or(Error::Invalid("adapter SAM arity"))?
                && parameter_count(text(k, v.instantiated_descriptor)?) == Some(v.normalized_arity)
                && parameter_count(text(k, v.invoked_descriptor)?) == Some(v.normalized_captures),
            "adapter normalized shape",
        )?;
        if v.resolved {
            need(
                enclosing.resolved
                    && bootstrap.resolved
                    && implementation.resolved
                    && sam.resolved
                    && !v.bootstrap_arguments.is_zero()
                    && !v.adaptation.is_zero(),
                "unbound resolved adapter",
            )?;
            need(
                (v.bootstrap_handle_kind == 6) == (bootstrap.method_flags & 8 != 0)
                    && (v.implementation_handle_kind == 6)
                        == (implementation.method_flags & 8 != 0),
                "adapter handle static ABI",
            )?;
        }
        unique(
            &mut previous,
            (v.enclosing_method, v.site),
            "duplicate or unordered adapter site",
        )?;
    }
    let mut previous = None;
    for i in 0..k.phase_key_count() {
        let key = k.phase_key(i).ok_or(Error::Invalid("runtime phase key"))?;
        need(
            (key.class as usize) < k.class_count()
                && (key.authority as usize) < k.authority_count(),
            "runtime phase class/authority",
        )?;
        unique(
            &mut previous,
            (key.class, key.kind as u32),
            "duplicate or unordered runtime phase",
        )?;
    }
    let mut previous = None;
    for i in 0..k.bridge_proof_count() {
        let key = k
            .bridge_proof(i)
            .ok_or(Error::Invalid("bridge proof key"))?;
        need(
            (key.authority as usize) < k.authority_count(),
            "bridge proof authority",
        )?;
        let creation = t
            .creation(key.creation as usize)
            .ok_or(Error::Invalid("bridge creation key"))?;
        let implementation = t
            .method(creation.implementation.0 as usize)
            .ok_or(Error::Invalid("bridge creator implementation"))?;
        let adapter = k
            .adapter(key.creator_adapter as usize)
            .ok_or(Error::Invalid("bridge creator adapter key"))?;
        let from = k
            .sam_key(key.from_sam as usize)
            .ok_or(Error::Invalid("bridge source SAM"))?;
        let to = k
            .sam_key(key.to_sam as usize)
            .ok_or(Error::Invalid("bridge requested SAM"))?;
        let default = k
            .foreign_method(key.default_foreign_method as usize)
            .ok_or(Error::Invalid("bridge default foreign method"))?;
        need(
            creation.sam == key.from_sam
                && key.from_sam != key.to_sam
                && implementation.subject.kind == SubjectKind::CallableAdapter
                && implementation.subject.index == key.creator_adapter,
            "bridge creator identity transplant",
        )?;
        need(
            adapter.sam == key.from_sam
                && from.context == to.context
                && from.context == default.context,
            "bridge SAM/context transplant",
        )?;
        need(
            default.name == to.name && default.descriptor == to.descriptor,
            "bridge requested member ABI",
        )?;
        if key.resolved {
            need(
                adapter.resolved
                    && from.resolved
                    && to.resolved
                    && default.resolved
                    && key.no_override
                    && !key.generated_method_set.is_zero()
                    && !key.default_code.is_zero()
                    && !key.transport_policy.is_zero()
                    && !key.proof.is_zero(),
                "unbound resolved bridge proof",
            )?;
            need(
                default.method_flags & 1 != 0
                    && default.method_flags & (2 | 8 | 0x100 | 0x400) == 0
                    && !matches!(text(k, default.name)?, "<init>" | "<clinit>"),
                "bridge default method is not public executable instance method",
            )?;
        }
        unique(
            &mut previous,
            (key.creation, key.to_sam),
            "duplicate or unordered bridge proof",
        )?;
    }
    selector_effects::validate_tables(t, bounds, limits.effects)
        .map_err(|_| Error::Invalid("effect table contract"))?;
    for i in 0..t.callable_bridge_count() {
        let bridge = t
            .callable_bridge(i)
            .ok_or(Error::Invalid("callable bridge row"))?;
        let key = k
            .bridge_proof(bridge.proof as usize)
            .ok_or(Error::Invalid("callable bridge proof"))?;
        let target = t
            .method(bridge.implementation.0 as usize)
            .ok_or(Error::Invalid("callable bridge target"))?;
        need(
            bridge.creation == key.creation
                && bridge.sam == key.to_sam
                && target.subject.kind == SubjectKind::ForeignMethod
                && target.subject.index == key.default_foreign_method,
            "bridge row/proof/default identity transplant",
        )?;
        if !key.resolved {
            need(
                target.top == TopMask::ALL,
                "unresolved bridge target without ALL TOP",
            )?;
        }
    }
    let mut previous = None;
    let mut next = [0u32; 12];
    let mut origin_next = 0u32;
    for i in 0..t.method_count() {
        let m = t.method(i).ok_or(Error::Invalid("method row"))?;
        unique(
            &mut previous,
            (m.subject.kind as u32, m.subject.index),
            "duplicate or unordered method subject",
        )?;
        if m.subject.kind == SubjectKind::ForeignMethod {
            let v = k
                .foreign_method(m.subject.index as usize)
                .ok_or(Error::Invalid("foreign subject"))?;
            need(
                v.resolved || m.top == TopMask::ALL,
                "missing foreign evidence without ALL TOP",
            )?;
            if v.resolved && m.top != TopMask::ALL {
                need(
                    m.captures == 0 && parameter_count(text(k, v.descriptor)?) == Some(m.arity),
                    "foreign method shape contradicts exact JVM descriptor",
                )?;
            }
        }
        if m.subject.kind == SubjectKind::RuntimePhase {
            let phase = k
                .phase_key(m.subject.index as usize)
                .ok_or(Error::Invalid("runtime phase subject"))?;
            need(
                m.authority == phase.authority,
                "runtime phase producer authority mismatch",
            )?;
        }
        if m.subject.kind == SubjectKind::CallableAdapter {
            let key = k
                .adapter(m.subject.index as usize)
                .ok_or(Error::Invalid("adapter subject"))?;
            need(
                key.resolved || m.top == TopMask::ALL,
                "unresolved adapter without ALL TOP",
            )?;
            if m.top != TopMask::ALL {
                need(
                    m.arity == key.normalized_arity && m.captures == key.normalized_captures,
                    "adapter capsule shape",
                )?;
            }
        }
        for (index, r) in [
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
        ]
        .into_iter()
        .enumerate()
        {
            partition(r, &mut next[index])?;
        }
        for ci in m
            .calls
            .checked(t.call_count())
            .map_err(|_| Error::Invalid("call range"))?
        {
            let call = t.call(ci).ok_or(Error::Invalid("call row"))?;
            partition(call.arguments, &mut origin_next)?;
            partition(call.captures, &mut origin_next)?;
            need(
                k.site(call.site as usize)
                    .ok_or(Error::Invalid("call site"))?
                    .method
                    == i as u32,
                "call site cross-method alias",
            )?;
            if let CallTarget::Callable { sam, .. } = call.target {
                if sam == NONE
                    || !k
                        .sam_key(sam as usize)
                        .ok_or(Error::Invalid("call SAM"))?
                        .resolved
                {
                    top(
                        m,
                        Channel::Calls,
                        "unadmitted callable invocation without Calls TOP",
                    )?;
                }
            }
            if let CallTarget::Direct(id) = call.target {
                let target = t
                    .method(id.0 as usize)
                    .ok_or(Error::Invalid("call target"))?;
                if target.subject.kind == SubjectKind::ForeignMethod {
                    let foreign = k
                        .foreign_method(target.subject.index as usize)
                        .ok_or(Error::Invalid("foreign call target"))?;
                    if foreign.resolved && call.kind != CallKind::Callback {
                        need(
                            (call.kind == CallKind::Static) == (foreign.method_flags & 8 != 0),
                            "foreign call ABI static/instance contradiction",
                        )?;
                    }
                }
            }
        }
        for ci in m
            .creations
            .checked(t.creation_count())
            .map_err(|_| Error::Invalid("creation range"))?
        {
            let c = t.creation(ci).ok_or(Error::Invalid("creation row"))?;
            partition(c.captures, &mut origin_next)?;
            need(
                k.site(c.site as usize)
                    .is_some_and(|s| s.method == i as u32),
                "creation site cross-method alias",
            )?;
        }
        for ri in m
            .reads
            .checked(t.read_count())
            .map_err(|_| Error::Invalid("read range"))?
        {
            storage(
                k,
                m,
                t.read(ri).ok_or(Error::Invalid("read row"))?,
                Channel::Reads,
            )?;
        }
        for ri in m
            .writes
            .checked(t.write_count())
            .map_err(|_| Error::Invalid("write range"))?
        {
            storage(
                k,
                m,
                t.write(ri).ok_or(Error::Invalid("write row"))?,
                Channel::Writes,
            )?;
        }
        for ri in m
            .code_observations
            .checked(t.code_observation_count())
            .map_err(|_| Error::Invalid("code range"))?
        {
            let v = t.code_observation(ri).ok_or(Error::Invalid("code row"))?;
            if v.kind == CodeKind::Class
                && !k
                    .class(v.index as usize)
                    .ok_or(Error::Invalid("code class"))?
                    .resolved
            {
                top(
                    m,
                    Channel::CodeObservations,
                    "unresolved class without code TOP",
                )?;
            }
        }
        for ri in m
            .initializes
            .checked(t.initialize_count())
            .map_err(|_| Error::Invalid("initialization range"))?
        {
            let target = t
                .method(
                    t.initialize(ri)
                        .ok_or(Error::Invalid("initialization row"))?
                        .0 as usize,
                )
                .ok_or(Error::Invalid("initialization target"))?;
            need(
                target.top == TopMask::ALL || (target.arity == 0 && target.captures == 0),
                "initialization target needs actual arguments",
            )?;
        }
        for ri in m
            .throws
            .checked(t.throw_count())
            .map_err(|_| Error::Invalid("throw range"))?
        {
            let key = k
                .exception_key(t.r#throw(ri).ok_or(Error::Invalid("throw row"))? as usize)
                .ok_or(Error::Invalid("throw key"))?;
            let resolved = key.known && k.class(key.class as usize).is_some_and(|c| c.resolved);
            if !resolved {
                top(
                    m,
                    Channel::Throws,
                    "unresolved exception without throws TOP",
                )?;
            }
        }
        for ri in m
            .external
            .checked(t.external_count())
            .map_err(|_| Error::Invalid("external range"))?
        {
            let v = t.external(ri).ok_or(Error::Invalid("external row"))?;
            if !k
                .external_key(v.key as usize)
                .ok_or(Error::Invalid("external key"))?
                .canonical
            {
                top(m, Channel::External, "unbound external effect without TOP")?;
            }
        }
        for ri in m
            .escapes
            .checked(t.escape_count())
            .map_err(|_| Error::Invalid("escape range"))?
        {
            let v = t.escape(ri).ok_or(Error::Invalid("escape row"))?;
            if v.sink == EscapeSink::Heap && !member(k, v.index)?.canonical {
                top(m, Channel::Escapes, "noncanonical escape without TOP")?;
            }
            if v.sink == EscapeSink::External
                && !k
                    .external_key(v.index as usize)
                    .ok_or(Error::Invalid("escape external key"))?
                    .canonical
            {
                top(m, Channel::Escapes, "unbound external escape without TOP")?;
            }
        }
        for ri in m
            .flows
            .checked(t.flow_count())
            .map_err(|_| Error::Invalid("flow range"))?
        {
            let v = t.flow(ri).ok_or(Error::Invalid("flow row"))?;
            match v.sink {
                FlowSink::HeapWrite => {
                    let value = t
                        .write(m.writes.start as usize + v.via as usize)
                        .ok_or(Error::Invalid("flow write"))?;
                    if value.kind != StorageKind::ArrayElements
                        && !member(k, value.member)?.canonical
                    {
                        top(m, Channel::Flows, "noncanonical heap flow without TOP")?;
                    }
                }
                FlowSink::External => {
                    let value = t
                        .external(m.external.start as usize + v.via as usize)
                        .ok_or(Error::Invalid("flow external"))?;
                    if !k
                        .external_key(value.key as usize)
                        .ok_or(Error::Invalid("flow external key"))?
                        .canonical
                    {
                        top(m, Channel::Flows, "unbound external flow without TOP")?;
                    }
                }
                FlowSink::Throw => {
                    let key = k
                        .exception_key(v.index as usize)
                        .ok_or(Error::Invalid("flow exception key"))?;
                    if !key.known || !k.class(key.class as usize).is_some_and(|c| c.resolved) {
                        top(m, Channel::Flows, "unresolved thrown flow without TOP")?;
                    }
                }
                _ => (),
            }
        }
    }
    let counts = [
        t.call_count(),
        t.code_observation_count(),
        t.read_count(),
        t.write_count(),
        t.escape_count(),
        t.initialize_count(),
        t.throw_count(),
        t.synchronize_count(),
        t.external_count(),
        t.flow_count(),
        t.creation_count(),
        t.value_flow_count(),
    ];
    for (actual, expected) in next.into_iter().zip(counts) {
        need(actual as usize == expected, "orphan effect table rows")?;
    }
    need(
        origin_next as usize == t.origin_count(),
        "orphan call origin rows",
    )?;
    Ok(())
}
