//! Exact Scala runtime release-fence contract under SelectionContract::CURRENT.
//!
//! A release fence retains its memory-ordering meaning. Under the explicit
//! functional-behavior premise that ordering is not an arbitrary application
//! heap read/write or callback. We preserve the private handle read/publication,
//! ordinary class initialization, and any unresolved initialization frontier.
//! This is no model of arbitrary reflection or MethodHandle invocation.
use super::*;
use selector_models::binary::{ClassFile, MethodInfo, MethodSummary, Value};

pub(super) const VERSION: &str = "trusted-scala-runtime/1:release-fence-java21";
const STATICS: &str = "scala/runtime/Statics";
const VM: &str = "scala/runtime/Statics$VM";
const VAR_HANDLE: &str = "java/lang/invoke/VarHandle";
const HANDLE: &str = "Ljava/lang/invoke/MethodHandle;";
const STATICS_SHA: &str = "0fcbcbeb38436fdff60e576baadfaf269a9eb93ac3594c139f76ad13fde4e296";
const VM_SHA: &str = "ebf2ff536c34b994586895b57106202b730f182ac95ff752c18012a29293e8a7";
const VAR_HANDLE_SHA: &str = "7039c0f15daf2409afd9f0d0335503474cbef3431ccba5065fdbf957f8bb94a7";
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum MemoryEffect {
    ReleaseFence,
    HandleBootstrap,
}
pub(super) struct Model<'a> {
    pub summary: MethodSummary<'a>,
    pub additional_initialization_owners: &'static [&'static str],
    pub memory_effect: MemoryEffect,
}
fn exact_hash(observed: ContentHash, expected: &str) -> bool {
    ContentHash::from_hex(expected).is_ok_and(|hash| hash == observed)
}
pub(super) fn candidate(owner: &str, name: &str, descriptor: &str) -> bool {
    matches!(
        (owner, name, descriptor),
        (STATICS, "releaseFence", "()V") | (VM, "mkHandle", "()Ljava/lang/invoke/MethodHandle;")
    )
}
fn matched(
    class: &ClassFile<'_>,
    method: &MethodInfo<'_>,
    hash: ContentHash,
) -> Option<MemoryEffect> {
    if method.code.is_none()
        || method.flags & 0x0500 != 0
        || method.exception_handlers != 0 && class.name == STATICS
    {
        return None;
    }
    let (effect, code_hash) = match (class.name, method.name, method.descriptor, method.flags) {
        (STATICS, "releaseFence", "()V", 9) if exact_hash(hash, STATICS_SHA) => (
            MemoryEffect::ReleaseFence,
            "070c77b11d1339e5c2fde6cc548b26d761288bf548af1c7589e9d063c381e6b6",
        ),
        (VM, "mkHandle", "()Ljava/lang/invoke/MethodHandle;", 10) if exact_hash(hash, VM_SHA) => (
            MemoryEffect::HandleBootstrap,
            "b3153574e858e041f912ace5fe44f2405bc9a90c24ea792e6dfad5cf47adc76b",
        ),
        _ => return None,
    };
    exact_hash(ContentHash(Sha256::digest(method.code?).into()), code_hash).then_some(effect)
}
fn recipe(effect: MemoryEffect) -> Model<'static> {
    let (values, value_offsets, returned, initializes) = match effect {
        MemoryEffect::ReleaseFence => (
            vec![Value::StaticField(MemberRef {
                owner: VM,
                name: "RELEASE_FENCE",
                descriptor: HANDLE,
            })],
            vec![0],
            None,
            &[][..],
        ),
        // The handle is intentionally opaque, never EMPTY or a fabricated
        // callable. Only this exact fence API consumes it through its contract.
        MemoryEffect::HandleBootstrap => (
            vec![Value::UnknownData],
            vec![0],
            Some(binary::BinaryValueId(0)),
            &[VAR_HANDLE][..],
        ),
    };
    Model {
        summary: MethodSummary {
            descriptor: if effect == MemoryEffect::ReleaseFence {
                "()V"
            } else {
                "()Ljava/lang/invoke/MethodHandle;"
            },
            values,
            value_offsets,
            calls: Vec::new(),
            arguments: Vec::new(),
            field_writes: Vec::new(),
            lambdas: Vec::new(),
            unknown_offsets: Vec::new(),
            returned,
            unknown: None,
            envelope: None,
        },
        additional_initialization_owners: initializes,
        memory_effect: effect,
    }
}
/// This private path receives only normally admitted first-provider classes.
/// The Java21 class must additionally be selected from the declared java.base
/// prefix; same-spelling classpath classes and absent platform inputs fail shut.
pub(super) fn model<'a>(
    context: &mut AdmittedContext,
    loader: &mut CapturedClasspath,
    class: &ClassFile<'a>,
    method: &MethodInfo<'a>,
    bytes: &ClassBytes,
    has_platform: bool,
) -> Result<Option<Model<'a>>, Error> {
    let Some(effect) = matched(class, method, bytes.hash) else {
        return Ok(None);
    };
    if !has_platform || context.java_feature != Some(21) {
        return Ok(None);
    }
    let sibling = if class.name == STATICS { VM } else { STATICS };
    let Some(sibling_bytes) = proof_class(context, loader, sibling)? else {
        return Ok(None);
    };
    if !exact_hash(
        sibling_bytes.hash,
        if sibling == VM { VM_SHA } else { STATICS_SHA },
    ) {
        return Ok(None);
    }
    let Some(var_handle) = proof_class(context, loader, VAR_HANDLE)? else {
        return Ok(None);
    };
    if !declared_class(context, VAR_HANDLE, &var_handle)
        || !exact_hash(var_handle.hash, VAR_HANDLE_SHA)
    {
        return Ok(None);
    }
    let header = var_handle.metadata.as_ref();
    if header.header().major != 65
        || !header
            .method("releaseFence", Some("()V"))
            .is_ok_and(|method| method.flags == 9 && method.code.is_some())
    {
        return Ok(None);
    }
    // VM.RELEASE_FENCE is a runtime-owned static final field. Its real <clinit> and
    // static store remain normal recipes, not a fabricated empty initializer.
    let vm = if class.name == VM {
        bytes.metadata.as_ref()
    } else {
        sibling_bytes.metadata.as_ref()
    };
    if !vm
        .field("RELEASE_FENCE", HANDLE)
        .is_ok_and(|field| field.is_some_and(|field| field.flags & 0x18 == 0x18))
    {
        return Ok(None);
    }
    Ok(Some(recipe(effect)))
}
fn proof_class(
    context: &mut AdmittedContext,
    loader: &mut CapturedClasspath,
    owner: &str,
) -> Result<Option<Arc<ClassBytes>>, Error> {
    match cache_class(context, loader, owner) {
        Ok(value) => Ok(value),
        // Optional model proof failed; the original open reflection recipe is
        // kept. This is not an omitted real call or a class-absence certificate.
        Err(Error::Limit(_)) => Ok(None),
        Err(error) => Err(error),
    }
}
pub(super) fn declared_class(context: &AdmittedContext, owner: &str, bytes: &ClassBytes) -> bool {
    context.entries.first().is_some_and(|entry| {
        matches!(entry.kind, EntryKind::Jar)
            && bytes.origin == format!("{}!/{owner}.class", entry.path.display())
    })
}
pub(super) fn body_hash(original: ContentHash, label: &[u8]) -> ContentHash {
    let mut hash = Sha256::new();
    hash.update(VERSION);
    hash.update(SelectionContract::VERSION);
    hash.update(SelectionContract::CURRENT_BASE_BITS.to_le_bytes());
    hash.update(original.0);
    hash.update(label);
    ContentHash(hash.finalize().into())
}
#[cfg(test)]
#[path = "binary_trusted_scala_tests.rs"]
mod tests;
