//! Explicit synthetic reads of compiler-witnessed global Scala modules.
//! This adapter is not a JVM method declaration. It retains normal class
//! initialization and the actual MODULE$ heap slot, including all open effects.
use super::*;

const VERSION: &[u8] = b"binary-top-level-module-read/1";

fn header(class: &binary::ClassMetadata, candidate: &Candidate) -> bool {
    header_rows(
        class.name(),
        class.flags(),
        class.fields().map(|f| (f.name, f.descriptor, f.flags)),
        class
            .methods()
            .map(|m| (m.name, m.descriptor, m.flags, m.code.is_some())),
        candidate,
    )
}

fn header_rows<'a>(
    name: &str,
    flags: u16,
    fields: impl Iterator<Item = (&'a str, &'a str, u16)>,
    methods: impl Iterator<Item = (&'a str, &'a str, u16, bool)>,
    candidate: &Candidate,
) -> bool {
    if !candidate.global || name != candidate.module_owner || flags & 0x0601 != 0x0001 {
        return false;
    }
    let mut fields = fields.filter(|field| field.0 == "MODULE$");
    if !fields
        .next()
        .is_some_and(|field| field.1 == candidate.descriptor && field.2 & 0x001f == 0x0019)
        || fields.next().is_some()
    {
        return false;
    }
    let mut methods = methods.filter(|method| method.0 == "<clinit>");
    methods
        .next()
        .is_some_and(|method| method.1 == "()V" && method.2 & 0x0008 != 0 && method.3)
        && methods.next().is_none()
}

fn declare(
    facts: &mut FactSnapshot,
    registry: &mut Registry,
    context_index: usize,
    context: &mut AdmittedContext,
    loader: &mut CapturedClasspath,
    candidate: &Candidate,
    pending: &mut VecDeque<MethodKey>,
) -> Result<Option<(SymbolId, ContentHash)>, Error> {
    let Some(class) = cache_class(context, loader, &candidate.module_owner)? else {
        return Ok(None);
    };
    if !header(&class.metadata, candidate) {
        return Ok(None);
    }
    let (target, phase) = registry.field(
        facts,
        context_index,
        context,
        loader,
        MemberRef {
            owner: &candidate.module_owner,
            name: "MODULE$",
            descriptor: &candidate.descriptor,
        },
        true,
        pending,
    )?;
    if target.is_none() {
        return Ok(None);
    }
    context.admission.check_method(
        registry
            .methods
            .len()
            .saturating_add(registry.synthetic_methods),
    )?;
    let file = registry.file(
        facts,
        context_index,
        context.id,
        &candidate.module_owner,
        &class,
    )?;
    let owner = facts.symbols[target.index()].owner;
    let name = format!(
        "@jvm-module-read/{}:{}:{}",
        candidate.module_owner.len(),
        candidate.module_owner,
        class.hash
    );
    let symbol = super::super::declare(facts, context.id, owner, &name, 3, file, 0)?;
    registry.synthetic_methods += 1;
    context.admission.admitted_method();
    let body = BodyId::checked(facts.bodies.len())?;
    let start = u32::try_from(facts.operations.len())
        .map_err(|_| Error::Limit("module adapter operations"))?;
    let mut emit = |opcode, target, dest, a, flags| {
        facts.operations.push(OperationRecord {
            body,
            opcode,
            target,
            dest,
            a,
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span::default(),
            flags,
        });
    };
    match phase {
        Initialization::Target(target) => {
            emit(Opcode::Initialize, target, ValueId::NONE, ValueId::NONE, 0)
        }
        Initialization::Unknown => emit(
            Opcode::Unknown,
            SymbolId::NONE,
            ValueId::NONE,
            ValueId::NONE,
            0,
        ),
        Initialization::KnownEmpty => (),
    }
    emit(
        Opcode::LoadField,
        target,
        ValueId(1),
        ValueId::NONE,
        OP_STATIC_FIELD,
    );
    emit(Opcode::Return, SymbolId::NONE, ValueId::NONE, ValueId(1), 0);
    drop(emit);
    let mut hash = Sha256::new();
    hash.update(VERSION);
    hash.update(candidate.evidence.0);
    hash.update(class.hash.0);
    match phase {
        Initialization::Unknown => hash.update([0]),
        Initialization::KnownEmpty => hash.update([1]),
        Initialization::Target(target) => {
            hash.update([2]);
            let name = facts.symbol_name(target);
            hash.update((name.len() as u64).to_le_bytes());
            hash.update(name.as_bytes());
        }
    }
    let proof = ContentHash(hash.finalize().into());
    facts.bodies.push(BodyRecord {
        symbol,
        file,
        span: Span::default(),
        name_span: Span::default(),
        operations: IdRange {
            start,
            len: facts.operations.len() as u32 - start,
        },
        parameters: IdRange::default(),
        body_hash: proof,
        flags: BODY_BINARY_RECIPE,
    });
    Ok(Some((symbol, proof)))
}

pub(crate) fn declare_globals(
    facts: &mut FactSnapshot,
    inputs: &mut OwnedBinaryInputs,
    registry: &mut Registry,
    candidates: &[Candidate],
    pending: &mut VecDeque<MethodKey>,
) -> Result<HashMap<SymbolId, (SymbolId, ContentHash)>, Error> {
    let mut result = HashMap::new();
    if !candidates.iter().any(|candidate| candidate.global) {
        return Ok(result);
    }
    for (index, context) in inputs.contexts.iter_mut().enumerate() {
        let mut loader = context_loader(context, &inputs.admitted)?;
        for candidate in candidates {
            if !candidate.global || facts.symbols[candidate.symbol.index()].context != context.id {
                continue;
            }
            let previous = (context.active_method, context.active_file);
            context.active_method = candidate.symbol;
            context.active_file = facts.symbols[candidate.symbol.index()].file;
            let value = declare(
                facts,
                registry,
                index,
                context,
                &mut loader,
                candidate,
                pending,
            );
            let declared =
                optional_effect(facts, context, candidate.symbol, FileId::NONE, value, None)?;
            (context.active_method, context.active_file) = previous;
            if let Some(value) = declared {
                result.insert(candidate.symbol, value);
            }
        }
    }
    Ok(result)
}

#[cfg(test)]
#[path = "binary_top_modules_tests.rs"]
mod tests;
