//! Explicit, user-authorized data-property laws for the reviewed WordSpec API.
//!
//! These are logical slots, not claims about JVM backing-field declarations.
//! Native property implementations share the law; written source methods and
//! source value initializers keep their original execution and precedence.
use super::*;
use selector_framework::scalatest_execution::{self as contract, AccessorKind};

const VERSION: &[u8] = b"trusted-wordspec-data-accessors/1";

#[derive(Default)]
pub(super) struct State {
    slots: HashMap<usize, [SymbolId; 8]>,
    pub(super) modeled: HashSet<SymbolId>,
    bound_source_overrides: HashSet<(SymbolId, SymbolId)>,
    // Only owners with one of the sixteen relevant source names are retained.
    source_members: HashMap<String, u8>,
    conflicts: HashSet<SymbolId>,
    conflicted_contexts: HashSet<StrId>,
    global_conflict: bool,
    owners: HashMap<usize, HashMap<String, [bool; 8]>>,
}

fn source_index(facts: &FactSnapshot, state: &mut State) {
    for issue in &facts.issues {
        if issue.kind != IssueKind::ContextConflict {
            continue;
        }
        if !issue.symbol.is_none() {
            state.conflicts.insert(issue.symbol);
        } else if !issue.file.is_none() {
            state
                .conflicted_contexts
                .insert(facts.files[issue.file.index()].context);
        } else {
            state.global_conflict = true;
        }
    }
    for declaration in &facts.symbols {
        if declaration.flags & SYMBOL_DEFINED == 0 {
            continue;
        }
        if declaration.owner.is_none() {
            continue;
        }
        let owner = &facts.symbols[declaration.owner.index()];
        if owner.flags & SYMBOL_DEFINED == 0 || !matches!(owner.kind, 10 | 13 | 14) {
            continue;
        }
        let Some(name) = selector_types::symbol::member_name(facts.text(declaration.name)) else {
            continue;
        };
        let mask = contract::ACCESSORS
            .iter()
            .enumerate()
            .fold(0u8, |mask, (ordinal, spec)| {
                let relevant = name == spec.getter
                    || name == spec.setter
                    || name.strip_suffix("_=") == Some(spec.getter)
                    || name.strip_suffix("_$eq") == Some(spec.getter)
                    || (name.ends_with("_=")
                        && name.strip_suffix("_=") == spec.setter.strip_suffix("_$eq"));
                mask | if relevant { 1 << ordinal } else { 0 }
            });
        if mask != 0
            && let Some(owner) =
                selector_types::symbol::jvm_owner(facts.symbol_name(declaration.owner))
        {
            *state.source_members.entry(owner).or_default() |= mask;
        }
    }
}

fn pinned_trait(context: &AdmittedContext) -> bool {
    let Some(CachedClass::Found(bytes)) = context.classes.get(contract::WORDSPEC) else {
        return false;
    };
    bytes.metadata.name() == contract::WORDSPEC
        && bytes.metadata.hash() == bytes.hash
        && ContentHash::from_hex(contract::WORDSPEC_CLASS_SHA256).is_ok_and(|h| h == bytes.hash)
        && context.entries.iter().enumerate().any(|(index, entry)| {
            !context.entries[..index]
                .iter()
                .any(|earlier| matches!(earlier.kind, EntryKind::Unavailable))
                && matches!(entry.kind, EntryKind::Jar)
                && ContentHash::from_hex(contract::WORDSPEC_ARCHIVE)
                    .is_ok_and(|h| h == entry.sha256)
                && bytes.origin == format!("{}!/{}.class", entry.path.display(), contract::WORDSPEC)
        })
}

fn descriptors(spec: &contract::Accessor) -> (String, String) {
    (
        format!("(){}", spec.value_descriptor),
        format!("({})V", spec.value_descriptor),
    )
}

/// Called once after exact mandatory bindings have resolved their providers,
/// before optional fair shares are computed. Unreferenced contexts do no work.
pub(super) fn declare(
    facts: &mut FactSnapshot,
    inputs: &mut OwnedBinaryInputs,
    registry: &mut Registry,
    pending: &mut VecDeque<MethodKey>,
    existing: &mut HashSet<SymbolId>,
) -> Result<(), Error> {
    source_index(facts, &mut registry.accessors);
    for index in 0..inputs.contexts.len() {
        if registry.accessors.global_conflict
            || registry
                .accessors
                .conflicted_contexts
                .contains(&inputs.contexts[index].id)
            || !registry
                .methods
                .keys()
                .any(|key| key.context == index && key.owner == contract::WORDSPEC)
            || !pinned_trait(&inputs.contexts[index])
        {
            continue;
        }
        let context = &mut inputs.contexts[index];
        let Some(CachedClass::Found(bytes)) = context.classes.get(contract::WORDSPEC) else {
            continue;
        };
        let bytes = bytes.clone();
        // The explicit API, not getter spelling conventions, supplies the law.
        if !contract::ACCESSORS.iter().all(|spec| {
            let (get, set) = descriptors(spec);
            [(spec.getter, get.as_str()), (spec.setter, set.as_str())]
                .iter()
                .all(|(name, desc)| {
                    bytes
                        .metadata
                        .method(name, Some(desc))
                        .is_ok_and(|method| method.flags & 0x000b == 1)
                })
        }) {
            continue;
        }
        let mut loader = context_loader(context, &inputs.admitted)?;
        let file = registry.file(facts, index, context.id, contract::WORDSPEC, &bytes)?;
        let owner = registry.class(facts, index, context.id, contract::WORDSPEC, file, &bytes)?;
        let mut slots = [SymbolId::NONE; 8];
        for (ordinal, spec) in contract::ACCESSORS.iter().enumerate() {
            let name = append_text(
                facts,
                &format!("{}{}", contract::ACCESSOR_NAMESPACE, spec.slot),
            )?;
            slots[ordinal] = SymbolId::checked(facts.symbols.len())?;
            facts.symbols.push(SymbolRecord {
                name,
                display: StrId::NONE,
                owner,
                file: FileId::NONE,
                context: context.id,
                kind: 20,
                properties: 0,
                signature: StrId::NONE,
                span: Span::default(),
                flags: 0,
            });
        }
        registry.accessors.slots.insert(index, slots);
        for spec in contract::ACCESSORS {
            let (get, set) = descriptors(spec);
            for (name, descriptor) in [(spec.getter, get), (spec.setter, set)] {
                let symbol = registry.method(
                    facts,
                    index,
                    context,
                    &mut loader,
                    MemberRef {
                        owner: contract::WORDSPEC,
                        name,
                        descriptor: &descriptor,
                    },
                    None,
                    None,
                    pending,
                )?;
                let key = MethodKey {
                    context: index,
                    owner: contract::WORDSPEC.into(),
                    name: name.into(),
                    descriptor,
                };
                let data = registry.methods[&key].clone();
                if materialize(
                    facts,
                    registry,
                    index,
                    context,
                    &mut loader,
                    &key,
                    &data,
                    existing,
                )? {
                    existing.insert(symbol);
                }
            }
        }
    }
    // A direct, compiler-bound custom method remains an ordinary dispatch
    // target. A value initializer is not such a getter implementation.
    let mut source_methods = vec![false; facts.symbols.len()];
    for body in &facts.bodies {
        if body.flags & (BODY_BINARY_RECIPE | BODY_INITIALIZER) == 0
            && facts.symbols[body.symbol.index()].flags & SYMBOL_DEFINED != 0
            && !body.file.is_none()
            && facts.files[body.file.index()].flags & (SOURCE_VERIFIED | SYNTAX_VERIFIED)
                == SOURCE_VERIFIED | SYNTAX_VERIFIED
        {
            source_methods[body.symbol.index()] = true;
        }
    }
    for relation in &facts.relations {
        if relation.kind == RelationKind::Override
            && registry.accessors.modeled.contains(&relation.target)
            && source_methods[relation.source.index()]
        {
            let source = &facts.symbols[relation.source.index()];
            if !source.owner.is_none() {
                registry
                    .accessors
                    .bound_source_overrides
                    .insert((source.owner, relation.target));
            }
        }
    }
    Ok(())
}

pub(super) fn modeled_contract(registry: &Registry, contract: SymbolId) -> bool {
    registry.accessors.modeled.contains(&contract)
}

pub(super) fn bound_source_override(
    registry: &Registry,
    receiver: SymbolId,
    contract: SymbolId,
) -> bool {
    registry
        .accessors
        .bound_source_overrides
        .contains(&(receiver, contract))
}

fn source_blocks(state: &State, owner: &str, ordinal: usize) -> bool {
    state
        .source_members
        .get(owner)
        .is_some_and(|mask| mask & (1 << ordinal) != 0)
}

/// Positive selected-header ancestry, plus source precedence. No native method
/// Code/absence proof is needed for these explicitly trusted property laws.
fn eligible(
    facts: &FactSnapshot,
    registry: &mut Registry,
    index: usize,
    context: &mut AdmittedContext,
    loader: &mut CapturedClasspath,
    owner: &str,
) -> Result<[bool; 8], Error> {
    if registry.accessors.global_conflict
        || registry.accessors.conflicted_contexts.contains(&context.id)
        || !registry.accessors.slots.contains_key(&index)
    {
        return Ok([false; 8]);
    }
    if let Some(result) = registry
        .accessors
        .owners
        .get(&index)
        .and_then(|owners| owners.get(owner))
    {
        return Ok(*result);
    }
    if !pinned_trait(context) {
        return Ok([false; 8]);
    }
    let mut allowed = [true; 8];
    let mut trait_found = false;
    let mut pending = vec![owner.to_owned()];
    let mut seen = HashSet::new();
    while let Some(owner) = pending.pop() {
        if owner == "java/lang/Object" || !seen.insert(owner.clone()) {
            continue;
        }
        if seen.len() > context.admission.limits.classes_per_context {
            return Ok([false; 8]);
        }
        let bytes = match cache_class(context, loader, &owner) {
            Ok(Some(bytes)) => bytes,
            // Failed semantic proof never certifies an accessor or deletes the
            // normal caller's class/body/provenance frontier.
            Ok(None) | Err(Error::Limit(_)) => return Ok([false; 8]),
            Err(error) => return Err(error),
        };
        let metadata = &bytes.metadata;
        if metadata.name() != owner || metadata.hash() != bytes.hash {
            return Err(Error::Invalid("accessor ancestor header"));
        }
        trait_found |= owner == contract::WORDSPEC;
        let application_product = context.entries.iter().any(|entry| {
            matches!(entry.kind, EntryKind::Directory { .. })
                && bytes.origin
                    == entry
                        .path
                        .join(format!("{owner}.class"))
                        .display()
                        .to_string()
        });
        let source_owner = registry
            .types
            .get(&(index, owner.clone()))
            .is_some_and(|symbol| {
                let declaration = &facts.symbols[symbol.index()];
                declaration.flags & SYMBOL_DEFINED != 0
                    && matches!(declaration.kind, 10 | 13 | 14)
                    && !declaration.file.is_none()
                    && facts.files[declaration.file.index()].flags
                        & (SOURCE_VERIFIED | SYNTAX_VERIFIED)
                        == SOURCE_VERIFIED | SYNTAX_VERIFIED
            });
        let conflicted = registry
            .types
            .get(&(index, owner.clone()))
            .is_some_and(|symbol| registry.accessors.conflicts.contains(symbol));
        let untyped_source_owner =
            registry
                .types
                .get(&(index, owner.clone()))
                .is_some_and(|symbol| {
                    let declaration = &facts.symbols[symbol.index()];
                    declaration.flags & SYMBOL_DEFINED != 0
                        && !matches!(declaration.kind, 10 | 13 | 14)
                });
        for (ordinal, spec) in contract::ACCESSORS.iter().enumerate() {
            if conflicted
                || untyped_source_owner
                || source_blocks(&registry.accessors, &owner, ordinal)
                || (application_product
                    && !source_owner
                    && metadata
                        .methods()
                        .any(|method| method.name == spec.getter || method.name == spec.setter))
            {
                allowed[ordinal] = false;
            }
        }
        if owner != contract::WORDSPEC {
            pending.extend(
                metadata
                    .parent()
                    .into_iter()
                    .chain(metadata.interfaces())
                    .map(str::to_owned),
            );
        }
    }
    if !trait_found {
        allowed = [false; 8];
    }
    registry
        .accessors
        .owners
        .entry(index)
        .or_default()
        .insert(owner.to_owned(), allowed);
    Ok(allowed)
}

fn pair(name: &str, descriptor: &str) -> Option<(usize, AccessorKind)> {
    contract::accessor(contract::WORDSPEC, name, descriptor).map(|(spec, kind)| {
        (
            contract::ACCESSORS
                .iter()
                .position(|s| s.slot == spec.slot)
                .unwrap(),
            kind,
        )
    })
}

/// The same function handles predeclared trait properties and any ordinarily
/// admitted native implementation. Source-owned bodies are never replaced.
pub(super) fn materialize(
    facts: &mut FactSnapshot,
    registry: &mut Registry,
    index: usize,
    context: &mut AdmittedContext,
    loader: &mut CapturedClasspath,
    key: &MethodKey,
    data: &MethodData,
    existing: &HashSet<SymbolId>,
) -> Result<bool, Error> {
    let Some((ordinal, kind)) = pair(&key.name, &key.descriptor) else {
        return Ok(false);
    };
    if existing.contains(&data.symbol)
        || facts.symbols[data.symbol.index()].flags & SYMBOL_DEFINED != 0
        || facts.symbols[data.symbol.index()].context != context.id
        || registry.accessors.conflicts.contains(&data.symbol)
        || data.flags & 0x000b != 1
        || data.receiver_parameter.is_some()
        || !eligible(facts, registry, index, context, loader, &key.owner)?[ordinal]
    {
        return Ok(false);
    }
    let slot = registry.accessors.slots[&index][ordinal];
    let Some(CachedClass::Found(bytes)) = context.classes.get(&key.owner) else {
        return Ok(false);
    };
    let bytes = bytes.clone();
    let file = registry.file(facts, index, context.id, &key.owner, &bytes)?;
    let body = BodyId::checked(facts.bodies.len())?;
    let start =
        u32::try_from(facts.operations.len()).map_err(|_| Error::Limit("accessor operations"))?;
    let parameters = IdRange {
        start: u32::try_from(facts.operands.len())
            .map_err(|_| Error::Limit("accessor parameters"))?,
        len: u32::from(kind == AccessorKind::Set),
    };
    if kind == AccessorKind::Set {
        facts.operands.push(ValueId(1));
    }
    let mut operation = |opcode, target, dest, a, b| {
        facts.operations.push(OperationRecord {
            body,
            opcode,
            target,
            dest,
            a,
            b,
            arguments: IdRange::default(),
            span: Span::default(),
            flags: 0,
        })
    };
    if kind == AccessorKind::Get {
        operation(
            Opcode::LoadField,
            slot,
            ValueId(1),
            ValueId(0),
            ValueId::NONE,
        );
        operation(
            Opcode::Return,
            SymbolId::NONE,
            ValueId::NONE,
            ValueId(1),
            ValueId::NONE,
        );
    } else {
        operation(
            Opcode::Parameter,
            SymbolId::NONE,
            ValueId(1),
            ValueId::NONE,
            ValueId::NONE,
        );
        operation(
            Opcode::StoreField,
            slot,
            ValueId::NONE,
            ValueId(0),
            ValueId(1),
        );
    }
    let mut hash = Sha256::new();
    hash.update(VERSION);
    hash.update(SelectionContract::VERSION.as_bytes());
    hash.update(bytes.hash.0);
    hash.update(context.name.as_bytes());
    hash.update(key.owner.as_bytes());
    hash.update(key.name.as_bytes());
    hash.update(key.descriptor.as_bytes());
    facts.bodies.push(BodyRecord {
        symbol: data.symbol,
        file,
        span: Span::default(),
        name_span: Span::default(),
        operations: IdRange { start, len: 2 },
        parameters,
        body_hash: ContentHash(hash.finalize().into()),
        flags: BODY_BINARY_RECIPE,
    });
    registry.accessors.modeled.insert(data.symbol);
    context.cache_metrics.trusted_runtime_models += 1;
    Ok(true)
}

pub(super) fn trusted_receiver(
    facts: &FactSnapshot,
    registry: &mut Registry,
    index: usize,
    context: &mut AdmittedContext,
    loader: &mut CapturedClasspath,
    owner: &str,
    contract: SymbolId,
    name: &str,
    descriptor: &str,
) -> Result<bool, Error> {
    let Some((ordinal, _)) = pair(name, descriptor) else {
        return Ok(false);
    };
    Ok(registry.accessors.modeled.contains(&contract)
        && eligible(facts, registry, index, context, loader, owner)?[ordinal])
}

pub(super) fn backing_field(
    facts: &FactSnapshot,
    registry: &mut Registry,
    index: usize,
    context: &mut AdmittedContext,
    loader: &mut CapturedClasspath,
    member: MemberRef<'_>,
    flags: u16,
) -> Result<Option<SymbolId>, Error> {
    if flags & 8 != 0 {
        return Ok(None);
    }
    let Some(ordinal) = contract::ACCESSORS
        .iter()
        .position(|spec| spec.getter == member.name && spec.value_descriptor == member.descriptor)
    else {
        return Ok(None);
    };
    if eligible(facts, registry, index, context, loader, member.owner)?[ordinal] {
        Ok(Some(registry.accessors.slots[&index][ordinal]))
    } else {
        Ok(None)
    }
}

#[cfg(test)]
#[path = "binary_accessors_tests.rs"]
mod tests;
