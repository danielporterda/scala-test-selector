//! A descriptor/class-bound additive element view, not a Seq implementation.
//! Native calls and their effects/unknown results remain present. A container
//! has no concrete class; transfer keeps an explicit partial-operation guard.
use super::*;

const POLICY: &[u8] = b"native-sequence-element-view/1";
const OWNER: &str = "scala/collection/SeqOps";
const COMPILER: &str = "scala/collection/SeqOps#apply().";
const DESCRIPTOR: &str = "(I)Ljava/lang/Object;";

fn authority(
    facts: &FactSnapshot,
    inputs: &OwnedBinaryInputs,
    key: &MethodKey,
    data: &MethodData,
) -> Option<ContentHash> {
    if key.owner != OWNER
        || key.name != "apply"
        || key.descriptor != DESCRIPTOR
        || data.flags & 0x0008 != 0
        || data.receiver_parameter.is_some()
        || facts.symbol_name(data.symbol) != COMPILER
    {
        return None;
    }
    let context = inputs.contexts.get(key.context)?;
    if facts.symbols[data.symbol.index()].context != context.id {
        return None;
    }
    let CachedClass::Found(class) = context.classes.get(OWNER)? else {
        return None;
    };
    let method = class.metadata.method("apply", Some(DESCRIPTOR)).ok()?;
    if class.hash == ContentHash::default()
        || class.metadata.hash() != class.hash
        || class.metadata.name() != OWNER
        || class.metadata.flags() & 0x0200 == 0
        || method.flags != data.flags
        || method.flags & 0x0008 != 0
    {
        return None;
    }
    let mut hash = Sha256::new();
    hash.update(POLICY);
    hash.update(class.hash.0);
    for text in [
        key.owner.as_str(),
        key.name.as_str(),
        key.descriptor.as_str(),
    ] {
        hash.update((text.len() as u64).to_le_bytes());
        hash.update(text.as_bytes());
    }
    hash.update(method.flags.to_le_bytes());
    Some(ContentHash(hash.finalize().into()))
}

pub(super) fn augment(
    facts: &mut FactSnapshot,
    registry: &Registry,
    inputs: &OwnedBinaryInputs,
) -> Result<usize, Error> {
    // Most native programs have no exact SeqOps compiler endpoint. Avoid a
    // per-symbol table: retain only the tiny admitted adapter authority set.
    let mut authorities: HashMap<SymbolId, Option<ContentHash>> = HashMap::new();
    for (key, data) in &registry.methods {
        if facts.symbol_name(data.symbol) != COMPILER {
            continue;
        }
        let admitted = authority(facts, inputs, key, data);
        match authorities.entry(data.symbol) {
            std::collections::hash_map::Entry::Vacant(slot) => {
                slot.insert(admitted);
            }
            std::collections::hash_map::Entry::Occupied(mut slot) => {
                // Competing native declarations revoke this exact certificate.
                slot.insert(None);
            }
        }
    }
    let mut changed = 0;
    for body in &mut facts.bodies {
        let mut hash = None;
        for (ordinal, op) in facts.operations[body.operations.range()]
            .iter_mut()
            .enumerate()
        {
            // Source recipes cannot supply this native admission bit themselves.
            // Re-enrichment uses original captured facts; never honor stale bits.
            op.flags &= !OP_SEQUENCE_ELEMENT_VIEW;
            if !matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
                || op.dest.is_none()
                || op.a.is_none()
                || op.arguments.len != 1
                || op.flags & (OP_SUPER | OP_QUALIFIED_SUPER | OP_SYNTHETIC_PARAMETER_APPLY) != 0
            {
                continue;
            }
            let Some(Some(authority)) = authorities.get(&op.target) else {
                continue;
            };
            op.flags |= OP_SEQUENCE_ELEMENT_VIEW;
            let hash = hash.get_or_insert_with(|| {
                let mut hash = Sha256::new();
                hash.update(POLICY);
                hash.update(body.body_hash.0);
                hash
            });
            hash.update((ordinal as u64).to_le_bytes());
            hash.update(authority.0);
            changed += 1;
        }
        if let Some(hash) = hash {
            body.body_hash = ContentHash(hash.finalize().into());
        }
    }
    Ok(changed)
}

#[cfg(test)]
#[path = "binary_sequence_tests.rs"]
mod tests;
