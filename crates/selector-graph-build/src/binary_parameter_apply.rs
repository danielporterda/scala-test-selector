//! Reassemble compiler-tagged parameter clauses only after exact JVM admission.
//! No source spelling or inferred callable result supplies method arity here.
use super::*;

const VERSION: &[u8] = b"binary-parameter-apply/2";

#[derive(Clone, Copy)]
struct Authority {
    parameters: u32,
    evidence: ContentHash,
    body: bool,
}

fn field(hash: &mut Sha256, bytes: &[u8]) {
    hash.update((bytes.len() as u64).to_le_bytes());
    hash.update(bytes);
}

fn authorities(facts: &FactSnapshot, registry: &Registry) -> HashMap<SymbolId, Option<Authority>> {
    let mut result = HashMap::with_capacity(registry.methods.len());
    for (key, data) in &registry.methods {
        if matches!(key.name.as_str(), "<init>" | "<clinit>" | "$init$") {
            continue;
        }
        let Ok(descriptor) = binary::method_descriptor(&key.descriptor) else {
            continue;
        };
        if data
            .receiver_parameter
            .is_some_and(|p| data.flags & 8 == 0 || p as usize >= descriptor.parameter_count)
        {
            continue;
        }
        let parameters =
            descriptor.parameter_count - usize::from(data.receiver_parameter.is_some());
        let Ok(parameters) = u32::try_from(parameters) else {
            continue;
        };
        let mut hash = Sha256::new();
        hash.update(VERSION);
        field(&mut hash, key.owner.as_bytes());
        field(&mut hash, key.name.as_bytes());
        field(&mut hash, key.descriptor.as_bytes());
        hash.update(data.receiver_parameter.unwrap_or(u16::MAX).to_le_bytes());
        let authority = Authority {
            parameters,
            evidence: ContentHash(hash.finalize().into()),
            body: false,
        };
        // A compiler identity mapped to competing JVM declarations is not an
        // authority, even when the declarations happen to have equal arity.
        match result.entry(data.symbol) {
            std::collections::hash_map::Entry::Vacant(slot) => {
                slot.insert(Some(authority));
            }
            std::collections::hash_map::Entry::Occupied(mut slot) => {
                slot.insert(None);
            }
        }
    }
    for body in &facts.bodies {
        let Some(slot) = result.get_mut(&body.symbol) else {
            continue;
        };
        let Some(authority) = slot else { continue };
        let file = facts.files[body.file.index()];
        if authority.body
            || body.flags & BODY_BINARY_RECIPE == 0
            || file.flags & FILE_BINARY_SOURCE == 0
            || body.parameters.len != authority.parameters
            || body.body_hash != file.source_hash
            || file.source_hash == ContentHash::default()
            || file.context != facts.symbols[body.symbol.index()].context
        {
            *slot = None;
        } else {
            let mut hash = Sha256::new();
            hash.update(authority.evidence.0);
            hash.update(file.source_hash.0);
            authority.evidence = ContentHash(hash.finalize().into());
            authority.body = true;
        }
    }
    result
}

fn entries(rows: &[(ValueId, usize)], value: ValueId) -> &[(ValueId, usize)] {
    let begin = rows.partition_point(|&(id, _)| id < value);
    let end = rows.partition_point(|&(id, _)| id <= value);
    &rows[begin..end]
}

/// Operations and pooled operands keep their IDs. Only exact result clauses on
/// a moved method operation are rebound to the final operation's stable slot.
pub(super) fn augment(facts: &mut FactSnapshot, registry: &Registry) -> Result<usize, Error> {
    if !facts
        .operations
        .iter()
        .any(|op| op.flags & OP_SYNTHETIC_PARAMETER_APPLY != 0)
    {
        return Ok(0);
    }
    let authority = authorities(facts, registry);
    let mut uses = Vec::new();
    let mut definitions = Vec::new();
    let mut chain = Vec::new();
    let mut arguments = Vec::new();
    let mut held = Vec::new();
    let mut moved = Vec::new();
    let mut repaired = 0;
    for body_index in 0..facts.bodies.len() {
        let body = facts.bodies[body_index];
        if body.flags & BODY_BINARY_RECIPE != 0
            || !facts.operations[body.operations.range()]
                .iter()
                .any(|op| op.flags & OP_SYNTHETIC_PARAMETER_APPLY != 0)
        {
            continue;
        }
        uses.clear();
        definitions.clear();
        for (offset, op) in facts.operations[body.operations.range()].iter().enumerate() {
            if !op.dest.is_none() {
                definitions.push((op.dest, offset));
            }
            // Counting unused a/b fields too can only reject an optimization;
            // it never hides an actual use or escape of an intermediate value.
            for id in [op.a, op.b]
                .into_iter()
                .chain(facts.operands[op.arguments.range()].iter().copied())
            {
                if !id.is_none() {
                    uses.push((id, offset));
                }
            }
        }
        uses.sort_unstable();
        definitions.sort_unstable();
        let mut hash: Option<Sha256> = None;
        for prefix in body.operations.range() {
            let original = facts.operations[prefix];
            if !matches!(original.opcode, Opcode::Call | Opcode::VirtualCall)
                || original.dest.is_none()
                || original.flags
                    & (OP_MACRO_EXPANSION | OP_MACRO_RESULT_TYPE | OP_MACRO_DIRECT_TREE)
                    != 0
            {
                continue;
            }
            let Some(Some(proof)) = authority.get(&original.target) else {
                continue;
            };
            if !proof.body || original.arguments.len >= proof.parameters {
                continue;
            }
            chain.clear();
            arguments.clear();
            held.clear();
            chain.push(prefix);
            arguments.extend_from_slice(&facts.operands[original.arguments.range()]);
            held.extend(arguments.iter().copied().map(|id| (id, prefix)));
            if !original.a.is_none() {
                held.push((original.a, prefix));
            }
            let mut current = prefix;
            let mut valid = false;
            while arguments.len() < proof.parameters as usize {
                let value = facts.operations[current].dest;
                let defs = entries(&definitions, value);
                let reads = entries(&uses, value);
                if value.is_none()
                    || defs.len() != 1
                    || defs[0].1 + body.operations.start as usize != current
                    || reads.len() != 1
                {
                    break;
                }
                let next = body.operations.start as usize + reads[0].1;
                let op = facts.operations[next];
                if next <= current
                    || op.opcode != Opcode::InvokeCallback
                    || op.a != value
                    || !op.target.is_none()
                    || op.flags != OP_SYNTHETIC_PARAMETER_APPLY
                    || op.arguments.len == 0
                {
                    break;
                }
                chain.push(next);
                let clause = &facts.operands[op.arguments.range()];
                arguments.extend_from_slice(clause);
                held.extend(clause.iter().copied().map(|id| (id, next)));
                current = next;
                if arguments.len() == proof.parameters as usize {
                    valid = true;
                    break;
                }
            }
            if !valid {
                continue;
            }
            // Moving the call must not reread a mutable value after intervening
            // argument effects, or consume one of the removed partial results.
            if held.iter().any(|&(id, at)| {
                chain[..chain.len() - 1]
                    .iter()
                    .any(|&index| facts.operations[index].dest == id)
                    || entries(&definitions, id).iter().any(|&(_, offset)| {
                        let index = offset + body.operations.start as usize;
                        index > at && index <= current
                    })
            }) {
                continue;
            }
            let start = u32::try_from(facts.operands.len())
                .map_err(|_| Error::Limit("curried operands"))?;
            let len =
                u32::try_from(arguments.len()).map_err(|_| Error::Limit("curried arguments"))?;
            start
                .checked_add(len)
                .ok_or(Error::Limit("curried operand range"))?;
            facts.operands.extend_from_slice(&arguments);
            let final_operation = facts.operations[current];
            let state = hash.get_or_insert_with(|| {
                let mut hash = Sha256::new();
                hash.update(VERSION);
                hash.update(body.body_hash.0);
                hash
            });
            state.update(proof.evidence.0);
            field(state, facts.symbol_name(original.target).as_bytes());
            field(
                state,
                facts
                    .text(facts.symbols[original.target.index()].context)
                    .as_bytes(),
            );
            for value in [
                original.opcode as u32,
                original.flags,
                original.a.0,
                original.b.0,
                final_operation.dest.0,
            ] {
                state.update(value.to_le_bytes());
            }
            // Absolute source coordinates are evidence, not method semantics.
            // The raw owned-body digest already binds source-sensitive Unknown
            // and Constant operations (including actual position-macro data).
            // Inserting unrelated text before this body must not seed it as a
            // changed method. Keep spans on the operations for explanations.
            state.update((chain.len() as u64).to_le_bytes());
            for &index in &chain {
                state.update(((index - body.operations.start as usize) as u64).to_le_bytes());
            }
            state.update((arguments.len() as u64).to_le_bytes());
            for id in &arguments {
                state.update(id.0.to_le_bytes());
            }
            for &index in &chain[..chain.len() - 1] {
                let op = &mut facts.operations[index];
                op.opcode = Opcode::Constant;
                op.target = SymbolId::NONE;
                op.a = ValueId::NONE;
                op.b = ValueId::NONE;
                op.arguments = IdRange::default();
                op.flags = 0;
            }
            facts.operations[current] = OperationRecord {
                dest: final_operation.dest,
                span: final_operation.span,
                arguments: IdRange { start, len },
                ..original
            };
            moved.push((OperationId(prefix as u32), OperationId(current as u32)));
            repaired += 1;
        }
        if let Some(hash) = hash {
            facts.bodies[body_index].body_hash = ContentHash(hash.finalize().into());
        }
    }
    if !moved.is_empty() {
        moved.sort_unstable();
        for bound in &mut facts.result_bounds {
            if let Ok(index) = moved.binary_search_by_key(&bound.operation, |&(old, _)| old) {
                bound.operation = moved[index].1;
            }
        }
        facts
            .result_bounds
            .sort_unstable_by_key(|bound| (bound.symbol, bound.operation));
    }
    Ok(repaired)
}

#[cfg(test)]
#[path = "binary_parameter_apply_tests.rs"]
mod tests;
