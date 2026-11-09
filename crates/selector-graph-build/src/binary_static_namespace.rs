//! A compiler class qualifier is a static namespace, never a receiver field.
//! Only admitted class bytes and exclusively static receiver uses license this
//! repair. Native call recipes, initialization and uncertainty stay executable.
use super::*;

const VERSION: &[u8] = b"binary-static-namespace/1";

#[derive(Clone, Copy)]
struct Authority {
    owner: SymbolId,
    context: StrId,
    parameters: u32,
    class_hash: ContentHash,
    evidence: ContentHash,
    body: bool,
}

fn field(hash: &mut Sha256, bytes: &[u8]) {
    hash.update((bytes.len() as u64).to_le_bytes());
    hash.update(bytes);
}

fn source_body(facts: &FactSnapshot, body: &BodyRecord) -> bool {
    body.flags & BODY_BINARY_RECIPE == 0
        && facts.files[body.file.index()].flags
            & (SOURCE_VERIFIED | SYNTAX_VERIFIED | FILE_BINARY_SOURCE)
            == SOURCE_VERIFIED | SYNTAX_VERIFIED
}

fn namespace(facts: &FactSnapshot, body: &BodyRecord, op: &OperationRecord) -> bool {
    if op.opcode != Opcode::LoadField
        || op.target.is_none()
        || op.dest.is_none()
        || op.dest == ValueId(0)
        || !matches!(op.a, ValueId::NONE | ValueId(0))
        || !op.b.is_none()
        || op.arguments.len != 0
        || op.flags != 0
    {
        return false;
    }
    let class = facts.symbols[op.target.index()];
    // Compiler nominal identities keep their spelling and gain header
    // authority; SYMBOL_NATIVE_BINARY instead describes new @jvm identities.
    matches!(class.kind, 13 | 14)
        && class.flags & (SYMBOL_DEFINED | SYMBOL_JVM_CLASS_HEADER_VERIFIED)
            == SYMBOL_JVM_CLASS_HEADER_VERIFIED
        && class.context == facts.files[body.file.index()].context
        && facts.symbol_name(op.target).ends_with('#')
}

fn authorities(
    facts: &FactSnapshot,
    registry: &Registry,
    inputs: &OwnedBinaryInputs,
    candidates: &[SymbolId],
) -> HashMap<SymbolId, Option<Authority>> {
    let mut result = HashMap::with_capacity(candidates.len());
    let mut namespaces = HashMap::new();
    for (key, data) in &registry.methods {
        if candidates.binary_search(&data.symbol).is_err() {
            continue;
        }
        let proof = (|| {
            let context = inputs.contexts.get(key.context)?;
            if data.flags & 0x0008 == 0
                || data.receiver_parameter.is_some()
                || matches!(key.name.as_str(), "<init>" | "<clinit>" | "$init$")
                || facts.symbols[data.symbol.index()].flags & SYMBOL_DEFINED != 0
                || facts.symbols[data.symbol.index()].context != context.id
                || facts.symbols[data.owner.index()].context != context.id
            {
                return None;
            }
            let CachedClass::Found(class) = context.classes.get(key.owner.as_str())? else {
                return None;
            };
            let info = class.metadata.as_ref();
            if info.name() != key.owner
                || info.hash() != class.hash
                || class.hash == ContentHash::default()
                || !*namespaces
                    .entry((key.context, key.owner.as_str()))
                    .or_insert_with(|| !info.fields().any(|field| field.name == "MODULE$"))
            {
                return None;
            }
            let method = info.method(&key.name, Some(&key.descriptor)).ok()?;
            if method.flags != data.flags {
                return None;
            }
            let descriptor = binary::method_descriptor(&key.descriptor).ok()?;
            let parameters = u32::try_from(descriptor.parameter_count).ok()?;
            let mut hash = Sha256::new();
            hash.update(VERSION);
            hash.update(class.hash.0);
            field(&mut hash, facts.text(context.id).as_bytes());
            field(&mut hash, key.owner.as_bytes());
            field(&mut hash, key.name.as_bytes());
            field(&mut hash, key.descriptor.as_bytes());
            hash.update(data.flags.to_le_bytes());
            Some(Authority {
                owner: data.owner,
                context: context.id,
                parameters,
                class_hash: class.hash,
                evidence: ContentHash(hash.finalize().into()),
                body: false,
            })
        })();
        // Every competing binding poisons the identity, including one that is
        // unavailable, instance-only, or has otherwise unusable authority.
        match result.entry(data.symbol) {
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(proof);
            }
            std::collections::hash_map::Entry::Occupied(mut entry) => {
                entry.insert(None);
            }
        }
    }
    for body in &facts.bodies {
        let Some(Some(proof)) = result.get_mut(&body.symbol) else {
            continue;
        };
        let file = facts.files[body.file.index()];
        if proof.body
            || body.flags & BODY_BINARY_RECIPE == 0
            || file.flags & FILE_BINARY_SOURCE == 0
            || file.context != proof.context
            || file.source_hash != proof.class_hash
            || body.body_hash != proof.class_hash
            || body.parameters.len != proof.parameters
        {
            result.insert(body.symbol, None);
        } else {
            // Its unchanged native entry recipe retains class initialization.
            proof.body = true;
        }
    }
    result
}

fn entries(rows: &[(ValueId, usize)], value: ValueId) -> &[(ValueId, usize)] {
    let start = rows.partition_point(|&(id, _)| id < value);
    let end = rows.partition_point(|&(id, _)| id <= value);
    &rows[start..end]
}

/// Stable operation/operand IDs: the namespace becomes an empty scalar receiver,
/// and certified static consumers cease dispatching on an imaginary receiver.
pub(super) fn augment(
    facts: &mut FactSnapshot,
    registry: &Registry,
    inputs: &OwnedBinaryInputs,
) -> Result<usize, Error> {
    let mut candidates = Vec::new();
    for body in &facts.bodies {
        let operations = &facts.operations[body.operations.range()];
        if source_body(facts, body) && operations.iter().any(|op| namespace(facts, body, op)) {
            candidates.extend(operations.iter().filter_map(|op| {
                (matches!(op.opcode, Opcode::Call | Opcode::VirtualCall) && !op.target.is_none())
                    .then_some(op.target)
            }));
        }
    }
    candidates.sort_unstable();
    candidates.dedup();
    if candidates.is_empty() {
        return Ok(0);
    }
    let authority = authorities(facts, registry, inputs, &candidates);
    let mut uses = Vec::new();
    let mut definitions = Vec::new();
    let mut repaired = 0;
    for body_index in 0..facts.bodies.len() {
        let body = facts.bodies[body_index];
        if !source_body(facts, &body)
            || !facts.operations[body.operations.range()]
                .iter()
                .any(|op| namespace(facts, &body, op))
        {
            continue;
        }
        uses.clear();
        definitions.clear();
        for (index, op) in facts.operations[body.operations.range()].iter().enumerate() {
            if !op.dest.is_none() {
                definitions.push((op.dest, index));
            }
            for id in [op.a, op.b]
                .into_iter()
                .chain(facts.operands[op.arguments.range()].iter().copied())
            {
                if !id.is_none() {
                    uses.push((id, index));
                }
            }
        }
        definitions.sort_unstable();
        uses.sort_unstable();
        let mut hash = None;
        for offset in 0..body.operations.len as usize {
            let index = body.operations.start as usize + offset;
            let op = facts.operations[index];
            if !namespace(facts, &body, &op)
                || entries(&definitions, op.dest) != [(op.dest, offset)]
            {
                continue;
            }
            let consumers = entries(&uses, op.dest);
            if consumers.is_empty()
                || !consumers.iter().all(|&(_, at)| {
                    let call = facts.operations[body.operations.start as usize + at];
                    let Some(Some(proof)) = authority.get(&call.target) else {
                        return false;
                    };
                    at > offset
                        && proof.body
                        && proof.owner == op.target
                        && proof.context == facts.files[body.file.index()].context
                        && matches!(call.opcode, Opcode::Call | Opcode::VirtualCall)
                        && call.a == op.dest
                        && call.b != op.dest
                        && call.flags & OP_SYNTHETIC_PARAMETER_APPLY == 0
                        && call.arguments.len == proof.parameters
                        && !facts.operands[call.arguments.range()].contains(&op.dest)
                })
            {
                continue;
            }
            let state = hash.get_or_insert_with(|| {
                let mut hash = Sha256::new();
                hash.update(VERSION);
                hash.update(body.body_hash.0);
                hash
            });
            state.update((offset as u64).to_le_bytes());
            field(state, facts.symbol_name(op.target).as_bytes());
            state.update(op.dest.0.to_le_bytes());
            for &(_, at) in consumers {
                let index = body.operations.start as usize + at;
                let call = facts.operations[index];
                let proof = authority[&call.target].expect("checked static authority");
                state.update((at as u64).to_le_bytes());
                state.update(proof.evidence.0);
                state.update((call.opcode as u32).to_le_bytes());
                state.update(call.flags.to_le_bytes());
                facts.operations[index].opcode = Opcode::Call;
                // Keep the explicit EMPTY receiver. NONE would inherit the
                // enclosing source instance under ordinary call transfer.
            }
            facts.operations[index] = OperationRecord {
                opcode: Opcode::Constant,
                target: SymbolId::NONE,
                a: ValueId::NONE,
                b: ValueId::NONE,
                arguments: IdRange::default(),
                ..op
            };
            repaired += 1;
        }
        if let Some(hash) = hash {
            facts.bodies[body_index].body_hash = ContentHash(hash.finalize().into());
        }
    }
    Ok(repaired)
}

#[cfg(test)]
#[path = "binary_static_namespace_tests.rs"]
mod tests;
