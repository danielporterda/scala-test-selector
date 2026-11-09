//! Declared JVM reference-result constraints. No class loading, object creation,
//! dispatch completion or effect authority follows from a result descriptor.
use super::*;

fn reference_owner(descriptor: &str) -> Option<&str> {
    // Arrays need a distinct JVM type model and cannot inherit element bounds.
    descriptor.strip_prefix('L')?.strip_suffix(';')
}

pub(super) fn publish(
    facts: &mut FactSnapshot,
    inputs: &OwnedBinaryInputs,
    registry: &Registry,
) -> Result<(), Error> {
    if registry.methods.len() > MAX_METHODS {
        return Err(Error::Limit("native result bound methods"));
    }
    let mut conflicted = vec![false; facts.symbols.len()];
    let mut contexts = HashSet::new();
    let mut global = false;
    for issue in &facts.issues {
        if issue.kind != IssueKind::ContextConflict {
            continue;
        }
        if !issue.symbol.is_none() {
            conflicted[issue.symbol.index()] = true;
        } else if !issue.file.is_none() {
            contexts.insert(facts.files[issue.file.index()].context);
        } else {
            global = true;
        }
    }
    if global {
        return Ok(());
    }
    // One flat index, not a whole-program body scan for each admitted method.
    let mut bodies: Vec<_> = facts
        .bodies
        .iter()
        .filter(|body| body.flags & BODY_BINARY_RECIPE != 0)
        .filter_map(|body| {
            let file = facts.files.get(body.file.index())?;
            (file.flags & FILE_BINARY_SOURCE != 0 && file.source_hash != ContentHash::default())
                .then_some((body.symbol, file.context, file.source_hash))
        })
        .collect();
    bodies.sort_unstable_by_key(|&(symbol, context, hash)| (symbol, context, hash.0));
    bodies.dedup();
    // Keys borrow the retained registry. Missing result owners are deliberately
    // not admitted here; this pass must never grow the native closure.
    let mut classes: Vec<_> = registry
        .types
        .iter()
        .filter_map(|((index, owner), &symbol)| {
            let context = inputs.contexts.get(*index)?;
            let declaration = facts.symbols.get(symbol.index())?;
            let Some(CachedClass::Found(bytes)) = context.classes.get(owner) else {
                return None;
            };
            let kind = if bytes.metadata.flags() & 0x0200 != 0 {
                14
            } else {
                13
            };
            (declaration.flags & SYMBOL_JVM_CLASS_HEADER_VERIFIED != 0
                && declaration.kind == kind
                && declaration.context == context.id
                && !conflicted[symbol.index()]
                && !contexts.contains(&context.id)
                && bytes.hash != ContentHash::default()
                && bytes.metadata.hash() == bytes.hash
                && bytes.metadata.name() == owner)
                .then_some((*index, owner.as_str(), symbol))
        })
        .collect();
    classes.sort_unstable_by_key(|&(context, owner, _)| (context, owner));
    let class = |context, owner| {
        classes
            .binary_search_by_key(&(context, owner), |&(context, owner, _)| (context, owner))
            .ok()
            .map(|index| classes[index].2)
    };
    let mut candidates = Vec::with_capacity(registry.methods.len());
    for (key, data) in &registry.methods {
        let declaration = &facts.symbols[data.symbol.index()];
        let Some(context) = inputs.contexts.get(key.context) else {
            continue;
        };
        if declaration.flags & SYMBOL_NATIVE_BINARY == 0
            || declaration.kind != 3
            || declaration.context != context.id
            || declaration.owner != data.owner
            || conflicted[data.symbol.index()]
            || contexts.contains(&context.id)
            || class(key.context, key.owner.as_str()) != Some(data.owner)
            || matches!(key.name.as_str(), "<init>" | "<clinit>")
        {
            continue;
        }
        let Some(CachedClass::Found(bytes)) = context.classes.get(&key.owner) else {
            continue;
        };
        let Ok(method) = bytes.metadata.method(&key.name, Some(&key.descriptor)) else {
            continue;
        };
        if method.flags != data.flags
            || bodies
                .binary_search_by_key(
                    &(data.symbol, context.id, bytes.hash.0),
                    |&(symbol, context, hash)| (symbol, context, hash.0),
                )
                .is_err()
        {
            continue;
        }
        let Ok(descriptor) = binary::method_descriptor(method.descriptor) else {
            continue;
        };
        let Some(owner) = reference_owner(descriptor.return_type) else {
            continue;
        };
        let Some(result) = class(key.context, owner) else {
            continue;
        };
        if facts
            .result_bounds
            .binary_search_by_key(&(data.symbol, OperationId::NONE), |row| {
                (row.symbol, row.operation)
            })
            .is_ok()
        {
            // Compiler conjunctions are stronger authority; never overwrite
            // an existing declaration or an operation-specific specialization.
            continue;
        }
        candidates.push((data.symbol, OperationId::NONE, result));
    }
    // Index only exact, provider-bound field declarations. Source aliases can
    // denote accessors rather than native fields and keep their compiler bounds.
    let fields: HashMap<_, _> = registry
        .fields
        .iter()
        .filter_map(|(key, &symbol)| {
            let result = class(key.context, reference_owner(&key.descriptor)?)?;
            let declaration = &facts.symbols[symbol.index()];
            let context = inputs.contexts.get(key.context)?;
            let owner = class(key.context, key.owner.as_str())?;
            if declaration.flags & SYMBOL_NATIVE_BINARY == 0
                || declaration.kind != 20
                || declaration.context != context.id
                || declaration.owner != owner
                || conflicted[symbol.index()]
                || contexts.contains(&context.id)
            {
                return None;
            }
            let Some(CachedClass::Found(bytes)) = context.classes.get(&key.owner) else {
                return None;
            };
            let file = facts.files.get(declaration.file.index())?;
            if file.flags & FILE_BINARY_SOURCE == 0
                || file.context != context.id
                || file.source_hash != bytes.hash
            {
                return None;
            }
            let field = bytes.metadata.field(&key.name, &key.descriptor).ok()??;
            Some((symbol, (context.id, result, field.flags & 0x0008 != 0)))
        })
        .collect();
    if !fields.is_empty() {
        for body in facts
            .bodies
            .iter()
            .filter(|body| body.flags & BODY_BINARY_RECIPE != 0)
        {
            let Some(file) = facts.files.get(body.file.index()) else {
                continue;
            };
            if file.flags & FILE_BINARY_SOURCE == 0
                || file.source_hash == ContentHash::default()
                || conflicted[body.symbol.index()]
            {
                continue;
            }
            for index in body.operations.range() {
                let op = &facts.operations[index];
                if op.opcode != Opcode::LoadField || op.dest.is_none() {
                    continue;
                }
                let Some(&(context, result, is_static)) = fields.get(&op.target) else {
                    continue;
                };
                if context != file.context || is_static != (op.flags & OP_STATIC_FIELD != 0) {
                    continue;
                }
                let operation = OperationId::checked(index)?;
                if facts.result_bound(op.target, operation).is_none()
                    && facts.result_bound(op.target, OperationId::NONE).is_none()
                {
                    candidates.push((op.target, operation, result));
                }
            }
        }
    }
    candidates.sort_unstable();
    candidates.dedup();
    let mut at = 0;
    while at < candidates.len() {
        let start = at;
        at += 1;
        let (symbol, operation, result) = candidates[start];
        while at < candidates.len() && (candidates[at].0, candidates[at].1) == (symbol, operation) {
            at += 1;
        }
        if at != start + 1 {
            // Contradictory bindings cannot select an arbitrary first type.
            continue;
        }
        let start = u32::try_from(facts.bound_classes.len())
            .map_err(|_| Error::Limit("native result bound classes"))?;
        facts.bound_classes.push(result);
        facts.result_bounds.push(ResultBoundRecord {
            symbol,
            operation,
            classes: IdRange { start, len: 1 },
        });
    }
    facts
        .result_bounds
        .sort_unstable_by_key(|row| (row.symbol, row.operation));
    Ok(())
}

#[cfg(test)]
#[path = "binary_native_result_bounds_tests.rs"]
mod tests;
