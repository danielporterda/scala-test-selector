//! Eager compiler VAL storage. RHS execution belongs to initialization, whereas
//! a later method call reads the stored value using the original compiler ID.
use super::hash_text;
use selector_facts::{BodyRecord, FactSnapshot, OperationRecord, SymbolRecord, TextRange};
use selector_types::*;
use sha2::{Digest, Sha256};
use std::collections::HashSet;

const PREFIX: &str = "@selector:source-val-initializer/1:";
const VERSION: &[u8] = b"source-eager-val-storage/1";

struct Split {
    symbol: SymbolId,
    body: BodyId,
    initializer: SymbolId,
    value: ValueId,
    initializer_hash: ContentHash,
    getter_hash: ContentHash,
}

/// Derive storage only from a unique verified compiler VAL definition and its
/// single eager expression recipe. Unsupported shapes retain their old facts.
/// This is also called by enrichment of previously sealed raw source inputs.
pub fn augment_eager_val_accessors(facts: &mut FactSnapshot) -> Result<usize, Error> {
    facts.validate()?;
    let mut body_counts = vec![0u8; facts.symbols.len()];
    let mut constructor_claims = vec![false; facts.symbols.len()];
    for body in &facts.bodies {
        body_counts[body.symbol.index()] =
            body_counts[body.symbol.index()].saturating_add(1).min(2);
        let owner = facts.symbols[body.symbol.index()];
        if !matches!(owner.kind, 10 | 13 | 14)
            || owner.flags & (SYMBOL_DEFINED | SYMBOL_NATIVE_BINARY) != SYMBOL_DEFINED
            || owner.file.is_none()
            || owner.file != body.file
            || body.flags & !BODY_SOURCE_RECIPE != BODY_INITIALIZER
        {
            continue;
        }
        let file = facts.files[body.file.index()];
        if file.context != owner.context
            || file.flags & (SOURCE_VERIFIED | SYNTAX_VERIFIED | FILE_BINARY_SOURCE)
                != SOURCE_VERIFIED | SYNTAX_VERIFIED
            || file.source_hash == ContentHash::default()
        {
            continue;
        }
        // A compiler constructor-parameter claim is a different storage lane.
        // Index those claims once rather than rescan owner bodies for each VAL.
        for operation in &facts.operations[body.operations.range()] {
            if operation.opcode != Opcode::Parameter
                || operation.target.is_none()
                || operation.dest.is_none()
                || operation.dest == ValueId(0)
            {
                continue;
            }
            let property = facts.symbols[operation.target.index()];
            if property.kind == 3
                && property.properties & 1024 != 0
                && property.flags & (SYMBOL_DEFINED | SYMBOL_NATIVE_BINARY) == SYMBOL_DEFINED
                && property.owner == body.symbol
                && property.file == body.file
                && property.context == owner.context
                && operation.span == property.span
            {
                constructor_claims[operation.target.index()] = true;
            }
        }
    }
    let mut definitions = vec![0u8; facts.symbols.len()];
    let mut exact_definition = vec![false; facts.symbols.len()];
    for occurrence in &facts.occurrences {
        if occurrence.role != 2 {
            continue;
        }
        let symbol = facts.symbols[occurrence.symbol.index()];
        definitions[occurrence.symbol.index()] = definitions[occurrence.symbol.index()]
            .saturating_add(1)
            .min(2);
        exact_definition[occurrence.symbol.index()] |= occurrence.file == symbol.file
            && occurrence.span == symbol.span
            && occurrence.span.start != occurrence.span.end;
    }
    let mut conflicts = HashSet::new();
    let mut conflicted_contexts = HashSet::new();
    for issue in &facts.issues {
        if issue.kind != IssueKind::ContextConflict {
            continue;
        }
        if !issue.symbol.is_none() {
            conflicts.insert(issue.symbol);
        } else if !issue.file.is_none() {
            conflicted_contexts.insert(facts.files[issue.file.index()].context);
        } else {
            return Ok(0);
        }
    }
    // Only reserved derived identities are indexed. Do not copy the enormous
    // source string pool, or linearly search it for every newly derived name.
    let mut reserved: Vec<_> = facts
        .symbols
        .iter()
        .enumerate()
        .filter_map(|(index, symbol)| {
            let name = facts.strings.get(symbol.name);
            name.starts_with(PREFIX).then(|| {
                (
                    symbol.context,
                    ContentHash(Sha256::digest(name.as_bytes()).into()),
                    SymbolId(index as u32),
                )
            })
        })
        .collect();
    reserved.sort_unstable_by_key(|&(context, hash, id)| (context, hash.0, id));
    let mut splits = Vec::new();
    for (index, body) in facts.bodies.iter().enumerate() {
        let symbol = facts.symbols[body.symbol.index()];
        if symbol.kind != 3
            || symbol.properties & 1024 == 0
            || symbol.properties & (4 | 64 | 2048) != 0
            || symbol.flags & (SYMBOL_DEFINED | SYMBOL_NATIVE_BINARY) != SYMBOL_DEFINED
            || symbol.owner.is_none()
            || symbol.file.is_none()
            || symbol.context.is_none()
            || symbol.file != body.file
            || body.name_span != symbol.span
            || body.flags & !BODY_SOURCE_RECIPE != BODY_INITIALIZER
            || body_counts[body.symbol.index()] != 1
            || constructor_claims[body.symbol.index()]
            || definitions[body.symbol.index()] != 1
            || !exact_definition[body.symbol.index()]
            || conflicts.contains(&body.symbol)
            || conflicts.contains(&symbol.owner)
            || conflicted_contexts.contains(&symbol.context)
        {
            continue;
        }
        let owner = facts.symbols[symbol.owner.index()];
        let file = facts.files[body.file.index()];
        if !matches!(owner.kind, 10 | 13 | 14)
            || owner.flags & SYMBOL_DEFINED == 0
            || owner.file != symbol.file
            || owner.context != symbol.context
            || file.context != symbol.context
            || file.flags & (SOURCE_VERIFIED | SYNTAX_VERIFIED | FILE_BINARY_SOURCE)
                != SOURCE_VERIFIED | SYNTAX_VERIFIED
            || file.source_hash == ContentHash::default()
            || selector_types::symbol::global_owner(facts.strings.get(symbol.name))
                != Some(facts.strings.get(owner.name))
        {
            continue;
        }
        let operations = &facts.operations[body.operations.range()];
        let Some(terminal) = operations.last() else {
            continue;
        };
        if terminal.opcode != Opcode::Return
            || terminal.a.is_none()
            || !terminal.target.is_none()
            || terminal.arguments.len != 0
            || operations[..operations.len() - 1]
                .iter()
                .any(|op| op.opcode == Opcode::Return)
            || operations.iter().any(|op| {
                op.dest == ValueId(0)
                    || (op.opcode == Opcode::Parameter && op.target == body.symbol)
            })
        {
            continue;
        }
        let original_name = facts.strings.get(symbol.name);
        let path = facts.strings.get(file.path);
        let name = format!(
            "{PREFIX}{}:{original_name}{}:{path}",
            original_name.len(),
            path.len()
        );
        let name_hash = ContentHash(Sha256::digest(name.as_bytes()).into());
        let begin = reserved.partition_point(|&(context, hash, _)| {
            (context, hash.0) < (symbol.context, name_hash.0)
        });
        let end = reserved.partition_point(|&(context, hash, _)| {
            (context, hash.0) <= (symbol.context, name_hash.0)
        });
        if reserved[begin..end]
            .iter()
            .any(|&(_, _, id)| facts.symbol_name(id) == name)
        {
            // A pre-existing incompatible facet is never repurposed. A second
            // invocation normally finds a getter, not another eligible RHS.
            continue;
        }
        let mut getter_hash = Sha256::new();
        getter_hash.update(VERSION);
        getter_hash.update(b"getter");
        hash_text(&mut getter_hash, original_name);
        hash_text(&mut getter_hash, facts.strings.get(symbol.context));
        hash_text(&mut getter_hash, facts.strings.get(symbol.signature));
        let mut initializer_hash = Sha256::new();
        initializer_hash.update(VERSION);
        initializer_hash.update(b"initializer");
        initializer_hash.update(body.body_hash.0);
        hash_text(&mut initializer_hash, &name);
        hash_text(&mut initializer_hash, facts.strings.get(symbol.context));
        splits.push(Split {
            symbol: body.symbol,
            body: BodyId(index as u32),
            initializer: SymbolId::NONE,
            value: terminal.a,
            initializer_hash: ContentHash(initializer_hash.finalize().into()),
            getter_hash: ContentHash(getter_hash.finalize().into()),
        });
    }
    if splits.is_empty() {
        return Ok(0);
    }
    let count = facts
        .operations
        .len()
        .checked_add(
            splits
                .len()
                .checked_mul(3)
                .ok_or(Error::Limit("VAL storage operations"))?,
        )
        .ok_or(Error::Limit("VAL storage operations"))?;
    if count > u32::MAX as usize
        || facts.bodies.len().saturating_add(splits.len()) > u32::MAX as usize
        || facts.symbols.len().saturating_add(splits.len()) > u32::MAX as usize
    {
        return Err(Error::Limit("VAL storage identifiers"));
    }
    let mut operations = Vec::new();
    operations
        .try_reserve_exact(count)
        .map_err(|_| Error::Limit("VAL storage operations"))?;
    let mut operation_map = if facts.result_bounds.iter().any(|b| !b.operation.is_none()) {
        vec![OperationId::NONE; facts.operations.len()]
    } else {
        Vec::new()
    };
    let mut initializers = vec![SymbolId::NONE; facts.symbols.len()];
    for split in &mut splits {
        let symbol = facts.symbols[split.symbol.index()];
        let property = facts.strings.get(symbol.name);
        let path = facts.strings.get(facts.files[symbol.file.index()].path);
        let name = format!("{PREFIX}{}:{property}{}:{path}", property.len(), path.len());
        let name_id = StrId::checked(facts.strings.entries.len())?;
        facts.strings.entries.push(TextRange {
            start: facts.strings.bytes.len() as u64,
            len: u32::try_from(name.len()).map_err(|_| Error::Limit("VAL initializer identity"))?,
        });
        facts.strings.bytes.extend_from_slice(name.as_bytes());
        split.initializer = SymbolId::checked(facts.symbols.len())?;
        facts.symbols.push(SymbolRecord {
            name: name_id,
            display: StrId::NONE,
            owner: symbol.owner,
            file: symbol.file,
            context: symbol.context,
            kind: 3,
            properties: 0,
            signature: StrId::NONE,
            span: symbol.span,
            flags: 0,
        });
        initializers[split.symbol.index()] = split.initializer;
    }
    let mut next = 0;
    for (body_index, body) in facts.bodies.iter_mut().enumerate() {
        let original = body.operations;
        let start = operations.len();
        let split = splits
            .get(next)
            .filter(|split| split.body.index() == body_index);
        for (ordinal, mut operation) in facts.operations[original.range()]
            .iter()
            .copied()
            .enumerate()
        {
            if let Some(split) = split
                && ordinal + 1 == original.len as usize
            {
                operations.push(OperationRecord {
                    body: split.body,
                    opcode: Opcode::StoreField,
                    target: split.symbol,
                    dest: ValueId::NONE,
                    a: ValueId(0),
                    b: split.value,
                    arguments: IdRange::default(),
                    span: operation.span,
                    flags: 0,
                });
            }
            if !operation_map.is_empty() {
                operation_map[original.start as usize + ordinal] =
                    OperationId::checked(operations.len())?;
            }
            if operation.opcode == Opcode::Initialize
                && !operation.target.is_none()
                && let Some(&initializer) = initializers.get(operation.target.index())
                && !initializer.is_none()
            {
                operation.target = initializer;
            }
            operations.push(operation);
        }
        if let Some(split) = split {
            body.symbol = split.initializer;
            body.flags |= BODY_SOURCE_RECIPE;
            body.body_hash = split.initializer_hash;
            next += 1;
        }
        body.operations = IdRange {
            start: start as u32,
            len: (operations.len() - start) as u32,
        };
    }
    for split in &splits {
        let symbol = facts.symbols[split.symbol.index()];
        let body = BodyId::checked(facts.bodies.len())?;
        let start = operations.len() as u32;
        operations.push(OperationRecord {
            body,
            opcode: Opcode::LoadField,
            target: split.symbol,
            dest: ValueId(1),
            a: ValueId(0),
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: symbol.span,
            flags: 0,
        });
        operations.push(OperationRecord {
            body,
            opcode: Opcode::Return,
            target: SymbolId::NONE,
            dest: ValueId::NONE,
            a: ValueId(1),
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: symbol.span,
            flags: 0,
        });
        facts.bodies.push(BodyRecord {
            symbol: split.symbol,
            file: symbol.file,
            span: symbol.span,
            name_span: symbol.span,
            operations: IdRange { start, len: 2 },
            parameters: IdRange::default(),
            body_hash: split.getter_hash,
            flags: BODY_SOURCE_RECIPE,
        });
    }
    for bound in &mut facts.result_bounds {
        if bound.operation.is_none() {
            continue;
        }
        bound.operation = operation_map[bound.operation.index()];
        // Only a changed initialization target changes the ABI key. A getter's
        // declaration or ordinary callsite clause stays on the compiler VAL ID.
        let operation = operations[bound.operation.index()];
        if operation.opcode == Opcode::Initialize {
            bound.symbol = operation.target;
        }
    }
    facts
        .result_bounds
        .sort_unstable_by_key(|bound| (bound.symbol, bound.operation));
    // Declaration/RHS diagnostics remain visible on the original symbol, while
    // its eager execution obligation follows the reowned expression as well.
    let original_issues = facts.issues.len();
    for index in 0..original_issues {
        let issue = facts.issues[index];
        if !issue.symbol.is_none()
            && let Some(&initializer) = initializers.get(issue.symbol.index())
            && !initializer.is_none()
        {
            facts.issues.push(selector_facts::IssueRecord {
                symbol: initializer,
                ..issue
            });
        }
    }
    facts.operations = operations;
    facts.validate()?;
    Ok(splits.len())
}

#[cfg(test)]
#[path = "binary_source_val_accessors_tests.rs"]
mod tests;
