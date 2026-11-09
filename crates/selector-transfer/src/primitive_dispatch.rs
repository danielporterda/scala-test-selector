//! Receiver-only compiler proof for direct primitive Scala `Any.toString`.
//! A primitive operand can only reach the corresponding platform formatter;
//! this neither resolves that formatter nor certifies its remaining effects.
use super::*;

pub(super) const ANY_TO_STRING: &str = "scala/Any#toString().";
const MAX_BODY_OPERATIONS: usize = 4096;
const MAX_CANDIDATE_SITES: usize = 64;

fn is_long_signature(opcode: Opcode, kind: u32, signature: &str) -> bool {
    // Accept only the canonical bare compiler signatures used by the
    // saved source facts. An alias, wrapper or other serialization simply
    // leaves the existing conservative dispatch behavior in place.
    matches!(
        (opcode, kind, signature),
        (
            Opcode::Call | Opcode::VirtualCall,
            3,
            r#"{"method_signature":{"type_parameters":{},"return_type":{"type_ref":{"symbol":"scala/Long#"}}}}"#,
        ) | (
            Opcode::Parameter,
            8,
            r#"{"value_signature":{"tpe":{"type_ref":{"symbol":"scala/Long#"}}}}"#,
        )
    )
}

pub(super) fn possible_virtual_target(name: &str) -> bool {
    matches!(
        name,
        ANY_TO_STRING
            | "scala/Long#toString()."
            | "java/lang/Object#toString()."
            | "java/lang/Long#toString()."
            | "@jvm/14:java/lang/Long8:toString20:()Ljava/lang/String;"
            | "@jvm/14:java/lang/Long8:toString21:(J)Ljava/lang/String;"
            | "@jvm/16:java/lang/Object8:toString20:()Ljava/lang/String;"
    )
}

fn source_file(facts: &FactSnapshot, id: FileId) -> Option<&FileRecord> {
    let file = facts.files.get(id.index())?;
    (file.flags & (SOURCE_VERIFIED | SYNTAX_VERIFIED | FILE_BINARY_SOURCE)
        == SOURCE_VERIFIED | SYNTAX_VERIFIED
        && file.source_hash != ContentHash::default())
    .then_some(file)
}

/// Sorted operation and exact compiler producer pairs. Used by compact replay
/// to retain only the source evidence that transfer actually consumes.
pub fn sites(facts: &FactSnapshot) -> Vec<(OperationId, SymbolId)> {
    let mut conflicted_symbols = Vec::new();
    let mut conflicted_contexts = Vec::new();
    for issue in &facts.issues {
        if issue.kind != IssueKind::ContextConflict {
            continue;
        }
        if !issue.symbol.is_none() {
            conflicted_symbols.push(issue.symbol);
        } else if !issue.file.is_none() {
            conflicted_contexts.push(facts.files[issue.file.index()].context);
        } else {
            return Vec::new();
        }
    }
    conflicted_symbols.sort_unstable();
    conflicted_contexts.sort_unstable();
    let unconflicted = |id: SymbolId, symbol: &SymbolRecord| {
        conflicted_symbols.binary_search(&id).is_err()
            && conflicted_contexts.binary_search(&symbol.context).is_err()
    };
    let mut sites = Vec::new();
    for body in &facts.bodies {
        if body.flags & BODY_BINARY_RECIPE != 0 {
            continue;
        }
        let Some(file) = source_file(facts, body.file) else {
            continue;
        };
        let Some(symbol) = facts.symbols.get(body.symbol.index()) else {
            continue;
        };
        if symbol.flags & (SYMBOL_DEFINED | SYMBOL_NATIVE_BINARY) != SYMBOL_DEFINED
            || symbol.file != body.file
            || symbol.context != file.context
            || !unconflicted(body.symbol, symbol)
        {
            continue;
        }
        let ops = &facts.operations[body.operations.range()];
        if ops.len() > MAX_BODY_OPERATIONS {
            continue;
        }
        for (index, call) in ops
            .iter()
            .enumerate()
            .filter(|(_, call)| {
                call.opcode == Opcode::VirtualCall
                    && call.flags == 0
                    && !call.a.is_none()
                    && call.a != ValueId(0)
                    && call.b.is_none()
                    && call.arguments.len == 0
                    && facts.symbol_name(call.target) == ANY_TO_STRING
            })
            .take(MAX_CANDIDATE_SITES)
        {
            let target = &facts.symbols[call.target.index()];
            if target.context != file.context || !unconflicted(call.target, target) {
                continue;
            }
            // Require a single writer in the whole source recipe. Never infer
            // the type from a coincidentally nearby expression or a merged
            // local slot, and never look through a cast, join or synthetic.
            let mut definitions = ops.iter().enumerate().filter(|(_, op)| op.dest == call.a);
            let Some((at, producer)) = definitions.next() else {
                continue;
            };
            if at >= index || definitions.next().is_some() || producer.flags != 0 {
                continue;
            }
            let Some(declared) = facts.symbols.get(producer.target.index()) else {
                continue;
            };
            if declared.flags & (SYMBOL_DEFINED | SYMBOL_NATIVE_BINARY) != SYMBOL_DEFINED
                || !unconflicted(producer.target, declared)
                || !source_file(facts, declared.file)
                    .is_some_and(|file| file.context == declared.context)
                || (producer.opcode == Opcode::Parameter
                    && (declared.owner != body.symbol
                        || !facts.operands[body.parameters.range()].contains(&producer.dest)))
                || (matches!(producer.opcode, Opcode::Call | Opcode::VirtualCall)
                    && producer.arguments.len != 0)
            {
                continue;
            }
            if is_long_signature(
                producer.opcode,
                declared.kind,
                facts.text(declared.signature),
            ) {
                sites.push((
                    OperationId(body.operations.start + index as u32),
                    producer.target,
                ));
            }
        }
    }
    sites.sort_unstable_by_key(|(operation, _)| *operation);
    sites
}

#[cfg(test)]
mod tests;
