//! Receiver-only native discovery frontiers. These are consulted at invocation,
//! never projected into a cross product of graph operations and class markers.
use super::*;

pub fn eligible(facts: &FactSnapshot, operation: OperationId) -> bool {
    let Some(op) = facts.operations.get(operation.index()) else {
        return false;
    };
    if !matches!(
        op.opcode,
        Opcode::Call
            | Opcode::VirtualCall
            | Opcode::DefaultArgument
            | Opcode::RegisterTest
            | Opcode::InvokeCallback
    ) || op.flags & (OP_SUPER | OP_QUALIFIED_SUPER) != 0
    {
        return false;
    }
    if facts.compiler_private_dispatch(op) {
        return false;
    }
    if op.opcode == Opcode::Call
        && op.flags & OP_JVM_NONVIRTUAL != 0
        && facts.bodies.get(op.body.index()).is_some_and(|body| {
            body.flags & BODY_BINARY_RECIPE != 0
                && facts
                    .files
                    .get(body.file.index())
                    .is_some_and(|file| file.flags & FILE_BINARY_SOURCE != 0)
        })
    {
        // Exact native invokestatic/invokespecial selection is independent of
        // runtime receiver methods. A copied source flag has no such authority.
        return false;
    }
    // A constructor is statically selected. Opcode::Call alone does not prove
    // nonvirtual dispatch: incomplete metadata can leave instance calls there.
    !facts
        .symbols
        .get(op.target.index())
        .is_some_and(|target| target.kind == 21)
}

pub(super) fn possible(
    facts: &FactSnapshot,
    types: &TypeIndex,
    pool: &ValuePool,
    receiver: Value,
    operation: OperationId,
    work: &mut Vec<SymbolId>,
    linearization: &mut LinearizationScratch,
) -> bool {
    if types.deferred_receivers.is_empty() || !eligible(facts, operation) {
        return false;
    }
    let contract = facts.operations[operation.index()].target;
    if receiver.is_unknown()
        && types
            .deferred_receivers
            .iter()
            .any(|owner| types.unknown_possible(facts, pool, receiver, *owner, work))
    {
        return true;
    }
    for atom in pool.members(receiver) {
        // A literal lexical callback has exact code identity, independent of
        // missing methods on native Function objects or its enclosing suite.
        if atom.kind != AtomKind::Object {
            continue;
        }
        if !types.exact_ancestry_complete(atom.symbol, linearization) {
            return true;
        }
        if types
            .known_receiver_dispatch
            .binary_search(&(atom.symbol, contract))
            .is_ok()
        {
            // The producer proved the entire lookup for this exact runtime
            // class and contract, including inherited selection and absence of
            // a child override. This says nothing about body effects or data.
            continue;
        }
        work.clear();
        work.push(atom.symbol);
        let mut at = 0;
        while at < work.len() {
            let symbol = work[at];
            at += 1;
            if types.deferred_receivers.binary_search(&symbol).is_ok() {
                return true;
            }
            let Some(parents) = types.direct_parents(symbol) else {
                return true;
            };
            for parent in parents {
                if !work.contains(parent) {
                    work.push(*parent);
                }
            }
        }
    }
    false
}

#[cfg(test)]
mod tests;
