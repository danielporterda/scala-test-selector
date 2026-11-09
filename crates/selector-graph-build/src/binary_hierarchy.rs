//! Seal unordered direct JVM inventories after context-qualified provider
//! admission. This does not alter compiler parent order or prove a closed
//! transitive hierarchy; the bounds consumer checks that closure separately.
use super::*;

/// An exact child header can require the platform Object type even when its
/// historical method bytes are unavailable. This identity has no header/effect
/// authority and receives no executable body.
pub(super) fn object_endpoint(
    facts: &mut FactSnapshot,
    registry: &mut Registry,
    context: usize,
    context_id: StrId,
) -> Result<SymbolId, Error> {
    let symbol = declare(
        facts,
        context_id,
        SymbolId::NONE,
        &native_name("java/lang/Object", "<type>", ""),
        13,
        FileId::NONE,
        0,
    )?;
    registry
        .types
        .insert((context, "java/lang/Object".into()), symbol);
    Ok(symbol)
}

fn object_name(facts: &FactSnapshot, symbol: SymbolId) -> bool {
    matches!(
        facts.symbol_name(symbol),
        "java/lang/Object#" | "@jvm/16:java/lang/Object6:<type>0:"
    )
}

// JVMS 4.1 fixes Object's empty ancestry, independent of JDK method bodies:
// https://docs.oracle.com/javase/specs/jvms/se21/html/jvms-4.html#jvms-4.1
// Assumption: captured compiler/JVM inputs describe a valid JVM program. Apply
// the law only to the same-context canonical Object endpoint required by an
// exact admitted child header; contradictory metadata/relations fail closed.
fn object_axiom(
    facts: &FactSnapshot,
    context: &AdmittedContext,
    symbol: SymbolId,
    degree: u32,
    conflicted: &HashSet<SymbolId>,
) -> bool {
    let declaration = facts.symbols[symbol.index()];
    if !object_name(facts, symbol)
        || declaration.context != context.id
        || !matches!(declaration.kind, 0 | 13)
        || degree != 0
        || conflicted.contains(&symbol)
    {
        return false;
    }
    if let Some(CachedClass::Found(class)) = context.classes.get("java/lang/Object") {
        if class.metadata.name() != "java/lang/Object"
            || class.metadata.hash() != class.hash
            || class.metadata.flags() & 0x0200 != 0
            || class.metadata.parent().is_some()
            || class.metadata.interfaces().next().is_some()
        {
            return false;
        }
    } else if matches!(context.classes.get("java/lang/Object"), Some(CachedClass::Unknown(kind))
        if *kind != binary::ErrorKind::ClassNotFound)
    {
        return false;
    }
    context.classes.iter().any(|(owner, class)| match class {
        CachedClass::Found(class) => {
            class.metadata.name() == owner
                && class.hash != ContentHash::default()
                && class.metadata.hash() == class.hash
                && class.metadata.parent() == Some("java/lang/Object")
        }
        _ => false,
    })
}

fn nominal_kind(flags: u16) -> u32 {
    if flags & 0x0200 != 0 { 14 } else { 13 }
}

fn endpoint(
    facts: &FactSnapshot,
    context: &AdmittedContext,
    owner: &str,
    symbol: SymbolId,
) -> bool {
    let Some(CachedClass::Found(class)) = context.classes.get(owner) else {
        return false;
    };
    let declaration = facts.symbols[symbol.index()];
    if owner != "java/lang/Object" && class.metadata.parent().is_none() {
        return false;
    }
    if owner == "java/lang/Object"
        && (class.metadata.parent().is_some()
            || class.metadata.interfaces().next().is_some()
            || class.metadata.flags() & 0x0200 != 0)
    {
        return false;
    }
    declaration.context == context.id
        && declaration.kind == nominal_kind(class.metadata.flags())
        && declaration.flags
            & (SYMBOL_DEFINED | SYMBOL_NATIVE_BINARY | SYMBOL_JVM_CLASS_HEADER_VERIFIED)
            != 0
        && class.metadata.name() == owner
        && class.metadata.hash() == class.hash
        && class.hash != ContentHash::default()
}

pub(super) fn seal(
    facts: &mut FactSnapshot,
    inputs: &OwnedBinaryInputs,
    registry: &Registry,
    parents: &HashSet<(SymbolId, SymbolId)>,
) {
    // A fresh admission must not inherit a previous producer's local proof.
    for symbol in &mut facts.symbols {
        symbol.flags &= !SYMBOL_JVM_PARENTS_COMPLETE;
    }
    let mut conflicted = HashSet::new();
    let mut contexts = HashSet::new();
    let mut global_conflict = false;
    for issue in &facts.issues {
        if issue.kind != IssueKind::ContextConflict {
            continue;
        }
        if !issue.symbol.is_none() {
            conflicted.insert(issue.symbol);
        } else if !issue.file.is_none() {
            contexts.insert(facts.files[issue.file.index()].context);
        } else {
            global_conflict = true;
        }
    }
    if global_conflict {
        return;
    }
    // Compare sets without sorting/replacing the actual Scala parent list.
    // Duplicate publication of the same edge does not change the inventory.
    let mut degrees = vec![0u32; facts.symbols.len()];
    for &(source, _) in parents {
        degrees[source.index()] += 1;
    }
    let mut expected = Vec::new();
    let mut bindings: Vec<_> = registry
        .types
        .iter()
        .map(|((context, owner), &symbol)| (*context, owner.as_str(), symbol))
        .collect();
    bindings.sort_unstable_by_key(|&(context, owner, _)| (context, owner));
    let mut object_roots = HashSet::new();
    for &(context_index, owner, source) in &bindings {
        let context = &inputs.contexts[context_index];
        if owner == "java/lang/Object"
            && !contexts.contains(&context.id)
            && object_axiom(facts, context, source, degrees[source.index()], &conflicted)
        {
            object_roots.insert(source);
            facts.symbols[source.index()].flags |= SYMBOL_JVM_PARENTS_COMPLETE;
        }
    }
    for &(context_index, owner, source) in &bindings {
        let context = &inputs.contexts[context_index];
        if contexts.contains(&context.id)
            || conflicted.contains(&source)
            || !endpoint(facts, context, owner, source)
        {
            continue;
        }
        let declaration = facts.symbols[source.index()];
        if declaration.flags & SYMBOL_DEFINED != 0 {
            // A source mapping may not erase unknown mixins or attach the
            // complete inventory of a similarly named class to another owner.
            // Keep compiler order; require its independently verified inventory
            // to agree exactly with the admitted JVM direct endpoint set.
            if declaration.flags & SYMBOL_SCALA_PARENTS_COMPLETE == 0
                || declaration.file.is_none()
                || facts.files[declaration.file.index()].context != context.id
                || facts.files[declaration.file.index()].flags
                    & (SOURCE_VERIFIED | SYNTAX_VERIFIED | FILE_BINARY_SOURCE)
                    != SOURCE_VERIFIED | SYNTAX_VERIFIED
            {
                continue;
            }
        }
        let Some(CachedClass::Found(class)) = context.classes.get(owner) else {
            continue;
        };
        expected.clear();
        let mut complete = true;
        for parent in class
            .metadata
            .parent()
            .into_iter()
            .chain(class.metadata.interfaces())
        {
            let Ok(index) = bindings
                .binary_search_by_key(&(context_index, parent), |&(context, owner, _)| {
                    (context, owner)
                })
            else {
                complete = false;
                break;
            };
            let target = bindings[index].2;
            // A symbol fallback, deferred lookup or verified negative is not
            // an admitted parent header. Provider failures never prove absence.
            if conflicted.contains(&target)
                || (!object_roots.contains(&target) && !endpoint(facts, context, parent, target))
            {
                complete = false;
                break;
            }
            expected.push(target);
        }
        expected.sort_unstable();
        expected.dedup();
        if complete
            && degrees[source.index()] as usize == expected.len()
            && expected
                .iter()
                .all(|target| parents.contains(&(source, *target)))
        {
            facts.symbols[source.index()].flags |= SYMBOL_JVM_PARENTS_COMPLETE;
        }
    }
}

#[cfg(test)]
#[path = "binary_hierarchy_tests.rs"]
mod tests;
