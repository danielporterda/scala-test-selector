//! Source reads of compiler-owned nested modules are JVM accessor calls.
//! A declared compiler method owned by the exact term witnesses its module
//! namespace. A separately admitted compiler OBJECT header can also prove a
//! global module namespace. Native headers then prove the accessor or MODULE$
//! ABI; neither source spelling nor a kind-0 term alone supplies that proof.
use super::*;

const VERSION: &[u8] = b"binary-source-module-accessor/1";

pub(crate) struct Candidate {
    pub symbol: SymbolId,
    pub owner: SymbolId,
    pub jvm_owner: String,
    pub name: String,
    pub module_owner: String,
    pub descriptor: String,
    pub global: bool,
    /// Captured before native class-facet projection. Only a compiler OBJECT
    /// header can authorize the source module-reference Allocate encoding.
    allocation_reference: bool,
    evidence: ContentHash,
}

fn source_body(facts: &FactSnapshot, body: &BodyRecord) -> bool {
    body.flags & BODY_BINARY_RECIPE == 0
        && facts.files[body.file.index()].flags
            & (SOURCE_VERIFIED | SYNTAX_VERIFIED | FILE_BINARY_SOURCE)
            == SOURCE_VERIFIED | SYNTAX_VERIFIED
}

fn read(op: &OperationRecord) -> bool {
    op.opcode == Opcode::LoadField && reference_operands(op)
}

fn reference_operands(op: &OperationRecord) -> bool {
    !op.target.is_none()
        && !op.dest.is_none()
        && !op.a.is_none()
        && op.b.is_none()
        && op.arguments.len == 0
        && op.flags == 0
}

fn global_object_header(facts: &FactSnapshot, term: SymbolId) -> bool {
    let record = facts.symbols[term.index()];
    record.kind == 10
        && record.flags == 0
        && record.properties == 0
        && record.file.is_none()
        && record.signature.is_none()
        && !record.owner.is_none()
        && facts.symbol_name(record.owner).ends_with('/')
}

fn complete_method(
    facts: &FactSnapshot,
    method: SymbolId,
    children: &[SymbolId],
    conflicts: &[SymbolId],
) -> bool {
    let record = facts.symbols[method.index()];
    let Ok(value) = serde_json::from_str::<serde_json::Value>(facts.text(record.signature)) else {
        return false;
    };
    let Some(signature) = value.get("method_signature").and_then(|v| v.as_object()) else {
        return false;
    };
    if value.as_object().is_none_or(|v| v.len() != 1)
        || signature
            .get("return_type")
            .is_none_or(|v| v.as_object().is_none_or(|v| v.is_empty()))
    {
        return false;
    }
    let mut slots = Vec::new();
    let mut scope = |value: &serde_json::Value, kind: u32| -> Option<()> {
        let scope = value.as_object()?;
        if scope
            .get("hardlinks")
            .is_some_and(|v| v.as_array().is_none_or(|v| !v.is_empty()))
        {
            return None;
        }
        for name in scope
            .get("symlinks")
            .map_or(Some(&[][..]), |v| v.as_array().map(Vec::as_slice))?
        {
            let name = name.as_str()?;
            let mut matches = children
                .iter()
                .copied()
                .filter(|&id| facts.symbol_name(id) == name);
            let id = matches.next()?;
            let child = facts.symbols[id.index()];
            if matches.next().is_some()
                || child.owner != method
                || child.context != record.context
                || child.kind != kind
                || child.signature.is_none()
                || conflicts.binary_search(&id).is_ok()
                || slots.contains(&id)
            {
                return None;
            }
            let signature =
                serde_json::from_str::<serde_json::Value>(facts.text(child.signature)).ok()?;
            if kind == 8 {
                if signature
                    .pointer("/value_signature/tpe")
                    .is_none_or(|v| v.as_object().is_none_or(|v| v.is_empty()))
                {
                    return None;
                }
            } else if signature.get("type_signature").is_none() {
                return None;
            }
            slots.push(id);
        }
        Some(())
    };
    if signature
        .get("type_parameters")
        .is_some_and(|v| scope(v, 9).is_none())
    {
        return false;
    }
    if let Some(clauses) = signature.get("parameter_lists") {
        let Some(clauses) = clauses.as_array() else {
            return false;
        };
        for clause in clauses {
            if scope(clause, 8).is_none() {
                return false;
            }
        }
    }
    children.iter().all(|id| slots.contains(id))
}

pub(crate) fn candidates(facts: &FactSnapshot) -> Vec<Candidate> {
    let mut conflicts: Vec<_> = facts
        .issues
        .iter()
        .filter(|issue| issue.kind == IssueKind::ContextConflict && !issue.symbol.is_none())
        .map(|issue| issue.symbol)
        .collect();
    conflicts.sort_unstable();
    conflicts.dedup();
    let mut terms = Vec::new();
    for body in &facts.bodies {
        if !source_body(facts, body) {
            continue;
        }
        let context = facts.files[body.file.index()].context;
        for op in &facts.operations[body.operations.range()] {
            if !read(op)
                && !(op.opcode == Opcode::Allocate
                    && reference_operands(op)
                    && global_object_header(facts, op.target))
            {
                continue;
            }
            let term = facts.symbols[op.target.index()];
            if term.context == context
                && term.flags & SYMBOL_DEFINED == 0
                && conflicts.binary_search(&op.target).is_err()
                && conflicts.binary_search(&term.owner).is_err()
                && matches!(term.kind, 0 | 10)
                && !term.owner.is_none()
                && (facts.symbol_name(term.owner).ends_with('#')
                    || facts.symbol_name(term.owner).ends_with('/'))
                && facts.symbols[term.owner.index()].context == context
                && facts.symbol_name(op.target).ends_with('.')
                && !facts.symbol_name(op.target).ends_with(").")
            {
                terms.push(op.target);
            }
        }
    }
    terms.sort_unstable();
    terms.dedup();
    let mut witnesses = Vec::new();
    for (index, method) in facts.symbols.iter().enumerate() {
        if terms.binary_search(&method.owner).is_ok()
            && method.kind == 3
            && method.flags & SYMBOL_DEFINED == 0
            && !method.signature.is_none()
            && conflicts.binary_search(&SymbolId(index as u32)).is_err()
            && method.file.is_none()
            && method.context == facts.symbols[method.owner.index()].context
            && selector_types::symbol::global_owner(facts.text(method.name))
                == Some(facts.symbol_name(method.owner))
        {
            witnesses.push((method.owner, SymbolId(index as u32)));
        }
    }
    let mut children = Vec::new();
    let mut methods: Vec<_> = witnesses.iter().map(|v| v.1).collect();
    methods.sort_unstable();
    for (index, formal) in facts.symbols.iter().enumerate() {
        if methods.binary_search(&formal.owner).is_ok() && matches!(formal.kind, 8 | 9) {
            children.push((formal.owner, SymbolId(index as u32)));
        }
    }
    children.sort_unstable();
    witnesses.sort_unstable();
    let mut result = Vec::new();
    let mut child_ids = Vec::new();
    for term in terms {
        let record = facts.symbols[term.index()];
        if !record.signature.is_none()
            && serde_json::from_str::<serde_json::Value>(facts.text(record.signature))
                .map_or(true, |value| value.get("method_signature").is_some())
        {
            continue;
        }
        let name = facts.symbol_name(term);
        if selector_types::symbol::global_owner(name) != Some(facts.symbol_name(record.owner)) {
            continue;
        }
        let Some(module_owner) = selector_types::symbol::jvm_owner(name) else {
            continue;
        };
        let global = facts.symbol_name(record.owner).ends_with('/');
        let allocation_reference = global_object_header(facts, term);
        let (jvm_owner, name, descriptor) = if global {
            (
                module_owner.clone(),
                "MODULE$".to_owned(),
                format!("L{module_owner};"),
            )
        } else {
            let (Some(owner), Some(name)) = (
                selector_types::symbol::jvm_owner(facts.symbol_name(record.owner)),
                selector_types::symbol::member_name(name)
                    .and_then(selector_types::symbol::jvm_name),
            ) else {
                continue;
            };
            (owner, name, format!("()L{module_owner};"))
        };
        let mut hash = Sha256::new();
        hash.update(VERSION);
        let mut proven = allocation_reference;
        if allocation_reference {
            // A separately admitted compiler OBJECT header proves the namespace,
            // not native shape, members, finality, parents or execution effects.
            hash.update(b"compiler-global-object-header/1");
            for value in [
                facts.symbol_name(term),
                facts.symbol_name(record.owner),
                facts.text(record.context),
            ] {
                hash.update((value.len() as u64).to_le_bytes());
                hash.update(value.as_bytes());
            }
        }
        let start = witnesses.partition_point(|v| v.0 < term);
        for &(_, method) in witnesses[start..].iter().take_while(|v| v.0 == term) {
            if allocation_reference {
                break;
            }
            child_ids.clear();
            let start = children.partition_point(|v| v.0 < method);
            child_ids.extend(
                children[start..]
                    .iter()
                    .take_while(|v| v.0 == method)
                    .map(|v| v.1),
            );
            if !complete_method(facts, method, &child_ids, &conflicts) {
                continue;
            }
            let method = facts.symbols[method.index()];
            for value in [
                facts.text(method.name),
                facts.text(method.context),
                facts.text(method.signature),
            ] {
                hash.update((value.len() as u64).to_le_bytes());
                hash.update(value.as_bytes());
            }
            proven = true;
        }
        if proven {
            result.push(Candidate {
                symbol: term,
                owner: record.owner,
                jvm_owner,
                name,
                descriptor,
                module_owner,
                global,
                allocation_reference,
                evidence: ContentHash(hash.finalize().into()),
            });
        }
    }
    result
}

/// The nested module's constructor takes its actual enclosing instance. A
/// global MODULE$ or another returned class cannot substitute for this ABI.
pub(crate) fn module_header(class: &binary::ClassMetadata, candidate: &Candidate) -> bool {
    module_rows(
        class.name(),
        class.flags(),
        class.fields().map(|f| f.name),
        class.methods().map(|m| (m.name, m.descriptor, m.flags)),
        candidate,
    )
}

pub(crate) fn getter(class: &binary::ClassMetadata, candidate: &Candidate) -> bool {
    getter_rows(
        class.name(),
        class.fields().map(|f| f.name),
        class.methods().map(|m| (m.name, m.descriptor, m.flags)),
        candidate,
    )
}

pub(crate) fn module_rows<'a>(
    name: &str,
    flags: u16,
    mut fields: impl Iterator<Item = &'a str>,
    methods: impl Iterator<Item = (&'a str, &'a str, u16)>,
    candidate: &Candidate,
) -> bool {
    let constructor = format!("(L{};)V", candidate.jvm_owner);
    let mut matching = methods.filter(|m| m.0 == "<init>" && m.1 == constructor);
    name == candidate.module_owner
        && flags & (0x0200 | 0x0400) == 0
        && !fields.any(|f| f == "MODULE$")
        && matching
            .next()
            .is_some_and(|m| m.2 & 0x0001 != 0 && m.2 & (0x0002 | 0x0008) == 0)
        && matching.next().is_none()
}

pub(crate) fn getter_rows<'a>(
    name: &str,
    mut fields: impl Iterator<Item = &'a str>,
    methods: impl Iterator<Item = (&'a str, &'a str, u16)>,
    candidate: &Candidate,
) -> bool {
    if name != candidate.jvm_owner || fields.any(|f| f == candidate.name) {
        return false;
    }
    let mut matching = methods.filter(|m| m.0 == candidate.name);
    matching.next().is_some_and(|m| {
        m.1 == candidate.descriptor && m.2 & 0x0001 != 0 && m.2 & (0x0002 | 0x0008 | 0x0040) == 0
    }) && matching.next().is_none()
}

pub(super) fn augment(
    facts: &mut FactSnapshot,
    registry: &Registry,
    inputs: &OwnedBinaryInputs,
    candidates: &[Candidate],
    globals: &HashMap<SymbolId, (SymbolId, ContentHash)>,
) -> Result<usize, Error> {
    let candidate_key = |id: usize| {
        let candidate = &candidates[id];
        (
            facts.symbols[candidate.symbol.index()].context,
            candidate.jvm_owner.as_str(),
            candidate.name.as_str(),
            candidate.descriptor.as_str(),
        )
    };
    let mut by_key: Vec<_> = (0..candidates.len())
        .filter(|&id| !candidates[id].global)
        .collect();
    by_key.sort_unstable_by_key(|&id| candidate_key(id));
    let mut authorities = HashMap::new();
    // Scan native metadata once, looking up only the sparse source candidates.
    // Neither a member String nor a per-owner/member posting list is allocated.
    for (key, data) in &registry.methods {
        let Some(context) = inputs.contexts.get(key.context) else {
            continue;
        };
        let lookup = (
            context.id,
            key.owner.as_str(),
            key.name.as_str(),
            key.descriptor.as_str(),
        );
        let start = by_key.partition_point(|&id| candidate_key(id) < lookup);
        let Some(&id) = by_key.get(start) else {
            continue;
        };
        if candidate_key(id) != lookup
            || by_key
                .get(start + 1)
                .is_some_and(|&id| candidate_key(id) == lookup)
        {
            continue;
        }
        let candidate = &candidates[id];
        if data.owner != candidate.owner
            || data.receiver_parameter.is_some()
            || facts.symbols[data.symbol.index()].flags & SYMBOL_NATIVE_BINARY == 0
            || data.symbol == candidate.symbol
            || facts.symbols[data.symbol.index()].context != context.id
        {
            continue;
        }
        let (Some(CachedClass::Found(owner)), Some(CachedClass::Found(module))) = (
            context.classes.get(&candidate.jvm_owner),
            context.classes.get(&candidate.module_owner),
        ) else {
            continue;
        };
        if owner.hash == ContentHash::default()
            || module.hash == ContentHash::default()
            || owner.metadata.hash() != owner.hash
            || module.metadata.hash() != module.hash
            || !owner
                .metadata
                .method(&key.name, Some(&key.descriptor))
                .is_ok_and(|method| method.flags == data.flags)
            || !getter(&owner.metadata, candidate)
            || !module_header(&module.metadata, candidate)
        {
            continue;
        }
        let mut hash = Sha256::new();
        hash.update(candidate.evidence.0);
        hash.update(owner.hash.0);
        hash.update(module.hash.0);
        authorities.insert(
            candidate.symbol,
            (
                data.symbol,
                ContentHash(hash.finalize().into()),
                Opcode::VirtualCall,
            ),
        );
    }
    authorities.extend(
        globals
            .iter()
            .map(|(&source, &(target, proof))| (source, (target, proof, Opcode::Call))),
    );
    let mut allocation_references: Vec<_> = candidates
        .iter()
        .filter(|candidate| candidate.global && candidate.allocation_reference)
        .map(|candidate| candidate.symbol)
        .collect();
    allocation_references.sort_unstable();
    let mut changed = 0;
    let mut remapped = Vec::new();
    for body in &mut facts.bodies {
        if body.flags & BODY_BINARY_RECIPE != 0
            || facts.files[body.file.index()].flags
                & (SOURCE_VERIFIED | SYNTAX_VERIFIED | FILE_BINARY_SOURCE)
                != SOURCE_VERIFIED | SYNTAX_VERIFIED
        {
            continue;
        }
        let mut hash = None;
        for (offset, op) in facts.operations[body.operations.range()]
            .iter_mut()
            .enumerate()
        {
            if !read(op)
                && !(op.opcode == Opcode::Allocate
                    && reference_operands(op)
                    && allocation_references.binary_search(&op.target).is_ok())
            {
                continue;
            }
            let Some((getter, proof, opcode)) = authorities.get(&op.target) else {
                continue;
            };
            remapped.push((
                OperationId(body.operations.start + offset as u32),
                op.target,
                *getter,
            ));
            op.opcode = *opcode;
            op.target = *getter;
            let hash = hash.get_or_insert_with(|| {
                let mut hash = Sha256::new();
                hash.update(VERSION);
                hash.update(body.body_hash.0);
                hash
            });
            hash.update((offset as u64).to_le_bytes());
            hash.update(proof.0);
            changed += 1;
        }
        if let Some(hash) = hash {
            body.body_hash = ContentHash(hash.finalize().into());
        }
    }
    remapped.sort_unstable();
    for bound in &mut facts.result_bounds {
        if bound.operation.is_none() {
            continue;
        }
        if let Ok(index) = remapped.binary_search_by_key(&bound.operation, |row| row.0) {
            let (_, old, new) = remapped[index];
            if bound.symbol != old {
                return Err(Error::Invalid("module accessor result bound target"));
            }
            bound.symbol = new;
        }
    }
    Ok(changed)
}

#[cfg(test)]
#[path = "binary_source_modules_tests.rs"]
mod tests;

#[path = "binary_top_modules.rs"]
mod top;
pub(super) use top::declare_globals;
