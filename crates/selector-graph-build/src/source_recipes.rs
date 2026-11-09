//! Compiler-backed normalization performed before facts are sealed. This stage
//! changes neither compiler identities nor source ownership. Graph construction
//! and receiver linearization must consume the same normalized parent records.
use selector_facts::{
    BodyRecord, FactSnapshot, IssueRecord, OperationRecord, RelationRecord, TextRange,
};
use selector_types::*;
use serde::Deserialize;
use serde_json::value::RawValue;
use sha2::{Digest, Sha256};
use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
};

#[path = "binary_source_val_accessors.rs"]
mod eager_values;
pub use eager_values::augment_eager_val_accessors;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SourceRecipeStats {
    pub normalized_parents: usize,
    pub normalized_initializers: usize,
    pub unsupported_alias_parents: usize,
    pub parameter_accessors: usize,
}

/// Normalize transparent compiler aliases before serializing the source facts.
/// A graph-only rewrite would disagree with the solver's fact-based type index.
pub fn augment_source_recipes(facts: &mut FactSnapshot) -> Result<SourceRecipeStats, Error> {
    facts.validate()?;
    let mut stats = SourceRecipeStats::default();
    normalize_parent_aliases(facts, &mut stats)?;
    parameter_accessors(facts, &mut stats)?;
    facts.validate()?;
    Ok(stats)
}

#[derive(Clone, Copy)]
struct Accessor {
    symbol: SymbolId,
    parameter: ValueId,
    parameter_ordinal: u32,
    initializer: BodyId,
}

fn parameter_accessors(
    facts: &mut FactSnapshot,
    stats: &mut SourceRecipeStats,
) -> Result<(), Error> {
    let mut bodies = vec![0u32; facts.symbols.len()];
    for body in &facts.bodies {
        bodies[body.symbol.index()] += 1;
    }
    let mut definitions = vec![false; facts.symbols.len()];
    for occurrence in &facts.occurrences {
        let symbol = facts.symbols[occurrence.symbol.index()];
        if occurrence.role == 2 && occurrence.file == symbol.file && occurrence.span == symbol.span
        {
            definitions[occurrence.symbol.index()] = true;
        }
    }
    let mut accessors = Vec::new();
    let mut claims = HashSet::new();
    let mut duplicate_claims = HashSet::new();
    for (body_index, body) in facts.bodies.iter().enumerate() {
        let owner = facts.symbols[body.symbol.index()];
        if owner.kind != 13
            || owner.flags & SYMBOL_DEFINED == 0
            || owner.file != body.file
            || bodies[body.symbol.index()] != 1
            || body.flags != BODY_INITIALIZER
            || facts.files[body.file.index()].flags
                & (SOURCE_VERIFIED | SYNTAX_VERIFIED | FILE_BINARY_SOURCE)
                != SOURCE_VERIFIED | SYNTAX_VERIFIED
        {
            continue;
        }
        let parameters = &facts.operands[body.parameters.range()];
        for op in facts.operations[body.operations.range()]
            .iter()
            .take_while(|op| op.opcode == Opcode::Parameter)
        {
            if op.target.is_none() || op.dest.is_none() || op.dest == ValueId(0) {
                continue;
            }
            let symbol = facts.symbols[op.target.index()];
            // SemanticDB VAL=1024, ABSTRACT=4, LAZY=64. A source constructor
            // parameter is a field accessor only if the compiler itself bound
            // the exact definition token to an owned, non-lazy VAL method.
            if symbol.kind != 3
                || symbol.properties & 1024 == 0
                || symbol.properties & (4 | 64 | 2048) != 0
                || symbol.flags & SYMBOL_DEFINED == 0
                || symbol.owner != body.symbol
                || symbol.file != body.file
                || symbol.context != owner.context
                || symbol.span != op.span
                || symbol.span.start == symbol.span.end
                || !body.span.contains(symbol.span)
                || !definitions[op.target.index()]
                || bodies[op.target.index()] != 0
            {
                continue;
            }
            let Some(ordinal) = parameters.iter().position(|&value| value == op.dest) else {
                continue;
            };
            if parameters.iter().filter(|&&value| value == op.dest).count() != 1 {
                continue;
            }
            if !claims.insert(op.target) {
                duplicate_claims.insert(op.target);
            }
            accessors.push(Accessor {
                symbol: op.target,
                parameter: op.dest,
                parameter_ordinal: ordinal as u32,
                initializer: BodyId(body_index as u32),
            });
        }
    }
    accessors.retain(|a| !duplicate_claims.contains(&a.symbol));
    if accessors.is_empty() {
        return Ok(());
    }
    // One linear rebuild keeps every operation owned by exactly one body. A
    // per-body append-and-abandon strategy would leave invalid orphan records.
    let operation_count = facts
        .operations
        .len()
        .checked_add(
            accessors
                .len()
                .checked_mul(3)
                .ok_or(Error::Limit("source accessor operations"))?,
        )
        .ok_or(Error::Limit("source accessor operations"))?;
    let mut operations = Vec::new();
    operations
        .try_reserve_exact(operation_count)
        .map_err(|_| Error::Limit("source accessor operations"))?;
    // Declared bounds need no operation map. Allocate it only for an admitted
    // exact-callsite clause, then preserve its key across the linear rebuild.
    let mut operation_map = if facts.result_bounds.iter().any(|b| !b.operation.is_none()) {
        vec![OperationId::NONE; facts.operations.len()]
    } else {
        Vec::new()
    };
    let mut next = 0;
    for (body_index, body) in facts.bodies.iter_mut().enumerate() {
        let original_range = body.operations;
        let original = &facts.operations[body.operations.range()];
        let start = operations.len();
        let mut insertion = (usize::MAX, 0);
        if next < accessors.len() && accessors[next].initializer.index() == body_index {
            let begin = next;
            while next < accessors.len() && accessors[next].initializer.index() == body_index {
                next += 1;
            }
            let parameters = original
                .iter()
                .take_while(|op| op.opcode == Opcode::Parameter)
                .count();
            insertion = (parameters, next - begin);
            operations.extend_from_slice(&original[..parameters]);
            let mut hash = Sha256::new();
            hash.update(b"source-constructor-accessor-stores/1");
            hash.update(body.body_hash.0);
            for accessor in &accessors[begin..next] {
                let symbol = facts.symbols[accessor.symbol.index()];
                operations.push(OperationRecord {
                    body: accessor.initializer,
                    opcode: Opcode::StoreField,
                    target: accessor.symbol,
                    dest: ValueId::NONE,
                    a: ValueId(0),
                    b: accessor.parameter,
                    arguments: IdRange::default(),
                    span: symbol.span,
                    flags: 0,
                });
                hash_text(&mut hash, facts.strings.get(symbol.name));
                hash_text(&mut hash, facts.strings.get(symbol.context));
                hash.update(accessor.parameter_ordinal.to_le_bytes());
            }
            operations.extend_from_slice(&original[parameters..]);
            body.body_hash = ContentHash(hash.finalize().into());
        } else {
            operations.extend_from_slice(original);
        }
        body.operations = IdRange {
            start: u32::try_from(start)
                .map_err(|_| Error::Limit("source accessor operation offset"))?,
            len: u32::try_from(operations.len() - start)
                .map_err(|_| Error::Limit("source accessor operation count"))?,
        };
        if !operation_map.is_empty() {
            for ordinal in 0..original.len() {
                let shift = if ordinal >= insertion.0 {
                    insertion.1
                } else {
                    0
                };
                operation_map[original_range.start as usize + ordinal] =
                    OperationId::checked(start + ordinal + shift)?;
            }
        }
    }
    for accessor in &accessors {
        let symbol = facts.symbols[accessor.symbol.index()];
        let body = BodyId::checked(facts.bodies.len())?;
        let start = u32::try_from(operations.len())
            .map_err(|_| Error::Limit("source accessor operation offset"))?;
        operations.push(OperationRecord {
            body,
            opcode: Opcode::LoadField,
            target: accessor.symbol,
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
        let mut hash = Sha256::new();
        hash.update(b"source-constructor-accessor-getter/1");
        hash_text(&mut hash, facts.text(symbol.name));
        hash_text(&mut hash, facts.text(symbol.context));
        hash_text(&mut hash, facts.text(symbol.signature));
        facts.bodies.push(BodyRecord {
            symbol: accessor.symbol,
            file: symbol.file,
            span: symbol.span,
            name_span: symbol.span,
            operations: IdRange { start, len: 2 },
            parameters: IdRange::default(),
            body_hash: ContentHash(hash.finalize().into()),
            flags: BODY_SOURCE_RECIPE,
        });
    }
    for bound in &mut facts.result_bounds {
        if !bound.operation.is_none() {
            bound.operation = operation_map[bound.operation.index()];
        }
    }
    facts
        .result_bounds
        .sort_unstable_by_key(|bound| (bound.symbol, bound.operation));
    facts.operations = operations;
    stats.parameter_accessors = accessors.len();
    Ok(())
}

fn hash_text(hash: &mut Sha256, text: &str) {
    hash.update((text.len() as u64).to_le_bytes());
    hash.update(text.as_bytes());
}

#[derive(Deserialize)]
struct Signature<'a> {
    #[serde(default, borrow)]
    type_signature: Option<TypeSignature<'a>>,
}
#[derive(Deserialize)]
struct TypeSignature<'a> {
    #[serde(default, borrow)]
    lower_bound: Option<&'a RawValue>,
    #[serde(default, borrow)]
    upper_bound: Option<&'a RawValue>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct NominalType<'a> {
    #[serde(borrow)]
    type_ref: NominalReference<'a>,
}
#[derive(Deserialize)]
struct NominalReference<'a> {
    #[serde(borrow)]
    symbol: Cow<'a, str>,
}

fn alias_head(facts: &FactSnapshot, alias: SymbolId) -> Option<Cow<'_, str>> {
    let record = facts.symbols[alias.index()];
    if record.kind != 7 || record.signature.is_none() {
        return None;
    }
    let signature: Signature<'_> = serde_json::from_str(facts.text(record.signature)).ok()?;
    let signature = signature.type_signature?;
    let lower = signature.lower_bound?;
    let upper = signature.upper_bound?;
    // Compiler-produced equal bounds normally share identical JSON. Materialize
    // only an unusually formatted pair, never every signature in the program.
    if lower.get() != upper.get() {
        let a: serde_json::Value = serde_json::from_str(lower.get()).ok()?;
        let b: serde_json::Value = serde_json::from_str(upper.get()).ok()?;
        if a != b {
            return None;
        }
    }
    let nominal: NominalType<'_> = serde_json::from_str(lower.get()).ok()?;
    Some(nominal.type_ref.symbol)
}

fn normalize_parent_aliases(
    facts: &mut FactSnapshot,
    stats: &mut SourceRecipeStats,
) -> Result<(), Error> {
    let mut references: HashMap<SymbolId, Vec<SymbolId>> = HashMap::new();
    let mut roots = Vec::new();
    for relation in &facts.relations {
        if relation.kind == RelationKind::Signature
            && facts.symbols[relation.source.index()].kind == 7
        {
            references
                .entry(relation.source)
                .or_default()
                .push(relation.target);
        } else if relation.kind == RelationKind::Parent
            && facts.symbols[relation.target.index()].kind == 7
        {
            roots.push(relation.target);
        }
    }
    for op in &facts.operations {
        if op.opcode == Opcode::Initialize
            && !op.target.is_none()
            && facts.symbols[op.target.index()].kind == 7
        {
            roots.push(op.target);
        }
    }
    roots.sort_unstable();
    roots.dedup();
    if roots.is_empty() {
        return Ok(());
    }
    let mut resolved: HashMap<SymbolId, Option<SymbolId>> = HashMap::new();
    let mut chain = Vec::new();
    for root in roots {
        if resolved.contains_key(&root) {
            continue;
        }
        chain.clear();
        let mut current = root;
        let terminal = loop {
            if let Some(known) = resolved.get(&current) {
                break *known;
            }
            if chain.len() >= 256 || chain.contains(&current) {
                break None;
            }
            chain.push(current);
            let Some(head) = alias_head(facts, current) else {
                break None;
            };
            let mut target = SymbolId::NONE;
            let mut ambiguous = false;
            for &candidate in references.get(&current).into_iter().flatten() {
                if facts.symbol_name(candidate) == head {
                    if !target.is_none() && target != candidate {
                        ambiguous = true;
                        break;
                    }
                    target = candidate;
                }
            }
            if ambiguous || target.is_none() {
                break None;
            }
            let declaration = facts.symbols[target.index()];
            if declaration.kind == 7 {
                current = target;
            } else if matches!(declaration.kind, 10 | 13 | 14)
                || (declaration.kind == 0 && facts.symbol_name(target).ends_with('#'))
            {
                break Some(target);
            } else {
                // A type parameter (including Alias[T] = T) needs an actual type
                // substitution proof. Its source spelling cannot choose a class.
                break None;
            }
        };
        for &alias in &chain {
            resolved.insert(alias, terminal);
        }
    }
    let mut compilation = Vec::new();
    let mut unsupported = Vec::new();
    for relation in &mut facts.relations {
        if relation.kind != RelationKind::Parent {
            continue;
        }
        match resolved.get(&relation.target) {
            Some(Some(target)) => {
                compilation.push(RelationRecord {
                    kind: RelationKind::Signature,
                    ..*relation
                });
                relation.target = *target;
                stats.normalized_parents += 1;
            }
            Some(None) => {
                facts.symbols[relation.source.index()].flags &= !SYMBOL_SCALA_PARENTS_COMPLETE;
                unsupported.push((relation.source, relation.file));
                stats.unsupported_alias_parents += 1;
            }
            None => {}
        }
    }
    // Scala syntax captures explicit parent-initializer operations as well as
    // ClassSignature parents. Normalize both or the executable recipe would
    // still enter the alias leaf after its receiver hierarchy was corrected.
    let mut normalized_operations = HashMap::new();
    for (index, op) in facts.operations.iter_mut().enumerate() {
        if op.opcode != Opcode::Initialize {
            continue;
        }
        match resolved.get(&op.target) {
            Some(Some(target)) => {
                let body = facts.bodies[op.body.index()];
                compilation.push(RelationRecord {
                    source: body.symbol,
                    target: op.target,
                    kind: RelationKind::Signature,
                    file: body.file,
                });
                op.target = *target;
                normalized_operations.insert(OperationId(index as u32), *target);
                stats.normalized_initializers += 1;
            }
            Some(None) => {
                let body = facts.bodies[op.body.index()];
                unsupported.push((body.symbol, body.file));
            }
            None => {}
        }
    }
    for bound in &mut facts.result_bounds {
        if let Some(&target) = normalized_operations.get(&bound.operation) {
            bound.symbol = target;
        }
    }
    facts
        .result_bounds
        .sort_unstable_by_key(|bound| (bound.symbol, bound.operation));
    // Keep the original alias as a compilation dependency after replacing the
    // executable parent. Do not duplicate a compiler-emitted Signature record.
    compilation.sort_unstable_by_key(|r| (r.source, r.target, r.file));
    compilation.dedup_by_key(|r| (r.source, r.target, r.file));
    let mut missing: HashSet<_> = compilation
        .iter()
        .map(|r| (r.source, r.target, r.file))
        .collect();
    for r in &facts.relations {
        if r.kind == RelationKind::Signature {
            missing.remove(&(r.source, r.target, r.file));
        }
    }
    compilation.retain(|r| missing.contains(&(r.source, r.target, r.file)));
    facts.relations.extend(compilation);
    unsupported.sort_unstable();
    unsupported.dedup();
    if !unsupported.is_empty() {
        let detail = intern(
            facts,
            "parent type alias has no unique equal-bound nominal compiler target",
        )?;
        for (symbol, file) in unsupported {
            if !facts.issues.iter().any(|i| {
                i.kind == IssueKind::UnsupportedModel
                    && i.file == file
                    && i.symbol == symbol
                    && i.detail == detail
            }) {
                facts.issues.push(IssueRecord {
                    kind: IssueKind::UnsupportedModel,
                    file,
                    symbol,
                    detail,
                });
            }
        }
    }
    Ok(())
}

fn intern(facts: &mut FactSnapshot, text: &str) -> Result<StrId, Error> {
    if let Some(index) = facts
        .strings
        .entries
        .iter()
        .enumerate()
        .find_map(|(i, entry)| {
            (entry.len as usize == text.len() && facts.text(StrId(i as u32)) == text).then_some(i)
        })
    {
        return StrId::checked(index);
    }
    let id = StrId::checked(facts.strings.entries.len())?;
    facts.strings.entries.push(TextRange {
        start: facts.strings.bytes.len() as u64,
        len: u32::try_from(text.len()).map_err(|_| Error::Limit("source recipe text"))?,
    });
    facts.strings.bytes.extend_from_slice(text.as_bytes());
    Ok(id)
}

#[cfg(test)]
mod tests {
    use super::*;
    use selector_facts::{FactBuilder, FileRecord, OccurrenceRecord};

    fn fixture() -> FactBuilder {
        let mut b = FactBuilder::new();
        let path = b.intern("Aliases.scala").unwrap();
        let source = b
            .intern("class Child extends Shared with Other\ntype Shared = Base[Config]")
            .unwrap();
        let context = b.intern("compile-A").unwrap();
        b.facts.files.push(FileRecord {
            path,
            source,
            context,
            revision: StrId::NONE,
            source_hash: ContentHash([1; 32]),
            flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
        });
        b
    }
    fn symbol(b: &mut FactBuilder, name: &str, kind: u32, signature: &str) -> SymbolId {
        let id = b.ensure_symbol(name, FileId(0)).unwrap();
        let signature = b.intern(signature).unwrap();
        let r = &mut b.facts.symbols[id.index()];
        r.kind = kind;
        r.file = FileId(0);
        r.signature = signature;
        r.flags = SYMBOL_DEFINED
            | if kind == 13 {
                SYMBOL_SCALA_PARENTS_COMPLETE
            } else {
                0
            };
        id
    }
    fn alias(b: &mut FactBuilder, name: &str, target: &str) -> SymbolId {
        symbol(
            b,
            name,
            7,
            &format!(
                r#"{{"type_signature":{{"lower_bound":{{"type_ref":{{"symbol":"{target}"}}}},"upper_bound":{{"type_ref":{{"symbol":"{target}"}}}}}}}}"#
            ),
        )
    }
    fn relation(b: &mut FactBuilder, source: SymbolId, target: SymbolId, kind: RelationKind) {
        b.facts.relations.push(RelationRecord {
            source,
            target,
            kind,
            file: FileId(0),
        });
    }
    #[test]
    fn captured_generic_parent_alias_selects_only_its_nominal_compiler_target() {
        let mut b = fixture();
        let child = symbol(&mut b, "p/Child#", 13, "{}");
        let base = symbol(
            &mut b,
            "com/digitalasset/canton/integration/BaseSharedEnvironment#",
            13,
            "{}",
        );
        let config = symbol(
            &mut b,
            "org/lfdecentralizedtrust/splice/config/SpliceConfig#",
            13,
            "{}",
        );
        let other = symbol(&mut b, "p/Other#", 14, "{}");
        let shared = symbol(
            &mut b,
            "p/SpliceTests.SharedSpliceEnvironment#",
            7,
            r#"{"type_signature":{"type_parameters":{},"lower_bound":{"type_ref":{"symbol":"com/digitalasset/canton/integration/BaseSharedEnvironment#","type_arguments":[{"type_ref":{"symbol":"org/lfdecentralizedtrust/splice/config/SpliceConfig#"}}]}},"upper_bound":{"type_ref":{"symbol":"com/digitalasset/canton/integration/BaseSharedEnvironment#","type_arguments":[{"type_ref":{"symbol":"org/lfdecentralizedtrust/splice/config/SpliceConfig#"}}]}}}}"#,
        );
        relation(&mut b, shared, config, RelationKind::Signature);
        relation(&mut b, shared, base, RelationKind::Signature);
        relation(&mut b, child, shared, RelationKind::Parent);
        relation(&mut b, child, other, RelationKind::Parent);
        let mut facts = b.finish().unwrap();
        let stats = augment_source_recipes(&mut facts).unwrap();
        assert_eq!(stats.normalized_parents, 1);
        let parents: Vec<_> = facts
            .relations
            .iter()
            .filter(|r| r.kind == RelationKind::Parent && r.source == child)
            .map(|r| r.target)
            .collect();
        assert_eq!(parents, [base, other]);
        assert!(
            facts.relations.iter().any(|r| r.source == child
                && r.target == shared
                && r.kind == RelationKind::Signature)
        );
        assert_ne!(
            facts.symbols[child.index()].flags & SYMBOL_SCALA_PARENTS_COMPLETE,
            0
        );
        assert_eq!(
            augment_source_recipes(&mut facts).unwrap(),
            SourceRecipeStats::default()
        );
    }
    #[test]
    fn transitive_aliases_follow_compiler_bound_context_instead_of_global_name() {
        let mut b = fixture();
        let child = symbol(&mut b, "p/Child#", 13, "{}");
        let base = symbol(&mut b, "p/Base#", 13, "{}");
        let alias2 = alias(&mut b, "p/Alias2#", "p/Base#");
        let alias1 = alias(&mut b, "p/Alias1#", "p/Alias2#");
        let other_context = b.intern("compile-B").unwrap();
        let mut duplicate = b.facts.symbols[base.index()];
        duplicate.context = other_context;
        let duplicate_id = SymbolId::checked(b.facts.symbols.len()).unwrap();
        b.facts.symbols.push(duplicate);
        assert_ne!(duplicate_id, base);
        relation(&mut b, alias1, alias2, RelationKind::Signature);
        relation(&mut b, alias2, base, RelationKind::Signature);
        relation(&mut b, child, alias1, RelationKind::Parent);
        let mut facts = b.finish().unwrap();
        augment_source_recipes(&mut facts).unwrap();
        assert_eq!(
            facts
                .relations
                .iter()
                .find(|r| r.kind == RelationKind::Parent)
                .unwrap()
                .target,
            base
        );
    }
    #[test]
    fn abstract_bounds_cycles_and_missing_or_ambiguous_contexts_remain_unknown() {
        for case in 0..5 {
            let mut b = fixture();
            let child = symbol(&mut b, "p/Child#", 13, "{}");
            let base = symbol(&mut b, "p/Base#", 13, "{}");
            let a = alias(&mut b, "p/A#", "p/Base#");
            match case {
                0 => {
                    b.facts.symbols[a.index()].signature = b.intern(r#"{"type_signature":{"lower_bound":{"type_ref":{"symbol":"p/Base#"}},"upper_bound":{"type_ref":{"symbol":"p/Other#"}}}}"#).unwrap();
                    relation(&mut b, a, base, RelationKind::Signature);
                }
                1 => {
                    b.facts.symbols[a.index()].signature = b.intern(r#"{"type_signature":{"lower_bound":{"type_ref":{"symbol":"p/A#"}},"upper_bound":{"type_ref":{"symbol":"p/A#"}}}}"#).unwrap();
                    relation(&mut b, a, a, RelationKind::Signature);
                }
                2 => {} // The spelling alone must not manufacture a relation.
                3 => {
                    let mut copy = b.facts.symbols[base.index()];
                    copy.context = b.intern("other").unwrap();
                    let duplicate = SymbolId(b.facts.symbols.len() as u32);
                    b.facts.symbols.push(copy);
                    relation(&mut b, a, base, RelationKind::Signature);
                    relation(&mut b, a, duplicate, RelationKind::Signature);
                }
                _ => {
                    b.facts.symbols[base.index()].kind = 9;
                    relation(&mut b, a, base, RelationKind::Signature);
                }
            }
            relation(&mut b, child, a, RelationKind::Parent);
            let mut facts = b.finish().unwrap();
            let stats = augment_source_recipes(&mut facts).unwrap();
            assert_eq!(stats.unsupported_alias_parents, 1, "case {case}");
            assert_eq!(facts.relations.last().unwrap().target, a);
            assert_eq!(
                facts.symbols[child.index()].flags & SYMBOL_SCALA_PARENTS_COMPLETE,
                0
            );
            assert_eq!(facts.issues.len(), 1);
            augment_source_recipes(&mut facts).unwrap();
            assert_eq!(facts.issues.len(), 1);
        }
    }

    fn accessor_fixture() -> (FactSnapshot, SymbolId, SymbolId) {
        let mut b = fixture();
        let source = b
            .intern("class Holder(val callback: Function0[Int])")
            .unwrap();
        b.facts.files[0].source = source;
        let class = symbol(&mut b, "p/Holder#", 13, "{}");
        b.facts.symbols[class.index()].span = Span { start: 6, end: 12 };
        let accessor = symbol(
            &mut b,
            "p/Holder#callback.",
            3,
            r#"{"method_signature":{"type_parameters":{},"return_type":{"type_ref":{"symbol":"scala/Function0#"}}}}"#,
        );
        let span = Span { start: 17, end: 25 };
        let field = &mut b.facts.symbols[accessor.index()];
        field.owner = class;
        field.properties = 1024;
        field.span = span;
        b.facts.occurrences.push(OccurrenceRecord {
            file: FileId(0),
            symbol: accessor,
            span,
            role: 2,
            ordinal: 0,
        });
        b.facts.operands.push(ValueId(1));
        b.facts.operations.push(OperationRecord {
            body: BodyId(0),
            opcode: Opcode::Parameter,
            target: accessor,
            dest: ValueId(1),
            a: ValueId::NONE,
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span,
            flags: 0,
        });
        b.facts.operations.push(OperationRecord {
            body: BodyId(0),
            opcode: Opcode::Constant,
            target: SymbolId::NONE,
            dest: ValueId(2),
            a: ValueId::NONE,
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span { start: 39, end: 40 },
            flags: 0,
        });
        b.facts.bodies.push(BodyRecord {
            symbol: class,
            file: FileId(0),
            span: Span { start: 0, end: 41 },
            name_span: b.facts.symbols[class.index()].span,
            operations: IdRange { start: 0, len: 2 },
            parameters: IdRange { start: 0, len: 1 },
            body_hash: ContentHash([2; 32]),
            flags: BODY_INITIALIZER,
        });
        (b.finish().unwrap(), class, accessor)
    }
    #[test]
    fn exact_source_parameter_accessor_stores_argument_and_returns_receiver_field() {
        let (mut facts, class, accessor) = accessor_fixture();
        let old_hash = facts.bodies[0].body_hash;
        let stats = augment_source_recipes(&mut facts).unwrap();
        assert_eq!(stats.parameter_accessors, 1);
        let init = facts.bodies[0];
        assert_ne!(init.body_hash, old_hash);
        let operations = &facts.operations[init.operations.range()];
        assert_eq!(
            operations
                .iter()
                .map(|op| op.opcode as u32)
                .collect::<Vec<_>>(),
            [
                Opcode::Parameter as u32,
                Opcode::StoreField as u32,
                Opcode::Constant as u32
            ]
        );
        assert_eq!(
            (operations[1].target, operations[1].a, operations[1].b),
            (accessor, ValueId(0), ValueId(1))
        );
        let getter = facts.bodies[1];
        assert_eq!(
            (getter.symbol, getter.file, getter.flags),
            (accessor, FileId(0), BODY_SOURCE_RECIPE)
        );
        let operations = &facts.operations[getter.operations.range()];
        assert_eq!(
            (operations[0].opcode, operations[0].target, operations[0].a),
            (Opcode::LoadField, accessor, ValueId(0))
        );
        assert_eq!(
            (operations[1].opcode, operations[1].a),
            (Opcode::Return, operations[0].dest)
        );
        assert_eq!(
            augment_source_recipes(&mut facts).unwrap(),
            SourceRecipeStats::default()
        );
        let graph = crate::build(
            &facts,
            &crate::BuildOptions {
                workers: 2,
                include_models: false,
            },
        )
        .unwrap();
        assert!(
            !graph
                .issues
                .iter()
                .any(|issue| issue.symbol == accessor && issue.kind == IssueKind::MissingSyntax)
        );
        assert!(
            !graph
                .edges
                .iter()
                .any(|edge| edge.source == graph.symbol_nodes[class.index()]
                    && edge.target == graph.symbol_nodes[accessor.index()]
                    && matches!(edge.kind, EdgeKind::Initialize | EdgeKind::Call))
        );
    }
    #[test]
    fn exact_operation_result_bound_is_rebased_when_constructor_stores_shift_later_bodies() {
        let (mut facts, class, accessor) = accessor_fixture();
        // Both an operation inside the affected initializer and an operation
        // in a later body need new absolute IDs after inserted field stores.
        facts.operations[1].opcode = Opcode::Call;
        facts.operations[1].target = class;
        let old_start = facts.operations.len() as u32;
        facts.operations.push(OperationRecord {
            body: BodyId(1),
            target: class,
            ..facts.operations[1]
        });
        facts.bodies.push(BodyRecord {
            symbol: accessor,
            operations: IdRange {
                start: old_start,
                len: 1,
            },
            flags: BODY_DEFERRED,
            ..facts.bodies[0]
        });
        // Use a separate later method, so the constructor accessor is genuinely
        // missing a recipe and is eligible for enrichment.
        let mut later = facts.symbols[class.index()];
        later.kind = 3;
        later.owner = class;
        let later_symbol = SymbolId(facts.symbols.len() as u32);
        facts.symbols.push(later);
        facts.bodies[1].symbol = later_symbol;
        facts.bound_classes.push(class);
        facts.result_bounds = vec![
            selector_facts::ResultBoundRecord {
                symbol: class,
                operation: OperationId(1),
                classes: IdRange { start: 0, len: 1 },
            },
            selector_facts::ResultBoundRecord {
                symbol: class,
                operation: OperationId(old_start),
                classes: IdRange { start: 0, len: 1 },
            },
        ];
        assert_eq!(
            augment_source_recipes(&mut facts)
                .unwrap()
                .parameter_accessors,
            1
        );
        let ids: Vec<_> = facts
            .result_bounds
            .iter()
            .map(|bound| bound.operation)
            .collect();
        assert_eq!(ids, [OperationId(2), OperationId(old_start + 1)]);
        for bound in &facts.result_bounds {
            assert_eq!(
                facts.operations[bound.operation.index()].target,
                bound.symbol
            );
        }
    }
    #[test]
    fn custom_lazy_abstract_foreign_or_ambiguous_parameters_do_not_get_recipes() {
        for case in 0..11 {
            let (mut facts, class, accessor) = accessor_fixture();
            match case {
                0 => facts.symbols[accessor.index()].properties |= 64,
                1 => facts.symbols[accessor.index()].properties |= 4,
                2 => facts.symbols[accessor.index()].properties = 0,
                3 => facts.files[0].flags &= !SYNTAX_VERIFIED,
                4 => facts.occurrences.clear(),
                5 => facts.symbols[accessor.index()].owner = SymbolId::NONE,
                6 => facts.operands[0] = ValueId(4),
                7 => {
                    facts.operations[1] = facts.operations[0];
                }
                8 => facts.bodies[0].flags |= BODY_BINARY_RECIPE,
                9 => facts.symbols[accessor.index()].span = Span { start: 18, end: 25 },
                _ => {
                    let body = facts.bodies[0];
                    facts.bodies.push(BodyRecord {
                        symbol: accessor,
                        flags: 0,
                        operations: IdRange::default(),
                        parameters: IdRange::default(),
                        ..body
                    });
                }
            }
            let body_count = facts.bodies.len();
            let old_hash = facts.bodies[0].body_hash;
            assert_eq!(
                augment_source_recipes(&mut facts)
                    .unwrap()
                    .parameter_accessors,
                0,
                "case {case}"
            );
            assert_eq!(facts.bodies.len(), body_count);
            assert_eq!(facts.bodies[0].body_hash, old_hash);
            assert_eq!(facts.bodies[0].symbol, class);
            assert!(
                !facts
                    .operations
                    .iter()
                    .any(|op| op.opcode == Opcode::StoreField)
            );
        }
    }
    #[test]
    fn explicit_parent_initializer_uses_the_same_normalized_alias_as_hierarchy() {
        // Existing compiler identities are used here so no name resolver or new
        // compiler symbol is needed to join the alias's nominal target.
        let mut b = fixture();
        let child = symbol(&mut b, "p/Child#", 13, "{}");
        let target = symbol(&mut b, "p/Base#", 13, "{}");
        let alias = alias(&mut b, "p/Shared#", "p/Base#");
        relation(&mut b, alias, target, RelationKind::Signature);
        relation(&mut b, child, alias, RelationKind::Parent);
        b.facts.operations.push(OperationRecord {
            body: BodyId(0),
            opcode: Opcode::Initialize,
            target: alias,
            dest: ValueId::NONE,
            a: ValueId(0),
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span::default(),
            flags: 0,
        });
        b.facts.bodies.push(BodyRecord {
            symbol: child,
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange { start: 0, len: 1 },
            parameters: IdRange::default(),
            body_hash: ContentHash::default(),
            flags: BODY_INITIALIZER,
        });
        let mut f = b.finish().unwrap();
        let stats = augment_source_recipes(&mut f).unwrap();
        assert_eq!(
            (stats.normalized_parents, stats.normalized_initializers),
            (1, 1)
        );
        assert_eq!(f.operations[0].target, target);
        assert!(
            f.relations.iter().any(|r| r.source == child
                && r.target == alias
                && r.kind == RelationKind::Signature)
        );
    }
}
