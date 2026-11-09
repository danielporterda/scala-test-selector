//! Complete compiler result constraints. A record is one conjunction; value
//! atoms retain disjunctive records without manufacturing runtime objects.
use super::*;
use std::collections::HashMap;

#[derive(Debug, Default)]
pub(super) struct BoundIndex {
    declarations: Vec<u32>,
    operations: HashMap<OperationId, u32>,
    // Exact semantic conjunction -> one active row. Producers are validated
    // separately; this reference carries no allocation or producer identity.
    canonical: Vec<u32>,
    representatives: Vec<u32>,
    runtime: Vec<u8>,
    complete: Vec<bool>,
}
impl BoundIndex {
    pub(super) fn new(
        facts: &FactSnapshot,
        ordered: &[bool],
        offsets: &[usize],
        parents: &[SymbolId],
    ) -> Self {
        if facts.result_bounds.is_empty() {
            return Self::default();
        }
        let mut conflicted = vec![false; facts.symbols.len()];
        let mut conflicted_contexts = Vec::new();
        let mut global_conflict = false;
        for issue in &facts.issues {
            if issue.kind != IssueKind::ContextConflict {
                continue;
            }
            if !issue.symbol.is_none() {
                conflicted[issue.symbol.index()] = true;
            } else if !issue.file.is_none() {
                conflicted_contexts.push(facts.files[issue.file.index()].context);
            } else {
                global_conflict = true;
            }
        }
        conflicted_contexts.sort_unstable();
        conflicted_contexts.dedup();
        for (index, symbol) in facts.symbols.iter().enumerate() {
            conflicted[index] |=
                global_conflict || conflicted_contexts.binary_search(&symbol.context).is_ok();
        }
        let runtime: Vec<_> = facts
            .symbols
            .iter()
            .enumerate()
            .map(|(i, s)| {
                if !conflicted[i]
                    && s.flags
                        & (SYMBOL_DEFINED | SYMBOL_NATIVE_BINARY | SYMBOL_JVM_CLASS_HEADER_VERIFIED)
                        != 0
                    && matches!(s.kind, 13 | 14)
                {
                    s.kind as u8 | if s.properties & 8 != 0 { 128 } else { 0 }
                } else {
                    0
                }
            })
            .collect();
        // The JVM proof supplies only unordered direct parents. It must not
        // enter TypeIndex::ordered or license Scala trait-super selection.
        let local_inventory = |node: usize| {
            ordered[node]
                || (runtime[node] != 0
                    && facts.symbols[node].flags & SYMBOL_JVM_PARENTS_COMPLETE != 0)
        };
        // Iterative parent-first DFS proves complete ancestry in O(V+E), with
        // one reusable depth stack. Cycles and unknown parent inventories fail
        // closed: they cannot prove two receiver classes are disjoint.
        let mut states = vec![0u8; ordered.len()];
        let mut stack = Vec::<(usize, usize, bool)>::new();
        for root in 0..ordered.len() {
            if states[root] != 0 {
                continue;
            }
            states[root] = 1;
            stack.push((root, offsets[root], local_inventory(root)));
            while let Some(&(node, next, good)) = stack.last() {
                if !good || next == offsets[node + 1] {
                    states[node] = if good { 2 } else { 3 };
                    stack.pop();
                    continue;
                }
                let parent = parents[next].index();
                if states[parent] == 0 {
                    states[parent] = 1;
                    stack.push((parent, offsets[parent], local_inventory(parent)));
                } else {
                    let frame = stack.last_mut().unwrap();
                    frame.1 += 1;
                    frame.2 &= states[parent] == 2;
                }
            }
        }
        let complete = states.iter().map(|s| *s == 2).collect();
        let mut declarations = vec![u32::MAX; facts.symbols.len()];
        let mut operations = HashMap::new();
        let mut canonical = vec![u32::MAX; facts.result_bounds.len()];
        let mut valid = Vec::new();
        for (i, row) in facts.result_bounds.iter().enumerate() {
            if conflicted[row.symbol.index()]
                || facts.symbols[row.symbol.index()].flags
                    & (SYMBOL_DEFINED | SYMBOL_NATIVE_BINARY | SYMBOL_JVM_CLASS_HEADER_VERIFIED)
                    == 0
                || facts.bound_classes[row.classes.range()]
                    .iter()
                    .any(|s| runtime[s.index()] == 0)
            {
                continue;
            }
            if row.operation.is_none() {
                declarations[row.symbol.index()] = i as u32;
            } else {
                operations.insert(row.operation, i as u32);
            }
            valid.push(i as u32);
        }
        // A flat temporary row permutation avoids a separately allocated key
        // for every clause. Declaration representatives minimize coupling to
        // incidental call-site specializations; identical conjunctions alone
        // are equivalent, regardless of their producer.
        valid.sort_unstable_by(|a, b| {
            let arow = facts.result_bounds[*a as usize];
            let brow = facts.result_bounds[*b as usize];
            facts.bound_classes[arow.classes.range()]
                .cmp(&facts.bound_classes[brow.classes.range()])
                .then_with(|| (!arow.operation.is_none(), *a).cmp(&(!brow.operation.is_none(), *b)))
        });
        let mut representative = u32::MAX;
        let mut representatives = Vec::new();
        for row in valid {
            if representative == u32::MAX
                || facts.bound_classes[facts.result_bounds[representative as usize].classes.range()]
                    != facts.bound_classes[facts.result_bounds[row as usize].classes.range()]
            {
                representative = row;
                representatives.push(row);
            }
            canonical[row as usize] = representative;
        }
        Self {
            declarations,
            operations,
            canonical,
            representatives,
            runtime,
            complete,
        }
    }
    pub(super) fn owned_bytes(&self) -> usize {
        self.declarations.capacity() * 4
            + self.operations.capacity() * 16
            + self.canonical.capacity() * 4
            + self.representatives.capacity() * 4
            + self.runtime.capacity()
            + self.complete.capacity()
    }
    fn row(&self, facts: &FactSnapshot, symbol: SymbolId, operation: OperationId) -> Option<usize> {
        if symbol.is_none() {
            return None;
        }
        let row = if operation.is_none() {
            *self.declarations.get(symbol.index())?
        } else {
            *self.operations.get(&operation)?
        };
        (row != u32::MAX && facts.result_bounds[row as usize].symbol == symbol)
            .then_some(row as usize)
    }
}
impl TypeIndex {
    /// A failed subtype lookup proves disjoint exact receivers only when the
    /// receiver's complete ancestry is known. The bounds index already proves
    /// unordered JVM ancestry; small snapshots without result bounds can still
    /// use the complete Scala linearization proof.
    pub(super) fn exact_ancestry_complete(
        &self,
        symbol: SymbolId,
        scratch: &mut LinearizationScratch,
    ) -> bool {
        self.bounds
            .complete
            .get(symbol.index())
            .copied()
            .unwrap_or_else(|| self.linearization(symbol, scratch).is_some())
    }
    /// Resolve an exact, validated class conjunction without coupling its
    /// identity to any particular producer. Used by semantic cache admission.
    pub fn canonical_bound_for_classes(
        &self,
        facts: &FactSnapshot,
        classes: &[SymbolId],
    ) -> Option<Atom> {
        let at = self
            .bounds
            .representatives
            .binary_search_by(|row| {
                facts.bound_classes[facts.result_bounds[*row as usize].classes.range()].cmp(classes)
            })
            .ok()?;
        let row = facts.result_bounds[self.bounds.representatives[at] as usize];
        Some(Atom {
            kind: AtomKind::UpperBound,
            site: row.operation,
            symbol: row.symbol,
            binding: 0,
        })
    }
    /// Normalize a validated abstract type constraint, preserving every concrete
    /// object/callback identity. The representative row is a semantic reference,
    /// never evidence that its producer executed. Invalid metadata fails closed.
    pub fn canonical_bound_atom(&self, facts: &FactSnapshot, atom: Atom) -> Option<Atom> {
        if atom.kind != AtomKind::UpperBound {
            return Some(atom);
        }
        if atom.binding != 0 {
            return None;
        }
        let row = self.bounds.row(facts, atom.symbol, atom.site)?;
        let canonical = *self.bounds.canonical.get(row)?;
        let row = facts.result_bounds.get(canonical as usize)?;
        Some(Atom {
            kind: AtomKind::UpperBound,
            site: row.operation,
            symbol: row.symbol,
            binding: 0,
        })
    }
    fn clause<'a>(&self, facts: &'a FactSnapshot, atom: Atom) -> Option<&'a [SymbolId]> {
        let row = self.bounds.row(facts, atom.symbol, atom.site)?;
        Some(&facts.bound_classes[facts.result_bounds[row].classes.range()])
    }
    fn possible_upper(
        &self,
        facts: &FactSnapshot,
        upper: SymbolId,
        owner: SymbolId,
        work: &mut Vec<SymbolId>,
    ) -> bool {
        if owner.is_none() {
            return true;
        }
        // Binary result descriptors name a class in the field or method's
        // classpath. Another context may represent that same loaded class under
        // a different symbol, so missing cross-context ancestry proves nothing.
        let upper_record = &facts.symbols[upper.index()];
        let owner_record = &facts.symbols[owner.index()];
        if upper_record.context != owner_record.context
            && upper_record.flags & SYMBOL_JVM_CLASS_HEADER_VERIFIED != 0
        {
            return true;
        }
        if self.subtype(upper, owner, work) || self.subtype(owner, upper, work) {
            return true;
        }
        let (a, b) = (
            self.bounds.runtime[upper.index()],
            self.bounds.runtime[owner.index()],
        );
        if a == 0
            || b == 0
            || !self.bounds.complete[upper.index()]
            || !self.bounds.complete[owner.index()]
        {
            return true;
        }
        !(a & 128 != 0 || b & 128 != 0 || (a & 127 == 13 && b & 127 == 13))
    }
    pub(super) fn clause_possible(
        &self,
        facts: &FactSnapshot,
        atom: Atom,
        owner: SymbolId,
        work: &mut Vec<SymbolId>,
    ) -> bool {
        self.clause(facts, atom).is_none_or(|classes| {
            classes
                .iter()
                .all(|upper| self.possible_upper(facts, *upper, owner, work))
        })
    }
    pub(super) fn unknown_possible(
        &self,
        facts: &FactSnapshot,
        pool: &ValuePool,
        receiver: Value,
        owner: SymbolId,
        work: &mut Vec<SymbolId>,
    ) -> bool {
        if !receiver.is_unknown() {
            return false;
        }
        if receiver.is_unbounded() {
            return true;
        }
        let mut found = false;
        for atom in pool.members(receiver) {
            if atom.kind == AtomKind::UpperBound {
                found = true;
                if self.clause_possible(facts, *atom, owner, work) {
                    return true;
                }
            }
        }
        !found
    }
}

pub(super) fn constrain_result(
    facts: &FactSnapshot,
    types: &TypeIndex,
    s: &mut Scratch,
    value: Value,
    symbol: SymbolId,
    operation: OperationId,
) -> Result<Value, Error> {
    if !value.is_unknown() {
        return Ok(value);
    }
    let Some(row) = types
        .bounds
        .row(facts, symbol, operation)
        .or_else(|| types.bounds.row(facts, symbol, OperationId::NONE))
    else {
        return Ok(value);
    };
    let upper = &facts.bound_classes[facts.result_bounds[row].classes.range()];
    if !value.is_unbounded()
        && s.pool
            .members(value)
            .iter()
            .filter(|a| a.kind == AtomKind::UpperBound)
            .all(|atom| {
                types.clause(facts, *atom).is_some_and(|existing| {
                    upper.iter().all(|bound| {
                        existing
                            .iter()
                            .any(|old| types.subtype(*old, *bound, &mut s.type_work))
                    })
                })
            })
    {
        return Ok(value);
    }
    s.receiver_atoms.clear();
    s.receiver_atoms.extend(
        s.pool
            .members(value)
            .iter()
            .copied()
            .filter(|a| a.kind != AtomKind::UpperBound),
    );
    let row = facts.result_bounds[types.bounds.canonical[row] as usize];
    s.receiver_atoms.push(Atom {
        kind: AtomKind::UpperBound,
        site: row.operation,
        symbol: row.symbol,
        binding: 0,
    });
    s.receiver_atoms.sort_unstable();
    s.pool
        .intern(&s.receiver_atoms, value.unknown | UNKNOWN_TYPED)
}

/// Prove only the unknown receiver's method selection, retaining its original
/// upper-bound value, every compatible call, and all callee/heap/init guards.
#[allow(clippy::too_many_arguments)]
pub(super) fn final_dispatch_complete(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    types: &TypeIndex,
    pool: &ValuePool,
    receiver: Value,
    operation: OperationId,
    targets: &[(NodeId, EdgeId, SymbolId)],
    work: &mut Vec<SymbolId>,
    linearization: &mut LinearizationScratch,
) -> bool {
    if !receiver.is_unknown() || receiver.is_unbounded() {
        return false;
    }
    let Some(op) = facts.operations.get(operation.index()) else {
        return false;
    };
    if op.opcode != Opcode::VirtualCall
        || op.target.is_none()
        || op.flags & (OP_SUPER | OP_QUALIFIED_SUPER) != 0
    {
        return false;
    }
    let mut found = false;
    for atom in pool.members(receiver) {
        if atom.kind == AtomKind::Object {
            continue;
        }
        if atom.kind != AtomKind::UpperBound || atom.binding != 0 {
            return false;
        }
        found = true;
        let Some(classes) = types.clause(facts, *atom) else {
            return false;
        };
        let mut final_class = SymbolId::NONE;
        for &class in classes {
            let record = &facts.symbols[class.index()];
            if record.kind == 13
                && record.flags & SYMBOL_JVM_CLASS_HEADER_VERIFIED != 0
                && record.properties & 8 != 0
                && types.exact_ancestry_complete(class, linearization)
            {
                if !final_class.is_none() && final_class != class {
                    return false;
                }
                final_class = class;
            }
        }
        if final_class.is_none() {
            return false;
        }
        let known = types
            .known_receiver_dispatch
            .binary_search(&(final_class, op.target))
            .is_ok();
        let mut selected = NodeId::NONE;
        for &(target, edge, owner) in targets {
            if owner.is_none() || !types.subtype(final_class, owner, work) {
                continue;
            }
            if targets.iter().any(|(_, _, other)| {
                *other != owner
                    && !other.is_none()
                    && types.subtype(final_class, *other, work)
                    && types.subtype(*other, owner, work)
            }) {
                continue;
            }
            // An inherited candidate alone cannot prove that a method on the
            // exact class was not omitted. A known full lookup supplies that
            // separate authority. Own-class ABI identity is intrinsically exact.
            if owner != final_class && !known {
                return false;
            }
            let Some(node) = graph.nodes.get(target.index()) else {
                return false;
            };
            let Some(method) = facts.symbols.get(node.symbol.index()) else {
                return false;
            };
            let Some(body) = facts.bodies.get(node.body.index()) else {
                return false;
            };
            let Some(file) = facts.files.get(body.file.index()) else {
                return false;
            };
            if method.owner != owner
                || method.context != facts.symbols[owner.index()].context
                || method.properties & 4 != 0
                || body.symbol != node.symbol
                || body.flags & BODY_BINARY_RECIPE == 0
                || file.flags & FILE_BINARY_SOURCE == 0
                || body.body_hash != file.source_hash
                || file.context != method.context
            {
                return false;
            }
            if node.symbol != op.target {
                let Some(candidate) = graph.edges.get(edge.index()) else {
                    return false;
                };
                if candidate.operation != operation
                    || candidate.target != target
                    || candidate.receiver != owner
                    || candidate.kind != EdgeKind::VirtualCall
                    || candidate.flags & EDGE_UNKNOWN != 0
                {
                    return false;
                }
            }
            if !selected.is_none() && selected != target {
                return false;
            }
            selected = target;
        }
        if selected.is_none() {
            return false;
        }
    }
    found
}

#[cfg(test)]
mod final_dispatch_tests;

#[cfg(test)]
mod tests {
    use super::*;

    fn unordered_jvm_hierarchy() -> FactSnapshot {
        let mut builder = FactBuilder::new();
        for name in ["j/Root#", "j/A#", "j/B#", "j/Contract#", "j/create()."] {
            builder.ensure_symbol(name, FileId::NONE).unwrap();
        }
        for (i, symbol) in builder.facts.symbols.iter_mut().enumerate() {
            symbol.flags = SYMBOL_JVM_CLASS_HEADER_VERIFIED | SYMBOL_JVM_PARENTS_COMPLETE;
            symbol.kind = if i == 3 { 14 } else { 13 };
        }
        builder.facts.symbols[4].kind = 3;
        builder.facts.symbols[4].flags = SYMBOL_NATIVE_BINARY;
        for (child, parent) in [(1, 0), (1, 3), (2, 0), (2, 3), (3, 0)] {
            builder.facts.relations.push(RelationRecord {
                source: SymbolId(child),
                target: SymbolId(parent),
                kind: RelationKind::Parent,
                file: FileId::NONE,
            });
        }
        builder.facts.bound_classes.push(SymbolId(1));
        builder.facts.result_bounds.push(ResultBoundRecord {
            symbol: SymbolId(4),
            operation: OperationId::NONE,
            classes: IdRange { start: 0, len: 1 },
        });
        builder.finish().unwrap()
    }

    #[test]
    fn unordered_jvm_inventory_bounds_unrelated_classes_without_scala_order() {
        let facts = unordered_jvm_hierarchy();
        let types = TypeIndex::new(&facts);
        let atom = types
            .canonical_bound_for_classes(&facts, &[SymbolId(1)])
            .unwrap();
        assert!(types.bounds.complete[..4].iter().all(|complete| *complete));
        assert!(!types.clause_possible(&facts, atom, SymbolId(2), &mut Vec::new()));
        assert!(types.clause_possible(&facts, atom, SymbolId(1), &mut Vec::new()));
        assert!(types.clause_possible(&facts, atom, SymbolId(3), &mut Vec::new()));
        assert!(
            types
                .linearization(SymbolId(1), &mut LinearizationScratch::default())
                .is_none(),
            "unordered inventory must never license Scala super/linearization"
        );
    }

    #[test]
    fn independent_classpath_symbol_ids_do_not_prove_native_bounds_disjoint() {
        let mut facts = unordered_jvm_hierarchy();
        // Two captures can describe the same JVM class with distinct symbol
        // ids. Complete local parent inventories cannot establish identity.
        facts.symbols[2].name = facts.symbols[1].name;
        facts.symbols[2].context = StrId(1);
        let types = TypeIndex::new(&facts);
        let atom = types
            .canonical_bound_for_classes(&facts, &[SymbolId(1)])
            .unwrap();
        assert!(types.bounds.complete[..4].iter().all(|complete| *complete));
        assert!(types.clause_possible(&facts, atom, SymbolId(2), &mut Vec::new()));
    }

    #[test]
    fn missing_conflicting_nonruntime_and_cyclic_jvm_ancestry_stays_broad() {
        for control in 0..5 {
            let mut facts = unordered_jvm_hierarchy();
            match control {
                0 => facts.symbols[0].flags &= !SYMBOL_JVM_PARENTS_COMPLETE,
                1 => facts.symbols[0].flags = SYMBOL_JVM_PARENTS_COMPLETE,
                2 => facts.symbols[0].kind = 3,
                3 => facts.issues.push(IssueRecord {
                    kind: IssueKind::ContextConflict,
                    file: FileId::NONE,
                    symbol: SymbolId(0),
                    detail: StrId::NONE,
                }),
                4 => facts.relations.push(RelationRecord {
                    source: SymbolId(0),
                    target: SymbolId(1),
                    kind: RelationKind::Parent,
                    file: FileId::NONE,
                }),
                _ => unreachable!(),
            }
            facts.validate().unwrap();
            let types = TypeIndex::new(&facts);
            let atom = types
                .canonical_bound_for_classes(&facts, &[SymbolId(1)])
                .unwrap();
            assert!(!types.bounds.complete[1], "control {control}");
            assert!(
                types.clause_possible(&facts, atom, SymbolId(2), &mut Vec::new()),
                "control {control}"
            );
        }
    }

    #[test]
    fn context_and_global_conflicts_revoke_persisted_jvm_inventory_authority() {
        for scoped in [false, true] {
            let mut facts = unordered_jvm_hierarchy();
            facts.files.push(FileRecord {
                path: StrId(0),
                source: StrId(0),
                revision: StrId::NONE,
                context: StrId::NONE,
                source_hash: ContentHash::default(),
                flags: 0,
            });
            facts.issues.push(IssueRecord {
                kind: IssueKind::ContextConflict,
                symbol: SymbolId::NONE,
                file: if scoped { FileId(0) } else { FileId::NONE },
                detail: StrId::NONE,
            });
            facts.validate().unwrap();
            assert!(
                TypeIndex::new(&facts)
                    .canonical_bound_for_classes(&facts, &[SymbolId(1)])
                    .is_none()
            );
        }
    }

    #[test]
    fn semantic_clauses_canonicalize_producers_without_merging_conjunctions_or_unknowns() {
        let mut builder = FactBuilder::new();
        for name in [
            "a().",
            "b().",
            "Narrow#",
            "Marker#",
            "Other#",
            "and().",
            "other().",
            "marker().",
        ] {
            builder.ensure_symbol(name, FileId::NONE).unwrap();
        }
        let mut facts = builder.finish().unwrap();
        for symbol in &mut facts.symbols {
            symbol.flags = SYMBOL_DEFINED | SYMBOL_SCALA_PARENTS_COMPLETE;
        }
        for class in [2, 3, 4] {
            facts.symbols[class].kind = if class == 3 { 14 } else { 13 };
        }
        for (producer, clause) in [
            (0, vec![2]),
            (1, vec![2]),
            (5, vec![2, 3]),
            (6, vec![4]),
            (7, vec![3]),
        ] {
            let start = facts.bound_classes.len() as u32;
            facts
                .bound_classes
                .extend(clause.iter().copied().map(SymbolId));
            facts.result_bounds.push(ResultBoundRecord {
                symbol: SymbolId(producer),
                operation: OperationId::NONE,
                classes: IdRange {
                    start,
                    len: clause.len() as u32,
                },
            });
        }
        facts.validate().unwrap();
        let types = TypeIndex::new(&facts);
        let mut scratch = Scratch::new(16);
        let mut values = Vec::new();
        for producer in [0, 1, 5, 6, 7] {
            values.push(
                constrain_result(
                    &facts,
                    &types,
                    &mut scratch,
                    Value::TOP,
                    SymbolId(producer),
                    OperationId::NONE,
                )
                .unwrap(),
            );
        }
        assert_eq!(
            values[0], values[1],
            "equal semantic constraints have one value identity"
        );
        assert_ne!(values[0], values[2], "Narrow and Narrow AND Marker differ");
        assert_ne!(values[0], values[3], "different classes remain distinct");
        let disjunction = scratch.pool.join(values[0], values[4]).unwrap();
        assert_ne!(
            disjunction, values[2],
            "two disjunctive clauses cannot become one conjunction"
        );
        assert_eq!(scratch.pool.members(disjunction).len(), 2);
        assert_eq!(scratch.pool.members(values[2]).len(), 1);
        let field_unknown = constrain_result(
            &facts,
            &types,
            &mut scratch,
            Value {
                set: SetId(0),
                unknown: UNKNOWN_FIELD,
            },
            SymbolId(1),
            OperationId::NONE,
        )
        .unwrap();
        assert_ne!(field_unknown, values[0]);
        assert_eq!(field_unknown.unknown, UNKNOWN_FIELD | UNKNOWN_TYPED);
        let unbounded = scratch.pool.join(values[0], Value::TOP).unwrap();
        assert!(
            unbounded.is_unbounded(),
            "an independent unbounded alternative stays unbounded"
        );
        let object = Atom {
            kind: AtomKind::Object,
            site: OperationId::NONE,
            symbol: SymbolId(2),
            binding: 0,
        };
        let callback = Atom {
            kind: AtomKind::Callback,
            site: OperationId::NONE,
            symbol: SymbolId(5),
            binding: 23,
        };
        for atom in [object, callback] {
            assert_eq!(types.canonical_bound_atom(&facts, atom), Some(atom));
            let concrete = scratch.pool.singleton(atom).unwrap();
            let joined = scratch.pool.join(concrete, values[0]).unwrap();
            assert!(scratch.pool.members(joined).contains(&atom));
        }
        let representative = types
            .canonical_bound_for_classes(&facts, &[SymbolId(2)])
            .unwrap();
        assert_eq!(scratch.pool.members(values[0]), &[representative]);
        assert_eq!(
            types.canonical_bound_atom(
                &facts,
                Atom {
                    symbol: SymbolId(1),
                    ..representative
                }
            ),
            Some(representative)
        );
        assert!(
            types
                .canonical_bound_for_classes(&facts, &[SymbolId(2), SymbolId(4)])
                .is_none(),
            "no conjunction may be invented"
        );

        // A valid unrelated representative never supplies authority for an
        // invalid actual producer, and invalid class metadata broadens the
        // entire conjunction rather than keeping its remaining classes.
        facts.symbols[0].flags = 0;
        let types = TypeIndex::new(&facts);
        assert_eq!(
            constrain_result(
                &facts,
                &types,
                &mut scratch,
                Value::TOP,
                SymbolId(0),
                OperationId::NONE
            )
            .unwrap(),
            Value::TOP
        );
        assert!(
            types
                .canonical_bound_for_classes(&facts, &[SymbolId(2)])
                .is_some()
        );
        facts.symbols[2].flags = 0;
        let types = TypeIndex::new(&facts);
        assert!(
            types
                .canonical_bound_for_classes(&facts, &[SymbolId(2)])
                .is_none()
        );
        assert!(
            types
                .canonical_bound_for_classes(&facts, &[SymbolId(2), SymbolId(3)])
                .is_none()
        );
        assert_eq!(
            constrain_result(
                &facts,
                &types,
                &mut scratch,
                Value::TOP,
                SymbolId(5),
                OperationId::NONE
            )
            .unwrap(),
            Value::TOP
        );
    }

    #[test]
    fn verified_header_authorizes_bounds_without_proving_complete_ancestry() {
        let mut builder = FactBuilder::new();
        let external = builder.ensure_symbol("p/External#", FileId::NONE).unwrap();
        let mut facts = builder.finish().unwrap();
        facts.symbols[external.index()].kind = 13;
        facts.symbols[external.index()].flags = SYMBOL_JVM_CLASS_HEADER_VERIFIED;
        facts.bound_classes.push(external);
        facts.result_bounds.push(ResultBoundRecord {
            symbol: external,
            operation: OperationId::NONE,
            classes: IdRange { start: 0, len: 1 },
        });
        facts.validate().unwrap();
        let types = TypeIndex::new(&facts);
        assert!(
            !types.bounds.complete[external.index()],
            "a header is not a complete parent inventory"
        );
        let mut scratch = Scratch::new(8);
        let value = constrain_result(
            &facts,
            &types,
            &mut scratch,
            Value::TOP,
            external,
            OperationId::NONE,
        )
        .unwrap();
        assert_eq!(value.unknown, UNKNOWN_VALUE | UNKNOWN_TYPED);
        assert_eq!(
            scratch.pool.members(value),
            &[Atom {
                kind: AtomKind::UpperBound,
                site: OperationId::NONE,
                symbol: external,
                binding: 0
            }]
        );
        let header_owned = types.owned_bytes();
        facts.symbols[external.index()].flags = SYMBOL_DEFINED;
        assert_eq!(
            TypeIndex::new(&facts).owned_bytes(),
            header_owned,
            "header authority uses the existing index and ownership ledger"
        );

        for (kind, flags) in [
            (13, 0),
            (0, SYMBOL_JVM_CLASS_HEADER_VERIFIED),
            (9, SYMBOL_JVM_CLASS_HEADER_VERIFIED),
        ] {
            facts.symbols[external.index()].kind = kind;
            facts.symbols[external.index()].flags = flags;
            let types = TypeIndex::new(&facts);
            let value = constrain_result(
                &facts,
                &types,
                &mut scratch,
                Value::TOP,
                external,
                OperationId::NONE,
            )
            .unwrap();
            assert_eq!(
                value,
                Value::TOP,
                "missing/nonruntime declaration kind={kind} flags={flags} must stay broad"
            );
        }
    }
}
