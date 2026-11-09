//! Complete compiler result constraints, projected once into flat facts.
//! Raw JSON and symbol strings borrow the retained pool. Common projections
//! allocate only in the final output columns, never a DOM or per-type vector.
use crate::signature::Text;
use selector_facts::{FactBuilder, FactSnapshot, ResultBoundRecord};
use selector_types::*;
use serde::de::{DeserializeSeed, MapAccess, SeqAccess, Visitor};
use std::collections::HashMap;

const MAX_CLASSES: usize = selector_facts::MAX_RESULT_BOUND_CLASSES;
const MAX_TYPE_DEPTH: usize = 128;
const MAX_SYMBOL_DEPTH: usize = 64;

#[derive(Clone, Copy)]
enum Mode {
    Signature(bool),
    Method,
    Wrapper,
    TypeSignature,
    Type,
    Reference,
    Conjunction,
    Members,
}
struct Node<'a, 'b> {
    projector: &'a mut Projector<'b>,
    mode: Mode,
    file: FileId,
    owner: SymbolId,
    depth: usize,
    active: usize,
}
impl<'de> DeserializeSeed<'de> for Node<'_, '_> {
    type Value = bool;
    fn deserialize<D: serde::Deserializer<'de>>(self, decoder: D) -> Result<bool, D::Error> {
        if self.depth >= MAX_TYPE_DEPTH {
            Skip(self.depth).deserialize(decoder)?;
            return Ok(false);
        }
        if matches!(self.mode, Mode::Members) {
            decoder.deserialize_seq(self)
        } else {
            decoder.deserialize_map(self)
        }
    }
}
impl<'de> Visitor<'de> for Node<'_, '_> {
    type Value = bool;
    fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("compiler result type")
    }
    fn visit_map<M: MapAccess<'de>>(self, mut map: M) -> Result<bool, M::Error> {
        let mut fields = 0usize;
        let mut required = false;
        let mut complete = true;
        while let Some(key) = map.next_key::<Text<'de>>()? {
            fields += 1;
            let child = match (self.mode, key.0.as_ref()) {
                (Mode::Signature(false), "method_signature") => Some(Mode::Method),
                (Mode::Signature(false), "value_signature") => Some(Mode::Wrapper),
                (Mode::Signature(_), "type_signature") => Some(Mode::TypeSignature),
                (Mode::Method, "return_type")
                | (Mode::Wrapper, "tpe")
                | (Mode::TypeSignature, "upper_bound") => Some(Mode::Type),
                (Mode::Type, "type_ref" | "single_type" | "this_type" | "super_type") => {
                    Some(Mode::Reference)
                }
                (Mode::Type, "annotated_type" | "existential_type" | "structural_type") => {
                    Some(Mode::Wrapper)
                }
                (Mode::Type, "intersection_type" | "with_type") => Some(Mode::Conjunction),
                (Mode::Conjunction, "types") => Some(Mode::Members),
                _ => None,
            };
            if let Some(mode) = child {
                if required && !matches!(self.mode, Mode::Signature(_) | Mode::Type) {
                    complete = false;
                }
                required = true;
                complete &= map.next_value_seed(Node {
                    projector: self.projector,
                    mode,
                    file: self.file,
                    owner: self.owner,
                    depth: self.depth + 1,
                    active: self.active,
                })?;
            } else if matches!(self.mode, Mode::Reference) && key.0 == "symbol" {
                if required {
                    complete = false;
                }
                required = true;
                let name = map.next_value::<Text<'de>>()?;
                complete &= self
                    .projector
                    .symbol(&name.0, self.file, self.owner, self.depth, self.active)
                    .map_err(serde::de::Error::custom)?;
            } else {
                map.next_value_seed(Skip(self.depth + 1))?;
                if matches!(self.mode, Mode::Signature(_) | Mode::Type) {
                    complete = false;
                }
            }
        }
        Ok(required
            && complete
            && (!matches!(self.mode, Mode::Signature(_) | Mode::Type) || fields == 1))
    }
    fn visit_seq<S: SeqAccess<'de>>(self, mut sequence: S) -> Result<bool, S::Error> {
        let mut present = false;
        let mut complete = true;
        while let Some(valid) = sequence.next_element_seed(Node {
            projector: self.projector,
            mode: Mode::Type,
            file: self.file,
            owner: self.owner,
            depth: self.depth + 1,
            active: self.active,
        })? {
            present = true;
            complete &= valid;
        }
        Ok(present && complete)
    }
}
// serde_json's RawValue / IgnoredAny skip path allocates a heap-backed nesting
// stack per decoder. Walk ignored structures directly to keep this pass flat.
struct Skip(usize);
impl<'de> DeserializeSeed<'de> for Skip {
    type Value = ();
    fn deserialize<D: serde::Deserializer<'de>>(self, decoder: D) -> Result<(), D::Error> {
        if self.0 > 512 {
            return Err(serde::de::Error::custom("compiler signature depth"));
        }
        decoder.deserialize_any(self)
    }
}
impl<'de> Visitor<'de> for Skip {
    type Value = ();
    fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("ignored compiler metadata")
    }
    fn visit_map<M: MapAccess<'de>>(self, mut map: M) -> Result<(), M::Error> {
        while map.next_key::<Text<'de>>()?.is_some() {
            map.next_value_seed(Skip(self.0 + 1))?;
        }
        Ok(())
    }
    fn visit_seq<S: SeqAccess<'de>>(self, mut sequence: S) -> Result<(), S::Error> {
        while sequence.next_element_seed(Skip(self.0 + 1))?.is_some() {}
        Ok(())
    }
    fn visit_bool<E: serde::de::Error>(self, _: bool) -> Result<(), E> {
        Ok(())
    }
    fn visit_i64<E: serde::de::Error>(self, _: i64) -> Result<(), E> {
        Ok(())
    }
    fn visit_u64<E: serde::de::Error>(self, _: u64) -> Result<(), E> {
        Ok(())
    }
    fn visit_f64<E: serde::de::Error>(self, _: f64) -> Result<(), E> {
        Ok(())
    }
    fn visit_str<E: serde::de::Error>(self, _: &str) -> Result<(), E> {
        Ok(())
    }
    fn visit_unit<E: serde::de::Error>(self) -> Result<(), E> {
        Ok(())
    }
}

struct Projector<'a> {
    facts: &'a FactSnapshot,
    declarations: HashMap<(&'a str, StrId, FileId), SymbolId>,
    signature_offsets: Vec<usize>,
    signature_targets: Vec<SymbolId>,
    conflicts: &'a [bool],
    classes: [SymbolId; MAX_CLASSES],
    count: usize,
    active: [SymbolId; MAX_SYMBOL_DEPTH],
}
impl<'a> Projector<'a> {
    fn signature(
        &mut self,
        symbol: SymbolId,
        aliases_only: bool,
        depth: usize,
        active: usize,
    ) -> Result<bool, Error> {
        let record = self.facts.symbols[symbol.index()];
        if record.flags & SYMBOL_DEFINED == 0
            || self.conflicts[symbol.index()]
            || record.signature.is_none()
        {
            return Ok(false);
        }
        let mut decoder = serde_json::Deserializer::from_str(self.facts.text(record.signature));
        decoder.disable_recursion_limit();
        let complete = Node {
            projector: self,
            mode: Mode::Signature(aliases_only),
            file: record.file,
            owner: symbol,
            depth,
            active,
        }
        .deserialize(&mut decoder)
        .map_err(crate::json_error)?;
        decoder.end().map_err(crate::json_error)?;
        Ok(complete)
    }
    fn result(&mut self, symbol: SymbolId) -> Result<bool, Error> {
        self.signature(symbol, false, 0, 0)
    }
    fn symbol(
        &mut self,
        name: &str,
        file: FileId,
        owner: SymbolId,
        depth: usize,
        active: usize,
    ) -> Result<bool, Error> {
        let context = if file.is_none() {
            StrId::NONE
        } else {
            self.facts.files[file.index()].context
        };
        let local = if selector_types::symbol::is_local(name) {
            file
        } else {
            FileId::NONE
        };
        let mut resolved = self.declarations.get(&(name, context, local)).copied();
        if resolved.is_none() {
            // Classpath qualification remaps exact compiler Signature links;
            // raw signature spellings remain in their original source context.
            // Use that normalized proof, never an arbitrary global-name match.
            for target in &self.signature_targets
                [self.signature_offsets[owner.index()]..self.signature_offsets[owner.index() + 1]]
            {
                if self.facts.symbol_name(*target) == name {
                    if resolved.is_some_and(|previous| previous != *target) {
                        return Ok(false);
                    }
                    resolved = Some(*target);
                }
            }
        }
        let Some(symbol) = resolved else {
            return Ok(false);
        };
        if active == MAX_SYMBOL_DEPTH
            || self.active[..active].contains(&symbol)
            || self.conflicts[symbol.index()]
        {
            return Ok(false);
        }
        let record = self.facts.symbols[symbol.index()];
        if record.flags & (SYMBOL_DEFINED | SYMBOL_NATIVE_BINARY | SYMBOL_JVM_CLASS_HEADER_VERIFIED)
            == 0
        {
            return Ok(false);
        }
        if matches!(record.kind, 13 | 14) {
            if !self.classes[..self.count].contains(&symbol) {
                if self.count == MAX_CLASSES {
                    return Ok(false);
                }
                self.classes[self.count] = symbol;
                self.count += 1;
            }
            return Ok(true);
        }
        self.active[active] = symbol;
        self.signature(symbol, true, depth + 1, active + 1)
    }
}

/// Rebuild declaration constraints after semantic import or verified native
/// class enrichment. Existing operation-specific compiler clauses and verified
/// native descriptor clauses survive; compiler declaration clauses take priority.
/// Signatures are streamed once; no JSON objects or symbol strings are cloned.
pub fn project_result_bounds(facts: &mut FactSnapshot) -> Result<(), Error> {
    let mut conflicts = vec![false; facts.symbols.len()];
    let mut file_conflicts = vec![false; facts.files.len()];
    let mut global_conflict = false;
    for issue in &facts.issues {
        if issue.kind == IssueKind::ContextConflict {
            if !issue.symbol.is_none() {
                conflicts[issue.symbol.index()] = true;
            } else if !issue.file.is_none() {
                file_conflicts[issue.file.index()] = true;
            } else {
                global_conflict = true;
            }
        }
    }
    for (index, record) in facts.symbols.iter().enumerate() {
        conflicts[index] |=
            global_conflict || (!record.file.is_none() && file_conflicts[record.file.index()]);
    }
    let mut rows = Vec::with_capacity(facts.result_bounds.len());
    let mut classes = Vec::with_capacity(facts.bound_classes.len());
    {
        // Only type declarations can satisfy TypeRef bounds. The index borrows
        // pooled spellings and includes compilation context and local-file ID.
        let eligible = |record: &&selector_facts::SymbolRecord| {
            matches!(record.kind, 7 | 9 | 13 | 14)
                && record.flags
                    & (SYMBOL_DEFINED | SYMBOL_NATIVE_BINARY | SYMBOL_JVM_CLASS_HEADER_VERIFIED)
                    != 0
        };
        let mut declarations =
            HashMap::with_capacity(facts.symbols.iter().filter(eligible).count());
        for (index, record) in facts
            .symbols
            .iter()
            .enumerate()
            .filter(|(_, record)| eligible(record))
        {
            let name = facts.text(record.name);
            let local = if selector_types::symbol::is_local(name) {
                record.file
            } else {
                FileId::NONE
            };
            declarations.insert((name, record.context, local), SymbolId(index as u32));
        }
        let mut signature_offsets = vec![0usize; facts.symbols.len() + 1];
        for relation in facts
            .relations
            .iter()
            .filter(|relation| relation.kind == RelationKind::Signature)
        {
            signature_offsets[relation.source.index() + 1] += 1;
        }
        for index in 1..signature_offsets.len() {
            signature_offsets[index] += signature_offsets[index - 1];
        }
        let mut signature_targets = vec![SymbolId::NONE; *signature_offsets.last().unwrap()];
        for relation in facts
            .relations
            .iter()
            .filter(|relation| relation.kind == RelationKind::Signature)
        {
            let end = &mut signature_offsets[relation.source.index() + 1];
            *end -= 1;
            signature_targets[*end] = relation.target;
        }
        // Scatter backwards using the prefix ends themselves, then restore
        // starts in place. This avoids a second symbol-sized cursor allocation.
        for index in 0..facts.symbols.len() {
            signature_offsets[index] = signature_offsets[index + 1];
        }
        *signature_offsets.last_mut().unwrap() = signature_targets.len();
        let mut projector = Projector {
            facts,
            declarations,
            signature_offsets,
            signature_targets,
            conflicts: &conflicts,
            classes: [SymbolId::NONE; MAX_CLASSES],
            count: 0,
            active: [SymbolId::NONE; MAX_SYMBOL_DEPTH],
        };
        for index in 0..projector.facts.symbols.len() {
            projector.count = 0;
            if matches!(projector.facts.symbols[index].kind, 10..=14) {
                continue;
            }
            if !projector.result(SymbolId(index as u32))? || projector.count == 0 {
                continue;
            }
            projector.classes[..projector.count].sort_unstable();
            let start =
                u32::try_from(classes.len()).map_err(|_| Error::Limit("compiler result bounds"))?;
            classes.extend_from_slice(&projector.classes[..projector.count]);
            rows.push(ResultBoundRecord {
                symbol: SymbolId(index as u32),
                operation: OperationId::NONE,
                classes: IdRange {
                    start,
                    len: projector.count as u32,
                },
            });
        }
    }
    // Native declarations have no compiler JSON signature to reproject. Keep
    // only independently admitted native clauses, behind an actual binary
    // recipe and same-context verified class endpoints. A copied source flag
    // or stale row cannot establish this authority. Compiler rows above win.
    let mut native_context_conflicts = Vec::new();
    for issue in &facts.issues {
        if issue.kind == IssueKind::ContextConflict
            && issue.symbol.is_none()
            && !issue.file.is_none()
        {
            native_context_conflicts.push(facts.files[issue.file.index()].context);
        }
    }
    native_context_conflicts.sort_unstable();
    native_context_conflicts.dedup();
    let native_needed = facts.result_bounds.iter().any(|row| {
        row.operation.is_none()
            && facts.symbols[row.symbol.index()].flags & SYMBOL_NATIVE_BINARY != 0
    });
    let mut native_sources = vec![
        false;
        if native_needed {
            facts.symbols.len()
        } else {
            0
        }
    ];
    for body in facts
        .bodies
        .iter()
        .take(if native_needed { facts.bodies.len() } else { 0 })
    {
        if body.flags & BODY_BINARY_RECIPE == 0 || body.file.is_none() {
            continue;
        }
        let source = facts.symbols[body.symbol.index()];
        let file = facts.files[body.file.index()];
        let Some(owner) = facts.symbols.get(source.owner.index()) else {
            continue;
        };
        native_sources[body.symbol.index()] |= source.flags & SYMBOL_NATIVE_BINARY != 0
            && source.kind == 3
            && source.file == body.file
            && !conflicts[body.symbol.index()]
            && !conflicts[source.owner.index()]
            && native_context_conflicts
                .binary_search(&source.context)
                .is_err()
            && file.flags & FILE_BINARY_SOURCE != 0
            && file.source_hash != ContentHash::default()
            && file.context == source.context
            && owner.context == source.context
            && matches!(owner.kind, 13 | 14)
            && owner.flags & SYMBOL_JVM_CLASS_HEADER_VERIFIED != 0;
    }
    let compiler_rows = rows.len();
    for prior in &facts.result_bounds {
        if prior.operation.is_none() {
            if !native_sources
                .get(prior.symbol.index())
                .copied()
                .unwrap_or(false)
                || rows[..compiler_rows]
                    .binary_search_by_key(&prior.symbol, |row| row.symbol)
                    .is_ok()
                || facts.bound_classes[prior.classes.range()]
                    .iter()
                    .any(|class| {
                        let declaration = facts.symbols[class.index()];
                        conflicts[class.index()]
                            || declaration.context != facts.symbols[prior.symbol.index()].context
                            || !matches!(declaration.kind, 13 | 14)
                            || declaration.flags & SYMBOL_JVM_CLASS_HEADER_VERIFIED == 0
                    })
            {
                continue;
            }
        }
        if conflicts[prior.symbol.index()]
            || facts.bound_classes[prior.classes.range()]
                .iter()
                .any(|class| {
                    let record = facts.symbols[class.index()];
                    conflicts[class.index()]
                        || !matches!(record.kind, 13 | 14)
                        || record.flags
                            & (SYMBOL_DEFINED
                                | SYMBOL_NATIVE_BINARY
                                | SYMBOL_JVM_CLASS_HEADER_VERIFIED)
                            == 0
                })
        {
            continue;
        }
        let start =
            u32::try_from(classes.len()).map_err(|_| Error::Limit("compiler result bounds"))?;
        classes.extend_from_slice(&facts.bound_classes[prior.classes.range()]);
        rows.push(ResultBoundRecord {
            classes: IdRange {
                start,
                len: prior.classes.len,
            },
            ..*prior
        });
    }
    rows.sort_unstable_by_key(|row| (row.symbol, row.operation));
    facts.result_bounds = rows;
    facts.bound_classes = classes;
    Ok(())
}

pub(crate) fn project(builder: &mut FactBuilder) -> Result<(), Error> {
    project_result_bounds(&mut builder.facts)
}

#[cfg(test)]
mod tests {
    use super::*;
    use selector_facts::FileRecord;
    fn builder() -> FactBuilder {
        let mut builder = FactBuilder::new();
        let path = builder.intern("bounds-control.scala").unwrap();
        let source = builder.intern("").unwrap();
        builder.facts.files.push(FileRecord {
            path,
            source,
            revision: StrId::NONE,
            context: StrId::NONE,
            source_hash: ContentHash::default(),
            flags: SOURCE_VERIFIED,
        });
        builder
    }
    fn defined(builder: &mut FactBuilder, name: &str, kind: u32, signature: &str) -> SymbolId {
        let symbol = builder.ensure_symbol(name, FileId(0)).unwrap();
        let signature = if signature.is_empty() {
            StrId::NONE
        } else {
            builder.intern(signature).unwrap()
        };
        let record = &mut builder.facts.symbols[symbol.index()];
        record.kind = kind;
        record.file = FileId(0);
        record.flags = SYMBOL_DEFINED;
        record.signature = signature;
        symbol
    }
    #[test]
    fn alias_parameter_and_wrapped_intersection_form_one_complete_conjunction() {
        let mut builder = builder();
        let class = defined(&mut builder, "p/Narrow#", 13, "");
        let marker = defined(&mut builder, "p/Marker#", 14, "");
        defined(
            &mut builder,
            "p/F.Alias#",
            7,
            r#"{"type_signature":{"lower_bound":{"type_ref":{"symbol":"p/Narrow#"}},"upper_bound":{"type_ref":{"symbol":"p/Narrow#"}}}}"#,
        );
        defined(
            &mut builder,
            "p/F.f().[T]",
            9,
            r#"{"type_signature":{"upper_bound":{"type_ref":{"symbol":"p/F.Alias#"}}}}"#,
        );
        let generic = defined(
            &mut builder,
            "p/F.f().",
            3,
            r#"{"method_signature":{"return_type":{"type_ref":{"symbol":"p/F.f().[T]"}}}}"#,
        );
        let intersection = defined(
            &mut builder,
            "p/F.intersection().",
            3,
            r#"{"method_signature":{"return_type":{"structural_type":{"declarations":{},"tpe":{"with_type":{"types":[{"type_ref":{"symbol":"p/Marker#"}},{"type_ref":{"symbol":"p/Narrow#"}},{"type_ref":{"symbol":"p/Marker#"}}]}}}}}}"#,
        );
        project(&mut builder).unwrap();
        assert_eq!(
            builder.facts.result_bound(generic, OperationId::NONE),
            Some(&[class][..])
        );
        assert_eq!(
            builder.facts.result_bound(intersection, OperationId::NONE),
            Some(&[class, marker][..])
        );
        builder.finish().unwrap();
    }
    #[test]
    fn a_missing_conjunct_cycle_or_by_name_wrapper_cannot_license_partial_narrowing() {
        let mut builder = builder();
        defined(&mut builder, "p/Narrow#", 13, "");
        defined(
            &mut builder,
            "p/A#",
            9,
            r#"{"type_signature":{"upper_bound":{"type_ref":{"symbol":"p/B#"}}}}"#,
        );
        defined(
            &mut builder,
            "p/B#",
            9,
            r#"{"type_signature":{"upper_bound":{"type_ref":{"symbol":"p/A#"}}}}"#,
        );
        let cycle = defined(
            &mut builder,
            "p/F.cycle().",
            3,
            r#"{"method_signature":{"return_type":{"type_ref":{"symbol":"p/A#"}}}}"#,
        );
        let partial = defined(
            &mut builder,
            "p/F.partial().",
            3,
            r#"{"method_signature":{"return_type":{"with_type":{"types":[{"type_ref":{"symbol":"p/Narrow#"}},{"type_ref":{"symbol":"p/Missing#"}}]}}}}"#,
        );
        let thunk = defined(
            &mut builder,
            "p/F.thunk().(arg)",
            8,
            r#"{"value_signature":{"tpe":{"by_name_type":{"tpe":{"type_ref":{"symbol":"p/Narrow#"}}}}}}"#,
        );
        project(&mut builder).unwrap();
        for symbol in [cycle, partial, thunk] {
            assert_eq!(builder.facts.result_bound(symbol, OperationId::NONE), None);
        }
        assert!(builder.facts.bound_classes.is_empty());
    }
    #[test]
    fn absent_unverified_or_conflicted_class_metadata_is_not_a_runtime_class_bound() {
        for control in ["missing", "parameter", "conflict"] {
            let mut builder = builder();
            let class = defined(
                &mut builder,
                "p/Narrow#",
                if control == "parameter" { 9 } else { 13 },
                "",
            );
            if control == "missing" {
                builder.facts.symbols[class.index()].flags = 0;
            }
            if control == "conflict" {
                builder
                    .issue(
                        IssueKind::ContextConflict,
                        FileId(0),
                        class,
                        "synthetic conflicting declaration",
                    )
                    .unwrap();
            }
            let factory = defined(
                &mut builder,
                "p/F.narrow().",
                3,
                r#"{"method_signature":{"return_type":{"type_ref":{"symbol":"p/Narrow#"}}}}"#,
            );
            project(&mut builder).unwrap();
            assert_eq!(
                builder.facts.result_bound(factory, OperationId::NONE),
                None,
                "{control}"
            );
        }
    }
    #[test]
    fn exact_context_lookup_cannot_borrow_another_compilation_declaration() {
        let mut builder = builder();
        let first = builder.intern("context:first").unwrap();
        builder.facts.files[0].context = first;
        defined(&mut builder, "p/Narrow#", 13, "");
        let second = builder.intern("context:second").unwrap();
        let source = builder.facts.files[0];
        builder.facts.files.push(FileRecord {
            context: second,
            ..source
        });
        let factory = builder.ensure_symbol("p/F.narrow().", FileId(1)).unwrap();
        let signature = builder
            .intern(r#"{"method_signature":{"return_type":{"type_ref":{"symbol":"p/Narrow#"}}}}"#)
            .unwrap();
        let record = &mut builder.facts.symbols[factory.index()];
        record.file = FileId(1);
        record.kind = 3;
        record.signature = signature;
        record.flags = SYMBOL_DEFINED;
        project(&mut builder).unwrap();
        assert_eq!(builder.facts.result_bound(factory, OperationId::NONE), None);
    }
    #[test]
    fn a_unique_classpath_qualified_signature_link_is_authoritative_until_its_scope_is_conflicted()
    {
        use selector_facts::RelationRecord;
        let mut builder = builder();
        let provider = builder.intern("context:provider").unwrap();
        builder.facts.files[0].context = provider;
        let class = defined(&mut builder, "p/Narrow#", 13, "");
        let consumer = builder.intern("context:consumer").unwrap();
        let source = builder.facts.files[0];
        builder.facts.files.push(FileRecord {
            context: consumer,
            ..source
        });
        let factory = builder.ensure_symbol("p/F.narrow().", FileId(1)).unwrap();
        let signature = builder
            .intern(r#"{"method_signature":{"return_type":{"type_ref":{"symbol":"p/Narrow#"}}}}"#)
            .unwrap();
        let record = &mut builder.facts.symbols[factory.index()];
        record.file = FileId(1);
        record.kind = 3;
        record.signature = signature;
        record.flags = SYMBOL_DEFINED;
        builder.facts.relations.push(RelationRecord {
            source: factory,
            target: class,
            kind: RelationKind::Signature,
            file: FileId(1),
        });
        project(&mut builder).unwrap();
        assert_eq!(
            builder.facts.result_bound(factory, OperationId::NONE),
            Some(&[class][..])
        );
        for (file, symbol) in [
            (FileId(1), factory),
            (FileId(1), SymbolId::NONE),
            (FileId::NONE, SymbolId::NONE),
        ] {
            builder.facts.issues.clear();
            builder
                .issue(
                    IssueKind::ContextConflict,
                    file,
                    symbol,
                    "synthetic qualified binding or context uncertainty",
                )
                .unwrap();
            project(&mut builder).unwrap();
            assert_eq!(builder.facts.result_bound(factory, OperationId::NONE), None);
        }
        builder.facts.issues.clear();
        let third = builder.intern("context:other-provider").unwrap();
        builder.facts.files.push(FileRecord {
            context: third,
            ..source
        });
        let other = builder.ensure_symbol("p/Narrow#", FileId(2)).unwrap();
        let record = &mut builder.facts.symbols[other.index()];
        record.kind = 13;
        record.file = FileId(2);
        record.flags = SYMBOL_DEFINED;
        builder.facts.relations.push(RelationRecord {
            source: factory,
            target: other,
            kind: RelationKind::Signature,
            file: FileId(1),
        });
        project(&mut builder).unwrap();
        assert_eq!(
            builder.facts.result_bound(factory, OperationId::NONE),
            None,
            "two exact qualified providers cannot be resolved by first match"
        );
    }
    #[test]
    fn post_binary_projection_admits_verified_class_metadata_and_preserves_operation_clauses() {
        use selector_facts::{BodyRecord, OperationRecord};
        let mut builder = builder();
        let class = builder
            .ensure_symbol("external/Narrow#", FileId(0))
            .unwrap();
        let factory = defined(
            &mut builder,
            "p/F.external().",
            3,
            r#"{"method_signature":{"return_type":{"type_ref":{"symbol":"external/Narrow#"}}}}"#,
        );
        project(&mut builder).unwrap();
        assert_eq!(builder.facts.result_bound(factory, OperationId::NONE), None);
        let record = &mut builder.facts.symbols[class.index()];
        record.kind = 13;
        record.flags = SYMBOL_NATIVE_BINARY;
        let operation = OperationId(0);
        builder.facts.bodies.push(BodyRecord {
            symbol: factory,
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange { start: 0, len: 1 },
            parameters: IdRange::default(),
            body_hash: ContentHash::default(),
            flags: 0,
        });
        builder.facts.operations.push(OperationRecord {
            body: BodyId(0),
            opcode: Opcode::Call,
            target: factory,
            dest: ValueId::NONE,
            a: ValueId::NONE,
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span::default(),
            flags: 0,
        });
        builder.facts.bound_classes.push(class);
        builder.facts.result_bounds.push(ResultBoundRecord {
            symbol: factory,
            operation,
            classes: IdRange { start: 0, len: 1 },
        });
        for authority in [SYMBOL_NATIVE_BINARY, SYMBOL_JVM_CLASS_HEADER_VERIFIED] {
            builder.facts.symbols[class.index()].flags = authority;
            project_result_bounds(&mut builder.facts).unwrap();
            assert_eq!(builder.facts.result_bounds.len(), 2);
            assert_eq!(
                builder.facts.result_bound(factory, OperationId::NONE),
                Some(&[class][..])
            );
            assert_eq!(
                builder.facts.result_bound(factory, operation),
                Some(&[class][..])
            );
            builder.facts.validate().unwrap();
        }
    }
    // Normalized authority controls, not a compiler/JVM fixture producer.
    fn native_declaration() -> (FactBuilder, SymbolId, SymbolId, SymbolId) {
        use selector_facts::{BodyRecord, OperationRecord};
        let mut builder = builder();
        let context = builder.intern("native-bound").unwrap();
        let path = builder.intern("captured.jar!/p/Owner.class").unwrap();
        let source = builder.intern("").unwrap();
        builder.facts.files.push(FileRecord {
            path,
            source,
            revision: StrId::NONE,
            context,
            source_hash: ContentHash([1; 32]),
            flags: FILE_BINARY_SOURCE,
        });
        let owner = builder.ensure_global_symbol("p/Owner#", context).unwrap();
        let class = builder.ensure_global_symbol("p/Result#", context).unwrap();
        for symbol in [owner, class] {
            let row = &mut builder.facts.symbols[symbol.index()];
            row.kind = 13;
            row.flags = SYMBOL_NATIVE_BINARY | SYMBOL_JVM_CLASS_HEADER_VERIFIED;
            row.file = FileId(1);
        }
        let method = builder
            .ensure_global_symbol("@jvm/7:p/Owner4:make11:()Lp/Result;", context)
            .unwrap();
        let row = &mut builder.facts.symbols[method.index()];
        row.kind = 3;
        row.owner = owner;
        row.file = FileId(1);
        row.flags = SYMBOL_NATIVE_BINARY;
        builder.facts.bodies.push(BodyRecord {
            symbol: method,
            file: FileId(1),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange { start: 0, len: 1 },
            parameters: IdRange::default(),
            body_hash: ContentHash([1; 32]),
            flags: BODY_BINARY_RECIPE,
        });
        builder.facts.operations.push(OperationRecord {
            body: BodyId(0),
            opcode: Opcode::Call,
            target: method,
            dest: ValueId::NONE,
            a: ValueId::NONE,
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span::default(),
            flags: 0,
        });
        builder.facts.bound_classes.extend([class, class]);
        builder.facts.result_bounds.extend([
            ResultBoundRecord {
                symbol: method,
                operation: OperationId(0),
                classes: IdRange { start: 0, len: 1 },
            },
            ResultBoundRecord {
                symbol: method,
                operation: OperationId::NONE,
                classes: IdRange { start: 1, len: 1 },
            },
        ]);
        (builder, method, class, owner)
    }

    #[test]
    fn native_descriptor_clause_survives_reprojection_and_fact_codec_without_fake_signature() {
        let (mut builder, method, class, _) = native_declaration();
        assert!(builder.facts.symbols[method.index()].signature.is_none());
        for _ in 0..2 {
            project_result_bounds(&mut builder.facts).unwrap();
            assert_eq!(builder.facts.result_bounds.len(), 2);
            assert_eq!(
                builder.facts.result_bound(method, OperationId::NONE),
                Some(&[class][..])
            );
            assert_eq!(
                builder.facts.result_bound(method, OperationId(0)),
                Some(&[class][..])
            );
        }
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("native-result.bin");
        selector_facts::codec::write(&path, &builder.facts).unwrap();
        let mut read = selector_facts::codec::read(&path).unwrap();
        project_result_bounds(&mut read).unwrap();
        assert_eq!(
            read.result_bound(method, OperationId::NONE),
            Some(&[class][..])
        );
    }

    #[test]
    fn native_reprojection_revokes_missing_header_body_file_context_and_conflict_authority() {
        for mutation in 0..11 {
            let (mut builder, method, class, owner) = native_declaration();
            let other = builder.intern("other-context").unwrap();
            match mutation {
                0 => {
                    builder.facts.symbols[class.index()].flags &= !SYMBOL_JVM_CLASS_HEADER_VERIFIED
                }
                1 => builder.facts.bodies[0].flags = 0,
                2 => builder.facts.files[1].flags = SOURCE_VERIFIED | SYNTAX_VERIFIED,
                3 => builder.facts.files[1].context = other,
                4 => builder.facts.symbols[class.index()].context = other,
                5 => {
                    builder.facts.symbols[owner.index()].flags &= !SYMBOL_JVM_CLASS_HEADER_VERIFIED
                }
                6 => builder.facts.symbols[method.index()].flags = SYMBOL_DEFINED,
                7 => builder.facts.files[1].source_hash = ContentHash::default(),
                8..=10 => builder.facts.issues.push(selector_facts::IssueRecord {
                    kind: IssueKind::ContextConflict,
                    symbol: match mutation {
                        8 => method,
                        9 => class,
                        _ => SymbolId::NONE,
                    },
                    file: if mutation == 10 {
                        FileId(1)
                    } else {
                        FileId::NONE
                    },
                    detail: StrId::NONE,
                }),
                _ => unreachable!(),
            }
            project_result_bounds(&mut builder.facts).unwrap();
            assert_eq!(
                builder.facts.result_bound(method, OperationId::NONE),
                None,
                "mutation {mutation}"
            );
        }
    }

    #[test]
    fn compiler_projection_takes_precedence_without_erasing_exact_operation_native_clause() {
        let (mut builder, method, class, owner) = native_declaration();
        let signature = builder
            .intern(r#"{"method_signature":{"return_type":{"type_ref":{"symbol":"p/Owner#"}}}}"#)
            .unwrap();
        builder.facts.symbols[method.index()].signature = signature;
        // A signature string on a native-only declaration is not compiler
        // authority. This first pass must retain the independently admitted
        // native clause rather than trusting unowned JSON.
        project_result_bounds(&mut builder.facts).unwrap();
        assert_eq!(
            builder.facts.result_bound(method, OperationId::NONE),
            Some(&[class][..])
        );
        // Explicit normalized dual-authority control: the definition flag is
        // what makes this compiler signature eligible. Production never
        // manufactures a compiler signature for a native method.
        builder.facts.symbols[method.index()].flags |= SYMBOL_DEFINED;
        project_result_bounds(&mut builder.facts).unwrap();
        assert_eq!(builder.facts.result_bounds.len(), 2);
        assert_eq!(
            builder.facts.result_bound(method, OperationId::NONE),
            Some(&[owner][..])
        );
        assert_eq!(
            builder.facts.result_bound(method, OperationId(0)),
            Some(&[class][..])
        );
    }
}
