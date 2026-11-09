//! One admission contract for builders, persistence and query inputs.
use crate::*;

pub(crate) fn validate(facts: &FactSnapshot) -> Result<(), Error> {
    for count in [
        facts.strings.len(),
        facts.files.len(),
        facts.symbols.len(),
        facts.occurrences.len(),
        facts.relations.len(),
        facts.bodies.len(),
        facts.operations.len(),
        facts.operands.len(),
        facts.result_bounds.len(),
        facts.bound_classes.len(),
        facts.suites.len(),
        facts.issues.len(),
    ] {
        if count > u32::MAX as usize {
            return Err(Error::Limit("fact identifier capacity"));
        }
    }
    // Validate the text storage once, then its slice boundaries in constant time.
    // Rechecking UTF-8 for each source span would rescan a full file per operation.
    let pool =
        std::str::from_utf8(&facts.strings.bytes).map_err(|_| Error::Invalid("string UTF-8"))?;
    for entry in &facts.strings.entries {
        let start = usize::try_from(entry.start).map_err(|_| Error::Invalid("string offset"))?;
        let end = entry
            .start
            .checked_add(entry.len as u64)
            .ok_or(Error::Invalid("string overflow"))?;
        let end = usize::try_from(end).map_err(|_| Error::Invalid("string offset"))?;
        if start > end
            || end > pool.len()
            || !pool.is_char_boundary(start)
            || !pool.is_char_boundary(end)
        {
            return Err(Error::Invalid("string range"));
        }
    }
    let string_ok = |id: StrId| id.is_none() || id.index() < facts.strings.len();
    let symbol_ok = |id: SymbolId| id.is_none() || id.index() < facts.symbols.len();
    let file_ok = |id: FileId| id.is_none() || id.index() < facts.files.len();
    if !string_ok(facts.revision) {
        return Err(Error::Invalid("revision string"));
    }
    for file in &facts.files {
        if ![file.path, file.source, file.revision, file.context]
            .into_iter()
            .all(string_ok)
        {
            return Err(Error::Invalid("file strings"));
        }
        if file.path.is_none() || facts.strings.entries[file.path.index()].len == 0 {
            return Err(Error::Invalid("required file path"));
        }
        if file.flags & SOURCE_VERIFIED != 0 && file.source.is_none() {
            return Err(Error::Invalid("verified file source"));
        }
        if file.flags & SYNTAX_VERIFIED != 0 && file.flags & SOURCE_VERIFIED == 0 {
            return Err(Error::Invalid("syntax without verified source"));
        }
    }
    for (index, symbol) in facts.symbols.iter().enumerate() {
        if ![
            symbol.name,
            symbol.display,
            symbol.context,
            symbol.signature,
        ]
        .into_iter()
        .all(string_ok)
            || !symbol_ok(symbol.owner)
            || !file_ok(symbol.file)
        {
            return Err(Error::Invalid("symbol references"));
        }
        if symbol.name.is_none() || facts.strings.entries[symbol.name.index()].len == 0 {
            return Err(Error::Invalid("required symbol identity"));
        }
        source_span(facts, symbol.file, symbol.span, "symbol", index)?;
    }
    for (index, occurrence) in facts.occurrences.iter().enumerate() {
        if occurrence.file.is_none()
            || !file_ok(occurrence.file)
            || occurrence.symbol.is_none()
            || !symbol_ok(occurrence.symbol)
        {
            return Err(Error::Invalid("occurrence references"));
        }
        source_span(facts, occurrence.file, occurrence.span, "occurrence", index)?;
    }
    for relation in &facts.relations {
        if relation.source.is_none()
            || !symbol_ok(relation.source)
            || relation.target.is_none()
            || !symbol_ok(relation.target)
            || !file_ok(relation.file)
        {
            return Err(Error::Invalid("relation references"));
        }
        if matches!(
            relation.kind,
            RelationKind::DeferredDispatch | RelationKind::KnownReceiverDispatch
        ) {
            let receiver = facts.symbols[relation.source.index()];
            let contract = facts.symbols[relation.target.index()];
            if !matches!(receiver.kind, 10 | 13)
                || !matches!(contract.kind, 0 | 3 | 6)
                || contract.owner.is_none()
                || !matches!(facts.symbols[contract.owner.index()].kind, 10 | 13 | 14)
                || facts.symbols[contract.owner.index()].context != contract.context
                || relation.file.is_none()
                || facts.files[relation.file.index()].context != receiver.context
                || receiver.flags & (SYMBOL_DEFINED | SYMBOL_JVM_CLASS_HEADER_VERIFIED) == 0
            {
                return Err(Error::Invalid("deferred dispatch scope"));
            }
        }
        if relation.kind == RelationKind::DeferredReceiverDispatch {
            let receiver = facts.symbols[relation.source.index()];
            if relation.target != relation.source
                || !matches!(receiver.kind, 10 | 13)
                || receiver.flags & (SYMBOL_DEFINED | SYMBOL_JVM_CLASS_HEADER_VERIFIED) == 0
                || relation.file.is_none()
                || facts.files[relation.file.index()].context != receiver.context
            {
                return Err(Error::Invalid("deferred receiver dispatch scope"));
            }
        }
    }
    for (index, body) in facts.bodies.iter().enumerate() {
        if body.symbol.is_none()
            || !symbol_ok(body.symbol)
            || body.file.is_none()
            || !file_ok(body.file)
        {
            return Err(Error::Invalid("body references"));
        }
        source_span(facts, body.file, body.span, "body", index)?;
        // A method's name may precede its expression body. Both spans must refer
        // to its file; containment between these two ranges is not required.
        source_span(facts, body.file, body.name_span, "body name", index)?;
        checked_range(body.operations, facts.operations.len())?;
        checked_range(body.parameters, facts.operands.len())?;
    }
    for (index, operation) in facts.operations.iter().enumerate() {
        let body = facts
            .bodies
            .get(operation.body.index())
            .ok_or(Error::Invalid("operation body"))?;
        if !symbol_ok(operation.target) {
            return Err(Error::Invalid("operation target"));
        }
        if operation.opcode == Opcode::PackSequence
            && (operation.target.is_none()
                || facts.symbol_name(operation.target) != SEQUENCE_ELEMENTS_SYMBOL)
        {
            return Err(Error::Invalid("sequence element channel"));
        }
        if operation.flags & OP_SEQUENCE_ELEMENT_VIEW != 0
            && (!matches!(operation.opcode, Opcode::Call | Opcode::VirtualCall)
                || operation.target.is_none()
                || facts.symbol_name(operation.target) != "scala/collection/SeqOps#apply()."
                || operation.dest.is_none()
                || operation.a.is_none()
                || operation.arguments.len != 1
                || operation.flags & (OP_SUPER | OP_QUALIFIED_SUPER | OP_SYNTHETIC_PARAMETER_APPLY)
                    != 0)
        {
            return Err(Error::Invalid("sequence element view certificate shape"));
        }
        if !checked_range(body.operations, facts.operations.len())?.contains(&index) {
            return Err(Error::Invalid("operation body membership"));
        }
        checked_range(operation.arguments, facts.operands.len())?;
        source_span(facts, body.file, operation.span, "operation", index)?;
    }
    // Reverse ownership catches overlapping slices even when the operation's
    // designated body contains it. No temporary per-operation map is necessary.
    for (body_id, body) in facts.bodies.iter().enumerate() {
        for operation in &facts.operations[checked_range(body.operations, facts.operations.len())?]
        {
            if operation.body.index() != body_id {
                return Err(Error::Invalid("body operation ownership"));
            }
        }
    }
    for class in &facts.bound_classes {
        if class.is_none() || !symbol_ok(*class) {
            return Err(Error::Invalid("result bound class reference"));
        }
    }
    let mut previous_bound = None;
    for bound in &facts.result_bounds {
        if bound.symbol.is_none() || !symbol_ok(bound.symbol) {
            return Err(Error::Invalid("result bound symbol"));
        }
        if !bound.operation.is_none()
            && facts
                .operations
                .get(bound.operation.index())
                .is_none_or(|op| op.target != bound.symbol)
        {
            return Err(Error::Invalid("result bound operation target"));
        }
        let key = (bound.symbol, bound.operation);
        if previous_bound.is_some_and(|previous| previous >= key) {
            return Err(Error::Invalid("result bound key order"));
        }
        previous_bound = Some(key);
        if bound.classes.len == 0 || bound.classes.len as usize > MAX_RESULT_BOUND_CLASSES {
            return Err(Error::Invalid("result bound conjunction size"));
        }
        let classes =
            &facts.bound_classes[checked_range(bound.classes, facts.bound_classes.len())?];
        if classes.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(Error::Invalid("result bound class order"));
        }
        // Kind, definition and producer authority are intentionally not inferred
        // from this structural table. The solver must revalidate current class
        // metadata and broaden a clause whose source authority is unavailable.
    }
    for suite in &facts.suites {
        if !string_ok(suite.name) || !symbol_ok(suite.symbol) || !file_ok(suite.file) {
            return Err(Error::Invalid("suite references"));
        }
    }
    for issue in &facts.issues {
        if !string_ok(issue.detail) || !file_ok(issue.file) || !symbol_ok(issue.symbol) {
            return Err(Error::Invalid("issue references"));
        }
        if issue.kind == IssueKind::IncompleteHierarchy {
            if issue.file.is_none() || issue.symbol.is_none() {
                return Err(Error::Invalid("hierarchy diagnostic provenance"));
            }
            let file = facts.files[issue.file.index()];
            if file.flags & FILE_BINARY_SOURCE == 0
                || file.source_hash == ContentHash::default()
                || facts.symbols[issue.symbol.index()].context != file.context
            {
                return Err(Error::Invalid("hierarchy diagnostic binary provenance"));
            }
        }
    }
    Ok(())
}

fn checked_range(range: IdRange, count: usize) -> Result<std::ops::Range<usize>, Error> {
    let end = range
        .start
        .checked_add(range.len)
        .ok_or(Error::Invalid("fact range overflow"))?;
    if end as usize > count {
        return Err(Error::Invalid("fact range bounds"));
    }
    Ok(range.start as usize..end as usize)
}

fn source_span(
    facts: &FactSnapshot,
    file: FileId,
    span: Span,
    kind: &'static str,
    index: usize,
) -> Result<(), Error> {
    if span.start > span.end {
        return Err(span_error(
            facts,
            file,
            span,
            kind,
            index,
            "start is after end",
        ));
    }
    if file.is_none() {
        return Ok(());
    }
    let record = &facts.files[file.index()];
    if record.flags & SOURCE_VERIFIED == 0 {
        return Ok(());
    }
    // File/source references and UTF-8 have already been checked above. This is
    // a direct byte slice, avoiding StringPool::get's repeated full UTF-8 scan.
    let entry = facts.strings.entries[record.source.index()];
    let source =
        &facts.strings.bytes[entry.start as usize..entry.start as usize + entry.len as usize];
    let start = span.start as usize;
    let end = span.end as usize;
    if end > source.len() {
        return Err(span_error(
            facts,
            file,
            span,
            kind,
            index,
            "outside verified source",
        ));
    }
    let boundary = |offset: usize| offset == source.len() || source[offset] & 0xc0 != 0x80;
    if !boundary(start) || !boundary(end) {
        return Err(span_error(
            facts,
            file,
            span,
            kind,
            index,
            "splits a UTF-8 code point",
        ));
    }
    Ok(())
}

#[cold]
#[inline(never)]
fn span_error(
    facts: &FactSnapshot,
    file: FileId,
    span: Span,
    kind: &str,
    index: usize,
    reason: &str,
) -> Error {
    let (path, source_bytes) = if file.is_none() {
        ("<external>", 0)
    } else {
        let record = &facts.files[file.index()];
        let source_bytes = if record.source.is_none() {
            0
        } else {
            facts.strings.entries[record.source.index()].len
        };
        (facts.text(record.path), source_bytes)
    };
    Error::Message(format!(
        "invalid {kind}[{index}] span in {path}: {}..{}, source_bytes={source_bytes}: {reason}",
        span.start, span.end
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn hierarchy_diagnostic_requires_same_context_nonempty_binary_provenance() {
        let mut b = FactBuilder::new();
        let path = b.intern("admitted.jar!/p/Child.class").unwrap();
        let context = b.intern("captured-context").unwrap();
        b.facts.files.push(FileRecord {
            path,
            source: StrId::NONE,
            revision: StrId::NONE,
            context,
            source_hash: ContentHash([1; 32]),
            flags: FILE_BINARY_SOURCE,
        });
        let symbol = b.ensure_symbol("p/Child#", FileId::NONE).unwrap();
        b.facts.symbols[symbol.index()].context = context;
        b.facts.issues.push(IssueRecord {
            kind: IssueKind::IncompleteHierarchy,
            symbol,
            file: FileId(0),
            detail: StrId::NONE,
        });
        let mut facts = b.finish().unwrap();
        let original_file = facts.files[0];
        let original_issue = facts.issues[0];
        for control in 0..5 {
            facts.files[0] = original_file;
            facts.issues[0] = original_issue;
            facts.symbols[symbol.index()].context = context;
            match control {
                0 => facts.issues[0].file = FileId::NONE,
                1 => facts.issues[0].symbol = SymbolId::NONE,
                2 => facts.files[0].flags = 0,
                3 => facts.files[0].source_hash = ContentHash::default(),
                4 => facts.symbols[symbol.index()].context = StrId::NONE,
                _ => unreachable!(),
            }
            assert!(facts.validate().is_err(), "control{control}");
        }
        assert_eq!(
            IssueKind::decode(12).unwrap(),
            IssueKind::IncompleteHierarchy
        );
        assert!(!IssueKind::IncompleteHierarchy.is_execution_boundary());
        for raw in 1..12 {
            assert!(IssueKind::decode(raw).unwrap().is_execution_boundary());
        }
    }
    fn fixture() -> FactSnapshot {
        let mut b = FactBuilder::new();
        let path = b.intern("Unicode.scala").unwrap();
        let source = b.intern("def café = \"😀\"").unwrap();
        b.facts.files.push(FileRecord {
            path,
            source,
            revision: StrId::NONE,
            context: StrId::NONE,
            source_hash: ContentHash::default(),
            flags: SOURCE_VERIFIED,
        });
        let symbol = b.ensure_symbol("pkg/café().", FileId(0)).unwrap();
        b.facts.symbols[0].file = FileId(0);
        b.facts.symbols[0].span = Span { start: 4, end: 9 };
        b.facts.occurrences.push(OccurrenceRecord {
            file: FileId(0),
            symbol,
            span: Span { start: 4, end: 9 },
            role: 2,
            ordinal: 0,
        });
        b.facts.bodies.push(BodyRecord {
            symbol,
            file: FileId(0),
            span: Span { start: 12, end: 18 },
            name_span: Span { start: 4, end: 9 },
            operations: IdRange { start: 0, len: 1 },
            parameters: IdRange { start: 0, len: 0 },
            body_hash: ContentHash::default(),
            flags: BODY_DEFERRED,
        });
        b.facts.operations.push(OperationRecord {
            body: BodyId(0),
            opcode: Opcode::Constant,
            target: SymbolId::NONE,
            dest: ValueId(0),
            a: ValueId::NONE,
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span { start: 13, end: 17 },
            flags: 0,
        });
        b.facts
    }
    #[test]
    fn unicode_byte_spans_and_name_before_body_are_valid() {
        validate(&fixture()).unwrap();
    }
    fn bound_fixture() -> FactSnapshot {
        let mut facts = fixture();
        for (name, kind) in [("pkg/Bound#", 13), ("pkg/Mixin#", 14)] {
            let id = StrId(facts.strings.entries.len() as u32);
            facts.strings.entries.push(TextRange {
                start: facts.strings.bytes.len() as u64,
                len: name.len() as u32,
            });
            facts.strings.bytes.extend_from_slice(name.as_bytes());
            facts.symbols.push(SymbolRecord {
                name: id,
                display: StrId::NONE,
                owner: SymbolId::NONE,
                file: FileId::NONE,
                context: StrId::NONE,
                kind,
                properties: 0,
                signature: StrId::NONE,
                span: Span::default(),
                flags: 0,
            });
        }
        facts.operations[0].target = SymbolId(0);
        facts.bound_classes = vec![SymbolId(1), SymbolId(2)];
        facts.result_bounds = vec![
            ResultBoundRecord {
                symbol: SymbolId(0),
                operation: OperationId(0),
                classes: IdRange { start: 0, len: 2 },
            },
            ResultBoundRecord {
                symbol: SymbolId(0),
                operation: OperationId::NONE,
                classes: IdRange { start: 0, len: 1 },
            },
        ];
        facts
    }
    #[test]
    fn result_bounds_validate_order_width_and_exact_operation_ownership() {
        validate(&bound_fixture()).unwrap();
        for corruption in 0..12 {
            let mut f = bound_fixture();
            match corruption {
                0 => f.result_bounds[0].symbol = SymbolId::NONE,
                1 => f.result_bounds[0].symbol = SymbolId(9),
                2 => f.result_bounds[0].operation = OperationId(1),
                3 => f.operations[0].target = SymbolId(1),
                4 => f.result_bounds[0].classes.len = 0,
                5 => f.result_bounds[0].classes.len = 65,
                6 => f.result_bounds[0].classes.start = u32::MAX,
                7 => f.bound_classes[0] = SymbolId::NONE,
                8 => f.bound_classes[1] = SymbolId(9),
                9 => f.bound_classes.swap(0, 1),
                10 => f.result_bounds.swap(0, 1),
                _ => f.result_bounds[1].operation = OperationId(0),
            }
            assert!(
                validate(&f).is_err(),
                "result bound corruption {corruption}"
            );
        }
    }
    #[test]
    fn result_bound_admission_does_not_claim_current_class_authority() {
        let mut f = bound_fixture();
        f.symbols[1].kind = 0;
        f.symbols[2].kind = 3;
        f.symbols[1].flags = 0;
        validate(&f).unwrap();
        assert_eq!(
            f.result_bound(SymbolId(0), OperationId(0)),
            Some(&[SymbolId(1), SymbolId(2)][..])
        );
        assert!(f.result_bound(SymbolId(1), OperationId::NONE).is_none());
        // The table is structurally intact. Query admission must discard this
        // semantic clause because its classes no longer have class authority.
    }
    #[test]
    fn maximum_sized_conjunction_admits_without_per_record_ownership() {
        let mut b = FactBuilder::new();
        let result = b.ensure_symbol("pkg/result().", FileId::NONE).unwrap();
        for i in 0..MAX_RESULT_BOUND_CLASSES {
            let class = b
                .ensure_symbol(&format!("pkg/Class{i}#"), FileId::NONE)
                .unwrap();
            b.facts.bound_classes.push(class);
        }
        b.facts.result_bounds.push(ResultBoundRecord {
            symbol: result,
            operation: OperationId::NONE,
            classes: IdRange {
                start: 0,
                len: MAX_RESULT_BOUND_CLASSES as u32,
            },
        });
        let f = b.finish().unwrap();
        assert_eq!(
            f.result_bound(result, OperationId::NONE).unwrap().len(),
            MAX_RESULT_BOUND_CLASSES
        );
    }
    #[test]
    fn rejects_source_bounds_and_split_codepoints_on_every_record_kind() {
        for kind in 0..5 {
            for bad in [
                Span { start: 8, end: 9 },
                Span { start: 0, end: 19 },
                Span { start: 9, end: 4 },
            ] {
                let mut f = fixture();
                match kind {
                    0 => f.symbols[0].span = bad,
                    1 => f.occurrences[0].span = bad,
                    2 => f.bodies[0].span = bad,
                    3 => f.bodies[0].name_span = bad,
                    _ => f.operations[0].span = bad,
                }
                assert!(validate(&f).is_err(), "kind {kind}, {bad:?}");
            }
        }
    }
    #[test]
    fn rejects_missing_paths_sources_and_body_owners() {
        for corruption in 0..7 {
            let mut f = fixture();
            match corruption {
                0 => f.files[0].path = StrId::NONE,
                1 => {
                    let empty = StrId(f.strings.entries.len() as u32);
                    f.strings.entries.push(TextRange { start: 0, len: 0 });
                    f.files[0].path = empty;
                }
                2 => f.files[0].source = StrId::NONE,
                3 => f.bodies[0].symbol = SymbolId::NONE,
                4 => f.bodies[0].file = FileId::NONE,
                5 => f.operations[0].body = BodyId::NONE,
                _ => f.symbols[0].owner = SymbolId(9),
            }
            assert!(validate(&f).is_err(), "corruption {corruption}");
        }
    }
    #[test]
    fn rejects_checked_range_overflows_and_both_ownership_directions() {
        for corruption in 0..5 {
            let mut f = fixture();
            match corruption {
                0 => {
                    f.bodies[0].operations = IdRange {
                        start: u32::MAX,
                        len: 2,
                    }
                }
                1 => {
                    f.bodies[0].parameters = IdRange {
                        start: u32::MAX,
                        len: 1,
                    }
                }
                2 => {
                    f.operations[0].arguments = IdRange {
                        start: u32::MAX,
                        len: 9,
                    }
                }
                3 => f.bodies[0].operations = IdRange::default(),
                _ => {
                    let mut extra = f.bodies[0];
                    extra.symbol = SymbolId(0);
                    f.bodies.push(extra);
                }
            }
            assert!(validate(&f).is_err(), "corruption {corruption}");
        }
    }
    #[test]
    fn rejects_pool_slice_splitting_utf8_and_arithmetic_overflow() {
        let mut f = fixture();
        f.strings.entries.push(TextRange {
            start: 1,
            len: u32::MAX,
        });
        assert!(validate(&f).is_err());
        let mut f = fixture();
        f.strings.entries.push(TextRange {
            start: u64::MAX,
            len: 1,
        });
        assert!(validate(&f).is_err());
        let mut f = fixture();
        let source = f.strings.entries[f.files[0].source.index()];
        f.strings.entries.push(TextRange {
            start: source.start + 8,
            len: 1,
        });
        assert!(validate(&f).is_err());
    }
    #[test]
    fn unavailable_source_preserves_ordered_unverifiable_spans() {
        let mut f = fixture();
        f.files[0].flags = 0;
        f.files[0].source = StrId::NONE;
        f.operations[0].span = Span {
            start: 100,
            end: 200,
        };
        validate(&f).unwrap();
    }
    #[test]
    fn syntax_cannot_claim_verification_without_verified_source() {
        let mut f = fixture();
        f.files[0].flags = SYNTAX_VERIFIED;
        assert!(validate(&f).is_err());
    }
    #[test]
    fn invalid_span_diagnostic_names_record_path_and_bounds() {
        let mut f = fixture();
        f.operations[0].span = Span { start: 18, end: 19 };
        let error = validate(&f).unwrap_err().to_string();
        for expected in [
            "operation[0]",
            "Unicode.scala",
            "18..19",
            "source_bytes=18",
            "outside verified source",
        ] {
            assert!(error.contains(expected), "{error}");
        }
    }
}
