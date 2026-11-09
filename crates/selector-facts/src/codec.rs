//! Versioned little-endian fact persistence, independent of Rust record layout.
//!
//! Encoding uses one stack record at a time. Admission allocates one contiguous
//! vector per table and retains no artifact bytes after decoding completes.
use crate::*;
use selector_artifacts::{Artifact, ArtifactKind, StreamingSection};
use std::io::{self, Write};
use std::path::Path;

const VERSION: u32 = 2;
const META: u32 = 1;
const TEXT: u32 = 2;
const STRINGS: u32 = 3;
const FILES: u32 = 4;
const SYMBOLS: u32 = 5;
const OCCURRENCES: u32 = 6;
const RELATIONS: u32 = 7;
const BODIES: u32 = 8;
const OPERATIONS: u32 = 9;
const OPERANDS: u32 = 10;
const SUITES: u32 = 11;
const ISSUES: u32 = 12;
const RESULT_BOUNDS: u32 = 13;
const BOUND_CLASSES: u32 = 14;
const LAYOUT: [(u32, usize); 14] = [
    (META, 8),
    (TEXT, 1),
    (STRINGS, 12),
    (FILES, 52),
    (SYMBOLS, 48),
    (OCCURRENCES, 24),
    (RELATIONS, 16),
    (BODIES, 76),
    (OPERATIONS, 44),
    (OPERANDS, 4),
    (SUITES, 16),
    (ISSUES, 16),
    (RESULT_BOUNDS, 16),
    (BOUND_CLASSES, 4),
];

fn artifact_error(error: selector_artifacts::Error) -> Error {
    Error::Message(error.to_string())
}

fn section(id: u32, count: usize, width: usize) -> Result<StreamingSection, Error> {
    let length = count
        .checked_mul(width)
        .ok_or(Error::Limit("fact section bytes"))?;
    if id != TEXT && count >= u32::MAX as usize {
        return Err(Error::Limit("fact table identifiers"));
    }
    Ok(StreamingSection {
        id,
        count: count as u64,
        length: length as u64,
    })
}

/// Publish a complete immutable snapshot. The snapshot's old identity is ignored;
/// the returned digest identifies its canonical serialized content.
pub fn write(path: &Path, facts: &FactSnapshot) -> Result<ContentHash, Error> {
    facts.validate()?;
    let sections = [
        section(META, 1, 8)?,
        section(TEXT, facts.strings.bytes.len(), 1)?,
        section(STRINGS, facts.strings.entries.len(), 12)?,
        section(FILES, facts.files.len(), 52)?,
        section(SYMBOLS, facts.symbols.len(), 48)?,
        section(OCCURRENCES, facts.occurrences.len(), 24)?,
        section(RELATIONS, facts.relations.len(), 16)?,
        section(BODIES, facts.bodies.len(), 76)?,
        section(OPERATIONS, facts.operations.len(), 44)?,
        section(OPERANDS, facts.operands.len(), 4)?,
        section(SUITES, facts.suites.len(), 16)?,
        section(ISSUES, facts.issues.len(), 16)?,
        section(RESULT_BOUNDS, facts.result_bounds.len(), 16)?,
        section(BOUND_CLASSES, facts.bound_classes.len(), 4)?,
    ];
    let identity =
        selector_artifacts::write_streaming(path, ArtifactKind::Facts, &sections, |id, out| {
            match id {
                META => row::<8>(out, |r| {
                    r.u32(VERSION);
                    r.u32(facts.revision.0);
                })?,
                TEXT => out.write_all(&facts.strings.bytes)?,
                STRINGS => {
                    for value in &facts.strings.entries {
                        row::<12>(out, |r| {
                            r.u64(value.start);
                            r.u32(value.len);
                        })?;
                    }
                }
                FILES => {
                    for value in &facts.files {
                        row::<52>(out, |r| {
                            r.u32(value.path.0);
                            r.u32(value.source.0);
                            r.u32(value.revision.0);
                            r.u32(value.context.0);
                            r.bytes(&value.source_hash.0);
                            r.u32(value.flags);
                        })?;
                    }
                }
                SYMBOLS => {
                    for value in &facts.symbols {
                        row::<48>(out, |r| {
                            r.u32(value.name.0);
                            r.u32(value.display.0);
                            r.u32(value.owner.0);
                            r.u32(value.file.0);
                            r.u32(value.context.0);
                            r.u32(value.kind);
                            r.u64(value.properties);
                            r.u32(value.signature.0);
                            r.span(value.span);
                            r.u32(value.flags);
                        })?;
                    }
                }
                OCCURRENCES => {
                    for value in &facts.occurrences {
                        row::<24>(out, |r| {
                            r.u32(value.file.0);
                            r.u32(value.symbol.0);
                            r.span(value.span);
                            r.u32(value.role);
                            r.u32(value.ordinal);
                        })?;
                    }
                }
                RELATIONS => {
                    for value in &facts.relations {
                        row::<16>(out, |r| {
                            r.u32(value.source.0);
                            r.u32(value.target.0);
                            r.u32(value.kind as u32);
                            r.u32(value.file.0);
                        })?;
                    }
                }
                BODIES => {
                    for value in &facts.bodies {
                        row::<76>(out, |r| {
                            r.u32(value.symbol.0);
                            r.u32(value.file.0);
                            r.span(value.span);
                            r.span(value.name_span);
                            r.range(value.operations);
                            r.range(value.parameters);
                            r.bytes(&value.body_hash.0);
                            r.u32(value.flags);
                        })?;
                    }
                }
                OPERATIONS => {
                    for value in &facts.operations {
                        row::<44>(out, |r| {
                            r.u32(value.body.0);
                            r.u32(value.opcode as u32);
                            r.u32(value.target.0);
                            r.u32(value.dest.0);
                            r.u32(value.a.0);
                            r.u32(value.b.0);
                            r.range(value.arguments);
                            r.span(value.span);
                            r.u32(value.flags);
                        })?;
                    }
                }
                OPERANDS => {
                    for value in &facts.operands {
                        out.write_all(&value.0.to_le_bytes())?;
                    }
                }
                SUITES => {
                    for value in &facts.suites {
                        row::<16>(out, |r| {
                            r.u32(value.name.0);
                            r.u32(value.symbol.0);
                            r.u32(value.file.0);
                            r.u32(value.flags);
                        })?;
                    }
                }
                ISSUES => {
                    for value in &facts.issues {
                        row::<16>(out, |r| {
                            r.u32(value.kind as u32);
                            r.u32(value.file.0);
                            r.u32(value.symbol.0);
                            r.u32(value.detail.0);
                        })?;
                    }
                }
                RESULT_BOUNDS => {
                    for value in &facts.result_bounds {
                        row::<16>(out, |r| {
                            r.u32(value.symbol.0);
                            r.u32(value.operation.0);
                            r.range(value.classes);
                        })?;
                    }
                }
                BOUND_CLASSES => {
                    for value in &facts.bound_classes {
                        out.write_all(&value.0.to_le_bytes())?;
                    }
                }
                _ => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "unknown fact section",
                    ));
                }
            }
            Ok(())
        })
        .map_err(artifact_error)?;
    Ok(ContentHash(identity))
}

pub fn read(path: &Path) -> Result<FactSnapshot, Error> {
    let artifact = selector_artifacts::open(path, ArtifactKind::Facts).map_err(artifact_error)?;
    let (meta, _) = table(&artifact, META, 8)?;
    if meta.len() != 8 {
        return Err(Error::Invalid("fact metadata count"));
    }
    let mut meta = Cursor::new(meta);
    let version = meta.u32();
    let last_section = match version {
        1 => ISSUES,
        VERSION => BOUND_CLASSES,
        _ => return Err(Error::Invalid("fact schema version")),
    };
    if !artifact.section_ids().eq(META..=last_section) {
        return Err(Error::Invalid("fact section schema"));
    }
    // Reject a malformed trailing table before allocating/copying earlier ones.
    // Every width/count comes from the wire schema, never from a Rust layout.
    for (id, width) in LAYOUT.into_iter().take(last_section as usize) {
        table(&artifact, id, width)?;
    }
    let revision = StrId(meta.u32());
    let (text, text_count) = table(&artifact, TEXT, 1)?;
    let mut text_bytes = reserved(text_count)?;
    text_bytes.extend_from_slice(text);
    let facts = FactSnapshot {
        identity: ContentHash(artifact.identity()),
        revision,
        strings: StringPool {
            bytes: text_bytes,
            entries: decode(&artifact, STRINGS, 12, |r| {
                Ok(TextRange {
                    start: r.u64(),
                    len: r.u32(),
                })
            })?,
        },
        files: decode(&artifact, FILES, 52, |r| {
            Ok(FileRecord {
                path: StrId(r.u32()),
                source: StrId(r.u32()),
                revision: StrId(r.u32()),
                context: StrId(r.u32()),
                source_hash: ContentHash(r.hash()),
                flags: r.u32(),
            })
        })?,
        symbols: decode(&artifact, SYMBOLS, 48, |r| {
            Ok(SymbolRecord {
                name: StrId(r.u32()),
                display: StrId(r.u32()),
                owner: SymbolId(r.u32()),
                file: FileId(r.u32()),
                context: StrId(r.u32()),
                kind: r.u32(),
                properties: r.u64(),
                signature: StrId(r.u32()),
                span: r.span(),
                flags: r.u32(),
            })
        })?,
        occurrences: decode(&artifact, OCCURRENCES, 24, |r| {
            Ok(OccurrenceRecord {
                file: FileId(r.u32()),
                symbol: SymbolId(r.u32()),
                span: r.span(),
                role: r.u32(),
                ordinal: r.u32(),
            })
        })?,
        relations: decode(&artifact, RELATIONS, 16, |r| {
            Ok(RelationRecord {
                source: SymbolId(r.u32()),
                target: SymbolId(r.u32()),
                kind: RelationKind::decode(r.u32())?,
                file: FileId(r.u32()),
            })
        })?,
        bodies: decode(&artifact, BODIES, 76, |r| {
            Ok(BodyRecord {
                symbol: SymbolId(r.u32()),
                file: FileId(r.u32()),
                span: r.span(),
                name_span: r.span(),
                operations: r.range(),
                parameters: r.range(),
                body_hash: ContentHash(r.hash()),
                flags: r.u32(),
            })
        })?,
        operations: decode(&artifact, OPERATIONS, 44, |r| {
            Ok(OperationRecord {
                body: BodyId(r.u32()),
                opcode: Opcode::decode(r.u32())?,
                target: SymbolId(r.u32()),
                dest: ValueId(r.u32()),
                a: ValueId(r.u32()),
                b: ValueId(r.u32()),
                arguments: r.range(),
                span: r.span(),
                flags: r.u32(),
            })
        })?,
        operands: decode(&artifact, OPERANDS, 4, |r| Ok(ValueId(r.u32())))?,
        result_bounds: if version == 1 {
            Vec::new()
        } else {
            decode(&artifact, RESULT_BOUNDS, 16, |r| {
                Ok(ResultBoundRecord {
                    symbol: SymbolId(r.u32()),
                    operation: OperationId(r.u32()),
                    classes: r.range(),
                })
            })?
        },
        bound_classes: if version == 1 {
            Vec::new()
        } else {
            decode(&artifact, BOUND_CLASSES, 4, |r| Ok(SymbolId(r.u32())))?
        },
        suites: decode(&artifact, SUITES, 16, |r| {
            Ok(SuiteRecord {
                name: StrId(r.u32()),
                symbol: SymbolId(r.u32()),
                file: FileId(r.u32()),
                flags: r.u32(),
            })
        })?,
        issues: decode(&artifact, ISSUES, 16, |r| {
            Ok(IssueRecord {
                kind: IssueKind::decode(r.u32())?,
                file: FileId(r.u32()),
                symbol: SymbolId(r.u32()),
                detail: StrId(r.u32()),
            })
        })?,
    };
    facts.validate()?;
    // No builder interning indexes or artifact backing buffer survive this call.
    Ok(facts)
}

fn table(artifact: &Artifact, id: u32, width: usize) -> Result<(&[u8], usize), Error> {
    let bytes = artifact.section(id).map_err(artifact_error)?;
    let count = usize::try_from(artifact.count(id).map_err(artifact_error)?)
        .map_err(|_| Error::Invalid("fact count overflow"))?;
    if count.checked_mul(width) != Some(bytes.len()) || (id != TEXT && count >= u32::MAX as usize) {
        return Err(Error::Invalid("fact section count or width"));
    }
    Ok((bytes, count))
}
fn reserved<T>(count: usize) -> Result<Vec<T>, Error> {
    let mut values = Vec::new();
    values
        .try_reserve_exact(count)
        .map_err(|_| Error::Limit("fact admission allocation"))?;
    Ok(values)
}
fn decode<T>(
    artifact: &Artifact,
    id: u32,
    width: usize,
    mut read: impl FnMut(&mut Cursor<'_>) -> Result<T, Error>,
) -> Result<Vec<T>, Error> {
    let (bytes, count) = table(artifact, id, width)?;
    let mut values = reserved(count)?;
    for bytes in bytes.chunks_exact(width) {
        let mut cursor = Cursor::new(bytes);
        values.push(read(&mut cursor)?);
        debug_assert_eq!(cursor.offset, width);
    }
    Ok(values)
}
struct Cursor<'a> {
    bytes: &'a [u8],
    offset: usize,
}
impl<'a> Cursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }
    fn take<const N: usize>(&mut self) -> [u8; N] {
        let bytes = self.bytes[self.offset..self.offset + N].try_into().unwrap();
        self.offset += N;
        bytes
    }
    fn u32(&mut self) -> u32 {
        u32::from_le_bytes(self.take())
    }
    fn u64(&mut self) -> u64 {
        u64::from_le_bytes(self.take())
    }
    fn hash(&mut self) -> [u8; 32] {
        self.take()
    }
    fn span(&mut self) -> Span {
        Span {
            start: self.u32(),
            end: self.u32(),
        }
    }
    fn range(&mut self) -> IdRange {
        IdRange {
            start: self.u32(),
            len: self.u32(),
        }
    }
}
struct Row<const N: usize> {
    bytes: [u8; N],
    offset: usize,
}
impl<const N: usize> Row<N> {
    fn bytes(&mut self, value: &[u8]) {
        self.bytes[self.offset..self.offset + value.len()].copy_from_slice(value);
        self.offset += value.len();
    }
    fn u32(&mut self, value: u32) {
        self.bytes(&value.to_le_bytes());
    }
    fn u64(&mut self, value: u64) {
        self.bytes(&value.to_le_bytes());
    }
    fn span(&mut self, value: Span) {
        self.u32(value.start);
        self.u32(value.end);
    }
    fn range(&mut self, value: IdRange) {
        self.u32(value.start);
        self.u32(value.len);
    }
}
fn row<const N: usize>(out: &mut dyn Write, encode: impl FnOnce(&mut Row<N>)) -> io::Result<()> {
    let mut row = Row {
        bytes: [0; N],
        offset: 0,
    };
    encode(&mut row);
    debug_assert_eq!(row.offset, N);
    out.write_all(&row.bytes)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};
    static NEXT: AtomicU64 = AtomicU64::new(0);
    struct TestPath(std::path::PathBuf);
    impl TestPath {
        fn new() -> Self {
            Self(std::env::temp_dir().join(format!(
                "selector-facts-codec-{}-{}.rsel",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            )))
        }
    }
    impl Drop for TestPath {
        fn drop(&mut self) {
            let _ = std::fs::remove_file(&self.0);
        }
    }
    fn fixture() -> FactSnapshot {
        let mut b = FactBuilder::new();
        let source = b.intern("def run = work()").unwrap();
        let path = b.intern("src/Test.scala").unwrap();
        let revision = b.intern("abc123").unwrap();
        let context = b.intern("main").unwrap();
        let suite = b.intern("Suite").unwrap();
        b.facts.revision = revision;
        b.facts.files.push(FileRecord {
            path,
            source,
            revision,
            context,
            source_hash: ContentHash([7; 32]),
            flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
        });
        let first = b.ensure_symbol("pkg/run().", FileId(0)).unwrap();
        let second = b.ensure_symbol("pkg/work().", FileId(0)).unwrap();
        let class = b.ensure_symbol("pkg/Concrete#", FileId(0)).unwrap();
        let mixin = b.ensure_symbol("pkg/Mixin#", FileId(0)).unwrap();
        b.facts.symbols[class.index()].kind = 13;
        b.facts.symbols[mixin.index()].kind = 14;
        b.facts.symbols[0].file = FileId(0);
        b.facts.symbols[0].span = Span { start: 0, end: 15 };
        b.facts.symbols[0].properties = 1u64 << 40;
        b.facts.occurrences.push(OccurrenceRecord {
            file: FileId(0),
            symbol: second,
            span: Span { start: 10, end: 14 },
            role: 2,
            ordinal: 3,
        });
        b.facts.relations.push(RelationRecord {
            source: first,
            target: second,
            kind: RelationKind::Signature,
            file: FileId(0),
        });
        b.facts.bodies.push(BodyRecord {
            symbol: first,
            file: FileId(0),
            span: Span { start: 0, end: 15 },
            name_span: Span { start: 4, end: 7 },
            operations: IdRange { start: 0, len: 1 },
            parameters: IdRange { start: 0, len: 1 },
            body_hash: ContentHash([9; 32]),
            flags: BODY_DEFERRED,
        });
        b.facts.operands = vec![ValueId(0), ValueId(1)];
        b.facts.operations.push(OperationRecord {
            body: BodyId(0),
            opcode: Opcode::Call,
            target: second,
            dest: ValueId(2),
            a: ValueId(0),
            b: ValueId::NONE,
            arguments: IdRange { start: 1, len: 1 },
            span: Span { start: 10, end: 14 },
            flags: 4,
        });
        b.facts.bound_classes = vec![class, mixin, class];
        b.facts.result_bounds = vec![
            ResultBoundRecord {
                symbol: first,
                operation: OperationId::NONE,
                classes: IdRange { start: 0, len: 2 },
            },
            ResultBoundRecord {
                symbol: second,
                operation: OperationId(0),
                classes: IdRange { start: 2, len: 1 },
            },
            ResultBoundRecord {
                symbol: second,
                operation: OperationId::NONE,
                classes: IdRange { start: 0, len: 2 },
            },
        ];
        b.facts.suites.push(SuiteRecord {
            name: suite,
            symbol: first,
            file: FileId(0),
            flags: 5,
        });
        b.issue(
            IssueKind::UnsupportedModel,
            FileId(0),
            second,
            "dynamic boundary",
        )
        .unwrap();
        b.finish().unwrap()
    }
    #[test]
    fn typed_hierarchy_diagnostic_survives_persistence_and_changes_the_content_seal() {
        let mut b = FactBuilder::new();
        let path = b.intern("admitted.jar!/p/Child.class").unwrap();
        let context = b.intern("captured-context").unwrap();
        b.facts.files.push(FileRecord {
            path,
            source: StrId::NONE,
            revision: StrId::NONE,
            context,
            source_hash: ContentHash([7; 32]),
            flags: FILE_BINARY_SOURCE,
        });
        let symbol = b.ensure_symbol("p/Child#", FileId::NONE).unwrap();
        b.facts.symbols[symbol.index()].context = context;
        b.issue(
            IssueKind::IncompleteHierarchy,
            FileId(0),
            symbol,
            "Parent metadata is not admitted.",
        )
        .unwrap();
        let mut facts = b.finish().unwrap();
        let path = TestPath::new();
        let identity = write(&path.0, &facts).unwrap();
        let loaded = read(&path.0).unwrap();
        assert_eq!(loaded.identity, identity);
        assert_eq!(loaded.issues[0].kind, IssueKind::IncompleteHierarchy);
        assert_eq!(
            (loaded.issues[0].file, loaded.issues[0].symbol),
            (FileId(0), symbol)
        );
        assert_eq!(
            loaded.text(loaded.issues[0].detail),
            "Parent metadata is not admitted."
        );
        facts.issues[0].kind = IssueKind::MissingBinary;
        let changed_path = TestPath::new();
        assert_ne!(write(&changed_path.0, &facts).unwrap(), identity);
    }
    #[test]
    fn full_roundtrip_is_canonical_and_assigns_identity() {
        let path = TestPath::new();
        let facts = fixture();
        let identity = write(&path.0, &facts).unwrap();
        let loaded = read(&path.0).unwrap();
        assert_eq!(loaded.identity, identity);
        assert_ne!(identity, ContentHash::default());
        assert_eq!(loaded.text(loaded.revision), "abc123");
        assert_eq!(loaded.strings.bytes, facts.strings.bytes);
        assert_eq!(loaded.symbols[0].properties, 1u64 << 40);
        assert_eq!(loaded.operations[0].arguments, IdRange { start: 1, len: 1 });
        assert_eq!(loaded.operands, vec![ValueId(0), ValueId(1)]);
        assert_eq!(loaded.files[0].source_hash, ContentHash([7; 32]));
        assert_eq!(loaded.bodies[0].body_hash, ContentHash([9; 32]));
        assert_eq!(loaded.relations[0].kind, RelationKind::Signature);
        assert_eq!(loaded.occurrences[0].ordinal, 3);
        assert_eq!(loaded.suites[0].flags, 5);
        assert_eq!(loaded.issues[0].kind, IssueKind::UnsupportedModel);
        assert_eq!(loaded.result_bounds, facts.result_bounds);
        assert_eq!(loaded.bound_classes, facts.bound_classes);
        assert_eq!(
            loaded.result_bound(SymbolId(1), OperationId(0)),
            Some(&[SymbolId(2)][..])
        );
        assert_eq!(
            loaded.result_bound(SymbolId(1), OperationId::NONE),
            Some(&[SymbolId(2), SymbolId(3)][..])
        );
        assert!(
            loaded.result_bound(SymbolId(0), OperationId(0)).is_none(),
            "exact lookup must not silently fall back to declaration"
        );
        assert_eq!(write(&path.0, &loaded).unwrap(), identity);
    }
    #[test]
    fn rejects_count_enum_utf8_and_reference_corruption() {
        let original = TestPath::new();
        write(&original.0, &fixture()).unwrap();
        let artifact = selector_artifacts::open(&original.0, ArtifactKind::Facts).unwrap();
        for corruption in 0..5 {
            let path = TestPath::new();
            let mut bytes: Vec<_> = artifact
                .section_ids()
                .map(|id| {
                    (
                        id,
                        artifact.count(id).unwrap(),
                        artifact.section(id).unwrap().to_vec(),
                    )
                })
                .collect();
            match corruption {
                0 => {
                    bytes[(OPERATIONS - 1) as usize].2[4..8].copy_from_slice(&999u32.to_le_bytes())
                }
                1 => bytes[(TEXT - 1) as usize].2[0] = 0xff,
                2 => bytes[(SUITES - 1) as usize].2[4..8].copy_from_slice(&999u32.to_le_bytes()),
                3 => {
                    bytes[(BODIES - 1) as usize].2[24..28].copy_from_slice(&u32::MAX.to_le_bytes())
                }
                _ => bytes[(FILES - 1) as usize].1 += 1,
            }
            let sections: Vec<_> = bytes
                .iter()
                .map(|(id, count, bytes)| selector_artifacts::Section {
                    id: *id,
                    count: *count,
                    bytes,
                })
                .collect();
            selector_artifacts::write(&path.0, ArtifactKind::Facts, &sections).unwrap();
            assert!(read(&path.0).is_err(), "corruption {corruption}");
        }
    }
    #[test]
    fn empty_snapshot_roundtrips() {
        let path = TestPath::new();
        let facts = FactBuilder::new().finish().unwrap();
        write(&path.0, &facts).unwrap();
        assert!(read(&path.0).unwrap().symbols.is_empty());
    }
    #[test]
    fn rejects_unbounded_counts_unknown_missing_and_versioned_sections() {
        let original = TestPath::new();
        write(&original.0, &fixture()).unwrap();
        let artifact = selector_artifacts::open(&original.0, ArtifactKind::Facts).unwrap();
        for corruption in 0..18 {
            let path = TestPath::new();
            let mut bytes: Vec<_> = artifact
                .section_ids()
                .map(|id| {
                    (
                        id,
                        artifact.count(id).unwrap(),
                        artifact.section(id).unwrap().to_vec(),
                    )
                })
                .collect();
            match corruption {
                0..14 => bytes[corruption].1 = u64::MAX,
                14 => {
                    bytes[0].2[..4].copy_from_slice(&999u32.to_le_bytes());
                }
                15 => {
                    bytes.remove(5);
                }
                16 => {
                    bytes.push((99, 0, Vec::new()));
                }
                _ => {
                    bytes[0].1 = 0;
                    bytes[0].2.clear();
                }
            }
            let sections: Vec<_> = bytes
                .iter()
                .map(|(id, count, bytes)| selector_artifacts::Section {
                    id: *id,
                    count: *count,
                    bytes,
                })
                .collect();
            selector_artifacts::write(&path.0, ArtifactKind::Facts, &sections).unwrap();
            assert!(read(&path.0).is_err(), "corruption {corruption}");
        }
    }

    #[test]
    fn legacy_v1_keeps_original_identity_and_diagnostics_with_empty_bounds() {
        let current = TestPath::new();
        write(&current.0, &fixture()).unwrap();
        let artifact = selector_artifacts::open(&current.0, ArtifactKind::Facts).unwrap();
        let mut rows: Vec<_> = (META..=ISSUES)
            .map(|id| {
                (
                    id,
                    artifact.count(id).unwrap(),
                    artifact.section(id).unwrap().to_vec(),
                )
            })
            .collect();
        rows[0].2[..4].copy_from_slice(&1u32.to_le_bytes());
        let sections: Vec<_> = rows
            .iter()
            .map(|(id, count, bytes)| selector_artifacts::Section {
                id: *id,
                count: *count,
                bytes,
            })
            .collect();
        let path = TestPath::new();
        let identity = selector_artifacts::write(&path.0, ArtifactKind::Facts, &sections).unwrap();
        let loaded = read(&path.0).unwrap();
        assert_eq!(loaded.identity, ContentHash(identity));
        assert!(loaded.result_bounds.is_empty() && loaded.bound_classes.is_empty());
        assert_eq!(loaded.issues[0].kind, IssueKind::UnsupportedModel);
        assert_eq!(loaded.text(loaded.issues[0].detail), "dynamic boundary");
    }

    #[test]
    fn typed_bound_tables_are_sealed_and_malformed_wire_clauses_fail_closed() {
        let original = TestPath::new();
        let facts = fixture();
        let identity = write(&original.0, &facts).unwrap();
        let mut changed = fixture();
        changed.result_bounds[0].classes.len = 1;
        assert_ne!(identity, write(&TestPath::new().0, &changed).unwrap());
        let artifact = selector_artifacts::open(&original.0, ArtifactKind::Facts).unwrap();
        for corruption in 0..13 {
            let path = TestPath::new();
            let mut rows: Vec<_> = artifact
                .section_ids()
                .map(|id| {
                    (
                        id,
                        artifact.count(id).unwrap(),
                        artifact.section(id).unwrap().to_vec(),
                    )
                })
                .collect();
            match corruption {
                0 => rows[(RESULT_BOUNDS - 1) as usize].2[..4]
                    .copy_from_slice(&u32::MAX.to_le_bytes()),
                1 => rows[(RESULT_BOUNDS - 1) as usize].2[4..8]
                    .copy_from_slice(&(u32::MAX - 1).to_le_bytes()),
                2 => rows[(RESULT_BOUNDS - 1) as usize].2[8..12]
                    .copy_from_slice(&u32::MAX.to_le_bytes()),
                3 => rows[(RESULT_BOUNDS - 1) as usize].2[12..16]
                    .copy_from_slice(&0u32.to_le_bytes()),
                4 => rows[(RESULT_BOUNDS - 1) as usize].2[12..16]
                    .copy_from_slice(&65u32.to_le_bytes()),
                5 => rows[(BOUND_CLASSES - 1) as usize].2[..4]
                    .copy_from_slice(&u32::MAX.to_le_bytes()),
                6 => {
                    rows[(BOUND_CLASSES - 1) as usize].2[..4].copy_from_slice(&999u32.to_le_bytes())
                }
                7 => {
                    rows[(BOUND_CLASSES - 1) as usize].2[4..8].copy_from_slice(&2u32.to_le_bytes())
                }
                8 => rows[(RESULT_BOUNDS - 1) as usize].2[16..20]
                    .copy_from_slice(&0u32.to_le_bytes()),
                9 => rows[(RESULT_BOUNDS - 1) as usize].2[36..40]
                    .copy_from_slice(&0u32.to_le_bytes()),
                10 => {
                    rows[0].2[..4].copy_from_slice(&1u32.to_le_bytes());
                }
                11 => {
                    rows.pop();
                }
                _ => {
                    rows[(RESULT_BOUNDS - 1) as usize].1 += 1;
                }
            }
            let sections: Vec<_> = rows
                .iter()
                .map(|(id, count, bytes)| selector_artifacts::Section {
                    id: *id,
                    count: *count,
                    bytes,
                })
                .collect();
            selector_artifacts::write(&path.0, ArtifactKind::Facts, &sections).unwrap();
            assert!(
                read(&path.0).is_err(),
                "typed bound corruption {corruption}"
            );
        }
    }
}
