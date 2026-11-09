//! Explicit little-endian graph sections. No Rust layout or enum casts are read
//! from disk; worker-visible records are admitted into contiguous owned buffers.
use crate::*;
use selector_artifacts::{Artifact, ArtifactKind, StreamingSection};
use std::io::{self, Write};
use std::path::Path;

const VERSION: u32 = 3;
const META: u32 = 1;
const NODES: u32 = 2;
const EDGES: u32 = 3;
const FORWARD_OFFSETS: u32 = 4;
const FORWARD_EDGES: u32 = 5;
const REVERSE_OFFSETS: u32 = 6;
const REVERSE_EDGES: u32 = 7;
const SYMBOL_NODES: u32 = 8;
const ISSUES: u32 = 9;
const DIAGNOSTIC_TEXT: u32 = 10;
const DIAGNOSTICS: u32 = 11;
const LAYOUT: [(u32, usize); 11] = [
    (META, 68),
    (NODES, 16),
    (EDGES, 28),
    (FORWARD_OFFSETS, 8),
    (FORWARD_EDGES, 4),
    (REVERSE_OFFSETS, 8),
    (REVERSE_EDGES, 4),
    (SYMBOL_NODES, 4),
    (ISSUES, 20),
    (DIAGNOSTIC_TEXT, 1),
    (DIAGNOSTICS, 32),
];

fn artifact_error(error: selector_artifacts::Error) -> Error {
    Error::Message(error.to_string())
}
fn section(id: u32, count: usize, width: usize) -> Result<StreamingSection, Error> {
    let length = count
        .checked_mul(width)
        .ok_or(Error::Limit("graph section bytes"))?;
    if id != DIAGNOSTIC_TEXT && count >= u32::MAX as usize {
        return Err(Error::Limit("graph table identifiers"));
    }
    Ok(StreamingSection {
        id,
        count: count as u64,
        length: length as u64,
    })
}

/// Encode records through a stack buffer per record, with bounded streaming
/// publication. No full serialized copy of the graph is constructed.
pub fn write(path: &Path, graph: &ProgramGraph) -> Result<ContentHash, Error> {
    graph.validate()?;
    let sections = [
        section(META, 1, 68)?,
        section(NODES, graph.nodes.len(), 16)?,
        section(EDGES, graph.edges.len(), 28)?,
        section(FORWARD_OFFSETS, graph.forward_offsets.len(), 8)?,
        section(FORWARD_EDGES, graph.forward_edges.len(), 4)?,
        section(REVERSE_OFFSETS, graph.reverse_offsets.len(), 8)?,
        section(REVERSE_EDGES, graph.reverse_edges.len(), 4)?,
        section(SYMBOL_NODES, graph.symbol_nodes.len(), 4)?,
        section(ISSUES, graph.issues.len(), 20)?,
        section(DIAGNOSTIC_TEXT, graph.diagnostic_bytes.len(), 1)?,
        section(DIAGNOSTICS, graph.diagnostics.len(), 32)?,
    ];
    let identity =
        selector_artifacts::write_streaming(path, ArtifactKind::Graph, &sections, |id, out| {
            match id {
                META => row::<68>(out, |r| {
                    r.u32(VERSION);
                    r.bytes(&graph.facts_identity.0);
                    r.bytes(&graph.runtime_identity.0);
                })?,
                NODES => {
                    for value in &graph.nodes {
                        row::<16>(out, |r| {
                            r.u32(value.symbol.0);
                            r.u32(value.file.0);
                            r.u32(value.body.0);
                            r.u32(value.flags);
                        })?;
                    }
                }
                EDGES => {
                    for value in &graph.edges {
                        row::<28>(out, |r| {
                            r.u32(value.source.0);
                            r.u32(value.target.0);
                            r.u32(value.kind as u32);
                            r.u32(value.occurrence.0);
                            r.u32(value.operation.0);
                            r.u32(value.receiver.0);
                            r.u32(value.flags);
                        })?;
                    }
                }
                FORWARD_OFFSETS => {
                    for value in &graph.forward_offsets {
                        out.write_all(&value.to_le_bytes())?;
                    }
                }
                FORWARD_EDGES => {
                    for value in &graph.forward_edges {
                        out.write_all(&value.0.to_le_bytes())?;
                    }
                }
                REVERSE_OFFSETS => {
                    for value in &graph.reverse_offsets {
                        out.write_all(&value.to_le_bytes())?;
                    }
                }
                REVERSE_EDGES => {
                    for value in &graph.reverse_edges {
                        out.write_all(&value.0.to_le_bytes())?;
                    }
                }
                SYMBOL_NODES => {
                    for value in &graph.symbol_nodes {
                        out.write_all(&value.0.to_le_bytes())?;
                    }
                }
                ISSUES => {
                    for value in &graph.issues {
                        row::<20>(out, |r| {
                            r.u32(value.kind as u32);
                            r.u32(value.node.0);
                            r.u32(value.file.0);
                            r.u32(value.symbol.0);
                            r.u32(value.detail.0);
                        })?;
                    }
                }
                DIAGNOSTIC_TEXT => out.write_all(&graph.diagnostic_bytes)?,
                DIAGNOSTICS => {
                    for value in &graph.diagnostics {
                        row::<32>(out, |r| {
                            r.u32(value.kind as u32);
                            r.u32(value.node.0);
                            r.u32(value.file.0);
                            r.u32(value.symbol.0);
                            r.u32(value.reason.start);
                            r.u32(value.reason.len);
                            r.u32(value.metadata_path.start);
                            r.u32(value.metadata_path.len);
                        })?;
                    }
                }
                _ => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "unknown graph section",
                    ));
                }
            }
            Ok(())
        })
        .map_err(artifact_error)?;
    Ok(ContentHash(identity))
}

pub fn read(path: &Path) -> Result<ProgramGraph, Error> {
    read_with_binding(path, None)
}

fn read_with_binding(
    path: &Path,
    expected_facts: Option<ContentHash>,
) -> Result<ProgramGraph, Error> {
    let artifact = selector_artifacts::open(path, ArtifactKind::Graph).map_err(artifact_error)?;
    if !artifact.section_ids().eq(META..=DIAGNOSTICS) {
        return Err(Error::Invalid("graph section schema"));
    }
    for (id, width) in LAYOUT {
        table(&artifact, id, width)?;
    }
    let (meta, _) = table(&artifact, META, 68)?;
    if meta.len() != 68 {
        return Err(Error::Invalid("graph metadata count"));
    }
    let mut meta = Cursor::new(meta);
    if meta.u32() != VERSION {
        return Err(Error::Invalid("graph schema version"));
    }
    let facts_identity = ContentHash(meta.hash());
    let runtime_identity = ContentHash(meta.hash());
    if expected_facts.is_some_and(|expected| expected != facts_identity) {
        return Err(Error::Invalid("graph fact identity binding"));
    }
    let (text, count) = table(&artifact, DIAGNOSTIC_TEXT, 1)?;
    let mut diagnostic_bytes = reserved(count)?;
    diagnostic_bytes.extend_from_slice(text);
    let graph = ProgramGraph {
        identity: ContentHash(artifact.identity()),
        facts_identity,
        runtime_identity,
        nodes: decode(&artifact, NODES, 16, |r| {
            Ok(NodeRecord {
                symbol: SymbolId(r.u32()),
                file: FileId(r.u32()),
                body: BodyId(r.u32()),
                flags: r.u32(),
            })
        })?,
        edges: decode(&artifact, EDGES, 28, |r| {
            Ok(EdgeRecord {
                source: NodeId(r.u32()),
                target: NodeId(r.u32()),
                kind: EdgeKind::decode(r.u32())?,
                occurrence: OccurrenceId(r.u32()),
                operation: OperationId(r.u32()),
                receiver: SymbolId(r.u32()),
                flags: r.u32(),
            })
        })?,
        forward_offsets: decode(&artifact, FORWARD_OFFSETS, 8, |r| Ok(r.u64()))?,
        forward_edges: decode(&artifact, FORWARD_EDGES, 4, |r| Ok(EdgeId(r.u32())))?,
        reverse_offsets: decode(&artifact, REVERSE_OFFSETS, 8, |r| Ok(r.u64()))?,
        reverse_edges: decode(&artifact, REVERSE_EDGES, 4, |r| Ok(EdgeId(r.u32())))?,
        symbol_nodes: decode(&artifact, SYMBOL_NODES, 4, |r| Ok(NodeId(r.u32())))?,
        issues: decode(&artifact, ISSUES, 20, |r| {
            Ok(GraphIssue {
                kind: IssueKind::decode(r.u32())?,
                node: NodeId(r.u32()),
                file: FileId(r.u32()),
                symbol: SymbolId(r.u32()),
                detail: StrId(r.u32()),
            })
        })?,
        diagnostic_bytes,
        diagnostics: decode(&artifact, DIAGNOSTICS, 32, |r| {
            Ok(GraphDiagnostic {
                kind: IssueKind::decode(r.u32())?,
                node: NodeId(r.u32()),
                file: FileId(r.u32()),
                symbol: SymbolId(r.u32()),
                reason: IdRange {
                    start: r.u32(),
                    len: r.u32(),
                },
                metadata_path: IdRange {
                    start: r.u32(),
                    len: r.u32(),
                },
            })
        })?,
    };
    graph.validate()?;
    Ok(graph)
}

/// Admission bound to the exact source fact artifact. Further source-table bounds
/// are checked by the orchestrator holding the facts, without coupling this crate
/// to extraction or to the fact schema.
pub fn read_bound(path: &Path, expected_facts: ContentHash) -> Result<ProgramGraph, Error> {
    read_with_binding(path, Some(expected_facts))
}

fn table(artifact: &Artifact, id: u32, width: usize) -> Result<(&[u8], usize), Error> {
    let bytes = artifact.section(id).map_err(artifact_error)?;
    let count = usize::try_from(artifact.count(id).map_err(artifact_error)?)
        .map_err(|_| Error::Invalid("graph count overflow"))?;
    if count.checked_mul(width) != Some(bytes.len())
        || (id != DIAGNOSTIC_TEXT && count >= u32::MAX as usize)
    {
        return Err(Error::Invalid("graph section count or width"));
    }
    Ok((bytes, count))
}
fn reserved<T>(count: usize) -> Result<Vec<T>, Error> {
    let mut values = Vec::new();
    values
        .try_reserve_exact(count)
        .map_err(|_| Error::Limit("graph admission allocation"))?;
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
                "selector-graph-codec-{}-{}.rsel",
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
    fn fixture() -> ProgramGraph {
        let mut graph = ProgramGraph {
            facts_identity: ContentHash([3; 32]),
            runtime_identity: ContentHash([12; 32]),
            nodes: vec![
                NodeRecord {
                    symbol: SymbolId(0),
                    file: FileId(0),
                    body: BodyId(0),
                    flags: 4,
                },
                NodeRecord {
                    symbol: SymbolId(1),
                    file: FileId(0),
                    body: BodyId::NONE,
                    flags: 0,
                },
            ],
            symbol_nodes: vec![NodeId(0), NodeId(1), NodeId::NONE],
            ..Default::default()
        };
        let edge = EdgeRecord {
            source: NodeId(0),
            target: NodeId(1),
            kind: EdgeKind::Call,
            occurrence: OccurrenceId(0),
            operation: OperationId(1),
            receiver: SymbolId(0),
            flags: 7,
        };
        graph.edges = vec![
            edge,
            edge,
            EdgeRecord {
                source: NodeId(1),
                target: NodeId(0),
                kind: EdgeKind::Callback,
                ..edge
            },
        ];
        graph.issues.push(GraphIssue {
            kind: IssueKind::UnknownExecution,
            node: NodeId(1),
            file: FileId(0),
            symbol: SymbolId(1),
            detail: StrId(8),
        });
        let reason = "runtime_unknown";
        let path = "métadata.yaml";
        graph.diagnostic_bytes.extend_from_slice(reason.as_bytes());
        graph.diagnostic_bytes.extend_from_slice(path.as_bytes());
        graph.diagnostics.push(GraphDiagnostic {
            kind: IssueKind::UnknownExecution,
            node: NodeId(1),
            file: FileId(0),
            symbol: SymbolId(1),
            reason: IdRange {
                start: 0,
                len: reason.len() as u32,
            },
            metadata_path: IdRange {
                start: reason.len() as u32,
                len: path.len() as u32,
            },
        });
        graph.index().unwrap();
        graph
    }
    #[test]
    fn roundtrip_keeps_duplicate_records_cycles_and_identity() {
        let path = TestPath::new();
        let original = fixture();
        let identity = write(&path.0, &original).unwrap();
        let graph = read_bound(&path.0, original.facts_identity).unwrap();
        assert_eq!(graph.identity, identity);
        assert_eq!(graph.runtime_identity, ContentHash([12; 32]));
        assert_eq!(graph.edges, original.edges);
        assert_eq!(graph.forward_edges, vec![EdgeId(0), EdgeId(1), EdgeId(2)]);
        assert_eq!(graph.successors(NodeId(0)).count(), 2);
        assert_eq!(graph.predecessors(NodeId(0)).count(), 1);
        assert_eq!(graph.node_for_symbol(SymbolId(2)), None);
        assert_eq!(graph.nodes[0].body, BodyId(0));
        assert_eq!(graph.issues[0].kind, IssueKind::UnknownExecution);
        assert_eq!(graph.diagnostics, original.diagnostics);
        assert_eq!(graph.diagnostic_bytes, original.diagnostic_bytes);
        assert_eq!(
            graph.diagnostic_text(graph.diagnostics[0].reason),
            "runtime_unknown"
        );
        assert_eq!(
            graph.diagnostic_text(graph.diagnostics[0].metadata_path),
            "métadata.yaml"
        );
        assert_eq!(write(&path.0, &graph).unwrap(), identity);
        assert!(read_bound(&path.0, ContentHash([4; 32])).is_err());
    }
    #[test]
    fn rejects_self_consistent_artifacts_with_invalid_semantics() {
        let original = TestPath::new();
        write(&original.0, &fixture()).unwrap();
        let artifact = selector_artifacts::open(&original.0, ArtifactKind::Graph).unwrap();
        for corruption in 0..6 {
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
                0 => bytes[(EDGES - 1) as usize].2[8..12].copy_from_slice(&999u32.to_le_bytes()),
                1 => {
                    bytes[(FORWARD_EDGES - 1) as usize].2[4..8].copy_from_slice(&0u32.to_le_bytes())
                }
                2 => bytes[(FORWARD_OFFSETS - 1) as usize].2[8..16]
                    .copy_from_slice(&99u64.to_le_bytes()),
                3 => {
                    bytes[(SYMBOL_NODES - 1) as usize].2[0..4].copy_from_slice(&99u32.to_le_bytes())
                }
                4 => bytes[(ISSUES - 1) as usize].2[4..8].copy_from_slice(&99u32.to_le_bytes()),
                _ => bytes[(NODES - 1) as usize].1 += 1,
            }
            let sections: Vec<_> = bytes
                .iter()
                .map(|(id, count, bytes)| selector_artifacts::Section {
                    id: *id,
                    count: *count,
                    bytes,
                })
                .collect();
            selector_artifacts::write(&path.0, ArtifactKind::Graph, &sections).unwrap();
            assert!(read(&path.0).is_err(), "corruption {corruption}");
        }
    }
    #[test]
    fn empty_graph_roundtrips() {
        let path = TestPath::new();
        let mut graph = ProgramGraph::default();
        graph.index().unwrap();
        write(&path.0, &graph).unwrap();
        let loaded = read(&path.0).unwrap();
        assert!(loaded.nodes.is_empty());
        assert_eq!(loaded.runtime_identity, ContentHash::default());
    }
    #[test]
    fn auxiliary_runtime_binding_changes_persisted_content_identity() {
        let first = TestPath::new();
        let second = TestPath::new();
        let original = fixture();
        let mut changed = fixture();
        changed.runtime_identity = ContentHash([13; 32]);
        let first_id = write(&first.0, &original).unwrap();
        let second_id = write(&second.0, &changed).unwrap();
        assert_ne!(first_id, second_id);
        assert_eq!(
            read_bound(&first.0, original.facts_identity)
                .unwrap()
                .runtime_identity,
            original.runtime_identity
        );
        assert_eq!(
            read_bound(&second.0, changed.facts_identity)
                .unwrap()
                .runtime_identity,
            changed.runtime_identity
        );
    }
    #[test]
    fn rejects_unbounded_counts_unknown_missing_and_versioned_sections() {
        let original = TestPath::new();
        write(&original.0, &fixture()).unwrap();
        let artifact = selector_artifacts::open(&original.0, ArtifactKind::Graph).unwrap();
        for corruption in 0..LAYOUT.len() + 4 {
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
                index if index < LAYOUT.len() => bytes[index].1 = u64::MAX,
                index if index == LAYOUT.len() => {
                    bytes[0].2[..4].copy_from_slice(&999u32.to_le_bytes());
                }
                index if index == LAYOUT.len() + 1 => {
                    bytes.remove(5);
                }
                index if index == LAYOUT.len() + 2 => {
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
            selector_artifacts::write(&path.0, ArtifactKind::Graph, &sections).unwrap();
            assert!(read(&path.0).is_err(), "corruption {corruption}");
        }
    }
    #[test]
    fn rejects_malformed_diagnostic_records_even_with_valid_checksums() {
        let original = TestPath::new();
        write(&original.0, &fixture()).unwrap();
        let artifact = selector_artifacts::open(&original.0, ArtifactKind::Graph).unwrap();
        for corruption in 0..7 {
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
            let row = &mut bytes[(DIAGNOSTICS - 1) as usize].2;
            match corruption {
                0 => row[0..4].copy_from_slice(&999u32.to_le_bytes()),
                1 => row[4..8].copy_from_slice(&999u32.to_le_bytes()),
                2 => row[12..16].copy_from_slice(&999u32.to_le_bytes()),
                3 => {
                    row[16..20].copy_from_slice(&u32::MAX.to_le_bytes());
                    row[20..24].copy_from_slice(&2u32.to_le_bytes());
                }
                4 => row[20..24].copy_from_slice(&0u32.to_le_bytes()),
                5 => {
                    row[24..28].copy_from_slice(&17u32.to_le_bytes());
                    row[28..32].copy_from_slice(&0u32.to_le_bytes());
                }
                _ => bytes[(DIAGNOSTIC_TEXT - 1) as usize].2[0] = 0xff,
            }
            let sections: Vec<_> = bytes
                .iter()
                .map(|(id, count, bytes)| selector_artifacts::Section {
                    id: *id,
                    count: *count,
                    bytes,
                })
                .collect();
            selector_artifacts::write(&path.0, ArtifactKind::Graph, &sections).unwrap();
            assert!(read(&path.0).is_err(), "corruption {corruption}");
        }
    }
}
