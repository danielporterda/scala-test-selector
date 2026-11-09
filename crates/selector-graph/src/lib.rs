//! Compact immutable program relationships; independent of graph construction.
pub mod codec;
mod validation;
use selector_types::*;

#[derive(Clone, Copy, Debug)]
pub struct NodeRecord {
    pub symbol: SymbolId,
    pub file: FileId,
    pub body: BodyId,
    pub flags: u32,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct EdgeRecord {
    pub source: NodeId,
    pub target: NodeId,
    pub kind: EdgeKind,
    pub occurrence: OccurrenceId,
    pub operation: OperationId,
    pub receiver: SymbolId,
    pub flags: u32,
}
#[derive(Clone, Copy, Debug)]
pub struct GraphIssue {
    pub kind: IssueKind,
    pub node: NodeId,
    pub file: FileId,
    pub symbol: SymbolId,
    pub detail: StrId,
}
/// Graph-owned model evidence. Text ranges refer only to diagnostic_bytes, never
/// to the immutable fact pool. Only diagnostics carry these fixed-size records.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GraphDiagnostic {
    pub kind: IssueKind,
    pub node: NodeId,
    pub file: FileId,
    pub symbol: SymbolId,
    pub reason: IdRange,
    pub metadata_path: IdRange,
}

#[derive(Debug, Default)]
pub struct ProgramGraph {
    pub identity: ContentHash,
    pub facts_identity: ContentHash,
    /// Exact admitted auxiliary runtime input identity; zero without explicit inputs.
    pub runtime_identity: ContentHash,
    pub nodes: Vec<NodeRecord>,
    pub edges: Vec<EdgeRecord>,
    pub forward_offsets: Vec<u64>,
    pub forward_edges: Vec<EdgeId>,
    pub reverse_offsets: Vec<u64>,
    pub reverse_edges: Vec<EdgeId>,
    pub symbol_nodes: Vec<NodeId>,
    pub issues: Vec<GraphIssue>,
    pub diagnostic_bytes: Vec<u8>,
    pub diagnostics: Vec<GraphDiagnostic>,
}
impl ProgramGraph {
    pub fn successors(&self, node: NodeId) -> impl Iterator<Item = (EdgeId, &EdgeRecord)> + '_ {
        let a = self.forward_offsets[node.index()] as usize;
        let b = self.forward_offsets[node.index() + 1] as usize;
        self.forward_edges[a..b]
            .iter()
            .map(|id| (*id, &self.edges[id.index()]))
    }
    pub fn predecessors(&self, node: NodeId) -> impl Iterator<Item = (EdgeId, &EdgeRecord)> + '_ {
        let a = self.reverse_offsets[node.index()] as usize;
        let b = self.reverse_offsets[node.index() + 1] as usize;
        self.reverse_edges[a..b]
            .iter()
            .map(|id| (*id, &self.edges[id.index()]))
    }
    pub fn node_for_symbol(&self, symbol: SymbolId) -> Option<NodeId> {
        self.symbol_nodes
            .get(symbol.index())
            .copied()
            .filter(|x| !x.is_none())
    }
    pub fn diagnostic_text(&self, range: IdRange) -> &str {
        std::str::from_utf8(&self.diagnostic_bytes[range.range()])
            .expect("validated graph diagnostic text")
    }
    pub fn index(&mut self) -> Result<(), Error> {
        let n = self.nodes.len();
        self.forward_offsets = vec![0; n + 1];
        self.reverse_offsets = vec![0; n + 1];
        for e in &self.edges {
            if e.source.index() >= n || e.target.index() >= n {
                return Err(Error::Invalid("edge endpoint"));
            }
            self.forward_offsets[e.source.index() + 1] += 1;
            self.reverse_offsets[e.target.index() + 1] += 1;
        }
        for i in 1..=n {
            self.forward_offsets[i] += self.forward_offsets[i - 1];
            self.reverse_offsets[i] += self.reverse_offsets[i - 1];
        }
        self.forward_edges.resize(self.edges.len(), EdgeId::NONE);
        self.reverse_edges.resize(self.edges.len(), EdgeId::NONE);
        let mut f = self.forward_offsets[..n].to_vec();
        let mut r = self.reverse_offsets[..n].to_vec();
        for (i, e) in self.edges.iter().enumerate() {
            let id = EdgeId::checked(i)?;
            self.forward_edges[f[e.source.index()] as usize] = id;
            f[e.source.index()] += 1;
            self.reverse_edges[r[e.target.index()] as usize] = id;
            r[e.target.index()] += 1;
        }
        Ok(())
    }
    pub fn validate(&self) -> Result<(), Error> {
        validation::validate(self)
    }
    pub fn owned_bytes(&self) -> usize {
        self.nodes.capacity() * std::mem::size_of::<NodeRecord>()
            + self.edges.capacity() * std::mem::size_of::<EdgeRecord>()
            + (self.forward_offsets.capacity() + self.reverse_offsets.capacity()) * 8
            + (self.forward_edges.capacity()
                + self.reverse_edges.capacity()
                + self.symbol_nodes.capacity())
                * 4
            + self.issues.capacity() * std::mem::size_of::<GraphIssue>()
            + self.diagnostic_bytes.capacity()
            + self.diagnostics.capacity() * std::mem::size_of::<GraphDiagnostic>()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn indexes_preserve_duplicate_edges_and_cycles() {
        let mut g = ProgramGraph::default();
        g.nodes = vec![
            NodeRecord {
                symbol: SymbolId(0),
                file: FileId::NONE,
                body: BodyId::NONE,
                flags: 0
            };
            2
        ];
        g.nodes[1].symbol = SymbolId(1);
        g.symbol_nodes = vec![NodeId(0), NodeId(1)];
        let e = EdgeRecord {
            source: NodeId(0),
            target: NodeId(1),
            kind: EdgeKind::Call,
            occurrence: OccurrenceId::NONE,
            operation: OperationId::NONE,
            receiver: SymbolId::NONE,
            flags: 0,
        };
        g.edges = vec![
            e,
            e,
            EdgeRecord {
                source: NodeId(1),
                target: NodeId(0),
                ..e
            },
        ];
        g.index().unwrap();
        g.validate().unwrap();
        assert_eq!(g.successors(NodeId(0)).count(), 2);
        assert_eq!(g.predecessors(NodeId(0)).count(), 1);
    }
}
