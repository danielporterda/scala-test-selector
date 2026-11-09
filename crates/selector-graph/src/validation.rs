//! Canonical graph admission. Equal edge records remain distinct edge IDs.
use crate::*;

pub(crate) fn validate(graph: &ProgramGraph) -> Result<(), Error> {
    for count in [
        graph.nodes.len(),
        graph.edges.len(),
        graph.symbol_nodes.len(),
        graph.issues.len(),
        graph.diagnostics.len(),
    ] {
        if count > u32::MAX as usize {
            return Err(Error::Limit("graph identifier capacity"));
        }
    }
    let symbol_ok = |id: SymbolId| id.is_none() || id.index() < graph.symbol_nodes.len();
    for node in &graph.nodes {
        if node.symbol.is_none()
            || !symbol_ok(node.symbol)
            || graph.symbol_nodes[node.symbol.index()].is_none()
        {
            return Err(Error::Invalid("node symbol index"));
        }
    }
    for (symbol, node) in graph.symbol_nodes.iter().enumerate() {
        if !node.is_none()
            && graph
                .nodes
                .get(node.index())
                .is_none_or(|node| node.symbol.index() != symbol)
        {
            return Err(Error::Invalid("symbol node identity"));
        }
    }
    for edge in &graph.edges {
        if edge.source.index() >= graph.nodes.len() || edge.target.index() >= graph.nodes.len() {
            return Err(Error::Invalid("graph endpoints"));
        }
        if !symbol_ok(edge.receiver) {
            return Err(Error::Invalid("graph receiver symbol"));
        }
        if edge.flags & EDGE_DEFERRED_DISPATCH != 0
            && (edge.kind != EdgeKind::Guard
                || edge.flags != (EDGE_UNKNOWN | EDGE_DEFERRED_DISPATCH)
                || edge.operation.is_none()
                || edge.receiver.is_none())
        {
            return Err(Error::Invalid("deferred dispatch edge"));
        }
    }
    for issue in &graph.issues {
        if !issue.kind.is_execution_boundary() {
            return Err(Error::Invalid("metadata issue used as execution boundary"));
        }
        if (!issue.node.is_none() && issue.node.index() >= graph.nodes.len())
            || !symbol_ok(issue.symbol)
        {
            return Err(Error::Invalid("graph issue reference"));
        }
    }
    if graph.diagnostic_bytes.len() > u32::MAX as usize {
        return Err(Error::Limit("graph diagnostic text"));
    }
    let diagnostic_text = std::str::from_utf8(&graph.diagnostic_bytes)
        .map_err(|_| Error::Invalid("graph diagnostic UTF-8"))?;
    for diagnostic in &graph.diagnostics {
        if !diagnostic.kind.is_execution_boundary() {
            return Err(Error::Invalid("metadata issue used as runtime diagnostic"));
        }
        if (!diagnostic.node.is_none() && diagnostic.node.index() >= graph.nodes.len())
            || !symbol_ok(diagnostic.symbol)
        {
            return Err(Error::Invalid("graph diagnostic scope"));
        }
        if diagnostic.reason.len == 0 {
            return Err(Error::Invalid("empty graph diagnostic reason"));
        }
        for range in [diagnostic.reason, diagnostic.metadata_path] {
            let end = range
                .start
                .checked_add(range.len)
                .ok_or(Error::Invalid("graph diagnostic range overflow"))?
                as usize;
            if end > diagnostic_text.len()
                || !diagnostic_text.is_char_boundary(range.start as usize)
                || !diagnostic_text.is_char_boundary(end)
            {
                return Err(Error::Invalid("graph diagnostic text range"));
            }
        }
    }
    let offset_count = graph
        .nodes
        .len()
        .checked_add(1)
        .ok_or(Error::Invalid("graph index length overflow"))?;
    for (offsets, ids) in [
        (&graph.forward_offsets, &graph.forward_edges),
        (&graph.reverse_offsets, &graph.reverse_edges),
    ] {
        if offsets.len() != offset_count
            || offsets.first() != Some(&0)
            || offsets.last().copied() != Some(ids.len() as u64)
            || ids.len() != graph.edges.len()
        {
            return Err(Error::Invalid("graph index length"));
        }
        if offsets
            .windows(2)
            .any(|range| range[0] > range[1] || range[1] > ids.len() as u64)
        {
            return Err(Error::Invalid("graph index offset"));
        }
    }
    // One bounded admission scratch allocation, reused for the two permutations.
    // No per-edge allocation or retained auxiliary index is necessary.
    let words = graph
        .edges
        .len()
        .checked_add(63)
        .ok_or(Error::Limit("graph validation scratch"))?
        / 64;
    let mut seen = Vec::new();
    seen.try_reserve_exact(words)
        .map_err(|_| Error::Limit("graph validation scratch"))?;
    seen.resize(words, 0u64);
    for (offsets, ids, reverse) in [
        (&graph.forward_offsets, &graph.forward_edges, false),
        (&graph.reverse_offsets, &graph.reverse_edges, true),
    ] {
        seen.fill(0);
        for (node, range) in offsets.windows(2).enumerate() {
            for id in &ids[range[0] as usize..range[1] as usize] {
                let edge = graph
                    .edges
                    .get(id.index())
                    .ok_or(Error::Invalid("indexed edge"))?;
                if (if reverse { edge.target } else { edge.source }).index() != node {
                    return Err(Error::Invalid("index owner"));
                }
                let mask = 1u64 << (id.index() % 64);
                let word = &mut seen[id.index() / 64];
                if *word & mask != 0 {
                    return Err(Error::Invalid("duplicate indexed edge identifier"));
                }
                *word |= mask;
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn fixture() -> ProgramGraph {
        let mut g = ProgramGraph {
            nodes: vec![
                NodeRecord {
                    symbol: SymbolId(0),
                    file: FileId::NONE,
                    body: BodyId::NONE,
                    flags: 0,
                },
                NodeRecord {
                    symbol: SymbolId(2),
                    file: FileId::NONE,
                    body: BodyId::NONE,
                    flags: 0,
                },
            ],
            symbol_nodes: vec![NodeId(0), NodeId::NONE, NodeId(1)],
            ..Default::default()
        };
        let edge = EdgeRecord {
            source: NodeId(0),
            target: NodeId(1),
            kind: EdgeKind::Call,
            occurrence: OccurrenceId::NONE,
            operation: OperationId::NONE,
            receiver: SymbolId::NONE,
            flags: 0,
        };
        g.edges = vec![
            edge,
            edge,
            EdgeRecord {
                source: NodeId(1),
                target: NodeId(0),
                ..edge
            },
        ];
        g.index().unwrap();
        g
    }
    #[test]
    fn duplicate_records_and_cycles_have_distinct_index_ids() {
        let mut g = fixture();
        g.forward_edges.swap(0, 1);
        validate(&g).unwrap();
    }
    #[test]
    fn additional_bodies_keep_the_same_compiler_identity() {
        let mut g = fixture();
        g.nodes[0].body = BodyId(0);
        g.nodes.push(NodeRecord {
            symbol: SymbolId(0),
            file: FileId::NONE,
            body: BodyId(1),
            flags: 0,
        });
        g.edges.push(EdgeRecord {
            source: NodeId(0),
            target: NodeId(2),
            kind: EdgeKind::Initialize,
            occurrence: OccurrenceId::NONE,
            operation: OperationId::NONE,
            receiver: SymbolId::NONE,
            flags: 0,
        });
        g.index().unwrap();
        validate(&g).unwrap();
        assert_eq!(g.node_for_symbol(SymbolId(0)), Some(NodeId(0)));
    }
    #[test]
    fn rejects_duplicate_or_omitted_ids_in_either_index() {
        for reverse in [false, true] {
            let mut g = fixture();
            let ids = if reverse {
                &mut g.reverse_edges
            } else {
                &mut g.forward_edges
            };
            let second = if reverse { 2 } else { 1 };
            ids[second] = ids[second - 1];
            assert!(validate(&g).is_err());
        }
    }
    #[test]
    fn rejects_aliasing_different_symbols_and_unmapped_nodes() {
        for corruption in 0..5 {
            let mut g = fixture();
            match corruption {
                0 => g.symbol_nodes[1] = NodeId(0),
                1 => g.symbol_nodes[0] = NodeId::NONE,
                2 => g.nodes[1].symbol = SymbolId(0),
                3 => g.nodes[0].symbol = SymbolId::NONE,
                _ => g.symbol_nodes[0] = NodeId(99),
            }
            assert!(validate(&g).is_err());
        }
    }
    #[test]
    fn rejects_offsets_endpoints_receivers_and_issues() {
        for corruption in 0..7 {
            let mut g = fixture();
            match corruption {
                0 => g.forward_offsets[1] = u64::MAX,
                1 => g.reverse_offsets[0] = 1,
                2 => g.forward_edges[0] = EdgeId::NONE,
                3 => g.edges[0].target = NodeId::NONE,
                4 => g.edges[0].receiver = SymbolId(99),
                5 => g.reverse_offsets.pop().map(|_| ()).unwrap(),
                _ => g.issues.push(GraphIssue {
                    kind: IssueKind::InvalidInput,
                    node: NodeId(99),
                    file: FileId::NONE,
                    symbol: SymbolId::NONE,
                    detail: StrId::NONE,
                }),
            }
            assert!(validate(&g).is_err(), "corruption {corruption}");
        }
    }
    #[test]
    fn sealed_empty_graph_is_valid() {
        let mut g = ProgramGraph::default();
        g.index().unwrap();
        validate(&g).unwrap();
    }

    #[test]
    fn metadata_diagnostic_cannot_masquerade_as_runtime_graph_issue() {
        let mut g = fixture();
        g.issues.push(GraphIssue {
            kind: IssueKind::IncompleteHierarchy,
            node: NodeId(0),
            file: FileId::NONE,
            symbol: SymbolId(0),
            detail: StrId::NONE,
        });
        assert!(matches!(
            validate(&g),
            Err(Error::Invalid("metadata issue used as execution boundary"))
        ));
        g.issues[0].kind = IssueKind::MissingBinary;
        validate(&g).unwrap();
        g.diagnostic_bytes
            .extend_from_slice(b"ancestry unavailable");
        g.diagnostics.push(GraphDiagnostic {
            kind: IssueKind::IncompleteHierarchy,
            node: NodeId(0),
            file: FileId::NONE,
            symbol: SymbolId(0),
            reason: IdRange { start: 0, len: 20 },
            metadata_path: IdRange::default(),
        });
        assert!(matches!(
            validate(&g),
            Err(Error::Invalid("metadata issue used as runtime diagnostic"))
        ));
        for raw in 1..12 {
            let kind = IssueKind::decode(raw).unwrap();
            g.issues[0].kind = kind;
            g.diagnostics[0].kind = kind;
            validate(&g).unwrap();
        }
    }
}
