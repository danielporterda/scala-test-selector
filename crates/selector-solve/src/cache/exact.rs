//! Exact-snapshot admission without rebuilding whole-program rebase tables.
use super::*;

/// Public snapshots can be changed after loading. A cache identity field alone
/// therefore cannot authorize the numeric fast path. Seal every logical table,
/// with explicit lengths and field encodings, through one bounded SHA stream.
pub(super) fn content_seal(f: &FactSnapshot, g: &ProgramGraph) -> Key {
    struct Seal {
        hash: Sha256,
        buffer: [u8; 16_384],
        used: usize,
    }
    impl Seal {
        fn flush(&mut self) {
            self.hash.update(&self.buffer[..self.used]);
            self.used = 0;
        }
        fn bytes(&mut self, bytes: &[u8]) {
            if bytes.len() > self.buffer.len() {
                self.flush();
                self.hash.update(bytes);
                return;
            }
            if self.used + bytes.len() > self.buffer.len() {
                self.flush();
            }
            self.buffer[self.used..self.used + bytes.len()].copy_from_slice(bytes);
            self.used += bytes.len();
        }
        fn n(&mut self, n: u32) {
            self.bytes(&n.to_le_bytes());
        }
        fn q(&mut self, n: u64) {
            self.bytes(&n.to_le_bytes());
        }
        fn len(&mut self, n: usize) {
            self.q(n as u64);
        }
        fn span(&mut self, span: Span) {
            self.n(span.start);
            self.n(span.end);
        }
        fn range(&mut self, range: IdRange) {
            self.n(range.start);
            self.n(range.len);
        }
    }
    let mut w = Seal {
        hash: Sha256::new(),
        buffer: [0; 16_384],
        used: 0,
    };
    w.bytes(b"selector-exact-input-seal/v1");
    w.bytes(&f.identity.0);
    w.n(f.revision.0);
    w.len(f.strings.bytes.len());
    w.bytes(&f.strings.bytes);
    w.len(f.strings.entries.len());
    for r in &f.strings.entries {
        w.q(r.start);
        w.n(r.len);
    }
    w.len(f.files.len());
    for r in &f.files {
        for n in [r.path.0, r.source.0, r.revision.0, r.context.0] {
            w.n(n);
        }
        w.bytes(&r.source_hash.0);
        w.n(r.flags);
    }
    w.len(f.symbols.len());
    for r in &f.symbols {
        for n in [
            r.name.0,
            r.display.0,
            r.owner.0,
            r.file.0,
            r.context.0,
            r.kind,
        ] {
            w.n(n);
        }
        w.q(r.properties);
        w.n(r.signature.0);
        w.span(r.span);
        w.n(r.flags);
    }
    w.len(f.occurrences.len());
    for r in &f.occurrences {
        w.n(r.file.0);
        w.n(r.symbol.0);
        w.span(r.span);
        w.n(r.role);
        w.n(r.ordinal);
    }
    w.len(f.relations.len());
    for r in &f.relations {
        w.n(r.source.0);
        w.n(r.target.0);
        w.n(r.kind as u32);
        w.n(r.file.0);
    }
    w.len(f.bodies.len());
    for r in &f.bodies {
        w.n(r.symbol.0);
        w.n(r.file.0);
        w.span(r.span);
        w.span(r.name_span);
        w.range(r.operations);
        w.range(r.parameters);
        w.bytes(&r.body_hash.0);
        w.n(r.flags);
    }
    w.len(f.operations.len());
    for r in &f.operations {
        for n in [
            r.body.0,
            r.opcode as u32,
            r.target.0,
            r.dest.0,
            r.a.0,
            r.b.0,
        ] {
            w.n(n);
        }
        w.range(r.arguments);
        w.span(r.span);
        w.n(r.flags);
    }
    w.len(f.operands.len());
    for r in &f.operands {
        w.n(r.0);
    }
    w.len(f.suites.len());
    for r in &f.suites {
        w.n(r.name.0);
        w.n(r.symbol.0);
        w.n(r.file.0);
        w.n(r.flags);
    }
    w.len(f.issues.len());
    for r in &f.issues {
        w.n(r.kind as u32);
        w.n(r.file.0);
        w.n(r.symbol.0);
        w.n(r.detail.0);
    }
    w.len(f.result_bounds.len());
    for r in &f.result_bounds {
        w.n(r.symbol.0);
        w.n(r.operation.0);
        w.range(r.classes);
    }
    w.len(f.bound_classes.len());
    for class in &f.bound_classes {
        w.n(class.0);
    }
    w.bytes(&g.identity.0);
    w.bytes(&g.facts_identity.0);
    w.bytes(&g.runtime_identity.0);
    w.len(g.nodes.len());
    for r in &g.nodes {
        w.n(r.symbol.0);
        w.n(r.file.0);
        w.n(r.body.0);
        w.n(r.flags);
    }
    w.len(g.edges.len());
    for r in &g.edges {
        for n in [
            r.source.0,
            r.target.0,
            r.kind as u32,
            r.occurrence.0,
            r.operation.0,
            r.receiver.0,
            r.flags,
        ] {
            w.n(n);
        }
    }
    for values in [&g.forward_offsets, &g.reverse_offsets] {
        w.len(values.len());
        for n in values {
            w.q(*n);
        }
    }
    for values in [&g.forward_edges, &g.reverse_edges] {
        w.len(values.len());
        for n in values {
            w.n(n.0);
        }
    }
    w.len(g.symbol_nodes.len());
    for n in &g.symbol_nodes {
        w.n(n.0);
    }
    w.len(g.issues.len());
    for r in &g.issues {
        w.n(r.kind as u32);
        w.n(r.node.0);
        w.n(r.file.0);
        w.n(r.symbol.0);
        w.n(r.detail.0);
    }
    w.len(g.diagnostic_bytes.len());
    w.bytes(&g.diagnostic_bytes);
    w.len(g.diagnostics.len());
    for r in &g.diagnostics {
        w.n(r.kind as u32);
        w.n(r.node.0);
        w.n(r.file.0);
        w.n(r.symbol.0);
        w.range(r.reason);
        w.range(r.metadata_path);
    }
    w.flush();
    w.hash.finalize().into()
}

/// Stable/numeric pairs are still verified against the referenced records.
/// Only referenced identities are memoized; no whole-program string/key maps.
pub(super) struct ExactProgram<'a> {
    facts: &'a FactSnapshot,
    graph: &'a ProgramGraph,
    ordinals: Vec<u32>,
    body_nodes: Vec<NodeId>,
    local_files: Option<Vec<FileId>>,
    symbols: HashMap<SymbolId, Key>,
    nodes: HashMap<NodeId, Key>,
    ops: HashMap<OperationId, Key>,
    edges: HashMap<EdgeId, Key>,
}
impl<'a> ExactProgram<'a> {
    pub(super) fn new(facts: &'a FactSnapshot, graph: &'a ProgramGraph) -> Self {
        let mut ordinals = vec![0; graph.nodes.len()];
        let mut first = vec![u64::MAX; facts.symbols.len()];
        let mut repeats = HashMap::new();
        let mut body_nodes = vec![NodeId::NONE; facts.bodies.len()];
        for (i, node) in graph.nodes.iter().enumerate() {
            let flags = if node.body.is_none() {
                u32::MAX
            } else {
                facts.bodies[node.body.index()].flags
            };
            if first[node.symbol.index()] == u64::MAX {
                first[node.symbol.index()] = flags as u64;
            } else {
                let next = repeats.entry((node.symbol, flags)).or_insert(
                    if first[node.symbol.index()] == flags as u64 {
                        1
                    } else {
                        0
                    },
                );
                ordinals[i] = *next;
                *next += 1;
            }
            if !node.body.is_none() {
                body_nodes[node.body.index()] = NodeId(i as u32);
            }
        }
        Self {
            facts,
            graph,
            ordinals,
            body_nodes,
            local_files: None,
            symbols: HashMap::new(),
            nodes: HashMap::new(),
            ops: HashMap::new(),
            edges: HashMap::new(),
        }
    }
    pub(super) fn operation_count(&self) -> usize {
        self.facts.operations.len()
    }
    pub(super) fn owned_bytes(&self) -> usize {
        self.ordinals.capacity() * 4
            + self.body_nodes.capacity() * 4
            + self.local_files.as_ref().map_or(0, |v| v.capacity() * 4)
            + (self.symbols.capacity()
                + self.nodes.capacity()
                + self.ops.capacity()
                + self.edges.capacity())
                * 48
    }
    pub(super) fn symbol(&mut self, id: SymbolId) -> Result<Key, Error> {
        if id.is_none() {
            return Ok(ZERO);
        }
        if let Some(key) = self.symbols.get(&id) {
            return Ok(*key);
        }
        let symbol = *self
            .facts
            .symbols
            .get(id.index())
            .ok_or(Error::Invalid("exact cached symbol ID"))?;
        let mut file = symbol.file;
        if file.is_none() && selector_types::symbol::is_local(self.facts.symbol_name(id)) {
            let files = self.local_files.get_or_insert_with(|| {
                let mut files: Vec<_> = self.facts.symbols.iter().map(|s| s.file).collect();
                for o in &self.facts.occurrences {
                    if files[o.symbol.index()].is_none() {
                        files[o.symbol.index()] = o.file;
                    }
                }
                files
            });
            file = files[id.index()];
        }
        let key = sym_key(self.facts, id, file);
        self.symbols.insert(id, key);
        Ok(key)
    }
    pub(super) fn node(&mut self, id: NodeId) -> Result<Key, Error> {
        if let Some(key) = self.nodes.get(&id) {
            return Ok(*key);
        }
        let n = *self
            .graph
            .nodes
            .get(id.index())
            .ok_or(Error::Invalid("exact cached node ID"))?;
        let flags = if n.body.is_none() {
            u32::MAX
        } else {
            self.facts.bodies[n.body.index()].flags
        };
        let key = digest(&[
            b"program-node/v1",
            &self.symbol(n.symbol)?,
            &u(flags),
            &u(self.ordinals[id.index()]),
        ]);
        self.nodes.insert(id, key);
        Ok(key)
    }
    pub(super) fn operation(&mut self, id: OperationId) -> Result<Key, Error> {
        if id.is_none() {
            return Ok(ZERO);
        }
        if let Some(key) = self.ops.get(&id) {
            return Ok(*key);
        }
        let op = *self
            .facts
            .operations
            .get(id.index())
            .ok_or(Error::Invalid("exact cached operation ID"))?;
        let body = self.facts.bodies[op.body.index()];
        let node = self.body_nodes[op.body.index()];
        if node.is_none() {
            return Err(Error::Invalid("unowned exact cached operation"));
        }
        let key = digest(&[
            b"operation/v1",
            &self.node(node)?,
            &u(id.0 - body.operations.start),
        ]);
        self.ops.insert(id, key);
        Ok(key)
    }
    pub(super) fn edge(&mut self, id: EdgeId) -> Result<Key, Error> {
        if id.is_none() {
            return Ok(ZERO);
        }
        if let Some(key) = self.edges.get(&id) {
            return Ok(*key);
        }
        let e = *self
            .graph
            .edges
            .get(id.index())
            .ok_or(Error::Invalid("exact cached edge ID"))?;
        if !e.kind.is_execution() {
            return Err(Error::Invalid("compile edge in execution cache"));
        }
        let key = digest(&[
            b"edge/v1",
            &self.node(e.source)?,
            &self.node(e.target)?,
            &u(e.kind as u32),
            &self.operation(e.operation)?,
            &self.symbol(e.receiver)?,
            &u(e.flags),
        ]);
        self.edges.insert(id, key);
        Ok(key)
    }
}
