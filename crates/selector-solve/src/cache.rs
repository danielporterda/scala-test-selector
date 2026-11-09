//! Completed fixed points are persisted as independent dependency families.
//!
//! A family joins call contexts and every reader/writer of a shared heap/capture
//! slot. Admission validates lowered recipes, outgoing relationships, negative
//! lookup scopes and global compiler/model shape before rebinding stable IDs.
//! A changed family is recomputed; unrelated complete families remain reusable.
//! We never subtract contributions from a previously joined mutable heap.
use super::*;
mod exact;
#[cfg(test)]
mod heap_tests;
use selector_artifacts::{ArtifactKind, Section};
use sha2::{Digest, Sha256};
use std::{
    fs,
    io::Write,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

type Key = [u8; 32];
const VERSION: u32 = 15;
const ZERO: Key = [0; 32];
static TEMP_ID: AtomicU64 = AtomicU64::new(0);
#[derive(Clone)]
pub(super) struct CacheConfig {
    pub directory: PathBuf,
    pub producer: ContentHash,
}
#[derive(Clone, Copy, Debug, Default)]
pub struct ReuseMetrics {
    pub loaded_families: u64,
    pub rejected_families: u64,
    pub loaded_contexts: u64,
    pub same_snapshot: bool,
}
/// One aggregate cache decision, forwarded to the observer without retaining
/// per-family events or any borrowed graph/query owners.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CacheAction {
    PreparingSchema,
    Grouping,
    Encoding,
    Publishing,
    Hit,
    Miss,
    Rejected,
    Written,
    WriteSkipped,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CacheReason {
    ExactSnapshot,
    IndependentFamilies,
    ReferenceAbsent,
    FormatVersion,
    ProducerMismatch,
    OptionsMismatch,
    GlobalShapeChanged,
    FamilyFingerprintChanged,
    NegativeLookupScopeChanged,
    ContextBudget,
    MemoryBudget,
    IncompleteFamily,
    NoContexts,
    AlreadyWarm,
    AmbiguousIdentity,
    CorruptArtifact,
    IoFailure,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CacheIdentity {
    pub producer: ContentHash,
    pub facts: ContentHash,
    pub graph: ContentHash,
    pub models: ContentHash,
    pub options: ContentHash,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CacheEvent {
    pub action: CacheAction,
    pub reason: CacheReason,
    pub identity: CacheIdentity,
    pub families: u64,
    pub contexts: u64,
    /// Zero when no immutable artifact was admitted/published.
    pub artifact: ContentHash,
}

pub(crate) fn continuation_content_seal(f: &FactSnapshot, g: &ProgramGraph) -> Key {
    exact::content_seal(f, g)
}
fn emit(
    s: &QuerySession<'_>,
    config: &CacheConfig,
    action: CacheAction,
    reason: CacheReason,
    families: u64,
    contexts: u64,
    artifact: Key,
) {
    s.emit_cache(CacheEvent {
        action,
        reason,
        identity: CacheIdentity {
            producer: config.producer,
            facts: s.facts.identity,
            graph: s.graph.identity,
            models: s.graph.runtime_identity,
            options: ContentHash(digest(&[
                b"summary-options/v8",
                &(s.options.max_set_members as u64).to_le_bytes(),
                &cache_policy_key(&s.options),
            ])),
        },
        families,
        contexts,
        artifact: ContentHash(artifact),
    });
}
fn negative_frontier(s: &QuerySession<'_>, seal: Key, saving: bool) -> Option<Key> {
    let roots = s.options.execution_roots.as_ref()?;
    let entries = roots
        .len()
        .checked_add(if saving { s.roots.len() } else { 0 })?;
    if entries.checked_mul(std::mem::size_of::<(u32, u32)>())?
        > s.options
            .memory_budget_bytes
            .saturating_sub(s.owned_bytes())
    {
        return None;
    }
    let mut expected: Vec<_> = roots
        .iter()
        .map(|root| (root.node.0, root.receiver.0))
        .collect();
    expected.sort_unstable();
    expected.dedup();
    if saving {
        if !s.pending_roots.is_empty() {
            return None;
        }
        let mut actual = Vec::with_capacity(s.roots.len());
        for id in &s.roots {
            let context = s.contexts[id.index()];
            if !s.frames.get(context.key.arguments).is_empty() {
                return None;
            }
            let receiver = if context.key.receiver == Value::TOP {
                SymbolId::NONE
            } else {
                let atoms = s.pool.members(context.key.receiver);
                if context.key.receiver.unknown != 0
                    || atoms.len() != 1
                    || atoms[0].kind != AtomKind::Object
                    || !atoms[0].site.is_none()
                    || atoms[0].binding != 0
                {
                    return None;
                }
                atoms[0].symbol
            };
            actual.push((context.key.node.0, receiver.0));
        }
        actual.sort_unstable();
        actual.dedup();
        if expected != actual {
            return None;
        }
    }
    let mut hash = Sha256::new();
    hash.update(b"sealed-negative-frontier/v2\0");
    // A negative absence can depend on any writer in the exact program. Bind
    // every logical table and the declared complete root frontier. Positive
    // families retain their independent, cross-snapshot admission path.
    hash.update(seal);
    hash.update((expected.len() as u64).to_le_bytes());
    for (node, receiver) in expected {
        hash.update(node.to_le_bytes());
        hash.update(receiver.to_le_bytes());
    }
    Some(hash.finalize().into())
}
fn error(e: selector_artifacts::Error) -> Error {
    Error::Message(e.to_string())
}
fn digest(parts: &[&[u8]]) -> Key {
    let mut h = Sha256::new();
    for p in parts {
        h.update((p.len() as u64).to_le_bytes());
        h.update(p);
    }
    h.finalize().into()
}
fn add(h: &mut Sha256, p: &[u8]) {
    h.update((p.len() as u64).to_le_bytes());
    h.update(p);
}
fn u(n: u32) -> [u8; 4] {
    n.to_le_bytes()
}
fn sym_key(f: &FactSnapshot, id: SymbolId, file: FileId) -> Key {
    if id.is_none() {
        return ZERO;
    }
    let s = f.symbols[id.index()];
    let local = f
        .text(s.name)
        .strip_prefix("local")
        .is_some_and(|s| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()));
    digest(&[
        b"compiler-symbol/v1",
        f.text(s.name).as_bytes(),
        f.text(s.context).as_bytes(),
        if local { f.path(file).as_bytes() } else { b"" },
    ])
}
struct Schema {
    symbols: Vec<Key>,
    symbol_map: HashMap<Key, SymbolId>,
    nodes: Vec<Key>,
    node_map: HashMap<Key, NodeId>,
    ops: Vec<Key>,
    body_nodes: Vec<NodeId>,
    op_map: HashMap<Key, OperationId>,
    edges: Vec<Key>,
    edge_slots: Vec<u32>,
    edge_map: HashMap<Key, EdgeId>,
    operation_count: usize,
    fingerprints: Vec<Key>,
    global: Key,
    execution_global: Key,
}
impl Schema {
    fn new(f: &FactSnapshot, g: &ProgramGraph, rebind: bool) -> Result<Self, Error> {
        let mut local_files: Vec<_> = f.symbols.iter().map(|s| s.file).collect();
        for occurrence in &f.occurrences {
            let id = occurrence.symbol;
            if local_files[id.index()].is_none() {
                local_files[id.index()] = occurrence.file;
            }
        }
        let mut symbols: Vec<_> = (0..f.symbols.len())
            .map(|i| sym_key(f, SymbolId(i as u32), local_files[i]))
            .collect();
        drop(local_files);
        let mut symbol_map = HashMap::with_capacity(f.symbols.len());
        for (i, key) in symbols.iter().enumerate() {
            if symbol_map.insert(*key, SymbolId(i as u32)).is_some() {
                return Err(Error::Invalid("ambiguous stable compiler identity"));
            }
        }
        // Encoding requires only forward identities. Retain reverse maps only
        // for admission/rebinding; no graph owner survives this cache operation.
        if !rebind {
            symbol_map = HashMap::new();
        }
        let mut ordinals = HashMap::new();
        let mut nodes = Vec::with_capacity(g.nodes.len());
        let mut node_map = HashMap::with_capacity(g.nodes.len());
        for (i, n) in g.nodes.iter().enumerate() {
            let flags = if n.body.is_none() {
                u32::MAX
            } else {
                f.bodies[n.body.index()].flags
            };
            let ordinal = ordinals.entry((n.symbol, flags)).or_insert(0u32);
            let key = digest(&[
                b"program-node/v1",
                &symbols[n.symbol.index()],
                &u(flags),
                &u(*ordinal),
            ]);
            *ordinal += 1;
            nodes.push(key);
            if node_map.insert(key, NodeId(i as u32)).is_some() {
                return Err(Error::Invalid("ambiguous stable node"));
            }
        }
        drop(ordinals);
        if !rebind {
            node_map = HashMap::new();
        }
        let mut body_nodes = if rebind {
            Vec::new()
        } else {
            vec![NodeId::NONE; f.bodies.len()]
        };
        let mut ops = vec![ZERO; f.operations.len()];
        let mut op_map = if rebind {
            HashMap::with_capacity(f.operations.len())
        } else {
            HashMap::new()
        };
        for (i, n) in g.nodes.iter().enumerate() {
            if n.body.is_none() {
                continue;
            }
            if !rebind {
                body_nodes[n.body.index()] = NodeId(i as u32);
            }
            for (ordinal, op) in f.bodies[n.body.index()].operations.range().enumerate() {
                let key = digest(&[b"operation/v1", &nodes[i], &u(ordinal as u32)]);
                ops[op] = key;
                if rebind {
                    op_map.insert(key, OperationId(op as u32));
                }
            }
        }
        let execution_edges = g.edges.iter().filter(|e| e.kind.is_execution()).count();
        let mut edges = Vec::with_capacity(execution_edges);
        let mut edge_slots = vec![u32::MAX; g.edges.len()];
        let mut edge_map = if rebind {
            HashMap::with_capacity(execution_edges)
        } else {
            HashMap::new()
        };
        for (i, e) in g.edges.iter().enumerate() {
            if !e.kind.is_execution() {
                continue;
            }
            let key = digest(&[
                b"edge/v1",
                &nodes[e.source.index()],
                &nodes[e.target.index()],
                &u(e.kind as u32),
                &if e.operation.is_none() {
                    ZERO
                } else {
                    ops[e.operation.index()]
                },
                &if e.receiver.is_none() {
                    ZERO
                } else {
                    symbols[e.receiver.index()]
                },
                &u(e.flags),
            ]);
            edge_slots[i] = edges.len() as u32;
            edges.push(key);
            if rebind {
                edge_map.entry(key).or_insert(EdgeId(i as u32));
            }
        }
        let global_issues = g
            .issues
            .iter()
            .filter(|i| i.node.is_none() && i.file.is_none())
            .count();
        let mut shapes = Vec::with_capacity(
            f.symbols.len()
                + f.relations.len()
                + f.suites.len()
                + global_issues
                + f.result_bounds
                    .iter()
                    .filter(|r| r.operation.is_none())
                    .count(),
        );
        for (i, s) in f.symbols.iter().enumerate() {
            shapes.push(digest(&[
                b"symbol-shape",
                &symbols[i],
                &u(s.kind),
                &s.properties.to_le_bytes(),
                f.text(s.signature).as_bytes(),
                &if s.owner.is_none() {
                    ZERO
                } else {
                    symbols[s.owner.index()]
                },
                &u(s.flags),
            ]));
        }
        let mut parent_ordinals = vec![0u32; f.symbols.len()];
        for r in &f.relations {
            let ordinal = if r.kind == RelationKind::Parent {
                let next = &mut parent_ordinals[r.source.index()];
                let ordinal = *next;
                *next += 1;
                ordinal
            } else {
                0
            };
            shapes.push(digest(&[
                b"relation",
                &symbols[r.source.index()],
                &symbols[r.target.index()],
                &u(r.kind as u32),
                &u(ordinal),
            ]));
        }
        drop(parent_ordinals);
        for suite in &f.suites {
            shapes.push(digest(&[
                b"suite",
                f.text(suite.name).as_bytes(),
                &if suite.symbol.is_none() {
                    ZERO
                } else {
                    symbols[suite.symbol.index()]
                },
                f.path(suite.file).as_bytes(),
                &u(suite.flags),
            ]));
        }
        let mut bound_keys = Vec::new();
        for bound in &f.result_bounds {
            if !bound.operation.is_none() {
                continue;
            }
            let mut h = Sha256::new();
            h.update(b"declared-result-bound/v1");
            h.update(symbols[bound.symbol.index()]);
            h.update(u(bound.classes.len));
            bound_keys.clear();
            bound_keys.extend(
                f.bound_classes[bound.classes.range()]
                    .iter()
                    .map(|class| symbols[class.index()]),
            );
            bound_keys.sort_unstable();
            for key in &bound_keys {
                h.update(key);
            }
            shapes.push(h.finalize().into());
        }
        for issue in &g.issues {
            if issue.node.is_none() && issue.file.is_none() {
                shapes.push(digest(&[
                    b"global-issue",
                    &u(issue.kind as u32),
                    f.text(issue.detail).as_bytes(),
                ]));
            }
        }
        shapes.sort_unstable();
        let mut global = Sha256::new();
        for shape in shapes {
            global.update(shape);
        }
        let global = global.finalize().into();
        let mut issue_scopes = Vec::with_capacity(g.issues.len());
        for issue in &g.issues {
            let scope = if !issue.node.is_none() {
                (0, issue.node.0)
            } else if !issue.file.is_none() {
                (1, issue.file.0)
            } else {
                continue;
            };
            let key = digest(&[
                b"scoped-issue/v1",
                &u(issue.kind as u32),
                f.text(issue.detail).as_bytes(),
            ]);
            issue_scopes.push((scope, key));
        }
        issue_scopes.sort_unstable();
        let mut scope_hashes = HashMap::new();
        let mut at = 0;
        while at < issue_scopes.len() {
            let scope = issue_scopes[at].0;
            let mut hash = Sha256::new();
            while at < issue_scopes.len() && issue_scopes[at].0 == scope {
                hash.update(issue_scopes[at].1);
                at += 1;
            }
            scope_hashes.insert(scope, Key::from(hash.finalize()));
        }
        drop(issue_scopes);
        let mut outgoing = Vec::new();
        let mut fingerprints = Vec::with_capacity(g.nodes.len());
        for (i, n) in g.nodes.iter().enumerate() {
            let mut h = Sha256::new();
            h.update(nodes[i]);
            h.update(u(n.flags));
            if !n.file.is_none() {
                let file = f.files[n.file.index()];
                h.update(u(file.flags));
                add(&mut h, f.path(n.file).as_bytes());
                add(&mut h, f.text(file.context).as_bytes());
            }
            if !n.body.is_none() {
                let b = f.bodies[n.body.index()];
                h.update(b.body_hash.0);
                h.update(u(b.flags));
                h.update(u(b.parameters.len));
                h.update(u(b.operations.len));
                for id in &f.operands[b.parameters.range()] {
                    h.update(u(id.0));
                }
                for (ordinal, op) in f.operations[b.operations.range()].iter().enumerate() {
                    h.update(u(op.opcode as u32));
                    h.update(if op.target.is_none() {
                        ZERO
                    } else {
                        symbols[op.target.index()]
                    });
                    for id in [op.dest, op.a, op.b] {
                        h.update(u(id.0));
                    }
                    h.update(u(op.flags));
                    h.update(u(op.arguments.len));
                    for id in &f.operands[op.arguments.range()] {
                        h.update(u(id.0));
                    }
                    let bound =
                        f.result_bound(op.target, OperationId(b.operations.start + ordinal as u32));
                    h.update(u(bound.map_or(0, |b| b.len() as u32)));
                    if let Some(bound) = bound {
                        bound_keys.clear();
                        bound_keys.extend(bound.iter().map(|class| symbols[class.index()]));
                        bound_keys.sort_unstable();
                        for key in &bound_keys {
                            h.update(key);
                        }
                    }
                }
            }
            outgoing.clear();
            outgoing.extend(
                g.successors(NodeId(i as u32))
                    .filter(|(_, e)| e.kind.is_execution())
                    .map(|(id, _)| edges[edge_slots[id.index()] as usize]),
            );
            outgoing.sort_unstable();
            h.update((outgoing.len() as u64).to_le_bytes());
            for edge in &outgoing {
                h.update(edge);
            }
            h.update(scope_hashes.get(&(0, i as u32)).copied().unwrap_or(ZERO));
            h.update(scope_hashes.get(&(1, n.file.0)).copied().unwrap_or(ZERO));
            fingerprints.push(h.finalize().into());
        }
        drop(scope_hashes);
        drop(outgoing);
        let mut execution: Vec<_> = nodes
            .iter()
            .copied()
            .zip(fingerprints.iter().copied())
            .collect();
        execution.sort_unstable();
        let mut all = Sha256::new();
        for (node, fingerprint) in execution {
            all.update(node);
            all.update(fingerprint);
        }
        let execution_global = all.finalize().into();
        // Decode has finished fingerprinting. Rebinding uses reverse tables,
        // so release these large temporary forward vectors before family import.
        if rebind {
            symbols = Vec::new();
            nodes = Vec::new();
            ops = Vec::new();
            edges = Vec::new();
            edge_slots = Vec::new();
        }
        Ok(Self {
            symbols,
            symbol_map,
            nodes,
            node_map,
            ops,
            body_nodes,
            op_map,
            edges,
            edge_slots,
            edge_map,
            operation_count: f.operations.len(),
            fingerprints,
            global,
            execution_global,
        })
    }
    fn owned_bytes(&self) -> usize {
        (self.symbols.capacity()
            + self.nodes.capacity()
            + self.ops.capacity()
            + self.edges.capacity()
            + self.fingerprints.capacity())
            * 32
            + (self.edge_slots.capacity() + self.body_nodes.capacity()) * 4
            + (self.symbol_map.capacity()
                + self.node_map.capacity()
                + self.op_map.capacity()
                + self.edge_map.capacity())
                * 48
    }
    fn edge(&self, id: EdgeId) -> Result<Key, Error> {
        let slot = self
            .edge_slots
            .get(id.index())
            .copied()
            .ok_or(Error::Invalid("cached execution edge"))?;
        self.edges
            .get(slot as usize)
            .copied()
            .ok_or(Error::Invalid("compile edge in execution cache"))
    }
    fn symbol(&self, id: SymbolId) -> Key {
        if id.is_none() {
            ZERO
        } else {
            self.symbols[id.index()]
        }
    }
    fn operation(&self, id: OperationId) -> Result<Key, Error> {
        if id.is_none() {
            return Ok(ZERO);
        }
        let key = *self
            .ops
            .get(id.index())
            .ok_or(Error::Invalid("cached operation"))?;
        if key == ZERO {
            return Err(Error::Invalid("unowned cached operation"));
        }
        Ok(key)
    }
    fn sym(&self, key: Key) -> Result<SymbolId, Error> {
        if key == ZERO {
            Ok(SymbolId::NONE)
        } else {
            self.symbol_map
                .get(&key)
                .copied()
                .ok_or(Error::Invalid("cached compiler symbol"))
        }
    }
    fn op(&self, key: Key) -> Result<OperationId, Error> {
        if key == ZERO {
            Ok(OperationId::NONE)
        } else {
            self.op_map
                .get(&key)
                .copied()
                .ok_or(Error::Invalid("cached operation identity"))
        }
    }
}
struct Writer(Vec<u8>);
impl Writer {
    fn n(&mut self, n: u32) {
        self.0.extend_from_slice(&n.to_le_bytes());
    }
    fn q(&mut self, n: u64) {
        self.0.extend_from_slice(&n.to_le_bytes());
    }
    fn key(&mut self, key: Key) {
        self.0.extend_from_slice(&key);
    }
    fn reference(&mut self, key: Key, id: u32) {
        self.key(key);
        self.n(id);
    }
    fn symbol(&mut self, schema: &Schema, id: SymbolId) {
        self.reference(schema.symbol(id), id.0);
    }
    fn operation(&mut self, schema: &Schema, id: OperationId) -> Result<(), Error> {
        self.reference(schema.operation(id)?, id.0);
        Ok(())
    }
    fn node(&mut self, schema: &Schema, id: NodeId) {
        self.reference(schema.nodes[id.index()], id.0);
    }
    fn edge(&mut self, schema: &Schema, id: EdgeId) -> Result<(), Error> {
        self.reference(if id.is_none() { ZERO } else { schema.edge(id)? }, id.0);
        Ok(())
    }
}
enum Admission<'a> {
    Rebase(Schema),
    Exact(exact::ExactProgram<'a>),
}
impl Admission<'_> {
    fn pair(r: &mut Reader<'_>) -> Result<(Key, u32), Error> {
        let key = r.key()?;
        let id = r.n()?;
        if (key == ZERO) != (id == u32::MAX) {
            return Err(Error::Invalid("cached numeric/key null mismatch"));
        }
        Ok((key, id))
    }
    fn symbol(&mut self, r: &mut Reader<'_>) -> Result<SymbolId, Error> {
        let (key, id) = Self::pair(r)?;
        match self {
            Self::Rebase(s) => s.sym(key),
            Self::Exact(s) => {
                if s.symbol(SymbolId(id))? != key {
                    return Err(Error::Invalid("exact cached symbol/key mismatch"));
                }
                Ok(SymbolId(id))
            }
        }
    }
    fn operation(&mut self, r: &mut Reader<'_>) -> Result<OperationId, Error> {
        let (key, id) = Self::pair(r)?;
        match self {
            Self::Rebase(s) => s.op(key),
            Self::Exact(s) => {
                if s.operation(OperationId(id))? != key {
                    return Err(Error::Invalid("exact cached operation/key mismatch"));
                }
                Ok(OperationId(id))
            }
        }
    }
    fn node(&mut self, r: &mut Reader<'_>) -> Result<NodeId, Error> {
        let (key, id) = Self::pair(r)?;
        if id == u32::MAX {
            return Err(Error::Invalid("cached required node"));
        }
        match self {
            Self::Rebase(s) => s
                .node_map
                .get(&key)
                .copied()
                .ok_or(Error::Invalid("cached node identity")),
            Self::Exact(s) => {
                if s.node(NodeId(id))? != key {
                    return Err(Error::Invalid("exact cached node/key mismatch"));
                }
                Ok(NodeId(id))
            }
        }
    }
    fn edge(&mut self, r: &mut Reader<'_>) -> Result<EdgeId, Error> {
        let (key, id) = Self::pair(r)?;
        match self {
            Self::Rebase(s) => {
                if key == ZERO {
                    Ok(EdgeId::NONE)
                } else {
                    s.edge_map
                        .get(&key)
                        .copied()
                        .ok_or(Error::Invalid("cached call edge"))
                }
            }
            Self::Exact(s) => {
                if s.edge(EdgeId(id))? != key {
                    return Err(Error::Invalid("exact cached edge/key mismatch"));
                }
                Ok(EdgeId(id))
            }
        }
    }
    fn manifest(&mut self, r: &mut Reader<'_>) -> Result<(NodeId, bool), Error> {
        let (key, id) = Self::pair(r)?;
        let fingerprint = r.key()?;
        Ok(match self {
            Self::Rebase(s) => match s.node_map.get(&key) {
                Some(id) => (*id, s.fingerprints[id.index()] == fingerprint),
                None => (NodeId::NONE, false),
            },
            Self::Exact(s) => {
                if s.node(NodeId(id))? != key {
                    return Err(Error::Invalid("exact manifest node/key mismatch"));
                }
                (NodeId(id), true)
            }
        })
    }
    fn negative_scope_valid(&self, key: Key, expected: Option<Key>) -> bool {
        key == ZERO || expected == Some(key)
    }
    fn operation_count(&self) -> usize {
        match self {
            Self::Exact(s) => s.operation_count(),
            Self::Rebase(s) => s.operation_count,
        }
    }
    fn owned_bytes(&self) -> usize {
        match self {
            Self::Exact(s) => s.owned_bytes(),
            Self::Rebase(s) => s.owned_bytes(),
        }
    }
}
struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}
impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, at: 0 }
    }
    fn take(&mut self, n: usize) -> Result<&'a [u8], Error> {
        let end = self
            .at
            .checked_add(n)
            .ok_or(Error::Invalid("cache offset"))?;
        let out = self
            .bytes
            .get(self.at..end)
            .ok_or(Error::Invalid("truncated summary cache"))?;
        self.at = end;
        Ok(out)
    }
    fn n(&mut self) -> Result<u32, Error> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
    }
    fn q(&mut self) -> Result<u64, Error> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }
    fn key(&mut self) -> Result<Key, Error> {
        Ok(self.take(32)?.try_into().unwrap())
    }
    fn count(&mut self, min: usize) -> Result<usize, Error> {
        let n = self.n()? as usize;
        if n > (self.bytes.len() - self.at) / min.max(1) {
            return Err(Error::Invalid("summary cache count"));
        }
        Ok(n)
    }
    fn done(&self) -> Result<(), Error> {
        if self.at == self.bytes.len() {
            Ok(())
        } else {
            Err(Error::Invalid("summary cache trailing bytes"))
        }
    }
}
struct Union(Vec<usize>);
impl Union {
    fn new(n: usize) -> Self {
        Self((0..n).collect())
    }
    fn root(&mut self, mut i: usize) -> usize {
        while self.0[i] != i {
            let next = self.0[i];
            self.0[i] = self.0[next];
            i = next;
        }
        i
    }
    fn join(&mut self, a: usize, b: usize) {
        let a = self.root(a);
        let b = self.root(b);
        if a != b {
            self.0[a.max(b)] = a.min(b);
        }
    }
}
fn family_groups(s: &QuerySession<'_>) -> (Vec<Vec<ContextId>>, HashMap<Slot, ContextId>) {
    let mut union = Union::new(s.contexts.len());
    for call in &s.calls {
        union.join(call.source.index(), call.target.index());
    }
    // Only actual contributors connect independent families. Shared negative
    // subscriptions do not manufacture a writer or couple unrelated readers.
    let mut owners = HashMap::new();
    for (query, slot) in &s.writes {
        if matches!(slot.kind, SlotKind::FieldAll | SlotKind::FieldMissing) {
            continue;
        }
        if let Some(previous) = owners.insert(*slot, *query) {
            union.join(query.index(), previous.index());
        }
    }
    let mut all_readers = HashMap::new();
    for (query, read) in s.dependencies.active_reads() {
        if read.slot.kind == SlotKind::FieldAll {
            all_readers
                .entry((read.slot.owner, read.slot.member))
                .or_insert(query);
        } else if let Some(previous) = owners.get(&read.slot) {
            union.join(query.index(), previous.index());
        }
    }
    let mut contributed_all = HashSet::new();
    for (query, slot) in &s.writes {
        let site = match slot.kind {
            SlotKind::FieldWildcard => Some(slot.owner),
            SlotKind::Field => s.heap_owners.key(slot.owner).map(|key| key.site.0),
            _ => None,
        };
        if let Some(site) = site {
            let key = (site, slot.member);
            if let Some(reader) = all_readers.get(&key) {
                union.join(query.index(), reader.index());
                contributed_all.insert(key);
            }
        }
    }
    for (query, read) in s.dependencies.active_reads() {
        let key = (read.slot.owner, read.slot.member);
        if read.slot.kind == SlotKind::FieldAll && contributed_all.contains(&key) {
            union.join(query.index(), all_readers[&key].index());
        }
    }
    // Values can carry a closure from a different root without an invocation.
    // Connect its creator before splitting the heap/capture publication scopes.
    for (i, c) in s.contexts.iter().enumerate() {
        for value in std::iter::once(c.key.receiver)
            .chain(s.frames.get(c.key.arguments).iter().copied())
            .chain(std::iter::once(c.value))
        {
            for atom in s.pool.members(value) {
                if atom.kind == AtomKind::Callback {
                    if let Some(owner) = owners.get(&Slot {
                        kind: SlotKind::Capture,
                        owner: atom.binding,
                        member: 0,
                    }) {
                        union.join(i, owner.index());
                    }
                }
            }
        }
    }
    for (slot, v) in &s.slots {
        if let Some(owner) = owners.get(slot) {
            for atom in s.pool.members(v.value) {
                if atom.kind == AtomKind::Callback {
                    if let Some(capture_owner) = owners.get(&Slot {
                        kind: SlotKind::Capture,
                        owner: atom.binding,
                        member: 0,
                    }) {
                        union.join(owner.index(), capture_owner.index());
                    }
                }
            }
        }
    }
    for (binding, c) in &s.captures {
        if let Some(owner) = owners.get(&Slot {
            kind: SlotKind::Capture,
            owner: *binding,
            member: 0,
        }) {
            for value in
                std::iter::once(c.receiver).chain(s.frames.get(c.arguments).iter().copied())
            {
                for atom in s.pool.members(value) {
                    if atom.kind == AtomKind::Callback {
                        if let Some(other) = owners.get(&Slot {
                            kind: SlotKind::Capture,
                            owner: atom.binding,
                            member: 0,
                        }) {
                            union.join(owner.index(), other.index());
                        }
                    }
                }
            }
        }
    }
    let mut groups = HashMap::<usize, Vec<ContextId>>::new();
    for i in 0..s.contexts.len() {
        groups
            .entry(union.root(i))
            .or_default()
            .push(ContextId(i as u32));
    }
    let mut groups: Vec<_> = groups.into_values().collect();
    groups.sort_unstable_by_key(|g| g[0]);
    (groups, owners)
}
fn value_id(value: Value, values: &mut Vec<Value>, index: &mut HashMap<Value, u32>) -> u32 {
    if let Some(id) = index.get(&value) {
        *id
    } else {
        let id = values.len() as u32;
        values.push(value);
        index.insert(value, id);
        id
    }
}
/// Family-local semantic constraints. Their producer/site is not serialized:
/// a representative may change without changing the exact class conjunction.
struct BoundClauses(Vec<Atom>);
impl BoundClauses {
    fn index(&self, s: &QuerySession<'_>, atom: Atom) -> Result<u32, Error> {
        let atom = s
            .types
            .canonical_bound_atom(s.facts, atom)
            .ok_or(Error::Invalid("cached bound atom authority"))?;
        self.0
            .binary_search(&atom)
            .map(|i| i as u32)
            .map_err(|_| Error::Invalid("cached bound clause table"))
    }
    fn atom(&self, id: u32) -> Result<Atom, Error> {
        self.0
            .get(id as usize)
            .copied()
            .ok_or(Error::Invalid("cached bound clause ID"))
    }
    fn encoded_bytes(&self, facts: &FactSnapshot) -> Result<usize, Error> {
        self.0.iter().try_fold(4usize, |sum, atom| {
            let classes = facts
                .result_bound(atom.symbol, atom.site)
                .ok_or(Error::Invalid("cached bound clause authority"))?;
            sum.checked_add(4)
                .and_then(|n| classes.len().checked_mul(36).and_then(|m| n.checked_add(m)))
                .ok_or(Error::Limit("cached bound clause bytes"))
        })
    }
    fn write(&self, w: &mut Writer, schema: &Schema, facts: &FactSnapshot) -> Result<(), Error> {
        w.n(self.0.len() as u32);
        for atom in &self.0 {
            let classes = facts
                .result_bound(atom.symbol, atom.site)
                .ok_or(Error::Invalid("cached bound clause authority"))?;
            w.n(classes.len() as u32);
            for class in classes {
                w.symbol(schema, *class);
            }
        }
        Ok(())
    }
    /// Admit every clause before publishing any family values or contexts.
    /// Absence of a validated current conjunction is a cache miss, never an
    /// invitation to reinterpret the old representative's new producer row.
    fn read(
        r: &mut Reader<'_>,
        schema: &mut Admission<'_>,
        facts: &FactSnapshot,
        types: &TypeIndex,
    ) -> Result<Option<Self>, Error> {
        let count = r.count(40)?;
        if count == 0 {
            return Ok(Some(Self(Vec::new())));
        }
        let mut atoms = Vec::new();
        atoms
            .try_reserve_exact(count)
            .map_err(|_| Error::Limit("cached bound clauses allocation"))?;
        let mut classes = Vec::with_capacity(MAX_RESULT_BOUND_CLASSES);
        for _ in 0..count {
            let n = r.count(36)?;
            if n == 0 || n > MAX_RESULT_BOUND_CLASSES {
                return Err(Error::Invalid("cached bound conjunction size"));
            }
            classes.clear();
            for _ in 0..n {
                let class = schema.symbol(r)?;
                if class.is_none() {
                    return Err(Error::Invalid("cached bound class"));
                }
                classes.push(class);
            }
            classes.sort_unstable();
            classes.dedup();
            if classes.len() != n {
                return Err(Error::Invalid("duplicate cached bound class"));
            }
            let Some(atom) = types.canonical_bound_for_classes(facts, &classes) else {
                return Ok(None);
            };
            atoms.push(atom);
        }
        Ok(Some(Self(atoms)))
    }
}
fn write_family_value(
    w: &mut Writer,
    schema: &Schema,
    pool: &ValuePool,
    value: Value,
    bounds: &BoundClauses,
    session: &QuerySession<'_>,
) -> Result<(), Error> {
    w.n(value.unknown);
    w.n(pool.members(value).len() as u32);
    for atom in pool.members(value) {
        if !matches!(atom.kind, AtomKind::Object | AtomKind::Container) && atom.binding != 0 {
            return Err(Error::Invalid("non-normalized capture family"));
        }
        w.n(atom_tag(atom.kind));
        if atom.kind == AtomKind::UpperBound {
            w.n(bounds.index(session, *atom)?);
            continue;
        }
        w.operation(schema, atom.site)?;
        w.symbol(schema, atom.symbol);
        if matches!(atom.kind, AtomKind::Object | AtomKind::Container) {
            w.symbol(schema, object_origin(atom.binding));
        }
    }
    Ok(())
}
fn read_family_value(
    r: &mut Reader<'_>,
    schema: &mut Admission<'_>,
    pool: &mut ValuePool,
    atoms: &mut Vec<Atom>,
    max_members: usize,
    bounds: &BoundClauses,
    facts: &FactSnapshot,
    types: &TypeIndex,
) -> Result<Value, Error> {
    let unknown = r.n()?;
    let count = r.count(8)?;
    if count > max_members {
        return Err(Error::Invalid("capture family set precision"));
    }
    atoms.clear();
    atoms
        .try_reserve(count)
        .map_err(|_| Error::Limit("cached family atoms"))?;
    for _ in 0..count {
        let kind = match r.n()? {
            1 => AtomKind::Object,
            2 => AtomKind::Callback,
            3 => AtomKind::UpperBound,
            4 => AtomKind::Container,
            _ => return Err(Error::Invalid("capture family atom kind")),
        };
        if kind == AtomKind::UpperBound {
            atoms.push(bounds.atom(r.n()?)?);
            continue;
        }
        let site = schema.operation(r)?;
        let symbol = schema.symbol(r)?;
        let binding = if matches!(kind, AtomKind::Object | AtomKind::Container) {
            origin_binding(schema.symbol(r)?)?
        } else {
            0
        };
        if (kind == AtomKind::Callback && site.is_none()) || symbol.is_none() {
            return Err(Error::Invalid("non-normalized capture family atom"));
        }
        if kind == AtomKind::Object {
            validate_cached_object(facts, types, site, symbol, binding)?;
        } else if kind == AtomKind::Container {
            validate_container_atom(
                facts,
                Atom {
                    kind,
                    site,
                    symbol,
                    binding,
                },
            )?;
        }
        atoms.push(Atom {
            kind,
            site,
            symbol,
            binding,
        });
    }
    atoms.sort_unstable();
    atoms.dedup();
    pool.intern(atoms, unknown)
}
fn validate_cached_object(
    facts: &FactSnapshot,
    types: &TypeIndex,
    site: OperationId,
    symbol: SymbolId,
    binding: u32,
) -> Result<(), Error> {
    if symbol.is_none()
        || symbol.index() >= facts.symbols.len()
        || (!site.is_none()
            && facts
                .operations
                .get(site.index())
                .is_none_or(|op| op.opcode != Opcode::Allocate))
        || (binding != 0 && object_origin(binding).index() >= facts.symbols.len())
        || (site.is_none() && binding != 0)
        || (!site.is_none() && types.global_module_owner(symbol) == Some(symbol))
    {
        return Err(Error::Invalid("cached object identity"));
    }
    Ok(())
}
fn object_origin(binding: u32) -> SymbolId {
    if binding == 0 {
        SymbolId::NONE
    } else {
        SymbolId(binding - 1)
    }
}
fn origin_binding(root: SymbolId) -> Result<u32, Error> {
    if root.is_none() {
        Ok(0)
    } else {
        root.0
            .checked_add(1)
            .ok_or(Error::Limit("cached object origin"))
    }
}
fn write_slot(
    w: &mut Writer,
    slot: Slot,
    schema: &Schema,
    contexts: &HashMap<ContextId, u32>,
    bindings: &HashMap<u32, u32>,
    heap: &HeapOwners,
) -> Result<(), Error> {
    w.n(slot.kind as u32);
    match slot.kind {
        SlotKind::Summary => {
            w.n(*contexts
                .get(&ContextId(slot.owner))
                .ok_or(Error::Invalid("cross-family summary"))?);
            w.n(slot.member);
        }
        SlotKind::Capture => {
            w.n(*bindings
                .get(&slot.owner)
                .ok_or(Error::Invalid("cross-family capture"))?);
            w.n(slot.member);
        }
        SlotKind::Field | SlotKind::FieldMissing => {
            if slot.owner == u32::MAX {
                w.n(0);
                w.reference(ZERO, u32::MAX);
            } else if let Some(key) = heap.key(slot.owner) {
                w.n(3);
                w.operation(schema, key.site)?;
                w.symbol(schema, key.root);
            } else if (slot.owner as usize) >= schema.operation_count && slot.owner < heap.base() {
                w.n(2);
                w.symbol(schema, SymbolId(slot.owner - schema.operation_count as u32));
            } else if slot.kind == SlotKind::FieldMissing
                && (slot.owner as usize) < schema.operation_count
            {
                w.n(1);
                w.operation(schema, OperationId(slot.owner))?;
            } else {
                return Err(Error::Invalid("cached field owner"));
            }
            w.symbol(schema, SymbolId(slot.member));
        }
        SlotKind::FieldWildcard | SlotKind::FieldAll => {
            w.operation(schema, OperationId(slot.owner))?;
            w.symbol(schema, SymbolId(slot.member));
        }
        SlotKind::StaticField => {
            w.symbol(schema, SymbolId(slot.owner));
            w.n(slot.member);
        }
        SlotKind::Body | SlotKind::Dispatch => {
            return Err(Error::Invalid("unsupported cache dependency scope"));
        }
    }
    Ok(())
}
fn read_slot(
    r: &mut Reader<'_>,
    schema: &mut Admission<'_>,
    contexts: &[ContextId],
    bindings: &[u32],
    heap: &mut HeapOwners,
) -> Result<Slot, Error> {
    let kind = r.n()?;
    Ok(match kind {
        x if x == SlotKind::Summary as u32 => Slot {
            kind: SlotKind::Summary,
            owner: contexts
                .get(r.n()? as usize)
                .ok_or(Error::Invalid("summary dependency context"))?
                .0,
            member: r.n()?,
        },
        x if x == SlotKind::Capture as u32 => Slot {
            kind: SlotKind::Capture,
            owner: *bindings
                .get(r.n()? as usize)
                .ok_or(Error::Invalid("capture dependency binding"))?,
            member: r.n()?,
        },
        x if x == SlotKind::Field as u32 || x == SlotKind::FieldMissing as u32 => {
            let kind = if x == SlotKind::Field as u32 {
                SlotKind::Field
            } else {
                SlotKind::FieldMissing
            };
            let owner = match r.n()? {
                0 => {
                    if Admission::pair(r)? != (ZERO, u32::MAX) {
                        return Err(Error::Invalid("unknown receiver field owner"));
                    }
                    u32::MAX
                }
                1 if kind == SlotKind::FieldMissing => {
                    let op = schema.operation(r)?;
                    if op.is_none() {
                        return Err(Error::Invalid("coarse missing field site"));
                    }
                    op.0
                }
                2 => {
                    let root = schema.symbol(r)?;
                    if root.is_none() {
                        return Err(Error::Invalid("root field owner"));
                    }
                    let owner = schema
                        .operation_count()
                        .checked_add(root.index())
                        .ok_or(Error::Limit("cached root field owner"))?;
                    if owner >= heap.base() as usize {
                        return Err(Error::Invalid("cached root field namespace"));
                    }
                    owner as u32
                }
                3 => {
                    let site = schema.operation(r)?;
                    let root = schema.symbol(r)?;
                    heap.intern(HeapOwnerKey { site, root })?
                }
                _ => return Err(Error::Invalid("field owner namespace")),
            };
            Slot {
                kind,
                owner,
                member: schema.symbol(r)?.0,
            }
        }
        x if x == SlotKind::FieldWildcard as u32 || x == SlotKind::FieldAll as u32 => {
            let site = schema.operation(r)?;
            let field = schema.symbol(r)?;
            if site.is_none() || field.is_none() {
                return Err(Error::Invalid("aggregate field identity"));
            }
            Slot {
                kind: if x == SlotKind::FieldWildcard as u32 {
                    SlotKind::FieldWildcard
                } else {
                    SlotKind::FieldAll
                },
                owner: site.0,
                member: field.0,
            }
        }
        x if x == SlotKind::StaticField as u32 => Slot {
            kind: SlotKind::StaticField,
            owner: schema.symbol(r)?.0,
            member: r.n()?,
        },
        _ => return Err(Error::Invalid("cache dependency kind")),
    })
}
struct Grouped<T> {
    rows: Vec<(usize, T)>,
    offsets: Vec<usize>,
}
impl<T> Grouped<T> {
    fn new(mut rows: Vec<(usize, T)>, groups: usize) -> Self {
        rows.sort_by_key(|(group, _)| *group);
        let mut offsets = vec![0usize; groups + 1];
        for (group, _) in &rows {
            offsets[group + 1] += 1;
        }
        for i in 1..offsets.len() {
            offsets[i] += offsets[i - 1];
        }
        Self { rows, offsets }
    }
    fn get(&self, group: usize) -> &[(usize, T)] {
        &self.rows[self.offsets[group]..self.offsets[group + 1]]
    }
    fn owned_bytes(&self) -> usize {
        self.rows.capacity() * std::mem::size_of::<(usize, T)>()
            + self.offsets.capacity() * std::mem::size_of::<usize>()
    }
}
struct EncodedFamilies {
    slots: Grouped<(Slot, SlotValue)>,
    captures: Grouped<(u32, Capture)>,
    calls: Grouped<usize>,
    reads: Grouped<(ContextId, Read)>,
    writes: Grouped<(ContextId, Slot)>,
    roots: Grouped<ContextId>,
    keys: HashMap<u32, ClosureFamily>,
    issues: Vec<(SymbolId, u32)>,
}
impl EncodedFamilies {
    fn owned_bytes(&self) -> usize {
        self.slots.owned_bytes()
            + self.captures.owned_bytes()
            + self.calls.owned_bytes()
            + self.reads.owned_bytes()
            + self.writes.owned_bytes()
            + self.roots.owned_bytes()
            + self.keys.capacity() * 40
            + self.issues.capacity() * 8
    }
    fn new(
        s: &QuerySession<'_>,
        groups: &[Vec<ContextId>],
        owners: &HashMap<Slot, ContextId>,
    ) -> Self {
        let mut family = vec![0usize; s.contexts.len()];
        for (i, group) in groups.iter().enumerate() {
            for id in group {
                family[id.index()] = i;
            }
        }
        let mut slots = Vec::new();
        for (slot, value) in &s.slots {
            if let Some(owner) = owners.get(slot) {
                slots.push((family[owner.index()], (*slot, *value)));
            }
        }
        // Writer-free finalized absence is a family-local certificate. Copy
        // its compact cell into each consumer family instead of joining those
        // families merely to store one absence. Unobserved ALL aggregates are
        // reconstructed from admitted real contributors, not persisted owners.
        for (query, read) in s.dependencies.active_reads() {
            if !owners.contains_key(&read.slot) {
                if let Some(value) = s.slots.get(&read.slot) {
                    slots.push((family[query.index()], (read.slot, *value)));
                }
            }
        }
        slots.sort_unstable_by_key(|(family, (slot, _))| (*family, *slot));
        slots.dedup_by_key(|(family, (slot, _))| (*family, *slot));
        let captures = s
            .captures
            .iter()
            .filter_map(|(binding, c)| {
                owners
                    .get(&Slot {
                        kind: SlotKind::Capture,
                        owner: *binding,
                        member: 0,
                    })
                    .map(|owner| (family[owner.index()], (*binding, *c)))
            })
            .collect();
        let calls = s
            .calls
            .iter()
            .enumerate()
            .map(|(i, c)| (family[c.source.index()], i))
            .collect();
        let reads = s
            .dependencies
            .active_reads()
            .map(|(id, r)| (family[id.index()], (id, r)))
            .collect();
        let writes = s
            .writes
            .iter()
            .map(|(id, slot)| (family[id.index()], (*id, *slot)))
            .collect();
        let roots = s.roots.iter().map(|id| (family[id.index()], *id)).collect();
        let keys = s
            .closure_families
            .iter()
            .map(|(key, binding)| (*binding, *key))
            .collect();
        let mut issues: Vec<_> = s.issues.iter().map(|i| (i.symbol, i.kind as u32)).collect();
        issues.sort_unstable();
        issues.dedup();
        let n = groups.len();
        Self {
            slots: Grouped::new(slots, n),
            captures: Grouped::new(captures, n),
            calls: Grouped::new(calls, n),
            reads: Grouped::new(reads, n),
            writes: Grouped::new(writes, n),
            roots: Grouped::new(roots, n),
            keys,
            issues,
        }
    }
}
fn encode_group(
    s: &QuerySession<'_>,
    schema: &Schema,
    group: &[ContextId],
    family_index: usize,
    families: &EncodedFamilies,
    writer_slots: &HashSet<Slot>,
    w: &mut Writer,
    resident_bytes: usize,
    negative_scope: Key,
) -> Result<bool, Error> {
    // Check preparation tables before allocating them. Values are canonical
    // pool entries; each can occur at most once in this family's value index.
    let auxiliary = table_bound(group.len(), 8)
        .saturating_add(table_bound(families.captures.get(family_index).len(), 8))
        .saturating_add(s.pool.len().saturating_mul(16))
        .saturating_add(table_bound(s.pool.len(), 12))
        .saturating_add(group.len().saturating_mul(8))
        .saturating_add(families.captures.get(family_index).len().saturating_mul(32))
        .saturating_add(families.slots.get(family_index).len().saturating_mul(32))
        .saturating_add(families.writes.get(family_index).len().saturating_mul(16));
    if resident_bytes
        .saturating_add(auxiliary)
        .saturating_add(w.0.capacity())
        > s.options.memory_budget_bytes
    {
        return Ok(false);
    }
    let contexts: HashMap<_, _> = group
        .iter()
        .enumerate()
        .map(|(i, id)| (*id, i as u32))
        .collect();
    let mut shapes: Vec<_> = group
        .iter()
        .map(|id| s.contexts[id.index()].callback_shape)
        .collect();
    shapes.sort_unstable();
    shapes.dedup();
    let shape_rows = shapes
        .iter()
        .map(|id| s.callback_shapes.get(*id).atoms.len())
        .fold(0usize, usize::saturating_add);
    let mut captures: Vec<_> = families
        .captures
        .get(family_index)
        .iter()
        .map(|(_, capture)| *capture)
        .collect();
    captures.sort_unstable_by_key(|(b, _)| *b);
    let bindings: HashMap<_, _> = captures
        .iter()
        .enumerate()
        .map(|(i, (b, _))| (*b, i as u32))
        .collect();
    let mut values = Vec::new();
    let mut value_index = HashMap::new();
    for id in group {
        let c = s.contexts[id.index()];
        value_id(c.key.receiver, &mut values, &mut value_index);
        value_id(c.value, &mut values, &mut value_index);
        for arg in s.frames.get(c.key.arguments) {
            value_id(*arg, &mut values, &mut value_index);
        }
    }
    let mut slots: Vec<_> = families
        .slots
        .get(family_index)
        .iter()
        .map(|(_, slot)| *slot)
        .collect();
    slots.sort_unstable_by_key(|(slot, _)| *slot);
    for (_, v) in &slots {
        value_id(v.value, &mut values, &mut value_index);
    }
    for (_, c) in &captures {
        value_id(c.receiver, &mut values, &mut value_index);
        for arg in s.frames.get(c.arguments) {
            value_id(*arg, &mut values, &mut value_index);
        }
    }
    let bound_values = || {
        values
            .iter()
            .copied()
            .chain(captures.iter().flat_map(|(binding, _)| {
                let key = families.keys[binding];
                std::iter::once(key.receiver).chain(s.frames.get(key.arguments).iter().copied())
            }))
    };
    let bound_count = bound_values()
        .map(|value| {
            s.pool
                .members(value)
                .iter()
                .filter(|atom| atom.kind == AtomKind::UpperBound)
                .count()
        })
        .fold(0usize, usize::saturating_add);
    let origin_rows = captures
        .iter()
        .map(|(binding, _)| s.pool.members(families.keys[binding].origins).len())
        .fold(0usize, usize::saturating_add);
    let prepared_bytes = contexts.capacity() * 16
        + captures.capacity() * 32
        + bindings.capacity() * 16
        + values.capacity() * 8
        + value_index.capacity() * 24
        + slots.capacity() * 32
        + shapes.capacity() * 4;
    if resident_bytes
        .saturating_add(prepared_bytes)
        .saturating_add(
            group
                .len()
                .saturating_add(shape_rows)
                .saturating_add(origin_rows)
                .saturating_mul(4),
        )
        .saturating_add(bound_count.saturating_mul(std::mem::size_of::<Atom>()))
        > s.options.memory_budget_bytes
    {
        return Ok(false);
    }
    let mut bound_atoms = Vec::new();
    bound_atoms
        .try_reserve_exact(bound_count)
        .map_err(|_| Error::Limit("cached bound clause preparation"))?;
    for value in bound_values() {
        for atom in s
            .pool
            .members(value)
            .iter()
            .filter(|atom| atom.kind == AtomKind::UpperBound)
        {
            bound_atoms.push(
                s.types
                    .canonical_bound_atom(s.facts, *atom)
                    .ok_or(Error::Invalid("cached bound atom authority"))?,
            );
        }
    }
    bound_atoms.sort_unstable();
    bound_atoms.dedup();
    let bounds = BoundClauses(bound_atoms);
    let mut manifest: Vec<_> = group
        .iter()
        .map(|id| s.contexts[id.index()].key.node)
        .collect();
    manifest
        .try_reserve_exact(shape_rows.saturating_add(origin_rows))
        .map_err(|_| Error::Limit("cached callback shape manifest"))?;
    for shape in &shapes {
        for atom in s.callback_shapes.get(*shape).atoms {
            if !atom.site.is_none() {
                let body = s
                    .facts
                    .operations
                    .get(atom.site.index())
                    .ok_or(Error::Invalid("cached callback shape operation"))?
                    .body;
                let node = *schema
                    .body_nodes
                    .get(body.index())
                    .filter(|node| !node.is_none())
                    .ok_or(Error::Invalid("unowned cached callback shape"))?;
                manifest.push(node);
            }
        }
    }
    for (binding, _) in &captures {
        let family = families.keys[binding];
        capture_origins::validate(s.facts, &s.pool, &s.frames, family)?;
        for atom in s.pool.members(family.origins) {
            let body = s.facts.operations[atom.site.index()].body;
            let node = *schema
                .body_nodes
                .get(body.index())
                .filter(|node| !node.is_none())
                .ok_or(Error::Invalid("unowned cached callback origin"))?;
            manifest.push(node);
        }
    }
    manifest.sort_unstable();
    manifest.dedup();
    let mut size = 72usize
        .saturating_add(manifest.len().saturating_mul(68))
        .saturating_add(bounds.encoded_bytes(s.facts)?)
        .saturating_add(4)
        .saturating_add(shapes.len().saturating_mul(8))
        .saturating_add(shape_rows.saturating_mul(76));
    for value in &values {
        size = size.saturating_add(8).saturating_add(
            s.pool
                .members(*value)
                .iter()
                .map(|atom| {
                    if atom.kind == AtomKind::UpperBound {
                        8usize
                    } else if matches!(atom.kind, AtomKind::Object | AtomKind::Container) {
                        112
                    } else {
                        80
                    }
                })
                .sum::<usize>(),
        );
    }
    for id in group {
        let c = s.contexts[id.index()];
        size = size
            .saturating_add(76)
            .saturating_add(s.frames.get(c.key.arguments).len().saturating_mul(4));
        if s.runtime_issue_sites.contains_key(id) {
            size = size.saturating_add(44);
        }
        if s.issue_contexts.contains(id) {
            let symbol = s.graph.nodes[c.key.node.index()].symbol;
            let a = families.issues.partition_point(|(s, _)| *s < symbol);
            let b = families.issues.partition_point(|(s, _)| *s <= symbol);
            size = size.saturating_add((b - a).saturating_mul(4));
        }
    }
    for (binding, c) in &captures {
        let family = families.keys[binding];
        size = size
            .saturating_add(64)
            .saturating_add(8 + s.pool.members(family.origins).len() * 76)
            .saturating_add(
                s.pool
                    .members(family.receiver)
                    .iter()
                    .map(|atom| {
                        if atom.kind == AtomKind::UpperBound {
                            8usize
                        } else if matches!(atom.kind, AtomKind::Object | AtomKind::Container) {
                            112
                        } else {
                            76
                        }
                    })
                    .sum::<usize>(),
            )
            .saturating_add(s.frames.get(c.arguments).len().saturating_mul(4));
        for value in s.frames.get(family.arguments) {
            size = size.saturating_add(8).saturating_add(
                s.pool
                    .members(*value)
                    .iter()
                    .map(|atom| {
                        if atom.kind == AtomKind::UpperBound {
                            8usize
                        } else if matches!(atom.kind, AtomKind::Object | AtomKind::Container) {
                            112
                        } else {
                            76
                        }
                    })
                    .sum::<usize>(),
            );
        }
    }
    size = size.saturating_add(families.calls.get(family_index).len().saturating_mul(88));
    let slot_size = |slot: Slot| -> usize {
        match slot.kind {
            SlotKind::Summary | SlotKind::Capture => 12,
            SlotKind::Field | SlotKind::FieldMissing => {
                if s.heap_owners.key(slot.owner).is_some() {
                    116
                } else {
                    80
                }
            }
            SlotKind::FieldAll | SlotKind::FieldWildcard => 76,
            SlotKind::StaticField => 44,
            SlotKind::Body | SlotKind::Dispatch => 0,
        }
    };
    for (slot, _) in &slots {
        size = size.saturating_add(slot_size(*slot) + 12);
    }
    for (_, (_, read)) in families.reads.get(family_index) {
        size = size.saturating_add(slot_size(read.slot) + 16);
    }
    for (_, (_, slot)) in families.writes.get(family_index) {
        size = size.saturating_add(slot_size(*slot) + 4);
    }
    size = size.saturating_add(families.roots.get(family_index).len().saturating_mul(4));
    let end = w.0.len().saturating_add(8).saturating_add(size);
    let local_bytes = contexts.capacity() * 16
        + captures.capacity() * 32
        + bindings.capacity() * 16
        + values.capacity() * 8
        + value_index.capacity() * 24
        + slots.capacity() * 32
        + manifest.capacity() * 4
        + shapes.capacity() * 4
        + bounds.0.capacity() * std::mem::size_of::<Atom>()
        + families.writes.get(family_index).len() * 16;
    if resident_bytes
        .saturating_add(local_bytes)
        .saturating_add(end.max(w.0.capacity()))
        > s.options.memory_budget_bytes
    {
        return Ok(false);
    }
    w.0.try_reserve_exact(end - w.0.len())
        .map_err(|_| Error::Limit("summary payload allocation"))?;
    w.q(size as u64);
    w.n(group.len() as u32);
    w.n(manifest.len() as u32);
    for node in manifest {
        w.node(schema, node);
        w.key(schema.fingerprints[node.index()]);
    }
    // A sealed missing field was conservatively promoted to unknown. Reusing
    // that approximation after an unrelated new writer would retain a stale
    // unknown (joins cannot retract it). Bind such negative scopes to the full
    // execution recipe epoch; ordinary positive scopes remain family-local.
    let sealed_absence = slots
        .iter()
        .any(|(slot, v)| v.value.unknown & UNKNOWN_FIELD != 0 && !writer_slots.contains(slot));
    w.key(if sealed_absence { negative_scope } else { ZERO });
    bounds.write(w, schema, s.facts)?;
    w.n(captures.len() as u32);
    w.n(values.len() as u32);
    for value in &values {
        w.n(value.unknown);
        w.n(s.pool.members(*value).len() as u32);
        for atom in s.pool.members(*value) {
            w.n(atom_tag(atom.kind));
            if atom.kind == AtomKind::UpperBound {
                w.n(bounds.index(s, *atom)?);
                continue;
            }
            w.operation(schema, atom.site)?;
            w.symbol(schema, atom.symbol);
            if matches!(atom.kind, AtomKind::Object | AtomKind::Container) {
                w.symbol(schema, object_origin(atom.binding));
            } else {
                w.n(*bindings
                    .get(&atom.binding)
                    .ok_or(Error::Invalid("cross-family closure value"))?);
            }
        }
    }
    w.n(shapes.len() as u32);
    for id in &shapes {
        let shape = s.callback_shapes.get(*id);
        w.n(shape.arity);
        w.n(shape.atoms.len() as u32);
        for atom in shape.atoms {
            w.n(atom.argument);
            w.operation(schema, atom.site)?;
            w.symbol(schema, atom.symbol);
        }
    }
    w.n(group.len() as u32);
    for id in group {
        let c = s.contexts[id.index()];
        w.node(schema, c.key.node);
        w.n(value_index[&c.key.receiver]);
        w.n(value_index[&c.value]);
        w.q(c.version);
        w.n(u32::from(c.widened));
        w.n(u32::from(c.effects_open));
        w.n(shapes
            .binary_search(&c.callback_shape)
            .map_err(|_| Error::Invalid("cached context callback shape"))? as u32);
        let args = s.frames.get(c.key.arguments);
        w.n(args.len() as u32);
        for arg in args {
            w.n(value_index[arg]);
        }
        if s.issue_contexts.contains(id) {
            let symbol = s.graph.nodes[c.key.node.index()].symbol;
            let a = families.issues.partition_point(|(s, _)| *s < symbol);
            let b = families.issues.partition_point(|(s, _)| *s <= symbol);
            w.n((b - a) as u32);
            for (_, kind) in &families.issues[a..b] {
                w.n(*kind);
            }
        } else {
            w.n(0);
        }
        if let Some(site) = s.runtime_issue_sites.get(id) {
            s.validate_runtime_issue_site(c.key.node, *site)?;
            if !s.issue_contexts.contains(id) {
                return Err(Error::Invalid("cached runtime issue context"));
            }
            w.n(1);
            w.n(site.kind as u32);
            w.operation(schema, site.operation)?;
            w.n(site.reason as u32);
        } else {
            w.n(0);
        }
    }
    for (binding, c) in &captures {
        let family = families.keys[binding];
        w.operation(schema, family.site)?;
        write_family_value(w, schema, &s.pool, family.receiver, &bounds, s)?;
        let family_args = s.frames.get(family.arguments);
        w.n(family_args.len() as u32);
        for value in family_args {
            write_family_value(w, schema, &s.pool, *value, &bounds, s)?;
        }
        write_family_value(w, schema, &s.pool, family.origins, &bounds, s)?;
        w.n(value_index[&c.receiver]);
        w.q(c.version);
        let args = s.frames.get(c.arguments);
        w.n(args.len() as u32);
        for arg in args {
            w.n(value_index[arg]);
        }
    }
    let calls = families.calls.get(family_index);
    w.n(calls.len() as u32);
    for (_, index) in calls {
        let c = &s.calls[*index];
        w.n(contexts[&c.source]);
        w.n(contexts[&c.target]);
        w.operation(schema, c.operation)?;
        w.n(c.kind as u32);
        w.edge(schema, c.edge)?;
        w.n(if c.binding == u32::MAX {
            u32::MAX
        } else {
            bindings[&c.binding]
        });
    }
    w.n(slots.len() as u32);
    for (slot, v) in slots {
        write_slot(w, slot, schema, &contexts, &bindings, &s.heap_owners)?;
        w.n(value_index[&v.value]);
        w.q(v.version);
    }
    let reads = families.reads.get(family_index);
    w.n(reads.len() as u32);
    for (_, (id, read)) in reads {
        w.n(contexts[id]);
        write_slot(w, read.slot, schema, &contexts, &bindings, &s.heap_owners)?;
        w.q(read.version);
        w.n(u32::from(read.present));
    }
    let mut writes: Vec<_> = families
        .writes
        .get(family_index)
        .iter()
        .map(|(_, value)| *value)
        .collect();
    writes.sort_unstable();
    w.n(writes.len() as u32);
    for (id, slot) in writes {
        w.n(contexts[&id]);
        write_slot(w, slot, schema, &contexts, &bindings, &s.heap_owners)?;
    }
    let roots = families.roots.get(family_index);
    w.n(roots.len() as u32);
    for (_, root) in roots {
        w.n(contexts[root]);
    }
    if w.0.len() != end {
        return Err(Error::Invalid("summary payload size"));
    }
    Ok(true)
}
fn decode_group(
    s: &mut QuerySession<'_>,
    schema: &mut Admission<'_>,
    bytes: &[u8],
    resident_bytes: usize,
    rejection: &mut CacheReason,
    expected_negative_scope: Option<Key>,
) -> Result<bool, Error> {
    let mut r = Reader::new(bytes);
    let declared_contexts = r.n()? as usize;
    if declared_contexts > s.options.max_contexts.saturating_sub(s.contexts.len()) {
        *rejection = CacheReason::ContextBudget;
        return Ok(false);
    }
    let allowance = s
        .options
        .memory_budget_bytes
        .saturating_sub(s.owned_bytes())
        .saturating_sub(schema.owned_bytes())
        .saturating_sub(resident_bytes);
    let predicted = declared_contexts
        .saturating_mul(256)
        .saturating_add(bytes.len().saturating_mul(4));
    if predicted > allowance {
        *rejection = CacheReason::MemoryBudget;
        return Ok(false);
    }
    let count = r.count(68)?;
    let mut valid = true;
    let mut manifest_bodies = Vec::new();
    manifest_bodies
        .try_reserve_exact(count)
        .map_err(|_| Error::Limit("cached manifest bodies"))?;
    for _ in 0..count {
        let (node, matches) = schema.manifest(&mut r)?;
        valid &= matches;
        if matches {
            manifest_bodies.push(s.graph.nodes[node.index()].body);
        }
    }
    if !valid {
        *rejection = CacheReason::FamilyFingerprintChanged;
        return Ok(false);
    }
    manifest_bodies.sort_unstable();
    manifest_bodies.dedup();
    let negative_scope = r.key()?;
    if !schema.negative_scope_valid(negative_scope, expected_negative_scope) {
        *rejection = CacheReason::NegativeLookupScopeChanged;
        return Ok(false);
    }
    let Some(bounds) = BoundClauses::read(&mut r, schema, s.facts, &s.types)? else {
        *rejection = CacheReason::FamilyFingerprintChanged;
        return Ok(false);
    };
    let capture_count = r.count(4)?;
    if s.closure_families.len() + capture_count >= LOCAL_BINDING as usize {
        return Err(Error::Limit("cached closure families"));
    }
    let bindings: Vec<_> = (0..capture_count)
        .map(|i| (s.closure_families.len() + i) as u32)
        .collect();
    let value_count = r.count(8)?;
    let mut values = Vec::new();
    values
        .try_reserve_exact(value_count)
        .map_err(|_| Error::Limit("cached values allocation"))?;
    let mut atoms = Vec::new();
    for _ in 0..value_count {
        let unknown = r.n()?;
        let n = r.count(8)?;
        if n > s.options.max_set_members {
            return Err(Error::Invalid("cache set precision"));
        }
        atoms.clear();
        for _ in 0..n {
            let kind = match r.n()? {
                1 => AtomKind::Object,
                2 => AtomKind::Callback,
                3 => AtomKind::UpperBound,
                4 => AtomKind::Container,
                _ => return Err(Error::Invalid("cache atom kind")),
            };
            if kind == AtomKind::UpperBound {
                atoms.push(bounds.atom(r.n()?)?);
                continue;
            }
            let site = schema.operation(&mut r)?;
            let symbol = schema.symbol(&mut r)?;
            let binding = if matches!(kind, AtomKind::Object | AtomKind::Container) {
                origin_binding(schema.symbol(&mut r)?)?
            } else {
                *bindings
                    .get(r.n()? as usize)
                    .ok_or(Error::Invalid("cached closure value"))?
            };
            if kind == AtomKind::Object {
                validate_cached_object(s.facts, &s.types, site, symbol, binding)?;
            } else if kind == AtomKind::Container {
                validate_container_atom(
                    s.facts,
                    Atom {
                        kind,
                        site,
                        symbol,
                        binding,
                    },
                )?;
            }
            atoms.push(Atom {
                kind,
                site,
                symbol,
                binding,
            });
        }
        atoms.sort_unstable();
        atoms.dedup();
        values.push(s.pool.intern(&atoms, unknown)?);
    }
    let val = |i: u32| {
        values
            .get(i as usize)
            .copied()
            .ok_or(Error::Invalid("cache value ID"))
    };
    let shape_count = r.count(8)?;
    if shape_count == 0 || shape_count > declared_contexts {
        return Err(Error::Invalid("cached callback shape count"));
    }
    let mut shapes = Vec::new();
    shapes
        .try_reserve_exact(shape_count)
        .map_err(|_| Error::Limit("cached callback shape IDs"))?;
    let mut shape_atoms = Vec::new();
    for _ in 0..shape_count {
        let arity = r.n()?;
        let count = r.count(76)?;
        shape_atoms.clear();
        shape_atoms
            .try_reserve(count)
            .map_err(|_| Error::Limit("cached callback shape atoms"))?;
        for _ in 0..count {
            let atom = context_policy::CallbackShapeAtom {
                argument: r.n()?,
                site: schema.operation(&mut r)?,
                symbol: schema.symbol(&mut r)?,
            };
            if atom.site.is_none() != atom.symbol.is_none() {
                return Err(Error::Invalid("cached callback shape marker"));
            }
            if !atom.site.is_none() {
                let operation = &s.facts.operations[atom.site.index()];
                if operation.opcode != Opcode::BindCallback || operation.target != atom.symbol {
                    return Err(Error::Invalid("cached callback shape code"));
                }
                if manifest_bodies.binary_search(&operation.body).is_err() {
                    return Err(Error::Invalid("unfingerprinted cached callback shape"));
                }
            }
            shape_atoms.push(atom);
        }
        // Compiler IDs may reorder across revisions; canonicalize the rebound
        // numeric order while rejecting duplicate code or unknown-marker rows.
        shape_atoms.sort_unstable();
        let scratch_bytes = manifest_bodies.capacity() * std::mem::size_of::<BodyId>()
            + shapes.capacity() * std::mem::size_of::<context_policy::CallbackShapeId>()
            + shape_atoms.capacity() * std::mem::size_of::<context_policy::CallbackShapeAtom>()
            + values.capacity() * std::mem::size_of::<Value>()
            + atoms.capacity() * std::mem::size_of::<Atom>()
            + bindings.capacity() * std::mem::size_of::<u32>();
        let shape_budget = s
            .options
            .memory_budget_bytes
            .saturating_sub(
                s.owned_bytes()
                    .saturating_sub(s.callback_shapes.owned_bytes()),
            )
            .saturating_sub(schema.owned_bytes())
            .saturating_sub(resident_bytes)
            .saturating_sub(scratch_bytes);
        shapes.push(
            s.callback_shapes
                .intern_rows_bounded(arity, &shape_atoms, shape_budget)?,
        );
    }
    let mut unique_shapes = shapes.clone();
    unique_shapes.sort_unstable();
    if unique_shapes.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err(Error::Invalid("duplicate cached callback shape"));
    }
    drop(unique_shapes);
    drop(shape_atoms);
    let context_count = r.count(76)?;
    if context_count != declared_contexts {
        return Err(Error::Invalid("summary context count"));
    }
    let mut contexts = Vec::new();
    contexts
        .try_reserve_exact(context_count)
        .map_err(|_| Error::Limit("cached context allocation"))?;
    let mut args = Vec::new();
    for _ in 0..context_count {
        let node = schema.node(&mut r)?;
        let receiver = val(r.n()?)?;
        let value = val(r.n()?)?;
        let version = r.q()?;
        let widened = match r.n()? {
            0 => false,
            1 => true,
            _ => return Err(Error::Invalid("cached widened context flag")),
        };
        let effects_open = match r.n()? {
            0 => false,
            1 => true,
            _ => return Err(Error::Invalid("cached effects-open context flag")),
        };
        let shape = *shapes
            .get(r.n()? as usize)
            .ok_or(Error::Invalid("cached context callback shape"))?;
        if version == 0 || version == u64::MAX {
            return Err(Error::Invalid("uncompleted cached context"));
        }
        let argc = r.count(4)?;
        args.clear();
        for _ in 0..argc {
            args.push(val(r.n()?)?);
        }
        let arguments = s.frames.intern(&args)?;
        let id = s.restore_completed_context(
            ContextKey {
                node,
                receiver,
                arguments,
            },
            value,
            version,
            widened,
            shape,
            effects_open,
        )?;
        contexts.push(id);
        let issues = r.count(4)?;
        for _ in 0..issues {
            let kind = IssueKind::decode(r.n()?)?;
            if !kind.is_execution_boundary() {
                return Err(Error::Invalid(
                    "metadata issue in cached execution obligations",
                ));
            }
            s.obligation(kind, node);
            s.issue_contexts.insert(id);
        }
        match r.n()? {
            0 => {}
            1 => {
                let site = RuntimeIssueSite {
                    kind: IssueKind::decode(r.n()?)?,
                    operation: schema.operation(&mut r)?,
                    reason: RuntimeIssueReason::decode(r.n()?)?,
                };
                s.record_runtime_issue_site(id, site)?;
            }
            _ => return Err(Error::Invalid("cached runtime issue flag")),
        }
    }
    let mut normalized = Vec::new();
    for binding in &bindings {
        let site = schema.operation(&mut r)?;
        if site.is_none() {
            return Err(Error::Invalid("capture family operation"));
        }
        // The finite creation key is independent of the joined payload. A
        // payload may widen after many concrete environments share this key.
        let family_receiver = read_family_value(
            &mut r,
            schema,
            &mut s.pool,
            &mut atoms,
            s.options.max_set_members,
            &bounds,
            s.facts,
            &s.types,
        )?;
        let family_argc = r.count(8)?;
        normalized.clear();
        normalized
            .try_reserve(family_argc)
            .map_err(|_| Error::Limit("cached family arguments"))?;
        for _ in 0..family_argc {
            normalized.push(read_family_value(
                &mut r,
                schema,
                &mut s.pool,
                &mut atoms,
                s.options.max_set_members,
                &bounds,
                s.facts,
                &s.types,
            )?);
        }
        let family_args = s.frames.intern(&normalized)?;
        let origins = read_family_value(
            &mut r,
            schema,
            &mut s.pool,
            &mut atoms,
            s.options.max_set_members,
            &bounds,
            s.facts,
            &s.types,
        )?;
        let receiver = val(r.n()?)?;
        let version = r.q()?;
        if version == 0 || version == u64::MAX {
            return Err(Error::Invalid("capture cache version"));
        }
        let argc = r.count(4)?;
        if argc != family_argc {
            return Err(Error::Invalid("capture family payload arity"));
        }
        args.clear();
        for _ in 0..argc {
            args.push(val(r.n()?)?);
        }
        let arguments = s.frames.intern(&args)?;
        let capture = Capture {
            receiver,
            arguments,
            version,
        };
        let family = ClosureFamily {
            site,
            receiver: family_receiver,
            arguments: family_args,
            origins,
        };
        capture_origins::validate(s.facts, &s.pool, &s.frames, family)?;
        if s.pool.members(origins).iter().any(|atom| {
            manifest_bodies
                .binary_search(&s.facts.operations[atom.site.index()].body)
                .is_err()
        }) {
            return Err(Error::Invalid("unfingerprinted cached callback origin"));
        }
        if s.closure_families.insert(family, *binding).is_some() {
            return Err(Error::Invalid("overlapping cached capture families"));
        }
        s.captures.insert(*binding, capture);
    }
    let call_count = r.count(88)?;
    for _ in 0..call_count {
        let source = *contexts
            .get(r.n()? as usize)
            .ok_or(Error::Invalid("cache call source"))?;
        let target = *contexts
            .get(r.n()? as usize)
            .ok_or(Error::Invalid("cache call target"))?;
        let operation = schema.operation(&mut r)?;
        let kind = EdgeKind::decode(r.n()?)?;
        let edge = schema.edge(&mut r)?;
        let binding = r.n()?;
        let binding = if binding == u32::MAX {
            u32::MAX
        } else {
            *bindings
                .get(binding as usize)
                .ok_or(Error::Invalid("cache call binding"))?
        };
        let call = ContextCall {
            source,
            target,
            operation,
            kind,
            edge,
            binding,
        };
        if s.call_index.insert(call) {
            s.calls.push(call);
        }
    }
    let slot_count = r.count(24)?;
    for _ in 0..slot_count {
        let slot = read_slot(&mut r, schema, &contexts, &bindings, &mut s.heap_owners)?;
        let value = val(r.n()?)?;
        let version = r.q()?;
        if version == 0 || version == u64::MAX {
            return Err(Error::Invalid("field cache version"));
        }
        if let Some(old) = s.slots.get(&slot) {
            // Independent families can carry the same finalized absence
            // certificate. Actual contributor cells must have one owner.
            if !matches!(slot.kind, SlotKind::FieldMissing | SlotKind::FieldAll)
                || value.unknown & UNKNOWN_FIELD == 0
                || old.value != value
                || old.version != version
                || negative_scope == ZERO
            {
                return Err(Error::Invalid("overlapping cached heap scopes"));
            }
        } else {
            s.slots.insert(slot, SlotValue { value, version });
        }
    }
    let read_count = r.count(28)?;
    for _ in 0..read_count {
        let query = *contexts
            .get(r.n()? as usize)
            .ok_or(Error::Invalid("cache dependency query"))?;
        let slot = read_slot(&mut r, schema, &contexts, &bindings, &mut s.heap_owners)?;
        let version = r.q()?;
        let present = match r.n()? {
            0 => false,
            1 => true,
            _ => return Err(Error::Invalid("cache dependency presence")),
        };
        s.dependencies.subscribe(
            query,
            Read {
                slot,
                version,
                present,
            },
        )?;
        if (slot.kind == SlotKind::Field && slot.owner != u32::MAX)
            || matches!(slot.kind, SlotKind::StaticField | SlotKind::FieldAll)
        {
            s.field_reads.insert(slot);
        }
    }
    let write_count = r.count(16)?;
    for _ in 0..write_count {
        let query = *contexts
            .get(r.n()? as usize)
            .ok_or(Error::Invalid("cache writer"))?;
        let slot = read_slot(&mut r, schema, &contexts, &bindings, &mut s.heap_owners)?;
        if matches!(slot.kind, SlotKind::FieldAll | SlotKind::FieldMissing) {
            return Err(Error::Invalid("derived cached writer"));
        }
        s.writes.insert((query, slot));
    }
    let root_count = r.count(4)?;
    for _ in 0..root_count {
        let root = *contexts
            .get(r.n()? as usize)
            .ok_or(Error::Invalid("cache root"))?;
        s.roots.push(root);
    }
    r.done()?;
    let loaded: HashSet<_> = contexts.iter().copied().collect();
    s.ready.retain(|id| !loaded.contains(id));
    s.metrics.summary_hits += contexts.len() as u64;
    s.metrics.states = s.contexts.len() as u64;
    if s.owned_bytes()
        .saturating_add(schema.owned_bytes())
        .saturating_add(resident_bytes)
        > s.options.memory_budget_bytes
    {
        return Err(Error::Limit("decoded completed summary state"));
    }
    Ok(true)
}
// Derived aggregates never carry an independent ownership claim. A cached
// consumer may retain a checked aggregate/version; unobserved aggregates are
// rebuilt only from the actual primary contributions admitted into this query.
fn restore_heap_aggregates(s: &mut QuerySession<'_>) -> Result<(), Error> {
    if s.heap_owners.rows().iter().any(|key| {
        s.facts
            .operations
            .get(key.site.index())
            .is_none_or(|op| !op.opcode.is_heap_site())
    }) {
        return Err(Error::Invalid("cached partition allocation authority"));
    }
    if s.slots.keys().any(|slot| {
        matches!(slot.kind, SlotKind::FieldAll | SlotKind::FieldWildcard)
            && s.facts
                .operations
                .get(slot.owner as usize)
                .is_none_or(|op| !op.opcode.is_heap_site())
    }) {
        return Err(Error::Invalid("cached aggregate allocation authority"));
    }
    let bytes = s.slots.len().saturating_mul(96);
    if s.owned_bytes().saturating_add(bytes) > s.options.memory_budget_bytes {
        return Err(Error::Limit("cached aggregate validation"));
    }
    let mut expected = HashMap::<Slot, Value>::new();
    expected
        .try_reserve(s.slots.len())
        .map_err(|_| Error::Limit("cached aggregate validation"))?;
    for (slot, value) in &s.slots {
        let site = match slot.kind {
            SlotKind::Field => s.heap_owners.key(slot.owner).map(|key| key.site.0),
            SlotKind::FieldWildcard => Some(slot.owner),
            _ => None,
        };
        if let Some(site) = site {
            let all = Slot {
                kind: SlotKind::FieldAll,
                owner: site,
                member: slot.member,
            };
            let old = expected.get(&all).copied().unwrap_or(Value::EMPTY);
            expected.insert(all, s.pool.join(old, value.value)?);
        }
    }
    for (slot, value) in &s.slots {
        if slot.kind == SlotKind::FieldAll && expected.get(slot) != Some(&value.value) {
            return Err(Error::Invalid("cached aggregate contributor closure"));
        }
    }
    drop(expected);
    s.rebuild_heap_aggregates()
}
fn ref_name(config: &CacheConfig, graph: ContentHash, options: &SolveOptions) -> String {
    format!(
        "{graph}-{}-{}-{}.ref",
        config.producer,
        options.max_set_members,
        ContentHash(cache_policy_key(options))
    )
}
fn latest_name(config: &CacheConfig, options: &SolveOptions) -> String {
    format!(
        "latest-{}-{}-{}.ref",
        config.producer,
        options.max_set_members,
        ContentHash(cache_policy_key(options))
    )
}
fn write_ref(directory: &Path, name: &str, value: &str) -> Result<(), Error> {
    let id = TEMP_ID.fetch_add(1, Ordering::Relaxed);
    let path = directory.join(format!(".summary-ref-{}-{id}.tmp", std::process::id()));
    struct Cleanup<'a>(&'a Path);
    impl Drop for Cleanup<'_> {
        fn drop(&mut self) {
            let _ = fs::remove_file(self.0);
        }
    }
    let _cleanup = Cleanup(&path);
    let mut file = fs::OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(&path)?;
    file.write_all(value.as_bytes())?;
    file.sync_all()?;
    drop(file);
    fs::rename(&path, directory.join(name))?;
    #[cfg(unix)]
    fs::File::open(directory)?.sync_all()?;
    Ok(())
}
fn table_bound(entries: usize, row: usize) -> usize {
    // Include bucket slack and control bytes without relying on the current
    // HashMap capacity policy. Empty maps allocate nothing.
    if entries == 0 {
        0
    } else {
        entries
            .saturating_mul(3)
            .saturating_mul(row + 1)
            .saturating_add(64)
    }
}
fn metadata_peak(f: &FactSnapshot, g: &ProgramGraph, rebind: bool) -> usize {
    let (mut edges, mut largest_fanout) = (0usize, 0usize);
    for node in 0..g.nodes.len() {
        let n = g
            .successors(NodeId(node as u32))
            .filter(|(_, e)| e.kind.is_execution())
            .count();
        edges = edges.saturating_add(n);
        largest_fanout = largest_fanout.max(n);
    }
    let (symbols, nodes, ops, issues) = (
        f.symbols.len(),
        g.nodes.len(),
        f.operations.len(),
        g.issues.len(),
    );
    let base = symbols
        .saturating_add(nodes)
        .saturating_add(ops)
        .saturating_add(edges)
        .saturating_mul(32)
        .saturating_add(g.edges.len().saturating_mul(4))
        .saturating_add(f.bodies.len().saturating_mul(4));
    let scope_map = table_bound(issues.min(nodes.saturating_add(f.files.len())), 40);
    let symbol_phase = symbols
        .saturating_mul(36)
        .saturating_add(table_bound(symbols, 36));
    let node_phase = symbols
        .saturating_add(nodes)
        .saturating_mul(32)
        .saturating_add(table_bound(nodes, 36))
        .saturating_add(table_bound(nodes, 12));
    let shapes = symbols
        .saturating_add(f.relations.len())
        .saturating_add(f.suites.len())
        .saturating_add(
            f.result_bounds
                .iter()
                .filter(|r| r.operation.is_none())
                .count(),
        )
        .saturating_add(
            g.issues
                .iter()
                .filter(|i| i.node.is_none() && i.file.is_none())
                .count(),
        );
    let shape_phase = base
        .saturating_add(shapes.saturating_mul(32))
        .saturating_add(symbols.saturating_mul(4));
    let issue_phase = base
        .saturating_add(issues.saturating_mul(40))
        .saturating_add(scope_map);
    let fingerprint_phase = base
        .saturating_add(nodes.saturating_mul(32))
        .saturating_add(scope_map)
        .saturating_add(largest_fanout.saturating_mul(64));
    let execution_phase = base.saturating_add(nodes.saturating_mul(96));
    let peak = [
        symbol_phase,
        node_phase,
        shape_phase,
        issue_phase,
        fingerprint_phase,
        execution_phase,
    ]
    .into_iter()
    .max()
    .unwrap_or(0);
    if rebind {
        peak.saturating_add(table_bound(symbols, 36))
            .saturating_add(table_bound(nodes, 36))
            .saturating_add(table_bound(ops, 36))
            .saturating_add(table_bound(edges, 36))
    } else {
        peak
    }
}
fn metadata_fits(s: &QuerySession<'_>, rebind: bool, resident_bytes: usize) -> bool {
    metadata_peak(s.facts, s.graph, rebind).saturating_add(resident_bytes)
        <= s.options
            .memory_budget_bytes
            .saturating_sub(s.owned_bytes())
}
pub(super) fn save(s: &QuerySession<'_>, config: &CacheConfig) -> Result<(), Error> {
    match save_inner(s, config) {
        Err(Error::Io(_)) => {
            emit(
                s,
                config,
                CacheAction::WriteSkipped,
                CacheReason::IoFailure,
                0,
                0,
                ZERO,
            );
            Ok(())
        }
        Err(error) => {
            emit(
                s,
                config,
                CacheAction::WriteSkipped,
                CacheReason::CorruptArtifact,
                0,
                0,
                ZERO,
            );
            Err(error)
        }
        result => result,
    }
}
fn save_inner(s: &QuerySession<'_>, config: &CacheConfig) -> Result<(), Error> {
    if s.reuse.same_snapshot
        && s.reuse.loaded_contexts == s.contexts.len() as u64
        && s.metrics.edge_visits == 0
    {
        emit(
            s,
            config,
            CacheAction::WriteSkipped,
            CacheReason::AlreadyWarm,
            0,
            s.contexts.len() as u64,
            ZERO,
        );
        return Ok(());
    }
    emit(
        s,
        config,
        CacheAction::PreparingSchema,
        CacheReason::IndependentFamilies,
        0,
        s.contexts.len() as u64,
        ZERO,
    );
    if !metadata_fits(s, false, 0) {
        emit(
            s,
            config,
            CacheAction::WriteSkipped,
            CacheReason::MemoryBudget,
            0,
            0,
            ZERO,
        );
        return Ok(());
    }
    if s.contexts.is_empty() {
        emit(
            s,
            config,
            CacheAction::WriteSkipped,
            CacheReason::NoContexts,
            0,
            0,
            ZERO,
        );
        return Ok(());
    }
    let partial = !s.sealed || !s.ready.is_empty() || s.completion == Completion::ResourceLimited;
    let schema = match Schema::new(s.facts, s.graph, false) {
        Ok(schema) => schema,
        Err(Error::Invalid("ambiguous stable compiler identity")) => {
            emit(
                s,
                config,
                CacheAction::WriteSkipped,
                CacheReason::AmbiguousIdentity,
                0,
                0,
                ZERO,
            );
            return Ok(());
        }
        Err(e) => return Err(e),
    };
    if s.owned_bytes().saturating_add(schema.owned_bytes()) > s.options.memory_budget_bytes {
        emit(
            s,
            config,
            CacheAction::WriteSkipped,
            CacheReason::MemoryBudget,
            0,
            0,
            ZERO,
        );
        return Ok(());
    }
    emit(
        s,
        config,
        CacheAction::Grouping,
        CacheReason::IndependentFamilies,
        0,
        s.contexts.len() as u64,
        ZERO,
    );
    let reads = s.dependencies.active_reads().count();
    let all_reads = s
        .dependencies
        .active_reads()
        .filter(|(_, read)| read.slot.kind == SlotKind::FieldAll)
        .count();
    let all_contributors = s
        .writes
        .iter()
        .filter(|(_, slot)| s.field_all_slot(*slot).is_some())
        .count();
    // Contributor-only closure keeps separate indexes for actual writers,
    // coarse readers, and the aggregates with a contributor. Admit their peak
    // before constructing any of them; shared negative readers can otherwise
    // make the new indexes much larger than the writer index alone.
    let grouping_peak = s
        .contexts
        .len()
        .saturating_mul(128)
        .saturating_add(table_bound(reads.saturating_add(s.writes.len()), 16))
        .saturating_add(table_bound(all_reads, 12))
        .saturating_add(table_bound(all_contributors, 8))
        .saturating_add(table_bound(s.writes.len(), 12));
    let initial_bytes = s.owned_bytes().saturating_add(schema.owned_bytes());
    if initial_bytes.saturating_add(grouping_peak) > s.options.memory_budget_bytes {
        emit(
            s,
            config,
            CacheAction::WriteSkipped,
            CacheReason::MemoryBudget,
            0,
            0,
            ZERO,
        );
        return Ok(());
    }
    let (groups, owners) = family_groups(s);
    let writer_slots: HashSet<_> = s.writes.iter().map(|(_, slot)| *slot).collect();
    let groups_bytes = groups.capacity() * std::mem::size_of::<Vec<ContextId>>()
        + groups.iter().map(|g| g.capacity() * 4).sum::<usize>();
    let grouped_bytes = initial_bytes
        .saturating_add(groups_bytes)
        .saturating_add(owners.capacity() * 24)
        .saturating_add(writer_slots.capacity() * 24);
    let rows = [
        s.calls.len().saturating_mul(16),
        reads.saturating_mul(48),
        s.writes.len().saturating_mul(24),
        s.slots.len().saturating_mul(40),
        s.captures.len().saturating_mul(40),
        s.roots.len().saturating_mul(16),
        s.issues.len().saturating_mul(8),
    ];
    let encoding_peak = rows
        .iter()
        .copied()
        .fold(0usize, usize::saturating_add)
        .saturating_mul(2)
        .saturating_add(rows.into_iter().max().unwrap_or(0) / 2)
        .saturating_add(groups.len().saturating_add(1).saturating_mul(48))
        .saturating_add(table_bound(s.closure_families.len(), 32));
    if grouped_bytes.saturating_add(encoding_peak) > s.options.memory_budget_bytes {
        emit(
            s,
            config,
            CacheAction::WriteSkipped,
            CacheReason::MemoryBudget,
            0,
            0,
            ZERO,
        );
        return Ok(());
    }
    emit(
        s,
        config,
        CacheAction::Encoding,
        CacheReason::IndependentFamilies,
        groups.len() as u64,
        s.contexts.len() as u64,
        ZERO,
    );
    let families = EncodedFamilies::new(s, &groups, &owners);
    let mut pending = vec![false; s.contexts.len()];
    for id in &s.ready {
        pending[id.index()] = true;
    }
    let resident_bytes = grouped_bytes
        .saturating_add(families.owned_bytes())
        .saturating_add(pending.capacity());
    let completed = |index: usize, group: &[ContextId]| {
        if !partial {
            return true;
        }
        // A capped coordinator can publish only pure, closed call families.
        // No future outside writer/capture publication can affect this family;
        // mutable or unfinished groups belong exclusively in continuations.
        families.reads.get(index).is_empty()
            && families.writes.get(index).is_empty()
            && families.slots.get(index).is_empty()
            && families.captures.get(index).is_empty()
            && group.iter().all(|id| {
                let context = s.contexts[id.index()];
                context.evaluated
                    && context.version != 0
                    && context.version != u64::MAX
                    && !pending[id.index()]
                    && std::iter::once(context.key.receiver)
                        .chain(std::iter::once(context.value))
                        .chain(s.frames.get(context.key.arguments).iter().copied())
                        .all(|value| {
                            s.pool
                                .members(value)
                                .iter()
                                .all(|atom| atom.kind != AtomKind::Callback)
                        })
            })
    };
    let selected_families = groups
        .iter()
        .enumerate()
        .filter(|(index, group)| completed(*index, group))
        .count();
    let selected_contexts: usize = groups
        .iter()
        .enumerate()
        .filter(|(index, group)| completed(*index, group))
        .map(|(_, group)| group.len())
        .sum();
    if partial && selected_families < groups.len() {
        emit(
            s,
            config,
            CacheAction::WriteSkipped,
            CacheReason::IncompleteFamily,
            (groups.len() - selected_families) as u64,
            (s.contexts.len() - selected_contexts) as u64,
            ZERO,
        );
    }
    if selected_families == 0 {
        return Ok(());
    }
    let mut w = Writer(Vec::with_capacity(204));
    w.n(VERSION);
    w.key(config.producer.0);
    w.n(s.options.max_set_members as u32);
    w.key(cache_policy_key(&s.options));
    w.key(schema.global);
    w.key(s.facts.identity.0);
    w.key(s.graph.identity.0);
    let seal = exact::content_seal(s.facts, s.graph);
    w.key(seal);
    let negative_scope = negative_frontier(s, seal, true).unwrap_or_else(|| {
        digest(&[
            b"unproven-negative-frontier/v2",
            &schema.execution_global,
            &seal,
        ])
    });
    w.n(selected_families as u32);
    for (index, group) in groups.iter().enumerate() {
        if !completed(index, group) {
            continue;
        }
        if !encode_group(
            s,
            &schema,
            group,
            index,
            &families,
            &writer_slots,
            &mut w,
            resident_bytes,
            negative_scope,
        )? {
            emit(
                s,
                config,
                CacheAction::WriteSkipped,
                CacheReason::MemoryBudget,
                0,
                0,
                ZERO,
            );
            return Ok(());
        }
    }
    emit(
        s,
        config,
        CacheAction::Publishing,
        CacheReason::IndependentFamilies,
        selected_families as u64,
        selected_contexts as u64,
        ZERO,
    );
    let artifact = selector_artifacts::publish(
        &config.directory,
        ArtifactKind::Summaries,
        &[Section {
            id: 1,
            count: selected_contexts as u64,
            bytes: &w.0,
        }],
    )
    .map_err(error)?;
    let name = artifact
        .path
        .file_name()
        .and_then(|s| s.to_str())
        .ok_or(Error::Invalid("summary artifact filename"))?;
    write_ref(
        &config.directory,
        &ref_name(config, s.graph.identity, &s.options),
        name,
    )?;
    write_ref(&config.directory, &latest_name(config, &s.options), name)?;
    emit(
        s,
        config,
        CacheAction::Written,
        if partial {
            CacheReason::IndependentFamilies
        } else {
            CacheReason::ExactSnapshot
        },
        selected_families as u64,
        selected_contexts as u64,
        artifact.identity,
    );
    Ok(())
}
pub(super) fn restore(
    s: &mut QuerySession<'_>,
    config: &CacheConfig,
) -> Result<ReuseMetrics, Error> {
    let result = restore_inner(s, config);
    if let Err(error) = &result {
        emit(
            s,
            config,
            CacheAction::Rejected,
            if matches!(error, Error::Io(_)) {
                CacheReason::IoFailure
            } else {
                CacheReason::CorruptArtifact
            },
            0,
            0,
            ZERO,
        );
    }
    result
}
fn restore_inner(s: &mut QuerySession<'_>, config: &CacheConfig) -> Result<ReuseMetrics, Error> {
    let exact = config
        .directory
        .join(ref_name(config, s.graph.identity, &s.options));
    let latest = config.directory.join(latest_name(config, &s.options));
    let reference = if exact.exists() {
        exact
    } else if latest.exists() {
        latest
    } else {
        emit(
            s,
            config,
            CacheAction::Miss,
            CacheReason::ReferenceAbsent,
            0,
            0,
            ZERO,
        );
        return Ok(ReuseMetrics::default());
    };
    let metadata = fs::metadata(&reference)?;
    if metadata.len() > 128 {
        return Err(Error::Invalid("summary reference length"));
    }
    let mut input = fs::File::open(&reference)?;
    let mut reference_bytes = Vec::new();
    std::io::Read::read_to_end(
        &mut std::io::Read::take(&mut input, 129),
        &mut reference_bytes,
    )?;
    if reference_bytes.len() > 128 {
        return Err(Error::Invalid("summary reference length"));
    }
    let name = std::str::from_utf8(&reference_bytes)
        .map_err(|_| Error::Invalid("summary reference UTF-8"))?
        .trim();
    let key = name
        .strip_suffix(".rsel")
        .ok_or(Error::Invalid("summary reference"))?;
    if !key.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err(Error::Invalid("summary reference digest"));
    }
    let expected_identity = ContentHash::from_hex(key)?;
    let path = config.directory.join(name);
    let available_bytes = s
        .options
        .memory_budget_bytes
        .saturating_sub(s.owned_bytes());
    // The artifact reader owns a verified byte copy. Count that live owner
    // before opening it rather than admitting a budget-sized copy on top of
    // the already constructed query tables.
    if fs::metadata(&path)?.len() > available_bytes as u64 {
        emit(
            s,
            config,
            CacheAction::Rejected,
            CacheReason::MemoryBudget,
            0,
            0,
            expected_identity.0,
        );
        return Ok(ReuseMetrics::default());
    }
    let artifact =
        selector_artifacts::open_bounded(&path, ArtifactKind::Summaries, available_bytes as u64)
            .map_err(error)?;
    if artifact.identity() != expected_identity.0 {
        return Err(Error::Invalid("summary content identity"));
    }
    if artifact.section_ids().collect::<Vec<_>>() != vec![1] {
        return Err(Error::Invalid("summary sections"));
    }
    let expected_contexts = artifact.count(1).map_err(error)?;
    let mut decoded_contexts = 0u64;
    let mut r = Reader::new(artifact.section(1).map_err(error)?);
    if r.n()? != VERSION {
        emit(
            s,
            config,
            CacheAction::Rejected,
            CacheReason::FormatVersion,
            0,
            0,
            artifact.identity(),
        );
        return Ok(ReuseMetrics::default());
    }
    if r.key()? != config.producer.0 {
        emit(
            s,
            config,
            CacheAction::Rejected,
            CacheReason::ProducerMismatch,
            0,
            0,
            artifact.identity(),
        );
        return Ok(ReuseMetrics::default());
    }
    if r.n()? as usize != s.options.max_set_members {
        emit(
            s,
            config,
            CacheAction::Rejected,
            CacheReason::OptionsMismatch,
            0,
            0,
            artifact.identity(),
        );
        return Ok(ReuseMetrics::default());
    }
    if r.key()? != cache_policy_key(&s.options) {
        emit(
            s,
            config,
            CacheAction::Rejected,
            CacheReason::OptionsMismatch,
            0,
            0,
            artifact.identity(),
        );
        return Ok(ReuseMetrics::default());
    }
    let expected_global = r.key()?;
    let facts = r.key()?;
    let graph = r.key()?;
    let seal = r.key()?;
    let count = r.count(8)?;
    let mut stats = ReuseMetrics {
        same_snapshot: facts == s.facts.identity.0 && graph == s.graph.identity.0,
        ..Default::default()
    };
    let resident_bytes = artifact.byte_len();
    let mut schema = if stats.same_snapshot {
        let fixed_peak = s
            .graph
            .nodes
            .len()
            .saturating_mul(12)
            .saturating_add(s.facts.bodies.len().saturating_mul(4))
            .saturating_add(table_bound(s.graph.nodes.len(), 12));
        if fixed_peak
            .saturating_add(resident_bytes)
            .saturating_add(s.owned_bytes())
            > s.options.memory_budget_bytes
        {
            stats.rejected_families = count as u64;
            emit(
                s,
                config,
                CacheAction::Rejected,
                CacheReason::MemoryBudget,
                count as u64,
                0,
                artifact.identity(),
            );
            return Ok(stats);
        }
        if exact::content_seal(s.facts, s.graph) != seal {
            return Err(Error::Invalid("summary snapshot content seal"));
        }
        Admission::Exact(exact::ExactProgram::new(s.facts, s.graph))
    } else {
        if !metadata_fits(s, true, resident_bytes) {
            stats.rejected_families = count as u64;
            emit(
                s,
                config,
                CacheAction::Rejected,
                CacheReason::MemoryBudget,
                count as u64,
                0,
                artifact.identity(),
            );
            return Ok(stats);
        }
        let schema = match Schema::new(s.facts, s.graph, true) {
            Ok(schema) => schema,
            Err(Error::Invalid("ambiguous stable compiler identity")) => {
                emit(
                    s,
                    config,
                    CacheAction::Rejected,
                    CacheReason::AmbiguousIdentity,
                    count as u64,
                    0,
                    artifact.identity(),
                );
                return Ok(ReuseMetrics::default());
            }
            Err(e) => return Err(e),
        };
        if expected_global != schema.global {
            stats.rejected_families = count as u64;
            emit(
                s,
                config,
                CacheAction::Rejected,
                CacheReason::GlobalShapeChanged,
                count as u64,
                0,
                artifact.identity(),
            );
            return Ok(stats);
        }
        Admission::Rebase(schema)
    };
    if s.owned_bytes()
        .saturating_add(schema.owned_bytes())
        .saturating_add(resident_bytes)
        > s.options.memory_budget_bytes
    {
        stats.rejected_families = count as u64;
        emit(
            s,
            config,
            CacheAction::Rejected,
            CacheReason::MemoryBudget,
            count as u64,
            0,
            artifact.identity(),
        );
        return Ok(stats);
    }
    let mut rejections = [
        (CacheReason::ContextBudget, 0u64),
        (CacheReason::MemoryBudget, 0),
        (CacheReason::FamilyFingerprintChanged, 0),
        (CacheReason::NegativeLookupScopeChanged, 0),
    ];
    let expected_negative_scope = if stats.same_snapshot {
        negative_frontier(s, seal, false)
    } else {
        None
    };
    for _ in 0..count {
        let len = usize::try_from(r.q()?).map_err(|_| Error::Invalid("summary family length"))?;
        let bytes = r.take(len)?;
        let mut family_header = Reader::new(bytes);
        decoded_contexts = decoded_contexts
            .checked_add(family_header.n()? as u64)
            .ok_or(Error::Invalid("summary context count overflow"))?;
        let before = s.contexts.len();
        let mut rejection = CacheReason::FamilyFingerprintChanged;
        if decode_group(
            s,
            &mut schema,
            bytes,
            resident_bytes,
            &mut rejection,
            expected_negative_scope,
        )? {
            stats.loaded_families += 1;
            stats.loaded_contexts += (s.contexts.len() - before) as u64;
        } else {
            stats.rejected_families += 1;
            rejections
                .iter_mut()
                .find(|(reason, _)| *reason == rejection)
                .unwrap()
                .1 += 1;
        }
    }
    r.done()?;
    if decoded_contexts != expected_contexts {
        return Err(Error::Invalid("summary artifact context count"));
    }
    restore_heap_aggregates(s)?;
    s.validate_effect_states()?;
    s.rebuild_context_policy()?;
    s.sealed = s.ready.is_empty();
    for (reason, families) in rejections {
        if families != 0 {
            emit(
                s,
                config,
                CacheAction::Rejected,
                reason,
                families,
                0,
                artifact.identity(),
            );
        }
    }
    if stats.loaded_families != 0 {
        emit(
            s,
            config,
            CacheAction::Hit,
            if stats.same_snapshot {
                CacheReason::ExactSnapshot
            } else {
                CacheReason::IndependentFamilies
            },
            stats.loaded_families,
            stats.loaded_contexts,
            artifact.identity(),
        );
    }
    Ok(stats)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[derive(Debug, Default)]
    struct Trace(std::sync::Mutex<Vec<CacheEvent>>);
    impl crate::SolveObserver for Trace {
        fn observe(&self, event: crate::SolveEvent) {
            if let Some(event) = event.cache {
                self.0.lock().unwrap().push(event);
            }
        }
    }
    fn pure_fixture() -> (FactSnapshot, ProgramGraph) {
        let (facts, mut graph) = fixture();
        graph.edges.clear();
        for node in &mut graph.nodes {
            node.flags = NODE_EFFECTS_COMPLETE;
        }
        graph.index().unwrap();
        (facts, graph)
    }
    fn bound_fixture() -> (FactSnapshot, ProgramGraph) {
        let (mut facts, graph) = pure_fixture();
        for symbol in &mut facts.symbols {
            symbol.kind = 13;
            symbol.flags = SYMBOL_DEFINED | SYMBOL_SCALA_PARENTS_COMPLETE;
        }
        facts.bound_classes.push(SymbolId(0));
        facts.result_bounds.push(ResultBoundRecord {
            symbol: SymbolId(0),
            operation: OperationId::NONE,
            classes: IdRange { start: 0, len: 1 },
        });
        (facts, graph)
    }
    #[test]
    fn effect_closure_survives_exact_and_rebased_completed_family_restore() {
        let (mut facts, mut graph) = pure_fixture();
        graph.nodes[1].flags = 0; // Missing executable body keeps this context open.
        let options = SolveOptions {
            workers: 1,
            ..Default::default()
        };
        let directory = tempfile::tempdir().unwrap();
        let runtime =
            SolverRuntime::with_cache_directory(&options, directory.path(), ContentHash([97; 32]))
                .unwrap();
        let roots = [0, 1].map(|id| ExecutionRoot {
            node: NodeId(id),
            receiver: SymbolId::NONE,
        });
        {
            let mut original =
                QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
            original.execute(&roots).unwrap();
            assert_eq!(
                original
                    .contexts
                    .iter()
                    .map(|c| c.effects_open)
                    .collect::<Vec<_>>(),
                [false, true]
            );
            original.persist_completed().unwrap();
        }
        for rebase in [false, true] {
            if rebase {
                facts.identity = ContentHash([98; 32]);
                graph.facts_identity = facts.identity;
                graph.identity = ContentHash([99; 32]);
            }
            let restored = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
            assert_eq!(restored.reuse_metrics().loaded_contexts, 2);
            for context in &restored.contexts {
                assert_eq!(context.effects_open, context.key.node == NodeId(1));
            }
        }
    }
    #[test]
    fn resealed_effect_closure_bits_are_checked_and_old_cache_cannot_certify_closed() {
        let (facts, mut graph) = pure_fixture();
        graph.nodes[1].flags = 0;
        let options = SolveOptions {
            workers: 1,
            ..Default::default()
        };
        let directory = tempfile::tempdir().unwrap();
        let runtime =
            SolverRuntime::with_cache_directory(&options, directory.path(), ContentHash([100; 32]))
                .unwrap();
        let config = runtime.inner.cache.as_ref().unwrap();
        let mut original = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
        original
            .execute(&[0, 1].map(|node| ExecutionRoot {
                node: NodeId(node),
                receiver: SymbolId::NONE,
            }))
            .unwrap();
        assert!(!original.contexts[0].effects_open);
        original.persist_completed().unwrap();
        let reference = directory
            .path()
            .join(ref_name(config, graph.identity, &options));
        let initial = fs::read(&reference).unwrap();
        let schema = Schema::new(&facts, &graph, false).unwrap();
        for (node_id, saved_flag, forged_flag) in [(0, 0u32, 2u32), (1, 1, 0)] {
            let mut node = Writer(Vec::new());
            node.node(&schema, NodeId(node_id));
            rewrite(config, &graph, &options, |bytes| {
                let positions: Vec<_> = bytes
                    .windows(node.0.len())
                    .enumerate()
                    .filter_map(|(i, row)| {
                        (row == node.0
                            && bytes.get(i + 44..i + 52) == Some(1u64.to_le_bytes().as_slice())
                            && bytes.get(i + 52..i + 56) == Some(0u32.to_le_bytes().as_slice())
                            && bytes.get(i + 56..i + 60)
                                == Some(saved_flag.to_le_bytes().as_slice()))
                        .then_some(i)
                    })
                    .collect();
                assert_eq!(positions.len(), 1);
                let effect = positions[0] + 56;
                bytes[effect..effect + 4].copy_from_slice(&forged_flag.to_le_bytes());
            });
            assert!(QuerySession::with_runtime(&facts, &graph, &options, &runtime).is_err());
            fs::write(&reference, &initial).unwrap();
        }
        rewrite(config, &graph, &options, |bytes| {
            bytes[..4].copy_from_slice(&13u32.to_le_bytes())
        });
        let legacy = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
        assert_eq!(legacy.reuse_metrics().loaded_contexts, 0);
        assert!(legacy.contexts.is_empty());
    }
    #[test]
    fn semantic_bound_table_checks_class_authority_before_import() {
        let (facts, graph) = bound_fixture();
        let schema = Schema::new(&facts, &graph, false).unwrap();
        let types = TypeIndex::new(&facts);
        let mut valid = Writer(Vec::new());
        valid.n(1);
        valid.n(1);
        valid.symbol(&schema, SymbolId(0));
        let read = |bytes: &[u8]| {
            let mut admission = Admission::Exact(exact::ExactProgram::new(&facts, &graph));
            BoundClauses::read(&mut Reader::new(bytes), &mut admission, &facts, &types)
        };
        let clause = read(&valid.0).unwrap().unwrap();
        assert_eq!(
            clause.atom(0).unwrap(),
            types
                .canonical_bound_for_classes(&facts, &[SymbolId(0)])
                .unwrap()
        );
        assert!(clause.atom(1).is_err());
        let mut missing = Writer(Vec::new());
        missing.n(1);
        missing.n(1);
        missing.symbol(&schema, SymbolId(1));
        assert!(
            read(&missing.0).unwrap().is_none(),
            "a valid class without an admitted exact conjunction is a cache miss"
        );
        let mut duplicate = Writer(Vec::new());
        duplicate.n(1);
        duplicate.n(2);
        duplicate.symbol(&schema, SymbolId(0));
        duplicate.symbol(&schema, SymbolId(0));
        let mut null = Writer(Vec::new());
        null.n(1);
        null.n(1);
        null.symbol(&schema, SymbolId::NONE);
        let mut wrong_id = valid.0.clone();
        wrong_id[40..44].copy_from_slice(&1u32.to_le_bytes());
        let mut empty = valid.0.clone();
        empty[4..8].copy_from_slice(&0u32.to_le_bytes());
        let mut excessive = Writer(Vec::new());
        excessive.n(1);
        excessive.n(MAX_RESULT_BOUND_CLASSES as u32 + 1);
        for _ in 0..=MAX_RESULT_BOUND_CLASSES {
            excessive.symbol(&schema, SymbolId(0));
        }
        for bytes in [duplicate.0, null.0, wrong_id, empty, excessive.0] {
            assert!(read(&bytes).is_err(), "malformed semantic conjunction");
        }
    }
    #[test]
    fn normalized_capture_key_retains_its_bound_when_joined_payload_forgets_it() {
        let (mut facts, mut graph) = bound_fixture();
        facts.files.push(FileRecord {
            path: facts.symbols[0].name,
            source: StrId::NONE,
            revision: StrId::NONE,
            context: StrId::NONE,
            source_hash: ContentHash::default(),
            flags: 0,
        });
        facts.bodies.push(BodyRecord {
            symbol: SymbolId(0),
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange { start: 0, len: 1 },
            parameters: IdRange::default(),
            body_hash: ContentHash([73; 32]),
            flags: 0,
        });
        facts.operations.push(OperationRecord {
            body: BodyId(0),
            opcode: Opcode::BindCallback,
            target: SymbolId(1),
            dest: ValueId(1),
            a: ValueId::NONE,
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span::default(),
            flags: 0,
        });
        graph.nodes[0].body = BodyId(0);
        let options = SolveOptions {
            workers: 1,
            ..Default::default()
        };
        let directory = tempfile::tempdir().unwrap();
        let runtime =
            SolverRuntime::with_cache_directory(&options, directory.path(), ContentHash([74; 32]))
                .unwrap();
        {
            let mut session =
                QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
            session
                .execute(&[ExecutionRoot {
                    node: NodeId(0),
                    receiver: SymbolId(0),
                }])
                .unwrap();
            assert_eq!(session.closure_families.len(), 1);
            let (old_key, binding) = session
                .closure_families
                .iter()
                .map(|(key, binding)| (*key, *binding))
                .next()
                .unwrap();
            let atom = session
                .types
                .canonical_bound_for_classes(&facts, &[SymbolId(0)])
                .unwrap();
            let typed = session
                .pool
                .intern(&[atom], UNKNOWN_VALUE | UNKNOWN_TYPED)
                .unwrap();
            let key_arguments = session.frames.intern(&[typed]).unwrap();
            let payload_arguments = session.frames.intern(&[Value::TOP]).unwrap();
            // Model an already joined capture payload. Its finite creation key
            // retains constraints that no ordinary serialized value now has.
            session.closure_families.remove(&old_key);
            session.closure_families.insert(
                ClosureFamily {
                    site: old_key.site,
                    receiver: typed,
                    arguments: key_arguments,
                    origins: old_key.origins,
                },
                binding,
            );
            session.captures.insert(
                binding,
                Capture {
                    receiver: Value::TOP,
                    arguments: payload_arguments,
                    version: 1,
                },
            );
            session.persist_completed().unwrap();
        }
        let warm = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
        assert_eq!(warm.reuse_metrics().loaded_families, 1);
        let (key, binding) = warm.closure_families.iter().next().unwrap();
        let expected = warm
            .types
            .canonical_bound_for_classes(&facts, &[SymbolId(0)])
            .unwrap();
        assert_eq!(warm.pool.members(key.receiver), &[expected]);
        assert_eq!(key.receiver.unknown, UNKNOWN_VALUE | UNKNOWN_TYPED);
        let arguments = warm.frames.get(key.arguments);
        assert_eq!(arguments, &[key.receiver]);
        let payload = warm.captures[binding];
        assert_eq!(payload.receiver, Value::TOP);
        assert_eq!(warm.frames.get(payload.arguments), &[Value::TOP]);
    }
    #[test]
    fn cached_runtime_site_requires_its_reason_body_and_actual_obligation() {
        let (mut facts, mut graph) = bound_fixture();
        facts.files.push(FileRecord {
            path: facts.symbols[0].name,
            source: StrId::NONE,
            revision: StrId::NONE,
            context: StrId::NONE,
            source_hash: ContentHash::default(),
            flags: 0,
        });
        for (id, opcode) in [Opcode::BindCallback, Opcode::Constant]
            .into_iter()
            .enumerate()
        {
            facts.bodies.push(BodyRecord {
                symbol: SymbolId(id as u32),
                file: FileId(0),
                span: Span::default(),
                name_span: Span::default(),
                operations: IdRange {
                    start: id as u32,
                    len: 1,
                },
                parameters: IdRange::default(),
                body_hash: ContentHash([id as u8; 32]),
                flags: 0,
            });
            facts.operations.push(OperationRecord {
                body: BodyId(id as u32),
                opcode,
                target: SymbolId::NONE,
                dest: ValueId(1),
                a: ValueId::NONE,
                b: ValueId::NONE,
                arguments: IdRange::default(),
                span: Span::default(),
                flags: 0,
            });
            graph.nodes[id].body = BodyId(id as u32);
        }
        let options = SolveOptions {
            workers: 1,
            ..Default::default()
        };
        let directory = tempfile::tempdir().unwrap();
        let runtime =
            SolverRuntime::with_cache_directory(&options, directory.path(), ContentHash([75; 32]))
                .unwrap();
        let config = runtime.inner.cache.as_ref().unwrap();
        {
            let mut session =
                QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
            session
                .execute(&[ExecutionRoot {
                    node: NodeId(0),
                    receiver: SymbolId::NONE,
                }])
                .unwrap();
            assert_eq!(session.runtime_issue_sites.len(), 1);
            session.persist_completed().unwrap();
        }
        let reference = directory
            .path()
            .join(ref_name(config, graph.identity, &options));
        let initial = fs::read(&reference).unwrap();
        let schema = Schema::new(&facts, &graph, false).unwrap();
        let mut row = Writer(Vec::new());
        row.n(1);
        row.n(IssueKind::UnknownExecution as u32);
        row.operation(&schema, OperationId(0)).unwrap();
        row.n(RuntimeIssueReason::UnboundCallbackTarget as u32);
        let mut other_operation = Writer(Vec::new());
        other_operation.operation(&schema, OperationId(1)).unwrap();
        for corruption in 0..7 {
            rewrite(config, &graph, &options, |bytes| {
                let positions: Vec<_> = bytes
                    .windows(row.0.len())
                    .enumerate()
                    .filter_map(|(index, bytes)| (bytes == row.0).then_some(index))
                    .collect();
                assert_eq!(positions.len(), 1);
                let start = positions[0];
                match corruption {
                    0 => bytes[start..start + 4].copy_from_slice(&2u32.to_le_bytes()),
                    1 => bytes[start + 4..start + 8]
                        .copy_from_slice(&(IssueKind::UnresolvedSymbol as u32).to_le_bytes()),
                    2 => bytes[start + 8..start + 44].copy_from_slice(&other_operation.0),
                    3 => bytes[start + 44..start + 48].copy_from_slice(
                        &(RuntimeIssueReason::MissingExecutableBody as u32).to_le_bytes(),
                    ),
                    4 => bytes[start + 44..start + 48].copy_from_slice(
                        &(RuntimeIssueReason::UnknownOperation as u32).to_le_bytes(),
                    ),
                    5 => bytes[start + 44..start + 48].copy_from_slice(&u32::MAX.to_le_bytes()),
                    _ => {
                        assert_eq!(
                            u32::from_le_bytes(bytes[start - 8..start - 4].try_into().unwrap()),
                            1
                        );
                        bytes[start - 4..start]
                            .copy_from_slice(&(IssueKind::UnresolvedSymbol as u32).to_le_bytes());
                    }
                }
            });
            assert!(
                QuerySession::with_runtime(&facts, &graph, &options, &runtime).is_err(),
                "invalid runtime provenance {corruption} cannot expose a session"
            );
            fs::write(&reference, &initial).unwrap();
        }
    }
    #[test]
    fn observer_distinguishes_cold_warm_producer_rejection_and_write_skip() {
        let (facts, graph) = pure_fixture();
        let trace = Arc::new(Trace::default());
        let options = SolveOptions {
            workers: 1,
            observer: Some(trace.clone()),
            ..Default::default()
        };
        let directory = tempfile::tempdir().unwrap();
        let runtime =
            SolverRuntime::with_cache_directory(&options, directory.path(), ContentHash([41; 32]))
                .unwrap();
        let config = runtime.inner.cache.as_ref().unwrap();
        {
            let mut session =
                QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
            session
                .execute(&[ExecutionRoot {
                    node: NodeId(0),
                    receiver: SymbolId(0),
                }])
                .unwrap();
            session.persist_completed().unwrap();
        }
        {
            let session = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
            assert_eq!(session.reuse_metrics().loaded_contexts, 1);
            session.persist_completed().unwrap();
        }
        rewrite(config, &graph, &options, |bytes| bytes[4..36].fill(99));
        let session = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
        assert_eq!(session.reuse_metrics().loaded_contexts, 0);
        let events = trace.0.lock().unwrap();
        let stages: Vec<_> = events
            .iter()
            .map(|event| event.action)
            .filter(|action| {
                matches!(
                    action,
                    CacheAction::PreparingSchema
                        | CacheAction::Grouping
                        | CacheAction::Encoding
                        | CacheAction::Publishing
                        | CacheAction::Written
                )
            })
            .collect();
        assert_eq!(
            stages,
            [
                CacheAction::PreparingSchema,
                CacheAction::Grouping,
                CacheAction::Encoding,
                CacheAction::Publishing,
                CacheAction::Written
            ]
        );
        for (action, reason) in [
            (CacheAction::Miss, CacheReason::ReferenceAbsent),
            (CacheAction::Written, CacheReason::ExactSnapshot),
            (CacheAction::Hit, CacheReason::ExactSnapshot),
            (CacheAction::WriteSkipped, CacheReason::AlreadyWarm),
            (CacheAction::Rejected, CacheReason::ProducerMismatch),
        ] {
            assert!(
                events
                    .iter()
                    .any(|event| event.action == action && event.reason == reason),
                "missing {action:?}/{reason:?}"
            );
        }
        assert!(
            events
                .iter()
                .all(|event| event.identity.producer == config.producer
                    && event.identity.facts == facts.identity
                    && event.identity.graph == graph.identity)
        );
    }
    #[test]
    fn capped_save_keeps_only_proven_closed_pure_families() {
        let (facts, graph) = pure_fixture();
        let options = SolveOptions {
            workers: 1,
            ..Default::default()
        };
        let directory = tempfile::tempdir().unwrap();
        let runtime =
            SolverRuntime::with_cache_directory(&options, directory.path(), ContentHash([42; 32]))
                .unwrap();
        let roots = [
            ExecutionRoot {
                node: NodeId(0),
                receiver: SymbolId(0),
            },
            ExecutionRoot {
                node: NodeId(1),
                receiver: SymbolId(1),
            },
        ];
        {
            let mut session =
                QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
            session.execute(&roots).unwrap();
            assert!(session.contexts.iter().all(|context| context.evaluated));
            session.ready.push(ContextId(0));
            session.completion = Completion::ResourceLimited;
            session.sealed = false;
            session.persist_completed().unwrap();
        }
        let mut warm = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
        assert_eq!(warm.reuse_metrics().loaded_contexts, 1);
        assert_eq!(warm.contexts[0].key.node, NodeId(1));
        warm.execute(&roots).unwrap();
        assert_eq!(warm.contexts.len(), 2);
        // A closed writer cannot certify independence from future outside
        // readers/writers at a capped frontier; it is not saved as complete.
        let other = tempfile::tempdir().unwrap();
        let runtime =
            SolverRuntime::with_cache_directory(&options, other.path(), ContentHash([42; 32]))
                .unwrap();
        let mut session = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
        session.execute(&roots).unwrap();
        session.ready.push(ContextId(0));
        session.writes.insert((
            ContextId(1),
            Slot {
                kind: SlotKind::StaticField,
                owner: 1,
                member: 0,
            },
        ));
        session.completion = Completion::ResourceLimited;
        session.sealed = false;
        session.persist_completed().unwrap();
        assert_eq!(fs::read_dir(other.path()).unwrap().count(), 0);
    }
    #[test]
    fn negative_absence_requires_the_exact_declared_complete_root_frontier() {
        let (facts, graph) = pure_fixture();
        let roots = [
            ExecutionRoot {
                node: NodeId(0),
                receiver: SymbolId(0),
            },
            ExecutionRoot {
                node: NodeId(1),
                receiver: SymbolId(1),
            },
        ];
        let options = SolveOptions {
            workers: 1,
            execution_roots: Some(Arc::from(roots)),
            ..Default::default()
        };
        let directory = tempfile::tempdir().unwrap();
        let producer = ContentHash([44; 32]);
        let runtime =
            SolverRuntime::with_cache_directory(&options, directory.path(), producer).unwrap();
        {
            let mut session =
                QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
            session.execute(&roots).unwrap();
            let slot = Slot {
                kind: SlotKind::StaticField,
                owner: 0,
                member: 0,
            };
            session.slots.insert(
                slot,
                SlotValue {
                    value: Value {
                        set: SetId(0),
                        unknown: UNKNOWN_FIELD,
                    },
                    version: 1,
                },
            );
            session
                .dependencies
                .subscribe(
                    ContextId(0),
                    Read {
                        slot,
                        version: 1,
                        present: true,
                    },
                )
                .unwrap();
            session.field_reads.insert(slot);
            session.persist_completed().unwrap();
        }
        let same = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
        assert_eq!(same.reuse_metrics().loaded_families, 2);
        drop(same);
        for frontier in [Some(Arc::<[ExecutionRoot]>::from(vec![roots[0]])), None] {
            let options = SolveOptions {
                execution_roots: frontier,
                ..options.clone()
            };
            let runtime =
                SolverRuntime::with_cache_directory(&options, directory.path(), producer).unwrap();
            let session = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
            assert_eq!(
                session.reuse_metrics().loaded_families,
                1,
                "positive family remains independent"
            );
            assert_eq!(
                session.reuse_metrics().rejected_families,
                1,
                "unproven negative absence is recomputed"
            );
        }
    }
    #[test]
    fn atomic_reference_failure_is_observed_without_losing_completed_query() {
        let (facts, graph) = pure_fixture();
        let trace = Arc::new(Trace::default());
        let options = SolveOptions {
            workers: 1,
            observer: Some(trace.clone()),
            ..Default::default()
        };
        let directory = tempfile::tempdir().unwrap();
        let runtime =
            SolverRuntime::with_cache_directory(&options, directory.path(), ContentHash([43; 32]))
                .unwrap();
        let config = runtime.inner.cache.as_ref().unwrap();
        let mut session = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
        session
            .execute(&[ExecutionRoot {
                node: NodeId(0),
                receiver: SymbolId(0),
            }])
            .unwrap();
        session.persist_completed().unwrap();
        let reference = directory
            .path()
            .join(ref_name(config, graph.identity, &options));
        let before = fs::read(&reference).unwrap();
        let latest = directory.path().join(latest_name(config, &options));
        fs::remove_file(&latest).unwrap();
        fs::create_dir(&latest).unwrap();
        session.persist_completed().unwrap();
        assert_eq!(fs::read(reference).unwrap(), before);
        assert!(
            trace
                .0
                .lock()
                .unwrap()
                .iter()
                .any(|event| event.action == CacheAction::WriteSkipped
                    && event.reason == CacheReason::IoFailure)
        );
        assert!(!fs::read_dir(directory.path()).unwrap().any(|row| {
            row.unwrap()
                .file_name()
                .to_string_lossy()
                .starts_with(".summary-ref-")
        }));
        assert!(session.analyze(&[NodeId(0)]).is_ok());
    }
    fn fixture() -> (FactSnapshot, ProgramGraph) {
        let mut b = FactBuilder::new();
        for name in ["source", "target"] {
            b.ensure_symbol(name, FileId::NONE).unwrap();
        }
        let f = b.finish().unwrap();
        let mut g = ProgramGraph {
            facts_identity: f.identity,
            ..Default::default()
        };
        g.nodes = (0..2)
            .map(|i| NodeRecord {
                symbol: SymbolId(i),
                file: FileId::NONE,
                body: BodyId::NONE,
                flags: if i == 1 { NODE_EFFECTS_COMPLETE } else { 0 },
            })
            .collect();
        g.symbol_nodes = vec![NodeId(0), NodeId(1)];
        g.edges.push(EdgeRecord {
            source: NodeId(0),
            target: NodeId(1),
            kind: EdgeKind::Call,
            operation: OperationId::NONE,
            receiver: SymbolId::NONE,
            occurrence: OccurrenceId::NONE,
            flags: 0,
        });
        g.index().unwrap();
        (f, g)
    }
    #[test]
    fn resealed_metadata_obligation_is_rejected_without_runtime_site_help() {
        let (facts, mut graph) = fixture();
        graph.edges[0].flags |= EDGE_UNKNOWN;
        let options = SolveOptions {
            workers: 1,
            ..Default::default()
        };
        let directory = tempfile::tempdir().unwrap();
        let runtime =
            SolverRuntime::with_cache_directory(&options, directory.path(), ContentHash([171; 32]))
                .unwrap();
        let config = runtime.inner.cache.as_ref().unwrap();
        {
            let mut session =
                QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
            session
                .execute(&[ExecutionRoot {
                    node: NodeId(0),
                    receiver: SymbolId(0),
                }])
                .unwrap();
            assert!(
                session
                    .issues
                    .iter()
                    .any(|issue| issue.kind == IssueKind::UnknownExecution)
            );
            session.runtime_issue_sites.clear();
            session.persist_completed().unwrap();
        }
        let positive = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
        assert!(positive.reuse_metrics().loaded_contexts > 0);
        assert!(
            positive
                .issues
                .iter()
                .any(|issue| issue.kind == IssueKind::UnknownExecution)
        );
        drop(positive);
        rewrite(config, &graph, &options, |bytes| {
            let needle: Vec<_> = [1u32, IssueKind::UnknownExecution as u32, 0]
                .into_iter()
                .flat_map(u32::to_le_bytes)
                .collect();
            let hits: Vec<_> = bytes
                .windows(needle.len())
                .enumerate()
                .filter_map(|(i, row)| (row == needle).then_some(i))
                .collect();
            assert_eq!(
                hits.len(),
                1,
                "the one stored obligation has no runtime site"
            );
            let at = hits[0] + 4;
            bytes[at..at + 4]
                .copy_from_slice(&(IssueKind::IncompleteHierarchy as u32).to_le_bytes());
        });
        assert!(matches!(
            QuerySession::with_runtime(&facts, &graph, &options, &runtime),
            Err(Error::Invalid(
                "metadata issue in cached execution obligations"
            ))
        ));
    }
    pub(super) fn rewrite(
        config: &CacheConfig,
        g: &ProgramGraph,
        options: &SolveOptions,
        change: impl FnOnce(&mut Vec<u8>),
    ) {
        let reference = config.directory.join(ref_name(config, g.identity, options));
        let name = fs::read_to_string(&reference).unwrap();
        let a =
            selector_artifacts::open(&config.directory.join(name.trim()), ArtifactKind::Summaries)
                .unwrap();
        let mut bytes = a.section(1).unwrap().to_vec();
        change(&mut bytes);
        let saved = selector_artifacts::publish(
            &config.directory,
            ArtifactKind::Summaries,
            &[Section {
                id: 1,
                count: a.count(1).unwrap(),
                bytes: &bytes,
            }],
        )
        .unwrap();
        let name = saved.path.file_name().unwrap().to_str().unwrap();
        write_ref(
            &config.directory,
            reference.file_name().unwrap().to_str().unwrap(),
            name,
        )
        .unwrap();
    }
    #[test]
    fn exact_admission_verifies_numeric_ids_and_complete_content_before_import() {
        let (facts, graph) = fixture();
        let options = SolveOptions {
            workers: 1,
            ..Default::default()
        };
        let dir = tempfile::tempdir().unwrap();
        let producer = ContentHash([93; 32]);
        let config = CacheConfig {
            directory: dir.path().to_owned(),
            producer,
        };
        let runtime = SolverRuntime::with_cache_directory(&options, dir.path(), producer).unwrap();
        let original;
        {
            let mut q = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
            q.execute(&[ExecutionRoot {
                node: NodeId(0),
                receiver: SymbolId(0),
            }])
            .unwrap();
            original = q.analyze(&[NodeId(1)]).unwrap();
            q.persist_completed().unwrap();
        }
        let reference = config
            .directory
            .join(ref_name(&config, graph.identity, &options));
        let initial_ref = fs::read(&reference).unwrap();
        {
            let mut q = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
            assert!(q.reuse_metrics().same_snapshot);
            assert_eq!(q.reuse_metrics().loaded_contexts, 2);
            let restored = q.analyze(&[NodeId(1)]).unwrap();
            assert_eq!(q.metrics().edge_visits, 0);
            assert_eq!(restored.affected, original.affected);
            assert_eq!(restored.witnesses, original.witnesses);
            assert_eq!(restored.evidence.atoms, original.evidence.atoms);
            assert_eq!(restored.evidence.values, original.evidence.values);
            assert_eq!(restored.evidence.contexts, original.evidence.contexts);
            assert_eq!(restored.evidence.witnesses, original.evidence.witnesses);
        }
        for id in [1, u32::MAX - 1] {
            // Header204B + familylength8 + contextcount4 + manifestcount4 + key32.
            rewrite(&config, &graph, &options, |bytes| {
                bytes[252..256].copy_from_slice(&id.to_le_bytes())
            });
            assert!(
                QuerySession::with_runtime(&facts, &graph, &options, &runtime).is_err(),
                "malformed numeric/key pair {id}"
            );
            fs::write(&reference, &initial_ref).unwrap();
        }
        rewrite(&config, &graph, &options, |bytes| {
            bytes[4..36].copy_from_slice(&[19; 32])
        });
        let q = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
        assert_eq!(
            q.reuse_metrics().loaded_contexts,
            0,
            "different producer cannot admit cached state"
        );
        drop(q);
        fs::write(&reference, &initial_ref).unwrap();
        for version in [8u32, 9] {
            rewrite(&config, &graph, &options, |bytes| {
                bytes[..4].copy_from_slice(&version.to_le_bytes())
            });
            let q = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
            assert_eq!(
                q.reuse_metrics().loaded_contexts,
                0,
                "old bound wire v{version} is a clean miss under runtime-site wire v10"
            );
            drop(q);
            fs::write(&reference, &initial_ref).unwrap();
        }
        let mut changed = facts;
        changed.symbols[0].properties ^= 32;
        assert!(matches!(
            QuerySession::with_runtime(&changed, &graph, &options, &runtime),
            Err(Error::Invalid("summary snapshot content seal"))
        ));
        changed.symbols[0].properties ^= 32;
        let mut changed_graph = graph;
        changed_graph.edges[0].flags ^= EDGE_EFFECTS_COMPLETE;
        assert!(matches!(
            QuerySession::with_runtime(&changed, &changed_graph, &options, &runtime),
            Err(Error::Invalid("summary snapshot content seal"))
        ));
    }
    #[test]
    fn compilation_edges_do_not_prevent_bounded_execution_cache_reuse() {
        let (facts, mut graph) = fixture();
        for flags in 0..8192 {
            graph.edges.push(EdgeRecord {
                source: NodeId(0),
                target: NodeId(1),
                kind: EdgeKind::Compile,
                operation: OperationId::NONE,
                receiver: SymbolId::NONE,
                occurrence: OccurrenceId::NONE,
                // Keep 8,192 distinct compile-only payloads outside reserved
                // execution flags, including receiver-scoped Guard authority.
                flags: flags << 6,
            });
        }
        graph.index().unwrap();
        let options = SolveOptions {
            workers: 2,
            memory_budget_bytes: 128 * 1024,
            scratch_bytes_per_worker: 4096,
            ..Default::default()
        };
        assert!(
            graph.edges.len() * 128 > options.memory_budget_bytes,
            "the old whole-graph estimate rejected this input"
        );
        let directory = tempfile::tempdir().unwrap();
        let producer = ContentHash([74; 32]);
        let runtime =
            SolverRuntime::with_cache_directory(&options, directory.path(), producer).unwrap();
        let original;
        {
            let mut q = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
            q.execute(&[ExecutionRoot {
                node: NodeId(0),
                receiver: SymbolId(0),
            }])
            .unwrap();
            original = q.analyze(&[NodeId(1)]).unwrap();
            assert!(metadata_fits(&q, false, 0));
            q.persist_completed().unwrap();
        }
        let config = runtime.inner.cache.as_ref().unwrap();
        let reference = directory
            .path()
            .join(ref_name(config, graph.identity, &options));
        assert!(reference.is_file(), "the bounded cold query must persist");
        let mut warm = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
        assert_eq!(warm.reuse_metrics().loaded_contexts, 2);
        let restored = warm.analyze(&[NodeId(1)]).unwrap();
        assert_eq!(warm.metrics().edge_visits, 0);
        assert_eq!(restored.affected, original.affected);
        assert_eq!(restored.witnesses, original.witnesses);
        assert_eq!(restored.evidence.contexts, original.evidence.contexts);
        assert_eq!(restored.evidence.witnesses, original.evidence.witnesses);
        assert!(warm.owned_bytes() <= options.memory_budget_bytes);
    }
    #[test]
    fn exact_referenced_keys_match_rebase_keys_without_a_whole_program_key_map() {
        let (facts, mut graph) = fixture();
        graph.nodes.push(graph.nodes[0]);
        graph.index().unwrap();
        let schema = Schema::new(&facts, &graph, false).unwrap();
        let mut exact = exact::ExactProgram::new(&facts, &graph);
        assert_eq!(
            exact.symbol(SymbolId(0)).unwrap(),
            schema.symbol(SymbolId(0))
        );
        for i in 0..graph.nodes.len() {
            assert_eq!(exact.node(NodeId(i as u32)).unwrap(), schema.nodes[i]);
        }
        assert_eq!(
            exact.edge(EdgeId(0)).unwrap(),
            schema.edge(EdgeId(0)).unwrap()
        );
        assert!(exact.edge(EdgeId(1)).is_err());
        let mut admission = Admission::Exact(exact);
        let mut w = Writer(Vec::new());
        w.reference(schema.symbol(SymbolId(0)), 1);
        assert!(admission.symbol(&mut Reader::new(&w.0)).is_err());
        let mut w = Writer(Vec::new());
        w.reference(schema.edge(EdgeId(0)).unwrap(), u32::MAX - 1);
        assert!(admission.edge(&mut Reader::new(&w.0)).is_err());
        let mut w = Writer(Vec::new());
        w.reference(ZERO, 0);
        assert!(admission.operation(&mut Reader::new(&w.0)).is_err());
    }
    #[test]
    fn cache_schema_indexes_only_execution_and_only_the_required_direction() {
        let mut b = FactBuilder::new();
        for name in ["source", "target"] {
            b.ensure_symbol(name, FileId::NONE).unwrap();
        }
        let facts = b.finish().unwrap();
        let mut graph = ProgramGraph::default();
        graph.nodes = (0..2)
            .map(|i| NodeRecord {
                symbol: SymbolId(i),
                file: FileId::NONE,
                body: BodyId::NONE,
                flags: 0,
            })
            .collect();
        graph.symbol_nodes = vec![NodeId(0), NodeId(1)];
        let edge = EdgeRecord {
            source: NodeId(0),
            target: NodeId(1),
            kind: EdgeKind::Compile,
            operation: OperationId::NONE,
            receiver: SymbolId::NONE,
            occurrence: OccurrenceId::NONE,
            flags: 0,
        };
        graph.edges = vec![edge; 4096];
        graph.edges.extend([
            EdgeRecord {
                kind: EdgeKind::Call,
                ..edge
            },
            EdgeRecord {
                kind: EdgeKind::Initialize,
                ..edge
            },
        ]);
        graph.index().unwrap();
        let encode = Schema::new(&facts, &graph, false).unwrap();
        assert_eq!(encode.edges.len(), 2);
        assert!(
            encode.symbol_map.is_empty()
                && encode.node_map.is_empty()
                && encode.op_map.is_empty()
                && encode.edge_map.is_empty()
        );
        assert!(encode.edge(EdgeId(0)).is_err());
        let decode = Schema::new(&facts, &graph, true).unwrap();
        assert_eq!(decode.edge_map.len(), 2);
        assert!(
            decode.symbols.is_empty()
                && decode.nodes.is_empty()
                && decode.ops.is_empty()
                && decode.edges.is_empty()
                && decode.edge_slots.is_empty()
        );
        assert_eq!(
            decode.edge_map[&encode.edge(EdgeId(4096)).unwrap()],
            EdgeId(4096)
        );
        assert_eq!(
            decode.edge_map[&encode.edge(EdgeId(4097)).unwrap()],
            EdgeId(4097)
        );
        assert_eq!(decode.fingerprints, encode.fingerprints);
    }
}
