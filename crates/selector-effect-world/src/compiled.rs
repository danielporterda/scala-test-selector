use selector_compiled_products as p;
use selector_facts::{FactSnapshot, FileRecord, SuiteRecord};
use selector_graph::ProgramGraph;
use selector_types::*;
use sha2::{Digest, Sha256};
use std::mem::size_of;

#[derive(Clone, Copy, Debug)]
pub struct SnapshotPins {
    pub facts: ContentHash,
    pub graph: ContentHash,
    /// None explicitly means no admitted auxiliary runtime input.
    pub runtime: Option<ContentHash>,
}
/// Immutable borrowed input after one geometry and exact identity check. It is
/// not a substitute for the supervising physical artifact/producers admission.
#[derive(Clone, Copy)]
pub struct ValidatedSnapshot<'a> {
    facts: &'a FactSnapshot,
    graph: &'a ProgramGraph,
    pins: SnapshotPins,
}
impl<'a> ValidatedSnapshot<'a> {
    pub fn new(
        facts: &'a FactSnapshot,
        graph: &'a ProgramGraph,
        pins: SnapshotPins,
    ) -> Result<Self, Error> {
        if pins.facts == ContentHash::default()
            || pins.graph == ContentHash::default()
            || pins.facts != facts.identity
            || pins.graph != graph.identity
            || graph.facts_identity != facts.identity
        {
            return Err(Error::Invalid("world snapshot identity"));
        }
        match pins.runtime {
            Some(h) if h != ContentHash::default() && h == graph.runtime_identity => (),
            None if graph.runtime_identity == ContentHash::default() => (),
            _ => return Err(Error::Invalid("world runtime identity")),
        }
        facts.validate()?;
        graph.validate()?;
        let sym = |id: SymbolId| id.is_none() || id.index() < facts.symbols.len();
        let file = |id: FileId| id.is_none() || id.index() < facts.files.len();
        for n in &graph.nodes {
            if !sym(n.symbol) || !file(n.file) {
                return Err(Error::Invalid("world graph fact reference"));
            }
            if !n.body.is_none() {
                let b = facts
                    .bodies
                    .get(n.body.index())
                    .ok_or(Error::Invalid("world graph body"))?;
                if b.symbol != n.symbol || b.file != n.file {
                    return Err(Error::Invalid("world graph body owner"));
                }
            }
        }
        for e in &graph.edges {
            if !sym(e.receiver)
                || (!e.operation.is_none() && e.operation.index() >= facts.operations.len())
                || (!e.occurrence.is_none() && e.occurrence.index() >= facts.occurrences.len())
            {
                return Err(Error::Invalid("world graph edge fact reference"));
            }
        }
        for i in &graph.issues {
            if !sym(i.symbol)
                || !file(i.file)
                || (!i.detail.is_none() && i.detail.index() >= facts.strings.len())
            {
                return Err(Error::Invalid("world graph issue fact reference"));
            }
        }
        for i in &graph.diagnostics {
            if !sym(i.symbol) || !file(i.file) {
                return Err(Error::Invalid("world graph diagnostic fact reference"));
            }
        }
        if graph.symbol_nodes.len() > facts.symbols.len() {
            return Err(Error::Invalid("world graph symbol map"));
        }
        Ok(Self { facts, graph, pins })
    }
    pub fn facts(&self) -> &'a FactSnapshot {
        self.facts
    }
    pub fn graph(&self) -> &'a ProgramGraph {
        self.graph
    }
    pub fn pins(&self) -> SnapshotPins {
        self.pins
    }
}
#[derive(Clone, Copy, Debug)]
pub struct ProductPins {
    pub manifest: p::Hash,
    pub contexts: p::Hash,
    pub documents: p::Hash,
}
#[derive(Clone, Copy, Debug)]
pub struct BindingLimits {
    pub max_roots: usize,
    pub max_seed_rows: usize,
    pub max_seed_methods: usize,
    pub max_delta_rows: usize,
    pub max_bytes: usize,
}
impl Default for BindingLimits {
    fn default() -> Self {
        Self {
            max_roots: 100_000,
            max_seed_rows: 100_000,
            max_seed_methods: 2_000_000,
            max_delta_rows: 100_000,
            max_bytes: 128 << 20,
        }
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PendingBinding {
    CatalogueUnresolved,
    MissingSourceFile,
    UnverifiedSource,
    MissingContext,
    CompositeContext,
    CompilerClassUnverified,
    UnsupportedCompilerClass,
    MissingProductSource,
    SourceHashMismatch,
    MissingSemanticDb,
    CompiledEntry(p::Pending),
}
#[derive(Clone, Copy, Debug)]
pub struct CompiledRoot {
    pub source: p::SourceId,
    pub class: p::ClassId,
    pub entry: p::MethodId,
    pub kind: p::RootKind,
    /// Enter this class's verified initialization phase as well as the ctor. This
    /// is a demand, not a claim that missing parent/default-interface effects empty.
    pub initialize_class: p::ClassId,
}
#[derive(Clone, Copy, Debug)]
pub enum RootBinding {
    Bound(CompiledRoot),
    Pending(PendingBinding),
}
#[derive(Clone, Copy, Debug)]
pub struct RootRow {
    pub suite: u32,
    pub symbol: SymbolId,
    pub file: FileId,
    pub graph_node: NodeId,
    pub binding: RootBinding,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct RootKey<'a> {
    pub name: &'a str,
    pub context: &'a str,
    pub compiler_class: &'a str,
}
impl RootKey<'_> {
    pub fn digest(self) -> ContentHash {
        let mut h = Sha256::new();
        h.update(b"selector-compiled-root-key/v1\0");
        for text in [self.name, self.context, self.compiler_class] {
            h.update((text.len() as u64).to_le_bytes());
            h.update(text.as_bytes());
        }
        ContentHash(h.finalize().into())
    }
}
/// One row for every captured suite, including unresolved entries. Numeric rows
/// borrow the original facts/product text pools; no per-root string is retained.
pub struct CompiledCatalogue<'f, 'p> {
    snapshot: ValidatedSnapshot<'f>,
    products: &'p p::VerifiedBinding,
    roots: Vec<RootRow>,
    root_order: Vec<u32>,
    files: Vec<FileId>,
    owned_bytes: usize,
}
fn bytes(rows: usize, size: usize) -> Result<usize, Error> {
    rows.checked_mul(size)
        .ok_or(Error::Limit("world binding bytes"))
}
fn reserve<T>(v: &mut Vec<T>, n: usize) -> Result<(), Error> {
    v.try_reserve_exact(n)
        .map_err(|_| Error::Limit("world binding allocation"))
}
fn source_verified(file: FileRecord) -> bool {
    file.flags & SOURCE_VERIFIED != 0
        && file.flags & FILE_BINARY_SOURCE == 0
        && !file.source.is_none()
        && file.source_hash != ContentHash::default()
}
fn source_key(facts: &FactSnapshot, id: FileId) -> (&str, &str) {
    let f = facts.files[id.index()];
    (facts.text(f.context), facts.text(f.path))
}
fn root_key(facts: &FactSnapshot, s: SuiteRecord) -> RootKey<'_> {
    let (context, class) = if s.symbol.is_none() {
        ("", "")
    } else {
        let symbol = facts.symbols[s.symbol.index()];
        let context = if !symbol.context.is_none() {
            facts.text(symbol.context)
        } else if !s.file.is_none() {
            facts.text(facts.files[s.file.index()].context)
        } else {
            ""
        };
        (context, facts.symbol_name(s.symbol))
    };
    RootKey {
        name: facts.text(s.name),
        context,
        compiler_class: class,
    }
}
impl<'f, 'p> CompiledCatalogue<'f, 'p> {
    pub fn bind(
        snapshot: &ValidatedSnapshot<'f>,
        products: &'p p::VerifiedBinding,
        pins: ProductPins,
        limits: BindingLimits,
    ) -> Result<Self, Error> {
        if pins.manifest == [0; 32]
            || pins.contexts == [0; 32]
            || pins.documents == [0; 32]
            || pins.manifest != products.identity()
            || pins.contexts != products.contexts_identity()
            || pins.documents != products.documents_identity()
        {
            return Err(Error::Invalid("world product input identity"));
        }
        let facts = snapshot.facts;
        let mut name_capacity = 0usize;
        for s in &facts.suites {
            if !s.symbol.is_none() {
                name_capacity = name_capacity.max(
                    facts
                        .symbol_name(s.symbol)
                        .len()
                        .checked_add(1)
                        .ok_or(Error::Limit("world class name"))?,
                );
            }
        }
        let max_bytes = bytes(facts.suites.len(), size_of::<RootRow>() + 4)?
            .checked_add(bytes(facts.files.len(), 4)?)
            .and_then(|b| b.checked_add(name_capacity))
            .ok_or(Error::Limit("world catalogue bytes"))?;
        if facts.suites.len() > limits.max_roots
            || max_bytes > limits.max_bytes
            || facts.suites.len() >= u32::MAX as usize
        {
            return Err(Error::Limit("world catalogue preflight"));
        }
        let mut out = Self {
            snapshot: *snapshot,
            products,
            roots: Vec::new(),
            root_order: Vec::new(),
            files: Vec::new(),
            owned_bytes: max_bytes,
        };
        reserve(&mut out.roots, facts.suites.len())?;
        reserve(&mut out.root_order, facts.suites.len())?;
        reserve(&mut out.files, facts.files.len())?;
        let mut scratch = String::new();
        scratch
            .try_reserve_exact(name_capacity)
            .map_err(|_| Error::Limit("world module class scratch"))?;
        for (i, suite) in facts.suites.iter().copied().enumerate() {
            let binding = out.bind_root(suite, &mut scratch);
            out.roots.push(RootRow {
                suite: i as u32,
                symbol: suite.symbol,
                file: suite.file,
                graph_node: snapshot
                    .graph
                    .node_for_symbol(suite.symbol)
                    .unwrap_or(NodeId::NONE),
                binding,
            });
            out.root_order.push(i as u32);
        }
        out.root_order.sort_unstable_by(|a, b| {
            root_key(facts, facts.suites[*a as usize])
                .cmp(&root_key(facts, facts.suites[*b as usize]))
        });
        if out.root_order.windows(2).any(|p| {
            root_key(facts, facts.suites[p[0] as usize])
                == root_key(facts, facts.suites[p[1] as usize])
        }) {
            return Err(Error::Invalid("ambiguous compiled root key"));
        }
        out.files.extend(
            facts
                .files
                .iter()
                .enumerate()
                .filter(|(_, f)| f.flags & FILE_BINARY_SOURCE == 0)
                .map(|(i, _)| FileId(i as u32)),
        );
        out.files
            .sort_unstable_by(|a, b| source_key(facts, *a).cmp(&source_key(facts, *b)));
        if out
            .files
            .windows(2)
            .any(|p| source_key(facts, p[0]) == source_key(facts, p[1]))
        {
            return Err(Error::Invalid("ambiguous source file context/path"));
        }
        Ok(out)
    }
    fn bind_root(&self, suite: SuiteRecord, scratch: &mut String) -> RootBinding {
        let pending = |p| RootBinding::Pending(p);
        if suite.flags & EDGE_UNKNOWN != 0 || suite.symbol.is_none() {
            return pending(PendingBinding::CatalogueUnresolved);
        }
        if suite.file.is_none() {
            return pending(PendingBinding::MissingSourceFile);
        }
        let facts = self.snapshot.facts;
        let symbol = facts.symbols[suite.symbol.index()];
        let file = facts.files[suite.file.index()];
        if !source_verified(file) {
            return pending(PendingBinding::UnverifiedSource);
        }
        if symbol.flags & SYMBOL_DEFINED == 0 || symbol.file != suite.file {
            return pending(PendingBinding::CompilerClassUnverified);
        }
        let key = root_key(facts, suite);
        if key.context.is_empty() {
            return pending(PendingBinding::MissingContext);
        }
        if key.context.contains('\0') {
            return pending(PendingBinding::CompositeContext);
        }
        if facts.text(file.context) != key.context {
            return pending(PendingBinding::CompilerClassUnverified);
        }
        let kind = match symbol.kind {
            13 => p::RootKind::Class,
            10 => p::RootKind::Module,
            _ => return pending(PendingBinding::UnsupportedCompilerClass),
        };
        let tail = match kind {
            p::RootKind::Class => '#',
            p::RootKind::Module => '.',
        };
        let Some(raw) = key.compiler_class.strip_suffix(tail) else {
            return pending(PendingBinding::UnsupportedCompilerClass);
        };
        // Only the exact top-level descriptor grammar is licensed. Encoded/nested
        // compiler-to-JVM names need an independently admitted bridge, not rfind().
        if raw.is_empty()
            || !raw
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'/' | b'_' | b'$'))
            || selector_types::symbol::global_owner(key.compiler_class)
                .is_none_or(|owner| !owner.ends_with('/'))
        {
            return pending(PendingBinding::UnsupportedCompilerClass);
        }
        let path = facts.text(file.path);
        let Some(source) = self.products.find_source(key.context, path) else {
            return pending(PendingBinding::MissingProductSource);
        };
        let proof = self.products.source(source).expect("admitted source id");
        if proof.source_sha256 != file.source_hash.0 {
            return pending(PendingBinding::SourceHashMismatch);
        }
        if !proof.semantic_db_verified {
            return pending(PendingBinding::MissingSemanticDb);
        }
        let jvm = if kind == p::RootKind::Module {
            scratch.clear();
            scratch.push_str(raw);
            scratch.push('$');
            scratch.as_str()
        } else {
            raw
        };
        match self.products.root_entry(key.context, path, jvm, kind) {
            Ok(entry) => RootBinding::Bound(CompiledRoot {
                source: entry.source,
                class: entry.class,
                entry: entry.entry,
                kind: entry.kind,
                initialize_class: entry.class,
            }),
            Err(why) => pending(PendingBinding::CompiledEntry(why)),
        }
    }
    pub fn snapshot(&self) -> ValidatedSnapshot<'f> {
        self.snapshot
    }
    pub fn products(&self) -> &'p p::VerifiedBinding {
        self.products
    }
    pub fn roots(&self) -> &[RootRow] {
        &self.roots
    }
    pub fn root_order(&self) -> &[u32] {
        &self.root_order
    }
    pub fn owned_bytes(&self) -> usize {
        self.owned_bytes
    }
    pub fn key(&self, root: u32) -> Option<RootKey<'f>> {
        let row = self.roots.get(root as usize)?;
        Some(root_key(
            self.snapshot.facts,
            self.snapshot.facts.suites[row.suite as usize],
        ))
    }
    pub fn entry_method(&self, root: u32) -> Option<p::MethodView<'p>> {
        match self.roots.get(root as usize)?.binding {
            RootBinding::Bound(r) => self.products.method(r.entry),
            RootBinding::Pending(_) => None,
        }
    }
    fn source_binding(
        &self,
        context: &str,
        path: &str,
    ) -> Result<(FileId, p::SourceId, usize), PendingBinding> {
        if context.is_empty() {
            return Err(PendingBinding::MissingContext);
        }
        if context.contains('\0') {
            return Err(PendingBinding::CompositeContext);
        }
        let facts = self.snapshot.facts;
        let i = self
            .files
            .binary_search_by(|id| source_key(facts, *id).cmp(&(context, path)))
            .map_err(|_| PendingBinding::MissingSourceFile)?;
        let file = self.files[i];
        let row = facts.files[file.index()];
        if !source_verified(row) {
            return Err(PendingBinding::UnverifiedSource);
        }
        let source = self
            .products
            .find_source(context, path)
            .ok_or(PendingBinding::MissingProductSource)?;
        let proof = self.products.source(source).expect("admitted source");
        if proof.source_sha256 != row.source_hash.0 {
            return Err(PendingBinding::SourceHashMismatch);
        }
        if !proof.semantic_db_verified {
            return Err(PendingBinding::MissingSemanticDb);
        }
        Ok((file, source, proof.methods))
    }
    pub fn bind_requested(
        &self,
        requests: &[RequestedSource<'_>],
        limits: BindingLimits,
    ) -> Result<RequestedBindings, Error> {
        let mut count = 0usize;
        for request in requests {
            if let Ok((_, _, n)) = self.source_binding(request.context, request.path) {
                count = count
                    .checked_add(n)
                    .ok_or(Error::Limit("world seed count"))?;
            }
        }
        let needed = bytes(requests.len(), size_of::<SeedRow>())?
            .checked_add(bytes(count, size_of::<p::MethodId>())?)
            .ok_or(Error::Limit("world seed bytes"))?;
        if requests.len() > limits.max_seed_rows
            || count > limits.max_seed_methods
            || needed > limits.max_bytes
            || requests.len() >= u32::MAX as usize
        {
            return Err(Error::Limit("world seed preflight"));
        }
        let mut rows = Vec::new();
        let mut methods = Vec::new();
        reserve(&mut rows, requests.len())?;
        reserve(&mut methods, count)?;
        for (i, request) in requests.iter().enumerate() {
            let (file, binding) = match self.source_binding(request.context, request.path) {
                Ok((file, source, count)) => {
                    methods.extend(
                        self.products
                            .changed_methods(source)
                            .map_err(|_| Error::Invalid("world admitted source changed"))?,
                    );
                    (
                        file,
                        SeedBinding::Bound {
                            source,
                            methods: count as u32,
                        },
                    )
                }
                Err(p) => (FileId::NONE, SeedBinding::Pending(p)),
            };
            rows.push(SeedRow {
                request: i as u32,
                file,
                binding,
            });
        }
        methods.sort_unstable_by_key(|m| m.0);
        methods.dedup();
        Ok(RequestedBindings {
            rows,
            methods,
            owned_bytes: needed,
        })
    }
}
#[derive(Clone, Copy, Debug)]
pub struct RequestedSource<'a> {
    pub context: &'a str,
    pub path: &'a str,
}
#[derive(Clone, Copy, Debug)]
pub enum SeedBinding {
    Bound { source: p::SourceId, methods: u32 },
    Pending(PendingBinding),
}
#[derive(Clone, Copy, Debug)]
pub struct SeedRow {
    pub request: u32,
    pub file: FileId,
    pub binding: SeedBinding,
}
/// This is explicitly a requested-source subset, never whole-checkout coverage.
pub struct RequestedBindings {
    rows: Vec<SeedRow>,
    methods: Vec<p::MethodId>,
    owned_bytes: usize,
}
impl RequestedBindings {
    pub fn rows(&self) -> &[SeedRow] {
        &self.rows
    }
    pub fn methods(&self) -> &[p::MethodId] {
        &self.methods
    }
    pub fn owned_bytes(&self) -> usize {
        self.owned_bytes
    }
    pub fn all_requested_bound(&self) -> bool {
        self.rows
            .iter()
            .all(|r| matches!(r.binding, SeedBinding::Bound { .. }))
    }
}
#[derive(Clone, Copy, Debug)]
pub struct SourceDeltaRow {
    pub base_file: FileId,
    pub head_file: FileId,
    pub base_pending: Option<PendingBinding>,
    pub head_pending: Option<PendingBinding>,
}
/// All captured nonbinary source file/context deltas, separately from requested
/// subsets. Native/runtime/catalogue changes remain outside this type's scope.
pub struct CapturedSourceDelta {
    rows: Vec<SourceDeltaRow>,
}
impl CapturedSourceDelta {
    pub fn rows(&self) -> &[SourceDeltaRow] {
        &self.rows
    }
    pub fn all_changed_sources_bound(&self) -> bool {
        self.rows
            .iter()
            .all(|r| r.base_pending.is_none() && r.head_pending.is_none())
    }
}
pub fn compare_captured_sources(
    base: &CompiledCatalogue<'_, '_>,
    head: &CompiledCatalogue<'_, '_>,
    limits: BindingLimits,
) -> Result<CapturedSourceDelta, Error> {
    fn walk(
        base: &CompiledCatalogue<'_, '_>,
        head: &CompiledCatalogue<'_, '_>,
        mut visit: impl FnMut(FileId, FileId) -> Result<(), Error>,
    ) -> Result<(), Error> {
        let (mut a, mut b) = (0, 0);
        while a < base.files.len() || b < head.files.len() {
            let x = base.files.get(a).copied();
            let y = head.files.get(b).copied();
            let cmp = match (x, y) {
                (Some(x), Some(y)) => {
                    source_key(base.snapshot.facts, x).cmp(&source_key(head.snapshot.facts, y))
                }
                (Some(_), None) => std::cmp::Ordering::Less,
                (None, Some(_)) => std::cmp::Ordering::Greater,
                (None, None) => break,
            };
            match cmp {
                std::cmp::Ordering::Less => {
                    visit(x.unwrap(), FileId::NONE)?;
                    a += 1
                }
                std::cmp::Ordering::Greater => {
                    visit(FileId::NONE, y.unwrap())?;
                    b += 1
                }
                std::cmp::Ordering::Equal => {
                    let (x, y) = (x.unwrap(), y.unwrap());
                    let f = base.snapshot.facts.files[x.index()];
                    let g = head.snapshot.facts.files[y.index()];
                    if f.source_hash != g.source_hash || !source_verified(f) || !source_verified(g)
                    {
                        visit(x, y)?
                    }
                    a += 1;
                    b += 1
                }
            }
        }
        Ok(())
    }
    let mut count = 0usize;
    walk(base, head, |_, _| {
        count = count
            .checked_add(1)
            .ok_or(Error::Limit("world source delta rows"))?;
        Ok(())
    })?;
    if count > limits.max_delta_rows
        || bytes(count, size_of::<SourceDeltaRow>())? > limits.max_bytes
    {
        return Err(Error::Limit("world source delta preflight"));
    }
    let mut rows = Vec::new();
    reserve(&mut rows, count)?;
    walk(base, head, |a, b| {
        let pending = |c: &CompiledCatalogue<'_, '_>, id: FileId| {
            if id.is_none() {
                None
            } else {
                let (context, path) = source_key(c.snapshot.facts, id);
                c.source_binding(context, path).err()
            }
        };
        rows.push(SourceDeltaRow {
            base_file: a,
            head_file: b,
            base_pending: pending(base, a),
            head_pending: pending(head, b),
        });
        Ok(())
    })?;
    Ok(CapturedSourceDelta { rows })
}
