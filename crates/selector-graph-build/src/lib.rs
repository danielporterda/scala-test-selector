//! Parallel construction of immutable program relationships. All temporary
//! indexes belong to one build; graph readers retain only flat records and CSR.
use rayon::prelude::*;
use selector_facts::{BodyRecord, FactSnapshot, OperationRecord};
use selector_graph::{EdgeRecord, GraphDiagnostic, GraphIssue, NodeRecord, ProgramGraph};
use selector_types::*;
use sha2::{Digest, Sha256};
pub mod binary_capture;
pub mod binary_inputs;
pub mod binary_lower;
pub mod binary_platform;
pub mod binary_resolve;
pub mod runtime_inputs;
pub mod source_recipes;

#[derive(Clone, Debug)]
pub struct BuildOptions {
    pub workers: usize,
    pub include_models: bool,
}
impl Default for BuildOptions {
    fn default() -> Self {
        Self {
            workers: std::thread::available_parallelism().map_or(1, usize::from),
            include_models: true,
        }
    }
}

/// Dense relation adjacency: two allocations regardless of the symbol count.
struct Adjacency {
    offsets: Vec<usize>,
    values: Vec<SymbolId>,
}

/// Sparse postings only when enrichment retained a dispatch frontier. Ancestor
/// method links protect calls compiled against an inherited concrete target.
struct DispatchFrontiers {
    receivers: Vec<(SymbolId, SymbolId)>,
    parents: Vec<(SymbolId, SymbolId)>,
}
impl DispatchFrontiers {
    fn new(facts: &FactSnapshot) -> Option<Self> {
        let mut receivers: Vec<_> = facts
            .relations
            .iter()
            .filter(|r| r.kind == RelationKind::DeferredDispatch)
            .map(|r| (r.target, r.source))
            .collect();
        if receivers.is_empty() {
            return None;
        }
        receivers.sort_unstable();
        receivers.dedup();
        let mut parents: Vec<_> = facts
            .relations
            .iter()
            .filter(|r| r.kind == RelationKind::Override)
            .map(|r| (r.source, r.target))
            .collect();
        parents.sort_unstable();
        parents.dedup();
        Some(Self { receivers, parents })
    }
    fn get(rows: &[(SymbolId, SymbolId)], key: SymbolId) -> &[(SymbolId, SymbolId)] {
        let begin = rows.partition_point(|r| r.0 < key);
        let end = rows.partition_point(|r| r.0 <= key);
        &rows[begin..end]
    }
}
impl Adjacency {
    fn new(facts: &FactSnapshot, kind: RelationKind, reverse: bool) -> Self {
        let mut offsets = vec![0; facts.symbols.len() + 1];
        for r in &facts.relations {
            if r.kind == kind {
                offsets[if reverse {
                    r.target.index()
                } else {
                    r.source.index()
                } + 1] += 1;
            }
        }
        for i in 1..offsets.len() {
            offsets[i] += offsets[i - 1];
        }
        let mut values = vec![SymbolId::NONE; *offsets.last().unwrap()];
        let mut cursor = offsets[..facts.symbols.len()].to_vec();
        for r in &facts.relations {
            if r.kind == kind {
                let (source, target) = if reverse {
                    (r.target, r.source)
                } else {
                    (r.source, r.target)
                };
                values[cursor[source.index()]] = target;
                cursor[source.index()] += 1;
            }
        }
        Self { offsets, values }
    }
    fn get(&self, symbol: SymbolId) -> &[SymbolId] {
        &self.values[self.offsets[symbol.index()]..self.offsets[symbol.index() + 1]]
    }
}

#[derive(Default)]
struct Contributions {
    edges: Vec<EdgeRecord>,
    issues: Vec<GraphIssue>,
}

pub fn build(facts: &FactSnapshot, options: &BuildOptions) -> Result<ProgramGraph, Error> {
    build_internal(facts, options, None)
}
pub fn build_with_runtime(
    facts: &FactSnapshot,
    options: &BuildOptions,
    inputs: &selector_models::runtime::RuntimeInputs<'_>,
) -> Result<ProgramGraph, Error> {
    build_internal(facts, options, Some(inputs))
}
fn build_internal(
    facts: &FactSnapshot,
    options: &BuildOptions,
    runtime_inputs: Option<&selector_models::runtime::RuntimeInputs<'_>>,
) -> Result<ProgramGraph, Error> {
    facts.validate()?;
    if options.workers == 0 {
        return Err(Error::Invalid("zero graph-build workers"));
    }
    let pool = if options.workers > 1 {
        Some(
            rayon::ThreadPoolBuilder::new()
                .num_threads(options.workers)
                .build()
                .map_err(|e| Error::Message(format!("graph worker pool: {e}")))?,
        )
    } else {
        None
    };
    let mut graph = ProgramGraph {
        facts_identity: facts.identity,
        ..Default::default()
    };
    graph.nodes.reserve_exact(facts.symbols.len());
    graph.symbol_nodes.reserve(facts.symbols.len());
    for (i, symbol) in facts.symbols.iter().enumerate() {
        let node = NodeId::checked(graph.nodes.len())?;
        graph.nodes.push(NodeRecord {
            symbol: SymbolId(i as u32),
            file: symbol.file,
            body: BodyId::NONE,
            flags: symbol.flags
                | if symbol.flags & SYMBOL_DEFINED == 0
                    && selector_models::bootstrap_initialization(
                        facts.symbol_name(SymbolId(i as u32)),
                    )
                {
                    NODE_EFFECTS_COMPLETE
                } else {
                    0
                },
        });
        graph.symbol_nodes.push(node);
    }
    let mut extra_bodies = 0usize;
    for (i, body) in facts.bodies.iter().enumerate() {
        if body.symbol.is_none() {
            return Err(Error::Invalid("body without compiler identity"));
        }
        let canonical = graph.symbol_nodes[body.symbol.index()];
        if graph.nodes[canonical.index()].body.is_none() {
            graph.nodes[canonical.index()].body = BodyId(i as u32);
            graph.nodes[canonical.index()].file = body.file;
        } else {
            extra_bodies += 1;
        }
    }
    // Reserving symbols+bodies would retain nearly twice the required node
    // memory when each symbol has one body. Count actual extras first.
    graph.nodes.reserve_exact(extra_bodies);
    let mut body_nodes = Vec::with_capacity(facts.bodies.len());
    for (i, body) in facts.bodies.iter().enumerate() {
        let canonical = graph.symbol_nodes[body.symbol.index()];
        let node = if graph.nodes[canonical.index()].body == BodyId(i as u32) {
            canonical
        } else {
            let id = NodeId::checked(graph.nodes.len())?;
            graph.nodes.push(NodeRecord {
                symbol: body.symbol,
                file: body.file,
                body: BodyId(i as u32),
                flags: body.flags,
            });
            id
        };
        body_nodes.push(node);
    }
    let overrides = Adjacency::new(facts, RelationKind::Override, true);
    let dispatch_frontiers = DispatchFrontiers::new(facts);
    let mut occurrences: Vec<OccurrenceId> = (0..facts.occurrences.len())
        .map(|i| OccurrenceId(i as u32))
        .collect();
    let occurrence_key = |&i: &OccurrenceId| {
        let o = &facts.occurrences[i.index()];
        (o.file, o.span.start, o.span.end, o.ordinal)
    };
    if occurrences.len() > 65_536 && pool.is_some() {
        pool.as_ref()
            .unwrap()
            .install(|| occurrences.par_sort_unstable_by_key(occurrence_key));
    } else {
        occurrences.sort_unstable_by_key(occurrence_key);
    }
    let mut file_occurrences = vec![0usize; facts.files.len() + 1];
    for o in &facts.occurrences {
        file_occurrences[o.file.index() + 1] += 1;
    }
    for i in 1..file_occurrences.len() {
        file_occurrences[i] += file_occurrences[i - 1];
    }
    // Initialization bodies may use an exact member identity (<clinit> or a
    // compiler constructor) while the type scope has no direct body. Keep one
    // compact fact-derived recipe bitmap for both admission and external-call
    // checks; absence of a direct type body is not an unknown execution effect.
    let mut initialized = vec![false; facts.symbols.len()];
    for body in &facts.bodies {
        if selector_models::implicit_initializer(facts, body) {
            let symbol = &facts.symbols[body.symbol.index()];
            // A field initializer alone cannot certify the complete owner
            // scope, and constructor overloads are entered by explicit calls.
            if matches!(symbol.kind, 10 | 13 | 14) {
                initialized[body.symbol.index()] = true;
            }
        }
    }
    let view = BuildView {
        facts,
        symbol_nodes: &graph.symbol_nodes,
        nodes: &graph.nodes,
        initialized: &initialized,
        body_nodes: &body_nodes,
        overrides: &overrides,
        dispatch_frontiers: dispatch_frontiers.as_ref(),
        occurrences: &occurrences,
        file_occurrences: &file_occurrences,
    };
    // Graph operations are independent once facts are admitted. Partition by
    // operation count so one large method cannot serialize graph construction.
    // Coarse slices bound output buffers to O(workers), not O(methods).
    let mut structural = Contributions::default();
    for i in 0..facts.bodies.len() {
        lower_body_entries(&view, BodyId(i as u32), &mut structural);
    }
    let chunk_size = facts
        .operations
        .len()
        .div_ceil(options.workers.saturating_mul(8))
        .max(256);
    let compute = || {
        facts
            .operations
            .par_chunks(chunk_size)
            .enumerate()
            .map(|(chunk, operations)| {
                let mut out = Contributions::default();
                let mut scratch = Scratch::default();
                out.edges.reserve(operations.len());
                for i in chunk * chunk_size..chunk * chunk_size + operations.len() {
                    lower_operation(&view, i, &mut scratch, &mut out);
                }
                out
            })
            .collect::<Vec<_>>()
    };
    let parts = if options.workers == 1 {
        let mut out = Contributions::default();
        let mut scratch = Scratch::default();
        for i in 0..facts.operations.len() {
            lower_operation(&view, i, &mut scratch, &mut out);
        }
        vec![out]
    } else {
        pool.as_ref().unwrap().install(compute)
    };
    let edge_count = structural.edges.len() + parts.iter().map(|p| p.edges.len()).sum::<usize>();
    graph.edges.reserve(edge_count + facts.relations.len());
    graph.edges.extend(structural.edges);
    graph.issues.extend(structural.issues);
    for part in parts {
        graph.edges.extend(part.edges);
        graph.issues.extend(part.issues);
    }
    // Compilation dependencies retain signature, parent and override facts,
    // without accidentally making those facts executable calls.
    for r in &facts.relations {
        graph.edges.push(edge(
            graph.symbol_nodes[r.source.index()],
            graph.symbol_nodes[r.target.index()],
            EdgeKind::Compile,
        ));
        if r.kind == RelationKind::Parent
            && matches!(facts.symbols[r.source.index()].kind, 10 | 13 | 14)
            && (r.file.is_none() || facts.files[r.file.index()].flags & FILE_BINARY_SOURCE == 0)
        {
            // Constructing a class/object executes parent and trait initializer
            // scopes. Merely mentioning a parent remains a Compile dependency;
            // this relationship is entered only through an initialization root.
            graph.edges.push(edge(
                graph.symbol_nodes[r.source.index()],
                graph.symbol_nodes[r.target.index()],
                EdgeKind::Initialize,
            ));
        }
    }
    add_occurrence_dependencies(facts, &body_nodes, &mut graph)?;
    for issue in &facts.issues {
        if !issue.kind.is_execution_boundary() {
            continue;
        }
        graph.issues.push(GraphIssue {
            kind: issue.kind,
            node: if issue.symbol.is_none() {
                NodeId::NONE
            } else {
                graph.symbol_nodes[issue.symbol.index()]
            },
            file: issue.file,
            symbol: issue.symbol,
            detail: issue.detail,
        });
    }
    // Source declarations with no executable recipe stay explicitly unknown.
    // Abstract declarations (SemanticDB ABSTRACT=4) have no body by design.
    for (i, s) in facts.symbols.iter().enumerate() {
        let missing_method = matches!(s.kind, 3 | 21)
            && s.properties & 4 == 0
            && graph.nodes[graph.symbol_nodes[i].index()].body.is_none();
        let missing_initialization = matches!(s.kind, 10 | 13 | 14) && !initialized[i];
        if s.flags & SYMBOL_DEFINED != 0 && (missing_method || missing_initialization) {
            let node = graph.symbol_nodes[i];
            graph.issues.push(GraphIssue {
                kind: IssueKind::MissingSyntax,
                node,
                file: s.file,
                symbol: SymbolId(i as u32),
                detail: StrId::NONE,
            });
            let mut guard = edge(node, node, EdgeKind::Guard);
            guard.flags = EDGE_UNKNOWN;
            graph.edges.push(guard);
        }
    }
    graph.runtime_identity = runtime_inputs
        .map(selector_models::runtime::runtime_identity)
        .unwrap_or_default();
    let mut runtime_identity = ContentHash::default();
    if options.include_models {
        if facts.suites.len() >= 16 && pool.is_some() {
            let prepared =
                selector_models::PreparedModels::new(facts, &graph.symbol_nodes, &body_nodes);
            let chunk = facts
                .suites
                .len()
                .div_ceil(options.workers.saturating_mul(4))
                .max(16);
            let mut bridge = selector_models::ModelContributions::default();
            prepared.contribute_bridges(&mut bridge);
            graph.edges.extend(bridge.edges);
            let models = pool.as_ref().unwrap().install(|| {
                facts
                    .suites
                    .par_chunks(chunk)
                    .map(|suites| {
                        let mut out = selector_models::ModelContributions::default();
                        let mut scratch = selector_models::ModelScratch::default();
                        prepared.contribute_suites(suites, &mut scratch, &mut out);
                        out
                    })
                    .collect::<Vec<_>>()
            });
            for model in models {
                graph.edges.extend(model.edges);
                graph.issues.extend(model.issues);
            }
        } else {
            let model = selector_models::contribute(facts, &graph.symbol_nodes, &body_nodes);
            graph.edges.extend(model.edges);
            graph.issues.extend(model.issues);
        }
        let default_inputs = selector_models::runtime::RuntimeInputs {
            sources: facts
                .files
                .iter()
                .filter(|file| file.flags & SOURCE_VERIFIED != 0)
                .filter_map(|file| {
                    let path = facts.text(file.path);
                    (path.ends_with(".yaml")
                        || path.ends_with(".yml")
                        || path.ends_with("build.sbt"))
                    .then(|| selector_models::runtime::RuntimeSource {
                        path,
                        text: facts.text(file.source),
                    })
                })
                .collect(),
            ..Default::default()
        };
        let runtime = selector_models::runtime::contribute(
            facts,
            &graph.symbol_nodes,
            runtime_inputs.unwrap_or(&default_inputs),
        )?;
        runtime_identity = runtime.identity;
        retain_runtime_diagnostics(&mut graph, &runtime.model.issues, &runtime.diagnostics)?;
        graph.edges.extend(runtime.model.edges);
        graph.issues.extend(runtime.model.issues);
    }
    if graph.edges.len() > 65_536 && pool.is_some() {
        pool.as_ref()
            .unwrap()
            .install(|| graph.edges.par_sort_unstable());
    } else {
        graph.edges.sort_unstable();
    }
    graph.edges.dedup();
    graph
        .issues
        .sort_unstable_by_key(|i| (i.node, i.file, i.symbol, i.kind as u32, i.detail));
    graph
        .issues
        .dedup_by_key(|i| (i.node, i.file, i.symbol, i.kind as u32, i.detail));
    // Never retain edge-buffer or repeated-boundary high-water capacities in
    // the sealed snapshot after canonicalization removes duplicates.
    graph.edges.shrink_to_fit();
    graph.issues.shrink_to_fit();
    graph.diagnostic_bytes.shrink_to_fit();
    graph.diagnostics.shrink_to_fit();
    let mut hash = Sha256::new();
    hash.update(b"selector-program-graph/1");
    hash.update(facts.identity.0);
    hash.update(runtime_identity.0);
    hash.update(graph.runtime_identity.0);
    hash.update(if options.include_models {
        selector_models::MODEL_VERSION.as_bytes()
    } else {
        b"models-disabled"
    });
    if options.include_models {
        hash.update(selector_models::FRAMEWORK_MODEL_VERSION.as_bytes());
    }
    for n in &graph.nodes {
        for word in [n.symbol.0, n.file.0, n.body.0, n.flags] {
            hash.update(word.to_le_bytes());
        }
    }
    for e in &graph.edges {
        for word in [
            e.source.0,
            e.target.0,
            e.kind as u32,
            e.occurrence.0,
            e.operation.0,
            e.receiver.0,
            e.flags,
        ] {
            hash.update(word.to_le_bytes());
        }
    }
    for i in &graph.issues {
        for word in [i.kind as u32, i.node.0, i.file.0, i.symbol.0, i.detail.0] {
            hash.update(word.to_le_bytes());
        }
    }
    hash.update(b"runtime-diagnostic-evidence/v1\0");
    hash.update((graph.diagnostic_bytes.len() as u64).to_le_bytes());
    hash.update(&graph.diagnostic_bytes);
    hash.update((graph.diagnostics.len() as u64).to_le_bytes());
    for diagnostic in &graph.diagnostics {
        for word in [
            diagnostic.kind as u32,
            diagnostic.node.0,
            diagnostic.file.0,
            diagnostic.symbol.0,
            diagnostic.reason.start,
            diagnostic.reason.len,
            diagnostic.metadata_path.start,
            diagnostic.metadata_path.len,
        ] {
            hash.update(word.to_le_bytes());
        }
    }
    graph.identity = ContentHash(hash.finalize().into());
    if graph.edges.len() > 65_536 && pool.is_some() {
        seal_sorted_indexes(&mut graph, pool.as_ref().unwrap())?;
    } else {
        graph.index()?;
    }
    graph.validate()?;
    Ok(graph)
}

/// Runtime model evidence cannot be interned into immutable compiler facts.
/// Retain one canonical flat pool and fixed-size rows only for diagnostics;
/// all sorting/index scratch borrows producer strings and dies with this phase.
fn retain_runtime_diagnostics(
    graph: &mut ProgramGraph,
    issues: &[GraphIssue],
    diagnostics: &[selector_models::runtime::RuntimeDiagnostic],
) -> Result<(), Error> {
    if issues.len() != diagnostics.len() {
        return Err(Error::Invalid("runtime diagnostic scope count"));
    }
    if diagnostics.is_empty() {
        return Ok(());
    }
    let mut texts = Vec::new();
    texts
        .try_reserve_exact(
            diagnostics
                .len()
                .checked_mul(2)
                .ok_or(Error::Limit("runtime diagnostic text"))?,
        )
        .map_err(|_| Error::Limit("runtime diagnostic text"))?;
    for diagnostic in diagnostics {
        texts.push(diagnostic.reason);
        texts.push(diagnostic.metadata_path.as_str());
    }
    texts.sort_unstable();
    texts.dedup();
    let bytes = texts.iter().try_fold(0usize, |total, text| {
        total
            .checked_add(text.len())
            .ok_or(Error::Limit("runtime diagnostic text"))
    })?;
    if bytes > u32::MAX as usize {
        return Err(Error::Limit("runtime diagnostic text"));
    }
    graph
        .diagnostic_bytes
        .try_reserve_exact(bytes)
        .map_err(|_| Error::Limit("runtime diagnostic text"))?;
    let mut ranges = std::collections::HashMap::new();
    ranges
        .try_reserve(texts.len())
        .map_err(|_| Error::Limit("runtime diagnostic index"))?;
    for text in texts {
        let range = IdRange {
            start: graph.diagnostic_bytes.len() as u32,
            len: text.len() as u32,
        };
        graph.diagnostic_bytes.extend_from_slice(text.as_bytes());
        ranges.insert(text, range);
    }
    graph
        .diagnostics
        .try_reserve_exact(diagnostics.len())
        .map_err(|_| Error::Limit("runtime diagnostic records"))?;
    for (issue, diagnostic) in issues.iter().zip(diagnostics) {
        if issue.symbol != diagnostic.symbol {
            return Err(Error::Invalid("runtime diagnostic symbol scope"));
        }
        graph.diagnostics.push(GraphDiagnostic {
            kind: issue.kind,
            node: issue.node,
            file: issue.file,
            symbol: issue.symbol,
            reason: ranges[diagnostic.reason],
            metadata_path: ranges[diagnostic.metadata_path.as_str()],
        });
    }
    graph.diagnostics.sort_unstable_by_key(|d| {
        (
            d.node,
            d.file,
            d.symbol,
            d.kind as u32,
            d.reason.start,
            d.reason.len,
            d.metadata_path.start,
            d.metadata_path.len,
        )
    });
    graph.diagnostics.dedup();
    Ok(())
}

/// Forward edges already have source order after canonicalization. Build the
/// independent directions concurrently, without dense per-worker count tables.
/// Only the reverse scatter needs a temporary cursor array.
fn seal_sorted_indexes(graph: &mut ProgramGraph, pool: &rayon::ThreadPool) -> Result<(), Error> {
    EdgeId::checked(graph.edges.len())?;
    let nodes = graph.nodes.len();
    let edges = &graph.edges;
    let forward = || {
        let mut offsets = vec![0u64; nodes + 1];
        for e in edges {
            offsets[e.source.index() + 1] += 1;
        }
        for i in 1..offsets.len() {
            offsets[i] += offsets[i - 1];
        }
        let ids = (0..edges.len())
            .map(|i| EdgeId(i as u32))
            .collect::<Vec<_>>();
        (offsets, ids)
    };
    let reverse = || {
        let mut offsets = vec![0u64; nodes + 1];
        for e in edges {
            offsets[e.target.index() + 1] += 1;
        }
        for i in 1..offsets.len() {
            offsets[i] += offsets[i - 1];
        }
        let mut ids = vec![EdgeId::NONE; edges.len()];
        let mut cursors = offsets[..nodes].to_vec();
        for (i, e) in edges.iter().enumerate() {
            ids[cursors[e.target.index()] as usize] = EdgeId(i as u32);
            cursors[e.target.index()] += 1;
        }
        (offsets, ids)
    };
    let ((fo, fe), (ro, re)) = pool.install(|| rayon::join(forward, reverse));
    graph.forward_offsets = fo;
    graph.forward_edges = fe;
    graph.reverse_offsets = ro;
    graph.reverse_edges = re;
    Ok(())
}

struct BuildView<'a> {
    facts: &'a FactSnapshot,
    symbol_nodes: &'a [NodeId],
    nodes: &'a [NodeRecord],
    initialized: &'a [bool],
    body_nodes: &'a [NodeId],
    overrides: &'a Adjacency,
    dispatch_frontiers: Option<&'a DispatchFrontiers>,
    occurrences: &'a [OccurrenceId],
    file_occurrences: &'a [usize],
}
#[derive(Default)]
struct Scratch {
    pending: Vec<SymbolId>,
    visited: std::collections::HashSet<SymbolId>,
}

fn lower_body_entries(view: &BuildView<'_>, bid: BodyId, out: &mut Contributions) {
    let facts = view.facts;
    let body = &facts.bodies[bid.index()];
    let source = view.body_nodes[bid.index()];
    let symbol = &facts.symbols[body.symbol.index()];
    if selector_models::implicit_initializer(facts, body)
        && !symbol.owner.is_none()
        && !matches!(symbol.kind, 10 | 13 | 14)
    {
        out.edges.push(edge(
            view.symbol_nodes[symbol.owner.index()],
            source,
            EdgeKind::Initialize,
        ));
    }
    // Additional eager bodies of the same symbol are attached to its canonical
    // node; a deferred body must have a distinct compiler/synthetic identity.
    let canonical = view.symbol_nodes[body.symbol.index()];
    if source != canonical && body.flags & (BODY_DEFERRED | BODY_LAZY) == 0 {
        out.edges
            .push(edge(canonical, source, EdgeKind::Initialize));
    }
}

fn lower_operation(view: &BuildView<'_>, i: usize, scratch: &mut Scratch, out: &mut Contributions) {
    let facts = view.facts;
    let op = &facts.operations[i];
    let bid = op.body;
    let body = &facts.bodies[bid.index()];
    let source = view.body_nodes[bid.index()];
    let operation = OperationId(i as u32);
    // Formal declarations belong to the method header, which can precede the
    // executable expression. They do not themselves contribute graph edges.
    if op.opcode == Opcode::Parameter {
        return;
    }
    if !body.operations.range().contains(&i) {
        out.issues
            .push(issue(IssueKind::InvalidInput, source, body));
        return;
    }
    if !body.span.contains(op.span) {
        out.issues
            .push(issue(IssueKind::UnknownExecution, source, body));
        return;
    }
    let compiler_private = facts.compiler_private_dispatch(op);
    let kind = match op.opcode {
        Opcode::Call => EdgeKind::Call,
        Opcode::VirtualCall if compiler_private => EdgeKind::Call,
        Opcode::VirtualCall => EdgeKind::VirtualCall,
        Opcode::Allocate => EdgeKind::Construct,
        Opcode::Initialize => EdgeKind::Initialize,
        Opcode::InvokeCallback => EdgeKind::Callback,
        Opcode::RegisterTest => EdgeKind::Call,
        Opcode::LoadField | Opcode::StoreField => EdgeKind::Field,
        Opcode::DefaultArgument => EdgeKind::Default,
        // Binding and capture have no execution edge until invoked.
        Opcode::BindCallback => EdgeKind::Compile,
        Opcode::Unknown => {
            let mut e = edge(source, source, EdgeKind::Guard);
            e.operation = operation;
            e.flags = EDGE_UNKNOWN;
            out.edges.push(e);
            out.issues
                .push(issue(IssueKind::UnknownExecution, source, body));
            return;
        }
        _ => return,
    };
    if op.target.is_none() {
        if !matches!(op.opcode, Opcode::InvokeCallback | Opcode::RegisterTest) {
            let mut e = edge(source, source, EdgeKind::Guard);
            e.operation = operation;
            e.flags = EDGE_UNKNOWN;
            out.edges.push(e);
            out.issues
                .push(issue(IssueKind::UnresolvedSymbol, source, body));
        }
        return;
    }
    let occurrence = matching_occurrence(view, body, op);
    if !compiler_private
        && op.flags & (OP_SUPER | OP_QUALIFIED_SUPER) == 0
        && matches!(
            op.opcode,
            Opcode::Call
                | Opcode::VirtualCall
                | Opcode::DefaultArgument
                | Opcode::RegisterTest
                | Opcode::InvokeCallback
        )
    {
        if let Some(frontiers) = view.dispatch_frontiers {
            scratch.pending.clear();
            scratch.visited.clear();
            scratch.pending.push(op.target);
            while let Some(contract) = scratch.pending.pop() {
                if !scratch.visited.insert(contract) {
                    continue;
                }
                for &(_, receiver) in DispatchFrontiers::get(&frontiers.receivers, contract) {
                    let mut guard =
                        edge(source, view.symbol_nodes[contract.index()], EdgeKind::Guard);
                    guard.operation = operation;
                    guard.occurrence = occurrence;
                    guard.receiver = receiver;
                    guard.flags = EDGE_UNKNOWN | EDGE_DEFERRED_DISPATCH;
                    out.edges.push(guard);
                }
                scratch.pending.extend(
                    DispatchFrontiers::get(&frontiers.parents, contract)
                        .iter()
                        .map(|r| r.1),
                );
            }
        }
    }
    let mut declaring = body.symbol;
    let mut trait_super = false;
    if op.flags & OP_SUPER != 0 && op.flags & OP_QUALIFIED_SUPER == 0 && op.opcode == Opcode::Call {
        // Closures retain their compiler owner chain. Only trait super is
        // receiver dependent; class and qualified super targets stay direct.
        for _ in 0..facts.symbols.len() {
            let declaration = &facts.symbols[declaring.index()];
            if matches!(declaration.kind, 10 | 13 | 14) {
                trait_super = declaration.kind == 14;
                break;
            }
            if declaration.owner.is_none() {
                break;
            }
            declaring = declaration.owner;
        }
    }
    if (op.opcode == Opcode::VirtualCall && !compiler_private)
        || trait_super
        || (op.opcode == Opcode::InvokeCallback
            && matches!(facts.symbols[op.target.index()].kind, 3 | 21))
    {
        scratch.pending.clear();
        scratch.visited.clear();
        scratch.pending.push(op.target);
        let mut concrete = false;
        while let Some(target) = scratch.pending.pop() {
            if !scratch.visited.insert(target) {
                continue;
            }
            let receiver = facts.symbols[target.index()].owner;
            if facts.symbols[target.index()].properties & 4 != 0
                && view.nodes[view.symbol_nodes[target.index()].index()]
                    .body
                    .is_none()
            {
                scratch.pending.extend(view.overrides.get(target));
                continue;
            }
            concrete = true;
            let mut e = edge(source, view.symbol_nodes[target.index()], kind);
            e.operation = operation;
            e.occurrence = occurrence;
            e.receiver = receiver;
            e.flags |= runtime_flags(facts, target, op);
            out.edges.push(e);
            scratch.pending.extend(view.overrides.get(target));
        }
        if !concrete && (op.opcode == Opcode::VirtualCall || trait_super) {
            let mut guard = edge(source, source, EdgeKind::Guard);
            guard.operation = operation;
            guard.flags = EDGE_UNKNOWN;
            out.edges.push(guard);
            out.issues
                .push(issue(IssueKind::UnknownExecution, source, body));
        }
    } else {
        let mut e = edge(source, view.symbol_nodes[op.target.index()], kind);
        e.operation = operation;
        e.occurrence = occurrence;
        if kind.is_execution() {
            e.flags |= runtime_flags(facts, op.target, op);
        }
        out.edges.push(e);
    }
    if kind.is_execution() {
        let target = &facts.symbols[op.target.index()];
        // Accessing an object member initializes that exact compiler owner;
        // allocation initializes the captured class owning its constructor.
        let initialization = if op.opcode == Opcode::Allocate && matches!(target.kind, 10 | 13 | 14)
        {
            // A validated allocation can target a compiler type rather than a
            // constructor. Its package owner is not an executable initializer.
            op.target
        } else if !target.owner.is_none()
            && (facts.symbols[target.owner.index()].kind == 10 || op.opcode == Opcode::Allocate)
        {
            target.owner
        } else {
            SymbolId::NONE
        };
        if !initialization.is_none() && initialization != op.target {
            let mut initialize = edge(
                source,
                view.symbol_nodes[initialization.index()],
                EdgeKind::Initialize,
            );
            initialize.operation = operation;
            initialize.occurrence = occurrence;
            out.edges.push(initialize);
        }
        if kind != EdgeKind::Field
            && target.flags & SYMBOL_DEFINED == 0
            && !(matches!(target.kind, 10 | 13 | 14) && view.initialized[op.target.index()])
            && view.nodes[view.symbol_nodes[op.target.index()].index()]
                .body
                .is_none()
            && !selector_models::classify_external(facts.symbol_name(op.target)).effects_complete
        {
            // Scope uncertainty to the external boundary; callers encounter
            // this obligation only if the boundary is actually reachable.
            out.issues.push(GraphIssue {
                kind: IssueKind::UnknownExecution,
                node: view.symbol_nodes[op.target.index()],
                file: target.file,
                symbol: op.target,
                detail: StrId::NONE,
            });
        }
    }
}

fn matching_occurrence(
    view: &BuildView<'_>,
    body: &BodyRecord,
    op: &OperationRecord,
) -> OccurrenceId {
    if body.file.is_none() {
        return OccurrenceId::NONE;
    }
    let file = &view.occurrences
        [view.file_occurrences[body.file.index()]..view.file_occurrences[body.file.index() + 1]];
    let start =
        file.partition_point(|&i| view.facts.occurrences[i.index()].span.start < op.span.start);
    for &i in &file[start..] {
        let o = &view.facts.occurrences[i.index()];
        if o.span.start > op.span.end {
            break;
        }
        if o.symbol == op.target && op.span.contains(o.span) {
            return i;
        }
    }
    OccurrenceId::NONE
}

fn edge(source: NodeId, target: NodeId, kind: EdgeKind) -> EdgeRecord {
    EdgeRecord {
        source,
        target,
        kind,
        occurrence: OccurrenceId::NONE,
        operation: OperationId::NONE,
        receiver: SymbolId::NONE,
        flags: 0,
    }
}
fn runtime_flags(facts: &FactSnapshot, target: SymbolId, op: &OperationRecord) -> u32 {
    if facts.symbols[target.index()].flags & SYMBOL_DEFINED != 0 {
        return 0;
    }
    let contract = selector_models::classify_external(facts.symbol_name(target));
    let callback = match contract.callbacks {
        selector_models::CallbackBehavior::Immediate => EDGE_CALLBACK_IMMEDIATE,
        selector_models::CallbackBehavior::Deferred => EDGE_CALLBACK_DEFERRED,
        selector_models::CallbackBehavior::TestRegistration => EDGE_TEST_REGISTRATION,
        _ => 0,
    };
    let argument = if callback != 0 && target == op.target {
        // The certificate names this exact compiler-bound contract. A source
        // shadow, an ordinary call or another dispatch candidate cannot inherit
        // its parameter mapping. Preserve malformed encodings for the solver's
        // explicit guard rather than silently dropping their evidence.
        op.flags & (CALLBACK_ARGUMENT_PRESENT | CALLBACK_ARGUMENT_MASK)
    } else {
        0
    };
    callback
        | argument
        | if contract.effects_complete {
            EDGE_EFFECTS_COMPLETE
        } else {
            0
        }
}
fn issue(kind: IssueKind, node: NodeId, body: &BodyRecord) -> GraphIssue {
    GraphIssue {
        kind,
        node,
        file: body.file,
        symbol: body.symbol,
        detail: StrId::NONE,
    }
}

/// Compiler occurrences contribute compilation dependencies. The innermost
/// containing executable body owns an occurrence; signatures remain attached to
/// declarations. Prefix maxima make nesting queries output-sensitive.
fn add_occurrence_dependencies(
    facts: &FactSnapshot,
    body_nodes: &[NodeId],
    graph: &mut ProgramGraph,
) -> Result<(), Error> {
    // A compiler declaration can be implemented by an admitted binary recipe
    // in another file. Keep its source occurrence provenance separate from the
    // canonical execution node without changing execution entry or arguments.
    let declaration_count = facts
        .symbols
        .iter()
        .filter(|symbol| !symbol.file.is_none() && symbol.span.start < symbol.span.end)
        .count();
    let exceptional = facts
        .symbols
        .iter()
        .enumerate()
        .filter(|(index, symbol)| {
            !symbol.file.is_none()
                && symbol.span.start < symbol.span.end
                && graph.nodes[graph.symbol_nodes[*index].index()].file != symbol.file
        })
        .count();
    graph.nodes.reserve_exact(exceptional);
    let mut spans: Vec<(FileId, u32, u32, NodeId)> =
        Vec::with_capacity(declaration_count + facts.bodies.len());
    for (index, symbol) in facts.symbols.iter().enumerate() {
        if symbol.file.is_none() || symbol.span.start >= symbol.span.end {
            continue;
        }
        let canonical = graph.symbol_nodes[index];
        let declaration = if graph.nodes[canonical.index()].file == symbol.file {
            canonical
        } else {
            let node = NodeId::checked(graph.nodes.len())?;
            graph.nodes.push(NodeRecord {
                symbol: SymbolId(index as u32),
                file: symbol.file,
                body: BodyId::NONE,
                flags: symbol.flags,
            });
            graph.edges.push(edge(canonical, node, EdgeKind::Compile));
            node
        };
        spans.push((symbol.file, symbol.span.start, symbol.span.end, declaration));
    }
    spans.extend(
        facts
            .bodies
            .iter()
            .enumerate()
            .filter(|(_, b)| !b.file.is_none())
            .map(|(i, b)| (b.file, b.span.start, b.span.end, body_nodes[i])),
    );
    spans.sort_unstable_by(|a, b| {
        (a.0, a.1, a.2).cmp(&(b.0, b.1, b.2)).then_with(|| {
            // Compiler-inserted by-name and callback bodies can cover exactly
            // the same text. The reverse sweep needs a stable winner even when
            // an unrelated file changes the global insertion order. Compare
            // compiler identities, not snapshot-local string or symbol IDs.
            let identity = |node: NodeId| {
                let record = graph.nodes[node.index()];
                let symbol = facts.symbols[record.symbol.index()];
                (facts.text(symbol.name), facts.text(symbol.context))
            };
            identity(b.3)
                .cmp(&identity(a.3))
                .then_with(|| a.3.cmp(&b.3))
        })
    });
    let mut maxima = Vec::with_capacity(spans.len());
    let mut last = FileId::NONE;
    let mut max = 0;
    for s in &spans {
        if s.0 != last {
            last = s.0;
            max = 0;
        }
        max = max.max(s.2);
        maxima.push(max);
    }
    for (i, o) in facts.occurrences.iter().enumerate() {
        if o.role == 2 {
            continue;
        }
        let mut at = spans.partition_point(|s| (s.0, s.1) <= (o.file, o.span.start));
        let target = graph.symbol_nodes[o.symbol.index()];
        let mut owner = None;
        let mut owner_start = u32::MAX;
        let mut width = u32::MAX;
        while at > 0 {
            at -= 1;
            let s = &spans[at];
            if s.0 != o.file || maxima[at] < o.span.end {
                break;
            }
            let candidate_width = s.2 - s.1;
            if s.2 >= o.span.end
                && (candidate_width < width
                    // If the stable winner is the target itself, keep a
                    // distinct owner on the same exact span when available.
                    // The graph has no use for a self dependency.
                    || (candidate_width == width
                        && s.1 == owner_start
                        && owner == Some(target)
                        && s.3 != target))
            {
                width = candidate_width;
                owner_start = s.1;
                owner = Some(s.3);
            }
        }
        if let Some(source) = owner {
            if source != target {
                let mut e = edge(source, target, EdgeKind::Compile);
                e.occurrence = OccurrenceId::checked(i)?;
                graph.edges.push(e);
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use selector_facts::*;

    struct Fixture {
        builder: FactBuilder,
        file: FileId,
    }
    impl Fixture {
        fn new() -> Self {
            let mut builder = FactBuilder::new();
            let path = builder.intern("suite.scala").unwrap();
            let context = builder.intern("project:test").unwrap();
            let source = builder.intern(&" ".repeat(1024)).unwrap();
            builder.facts.files.push(FileRecord {
                path,
                source,
                revision: StrId::NONE,
                context,
                source_hash: ContentHash::default(),
                flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
            });
            Self {
                builder,
                file: FileId(0),
            }
        }
        fn symbol(&mut self, name: &str, kind: u32, owner: SymbolId) -> SymbolId {
            let id = self.builder.ensure_symbol(name, self.file).unwrap();
            let s = &mut self.builder.facts.symbols[id.index()];
            s.file = self.file;
            s.kind = kind;
            s.owner = owner;
            s.flags = SYMBOL_DEFINED;
            id
        }
        fn body(
            &mut self,
            symbol: SymbolId,
            start: u32,
            flags: u32,
            ops: &[(Opcode, SymbolId)],
        ) -> BodyId {
            let bid = BodyId(self.builder.facts.bodies.len() as u32);
            let offset = self.builder.facts.operations.len() as u32;
            for &(opcode, target) in ops {
                self.builder.facts.operations.push(OperationRecord {
                    body: bid,
                    opcode,
                    target,
                    dest: ValueId::NONE,
                    a: ValueId::NONE,
                    b: ValueId::NONE,
                    arguments: IdRange::default(),
                    span: Span {
                        start: start + 1,
                        end: start + 2,
                    },
                    flags: 0,
                });
            }
            self.builder.facts.bodies.push(BodyRecord {
                symbol,
                file: self.file,
                span: Span {
                    start,
                    end: start + 20,
                },
                name_span: Span {
                    start,
                    end: start + 1,
                },
                operations: IdRange {
                    start: offset,
                    len: ops.len() as u32,
                },
                parameters: IdRange::default(),
                body_hash: ContentHash::default(),
                flags,
            });
            bid
        }
        fn relation(&mut self, source: SymbolId, target: SymbolId, kind: RelationKind) {
            self.builder.facts.relations.push(RelationRecord {
                source,
                target,
                kind,
                file: self.file,
            });
        }
        fn graph(self, workers: usize) -> ProgramGraph {
            build(
                &self.builder.finish().unwrap(),
                &BuildOptions {
                    workers,
                    include_models: true,
                },
            )
            .unwrap()
        }
    }
    fn reaches(g: &ProgramGraph, from: SymbolId, to: SymbolId) -> bool {
        let mut queue = vec![g.node_for_symbol(from).unwrap()];
        let mut seen = vec![false; g.nodes.len()];
        while let Some(node) = queue.pop() {
            if node == g.node_for_symbol(to).unwrap() {
                return true;
            }
            if seen[node.index()] {
                continue;
            }
            seen[node.index()] = true;
            queue.extend(
                g.successors(node)
                    .filter(|(_, e)| e.kind.is_execution())
                    .map(|(_, e)| e.target),
            );
        }
        false
    }
    #[test]
    fn private_trait_this_call_keeps_body_edge_but_no_override_frontier() {
        for (private, same_owner) in [(true, true), (false, true), (true, false)] {
            let mut f = Fixture::new();
            f.builder.facts.files[0].source_hash = ContentHash([1; 32]);
            let trait_owner = f.symbol("p/PrettyUtil#", 14, SymbolId::NONE);
            let child = f.symbol("p/Child#", 13, SymbolId::NONE);
            let target = f.symbol("p/PrettyUtil#conditionalParam().", 3, trait_owner);
            let alternative = f.symbol("p/Child#conditionalParam().", 3, child);
            let caller = f.symbol(
                "p/PrettyUtil#param().",
                3,
                if same_owner { trait_owner } else { child },
            );
            if private {
                f.builder.facts.symbols[target.index()].flags |= SYMBOL_SCALA_PRIVATE_METHOD;
            }
            f.body(caller, 0, 0, &[(Opcode::VirtualCall, target)]);
            f.builder.facts.operations[0].a = ValueId(0);
            f.body(target, 40, 0, &[]);
            f.body(alternative, 80, 0, &[]);
            f.relation(child, trait_owner, RelationKind::Parent);
            f.relation(alternative, target, RelationKind::Override);
            f.relation(child, target, RelationKind::DeferredDispatch);
            let graph = f.graph(1);
            let direct = private && same_owner;
            let start = graph.node_for_symbol(caller).unwrap();
            let target = graph.node_for_symbol(target).unwrap();
            assert!(graph.successors(start).any(|(_, e)| {
                e.target == target
                    && e.kind
                        == if direct {
                            EdgeKind::Call
                        } else {
                            EdgeKind::VirtualCall
                        }
            }));
            assert_eq!(reaches(&graph, caller, alternative), !direct);
            assert_eq!(
                graph
                    .successors(start)
                    .any(|(_, e)| e.flags & EDGE_DEFERRED_DISPATCH != 0),
                !direct
            );
        }
    }
    #[test]
    fn scoped_dispatch_frontiers_follow_inherited_contracts_without_poisoning_other_methods() {
        let mut f = Fixture::new();
        let child = f.symbol("p/Child#", 13, SymbolId::NONE);
        let base = f.symbol("p/Base#", 13, SymbolId::NONE);
        let interface = f.symbol("p/Contract#", 14, SymbolId::NONE);
        let contract = f.symbol("p/Contract#m().", 3, interface);
        let inherited = f.symbol("p/Base#m().", 3, base);
        let other = f.symbol("p/Base#other().", 3, base);
        f.relation(inherited, contract, RelationKind::Override);
        f.relation(child, contract, RelationKind::DeferredDispatch);
        for target in [contract, inherited, other] {
            f.body(target, 500, 0, &[]);
        }
        let mut callers = Vec::new();
        for (index, opcode) in [
            Opcode::Call,
            Opcode::VirtualCall,
            Opcode::DefaultArgument,
            Opcode::RegisterTest,
            Opcode::InvokeCallback,
        ]
        .into_iter()
        .enumerate()
        {
            let caller = f.symbol(&format!("p/Child#call{index}()."), 3, child);
            f.body(caller, index as u32 * 30, 0, &[(opcode, inherited)]);
            callers.push(caller);
        }
        let unrelated = f.symbol("p/Child#unrelated().", 3, child);
        f.body(unrelated, 200, 0, &[(Opcode::VirtualCall, other)]);
        let qualified = f.symbol("p/Child#qualified().", 3, child);
        f.body(qualified, 250, 0, &[(Opcode::Call, inherited)]);
        f.builder.facts.operations.last_mut().unwrap().flags = OP_SUPER | OP_QUALIFIED_SUPER;
        let facts = f.builder.finish().unwrap();
        let graph = build(
            &facts,
            &BuildOptions {
                workers: 4,
                include_models: false,
            },
        )
        .unwrap();
        for caller in callers {
            let node = graph.node_for_symbol(caller).unwrap();
            let guards: Vec<_> = graph
                .successors(node)
                .map(|(_, e)| e)
                .filter(|e| e.flags & EDGE_DEFERRED_DISPATCH != 0)
                .collect();
            assert_eq!(guards.len(), 1);
            assert_eq!(
                (guards[0].receiver, guards[0].target, guards[0].flags),
                (
                    child,
                    graph.node_for_symbol(contract).unwrap(),
                    EDGE_UNKNOWN | EDGE_DEFERRED_DISPATCH
                )
            );
            assert!(!guards[0].operation.is_none());
            assert!(
                !graph.issues.iter().any(|i| i.node == node),
                "not an unconditional source issue"
            );
        }
        for caller in [unrelated, qualified] {
            assert!(
                !graph
                    .successors(graph.node_for_symbol(caller).unwrap())
                    .any(|(_, e)| e.flags & EDGE_DEFERRED_DISPATCH != 0)
            );
        }
    }

    #[test]
    fn admitted_hierarchy_diagnostics_stay_in_facts_without_becoming_runtime_guards() {
        let mut f = Fixture::new();
        let initializer = f.symbol("p/LibraryTrait#", 14, SymbolId::NONE);
        f.body(initializer, 0, BODY_BINARY_RECIPE | BODY_INITIALIZER, &[]);
        f.builder.facts.files[0].flags = FILE_BINARY_SOURCE;
        f.builder.facts.files[0].source_hash = ContentHash([9; 32]);
        let context = f.builder.facts.files[0].context;
        f.builder.facts.symbols[initializer.index()].context = context;
        f.builder.facts.symbols[initializer.index()].flags = SYMBOL_JVM_CLASS_HEADER_VERIFIED;
        f.builder.facts.issues.push(IssueRecord {
            kind: IssueKind::IncompleteHierarchy,
            file: f.file,
            symbol: initializer,
            detail: StrId::NONE,
        });
        let mut facts = f.builder.finish().unwrap();
        let graph = build(&facts, &BuildOptions::default()).unwrap();
        assert_eq!(facts.issues.len(), 1);
        assert!(graph.issues.is_empty());
        facts.issues[0].kind = IssueKind::MissingBinary;
        let guarded = build(&facts, &BuildOptions::default()).unwrap();
        assert!(
            guarded
                .issues
                .iter()
                .any(|issue| issue.kind == IssueKind::MissingBinary && issue.symbol == initializer)
        );
    }
    #[test]
    fn bound_deferred_callback_is_not_eager_but_explicit_invoke_is() {
        let mut f = Fixture::new();
        let owner = f.symbol("p/Suite#", 13, SymbolId::NONE);
        let caller = f.symbol("p/Suite#run().", 3, owner);
        let closure = f.symbol("local-callback", 19, caller);
        let changed = f.symbol("p/Changed#work().", 3, SymbolId::NONE);
        f.body(changed, 90, 0, &[]);
        f.body(closure, 50, BODY_DEFERRED, &[(Opcode::Call, changed)]);
        f.body(caller, 10, 0, &[(Opcode::BindCallback, closure)]);
        let facts = f.builder.finish().unwrap();
        let g = build(
            &facts,
            &BuildOptions {
                workers: 1,
                include_models: true,
            },
        )
        .unwrap();
        assert!(!reaches(&g, caller, changed));
        assert!(
            g.successors(g.node_for_symbol(caller).unwrap())
                .any(|(_, e)| e.target == g.node_for_symbol(closure).unwrap()
                    && e.kind == EdgeKind::Compile)
        );
        let mut facts = facts;
        facts.operations.last_mut().unwrap().opcode = Opcode::InvokeCallback;
        let g = build(
            &facts,
            &BuildOptions {
                workers: 2,
                include_models: true,
            },
        )
        .unwrap();
        assert!(reaches(&g, caller, changed));
    }
    #[test]
    fn signatures_and_annotations_never_become_execution_edges() {
        let mut f = Fixture::new();
        let a = f.symbol("p/A#m().", 3, SymbolId::NONE);
        let b = f.symbol("p/B#", 13, SymbolId::NONE);
        f.body(a, 20, 0, &[]);
        f.relation(a, b, RelationKind::Signature);
        f.relation(a, b, RelationKind::Annotation);
        let g = f.graph(1);
        assert!(!reaches(&g, a, b));
        assert!(
            g.successors(g.node_for_symbol(a).unwrap())
                .all(|(_, e)| e.kind == EdgeKind::Compile)
        );
    }
    #[test]
    fn initialization_excludes_lazy_and_deferred_members() {
        let mut f = Fixture::new();
        let class = f.symbol("p/C#", 13, SymbolId::NONE);
        let eager = f.symbol("p/C#eager.", 3, class);
        let lazy = f.symbol("p/C#lazy.", 3, class);
        let deferred = f.symbol("local-deferred", 19, class);
        f.body(eager, 10, BODY_INITIALIZER, &[]);
        f.body(lazy, 50, BODY_INITIALIZER | BODY_LAZY, &[]);
        f.body(deferred, 90, BODY_INITIALIZER | BODY_DEFERRED, &[]);
        let g = f.graph(1);
        assert!(reaches(&g, class, eager));
        assert!(!reaches(&g, class, lazy));
        assert!(!reaches(&g, class, deferred));
    }
    #[test]
    fn virtual_dispatch_preserves_overloads_and_concrete_owners() {
        let mut f = Fixture::new();
        let base = f.symbol("p/Base#", 13, SymbolId::NONE);
        let sub = f.symbol("p/Sub#", 13, SymbolId::NONE);
        let caller = f.symbol("p/use().", 3, SymbolId::NONE);
        let m = f.symbol("p/Base#m().", 3, base);
        let overload = f.symbol("p/Base#m(+1).", 3, base);
        let override_m = f.symbol("p/Sub#m().", 3, sub);
        f.relation(override_m, m, RelationKind::Override);
        f.body(m, 50, 0, &[]);
        f.body(overload, 90, 0, &[]);
        f.body(override_m, 130, 0, &[]);
        f.body(caller, 10, 0, &[(Opcode::VirtualCall, m)]);
        let g = f.graph(3);
        assert!(reaches(&g, caller, m));
        assert!(reaches(&g, caller, override_m));
        assert!(!reaches(&g, caller, overload));
        let candidate = g
            .edges
            .iter()
            .find(|e| {
                e.kind == EdgeKind::VirtualCall
                    && e.target == g.node_for_symbol(override_m).unwrap()
            })
            .unwrap();
        assert_eq!(candidate.receiver, sub);
        assert!(!candidate.operation.is_none());
    }
    #[test]
    fn inherited_suite_initializers_and_proven_fixture_are_roots() {
        let mut f = Fixture::new();
        let suite = f.symbol("p/Child#", 13, SymbolId::NONE);
        let base = f.symbol("p/Base#", 13, SymbolId::NONE);
        let framework = f.symbol("org/scalatest/Suite#", 14, SymbolId::NONE);
        let contract = f.symbol(
            "org/scalatest/BeforeAndAfterEach#beforeEach().",
            3,
            framework,
        );
        let fixture = f.symbol("p/Base#beforeEach().", 3, base);
        let helper = f.symbol("p/Base#afterAll().", 3, base);
        let init = f.symbol("p/Base#`<init>`().", 21, base);
        f.relation(suite, base, RelationKind::Parent);
        f.relation(base, framework, RelationKind::Parent);
        f.relation(fixture, contract, RelationKind::Override);
        f.body(fixture, 10, 0, &[]);
        f.body(helper, 50, 0, &[]);
        f.body(init, 90, BODY_INITIALIZER, &[]);
        f.body(base, 130, BODY_INITIALIZER, &[(Opcode::Initialize, init)]);
        f.builder.facts.suites.push(SuiteRecord {
            name: f.builder.facts.symbols[suite.index()].name,
            symbol: suite,
            file: f.file,
            flags: 0,
        });
        let g = f.graph(2);
        assert!(reaches(&g, suite, fixture));
        assert!(reaches(&g, suite, init));
        assert!(!reaches(&g, suite, helper));
    }
    #[test]
    fn overriding_fixture_hides_ancestor_until_explicit_super_call() {
        let mut f = Fixture::new();
        let suite = f.symbol("p/Child#", 13, SymbolId::NONE);
        let base = f.symbol("p/Base#", 13, SymbolId::NONE);
        let framework = f.symbol("org/scalatest/Suite#", 14, SymbolId::NONE);
        let contract = f.symbol(
            "org/scalatest/BeforeAndAfterEach#beforeEach().",
            3,
            framework,
        );
        let base_fixture = f.symbol("p/Base#beforeEach().", 3, base);
        let child_fixture = f.symbol("p/Child#beforeEach().", 3, suite);
        f.relation(suite, base, RelationKind::Parent);
        f.relation(base, framework, RelationKind::Parent);
        f.relation(base_fixture, contract, RelationKind::Override);
        f.relation(child_fixture, base_fixture, RelationKind::Override);
        f.body(base_fixture, 10, 0, &[]);
        f.body(child_fixture, 50, 0, &[]);
        f.builder.facts.suites.push(SuiteRecord {
            name: f.builder.facts.symbols[suite.index()].name,
            symbol: suite,
            file: f.file,
            flags: 0,
        });
        let g = f.graph(1);
        assert!(reaches(&g, suite, child_fixture));
        assert!(!reaches(&g, suite, base_fixture));
    }
    #[test]
    fn unknown_execution_and_missing_body_stay_explicit() {
        let mut f = Fixture::new();
        let unknown = f.symbol("p/U#run().", 3, SymbolId::NONE);
        let missing = f.symbol("p/U#missing().", 3, SymbolId::NONE);
        f.body(unknown, 10, 0, &[(Opcode::Unknown, SymbolId::NONE)]);
        let g = f.graph(1);
        assert!(
            g.issues
                .iter()
                .any(|i| i.symbol == unknown && i.kind == IssueKind::UnknownExecution)
        );
        assert!(
            g.issues
                .iter()
                .any(|i| i.symbol == missing && i.kind == IssueKind::MissingSyntax)
        );
        assert!(
            g.edges
                .iter()
                .filter(|e| e.kind == EdgeKind::Guard)
                .all(|e| e.flags & EDGE_UNKNOWN != 0)
        );
    }
    #[test]
    fn out_of_body_operation_never_invents_a_call() {
        let mut f = Fixture::new();
        let a = f.symbol("p/a().", 3, SymbolId::NONE);
        let b = f.symbol("p/b().", 3, SymbolId::NONE);
        f.body(a, 10, 0, &[(Opcode::Call, b)]);
        f.body(b, 50, 0, &[]);
        f.builder.facts.operations[0].span = Span {
            start: 900,
            end: 901,
        };
        let g = f.graph(1);
        assert!(!reaches(&g, a, b));
        assert!(
            g.issues
                .iter()
                .any(|i| i.symbol == a && i.kind == IssueKind::UnknownExecution)
        );
    }
    #[test]
    fn parallel_build_is_deterministic() {
        let mut f = Fixture::new();
        let target = f.symbol("p/target().", 3, SymbolId::NONE);
        f.body(target, 900, 0, &[]);
        for i in 0..40 {
            let s = f.symbol(&format!("p/m{i}()."), 3, SymbolId::NONE);
            f.body(s, i * 21, 0, &[(Opcode::Call, target)]);
        }
        let facts = f.builder.finish().unwrap();
        let one = build(
            &facts,
            &BuildOptions {
                workers: 1,
                include_models: true,
            },
        )
        .unwrap();
        let many = build(
            &facts,
            &BuildOptions {
                workers: 4,
                include_models: true,
            },
        )
        .unwrap();
        assert_eq!(one.identity, many.identity);
        assert_eq!(one.edges, many.edges);
        assert_eq!(one.forward_edges, many.forward_edges);
    }
    #[test]
    fn parallel_suite_models_share_indexes_and_seal_deterministically() {
        let mut f = Fixture::new();
        let framework = f.symbol("org/scalatest/Suite#", 14, SymbolId::NONE);
        let base = f.symbol("p/Base#", 13, SymbolId::NONE);
        f.relation(base, framework, RelationKind::Parent);
        let ctor = f.symbol("p/Base#`<init>`().", 21, base);
        f.body(ctor, 10, BODY_INITIALIZER, &[]);
        f.body(base, 50, BODY_INITIALIZER, &[(Opcode::Initialize, ctor)]);
        for i in 0..40 {
            let suite = f.symbol(&format!("p/Suite{i}#"), 13, SymbolId::NONE);
            f.relation(suite, base, RelationKind::Parent);
            f.builder.facts.suites.push(SuiteRecord {
                name: f.builder.facts.symbols[suite.index()].name,
                symbol: suite,
                file: f.file,
                flags: 0,
            });
        }
        let facts = f.builder.finish().unwrap();
        let one = build(
            &facts,
            &BuildOptions {
                workers: 1,
                include_models: true,
            },
        )
        .unwrap();
        let many = build(
            &facts,
            &BuildOptions {
                workers: 4,
                include_models: true,
            },
        )
        .unwrap();
        assert_eq!(one.identity, many.identity);
        assert_eq!(one.edges, many.edges);
        for suite in &facts.suites {
            assert!(reaches(&many, suite.symbol, ctor));
        }
    }
    #[test]
    fn parallel_csr_matches_serial_for_large_duplicate_target_frontier() {
        let mut f = Fixture::new();
        let caller = f.symbol("p/caller().", 3, SymbolId::NONE);
        let target = f.symbol("p/target().", 3, SymbolId::NONE);
        let calls = vec![(Opcode::Call, target); 65_537];
        f.body(caller, 10, 0, &calls);
        f.body(target, 50, 0, &[]);
        let facts = f.builder.finish().unwrap();
        let serial = build(
            &facts,
            &BuildOptions {
                workers: 1,
                include_models: true,
            },
        )
        .unwrap();
        let parallel = build(
            &facts,
            &BuildOptions {
                workers: 4,
                include_models: true,
            },
        )
        .unwrap();
        assert_eq!(serial.edges, parallel.edges);
        assert_eq!(serial.forward_offsets, parallel.forward_offsets);
        assert_eq!(serial.forward_edges, parallel.forward_edges);
        assert_eq!(serial.reverse_offsets, parallel.reverse_offsets);
        assert_eq!(serial.reverse_edges, parallel.reverse_edges);
        assert_eq!(
            parallel
                .predecessors(parallel.node_for_symbol(target).unwrap())
                .count(),
            calls.len()
        );
    }
    #[test]
    fn tied_occurrence_spans_keep_the_same_owner_across_fact_order() {
        fn projected(order: [&str; 2], extra: bool, workers: usize) -> Vec<(String, String, u32)> {
            let mut fixture = Fixture::new();
            if extra {
                let previous = fixture.file;
                let other_path = fixture.builder.intern("unrelated.scala").unwrap();
                fixture.file = FileId(fixture.builder.facts.files.len() as u32);
                fixture.builder.facts.files.push(FileRecord {
                    path: other_path,
                    ..fixture.builder.facts.files[previous.index()]
                });
                let other = fixture.symbol("p/unrelated().", 3, SymbolId::NONE);
                fixture.body(other, 10, BODY_DEFERRED, &[]);
                fixture.file = previous;
            }
            for name in order {
                let owner = fixture.symbol(name, 3, SymbolId::NONE);
                fixture.body(owner, 10, BODY_DEFERRED, &[]);
            }
            for (name, start) in [
                ("p/Referenced#", 12),
                ("p/AlsoReferenced#", 16),
                ("@byname:p/caller().:0", 18),
            ] {
                let target = fixture.builder.ensure_symbol(name, fixture.file).unwrap();
                fixture.builder.facts.occurrences.push(OccurrenceRecord {
                    file: fixture.file,
                    symbol: target,
                    span: Span {
                        start,
                        end: start + 1,
                    },
                    role: 1,
                    ordinal: 0,
                });
            }
            let facts = fixture.builder.finish().unwrap();
            let graph = build(
                &facts,
                &BuildOptions {
                    workers,
                    include_models: false,
                },
            )
            .unwrap();
            let name = |node: NodeId| {
                facts
                    .text(facts.symbols[graph.nodes[node.index()].symbol.index()].name)
                    .to_owned()
            };
            let mut edges: Vec<_> = graph
                .edges
                .iter()
                .filter(|edge| edge.kind == EdgeKind::Compile && !edge.occurrence.is_none())
                .map(|edge| (name(edge.source), name(edge.target), edge.occurrence.0))
                .collect();
            edges.sort_unstable();
            edges
        }

        let a = "@byname:p/caller().:0";
        let z = "@synthetic-closure:p/caller().:0";
        let original = projected([a, z], false, 1);
        let reordered = projected([z, a], true, 4);
        assert_eq!(original, reordered);
        assert_eq!(
            original,
            [
                (a.to_owned(), "p/AlsoReferenced#".to_owned(), 1),
                (a.to_owned(), "p/Referenced#".to_owned(), 0),
                (z.to_owned(), a.to_owned(), 2),
            ]
        );
    }

    #[test]
    fn source_declaration_dependencies_keep_their_file_when_execution_uses_a_binary_recipe() {
        let mut fixture = Fixture::new();
        let declaration_file = fixture.file;
        let suite = fixture.symbol("org/scalatest/Suite#", 14, SymbolId::NONE);
        fixture.builder.facts.symbols[suite.index()].span = Span { start: 10, end: 20 };
        let string = fixture
            .builder
            .ensure_symbol("java/lang/String#", declaration_file)
            .unwrap();
        fixture.builder.facts.occurrences.push(OccurrenceRecord {
            file: declaration_file,
            symbol: string,
            span: Span { start: 12, end: 13 },
            role: 1,
            ordinal: 0,
        });
        let binary_file = FileId(fixture.builder.facts.files.len() as u32);
        let path = fixture
            .builder
            .intern("scalatest-core.jar!/org/scalatest/Suite.class")
            .unwrap();
        let empty = fixture.builder.intern("").unwrap();
        fixture.builder.facts.files.push(FileRecord {
            path,
            source: empty,
            revision: StrId::NONE,
            context: fixture.builder.facts.files[declaration_file.index()].context,
            source_hash: ContentHash::default(),
            flags: FILE_BINARY_SOURCE,
        });
        fixture.builder.facts.bodies.push(BodyRecord {
            symbol: suite,
            file: binary_file,
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange::default(),
            parameters: IdRange::default(),
            body_hash: ContentHash::default(),
            flags: BODY_BINARY_RECIPE | BODY_INITIALIZER,
        });
        let facts = fixture.builder.finish().unwrap();
        let graph = build(
            &facts,
            &BuildOptions {
                workers: 2,
                include_models: true,
            },
        )
        .unwrap();
        let execution = graph.node_for_symbol(suite).unwrap();
        assert_eq!(graph.nodes[execution.index()].file, binary_file);
        assert_eq!(graph.nodes[execution.index()].body, BodyId(0));
        let declaration = graph
            .successors(execution)
            .find(|(_, edge)| {
                edge.kind == EdgeKind::Compile
                    && graph.nodes[edge.target.index()].file == declaration_file
            })
            .map(|(_, edge)| edge.target)
            .expect("canonical symbol retains its declaration dependency");
        assert!(graph.nodes[declaration.index()].body.is_none());
        assert!(graph.successors(declaration).any(|(_, edge)| edge.target
            == graph.node_for_symbol(string).unwrap()
            && edge.occurrence == OccurrenceId(0)));
        assert!(
            !graph
                .successors(execution)
                .any(|(_, edge)| edge.kind.is_execution() && edge.target == declaration)
        );
        for edge in &graph.edges {
            if !edge.occurrence.is_none() {
                assert_eq!(
                    graph.nodes[edge.source.index()].file,
                    facts.occurrences[edge.occurrence.index()].file
                );
            }
        }
        let other = build(
            &facts,
            &BuildOptions {
                workers: 1,
                include_models: true,
            },
        )
        .unwrap();
        assert_eq!(graph.identity, other.identity);
        assert_eq!(graph.edges, other.edges);
    }
    #[test]
    fn only_plain_trait_super_retains_receiver_dependent_candidates() {
        let mut f = Fixture::new();
        let base = f.symbol("p/Base#", 14, SymbolId::NONE);
        let first = f.symbol("p/First#", 14, SymbolId::NONE);
        let last = f.symbol("p/Last#", 14, SymbolId::NONE);
        let base_method = f.symbol("p/Base#run().", 3, base);
        let first_method = f.symbol("p/First#run().", 3, first);
        let last_method = f.symbol("p/Last#run().", 3, last);
        f.builder.facts.symbols[first_method.index()].properties = 4;
        f.body(base_method, 10, 0, &[]);
        let body = f.body(
            first_method,
            50,
            0,
            &[(Opcode::Call, base_method), (Opcode::Call, base_method)],
        );
        f.body(last_method, 90, 0, &[]);
        f.relation(first_method, base_method, RelationKind::Override);
        f.relation(last_method, base_method, RelationKind::Override);
        let operations = f.builder.facts.bodies[body.index()].operations;
        f.builder.facts.operations[operations.start as usize].flags = OP_SUPER;
        f.builder.facts.operations[operations.start as usize + 1].flags =
            OP_SUPER | OP_QUALIFIED_SUPER;
        let class = f.symbol("p/Concrete#", 13, SymbolId::NONE);
        let class_method = f.symbol("p/Concrete#run().", 3, class);
        let class_body = f.body(class_method, 130, 0, &[(Opcode::Call, base_method)]);
        let class_operation = f.builder.facts.bodies[class_body.index()].operations.start;
        f.builder.facts.operations[class_operation as usize].flags = OP_SUPER;
        let graph = f.graph(2);
        let targets = |operation| {
            graph
                .edges
                .iter()
                .filter(|edge| {
                    edge.kind == EdgeKind::Call && edge.operation == OperationId(operation)
                })
                .map(|edge| graph.nodes[edge.target.index()].symbol)
                .collect::<Vec<_>>()
        };
        let candidates = targets(operations.start);
        for method in [base_method, first_method, last_method] {
            assert!(candidates.contains(&method));
        }
        assert_eq!(targets(operations.start + 1), vec![base_method]);
        assert_eq!(targets(class_operation), vec![base_method]);
    }
    #[test]
    fn binary_static_phase_and_fields_do_not_prove_instance_construction_or_execute_packages() {
        let mut f = Fixture::new();
        let package = f.symbol("p/", 11, SymbolId::NONE);
        f.builder.facts.symbols[package.index()].flags = 0;
        let class = f.symbol("@jvm/type", 13, package);
        let initializer = f.symbol("@jvm/clinit", 3, class);
        let field = f.symbol("@jvm/field", 20, class);
        for symbol in [class, initializer, field] {
            f.builder.facts.symbols[symbol.index()].flags = SYMBOL_NATIVE_BINARY;
        }
        f.body(
            initializer,
            10,
            BODY_INITIALIZER | BODY_BINARY_RECIPE | BODY_STATIC_INITIALIZER,
            &[],
        );
        let caller = f.symbol("p/caller().", 3, SymbolId::NONE);
        f.body(
            caller,
            50,
            0,
            &[
                (Opcode::Initialize, initializer),
                (Opcode::Allocate, class),
                (Opcode::LoadField, field),
            ],
        );
        let graph = f.graph(2);
        assert!(reaches(&graph, caller, initializer));
        assert!(
            !reaches(&graph, caller, package),
            "a type allocation cannot initialize its lexical package owner"
        );
        assert!(
            !graph
                .issues
                .iter()
                .any(|issue| issue.symbol == field && issue.kind == IssueKind::UnknownExecution)
        );
        assert!(
            graph
                .issues
                .iter()
                .any(|issue| issue.symbol == class && issue.kind == IssueKind::UnknownExecution),
            "a static phase is not an instance constructor recipe"
        );
    }
    #[test]
    fn constructor_overloads_run_only_through_explicit_constructor_calls() {
        let mut f = Fixture::new();
        let class = f.symbol("p/Secondary#", 13, SymbolId::NONE);
        let primary = f.symbol("p/Secondary#`<init>`().", 21, class);
        let secondary = f.symbol("p/Secondary#`<init>`(+1).", 21, class);
        let changed = f.symbol("p/Effects.changed().", 3, SymbolId::NONE);
        let explicit = f.symbol("p/explicit().", 3, SymbolId::NONE);
        let delegated = f.symbol("p/delegated().", 3, SymbolId::NONE);
        f.body(class, 10, BODY_INITIALIZER, &[]);
        f.body(
            primary,
            50,
            BODY_INITIALIZER,
            &[(Opcode::Initialize, class)],
        );
        f.body(
            secondary,
            90,
            BODY_INITIALIZER,
            &[(Opcode::Call, primary), (Opcode::Call, changed)],
        );
        f.body(changed, 130, 0, &[]);
        f.body(explicit, 170, 0, &[(Opcode::Allocate, primary)]);
        f.body(delegated, 210, 0, &[(Opcode::Allocate, secondary)]);
        let graph = f.graph(2);
        assert!(!reaches(&graph, class, secondary));
        assert!(!reaches(&graph, explicit, changed));
        assert!(reaches(&graph, delegated, secondary));
        assert!(reaches(&graph, delegated, primary));
        assert!(reaches(&graph, delegated, changed));
    }
    #[test]
    fn owned_constructor_or_field_body_alone_does_not_certify_a_source_class_scope() {
        for constructor in [false, true] {
            let mut f = Fixture::new();
            let class = f.symbol("p/Unproven#", 13, SymbolId::NONE);
            let member = f.symbol(
                if constructor {
                    "p/Unproven#`<init>`()."
                } else {
                    "p/Unproven#field."
                },
                if constructor { 21 } else { 3 },
                class,
            );
            f.body(member, 10, BODY_INITIALIZER, &[]);
            let graph = f.graph(1);
            assert!(
                graph
                    .issues
                    .iter()
                    .any(|issue| issue.symbol == class && issue.kind == IssueKind::MissingSyntax)
            );
            assert_eq!(reaches(&graph, class, member), !constructor);
        }
    }
    #[test]
    fn verified_binary_parent_metadata_retains_hierarchy_without_interface_execution() {
        let mut f = Fixture::new();
        let class = f.symbol("@jvm/AbstractFunction1", 13, SymbolId::NONE);
        let interface = f.symbol("@jvm/Function1", 14, SymbolId::NONE);
        for id in [class, interface] {
            f.builder.facts.symbols[id.index()].flags = SYMBOL_NATIVE_BINARY;
        }
        let binary_file = FileId(f.builder.facts.files.len() as u32);
        f.builder.facts.files.push(FileRecord {
            flags: FILE_BINARY_SOURCE,
            ..f.builder.facts.files[f.file.index()]
        });
        f.builder.facts.relations.push(RelationRecord {
            source: class,
            target: interface,
            file: binary_file,
            kind: RelationKind::Parent,
        });
        let graph = f.graph(2);
        assert!(!reaches(&graph, class, interface));
        assert!(graph.successors(graph.node_for_symbol(class).unwrap()).any(
            |(_, edge)| edge.target == graph.node_for_symbol(interface).unwrap()
                && edge.kind == EdgeKind::Compile
        ));
    }
    #[test]
    fn runtime_callback_flags_apply_only_to_external_compiler_contracts() {
        let mut f = Fixture::new();
        let caller = f.symbol("p/caller().", 3, SymbolId::NONE);
        let external = f
            .builder
            .ensure_symbol("scala/collection/IterableOnceOps#foreach().", f.file)
            .unwrap();
        let source = f.symbol("scala/collection/IterableOnceOps#map().", 3, SymbolId::NONE);
        f.body(source, 50, 0, &[]);
        f.body(
            caller,
            10,
            0,
            &[(Opcode::Call, external), (Opcode::Call, source)],
        );
        let g = f.graph(1);
        let outgoing: Vec<_> = g
            .successors(g.node_for_symbol(caller).unwrap())
            .map(|(_, e)| e)
            .collect();
        assert!(
            outgoing
                .iter()
                .any(|e| e.target == g.node_for_symbol(external).unwrap()
                    && e.flags & EDGE_CALLBACK_IMMEDIATE != 0)
        );
        assert!(
            outgoing
                .iter()
                .filter(|e| e.target == g.node_for_symbol(source).unwrap())
                .all(|e| e.flags & EDGE_CALLBACK_IMMEDIATE == 0)
        );
        assert!(
            g.issues
                .iter()
                .any(|i| i.symbol == external && i.kind == IssueKind::UnknownExecution)
        );
    }
    #[test]
    fn callback_argument_certificate_stays_on_the_exact_external_model_edge() {
        let mut f = Fixture::new();
        let caller = f.symbol("p/caller().", 3, SymbolId::NONE);
        let external = f
            .builder
            .ensure_symbol("scala/collection/IterableOnceOps#foreach().", f.file)
            .unwrap();
        let other = f
            .builder
            .ensure_symbol("scala/collection/ListOps#foreach().", f.file)
            .unwrap();
        let ordinary = f.builder.ensure_symbol("p/external().", f.file).unwrap();
        let source = f.symbol("scala/collection/IterableOnceOps#map().", 3, SymbolId::NONE);
        f.body(source, 50, 0, &[]);
        f.relation(other, external, RelationKind::Override);
        f.body(
            caller,
            10,
            0,
            &[
                (Opcode::VirtualCall, external),
                (Opcode::Call, source),
                (Opcode::Call, ordinary),
            ],
        );
        for op in &mut f.builder.facts.operations {
            op.flags = encode_callback_argument(0).unwrap();
        }
        let g = f.graph(1);
        let flags = |target| {
            g.successors(g.node_for_symbol(caller).unwrap())
                .find(|(_, edge)| {
                    edge.target == g.node_for_symbol(target).unwrap() && edge.kind.is_execution()
                })
                .unwrap()
                .1
                .flags
        };
        assert_eq!(callback_argument_slot(flags(external)), Some(0));
        assert_ne!(flags(external) & EDGE_CALLBACK_IMMEDIATE, 0);
        assert_eq!(callback_argument_slot(flags(other)), None);
        assert_eq!(callback_argument_slot(flags(source)), None);
        assert_eq!(callback_argument_slot(flags(ordinary)), None);
        assert!(
            g.issues
                .iter()
                .any(|issue| issue.symbol == external && issue.kind == IssueKind::UnknownExecution)
        );
    }
    #[test]
    fn object_initialization_uses_exact_owner_not_companion_class() {
        let mut f = Fixture::new();
        let object = f.symbol("p/Companion.", 10, SymbolId::NONE);
        let class = f.symbol("p/Companion#", 13, SymbolId::NONE);
        let method = f.symbol("p/Companion.run().", 3, object);
        let object_init = f.symbol("p/Companion.field.", 3, object);
        let class_init = f.symbol("p/Companion#field.", 3, class);
        let caller = f.symbol("p/caller().", 3, SymbolId::NONE);
        f.body(object_init, 10, BODY_INITIALIZER, &[]);
        f.body(class_init, 50, BODY_INITIALIZER, &[]);
        f.body(method, 90, 0, &[]);
        f.body(caller, 130, 0, &[(Opcode::Call, method)]);
        let g = f.graph(1);
        assert!(reaches(&g, caller, object_init));
        assert!(!reaches(&g, caller, class_init));
    }
    #[test]
    fn declaring_nested_types_does_not_eagerly_initialize_them() {
        let mut f = Fixture::new();
        let outer = f.symbol("p/Outer#", 13, SymbolId::NONE);
        let inner = f.symbol("p/Outer#Inner#", 13, outer);
        let object = f.symbol("p/Outer#Nested.", 10, outer);
        f.body(outer, 10, BODY_INITIALIZER, &[]);
        f.body(inner, 50, BODY_INITIALIZER, &[]);
        f.body(object, 90, BODY_INITIALIZER, &[]);
        let g = f.graph(1);
        assert!(!reaches(&g, outer, inner));
        assert!(!reaches(&g, outer, object));
    }
}
