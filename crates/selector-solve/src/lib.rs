//! Parallel context-sensitive fixed points over immutable facts and graph data.
//! Workers own bounded scratch and emit compact deltas. Completed contexts are
//! shared by canonical semantic inputs; positive and missing-slot reads subscribe
//! to the exact slot, including recursive summaries and lexical captures.
pub mod cache;
pub mod context_policy;
pub mod continuation;
pub mod finalization;
pub mod provider_scope;
pub mod replay;
pub mod telemetry;
pub mod work_census;
pub use cache::{CacheAction, CacheEvent, CacheIdentity, CacheReason, ReuseMetrics};
pub use context_policy::{
    CallbackShape, CallbackShapeAtom, CallbackShapeId, CallbackShapes, ContextPolicy,
};
pub(crate) use context_policy::{PolicyContextKey, cache_policy_key, context_index_key};
use rayon::prelude::*;
use selector_domain::*;
use selector_facts::*;
use selector_graph::*;
use selector_issue::{RuntimeIssueReason, RuntimeIssueSite};
use selector_result::*;
use selector_transfer::*;
use selector_types::*;
use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::{Arc, Mutex};
use std::time::Instant;
pub use telemetry::{
    SolveControl, SolveEvent, SolveObserver, SolvePhase, StopReason, WorkCounters, WorkOrigin,
};
pub use work_census::{CensusOptions, WorkRow};

#[derive(Clone, Debug)]
pub struct SolveOptions {
    pub workers: usize,
    pub memory_budget_bytes: usize,
    pub max_contexts: usize,
    pub max_set_members: usize,
    pub max_steps: u64,
    pub shard_count: usize,
    /// Maximum contexts evaluated against one immutable publication snapshot.
    /// This is a global round size, independent of workers and work shards.
    pub quantum: usize,
    pub scratch_bytes_per_worker: usize,
    /// None executes the suite catalogue. Some, including an empty slice,
    /// executes exactly the caller's admitted root frontier.
    pub execution_roots: Option<Arc<[ExecutionRoot]>>,
    pub observer: Option<Arc<dyn SolveObserver>>,
    pub control: Option<Arc<SolveControl>>,
    pub census: CensusOptions,
    pub context_policy: ContextPolicy,
    /// Reporting only: execution, dependency tracking and node proofs are unchanged.
    pub retain_context_evidence: bool,
}
impl Default for SolveOptions {
    fn default() -> Self {
        Self {
            workers: std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(1),
            memory_budget_bytes: 2 * 1024 * 1024 * 1024,
            max_contexts: 1_000_000,
            max_set_members: 64,
            max_steps: 100_000_000,
            shard_count: 0,
            quantum: 256,
            scratch_bytes_per_worker: 8 * 1024 * 1024,
            execution_roots: None,
            observer: None,
            control: None,
            census: CensusOptions::default(),
            context_policy: ContextPolicy::Exact,
            retain_context_evidence: true,
        }
    }
}
#[derive(Clone, Copy, Debug)]
pub struct AnalysisSeeds<'a> {
    pub execution: &'a [NodeId],
    pub declarations: &'a [NodeId],
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExecutionRoot {
    pub node: NodeId,
    pub receiver: SymbolId,
}
#[derive(Clone, Copy, Debug)]
struct Context {
    key: ContextKey,
    value: Value,
    version: u64,
    evaluated: bool,
    widened: bool,
    callback_shape: CallbackShapeId,
    /// Monotone local effect uncertainty from every committed evaluation.
    /// Transitive closure is checked over all retained contexts at finalization.
    effects_open: bool,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct ContextCall {
    source: ContextId,
    target: ContextId,
    operation: OperationId,
    kind: EdgeKind,
    edge: EdgeId,
    binding: u32,
}
#[derive(Clone, Copy, Debug)]
struct SlotValue {
    value: Value,
    version: u64,
}
#[derive(Clone, Copy, Debug)]
struct Capture {
    receiver: Value,
    arguments: FrameId,
    version: u64,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct ClosureFamily {
    site: OperationId,
    receiver: Value,
    arguments: FrameId,
    origins: Value,
}
mod capture_origins;
struct Batch {
    scratch: Scratch,
    outputs: Vec<(ContextId, Evaluation)>,
    work: Vec<ContextId>,
    attempted: usize,
}
impl Batch {
    fn new(max_members: usize) -> Self {
        Self {
            scratch: Scratch::new(max_members),
            outputs: Vec::new(),
            work: Vec::new(),
            attempted: 0,
        }
    }
}
/// Shared CPU runtime. Scratch leases are returned only after every borrowed
/// worker value has been committed. The idle bank has one bounded batch set;
/// concurrent sessions can borrow the pool without blocking on scratch owners.
#[derive(Clone)]
pub struct SolverRuntime {
    inner: Arc<RuntimeInner>,
}
struct RuntimeInner {
    pool: rayon::ThreadPool,
    idle: Mutex<Option<Vec<Batch>>>,
    workers: usize,
    max_members: usize,
    scratch_limit: usize,
    cache: Option<cache::CacheConfig>,
}
impl SolverRuntime {
    pub fn new(options: &SolveOptions) -> Result<Self, Error> {
        if options.workers == 0
            || options.max_contexts == 0
            || options.max_set_members == 0
            || options.quantum == 0
            || options.max_steps == 0
        {
            return Err(Error::Invalid("solver options"));
        }
        let admitted =
            (options.memory_budget_bytes / options.scratch_bytes_per_worker.max(4096)).max(1);
        let workers = options.workers.min(admitted).max(1);
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(workers)
            .build()
            .map_err(|e| Error::Message(e.to_string()))?;
        pool.broadcast(|_| {
            // Initialize the standard thread handle/TLS on every worker before
            // callers start allocation windows, including workers with no work.
            let _ = std::thread::current();
        });
        Ok(Self {
            inner: Arc::new(RuntimeInner {
                pool,
                idle: Mutex::new(None),
                workers,
                max_members: options.max_set_members,
                scratch_limit: options.scratch_bytes_per_worker,
                cache: None,
            }),
        })
    }
    pub fn with_cache_directory(
        options: &SolveOptions,
        directory: &std::path::Path,
        producer: ContentHash,
    ) -> Result<Self, Error> {
        std::fs::create_dir_all(directory)?;
        let mut runtime = Self::new(options)?;
        Arc::get_mut(&mut runtime.inner).expect("new runtime").cache = Some(cache::CacheConfig {
            directory: directory.to_owned(),
            producer,
        });
        Ok(runtime)
    }
    pub fn workers(&self) -> usize {
        self.inner.workers
    }
    pub fn retained_bytes(&self) -> usize {
        self.inner
            .idle
            .lock()
            .unwrap()
            .as_ref()
            .map(|b| {
                b.capacity() * std::mem::size_of::<Batch>()
                    + b.iter().map(batch_bytes).sum::<usize>()
            })
            .unwrap_or(0)
    }
    fn lease(&self, options: &SolveOptions) -> Vec<Batch> {
        if options.max_set_members == self.inner.max_members {
            if let Some(batches) = self.inner.idle.lock().unwrap().take() {
                return batches;
            }
        }
        let shards = if options.shard_count == 0 {
            self.workers()
        } else {
            options.shard_count.max(1).min(self.workers() * 4)
        };
        (0..shards)
            .map(|_| Batch::new(options.max_set_members))
            .collect()
    }
}
fn batch_bytes(b: &Batch) -> usize {
    b.scratch.owned_bytes()
        + b.work.capacity() * 4
        + b.outputs.capacity() * std::mem::size_of::<(ContextId, Evaluation)>()
        + b.outputs
            .iter()
            .map(|(_, o)| evaluation_bytes(o))
            .sum::<usize>()
}
struct ReadWorld<'a> {
    facts: &'a FactSnapshot,
    graph: &'a ProgramGraph,
    types: &'a TypeIndex,
    pool: &'a ValuePool,
    frames: &'a FramePool,
    contexts: &'a [Context],
    index: &'a HashMap<PolicyContextKey, ContextId>,
    callback_shapes: &'a CallbackShapes,
    slots: &'a HashMap<Slot, SlotValue>,
    heap_owners: &'a HeapOwners,
    captures: &'a HashMap<u32, Capture>,
    families: &'a HashMap<ClosureFamily, u32>,
    capture_origins: &'a [Value],
    context_policy: ContextPolicy,
    provider_scope: Option<&'a provider_scope::ProviderScope>,
}
impl World for ReadWorld<'_> {
    fn values(&self) -> &ValuePool {
        self.pool
    }
    fn summary(
        &self,
        node: NodeId,
        receiver: Value,
        args: &[Value],
        local: &ValuePool,
        scratch: &mut Vec<Value>,
    ) -> SummaryRead {
        if self.provider_scope.is_some_and(|scope| scope.blocks(node)) {
            return SummaryRead {
                context: None,
                value: Value::TOP,
                version: 0,
                present: false,
            };
        }
        let missing = SummaryRead {
            context: None,
            value: Value::EMPTY,
            version: 0,
            present: false,
        };
        let static_init = is_static_initializer(self.facts, self.graph, node);
        let receiver = if static_init {
            Some(Value::EMPTY)
        } else if let Some(module) = self
            .types
            .global_module_owner(self.graph.nodes[node.index()].symbol)
        {
            self.pool.lookup(
                &[Atom {
                    kind: AtomKind::Object,
                    site: OperationId::NONE,
                    symbol: module,
                    binding: 0,
                }],
                0,
            )
        } else {
            self.pool.lookup(local.members(receiver), receiver.unknown)
        };
        let Some(receiver) = receiver else {
            return missing;
        };
        scratch.clear();
        // The no-body kernel never consumes actual parameters. Structural
        // edges forward only the receiver, and opaque leaves return their
        // node-scoped unknown/bound. Match admission rather than partitioning
        // identical summaries by ignored callback argument identities.
        for arg in if static_init || self.graph.nodes[node.index()].body.is_none() {
            &[][..]
        } else {
            args
        } {
            let Some(v) = self.pool.lookup(local.members(*arg), arg.unknown) else {
                return missing;
            };
            scratch.push(v);
        }
        let shape = if self.context_policy == ContextPolicy::Exact {
            CallbackShapeId(0)
        } else {
            let Some(shape) = self.callback_shapes.lookup(self.pool, scratch) else {
                return missing;
            };
            shape
        };
        let exact = self
            .frames
            .lookup(scratch)
            .and_then(|arguments| {
                self.index.get(&PolicyContextKey {
                    key: ContextKey {
                        node,
                        receiver,
                        arguments,
                    },
                    shape,
                })
            })
            .copied();
        let id = exact.or_else(|| {
            if self.context_policy == ContextPolicy::Exact {
                return None;
            }
            self.index
                .get(&PolicyContextKey {
                    key: ContextKey {
                        node,
                        receiver,
                        arguments: FrameId(u32::MAX),
                    },
                    shape,
                })
                .copied()
                .filter(|id| {
                    !capture_origins::needs_exact_arguments(
                        self.pool,
                        self.capture_origins,
                        scratch,
                    ) && context_policy::arguments_subsumed(
                        self.pool,
                        self.frames.get(self.contexts[id.index()].key.arguments),
                        scratch,
                    )
                })
        });
        let Some(id) = id else {
            return missing;
        };
        let c = self.contexts[id.index()];
        SummaryRead {
            context: Some(id),
            value: c.value,
            version: c.version,
            present: c.evaluated,
        }
    }
    fn slot(&self, slot: Slot) -> (Value, u64, bool) {
        self.slots
            .get(&slot)
            .map(|v| (v.value, v.version, true))
            .unwrap_or((Value::EMPTY, 0, false))
    }
    fn heap_owner(&self, key: HeapOwnerKey) -> Option<u32> {
        self.heap_owners.lookup(key)
    }
    fn capture(&self, binding: u32) -> Option<(Value, &[Value], u64)> {
        self.captures
            .get(&binding)
            .map(|c| (c.receiver, self.frames.get(c.arguments), c.version))
    }
    fn binding(
        &self,
        site: OperationId,
        receiver: Value,
        args: &[Value],
        local: &ValuePool,
        atoms: &mut Vec<Atom>,
        values: &mut Vec<Value>,
    ) -> Option<u32> {
        let origins =
            capture_origins::lookup(self.pool, local, receiver, args, self.capture_origins)?;
        let receiver = self.pool.lookup_family(local, receiver, atoms)?;
        values.clear();
        for arg in args {
            values.push(self.pool.lookup_family(local, *arg, atoms)?);
        }
        let arguments = self.frames.lookup(values)?;
        self.families
            .get(&ClosureFamily {
                site,
                receiver,
                arguments,
                origins,
            })
            .copied()
    }
}

/// Flat postings index for uncertainty scopes; construction and querying are
/// linear in input/reached records, never nodes multiplied by all diagnostics.
struct IssueIndex {
    node_offsets: Vec<usize>,
    node_ids: Vec<usize>,
    file_offsets: Vec<usize>,
    file_ids: Vec<usize>,
    global: Vec<usize>,
}
impl IssueIndex {
    fn new(graph: &ProgramGraph, files: usize) -> Self {
        let mut node_offsets = vec![0; graph.nodes.len() + 1];
        let mut file_offsets = vec![0; files + 1];
        let mut global = Vec::new();
        for (i, issue) in graph.issues.iter().enumerate() {
            if !issue.node.is_none() {
                node_offsets[issue.node.index() + 1] += 1;
            } else if !issue.file.is_none() {
                file_offsets[issue.file.index() + 1] += 1;
            } else {
                global.push(i);
            }
        }
        for i in 1..node_offsets.len() {
            node_offsets[i] += node_offsets[i - 1];
        }
        for i in 1..file_offsets.len() {
            file_offsets[i] += file_offsets[i - 1];
        }
        let mut node_ids = vec![0; *node_offsets.last().unwrap_or(&0)];
        let mut file_ids = vec![0; *file_offsets.last().unwrap_or(&0)];
        let mut nodes = node_offsets[..graph.nodes.len()].to_vec();
        let mut files = file_offsets[..files].to_vec();
        for (i, issue) in graph.issues.iter().enumerate() {
            if !issue.node.is_none() {
                node_ids[nodes[issue.node.index()]] = i;
                nodes[issue.node.index()] += 1;
            } else if !issue.file.is_none() {
                file_ids[files[issue.file.index()]] = i;
                files[issue.file.index()] += 1;
            }
        }
        Self {
            node_offsets,
            node_ids,
            file_offsets,
            file_ids,
            global,
        }
    }
    fn nodes(&self, node: NodeId) -> &[usize] {
        &self.node_ids[self.node_offsets[node.index()]..self.node_offsets[node.index() + 1]]
    }
    fn files(&self, file: FileId) -> &[usize] {
        if file.is_none() {
            &[]
        } else {
            &self.file_ids[self.file_offsets[file.index()]..self.file_offsets[file.index() + 1]]
        }
    }
    fn owned_bytes(&self) -> usize {
        (self.node_offsets.capacity()
            + self.node_ids.capacity()
            + self.file_offsets.capacity()
            + self.file_ids.capacity()
            + self.global.capacity())
            * std::mem::size_of::<usize>()
    }
}
fn obligation_key(issue: Obligation) -> (u32, u32, u32, u32) {
    (
        issue.kind as u32,
        issue.file.0,
        issue.symbol.0,
        issue.detail.0,
    )
}
fn runtime_issue_key(site: Option<RuntimeIssueSite>) -> (u32, u32, u32) {
    site.map(|site| (site.kind as u32, site.operation.0, site.reason as u32))
        .unwrap_or((u32::MAX, u32::MAX, u32::MAX))
}

/// Owns reusable canonical execution summaries. Drop releases all query owners.
/// Repeated change queries reuse the completed execution fixed point exactly.
pub struct QuerySession<'a> {
    facts: &'a FactSnapshot,
    graph: &'a ProgramGraph,
    issue_postings: IssueIndex,
    options: SolveOptions,
    pool: ValuePool,
    frames: FramePool,
    types: TypeIndex,
    contexts: Vec<Context>,
    index: HashMap<PolicyContextKey, ContextId>,
    callback_shapes: CallbackShapes,
    calls: Vec<ContextCall>,
    call_index: HashSet<ContextCall>,
    dependencies: Dependencies,
    slots: HashMap<Slot, SlotValue>,
    heap_owners: HeapOwners,
    captures: HashMap<u32, Capture>,
    closure_families: HashMap<ClosureFamily, u32>,
    capture_origins: Vec<Value>,
    field_reads: HashSet<Slot>,
    writes: HashSet<(ContextId, Slot)>,
    reuse: ReuseMetrics,
    ready: Vec<ContextId>,
    roots: Vec<ContextId>,
    issues: Vec<Obligation>,
    issue_index: HashSet<(u32, u32, u32, u32)>,
    issue_contexts: HashSet<ContextId>,
    // One actual transfer occurrence per uncertain context, rather than an
    // Option on every context or a copy of each evaluation's issue list.
    runtime_issue_sites: HashMap<ContextId, RuntimeIssueSite>,
    completion: Completion,
    metrics: AnalysisMetrics,
    runtime: SolverRuntime,
    batches: Vec<Batch>,
    sealed: bool,
    pending_roots: Vec<ExecutionRoot>,
    stop_reason: Option<StopReason>,
    rounds: u64,
    counters: WorkCounters,
    census: work_census::WorkCensus,
    observed_at: Instant,
    started_at: Instant,
    context_families: HashMap<(NodeId, Value, CallbackShapeId), usize>,
    policy_arguments: Vec<Value>,
    provider_scope: Option<provider_scope::ProviderScope>,
}
impl<'a> QuerySession<'a> {
    pub fn new(
        facts: &'a FactSnapshot,
        graph: &'a ProgramGraph,
        options: &SolveOptions,
    ) -> Result<Self, Error> {
        Self::with_runtime(facts, graph, options, &SolverRuntime::new(options)?)
    }
    pub fn with_runtime(
        facts: &'a FactSnapshot,
        graph: &'a ProgramGraph,
        options: &SolveOptions,
        runtime: &SolverRuntime,
    ) -> Result<Self, Error> {
        let mut session = Self::with_runtime_unrestored(facts, graph, options, runtime)?;
        if let Some(config) = runtime.inner.cache.as_ref() {
            session.emit(SolvePhase::CacheAdmission, true, None);
            session.reuse = cache::restore(&mut session, config)?;
        }
        Ok(session)
    }
    pub(crate) fn with_runtime_unrestored(
        facts: &'a FactSnapshot,
        graph: &'a ProgramGraph,
        options: &SolveOptions,
        runtime: &SolverRuntime,
    ) -> Result<Self, Error> {
        facts.validate()?;
        graph.validate()?;
        if graph.facts_identity != facts.identity {
            return Err(Error::Invalid("graph fact identity"));
        }
        if graph.symbol_nodes.len() != facts.symbols.len() {
            return Err(Error::Invalid("graph symbol inventory"));
        }
        for node in &graph.nodes {
            if node.symbol.index() >= facts.symbols.len()
                || (!node.file.is_none() && node.file.index() >= facts.files.len())
                || (!node.body.is_none()
                    && (node.body.index() >= facts.bodies.len()
                        || facts.bodies[node.body.index()].symbol != node.symbol))
            {
                return Err(Error::Invalid("graph node facts binding"));
            }
        }
        for edge in &graph.edges {
            if (!edge.operation.is_none() && edge.operation.index() >= facts.operations.len())
                || (!edge.receiver.is_none() && edge.receiver.index() >= facts.symbols.len())
                || (!edge.occurrence.is_none()
                    && edge.occurrence.index() >= facts.occurrences.len())
            {
                return Err(Error::Invalid("graph edge facts binding"));
            }
        }
        for issue in &graph.issues {
            if (!issue.file.is_none() && issue.file.index() >= facts.files.len())
                || (!issue.symbol.is_none() && issue.symbol.index() >= facts.symbols.len())
                || (!issue.detail.is_none() && issue.detail.index() >= facts.strings.len())
            {
                return Err(Error::Invalid("graph issue facts binding"));
            }
        }

        if options.max_contexts == 0
            || options.max_set_members == 0
            || options.quantum == 0
            || options.max_steps == 0
        {
            return Err(Error::Invalid("solver options"));
        }
        if let Some(roots) = &options.execution_roots {
            if roots.iter().any(|r| {
                r.node.index() >= graph.nodes.len()
                    || (!r.receiver.is_none() && r.receiver.index() >= facts.symbols.len())
            }) {
                return Err(Error::Invalid("execution root frontier"));
            }
        }
        if options.census.capacity > 65_536 || options.census.evaluation_stride == 0 {
            return Err(Error::Invalid("work census options"));
        }
        if matches!(
            options.context_policy,
            ContextPolicy::BoundedArguments {
                max_variants_per_receiver: 0
            }
        ) {
            return Err(Error::Invalid("context variant policy"));
        }
        let session = Self {
            facts,
            graph,
            issue_postings: IssueIndex::new(graph, facts.files.len()),
            options: options.clone(),
            pool: ValuePool::new(options.max_set_members),
            frames: FramePool::default(),
            types: TypeIndex::new(facts),
            contexts: Vec::new(),
            index: HashMap::new(),
            callback_shapes: CallbackShapes::new(),
            calls: Vec::new(),
            call_index: HashSet::new(),
            dependencies: Dependencies::default(),
            slots: HashMap::new(),
            heap_owners: HeapOwners::new(facts.operations.len(), facts.symbols.len())?,
            captures: HashMap::new(),
            closure_families: HashMap::new(),
            capture_origins: Vec::new(),
            field_reads: HashSet::new(),
            writes: HashSet::new(),
            reuse: ReuseMetrics::default(),
            ready: Vec::new(),
            roots: Vec::new(),
            issues: Vec::new(),
            issue_index: HashSet::new(),
            issue_contexts: HashSet::new(),
            runtime_issue_sites: HashMap::new(),
            completion: Completion::Complete,
            metrics: AnalysisMetrics {
                workers: runtime.workers(),
                ..Default::default()
            },
            runtime: runtime.clone(),
            batches: runtime.lease(options),
            sealed: false,
            pending_roots: Vec::new(),
            stop_reason: None,
            rounds: 0,
            counters: WorkCounters::default(),
            census: work_census::WorkCensus::new(options.census.capacity),
            observed_at: Instant::now(),
            started_at: Instant::now(),
            context_families: HashMap::new(),
            policy_arguments: Vec::new(),
            provider_scope: None,
        };
        session.emit_initial();
        Ok(session)
    }
    fn emit_initial(&self) {
        if let Some(observer) = &self.options.observer {
            observer.observe(SolveEvent {
                phase: SolvePhase::Preparing,
                round: 0,
                elapsed_ns: 0,
                counters: self.work_counters(),
                stop: None,
                cache: None,
            });
        }
    }
    fn emit(&mut self, phase: SolvePhase, force: bool, cache: Option<cache::CacheEvent>) {
        if self.options.observer.is_none() {
            return;
        }
        if !force && self.observed_at.elapsed() < std::time::Duration::from_secs(1) {
            return;
        }
        self.observed_at = Instant::now();
        self.options.observer.as_ref().unwrap().observe(SolveEvent {
            phase,
            round: self.rounds,
            elapsed_ns: self.started_at.elapsed().as_nanos().min(u64::MAX as u128) as u64,
            counters: self.work_counters(),
            stop: self.stop_reason,
            cache,
        });
    }
    pub(crate) fn emit_cache(&self, event: cache::CacheEvent) {
        if let Some(observer) = &self.options.observer {
            observer.observe(SolveEvent {
                phase: SolvePhase::CacheAdmission,
                round: self.rounds,
                elapsed_ns: self.started_at.elapsed().as_nanos().min(u64::MAX as u128) as u64,
                counters: self.work_counters(),
                stop: self.stop_reason,
                cache: Some(event),
            });
        }
    }
    pub fn stop_reason(&self) -> Option<StopReason> {
        self.stop_reason
    }
    pub fn work_census(&self) -> &[WorkRow] {
        self.census.rows()
    }
    pub fn work_counters(&self) -> WorkCounters {
        WorkCounters {
            contexts: self.contexts.len() as u64,
            context_hits: self.metrics.summary_hits,
            operations: self.counters.operations,
            pending: (self.ready.len() + self.pending_roots.len()) as u64,
            owned_bytes: self.metrics.owned_bytes,
            ..self.counters
        }
    }
    fn context(&mut self, mut key: ContextKey) -> Result<ContextId, Error> {
        if self.graph.nodes[key.node.index()].body.is_none() {
            key.arguments = FrameId(0);
        }
        if is_static_initializer(self.facts, self.graph, key.node) {
            key.receiver = Value::EMPTY;
            key.arguments = FrameId(0);
        } else if let Some(module) = self
            .types
            .global_module_owner(self.graph.nodes[key.node.index()].symbol)
        {
            key.receiver = self.pool.singleton(Atom {
                kind: AtomKind::Object,
                site: OperationId::NONE,
                symbol: module,
                binding: 0,
            })?;
        }
        let callback_shape = if self.options.context_policy == ContextPolicy::Exact {
            CallbackShapeId(0)
        } else {
            if let Some(shape) = self
                .callback_shapes
                .lookup(&self.pool, self.frames.get(key.arguments))
            {
                shape
            } else {
                let budget = self.options.memory_budget_bytes.saturating_sub(
                    self.owned_bytes()
                        .saturating_sub(self.callback_shapes.owned_bytes()),
                );
                self.callback_shapes.intern_bounded(
                    &self.pool,
                    self.frames.get(key.arguments),
                    budget,
                )?
            }
        };
        if let Some(id) = self.index.get(&PolicyContextKey {
            key,
            shape: callback_shape,
        }) {
            self.metrics.summary_hits += 1;
            return Ok(*id);
        }
        let mut widened = false;
        if let ContextPolicy::BoundedArguments {
            max_variants_per_receiver,
        } = self.options.context_policy
        {
            let count = self
                .context_families
                .get(&(key.node, key.receiver, callback_shape))
                .copied()
                .unwrap_or(0);
            let marker = PolicyContextKey {
                key: ContextKey {
                    arguments: FrameId(u32::MAX),
                    ..key
                },
                shape: callback_shape,
            };
            if (count >= max_variants_per_receiver || self.index.contains_key(&marker))
                && !self.needs_exact_arguments(self.frames.get(key.arguments))
            {
                if let Some(id) = self.index.get(&marker).copied() {
                    let old = self.contexts[id.index()].key.arguments;
                    self.policy_arguments.clear();
                    let a = self.frames.get(old);
                    let b = self.frames.get(key.arguments);
                    for i in 0..a.len().max(b.len()) {
                        self.policy_arguments.push(self.pool.join(
                            a.get(i).copied().unwrap_or(Value::TOP),
                            b.get(i).copied().unwrap_or(Value::TOP),
                        )?);
                    }
                    let arguments = self.frames.intern(&self.policy_arguments)?;
                    if arguments != old {
                        self.contexts[id.index()].key.arguments = arguments;
                        self.ready.push(id);
                        self.counters.widened_contexts += 1;
                        self.census.update(WorkRow {
                            node: key.node,
                            widened_contexts: 1,
                            ..Default::default()
                        });
                    } else {
                        self.metrics.summary_hits += 1;
                    }
                    return Ok(id);
                }
                widened = true;
            }
        }
        self.insert_context(key, widened, callback_shape)
    }
    fn insert_context(
        &mut self,
        key: ContextKey,
        widened: bool,
        callback_shape: CallbackShapeId,
    ) -> Result<ContextId, Error> {
        if self.contexts.len() >= self.options.max_contexts {
            return Err(Error::Limit("analysis contexts"));
        }
        let id = ContextId::checked(self.contexts.len())?;
        self.contexts
            .try_reserve(1)
            .map_err(|_| Error::Limit("context allocation"))?;
        self.contexts.push(Context {
            key,
            value: Value::EMPTY,
            version: 0,
            evaluated: false,
            widened,
            callback_shape,
            effects_open: false,
        });
        self.index
            .insert(context_index_key(&self.contexts[id.index()]), id);
        if self.options.context_policy != ContextPolicy::Exact
            && !widened
            && !self.needs_exact_arguments(self.frames.get(key.arguments))
        {
            *self
                .context_families
                .entry((key.node, key.receiver, callback_shape))
                .or_default() += 1;
        }
        self.ready.push(id);
        self.metrics.novel_facts += 1;
        self.census.update(WorkRow {
            node: key.node,
            new_contexts: 1,
            ..Default::default()
        });
        Ok(id)
    }
    fn call_context(
        &mut self,
        node: NodeId,
        mut receiver: Value,
        args: &[Value],
    ) -> Result<ContextId, Error> {
        if is_static_initializer(self.facts, self.graph, node) {
            return self.context(ContextKey {
                node,
                receiver: Value::EMPTY,
                arguments: FrameId(0),
            });
        }
        if self.graph.nodes[node.index()].body.is_none() {
            return self.context(ContextKey {
                node,
                receiver,
                arguments: FrameId(0),
            });
        }
        if let Some(module) = self
            .types
            .global_module_owner(self.graph.nodes[node.index()].symbol)
        {
            receiver = self.pool.singleton(Atom {
                kind: AtomKind::Object,
                site: OperationId::NONE,
                symbol: module,
                binding: 0,
            })?;
        }
        if self.options.context_policy == ContextPolicy::Exact {
            let arguments = self.frames.intern(args)?;
            return self.context(ContextKey {
                node,
                receiver,
                arguments,
            });
        }
        let callback_shape = if let Some(shape) = self.callback_shapes.lookup(&self.pool, args) {
            shape
        } else {
            let budget = self.options.memory_budget_bytes.saturating_sub(
                self.owned_bytes()
                    .saturating_sub(self.callback_shapes.owned_bytes()),
            );
            self.callback_shapes
                .intern_bounded(&self.pool, args, budget)?
        };
        if let Some(arguments) = self.frames.lookup(args) {
            if let Some(id) = self
                .index
                .get(&PolicyContextKey {
                    key: ContextKey {
                        node,
                        receiver,
                        arguments,
                    },
                    shape: callback_shape,
                })
                .copied()
            {
                self.metrics.summary_hits += 1;
                return Ok(id);
            }
        }
        if self.options.context_policy != ContextPolicy::Exact
            && let Some(id) = self
                .index
                .get(&PolicyContextKey {
                    key: ContextKey {
                        node,
                        receiver,
                        arguments: FrameId(u32::MAX),
                    },
                    shape: callback_shape,
                })
                .copied()
            && !self.needs_exact_arguments(args)
        {
            let old = self.contexts[id.index()].key.arguments;
            let previous = self.frames.get(old);
            self.policy_arguments.clear();
            for i in 0..previous.len().max(args.len()) {
                self.policy_arguments.push(self.pool.join(
                    previous.get(i).copied().unwrap_or(Value::TOP),
                    args.get(i).copied().unwrap_or(Value::TOP),
                )?);
            }
            let arguments = self.frames.intern(&self.policy_arguments)?;
            if arguments != old {
                self.contexts[id.index()].key.arguments = arguments;
                self.ready.push(id);
                self.counters.widened_contexts += 1;
                self.census.update(WorkRow {
                    node,
                    widened_contexts: 1,
                    ..Default::default()
                });
            } else {
                self.metrics.summary_hits += 1;
            }
            return Ok(id);
        }
        let arguments = self.frames.intern(args)?;
        self.context(ContextKey {
            node,
            receiver,
            arguments,
        })
    }
    pub(crate) fn validate_context_shape(
        &self,
        key: ContextKey,
        widened: bool,
        shape: CallbackShapeId,
    ) -> Result<(), Error> {
        if shape.0 as usize >= self.callback_shapes.len() {
            return Err(Error::Invalid("context callback shape ID"));
        }
        if self.options.context_policy == ContextPolicy::Exact {
            return if shape.0 == 0 {
                Ok(())
            } else {
                Err(Error::Invalid("exact context callback shape"))
            };
        }
        let args = self.frames.get(key.arguments);
        let declared = self.callback_shapes.get(shape);
        if declared.arity as usize != args.len() {
            return Err(Error::Invalid("context callback shape arity"));
        }
        if !widened && self.callback_shapes.lookup(&self.pool, args) != Some(shape) {
            return Err(Error::Invalid("context callback shape input"));
        }
        if widened && !context_policy::shape_covers_payload(declared, &self.pool, args) {
            return Err(Error::Invalid("context callback shape overflow"));
        }
        Ok(())
    }
    pub(crate) fn rebuild_context_policy(&mut self) -> Result<(), Error> {
        self.capture_origins.clear();
        self.capture_origins
            .try_reserve_exact(self.closure_families.len())
            .map_err(|_| Error::Limit("capture origin index"))?;
        self.capture_origins
            .resize(self.closure_families.len(), Value::EMPTY);
        for (family, binding) in &self.closure_families {
            *self
                .capture_origins
                .get_mut(*binding as usize)
                .ok_or(Error::Invalid("capture origin index"))? = family.origins;
        }
        self.index.clear();
        self.context_families.clear();
        for (i, context) in self.contexts.iter().enumerate() {
            self.validate_context_shape(context.key, context.widened, context.callback_shape)?;
            if context.widened && self.options.context_policy == ContextPolicy::Exact {
                return Err(Error::Invalid("widened context in exact policy"));
            }
            if self
                .index
                .insert(context_index_key(context), ContextId::checked(i)?)
                .is_some()
            {
                return Err(Error::Invalid("duplicate context index"));
            }
            let needs_exact = self.needs_exact_arguments(self.frames.get(context.key.arguments));
            if context.widened && needs_exact {
                return Err(Error::Invalid("widened nested callback arguments"));
            }
            if self.options.context_policy != ContextPolicy::Exact
                && !context.widened
                && !needs_exact
            {
                *self
                    .context_families
                    .entry((
                        context.key.node,
                        context.key.receiver,
                        context.callback_shape,
                    ))
                    .or_default() += 1;
            }
        }
        if let ContextPolicy::BoundedArguments {
            max_variants_per_receiver,
        } = self.options.context_policy
        {
            if self
                .context_families
                .values()
                .any(|n| *n > max_variants_per_receiver)
            {
                return Err(Error::Invalid("context family variant count"));
            }
        }
        Ok(())
    }
    fn needs_exact_arguments(&self, args: &[Value]) -> bool {
        capture_origins::needs_exact_arguments(&self.pool, &self.capture_origins, args)
    }
    pub(crate) fn restore_completed_context(
        &mut self,
        key: ContextKey,
        value: Value,
        version: u64,
        widened: bool,
        callback_shape: CallbackShapeId,
        effects_open: bool,
    ) -> Result<ContextId, Error> {
        self.validate_context_shape(key, widened, callback_shape)?;
        let key_for_index = if widened {
            ContextKey {
                arguments: FrameId(u32::MAX),
                ..key
            }
        } else {
            key
        };
        let index_key = PolicyContextKey {
            key: key_for_index,
            shape: callback_shape,
        };
        if self.index.contains_key(&index_key) {
            return Err(Error::Invalid("overlapping completed cache families"));
        }
        if widened && self.options.context_policy == ContextPolicy::Exact {
            return Err(Error::Invalid("widened exact context"));
        }
        let id = self.insert_context(key, widened, callback_shape)?;
        self.contexts[id.index()].value = value;
        self.contexts[id.index()].version = version;
        self.contexts[id.index()].evaluated = true;
        self.contexts[id.index()].effects_open = effects_open;
        Ok(id)
    }
    /// Reject serialized contradictions; never derive closure from the first
    /// diagnostic site. The producer's accumulated bit remains indispensable
    /// when a later issue had the same kind as an earlier data-only read.
    pub(crate) fn validate_effect_states(&self) -> Result<(), Error> {
        for (id, context) in self.contexts.iter().enumerate() {
            if context.effects_open || !context.evaluated {
                continue;
            }
            if let Some(site) = self.runtime_issue_sites.get(&ContextId(id as u32)) {
                let data_read = site.reason == RuntimeIssueReason::UnknownFieldValue
                    && self
                        .facts
                        .operations
                        .get(site.operation.index())
                        .is_some_and(|op| op.opcode == Opcode::LoadField && !op.target.is_none());
                if !data_read {
                    return Err(Error::Invalid("closed effects contradict runtime issue"));
                }
            }
            let body = self.graph.nodes[context.key.node.index()].body;
            if body.is_none()
                && self
                    .graph
                    .successors(context.key.node)
                    .any(|(_, edge)| edge.kind == EdgeKind::Guard || edge.flags & EDGE_UNKNOWN != 0)
            {
                return Err(Error::Invalid(
                    "closed effects contradict execution frontier",
                ));
            }
            if !body.is_none()
                && self.facts.operations[self.facts.bodies[body.index()].operations.range()]
                    .iter()
                    .any(|op| {
                        op.opcode == Opcode::Unknown
                            || (matches!(
                                op.opcode,
                                Opcode::LoadField | Opcode::StoreField | Opcode::BindCallback
                            ) && op.target.is_none())
                            || (op.opcode == Opcode::PackSequence
                                && (op.target.is_none()
                                    || self.facts.symbol_name(op.target)
                                        != SEQUENCE_ELEMENTS_SYMBOL))
                    })
            {
                return Err(Error::Invalid("closed effects contradict recipe"));
            }
        }
        for (context, slot) in &self.writes {
            if !self.contexts[context.index()].effects_open
                && slot.kind == SlotKind::Field
                && (slot.owner == u32::MAX || slot.member == u32::MAX)
            {
                return Err(Error::Invalid(
                    "closed effects contradict unknown heap write",
                ));
            }
        }
        Ok(())
    }
    pub fn execute(&mut self, roots: &[ExecutionRoot]) -> Result<(), Error> {
        for root in roots {
            if root.node.index() >= self.graph.nodes.len()
                || (!root.receiver.is_none() && root.receiver.index() >= self.facts.symbols.len())
            {
                return Err(Error::Invalid("execution root"));
            }
        }
        if self.stop_reason.is_some() {
            for root in roots {
                if !self.pending_roots.contains(root) {
                    self.pending_roots.push(*root);
                }
            }
            return Ok(());
        }
        if let Some(reason) = self
            .options
            .control
            .as_ref()
            .and_then(|c| c.at_round(self.rounds))
        {
            self.pending_roots.extend_from_slice(roots);
            self.resource_stop(reason);
            return Ok(());
        }
        for (i, root) in roots.iter().enumerate() {
            let receiver = if root.receiver.is_none() {
                Value::TOP
            } else {
                self.pool.singleton(Atom {
                    kind: AtomKind::Object,
                    site: OperationId::NONE,
                    symbol: root.receiver,
                    binding: 0,
                })?
            };
            let id = match self.context(ContextKey {
                node: root.node,
                receiver,
                arguments: FrameId(0),
            }) {
                Ok(id) => id,
                Err(Error::Limit(limit)) => {
                    self.pending_roots.extend_from_slice(&roots[i..]);
                    self.resource_stop(if limit == "callback shape memory" {
                        StopReason::MemoryLimit
                    } else if self.contexts.len() >= self.options.max_contexts {
                        StopReason::ContextLimit
                    } else {
                        StopReason::AllocationLimit
                    });
                    return Ok(());
                }
                Err(e) => return Err(e),
            };
            if !self.roots.contains(&id) {
                self.roots.push(id);
            }
        }
        self.sealed = false;
        self.solve()
    }
    /// Continue a stopped fixed point. Callers may increase resource limits in
    /// checkpoint restore options; cancellation controls must be reset explicitly.
    pub fn resume(&mut self) -> Result<(), Error> {
        self.stop_reason = None;
        self.issues.retain(|i| i.kind != IssueKind::ResourceLimit);
        self.issue_index
            .retain(|key| key.0 != IssueKind::ResourceLimit as u32);
        self.completion = if self.issues.is_empty() {
            Completion::Complete
        } else {
            Completion::Conservative
        };
        let pending = std::mem::take(&mut self.pending_roots);
        self.execute(&pending)
    }
    fn obligation(&mut self, kind: IssueKind, node: NodeId) {
        let r = self.graph.nodes.get(node.index());
        let issue = Obligation {
            kind,
            file: r.map(|r| r.file).unwrap_or(FileId::NONE),
            symbol: r.map(|r| r.symbol).unwrap_or(SymbolId::NONE),
            detail: StrId::NONE,
        };
        if self.issue_index.insert(obligation_key(issue)) {
            self.issues.push(issue);
        }
        if self.completion == Completion::Complete {
            self.completion = Completion::Conservative;
        }
    }
    fn validate_runtime_issue_site(
        &self,
        node: NodeId,
        site: RuntimeIssueSite,
    ) -> Result<(), Error> {
        site.validate()?;
        let record = self
            .graph
            .nodes
            .get(node.index())
            .ok_or(Error::Invalid("runtime issue node"))?;
        if site.reason == RuntimeIssueReason::ExecutionGuard
            && !self.graph.successors(node).any(|(_, edge)| {
                edge.operation == site.operation
                    && (edge.kind == EdgeKind::Guard || edge.flags & EDGE_UNKNOWN != 0)
            })
        {
            return Err(Error::Invalid("runtime execution guard edge"));
        }
        if site.operation.is_none() {
            if site.reason == RuntimeIssueReason::MissingExecutableBody
                && (!record.body.is_none() || record.flags & NODE_EFFECTS_COMPLETE != 0)
            {
                return Err(Error::Invalid("runtime missing executable body"));
            }
            return Ok(());
        }
        let body = self
            .facts
            .bodies
            .get(record.body.index())
            .ok_or(Error::Invalid("runtime issue body"))?;
        let operation = self
            .facts
            .operations
            .get(site.operation.index())
            .ok_or(Error::Invalid("runtime issue operation"))?;
        if operation.body != record.body
            || !body.operations.range().contains(&site.operation.index())
        {
            return Err(Error::Invalid("runtime issue operation owner"));
        }
        if !site.reason.accepts_opcode(operation.opcode) {
            return Err(Error::Invalid("runtime issue operation kind"));
        }
        Ok(())
    }
    fn record_runtime_issue_site(
        &mut self,
        context: ContextId,
        site: RuntimeIssueSite,
    ) -> Result<(), Error> {
        let node = self
            .contexts
            .get(context.index())
            .ok_or(Error::Invalid("runtime issue context"))?
            .key
            .node;
        self.validate_runtime_issue_site(node, site)?;
        let record = self.graph.nodes[node.index()];
        if !self.issue_contexts.contains(&context)
            || !self.issue_index.contains(&obligation_key(Obligation {
                kind: site.kind,
                file: record.file,
                symbol: record.symbol,
                detail: StrId::NONE,
            }))
        {
            return Err(Error::Invalid("runtime issue matching obligation"));
        }
        if self.runtime_issue_sites.contains_key(&context) {
            return Ok(());
        }
        if self.runtime_issue_sites.len() == self.runtime_issue_sites.capacity() {
            let extra = self
                .runtime_issue_sites
                .capacity()
                .max(4)
                .saturating_mul(48);
            if self.owned_bytes().saturating_add(extra) > self.options.memory_budget_bytes {
                return Err(Error::Limit("runtime issue provenance"));
            }
            self.runtime_issue_sites
                .try_reserve(1)
                .map_err(|_| Error::Limit("runtime issue provenance allocation"))?;
        }
        self.runtime_issue_sites.insert(context, site);
        Ok(())
    }
    fn resource_stop(&mut self, reason: StopReason) {
        self.stop_reason = Some(reason);
        self.completion = Completion::ResourceLimited;
        let issue = Obligation {
            kind: IssueKind::ResourceLimit,
            file: FileId::NONE,
            symbol: SymbolId::NONE,
            detail: StrId::NONE,
        };
        if self.issue_index.insert(obligation_key(issue)) {
            self.issues.push(issue);
        }
        self.sealed = false;
        self.metrics.states = self.contexts.len() as u64;
        self.metrics.owned_bytes = self.owned_bytes() as u64;
        self.emit(SolvePhase::Stopped, true, None);
        self.emit_census();
    }
    fn emit_census(&self) {
        if let Some(observer) = &self.options.observer {
            for row in self.census.rows() {
                let node = self.graph.nodes[row.node.index()];
                let symbol = self.facts.symbols[node.symbol.index()];
                let path = if node.file.is_none() {
                    ""
                } else {
                    self.facts.text(self.facts.files[node.file.index()].path)
                };
                observer.work_row_with_origin(
                    *row,
                    WorkOrigin {
                        symbol: self.facts.text(symbol.name),
                        context: self.facts.text(symbol.context),
                        path,
                    },
                );
            }
        }
    }
    fn count_publication(&mut self, node: NodeId, changed: bool) {
        self.counters.novel_publications += u64::from(changed);
        self.counters.repeated_publications += u64::from(!changed);
        self.census.update(WorkRow {
            node,
            novel_publications: u64::from(changed),
            repeated_publications: u64::from(!changed),
            ..Default::default()
        });
    }
    fn solve(&mut self) -> Result<(), Error> {
        if self.stop_reason.is_some() {
            return Ok(());
        }
        let start = Instant::now();
        let mut invalidated = Vec::new();
        let mut published = Vec::new();
        let mut imported = Vec::new();
        let mut work = Vec::new();
        let mut bindings = Vec::new();
        if !self.ready.is_empty() {
            self.emit(SolvePhase::Executing, true, None);
        }
        while !self.ready.is_empty() {
            if let Some(reason) = self
                .options
                .control
                .as_ref()
                .and_then(|c| c.at_round(self.rounds))
            {
                self.resource_stop(reason);
                break;
            }
            self.ready.sort_unstable();
            self.ready.dedup();
            self.metrics.queued_peak = self.metrics.queued_peak.max(self.ready.len() as u64);
            let quantum = self.options.quantum;
            let n = self.batches.len();
            // Worker count must not alter summary visibility: intermediate
            // exact argument sets are themselves contexts and retained proofs.
            // Partition one deterministic global round among the workers.
            let take = self.ready.len().min(quantum);
            work.clear();
            work.extend(self.ready.drain(..take));
            for batch in &mut self.batches {
                batch.work.clear();
                batch.attempted = 0;
            }
            for id in &work {
                self.batches[id.index() % n].work.push(*id);
            }
            let world = ReadWorld {
                facts: self.facts,
                graph: self.graph,
                types: &self.types,
                pool: &self.pool,
                frames: &self.frames,
                contexts: &self.contexts,
                index: &self.index,
                slots: &self.slots,
                heap_owners: &self.heap_owners,
                captures: &self.captures,
                families: &self.closure_families,
                capture_origins: &self.capture_origins,
                callback_shapes: &self.callback_shapes,
                context_policy: self.options.context_policy,
                provider_scope: self.provider_scope.as_ref(),
            };
            let facts = self.facts;
            let graph = self.graph;
            let types = &self.types;
            let contexts = &self.contexts;
            let evaluated: Result<(), Error> = self.runtime.inner.pool.install(|| {
                self.batches.par_iter_mut().try_for_each(|batch| {
                    while batch.outputs.len() < batch.work.len() {
                        batch.outputs.push((ContextId::NONE, Evaluation::default()));
                    }
                    for (i, id) in batch.work.iter().enumerate() {
                        let c = contexts[id.index()];
                        batch.outputs[i].0 = *id;
                        batch.attempted += 1;
                        evaluate(
                            facts,
                            graph,
                            types,
                            &world,
                            c.key.node,
                            c.key.receiver,
                            world.frames.get(c.key.arguments),
                            &mut batch.scratch,
                            &mut batch.outputs[i].1,
                        )?;
                    }
                    for output in batch.outputs.iter_mut().skip(batch.work.len()) {
                        output.0 = ContextId::NONE;
                        output.1.clear();
                    }
                    Ok(())
                })
            });
            // Include work that ran even if a later admission fails. Visit in
            // global order so detailed sampling is independent of worker count.
            for id in &work {
                let batch = &self.batches[id.index() % n];
                let pos = batch.work.binary_search(id).expect("assigned context");
                if pos >= batch.attempted {
                    continue;
                }
                let out = &batch.outputs[pos].1;
                let context = self.contexts[id.index()];
                // Account for every attempted transfer before any fallible
                // publication. A later resource stop/resume cannot erase an
                // earlier opaque effect merely because its batch was pending.
                self.contexts[id.index()].effects_open |= out.effects_open;
                self.counters.evaluations += 1;
                self.counters.reevaluations += u64::from(context.evaluated);
                self.counters.operations += out.operation_visits + out.edges.len() as u64;
                let callbacks = out
                    .calls
                    .iter()
                    .filter(|c| c.kind == EdgeKind::Callback)
                    .count() as u64;
                let dispatch = out.calls.len() as u64 - callbacks;
                self.counters.callback_targets += callbacks;
                self.counters.dispatch_targets += dispatch;
                if self.counters.evaluations % self.options.census.evaluation_stride == 0 {
                    self.census.update(WorkRow {
                        node: context.key.node,
                        evaluations: 1,
                        reevaluations: u64::from(context.evaluated),
                        dispatch_targets: dispatch,
                        callback_targets: callbacks,
                        ..Default::default()
                    });
                }
            }
            if let Err(Error::Limit(_)) = evaluated {
                self.ready.extend_from_slice(&work);
                self.resource_stop(StopReason::AllocationLimit);
                break;
            }
            evaluated?;
            let mut commit_stop = None;
            for id in &work {
                let shard = id.index() % n;
                let pos = self.batches[shard]
                    .work
                    .binary_search(id)
                    .expect("evaluated context");
                let (_, mut out) = std::mem::replace(
                    &mut self.batches[shard].outputs[pos],
                    (ContextId::NONE, Evaluation::default()),
                );
                let result = self.commit(
                    *id,
                    &mut out,
                    shard,
                    &mut imported,
                    &mut published,
                    &mut bindings,
                );
                self.batches[shard].outputs[pos] = (*id, out);
                if let Err(Error::Limit(limit)) = result {
                    commit_stop = Some(if limit == "callback shape memory" {
                        StopReason::MemoryLimit
                    } else if self.contexts.len() >= self.options.max_contexts {
                        StopReason::ContextLimit
                    } else {
                        StopReason::AllocationLimit
                    });
                    break;
                }
                result?;
            }
            if !published.is_empty() {
                published.sort_unstable();
                published.dedup();
                invalidated.clear();
                let before = self.dependencies.epoch();
                self.dependencies
                    .publish(&published, before, before + 1, &mut invalidated);
                self.metrics.invalidations += invalidated.len() as u64;
                self.ready.extend_from_slice(&invalidated);
                published.clear();
            }
            if let Some(reason) = commit_stop {
                // A failed admission may leave a partially committed monotone
                // delta. Replay the entire immutable round after restoring its
                // published dependency wakeups; no pending execution is lost.
                self.ready.extend_from_slice(&work);
                self.resource_stop(reason);
                break;
            }
            // Missing field absence becomes authoritative only after runnable and
            // in-flight publications are drained. Promote unresolved reads to a
            // scoped unknown, then wake their exact negative-read continuations.
            if self.ready.is_empty() {
                for slot in &self.field_reads {
                    if !self.field_present(*slot) {
                        let marker = if slot.kind == SlotKind::StaticField {
                            *slot
                        } else {
                            Slot {
                                kind: SlotKind::FieldMissing,
                                ..*slot
                            }
                        };
                        if self.slots.contains_key(&marker) {
                            continue;
                        }
                        self.slots.insert(
                            marker,
                            SlotValue {
                                value: Value {
                                    set: SetId(0),
                                    unknown: UNKNOWN_FIELD,
                                },
                                version: 1,
                            },
                        );
                        published.push(marker);
                    }
                }
                if !published.is_empty() {
                    invalidated.clear();
                    let before = self.dependencies.epoch();
                    self.dependencies
                        .publish(&published, before, before + 1, &mut invalidated);
                    self.ready.extend_from_slice(&invalidated);
                    published.clear();
                }
            }
            for batch in &mut self.batches {
                batch.scratch.clear();
            }
            self.metrics.states = self.contexts.len() as u64;
            self.rounds += 1;
            self.metrics.owned_bytes = self.owned_bytes() as u64;
            let stop = if self.counters.operations > self.options.max_steps {
                Some(StopReason::StepLimit)
            } else if self.metrics.owned_bytes > self.options.memory_budget_bytes as u64 {
                Some(StopReason::MemoryLimit)
            } else {
                self.options
                    .control
                    .as_ref()
                    .and_then(|c| c.at_round(self.rounds))
            };
            if let Some(reason) = stop {
                self.resource_stop(reason);
                break;
            }
            self.emit(SolvePhase::Publication, false, None);
        }
        self.metrics.elapsed_ns = self
            .metrics
            .elapsed_ns
            .saturating_add(start.elapsed().as_nanos().min(u64::MAX as u128) as u64);
        self.metrics.owned_bytes = self.owned_bytes() as u64;
        self.sealed = self.completion != Completion::ResourceLimited;
        if self.sealed && !work.is_empty() {
            self.emit(SolvePhase::Complete, true, None);
            self.emit_census();
        }
        Ok(())
    }
    fn import_heap_slot(&mut self, mut slot: Slot, drafts: &[HeapOwnerKey]) -> Result<Slot, Error> {
        if matches!(slot.kind, SlotKind::Field | SlotKind::FieldMissing)
            && slot.owner != u32::MAX
            && slot.owner & LOCAL_HEAP_OWNER != 0
        {
            let key = *drafts
                .get((slot.owner & !LOCAL_HEAP_OWNER) as usize)
                .ok_or(Error::Invalid("local heap owner"))?;
            if self
                .facts
                .operations
                .get(key.site.index())
                .is_none_or(|op| !op.opcode.is_heap_site())
            {
                return Err(Error::Invalid("heap owner allocation site"));
            }
            slot.owner = self.heap_owners.intern(key)?;
        }
        Ok(slot)
    }
    fn field_all_slot(&self, slot: Slot) -> Option<Slot> {
        let site = match slot.kind {
            SlotKind::FieldWildcard => OperationId(slot.owner),
            SlotKind::Field => self.heap_owners.key(slot.owner)?.site,
            _ => return None,
        };
        Some(Slot {
            kind: SlotKind::FieldAll,
            owner: site.0,
            member: slot.member,
        })
    }
    fn field_present(&self, slot: Slot) -> bool {
        if self.slots.contains_key(&slot) {
            return true;
        }
        if slot.kind == SlotKind::Field {
            if let Some(key) = self.heap_owners.key(slot.owner) {
                return self.slots.contains_key(&Slot {
                    kind: SlotKind::FieldWildcard,
                    owner: key.site.0,
                    member: slot.member,
                });
            }
        }
        false
    }
    fn publish_heap_value(
        &mut self,
        slot: Slot,
        value: Value,
        published: &mut Vec<Slot>,
    ) -> Result<bool, Error> {
        let old = self.slots.get(&slot).copied().unwrap_or(SlotValue {
            value: Value::EMPTY,
            version: 0,
        });
        let joined = self.pool.join(old.value, value)?;
        let changed = joined != old.value || old.version == 0;
        if changed {
            self.slots.insert(
                slot,
                SlotValue {
                    value: joined,
                    version: old.version + 1,
                },
            );
            published.push(slot);
        }
        Ok(changed)
    }
    /// Rehydrate derived aggregate channels from admitted actual contributions.
    /// Existing equal aggregates keep their version; newly visible values wake
    /// retained coarse readers through the ordinary dependency index.
    pub(crate) fn rebuild_heap_aggregates(&mut self) -> Result<(), Error> {
        let count = self
            .slots
            .keys()
            .filter(|slot| self.field_all_slot(**slot).is_some())
            .count();
        let building = count
            .checked_mul(std::mem::size_of::<(Slot, Value)>() + std::mem::size_of::<Slot>())
            .ok_or(Error::Limit("heap aggregate rebuild"))?;
        let waking = count
            .checked_mul(std::mem::size_of::<Slot>())
            .and_then(|n| {
                n.checked_add(
                    self.contexts
                        .len()
                        .checked_mul(std::mem::size_of::<ContextId>())?,
                )
            })
            .ok_or(Error::Limit("heap aggregate rebuild"))?;
        let bytes = building
            .max(waking)
            .checked_add(self.owned_bytes())
            .ok_or(Error::Limit("heap aggregate rebuild"))?;
        if bytes > self.options.memory_budget_bytes {
            return Err(Error::Limit("heap aggregate rebuild"));
        }
        let mut values = Vec::new();
        values
            .try_reserve_exact(count)
            .map_err(|_| Error::Limit("heap aggregate rebuild"))?;
        for (slot, value) in &self.slots {
            if let Some(all) = self.field_all_slot(*slot) {
                values.push((all, value.value));
            }
        }
        let mut published = Vec::new();
        published
            .try_reserve_exact(count)
            .map_err(|_| Error::Limit("heap aggregate publications"))?;
        for (slot, value) in values {
            self.publish_heap_value(slot, value, &mut published)?;
        }
        if !published.is_empty() {
            published.sort_unstable();
            published.dedup();
            let mut invalidated = Vec::new();
            let epoch = self.dependencies.epoch();
            self.dependencies
                .publish(&published, epoch, epoch + 1, &mut invalidated);
            self.ready.extend_from_slice(&invalidated);
        }
        Ok(())
    }
    fn commit(
        &mut self,
        id: ContextId,
        out: &mut Evaluation,
        shard: usize,
        imported: &mut Vec<Value>,
        published: &mut Vec<Slot>,
        bindings: &mut Vec<u32>,
    ) -> Result<(), Error> {
        self.contexts[id.index()].effects_open |= out.effects_open
            || out.stores.iter().any(|store| {
                store.slot.kind == SlotKind::Field
                    && (store.slot.owner == u32::MAX || store.slot.member == u32::MAX)
            });
        bindings.clear();
        for capture in &out.captures {
            let origins = capture_origins::intern(
                &mut self.pool,
                &self.batches[shard].scratch.pool,
                capture.receiver,
                &out.arguments[capture.arguments.range()],
                &self.capture_origins,
                bindings,
            )?;
            let receiver = self
                .pool
                .family(&self.batches[shard].scratch.pool, capture.receiver)?;
            imported.clear();
            for arg in &out.arguments[capture.arguments.range()] {
                imported.push(self.pool.family(&self.batches[shard].scratch.pool, *arg)?);
            }
            let arguments = self.frames.intern(imported)?;
            let family = ClosureFamily {
                site: capture.site,
                receiver,
                arguments,
                origins,
            };
            let next = u32::try_from(self.closure_families.len())
                .map_err(|_| Error::Limit("closure families"))?;
            if next >= LOCAL_BINDING {
                return Err(Error::Limit("closure families"));
            }
            let binding = match self.closure_families.entry(family) {
                std::collections::hash_map::Entry::Occupied(entry) => *entry.get(),
                std::collections::hash_map::Entry::Vacant(entry) => {
                    self.capture_origins
                        .try_reserve(1)
                        .map_err(|_| Error::Limit("capture origin index"))?;
                    self.capture_origins.push(origins);
                    *entry.insert(next)
                }
            };
            bindings.push(binding);
        }
        let value =
            self.pool
                .import_bindings(&self.batches[shard].scratch.pool, out.value, &bindings)?;
        let context = &mut self.contexts[id.index()];
        let node = context.key.node;
        let joined = self.pool.join(context.value, value)?;
        let changed = joined != context.value || !context.evaluated;
        context.value = joined;
        context.evaluated = true;
        if changed {
            context.version += 1;
            published.push(Slot {
                kind: SlotKind::Summary,
                owner: id.0,
                member: 0,
            });
            self.metrics.novel_facts += 1;
        } else {
            self.metrics.repeated_facts += 1;
        }
        self.dependencies.acknowledge(id);
        for read in &out.reads {
            let mut read = *read;
            read.slot = self.import_heap_slot(read.slot, &out.heap_owners)?;
            self.dependencies.subscribe(id, read)?;
        }
        for slot in &out.field_reads {
            let slot = self.import_heap_slot(*slot, &out.heap_owners)?;
            self.field_reads.insert(slot);
        }
        // Static fields retain their single-slot absence contract.
        for read in &out.reads {
            if read.slot.kind == SlotKind::StaticField {
                self.field_reads.insert(read.slot);
            }
        }
        self.metrics.edge_visits += out.operation_visits + out.edges.len() as u64;
        self.count_publication(node, changed);
        for call in &out.calls {
            if self
                .provider_scope
                .as_mut()
                .is_some_and(|scope| scope.block(node, call))
            {
                self.contexts[id.index()].effects_open = true;
                self.obligation(IssueKind::UnknownExecution, node);
                self.issue_contexts.insert(id);
                continue;
            }
            let receiver = self.pool.import_bindings(
                &self.batches[shard].scratch.pool,
                call.receiver,
                &bindings,
            )?;
            imported.clear();
            for arg in &out.arguments[call.arguments.range()] {
                imported.push(self.pool.import_bindings(
                    &self.batches[shard].scratch.pool,
                    *arg,
                    &bindings,
                )?);
            }
            let target = self.call_context(call.target, receiver, imported)?;
            let c = self.contexts[target.index()];
            if call.observe_return {
                self.dependencies.subscribe(
                    id,
                    Read {
                        slot: Slot {
                            kind: SlotKind::Summary,
                            owner: target.0,
                            member: 0,
                        },
                        version: c.version,
                        present: c.evaluated,
                    },
                )?;
            }
            if call.observe_return && call.summary != Some(target) && c.evaluated {
                self.ready.push(id);
            }
            let binding = if call.binding == u32::MAX {
                u32::MAX
            } else if call.binding & LOCAL_BINDING != 0 {
                bindings[(call.binding & !LOCAL_BINDING) as usize]
            } else {
                call.binding
            };
            let link = ContextCall {
                source: id,
                target,
                operation: call.operation,
                kind: call.kind,
                edge: call.edge,
                binding,
            };
            if self.call_index.insert(link) {
                self.calls.push(link);
            }
        }
        for store in &out.stores {
            let slot = self.import_heap_slot(store.slot, &out.heap_owners)?;
            self.writes.insert((id, slot));
            let value = self.pool.import_bindings(
                &self.batches[shard].scratch.pool,
                store.value,
                &bindings,
            )?;
            let changed = self.publish_heap_value(slot, value, published)?;
            if let Some(all) = self.field_all_slot(slot) {
                let aggregate_changed = self.publish_heap_value(all, value, published)?;
                self.count_publication(node, aggregate_changed);
            }
            self.count_publication(node, changed);
        }
        for (capture_index, capture) in out.captures.iter().enumerate() {
            let binding = bindings[capture_index];
            self.writes.insert((
                id,
                Slot {
                    kind: SlotKind::Capture,
                    owner: binding,
                    member: 0,
                },
            ));
            let receiver = self.pool.import_bindings(
                &self.batches[shard].scratch.pool,
                capture.receiver,
                &bindings,
            )?;
            imported.clear();
            for arg in &out.arguments[capture.arguments.range()] {
                imported.push(self.pool.import_bindings(
                    &self.batches[shard].scratch.pool,
                    *arg,
                    &bindings,
                )?);
            }
            let old = self.captures.get(&binding).copied();
            let receiver = if let Some(old) = old {
                self.pool.join(old.receiver, receiver)?
            } else {
                receiver
            };
            if let Some(old) = old {
                let old_args = self.frames.get(old.arguments);
                for i in 0..imported.len().max(old_args.len()) {
                    let a = old_args.get(i).copied().unwrap_or(Value::TOP);
                    let b = imported.get(i).copied().unwrap_or(Value::TOP);
                    let v = self.pool.join(a, b)?;
                    if i < imported.len() {
                        imported[i] = v;
                    } else {
                        imported.push(v);
                    }
                }
            }
            let arguments = self.frames.intern(imported)?;
            let changed = old
                .map(|o| o.receiver != receiver || o.arguments != arguments)
                .unwrap_or(true);
            if changed {
                let version = old.map(|o| o.version + 1).unwrap_or(1);
                self.captures.insert(
                    binding,
                    Capture {
                        receiver,
                        arguments,
                        version,
                    },
                );
                published.push(Slot {
                    kind: SlotKind::Capture,
                    owner: binding,
                    member: 0,
                });
            }
            self.count_publication(node, changed);
        }
        for issue in &out.issues {
            self.obligation(*issue, self.contexts[id.index()].key.node);
            self.issue_contexts.insert(id);
        }
        if let Some(site) = out.first_issue {
            if !out.issues.contains(&site.kind) {
                return Err(Error::Invalid("runtime issue missing obligation"));
            }
            self.record_runtime_issue_site(id, site)?;
        }
        Ok(())
    }
    pub fn owned_bytes(&self) -> usize {
        self.pool.owned_bytes()
            + self.callback_shapes.owned_bytes()
            + self.frames.owned_bytes()
            + self.types.owned_bytes()
            + self.contexts.capacity() * std::mem::size_of::<Context>()
            + self.index.capacity() * 64
            + self.calls.capacity() * std::mem::size_of::<ContextCall>()
            + self.call_index.capacity() * 40
            + self.dependencies.owned_bytes()
            + self.slots.capacity() * 56
            + self.heap_owners.owned_bytes()
            + self.captures.capacity() * 40
            + self.closure_families.capacity() * 48
            + self.capture_origins.capacity() * std::mem::size_of::<Value>()
            + self.field_reads.capacity() * 24
            + self.writes.capacity() * 32
            + self.ready.capacity() * 4
            + self.roots.capacity() * 4
            + self.pending_roots.capacity() * std::mem::size_of::<ExecutionRoot>()
            + self.census.owned_bytes()
            + self.context_families.capacity() * 48
            + self.policy_arguments.capacity() * std::mem::size_of::<Value>()
            + self
                .provider_scope
                .as_ref()
                .map_or(0, provider_scope::ProviderScope::owned_bytes)
            + self.issues.capacity() * std::mem::size_of::<Obligation>()
            + self.issue_index.capacity() * 24
            + self.issue_postings.owned_bytes()
            + self.issue_contexts.capacity() * 8
            + self.runtime_issue_sites.capacity() * 24
            + self.batches.capacity() * std::mem::size_of::<Batch>()
            + self.batches.iter().map(batch_bytes).sum::<usize>()
    }
    pub fn persist_completed(&self) -> Result<(), Error> {
        if let Some(config) = self.runtime.inner.cache.as_ref() {
            cache::save(self, config)?;
        }
        Ok(())
    }
    pub fn reuse_metrics(&self) -> ReuseMetrics {
        self.reuse
    }
    pub fn context_count(&self) -> usize {
        self.contexts.len()
    }
    /// Borrow the first runtime issue ever recorded for each retained context.
    ///
    /// Later evaluations do not replace a context's recorded site. This is not
    /// a census of all issue occurrences or of issues in the latest evaluation.
    /// Retained contexts can include cache-restored state outside the current
    /// requested root frontier. Iteration order is unspecified; no storage is
    /// allocated and the returned IDs remain owned by this session.
    pub fn first_runtime_issue_sites(
        &self,
    ) -> impl ExactSizeIterator<Item = (ContextId, NodeId, RuntimeIssueSite)> + '_ {
        self.runtime_issue_sites
            .iter()
            .map(|(&context, &site)| (context, self.contexts[context.index()].key.node, site))
    }
    pub fn metrics(&self) -> AnalysisMetrics {
        self.metrics
    }
    /// Export one active transfer context and all of the reads/candidates needed
    /// to replay it without loading the original program. With no explicit ID,
    /// prefer the widest admitted input frame for this node.
    pub fn export_replay(
        &self,
        node: NodeId,
        context: Option<ContextId>,
        directory: &std::path::Path,
        limits: &replay::ReplayLimits,
    ) -> Result<replay::ReplayExportReport, Error> {
        let id = if let Some(id) = context {
            self.contexts
                .get(id.index())
                .filter(|c| c.key.node == node && c.evaluated)
                .ok_or(Error::Invalid("replay context node"))?;
            id
        } else {
            self.contexts
                .iter()
                .enumerate()
                .filter(|(_, c)| c.key.node == node && c.evaluated)
                .max_by_key(|(i, c)| {
                    let size = self
                        .frames
                        .get(c.key.arguments)
                        .iter()
                        .map(|v| self.pool.members(*v).len() + usize::from(v.unknown != 0))
                        .sum::<usize>();
                    (size, std::cmp::Reverse(*i))
                })
                .map(|(i, _)| ContextId(i as u32))
                .ok_or(Error::Invalid("replay node has no active context"))?
        };
        let key = self.contexts[id.index()].key;
        let world = ReadWorld {
            facts: self.facts,
            graph: self.graph,
            types: &self.types,
            pool: &self.pool,
            frames: &self.frames,
            contexts: &self.contexts,
            index: &self.index,
            slots: &self.slots,
            heap_owners: &self.heap_owners,
            captures: &self.captures,
            families: &self.closure_families,
            capture_origins: &self.capture_origins,
            callback_shapes: &self.callback_shapes,
            context_policy: self.options.context_policy,
            provider_scope: self.provider_scope.as_ref(),
        };
        let mut limits = limits.clone();
        limits.max_set_members = self.options.max_set_members;
        replay::capture_context(
            self.facts,
            self.graph,
            &self.types,
            &world,
            node,
            key.receiver,
            self.frames.get(key.arguments),
            &limits,
        )?
        .write(directory)
    }
    /// Capture every admitted input in a method, or every argument frame for
    /// the exact receiver of an explicit anchor. Pending inputs are included;
    /// these are immutable transfer snapshots, not completed fixed points.
    pub fn export_replay_family(
        &self,
        node: NodeId,
        anchor: Option<ContextId>,
        directory: &std::path::Path,
        limits: &replay::ReplayLimits,
        max_contexts: usize,
    ) -> Result<replay::ReplayFamilyReport, Error> {
        if node.index() >= self.graph.nodes.len() {
            return Err(Error::Invalid("replay family node"));
        }
        if max_contexts == 0 || max_contexts > replay::MAX_REPLAY_FAMILY_VARIANTS {
            return Err(Error::Limit("replay family maximum must be in 1..=64"));
        }
        let receiver = anchor
            .map(|id| {
                self.contexts
                    .get(id.index())
                    .filter(|c| c.key.node == node)
                    .map(|c| c.key.receiver)
                    .ok_or(Error::Invalid("replay family anchor"))
            })
            .transpose()?;
        let total_variants = self.contexts.iter().filter(|c| c.key.node == node).count();
        let selected_variants = self
            .contexts
            .iter()
            .filter(|c| c.key.node == node && receiver.is_none_or(|r| r == c.key.receiver))
            .count();
        if selected_variants == 0 {
            return Err(Error::Invalid("replay family has no admitted contexts"));
        }
        if selected_variants > max_contexts {
            return Err(Error::Limit(
                "replay family variants; select an explicit receiver family",
            ));
        }
        let scratch = total_variants
            .checked_mul(8)
            .and_then(|n| {
                n.checked_add(
                    selected_variants
                        * (std::mem::size_of::<ContextId>()
                            + std::mem::size_of::<(ContextId, replay::ReplayBundle)>()),
                )
            })
            .ok_or(Error::Limit("replay family inventory bytes"))?;
        if scratch > limits.max_bytes {
            return Err(Error::Limit("replay family inventory budget"));
        }
        let mut receivers = Vec::new();
        receivers
            .try_reserve_exact(total_variants)
            .map_err(|_| Error::Limit("replay family receiver inventory"))?;
        let mut selected = Vec::new();
        selected
            .try_reserve_exact(selected_variants)
            .map_err(|_| Error::Limit("replay family context inventory"))?;
        let mut selected_evaluated = 0;
        for (i, c) in self
            .contexts
            .iter()
            .enumerate()
            .filter(|(_, c)| c.key.node == node)
        {
            receivers.push((c.key.receiver.set.0, c.key.receiver.unknown));
            if receiver.is_none_or(|r| r == c.key.receiver) {
                selected.push(ContextId(i as u32));
                selected_evaluated += usize::from(c.evaluated);
            }
        }
        receivers.sort_unstable();
        receivers.dedup();
        let total_receivers = receivers.len();
        drop(receivers);
        let scope = if let Some(context) = anchor {
            replay::ReplayFamilyScope::ReceiverOf {
                context: context.0,
                receiver: replay::ReplayValue::from_value(&self.pool, receiver.unwrap())?,
            }
        } else {
            replay::ReplayFamilyScope::Method
        };
        let inventory = replay::ReplayFamilyInventory {
            node: node.0,
            total_variants,
            total_receivers,
            selected_variants,
            selected_evaluated,
            scope,
        };
        let world = ReadWorld {
            facts: self.facts,
            graph: self.graph,
            types: &self.types,
            pool: &self.pool,
            frames: &self.frames,
            contexts: &self.contexts,
            index: &self.index,
            slots: &self.slots,
            heap_owners: &self.heap_owners,
            captures: &self.captures,
            families: &self.closure_families,
            capture_origins: &self.capture_origins,
            callback_shapes: &self.callback_shapes,
            context_policy: self.options.context_policy,
            provider_scope: self.provider_scope.as_ref(),
        };
        let mut limits = limits.clone();
        limits.max_set_members = self.options.max_set_members;
        let mut bundles = Vec::new();
        bundles
            .try_reserve_exact(selected_variants)
            .map_err(|_| Error::Limit("replay family bundles"))?;
        let mut retained = selected_variants
            * (std::mem::size_of::<ContextId>()
                + std::mem::size_of::<(ContextId, replay::ReplayBundle)>())
            + match &inventory.scope {
                replay::ReplayFamilyScope::ReceiverOf { receiver, .. } => {
                    receiver.atoms.capacity() * std::mem::size_of::<replay::ReplayAtom>()
                }
                _ => 0,
            };
        if retained > limits.max_bytes {
            return Err(Error::Limit("replay family scope budget"));
        }
        for id in selected {
            let key = self.contexts[id.index()].key;
            let mut capture_limits = limits.clone();
            capture_limits.max_bytes = limits.max_bytes - retained;
            let bundle = replay::capture_context(
                self.facts,
                self.graph,
                &self.types,
                &world,
                node,
                key.receiver,
                self.frames.get(key.arguments),
                &capture_limits,
            )?;
            retained = retained
                .checked_add(bundle.report().owned_bytes)
                .ok_or(Error::Limit("replay family bytes"))?;
            if retained > limits.max_bytes {
                return Err(Error::Limit("replay family retained budget"));
            }
            bundles.push((id, bundle));
        }
        replay::ReplayFamily::from_contexts(inventory, bundles, &limits)?.write(directory)
    }
    fn analyzed_root(&self, id: ContextId) -> AnalyzedRoot {
        let key = self.contexts[id.index()].key;
        let receiver = match self.pool.members(key.receiver) {
            [a] if a.kind == AtomKind::Object && a.site.is_none() && key.receiver.unknown == 0 => {
                a.symbol
            }
            _ => SymbolId::NONE,
        };
        AnalyzedRoot {
            node: key.node,
            receiver,
        }
    }

    fn requested_root_evidence(&self, out: &mut Vec<AnalyzedRoot>) {
        if let Some(roots) = &self.options.execution_roots {
            out.extend(roots.iter().map(|r| AnalyzedRoot {
                node: r.node,
                receiver: r.receiver,
            }));
        }
        out.extend(self.pending_roots.iter().map(|r| AnalyzedRoot {
            node: r.node,
            receiver: r.receiver,
        }));
        out.extend(self.roots.iter().map(|id| self.analyzed_root(*id)));
        out.sort_unstable();
        out.dedup();
    }
    pub fn analyze(&mut self, seeds: &[NodeId]) -> Result<AnalysisResult, Error> {
        self.analyze_typed(AnalysisSeeds {
            execution: seeds,
            declarations: &[],
        })
    }
    pub fn analyze_typed(&mut self, seeds: AnalysisSeeds<'_>) -> Result<AnalysisResult, Error> {
        self.analyze_typed_guarded(seeds, &[])
    }
    /// Adds query-local uncertainty at auxiliary runtime dependencies. Only roots
    /// whose executed contexts reach these nodes are guarded.
    pub fn analyze_typed_guarded(
        &mut self,
        seeds: AnalysisSeeds<'_>,
        guard_nodes: &[NodeId],
    ) -> Result<AnalysisResult, Error> {
        for seed in seeds
            .execution
            .iter()
            .chain(seeds.declarations)
            .chain(guard_nodes)
        {
            if seed.index() >= self.graph.nodes.len() {
                return Err(Error::Invalid("change seed"));
            }
        }
        if let Some(roots) = self.options.execution_roots.clone() {
            self.execute(&roots)?;
        } else {
            let roots: Vec<_> = self
                .facts
                .suites
                .iter()
                .filter_map(|s| {
                    self.graph
                        .node_for_symbol(s.symbol)
                        .map(|node| ExecutionRoot {
                            node,
                            receiver: if matches!(
                                self.facts.symbols[s.symbol.index()].kind,
                                10..=14
                            ) {
                                s.symbol
                            } else {
                                self.facts.symbols[s.symbol.index()].owner
                            },
                        })
                })
                .collect();
            if !roots.is_empty() {
                self.execute(&roots)?;
            }
        }
        if !self.ready.is_empty() {
            self.solve()?;
        }
        let compilation = compilation_impact(self.graph, seeds.declarations);
        if self.roots.is_empty()
            && self.pending_roots.is_empty()
            && self.stop_reason.is_none()
            && self.options.execution_roots.is_none()
        {
            let mut result =
                reverse_potential(self.facts, self.graph, seeds.execution, &self.options)?;
            result.compilation = compilation;
            return Ok(result);
        }
        let start = Instant::now();
        self.emit(SolvePhase::Reporting, true, None);
        let mut obligations = self.issues.clone();
        let mut unscoped = self.completion == Completion::ResourceLimited;
        let mut uncertain = vec![false; self.contexts.len()];
        for id in &self.issue_contexts {
            uncertain[id.index()] = true;
        }
        let mut issue_index = self.issue_index.clone();
        let guard_nodes: HashSet<_> = guard_nodes.iter().copied().collect();
        let mut seen_nodes = HashSet::new();
        let mut seen_files = HashSet::new();
        let mut relevant_issues = self.issue_postings.global.clone();
        unscoped |= !relevant_issues.is_empty();
        let mut external_effects_open = unscoped || !self.sealed;
        for (i, c) in self.contexts.iter().enumerate() {
            let node = c.key.node;
            let file = self.graph.nodes[node.index()].file;
            let nodes = self.issue_postings.nodes(node);
            let files = self.issue_postings.files(file);
            if !nodes.is_empty() || !files.is_empty() {
                uncertain[i] = true;
                external_effects_open = true;
            }
            if seen_nodes.insert(node) {
                relevant_issues.extend_from_slice(nodes);
                if guard_nodes.contains(&node) {
                    let o = Obligation {
                        kind: IssueKind::UnsupportedModel,
                        file,
                        symbol: self.graph.nodes[node.index()].symbol,
                        detail: StrId::NONE,
                    };
                    if issue_index.insert(obligation_key(o)) {
                        obligations.push(o);
                    }
                }
            }
            if guard_nodes.contains(&node) {
                uncertain[i] = true;
                external_effects_open = true;
            }
            if seen_files.insert(file) {
                relevant_issues.extend_from_slice(files);
            }
        }
        for index in &relevant_issues {
            let issue = self.graph.issues[*index];
            let o = Obligation {
                kind: issue.kind,
                file: issue.file,
                symbol: issue.symbol,
                detail: issue.detail,
            };
            if issue_index.insert(obligation_key(o)) {
                obligations.push(o);
            }
        }
        obligations.sort_unstable_by_key(|o| obligation_key(*o));
        let mut offsets = vec![0usize; self.contexts.len() + 1];
        for call in &self.calls {
            offsets[call.target.index() + 1] += 1;
        }
        for i in 1..offsets.len() {
            offsets[i] += offsets[i - 1];
        }
        let mut positions = offsets[..self.contexts.len()].to_vec();
        let mut incoming = vec![0usize; self.calls.len()];
        for (i, c) in self.calls.iter().enumerate() {
            incoming[positions[c.target.index()]] = i;
            positions[c.target.index()] += 1;
        }
        let mut unknown_paths = vec![None; self.contexts.len()];
        let mut queue: VecDeque<_> = uncertain
            .iter()
            .enumerate()
            .filter_map(|(i, v)| v.then_some(ContextId(i as u32)))
            .collect();
        // Stable boundary priority also survives completed-family ID rebasing.
        queue.make_contiguous().sort_unstable_by_key(|id| {
            (
                self.contexts[id.index()].key.node,
                runtime_issue_key(self.runtime_issue_sites.get(id).copied()),
            )
        });
        // CSR fill positions are dead now; reuse them for each context's actual
        // unknown boundary, avoiding another whole-context allocation.
        positions.fill(usize::MAX);
        for (i, unknown) in uncertain.iter().enumerate() {
            if *unknown {
                positions[i] = i;
            }
        }
        while let Some(target) = queue.pop_front() {
            for index in &incoming[offsets[target.index()]..offsets[target.index() + 1]] {
                let source = self.calls[*index].source;
                if !uncertain[source.index()] {
                    uncertain[source.index()] = true;
                    unknown_paths[source.index()] = Some(*index);
                    positions[source.index()] = positions[target.index()];
                    queue.push_back(source);
                }
            }
        }
        let mut guarded_roots: Vec<_> = self
            .roots
            .iter()
            .filter(|id| uncertain[id.index()])
            .map(|id| self.contexts[id.index()].key.node)
            .collect();
        guarded_roots.sort_unstable();
        guarded_roots.dedup();
        // Reuse the graph-issue scratch for a flat runtime-issue posting index.
        // One exemplar per root is enough for a useful compact explanation.
        relevant_issues.clear();
        relevant_issues.extend(0..self.issues.len());
        relevant_issues.sort_unstable_by_key(|i| {
            let o = self.issues[*i];
            (o.symbol, o.file, o.kind as u32, o.detail)
        });
        let mut guard_causes = Vec::with_capacity(guarded_roots.len());
        for root in &self.roots {
            if !uncertain[root.index()] {
                continue;
            }
            let origin = positions[root.index()];
            if origin == usize::MAX {
                continue;
            }
            let node = self.contexts[origin].key.node;
            let record = self.graph.nodes[node.index()];
            let mut runtime = None;
            let issue = if guard_nodes.contains(&node) {
                Some(Obligation {
                    kind: IssueKind::UnsupportedModel,
                    file: record.file,
                    symbol: record.symbol,
                    detail: StrId::NONE,
                })
            } else if let Some(index) = self
                .issue_postings
                .nodes(node)
                .iter()
                .copied()
                .min_by_key(|i| {
                    let o = self.graph.issues[*i];
                    (o.kind as u32, o.file, o.symbol, o.detail)
                })
                .or_else(|| {
                    self.issue_postings
                        .files(record.file)
                        .iter()
                        .copied()
                        .min_by_key(|i| {
                            let o = self.graph.issues[*i];
                            (o.kind as u32, o.file, o.symbol, o.detail)
                        })
                })
            {
                let o = self.graph.issues[index];
                Some(Obligation {
                    kind: o.kind,
                    file: o.file,
                    symbol: o.symbol,
                    detail: o.detail,
                })
            } else if let Some(site) = self.runtime_issue_sites.get(&ContextId(origin as u32)) {
                runtime = Some(*site);
                Some(Obligation {
                    kind: site.kind,
                    file: record.file,
                    symbol: record.symbol,
                    detail: StrId::NONE,
                })
            } else {
                let key = (record.symbol, record.file);
                let start = relevant_issues.partition_point(|i| {
                    let o = self.issues[*i];
                    (o.symbol, o.file) < key
                });
                relevant_issues
                    .get(start)
                    .map(|i| self.issues[*i])
                    .filter(|o| (o.symbol, o.file) == key)
            };
            if let Some(o) = issue {
                guard_causes.push(RootGuardEvidence {
                    root: self.contexts[root.index()].key.node,
                    node,
                    kind: o.kind,
                    file: o.file,
                    symbol: o.symbol,
                    detail: o.detail,
                    runtime,
                });
            }
        }
        guard_causes.sort_unstable_by_key(|c| {
            (
                c.root,
                c.node,
                c.kind as u32,
                c.file,
                c.symbol,
                c.detail,
                runtime_issue_key(c.runtime),
            )
        });
        guard_causes.dedup_by_key(|c| c.root);
        let mut seed_nodes = vec![false; self.graph.nodes.len()];
        for seed in seeds.execution {
            seed_nodes[seed.index()] = true;
        }
        let mut reached = vec![false; self.contexts.len()];
        let mut paths = vec![None; self.contexts.len()];
        for (i, c) in self.contexts.iter().enumerate() {
            if seed_nodes[c.key.node.index()] {
                reached[i] = true;
                queue.push_back(ContextId(i as u32));
            }
        }
        while let Some(target) = queue.pop_front() {
            for index in &incoming[offsets[target.index()]..offsets[target.index() + 1]] {
                let call = self.calls[*index];
                if !reached[call.source.index()] {
                    reached[call.source.index()] = true;
                    paths[call.source.index()] = Some(*index);
                    queue.push_back(call.source);
                }
            }
        }
        let mut derived: Vec<_> = self
            .calls
            .iter()
            .filter(|c| {
                c.edge.is_none()
                    && ((reached[c.source.index()] && reached[c.target.index()])
                        || (uncertain[c.source.index()] && uncertain[c.target.index()]))
            })
            .map(|c| self.derived(*c))
            .collect();
        derived.sort_unstable();
        derived.dedup();
        // Project context-proven edges only after solving impact. Node witnesses
        // use shortest paths in that projection, preventing cycles when a method
        // occurs in several recursive contexts. ContextEvidence retains the
        // precise compatible path and bindings independently of that projection.
        let mut links: Vec<_> = self
            .calls
            .iter()
            .filter(|c| reached[c.source.index()] && reached[c.target.index()])
            .map(|c| {
                Ok((
                    self.contexts[c.source.index()].key.node,
                    self.contexts[c.target.index()].key.node,
                    self.proof_edge(*c, &derived)?,
                ))
            })
            .collect::<Result<_, Error>>()?;
        links.sort_unstable_by_key(|(source, target, edge)| (*target, *source, *edge));
        links.dedup();
        let mut node_offsets = vec![0usize; self.graph.nodes.len() + 1];
        for (_, target, _) in &links {
            node_offsets[target.index() + 1] += 1;
        }
        for i in 1..node_offsets.len() {
            node_offsets[i] += node_offsets[i - 1];
        }
        let mut affected = seed_nodes;
        let mut witnesses = vec![None; self.graph.nodes.len()];
        queue.extend(seeds.execution.iter().map(|n| ContextId(n.0)));
        while let Some(target) = queue.pop_front() {
            for (source, _, edge) in
                &links[node_offsets[target.index()]..node_offsets[target.index() + 1]]
            {
                if !affected[source.index()] {
                    affected[source.index()] = true;
                    witnesses[source.index()] = Some(WitnessStep {
                        node: *source,
                        next: NodeId(target.0),
                        edge: *edge,
                    });
                    queue.push_back(ContextId(source.0));
                }
            }
        }
        let mut evidence = if self.options.retain_context_evidence {
            self.detach_evidence(&reached, &paths, &uncertain, &unknown_paths, &derived)?
        } else {
            AnalysisEvidence::default()
        };
        self.requested_root_evidence(&mut evidence.requested_roots);
        evidence.guard_causes = guard_causes;
        let mut completion = self.completion;
        if !obligations.is_empty() && completion == Completion::Complete {
            completion = Completion::Conservative;
        }
        let mut metrics = self.metrics;
        metrics.elapsed_ns = metrics
            .elapsed_ns
            .saturating_add(start.elapsed().as_nanos().min(u64::MAX as u128) as u64);
        metrics.owned_bytes = self.owned_bytes() as u64;
        let mut result = AnalysisResult {
            snapshot: self.graph.identity,
            completion,
            affected: affected
                .iter()
                .enumerate()
                .filter_map(|(i, v)| v.then_some(NodeId(i as u32)))
                .collect(),
            witnesses: witnesses.into_iter().flatten().collect(),
            derived_edges: derived,
            obligations,
            guarded_roots,
            unscoped_uncertainty: unscoped,
            evidence,
            compilation,
            metrics,
        };
        let mut root_impacts: Vec<_> = self
            .roots
            .iter()
            .copied()
            .filter(|id| reached[id.index()])
            .map(|id| self.analyzed_root(id))
            .collect();
        root_impacts.sort_unstable();
        root_impacts.dedup();
        result.record_root_impacts(root_impacts)?;
        result.record_execution_effects(EffectClosureCoverage {
            contexts: self.contexts.len() as u64,
            evaluated_contexts: self.contexts.iter().filter(|c| c.evaluated).count() as u64,
            open_contexts: self.contexts.iter().filter(|c| c.effects_open).count() as u64,
            pending_work: self.ready.len().saturating_add(self.pending_roots.len()) as u64,
            external_open: external_effects_open,
        })?;
        Ok(result)
    }
    fn derived(&self, call: ContextCall) -> DerivedEdge {
        DerivedEdge {
            source: self.contexts[call.source.index()].key.node,
            target: self.contexts[call.target.index()].key.node,
            kind: call.kind,
            operation: call.operation,
            receiver: SymbolId::NONE,
        }
    }
    fn proof_edge(&self, call: ContextCall, derived: &[DerivedEdge]) -> Result<EdgeId, Error> {
        if !call.edge.is_none() {
            return Ok(call.edge);
        }
        let i = derived
            .binary_search(&self.derived(call))
            .map_err(|_| Error::Invalid("derived proof edge"))?;
        EdgeId::checked(self.graph.edges.len() + i)
    }
    fn detach_evidence(
        &self,
        reached: &[bool],
        paths: &[Option<usize>],
        uncertain: &[bool],
        unknown_paths: &[Option<usize>],
        derived: &[DerivedEdge],
    ) -> Result<AnalysisEvidence, Error> {
        let mut evidence = AnalysisEvidence::default();
        let mut values = HashMap::new();
        let mut pending_captures = Vec::new();
        let mut captured = HashSet::new();
        for (i, c) in self.contexts.iter().enumerate() {
            if !reached[i] && !uncertain[i] {
                continue;
            }
            let receiver = detach_value(
                &self.pool,
                c.key.receiver,
                &mut evidence,
                &mut values,
                &mut pending_captures,
            )?;
            let start = u32::try_from(evidence.value_ids.len())
                .map_err(|_| Error::Limit("evidence arguments"))?;
            for arg in self.frames.get(c.key.arguments) {
                let id = detach_value(
                    &self.pool,
                    *arg,
                    &mut evidence,
                    &mut values,
                    &mut pending_captures,
                )?;
                evidence.value_ids.push(id);
            }
            evidence.contexts.push(ContextEvidence {
                id: ContextId(i as u32),
                node: c.key.node,
                receiver,
                arguments: IdRange {
                    start,
                    len: self.frames.get(c.key.arguments).len() as u32,
                },
            });
            if let Some(path) = if reached[i] {
                paths[i]
            } else {
                unknown_paths[i]
            } {
                let call = self.calls[path];
                if call.binding != u32::MAX {
                    pending_captures.push(call.binding);
                }
                evidence.witnesses.push(ContextWitness {
                    context: call.source,
                    next: call.target,
                    edge: self.proof_edge(call, derived)?,
                    binding: call.binding,
                });
            }
        }
        evidence.root_contexts.extend(
            self.roots
                .iter()
                .copied()
                .filter(|id| reached[id.index()] || uncertain[id.index()]),
        );
        for call in &self.calls {
            if call.binding != u32::MAX
                && ((reached[call.source.index()] && reached[call.target.index()])
                    || (uncertain[call.source.index()] && uncertain[call.target.index()]))
            {
                pending_captures.push(call.binding);
            }
        }
        while let Some(site) = pending_captures.pop() {
            if !captured.insert(site) {
                continue;
            }
            let Some(c) = self.captures.get(&site) else {
                continue;
            };
            let receiver = detach_value(
                &self.pool,
                c.receiver,
                &mut evidence,
                &mut values,
                &mut pending_captures,
            )?;
            let start = u32::try_from(evidence.value_ids.len())
                .map_err(|_| Error::Limit("capture arguments"))?;
            for arg in self.frames.get(c.arguments) {
                let id = detach_value(
                    &self.pool,
                    *arg,
                    &mut evidence,
                    &mut values,
                    &mut pending_captures,
                )?;
                evidence.value_ids.push(id);
            }
            evidence.captures.push(CaptureEvidence {
                binding: site,
                receiver,
                arguments: IdRange {
                    start,
                    len: self.frames.get(c.arguments).len() as u32,
                },
            });
        }
        self.canonical_evidence(
            &mut evidence,
            reached,
            paths,
            uncertain,
            unknown_paths,
            derived,
        )?;
        Ok(evidence)
    }
    /// Published IDs follow semantic content, independent of worker completion,
    /// hash-table iteration and persisted-family admission order.
    fn canonical_evidence(
        &self,
        evidence: &mut AnalysisEvidence,
        reached: &[bool],
        paths: &[Option<usize>],
        uncertain: &[bool],
        unknown_paths: &[Option<usize>],
        derived: &[DerivedEdge],
    ) -> Result<(), Error> {
        let families: HashMap<_, _> = self
            .closure_families
            .iter()
            .map(|(family, binding)| (*binding, *family))
            .collect();
        let mut captures = Vec::with_capacity(evidence.captures.len());
        for capture in &evidence.captures {
            let family = families
                .get(&capture.binding)
                .ok_or(Error::Invalid("proof capture family"))?;
            let mut key = vec![family.site.0];
            append_value_key(&self.pool, family.receiver, &mut key);
            let args = self.frames.get(family.arguments);
            key.push(args.len() as u32);
            for value in args {
                append_value_key(&self.pool, *value, &mut key);
            }
            append_value_key(&self.pool, family.origins, &mut key);
            captures.push((key, capture.binding));
        }
        captures.sort_unstable();
        let bindings: HashMap<_, _> = captures
            .iter()
            .enumerate()
            .map(|(i, (_, old))| (*old, i as u32))
            .collect();
        for atom in &mut evidence.atoms {
            if atom.kind == 2 {
                atom.binding = *bindings
                    .get(&atom.binding)
                    .ok_or(Error::Invalid("proof callback capture"))?;
            }
        }
        for capture in &mut evidence.captures {
            capture.binding = bindings[&capture.binding];
        }
        evidence.captures.sort_unstable_by_key(|c| c.binding);
        for value in &evidence.values {
            evidence.atoms[value.atoms.range()]
                .sort_unstable_by_key(|a| (a.kind, a.site, a.symbol, a.binding));
        }
        let mut value_order: Vec<_> = (0..evidence.values.len()).collect();
        value_order.sort_unstable_by(|a, b| {
            let a = evidence.values[*a];
            let b = evidence.values[*b];
            a.unknown.cmp(&b.unknown).then_with(|| {
                evidence.atoms[a.atoms.range()]
                    .iter()
                    .map(|a| (a.kind, a.site, a.symbol, a.binding))
                    .cmp(
                        evidence.atoms[b.atoms.range()]
                            .iter()
                            .map(|a| (a.kind, a.site, a.symbol, a.binding)),
                    )
            })
        });
        let mut value_map = vec![0u32; value_order.len()];
        let mut atoms = Vec::with_capacity(evidence.atoms.len());
        let mut values = Vec::with_capacity(value_order.len());
        for (new, old) in value_order.into_iter().enumerate() {
            value_map[old] = new as u32;
            let value = evidence.values[old];
            let start = atoms.len() as u32;
            atoms.extend_from_slice(&evidence.atoms[value.atoms.range()]);
            values.push(EvidenceValue {
                atoms: IdRange {
                    start,
                    len: value.atoms.len,
                },
                unknown: value.unknown,
            });
        }
        evidence.atoms = atoms;
        evidence.values = values;
        for id in &mut evidence.value_ids {
            *id = value_map[*id as usize];
        }
        for c in &mut evidence.contexts {
            c.receiver = value_map[c.receiver as usize];
        }
        for c in &mut evidence.captures {
            c.receiver = value_map[c.receiver as usize];
        }
        let value_ids = &evidence.value_ids;
        evidence.contexts.sort_unstable_by(|a, b| {
            a.node
                .cmp(&b.node)
                .then(a.receiver.cmp(&b.receiver))
                .then_with(|| value_ids[a.arguments.range()].cmp(&value_ids[b.arguments.range()]))
                .then_with(|| {
                    // Distinct code partitions can both widen to the same TOP
                    // payload. Original IDs still address immutable creation
                    // shapes here; interner IDs/admission order are not semantic.
                    let a = self.contexts[a.id.index()];
                    let b = self.contexts[b.id.index()];
                    let sa = self.callback_shapes.get(a.callback_shape);
                    let sb = self.callback_shapes.get(b.callback_shape);
                    sa.arity
                        .cmp(&sb.arity)
                        .then_with(|| sa.atoms.cmp(sb.atoms))
                        .then(a.widened.cmp(&b.widened))
                })
        });
        let mut context_map = HashMap::with_capacity(evidence.contexts.len());
        for (new, context) in evidence.contexts.iter_mut().enumerate() {
            context_map.insert(context.id, ContextId(new as u32));
            context.id = ContextId(new as u32);
        }
        let old_arguments = std::mem::take(&mut evidence.value_ids);
        evidence.value_ids.reserve(old_arguments.len());
        for context in &mut evidence.contexts {
            let old = context.arguments;
            context.arguments.start = evidence.value_ids.len() as u32;
            evidence
                .value_ids
                .extend_from_slice(&old_arguments[old.range()]);
        }
        for capture in &mut evidence.captures {
            let old = capture.arguments;
            capture.arguments.start = evidence.value_ids.len() as u32;
            evidence
                .value_ids
                .extend_from_slice(&old_arguments[old.range()]);
        }
        for id in &mut evidence.root_contexts {
            *id = context_map[id];
        }
        evidence.root_contexts.sort_unstable();
        let choose = |valid: &[bool],
                      old_paths: &[Option<usize>]|
         -> Result<Vec<Option<ContextWitness>>, Error> {
            let mut links = Vec::new();
            for call in &self.calls {
                if !valid[call.source.index()] || !valid[call.target.index()] {
                    continue;
                }
                let source = context_map[&call.source];
                let target = context_map[&call.target];
                let edge = self.proof_edge(*call, derived)?;
                let binding = if call.binding == u32::MAX {
                    u32::MAX
                } else {
                    bindings[&call.binding]
                };
                links.push((target, source, edge, binding));
            }
            links.sort_unstable();
            links.dedup();
            let mut offsets = vec![0usize; evidence.contexts.len() + 1];
            for (target, _, _, _) in &links {
                offsets[target.index() + 1] += 1;
            }
            for i in 1..offsets.len() {
                offsets[i] += offsets[i - 1];
            }
            let mut terminals: Vec<_> = valid
                .iter()
                .enumerate()
                .filter_map(|(i, v)| {
                    (*v && old_paths[i].is_none()).then(|| context_map[&ContextId(i as u32)])
                })
                .collect();
            terminals.sort_unstable();
            let mut seen = vec![false; evidence.contexts.len()];
            let mut selected = vec![None; evidence.contexts.len()];
            let mut queue = VecDeque::new();
            for id in terminals {
                seen[id.index()] = true;
                queue.push_back(id);
            }
            while let Some(target) = queue.pop_front() {
                for (_, source, edge, binding) in
                    &links[offsets[target.index()]..offsets[target.index() + 1]]
                {
                    if !seen[source.index()] {
                        seen[source.index()] = true;
                        selected[source.index()] = Some(ContextWitness {
                            context: *source,
                            next: target,
                            edge: *edge,
                            binding: *binding,
                        });
                        queue.push_back(*source);
                    }
                }
            }
            Ok(selected)
        };
        let impact = choose(reached, paths)?;
        let unknown = choose(uncertain, unknown_paths)?;
        evidence.witnesses.clear();
        for (old, new) in &context_map {
            if let Some(witness) = if reached[old.index()] {
                impact[new.index()]
            } else {
                unknown[new.index()]
            } {
                evidence.witnesses.push(witness);
            }
        }
        evidence.witnesses.sort_unstable_by_key(|w| w.context);
        Ok(())
    }
}
impl Drop for QuerySession<'_> {
    fn drop(&mut self) {
        if self.options.max_set_members != self.runtime.inner.max_members {
            return;
        }
        for batch in &mut self.batches {
            batch.scratch.clear();
            batch.work.clear();
            for (_, out) in &mut batch.outputs {
                out.clear();
            }
        }
        let retained = self.batches.capacity() * std::mem::size_of::<Batch>()
            + self.batches.iter().map(batch_bytes).sum::<usize>();
        if retained
            <= self
                .runtime
                .inner
                .scratch_limit
                .saturating_mul(self.runtime.workers())
        {
            let mut idle = self.runtime.inner.idle.lock().unwrap();
            if idle.is_none() {
                *idle = Some(std::mem::take(&mut self.batches));
            }
        }
    }
}
fn evaluation_bytes(o: &Evaluation) -> usize {
    o.calls.capacity() * std::mem::size_of::<CallEffect>()
        + o.arguments.capacity() * std::mem::size_of::<Value>()
        + o.stores.capacity() * std::mem::size_of::<StoreEffect>()
        + o.captures.capacity() * std::mem::size_of::<CaptureEffect>()
        + o.reads.capacity() * std::mem::size_of::<Read>()
        + o.edges.capacity() * std::mem::size_of::<ExecutionEdge>()
        + o.issues.capacity() * std::mem::size_of::<IssueKind>()
        + o.heap_owners.capacity() * std::mem::size_of::<HeapOwnerKey>()
        + o.field_reads.capacity() * std::mem::size_of::<Slot>()
}
pub fn analyze(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    seeds: &[NodeId],
    options: &SolveOptions,
) -> Result<AnalysisResult, Error> {
    {
        let mut session = QuerySession::new(facts, graph, options)?;
        let result = session.analyze(seeds)?;
        session.persist_completed()?;
        Ok(result)
    }
}
pub fn analyze_typed_with_runtime(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    seeds: AnalysisSeeds<'_>,
    options: &SolveOptions,
    runtime: &SolverRuntime,
) -> Result<AnalysisResult, Error> {
    analyze_typed_guarded_with_runtime(facts, graph, seeds, &[], options, runtime)
}
pub fn analyze_typed_guarded_with_runtime(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    seeds: AnalysisSeeds<'_>,
    guard_nodes: &[NodeId],
    options: &SolveOptions,
    runtime: &SolverRuntime,
) -> Result<AnalysisResult, Error> {
    {
        let mut session = QuerySession::with_runtime(facts, graph, options, runtime)?;
        let result = session.analyze_typed_guarded(seeds, guard_nodes)?;
        session.persist_completed()?;
        Ok(result)
    }
}
pub fn analyze_with_runtime(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    seeds: &[NodeId],
    options: &SolveOptions,
    runtime: &SolverRuntime,
) -> Result<AnalysisResult, Error> {
    {
        let mut session = QuerySession::with_runtime(facts, graph, options, runtime)?;
        let result = session.analyze(seeds)?;
        session.persist_completed()?;
        Ok(result)
    }
}
fn reverse_potential(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    seeds: &[NodeId],
    options: &SolveOptions,
) -> Result<AnalysisResult, Error> {
    let start = Instant::now();
    let mut affected = vec![false; graph.nodes.len()];
    let mut witnesses = vec![None; graph.nodes.len()];
    let mut queue = VecDeque::new();
    for seed in seeds {
        if !affected[seed.index()] {
            affected[seed.index()] = true;
            queue.push_back(*seed);
        }
    }
    let mut visits = 0;
    let mut limited = false;
    while let Some(target) = queue.pop_front() {
        for (edge, e) in graph.predecessors(target) {
            if !e.kind.is_execution() {
                continue;
            }
            visits += 1;
            if visits > options.max_steps {
                limited = true;
                break;
            }
            if !affected[e.source.index()] {
                affected[e.source.index()] = true;
                witnesses[e.source.index()] = Some(WitnessStep {
                    node: e.source,
                    next: target,
                    edge,
                });
                queue.push_back(e.source);
            }
        }
        if limited {
            break;
        }
    }
    let mut obligations: Vec<_> = facts
        .issues
        .iter()
        .map(|i| Obligation {
            kind: i.kind,
            file: i.file,
            symbol: i.symbol,
            detail: i.detail,
        })
        .collect();
    obligations.push(Obligation {
        kind: if limited {
            IssueKind::ResourceLimit
        } else {
            IssueKind::UnknownExecution
        },
        file: FileId::NONE,
        symbol: SymbolId::NONE,
        detail: StrId::NONE,
    });
    let bytes =
        affected.capacity() + witnesses.capacity() * std::mem::size_of::<Option<WitnessStep>>();
    let states = affected.iter().filter(|x| **x).count() as u64;
    Ok(AnalysisResult {
        snapshot: graph.identity,
        completion: if limited {
            Completion::ResourceLimited
        } else {
            Completion::Conservative
        },
        affected: affected
            .iter()
            .enumerate()
            .filter_map(|(i, v)| v.then_some(NodeId(i as u32)))
            .collect(),
        witnesses: witnesses.into_iter().flatten().collect(),
        derived_edges: Vec::new(),
        obligations,
        guarded_roots: Vec::new(),
        unscoped_uncertainty: true,
        evidence: AnalysisEvidence::default(),
        compilation: CompilationImpact::default(),
        metrics: AnalysisMetrics {
            states,
            edge_visits: visits,
            workers: 1,
            elapsed_ns: start.elapsed().as_nanos().min(u64::MAX as u128) as u64,
            owned_bytes: bytes as u64,
            ..Default::default()
        },
    })
}

fn is_static_initializer(facts: &FactSnapshot, graph: &ProgramGraph, node: NodeId) -> bool {
    let body = graph.nodes[node.index()].body;
    !body.is_none() && facts.bodies[body.index()].flags & BODY_STATIC_INITIALIZER != 0
}

fn append_value_key(pool: &ValuePool, value: Value, out: &mut Vec<u32>) {
    out.push(value.unknown);
    out.push(pool.members(value).len() as u32);
    for atom in pool.members(value) {
        out.extend_from_slice(&[atom_tag(atom.kind), atom.site.0, atom.symbol.0]);
        if matches!(atom.kind, AtomKind::Object | AtomKind::Container) {
            out.push(atom.binding);
        }
    }
}
fn atom_tag(kind: AtomKind) -> u32 {
    match kind {
        AtomKind::Object => 1,
        AtomKind::Callback => 2,
        AtomKind::UpperBound => 3,
        AtomKind::Container => 4,
    }
}

fn validate_container_atom(facts: &FactSnapshot, atom: Atom) -> Result<(), Error> {
    if atom.site.is_none()
        || atom.symbol.is_none()
        || facts.symbols.get(atom.symbol.index()).is_none()
        || facts.symbol_name(atom.symbol) != SEQUENCE_ELEMENTS_SYMBOL
        || facts
            .operations
            .get(atom.site.index())
            .is_none_or(|op| op.opcode != Opcode::PackSequence || op.target != atom.symbol)
        || binding_root(atom.binding).is_some_and(|root| root.index() >= facts.symbols.len())
    {
        return Err(Error::Invalid("sequence container identity"));
    }
    Ok(())
}

fn detach_value(
    pool: &ValuePool,
    value: Value,
    out: &mut AnalysisEvidence,
    index: &mut HashMap<Value, u32>,
    captures: &mut Vec<u32>,
) -> Result<u32, Error> {
    if let Some(id) = index.get(&value) {
        return Ok(*id);
    }
    let id = u32::try_from(out.values.len()).map_err(|_| Error::Limit("evidence values"))?;
    let start = u32::try_from(out.atoms.len()).map_err(|_| Error::Limit("evidence atoms"))?;
    for atom in pool.members(value) {
        let binding = if atom.kind == AtomKind::Callback {
            captures.push(atom.binding);
            atom.binding
        } else if matches!(atom.kind, AtomKind::Object | AtomKind::Container) {
            atom.binding
        } else {
            0
        };
        out.atoms.push(EvidenceAtom {
            kind: atom_tag(atom.kind),
            site: atom.site,
            symbol: atom.symbol,
            binding,
        });
    }
    out.values.push(EvidenceValue {
        atoms: IdRange {
            start,
            len: pool.members(value).len() as u32,
        },
        unknown: value.unknown,
    });
    index.insert(value, id);
    Ok(id)
}
fn compilation_impact(graph: &ProgramGraph, seeds: &[NodeId]) -> CompilationImpact {
    if seeds.is_empty() {
        return CompilationImpact::default();
    }
    let mut affected = vec![false; graph.nodes.len()];
    let mut witnesses = vec![None; graph.nodes.len()];
    let mut queue = VecDeque::new();
    for seed in seeds {
        if !affected[seed.index()] {
            affected[seed.index()] = true;
            queue.push_back(*seed);
        }
    }
    while let Some(target) = queue.pop_front() {
        for (edge, e) in graph.predecessors(target) {
            if e.kind == EdgeKind::Compile && !affected[e.source.index()] {
                affected[e.source.index()] = true;
                witnesses[e.source.index()] = Some(WitnessStep {
                    node: e.source,
                    next: target,
                    edge,
                });
                queue.push_back(e.source);
            }
        }
    }
    CompilationImpact {
        affected: affected
            .iter()
            .enumerate()
            .filter_map(|(i, v)| v.then_some(NodeId(i as u32)))
            .collect(),
        witnesses: witnesses.into_iter().flatten().collect(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    struct Fixture {
        facts: FactSnapshot,
        graph: ProgramGraph,
    }
    fn op(code: Opcode) -> OperationRecord {
        OperationRecord {
            body: BodyId::NONE,
            opcode: code,
            target: SymbolId::NONE,
            dest: ValueId::NONE,
            a: ValueId::NONE,
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span::default(),
            flags: 0,
        }
    }
    impl Fixture {
        fn new(names: &[&str]) -> Self {
            let mut b = FactBuilder::new();
            for name in names {
                b.ensure_symbol(name, FileId::NONE).unwrap();
            }
            let path = b.intern("fixture.scala").unwrap();
            let source = b.intern("").unwrap();
            b.facts.files.push(FileRecord {
                path,
                source,
                revision: StrId::NONE,
                context: StrId::NONE,
                source_hash: ContentHash::default(),
                flags: SOURCE_VERIFIED,
            });
            let facts = b.finish().unwrap();
            let mut graph = ProgramGraph {
                facts_identity: facts.identity,
                ..Default::default()
            };
            for (i, _) in names.iter().enumerate() {
                graph.symbol_nodes.push(NodeId(i as u32));
                graph.nodes.push(NodeRecord {
                    symbol: SymbolId(i as u32),
                    file: FileId(0),
                    body: BodyId::NONE,
                    flags: 0,
                });
            }
            Self { facts, graph }
        }
        fn args(&mut self, ids: &[u32]) -> IdRange {
            let start = self.facts.operands.len() as u32;
            self.facts.operands.extend(ids.iter().map(|x| ValueId(*x)));
            IdRange {
                start,
                len: ids.len() as u32,
            }
        }
        fn body(&mut self, node: u32, params: &[u32], mut ops: Vec<OperationRecord>) {
            let id = BodyId(self.facts.bodies.len() as u32);
            let parameters = self.args(params);
            let start = self.facts.operations.len() as u32;
            for o in &mut ops {
                o.body = id;
            }
            self.facts.bodies.push(BodyRecord {
                symbol: SymbolId(node),
                file: FileId(0),
                span: Span::default(),
                name_span: Span::default(),
                operations: IdRange {
                    start,
                    len: ops.len() as u32,
                },
                parameters,
                body_hash: ContentHash::default(),
                flags: 0,
            });
            self.facts.operations.extend(ops);
            self.graph.nodes[node as usize].body = id;
        }
        fn seal(&mut self) {
            self.graph.edges.clear();
            for (source, n) in self.graph.nodes.iter().enumerate() {
                if n.body.is_none() {
                    continue;
                }
                let b = self.facts.bodies[n.body.index()];
                for (i, o) in self.facts.operations[b.operations.range()]
                    .iter()
                    .enumerate()
                {
                    let kind = match o.opcode {
                        Opcode::Call => EdgeKind::Call,
                        Opcode::Allocate => EdgeKind::Construct,
                        _ => continue,
                    };
                    if o.target.is_none() {
                        continue;
                    }
                    self.graph.edges.push(EdgeRecord {
                        source: NodeId(source as u32),
                        target: NodeId(o.target.0),
                        kind,
                        occurrence: OccurrenceId::NONE,
                        operation: OperationId(b.operations.start + i as u32),
                        receiver: SymbolId::NONE,
                        flags: 0,
                    });
                }
            }
            self.graph.index().unwrap();
        }
        fn run(&self, root: &[u32], seeds: &[u32], workers: usize) -> AnalysisResult {
            let options = SolveOptions {
                workers,
                ..Default::default()
            };
            let mut q = QuerySession::new(&self.facts, &self.graph, &options).unwrap();
            let roots: Vec<_> = root
                .iter()
                .map(|n| ExecutionRoot {
                    node: NodeId(*n),
                    receiver: SymbolId::NONE,
                })
                .collect();
            q.execute(&roots).unwrap();
            q.analyze(&seeds.iter().map(|n| NodeId(*n)).collect::<Vec<_>>())
                .unwrap()
        }
    }
    fn call(target: u32) -> OperationRecord {
        OperationRecord {
            target: SymbolId(target),
            ..op(Opcode::Call)
        }
    }
    #[test]
    fn effect_closure_accumulates_beyond_first_data_issue_and_preserves_root_guards() {
        for workers in [1, 4] {
            for suffix in [
                None,
                Some(Opcode::Unknown),
                Some(Opcode::InvokeCallback),
                Some(Opcode::VirtualCall),
                Some(Opcode::StoreField),
                Some(Opcode::Initialize),
                Some(Opcode::Allocate),
                Some(Opcode::ReadElements),
            ] {
                let mut f = Fixture::new(&[
                    "p/Owner#root().",
                    "unused",
                    "p/Owner#field.",
                    "p/Owner#",
                    "callee",
                ]);
                f.facts.symbols[3].kind = 13;
                f.facts.symbols[3].flags = SYMBOL_DEFINED | SYMBOL_SCALA_PARENTS_COMPLETE;
                let mut ops = vec![OperationRecord {
                    target: SymbolId(2),
                    a: ValueId(0),
                    dest: ValueId(1),
                    ..op(Opcode::LoadField)
                }];
                if let Some(code) = suffix {
                    ops.push(OperationRecord {
                        target: if matches!(code, Opcode::Initialize | Opcode::Allocate) {
                            SymbolId(4)
                        } else {
                            SymbolId::NONE
                        },
                        a: ValueId(1),
                        b: ValueId(1),
                        dest: ValueId(2),
                        ..op(code)
                    });
                }
                ops.push(OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::Return)
                });
                f.body(0, &[], ops);
                f.body(4, &[], vec![op(Opcode::Unknown)]);
                f.seal();
                let options = SolveOptions {
                    workers,
                    ..Default::default()
                };
                let mut q = QuerySession::new(&f.facts, &f.graph, &options).unwrap();
                let owner = object_owner(
                    Atom {
                        kind: AtomKind::Object,
                        site: OperationId::NONE,
                        symbol: SymbolId(3),
                        binding: 0,
                    },
                    f.facts.operations.len(),
                )
                .unwrap();
                q.slots.insert(
                    Slot {
                        kind: SlotKind::FieldMissing,
                        owner,
                        member: 2,
                    },
                    SlotValue {
                        value: Value {
                            set: SetId(0),
                            unknown: UNKNOWN_FIELD,
                        },
                        version: 1,
                    },
                );
                q.execute(&[ExecutionRoot {
                    node: NodeId(0),
                    receiver: SymbolId(3),
                }])
                .unwrap();
                let a = q.analyze(&[]).unwrap();
                assert_eq!(a.guarded_roots, [NodeId(0)]);
                assert_eq!(
                    q.runtime_issue_sites[&ContextId(0)].reason,
                    RuntimeIssueReason::UnknownFieldValue
                );
                assert_eq!(
                    a.validate_execution_effects().unwrap(),
                    if suffix.is_none() {
                        EffectClosure::Closed
                    } else {
                        EffectClosure::Open
                    },
                    "workers={workers} suffix={suffix:?}"
                );
            }
        }
    }
    #[test]
    fn effect_closure_rejects_unknown_field_receivers_and_incomplete_execution() {
        let mut f = Fixture::new(&["root", "callee", "field"]);
        f.body(
            0,
            &[],
            vec![
                OperationRecord {
                    target: SymbolId(2),
                    dest: ValueId(1),
                    flags: OP_STATIC_FIELD,
                    ..op(Opcode::LoadField)
                },
                OperationRecord {
                    target: SymbolId(2),
                    a: ValueId(1),
                    dest: ValueId(2),
                    ..op(Opcode::LoadField)
                },
            ],
        );
        f.body(1, &[], vec![]);
        f.seal();
        let a = f.run(&[0], &[], 1);
        assert_eq!(a.validate_execution_effects().unwrap(), EffectClosure::Open);
        let options = SolveOptions {
            max_steps: 1,
            ..Default::default()
        };
        let mut q = QuerySession::new(&f.facts, &f.graph, &options).unwrap();
        q.execute(&[ExecutionRoot {
            node: NodeId(0),
            receiver: SymbolId::NONE,
        }])
        .unwrap();
        let a = q.analyze(&[]).unwrap();
        assert_eq!(a.completion, Completion::ResourceLimited);
        assert_eq!(a.validate_execution_effects().unwrap(), EffectClosure::Open);
    }
    fn scoped_dispatch_fixture(deferred: bool) -> (Fixture, Vec<ExecutionRoot>) {
        let mut f = Fixture::new(&[
            "p/Base#root().",
            "p/Base#",
            "p/Child#",
            "p/Sibling#",
            "p/Grandchild#",
            "p/Base#method().",
            "p/Child#root().",
            "p/Sibling#root().",
            "p/Grandchild#root().",
            "p/Child#unrelated().",
            "p/Base#other().",
            "p/unused().",
        ]);
        for class in 1..=4 {
            f.facts.symbols[class].kind = 13;
            f.facts.symbols[class].flags = SYMBOL_DEFINED | SYMBOL_SCALA_PARENTS_COMPLETE;
        }
        for (member, owner) in [(0, 1), (5, 1), (6, 2), (7, 3), (8, 4), (9, 2), (10, 1)] {
            f.facts.symbols[member].kind = 3;
            f.facts.symbols[member].owner = SymbolId(owner);
            f.facts.symbols[member].flags = SYMBOL_DEFINED;
        }
        for (child, parent) in [(2, 1), (3, 1), (4, 2)] {
            f.facts.relations.push(RelationRecord {
                source: SymbolId(child),
                target: SymbolId(parent),
                kind: RelationKind::Parent,
                file: FileId(0),
            });
        }
        if deferred {
            f.facts.relations.push(RelationRecord {
                source: SymbolId(2),
                target: SymbolId(5),
                kind: RelationKind::DeferredDispatch,
                file: FileId(0),
            });
        }
        for node in [5, 10] {
            f.body(
                node,
                &[],
                vec![
                    OperationRecord {
                        dest: ValueId(1),
                        ..op(Opcode::Constant)
                    },
                    OperationRecord {
                        a: ValueId(1),
                        ..op(Opcode::Return)
                    },
                ],
            );
        }
        let roots: Vec<_> = [(0, 1), (6, 2), (7, 3), (8, 4), (9, 2)]
            .into_iter()
            .map(|(node, receiver)| {
                f.body(
                    node,
                    &[],
                    vec![
                        OperationRecord {
                            target: SymbolId(if node == 9 { 10 } else { 5 }),
                            a: ValueId(0),
                            dest: ValueId(1),
                            ..op(Opcode::VirtualCall)
                        },
                        OperationRecord {
                            a: ValueId(1),
                            ..op(Opcode::Return)
                        },
                    ],
                );
                ExecutionRoot {
                    node: NodeId(node),
                    receiver: SymbolId(receiver),
                }
            })
            .collect();
        f.seal();
        for root in &roots {
            let operation = OperationId(
                f.facts.bodies[f.graph.nodes[root.node.index()].body.index()]
                    .operations
                    .start,
            );
            let target = f.facts.operations[operation.index()].target;
            let edge = EdgeRecord {
                source: root.node,
                target: NodeId(target.0),
                kind: EdgeKind::VirtualCall,
                occurrence: OccurrenceId::NONE,
                operation,
                receiver: SymbolId(1),
                flags: 0,
            };
            f.graph.edges.push(edge);
            if deferred && target == SymbolId(5) {
                f.graph.edges.push(EdgeRecord {
                    kind: EdgeKind::Guard,
                    receiver: SymbolId(2),
                    flags: EDGE_UNKNOWN | EDGE_DEFERRED_DISPATCH,
                    ..edge
                });
            }
        }
        f.graph.index().unwrap();
        f.facts.validate().unwrap();
        identity(&mut f, if deferred { 201 } else { 199 });
        (f, roots)
    }
    #[test]
    fn scoped_dispatch_unknowns_are_worker_canonical_and_cache_admission_tracks_the_frontier() {
        let (f, roots) = scoped_dispatch_fixture(true);
        let mut expected = None;
        for workers in [1, 4] {
            let options = SolveOptions {
                workers,
                execution_roots: Some(roots.clone().into()),
                ..Default::default()
            };
            let directory = tempfile::tempdir().unwrap();
            let runtime = SolverRuntime::with_cache_directory(
                &options,
                directory.path(),
                ContentHash([202; 32]),
            )
            .unwrap();
            let proof = {
                let mut q =
                    QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
                let mut result = q.analyze(&[NodeId(11)]).unwrap();
                assert_eq!(result.guarded_roots, vec![NodeId(6), NodeId(8)]);
                assert!(!result.unscoped_uncertainty);
                assert_eq!(result.completion, Completion::Conservative);
                assert!(
                    q.contexts
                        .iter()
                        .any(|context| context.key.node == NodeId(5)),
                    "known inherited effects are retained conservatively"
                );
                q.persist_completed().unwrap();
                result.metrics = Default::default();
                format!("{result:?}")
            };
            if let Some(reference) = &expected {
                assert_eq!(&proof, reference);
            } else {
                expected = Some(proof.clone());
            }
            let mut warm =
                QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
            assert!(warm.reuse_metrics().loaded_contexts > 0);
            let mut restored = warm.analyze(&[NodeId(11)]).unwrap();
            assert_eq!(restored.metrics.edge_visits, 0);
            restored.metrics = Default::default();
            assert_eq!(format!("{restored:?}"), proof);
        }
        // Adding a scoped frontier must reject an otherwise unchanged completed
        // inherited-body summary. The relation is part of the global schema.
        let (before, roots) = scoped_dispatch_fixture(false);
        let options = SolveOptions {
            execution_roots: Some(roots.into()),
            ..Default::default()
        };
        let directory = tempfile::tempdir().unwrap();
        let runtime =
            SolverRuntime::with_cache_directory(&options, directory.path(), ContentHash([203; 32]))
                .unwrap();
        {
            let mut q =
                QuerySession::with_runtime(&before.facts, &before.graph, &options, &runtime)
                    .unwrap();
            assert!(q.analyze(&[NodeId(11)]).unwrap().guarded_roots.is_empty());
            q.persist_completed().unwrap();
        }
        let mut changed =
            QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
        assert_eq!(changed.reuse_metrics().loaded_contexts, 0);
        assert!(changed.reuse_metrics().rejected_families > 0);
        assert_eq!(
            changed.analyze(&[NodeId(11)]).unwrap().guarded_roots,
            vec![NodeId(6), NodeId(8)]
        );
    }
    fn bind(target: u32, dest: u32) -> OperationRecord {
        OperationRecord {
            target: SymbolId(target),
            dest: ValueId(dest),
            ..op(Opcode::BindCallback)
        }
    }
    fn runtime_guard_fixture(revision: u8, prefix_body: bool) -> Fixture {
        let mut f = Fixture::new(&["root", "callback_boundary", "unreached"]);
        let constant = || OperationRecord {
            dest: ValueId(2),
            ..op(Opcode::Constant)
        };
        if prefix_body {
            f.body(2, &[], vec![constant()]);
        }
        f.body(0, &[], vec![call(1)]);
        f.body(
            1,
            &[1],
            vec![
                constant(),
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::InvokeCallback)
                },
                op(Opcode::Call),
            ],
        );
        if !prefix_body {
            f.body(2, &[], vec![constant()]);
        }
        f.facts.identity = ContentHash([revision; 32]);
        f.graph.facts_identity = f.facts.identity;
        f.graph.identity = ContentHash([revision + 1; 32]);
        f.seal();
        f
    }
    #[test]
    fn first_runtime_issue_sites_borrows_only_first_recorded_context_sites() {
        let mut f = runtime_guard_fixture(150, false);
        f.graph.issues.push(GraphIssue {
            kind: IssueKind::UnsupportedModel,
            node: NodeId(0),
            file: FileId(0),
            symbol: SymbolId(0),
            detail: StrId::NONE,
        });
        let options = SolveOptions {
            workers: 1,
            retain_context_evidence: false,
            ..Default::default()
        };
        let mut q = QuerySession::new(&f.facts, &f.graph, &options).unwrap();
        assert_eq!(q.first_runtime_issue_sites().len(), 0);
        q.execute(&[ExecutionRoot {
            node: NodeId(0),
            receiver: SymbolId::NONE,
        }])
        .unwrap();
        let analysis = q.analyze(&[]).unwrap();
        assert_eq!(q.context_count(), 2);
        assert_eq!(
            analysis.evidence.guard_causes[0].kind,
            IssueKind::UnsupportedModel
        );
        let mut sites = q.first_runtime_issue_sites();
        assert_eq!(sites.len(), 1);
        let first = sites.next().unwrap();
        assert_eq!(sites.len(), 0);
        assert!(sites.next().is_none());
        assert_eq!(first.1, NodeId(1));
        assert_eq!(
            first.2,
            RuntimeIssueSite {
                kind: IssueKind::UnknownExecution,
                operation: OperationId(2),
                reason: RuntimeIssueReason::UnknownCallbackValue,
            }
        );
        drop(sites);
        // The same context also reports a later, genuinely recorded issue
        // kind. The accessor exposes its first site, not one row per kind.
        q.record_runtime_issue_site(
            first.0,
            RuntimeIssueSite {
                kind: IssueKind::UnresolvedSymbol,
                operation: OperationId(3),
                reason: RuntimeIssueReason::MissingCallTarget,
            },
        )
        .unwrap();
        let owned = q.owned_bytes();
        let visits = q.metrics().edge_visits;
        for _ in 0..1_000 {
            let mut sites = q.first_runtime_issue_sites();
            assert_eq!(sites.len(), 1);
            assert_eq!(sites.next(), Some(first));
            assert_eq!(sites.len(), 0);
            assert!(sites.next().is_none());
        }
        assert_eq!(q.owned_bytes(), owned);
        assert_eq!(q.metrics().edge_visits, visits);
    }
    #[test]
    fn finalization_separates_resolved_history_from_current_local_issues() {
        for workers in [1, 4] {
            let mut f = Fixture::new(&["reader", "writer", "field", "unresolved"]);
            f.body(
                0,
                &[],
                vec![OperationRecord {
                    target: SymbolId(2),
                    a: ValueId(0),
                    dest: ValueId(1),
                    ..op(Opcode::LoadField)
                }],
            );
            f.body(
                1,
                &[],
                vec![
                    OperationRecord {
                        dest: ValueId(1),
                        ..op(Opcode::Constant)
                    },
                    OperationRecord {
                        target: SymbolId(2),
                        a: ValueId(0),
                        b: ValueId(1),
                        ..op(Opcode::StoreField)
                    },
                ],
            );
            f.body(3, &[], vec![op(Opcode::Unknown)]);
            f.seal();
            let mut q = QuerySession::new(
                &f.facts,
                &f.graph,
                &SolveOptions {
                    workers,
                    ..Default::default()
                },
            )
            .unwrap();
            q.execute(&[ExecutionRoot {
                node: NodeId(0),
                receiver: SymbolId(0),
            }])
            .unwrap();
            let before = q
                .audit_current_local_transfers(finalization::CurrentAuditOptions::default())
                .unwrap();
            assert!(before.complete);
            assert_eq!(before.contexts_with_current_local_issues, 1);
            assert_eq!(
                before.first_current_issue_by_reason[0].reason,
                "unknown_field_value"
            );
            q.execute(&[ExecutionRoot {
                node: NodeId(1),
                receiver: SymbolId(0),
            }])
            .unwrap();
            let result = q.analyze(&[]).unwrap();
            assert!(
                result.guarded_roots.contains(&NodeId(0)),
                "published historical guard remains conservative"
            );
            assert_eq!(q.first_runtime_issue_sites().len(), 1);
            let census = q.finalization_census(&result).unwrap();
            assert!(census.fixed_point_reached);
            assert_eq!(census.requested_root_nodes, 2);
            assert_eq!(census.reported_guarded_requested_root_nodes, 1);
            assert_eq!(census.guard_free_fixed_point_requested_root_nodes, Some(1));
            assert_eq!(census.monotone_issue_contexts, 1);
            let counters = q.work_counters();
            let owned = q.owned_bytes();
            let history = q.runtime_issue_sites.clone();
            let current = q
                .audit_current_local_transfers(finalization::CurrentAuditOptions::default())
                .unwrap();
            assert!(current.complete);
            assert_eq!(current.contexts_with_current_local_issues, 0);
            assert_eq!(current.contexts_without_current_local_issues, 2);
            assert!(current.first_current_issue_by_reason.is_empty());
            assert!(current.first_current_site_ranking.audit_complete);
            assert_eq!(current.first_current_site_ranking.total_contexts, 0);
            assert!(current.first_current_site_ranking.top.is_empty());
            assert!(!current.root_path_proof && !current.selection_authority);
            assert_eq!(q.runtime_issue_sites, history);
            assert_eq!(q.work_counters(), counters);
            assert_eq!(q.owned_bytes(), owned);
            q.execute(&[ExecutionRoot {
                node: NodeId(3),
                receiver: SymbolId::NONE,
            }])
            .unwrap();
            let current = q
                .audit_current_local_transfers(finalization::CurrentAuditOptions::default())
                .unwrap();
            assert!(current.complete);
            assert_eq!(current.contexts_with_current_local_issues, 1);
            assert_eq!(
                current.first_current_issue_by_reason[0].reason,
                "unknown_operation"
            );
            assert_eq!(current.first_current_issue_by_reason[0].exemplar_node, 3);
            assert_eq!(current.first_current_site_ranking.total_contexts, 1);
            assert_eq!(current.first_current_site_ranking.top[0].node, 3);
            assert_eq!(current.first_current_site_ranking.top[0].contexts, 1);
            let skipped = q
                .audit_current_local_transfers(finalization::CurrentAuditOptions {
                    scratch_budget_bytes: current.estimated_scratch_bytes - 1,
                    ..Default::default()
                })
                .unwrap();
            assert!(!skipped.complete);
            assert_eq!(skipped.status, "not_run_scratch_estimate");
            assert_eq!(
                skipped.ranking_storage_bytes, 0,
                "charged before reserving any ranking rows"
            );
            assert_eq!(skipped.attempted_contexts, 0);
        }
    }
    #[test]
    fn finalization_never_calls_local_audit_a_root_guard_proof() {
        let mut f = Fixture::new(&["root"]);
        f.body(0, &[], vec![]);
        f.seal();
        f.graph.issues.push(GraphIssue {
            kind: IssueKind::MissingSyntax,
            node: NodeId(0),
            file: FileId::NONE,
            symbol: SymbolId(0),
            detail: StrId::NONE,
        });
        let mut q = QuerySession::new(&f.facts, &f.graph, &SolveOptions::default()).unwrap();
        q.execute(&[ExecutionRoot {
            node: NodeId(0),
            receiver: SymbolId::NONE,
        }])
        .unwrap();
        let result = q.analyze(&[]).unwrap();
        let census = q.finalization_census(&result).unwrap();
        assert_eq!(census.guard_free_fixed_point_requested_root_nodes, Some(0));
        let current = q
            .audit_current_local_transfers(finalization::CurrentAuditOptions::default())
            .unwrap();
        assert!(current.complete);
        assert_eq!(current.contexts_with_current_local_issues, 0);
        assert_eq!(result.guarded_roots, vec![NodeId(0)]);
        let skipped = q
            .audit_current_local_transfers(finalization::CurrentAuditOptions {
                max_contexts: 0,
                ..Default::default()
            })
            .unwrap();
        assert!(!skipped.complete);
        assert_eq!(skipped.status, "not_run_context_limit");
        assert_eq!(skipped.audited_contexts, 0);
        let skipped = q
            .audit_current_local_transfers(finalization::CurrentAuditOptions {
                scratch_budget_bytes: 0,
                ..Default::default()
            })
            .unwrap();
        assert!(!skipped.complete);
        assert_eq!(skipped.status, "not_run_scratch_estimate");
        assert_eq!(skipped.audited_contexts, 0);
        let mut foreign = result;
        foreign.evidence.requested_roots.clear();
        assert!(q.finalization_census(&foreign).is_err());
    }
    #[test]
    fn finalization_limited_frontier_has_no_guard_free_or_current_absence_claim() {
        let mut f = Fixture::new(&["root", "callee"]);
        f.body(0, &[], vec![call(1)]);
        f.body(1, &[], vec![]);
        f.seal();
        let opts = SolveOptions {
            max_contexts: 1,
            execution_roots: Some(Arc::from([ExecutionRoot {
                node: NodeId(0),
                receiver: SymbolId::NONE,
            }])),
            ..Default::default()
        };
        let mut q = QuerySession::new(&f.facts, &f.graph, &opts).unwrap();
        let result = q.analyze(&[]).unwrap();
        let census = q.finalization_census(&result).unwrap();
        assert!(!census.fixed_point_reached);
        assert_eq!(census.guard_free_fixed_point_requested_root_nodes, None);
        assert!(census.ready_frontier_rows > 0);
        let current = q
            .audit_current_local_transfers(finalization::CurrentAuditOptions::default())
            .unwrap();
        assert!(!current.complete);
        assert_eq!(current.status, "not_run_not_fixed_point");
        assert_eq!(current.audited_contexts, 0);
    }
    #[test]
    fn runtime_guard_uses_its_actual_context_operation_and_keeps_static_priority() {
        for workers in [1, 3] {
            let mut f = runtime_guard_fixture(151, false);
            let options = SolveOptions {
                workers,
                retain_context_evidence: false,
                ..Default::default()
            };
            let roots = [ExecutionRoot {
                node: NodeId(0),
                receiver: SymbolId::NONE,
            }];
            {
                let mut q = QuerySession::new(&f.facts, &f.graph, &options).unwrap();
                q.execute(&roots).unwrap();
                assert_eq!(q.runtime_issue_sites.len(), 1);
                let result = q.analyze(&[]).unwrap();
                assert!(result.evidence.contexts.is_empty());
                let cause = result.evidence.guard_causes[0];
                assert_eq!(cause.root, NodeId(0));
                assert_eq!(cause.node, NodeId(1));
                assert_eq!(cause.kind, IssueKind::UnknownExecution);
                assert!(
                    result.obligations.iter().any(|issue| {
                        issue.symbol == SymbolId(1) && issue.kind == IssueKind::UnresolvedSymbol
                    }),
                    "another issue kind in the same node cannot replace this actual first site"
                );
                assert_eq!(
                    cause.runtime,
                    Some(RuntimeIssueSite {
                        kind: cause.kind,
                        operation: OperationId(2),
                        reason: RuntimeIssueReason::UnknownCallbackValue,
                    })
                );
                let (&context, &site) = q.runtime_issue_sites.iter().next().unwrap();
                let bytes = q.owned_bytes();
                for _ in 0..1_000 {
                    q.record_runtime_issue_site(context, site).unwrap();
                }
                assert_eq!(q.owned_bytes(), bytes);
                assert!(
                    q.record_runtime_issue_site(
                        context,
                        RuntimeIssueSite {
                            operation: OperationId(4),
                            ..site
                        }
                    )
                    .is_err(),
                    "an operation in another body cannot label this context"
                );
            }
            f.graph.issues.push(GraphIssue {
                kind: IssueKind::UnsupportedModel,
                node: NodeId(1),
                file: FileId(0),
                symbol: SymbolId(1),
                detail: StrId::NONE,
            });
            let mut q = QuerySession::new(&f.facts, &f.graph, &options).unwrap();
            q.execute(&roots).unwrap();
            let result = q.analyze(&[]).unwrap();
            let cause = result.evidence.guard_causes[0];
            assert_eq!(cause.kind, IssueKind::UnsupportedModel);
            assert_eq!(cause.runtime, None);
        }
    }
    #[test]
    fn runtime_guard_site_survives_exact_cache_and_operation_id_rebasing() {
        for workers in [1, 3] {
            let base = runtime_guard_fixture(153, false);
            let options = SolveOptions {
                workers,
                retain_context_evidence: false,
                ..Default::default()
            };
            let roots = [ExecutionRoot {
                node: NodeId(0),
                receiver: SymbolId::NONE,
            }];
            let directory = tempfile::tempdir().unwrap();
            let runtime = SolverRuntime::with_cache_directory(
                &options,
                directory.path(),
                ContentHash([155; 32]),
            )
            .unwrap();
            let expected;
            {
                let mut q =
                    QuerySession::with_runtime(&base.facts, &base.graph, &options, &runtime)
                        .unwrap();
                q.execute(&roots).unwrap();
                expected = q.analyze(&[]).unwrap().evidence.guard_causes;
                q.persist_completed().unwrap();
            }
            let mut exact =
                QuerySession::with_runtime(&base.facts, &base.graph, &options, &runtime).unwrap();
            assert_eq!(exact.reuse_metrics().loaded_contexts, 2);
            let (_, node, site) = exact.first_runtime_issue_sites().next().unwrap();
            assert_eq!(node, NodeId(1));
            assert_eq!(site.operation, OperationId(2));
            assert_eq!(site.reason, RuntimeIssueReason::UnknownCallbackValue);
            assert_eq!(exact.first_runtime_issue_sites().len(), 1);
            assert_eq!(exact.analyze(&[]).unwrap().evidence.guard_causes, expected);
            assert_eq!(exact.metrics().edge_visits, 0);
            drop(exact);
            let head = runtime_guard_fixture(155, true);
            let mut cold = QuerySession::new(&head.facts, &head.graph, &options).unwrap();
            cold.execute(&roots).unwrap();
            let expected = cold.analyze(&[]).unwrap().evidence.guard_causes;
            assert_eq!(expected[0].runtime.unwrap().operation, OperationId(3));
            let mut warm =
                QuerySession::with_runtime(&head.facts, &head.graph, &options, &runtime).unwrap();
            assert_eq!(warm.reuse_metrics().loaded_contexts, 2);
            let (_, node, site) = warm.first_runtime_issue_sites().next().unwrap();
            assert_eq!(node, NodeId(1));
            assert_eq!(site.operation, OperationId(3));
            assert_eq!(site.reason, RuntimeIssueReason::UnknownCallbackValue);
            assert_eq!(warm.first_runtime_issue_sites().len(), 1);
            assert_eq!(warm.analyze(&[]).unwrap().evidence.guard_causes, expected);
            assert_eq!(warm.metrics().edge_visits, 0);
        }
    }
    #[test]
    fn explicit_frontier_executes_only_admitted_roots_including_empty() {
        let mut f = Fixture::new(&["candidate", "excluded", "changed"]);
        f.body(0, &[], vec![call(2)]);
        f.body(1, &[], vec![call(2)]);
        f.body(2, &[], vec![]);
        f.seal();
        for node in [0, 1] {
            f.facts.suites.push(SuiteRecord {
                symbol: SymbolId(node),
                name: f.facts.symbols[node as usize].name,
                file: FileId(0),
                flags: 0,
            });
        }
        for (roots, expected) in [
            (vec![], vec![]),
            (
                vec![ExecutionRoot {
                    node: NodeId(0),
                    receiver: SymbolId::NONE,
                }],
                vec![NodeId(0), NodeId(2)],
            ),
        ] {
            let opts = SolveOptions {
                workers: 1,
                execution_roots: Some(roots.into()),
                retain_context_evidence: false,
                ..Default::default()
            };
            let mut q = QuerySession::new(&f.facts, &f.graph, &opts).unwrap();
            let result = q.analyze(&[NodeId(2)]).unwrap();
            assert_eq!(
                q.contexts.iter().map(|c| c.key.node).collect::<Vec<_>>(),
                expected
            );
            assert!(!result.contains(NodeId(1)));
            assert!(!result.unscoped_uncertainty);
            assert_eq!(
                result.evidence.requested_roots,
                opts.execution_roots
                    .as_ref()
                    .unwrap()
                    .iter()
                    .map(|r| AnalyzedRoot {
                        node: r.node,
                        receiver: r.receiver
                    })
                    .collect::<Vec<_>>()
            );
            assert!(result.evidence.contexts.is_empty());
        }
    }
    #[test]
    fn stop_reasons_preserve_pending_roots_and_round_frontier() {
        let mut f = Fixture::new(&["root", "middle", "leaf"]);
        f.body(0, &[], vec![call(1)]);
        f.body(1, &[], vec![call(2)]);
        f.body(2, &[], vec![]);
        f.seal();
        let roots = [
            ExecutionRoot {
                node: NodeId(0),
                receiver: SymbolId::NONE,
            },
            ExecutionRoot {
                node: NodeId(2),
                receiver: SymbolId::NONE,
            },
        ];
        let mut q = QuerySession::new(
            &f.facts,
            &f.graph,
            &SolveOptions {
                workers: 1,
                max_contexts: 1,
                ..Default::default()
            },
        )
        .unwrap();
        q.execute(&roots).unwrap();
        assert_eq!(q.stop_reason(), Some(StopReason::ContextLimit));
        assert_eq!(q.pending_roots, &roots[1..]);
        assert!(!q.ready.is_empty());
        q.options.max_contexts = 100;
        q.resume().unwrap();
        assert!(q.sealed);
        assert_eq!(q.context_count(), 3);
        let control = Arc::new(SolveControl::default());
        control.request_checkpoint();
        let mut q = QuerySession::new(
            &f.facts,
            &f.graph,
            &SolveOptions {
                workers: 1,
                control: Some(control.clone()),
                ..Default::default()
            },
        )
        .unwrap();
        q.execute(&roots).unwrap();
        assert_eq!(q.stop_reason(), Some(StopReason::CheckpointRequested));
        assert_eq!(q.pending_roots, roots);
        let stopped = q.analyze(&[NodeId(2)]).unwrap();
        assert_eq!(stopped.completion, Completion::ResourceLimited);
        assert_eq!(
            stopped.evidence.requested_roots,
            roots
                .iter()
                .map(|r| AnalyzedRoot {
                    node: r.node,
                    receiver: r.receiver
                })
                .collect::<Vec<_>>()
        );
        control.reset();
        q.resume().unwrap();
        assert!(q.sealed);
        let mut q = QuerySession::new(
            &f.facts,
            &f.graph,
            &SolveOptions {
                workers: 1,
                max_steps: 1,
                ..Default::default()
            },
        )
        .unwrap();
        q.execute(&roots[..1]).unwrap();
        assert_eq!(q.stop_reason(), Some(StopReason::StepLimit));
        assert!(!q.ready.is_empty());
        q.options.max_steps = 1_000;
        q.resume().unwrap();
        assert!(q.sealed);
        assert_eq!(q.context_count(), 3);
    }
    #[test]
    fn observer_emits_bounded_census_and_real_work_counters() {
        #[derive(Debug, Default)]
        struct Recorder {
            events: Mutex<Vec<SolveEvent>>,
            rows: Mutex<Vec<WorkRow>>,
        }
        impl SolveObserver for Recorder {
            fn observe(&self, e: SolveEvent) {
                self.events.lock().unwrap().push(e);
            }
            fn work_row(&self, r: WorkRow) {
                self.rows.lock().unwrap().push(r);
            }
        }
        let mut f = Fixture::new(&["root", "leaf"]);
        f.body(
            0,
            &[],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..call(1)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::Return)
                },
            ],
        );
        // Publish a real non-bottom value after the caller's first transfer.
        // The dormant callback is returned, never invoked, so only these two
        // contexts are needed and the wakeup comes from the consumed summary.
        f.body(
            1,
            &[],
            vec![
                bind(0, 1),
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::Return)
                },
            ],
        );
        f.seal();
        let observer = Arc::new(Recorder::default());
        let opts = SolveOptions {
            workers: 2,
            observer: Some(observer.clone()),
            census: CensusOptions {
                capacity: 2,
                evaluation_stride: 1,
            },
            ..Default::default()
        };
        let mut q = QuerySession::new(&f.facts, &f.graph, &opts).unwrap();
        q.execute(&[ExecutionRoot {
            node: NodeId(0),
            receiver: SymbolId::NONE,
        }])
        .unwrap();
        let c = q.work_counters();
        assert_eq!(c.contexts, 2);
        assert!(c.evaluations >= 3);
        assert!(c.reevaluations >= 1);
        assert!(c.dispatch_targets >= 1);
        let root = q
            .contexts
            .iter()
            .find(|context| context.key.node == NodeId(0))
            .unwrap();
        assert!(
            q.pool
                .members(root.value)
                .iter()
                .any(|atom| { atom.kind == AtomKind::Callback && atom.symbol == SymbolId(0) })
        );
        let events = observer.events.lock().unwrap();
        assert!(events.iter().any(|e| e.phase == SolvePhase::Complete));
        assert!(
            events
                .iter()
                .filter(|e| e.phase == SolvePhase::Publication)
                .count()
                <= 1
        );
        assert!(observer.rows.lock().unwrap().len() <= 2);
    }
    #[test]
    fn family_export_includes_pending_frames_and_fails_before_partial_publication() {
        let mut f = Fixture::new(&["root", "target", "class"]);
        let args = f.args(&[1]);
        f.facts.symbols[2].kind = 13;
        f.body(
            0,
            &[],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..op(Opcode::Constant)
                },
                OperationRecord {
                    arguments: args,
                    ..call(1)
                },
                OperationRecord {
                    target: SymbolId(2),
                    dest: ValueId(1),
                    ..op(Opcode::Allocate)
                },
                OperationRecord {
                    arguments: args,
                    ..call(1)
                },
            ],
        );
        f.body(
            1,
            &[1],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..op(Opcode::Parameter)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::Return)
                },
            ],
        );
        f.body(2, &[], vec![]);
        f.seal();
        let control = Arc::new(SolveControl::default());
        control.checkpoint_after_round(1);
        let options = SolveOptions {
            workers: 2,
            control: Some(control),
            ..Default::default()
        };
        let mut q = QuerySession::new(&f.facts, &f.graph, &options).unwrap();
        q.execute(&[ExecutionRoot {
            node: NodeId(0),
            receiver: SymbolId(0),
        }])
        .unwrap();
        let anchor = ContextId(
            q.contexts
                .iter()
                .position(|c| c.key.node == NodeId(1))
                .unwrap() as u32,
        );
        assert_eq!(q.stop_reason(), Some(StopReason::CheckpointRequested));
        assert!(!q.contexts[anchor.index()].evaluated);
        let directory = tempfile::tempdir().unwrap();
        let limits = replay::ReplayLimits::default();
        let report = q
            .export_replay_family(
                NodeId(1),
                Some(anchor),
                &directory.path().join("receiver"),
                &limits,
                64,
            )
            .unwrap();
        assert_eq!(report.variants, 2);
        assert_eq!(report.inventory.total_receivers, 1);
        assert_eq!(report.inventory.selected_evaluated, 0);
        assert!(!report.truncated);
        let family =
            replay::ReplayFamily::read(&directory.path().join("receiver"), &limits).unwrap();
        assert_eq!(
            family
                .replay(&replay::ReplayOptions::default())
                .unwrap()
                .len(),
            2
        );
        assert!(
            q.export_replay_family(
                NodeId(1),
                None,
                &directory.path().join("too_many"),
                &limits,
                1
            )
            .is_err()
        );
        assert!(!directory.path().join("too_many").exists());
        let tiny = replay::ReplayLimits {
            max_bytes: 1,
            ..limits
        };
        assert!(
            q.export_replay_family(
                NodeId(1),
                Some(anchor),
                &directory.path().join("too_large"),
                &tiny,
                64
            )
            .is_err()
        );
        assert!(!directory.path().join("too_large").exists());
    }
    #[test]
    fn six_callback_codes_do_not_share_argument_overflow_or_unknown_effects() {
        let mut f = Fixture::new(&[
            "root0",
            "root1",
            "root2",
            "root3",
            "safe4",
            "changed5",
            "helper",
            "cb0",
            "cb1",
            "cb2",
            "cb3",
            "cb4",
            "cb5",
            "changed",
            "unknown_root",
        ]);
        for root in 0..6 {
            let arguments = f.args(&[1]);
            f.body(
                root,
                &[],
                vec![
                    bind(7 + root, 1),
                    OperationRecord {
                        arguments,
                        ..call(6)
                    },
                ],
            );
            f.body(
                7 + root,
                &[],
                if root == 5 { vec![call(13)] } else { vec![] },
            );
        }
        f.body(
            6,
            &[1],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..op(Opcode::Parameter)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        f.body(13, &[], vec![]);
        let arguments = f.args(&[1]);
        f.body(
            14,
            &[],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..op(Opcode::Unknown)
                },
                OperationRecord {
                    arguments,
                    ..call(6)
                },
            ],
        );
        f.seal();
        let mut expected = None;
        for workers in [1, 4] {
            let roots: Vec<_> = (0..6)
                .chain([14])
                .map(|n| ExecutionRoot {
                    node: NodeId(n),
                    receiver: SymbolId::NONE,
                })
                .collect();
            let mut q = QuerySession::new(
                &f.facts,
                &f.graph,
                &SolveOptions {
                    workers,
                    context_policy: ContextPolicy::BoundedArguments {
                        max_variants_per_receiver: 4,
                    },
                    ..Default::default()
                },
            )
            .unwrap();
            q.execute(&roots).unwrap();
            let mut result = q.analyze(&[NodeId(13)]).unwrap();
            assert!(result.contains(NodeId(5)));
            for root in 0..5 {
                assert!(
                    !result.contains(NodeId(root)),
                    "callback code at root {root} must stay separate from changed callback"
                );
            }
            assert!(
                !result.contains(NodeId(14)),
                "opaque callback does not invent a known callback execution"
            );
            assert_eq!(result.guarded_roots, vec![NodeId(14)]);
            result.metrics = Default::default();
            let proof = format!("{result:?}");
            if let Some(expected) = &expected {
                assert_eq!(&proof, expected)
            } else {
                expected = Some(proof)
            }
        }
    }
    #[test]
    fn identical_overflow_payloads_have_stable_full_proofs_across_shape_insertion_and_cache() {
        let mut f = Fixture::new(&[
            "root_a",
            "root_b",
            "factory_a",
            "factory_b",
            "invoke",
            "closure_a",
            "closure_b",
            "data_a0",
            "data_a1",
            "data_a2",
            "data_b0",
            "data_b1",
            "data_b2",
            "changed",
        ]);
        let captured = f.args(&[1]);
        for factory in 2..4 {
            f.body(
                factory,
                &[1],
                vec![
                    OperationRecord {
                        dest: ValueId(1),
                        ..op(Opcode::Parameter)
                    },
                    OperationRecord {
                        arguments: captured,
                        ..bind(factory + 3, 2)
                    },
                    OperationRecord {
                        a: ValueId(2),
                        ..op(Opcode::Return)
                    },
                ],
            );
            f.body(
                factory + 3,
                &[1],
                if factory == 2 { vec![call(13)] } else { vec![] },
            );
        }
        let invoked = f.args(&[2]);
        for root in 0..2 {
            let mut operations = vec![OperationRecord {
                dest: ValueId(9),
                ..op(Opcode::Constant)
            }];
            for data in (7 + root * 3)..(10 + root * 3) {
                // Ordinary captured data can still overflow; only nested
                // callback identities are protected from argument joining.
                operations.push(OperationRecord {
                    target: SymbolId(data),
                    dest: ValueId(1),
                    ..op(Opcode::Allocate)
                });
                operations.push(OperationRecord {
                    a: ValueId(1),
                    arguments: captured,
                    dest: ValueId(2),
                    ..call(2 + root)
                });
                operations.push(OperationRecord {
                    a: ValueId(9),
                    arguments: invoked,
                    ..call(4)
                });
                f.body(data, &[], vec![]);
            }
            f.body(root, &[], operations);
        }
        f.body(
            4,
            &[1],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..op(Opcode::Parameter)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        f.body(13, &[], vec![]);
        f.seal();
        identity(&mut f, 163);
        let mut reference = None;
        for reverse in [false, true] {
            for workers in [1, 4] {
                let roots: Vec<_> = if reverse { [1, 0] } else { [0, 1] }
                    .into_iter()
                    .map(|node| ExecutionRoot {
                        node: NodeId(node),
                        receiver: SymbolId::NONE,
                    })
                    .collect();
                let options = SolveOptions {
                    workers,
                    max_set_members: 1,
                    context_policy: ContextPolicy::BoundedArguments {
                        max_variants_per_receiver: 1,
                    },
                    execution_roots: Some(roots.clone().into()),
                    ..Default::default()
                };
                let directory = tempfile::tempdir().unwrap();
                let runtime = SolverRuntime::with_cache_directory(
                    &options,
                    directory.path(),
                    ContentHash([163; 32]),
                )
                .unwrap();
                let proof = {
                    let mut q =
                        QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
                    q.execute(&roots).unwrap();
                    let overflow: Vec<_> = q
                        .contexts
                        .iter()
                        .filter(|c| c.key.node == NodeId(4) && c.widened)
                        .collect();
                    assert_eq!(overflow.len(), 2);
                    assert_eq!(overflow[0].key, overflow[1].key);
                    assert_ne!(overflow[0].callback_shape, overflow[1].callback_shape);
                    assert!(
                        q.pool
                            .members(q.frames.get(overflow[0].key.arguments)[0])
                            .is_empty()
                    );
                    let mut result = q.analyze(&[NodeId(13)]).unwrap();
                    assert!(result.contains(NodeId(0)));
                    assert!(!result.contains(NodeId(1)));
                    assert_eq!(result.guarded_roots, vec![NodeId(0), NodeId(1)]);
                    assert!(!result.evidence.witnesses.is_empty());
                    q.persist_completed().unwrap();
                    result.metrics = Default::default();
                    format!("{result:?}")
                };
                if let Some(expected) = &reference {
                    assert_eq!(&proof, expected, "reverse={reverse},workers={workers}");
                } else {
                    reference = Some(proof.clone());
                }
                let mut warm = QuerySession::with_runtime(
                    &f.facts,
                    &f.graph,
                    &SolveOptions {
                        workers: if workers == 1 { 4 } else { 1 },
                        ..options
                    },
                    &runtime,
                )
                .unwrap();
                assert!(warm.reuse_metrics().loaded_contexts > 0);
                warm.execute(&roots).unwrap();
                let mut result = warm.analyze(&[NodeId(13)]).unwrap();
                assert_eq!(result.metrics.edge_visits, 0);
                result.metrics = Default::default();
                assert_eq!(
                    format!("{result:?}"),
                    proof,
                    "cache reverse={reverse},workers={workers}"
                );
            }
        }
    }
    #[test]
    fn bounded_arguments_preserve_distinct_callback_codes_and_receiver_families() {
        let names: Vec<_> = (0..35).map(|i| format!("node{i}")).collect();
        let mut f = Fixture::new(&names.iter().map(String::as_str).collect::<Vec<_>>());
        let args = f.args(&[1]);
        for root in 0..2 {
            let mut ops = Vec::new();
            for callback in (2 + root * 16)..(18 + root * 16) {
                ops.push(bind(callback, 1));
                ops.push(OperationRecord {
                    a: ValueId(0),
                    arguments: args,
                    ..call(34)
                });
            }
            f.body(root, &[], ops);
        }
        for callback in 2..34 {
            f.body(callback, &[], vec![]);
        }
        f.body(
            34,
            &[1],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..op(Opcode::Parameter)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        f.seal();
        identity(&mut f, 131);
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
        let mut reference = None;
        for policy in [
            ContextPolicy::Exact,
            ContextPolicy::BoundedArguments {
                max_variants_per_receiver: 2,
            },
        ] {
            for workers in [1, 4] {
                let options = SolveOptions {
                    workers,
                    context_policy: policy,
                    census: CensusOptions {
                        capacity: 64,
                        evaluation_stride: 1,
                    },
                    ..Default::default()
                };
                let mut q = QuerySession::new(&f.facts, &f.graph, &options).unwrap();
                q.execute(&roots).unwrap();
                let result = q.analyze(&[NodeId(2)]).unwrap();
                assert!(result.contains(NodeId(0)));
                assert!(!result.contains(NodeId(1)));
                assert_eq!(result.completion, Completion::Complete);
                for callback in 2..34 {
                    assert!(q.contexts.iter().any(|c| c.key.node == NodeId(callback)));
                }
                let variants = q
                    .contexts
                    .iter()
                    .filter(|c| c.key.node == NodeId(34))
                    .count();
                let measured = q
                    .work_census()
                    .iter()
                    .find(|r| r.node == NodeId(34))
                    .unwrap()
                    .new_contexts;
                assert_eq!(measured, variants as u64);
                if policy == ContextPolicy::Exact {
                    assert_eq!(variants, 32);
                    reference = Some(result.affected.clone());
                } else {
                    assert_eq!(
                        variants, 32,
                        "distinct callback code is a control-flow partition, not captured data"
                    );
                    assert_eq!(q.work_counters().widened_contexts, 0);
                    assert_eq!(result.affected, *reference.as_ref().unwrap());
                }
            }
        }
        let dir = tempfile::tempdir().unwrap();
        let options = SolveOptions {
            workers: 4,
            context_policy: ContextPolicy::BoundedArguments {
                max_variants_per_receiver: 2,
            },
            ..Default::default()
        };
        let runtime =
            SolverRuntime::with_cache_directory(&options, dir.path(), ContentHash([131; 32]))
                .unwrap();
        let expected = {
            let mut q = QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
            q.execute(&roots).unwrap();
            let mut r = q.analyze(&[NodeId(2)]).unwrap();
            q.persist_completed().unwrap();
            r.metrics = Default::default();
            format!("{r:?}")
        };
        let warm = SolveOptions {
            workers: 1,
            ..options.clone()
        };
        let mut q = QuerySession::with_runtime(&f.facts, &f.graph, &warm, &runtime).unwrap();
        assert!(q.reuse_metrics().loaded_contexts > 0);
        q.execute(&roots).unwrap();
        let mut result = q.analyze(&[NodeId(2)]).unwrap();
        assert_eq!(result.metrics.edge_visits, 0);
        result.metrics = Default::default();
        assert_eq!(format!("{result:?}"), expected);
    }
    #[test]
    fn argument_widening_that_exceeds_the_value_limit_retains_a_scoped_guard() {
        let mut f = Fixture::new(&["root", "invoke", "a", "b", "c", "d", "factory", "captured"]);
        let args = f.args(&[1]);
        let invoked = f.args(&[2]);
        let mut ops = Vec::new();
        for data in 2..6 {
            ops.push(OperationRecord {
                target: SymbolId(data),
                dest: ValueId(1),
                ..op(Opcode::Allocate)
            });
            ops.push(OperationRecord {
                a: ValueId(1),
                arguments: args,
                dest: ValueId(2),
                ..call(6)
            });
            ops.push(OperationRecord {
                arguments: invoked,
                ..call(1)
            });
        }
        f.body(0, &[], ops);
        f.body(
            6,
            &[1],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..op(Opcode::Parameter)
                },
                OperationRecord {
                    arguments: args,
                    ..bind(7, 2)
                },
                OperationRecord {
                    a: ValueId(2),
                    ..op(Opcode::Return)
                },
            ],
        );
        f.body(7, &[1], vec![]);
        f.body(
            1,
            &[1],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..op(Opcode::Parameter)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        for node in 2..6 {
            f.body(node, &[], vec![]);
        }
        f.seal();
        let opts = SolveOptions {
            workers: 2,
            max_set_members: 2,
            context_policy: ContextPolicy::BoundedArguments {
                max_variants_per_receiver: 1,
            },
            ..Default::default()
        };
        let mut q = QuerySession::new(&f.facts, &f.graph, &opts).unwrap();
        q.execute(&[ExecutionRoot {
            node: NodeId(0),
            receiver: SymbolId::NONE,
        }])
        .unwrap();
        let result = q.analyze(&[NodeId(5)]).unwrap();
        assert_eq!(result.guarded_roots, vec![NodeId(0)]);
        assert!(!result.unscoped_uncertainty);
        assert_eq!(result.completion, Completion::Conservative);
        assert_eq!(
            q.contexts
                .iter()
                .filter(|c| c.key.node == NodeId(1))
                .count(),
            3 // one pending-bottom shape plus one exact and one overflow callback frame
        );
        assert_eq!(
            q.contexts
                .iter()
                .filter(|c| c.key.node == NodeId(1)
                    && !q.callback_shapes.get(c.callback_shape).atoms.is_empty())
                .count(),
            2
        );
        let receiver = q
            .contexts
            .iter()
            .find(|c| c.key.node == NodeId(1) && c.widened)
            .unwrap()
            .key
            .receiver;
        let frames = q.frames.len();
        let site = OperationId(
            f.facts.bodies[f.graph.nodes[6].body.index()]
                .operations
                .start
                + 1,
        );
        for binding in 1000..2000 {
            let value = q
                .pool
                .singleton(Atom {
                    kind: AtomKind::Callback,
                    site,
                    symbol: SymbolId(7),
                    binding,
                })
                .unwrap();
            q.call_context(NodeId(1), receiver, &[value]).unwrap();
        }
        assert_eq!(
            q.frames.len(),
            frames,
            "overflow inputs must not intern discarded exact frames"
        );
    }
    #[test]
    fn recursive_fixed_point_and_repeated_summary_reuse() {
        let mut f = Fixture::new(&["root", "a", "b", "changed"]);
        f.body(0, &[], vec![call(1)]);
        f.body(1, &[], vec![call(2)]);
        f.body(2, &[], vec![call(1), call(3)]);
        f.body(3, &[], vec![]);
        f.seal();
        let mut session = QuerySession::new(
            &f.facts,
            &f.graph,
            &SolveOptions {
                workers: 2,
                ..Default::default()
            },
        )
        .unwrap();
        let roots = [ExecutionRoot {
            node: NodeId(0),
            receiver: SymbolId::NONE,
        }];
        session.execute(&roots).unwrap();
        assert_eq!(session.context_count(), 4);
        let first = session.analyze(&[NodeId(3)]).unwrap();
        assert!(first.contains(NodeId(0)));
        let visits = session.metrics.edge_visits;
        let bytes = session.owned_bytes();
        for _ in 0..20 {
            session.execute(&roots).unwrap();
            let next = session.analyze(&[NodeId(3)]).unwrap();
            assert_eq!(next.affected, first.affected);
        }
        assert_eq!(session.metrics.edge_visits, visits);
        assert_eq!(session.owned_bytes(), bytes);
    }
    #[test]
    fn provider_scope_suppresses_foreign_callback_but_keeps_guard_and_local_impact() {
        let mut f = Fixture::new(&["root", "foreign_callback", "local_root", "local_change"]);
        f.facts.files.push(f.facts.files[0]);
        f.graph.nodes[1].file = FileId(1);
        f.body(
            0,
            &[],
            vec![
                bind(1, 1),
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        f.body(1, &[], vec![]);
        f.body(2, &[], vec![call(3)]);
        f.body(3, &[], vec![]);
        f.seal();
        let roots = Arc::from([
            ExecutionRoot {
                node: NodeId(0),
                receiver: SymbolId::NONE,
            },
            ExecutionRoot {
                node: NodeId(2),
                receiver: SymbolId::NONE,
            },
        ]);
        let options = SolveOptions {
            workers: 1,
            ..Default::default()
        };
        let seeds = [NodeId(1), NodeId(3)];
        let run = |absent: &[FileId]| {
            provider_scope::diagnose(
                &f.facts,
                &f.graph,
                &options,
                Arc::clone(&roots),
                absent,
                &seeds,
            )
        };
        let open = run(&[]).unwrap();
        assert_eq!(
            open.root_impacts.iter().map(|r| r.node).collect::<Vec<_>>(),
            [NodeId(0), NodeId(2)]
        );
        assert!(open.guarded_roots.is_empty());
        let scoped = run(&[FileId(1)]).unwrap();
        assert_eq!(
            scoped
                .root_impacts
                .iter()
                .map(|r| r.node)
                .collect::<Vec<_>>(),
            [NodeId(2)]
        );
        assert_eq!(scoped.guarded_roots, [NodeId(0)]);
        assert_eq!(scoped.blocked_nodes, 1);
        assert_eq!(scoped.blocked_callbacks, 1);
        assert_eq!(scoped.first_blocked_call.unwrap().target, NodeId(1));
        assert_eq!(scoped.completion, Completion::Conservative);
        assert!(run(&[FileId(0)]).is_err());
    }
    #[test]
    fn callback_contexts_do_not_cross_contaminate_roots() {
        let mut f = Fixture::new(&[
            "yes",
            "no",
            "invoke",
            "cb_changed",
            "cb_other",
            "changed",
            "other",
        ]);
        let yesargs = f.args(&[1]);
        let noargs = f.args(&[1]);
        f.body(
            0,
            &[],
            vec![
                bind(3, 1),
                OperationRecord {
                    arguments: yesargs,
                    ..call(2)
                },
            ],
        );
        f.body(
            1,
            &[],
            vec![
                bind(4, 1),
                OperationRecord {
                    arguments: noargs,
                    ..call(2)
                },
            ],
        );
        f.body(
            2,
            &[1],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..op(Opcode::Parameter)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        f.body(3, &[], vec![call(5)]);
        f.body(4, &[], vec![call(6)]);
        f.body(5, &[], vec![]);
        f.body(6, &[], vec![]);
        f.seal();
        let one = f.run(&[0, 1], &[5], 1);
        let many = f.run(&[0, 1], &[5], 4);
        assert!(one.contains(NodeId(0)));
        assert!(!one.contains(NodeId(1)));
        assert_eq!(one.affected, many.affected);
        assert_eq!(one.witnesses, many.witnesses);
        assert_eq!(one.derived_edges, many.derived_edges);
        assert!(
            one.derived_edges
                .iter()
                .any(|e| e.source == NodeId(2) && e.target == NodeId(3))
        );
    }
    #[test]
    fn called_root_with_another_receiver_does_not_mark_the_requested_binding_hit() {
        let mut f = Fixture::new(&["driver", "entry", "callback", "changed"]);
        let arguments = f.args(&[1]);
        f.body(
            0,
            &[],
            vec![
                bind(2, 1),
                OperationRecord {
                    arguments,
                    ..call(1)
                },
            ],
        );
        f.body(
            1,
            &[1],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..op(Opcode::Parameter)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        f.body(2, &[], vec![call(3)]);
        f.body(3, &[], vec![]);
        f.seal();
        let options = SolveOptions {
            execution_roots: Some(Arc::from([
                ExecutionRoot {
                    node: NodeId(0),
                    receiver: SymbolId(0),
                },
                ExecutionRoot {
                    node: NodeId(1),
                    receiver: SymbolId(1),
                },
            ])),
            retain_context_evidence: false,
            ..Default::default()
        };
        let mut q = QuerySession::new(&f.facts, &f.graph, &options).unwrap();
        let result = q.analyze(&[NodeId(3)]).unwrap();
        assert!(
            result.contains(NodeId(1)),
            "entry remains in driver diagnostics"
        );
        assert!(result.root_reached(NodeId(0), SymbolId(0)));
        assert!(
            !result.root_reached(NodeId(1), SymbolId(0)),
            "the call is not a root"
        );
        assert!(
            !result.root_reached(NodeId(1), SymbolId(1)),
            "entry as a root never receives the driver's callback"
        );
        assert!(
            result.guarded_roots.contains(&NodeId(1)),
            "the unknown root argument still requires a guard"
        );
        assert_eq!(
            result.root_impacts(),
            Some(
                [AnalyzedRoot {
                    node: NodeId(0),
                    receiver: SymbolId(0)
                }]
                .as_slice()
            ),
        );
    }

    #[test]
    fn returned_callback_resumes_missing_summary_dependents() {
        let mut f = Fixture::new(&["root", "provider", "closure", "changed"]);
        f.body(
            0,
            &[],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..call(1)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        f.body(
            1,
            &[],
            vec![
                bind(2, 1),
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::Return)
                },
            ],
        );
        f.body(2, &[], vec![call(3)]);
        f.body(3, &[], vec![]);
        f.seal();
        let result = f.run(&[0], &[3], 3);
        assert!(result.contains(NodeId(0)));
        assert!(result.metrics.invalidations > 0);
    }
    #[test]
    fn supplied_bottom_parameters_preserve_pending_callbacks_and_known_unit() {
        let mut f = Fixture::new(&[
            "pending", "unit", "missing", "unknown", "provider", "invoke", "closure", "changed",
        ]);
        let supplied = f.args(&[1]);
        f.body(
            0,
            &[],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..call(4)
                },
                OperationRecord {
                    arguments: supplied,
                    ..call(5)
                },
            ],
        );
        f.body(
            1,
            &[],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..op(Opcode::Constant)
                },
                OperationRecord {
                    arguments: supplied,
                    ..call(5)
                },
            ],
        );
        f.body(2, &[], vec![call(5)]);
        f.body(
            3,
            &[],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    a: ValueId::NONE,
                    ..op(Opcode::Assign)
                },
                OperationRecord {
                    arguments: supplied,
                    ..call(5)
                },
            ],
        );
        f.body(
            4,
            &[],
            vec![
                bind(6, 1),
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::Return)
                },
            ],
        );
        f.body(
            5,
            &[1],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..op(Opcode::Parameter)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        f.body(6, &[], vec![call(7)]);
        f.body(7, &[], vec![]);
        f.seal();
        identity(&mut f, 97);
        let roots: Vec<_> = (0..4)
            .map(|node| ExecutionRoot {
                node: NodeId(node),
                receiver: SymbolId::NONE,
            })
            .collect();
        let mut expected = None;
        for workers in [1, 2, 4, 8] {
            let options = SolveOptions {
                workers,
                quantum: 31,
                ..Default::default()
            };
            let dir = tempfile::tempdir().unwrap();
            let runtime =
                SolverRuntime::with_cache_directory(&options, dir.path(), ContentHash([98; 32]))
                    .unwrap();
            let proof;
            {
                let mut session =
                    QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
                session.execute(&roots).unwrap();
                let bottom_context = session
                    .contexts
                    .iter()
                    .enumerate()
                    .find(|(_, c)| {
                        c.key.node == NodeId(5)
                            && session.frames.get(c.key.arguments) == [Value::EMPTY]
                    })
                    .unwrap()
                    .0;
                assert!(
                    !session
                        .issue_contexts
                        .contains(&ContextId(bottom_context as u32)),
                    "a supplied empty value is not an unknown callback"
                );
                let mut result = session.analyze(&[NodeId(7)]).unwrap();
                assert!(result.contains(NodeId(0)));
                assert!(!result.contains(NodeId(1)));
                assert_eq!(
                    result.guarded_roots,
                    [NodeId(2), NodeId(3)],
                    "only missing and explicit unknown actuals require guards"
                );
                assert!(result.metrics.invalidations > 0);
                result.metrics = AnalysisMetrics::default();
                proof = format!("{result:?}");
                if let Some(expected) = &expected {
                    assert_eq!(&proof, expected, "workers={workers}");
                } else {
                    expected = Some(proof.clone());
                }
                session.persist_completed().unwrap();
            }
            let warm_options = SolveOptions {
                workers: 1,
                ..options
            };
            let warm_runtime = SolverRuntime::with_cache_directory(
                &warm_options,
                dir.path(),
                ContentHash([98; 32]),
            )
            .unwrap();
            let mut warm =
                QuerySession::with_runtime(&f.facts, &f.graph, &warm_options, &warm_runtime)
                    .unwrap();
            assert!(warm.reuse_metrics().loaded_contexts > 0);
            let mut result = warm.analyze(&[NodeId(7)]).unwrap();
            assert_eq!(warm.metrics().edge_visits, 0);
            result.metrics = AnalysisMetrics::default();
            assert_eq!(
                format!("{result:?}"),
                proof,
                "persisted parameter proof workers={workers}"
            );
        }
    }
    #[test]
    fn publication_rounds_are_independent_of_workers_and_shards() {
        const ROOTS: u32 = 384;
        let names: Vec<_> = (0..ROOTS * 2 + 3).map(|n| format!("node{n}")).collect();
        let mut f = Fixture::new(&names.iter().map(String::as_str).collect::<Vec<_>>());
        let invoke = ROOTS * 2;
        let closure = invoke + 1;
        let changed = invoke + 2;
        for root in 0..ROOTS {
            let arguments = f.args(&[1]);
            f.body(
                root,
                &[],
                vec![
                    OperationRecord {
                        dest: ValueId(1),
                        ..call(ROOTS + root)
                    },
                    OperationRecord {
                        arguments,
                        ..call(invoke)
                    },
                ],
            );
            // Each three-node family has backward summary dependencies. A
            // publication boundary through a family changes which intermediate
            // callback sets a later provider can initially observe.
            let mut recipe = vec![
                bind(closure, 1),
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::Return)
                },
            ];
            if root % 3 != 0 {
                recipe.extend([
                    OperationRecord {
                        dest: ValueId(2),
                        ..call(ROOTS + root - 1)
                    },
                    OperationRecord {
                        a: ValueId(2),
                        ..op(Opcode::Return)
                    },
                ]);
            }
            f.body(ROOTS + root, &[], recipe);
        }
        f.body(
            invoke,
            &[1],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..op(Opcode::Parameter)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        f.body(closure, &[], vec![call(changed)]);
        f.body(changed, &[], vec![]);
        f.seal();
        let roots: Vec<_> = (0..ROOTS)
            .map(|node| ExecutionRoot {
                node: NodeId(node),
                receiver: SymbolId::NONE,
            })
            .collect();
        for quantum in [31, 256] {
            let mut expected = None;
            for (workers, shard_count) in [(1, 1), (2, 1), (2, 2), (4, 2), (4, 4), (8, 8)] {
                let options = SolveOptions {
                    workers,
                    shard_count,
                    quantum,
                    ..Default::default()
                };
                let mut session = QuerySession::new(&f.facts, &f.graph, &options).unwrap();
                session.execute(&roots).unwrap();
                assert!(session.context_count() > 256);
                let mut result = session.analyze(&[NodeId(changed)]).unwrap();
                assert_eq!(result.completion, Completion::Complete);
                assert!(roots.iter().all(|root| result.contains(root.node)));
                // Compare every detached value, binding, context and proof as
                // well as impact; scheduling metrics intentionally differ.
                result.metrics = AnalysisMetrics::default();
                let proof = format!("{result:?}");
                if let Some(expected) = &expected {
                    assert_eq!(
                        &proof, expected,
                        "workers={workers}, shards={shard_count}, quantum={quantum}"
                    );
                } else {
                    expected = Some(proof);
                }
            }
        }
    }
    #[test]
    fn field_absence_subscription_observes_late_store() {
        let mut f = Fixture::new(&["root", "class", "closure", "changed", "field"]);
        f.facts.symbols[1].kind = 13;
        let allocation = OperationRecord {
            target: SymbolId(1),
            dest: ValueId(1),
            ..op(Opcode::Allocate)
        };
        f.body(
            0,
            &[],
            vec![
                allocation,
                bind(2, 2),
                OperationRecord {
                    target: SymbolId(4),
                    a: ValueId(1),
                    b: ValueId(2),
                    ..op(Opcode::StoreField)
                },
                OperationRecord {
                    target: SymbolId(4),
                    a: ValueId(1),
                    dest: ValueId(3),
                    ..op(Opcode::LoadField)
                },
                OperationRecord {
                    a: ValueId(3),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        f.body(1, &[], vec![]);
        f.body(2, &[], vec![call(3)]);
        f.body(3, &[], vec![]);
        f.body(4, &[], vec![]);
        f.seal();
        let result = f.run(&[0], &[3], 2);
        assert!(result.contains(NodeId(0)));
        assert!(result.metrics.invalidations > 0);
    }
    #[test]
    fn exact_virtual_receivers_choose_most_specific_override() {
        let mut f = Fixture::new(&[
            "yes",
            "no",
            "A",
            "B",
            "base_method",
            "A_method",
            "B_method",
            "changed",
        ]);
        f.facts.symbols[2].kind = 13;
        f.facts.symbols[3].kind = 13;
        f.facts.relations.push(RelationRecord {
            source: SymbolId(3),
            target: SymbolId(2),
            kind: RelationKind::Parent,
            file: FileId::NONE,
        });
        f.body(
            0,
            &[],
            vec![
                OperationRecord {
                    target: SymbolId(2),
                    dest: ValueId(1),
                    ..op(Opcode::Allocate)
                },
                OperationRecord {
                    target: SymbolId(4),
                    a: ValueId(1),
                    ..op(Opcode::VirtualCall)
                },
            ],
        );
        f.body(
            1,
            &[],
            vec![
                OperationRecord {
                    target: SymbolId(3),
                    dest: ValueId(1),
                    ..op(Opcode::Allocate)
                },
                OperationRecord {
                    target: SymbolId(4),
                    a: ValueId(1),
                    ..op(Opcode::VirtualCall)
                },
            ],
        );
        for i in 2..5 {
            f.body(i, &[], vec![]);
        }
        f.body(5, &[], vec![call(7)]);
        f.body(6, &[], vec![]);
        f.body(7, &[], vec![]);
        f.seal();
        for root in [0, 1] {
            let body = f.facts.bodies[f.graph.nodes[root].body.index()];
            for (target, receiver) in [(5, 2), (6, 3)] {
                f.graph.edges.push(EdgeRecord {
                    source: NodeId(root as u32),
                    target: NodeId(target),
                    kind: EdgeKind::VirtualCall,
                    occurrence: OccurrenceId::NONE,
                    operation: OperationId(body.operations.start + 1),
                    receiver: SymbolId(receiver),
                    flags: 0,
                });
            }
        }
        f.graph.index().unwrap();
        let result = f.run(&[0, 1], &[7], 4);
        assert!(result.contains(NodeId(0)));
        assert!(!result.contains(NodeId(1)));
    }
    fn mixin_fixture() -> Fixture {
        let mut f = Fixture::new(&[
            "left",
            "right",
            "Root",
            "A",
            "B",
            "Left",
            "Right",
            "root_x",
            "a_x",
            "b_x",
            "left_x",
            "superB",
            "changedA",
            "changedRoot",
        ]);
        for node in 2..7 {
            f.facts.symbols[node].kind = if node == 4 { 14 } else { 13 };
            f.facts.symbols[node].flags = SYMBOL_SCALA_PARENTS_COMPLETE;
        }
        for (child, parents) in [
            (3, &[2][..]),
            (4, &[2][..]),
            (5, &[3, 4][..]),
            (6, &[4, 3][..]),
        ] {
            for parent in parents {
                f.facts.relations.push(RelationRecord {
                    source: SymbolId(child),
                    target: SymbolId(*parent),
                    kind: RelationKind::Parent,
                    file: FileId(0),
                });
            }
        }
        for (method, owner) in [(7, 2), (8, 3), (9, 4), (10, 5), (11, 4)] {
            f.facts.symbols[method].owner = SymbolId(owner);
            f.facts.symbols[method].kind = 3;
        }
        for root in 0..2 {
            f.body(
                root,
                &[],
                vec![
                    OperationRecord {
                        target: SymbolId(root + 5),
                        dest: ValueId(1),
                        ..op(Opcode::Allocate)
                    },
                    OperationRecord {
                        opcode: Opcode::VirtualCall,
                        target: SymbolId(7),
                        a: ValueId(1),
                        ..op(Opcode::Call)
                    },
                ],
            );
        }
        for node in 2..7 {
            f.body(node, &[], vec![]);
        }
        f.body(7, &[], vec![call(13)]);
        f.body(8, &[], vec![call(12)]);
        for node in 9..14 {
            f.body(node, &[], vec![]);
        }
        f.seal();
        for root in 0..2 {
            let operation = f.facts.bodies[f.graph.nodes[root].body.index()]
                .operations
                .start
                + 1;
            for (target, receiver) in [(7, 2), (8, 3), (9, 4)] {
                f.graph.edges.push(EdgeRecord {
                    source: NodeId(root as u32),
                    target: NodeId(target),
                    kind: EdgeKind::VirtualCall,
                    operation: OperationId(operation),
                    receiver: SymbolId(receiver),
                    occurrence: OccurrenceId::NONE,
                    flags: 0,
                });
            }
        }
        f.graph.index().unwrap();
        f
    }
    #[test]
    fn ordered_mixin_dispatch_and_parent_reorder_revoke_persisted_proof() {
        let mut f = mixin_fixture();
        for workers in [1, 3] {
            let result = f.run(&[0, 1], &[12], workers);
            assert!(!result.contains(NodeId(0)), "rightmost B wins on Left");
            assert!(result.contains(NodeId(1)), "rightmost A wins on Right");
            assert!(result.guarded_roots.is_empty());
        }
        f.facts.symbols[3].flags = SYMBOL_NATIVE_BINARY;
        let unordered = f.run(&[0, 1], &[12], 2);
        assert!(unordered.contains(NodeId(0)) && unordered.contains(NodeId(1)));
        assert_eq!(unordered.guarded_roots, vec![NodeId(0), NodeId(1)]);
        f.facts.symbols[3].flags = SYMBOL_SCALA_PARENTS_COMPLETE;
        identity(&mut f, 31);
        let dir = tempfile::tempdir().unwrap();
        let options = SolveOptions {
            workers: 2,
            ..Default::default()
        };
        let runtime =
            SolverRuntime::with_cache_directory(&options, dir.path(), ContentHash([19; 32]))
                .unwrap();
        {
            let mut q = QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
            q.execute(&[ExecutionRoot {
                node: NodeId(0),
                receiver: SymbolId::NONE,
            }])
            .unwrap();
            q.persist_completed().unwrap();
        }
        let positions: Vec<_> = f
            .facts
            .relations
            .iter()
            .enumerate()
            .filter_map(|(i, r)| (r.source == SymbolId(5)).then_some(i))
            .collect();
        f.facts.relations.swap(positions[0], positions[1]);
        identity(&mut f, 32);
        let mut q = QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
        assert_eq!(q.reuse_metrics().loaded_families, 0);
        q.execute(&[ExecutionRoot {
            node: NodeId(0),
            receiver: SymbolId::NONE,
        }])
        .unwrap();
        assert!(q.analyze(&[NodeId(12)]).unwrap().contains(NodeId(0)));
    }
    #[test]
    fn trait_super_uses_actual_receiver_chain_and_qualified_super_stays_direct() {
        let mut f = mixin_fixture();
        // Left = A with B: B.super.x selects A.x. Right = B with A:
        // B.super.x selects Root.x, even though A precedes B at runtime.
        for root in 0..2 {
            let operation = f.facts.bodies[f.graph.nodes[root].body.index()]
                .operations
                .start
                + 1;
            f.facts.operations[operation as usize].opcode = Opcode::Call;
            f.facts.operations[operation as usize].target = SymbolId(11);
        }
        let body = f.graph.nodes[11].body;
        let operation = OperationId(f.facts.operations.len() as u32);
        f.facts.bodies[body.index()].operations = IdRange {
            start: operation.0,
            len: 1,
        };
        f.facts.operations.push(OperationRecord {
            body,
            target: SymbolId(7),
            a: ValueId(0),
            flags: OP_SUPER,
            ..op(Opcode::Call)
        });
        f.seal();
        f.graph.edges.retain(|e| e.source != NodeId(11));
        for (target, receiver) in [(7, 2), (8, 3), (9, 4), (10, 5)] {
            f.graph.edges.push(EdgeRecord {
                source: NodeId(11),
                target: NodeId(target),
                kind: EdgeKind::Call,
                operation,
                receiver: SymbolId(receiver),
                occurrence: OccurrenceId::NONE,
                flags: 0,
            });
        }
        f.graph.index().unwrap();
        for workers in [1, 3] {
            let a = f.run(&[0, 1], &[12], workers);
            assert!(a.contains(NodeId(0)));
            assert!(!a.contains(NodeId(1)));
            assert!(a.guarded_roots.is_empty());
            let base = f.run(&[0, 1], &[13], workers);
            assert!(!base.contains(NodeId(0)));
            assert!(base.contains(NodeId(1)));
        }
        f.facts.operations[operation.index()].flags = OP_SUPER | OP_QUALIFIED_SUPER;
        let qualified = f.run(&[0, 1], &[13], 2);
        assert!(qualified.contains(NodeId(0)) && qualified.contains(NodeId(1)));
        assert!(qualified.guarded_roots.is_empty());
        f.facts.operations[operation.index()].flags = OP_SUPER;
        f.facts.symbols[3].flags = SYMBOL_NATIVE_BINARY;
        let incomplete = f.run(&[0, 1], &[12], 2);
        assert!(incomplete.contains(NodeId(0)) && incomplete.contains(NodeId(1)));
        assert_eq!(incomplete.guarded_roots, vec![NodeId(0), NodeId(1)]);
        assert!(!incomplete.unscoped_uncertainty);
    }
    #[test]
    fn parent_super_preserves_actual_object_for_inner_virtual_dispatch() {
        let mut f = Fixture::new(&[
            "left_root",
            "right_root",
            "Base",
            "Wrapper",
            "Left",
            "Right",
            "base_close",
            "wrapper_close",
            "base_selected",
            "left_selected",
            "right_selected",
            "changed",
        ]);
        for node in 2..6 {
            f.facts.symbols[node].kind = if node == 3 { 14 } else { 13 };
            f.facts.symbols[node].flags = SYMBOL_SCALA_PARENTS_COMPLETE;
        }
        for (child, parent) in [(3, 2), (4, 3), (5, 3)] {
            f.facts.relations.push(RelationRecord {
                source: SymbolId(child),
                target: SymbolId(parent),
                kind: RelationKind::Parent,
                file: FileId(0),
            });
        }
        for (method, owner) in [(6, 2), (7, 3), (8, 2), (9, 4), (10, 5)] {
            f.facts.symbols[method].owner = SymbolId(owner);
            f.facts.symbols[method].kind = 3;
        }
        for root in 0..2 {
            f.body(
                root,
                &[],
                vec![
                    OperationRecord {
                        target: SymbolId(root + 4),
                        dest: ValueId(1),
                        ..op(Opcode::Allocate)
                    },
                    OperationRecord {
                        target: SymbolId(7),
                        a: ValueId(1),
                        ..op(Opcode::Call)
                    },
                ],
            );
        }
        for node in 2..6 {
            f.body(node, &[], vec![]);
        }
        f.body(
            6,
            &[],
            vec![OperationRecord {
                target: SymbolId(8),
                a: ValueId(0),
                ..op(Opcode::VirtualCall)
            }],
        );
        f.body(
            7,
            &[],
            vec![OperationRecord {
                target: SymbolId(6),
                a: ValueId(0),
                flags: OP_SUPER,
                ..op(Opcode::Call)
            }],
        );
        f.body(8, &[], vec![]);
        f.body(9, &[], vec![call(11)]);
        f.body(10, &[], vec![]);
        f.body(11, &[], vec![]);
        f.seal();
        let inner = f.facts.bodies[f.graph.nodes[6].body.index()]
            .operations
            .start;
        let outer = f.facts.bodies[f.graph.nodes[7].body.index()]
            .operations
            .start;
        // Attach concrete owners to the compiler-bound trait-super candidates.
        for edge in &mut f.graph.edges {
            if edge.source == NodeId(7) {
                edge.receiver = SymbolId(2);
            }
        }
        for (target, owner) in [(8, 2), (9, 4), (10, 5)] {
            f.graph.edges.push(EdgeRecord {
                source: NodeId(6),
                target: NodeId(target),
                kind: EdgeKind::VirtualCall,
                operation: OperationId(inner),
                receiver: SymbolId(owner),
                occurrence: OccurrenceId::NONE,
                flags: 0,
            });
        }
        f.graph.index().unwrap();
        for flags in [OP_SUPER, OP_SUPER | OP_QUALIFIED_SUPER] {
            f.facts.operations[outer as usize].flags = flags;
            let result = f.run(&[0, 1], &[11], 3);
            assert!(result.contains(NodeId(0)));
            assert!(!result.contains(NodeId(1)));
            assert!(result.guarded_roots.is_empty());
        }
    }
    #[test]
    fn limits_are_explicit_and_never_complete() {
        let mut f = Fixture::new(&["root", "callee"]);
        f.body(0, &[], vec![call(1)]);
        f.body(1, &[], vec![]);
        f.seal();
        let mut q = QuerySession::new(
            &f.facts,
            &f.graph,
            &SolveOptions {
                workers: 1,
                max_contexts: 1,
                ..Default::default()
            },
        )
        .unwrap();
        q.execute(&[ExecutionRoot {
            node: NodeId(0),
            receiver: SymbolId::NONE,
        }])
        .unwrap();
        let result = q.analyze(&[NodeId(1)]).unwrap();
        assert_eq!(result.completion, Completion::ResourceLimited);
        assert!(
            result
                .obligations
                .iter()
                .any(|o| o.kind == IssueKind::ResourceLimit)
        );
    }
    #[test]
    fn closure_factory_capture_families_preserve_callback_origins() {
        let mut f = Fixture::new(&[
            "yes",
            "no",
            "factory",
            "wrapper",
            "cb_changed",
            "cb_other",
            "changed",
            "other",
        ]);
        let a = f.args(&[1]);
        f.body(
            0,
            &[],
            vec![
                bind(4, 1),
                OperationRecord {
                    dest: ValueId(2),
                    arguments: a,
                    ..call(2)
                },
                OperationRecord {
                    a: ValueId(2),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        let a = f.args(&[1]);
        f.body(
            1,
            &[],
            vec![
                bind(5, 1),
                OperationRecord {
                    dest: ValueId(2),
                    arguments: a,
                    ..call(2)
                },
                OperationRecord {
                    a: ValueId(2),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        let captures = f.args(&[1]);
        f.body(
            2,
            &[1],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..op(Opcode::Parameter)
                },
                OperationRecord {
                    arguments: captures,
                    ..bind(3, 2)
                },
                OperationRecord {
                    a: ValueId(2),
                    ..op(Opcode::Return)
                },
            ],
        );
        f.body(
            3,
            &[1],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    flags: 1,
                    ..op(Opcode::Parameter)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        f.body(4, &[], vec![call(6)]);
        f.body(5, &[], vec![call(7)]);
        f.body(6, &[], vec![]);
        f.body(7, &[], vec![]);
        f.seal();
        let a = f.run(&[0, 1], &[6], 1);
        let b = f.run(&[0, 1], &[6], 4);
        assert!(a.contains(NodeId(0)));
        assert!(!a.contains(NodeId(1)));
        assert_eq!(a.affected, b.affected);
        assert_eq!(a.witnesses, b.witnesses);
        assert_eq!(a.evidence.contexts, b.evidence.contexts);
        assert_eq!(a.evidence.witnesses, b.evidence.witnesses);
        assert_eq!(a.evidence.values, b.evidence.values);
        assert_eq!(a.evidence.atoms, b.evidence.atoms);
        assert_eq!(a.evidence.captures, b.evidence.captures);
        assert!(a.evidence.captures.len() >= 2);
        for atom in &a.evidence.atoms {
            if atom.kind == 2 {
                assert!(
                    a.evidence
                        .captures
                        .iter()
                        .any(|c| c.binding == atom.binding)
                );
            }
        }
        for witness in &a.evidence.witnesses {
            if witness.binding != u32::MAX {
                assert!(
                    a.evidence
                        .captures
                        .iter()
                        .any(|c| c.binding == witness.binding)
                );
            }
        }
    }
    #[test]
    fn shared_nested_wrapper_does_not_invoke_another_roots_callback() {
        let mut f = Fixture::new(&[
            "safe_a",
            "safe_b",
            "affected",
            "inner_factory",
            "outer_factory",
            "wrapper",
            "safe_callback",
            "changed_callback",
            "invoke",
        ]);
        for root in 0..3 {
            let first = f.args(&[1]);
            let second = f.args(&[2]);
            let run = f.args(&[3]);
            f.body(
                root,
                &[],
                vec![
                    bind(if root == 2 { 7 } else { 6 }, 1),
                    OperationRecord {
                        arguments: first,
                        dest: ValueId(2),
                        ..call(3)
                    },
                    OperationRecord {
                        arguments: second,
                        dest: ValueId(3),
                        ..call(4)
                    },
                    OperationRecord {
                        arguments: run,
                        ..call(8)
                    },
                ],
            );
        }
        for factory in [3, 4] {
            let captures = f.args(&[1]);
            f.body(
                factory,
                &[1],
                vec![
                    OperationRecord {
                        dest: ValueId(1),
                        ..op(Opcode::Parameter)
                    },
                    OperationRecord {
                        arguments: captures,
                        ..bind(5, 2)
                    },
                    OperationRecord {
                        a: ValueId(2),
                        ..op(Opcode::Return)
                    },
                ],
            );
        }
        for invoke in [5, 8] {
            f.body(
                invoke,
                &[1],
                vec![
                    OperationRecord {
                        dest: ValueId(1),
                        flags: u32::from(invoke == 5),
                        ..op(Opcode::Parameter)
                    },
                    OperationRecord {
                        a: ValueId(1),
                        ..op(Opcode::InvokeCallback)
                    },
                ],
            );
        }
        f.body(6, &[], vec![]);
        f.body(7, &[], vec![]);
        f.seal();
        identity(&mut f, 89);
        let roots: Arc<[ExecutionRoot]> = (0..3)
            .map(|node| ExecutionRoot {
                node: NodeId(node),
                receiver: SymbolId::NONE,
            })
            .collect::<Vec<_>>()
            .into();
        for policy in [
            ContextPolicy::Exact,
            ContextPolicy::BoundedArguments {
                max_variants_per_receiver: 1,
            },
        ] {
            let directory = tempfile::tempdir().unwrap();
            let producer = ContentHash([84; 32]);
            let options = SolveOptions {
                workers: 2,
                context_policy: policy,
                execution_roots: Some(roots.clone()),
                ..Default::default()
            };
            let runtime =
                SolverRuntime::with_cache_directory(&options, directory.path(), producer).unwrap();
            let mut session =
                QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
            let verify = |analysis: &AnalysisResult| {
                assert!(analysis.root_reached(NodeId(2), SymbolId::NONE));
                for node in [0, 1] {
                    assert!(!analysis.root_reached(NodeId(node), SymbolId::NONE));
                }
                assert!(analysis.guarded_roots.is_empty());
            };
            let cold = session.analyze(&[NodeId(7)]).unwrap();
            verify(&cold);
            assert!(
                session
                    .closure_families
                    .keys()
                    .any(|key| session.pool.members(key.origins).len() == 2)
            );
            session.persist_completed().unwrap();
            let checkpoint = directory.path().join("nested.bin");
            session.save_checkpoint(&checkpoint, producer).unwrap();
            drop(session);
            let mut warm =
                QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
            assert!(warm.reuse_metrics().loaded_contexts > 0);
            let cached = warm.analyze(&[NodeId(7)]).unwrap();
            verify(&cached);
            assert_eq!(cold.evidence.witnesses, cached.evidence.witnesses);
            let mut restored = QuerySession::from_checkpoint(
                &f.facts,
                &f.graph,
                &options,
                &runtime,
                &checkpoint,
                producer,
            )
            .unwrap();
            let saved = restored.analyze(&[NodeId(7)]).unwrap();
            verify(&saved);
            assert_eq!(cold.evidence.witnesses, saved.evidence.witnesses);
        }
    }
    #[test]
    fn recursive_closure_history_is_payload_not_identity() {
        let mut f = Fixture::new(&["root", "factory", "wrapper", "changed"]);
        let args = f.args(&[1]);
        f.body(
            0,
            &[],
            vec![
                bind(3, 1),
                OperationRecord {
                    arguments: args,
                    ..call(1)
                },
            ],
        );
        let captures = f.args(&[1]);
        let recurse = f.args(&[2]);
        f.body(
            1,
            &[1],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..op(Opcode::Parameter)
                },
                OperationRecord {
                    arguments: captures,
                    ..bind(2, 2)
                },
                OperationRecord {
                    arguments: recurse,
                    ..call(1)
                },
                OperationRecord {
                    a: ValueId(2),
                    ..op(Opcode::Return)
                },
            ],
        );
        f.body(
            2,
            &[1],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    flags: 1,
                    ..op(Opcode::Parameter)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        f.body(3, &[], vec![]);
        f.seal();
        let mut q = QuerySession::new(
            &f.facts,
            &f.graph,
            &SolveOptions {
                workers: 3,
                max_contexts: 100,
                ..Default::default()
            },
        )
        .unwrap();
        q.execute(&[ExecutionRoot {
            node: NodeId(0),
            receiver: SymbolId::NONE,
        }])
        .unwrap();
        assert!(q.context_count() < 20);
        assert_ne!(q.completion, Completion::ResourceLimited);
    }
    #[test]
    fn compilation_dependencies_never_imply_execution() {
        let mut f = Fixture::new(&["unused", "changed"]);
        f.body(0, &[], vec![]);
        f.body(1, &[], vec![]);
        f.seal();
        f.graph.edges.push(EdgeRecord {
            source: NodeId(0),
            target: NodeId(1),
            kind: EdgeKind::Compile,
            operation: OperationId::NONE,
            occurrence: OccurrenceId::NONE,
            receiver: SymbolId::NONE,
            flags: 0,
        });
        f.graph.index().unwrap();
        let mut q = QuerySession::new(
            &f.facts,
            &f.graph,
            &SolveOptions {
                workers: 1,
                ..Default::default()
            },
        )
        .unwrap();
        q.execute(&[ExecutionRoot {
            node: NodeId(0),
            receiver: SymbolId::NONE,
        }])
        .unwrap();
        let result = q
            .analyze_typed(AnalysisSeeds {
                execution: &[NodeId(1)],
                declarations: &[NodeId(1)],
            })
            .unwrap();
        assert!(!result.contains(NodeId(0)));
        assert_eq!(result.compilation.affected, vec![NodeId(0), NodeId(1)]);
    }
    #[test]
    fn unknowns_guard_only_roots_that_can_reach_them() {
        let mut f = Fixture::new(&["precise", "uncertain", "external", "dormant"]);
        f.body(0, &[], vec![]);
        f.body(1, &[], vec![call(2)]);
        f.seal();
        f.graph.issues.push(GraphIssue {
            kind: IssueKind::MissingSyntax,
            node: NodeId(3),
            file: FileId::NONE,
            symbol: SymbolId(3),
            detail: StrId::NONE,
        });
        let result = f.run(&[0, 1], &[0], 2);
        assert_eq!(result.guarded_roots, vec![NodeId(1)]);
        assert!(!result.unscoped_uncertainty);
        assert!(!result.obligations.iter().any(|o| o.symbol == SymbolId(3)));
        assert_eq!(result.evidence.guard_causes.len(), 1);
        let cause = result.evidence.guard_causes[0];
        assert_eq!(
            (cause.root, cause.node, cause.kind),
            (NodeId(1), NodeId(2), IssueKind::UnknownExecution)
        );
    }
    #[test]
    fn auxiliary_guards_are_scoped_and_query_local() {
        let mut f = Fixture::new(&["guarded", "precise", "router", "dormant"]);
        f.body(0, &[], vec![call(2)]);
        for node in 1..4 {
            f.body(node, &[], vec![]);
        }
        f.seal();
        let mut q = QuerySession::new(
            &f.facts,
            &f.graph,
            &SolveOptions {
                workers: 2,
                ..Default::default()
            },
        )
        .unwrap();
        q.execute(&[
            ExecutionRoot {
                node: NodeId(0),
                receiver: SymbolId::NONE,
            },
            ExecutionRoot {
                node: NodeId(1),
                receiver: SymbolId::NONE,
            },
        ])
        .unwrap();
        let visits = q.metrics().edge_visits;
        let result = q
            .analyze_typed_guarded(
                AnalysisSeeds {
                    execution: &[NodeId(1)],
                    declarations: &[NodeId(3)],
                },
                &[NodeId(2), NodeId(2), NodeId(3)],
            )
            .unwrap();
        assert_eq!(result.guarded_roots, vec![NodeId(0)]);
        assert_eq!(result.evidence.guard_causes.len(), 1);
        let cause = result.evidence.guard_causes[0];
        assert_eq!(
            (cause.root, cause.node, cause.kind),
            (NodeId(0), NodeId(2), IssueKind::UnsupportedModel)
        );
        assert_eq!(result.affected, vec![NodeId(1)]);
        assert_eq!(result.compilation.affected, vec![NodeId(3)]);
        assert!(!result.unscoped_uncertainty);
        assert_eq!(
            result
                .obligations
                .iter()
                .filter(|o| o.kind == IssueKind::UnsupportedModel)
                .map(|o| o.symbol)
                .collect::<Vec<_>>(),
            vec![SymbolId(2)]
        );
        let next = q.analyze(&[]).unwrap();
        assert!(next.guarded_roots.is_empty());
        assert!(next.obligations.is_empty());
        assert!(next.evidence.guard_causes.is_empty());
        assert_eq!(q.metrics().edge_visits, visits);
        assert!(
            q.analyze_typed_guarded(
                AnalysisSeeds {
                    execution: &[],
                    declarations: &[],
                },
                &[NodeId(4)],
            )
            .is_err()
        );
    }
    #[test]
    fn external_callback_contract_executes_only_proven_arguments() {
        let mut f = Fixture::new(&["root", "external", "closure", "changed"]);
        let args = f.args(&[1]);
        f.body(
            0,
            &[],
            vec![
                bind(2, 1),
                OperationRecord {
                    arguments: args,
                    ..call(1)
                },
            ],
        );
        f.body(2, &[], vec![call(3)]);
        f.body(3, &[], vec![]);
        f.seal();
        for edge in &mut f.graph.edges {
            if edge.target == NodeId(1) {
                edge.flags |= EDGE_CALLBACK_IMMEDIATE;
            }
        }
        let immediate = f.run(&[0], &[3], 2);
        assert!(immediate.contains(NodeId(0)));
        for edge in &mut f.graph.edges {
            if edge.target == NodeId(1) {
                edge.flags = EDGE_CALLBACK_DEFERRED;
            }
        }
        let deferred = f.run(&[0], &[3], 2);
        assert!(!deferred.contains(NodeId(0)));
        assert_eq!(deferred.guarded_roots, vec![NodeId(0)]);
    }
    #[test]
    fn sealed_missing_fields_produce_scoped_unknown() {
        let mut f = Fixture::new(&["root", "class", "field"]);
        f.facts.symbols[1].kind = 13;
        f.body(
            0,
            &[],
            vec![
                OperationRecord {
                    target: SymbolId(1),
                    dest: ValueId(1),
                    ..op(Opcode::Allocate)
                },
                OperationRecord {
                    target: SymbolId(2),
                    a: ValueId(1),
                    dest: ValueId(2),
                    ..op(Opcode::LoadField)
                },
                OperationRecord {
                    a: ValueId(2),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        f.body(1, &[], vec![]);
        f.body(2, &[], vec![]);
        f.seal();
        let result = f.run(&[0], &[2], 3);
        assert_eq!(result.guarded_roots, vec![NodeId(0)]);
        assert!(!result.unscoped_uncertainty);
        assert_eq!(result.completion, Completion::Conservative);
    }

    fn identity(f: &mut Fixture, n: u8) {
        f.facts.identity = ContentHash([n; 32]);
        f.graph.facts_identity = f.facts.identity;
        f.graph.identity = ContentHash([n + 1; 32]);
    }
    #[test]
    fn persisted_fixed_point_restores_exact_dependencies_and_contexts() {
        let mut f = Fixture::new(&["root", "provider", "closure", "changed"]);
        f.body(
            0,
            &[],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..call(1)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        f.body(
            1,
            &[],
            vec![
                bind(2, 1),
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::Return)
                },
            ],
        );
        f.body(2, &[], vec![call(3)]);
        f.body(3, &[], vec![]);
        f.seal();
        identity(&mut f, 1);
        let dir = tempfile::tempdir().unwrap();
        let options = SolveOptions {
            workers: 2,
            ..Default::default()
        };
        let runtime =
            SolverRuntime::with_cache_directory(&options, dir.path(), ContentHash([5; 32]))
                .unwrap();
        let expected;
        let count;
        let reads;
        {
            let mut q = QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
            q.execute(&[ExecutionRoot {
                node: NodeId(0),
                receiver: SymbolId::NONE,
            }])
            .unwrap();
            expected = q.analyze(&[NodeId(3)]).unwrap();
            count = q.context_count();
            reads = q.dependencies.active_reads().count();
            q.persist_completed().unwrap();
        }
        let mut q = QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
        assert_eq!(q.reuse_metrics().loaded_contexts, count as u64);
        assert!(q.reuse_metrics().same_snapshot);
        assert_eq!(q.dependencies.active_reads().count(), reads);
        assert_eq!(q.metrics.edge_visits, 0);
        let result = q.analyze(&[NodeId(3)]).unwrap();
        assert_eq!(result.affected, expected.affected);
        assert_eq!(result.witnesses, expected.witnesses);
        assert_eq!(result.derived_edges, expected.derived_edges);
        assert_eq!(
            result.evidence.captures.len(),
            expected.evidence.captures.len()
        );
    }
    #[test]
    fn persisted_rebase_preserves_disconnected_solved_family_after_active_edit() {
        let mut base = Fixture::new(&[
            "changed_root",
            "unchanged_root",
            "changed_method",
            "unchanged_method",
        ]);
        base.body(0, &[], vec![call(2)]);
        base.body(1, &[], vec![call(3)]);
        base.body(2, &[], vec![]);
        base.body(3, &[], vec![]);
        base.seal();
        identity(&mut base, 1);
        let mut head = Fixture::new(&[
            "changed_root",
            "unchanged_root",
            "changed_method",
            "unchanged_method",
        ]);
        head.body(0, &[], vec![call(2)]);
        head.body(1, &[], vec![call(3)]);
        head.body(2, &[], vec![]);
        head.body(3, &[], vec![]);
        head.facts.bodies[2].body_hash = ContentHash([9; 32]);
        head.seal();
        identity(&mut head, 3);
        let dir = tempfile::tempdir().unwrap();
        let options = SolveOptions {
            workers: 2,
            ..Default::default()
        };
        let runtime =
            SolverRuntime::with_cache_directory(&options, dir.path(), ContentHash([5; 32]))
                .unwrap();
        {
            let mut q =
                QuerySession::with_runtime(&base.facts, &base.graph, &options, &runtime).unwrap();
            q.execute(&[
                ExecutionRoot {
                    node: NodeId(0),
                    receiver: SymbolId::NONE,
                },
                ExecutionRoot {
                    node: NodeId(1),
                    receiver: SymbolId::NONE,
                },
            ])
            .unwrap();
            q.persist_completed().unwrap();
        }
        let mut q =
            QuerySession::with_runtime(&head.facts, &head.graph, &options, &runtime).unwrap();
        let stats = q.reuse_metrics();
        assert_eq!(stats.loaded_families, 1);
        assert_eq!(stats.rejected_families, 1);
        assert_eq!(stats.loaded_contexts, 2);
        assert!(!stats.same_snapshot);
        q.execute(&[
            ExecutionRoot {
                node: NodeId(0),
                receiver: SymbolId::NONE,
            },
            ExecutionRoot {
                node: NodeId(1),
                receiver: SymbolId::NONE,
            },
        ])
        .unwrap();
        let result = q.analyze(&[NodeId(2)]).unwrap();
        assert!(result.contains(NodeId(0)));
        assert!(!result.contains(NodeId(1)));
        assert_eq!(q.context_count(), 4);
        assert!(q.metrics.edge_visits < 8);
    }
    #[test]
    fn persisted_rebase_remaps_compiler_node_operation_and_callback_ids() {
        let mut base = Fixture::new(&["root", "provider", "closure", "changed"]);
        base.body(
            0,
            &[],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..call(1)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        base.body(
            1,
            &[],
            vec![
                bind(2, 1),
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::Return)
                },
            ],
        );
        base.body(2, &[], vec![call(3)]);
        base.body(3, &[], vec![]);
        base.seal();
        identity(&mut base, 1);
        let mut head = Fixture::new(&["changed", "closure", "provider", "root"]);
        head.body(0, &[], vec![]);
        head.body(1, &[], vec![call(0)]);
        head.body(
            2,
            &[],
            vec![
                bind(1, 1),
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::Return)
                },
            ],
        );
        head.body(
            3,
            &[],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..call(2)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        head.seal();
        identity(&mut head, 3);
        let dir = tempfile::tempdir().unwrap();
        let options = SolveOptions {
            workers: 1,
            ..Default::default()
        };
        let runtime =
            SolverRuntime::with_cache_directory(&options, dir.path(), ContentHash([5; 32]))
                .unwrap();
        {
            let mut q =
                QuerySession::with_runtime(&base.facts, &base.graph, &options, &runtime).unwrap();
            q.execute(&[ExecutionRoot {
                node: NodeId(0),
                receiver: SymbolId::NONE,
            }])
            .unwrap();
            q.persist_completed().unwrap();
        }
        let mut q =
            QuerySession::with_runtime(&head.facts, &head.graph, &options, &runtime).unwrap();
        assert_eq!(q.reuse_metrics().loaded_families, 1);
        assert_eq!(q.metrics.edge_visits, 0);
        let result = q.analyze(&[NodeId(0)]).unwrap();
        assert!(result.contains(NodeId(3)));
        assert!(
            result
                .evidence
                .atoms
                .iter()
                .all(|a| a.symbol != SymbolId(2) || a.kind != 2)
        );
        assert!(
            result
                .derived_edges
                .iter()
                .any(|e| e.source == NodeId(3) && e.target == NodeId(1))
        );
    }
    #[test]
    fn initializer_effects_never_become_alternative_written_call_returns() {
        let mut f = Fixture::new(&[
            "root",
            "factory",
            "initializer",
            "Allowed",
            "work",
            "changed",
            "init_changed",
        ]);
        f.facts.symbols[3].kind = 13;
        f.body(
            0,
            &[],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..call(1)
                },
                OperationRecord {
                    target: SymbolId(4),
                    a: ValueId(1),
                    ..op(Opcode::VirtualCall)
                },
            ],
        );
        f.body(
            1,
            &[],
            vec![
                OperationRecord {
                    target: SymbolId(3),
                    dest: ValueId(1),
                    ..op(Opcode::Allocate)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::Return)
                },
            ],
        );
        f.body(
            2,
            &[],
            vec![
                call(6),
                OperationRecord {
                    dest: ValueId(1),
                    ..op(Opcode::Unknown)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::Return)
                },
            ],
        );
        f.body(3, &[], vec![]);
        f.body(4, &[], vec![call(5)]);
        f.body(5, &[], vec![]);
        f.body(6, &[], vec![]);
        f.seal();
        f.graph.edges.push(EdgeRecord {
            source: NodeId(0),
            target: NodeId(2),
            kind: EdgeKind::Initialize,
            operation: OperationId(0),
            occurrence: OccurrenceId::NONE,
            receiver: SymbolId::NONE,
            flags: 0,
        });
        f.graph.edges.push(EdgeRecord {
            source: NodeId(0),
            target: NodeId(4),
            kind: EdgeKind::VirtualCall,
            operation: OperationId(1),
            occurrence: OccurrenceId::NONE,
            receiver: SymbolId(3),
            flags: 0,
        });
        f.graph.index().unwrap();
        for workers in [1, 4] {
            let mut q = QuerySession::new(
                &f.facts,
                &f.graph,
                &SolveOptions {
                    workers,
                    ..Default::default()
                },
            )
            .unwrap();
            q.execute(&[ExecutionRoot {
                node: NodeId(0),
                receiver: SymbolId::NONE,
            }])
            .unwrap();
            let entered: Vec<_> = q
                .contexts
                .iter()
                .filter(|c| c.key.node == NodeId(4))
                .collect();
            assert!(!entered.is_empty());
            assert!(
                entered.iter().all(|c| !c.key.receiver.is_unknown()),
                "the initializer's unknown result must not pollute factory's exact object return"
            );
            let effect = q.analyze(&[NodeId(6)]).unwrap();
            assert!(
                effect.contains(NodeId(0)),
                "initializer effects still execute"
            );
            assert_eq!(
                effect.guarded_roots,
                [NodeId(0)],
                "initializer uncertainty still guards its caller"
            );
            assert!(effect.witnesses.iter().any(|w| w.node == NodeId(0)
                && f.graph.edges[w.edge.index()].kind == EdgeKind::Initialize));
        }
    }
    #[test]
    fn globally_stable_module_references_share_initialization_fields_and_capture_receivers() {
        let mut f = Fixture::new(&[
            "writer",
            "reader",
            "Shared.",
            "field",
            "closure",
            "changed",
            "unrelated",
            "Outer#",
            "Outer#Inner.",
            "inner_member",
        ]);
        f.facts.symbols[2].kind = 10;
        f.facts.symbols[2].flags = SYMBOL_DEFINED;
        f.facts.symbols[3].owner = SymbolId(2);
        f.facts.symbols[7].kind = 13;
        f.facts.symbols[8].kind = 10;
        f.facts.symbols[8].owner = SymbolId(7);
        f.facts.symbols[9].kind = 3;
        f.facts.symbols[9].owner = SymbolId(8);
        f.body(
            0,
            &[],
            vec![
                OperationRecord {
                    target: SymbolId(2),
                    dest: ValueId(1),
                    ..op(Opcode::Allocate)
                },
                OperationRecord {
                    target: SymbolId(2),
                    dest: ValueId(2),
                    ..op(Opcode::Allocate)
                },
                OperationRecord {
                    target: SymbolId(8),
                    dest: ValueId(3),
                    ..op(Opcode::Allocate)
                },
                OperationRecord {
                    target: SymbolId(8),
                    dest: ValueId(4),
                    ..op(Opcode::Allocate)
                },
            ],
        );
        f.body(
            1,
            &[],
            vec![
                OperationRecord {
                    target: SymbolId(2),
                    dest: ValueId(1),
                    ..op(Opcode::Allocate)
                },
                OperationRecord {
                    target: SymbolId(3),
                    a: ValueId(1),
                    dest: ValueId(2),
                    ..op(Opcode::LoadField)
                },
                OperationRecord {
                    a: ValueId(2),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        f.body(
            2,
            &[],
            vec![
                bind(4, 1),
                OperationRecord {
                    target: SymbolId(3),
                    a: ValueId(0),
                    b: ValueId(1),
                    ..op(Opcode::StoreField)
                },
            ],
        );
        f.body(4, &[], vec![call(5)]);
        for node in [3, 5, 6, 7, 8, 9] {
            f.body(node, &[], vec![]);
        }
        f.seal();
        f.graph.edges.push(EdgeRecord {
            source: NodeId(6),
            target: NodeId(2),
            kind: EdgeKind::Initialize,
            operation: OperationId::NONE,
            occurrence: OccurrenceId::NONE,
            receiver: SymbolId::NONE,
            flags: 0,
        });
        f.graph.index().unwrap();
        identity(&mut f, 149);
        let roots = [
            ExecutionRoot {
                node: NodeId(0),
                receiver: SymbolId(0),
            },
            ExecutionRoot {
                node: NodeId(1),
                receiver: SymbolId(1),
            },
            ExecutionRoot {
                node: NodeId(6),
                receiver: SymbolId(6),
            },
        ];
        let options = SolveOptions {
            workers: 4,
            ..Default::default()
        };
        let directory = tempfile::tempdir().unwrap();
        let runtime =
            SolverRuntime::with_cache_directory(&options, directory.path(), ContentHash([149; 32]))
                .unwrap();
        let expected = {
            let mut q = QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
            q.execute(&roots).unwrap();
            let modules = q
                .contexts
                .iter()
                .filter(|c| c.key.node == NodeId(2))
                .collect::<Vec<_>>();
            assert_eq!(modules.len(), 1);
            assert_eq!(
                q.pool.members(modules[0].key.receiver),
                &[Atom {
                    kind: AtomKind::Object,
                    site: OperationId::NONE,
                    symbol: SymbolId(2),
                    binding: 0
                }]
            );
            assert_eq!(
                q.contexts
                    .iter()
                    .filter(|c| c.key.node == NodeId(8))
                    .count(),
                2,
                "instance-owned objects must retain separate sites"
            );
            assert!(q.slots.contains_key(&Slot {
                kind: SlotKind::Field,
                owner: f.facts.operations.len() as u32 + 2,
                member: 3
            }));
            let mut r = q.analyze(&[NodeId(5)]).unwrap();
            assert!(r.contains(NodeId(1)));
            assert!(!r.contains(NodeId(6)));
            assert!(r.guarded_roots.is_empty());
            assert_eq!(r.completion, Completion::Complete);
            for capture in q.captures.values() {
                for atom in q.pool.members(capture.receiver) {
                    assert!(atom.site.is_none());
                }
            }
            q.persist_completed().unwrap();
            r.metrics = Default::default();
            format!("{r:?}")
        };
        let mut q = QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
        q.execute(&roots).unwrap();
        let mut result = q.analyze(&[NodeId(5)]).unwrap();
        assert_eq!(result.metrics.edge_visits, 0);
        result.metrics = Default::default();
        assert_eq!(format!("{result:?}"), expected);
    }
    fn carrier_fixture(outer_field: bool, coarse_root: bool) -> Fixture {
        let mut f = Fixture::new(&[
            "ownerA#",
            "ownerB#",
            "factory",
            "Carrier#",
            "$outer",
            "ownerCallback",
            "carrierRun",
            "callbackA",
            "callbackB",
            "coarseUser",
            "callbackC",
        ]);
        for i in [0, 1, 3] {
            f.facts.symbols[i].kind = 13;
            f.facts.symbols[i].flags = SYMBOL_DEFINED;
        }
        let callback_argument = f.args(&[1]);
        for root in 0..if coarse_root { 3 } else { 2 } {
            let node = if root == 2 { 9 } else { root };
            let callback = if root == 2 { 10 } else { 7 + root };
            let mut operations = vec![bind(callback, 1)];
            if outer_field {
                operations.push(OperationRecord {
                    target: SymbolId(5),
                    a: ValueId(0),
                    b: ValueId(1),
                    ..op(Opcode::StoreField)
                });
            }
            operations.push(OperationRecord {
                target: SymbolId(2),
                a: if root == 2 { ValueId::NONE } else { ValueId(0) },
                dest: ValueId(2),
                arguments: if outer_field {
                    IdRange::default()
                } else {
                    callback_argument
                },
                ..op(Opcode::Call)
            });
            operations.push(OperationRecord {
                target: SymbolId(6),
                a: ValueId(2),
                ..op(Opcode::Call)
            });
            f.body(node, &[], operations);
        }
        let args = f.args(&[if outer_field { 0 } else { 1 }]);
        f.body(
            2,
            if outer_field { &[] } else { &[1] },
            vec![
                OperationRecord {
                    target: SymbolId(3),
                    dest: ValueId(2),
                    arguments: args,
                    ..op(Opcode::Allocate)
                },
                OperationRecord {
                    a: ValueId(2),
                    ..op(Opcode::Return)
                },
            ],
        );
        f.body(
            3,
            &[1],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..op(Opcode::Parameter)
                },
                OperationRecord {
                    target: SymbolId(4),
                    a: ValueId(0),
                    b: ValueId(1),
                    ..op(Opcode::StoreField)
                },
            ],
        );
        let mut run = vec![OperationRecord {
            target: SymbolId(4),
            a: ValueId(0),
            dest: ValueId(1),
            ..op(Opcode::LoadField)
        }];
        if outer_field {
            run.push(OperationRecord {
                target: SymbolId(5),
                a: ValueId(1),
                dest: ValueId(1),
                ..op(Opcode::LoadField)
            });
        }
        run.push(OperationRecord {
            a: ValueId(1),
            ..op(Opcode::InvokeCallback)
        });
        f.body(6, &[], run);
        for node in [4, 5, 7, 8, 10] {
            f.body(node, &[], vec![]);
        }
        if !coarse_root {
            f.body(9, &[], vec![]);
        }
        f.seal();
        identity(&mut f, 194);
        f
    }
    #[test]
    fn receiver_roots_partition_shared_carrier_outer_fields_and_callback_families() {
        let f = carrier_fixture(true, false);
        for workers in [1, 4] {
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
                workers,
                execution_roots: Some(std::sync::Arc::from(roots)),
                ..Default::default()
            };
            let mut q = QuerySession::new(&f.facts, &f.graph, &options).unwrap();
            q.execute(&roots).unwrap();
            let result = q.analyze(&[NodeId(7)]).unwrap();
            assert!(result.contains(NodeId(0)));
            assert!(
                !result.contains(NodeId(1)),
                "carrier outer fields must not cross suite roots"
            );
            assert_eq!(result.completion, Completion::Complete);
            assert!(
                result.guarded_roots.is_empty(),
                "missing optional wildcard is bottom"
            );
            assert_eq!(q.heap_owners.rows().len(), 2);
            for key in q.heap_owners.rows() {
                let owner = q.heap_owners.lookup(*key).unwrap();
                let outer = q.slots[&Slot {
                    kind: SlotKind::Field,
                    owner,
                    member: 4,
                }]
                    .value;
                assert_eq!(q.pool.members(outer).len(), 1);
                assert_eq!(q.pool.members(outer)[0].symbol, key.root);
            }
            let run: Vec<_> = q
                .contexts
                .iter()
                .filter(|c| c.key.node == NodeId(6) && !c.key.receiver.is_bottom())
                .collect();
            assert_eq!(run.len(), 2);
            assert!(
                q.dependencies
                    .active_reads()
                    .all(|(_, read)| read.slot.kind != SlotKind::FieldAll)
            );
        }
    }
    #[test]
    fn coarse_heap_reads_see_exact_writers_and_coarse_writes_wake_exact_readers() {
        let f = carrier_fixture(false, true);
        for workers in [1, 4] {
            let mut q = QuerySession::new(
                &f.facts,
                &f.graph,
                &SolveOptions {
                    workers,
                    ..Default::default()
                },
            )
            .unwrap();
            q.execute(&[
                ExecutionRoot {
                    node: NodeId(0),
                    receiver: SymbolId(0),
                },
                ExecutionRoot {
                    node: NodeId(1),
                    receiver: SymbolId(1),
                },
            ])
            .unwrap();
            let isolated = q.analyze(&[NodeId(7)]).unwrap();
            assert!(!isolated.contains(NodeId(1)));
            q.execute(&[ExecutionRoot {
                node: NodeId(9),
                receiver: SymbolId::NONE,
            }])
            .unwrap();
            let wildcard = q.analyze(&[NodeId(10)]).unwrap();
            for node in [0, 1, 9] {
                assert!(
                    wildcard.contains(NodeId(node)),
                    "coarse writer must reach exact readers"
                );
            }
            assert_eq!(wildcard.completion, Completion::Complete);
            let aggregate = q.analyze(&[NodeId(7)]).unwrap();
            assert!(
                aggregate.contains(NodeId(9)),
                "coarse reader must see earlier exact writes"
            );
            assert!(
                !aggregate.contains(NodeId(1)),
                "coarse read must not feed an exact primary back"
            );
            assert!(wildcard.guarded_roots.is_empty());
        }
    }
    #[test]
    fn allocation_keeps_each_finite_receiver_origin_and_an_independent_coarse_alternative() {
        let f = carrier_fixture(true, false);
        let mut q = QuerySession::new(&f.facts, &f.graph, &SolveOptions::default()).unwrap();
        let receiver = q
            .pool
            .intern(
                &[
                    Atom {
                        kind: AtomKind::Object,
                        site: OperationId::NONE,
                        symbol: SymbolId(0),
                        binding: 0,
                    },
                    Atom {
                        kind: AtomKind::Object,
                        site: OperationId::NONE,
                        symbol: SymbolId(1),
                        binding: 0,
                    },
                ],
                UNKNOWN_VALUE,
            )
            .unwrap();
        let context = q.call_context(NodeId(2), receiver, &[]).unwrap();
        q.solve().unwrap();
        let value = q.contexts[context.index()].value;
        let atoms = q.pool.members(value);
        assert_eq!(atoms.len(), 3);
        let mut origins: Vec<_> = atoms
            .iter()
            .map(|atom| {
                assert_eq!(atom.kind, AtomKind::Object);
                assert_eq!(atom.symbol, SymbolId(3));
                assert!(!atom.site.is_none());
                object_origin(atom.binding)
            })
            .collect();
        origins.sort_unstable();
        assert_eq!(origins, [SymbolId(0), SymbolId(1), SymbolId::NONE]);
    }
    #[test]
    fn callback_receiver_projection_keeps_argument_receivers_and_explicit_captures() {
        let mut names = vec!["factory", "projection", "getter", "argument", "captured"];
        names.extend((0..24).map(|_| "root_receiver"));
        // Compiler symbols must be unique even though only their compact IDs
        // matter to this execution control.
        let owned: Vec<_> = names
            .iter()
            .enumerate()
            .map(|(i, n)| format!("{n}{i}"))
            .collect();
        let names: Vec<_> = owned.iter().map(String::as_str).collect();
        let mut f = Fixture::new(&names);
        let actual = f.args(&[1]);
        let captured = f.args(&[0]);
        f.body(
            0,
            &[],
            vec![
                OperationRecord {
                    target: SymbolId(3),
                    dest: ValueId(1),
                    ..op(Opcode::Allocate)
                },
                bind(1, 2),
                OperationRecord {
                    a: ValueId(2),
                    arguments: actual,
                    dest: ValueId(3),
                    ..op(Opcode::InvokeCallback)
                },
                OperationRecord {
                    arguments: captured,
                    ..bind(4, 4)
                },
                OperationRecord {
                    a: ValueId(4),
                    dest: ValueId(5),
                    ..op(Opcode::InvokeCallback)
                },
                OperationRecord {
                    a: ValueId(3),
                    ..op(Opcode::Return)
                },
            ],
        );
        f.body(
            1,
            &[1],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..op(Opcode::Parameter)
                },
                OperationRecord {
                    a: ValueId(1),
                    dest: ValueId(2),
                    ..call(2)
                },
                OperationRecord {
                    a: ValueId(2),
                    ..op(Opcode::Return)
                },
            ],
        );
        f.body(
            2,
            &[],
            vec![OperationRecord {
                a: ValueId(0),
                ..op(Opcode::Return)
            }],
        );
        f.body(3, &[], vec![]);
        f.body(
            4,
            &[1],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    flags: 1,
                    ..op(Opcode::Parameter)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::Return)
                },
            ],
        );
        f.seal();
        identity(&mut f, 156);
        let roots: Vec<_> = (5..29)
            .map(|i| ExecutionRoot {
                node: NodeId(0),
                receiver: SymbolId(i),
            })
            .collect();
        let mut expected = None;
        for workers in [1, 4] {
            let options = SolveOptions {
                workers,
                execution_roots: Some(roots.clone().into()),
                ..Default::default()
            };
            let dir = tempfile::tempdir().unwrap();
            let runtime =
                SolverRuntime::with_cache_directory(&options, dir.path(), ContentHash([156; 32]))
                    .unwrap();
            let mut q = QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
            q.execute(&roots).unwrap();
            assert_eq!(
                q.contexts
                    .iter()
                    .filter(|c| c.key.node == NodeId(0))
                    .count(),
                24
            );
            let projection: Vec<_> = q
                .contexts
                .iter()
                .filter(|c| c.key.node == NodeId(1))
                .collect();
            assert_eq!(
                projection.len(),
                24,
                "distinct actual heap origins remain distinct argument frames"
            );
            assert!(projection.iter().all(|c| c.key.receiver == Value::EMPTY));
            assert_eq!(
                q.closure_families
                    .keys()
                    .filter(|c| c.site == OperationId(1))
                    .count(),
                1
            );
            let getter: Vec<_> = q
                .contexts
                .iter()
                .filter(|c| c.key.node == NodeId(2))
                .collect();
            assert_eq!(getter.len(), 24);
            let mut origins = Vec::new();
            for context in getter {
                let atoms = q.pool.members(context.key.receiver);
                assert_eq!(atoms.len(), 1);
                assert_eq!(atoms[0].site, OperationId(0));
                assert_eq!(atoms[0].symbol, SymbolId(3));
                origins.push(object_origin(atoms[0].binding));
            }
            origins.sort_unstable();
            assert_eq!(
                origins,
                (5..29).map(SymbolId).collect::<Vec<_>>(),
                "the projection formal retains each actual receiver origin"
            );
            let captures: Vec<_> = q
                .contexts
                .iter()
                .filter(|c| c.key.node == NodeId(4))
                .collect();
            assert_eq!(
                captures.len(),
                24,
                "explicit captures are independent of unused lexical this"
            );
            let mut captured_classes: Vec<_> = captures
                .iter()
                .map(|c| {
                    assert_eq!(c.key.receiver, Value::EMPTY);
                    q.pool.members(q.frames.get(c.key.arguments)[0])[0].symbol
                })
                .collect();
            captured_classes.sort_unstable();
            assert_eq!(captured_classes, (5..29).map(SymbolId).collect::<Vec<_>>());
            let mut result = q.analyze(&[NodeId(2)]).unwrap();
            assert!(result.contains(NodeId(0)));
            assert_eq!(result.completion, Completion::Complete);
            assert!(result.guarded_roots.is_empty());
            q.persist_completed().unwrap();
            result.metrics = Default::default();
            let proof = format!("{result:?}");
            if let Some(expected) = &expected {
                assert_eq!(&proof, expected);
            } else {
                expected = Some(proof.clone());
            }
            drop(q);
            let mut warm =
                QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
            warm.execute(&roots).unwrap();
            let mut result = warm.analyze(&[NodeId(2)]).unwrap();
            assert_eq!(result.metrics.edge_visits, 0);
            result.metrics = Default::default();
            assert_eq!(format!("{result:?}"), proof);
        }
    }
    #[test]
    fn callback_receiver_projection_requires_a_complete_receiver_free_recipe() {
        let mut f = Fixture::new(&[
            "free",
            "field",
            "implicit",
            "nested",
            "passed",
            "unknown",
            "init",
            "absent",
            "structural",
            "p/Module.",
            "p/",
            "formal",
            "default",
            "member",
            "capture",
            "initializer",
            "callee",
            "guarded",
        ]);
        let capture = f.args(&[0]);
        f.body(
            0,
            &[1],
            vec![OperationRecord {
                a: ValueId(1),
                ..op(Opcode::Return)
            }],
        );
        f.body(
            1,
            &[],
            vec![OperationRecord {
                a: ValueId(0),
                target: SymbolId(16),
                dest: ValueId(1),
                ..op(Opcode::LoadField)
            }],
        );
        f.body(2, &[], vec![call(16)]);
        f.body(3, &[], vec![bind(0, 1)]);
        f.body(
            4,
            &[],
            vec![OperationRecord {
                a: ValueId(0),
                ..op(Opcode::Return)
            }],
        );
        f.body(5, &[], vec![op(Opcode::Unknown)]);
        f.body(
            6,
            &[],
            vec![OperationRecord {
                a: ValueId(1),
                target: SymbolId(16),
                ..op(Opcode::Initialize)
            }],
        );
        f.body(8, &[], vec![]);
        f.body(9, &[], vec![]);
        f.facts.symbols[9].kind = 10;
        f.facts.symbols[9].owner = SymbolId(10);
        f.facts.symbols[10].kind = 11;
        let explicit = f.args(&[2]);
        f.body(
            11,
            &[1, 2],
            vec![OperationRecord {
                a: ValueId(1),
                arguments: explicit,
                ..op(Opcode::InvokeCallback)
            }],
        );
        f.body(
            12,
            &[],
            vec![OperationRecord {
                target: SymbolId(16),
                ..op(Opcode::DefaultArgument)
            }],
        );
        f.body(
            13,
            &[],
            vec![OperationRecord {
                a: ValueId(0),
                ..call(16)
            }],
        );
        f.body(
            14,
            &[1],
            vec![OperationRecord {
                a: ValueId(1),
                arguments: capture,
                ..bind(0, 2)
            }],
        );
        f.body(15, &[], vec![]);
        f.facts.bodies[f.graph.nodes[15].body.index()].flags |= BODY_INITIALIZER;
        f.body(16, &[], vec![]);
        f.body(17, &[], vec![]);
        f.seal();
        for (source, kind, flags) in [
            (8, EdgeKind::Fixture, 0),
            (17, EdgeKind::Guard, EDGE_UNKNOWN),
        ] {
            f.graph.edges.push(EdgeRecord {
                source: NodeId(source),
                target: NodeId(16),
                kind,
                operation: OperationId::NONE,
                occurrence: OccurrenceId::NONE,
                receiver: SymbolId::NONE,
                flags,
            });
        }
        f.graph.index().unwrap();
        let types = TypeIndex::new(&f.facts);
        for node in 0..18 {
            assert_eq!(
                types.callback_receiver_unused(&f.graph, SymbolId(node)),
                matches!(node, 0 | 11 | 16),
                "receiver proof for node{node}"
            );
        }
    }
    #[test]
    fn no_body_summaries_ignore_arguments_but_preserve_receivers_effects_and_guards() {
        let mut expected = None;
        for erase_ignored_actuals in [false, true] {
            let mut f = Fixture::new(&[
                "root",
                "other",
                "opaque",
                "structural",
                "reader",
                "writer",
                "closure",
                "changed",
                "field",
            ]);
            let actual = f.args(&[1]);
            let scalar = f.args(&[2]);
            f.body(
                0,
                &[],
                vec![
                    bind(6, 1),
                    OperationRecord {
                        arguments: actual,
                        ..call(2)
                    },
                    OperationRecord {
                        arguments: actual,
                        ..call(3)
                    },
                    OperationRecord {
                        dest: ValueId(2),
                        ..op(Opcode::Constant)
                    },
                    OperationRecord {
                        arguments: scalar,
                        ..call(2)
                    },
                ],
            );
            f.body(
                1,
                &[],
                vec![
                    bind(6, 1),
                    OperationRecord {
                        arguments: actual,
                        ..call(2)
                    },
                ],
            );
            f.body(
                4,
                &[1],
                vec![
                    OperationRecord {
                        dest: ValueId(1),
                        ..op(Opcode::Parameter)
                    },
                    OperationRecord {
                        target: SymbolId(8),
                        a: ValueId(0),
                        dest: ValueId(2),
                        ..op(Opcode::LoadField)
                    },
                    OperationRecord {
                        a: ValueId(2),
                        ..op(Opcode::InvokeCallback)
                    },
                    OperationRecord {
                        a: ValueId(1),
                        ..op(Opcode::Return)
                    },
                ],
            );
            f.body(
                5,
                &[],
                vec![
                    bind(6, 1),
                    OperationRecord {
                        target: SymbolId(8),
                        a: ValueId(0),
                        b: ValueId(1),
                        ..op(Opcode::StoreField)
                    },
                ],
            );
            f.body(6, &[], vec![call(7)]);
            f.body(7, &[], vec![]);
            f.body(8, &[], vec![]);
            if erase_ignored_actuals {
                for operation in &mut f.facts.operations {
                    if operation.opcode == Opcode::Call && matches!(operation.target.0, 2 | 3) {
                        operation.arguments = IdRange::default();
                    }
                }
            }
            f.seal();
            for (target, kind) in [(5, EdgeKind::Initialize), (4, EdgeKind::Fixture)] {
                f.graph.edges.push(EdgeRecord {
                    source: NodeId(3),
                    target: NodeId(target),
                    kind,
                    operation: OperationId::NONE,
                    occurrence: OccurrenceId::NONE,
                    receiver: SymbolId::NONE,
                    flags: 0,
                });
            }
            f.graph.index().unwrap();
            identity(&mut f, 154);
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
                workers: 2,
                execution_roots: Some(roots.to_vec().into()),
                ..Default::default()
            };
            let dir = tempfile::tempdir().unwrap();
            let runtime =
                SolverRuntime::with_cache_directory(&options, dir.path(), ContentHash([154; 32]))
                    .unwrap();
            let mut q = QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
            q.execute(&roots).unwrap();
            let opaque = q
                .contexts
                .iter()
                .filter(|c| c.key.node == NodeId(2))
                .collect::<Vec<_>>();
            assert_eq!(opaque.len(), 2, "receiver identities remain distinct");
            assert!(opaque.iter().all(|c| c.key.arguments == FrameId(0)));
            let reader = q.contexts.iter().find(|c| c.key.node == NodeId(4)).unwrap();
            assert_eq!(
                reader.key.arguments,
                FrameId(0),
                "structural edges forward no actuals"
            );
            assert!(
                reader.value.is_unknown(),
                "missing formal stays unknown rather than inheriting the outer callback"
            );
            assert!(
                !q.contexts.iter().any(|c| c.key.node == NodeId(6)
                    && q.pool
                        .members(c.key.receiver)
                        .iter()
                        .any(|a| a.symbol == SymbolId(1))),
                "opaque callback arguments are not invented executions"
            );
            let mut result = q.analyze(&[NodeId(7)]).unwrap();
            assert!(
                result.contains(NodeId(0)),
                "late field store must resume the reader and callback"
            );
            assert!(!result.contains(NodeId(1)));
            assert_eq!(result.guarded_roots, vec![NodeId(0), NodeId(1)]);
            assert!(!result.unscoped_uncertainty);
            q.persist_completed().unwrap();
            result.metrics = Default::default();
            let proof = format!("{result:?}");
            if let Some(expected) = &expected {
                assert_eq!(&proof, expected);
            } else {
                expected = Some(proof.clone());
            }
            drop(q);
            let mut warm =
                QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
            warm.execute(&roots).unwrap();
            let mut result = warm.analyze(&[NodeId(7)]).unwrap();
            assert_eq!(result.metrics.edge_visits, 0);
            result.metrics = Default::default();
            assert_eq!(format!("{result:?}"), proof);
        }
    }
    #[test]
    fn ignored_no_body_actuals_never_intern_argument_frames() {
        let mut f = Fixture::new(&["opaque", "receiver"]);
        f.seal();
        let mut q = QuerySession::new(
            &f.facts,
            &f.graph,
            &SolveOptions {
                workers: 1,
                ..Default::default()
            },
        )
        .unwrap();
        let receiver = q
            .pool
            .singleton(Atom {
                kind: AtomKind::Object,
                symbol: SymbolId(1),
                site: OperationId::NONE,
                binding: 0,
            })
            .unwrap();
        let id = q.call_context(NodeId(0), receiver, &[Value::TOP]).unwrap();
        let before = q.frames.owned_bytes();
        for n in 0..10_000 {
            // These opaque arguments deliberately need not exist in the global
            // pool: neither admission nor lookup may read or intern them.
            let actual = Value {
                set: SetId(n + 1),
                unknown: 0,
            };
            assert_eq!(q.call_context(NodeId(0), receiver, &[actual]).unwrap(), id);
            let world = ReadWorld {
                facts: &f.facts,
                graph: &f.graph,
                types: &q.types,
                pool: &q.pool,
                frames: &q.frames,
                contexts: &q.contexts,
                index: &q.index,
                slots: &q.slots,
                heap_owners: &q.heap_owners,
                captures: &q.captures,
                families: &q.closure_families,
                capture_origins: &q.capture_origins,
                callback_shapes: &q.callback_shapes,
                context_policy: ContextPolicy::Exact,
                provider_scope: None,
            };
            assert_eq!(
                world
                    .summary(NodeId(0), receiver, &[actual], &q.pool, &mut Vec::new())
                    .context,
                Some(id)
            );
        }
        assert_eq!(q.frames.len(), 1);
        assert_eq!(q.frames.owned_bytes(), before);
        assert_eq!(q.contexts.len(), 1);
    }
    #[test]
    fn effect_only_initializer_edges_do_not_replay_but_fields_callbacks_and_guards_still_propagate()
    {
        for guarded in [false, true] {
            let mut f = Fixture::new(&[
                "root",
                "base",
                "store_initializer",
                "closure",
                "changed",
                "field",
                "read_initializer",
                "unrelated",
                "external",
            ]);
            f.facts.symbols[0].kind = 13;
            f.facts.symbols[1].kind = 14;
            let mut initializer = vec![
                bind(3, 1),
                OperationRecord {
                    target: SymbolId(5),
                    a: ValueId(0),
                    b: ValueId(1),
                    ..op(Opcode::StoreField)
                },
            ];
            if guarded {
                initializer.push(call(8));
            }
            f.body(2, &[], initializer);
            f.body(3, &[], vec![call(4)]);
            f.body(4, &[], vec![]);
            f.body(5, &[], vec![]);
            f.body(
                6,
                &[],
                vec![
                    OperationRecord {
                        target: SymbolId(5),
                        a: ValueId(0),
                        dest: ValueId(1),
                        ..op(Opcode::LoadField)
                    },
                    OperationRecord {
                        a: ValueId(1),
                        ..op(Opcode::InvokeCallback)
                    },
                ],
            );
            f.body(7, &[], vec![]);
            f.seal();
            for (source, target) in [(0, 1), (1, 2), (0, 6)] {
                f.graph.edges.push(EdgeRecord {
                    source: NodeId(source),
                    target: NodeId(target),
                    kind: EdgeKind::Initialize,
                    operation: OperationId::NONE,
                    occurrence: OccurrenceId::NONE,
                    receiver: SymbolId::NONE,
                    flags: 0,
                });
            }
            f.graph.index().unwrap();
            identity(&mut f, 151 + u8::from(guarded));
            let roots = [
                ExecutionRoot {
                    node: NodeId(0),
                    receiver: SymbolId(0),
                },
                ExecutionRoot {
                    node: NodeId(7),
                    receiver: SymbolId(7),
                },
            ];
            let options = SolveOptions {
                workers: 4,
                census: CensusOptions {
                    capacity: 32,
                    evaluation_stride: 1,
                },
                ..Default::default()
            };
            let dir = tempfile::tempdir().unwrap();
            let runtime =
                SolverRuntime::with_cache_directory(&options, dir.path(), ContentHash([151; 32]))
                    .unwrap();
            let expected = {
                let mut q =
                    QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
                q.execute(&roots).unwrap();
                for node in [0, 1] {
                    assert_eq!(
                        q.work_census()
                            .iter()
                            .find(|r| r.node == NodeId(node))
                            .unwrap()
                            .evaluations,
                        1,
                        "structural effects must not depend on child return publication"
                    );
                    let id = q
                        .contexts
                        .iter()
                        .position(|c| c.key.node == NodeId(node))
                        .unwrap();
                    assert!(
                        !q.dependencies
                            .snapshot_reads()
                            .any(|(consumer, read)| consumer == ContextId(id as u32)
                                && read.slot.kind == SlotKind::Summary)
                    );
                }
                assert!(
                    q.work_census()
                        .iter()
                        .find(|r| r.node == NodeId(6))
                        .unwrap()
                        .reevaluations
                        > 0,
                    "the negative field read must still resume after the store"
                );
                let mut r = q.analyze(&[NodeId(4)]).unwrap();
                assert!(r.contains(NodeId(0)));
                assert!(!r.contains(NodeId(7)));
                assert!(!r.evidence.captures.is_empty());
                assert!(r.evidence.witnesses.iter().any(|w| w.binding != u32::MAX));
                assert_eq!(
                    r.guarded_roots,
                    if guarded { vec![NodeId(0)] } else { vec![] }
                );
                assert!(!r.unscoped_uncertainty);
                if guarded {
                    assert!(
                        r.evidence
                            .guard_causes
                            .iter()
                            .any(|c| c.root == NodeId(0) && c.node == NodeId(8))
                    );
                }
                q.persist_completed().unwrap();
                r.metrics = Default::default();
                format!("{r:?}")
            };
            let mut q = QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
            q.execute(&roots).unwrap();
            let mut r = q.analyze(&[NodeId(4)]).unwrap();
            assert_eq!(r.metrics.edge_visits, 0);
            r.metrics = Default::default();
            assert_eq!(format!("{r:?}"), expected);
        }
    }
    #[test]
    fn equal_declared_constraints_share_receiver_contexts_and_preserve_dispatch() {
        let mut f = Fixture::new(&[
            "root",
            "producer_a",
            "producer_b",
            "narrow_work",
            "sibling_work",
            "Narrow",
            "Sibling",
            "changed",
            "outside",
        ]);
        for symbol in &mut f.facts.symbols {
            symbol.flags = SYMBOL_DEFINED | SYMBOL_SCALA_PARENTS_COMPLETE;
        }
        for class in [5, 6] {
            f.facts.symbols[class].kind = 13;
            f.facts.symbols[class].properties = 8;
        }
        f.facts.symbols[3].owner = SymbolId(5);
        f.facts.symbols[4].owner = SymbolId(6);
        f.body(
            0,
            &[],
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..call(1)
                },
                OperationRecord {
                    target: SymbolId(3),
                    a: ValueId(1),
                    ..op(Opcode::VirtualCall)
                },
                OperationRecord {
                    dest: ValueId(2),
                    ..call(2)
                },
                OperationRecord {
                    target: SymbolId(3),
                    a: ValueId(2),
                    ..op(Opcode::VirtualCall)
                },
            ],
        );
        for producer in [1, 2] {
            f.body(
                producer,
                &[],
                vec![
                    OperationRecord {
                        dest: ValueId(1),
                        ..op(Opcode::Unknown)
                    },
                    OperationRecord {
                        a: ValueId(1),
                        ..op(Opcode::Return)
                    },
                ],
            );
        }
        f.body(3, &[], vec![call(7)]);
        f.body(4, &[], vec![call(8)]);
        for node in 5..=8 {
            f.body(node, &[], vec![]);
        }
        f.seal();
        for operation in [1, 3] {
            for (target, owner) in [(3, 5), (4, 6)] {
                f.graph.edges.push(EdgeRecord {
                    source: NodeId(0),
                    target: NodeId(target),
                    kind: EdgeKind::VirtualCall,
                    operation: OperationId(operation),
                    occurrence: OccurrenceId::NONE,
                    receiver: SymbolId(owner),
                    flags: 0,
                });
            }
        }
        f.graph.index().unwrap();
        f.facts.bound_classes = vec![SymbolId(5), SymbolId(5)];
        f.facts.result_bounds = [1, 2]
            .into_iter()
            .enumerate()
            .map(|(i, producer)| ResultBoundRecord {
                symbol: SymbolId(producer),
                operation: OperationId::NONE,
                classes: IdRange {
                    start: i as u32,
                    len: 1,
                },
            })
            .collect();
        identity(&mut f, 158);
        let roots = [ExecutionRoot {
            node: NodeId(0),
            receiver: SymbolId::NONE,
        }];
        let mut expected = None;
        for workers in [1, 4] {
            let options = SolveOptions {
                workers,
                execution_roots: Some(roots.to_vec().into()),
                ..Default::default()
            };
            let directory = tempfile::tempdir().unwrap();
            let runtime = SolverRuntime::with_cache_directory(
                &options,
                directory.path(),
                ContentHash([158; 32]),
            )
            .unwrap();
            let mut q = QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
            q.execute(&roots).unwrap();
            let producer = |node| {
                q.contexts
                    .iter()
                    .find(|c| c.key.node == NodeId(node))
                    .unwrap()
                    .value
            };
            assert_eq!(producer(1), producer(2));
            assert_eq!(
                q.contexts
                    .iter()
                    .filter(|c| c.key.node == NodeId(3))
                    .count(),
                1
            );
            assert!(!q.contexts.iter().any(|c| c.key.node == NodeId(4)));
            assert!(
                q.pool
                    .members(producer(1))
                    .iter()
                    .all(|a| a.kind == AtomKind::UpperBound)
            );
            assert!(!q.analyze(&[NodeId(8)]).unwrap().contains(NodeId(0)));
            let mut result = q.analyze(&[NodeId(7)]).unwrap();
            assert!(result.contains(NodeId(0)));
            assert_eq!(
                result.guarded_roots,
                vec![NodeId(0)],
                "unknown execution remains explicitly guarded"
            );
            q.persist_completed().unwrap();
            result.metrics = Default::default();
            let proof = format!("{result:?}");
            if let Some(expected) = &expected {
                assert_eq!(&proof, expected);
            } else {
                expected = Some(proof.clone());
            }
            drop(q);
            let mut warm =
                QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
            warm.execute(&roots).unwrap();
            let mut result = warm.analyze(&[NodeId(7)]).unwrap();
            assert_eq!(result.metrics.edge_visits, 0);
            result.metrics = Default::default();
            assert_eq!(format!("{result:?}"), proof);
        }
    }
    #[test]
    fn typed_unknown_clauses_survive_cache_rebase_and_invalidate_per_operation() {
        fn fixture(reverse: bool) -> Fixture {
            let names = [
                "narrow_root",
                "broad_root",
                "known_root",
                "provider",
                "Base",
                "Narrow",
                "Allowed",
                "Sibling",
                "NoMarker",
                "Marker",
                "base_work",
                "allowed_work",
                "sibling_work",
                "unmarked_work",
                "changed",
                "outsider",
                "unmarked",
            ];
            let id = |n: u32| {
                if reverse {
                    names.len() as u32 - 1 - n
                } else {
                    n
                }
            };
            let ordered: Vec<_> = (0..names.len())
                .map(|n| names[if reverse { names.len() - 1 - n } else { n }])
                .collect();
            let mut f = Fixture::new(&ordered);
            for symbol in &mut f.facts.symbols {
                symbol.flags = SYMBOL_DEFINED;
            }
            for logical in 4..=9 {
                let symbol = &mut f.facts.symbols[id(logical) as usize];
                symbol.kind = if logical == 4 || logical == 9 { 14 } else { 13 };
                symbol.flags |= SYMBOL_SCALA_PARENTS_COMPLETE;
                if (6..=8).contains(&logical) {
                    symbol.properties |= 8;
                }
            }
            for (child, parent) in [(5, 4), (6, 5), (6, 9), (7, 4), (8, 5)] {
                f.facts.relations.push(RelationRecord {
                    source: SymbolId(id(child)),
                    target: SymbolId(id(parent)),
                    kind: RelationKind::Parent,
                    file: FileId(0),
                });
            }
            for (method, owner) in [(10, 4), (11, 6), (12, 7), (13, 8)] {
                f.facts.symbols[id(method) as usize].owner = SymbolId(id(owner));
            }
            for position in 0..names.len() as u32 {
                let logical = if reverse {
                    names.len() as u32 - 1 - position
                } else {
                    position
                };
                let recipe = match logical {
                    0 => vec![
                        OperationRecord {
                            dest: ValueId(1),
                            ..call(id(3))
                        },
                        OperationRecord {
                            target: SymbolId(id(10)),
                            a: ValueId(1),
                            ..op(Opcode::VirtualCall)
                        },
                    ],
                    1 => vec![
                        OperationRecord {
                            dest: ValueId(1),
                            ..call(id(3))
                        },
                        OperationRecord {
                            dest: ValueId(2),
                            ..op(Opcode::Unknown)
                        },
                        OperationRecord {
                            a: ValueId(1),
                            b: ValueId(2),
                            dest: ValueId(3),
                            ..op(Opcode::Join)
                        },
                        OperationRecord {
                            target: SymbolId(id(10)),
                            a: ValueId(3),
                            ..op(Opcode::VirtualCall)
                        },
                    ],
                    2 => vec![
                        OperationRecord {
                            target: SymbolId(id(6)),
                            dest: ValueId(1),
                            ..op(Opcode::Allocate)
                        },
                        OperationRecord {
                            target: SymbolId(id(10)),
                            a: ValueId(1),
                            ..op(Opcode::VirtualCall)
                        },
                    ],
                    3 => vec![
                        OperationRecord {
                            dest: ValueId(1),
                            ..op(Opcode::Unknown)
                        },
                        OperationRecord {
                            a: ValueId(1),
                            ..op(Opcode::Return)
                        },
                    ],
                    11 => vec![call(id(14))],
                    12 => vec![call(id(15))],
                    13 => vec![call(id(16))],
                    _ => vec![],
                };
                f.body(id(logical), &[], recipe);
            }
            f.seal();
            for (root, ordinal) in [(0, 1), (1, 3), (2, 1)] {
                let body = f.facts.bodies[f.graph.nodes[id(root) as usize].body.index()];
                for (method, owner) in [(11, 6), (12, 7), (13, 8)] {
                    f.graph.edges.push(EdgeRecord {
                        source: NodeId(id(root)),
                        target: NodeId(id(method)),
                        kind: EdgeKind::VirtualCall,
                        occurrence: OccurrenceId::NONE,
                        operation: OperationId(body.operations.start + ordinal),
                        receiver: SymbolId(id(owner)),
                        flags: 0,
                    });
                }
            }
            f.graph.index().unwrap();
            let source = f.facts.bodies[f.graph.nodes[id(0) as usize].body.index()]
                .operations
                .start;
            let mut conjunction = [SymbolId(id(5)), SymbolId(id(9))];
            conjunction.sort_unstable();
            f.facts.bound_classes.extend(conjunction);
            f.facts.bound_classes.push(SymbolId(id(4)));
            f.facts.result_bounds = vec![
                ResultBoundRecord {
                    symbol: SymbolId(id(3)),
                    operation: OperationId(source),
                    classes: IdRange { start: 0, len: 2 },
                },
                ResultBoundRecord {
                    symbol: SymbolId(id(3)),
                    operation: OperationId::NONE,
                    classes: IdRange { start: 2, len: 1 },
                },
            ];
            identity(&mut f, if reverse { 83 } else { 81 });
            f
        }
        fn proof(mut result: AnalysisResult) -> String {
            result.metrics = AnalysisMetrics::default();
            format!("{result:?}")
        }
        for workers in [1, 4] {
            let base = fixture(false);
            let mut head = fixture(true);
            let id = |n: u32| 16 - n;
            let options = SolveOptions {
                workers,
                ..Default::default()
            };
            let directory = tempfile::tempdir().unwrap();
            let runtime = SolverRuntime::with_cache_directory(
                &options,
                directory.path(),
                ContentHash([89; 32]),
            )
            .unwrap();
            let roots = |head: bool| {
                (0..3)
                    .map(|n| ExecutionRoot {
                        node: NodeId(if head { id(n) } else { n }),
                        receiver: SymbolId::NONE,
                    })
                    .collect::<Vec<_>>()
            };
            let cold;
            {
                let mut q =
                    QuerySession::with_runtime(&base.facts, &base.graph, &options, &runtime)
                        .unwrap();
                q.execute(&roots(false)).unwrap();
                let result = q.analyze(&[NodeId(15)]).unwrap();
                assert!(
                    !result.contains(NodeId(0))
                        && result.contains(NodeId(1))
                        && !result.contains(NodeId(2))
                );
                assert_eq!(result.guarded_roots, [NodeId(0), NodeId(1)]);
                let unmarked = q.analyze(&[NodeId(16)]).unwrap();
                assert!(
                    !unmarked.contains(NodeId(0))
                        && unmarked.contains(NodeId(1))
                        && !unmarked.contains(NodeId(2))
                );
                cold = proof(result);
                q.persist_completed().unwrap();
            }
            {
                let mut warm =
                    QuerySession::with_runtime(&base.facts, &base.graph, &options, &runtime)
                        .unwrap();
                assert!(
                    warm.reuse_metrics().same_snapshot && warm.reuse_metrics().loaded_contexts > 0
                );
                assert_eq!(proof(warm.analyze(&[NodeId(15)]).unwrap()), cold);
                assert_eq!(warm.metrics().edge_visits, 0);
            }
            let expected;
            {
                let mut fresh = QuerySession::new(&head.facts, &head.graph, &options).unwrap();
                fresh.execute(&roots(true)).unwrap();
                expected = proof(fresh.analyze(&[NodeId(id(15))]).unwrap());
            }
            {
                let mut rebased =
                    QuerySession::with_runtime(&head.facts, &head.graph, &options, &runtime)
                        .unwrap();
                assert!(
                    rebased.reuse_metrics().loaded_contexts > 0
                        && !rebased.reuse_metrics().same_snapshot
                );
                assert_eq!(proof(rebased.analyze(&[NodeId(id(15))]).unwrap()), expected);
                assert_eq!(rebased.metrics().edge_visits, 0);
            }
            // Only this call's complete conjunction changes. The declaration
            // and the independent exact-object family remain unchanged.
            let narrow = head
                .facts
                .bound_classes
                .iter()
                .position(|s| *s == SymbolId(id(5)))
                .unwrap();
            head.facts.result_bounds[0].classes = IdRange {
                start: narrow as u32,
                len: 1,
            };
            identity(&mut head, 85);
            let mut partial =
                QuerySession::with_runtime(&head.facts, &head.graph, &options, &runtime).unwrap();
            assert!(partial.reuse_metrics().loaded_contexts > 0);
            assert!(partial.reuse_metrics().rejected_families > 0);
            partial.execute(&roots(true)).unwrap();
            let unmarked = partial.analyze(&[NodeId(id(16))]).unwrap();
            assert!(
                unmarked.contains(NodeId(id(0))),
                "removing Marker must admit NoMarker"
            );
            assert!(partial.metrics().edge_visits > 0);
        }
    }
    #[test]
    fn persisted_negative_shape_change_rejects_affected_scope() {
        let mut f = Fixture::new(&["root", "callee"]);
        f.body(0, &[], vec![call(1)]);
        f.body(1, &[], vec![]);
        f.seal();
        identity(&mut f, 1);
        let dir = tempfile::tempdir().unwrap();
        let options = SolveOptions {
            workers: 1,
            ..Default::default()
        };
        let runtime =
            SolverRuntime::with_cache_directory(&options, dir.path(), ContentHash([5; 32]))
                .unwrap();
        {
            let mut q = QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
            q.execute(&[ExecutionRoot {
                node: NodeId(0),
                receiver: SymbolId::NONE,
            }])
            .unwrap();
            q.persist_completed().unwrap();
        }
        f.facts.relations.push(RelationRecord {
            source: SymbolId(0),
            target: SymbolId(1),
            kind: RelationKind::Parent,
            file: FileId(0),
        });
        identity(&mut f, 3);
        let q = QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
        assert_eq!(q.reuse_metrics().loaded_families, 0);
        assert_eq!(q.reuse_metrics().rejected_families, 1);
    }
    #[test]
    fn persistent_family_order_cannot_change_detached_proof_ids() {
        let mut f = Fixture::new(&["root_a", "root_b", "changed_a", "changed_b"]);
        f.body(0, &[], vec![call(2)]);
        f.body(1, &[], vec![call(3)]);
        f.body(2, &[], vec![]);
        f.body(3, &[], vec![]);
        f.seal();
        identity(&mut f, 1);
        let options = SolveOptions {
            workers: 2,
            ..Default::default()
        };
        let dir = tempfile::tempdir().unwrap();
        let runtime =
            SolverRuntime::with_cache_directory(&options, dir.path(), ContentHash([5; 32]))
                .unwrap();
        let expected;
        {
            let mut q = QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
            q.execute(&[
                ExecutionRoot {
                    node: NodeId(0),
                    receiver: SymbolId::NONE,
                },
                ExecutionRoot {
                    node: NodeId(1),
                    receiver: SymbolId::NONE,
                },
            ])
            .unwrap();
            expected = q.analyze(&[NodeId(2), NodeId(3)]).unwrap();
            q.persist_completed().unwrap();
        }
        let mut q = QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
        assert_eq!(q.reuse_metrics().loaded_families, 2);
        let result = q.analyze(&[NodeId(2), NodeId(3)]).unwrap();
        assert_eq!(result.evidence.contexts, expected.evidence.contexts);
        assert_eq!(result.evidence.witnesses, expected.evidence.witnesses);
        assert_eq!(result.evidence.values, expected.evidence.values);
        assert_eq!(result.evidence.value_ids, expected.evidence.value_ids);
        assert_eq!(
            result.evidence.root_contexts,
            expected.evidence.root_contexts
        );
    }
    #[test]
    fn persisted_capture_family_preserves_finite_object_origins_and_independent_unknowns() {
        let mut f = Fixture::new(&[
            "root_a",
            "root_b",
            "root_unknown",
            "factory",
            "closure",
            "A",
            "B",
            "changed",
        ]);
        for node in [5, 6] {
            f.facts.symbols[node].kind = 13;
        }
        let mut operations = Vec::new();
        for _ in 0..3 {
            operations.extend([
                OperationRecord {
                    target: SymbolId(5),
                    dest: ValueId(1),
                    ..op(Opcode::Allocate)
                },
                OperationRecord {
                    target: SymbolId(3),
                    a: ValueId(1),
                    dest: ValueId(2),
                    ..op(Opcode::Call)
                },
                OperationRecord {
                    a: ValueId(2),
                    ..op(Opcode::InvokeCallback)
                },
            ]);
        }
        f.body(0, &[], operations);
        f.body(
            1,
            &[],
            vec![
                OperationRecord {
                    target: SymbolId(6),
                    dest: ValueId(1),
                    ..op(Opcode::Allocate)
                },
                OperationRecord {
                    target: SymbolId(3),
                    a: ValueId(1),
                    dest: ValueId(2),
                    ..op(Opcode::Call)
                },
                OperationRecord {
                    a: ValueId(2),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        f.body(
            2,
            &[],
            vec![
                OperationRecord {
                    target: SymbolId(3),
                    a: ValueId(0),
                    dest: ValueId(1),
                    ..op(Opcode::Call)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        f.body(
            3,
            &[],
            vec![
                bind(4, 1),
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::Return)
                },
            ],
        );
        f.body(4, &[], vec![call(7)]);
        for node in 5..8 {
            f.body(node, &[], vec![]);
        }
        f.seal();
        identity(&mut f, 42);
        let dir = tempfile::tempdir().unwrap();
        let cold_options = SolveOptions {
            workers: 3,
            max_set_members: 2,
            ..Default::default()
        };
        let runtime =
            SolverRuntime::with_cache_directory(&cold_options, dir.path(), ContentHash([41; 32]))
                .unwrap();
        let roots: Vec<_> = (0..3)
            .map(|node| ExecutionRoot {
                node: NodeId(node),
                receiver: SymbolId::NONE,
            })
            .collect();
        let family_keys = |q: &QuerySession<'_>| {
            let mut keys = Vec::new();
            for family in q.closure_families.keys() {
                let mut key = vec![family.site.0];
                append_value_key(&q.pool, family.receiver, &mut key);
                for value in q.frames.get(family.arguments) {
                    append_value_key(&q.pool, *value, &mut key);
                }
                keys.push(key);
            }
            keys.sort_unstable();
            keys
        };
        let expected;
        let keys;
        {
            let mut q =
                QuerySession::with_runtime(&f.facts, &f.graph, &cold_options, &runtime).unwrap();
            q.execute(&roots).unwrap();
            let exact_receivers: Vec<_> = q
                .closure_families
                .keys()
                .filter(|family| !family.receiver.is_unknown())
                .flat_map(|family| q.pool.members(family.receiver).iter())
                .collect();
            assert_eq!(
                exact_receivers.len(),
                4,
                "finite allocation origins stay separate rather than widening an erased-site family"
            );
            assert!(exact_receivers.iter().all(|atom| !atom.site.is_none()));
            assert!(
                q.closure_families
                    .keys()
                    .any(|family| family.receiver.is_unknown()),
                "an independent unknown receiver remains an unknown alternative"
            );
            keys = family_keys(&q);
            expected = q.analyze(&[NodeId(7)]).unwrap();
            q.persist_completed().unwrap();
        }
        let warm_options = SolveOptions {
            workers: 1,
            ..cold_options.clone()
        };
        let warm =
            SolverRuntime::with_cache_directory(&warm_options, dir.path(), ContentHash([41; 32]))
                .unwrap();
        let mut q = QuerySession::with_runtime(&f.facts, &f.graph, &warm_options, &warm).unwrap();
        assert!(q.reuse_metrics().loaded_contexts > 0);
        assert_eq!(
            family_keys(&q),
            keys,
            "family identity must not be reconstructed from joined payload"
        );
        let result = q.analyze(&[NodeId(7)]).unwrap();
        assert_eq!(q.metrics().edge_visits, 0);
        assert_eq!(result.evidence.atoms, expected.evidence.atoms);
        assert_eq!(result.evidence.values, expected.evidence.values);
        assert_eq!(result.evidence.value_ids, expected.evidence.value_ids);
        assert_eq!(result.evidence.captures, expected.evidence.captures);
        assert_eq!(result.evidence.contexts, expected.evidence.contexts);
        assert_eq!(result.evidence.witnesses, expected.evidence.witnesses);
        assert_eq!(
            result.evidence.root_contexts,
            expected.evidence.root_contexts
        );
    }
    #[test]
    fn compilation_graph_changes_reuse_execution_and_rebind_global_proof_edges() {
        let mut f = Fixture::new(&["root", "changed"]);
        f.body(0, &[], vec![call(1)]);
        f.body(1, &[], vec![]);
        f.seal();
        identity(&mut f, 71);
        let dir = tempfile::tempdir().unwrap();
        let options = SolveOptions {
            workers: 1,
            ..Default::default()
        };
        let runtime =
            SolverRuntime::with_cache_directory(&options, dir.path(), ContentHash([72; 32]))
                .unwrap();
        {
            let mut q = QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
            q.execute(&[ExecutionRoot {
                node: NodeId(0),
                receiver: SymbolId::NONE,
            }])
            .unwrap();
            q.persist_completed().unwrap();
        }
        f.graph.edges.insert(
            0,
            EdgeRecord {
                source: NodeId(0),
                target: NodeId(1),
                kind: EdgeKind::Compile,
                operation: OperationId::NONE,
                receiver: SymbolId::NONE,
                occurrence: OccurrenceId::NONE,
                flags: 0,
            },
        );
        f.graph.index().unwrap();
        identity(&mut f, 73);
        let mut q = QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
        assert_eq!(q.reuse_metrics().loaded_families, 1);
        let result = q
            .analyze_typed(AnalysisSeeds {
                execution: &[NodeId(1)],
                declarations: &[NodeId(1)],
            })
            .unwrap();
        assert_eq!(q.metrics().edge_visits, 0);
        assert!(result.contains(NodeId(0)));
        assert_eq!(result.witnesses[0].edge, EdgeId(1));
        assert_eq!(result.compilation.witnesses[0].edge, EdgeId(0));
    }
    #[test]
    fn native_callable_inherits_apply_and_prefers_concrete_override() {
        let mut f = Fixture::new(&[
            "root",
            "BaseFunction",
            "DerivedFunction",
            "base_apply",
            "derived_apply",
            "changed",
        ]);
        f.facts.symbols[1].kind = 13;
        f.facts.symbols[2].kind = 13;
        f.facts.relations.push(RelationRecord {
            source: SymbolId(2),
            target: SymbolId(1),
            kind: RelationKind::Parent,
            file: FileId(0),
        });
        f.body(
            0,
            &[],
            vec![
                OperationRecord {
                    target: SymbolId(2),
                    dest: ValueId(1),
                    ..op(Opcode::Allocate)
                },
                OperationRecord {
                    target: SymbolId(3),
                    a: ValueId(1),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        f.body(1, &[], vec![]);
        f.body(2, &[], vec![]);
        f.body(3, &[], vec![call(5)]);
        f.body(4, &[], vec![]);
        f.body(5, &[], vec![]);
        f.seal();
        let invocation = OperationId(
            f.facts.bodies[f.graph.nodes[0].body.index()]
                .operations
                .start
                + 1,
        );
        f.graph.edges.push(EdgeRecord {
            source: NodeId(0),
            target: NodeId(3),
            kind: EdgeKind::Callback,
            operation: invocation,
            occurrence: OccurrenceId::NONE,
            receiver: SymbolId(1),
            flags: 0,
        });
        f.graph.index().unwrap();
        let inherited = f.run(&[0], &[5], 2);
        assert!(inherited.contains(NodeId(0)));
        assert!(inherited.guarded_roots.is_empty());
        f.graph.edges.push(EdgeRecord {
            source: NodeId(0),
            target: NodeId(4),
            kind: EdgeKind::Callback,
            operation: invocation,
            occurrence: OccurrenceId::NONE,
            receiver: SymbolId(2),
            flags: 0,
        });
        f.graph.index().unwrap();
        let overridden = f.run(&[0], &[5], 2);
        assert!(!overridden.contains(NodeId(0)));
        assert!(overridden.guarded_roots.is_empty());
    }
    #[test]
    fn macro_result_type_metadata_stays_unknown_until_verified_rewrite() {
        for tagged in [true, false] {
            let mut f = Fixture::new(&["root", "Position"]);
            f.body(
                0,
                &[],
                vec![
                    OperationRecord {
                        dest: ValueId(1),
                        target: if tagged { SymbolId(1) } else { SymbolId::NONE },
                        flags: if tagged { OP_MACRO_RESULT_TYPE } else { 0 },
                        ..op(Opcode::Constant)
                    },
                    OperationRecord {
                        a: ValueId(1),
                        ..op(Opcode::InvokeCallback)
                    },
                    OperationRecord {
                        a: ValueId(1),
                        ..op(Opcode::Return)
                    },
                ],
            );
            f.seal();
            let mut q = QuerySession::new(
                &f.facts,
                &f.graph,
                &SolveOptions {
                    workers: 1,
                    ..Default::default()
                },
            )
            .unwrap();
            q.execute(&[ExecutionRoot {
                node: NodeId(0),
                receiver: SymbolId::NONE,
            }])
            .unwrap();
            assert_eq!(
                q.contexts.len(),
                1,
                "type metadata must not allocate or invoke Position"
            );
            assert_eq!(
                q.contexts[0].value,
                if tagged { Value::TOP } else { Value::EMPTY }
            );
            assert!(q.pool.members(q.contexts[0].value).is_empty());
            let result = q.analyze(&[]).unwrap();
            assert_eq!(
                result.guarded_roots,
                if tagged { vec![NodeId(0)] } else { vec![] }
            );
            assert!(!result.unscoped_uncertainty);
        }
    }
    #[test]
    fn constructor_scalar_empty_fields_are_present_and_not_missing() {
        for store_line in [true, false] {
            let mut f =
                Fixture::new(&["root", "Position_ctor", "Position", "file", "path", "line"]);
            f.facts.symbols[1].kind = 21;
            f.facts.symbols[1].owner = SymbolId(2);
            f.facts.symbols[2].kind = 13;
            let actuals = f.args(&[1, 1, 1]);
            let mut root = vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..op(Opcode::Constant)
                },
                OperationRecord {
                    target: SymbolId(1),
                    dest: ValueId(2),
                    arguments: actuals,
                    ..op(Opcode::Allocate)
                },
            ];
            for (field, dest) in [(3, 3), (4, 4), (5, 5)] {
                root.push(OperationRecord {
                    target: SymbolId(field),
                    a: ValueId(2),
                    dest: ValueId(dest),
                    ..op(Opcode::LoadField)
                });
            }
            root.push(OperationRecord {
                a: ValueId(5),
                ..op(Opcode::Return)
            });
            f.body(0, &[], root);
            let mut constructor = Vec::new();
            for value in 1..=3 {
                constructor.push(OperationRecord {
                    dest: ValueId(value),
                    ..op(Opcode::Parameter)
                });
            }
            for (field, actual) in [(3, 1), (4, 2), (5, 3)] {
                if field != 5 || store_line {
                    constructor.push(OperationRecord {
                        target: SymbolId(field),
                        a: ValueId(0),
                        b: ValueId(actual),
                        ..op(Opcode::StoreField)
                    });
                }
            }
            f.body(1, &[1, 2, 3], constructor);
            f.seal();
            for workers in [1, 4] {
                let mut q = QuerySession::new(
                    &f.facts,
                    &f.graph,
                    &SolveOptions {
                        workers,
                        ..Default::default()
                    },
                )
                .unwrap();
                q.execute(&[ExecutionRoot {
                    node: NodeId(0),
                    receiver: SymbolId::NONE,
                }])
                .unwrap();
                for field in 3..=5 {
                    let slot = Slot {
                        kind: if field == 5 && !store_line {
                            SlotKind::FieldMissing
                        } else {
                            SlotKind::FieldAll
                        },
                        owner: 1,
                        member: field,
                    };
                    let found = q
                        .slots
                        .get(&slot)
                        .expect("concrete field was stored or sealed");
                    assert_eq!(
                        found.value,
                        if field == 5 && !store_line {
                            Value {
                                set: SetId(0),
                                unknown: UNKNOWN_FIELD,
                            }
                        } else {
                            Value::EMPTY
                        }
                    );
                    assert_eq!(found.version, 1);
                    assert!(
                        q.dependencies
                            .active_reads()
                            .any(|(consumer, read)| consumer == ContextId(0)
                                && read.slot == slot
                                && read.present)
                    );
                }
                let result = q.analyze(&[NodeId(1)]).unwrap();
                assert!(
                    result.contains(NodeId(0)),
                    "the constructor remains an execution dependency"
                );
                assert_eq!(
                    result.guarded_roots,
                    if store_line { vec![] } else { vec![NodeId(0)] }
                );
                assert_eq!(
                    result.completion,
                    if store_line {
                        Completion::Complete
                    } else {
                        Completion::Conservative
                    }
                );
            }
        }
    }
    #[test]
    fn static_field_negative_read_resumes_after_verified_initializer_store() {
        let mut f = Fixture::new(&["root", "initializer", "closure", "changed", "static_field"]);
        f.body(
            0,
            &[],
            vec![
                call(1),
                OperationRecord {
                    target: SymbolId(4),
                    dest: ValueId(1),
                    flags: OP_STATIC_FIELD,
                    ..op(Opcode::LoadField)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        f.body(
            1,
            &[],
            vec![
                bind(2, 1),
                OperationRecord {
                    target: SymbolId(4),
                    b: ValueId(1),
                    flags: OP_STATIC_FIELD,
                    ..op(Opcode::StoreField)
                },
            ],
        );
        f.body(2, &[], vec![call(3)]);
        f.body(3, &[], vec![]);
        f.body(4, &[], vec![]);
        f.seal();
        let result = f.run(&[0], &[3], 3);
        assert!(result.contains(NodeId(0)));
        assert!(result.guarded_roots.is_empty());
        assert_eq!(result.completion, Completion::Complete);
        identity(&mut f, 1);
        let options = SolveOptions {
            workers: 2,
            ..Default::default()
        };
        let directory = tempfile::tempdir().unwrap();
        let runtime =
            SolverRuntime::with_cache_directory(&options, directory.path(), ContentHash([5; 32]))
                .unwrap();
        {
            let mut q = QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
            q.execute(&[ExecutionRoot {
                node: NodeId(0),
                receiver: SymbolId::NONE,
            }])
            .unwrap();
            assert!(q.slots.contains_key(&Slot {
                kind: SlotKind::StaticField,
                owner: 4,
                member: 0
            }));
            assert!(!q.slots.contains_key(&Slot {
                kind: SlotKind::Field,
                owner: u32::MAX,
                member: 4
            }));
            q.persist_completed().unwrap();
        }
        let mut restored =
            QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
        assert!(restored.reuse_metrics().loaded_contexts > 0);
        let loaded = restored.analyze(&[NodeId(3)]).unwrap();
        assert_eq!(loaded.affected, result.affected);
        assert_eq!(loaded.guarded_roots, result.guarded_roots);
        assert_eq!(loaded.completion, result.completion);
    }
    #[test]
    fn static_field_without_initializer_or_zero_proof_is_scoped_unknown() {
        let mut f = Fixture::new(&["reader", "unrelated", "static_field"]);
        f.body(
            0,
            &[],
            vec![
                OperationRecord {
                    target: SymbolId(2),
                    dest: ValueId(1),
                    flags: OP_STATIC_FIELD,
                    ..op(Opcode::LoadField)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        f.body(1, &[], vec![]);
        f.body(2, &[], vec![]);
        f.seal();
        let result = f.run(&[0, 1], &[2], 2);
        assert_eq!(result.guarded_roots, vec![NodeId(0)]);
        assert!(!result.unscoped_uncertainty);
        assert_eq!(result.completion, Completion::Conservative);
    }
    #[test]
    fn static_initializer_context_is_global_but_trait_initializer_keeps_receiver() {
        let mut f = Fixture::new(&["root_a", "root_b", "initializer"]);
        f.body(0, &[], vec![call(2)]);
        f.body(1, &[], vec![call(2)]);
        f.body(2, &[], vec![]);
        f.facts.bodies[2].flags = BODY_STATIC_INITIALIZER;
        f.seal();
        let options = SolveOptions {
            workers: 2,
            ..Default::default()
        };
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
        let mut q = QuerySession::new(&f.facts, &f.graph, &options).unwrap();
        q.execute(&roots).unwrap();
        assert_eq!(q.context_count(), 3);
        assert!(
            q.contexts
                .iter()
                .find(|c| c.key.node == NodeId(2))
                .unwrap()
                .key
                .receiver
                .is_bottom()
        );
        drop(q);
        f.facts.bodies[2].flags = BODY_INITIALIZER;
        let mut q = QuerySession::new(&f.facts, &f.graph, &options).unwrap();
        q.execute(&roots).unwrap();
        assert_eq!(q.context_count(), 4);
    }
    #[test]
    fn verified_module_metadata_never_adds_a_this_receiver_to_static_initializers() {
        let mut f = Fixture::new(&["root", "Global."]);
        f.facts.symbols[1].kind = 10;
        f.body(0, &[], vec![call(1)]);
        f.body(
            1,
            &[],
            vec![OperationRecord {
                a: ValueId(0),
                ..op(Opcode::Return)
            }],
        );
        f.facts.bodies[1].flags = BODY_STATIC_INITIALIZER;
        f.seal();
        let mut q = QuerySession::new(
            &f.facts,
            &f.graph,
            &SolveOptions {
                workers: 1,
                ..Default::default()
            },
        )
        .unwrap();
        q.execute(&[ExecutionRoot {
            node: NodeId(0),
            receiver: SymbolId(0),
        }])
        .unwrap();
        let init = q.contexts.iter().find(|c| c.key.node == NodeId(1)).unwrap();
        assert!(init.key.receiver.is_bottom());
        assert!(init.value.is_bottom());
    }
    #[test]
    fn inherited_field_cells_do_not_alias_distinct_exact_root_receivers() {
        let mut f = Fixture::new(&[
            "root_a",
            "root_b",
            "closure_changed",
            "closure_other",
            "changed",
            "other",
            "field",
            "base",
        ]);
        for root in [0, 1] {
            f.facts.symbols[root].kind = 13;
            f.facts.relations.push(RelationRecord {
                source: SymbolId(root as u32),
                target: SymbolId(7),
                kind: RelationKind::Parent,
                file: FileId(0),
            });
            let closure = if root == 0 { 2 } else { 3 };
            f.body(
                root as u32,
                &[],
                vec![
                    bind(closure, 1),
                    OperationRecord {
                        target: SymbolId(6),
                        a: ValueId(0),
                        b: ValueId(1),
                        ..op(Opcode::StoreField)
                    },
                    OperationRecord {
                        target: SymbolId(6),
                        a: ValueId(0),
                        dest: ValueId(2),
                        ..op(Opcode::LoadField)
                    },
                    OperationRecord {
                        a: ValueId(2),
                        ..op(Opcode::InvokeCallback)
                    },
                ],
            );
        }
        f.body(2, &[], vec![call(4)]);
        f.body(3, &[], vec![call(5)]);
        for node in 4..8 {
            f.body(node, &[], vec![]);
        }
        f.seal();
        identity(&mut f, 1);
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
            workers: 3,
            ..Default::default()
        };
        let directory = tempfile::tempdir().unwrap();
        let runtime =
            SolverRuntime::with_cache_directory(&options, directory.path(), ContentHash([5; 32]))
                .unwrap();
        let result;
        {
            let mut q = QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
            q.execute(&roots).unwrap();
            result = q.analyze(&[NodeId(4)]).unwrap();
            assert!(result.contains(NodeId(0)));
            assert!(!result.contains(NodeId(1)));
            assert!(result.guarded_roots.is_empty());
            assert!(!q.slots.contains_key(&Slot {
                kind: SlotKind::Field,
                owner: u32::MAX,
                member: 6
            }));
            q.persist_completed().unwrap();
        }
        let mut loaded =
            QuerySession::with_runtime(&f.facts, &f.graph, &options, &runtime).unwrap();
        assert!(loaded.reuse_metrics().loaded_contexts > 0);
        let restored = loaded.analyze(&[NodeId(4)]).unwrap();
        assert_eq!(restored.affected, result.affected);
        assert_eq!(restored.evidence.contexts, result.evidence.contexts);
        assert_eq!(restored.evidence.captures, result.evidence.captures);
    }
    #[test]
    fn matched_native_callable_does_not_hide_unresolved_object_alternative() {
        let mut f = Fixture::new(&[
            "root",
            "KnownFunction",
            "MissingFunction",
            "known_apply",
            "changed",
        ]);
        f.facts.symbols[1].kind = 13;
        f.facts.symbols[2].kind = 13;
        f.body(
            0,
            &[],
            vec![
                OperationRecord {
                    target: SymbolId(1),
                    dest: ValueId(1),
                    ..op(Opcode::Allocate)
                },
                OperationRecord {
                    target: SymbolId(2),
                    dest: ValueId(2),
                    ..op(Opcode::Allocate)
                },
                OperationRecord {
                    a: ValueId(1),
                    b: ValueId(2),
                    dest: ValueId(3),
                    ..op(Opcode::Join)
                },
                OperationRecord {
                    target: SymbolId(3),
                    a: ValueId(3),
                    ..op(Opcode::InvokeCallback)
                },
            ],
        );
        for node in 1..5 {
            f.body(node, &[], vec![]);
        }
        f.seal();
        f.graph.edges.push(EdgeRecord {
            source: NodeId(0),
            target: NodeId(3),
            kind: EdgeKind::Callback,
            operation: OperationId(3),
            occurrence: OccurrenceId::NONE,
            receiver: SymbolId(1),
            flags: 0,
        });
        f.graph.index().unwrap();
        let result = f.run(&[0], &[4], 2);
        assert_eq!(result.guarded_roots, vec![NodeId(0)]);
        assert_eq!(result.completion, Completion::Conservative);
        assert!(!result.unscoped_uncertainty);
    }
}
