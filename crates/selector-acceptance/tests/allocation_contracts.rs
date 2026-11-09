//! A separate, sequential executable: the test harness cannot allocate in windows.
//! Counters never allocate, print, lock, or inspect a backtrace inside the allocator.
use selector_domain::{Atom, Slot, Value, ValuePool};
use selector_facts::FactBuilder;
use selector_graph::{EdgeRecord, NodeRecord, ProgramGraph};
use selector_transfer::{SummaryRead, World};
use selector_types::*;
use std::alloc::{GlobalAlloc, Layout, System};
use std::hint::black_box;
use std::sync::atomic::{AtomicBool, AtomicIsize, AtomicUsize, Ordering::Relaxed};

struct CountingAllocator;
static ACTIVE: AtomicBool = AtomicBool::new(false);
static ALLOCATIONS: AtomicUsize = AtomicUsize::new(0);
static REALLOCATIONS: AtomicUsize = AtomicUsize::new(0);
static ALLOCATED_BYTES: AtomicUsize = AtomicUsize::new(0);
static LIVE_BYTES: AtomicIsize = AtomicIsize::new(0);

unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // SAFETY: Pass the caller's valid layout directly through to System.
        let pointer = unsafe { System.alloc(layout) };
        if !pointer.is_null() {
            record_allocation(layout.size());
        }
        pointer
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        // SAFETY: Pass the caller's valid layout directly through to System.
        let pointer = unsafe { System.alloc_zeroed(layout) };
        if !pointer.is_null() {
            record_allocation(layout.size());
        }
        pointer
    }
    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        LIVE_BYTES.fetch_sub(layout.size() as isize, Relaxed);
        // SAFETY: The pointer and original layout are supplied by the allocator caller.
        unsafe { System.dealloc(pointer, layout) };
    }
    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // SAFETY: Forward the caller's allocated pointer, layout and valid new size.
        let result = unsafe { System.realloc(pointer, layout, new_size) };
        if !result.is_null() {
            LIVE_BYTES.fetch_add(new_size as isize - layout.size() as isize, Relaxed);
            if ACTIVE.load(Relaxed) {
                REALLOCATIONS.fetch_add(1, Relaxed);
                ALLOCATED_BYTES.fetch_add(new_size, Relaxed);
            }
        }
        result
    }
}
fn record_allocation(bytes: usize) {
    LIVE_BYTES.fetch_add(bytes as isize, Relaxed);
    if ACTIVE.load(Relaxed) {
        ALLOCATIONS.fetch_add(1, Relaxed);
        ALLOCATED_BYTES.fetch_add(bytes, Relaxed);
    }
}
#[global_allocator]
static ALLOCATOR: CountingAllocator = CountingAllocator;

#[derive(Debug)]
struct Counts {
    allocations: usize,
    reallocations: usize,
    allocated_bytes: usize,
}
struct Window;
impl Window {
    fn begin() -> Self {
        assert!(!ACTIVE.load(Relaxed));
        ALLOCATIONS.store(0, Relaxed);
        REALLOCATIONS.store(0, Relaxed);
        ALLOCATED_BYTES.store(0, Relaxed);
        ACTIVE.store(true, Relaxed);
        Self
    }
    fn finish(self) -> Counts {
        ACTIVE.store(false, Relaxed);
        Counts {
            allocations: ALLOCATIONS.load(Relaxed),
            reallocations: REALLOCATIONS.load(Relaxed),
            allocated_bytes: ALLOCATED_BYTES.load(Relaxed),
        }
    }
}
impl Drop for Window {
    fn drop(&mut self) {
        ACTIVE.store(false, Relaxed);
    }
}
fn expect_zero(name: &str, counts: Counts) {
    assert_eq!(counts.allocations, 0, "{name}: {counts:?}");
    assert_eq!(counts.reallocations, 0, "{name}: {counts:?}");
    assert_eq!(counts.allocated_bytes, 0, "{name}: {counts:?}");
    println!(
        "{{\"operation\":\"{name}\",\"allocations\":0,\"reallocations\":0,\"allocated_bytes\":0}}"
    );
}

fn counter_calibration() {
    // Opaque input/output keeps this real allocation observable to the optimizer.
    // The harness does not infer behavior from whether allocation failure aborts.
    let window = Window::begin();
    let mut bytes = Vec::<u8>::with_capacity(black_box(257));
    bytes.extend_from_slice(black_box(&[0xabu8; 257]));
    black_box(&mut bytes);
    bytes.reserve(black_box(4096));
    black_box(&mut bytes);
    drop(black_box(bytes));
    let counts = window.finish();
    assert!(
        counts.allocations >= 1 && counts.allocated_bytes >= 257,
        "allocator failed calibration: {counts:?}"
    );
    assert!(
        counts.reallocations >= 1,
        "reallocation counter failed calibration: {counts:?}"
    );
}

fn fact_hits() {
    let mut builder = FactBuilder::new();
    let symbol_name = black_box("com/example/Owner#method().");
    let expected = builder.ensure_symbol(symbol_name, FileId::NONE).unwrap();
    let text = builder.intern(symbol_name).unwrap();
    let before = builder.facts.owned_bytes();
    let window = Window::begin();
    for _ in 0..black_box(100_000) {
        black_box(builder.intern(black_box(symbol_name)).unwrap());
        black_box(
            builder
                .ensure_symbol(black_box(symbol_name), FileId::NONE)
                .unwrap(),
        );
        black_box(builder.facts.text(black_box(text)));
        black_box(builder.facts.symbol_name(black_box(expected)));
    }
    let counts = window.finish();
    assert_eq!(before, builder.facts.owned_bytes());
    assert_eq!(builder.facts.symbols.len(), 1);
    expect_zero("known_fact_and_string_hits", counts);
}

fn fact_lookup_hits_and_misses() {
    let mut builder = FactBuilder::new();
    let name = "com/example/Owner#method().";
    let expected = builder.ensure_symbol(name, FileId::NONE).unwrap();
    let pooled_only = "com/example/Other#method().";
    builder.intern(pooled_only).unwrap();
    let absent = "com/example/Absent#method().";
    assert_eq!(builder.lookup_symbol(name, FileId::NONE), Some(expected));
    assert_eq!(builder.lookup_symbol(pooled_only, FileId::NONE), None);
    assert_eq!(builder.lookup_symbol(absent, FileId::NONE), None);
    let before = builder.facts.owned_bytes();
    let mut hits = 0;
    let mut misses = 0;
    let window = Window::begin();
    for _ in 0..black_box(100_000) {
        hits += usize::from(
            black_box(builder.lookup_symbol(black_box(name), FileId::NONE)) == Some(expected),
        );
        for missing in black_box([pooled_only, absent]) {
            misses += usize::from(
                black_box(builder.lookup_symbol(black_box(missing), FileId::NONE)).is_none(),
            );
        }
    }
    let counts = window.finish();
    assert_eq!(hits, 100_000);
    assert_eq!(misses, 200_000);
    assert_eq!(builder.facts.owned_bytes(), before);
    assert_eq!(builder.facts.symbols.len(), 1);
    assert_eq!(builder.facts.strings.len(), 2);
    expect_zero("read_only_symbol_lookup_hits_and_misses", counts);
}

fn result_bound_hits_and_misses() {
    let mut builder = FactBuilder::new();
    let result = builder
        .ensure_symbol("com/example/Factory#result().", FileId::NONE)
        .unwrap();
    let class = builder
        .ensure_symbol("com/example/Result#", FileId::NONE)
        .unwrap();
    builder.facts.bound_classes.push(class);
    builder
        .facts
        .result_bounds
        .push(selector_facts::ResultBoundRecord {
            symbol: result,
            operation: OperationId::NONE,
            classes: IdRange { start: 0, len: 1 },
        });
    let facts = builder.finish().unwrap();
    let before = facts.owned_bytes();
    let mut hits = 0;
    let mut misses = 0;
    let window = Window::begin();
    for _ in 0..black_box(100_000) {
        hits += usize::from(
            black_box(facts.result_bound(black_box(result), OperationId::NONE))
                == Some(&[class][..]),
        );
        misses +=
            usize::from(black_box(facts.result_bound(black_box(result), OperationId(0))).is_none());
        misses +=
            usize::from(black_box(facts.result_bound(SymbolId::NONE, OperationId::NONE)).is_none());
    }
    let counts = window.finish();
    assert_eq!((hits, misses), (100_000, 200_000));
    assert_eq!(facts.owned_bytes(), before);
    expect_zero("typed_result_bound_lookup_hits_and_misses", counts);
}

fn graph_hits() {
    let n = 4096;
    let mut graph = ProgramGraph::default();
    graph.nodes = (0..n)
        .map(|i| NodeRecord {
            symbol: SymbolId(i),
            file: FileId::NONE,
            body: BodyId::NONE,
            flags: 0,
        })
        .collect();
    graph.symbol_nodes = (0..n).map(NodeId).collect();
    graph.edges.reserve(n as usize * 4);
    for source in 0..n {
        for offset in 1..=4 {
            graph.edges.push(EdgeRecord {
                source: NodeId(source),
                target: NodeId((source + offset) % n),
                kind: EdgeKind::Call,
                occurrence: OccurrenceId::NONE,
                operation: OperationId::NONE,
                receiver: SymbolId::NONE,
                flags: 0,
            });
        }
    }
    graph.index().unwrap();
    graph.validate().unwrap();
    let window = Window::begin();
    let mut checksum = 0u64;
    for _ in 0..black_box(16) {
        for source in 0..black_box(n) {
            let node = black_box(graph.node_for_symbol(black_box(SymbolId(source))).unwrap());
            for (id, edge) in graph.successors(node) {
                checksum = checksum.wrapping_add(black_box((id.0 + edge.target.0) as u64));
            }
            for (id, edge) in graph.predecessors(node) {
                checksum = checksum.wrapping_add(black_box((id.0 + edge.source.0) as u64));
            }
        }
    }
    black_box(checksum);
    expect_zero("borrowed_graph_forward_reverse_lookup", window.finish());
}

fn dependency_hits() {
    use selector_domain::{Dependencies, Read, Slot, SlotKind};
    let mut dependencies = Dependencies::default();
    let slot = Slot {
        kind: SlotKind::StaticField,
        owner: 7,
        member: 0,
    };
    let read = Read {
        slot,
        version: 0,
        present: false,
    };
    for query in 0..4096 {
        dependencies.subscribe(ContextId(query), read).unwrap();
    }
    let bytes = dependencies.owned_bytes();
    let window = Window::begin();
    for version in 1..black_box(17) {
        for query in 0..black_box(4096) {
            let current = black_box(Read {
                version,
                present: version % 2 == 0,
                ..read
            });
            dependencies
                .subscribe(black_box(ContextId(query)), current)
                .unwrap();
            dependencies
                .replace(black_box(ContextId(query)), black_box(&[current]))
                .unwrap();
        }
    }
    let counts = window.finish();
    assert_eq!(dependencies.owned_bytes(), bytes);
    let mut invalid = Vec::new();
    dependencies.publish(&[slot], 0, 1, &mut invalid);
    invalid.sort_unstable();
    assert_eq!(invalid, (0..4096).map(ContextId).collect::<Vec<_>>());
    expect_zero(
        "indexed_dependency_subscription_and_replacement_hits",
        counts,
    );
}

fn artifact_hits() {
    use selector_artifacts::{ArtifactKind, Section};
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("facts.bin");
    let payload = [0xabu8; 4096];
    selector_artifacts::write(
        &path,
        ArtifactKind::Facts,
        &[Section {
            id: 1,
            count: 512,
            bytes: &payload,
        }],
    )
    .unwrap();
    let artifact = selector_artifacts::open(&path, ArtifactKind::Facts).unwrap();
    let window = Window::begin();
    for _ in 0..black_box(100_000) {
        black_box(artifact.section(black_box(1)).unwrap());
        black_box(artifact.count(black_box(1)).unwrap());
        black_box(artifact.identity());
    }
    expect_zero("borrowed_artifact_section_lookup", window.finish());
}

fn canonical_domain_hits() {
    use selector_domain::{Atom, AtomKind, FramePool, ValuePool};
    let mut values = ValuePool::new(64);
    let a = Atom {
        kind: AtomKind::Object,
        site: OperationId(1),
        symbol: SymbolId(1),
        binding: 0,
    };
    let b = Atom {
        kind: AtomKind::Callback,
        site: OperationId(2),
        symbol: SymbolId(2),
        binding: 0,
    };
    let left = values.singleton(a).unwrap();
    let right = values.singleton(b).unwrap();
    let both = values.join(left, right).unwrap();
    let mut frames = FramePool::default();
    let arguments = [both, left];
    let frame = frames.intern(&arguments).unwrap();
    let window = Window::begin();
    for _ in 0..black_box(100_000) {
        black_box(values.singleton(black_box(a)).unwrap());
        black_box(values.join(black_box(left), black_box(right)).unwrap());
        black_box(values.lookup(black_box(&[a, b]), 0));
        black_box(frames.intern(black_box(&arguments)).unwrap());
        black_box(frames.lookup(black_box(&arguments)));
        black_box(frames.get(black_box(frame)));
    }
    expect_zero("canonical_value_and_argument_hits", window.finish());
}

fn callback_shape_hits() {
    use selector_domain::{Atom, AtomKind, Value, ValuePool};
    use selector_solve::context_policy::CallbackShapes;
    let mut values = ValuePool::new(64);
    let bindings: Vec<_> = (1..=32)
        .map(|binding| {
            values
                .singleton(Atom {
                    kind: AtomKind::Callback,
                    site: OperationId(7),
                    symbol: SymbolId(11),
                    binding,
                })
                .unwrap()
        })
        .collect();
    let mut joined = Value::EMPTY;
    for &value in &bindings {
        joined = values.join(joined, value).unwrap();
    }
    let mut shapes = CallbackShapes::new();
    let known = shapes.intern(&values, &[bindings[0]]).unwrap();
    for &value in &bindings {
        assert_eq!(shapes.intern(&values, &[value]).unwrap(), known);
    }
    assert_eq!(
        shapes.intern(&values, &[joined]).unwrap(),
        known,
        "capture bindings do not alter lexical callback code"
    );
    let unknown = shapes.intern(&values, &[Value::TOP]).unwrap();
    assert_ne!(known, unknown);
    let owned = shapes.owned_bytes();
    let value_bytes = values.owned_bytes();
    let window = Window::begin();
    for i in 0..black_box(100_000) {
        let argument = black_box(bindings[i % bindings.len()]);
        black_box(
            shapes
                .lookup(black_box(&values), black_box(&[argument]))
                .unwrap(),
        );
        black_box(
            shapes
                .intern(black_box(&values), black_box(&[argument]))
                .unwrap(),
        );
        black_box(
            shapes
                .intern(black_box(&values), black_box(&[joined]))
                .unwrap(),
        );
        black_box(
            shapes
                .lookup(black_box(&values), black_box(&[Value::TOP]))
                .unwrap(),
        );
        black_box(shapes.get(black_box(known)));
    }
    expect_zero(
        "callback_code_shape_hits_with_varied_capture_bindings",
        window.finish(),
    );
    assert_eq!(shapes.owned_bytes(), owned);
    assert_eq!(values.owned_bytes(), value_bytes);
}

fn query_fixture() -> (selector_facts::FactSnapshot, ProgramGraph) {
    use selector_facts::{BodyRecord, FileRecord, OperationRecord};
    let mut builder = FactBuilder::new();
    let path = builder.intern("example.scala").unwrap();
    let source = builder
        .intern("def caller = callee()\ndef callee = ()\n")
        .unwrap();
    builder.facts.files.push(FileRecord {
        path,
        source,
        revision: StrId::NONE,
        context: StrId::NONE,
        source_hash: ContentHash::from_hex(
            "e64c561a8de147b8aaf6fac4691ebe3f7737ab0e4bc793f6ee499f9ab03faacc",
        )
        .unwrap(),
        flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
    });
    let caller = builder
        .ensure_symbol("example/Owner#caller().", FileId(0))
        .unwrap();
    let callee = builder
        .ensure_symbol("example/Owner#callee().", FileId(0))
        .unwrap();
    for (i, symbol) in [caller, callee].into_iter().enumerate() {
        let span = if i == 0 {
            Span { start: 13, end: 21 }
        } else {
            Span { start: 35, end: 37 }
        };
        let name_span = if i == 0 {
            Span { start: 4, end: 10 }
        } else {
            Span { start: 26, end: 32 }
        };
        builder.facts.symbols[symbol.index()].file = FileId(0);
        builder.facts.symbols[symbol.index()].flags = SYMBOL_DEFINED;
        builder.facts.symbols[symbol.index()].span = name_span;
        builder.facts.bodies.push(BodyRecord {
            symbol,
            file: FileId(0),
            span,
            name_span,
            operations: IdRange {
                start: i as u32,
                len: 1,
            },
            parameters: IdRange::default(),
            body_hash: ContentHash::from_hex(if i == 0 {
                "b6873fc60625b3d38b7d2f1cb6318a8369fdda68a216a21eaf594db8c71f9025"
            } else {
                "2e38e77b22c314a449e91fafed92a43826ac6aa403ae6a8acb6cf58239fbaf5d"
            })
            .unwrap(),
            flags: 0,
        });
    }
    builder.facts.operations = vec![
        OperationRecord {
            body: BodyId(0),
            opcode: Opcode::Call,
            target: callee,
            dest: ValueId(1),
            a: ValueId::NONE,
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span { start: 13, end: 21 },
            flags: 0,
        },
        OperationRecord {
            body: BodyId(1),
            opcode: Opcode::Constant,
            target: SymbolId::NONE,
            dest: ValueId(1),
            a: ValueId::NONE,
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span { start: 35, end: 37 },
            flags: 0,
        },
    ];
    let facts = builder.finish().unwrap();
    let mut graph = ProgramGraph {
        facts_identity: facts.identity,
        ..ProgramGraph::default()
    };
    graph.nodes = [caller, callee]
        .into_iter()
        .enumerate()
        .map(|(i, symbol)| NodeRecord {
            symbol,
            file: FileId(0),
            body: BodyId(i as u32),
            flags: 0,
        })
        .collect();
    graph.symbol_nodes = vec![NodeId(0), NodeId(1)];
    graph.edges.push(EdgeRecord {
        source: NodeId(0),
        target: NodeId(1),
        kind: EdgeKind::Call,
        occurrence: OccurrenceId::NONE,
        operation: OperationId(0),
        receiver: SymbolId::NONE,
        flags: 0,
    });
    graph.index().unwrap();
    (facts, graph)
}

// On macOS, Rayon workers lazily allocate a 48-byte pthread condition variable
// on their first idle wait. Native pointer/backtrace diagnostics identified that
// runtime-owned cache independently from query buffers. Let every idle worker
// reach its parking path before taking process-wide allocation baselines.
fn settle_idle_workers() {
    let mut previous = LIVE_BYTES.load(Relaxed);
    let mut stable = 0;
    for _ in 0..32 {
        std::thread::sleep(std::time::Duration::from_millis(5));
        let current = LIVE_BYTES.load(Relaxed);
        stable = if current == previous { stable + 1 } else { 0 };
        previous = current;
        if stable == 4 {
            return;
        }
    }
    panic!("idle runtime allocations did not reach a bounded warm baseline");
}

fn query_lifecycle() -> selector_solve::SolverRuntime {
    use selector_solve::{ExecutionRoot, QuerySession, SolveOptions, SolverRuntime};
    let (facts, graph) = query_fixture();
    let options = SolveOptions {
        workers: 2,
        ..SolveOptions::default()
    };
    let roots = [ExecutionRoot {
        node: NodeId(0),
        receiver: SymbolId(0),
    }];
    let runtime = SolverRuntime::new(&options).unwrap();
    settle_idle_workers();
    {
        let mut warm = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
        warm.execute(&roots).unwrap();
        drop(warm.analyze(&[NodeId(1)]).unwrap());
    }
    let idle_baseline = LIVE_BYTES.load(Relaxed);
    let idle_capacity = runtime.retained_bytes();
    let mut query = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
    query.execute(&roots).unwrap();
    let contexts = query.context_count();
    let owned = query.owned_bytes();
    let window = Window::begin();
    for _ in 0..black_box(100_000) {
        black_box(query.execute(black_box(&roots)).unwrap());
    }
    expect_zero("completed_query_context_hits", window.finish());
    assert_eq!(query.context_count(), contexts);
    assert_eq!(query.owned_bytes(), owned);
    drop(query.analyze(&[NodeId(1)]).unwrap());
    let baseline = LIVE_BYTES.load(Relaxed);
    for _ in 0..100 {
        let result = query.analyze(black_box(&[NodeId(1)])).unwrap();
        assert_eq!(result.completion, Completion::Complete);
        assert_eq!(result.affected, [NodeId(0), NodeId(1)]);
        drop(black_box(result));
        assert_eq!(
            LIVE_BYTES.load(Relaxed),
            baseline,
            "analysis result retains bytes after drop"
        );
    }
    println!(
        "{{\"operation\":\"query_result_teardown\",\"repetitions\":100,\"retained_bytes\":0,\"query_owned_bytes\":{owned}}}"
    );
    drop(query);
    assert_eq!(
        LIVE_BYTES.load(Relaxed),
        idle_baseline,
        "query session retains allocations beyond the bounded runtime scratch bank"
    );
    for _ in 0..32 {
        let mut query = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
        query.execute(&roots).unwrap();
        drop(query.analyze(&[NodeId(1)]).unwrap());
        drop(query);
        assert_eq!(
            LIVE_BYTES.load(Relaxed),
            idle_baseline,
            "repeated query session retains owned state"
        );
        assert_eq!(runtime.retained_bytes(), idle_capacity);
    }
    assert!(runtime.retained_bytes() <= options.scratch_bytes_per_worker * runtime.workers());
    println!(
        "{{\"operation\":\"query_session_teardown\",\"repetitions\":32,\"retained_query_bytes\":0,\"bounded_runtime_retained_bytes\":{idle_capacity}}}"
    );
    runtime
}

fn stopped_query_teardown() -> selector_solve::SolverRuntime {
    use selector_solve::{ExecutionRoot, QuerySession, SolveOptions, SolverRuntime};
    let (facts, graph) = query_fixture();
    let options = SolveOptions {
        workers: 2,
        max_contexts: 1,
        scratch_bytes_per_worker: 1,
        ..SolveOptions::default()
    };
    let runtime = SolverRuntime::new(&options).unwrap();
    settle_idle_workers();
    let cycle = || {
        let mut query = QuerySession::with_runtime(&facts, &graph, &options, &runtime).unwrap();
        assert!(
            query
                .execute(&[ExecutionRoot {
                    node: NodeId::NONE,
                    receiver: SymbolId::NONE
                }])
                .is_err()
        );
        assert!(query.analyze(&[NodeId::NONE]).is_err());
        query
            .execute(&[ExecutionRoot {
                node: NodeId(0),
                receiver: SymbolId(0),
            }])
            .unwrap();
        let result = query.analyze(&[NodeId(1)]).unwrap();
        assert_eq!(result.completion, Completion::ResourceLimited);
        drop(result);
        drop(query);
        assert_eq!(
            runtime.retained_bytes(),
            0,
            "oversized scratch must not enter the idle bank"
        );
    };
    // Rayon can grow finite internal scheduling caches on its first real tasks.
    // Require them to stabilize; an unbounded owner leak cannot pass warmup.
    let mut previous = LIVE_BYTES.load(Relaxed);
    let mut stable = 0;
    for _ in 0..32 {
        cycle();
        let current = LIVE_BYTES.load(Relaxed);
        stable = if current == previous { stable + 1 } else { 0 };
        previous = current;
        if stable == 4 {
            break;
        }
    }
    assert_eq!(
        stable, 4,
        "runtime allocations did not reach a bounded warm baseline"
    );
    let baseline = LIVE_BYTES.load(Relaxed);
    for _ in 0..16 {
        cycle();
        assert_eq!(
            LIVE_BYTES.load(Relaxed),
            baseline,
            "resource-limited query retained state"
        );
    }
    println!(
        "{{\"operation\":\"resource_limited_query_teardown\",\"repetitions\":16,\"retained_query_bytes\":0,\"bounded_runtime_retained_bytes\":0}}"
    );
    runtime
}

fn continuation_query_teardown() -> selector_solve::SolverRuntime {
    use selector_solve::{
        ExecutionRoot, QuerySession, SolveControl, SolveOptions, SolverRuntime, StopReason,
    };
    use std::sync::Arc;
    let (facts, graph) = query_fixture();
    let options = SolveOptions {
        workers: 2,
        scratch_bytes_per_worker: 1,
        memory_budget_bytes: 64 * 1024 * 1024,
        ..Default::default()
    };
    let runtime = SolverRuntime::new(&options).unwrap();
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("query.continuation");
    let corrupt_path = directory.path().join("corrupt.continuation");
    let control = Arc::new(SolveControl::default());
    let paused_options = SolveOptions {
        control: Some(control.clone()),
        ..options.clone()
    };
    let producer = selector_types::ContentHash([0x35; 32]);
    let roots = [ExecutionRoot {
        node: NodeId(0),
        receiver: SymbolId(0),
    }];
    settle_idle_workers();
    let cycle = |cancel: bool| {
        control.reset();
        if cancel {
            control.cancel();
        } else {
            control.checkpoint_after_round(1);
        }
        let mut paused =
            QuerySession::with_runtime(&facts, &graph, &paused_options, &runtime).unwrap();
        paused.execute(&roots).unwrap();
        assert_eq!(
            paused.stop_reason(),
            Some(if cancel {
                StopReason::Cancelled
            } else {
                StopReason::CheckpointRequested
            })
        );
        if path.exists() {
            std::fs::remove_file(&path).unwrap();
        }
        paused.save_checkpoint(&path, producer).unwrap();
        drop(paused);
        assert!(
            QuerySession::from_checkpoint(
                &facts,
                &graph,
                &options,
                &runtime,
                &path,
                selector_types::ContentHash([0x36; 32])
            )
            .is_err()
        );
        let mut bytes = std::fs::read(&path).unwrap();
        *bytes.last_mut().unwrap() ^= 1;
        std::fs::write(&corrupt_path, &bytes).unwrap();
        drop(bytes);
        assert!(
            QuerySession::from_checkpoint(
                &facts,
                &graph,
                &options,
                &runtime,
                &corrupt_path,
                producer
            )
            .is_err()
        );
        let mut resumed =
            QuerySession::from_checkpoint(&facts, &graph, &options, &runtime, &path, producer)
                .unwrap();
        resumed.resume().unwrap();
        drop(resumed.analyze(&[NodeId(1)]).unwrap());
        assert_eq!(resumed.stop_reason(), None);
        drop(resumed);
        assert_eq!(runtime.retained_bytes(), 0);
    };
    let mut previous = LIVE_BYTES.load(Relaxed);
    let mut stable = 0;
    for _ in 0..32 {
        cycle(false);
        cycle(true);
        let current = LIVE_BYTES.load(Relaxed);
        stable = if current == previous { stable + 1 } else { 0 };
        previous = current;
        if stable == 4 {
            break;
        }
    }
    assert_eq!(stable, 4, "continuation runtime caches did not stabilize");
    let baseline = LIVE_BYTES.load(Relaxed);
    for index in 0..32 {
        cycle(index % 2 == 0);
        assert_eq!(
            LIVE_BYTES.load(Relaxed),
            baseline,
            "paused/cancelled/admitted/rejected checkpoint owners retain bytes at cycle {index}"
        );
    }
    println!(
        "{{\"operation\":\"continuation_query_teardown\",\"repetitions\":32,\"cancelled_cycles\":16,\"producer_rejections\":32,\"checksum_rejections\":32,\"retained_query_bytes\":0,\"bounded_runtime_retained_bytes\":0}}"
    );
    runtime
}

fn repeated_call_fixture(calls: usize) -> (selector_facts::FactSnapshot, ProgramGraph) {
    // Synthetic cardinality probe: repeat the same pure call at one verified
    // source site. This exercises real operation/posting/value capacities while
    // retaining exactly two semantic execution contexts. It is not a compiler
    // extraction or source-language conformance fixture.
    let (mut facts, mut graph) = query_fixture();
    let call = facts.operations[0];
    let terminal = facts.operations[1];
    facts.operations = (0..calls)
        .map(|index| selector_facts::OperationRecord {
            dest: ValueId(index as u32 + 1),
            ..call
        })
        .chain(std::iter::once(terminal))
        .collect();
    facts.bodies[0].operations.len = calls as u32;
    facts.bodies[1].operations.start = calls as u32;
    let edge = graph.edges[0];
    graph.edges = (0..calls)
        .map(|index| EdgeRecord {
            operation: OperationId(index as u32),
            ..edge
        })
        .collect();
    facts.validate().unwrap();
    graph.index().unwrap();
    graph.validate().unwrap();
    (facts, graph)
}

fn varied_query_teardown() -> selector_solve::SolverRuntime {
    use selector_solve::{ExecutionRoot, QuerySession, SolveOptions, SolverRuntime};
    let options = SolveOptions {
        workers: 2,
        // Discard variable scratch here so retained pool capacity cannot mask a
        // query-owner leak. The normal lifecycle separately checks stable bank
        // reuse. Logical HashMap capacity estimates are not allocator byte counts.
        scratch_bytes_per_worker: 1,
        ..SolveOptions::default()
    };
    let limited = SolveOptions {
        max_contexts: 1,
        ..options.clone()
    };
    let fixtures = [1024, 1, 64, 7].map(repeated_call_fixture);
    let runtime = SolverRuntime::new(&options).unwrap();
    settle_idle_workers();
    let roots = [ExecutionRoot {
        node: NodeId(0),
        receiver: SymbolId(0),
    }];
    let cycle = |index: usize| {
        let (facts, graph) = &fixtures[index % fixtures.len()];
        let stopped = index % 5 == 0;
        let mut query = QuerySession::with_runtime(
            facts,
            graph,
            if stopped { &limited } else { &options },
            &runtime,
        )
        .unwrap();
        if index % 7 == 0 {
            assert!(query.analyze(&[NodeId::NONE]).is_err());
        }
        query.execute(&roots).unwrap();
        let result = query.analyze(&[NodeId(1)]).unwrap();
        assert_eq!(
            result.completion,
            if stopped {
                Completion::ResourceLimited
            } else {
                Completion::Complete
            }
        );
        assert_eq!(query.context_count(), if stopped { 1 } else { 2 });
        let owned = query.owned_bytes();
        drop(black_box(result));
        drop(query);
        assert_eq!(runtime.retained_bytes(), 0);
        owned
    };
    // Warm all input sizes and success/failure schedules before taking a
    // process-global baseline. Runtime-owned parking/scheduling caches must
    // stabilize; every query and oversized scratch owner must be released.
    let mut previous = 0;
    let mut stable = 0;
    for batch in 0..16 {
        for offset in 0..20 {
            cycle(batch * 20 + offset);
        }
        let normalized = LIVE_BYTES.load(Relaxed);
        stable = if normalized == previous {
            stable + 1
        } else {
            0
        };
        previous = normalized;
        if stable == 4 {
            break;
        }
    }
    assert_eq!(stable, 4, "varied query ownership did not stabilize");
    let baseline = LIVE_BYTES.load(Relaxed);
    let mut minimum = usize::MAX;
    let mut maximum = 0;
    let mut peak_idle = 0;
    for index in 0..100 {
        let owned = cycle(index);
        minimum = minimum.min(owned);
        maximum = maximum.max(owned);
        peak_idle = peak_idle.max(runtime.retained_bytes());
        assert_eq!(
            LIVE_BYTES.load(Relaxed),
            baseline,
            "varied/large-then-small/failure query retains non-runtime bytes at cycle {index}"
        );
    }
    assert!(
        maximum > minimum,
        "cardinality probe did not grow real owned state"
    );
    let mut allocation_growth = [(0usize, 0usize); 4];
    for (position, index) in [1, 3, 2, 4].into_iter().enumerate() {
        let calls = fixtures[index % fixtures.len()].0.bodies[0].operations.len;
        let window = Window::begin();
        black_box(cycle(index));
        let counts = window.finish();
        allocation_growth[position] = (counts.allocations, counts.reallocations);
        assert_eq!(LIVE_BYTES.load(Relaxed), baseline);
        println!(
            "{{\"operation\":\"fresh_query_cardinality\",\"calls\":{calls},\"contexts\":2,\"allocations\":{},\"reallocations\":{},\"allocated_bytes\":{}}}",
            counts.allocations, counts.reallocations, counts.allocated_bytes
        );
    }
    // Increasing one body from 1 to 1024 calls adds local-value/posting table
    // capacity, not execution contexts. These explicit growth budgets allow
    // bounded flat-buffer/table expansion and reject allocation per call visit.
    assert!(allocation_growth[3].0 <= allocation_growth[0].0 + 32);
    assert!(allocation_growth[3].1 <= allocation_growth[0].1 + 64);
    println!(
        "{{\"operation\":\"varied_large_then_small_query_teardown\",\"repetitions\":100,\"operation_cardinalities\":[1024,1,64,7],\"resource_limited_cycles\":20,\"invalid_input_cycles\":15,\"retained_query_bytes\":0,\"peak_runtime_retained_bytes\":{peak_idle},\"min_query_owned_bytes\":{minimum},\"max_query_owned_bytes\":{maximum}}}"
    );
    runtime
}

fn owner_teardown() {
    // Exercise owned builder release separately from OS RSS/allocator page caching.
    let baseline = LIVE_BYTES.load(Relaxed);
    for _ in 0..32 {
        let mut builder = FactBuilder::new();
        for i in 0..2048 {
            builder
                .ensure_symbol(&format!("owner#{i}()."), FileId::NONE)
                .unwrap();
        }
        black_box(builder.finish().unwrap());
    }
    assert_eq!(
        LIVE_BYTES.load(Relaxed),
        baseline,
        "fact owners retain allocation bytes after drop"
    );
    println!("{{\"operation\":\"fact_owner_teardown\",\"repetitions\":32,\"retained_bytes\":0}}");
}

struct CompleteWorld(ValuePool, bool);
impl World for CompleteWorld {
    fn values(&self) -> &ValuePool {
        &self.0
    }
    fn summary(
        &self,
        node: NodeId,
        _: Value,
        _: &[Value],
        _: &ValuePool,
        _: &mut Vec<Value>,
    ) -> SummaryRead {
        assert!(
            !self.1 || node == NodeId(1),
            "unused Future callback return"
        );
        SummaryRead {
            context: None,
            value: Value::EMPTY,
            version: 1,
            present: true,
        }
    }
    fn slot(&self, _: Slot) -> (Value, u64, bool) {
        panic!("no heap access")
    }
    fn capture(&self, _: u32) -> Option<(Value, &[Value], u64)> {
        panic!("local capture")
    }
    fn binding(
        &self,
        _: OperationId,
        _: Value,
        _: &[Value],
        _: &ValuePool,
        _: &mut Vec<Atom>,
        _: &mut Vec<Value>,
    ) -> Option<u32> {
        None
    }
}
fn certified_callback_transfer_hits(future: bool) {
    use selector_facts::{BodyRecord, FileRecord, OperationRecord};
    use selector_transfer::{Evaluation, Scratch, TypeIndex, evaluate};
    let mut builder = FactBuilder::new();
    let path = builder.intern("Callback.scala").unwrap();
    let source = builder.intern(&" ".repeat(64)).unwrap();
    builder.facts.files.push(FileRecord {
        path,
        source,
        revision: StrId::NONE,
        context: StrId::NONE,
        source_hash: ContentHash([1; 32]),
        flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
    });
    let root = builder.ensure_symbol("p/root().", FileId(0)).unwrap();
    let external = builder
        .ensure_symbol(
            if future {
                "scala/concurrent/Future#map()."
            } else {
                "framework/scope()."
            },
            FileId::NONE,
        )
        .unwrap();
    let callback = builder
        .ensure_symbol("p/root().callback().", FileId(0))
        .unwrap();
    builder
        .facts
        .operands
        .extend([ValueId(2), ValueId(1), ValueId(2)]);
    builder.facts.operations = vec![
        OperationRecord {
            body: BodyId(0),
            opcode: Opcode::Parameter,
            target: SymbolId::NONE,
            dest: ValueId(2),
            a: ValueId::NONE,
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span::default(),
            flags: 0,
        },
        OperationRecord {
            body: BodyId(0),
            opcode: Opcode::BindCallback,
            target: callback,
            dest: ValueId(1),
            a: ValueId::NONE,
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span::default(),
            flags: 0,
        },
        OperationRecord {
            body: BodyId(0),
            opcode: Opcode::Call,
            target: external,
            dest: ValueId(3),
            a: ValueId::NONE,
            b: ValueId::NONE,
            arguments: IdRange { start: 1, len: 2 },
            span: Span::default(),
            flags: 0,
        },
    ];
    for (symbol, operations, parameters) in [
        (
            root,
            IdRange { start: 0, len: 3 },
            IdRange { start: 0, len: 1 },
        ),
        (callback, IdRange { start: 3, len: 0 }, IdRange::default()),
    ] {
        builder.facts.bodies.push(BodyRecord {
            symbol,
            file: FileId(0),
            span: Span { start: 0, end: 64 },
            name_span: Span::default(),
            operations,
            parameters,
            body_hash: ContentHash([2; 32]),
            flags: 0,
        });
    }
    let facts = builder.finish().unwrap();
    let mut graph = ProgramGraph {
        facts_identity: facts.identity,
        ..Default::default()
    };
    graph.symbol_nodes = vec![NodeId(0), NodeId(1), NodeId(2)];
    graph.nodes = vec![
        NodeRecord {
            symbol: root,
            file: FileId(0),
            body: BodyId(0),
            flags: 0,
        },
        NodeRecord {
            symbol: external,
            file: FileId::NONE,
            body: BodyId::NONE,
            flags: 0,
        },
        NodeRecord {
            symbol: callback,
            file: FileId(0),
            body: BodyId(1),
            flags: 0,
        },
    ];
    graph.edges.push(EdgeRecord {
        source: NodeId(0),
        target: NodeId(1),
        kind: EdgeKind::Call,
        occurrence: OccurrenceId::NONE,
        operation: OperationId(2),
        receiver: SymbolId::NONE,
        flags: (if future {
            EDGE_CALLBACK_DEFERRED
        } else {
            EDGE_TEST_REGISTRATION
        }) | encode_callback_argument(0).unwrap(),
    });
    graph.index().unwrap();
    let types = TypeIndex::new(&facts);
    let world = CompleteWorld(ValuePool::new(16), future);
    let mut scratch = Scratch::new(16);
    let mut output = Evaluation::default();
    for _ in 0..16 {
        evaluate(
            &facts,
            &graph,
            &types,
            &world,
            NodeId(0),
            Value::EMPTY,
            &[Value::TOP],
            &mut scratch,
            &mut output,
        )
        .unwrap();
    }
    assert_eq!(output.issues.is_empty(), !future);
    if future {
        assert_eq!(
            output.first_issue.unwrap().reason.as_str(),
            "incomplete_deferred_callback"
        );
    }
    assert!(
        output
            .calls
            .iter()
            .any(|call| call.kind == EdgeKind::Callback && call.target == NodeId(2))
    );
    let window = Window::begin();
    for _ in 0..1_000 {
        black_box(evaluate(
            black_box(&facts),
            black_box(&graph),
            &types,
            &world,
            NodeId(0),
            Value::EMPTY,
            &[Value::TOP],
            &mut scratch,
            &mut output,
        ))
        .unwrap();
    }
    expect_zero(
        if future {
            "possible_future_callback_effects_without_return_subscription"
        } else {
            "certified_callback_transfer_with_unknown_implicit_carrier"
        },
        window.finish(),
    );
    assert_eq!(output.issues.is_empty(), !future);
    assert!(
        output
            .calls
            .iter()
            .any(|call| call.kind == EdgeKind::Callback && call.observe_return != future)
    );
}

fn scoped_dispatch_transfer_hits() {
    use selector_facts::{BodyRecord, FileRecord, OperationRecord, RelationRecord};
    use selector_transfer::{Evaluation, Scratch, TypeIndex, evaluate};
    let mut builder = FactBuilder::new();
    let path = builder.intern("Scoped.scala").unwrap();
    builder.facts.files.push(FileRecord {
        path,
        source: StrId::NONE,
        revision: StrId::NONE,
        context: StrId::NONE,
        source_hash: ContentHash::default(),
        flags: 0,
    });
    for (index, name) in [
        "p/run().",
        "p/Base#",
        "p/Deferred#",
        "p/Sibling#",
        "p/Base#method().",
    ]
    .into_iter()
    .enumerate()
    {
        assert_eq!(
            builder.ensure_symbol(name, FileId(0)).unwrap(),
            SymbolId(index as u32)
        );
        builder.facts.symbols[index].kind = if (1..=3).contains(&index) { 13 } else { 3 };
        builder.facts.symbols[index].flags = SYMBOL_DEFINED | SYMBOL_SCALA_PARENTS_COMPLETE;
    }
    builder.facts.symbols[4].owner = SymbolId(1);
    for child in [2, 3] {
        builder.facts.relations.push(RelationRecord {
            source: SymbolId(child),
            target: SymbolId(1),
            kind: RelationKind::Parent,
            file: FileId(0),
        });
    }
    builder.facts.relations.push(RelationRecord {
        source: SymbolId(2),
        target: SymbolId(4),
        kind: RelationKind::DeferredDispatch,
        file: FileId(0),
    });
    builder.facts.bodies.push(BodyRecord {
        symbol: SymbolId(0),
        file: FileId(0),
        span: Span::default(),
        name_span: Span::default(),
        operations: IdRange { start: 0, len: 2 },
        parameters: IdRange::default(),
        body_hash: ContentHash::default(),
        flags: 0,
    });
    let invocation = OperationRecord {
        body: BodyId(0),
        opcode: Opcode::VirtualCall,
        target: SymbolId(4),
        dest: ValueId(1),
        a: ValueId(0),
        b: ValueId::NONE,
        arguments: IdRange::default(),
        span: Span::default(),
        flags: 0,
    };
    builder.facts.operations.extend([
        invocation,
        OperationRecord {
            opcode: Opcode::Return,
            target: SymbolId::NONE,
            dest: ValueId::NONE,
            a: ValueId(1),
            ..invocation
        },
    ]);
    let facts = builder.finish().unwrap();
    let mut graph = ProgramGraph {
        facts_identity: facts.identity,
        ..Default::default()
    };
    for index in 0..5 {
        graph.symbol_nodes.push(NodeId(index));
        graph.nodes.push(NodeRecord {
            symbol: SymbolId(index),
            file: FileId(0),
            body: if index == 0 { BodyId(0) } else { BodyId::NONE },
            flags: 0,
        });
    }
    let candidate = EdgeRecord {
        source: NodeId(0),
        target: NodeId(4),
        kind: EdgeKind::VirtualCall,
        operation: OperationId(0),
        occurrence: OccurrenceId::NONE,
        receiver: SymbolId(1),
        flags: 0,
    };
    graph.edges.extend([
        candidate,
        EdgeRecord {
            kind: EdgeKind::Guard,
            receiver: SymbolId(2),
            flags: EDGE_UNKNOWN | EDGE_DEFERRED_DISPATCH,
            ..candidate
        },
    ]);
    graph.index().unwrap();
    let types = TypeIndex::new(&facts);
    let mut world = CompleteWorld(ValuePool::new(16), false);
    let receivers = [2, 3].map(|class| {
        world
            .0
            .singleton(Atom {
                kind: selector_domain::AtomKind::Object,
                site: OperationId::NONE,
                symbol: SymbolId(class),
                binding: 0,
            })
            .unwrap()
    });
    let mut scratch = Scratch::new(16);
    let mut output = Evaluation::default();
    for i in 0..32 {
        evaluate(
            &facts,
            &graph,
            &types,
            &world,
            NodeId(0),
            receivers[i % 2],
            &[],
            &mut scratch,
            &mut output,
        )
        .unwrap();
        assert_eq!(output.issues.is_empty(), i % 2 != 0);
    }
    let retained = scratch.owned_bytes();
    let live = LIVE_BYTES.load(Relaxed);
    let window = Window::begin();
    for i in 0..black_box(10_000) {
        evaluate(
            black_box(&facts),
            black_box(&graph),
            &types,
            &world,
            NodeId(0),
            receivers[i % 2],
            &[],
            &mut scratch,
            &mut output,
        )
        .unwrap();
        assert_eq!(output.value.is_unknown(), i % 2 == 0);
        assert_eq!(output.issues.is_empty(), i % 2 != 0);
        assert_eq!(output.calls.len(), 1, "frontier does not become a callee");
        if i % 2 == 0 {
            assert_eq!(
                output.first_issue.unwrap().reason.as_str(),
                "incomplete_virtual_dispatch"
            );
        } else {
            assert!(output.first_issue.is_none());
        }
    }
    expect_zero(
        "scoped_dispatch_matching_and_disjoint_receiver_hits",
        window.finish(),
    );
    assert_eq!(scratch.owned_bytes(), retained);
    assert_eq!(
        LIVE_BYTES.load(Relaxed),
        live,
        "warmed scoped transfer retained growth"
    );
}

fn heap_owner_hits() {
    use selector_domain::{HeapOwnerKey, HeapOwners};
    let mut owners = HeapOwners::new(32, 8).unwrap();
    let keys = [
        HeapOwnerKey {
            site: OperationId(3),
            root: SymbolId(1),
        },
        HeapOwnerKey {
            site: OperationId(3),
            root: SymbolId(2),
        },
    ];
    let ids = keys.map(|key| owners.intern(key).unwrap());
    assert_ne!(ids[0], ids[1]);
    let owned = owners.owned_bytes();
    let window = Window::begin();
    for index in 0..black_box(100_000) {
        let index = index % 2;
        assert_eq!(owners.lookup(black_box(keys[index])), Some(ids[index]));
        assert_eq!(owners.key(black_box(ids[index])), Some(keys[index]));
        assert_eq!(owners.intern(black_box(keys[index])).unwrap(), ids[index]);
    }
    expect_zero("known_root_partitioned_heap_owner_hits", window.finish());
    assert_eq!(owners.rows(), keys);
    assert_eq!(owners.owned_bytes(), owned);
}

fn partitioned_heap_transfer_hits(known: bool, carrier: bool) {
    use selector_domain::{
        Atom, AtomKind, HeapOwnerKey, HeapOwners, LOCAL_HEAP_OWNER, Slot, SlotKind, Value,
        ValuePool,
    };
    use selector_facts::{BodyRecord, FileRecord, OperationRecord};
    use selector_transfer::{Evaluation, Scratch, SummaryRead, TypeIndex, World, evaluate};
    struct HeapWorld {
        pool: ValuePool,
        owners: HeapOwners,
        roots: [Value; 2],
        owner_ids: [u32; 2],
        known: bool,
    }
    impl World for HeapWorld {
        fn values(&self) -> &ValuePool {
            &self.pool
        }
        fn summary(
            &self,
            _: NodeId,
            _: Value,
            _: &[Value],
            _: &ValuePool,
            _: &mut Vec<Value>,
        ) -> SummaryRead {
            SummaryRead {
                context: None,
                value: Value::EMPTY,
                version: 1,
                present: true,
            }
        }
        fn slot(&self, slot: Slot) -> (Value, u64, bool) {
            if slot.kind == SlotKind::Field {
                for (i, &owner) in self.owner_ids.iter().enumerate() {
                    if slot.owner == owner {
                        return (self.roots[i], 1, true);
                    }
                }
            }
            (Value::EMPTY, 0, false)
        }
        fn heap_owner(&self, key: HeapOwnerKey) -> Option<u32> {
            if self.known {
                self.owners.lookup(key)
            } else {
                None
            }
        }
        fn capture(&self, _: u32) -> Option<(Value, &[Value], u64)> {
            None
        }
        fn binding(
            &self,
            _: OperationId,
            _: Value,
            _: &[Value],
            _: &ValuePool,
            _: &mut Vec<Atom>,
            _: &mut Vec<Value>,
        ) -> Option<u32> {
            None
        }
    }
    let mut builder = FactBuilder::new();
    let path = builder.intern("Heap.scala").unwrap();
    let source = builder.intern(&" ".repeat(64)).unwrap();
    builder.facts.files.push(FileRecord {
        path,
        source,
        revision: StrId::NONE,
        context: StrId::NONE,
        source_hash: ContentHash([1; 32]),
        flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
    });
    let root = builder.ensure_symbol("p/root().", FileId(0)).unwrap();
    let roots = [
        builder.ensure_symbol("p/RootA#", FileId(0)).unwrap(),
        builder.ensure_symbol("p/RootB#", FileId(0)).unwrap(),
    ];
    let object = builder.ensure_symbol("p/Box#", FileId(0)).unwrap();
    let field = builder
        .ensure_symbol(
            if carrier {
                SEQUENCE_ELEMENTS_SYMBOL
            } else {
                "p/Box#value."
            },
            FileId(0),
        )
        .unwrap();
    for class in [roots[0], roots[1], object] {
        builder.facts.symbols[class.index()].kind = 13;
    }
    if !carrier {
        builder.facts.symbols[field.index()].owner = object;
    }
    let template = OperationRecord {
        body: BodyId(0),
        opcode: Opcode::Parameter,
        target: SymbolId::NONE,
        dest: ValueId::NONE,
        a: ValueId::NONE,
        b: ValueId::NONE,
        arguments: IdRange::default(),
        span: Span { start: 0, end: 64 },
        flags: 0,
    };
    builder.facts.operations = vec![
        OperationRecord {
            dest: ValueId(2),
            ..template
        },
        OperationRecord {
            opcode: Opcode::Allocate,
            target: object,
            dest: ValueId(1),
            ..template
        },
        OperationRecord {
            opcode: Opcode::StoreField,
            target: field,
            a: ValueId(1),
            b: ValueId(2),
            ..template
        },
        OperationRecord {
            opcode: Opcode::LoadField,
            target: field,
            a: ValueId(1),
            dest: ValueId(3),
            ..template
        },
        OperationRecord {
            opcode: Opcode::Return,
            a: ValueId(3),
            ..template
        },
    ];
    if carrier {
        builder.facts.operations[1].opcode = Opcode::PackSequence;
        builder.facts.operations[1].target = field;
        builder.facts.operations[1].arguments = IdRange { start: 0, len: 1 };
        builder.facts.operations.remove(2);
        builder.facts.operations[2].opcode = Opcode::ReadElements;
        builder.facts.operations[2].target = SymbolId::NONE;
    }
    builder.facts.operands.push(ValueId(2));
    let operations = u32::try_from(builder.facts.operations.len()).unwrap();
    builder.facts.bodies.push(BodyRecord {
        symbol: root,
        file: FileId(0),
        span: Span { start: 0, end: 64 },
        name_span: Span::default(),
        operations: IdRange {
            start: 0,
            len: operations,
        },
        parameters: IdRange { start: 0, len: 1 },
        body_hash: ContentHash([2; 32]),
        flags: 0,
    });
    let facts = builder.finish().unwrap();
    let mut graph = ProgramGraph {
        facts_identity: facts.identity,
        ..Default::default()
    };
    graph.nodes = facts
        .symbols
        .iter()
        .enumerate()
        .map(|(i, _)| NodeRecord {
            symbol: SymbolId(i as u32),
            file: if i == root.index() {
                FileId(0)
            } else {
                FileId::NONE
            },
            body: if i == root.index() {
                BodyId(0)
            } else {
                BodyId::NONE
            },
            flags: 0,
        })
        .collect();
    graph.symbol_nodes = (0..facts.symbols.len()).map(|i| NodeId(i as u32)).collect();
    if !carrier {
        graph.edges.push(EdgeRecord {
            source: NodeId(root.0),
            target: NodeId(object.0),
            kind: EdgeKind::Construct,
            occurrence: OccurrenceId::NONE,
            operation: OperationId(1),
            receiver: object,
            flags: 0,
        });
    }
    graph.index().unwrap();
    let mut pool = ValuePool::new(16);
    let receivers = roots.map(|symbol| {
        pool.singleton(Atom {
            kind: AtomKind::Object,
            site: OperationId::NONE,
            symbol,
            binding: 0,
        })
        .unwrap()
    });
    let mut owners = HeapOwners::new(facts.operations.len(), facts.symbols.len()).unwrap();
    let keys = roots.map(|root| HeapOwnerKey {
        site: OperationId(1),
        root,
    });
    let owner_ids = keys.map(|key| owners.intern(key).unwrap());
    let world = HeapWorld {
        pool,
        owners,
        roots: receivers,
        owner_ids,
        known,
    };
    let types = TypeIndex::new(&facts);
    let mut scratch = Scratch::new(16);
    let mut output = Evaluation::default();
    for i in 0..16 {
        let index = i % 2;
        evaluate(
            &facts,
            &graph,
            &types,
            &world,
            NodeId(root.0),
            receivers[index],
            &[receivers[index]],
            &mut scratch,
            &mut output,
        )
        .unwrap();
        assert_eq!(output.stores.len(), 1);
        let owner = if known {
            owner_ids[index]
        } else {
            LOCAL_HEAP_OWNER
        };
        assert_eq!(
            output.stores[0].slot,
            Slot {
                kind: SlotKind::Field,
                owner,
                member: field.0
            }
        );
        assert_eq!(output.field_reads, [output.stores[0].slot]);
        if known {
            assert!(output.heap_owners.is_empty());
            assert_eq!(
                scratch.pool.members(output.value),
                world.pool.members(receivers[index])
            );
        } else {
            assert_eq!(output.heap_owners, [keys[index]]);
        }
    }
    let owners_before = world.owners.owned_bytes();
    let scratch_before = scratch.owned_bytes();
    let window = Window::begin();
    for i in 0..black_box(2_000) {
        let index = i % 2;
        black_box(evaluate(
            black_box(&facts),
            black_box(&graph),
            &types,
            &world,
            NodeId(root.0),
            receivers[index],
            &[receivers[index]],
            &mut scratch,
            &mut output,
        ))
        .unwrap();
    }
    expect_zero(
        match (carrier, known) {
            (true, true) => "root_partitioned_sequence_pack_read_transfer",
            (true, false) => "worker_local_sequence_pack_read_transfer",
            (false, true) => "root_partitioned_allocation_store_load_transfer",
            (false, false) => "worker_local_heap_owner_draft_transfer",
        },
        window.finish(),
    );
    assert_eq!(owners_before, world.owners.owned_bytes());
    assert_eq!(scratch_before, scratch.owned_bytes());
    assert_ne!(owner_ids[0], owner_ids[1]);
}

fn main() {
    // Force stdout setup outside measured windows and release windows before reports.
    println!("{{\"harness\":\"selector-allocation-contracts/v1\"}}");
    counter_calibration();
    fact_hits();
    fact_lookup_hits_and_misses();
    result_bound_hits_and_misses();
    graph_hits();
    dependency_hits();
    artifact_hits();
    canonical_domain_hits();
    let shape_baseline = LIVE_BYTES.load(Relaxed);
    callback_shape_hits();
    assert_eq!(
        LIVE_BYTES.load(Relaxed),
        shape_baseline,
        "callback shape owners survive drop"
    );
    certified_callback_transfer_hits(false);
    certified_callback_transfer_hits(true);
    let scoped_baseline = LIVE_BYTES.load(Relaxed);
    scoped_dispatch_transfer_hits();
    assert_eq!(
        LIVE_BYTES.load(Relaxed),
        scoped_baseline,
        "scoped dispatch owners survive drop"
    );
    let heap_baseline = LIVE_BYTES.load(Relaxed);
    heap_owner_hits();
    partitioned_heap_transfer_hits(true, false);
    partitioned_heap_transfer_hits(false, false);
    partitioned_heap_transfer_hits(true, true);
    partitioned_heap_transfer_hits(false, true);
    assert_eq!(
        LIVE_BYTES.load(Relaxed),
        heap_baseline,
        "heap owner and transfer owners survive drop"
    );
    owner_teardown();
    let _runtime = query_lifecycle();
    let _limited_runtime = stopped_query_teardown();
    let _continuation_runtime = continuation_query_teardown();
    let _varied_runtime = varied_query_teardown();
}
