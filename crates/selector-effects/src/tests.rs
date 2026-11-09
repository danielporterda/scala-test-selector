use super::*;
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;

struct CountingAllocator;
thread_local! {
    static COUNTING: Cell<bool> = const { Cell::new(false) };
    static ALLOCS: Cell<(usize, usize, usize)> = const { Cell::new((0, 0, 0)) };
}
fn record(bytes: usize, realloc: bool) {
    let _ = COUNTING.try_with(|active| {
        if active.get() {
            ALLOCS.with(|counts| {
                let (a, r, b) = counts.get();
                counts.set((
                    a + usize::from(!realloc),
                    r + usize::from(realloc),
                    b + bytes,
                ));
            });
        }
    });
}
unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        record(layout.size(), false);
        unsafe { System.alloc(layout) }
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        record(layout.size(), false);
        unsafe { System.alloc_zeroed(layout) }
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        record(size, true);
        unsafe { System.realloc(ptr, layout, size) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
}
#[global_allocator]
static ALLOCATOR: CountingAllocator = CountingAllocator;

pub(crate) fn tracked(f: impl FnOnce()) -> (usize, usize, usize) {
    ALLOCS.with(|x| x.set((0, 0, 0)));
    COUNTING.with(|x| x.set(true));
    f();
    COUNTING.with(|x| x.set(false));
    ALLOCS.with(Cell::get)
}
fn r(start: u32, len: u32) -> Range {
    Range { start, len }
}
fn subject(index: u32) -> SubjectRef {
    SubjectRef {
        kind: SubjectKind::FactNode,
        index,
    }
}
fn empty(index: u32, arity: u32, captures: u32, fresh: u32) -> MethodRow {
    MethodRow {
        top: TopMask::NONE,
        ..MethodRow::unknown(subject(index), 0, arity, captures, fresh)
    }
}
fn fixture() -> (CapsuleData, RefBounds) {
    let mut method = empty(0, 2, 1, 1);
    method.calls = r(0, 1);
    method.code_observations = r(0, 1);
    method.reads = r(0, 2);
    method.writes = r(0, 2);
    method.throws = r(0, 1);
    method.synchronizes = r(0, 1);
    method.external = r(0, 1);
    method.flows = r(0, 2);
    let data = CapsuleData {
        methods: vec![method, MethodRow::unknown(subject(1), 0, 1, 1, 0)],
        calls: vec![CallRow {
            site: 0,
            target: CallTarget::Direct(MethodId(1)),
            receiver_value: ValueRef::UNKNOWN,
            result: NONE,
            kind: CallKind::Virtual,
            receiver: Origin::RECEIVER,
            arguments: r(0, 1),
            captures: r(1, 1),
        }],
        origins: vec![Origin::argument(1), Origin::capture(0)],
        callable_values: vec![ValueRef::UNKNOWN; 2],
        code_observations: vec![CodeRef {
            kind: CodeKind::Method,
            index: 1,
        }],
        reads: vec![
            StorageRef {
                kind: StorageKind::InstanceField,
                member: 0,
                base: Origin::RECEIVER,
            },
            StorageRef {
                kind: StorageKind::ArrayElements,
                member: NONE,
                base: Origin::argument(0),
            },
        ],
        writes: vec![
            StorageRef {
                kind: StorageKind::InstanceField,
                member: 1,
                base: Origin::capture(0),
            },
            StorageRef {
                kind: StorageKind::InstanceField,
                member: 0,
                base: Origin::fresh(0),
            },
        ],
        throws: vec![0],
        synchronizes: vec![SyncRef {
            kind: SyncKind::Monitor,
            base: Origin::RECEIVER,
        }],
        external: vec![ExternalRef {
            kind: ExternalKind::Read,
            key: 0,
        }],
        flows: vec![
            FlowRef {
                source: Origin::argument(1),
                sink: FlowSink::Return,
                via: NONE,
                index: 0,
            },
            FlowRef {
                source: Origin::capture(0),
                sink: FlowSink::HeapWrite,
                via: 0,
                index: 0,
            },
        ],
        ..CapsuleData::default()
    };
    let bounds = RefBounds {
        fact_nodes: 2,
        foreign_methods: 0,
        authorities: 1,
        members: 2,
        classes: 1,
        exceptions: 1,
        externals: 1,
        sites: 1,
        sams: 0,
        adapters: 0,
        bridge_proofs: 0,
        phases: 0,
    };
    (data, bounds)
}
fn caller() -> MethodRow {
    empty(0, 3, 1, 3)
}
fn capsules(data: CapsuleData, bounds: RefBounds) -> Capsules {
    Capsules::new(data, bounds, Limits::default()).unwrap()
}

#[test]
fn independent_channels_and_explicit_unknown_are_not_empty() {
    let (mut data, bounds) = fixture();
    data.methods[0].top.insert(Channel::Calls);
    let table = capsules(data, bounds);
    let known = table.view(MethodId(0)).unwrap();
    assert!(known.row.top.contains(Channel::Calls));
    assert!(!known.row.top.contains(Channel::Writes));
    assert_eq!(known.writes.len(), 2);
    let unknown = table.view(MethodId(1)).unwrap();
    assert_eq!(unknown.row.top, TopMask::ALL);
    assert!(unknown.writes.is_empty());
    assert_ne!(unknown.row.top, TopMask::NONE);
    assert_eq!(TopMask::from_bits(1 << 10), None);
    assert_eq!(OriginKind::from_u32(5), None);
    assert_eq!(FlowSink::from_u32(8), None);
}

#[test]
fn all_row_namespaces_and_storage_sentinels_are_checked() {
    let (original, bounds) = fixture();
    let mutations: &[fn(&mut CapsuleData)] = &[
        |d| d.calls[0].target = CallTarget::Direct(MethodId(NONE)),
        |d| d.calls[0].site = 1,
        |d| d.calls[0].arguments = r(NONE, 1),
        |d| d.origins[0] = Origin::argument(2),
        |d| d.methods[0].authority = 1,
        |d| {
            d.methods[0].subject = SubjectRef {
                kind: SubjectKind::ForeignMethod,
                index: 0,
            }
        },
        |d| d.reads[1].member = 0,
        |d| d.writes[0].member = 2,
        |d| {
            d.reads[0] = StorageRef {
                kind: StorageKind::StaticField,
                member: 0,
                base: Origin::RECEIVER,
            }
        },
        |d| {
            d.reads[0].base = Origin {
                kind: OriginKind::Any,
                index: 1,
            }
        },
        |d| {
            d.flows[0] = FlowRef {
                source: Origin::ANY,
                sink: FlowSink::CallArgument,
                via: 0,
                index: 1,
            }
        },
        |d| {
            d.synchronizes[0] = SyncRef {
                kind: SyncKind::FullFence,
                base: Origin::RECEIVER,
            }
        },
        |d| {
            d.code_observations[0] = CodeRef {
                kind: CodeKind::Class,
                index: 1,
            }
        },
        |d| d.throws[0] = 1,
        |d| d.external[0].key = 1,
    ];
    for mutate in mutations {
        let mut data = original.clone();
        mutate(&mut data);
        assert!(validate(&data, bounds, Limits::default()).is_err());
    }
    assert_eq!(
        validate(
            &original,
            bounds,
            Limits {
                max_rows: 0,
                ..Limits::default()
            }
        ),
        Err(Error::Budget)
    );
    assert_eq!(
        Range {
            start: u32::MAX,
            len: u32::MAX
        }
        .checked(4),
        Err(Error::Bounds)
    );
}

#[test]
fn checked_borrowed_scalar_view_never_treats_decode_failure_as_empty() {
    struct Broken<'a>(&'a CapsuleData);
    macro_rules! delegate {
        ($(($count:ident,$get:ident,$ty:ty)),+ $(,)?) => { $(fn $count(&self)->usize {self.0.$count()} fn $get(&self,i:usize)->Option<$ty>{self.0.$get(i)})+ };
    }
    impl TableView for Broken<'_> {
        fn call_count(&self) -> usize {
            self.0.calls.len()
        }
        fn call(&self, _: usize) -> Option<CallRow> {
            None
        }
        delegate!(
            (method_count, method, MethodRow),
            (origin_count, origin, Origin),
            (callable_value_count, callable_value, ValueRef),
            (sam_count, sam_arity, u32),
            (creation_count, creation, CallableCreation),
            (callable_bridge_count, callable_bridge, CallableBridge),
            (value_flow_count, value_flow, ValueFlow),
            (code_observation_count, code_observation, CodeRef),
            (read_count, read, StorageRef),
            (write_count, write, StorageRef),
            (escape_count, escape, EscapeRef),
            (initialize_count, initialize, MethodId),
            (throw_count, r#throw, u32),
            (synchronize_count, synchronize, SyncRef),
            (external_count, external, ExternalRef),
            (flow_count, flow, FlowRef)
        );
    }
    let (data, bounds) = fixture();
    let result = validate_tables(&Broken(&data), bounds, Limits::default());
    assert_eq!(result, Err(Error::Malformed));
    let counts = tracked(|| {
        validate_tables(&data, bounds, Limits::default()).unwrap();
    });
    assert_eq!(counts, (0, 0, 0));
}

#[test]
fn substitution_preserves_caller_coordinates_and_widens_callee_fresh() {
    let (data, bounds) = fixture();
    let table = capsules(data, bounds);
    let view = table.view(MethodId(0)).unwrap();
    let actuals = [Origin::fresh(1), Origin::argument(0)];
    let captures = [Origin::fresh(2)];
    let frame = Frame::new(
        view.row,
        caller(),
        Origin::argument(2),
        &actuals,
        &captures,
        &[2],
    )
    .unwrap();
    let mut scratch = SubstitutionScratch::default();
    assert!(matches!(
        substitute_into(view, &frame, &mut scratch),
        Err(Error::Capacity)
    ));
    scratch
        .reserve_for(view, &frame, Limits::default())
        .unwrap();
    let output = substitute_into(view, &frame, &mut scratch).unwrap();
    assert_eq!(output.reads[0].base, Origin::argument(2));
    assert_eq!(output.reads[1].base, Origin::fresh(1));
    assert_eq!(output.writes[0].base, Origin::ANY);
    assert_eq!(output.writes[1].base, Origin::ANY);
    assert_eq!(output.origins, &[Origin::argument(0), Origin::ANY]);
    assert_eq!(output.calls[0].receiver, Origin::argument(2));
    assert_eq!(output.flows[0].source, Origin::argument(0));
    assert_eq!(output.synchronizes[0].base, Origin::argument(2));
    assert_eq!(output.external, view.external);
    assert_eq!(output.throws, view.throws);
    assert!(
        Frame::new(
            view.row,
            caller(),
            Origin::ANY,
            &actuals[..1],
            &captures,
            &[]
        )
        .is_err()
    );
    assert!(
        Frame::new(
            view.row,
            caller(),
            Origin::ANY,
            &actuals,
            &captures,
            &[2, 1]
        )
        .is_err()
    );
}

#[test]
fn every_escape_is_applied_before_storage_and_unknown_escape_opens_all_fresh() {
    for sink in [
        EscapeSink::Return,
        EscapeSink::Heap,
        EscapeSink::Callback,
        EscapeSink::External,
        EscapeSink::Unknown,
    ] {
        let (mut data, bounds) = fixture();
        let index = if sink == EscapeSink::Heap { 1 } else { 0 };
        data.escapes.push(EscapeRef {
            origin: Origin::argument(0),
            sink,
            index,
        });
        data.methods[0].escapes = r(0, 1);
        if sink == EscapeSink::Unknown {
            data.methods[0].top.insert(Channel::Escapes);
        }
        let table = capsules(data, bounds);
        let view = table.view(MethodId(0)).unwrap();
        let actuals = [Origin::fresh(1), Origin::argument(0)];
        let captures = [Origin::fresh(2)];
        let frame = Frame::new(
            view.row,
            caller(),
            Origin::RECEIVER,
            &actuals,
            &captures,
            &[],
        )
        .unwrap();
        let mut scratch = SubstitutionScratch::default();
        scratch
            .reserve_for(view, &frame, Limits::default())
            .unwrap();
        let output = substitute_into(view, &frame, &mut scratch).unwrap();
        assert_eq!(output.reads[1].base, Origin::ANY);
        assert_eq!(output.escapes[0].origin, Origin::ANY);
        if sink == EscapeSink::Unknown {
            assert_eq!(output.writes[0].base, Origin::ANY);
        } else {
            assert_eq!(output.writes[0].base, Origin::fresh(2));
        }
    }
}

#[test]
fn unknown_escape_requires_explicit_open_channel() {
    let (mut data, bounds) = fixture();
    data.methods[0].escapes = r(0, 1);
    data.escapes.push(EscapeRef {
        origin: Origin::ANY,
        sink: EscapeSink::Unknown,
        index: 0,
    });
    assert_eq!(
        validate(&data, bounds, Limits::default()),
        Err(Error::Malformed)
    );
    data.methods[0].top.insert(Channel::Escapes);
    validate(&data, bounds, Limits::default()).unwrap();
}

#[test]
fn budget_rejection_precedes_any_scratch_capacity_growth() {
    let (data, bounds) = fixture();
    let table = capsules(data, bounds);
    let view = table.view(MethodId(0)).unwrap();
    let actuals = [Origin::ANY; 2];
    let captures = [Origin::ANY];
    let frame = Frame::new(view.row, caller(), Origin::ANY, &actuals, &captures, &[]).unwrap();
    let mut scratch = SubstitutionScratch::default();
    let counts = tracked(|| {
        assert_eq!(
            scratch.reserve_for(
                view,
                &frame,
                Limits {
                    max_bytes: 1,
                    ..Limits::default()
                }
            ),
            Err(Error::Budget)
        );
    });
    assert_eq!(counts, (0, 0, 0));
    assert_eq!(scratch.owned_bytes(), 0);
    scratch
        .reserve_for(view, &frame, Limits::default())
        .unwrap();
    let before = scratch.owned_bytes();
    assert_eq!(
        scratch.reserve_for(
            view,
            &frame,
            Limits {
                max_rows: 1,
                ..Limits::default()
            }
        ),
        Err(Error::Budget)
    );
    assert_eq!(scratch.owned_bytes(), before);
}

#[test]
fn borrowed_reads_and_warmed_substitution_allocate_zero() {
    let (data, bounds) = fixture();
    let table = capsules(data, bounds);
    let view = table.view(MethodId(0)).unwrap();
    let actuals = [Origin::fresh(1), Origin::argument(0)];
    let captures = [Origin::fresh(2)];
    let frame = Frame::new(
        view.row,
        caller(),
        Origin::argument(2),
        &actuals,
        &captures,
        &[2],
    )
    .unwrap();
    let mut scratch = SubstitutionScratch::default();
    scratch
        .reserve_for(view, &frame, Limits::default())
        .unwrap();
    let owned = scratch.owned_bytes();
    let mut count = 0usize;
    let allocation = tracked(|| {
        for _ in 0..100_000 {
            let view = table.view(MethodId(0)).unwrap();
            let output = substitute_into(view, &frame, &mut scratch).unwrap();
            std::hint::black_box(&output);
            count += output.writes.len() + output.calls.len();
        }
    });
    assert_eq!(count, 300_000);
    assert_eq!(allocation, (0, 0, 0));
    assert_eq!(scratch.owned_bytes(), owned);
}

#[test]
fn bounded_channel_join_never_silently_truncates() {
    let mut left = BoundedSet::new(2);
    left.reserve(4096).unwrap();
    left.insert(2u32).unwrap();
    left.insert(1).unwrap();
    left.insert(2).unwrap();
    assert_eq!(left.values(), &[1, 2]);
    assert!(!left.is_top());
    let mut right = BoundedSet::new(2);
    right.reserve(4096).unwrap();
    right.insert(3).unwrap();
    let counts = tracked(|| {
        left.join(&right).unwrap();
    });
    assert!(left.is_top());
    assert!(left.values().is_empty());
    assert_eq!(counts, (0, 0, 0));
    let mut unreserved = BoundedSet::new(1);
    assert_eq!(unreserved.insert(1), Err(Error::Capacity));
    assert!(unreserved.is_top());
    assert!(unreserved.values().is_empty());
    let mut zero = BoundedSet::<u32>::new(0);
    zero.insert(1).unwrap();
    assert!(zero.is_top());
}

#[test]
fn finite_call_arity_mismatch_rejects_and_unknown_callee_stays_open() {
    let (mut data, bounds) = fixture();
    data.methods[1].top = TopMask::NONE;
    data.methods[1].arity = 2;
    assert_eq!(
        validate(&data, bounds, Limits::default()),
        Err(Error::Arity)
    );
    data.methods[1].top = TopMask::ALL;
    validate(&data, bounds, Limits::default()).unwrap();
    assert!(matches!(
        Frame::new(
            data.methods[1],
            caller(),
            Origin::ANY,
            &[Origin::ANY],
            &[Origin::ANY],
            &[]
        ),
        Err(Error::Arity)
    ));
}

#[test]
fn wrong_signature_frame_cannot_be_reused_for_different_creation_recipe() {
    let (data, bounds) = fixture();
    let table = capsules(data, bounds);
    let view = table.view(MethodId(0)).unwrap();
    let actuals = [Origin::ANY; 2];
    let captures = [Origin::ANY];
    let mut different = view.row;
    different.top.insert(Channel::Writes);
    let frame = Frame::new(different, caller(), Origin::ANY, &actuals, &captures, &[]).unwrap();
    let mut scratch = SubstitutionScratch::default();
    scratch
        .reserve_for(view, &frame, Limits::default())
        .unwrap();
    assert!(matches!(
        substitute_into(view, &frame, &mut scratch),
        Err(Error::Malformed)
    ));
}

#[test]
fn scalar_origin_substitution_cannot_silently_rebind_callable_coordinates() {
    let (mut data, bounds) = fixture();
    data.callable_values[0] = ValueRef::argument(1);
    let table = capsules(data, bounds);
    let view = table.view(MethodId(0)).unwrap();
    let actuals = [Origin::ANY; 2];
    let captures = [Origin::ANY];
    let frame = Frame::new(view.row, caller(), Origin::ANY, &actuals, &captures, &[]).unwrap();
    let mut scratch = SubstitutionScratch::default();
    scratch
        .reserve_for(view, &frame, Limits::default())
        .unwrap();
    assert!(matches!(
        substitute_into(view, &frame, &mut scratch),
        Err(Error::Malformed)
    ));
}
