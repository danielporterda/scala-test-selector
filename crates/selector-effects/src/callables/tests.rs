use super::*;

fn row(index: u32, arity: u32, captures: u32, locals: u32) -> MethodRow {
    MethodRow {
        top: TopMask::NONE,
        locals,
        ..MethodRow::unknown(
            SubjectRef {
                kind: SubjectKind::FactNode,
                index,
            },
            0,
            arity,
            captures,
            0,
        )
    }
}
fn program() -> Capsules {
    let mut factory = row(0, 1, 0, 1);
    factory.creations = Range { start: 0, len: 1 };
    factory.value_flows = Range { start: 0, len: 1 };
    let mut body = row(1, 0, 1, 0);
    body.calls = Range { start: 0, len: 1 };
    let callback = row(2, 0, 0, 0);
    let mut caller = row(3, 0, 0, 2);
    caller.creations = Range { start: 1, len: 1 };
    caller.calls = Range { start: 1, len: 2 };
    let data = CapsuleData {
        methods: vec![factory, body, callback, caller],
        sam_arities: vec![0],
        origins: vec![Origin::argument(0), Origin::ANY],
        callable_values: vec![ValueRef::argument(0), ValueRef::local(0)],
        creations: vec![
            CallableCreation {
                site: 0,
                destination: 0,
                implementation: MethodId(1),
                sam: 0,
                receiver: Origin::ANY,
                receiver_value: ValueRef::UNKNOWN,
                captures: Range { start: 0, len: 1 },
            },
            CallableCreation {
                site: 1,
                destination: 0,
                implementation: MethodId(2),
                sam: 0,
                receiver: Origin::ANY,
                receiver_value: ValueRef::UNKNOWN,
                captures: Range::EMPTY,
            },
        ],
        calls: vec![
            CallRow {
                site: 2,
                target: CallTarget::Callable {
                    value: ValueRef::capture(0),
                    sam: 0,
                },
                kind: CallKind::Callback,
                receiver: Origin::ANY,
                receiver_value: ValueRef::UNKNOWN,
                result: NONE,
                arguments: Range::EMPTY,
                captures: Range::EMPTY,
            },
            CallRow {
                site: 3,
                target: CallTarget::Direct(MethodId(0)),
                kind: CallKind::Static,
                receiver: Origin::ANY,
                receiver_value: ValueRef::CONSTANT,
                result: 1,
                arguments: Range { start: 1, len: 1 },
                captures: Range::EMPTY,
            },
            CallRow {
                site: 4,
                target: CallTarget::Callable {
                    value: ValueRef::local(1),
                    sam: 0,
                },
                kind: CallKind::Callback,
                receiver: Origin::ANY,
                receiver_value: ValueRef::UNKNOWN,
                result: NONE,
                arguments: Range::EMPTY,
                captures: Range::EMPTY,
            },
        ],
        value_flows: vec![ValueFlow {
            kind: ValueFlowKind::Return,
            value: ValueRef::local(0),
            index: 0,
        }],
        ..Default::default()
    };
    Capsules::new(
        data,
        RefBounds {
            fact_nodes: 4,
            authorities: 1,
            sites: 5,
            sams: 1,
            ..Default::default()
        },
        Limits::default(),
    )
    .unwrap()
}
fn cells(seeds: &[CellSeed], targets: u32) -> CallableCells {
    let mut bank = CallableCells::default();
    bank.reserve(seeds.len(), 64, targets, 8192).unwrap();
    bank.reset(seeds).unwrap();
    bank
}

#[test]
fn factory_returned_closure_preserves_captured_callback_after_heap_origin_widens() {
    let p = program();
    // Payload0 = safe lexical callback (template1). Payload1 = factory closure
    // (template0) with capture pointing to cell1 in its DEFINING frame.
    let mut bank = cells(&[CellSeed::Pending; 6], 4);
    bank.add_payload(CellId(0), 0).unwrap();
    bank.join(CellId(1), CellId(0)).unwrap(); // factory formal/capture dataflow
    bank.add_payload(CellId(2), 1).unwrap(); // factory creation, not invocation
    bank.join(CellId(3), CellId(2)).unwrap(); // return→call result
    bank.join(CellId(4), CellId(3)).unwrap(); // store→canonical heap
    bank.load_heap(CellId(5), Some(CellId(4))).unwrap();
    let heap_origin = Origin::ANY;
    assert_eq!(heap_origin, Origin::ANY);
    let mut methods = Vec::new();
    let complete = bank
        .visit_invocations(
            CellId(5),
            0,
            &p,
            |payload| Some(if payload == 1 { 0 } else { 1 }),
            |payload, row| {
                methods.push((payload, row.implementation));
            },
        )
        .unwrap();
    assert!(complete);
    assert_eq!(methods, vec![(1, MethodId(1))]);
    methods.clear();
    assert!(
        bank.visit_invocations(
            CellId(1),
            0,
            &p,
            |_| Some(1),
            |payload, row| methods.push((payload, row.implementation))
        )
        .unwrap()
    );
    assert_eq!(methods, vec![(0, MethodId(2))]);
}

#[test]
fn identical_template_different_capture_frames_survive_shared_heap() {
    let p = program();
    let mut bank = cells(&[CellSeed::Pending; 4], 4);
    bank.add_payload(CellId(0), 10).unwrap();
    bank.add_payload(CellId(1), 11).unwrap();
    bank.join(CellId(2), CellId(0)).unwrap();
    bank.join(CellId(2), CellId(1)).unwrap();
    bank.load_heap(CellId(3), Some(CellId(2))).unwrap();
    let mut seen = Vec::new();
    assert!(
        bank.visit_invocations(
            CellId(3),
            0,
            &p,
            |payload| (payload == 10 || payload == 11).then_some(0),
            |payload, _| seen.push(payload)
        )
        .unwrap()
    );
    seen.sort_unstable();
    assert_eq!(seen, [10, 11]);
}

#[test]
fn unknown_noncallable_unproduced_and_sam_mismatch_never_mean_no_execution() {
    let p = program();
    let mut bank = cells(
        &[
            CellSeed::Unknown,
            CellSeed::NonCallable,
            CellSeed::Pending,
            CellSeed::Pending,
        ],
        4,
    );
    for id in [0, 1, 2] {
        assert!(
            !bank
                .visit_invocations(
                    CellId(id),
                    0,
                    &p,
                    |x| Some(x),
                    |_, _| panic!("no known target")
                )
                .unwrap()
        );
    }
    bank.add_payload(CellId(3), 1).unwrap();
    assert!(
        !bank
            .visit_invocations(
                CellId(3),
                NONE,
                &p,
                |_| Some(0),
                |_, _| panic!("missing SAM")
            )
            .unwrap()
    );
    assert!(
        !bank
            .visit_invocations(
                CellId(3),
                1,
                &p,
                |_| Some(0),
                |_, _| panic!("mismatched SAM")
            )
            .unwrap()
    );
    assert!(
        !bank
            .visit_invocations(CellId(3), 0, &p, |_| None, |_, _| panic!("missing payload"))
            .unwrap()
    );
}

#[test]
fn creation_is_dormant_and_capture_cycles_converge_without_recursive_payloads() {
    let p = program();
    assert_eq!(p.view(MethodId(0)).unwrap().calls.len(), 0);
    let mut bank = cells(&[CellSeed::Pending; 3], 4);
    bank.add_payload(CellId(0), 7).unwrap();
    assert!(bank.join(CellId(1), CellId(0)).unwrap());
    assert!(bank.join(CellId(2), CellId(1)).unwrap());
    assert!(!bank.join(CellId(0), CellId(2)).unwrap());
    assert_eq!(
        bank.payloads(CellId(2)).unwrap().collect::<Vec<_>>(),
        vec![7]
    );
}

#[test]
fn overflow_is_unknown_and_missing_heap_never_uses_coincidental_local_ordinal() {
    let mut bank = cells(&[CellSeed::Pending; 3], 1);
    bank.add_payload(CellId(0), 0).unwrap();
    bank.add_payload(CellId(0), 1).unwrap();
    assert!(bank.is_unknown(CellId(0)).unwrap());
    bank.add_payload(CellId(1), 4).unwrap();
    bank.load_heap(CellId(2), None).unwrap();
    assert!(bank.is_unknown(CellId(2)).unwrap());
    assert!(!bank.is_complete_callable(CellId(2)).unwrap());
    let locals = [CellValue::Cell(CellId(1))];
    let frame = ValueFrame {
        method: MethodId(3),
        receiver: CellValue::Unknown,
        arguments: &[],
        captures: &[],
        locals: &locals,
    };
    assert_eq!(
        frame.resolve(MethodId(2), ValueRef::local(0)),
        Err(Error::Malformed)
    );
    assert_eq!(
        frame.resolve(MethodId(3), ValueRef::local(1)),
        Err(Error::Bounds)
    );
}

#[test]
fn all_callable_coordinates_are_scoped_to_the_owning_method() {
    let p = program();
    let original = p.data();
    let bounds = p.bounds();
    let mutations: &[fn(&mut CapsuleData)] = &[
        |d| d.creations[0].destination = 1,
        |d| d.callable_values[0] = ValueRef::argument(1),
        |d| d.calls[1].result = 2,
        |d| {
            d.calls[2].target = CallTarget::Callable {
                value: ValueRef::local(2),
                sam: 0,
            }
        },
        |d| d.value_flows[0].value = ValueRef::local(1),
        |d| d.callable_values[0] = ValueRef::local(1),
        |d| d.sam_arities[0] = 1,
    ];
    for mutation in mutations {
        let mut d = original.clone();
        mutation(&mut d);
        assert!(validate(&d, bounds, Limits::default()).is_err());
    }
    let mut d = original.clone();
    d.callable_values.pop();
    assert_eq!(
        validate(&d, bounds, Limits::default()),
        Err(Error::Malformed)
    );
}

#[test]
fn unknown_heap_and_overflow_retain_known_effect_alternatives() {
    let p = program();
    let mut bank = cells(&[CellSeed::Unknown, CellSeed::Pending], 1);
    assert!(bank.add_payload(CellId(0), 1).unwrap());
    assert!(bank.join(CellId(1), CellId(0)).unwrap());
    let mut targets = Vec::new();
    assert!(
        !bank
            .visit_invocations(
                CellId(1),
                0,
                &p,
                |_| Some(1),
                |payload, row| targets.push((payload, row.implementation))
            )
            .unwrap()
    );
    assert_eq!(targets, vec![(1, MethodId(2))]);
    bank.add_payload(CellId(1), 2).unwrap();
    assert!(bank.is_unknown(CellId(1)).unwrap());
    assert_eq!(
        bank.payloads(CellId(1)).unwrap().collect::<Vec<_>>(),
        vec![1]
    );
}

#[test]
fn warmed_payload_transport_and_resolution_allocate_zero() {
    let p = program();
    let mut bank = cells(&[CellSeed::Pending; 3], 4);
    bank.add_payload(CellId(0), 1).unwrap();
    bank.join(CellId(1), CellId(0)).unwrap();
    bank.load_heap(CellId(2), Some(CellId(1))).unwrap();
    let bytes = bank.owned_bytes();
    let mut count = 0;
    let result = crate::tests::tracked(|| {
        for _ in 0..100_000 {
            assert!(!bank.join(CellId(1), CellId(0)).unwrap());
            assert!(!bank.load_heap(CellId(2), Some(CellId(1))).unwrap());
            assert!(
                bank.visit_invocations(CellId(2), 0, &p, |_| Some(0), |_, _| count += 1)
                    .unwrap()
            );
        }
    });
    assert_eq!(count, 100_000);
    assert_eq!(result, (0, 0, 0));
    assert_eq!(bank.owned_bytes(), bytes);
}

#[test]
fn callable_bank_budget_rejects_before_any_capacity_growth() {
    let mut bank = CallableCells::default();
    let result =
        crate::tests::tracked(|| assert_eq!(bank.reserve(100, 100, 4, 1), Err(Error::Budget)));
    assert_eq!(result, (0, 0, 0));
    assert_eq!(bank.owned_bytes(), 0);
}

#[test]
fn sparse_cells_obey_declared_limit_and_never_grow_during_admission() {
    let mut bank = CallableCells::default();
    bank.reserve(1, 4, 2, 4096).unwrap();
    bank.reset(&[]).unwrap();
    let bytes = bank.owned_bytes();
    let allocations = crate::tests::tracked(|| {
        assert_eq!(bank.push_seed(CellSeed::Unknown), Ok(CellId(0)));
        assert_eq!(bank.push_seed(CellSeed::Pending), Err(Error::Capacity));
    });
    assert_eq!(bank.len(), 1);
    assert!(!bank.is_empty());
    assert!(bank.is_unknown(CellId(0)).unwrap());
    assert_eq!(allocations, (0, 0, 0));
    assert_eq!(bank.owned_bytes(), bytes);
}

fn bridge_program() -> (CapsuleData, RefBounds) {
    let mut factory = row(0, 1, 0, 3);
    factory.creations = Range { start: 0, len: 3 };
    let generic = row(1, 0, 1, 0);
    let specialized = row(2, 0, 1, 0);
    let mut discard = row(0, 0, 0, 0);
    discard.subject.kind = SubjectKind::ForeignMethod;
    discard.calls = Range { start: 0, len: 1 };
    let mut boxed = row(1, 0, 0, 0);
    boxed.subject.kind = SubjectKind::ForeignMethod;
    boxed.calls = Range { start: 1, len: 1 };
    boxed.reads = Range { start: 0, len: 1 };
    boxed.initializes = Range { start: 0, len: 1 };
    let phase = MethodRow::unknown(
        SubjectRef {
            kind: SubjectKind::RuntimePhase,
            index: 0,
        },
        0,
        0,
        0,
        0,
    );
    let creation = CallableCreation {
        site: 0,
        destination: 0,
        implementation: MethodId(1),
        sam: 0,
        receiver: Origin::argument(0),
        receiver_value: ValueRef::argument(0),
        captures: Range { start: 0, len: 1 },
    };
    let invoke = |site, sam| CallRow {
        site,
        target: CallTarget::Callable {
            value: ValueRef::RECEIVER,
            sam,
        },
        kind: CallKind::Callback,
        receiver: Origin::RECEIVER,
        receiver_value: ValueRef::RECEIVER,
        result: NONE,
        arguments: Range::EMPTY,
        captures: Range::EMPTY,
    };
    let data = CapsuleData {
        methods: vec![factory, generic, specialized, discard, boxed, phase],
        sam_arities: vec![0, 0],
        origins: vec![
            Origin::argument(0),
            Origin::argument(0),
            Origin::argument(0),
        ],
        callable_values: vec![ValueRef::argument(0); 3],
        creations: vec![
            creation,
            CallableCreation {
                site: 1,
                destination: 1,
                implementation: MethodId(2),
                sam: 1,
                captures: Range { start: 1, len: 1 },
                ..creation
            },
            // Same SAM/arity, but this distinct creator has no default proof.
            CallableCreation {
                site: 2,
                destination: 2,
                captures: Range { start: 2, len: 1 },
                ..creation
            },
        ],
        callable_bridges: vec![
            CallableBridge {
                creation: 0,
                sam: 1,
                implementation: MethodId(3),
                proof: 0,
            },
            CallableBridge {
                creation: 1,
                sam: 0,
                implementation: MethodId(4),
                proof: 1,
            },
        ],
        calls: vec![invoke(3, 0), invoke(4, 1)],
        reads: vec![StorageRef {
            kind: StorageKind::StaticField,
            member: 0,
            base: Origin::ANY,
        }],
        initializes: vec![MethodId(5)],
        ..Default::default()
    };
    let bounds = RefBounds {
        fact_nodes: 3,
        foreign_methods: 2,
        authorities: 1,
        sites: 5,
        sams: 2,
        members: 1,
        bridge_proofs: 2,
        phases: 1,
        ..Default::default()
    };
    (data, bounds)
}

#[test]
fn default_bridges_are_creation_specific_and_preserve_both_real_method_routes() {
    let (data, bounds) = bridge_program();
    let p = Capsules::new(data, bounds, Limits::default()).unwrap();
    for (creation, requested, expected, route) in [
        (0, 0, 1, InvocationRoute::Implementation),
        (0, 1, 3, InvocationRoute::DefaultBridge),
        (1, 1, 2, InvocationRoute::Implementation),
        (1, 0, 4, InvocationRoute::DefaultBridge),
    ] {
        assert_eq!(
            p.resolve_callable_invocation(creation, requested).unwrap(),
            Some(CallableInvocation {
                creation,
                implementation: MethodId(expected),
                route
            })
        );
    }
    assert_eq!(p.resolve_callable_invocation(2, 1), Ok(None));
    assert_eq!(p.resolve_callable_invocation(0, NONE), Ok(None));
    assert_eq!(p.resolve_callable_invocation(NONE, 0), Err(Error::Bounds));
    assert_eq!(p.resolve_callable_invocation(0, 2), Err(Error::Bounds));
    let boxed = p.view(MethodId(4)).unwrap();
    assert_eq!(boxed.reads.len(), 1); // inverse default still reads BoxedUnit
    assert_eq!(boxed.initializes, &[MethodId(5)]);
    assert_eq!(p.view(boxed.initializes[0]).unwrap().row.top, TopMask::ALL);
    // The bridge forwards its callable RECEIVER, not the creator's lexical
    // receiver (Argument0), then the original invocation recovers capture0.
    assert_eq!(boxed.calls[0].receiver_value, ValueRef::RECEIVER);
    assert_eq!(boxed.row.captures, 0);
    assert_eq!(p.view(MethodId(2)).unwrap().row.captures, 1);
}

#[test]
fn bridge_admission_rejects_duplicate_missing_proof_and_incompatible_frames() {
    for change in 0..9 {
        let (mut data, mut bounds) = bridge_program();
        match change {
            0 => data.callable_bridges.push(data.callable_bridges[0]),
            1 => data.callable_bridges[0].proof = bounds.bridge_proofs,
            2 => data.callable_bridges[0].sam = 0,
            3 => data.callable_bridges[0].creation = 3,
            4 => data.methods[3].captures = 1,
            5 => data.methods[3].arity = 1,
            6 => data.callable_bridges[0].implementation = MethodId(1),
            7 => data.creations[0].sam = NONE,
            _ => bounds.sams = 1,
        }
        assert!(
            Capsules::new(data, bounds, Limits::default()).is_err(),
            "case {change}"
        );
    }
    let (data, bounds) = bridge_program();
    let bytes = data.owned_bytes().unwrap();
    assert_eq!(std::mem::size_of::<CallableBridge>(), 16);
    assert!(matches!(
        Capsules::new(
            data,
            bounds,
            Limits {
                max_bytes: bytes - 1,
                ..Limits::default()
            }
        ),
        Err(Error::Budget)
    ));
}

#[test]
fn warm_default_bridge_activation_is_allocation_free_and_keeps_unknown_lower_bounds() {
    let (data, bounds) = bridge_program();
    let p = Capsules::new(data, bounds, Limits::default()).unwrap();
    let mut bank = cells(&[CellSeed::Pending; 2], 4);
    bank.add_payload(CellId(0), 7).unwrap();
    bank.add_payload(CellId(1), 8).unwrap();
    bank.set_unknown(CellId(1)).unwrap();
    let bytes = bank.owned_bytes();
    let mut visits = 0;
    let allocations = crate::tests::tracked(|| {
        for _ in 0..100_000 {
            assert!(
                bank.visit_invocations(
                    CellId(0),
                    1,
                    &p,
                    |_| Some(0),
                    |payload, call| {
                        assert_eq!(payload, 7);
                        assert_eq!(call.route, InvocationRoute::DefaultBridge);
                        visits += 1;
                    }
                )
                .unwrap()
            );
            assert!(
                !bank
                    .visit_invocations(
                        CellId(1),
                        0,
                        &p,
                        |_| Some(1),
                        |payload, call| {
                            assert_eq!(payload, 8);
                            assert_eq!(call.implementation, MethodId(4));
                            visits += 1;
                        }
                    )
                    .unwrap()
            );
        }
    });
    assert_eq!(visits, 200_000);
    assert_eq!(allocations, (0, 0, 0));
    assert_eq!(bank.owned_bytes(), bytes);
}

#[test]
fn runtime_phases_remain_open_and_keep_known_initialization_lower_bounds() {
    let (mut data, bounds) = bridge_program();
    data.methods[5].initializes = Range { start: 1, len: 1 };
    data.initializes.push(MethodId(3));
    data.methods[5].code_observations = Range { start: 0, len: 1 };
    data.code_observations.push(CodeRef {
        kind: CodeKind::Method,
        index: 3,
    });
    let p = Capsules::new(data.clone(), bounds, Limits::default()).unwrap();
    let phase = p.view(MethodId(5)).unwrap();
    assert_eq!(phase.row.top, TopMask::ALL);
    assert_eq!(phase.initializes, &[MethodId(3)]);
    assert_eq!(phase.code_observations[0].index, 3);
    for change in 0..5 {
        let mut bad = data.clone();
        match change {
            0 => bad.methods[5].top = TopMask::NONE,
            1 => bad.methods[5].arity = 1,
            2 => bad.methods[5].locals = 1,
            3 => bad.methods[5].reads = Range { start: 0, len: 1 },
            _ => bad.methods[5].subject.index = bounds.phases,
        }
        assert!(Capsules::new(bad, bounds, Limits::default()).is_err());
    }
}
