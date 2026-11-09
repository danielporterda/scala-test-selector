use super::*;

struct Fixture {
    builder: FactBuilder,
    method: SymbolId,
    effect: SymbolId,
    owner: SymbolId,
    root: SymbolId,
    descriptor: String,
    parameters: u32,
}
impl Fixture {
    fn new() -> Self {
        let mut b = FactBuilder::new();
        let context = b.intern("compile-context").unwrap();
        let path = b.intern("Caller.scala").unwrap();
        let source = b.intern(&" ".repeat(256)).unwrap();
        b.facts.files.push(FileRecord {
            path,
            source,
            revision: StrId::NONE,
            context,
            source_hash: ContentHash([1; 32]),
            flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
        });
        let path = b.intern("captured.jar!/lib/Api.class").unwrap();
        let source = b.intern("").unwrap();
        b.facts.files.push(FileRecord {
            path,
            source,
            revision: StrId::NONE,
            context,
            source_hash: ContentHash([9; 32]),
            flags: FILE_BINARY_SOURCE,
        });
        let mut symbol = |name: &str, file: FileId, kind: u32, owner: SymbolId| {
            let id = b.ensure_symbol(name, file).unwrap();
            let row = &mut b.facts.symbols[id.index()];
            row.kind = kind;
            row.context = context;
            row.owner = owner;
            if !file.is_none() {
                row.flags = SYMBOL_DEFINED;
            }
            id
        };
        let owner = symbol("lib/Api#", FileId::NONE, 13, SymbolId::NONE);
        let method = symbol("lib/Api#curried().", FileId::NONE, 3, owner);
        let effect = symbol("lib/Api#effect().", FileId::NONE, 3, owner);
        let root = symbol("p/root().", FileId(0), 3, SymbolId::NONE);
        Self {
            builder: b,
            method,
            effect,
            owner,
            root,
            descriptor: "(ILjava/lang/Object;Ljava/lang/Object;)I".to_owned(),
            parameters: 3,
        }
    }
    fn op(
        &mut self,
        opcode: Opcode,
        dest: u32,
        a: u32,
        target: SymbolId,
        args: &[u32],
        flags: u32,
    ) {
        let start = self.builder.facts.operands.len() as u32;
        self.builder
            .facts
            .operands
            .extend(args.iter().copied().map(ValueId));
        let index = self.builder.facts.operations.len() as u32;
        self.builder.facts.operations.push(OperationRecord {
            body: BodyId(0),
            opcode,
            target,
            dest: ValueId(dest),
            a: ValueId(a),
            b: ValueId::NONE,
            arguments: IdRange {
                start,
                len: args.len() as u32,
            },
            span: Span {
                start: index,
                end: index + 1,
            },
            flags,
        });
    }
    fn standard(&mut self) {
        self.op(Opcode::Constant, 1, u32::MAX, SymbolId::NONE, &[], 0);
        self.op(
            Opcode::Call,
            2,
            0,
            self.method,
            &[1],
            OP_SYNTHETIC_EXACT_ORIGINAL_ARGUMENT,
        );
        self.op(Opcode::Call, 3, 0, self.effect, &[], 0);
        self.op(Opcode::Call, 4, 0, self.effect, &[], 0);
        self.op(
            Opcode::InvokeCallback,
            5,
            2,
            SymbolId::NONE,
            &[3, 4],
            OP_SYNTHETIC_PARAMETER_APPLY,
        );
        self.op(Opcode::Return, u32::MAX, 5, SymbolId::NONE, &[], 0);
    }
    fn finish(mut self) -> (FactSnapshot, Registry, SymbolId) {
        let n = self.builder.facts.operations.len() as u32;
        self.builder.facts.bodies.push(BodyRecord {
            symbol: self.root,
            file: FileId(0),
            span: Span { start: 0, end: 256 },
            name_span: Span::default(),
            operations: IdRange { start: 0, len: n },
            parameters: IdRange::default(),
            body_hash: ContentHash([3; 32]),
            flags: 0,
        });
        let start = self.builder.facts.operands.len() as u32;
        self.builder
            .facts
            .operands
            .extend((1..=self.parameters).map(ValueId));
        self.builder.facts.bodies.push(BodyRecord {
            symbol: self.method,
            file: FileId(1),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange { start: n, len: 0 },
            parameters: IdRange {
                start,
                len: self.parameters,
            },
            body_hash: ContentHash([9; 32]),
            flags: BODY_BINARY_RECIPE,
        });
        let facts = self.builder.finish().unwrap();
        let registry = Registry {
            types: HashMap::new(),
            methods: HashMap::from([(
                MethodKey {
                    context: 0,
                    owner: "lib/Api".to_owned(),
                    name: "curried".to_owned(),
                    descriptor: self.descriptor,
                },
                MethodData {
                    symbol: self.method,
                    owner: self.owner,
                    flags: 0,
                    receiver_parameter: None,
                },
            )]),
            method_events: Vec::new(),
            synthetic_methods: 0,
            fields: HashMap::new(),
            accessors: accessors::State::default(),
            files: HashMap::new(),
            empty: StrId::NONE,
            initialized: HashSet::new(),
            static_phases: HashMap::new(),
            static_active: HashSet::new(),
            bootstrap: HashMap::new(),
        };
        (facts, registry, self.method)
    }
}

#[test]
fn exact_native_arity_delays_the_call_until_all_actual_effects_and_preserves_outer_result() {
    let mut f = Fixture::new();
    f.standard();
    let (mut facts, registry, method) = f.finish();
    assert!(facts.symbols[method.index()].signature.is_none());
    let old_hash = facts.bodies[0].body_hash;
    assert_eq!(augment(&mut facts, &registry).unwrap(), 1);
    assert_eq!(facts.operations[1].opcode, Opcode::Constant);
    assert_eq!(facts.operations[1].dest, ValueId(2));
    assert!(facts.operations[1].target.is_none());
    assert_eq!(facts.operations[2].opcode, Opcode::Call);
    assert_eq!(facts.operations[3].opcode, Opcode::Call);
    let call = facts.operations[4];
    assert_eq!(
        (call.opcode, call.target, call.dest, call.a),
        (Opcode::Call, method, ValueId(5), ValueId(0))
    );
    assert_eq!(call.flags, OP_SYNTHETIC_EXACT_ORIGINAL_ARGUMENT);
    assert_eq!(call.span, Span { start: 4, end: 5 });
    assert_eq!(
        &facts.operands[call.arguments.range()],
        &[ValueId(1), ValueId(3), ValueId(4)]
    );
    assert_ne!(facts.bodies[0].body_hash, old_hash);
    let hash = facts.bodies[0].body_hash;
    assert_eq!(augment(&mut facts, &registry).unwrap(), 0);
    assert_eq!(facts.bodies[0].body_hash, hash);
    facts.validate().unwrap();
}

#[test]
fn three_clauses_fold_only_until_formal_arity_then_keep_real_function_invocation() {
    let mut f = Fixture::new();
    f.op(Opcode::Call, 2, 0, f.method, &[1], 0);
    f.op(
        Opcode::InvokeCallback,
        4,
        2,
        SymbolId::NONE,
        &[3],
        OP_SYNTHETIC_PARAMETER_APPLY,
    );
    f.op(
        Opcode::InvokeCallback,
        6,
        4,
        SymbolId::NONE,
        &[5],
        OP_SYNTHETIC_PARAMETER_APPLY,
    );
    f.op(
        Opcode::InvokeCallback,
        7,
        6,
        SymbolId::NONE,
        &[],
        OP_SYNTHETIC_PARAMETER_APPLY,
    );
    let (mut facts, registry, method) = f.finish();
    assert_eq!(augment(&mut facts, &registry).unwrap(), 1);
    assert_eq!(facts.operations[0].opcode, Opcode::Constant);
    assert_eq!(facts.operations[1].opcode, Opcode::Constant);
    assert_eq!(
        (facts.operations[2].opcode, facts.operations[2].target),
        (Opcode::Call, method)
    );
    assert_eq!(facts.operations[3].opcode, Opcode::InvokeCallback);
    assert_eq!(facts.operations[3].a, ValueId(6));
    facts.validate().unwrap();
}

#[test]
fn an_already_saturated_method_returning_a_function_is_not_reassembled() {
    let mut f = Fixture::new();
    f.parameters = 1;
    f.descriptor = "(I)Ljava/lang/Runnable;".into();
    f.standard();
    let (mut facts, registry, _) = f.finish();
    assert_eq!(augment(&mut facts, &registry).unwrap(), 0);
    assert_eq!(facts.operations[1].opcode, Opcode::Call);
    assert_eq!(facts.operations[4].opcode, Opcode::InvokeCallback);
    assert_eq!(facts.bodies[0].body_hash, ContentHash([3; 32]));
}

#[test]
fn untagged_mixed_overfull_incomplete_and_zero_argument_chains_stay_unchanged() {
    for case in 0..5 {
        let mut f = Fixture::new();
        f.standard();
        let op = &mut f.builder.facts.operations[4];
        match case {
            0 => op.flags = 0,
            1 => op.target = f.effect,
            2 => {
                let start = f.builder.facts.operands.len() as u32;
                f.builder
                    .facts
                    .operands
                    .extend([ValueId(3), ValueId(4), ValueId(1)]);
                op.arguments = IdRange { start, len: 3 };
            }
            3 => op.arguments.len = 1,
            _ => op.arguments.len = 0,
        }
        let (mut facts, registry, _) = f.finish();
        assert_eq!(augment(&mut facts, &registry).unwrap(), 0, "case {case}");
        assert_eq!(facts.operations[1].opcode, Opcode::Call);
        assert_eq!(facts.operations[4].opcode, Opcode::InvokeCallback);
    }
}

#[test]
fn escapes_redefinitions_and_intervening_argument_reassignments_prevent_folding() {
    for case in 0..3 {
        let mut f = Fixture::new();
        f.standard();
        match case {
            0 => f.op(Opcode::Return, u32::MAX, 2, SymbolId::NONE, &[], 0),
            1 => f.op(Opcode::Constant, 2, u32::MAX, SymbolId::NONE, &[], 0),
            _ => {
                f.builder.facts.operations[2].opcode = Opcode::Constant;
                f.builder.facts.operations[2].dest = ValueId(1);
            }
        }
        let (mut facts, registry, _) = f.finish();
        assert_eq!(augment(&mut facts, &registry).unwrap(), 0, "case {case}");
        assert_eq!(facts.operations[1].opcode, Opcode::Call);
    }
}

#[test]
fn missing_unverified_mismatched_or_ambiguous_native_authority_cannot_supply_arity() {
    for case in 0..6 {
        let mut f = Fixture::new();
        f.standard();
        let (mut facts, mut registry, method) = f.finish();
        match case {
            0 => registry.methods.clear(),
            1 => facts.bodies[1].flags = 0,
            2 => facts.files[1].flags = 0,
            3 => facts.bodies[1].parameters.len = 2,
            4 => facts.bodies[1].body_hash = ContentHash([8; 32]),
            _ => {
                let (key, data) = registry.methods.iter().next().unwrap();
                let mut key = key.clone();
                key.name = "other".into();
                let data = data.clone();
                registry.methods.insert(key, data);
            }
        }
        assert_eq!(
            augment(&mut facts, &registry).unwrap(),
            0,
            "case {case}, {method:?}"
        );
        assert_eq!(facts.operations[1].opcode, Opcode::Call);
    }
}

#[test]
fn static_trait_receiver_is_excluded_from_admitted_formal_count() {
    let mut f = Fixture::new();
    f.standard();
    f.descriptor = "(Llib/Api;ILjava/lang/Object;Ljava/lang/Object;)I".into();
    let (mut facts, mut registry, _) = f.finish();
    let data = registry.methods.values_mut().next().unwrap();
    data.flags = 8;
    data.receiver_parameter = Some(0);
    assert_eq!(augment(&mut facts, &registry).unwrap(), 1);
}

#[test]
fn exact_operation_result_bounds_move_to_the_actual_call_and_are_resorted() {
    let mut f = Fixture::new();
    f.standard();
    // A second complete call to the same method evaluates an implicit actual.
    f.builder.facts.operations[2].target = f.method;
    let (mut facts, registry, method) = f.finish();
    facts
        .bound_classes
        .push(facts.symbols[method.index()].owner);
    facts
        .result_bounds
        .extend([1, 2].map(|operation| ResultBoundRecord {
            symbol: method,
            operation: OperationId(operation),
            classes: IdRange { start: 0, len: 1 },
        }));
    facts.validate().unwrap();
    assert_eq!(augment(&mut facts, &registry).unwrap(), 1);
    assert_eq!(
        facts
            .result_bounds
            .iter()
            .map(|row| row.operation)
            .collect::<Vec<_>>(),
        [OperationId(2), OperationId(4)]
    );
    facts.validate().unwrap();
}

#[test]
fn body_hash_is_deterministic_and_independent_of_unrelated_operand_pool_offsets() {
    let make = || {
        let mut f = Fixture::new();
        f.standard();
        f.finish()
    };
    let (mut a, ar, _) = make();
    let (mut b, br, _) = make();
    b.operands.push(ValueId(99));
    assert_eq!(augment(&mut a, &ar).unwrap(), 1);
    assert_eq!(augment(&mut b, &br).unwrap(), 1);
    assert_eq!(a.bodies[0].body_hash, b.bodies[0].body_hash);
    assert_ne!(
        a.operations[4].arguments.start,
        b.operations[4].arguments.start
    );
}

#[test]
fn relocated_source_coordinates_preserve_semantic_hash_and_operation_evidence() {
    let make = || {
        let mut fixture = Fixture::new();
        fixture.standard();
        fixture.finish()
    };
    let (mut before, before_registry, _) = make();
    let (mut after, after_registry, _) = make();
    for op in &mut after.operations {
        if op.body == BodyId(0) {
            op.span.start += 17;
            op.span.end += 17;
        }
    }
    after.bodies[0].span.start += 17;
    after.bodies[0].span.end += 17;
    after.bodies[0].name_span = Span { start: 17, end: 18 };
    after.files[0].source_hash = ContentHash([7; 32]);
    assert_eq!(augment(&mut before, &before_registry).unwrap(), 1);
    assert_eq!(augment(&mut after, &after_registry).unwrap(), 1);
    assert_eq!(before.bodies[0].body_hash, after.bodies[0].body_hash);
    assert_ne!(before.operations[4].span, after.operations[4].span);
    for (left, right) in before.operations.iter().zip(&after.operations) {
        assert_eq!(left.opcode, right.opcode);
        assert_eq!(left.dest, right.dest);
        assert_eq!(left.a, right.a);
        assert_eq!(left.target, right.target);
        assert_eq!(
            before.operands[left.arguments.range()],
            after.operands[right.arguments.range()]
        );
    }
}

#[test]
fn relocated_coordinates_do_not_hide_changed_owned_body_or_jvm_authority() {
    let make = || {
        let mut fixture = Fixture::new();
        fixture.standard();
        fixture.finish()
    };
    let (mut reference, registry, _) = make();
    assert_eq!(augment(&mut reference, &registry).unwrap(), 1);
    for changed_authority in [false, true] {
        let (mut candidate, registry, _) = make();
        if changed_authority {
            candidate.files[1].source_hash = ContentHash([8; 32]);
            candidate.bodies[1].body_hash = ContentHash([8; 32]);
        } else {
            candidate.bodies[0].body_hash = ContentHash([4; 32]);
        }
        assert_eq!(augment(&mut candidate, &registry).unwrap(), 1);
        assert_ne!(reference.bodies[0].body_hash, candidate.bodies[0].body_hash);
    }
}
