use super::*;

struct Fixture {
    facts: FactSnapshot,
    registry: Registry,
    inputs: OwnedBinaryInputs,
    class: SymbolId,
    method: SymbolId,
}

fn fixture() -> Fixture {
    let raw: Arc<[u8]> = include_bytes!("../../../fixtures/binary/classes/fixture/Probe.class")
        .to_vec()
        .into();
    let metadata = Arc::new(binary::ClassMetadata::new(raw.clone(), Limits::default()).unwrap());
    let hash = metadata.hash();
    let class_bytes = Arc::new(ClassBytes {
        bytes: raw,
        hash,
        origin: "captured.jar!/fixture/Probe.class".into(),
        metadata,
    });
    let mut builder = FactBuilder::new();
    let context = builder.intern("compile-context").unwrap();
    for (path, source, flags, source_hash) in [
        (
            "Caller.scala",
            " ".repeat(64),
            SOURCE_VERIFIED | SYNTAX_VERIFIED,
            ContentHash([1; 32]),
        ),
        (
            "captured.jar!/fixture/Probe.class",
            String::new(),
            FILE_BINARY_SOURCE,
            hash,
        ),
    ] {
        let path = builder.intern(path).unwrap();
        let source = builder.intern(&source).unwrap();
        builder.facts.files.push(FileRecord {
            path,
            source,
            revision: StrId::NONE,
            context,
            source_hash,
            flags,
        });
    }
    let class = builder
        .ensure_symbol("fixture/Probe#", FileId::NONE)
        .unwrap();
    let method = builder
        .ensure_symbol("fixture/Probe#forward().", FileId::NONE)
        .unwrap();
    let root = builder.ensure_symbol("p/root().", FileId(0)).unwrap();
    let phase = builder
        .ensure_symbol("@jvm/fixture/Probe/<class-init>", FileId(1))
        .unwrap();
    for (symbol, kind, flags) in [
        (class, 13, SYMBOL_JVM_CLASS_HEADER_VERIFIED),
        (method, 3, 0),
        (root, 3, SYMBOL_DEFINED),
        (phase, 3, SYMBOL_NATIVE_BINARY),
    ] {
        let record = &mut builder.facts.symbols[symbol.index()];
        record.kind = kind;
        record.flags = flags;
        record.context = context;
    }
    builder.facts.symbols[method.index()].owner = class;
    builder.facts.operands.extend([ValueId(2), ValueId(1)]);
    let operation = |body, opcode, target, dest, a, args| OperationRecord {
        body: BodyId(body),
        opcode,
        target,
        dest: ValueId(dest),
        a: ValueId(a),
        b: ValueId::NONE,
        arguments: args,
        span: Span::default(),
        flags: 0,
    };
    builder.facts.operations.extend([
        operation(
            0,
            Opcode::Constant,
            SymbolId::NONE,
            2,
            u32::MAX,
            IdRange::default(),
        ),
        operation(0, Opcode::LoadField, class, 1, 0, IdRange::default()),
        operation(
            0,
            Opcode::VirtualCall,
            method,
            3,
            1,
            IdRange { start: 0, len: 1 },
        ),
        operation(
            0,
            Opcode::Return,
            SymbolId::NONE,
            u32::MAX,
            3,
            IdRange::default(),
        ),
        operation(
            1,
            Opcode::Initialize,
            phase,
            u32::MAX,
            u32::MAX,
            IdRange::default(),
        ),
        operation(
            1,
            Opcode::Parameter,
            SymbolId::NONE,
            1,
            u32::MAX,
            IdRange::default(),
        ),
        operation(
            1,
            Opcode::Return,
            SymbolId::NONE,
            u32::MAX,
            1,
            IdRange::default(),
        ),
    ]);
    for (symbol, file, start, len, parameters, flags, body_hash) in [
        (
            root,
            FileId(0),
            0,
            4,
            IdRange::default(),
            0,
            ContentHash([2; 32]),
        ),
        (
            method,
            FileId(1),
            4,
            3,
            IdRange { start: 1, len: 1 },
            BODY_BINARY_RECIPE,
            hash,
        ),
        (
            phase,
            FileId(1),
            7,
            0,
            IdRange::default(),
            BODY_BINARY_RECIPE | BODY_STATIC_INITIALIZER,
            hash,
        ),
    ] {
        builder.facts.bodies.push(BodyRecord {
            symbol,
            file,
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange { start, len },
            parameters,
            body_hash,
            flags,
        });
    }
    let facts = builder.finish().unwrap();
    let registry = Registry {
        types: HashMap::from([((0, "fixture/Probe".into()), class)]),
        methods: HashMap::from([(
            MethodKey {
                context: 0,
                owner: "fixture/Probe".into(),
                name: "forward".into(),
                descriptor: "(Ljava/lang/Object;)Ljava/lang/Object;".into(),
            },
            MethodData {
                symbol: method,
                owner: class,
                flags: 0x0009,
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
    let inputs = OwnedBinaryInputs {
        identity: ContentHash([3; 32]),
        raw_identity: facts.identity,
        contexts: vec![AdmittedContext {
            id: context,
            name: "compile-context".into(),
            cache_metrics: ClassCacheMetrics::default(),
            phase: "test",
            active_method: SymbolId::NONE,
            active_file: FileId::NONE,
            pending_methods: 0,
            admission: Admission::default(),
            entries: Vec::new(),
            classes: HashMap::from([("fixture/Probe".into(), CachedClass::Found(class_bytes))]),
            shared_metadata: SharedMetadata::default(),
            java_feature: None,
            entries_at: Vec::new(),
        }],
        types: HashMap::new(),
        type_aliases: Vec::new(),
        methods: Vec::new(),
        admitted: Vec::new(),
        envelope_cache: binary::EnvelopeCache::new(0),
        platform_inputs: Vec::new(),
        platform_contexts: HashSet::new(),
    };
    Fixture {
        facts,
        registry,
        inputs,
        class,
        method,
    }
}

#[test]
fn exact_static_namespace_repair_preserves_native_entry_effects_ids_arguments_and_return() {
    let mut f = fixture();
    let before = f.facts.operations.clone();
    let operands = f.facts.operands.clone();
    let hash = f.facts.bodies[0].body_hash;
    assert_eq!(augment(&mut f.facts, &f.registry, &f.inputs).unwrap(), 1);
    let namespace = f.facts.operations[1];
    assert_eq!(
        (
            namespace.opcode,
            namespace.target,
            namespace.dest,
            namespace.a
        ),
        (
            Opcode::Constant,
            SymbolId::NONE,
            before[1].dest,
            ValueId::NONE
        )
    );
    let call = f.facts.operations[2];
    assert_eq!(
        (call.opcode, call.target, call.dest, call.a),
        (Opcode::Call, f.method, before[2].dest, before[2].a)
    );
    assert_eq!(
        (call.arguments, call.span, call.flags),
        (before[2].arguments, before[2].span, before[2].flags)
    );
    assert_eq!(f.facts.operands, operands);
    assert_eq!(
        format!("{:?}", &f.facts.operations[3..]),
        format!("{:?}", &before[3..])
    );
    assert_ne!(f.facts.bodies[0].body_hash, hash);
    f.facts.validate().unwrap();
    let after = f.facts.bodies[0].body_hash;
    assert_eq!(augment(&mut f.facts, &f.registry, &f.inputs).unwrap(), 0);
    assert_eq!(f.facts.bodies[0].body_hash, after);
}

#[test]
fn escaping_mixed_instance_partial_mutable_and_wrong_arity_values_remain_unknown() {
    for control in 0..13 {
        let mut f = fixture();
        match control {
            0 => f.facts.operations[3].a = ValueId(1), // class-literal/value escape
            1 => f.facts.operands[0] = ValueId(1),     // argument as well as receiver
            2 => f.facts.operations[2].b = ValueId(1),
            3 => f.facts.operations[2].flags = OP_SYNTHETIC_PARAMETER_APPLY,
            4 => f.facts.operations[2].arguments.len = 0,
            5 => f.facts.operations[0].dest = ValueId(1), // competing definition
            6 => f.facts.operations[2].opcode = Opcode::LoadField,
            7 => f.facts.operations[1].a = ValueId(2), // evaluated receiver expression
            8 => f.facts.symbols[f.class.index()].flags |= SYMBOL_DEFINED,
            9 => {
                f.registry
                    .methods
                    .values_mut()
                    .next()
                    .unwrap()
                    .receiver_parameter = Some(0)
            }
            10 => f.facts.symbols[f.class.index()].flags = SYMBOL_NATIVE_BINARY,
            11 => f.facts.operations[2].a = ValueId(0), // no receiver use at all
            12 => f.facts.symbols[f.class.index()].kind = 10, // Scala module
            _ => unreachable!(),
        }
        let before = format!("{:?}", f.facts.operations);
        let hash = f.facts.bodies[0].body_hash;
        assert_eq!(
            augment(&mut f.facts, &f.registry, &f.inputs).unwrap(),
            0,
            "control{control}"
        );
        assert_eq!(
            format!("{:?}", f.facts.operations),
            before,
            "control{control}"
        );
        assert_eq!(f.facts.bodies[0].body_hash, hash);
    }
}

#[test]
fn unavailable_conflicting_instance_or_incomplete_native_authority_never_repairs_a_namespace() {
    for control in 0..8 {
        let mut f = fixture();
        match control {
            0 => {
                f.inputs.contexts[0].classes.clear();
            }
            1 => {
                f.inputs.contexts[0].classes.insert(
                    "fixture/Probe".into(),
                    CachedClass::Unknown(binary::ErrorKind::MissingCode),
                );
            }
            2 => {
                f.registry.methods.values_mut().next().unwrap().flags = 0x0001;
            }
            3 => {
                f.facts.bodies[1].body_hash = ContentHash([99; 32]);
            }
            4 => {
                f.facts.bodies[1].parameters.len = 0;
            }
            5 => {
                f.facts.bodies.push(f.facts.bodies[1]);
            }
            6 => {
                f.registry.methods.insert(
                    MethodKey {
                        context: 0,
                        owner: "fixture/Probe".into(),
                        name: "self".into(),
                        descriptor: "()Ljava/lang/Object;".into(),
                    },
                    MethodData {
                        symbol: f.method,
                        owner: f.class,
                        flags: 0x0001,
                        receiver_parameter: None,
                    },
                );
            }
            7 => {
                f.facts.files[1].context = StrId::NONE;
            }
            _ => unreachable!(),
        }
        let before = format!("{:?}", f.facts.operations);
        assert_eq!(
            augment(&mut f.facts, &f.registry, &f.inputs).unwrap(),
            0,
            "control{control}"
        );
        assert_eq!(format!("{:?}", f.facts.operations), before);
    }
}

#[test]
fn every_receiver_use_must_have_independent_matching_static_authority() {
    for mixed in [false, true] {
        let mut f = fixture();
        // Two uses of one qualifier: a valid first use cannot license the
        // whole value when the second one is an instance call or escapes.
        f.facts.operations[3] = OperationRecord {
            dest: ValueId(4),
            ..f.facts.operations[2]
        };
        if mixed {
            let instance = SymbolId(f.facts.symbols.len() as u32);
            f.facts.symbols.push(f.facts.symbols[f.method.index()]);
            f.facts.operations[3].target = instance;
            f.registry.methods.insert(
                MethodKey {
                    context: 0,
                    owner: "fixture/Probe".into(),
                    name: "self".into(),
                    descriptor: "()Ljava/lang/Object;".into(),
                },
                MethodData {
                    symbol: instance,
                    owner: f.class,
                    flags: 0x0001,
                    receiver_parameter: Some(0),
                },
            );
        }
        let before = format!("{:?}", f.facts.operations);
        assert_eq!(
            augment(&mut f.facts, &f.registry, &f.inputs).unwrap(),
            usize::from(!mixed)
        );
        if mixed {
            assert_eq!(format!("{:?}", f.facts.operations), before);
        } else {
            assert_eq!(f.facts.operations[1].opcode, Opcode::Constant);
            for at in [2, 3] {
                assert_eq!(f.facts.operations[at].opcode, Opcode::Call);
                assert_eq!(f.facts.operations[at].a, ValueId(1));
            }
        }
    }
}
