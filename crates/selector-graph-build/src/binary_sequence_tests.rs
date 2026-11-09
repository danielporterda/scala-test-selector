use super::*;

fn fixture() -> (FactSnapshot, Registry, OwnedBinaryInputs, SymbolId) {
    let bytes: Arc<[u8]> =
        Arc::from(&include_bytes!("../../../fixtures/sequence-element-view/SeqOps.class")[..]);
    let metadata = Arc::new(binary::ClassMetadata::new(bytes.clone(), Limits::default()).unwrap());
    assert_eq!(
        metadata.hash().to_string(),
        "ac7eaf9dae947a982779b58caa14adab07d17e7ef1d003b9c274bf53b97672eb"
    );
    let flags = metadata.method("apply", Some(DESCRIPTOR)).unwrap().flags;
    let class = Arc::new(ClassBytes {
        hash: metadata.hash(),
        bytes,
        metadata,
        origin: "selected-scala-library.jar!/scala/collection/SeqOps.class".into(),
    });
    let mut b = FactBuilder::new();
    let context = b.intern("exact-context").unwrap();
    let path = b.intern("Caller.scala").unwrap();
    let source = b.intern(&" ".repeat(128)).unwrap();
    b.facts.files.push(FileRecord {
        path,
        source,
        revision: StrId::NONE,
        context,
        source_hash: ContentHash([1; 32]),
        flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
    });
    let owner = b
        .ensure_global_symbol("scala/collection/SeqOps#", context)
        .unwrap();
    b.facts.symbols[owner.index()].kind = 14;
    let method = b.ensure_global_symbol(COMPILER, context).unwrap();
    b.facts.symbols[method.index()].kind = 3;
    b.facts.symbols[method.index()].owner = owner;
    let root = b.ensure_symbol("p/root().", FileId(0)).unwrap();
    b.facts.symbols[root.index()].kind = 3;
    b.facts.symbols[root.index()].flags = SYMBOL_DEFINED;
    b.facts.operands.push(ValueId(0));
    b.facts.operations.push(OperationRecord {
        body: BodyId(0),
        opcode: Opcode::VirtualCall,
        target: method,
        dest: ValueId(1),
        a: ValueId(0),
        b: ValueId::NONE,
        arguments: IdRange { start: 0, len: 1 },
        span: Span { start: 20, end: 21 },
        flags: 0,
    });
    b.facts.bodies.push(BodyRecord {
        symbol: root,
        file: FileId(0),
        span: Span {
            start: 10,
            end: 100,
        },
        name_span: Span { start: 4, end: 8 },
        operations: IdRange { start: 0, len: 1 },
        parameters: IdRange::default(),
        body_hash: ContentHash([2; 32]),
        flags: 0,
    });
    let facts = b.finish().unwrap();
    let registry = Registry {
        types: HashMap::new(),
        methods: HashMap::from([(
            MethodKey {
                context: 0,
                owner: OWNER.into(),
                name: "apply".into(),
                descriptor: DESCRIPTOR.into(),
            },
            MethodData {
                symbol: method,
                owner,
                flags,
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
            name: "exact-context".into(),
            cache_metrics: ClassCacheMetrics::default(),
            phase: "test",
            active_method: SymbolId::NONE,
            active_file: FileId::NONE,
            pending_methods: 0,
            admission: Admission::default(),
            entries: Vec::new(),
            classes: HashMap::from([(OWNER.into(), CachedClass::Found(class))]),
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
    (facts, registry, inputs, method)
}

#[test]
fn actual_selected_seqops_descriptor_adds_only_a_guarded_view_certificate() {
    let (mut facts, registry, inputs, _) = fixture();
    let before = facts.operations[0];
    let hash = facts.bodies[0].body_hash;
    assert_eq!(augment(&mut facts, &registry, &inputs).unwrap(), 1);
    let after = facts.operations[0];
    assert_eq!(
        (
            after.opcode,
            after.target,
            after.dest,
            after.a,
            after.arguments,
            after.span
        ),
        (
            before.opcode,
            before.target,
            before.dest,
            before.a,
            before.arguments,
            before.span
        )
    );
    assert_eq!(after.flags, before.flags | OP_SEQUENCE_ELEMENT_VIEW);
    assert_ne!(facts.bodies[0].body_hash, hash);
    assert!(facts.issues.is_empty());
    facts.validate().unwrap();
    let (mut moved, registry, inputs, _) = fixture();
    moved.operations[0].span = Span { start: 75, end: 76 };
    assert_eq!(augment(&mut moved, &registry, &inputs).unwrap(), 1);
    assert_eq!(
        moved.bodies[0].body_hash, facts.bodies[0].body_hash,
        "absolute source spans are not semantic authority"
    );
}

#[test]
fn missing_or_competing_descriptor_class_context_or_call_shape_keeps_native_only() {
    for control in 0..10 {
        let (mut facts, mut registry, mut inputs, method) = fixture();
        match control {
            0 => {
                let (key, data) = registry.methods.drain().next().unwrap();
                registry.methods.insert(
                    MethodKey {
                        descriptor: "(J)Ljava/lang/Object;".into(),
                        ..key
                    },
                    data,
                );
            }
            1 => {
                let (key, data) = registry.methods.drain().next().unwrap();
                registry.methods.insert(
                    MethodKey {
                        owner: "shadow/SeqOps".into(),
                        ..key
                    },
                    data,
                );
            }
            2 => inputs.contexts[0].classes.clear(),
            3 => inputs.contexts[0].id = StrId::NONE,
            4 => {
                let CachedClass::Found(class) = inputs.contexts[0].classes.get_mut(OWNER).unwrap()
                else {
                    unreachable!()
                };
                Arc::get_mut(class).unwrap().hash = ContentHash([9; 32]);
            }
            5 => {
                let (_, data) = registry.methods.iter().next().unwrap();
                registry.methods.insert(
                    MethodKey {
                        context: 0,
                        owner: OWNER.into(),
                        name: "apply".into(),
                        descriptor: "(J)Ljava/lang/Object;".into(),
                    },
                    data.clone(),
                );
            }
            6 => facts.operations[0].flags = OP_SYNTHETIC_PARAMETER_APPLY,
            7 => facts.operations[0].a = ValueId::NONE,
            8 => facts.operations[0].arguments.len = 0,
            9 => {
                facts.symbols[method.index()].name =
                    facts.symbols[facts.bodies[0].symbol.index()].name
            }
            _ => unreachable!(),
        }
        assert_eq!(
            augment(&mut facts, &registry, &inputs).unwrap(),
            0,
            "control{control}"
        );
        assert_eq!(
            facts.operations[0].flags & OP_SEQUENCE_ELEMENT_VIEW,
            0,
            "control{control}"
        );
    }
}
