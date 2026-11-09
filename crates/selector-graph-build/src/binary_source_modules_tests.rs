use super::*;

const OWNER: &str = "selectedexternal/Configuration#";
const MODULE: &str = "selectedexternal/Configuration#PatienceConfig.";
const METHOD: &str = "selectedexternal/Configuration#PatienceConfig.apply(+1).";

fn fixture() -> (FactSnapshot, SymbolId) {
    let mut b = FactBuilder::new();
    let context = b.intern("compile").unwrap();
    let path = b.intern("Calls.scala").unwrap();
    let source = b
        .intern("class Calls extends Configuration { PatienceConfig }")
        .unwrap();
    b.facts.files.push(FileRecord {
        path,
        source,
        revision: StrId::NONE,
        context,
        source_hash: ContentHash([1; 32]),
        flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
    });
    let owner = b.ensure_symbol(OWNER, FileId::NONE).unwrap();
    let module = b.ensure_symbol(MODULE, FileId::NONE).unwrap();
    let method = b.ensure_symbol(METHOD, FileId::NONE).unwrap();
    let root = b
        .ensure_symbol("selectedexternal/Calls#read().", FileId(0))
        .unwrap();
    for id in [owner, module, method, root] {
        b.facts.symbols[id.index()].context = context;
    }
    b.facts.symbols[module.index()].owner = owner;
    b.facts.symbols[method.index()].owner = module;
    b.facts.symbols[method.index()].kind = 3;
    let mut clauses = Vec::new();
    for name in ["timeout", "interval"] {
        let name = format!("{METHOD}({name})");
        let formal = b.ensure_symbol(&name, FileId::NONE).unwrap();
        let signature = b
            .intern(r#"{"value_signature":{"tpe":{"type_ref":{"symbol":"scala/Int#"}}}}"#)
            .unwrap();
        let row = &mut b.facts.symbols[formal.index()];
        row.context = context;
        row.kind = 8;
        row.owner = method;
        row.signature = signature;
        clauses.push(name);
    }
    let signature = serde_json::json!({"method_signature":{"parameter_lists":[{"symlinks":clauses}],
        "return_type":{"type_ref":{"symbol":"selectedexternal/Configuration#PatienceConfig#"}}}});
    b.facts.symbols[method.index()].signature = b.intern(&signature.to_string()).unwrap();
    b.facts.operations.push(OperationRecord {
        body: BodyId(0),
        opcode: Opcode::LoadField,
        target: module,
        dest: ValueId(3),
        a: ValueId(2),
        b: ValueId::NONE,
        arguments: IdRange::default(),
        span: Span { start: 35, end: 49 },
        flags: 0,
    });
    b.facts.bodies.push(BodyRecord {
        symbol: root,
        file: FileId(0),
        span: Span { start: 0, end: 51 },
        name_span: Span::default(),
        operations: IdRange { start: 0, len: 1 },
        parameters: IdRange::default(),
        body_hash: ContentHash([2; 32]),
        flags: 0,
    });
    (b.finish().unwrap(), module)
}

#[test]
fn exact_compiler_owned_complete_method_witnesses_only_its_nested_module() {
    let (facts, module) = fixture();
    let c = candidates(&facts);
    assert_eq!(c.len(), 1);
    assert_eq!(c[0].symbol, module);
    assert_eq!(c[0].jvm_owner, "selectedexternal/Configuration");
    assert_eq!(
        c[0].module_owner,
        "selectedexternal/Configuration$PatienceConfig$"
    );
    assert_eq!(facts.symbols[module.index()].kind, 0);
    assert!(facts.symbols[module.index()].signature.is_none());
}

#[test]
fn missing_incomplete_foreign_defined_and_ordinary_value_witnesses_stay_fields() {
    for case in 0..17 {
        let (mut facts, module) = fixture();
        let method = facts.find_symbol(METHOD).unwrap();
        let formal = facts.find_symbol(&format!("{METHOD}(timeout)")).unwrap();
        match case {
            0 => facts.symbols[method.index()].signature = StrId::NONE,
            1 => facts.symbols[method.index()].flags |= SYMBOL_DEFINED,
            2 => facts.symbols[method.index()].context = StrId::NONE,
            3 => facts.symbols[method.index()].owner = facts.symbols[module.index()].owner,
            4 => facts.symbols[formal.index()].signature = StrId::NONE,
            5 => facts.symbols[formal.index()].owner = module,
            6 => facts.symbols[formal.index()].context = StrId::NONE,
            7 => facts.symbols[module.index()].flags |= SYMBOL_DEFINED,
            8 => facts.symbols[module.index()].kind = 20,
            9 => facts.files[0].flags = SOURCE_VERIFIED,
            10 => facts.operations[0].a = ValueId::NONE,
            11 => facts.operations[0].arguments.len = 1,
            12 => facts.issues.push(IssueRecord {
                kind: IssueKind::ContextConflict,
                file: FileId::NONE,
                symbol: method,
                detail: StrId::NONE,
            }),
            13 => facts.symbols[module.index()].signature = facts.symbols[method.index()].signature,
            14 => facts.symbols[module.index()].kind = 13,
            15 => facts.symbols[method.index()].file = FileId(0),
            16 => facts.issues.push(IssueRecord {
                kind: IssueKind::ContextConflict,
                file: FileId::NONE,
                symbol: formal,
                detail: StrId::NONE,
            }),
            _ => unreachable!(),
        }
        assert!(candidates(&facts).is_empty(), "case{case}");
        assert_eq!(facts.operations[0].opcode, Opcode::LoadField);
    }
}

fn classes() -> (Arc<binary::ClassMetadata>, Arc<binary::ClassMetadata>) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../fixtures/selected-external-apply/library.jar");
    let hash = ContentHash(Sha256::digest(std::fs::read(&path).unwrap()).into());
    let mut loader = CapturedClasspath::new(
        vec![ClasspathEntry {
            path,
            sha256: hash,
            kind: EntryKind::Jar,
        }],
        Limits::default(),
    )
    .unwrap();
    let mut read = |name| match loader.lookup(name).unwrap() {
        ClassLookup::Found(class) => {
            Arc::new(binary::ClassMetadata::new(class.bytes.into(), Limits::default()).unwrap())
        }
        _ => panic!("missing genuine fixture class"),
    };
    (
        read("selectedexternal/Configuration"),
        read("selectedexternal/Configuration$PatienceConfig$"),
    )
}

#[test]
fn genuine_nested_companion_requires_exact_instance_accessor_and_outer_constructor() {
    let (facts, _) = fixture();
    let mut c = candidates(&facts).pop().unwrap();
    let (owner, module) = classes();
    assert!(getter(&owner, &c));
    assert!(module_header(&module, &c));
    c.descriptor = "()Ljava/lang/Object;".into();
    assert!(!getter(&owner, &c));
    c.descriptor = "()Lselectedexternal/Configuration$PatienceConfig$;".into();
    c.jvm_owner = "selectedexternal/Unrelated".into();
    assert!(!getter(&owner, &c));
    assert!(!module_header(&module, &c));
}

#[test]
fn static_private_bridge_overloaded_field_and_wrong_return_accessors_are_rejected() {
    let (facts, _) = fixture();
    let c = candidates(&facts).pop().unwrap();
    for flags in [0, 0x0009, 0x0003, 0x0041] {
        assert!(!getter_rows(
            &c.jvm_owner,
            std::iter::empty(),
            std::iter::once((c.name.as_str(), c.descriptor.as_str(), flags)),
            &c
        ));
    }
    assert!(!getter_rows(
        &c.jvm_owner,
        std::iter::once(c.name.as_str()),
        std::iter::once((c.name.as_str(), c.descriptor.as_str(), 0x0401)),
        &c
    ));
    assert!(!getter_rows(
        &c.jvm_owner,
        std::iter::empty(),
        [
            (c.name.as_str(), c.descriptor.as_str(), 0x0401),
            (c.name.as_str(), "()Ljava/lang/Object;", 1)
        ]
        .into_iter(),
        &c
    ));
    assert!(!getter_rows(
        &c.jvm_owner,
        std::iter::empty(),
        std::iter::once((c.name.as_str(), "()Ljava/lang/Object;", 0x0401)),
        &c
    ));
    let ctor = format!("(L{};)V", c.jvm_owner);
    assert!(!module_rows(
        &c.module_owner,
        1,
        std::iter::once("MODULE$"),
        std::iter::once(("<init>", ctor.as_str(), 1)),
        &c
    ));
    assert!(!module_rows(
        &c.module_owner,
        1,
        std::iter::empty(),
        std::iter::once(("<init>", "()V", 1)),
        &c
    ));
}

fn admitted(facts: &mut FactSnapshot) -> (Registry, OwnedBinaryInputs, SymbolId) {
    let c = candidates(facts).pop().unwrap();
    let (owner, module) = classes();
    let context = facts.symbols[c.symbol.index()].context;
    let empty = append_text(facts, "").unwrap();
    let native = declare(
        facts,
        context,
        c.owner,
        &native_name(&c.jvm_owner, &c.name, &c.descriptor),
        3,
        FileId::NONE,
        0x0401,
    )
    .unwrap();
    let registry = Registry {
        types: HashMap::new(),
        methods: HashMap::from([(
            MethodKey {
                context: 0,
                owner: c.jvm_owner.clone(),
                name: c.name.clone(),
                descriptor: c.descriptor.clone(),
            },
            MethodData {
                symbol: native,
                owner: c.owner,
                flags: 0x0401,
                receiver_parameter: None,
            },
        )]),
        method_events: Vec::new(),
        synthetic_methods: 0,
        fields: HashMap::new(),
        accessors: accessors::State::default(),
        files: HashMap::new(),
        empty,
        initialized: HashSet::new(),
        static_phases: HashMap::new(),
        static_active: HashSet::new(),
        bootstrap: HashMap::new(),
    };
    let context = AdmittedContext {
        id: context,
        name: "compile".into(),
        cache_metrics: ClassCacheMetrics::default(),
        phase: "test",
        active_method: SymbolId::NONE,
        active_file: FileId::NONE,
        pending_methods: 0,
        admission: Admission::default(),
        entries: Vec::new(),
        classes: [(c.jvm_owner, owner), (c.module_owner, module)]
            .into_iter()
            .map(|(name, metadata)| {
                let hash = metadata.hash();
                let bytes = metadata.bytes().clone();
                (
                    name,
                    CachedClass::Found(Arc::new(ClassBytes {
                        bytes,
                        hash,
                        metadata,
                        origin: "pinned fixture".into(),
                    })),
                )
            })
            .collect(),
        shared_metadata: SharedMetadata::default(),
        java_feature: None,
        entries_at: Vec::new(),
    };
    let inputs = OwnedBinaryInputs {
        identity: ContentHash::default(),
        raw_identity: facts.identity,
        contexts: vec![context],
        types: HashMap::new(),
        type_aliases: Vec::new(),
        methods: Vec::new(),
        admitted: Vec::new(),
        envelope_cache: binary::EnvelopeCache::new(0),
        platform_inputs: Vec::new(),
        platform_contexts: HashSet::new(),
    };
    (registry, inputs, native)
}

#[test]
fn canonical_getter_retargets_only_the_source_slot_and_exact_result_bound() {
    let (mut facts, module) = fixture();
    let original = facts.operations[0];
    facts
        .bound_classes
        .push(facts.symbols[module.index()].owner);
    facts.result_bounds.push(ResultBoundRecord {
        symbol: module,
        operation: OperationId(0),
        classes: IdRange { start: 0, len: 1 },
    });
    let old_hash = facts.bodies[0].body_hash;
    let source_candidates = candidates(&facts);
    let (registry, inputs, native) = admitted(&mut facts);
    let term = facts.symbols[module.index()];
    assert_eq!(
        augment(
            &mut facts,
            &registry,
            &inputs,
            &source_candidates,
            &HashMap::new()
        )
        .unwrap(),
        1
    );
    let mut expected = original;
    expected.opcode = Opcode::VirtualCall;
    expected.target = native;
    assert_eq!(
        format!("{:?}", facts.operations[0]),
        format!("{expected:?}")
    );
    assert_eq!(
        format!("{:?}", facts.symbols[module.index()]),
        format!("{term:?}")
    );
    assert_eq!(facts.result_bounds[0].symbol, native);
    assert_ne!(facts.bodies[0].body_hash, old_hash);
    let after = facts.bodies[0].body_hash;
    assert_eq!(
        augment(
            &mut facts,
            &registry,
            &inputs,
            &source_candidates,
            &HashMap::new()
        )
        .unwrap(),
        0
    );
    assert_eq!(facts.bodies[0].body_hash, after);
}

#[test]
fn unavailable_or_wrong_context_native_headers_leave_the_original_field_open() {
    for case in 0..7 {
        let (mut facts, _) = fixture();
        let original = facts.operations[0];
        let source_candidates = candidates(&facts);
        let (mut registry, mut inputs, native) = admitted(&mut facts);
        match case {
            0 => inputs.contexts[0].classes.clear(),
            1 => inputs.contexts[0].id = StrId::NONE,
            2 => {
                registry
                    .methods
                    .values_mut()
                    .next()
                    .unwrap()
                    .receiver_parameter = Some(0)
            }
            3 => facts.symbols[native.index()].flags &= !SYMBOL_NATIVE_BINARY,
            4 => registry.methods.values_mut().next().unwrap().symbol = original.target,
            5 => registry.methods.values_mut().next().unwrap().flags |= 8,
            6 => {
                let class = inputs.contexts[0].classes.values_mut().next().unwrap();
                if let CachedClass::Found(class) = class {
                    let mut broken = ClassBytes {
                        bytes: class.bytes.clone(),
                        hash: ContentHash([3; 32]),
                        origin: class.origin.clone(),
                        metadata: class.metadata.clone(),
                    };
                    broken.hash = ContentHash([3; 32]);
                    *class = Arc::new(broken);
                }
            }
            _ => unreachable!(),
        }
        assert_eq!(
            augment(
                &mut facts,
                &registry,
                &inputs,
                &source_candidates,
                &HashMap::new()
            )
            .unwrap(),
            0,
            "case{case}"
        );
        assert_eq!(
            format!("{:?}", facts.operations[0]),
            format!("{original:?}")
        );
    }
}

#[test]
fn verified_runtime_class_facet_and_relocated_source_are_preserved_by_the_member_bridge() {
    let mut hashes = Vec::new();
    for moved in [false, true] {
        let (mut facts, module) = fixture();
        let source_candidates = candidates(&facts);
        let (registry, inputs, _) = admitted(&mut facts);
        let mut registry = registry;
        registry.types.insert(
            (0, "selectedexternal/Configuration$PatienceConfig$".into()),
            module,
        );
        facts.symbols[module.index()].kind = 13;
        facts.symbols[module.index()].properties = 4;
        if moved {
            facts.files[0].path = append_text(&mut facts, "relocated/Calls.scala").unwrap();
        }
        let before = format!("{:?}", facts.symbols[module.index()]);
        assert_eq!(
            augment(
                &mut facts,
                &registry,
                &inputs,
                &source_candidates,
                &HashMap::new()
            )
            .unwrap(),
            1
        );
        assert_eq!(format!("{:?}", facts.symbols[module.index()]), before);
        hashes.push(facts.bodies[0].body_hash);
    }
    assert_eq!(
        hashes[0], hashes[1],
        "physical source placement is not native member authority"
    );
}
