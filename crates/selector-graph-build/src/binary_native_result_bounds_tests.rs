//! Real retained Java21 headers with explicitly normalized admission state.
//! No generated test row is labeled compiler capture or classfile output.
use super::*;

const INTEGER: &[u8] =
    include_bytes!("../../../fixtures/jdk-primitive-models/java/lang/Integer.class");
const STRING: &[u8] =
    include_bytes!("../../../fixtures/jdk-primitive-models/java/lang/String.class");
struct Fixture {
    facts: FactSnapshot,
    inputs: OwnedBinaryInputs,
    registry: Registry,
    method: SymbolId,
    owner: SymbolId,
    string: SymbolId,
}
fn fixture() -> Fixture {
    fixture_with_classes(&[])
}
fn fixture_with_classes(extra: &[(&str, &[u8])]) -> Fixture {
    let mut builder = FactBuilder::new();
    let context = builder.intern("native-bound-context").unwrap();
    let other = builder.intern("other-context").unwrap();
    let empty = builder.intern("").unwrap();
    let mut facts = builder.finish().unwrap();
    let mut classes = HashMap::new();
    let mut types = HashMap::new();
    let mut files = HashMap::new();
    let mut symbols = Vec::new();
    for &(name, raw) in [("java/lang/Integer", INTEGER), ("java/lang/String", STRING)]
        .iter()
        .chain(extra)
    {
        let bytes: Arc<[u8]> = raw.into();
        let metadata =
            Arc::new(binary::ClassMetadata::new(bytes.clone(), Limits::default()).unwrap());
        let hash = metadata.hash();
        let path = append_text(&mut facts, name).unwrap();
        let file = FileId(facts.files.len() as u32);
        facts.files.push(FileRecord {
            path,
            source: empty,
            revision: facts.revision,
            context,
            source_hash: hash,
            flags: FILE_BINARY_SOURCE,
        });
        let symbol = declare(
            &mut facts,
            context,
            SymbolId::NONE,
            &native_name(name, "<type>", ""),
            13,
            file,
            0,
        )
        .unwrap();
        facts.symbols[symbol.index()].flags |= SYMBOL_JVM_CLASS_HEADER_VERIFIED;
        classes.insert(
            name.to_owned(),
            CachedClass::Found(Arc::new(ClassBytes {
                bytes,
                hash,
                origin: name.to_owned(),
                metadata,
            })),
        );
        types.insert((0, name.to_owned()), symbol);
        files.insert((0, name.to_owned()), file);
        symbols.push(symbol);
    }
    let owner = symbols[0];
    let string = symbols[1];
    let file = files[&(0, "java/lang/Integer".to_owned())];
    let method = declare(
        &mut facts,
        context,
        owner,
        &native_name("java/lang/Integer", "toString", "(I)Ljava/lang/String;"),
        3,
        file,
        9,
    )
    .unwrap();
    facts.bodies.push(BodyRecord {
        symbol: method,
        file,
        span: Span::default(),
        name_span: Span::default(),
        operations: IdRange { start: 0, len: 2 },
        parameters: IdRange::default(),
        body_hash: facts.files[file.index()].source_hash,
        flags: BODY_BINARY_RECIPE,
    });
    for opcode in [Opcode::Unknown, Opcode::Call] {
        facts.operations.push(OperationRecord {
            body: BodyId(0),
            opcode,
            target: method,
            dest: ValueId::NONE,
            a: ValueId::NONE,
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span::default(),
            flags: 0,
        });
    }
    let methods = HashMap::from([(
        MethodKey {
            context: 0,
            owner: "java/lang/Integer".to_owned(),
            name: "toString".to_owned(),
            descriptor: "(I)Ljava/lang/String;".to_owned(),
        },
        MethodData {
            symbol: method,
            owner,
            flags: 9,
            receiver_parameter: None,
        },
    )]);
    let inputs = OwnedBinaryInputs {
        identity: ContentHash([2; 32]),
        raw_identity: facts.identity,
        contexts: vec![AdmittedContext {
            id: context,
            name: "native-bound-context".to_owned(),
            cache_metrics: ClassCacheMetrics::default(),
            phase: "test",
            active_method: SymbolId::NONE,
            active_file: FileId::NONE,
            pending_methods: 0,
            admission: Admission::default(),
            entries: Vec::new(),
            classes,
            shared_metadata: Default::default(),
            java_feature: Some(21),
            entries_at: Vec::new(),
        }],
        types: types.clone(),
        type_aliases: Vec::new(),
        methods: Vec::new(),
        admitted: Vec::new(),
        envelope_cache: binary::EnvelopeCache::new(0),
        platform_inputs: Vec::new(),
        platform_contexts: HashSet::new(),
    };
    let registry = Registry {
        types,
        methods,
        method_events: Vec::new(),
        synthetic_methods: 0,
        fields: HashMap::new(),
        accessors: accessors::State::default(),
        files,
        empty,
        initialized: HashSet::new(),
        static_phases: HashMap::new(),
        static_active: HashSet::new(),
        bootstrap: HashMap::new(),
    };
    assert_ne!(context, other);
    facts.validate().unwrap();
    Fixture {
        facts,
        inputs,
        registry,
        method,
        owner,
        string,
    }
}

fn field_fixture() -> (Fixture, SymbolId, SymbolId, OperationId) {
    const GETTER: &[u8] = include_bytes!(
        "../../../fixtures/native-admission-chain/classes/admissioncase/Getter.class"
    );
    const BOX: &[u8] =
        include_bytes!("../../../fixtures/native-admission-chain/classes/admissioncase/Box.class");
    let mut f =
        fixture_with_classes(&[("admissioncase/Getter", GETTER), ("admissioncase/Box", BOX)]);
    let owner = "admissioncase/Getter";
    let descriptor = "Ladmissioncase/Box;";
    let file = f.registry.files[&(0, owner.to_owned())];
    let getter = f.registry.types[&(0, owner.to_owned())];
    let boxed = f.registry.types[&(0, "admissioncase/Box".to_owned())];
    let context = f.inputs.contexts[0].id;
    let field = declare(
        &mut f.facts,
        context,
        getter,
        &native_name(owner, "cached", descriptor),
        20,
        file,
        2,
    )
    .unwrap();
    f.registry.fields.insert(
        MethodKey {
            context: 0,
            owner: owner.to_owned(),
            name: "cached".to_owned(),
            descriptor: descriptor.to_owned(),
        },
        field,
    );
    let method = declare(
        &mut f.facts,
        context,
        getter,
        &native_name(owner, "lazyHelper", "()Ladmissioncase/Box;"),
        3,
        file,
        2,
    )
    .unwrap();
    let body = BodyId::checked(f.facts.bodies.len()).unwrap();
    let operation = OperationId::checked(f.facts.operations.len()).unwrap();
    f.facts.bodies.push(BodyRecord {
        symbol: method,
        file,
        span: Span::default(),
        name_span: Span::default(),
        operations: IdRange {
            start: operation.0,
            len: 1,
        },
        parameters: IdRange::default(),
        body_hash: f.facts.files[file.index()].source_hash,
        flags: BODY_BINARY_RECIPE,
    });
    f.facts.operations.push(OperationRecord {
        body,
        opcode: Opcode::LoadField,
        target: field,
        dest: ValueId(1),
        a: ValueId(0),
        b: ValueId::NONE,
        arguments: IdRange::default(),
        span: Span::default(),
        flags: 0,
    });
    (f, field, boxed, operation)
}

#[test]
fn reference_field_reads_publish_only_operation_bounds() {
    let (mut f, field, boxed, operation) = field_fixture();
    let operations = f.facts.operations.len();
    publish(&mut f.facts, &f.inputs, &f.registry).unwrap();
    publish(&mut f.facts, &f.inputs, &f.registry).unwrap();
    assert_eq!(f.facts.result_bound(field, operation), Some(&[boxed][..]));
    assert!(f.facts.result_bound(field, OperationId::NONE).is_none());
    assert_eq!(f.facts.result_bounds.len(), 2);
    assert_eq!(f.facts.operations.len(), operations);
    assert_eq!(
        f.facts.operations[operation.index()].opcode,
        Opcode::LoadField
    );
    f.facts.validate().unwrap();
}

#[test]
fn stale_field_provider_and_unverified_field_reads_keep_their_unknowns() {
    for mutation in 0..7 {
        let (mut f, field, boxed, operation) = field_fixture();
        let declaration = &mut f.facts.symbols[field.index()];
        match mutation {
            0 => f.facts.files[declaration.file.index()].source_hash = ContentHash([8; 32]),
            1 => declaration.flags &= !SYMBOL_NATIVE_BINARY,
            2 => f.facts.symbols[boxed.index()].flags &= !SYMBOL_JVM_CLASS_HEADER_VERIFIED,
            3 => f.facts.operations[operation.index()].flags |= OP_STATIC_FIELD,
            4 => f.facts.operations[operation.index()].opcode = Opcode::StoreField,
            5 => f.facts.bodies[1].flags &= !BODY_BINARY_RECIPE,
            6 => f.facts.issues.push(IssueRecord {
                kind: IssueKind::ContextConflict,
                symbol: field,
                file: FileId::NONE,
                detail: StrId::NONE,
            }),
            _ => unreachable!(),
        }
        publish(&mut f.facts, &f.inputs, &f.registry).unwrap();
        assert!(
            f.facts.result_bound(field, operation).is_none(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn admitted_reference_descriptor_is_bound_without_allocation_or_effect_waiver_and_persists() {
    let mut f = fixture();
    let prior = enriched_identity(f.inputs.raw_identity, f.inputs.identity, &f.facts);
    let symbols = f.facts.symbols.len();
    let operations = f.facts.operations.clone();
    publish(&mut f.facts, &f.inputs, &f.registry).unwrap();
    assert_eq!(
        f.facts.result_bound(f.method, OperationId::NONE),
        Some(&[f.string][..])
    );
    assert_eq!(f.facts.symbols.len(), symbols);
    assert_eq!(f.inputs.contexts[0].classes.len(), 2);
    assert_eq!(f.inputs.contexts[0].cache_metrics.requests, 0);
    assert_eq!(f.facts.operations.len(), operations.len());
    assert_eq!(f.facts.operations[0].opcode, Opcode::Unknown);
    assert_ne!(
        prior,
        enriched_identity(f.inputs.raw_identity, f.inputs.identity, &f.facts)
    );
    publish(&mut f.facts, &f.inputs, &f.registry).unwrap();
    assert_eq!(f.facts.result_bounds.len(), 1);
    let temp = tempfile::tempdir().unwrap();
    let path = temp.path().join("bounded.bin");
    let identity = selector_facts::codec::write(&path, &f.facts).unwrap();
    let read = selector_facts::codec::read(&path).unwrap();
    assert_eq!(read.identity, identity);
    assert_eq!(
        read.result_bound(f.method, OperationId::NONE),
        Some(&[f.string][..])
    );
    assert_eq!(read.operations[0].opcode, Opcode::Unknown);
}

#[test]
fn missing_stale_conflicted_context_or_unpublished_body_cannot_supply_a_native_bound() {
    for mutation in 0..13 {
        let mut f = fixture();
        let other = StrId(1);
        match mutation {
            0 => f.facts.symbols[f.string.index()].flags &= !SYMBOL_JVM_CLASS_HEADER_VERIFIED,
            1 => f.facts.symbols[f.string.index()].context = other,
            2 => f.facts.symbols[f.method.index()].flags = 0,
            3 => f.facts.bodies[0].flags = 0,
            4 => f.facts.files[0].flags = SOURCE_VERIFIED | SYNTAX_VERIFIED,
            5 => f.facts.files[0].source_hash = ContentHash([7; 32]),
            6 => f.inputs.contexts[0]
                .classes
                .remove("java/lang/String")
                .map(|_| ())
                .unwrap(),
            7 => f.facts.symbols[f.owner.index()].flags &= !SYMBOL_JVM_CLASS_HEADER_VERIFIED,
            8..=11 => f.facts.issues.push(IssueRecord {
                kind: IssueKind::ContextConflict,
                symbol: match mutation {
                    8 => f.method,
                    9 => f.string,
                    10 => f.owner,
                    _ => SymbolId::NONE,
                },
                file: if mutation == 11 {
                    FileId(0)
                } else {
                    FileId::NONE
                },
                detail: StrId::NONE,
            }),
            12 => f.inputs.contexts[0]
                .classes
                .insert(
                    "java/lang/Integer".to_owned(),
                    CachedClass::Unknown(binary::ErrorKind::ClassNotFound),
                )
                .map(|_| ())
                .unwrap(),
            _ => unreachable!(),
        }
        publish(&mut f.facts, &f.inputs, &f.registry).unwrap();
        assert!(f.facts.result_bounds.is_empty(), "mutation {mutation}");
    }
}

#[test]
fn primitive_array_void_or_unadmitted_exact_descriptor_is_never_reinterpreted_as_object() {
    for (owner, name, descriptor) in [
        ("java/lang/Integer", "bitCount", "(I)I"),
        ("java/lang/String", "getBytes", "()[B"),
        ("java/lang/String", "getChars", "(II[CI)V"),
        ("java/lang/Integer", "toString", "(I)Ljava/lang/Long;"),
    ] {
        let mut f = fixture();
        let (mut key, mut data) = f.registry.methods.drain().next().unwrap();
        key.owner = owner.to_owned();
        key.name = name.to_owned();
        key.descriptor = descriptor.to_owned();
        if owner == "java/lang/String" {
            data.owner = f.string;
            data.flags = 1;
            f.facts.symbols[f.method.index()].owner = f.string;
            f.facts.symbols[f.method.index()].file = FileId(1);
            f.facts.bodies[0].file = FileId(1);
        }
        f.registry.methods.insert(key, data);
        publish(&mut f.facts, &f.inputs, &f.registry).unwrap();
        assert!(
            f.facts.result_bounds.is_empty(),
            "{owner}.{name}{descriptor}"
        );
    }
}

#[test]
fn existing_compiler_conjunction_and_exact_operation_clause_are_not_overwritten() {
    let mut f = fixture();
    f.facts.bound_classes = vec![f.owner, f.string, f.string];
    f.facts.result_bounds = vec![
        ResultBoundRecord {
            symbol: f.method,
            operation: OperationId(1),
            classes: IdRange { start: 2, len: 1 },
        },
        ResultBoundRecord {
            symbol: f.method,
            operation: OperationId::NONE,
            classes: IdRange { start: 0, len: 2 },
        },
    ];
    let prior = f.facts.result_bounds.clone();
    publish(&mut f.facts, &f.inputs, &f.registry).unwrap();
    assert_eq!(f.facts.result_bounds, prior);
    assert_eq!(f.facts.bound_classes, vec![f.owner, f.string, f.string]);
}
