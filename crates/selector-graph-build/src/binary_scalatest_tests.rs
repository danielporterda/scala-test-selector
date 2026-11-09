use super::*;

const WORD: &[u8] = include_bytes!(
    "../../../fixtures/scalatest-execution/classes/org/scalatest/wordspec/AnyWordSpecLike.class"
);
const ENGINE: &[u8] =
    include_bytes!("../../../fixtures/scalatest-execution/classes/org/scalatest/Engine.class");
const SUPER_ENGINE: &[u8] =
    include_bytes!("../../../fixtures/scalatest-execution/classes/org/scalatest/SuperEngine.class");
const TRANSFORMER: &[u8] =
    include_bytes!("../../../fixtures/scalatest-execution/classes/org/scalatest/Transformer.class");
fn class_bytes(bytes: &[u8], path: &str, owner: &str) -> Arc<ClassBytes> {
    let bytes: Arc<[u8]> = Arc::from(bytes);
    Arc::new(ClassBytes {
        hash: hash(&bytes),
        origin: format!("{path}!/{owner}.class"),
        metadata: Arc::new(binary::ClassMetadata::new(bytes.clone(), Limits::default()).unwrap()),
        bytes,
    })
}
// Explicitly normalized private admission records over unchanged genuine library
// classes. Production reaches this boundary only through ordered provider proof.
fn fixture(
    name: &str,
    descriptor: &str,
) -> (
    FactSnapshot,
    AdmittedContext,
    MethodData,
    Arc<ClassBytes>,
    CapturedClasspath,
) {
    let mut b = FactBuilder::new();
    let context = b.intern("normalized-word-context").unwrap();
    let owner = b
        .ensure_global_symbol("org/scalatest/wordspec/AnyWordSpecLike#", context)
        .unwrap();
    let symbol = b
        .ensure_global_symbol(&native_name(contract::WORDSPEC, name, descriptor), context)
        .unwrap();
    b.facts.symbols[symbol.index()].owner = owner;
    b.facts.symbols[symbol.index()].kind = 3;
    let parsed = binary::parse_class(WORD, Limits::default()).unwrap();
    let method = parsed.method(name, Some(descriptor)).unwrap();
    let data = MethodData {
        symbol,
        owner,
        flags: method.flags,
        receiver_parameter: if name == "$init$" { Some(0) } else { None },
    };
    let bytes = class_bytes(WORD, "/normalized/wordspec.jar", contract::WORDSPEC);
    let mut classes = HashMap::new();
    classes.insert(contract::WORDSPEC.into(), CachedClass::Found(bytes.clone()));
    for (owner, bytes) in [
        ("org/scalatest/Engine", ENGINE),
        ("org/scalatest/SuperEngine", SUPER_ENGINE),
        ("org/scalatest/Transformer", TRANSFORMER),
    ] {
        classes.insert(
            owner.into(),
            CachedClass::Found(class_bytes(bytes, "/normalized/core.jar", owner)),
        );
    }
    let ctx = AdmittedContext {
        id: context,
        name: "normalized-word-context".into(),
        cache_metrics: Default::default(),
        phase: "word-model-test",
        active_method: SymbolId::NONE,
        active_file: FileId::NONE,
        pending_methods: 0,
        admission: Admission::default(),
        entries: vec![
            ClasspathEntry {
                path: "/normalized/wordspec.jar".into(),
                sha256: ContentHash::from_hex(contract::WORDSPEC_ARCHIVE).unwrap(),
                kind: EntryKind::Jar,
            },
            ClasspathEntry {
                path: "/normalized/core.jar".into(),
                sha256: ContentHash::from_hex(CORE_ARCHIVE).unwrap(),
                kind: EntryKind::Jar,
            },
        ],
        classes,
        shared_metadata: SharedMetadata::default(),
        java_feature: None,
        entries_at: Vec::new(),
    };
    (
        b.facts,
        ctx,
        data,
        bytes,
        CapturedClasspath::new(Vec::new(), Limits::default()).unwrap(),
    )
}
fn registry() -> Registry {
    Registry {
        types: HashMap::new(),
        methods: HashMap::new(),
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
    }
}

#[test]
fn genuine_initializer_cuts_only_engine_construction_and_keeps_all_outward_setters() {
    let name = "$init$";
    let descriptor = "(Lorg/scalatest/wordspec/AnyWordSpecLike;)V";
    let (facts, mut ctx, data, bytes, mut loader) = fixture(name, descriptor);
    let parsed = binary::parse_class(&bytes.bytes, Limits::default()).unwrap();
    let method = parsed.method(name, Some(descriptor)).unwrap();
    let original = binary::summarize(&parsed, method, Limits::default());
    let modeled = model(
        &facts,
        &Conflicts::new(&facts),
        &mut ctx,
        &mut loader,
        &data,
        &bytes,
        &parsed,
        method,
    )
    .unwrap()
    .expect("pinned init");
    let calls = |s: &MethodSummary<'_>| {
        s.calls
            .iter()
            .map(|c| {
                (
                    c.member.owner.to_owned(),
                    c.member.name.to_owned(),
                    c.member.descriptor.to_owned(),
                    c.offset,
                    c.kind,
                )
            })
            .collect::<Vec<_>>()
    };
    let mut expected = calls(&original);
    expected.retain(|c| !(c.0 == "org/scalatest/Engine" && c.1 == "<init>"));
    assert_eq!(calls(&modeled.summary), expected);
    assert_eq!(
        modeled
            .summary
            .calls
            .iter()
            .filter(|c| c.member.name.contains("$_setter_$"))
            .count(),
        8
    );
    for accessor in contract::ACCESSORS {
        assert!(
            modeled
                .summary
                .calls
                .iter()
                .any(|c| c.member.name == accessor.setter)
        );
    }
    assert_eq!(modeled.summary.lambdas.len(), original.lambdas.len());
    assert!(!modeled.summary.values.iter().any(|v| matches!(
        v,
        Value::Allocation {
            class: "org/scalatest/Engine",
            ..
        }
    )));
    assert!(
        modeled
            .summary
            .field_writes
            .iter()
            .any(|w| w.member == state("engine-input")
                && matches!(modeled.summary.values[w.value.0 as usize], Value::Lambda(_)))
    );
    assert!(
        modeled
            .summary
            .field_writes
            .iter()
            .filter(|w| w.offset == 0)
            .all(|w| matches!(modeled.summary.values[w.value.0 as usize], Value::Null))
    );
    assert_ne!(modeled.body_hash, bytes.hash);
    assert!(
        contract::lookup(
            "org/scalatest/Engine",
            "<init>",
            "(Lscala/Function0;Ljava/lang/String;)V"
        )
        .is_none()
    );
}
#[test]
fn genuine_trait_initializer_class_endpoint_requires_exact_static_receiver_binding() {
    // Normalized endpoint form copied from the real admitted WordSpec $init$
    // binding: the compiler trait CLASS is both symbol and owner. Its package
    // owner is not the trait itself; this is not a fabricated method definition.
    let descriptor = "(Lorg/scalatest/wordspec/AnyWordSpecLike;)V";
    for receiver in [Some(0), None, Some(1)] {
        let (mut facts, mut ctx, mut data, bytes, mut loader) = fixture("$init$", descriptor);
        data.symbol = data.owner;
        data.receiver_parameter = receiver;
        facts.symbols[data.owner.index()].kind = 13;
        assert_ne!(facts.symbols[data.symbol.index()].owner, data.owner);
        let parsed = binary::parse_class(&bytes.bytes, Limits::default()).unwrap();
        let method = parsed.method("$init$", Some(descriptor)).unwrap();
        let result = model(
            &facts,
            &Conflicts::new(&facts),
            &mut ctx,
            &mut loader,
            &data,
            &bytes,
            &parsed,
            method,
        )
        .unwrap();
        assert_eq!(result.is_some(), receiver == Some(0));
        if let Some(model) = result {
            assert_eq!(
                model
                    .summary
                    .calls
                    .iter()
                    .filter(|call| call.member.name.contains("$_setter_$"))
                    .count(),
                8
            );
            assert!(
                !model
                    .summary
                    .calls
                    .iter()
                    .any(|call| call.member.owner == "org/scalatest/Engine"
                        && call.member.name == "<init>")
            );
        }
    }
}

#[test]
fn class_provider_context_code_and_source_override_mutations_decline_without_fact_changes() {
    let name = "testNames";
    let descriptor = "()Lscala/collection/immutable/Set;";
    for case in 0..13 {
        let (mut facts, mut ctx, mut data, mut bytes, mut loader) = fixture(name, descriptor);
        let original = bytes.clone();
        let parsed = binary::parse_class(&original.bytes, Limits::default()).unwrap();
        let mut method = *parsed.method(name, Some(descriptor)).unwrap();
        match case {
            0 => facts.symbols[data.symbol.index()].flags |= SYMBOL_DEFINED,
            1 => ctx.entries[0].sha256 = ContentHash([7; 32]),
            2 => {
                bytes = Arc::new(ClassBytes {
                    bytes: bytes.bytes.clone(),
                    hash: ContentHash([8; 32]),
                    origin: bytes.origin.clone(),
                    metadata: bytes.metadata.clone(),
                });
            }
            3 => method.flags ^= 0x10,
            4 => method.max_locals += 1,
            5 => facts.symbols[data.symbol.index()].context = StrId::NONE,
            6 => data.flags ^= 0x10,
            7 => ctx.entries.insert(
                0,
                ClasspathEntry {
                    path: "/opaque/earlier.jar".into(),
                    sha256: ContentHash([9; 32]),
                    kind: EntryKind::Unavailable,
                },
            ),
            8 => facts.symbols[data.owner.index()].flags |= SYMBOL_DEFINED,
            9 => data.receiver_parameter = Some(0),
            10 => facts.issues.push(IssueRecord {
                kind: IssueKind::ContextConflict,
                file: FileId::NONE,
                symbol: SymbolId::NONE,
                detail: StrId::NONE,
            }),
            11 => facts.issues.push(IssueRecord {
                kind: IssueKind::ContextConflict,
                file: FileId::NONE,
                symbol: data.owner,
                detail: StrId::NONE,
            }),
            // The class endpoint exception is not available to ordinary methods.
            12 => data.symbol = data.owner,
            _ => unreachable!(),
        }
        let counts = (
            facts.symbols.len(),
            facts.bodies.len(),
            facts.operations.len(),
            facts.relations.len(),
        );
        assert!(
            model(
                &facts,
                &Conflicts::new(&facts),
                &mut ctx,
                &mut loader,
                &data,
                &bytes,
                &parsed,
                &method
            )
            .unwrap()
            .is_none(),
            "case {case}"
        );
        assert_eq!(
            counts,
            (
                facts.symbols.len(),
                facts.bodies.len(),
                facts.operations.len(),
                facts.relations.len()
            )
        );
    }
}
#[test]
fn omitted_implementation_provider_and_missing_sibling_are_not_trusted_by_name() {
    for case in 0..3 {
        let (facts, mut ctx, data, bytes, mut loader) =
            fixture("testNames", "()Lscala/collection/immutable/Set;");
        match case {
            0 => ctx.entries[1].sha256 = ContentHash([7; 32]),
            1 => {
                ctx.classes.remove("org/scalatest/Engine");
            }
            2 => {
                ctx.classes.insert(
                    "org/scalatest/Transformer".into(),
                    CachedClass::Found(class_bytes(
                        TRANSFORMER,
                        "/different/provider.jar",
                        "org/scalatest/Transformer",
                    )),
                );
            }
            _ => unreachable!(),
        }
        let parsed = binary::parse_class(&bytes.bytes, Limits::default()).unwrap();
        let method = parsed
            .method("testNames", Some("()Lscala/collection/immutable/Set;"))
            .unwrap();
        assert!(
            model(
                &facts,
                &Conflicts::new(&facts),
                &mut ctx,
                &mut loader,
                &data,
                &bytes,
                &parsed,
                method
            )
            .unwrap()
            .is_none()
        );
    }
}
#[test]
fn registration_retains_exact_callback_and_every_argument_in_registry_dependencies() {
    let descriptor = "(Ljava/lang/String;Lscala/collection/immutable/List;Ljava/lang/String;Lscala/Function0;Lorg/scalactic/source/Position;)V";
    let summary = protocol(descriptor, Recipe::Register { callback: 3 }).unwrap();
    let callback = V(4);
    assert!(
        summary
            .field_writes
            .iter()
            .any(|w| w.member == state("payloads") && w.value == callback)
    );
    let invoke = summary
        .calls
        .iter()
        .find(|c| c.member.owner == "scala/Function0")
        .unwrap();
    assert_eq!(invoke.receiver, Some(callback));
    assert_eq!(invoke.arguments.len, 0);
    assert_eq!(invoke.kind, InvokeKind::Interface);
    let meta = summary
        .field_writes
        .iter()
        .find(|w| w.member == state("metadata"))
        .unwrap();
    let Value::Alternatives(range) = summary.values[meta.value.0 as usize] else {
        panic!("metadata aliases");
    };
    assert_eq!(
        &summary.arguments[range.range()],
        &[V(1), V(2), V(3), V(4), V(5)]
    );
    assert!(
        !summary.unknown_offsets.is_empty(),
        "unverified tag/dynamic/error boundary remains explicit"
    );
}
#[test]
fn scope_callback_and_application_exception_extension_remain_possible() {
    let descriptor = "(Ljava/lang/String;Lscala/Option;Ljava/lang/String;Ljava/lang/String;IILorg/scalactic/source/Position;Lscala/Function0;)V";
    let summary = protocol(descriptor, Recipe::Scope { callback: 7 }).unwrap();
    assert!(
        summary
            .calls
            .iter()
            .any(|c| c.member.owner == "scala/Function0" && c.receiver == Some(V(8)))
    );
    assert!(
        summary
            .calls
            .iter()
            .any(|c| c.member.owner == "java/lang/Throwable"
                && c.member.name == "getMessage"
                && c.kind == InvokeKind::Virtual)
    );
    assert!(!summary.unknown_offsets.is_empty());
    assert!(
        !summary
            .field_writes
            .iter()
            .any(|w| w.member == state("payloads")),
        "scope is not a registered test payload"
    );
}
#[test]
fn public_registry_views_keep_dependencies_and_never_fabricate_empty_or_concrete_collection() {
    for (role, descriptor) in [
        (Recipe::Names, "()Lscala/collection/immutable/Set;"),
        (Recipe::Tags, "()Lscala/collection/immutable/Map;"),
        (
            Recipe::TestData,
            "(Ljava/lang/String;Lorg/scalatest/ConfigMap;)Lorg/scalatest/TestData;",
        ),
    ] {
        let summary = protocol(descriptor, role).unwrap();
        let getter = summary.calls.first().unwrap();
        assert_eq!(getter.member.owner, contract::WORDSPEC);
        assert_eq!(
            getter.member.name,
            "org$scalatest$wordspec$AnyWordSpecLike$$engine"
        );
        assert_eq!(getter.member.descriptor, "()Lorg/scalatest/Engine;");
        assert_eq!(getter.kind, InvokeKind::Interface);
        assert_eq!(getter.receiver, Some(V(0)));
        assert_eq!(getter.arguments.len, 0);
        assert!(summary.values.iter().any(
            |v| matches!(v,Value::Field{member,..}if member.owner==STATE&&member.name=="names")
        ));
        assert!(matches!(
            summary.values[summary.returned.unwrap().0 as usize],
            Value::UnknownData
        ));
        assert!(
            !summary
                .values
                .iter()
                .any(|v| matches!(v, Value::Allocation { .. } | Value::MayAllocation { .. }))
        );
        if role != Recipe::Names {
            assert!(!summary.unknown_offsets.is_empty());
        }
    }
}
#[test]
fn run_preserves_payloads_and_virtual_fixture_testdata_super_extension_points_with_open_args() {
    for (role, descriptor, member) in [
        (
            Recipe::Run,
            "(Lscala/Option;Lorg/scalatest/Args;)Lorg/scalatest/Status;",
            "org$scalatest$wordspec$AnyWordSpecLike$$super$run",
        ),
        (
            Recipe::RunTests,
            "(Lscala/Option;Lorg/scalatest/Args;)Lorg/scalatest/Status;",
            "runTest",
        ),
        (
            Recipe::RunTest,
            "(Ljava/lang/String;Lorg/scalatest/Args;)Lorg/scalatest/Status;",
            "withFixture",
        ),
    ] {
        let summary = protocol(descriptor, role).unwrap();
        let call = summary
            .calls
            .iter()
            .find(|c| c.member.name == member)
            .unwrap();
        assert_eq!(call.receiver, Some(V(0)));
        assert_eq!(call.kind, InvokeKind::Interface);
        assert!(
            summary
                .calls
                .iter()
                .any(|c| c.member.owner == "scala/Function0")
        );
        assert!(!summary.unknown_offsets.is_empty());
        assert!(matches!(
            summary.values[summary.returned.unwrap().0 as usize],
            Value::UnknownData
        ));
        if role == Recipe::RunTest {
            assert!(summary.calls.iter().any(|c| c.member.name == "testDataFor"));
        }
    }
}
#[test]
fn logical_registry_fields_are_contextual_not_native_claims_and_do_not_alias_accessors() {
    let (mut facts, ctx, _, _, _) = fixture("testNames", "()Lscala/collection/immutable/Set;");
    let mut reg = registry();
    let first = field(
        &mut facts,
        &mut reg,
        0,
        ctx.id,
        FileId::NONE,
        state("payloads"),
    )
    .unwrap()
    .unwrap();
    assert_eq!(
        field(
            &mut facts,
            &mut reg,
            0,
            ctx.id,
            FileId::NONE,
            state("payloads")
        )
        .unwrap(),
        Some(first)
    );
    let other_context = append_text(&mut facts, "other-context").unwrap();
    let second = field(
        &mut facts,
        &mut reg,
        1,
        other_context,
        FileId::NONE,
        state("payloads"),
    )
    .unwrap()
    .unwrap();
    assert_ne!(first, second);
    assert!(
        reg.fields
            .keys()
            .all(|key| binary::field_descriptor(&key.descriptor).is_err())
    );
    assert_eq!(facts.symbols[first.index()].flags, 0);
    assert!(facts.symbols[first.index()].owner.is_none());
    assert!(
        !facts
            .symbol_name(first)
            .starts_with(contract::ACCESSOR_NAMESPACE)
    );
    assert!(
        field(
            &mut facts,
            &mut reg,
            0,
            ctx.id,
            FileId::NONE,
            MemberRef {
                owner: STATE,
                name: "unknown-channel",
                descriptor: OBJECT
            }
        )
        .unwrap()
        .is_none()
    );
    assert!(
        field(
            &mut facts,
            &mut reg,
            0,
            ctx.id,
            FileId::NONE,
            MemberRef {
                owner: contract::WORDSPEC,
                name: "payloads",
                descriptor: OBJECT
            }
        )
        .unwrap()
        .is_none()
    );
}

#[test]
fn private_engine_input_remains_deferred_opaque_execution_not_a_pure_string_helper() {
    let descriptor = "()Ljava/lang/String;";
    let (facts, mut ctx, data, bytes, mut loader) = fixture("$anonfun$engine$1", descriptor);
    let parsed = binary::parse_class(&bytes.bytes, Limits::default()).unwrap();
    let method = parsed
        .method("$anonfun$engine$1", Some(descriptor))
        .unwrap();
    let modeled = model(
        &facts,
        &Conflicts::new(&facts),
        &mut ctx,
        &mut loader,
        &data,
        &bytes,
        &parsed,
        method,
    )
    .unwrap()
    .unwrap();
    assert!(!modeled.summary.unknown_offsets.is_empty());
    assert!(
        modeled.summary.calls.is_empty(),
        "opaque boundary does not enumerate formatting internals"
    );
    assert!(matches!(
        modeled.summary.values[modeled.summary.returned.unwrap().0 as usize],
        Value::UnknownData
    ));
}

#[test]
fn scoped_conflict_index_rejects_context_and_method_files_but_not_foreign_symbol_scope() {
    let (mut facts, ctx, data, _, _) = fixture("testNames", "()Lscala/collection/immutable/Set;");
    let path = append_text(&mut facts, "normalized-word.class").unwrap();
    let file = FileId(facts.files.len() as u32);
    facts.files.push(FileRecord {
        path,
        source: StrId::NONE,
        revision: StrId::NONE,
        context: ctx.id,
        source_hash: hash(WORD),
        flags: FILE_BINARY_SOURCE,
    });
    facts.issues.push(IssueRecord {
        kind: IssueKind::ContextConflict,
        file,
        symbol: SymbolId::NONE,
        detail: StrId::NONE,
    });
    assert!(Conflicts::new(&facts).relevant(&facts, ctx.id, data.symbol, data.owner));
    let other_name = append_text(&mut facts, "example/Other#method().").unwrap();
    let other = SymbolId(facts.symbols.len() as u32);
    facts.symbols.push(SymbolRecord {
        name: other_name,
        display: StrId::NONE,
        owner: SymbolId::NONE,
        file: FileId::NONE,
        context: ctx.id,
        kind: 3,
        properties: 0,
        signature: StrId::NONE,
        span: Span::default(),
        flags: 0,
    });
    facts.issues[0].symbol = other;
    assert!(!Conflicts::new(&facts).relevant(&facts, ctx.id, data.symbol, data.owner));
    facts.symbols[data.symbol.index()].file = file;
    assert!(Conflicts::new(&facts).relevant(&facts, ctx.id, data.symbol, data.owner));
}
