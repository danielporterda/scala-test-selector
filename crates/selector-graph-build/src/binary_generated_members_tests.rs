use super::*;

/// Normalized source identity/THIS demand over unchanged genuine javac bytes.
/// The method budget has exactly one optional slot: the used method must win
/// over an earlier, unused abstract contract without selecting by label/arity.
#[test]
fn exact_compiler_this_target_precedes_unused_generated_inventory_at_fixed_cap() {
    for requested in [true, false] {
        let directory = tempfile::tempdir().unwrap();
        let fixture =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/native-admission-chain");
        let source =
            std::fs::read_to_string(fixture.join("src/admissioncase/Fixture.java")).unwrap();
        let mut builder = FactBuilder::new();
        let context = builder.intern("normalized:this-demand").unwrap();
        let path = builder.intern("admissioncase/Fixture.java").unwrap();
        let text = builder.intern(&source).unwrap();
        builder.facts.files.push(FileRecord {
            path,
            source: text,
            revision: StrId::NONE,
            context,
            source_hash: ContentHash(Sha256::digest(source.as_bytes()).into()),
            flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
        });
        let receiver = builder
            .ensure_global_symbol("admissioncase/Getter#", context)
            .unwrap();
        let owner = builder
            .ensure_global_symbol("admissioncase/Contract#", context)
            .unwrap();
        builder.facts.symbols[receiver.index()].kind = 13;
        builder.facts.symbols[receiver.index()].flags = SYMBOL_DEFINED;
        builder.facts.symbols[receiver.index()].file = FileId(0);
        builder.facts.symbols[owner.index()].kind = 14;
        let mut methods = Vec::new();
        let mut wanted = SymbolId::NONE;
        for (name, descriptor) in [
            ("aGet", "()Ladmissioncase/Box;"),
            ("unused02", "()I"),
            ("unused03", "()I"),
        ] {
            let spelling = format!("admissioncase/Contract#{name}().");
            let symbol = builder.ensure_global_symbol(&spelling, context).unwrap();
            builder.facts.symbols[symbol.index()].owner = owner;
            // Real Scala getter captures may leave this exact compiler ID kind0.
            if name == "unused03" {
                wanted = symbol;
            }
            methods.push(
                serde_json::json!({"context":"normalized:this-demand", "compiler_symbol":spelling,
                "jvm_owner":"admissioncase/Contract", "jvm_name":name, "descriptor":descriptor}),
            );
        }
        builder.facts.operations.push(OperationRecord {
            body: BodyId(0),
            opcode: Opcode::VirtualCall,
            target: wanted,
            dest: ValueId(1),
            a: ValueId(0),
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span::default(),
            flags: 0,
        });
        builder.facts.bodies.push(BodyRecord {
            symbol: receiver,
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange { start: 0, len: 1 },
            parameters: IdRange::default(),
            body_hash: ContentHash([7; 32]),
            flags: if requested {
                BODY_INITIALIZER
            } else {
                BODY_DEFERRED
            },
        });
        let mut facts = builder.finish().unwrap();
        let receipt: serde_json::Value =
            serde_json::from_slice(&std::fs::read(fixture.join("manifest.json")).unwrap()).unwrap();
        let pinned = receipt["files"]
            .as_array()
            .unwrap()
            .iter()
            .find(|r| r["path"] == "bytecode.jar")
            .unwrap();
        let jar = fixture.join("bytecode.jar");
        assert_eq!(
            ContentHash(Sha256::digest(std::fs::read(&jar).unwrap()).into()).to_string(),
            pinned["sha256"].as_str().unwrap()
        );
        let manifest = directory.path().join("binary.json");
        std::fs::write(&manifest, serde_json::to_vec(&serde_json::json!({
            "version":1,"facts_identity":facts.identity.to_string(),
            "contexts":[{"id":"normalized:this-demand","entries":[{"path":jar,"kind":"jar","sha256":pinned["sha256"]}]}],
            "types":[{"context":"normalized:this-demand","compiler_symbol":"admissioncase/Getter#","jvm_owner":"admissioncase/Getter"},
                     {"context":"normalized:this-demand","compiler_symbol":"admissioncase/Contract#","jvm_owner":"admissioncase/Contract"}],
            "methods":methods
        })).unwrap()).unwrap();
        let mut inputs = load_binary_manifest(&manifest, &facts).unwrap();
        augment_binary_facts_with_limits(
            &mut facts,
            &mut inputs,
            NativeAdmissionLimits {
                methods: 4,
                ..Default::default()
            },
        )
        .unwrap();
        let desired = facts.find_symbol("@jvm/20:admissioncase/Getter8:unused033:()I");
        assert_eq!(
            desired.is_some_and(|id| facts.bodies.iter().any(|b| b.symbol == id)),
            requested
        );
        assert!(
            facts
                .relations
                .iter()
                .any(|r| r.kind == RelationKind::DeferredReceiverDispatch && r.source == receiver)
        );
        assert_eq!(
            facts
                .relations
                .iter()
                .any(|r| r.kind == RelationKind::KnownReceiverDispatch
                    && r.source == receiver
                    && r.target == wanted),
            requested
        );
        assert_eq!(inputs.context_metrics().next().unwrap().derived_methods, 1);
        facts.validate().unwrap();
    }
}

#[test]
fn requested_concrete_contract_selects_real_nearer_override_without_expanding_unused_concretes() {
    // Normalized source-THIS projection over the frozen genuine class hierarchy.
    // ResolveLeaf inherits Mid.ping, which overrides the already admitted Base
    // body; selecting Base just because it is present would be incorrect.
    for requested in [false, true] {
        let directory = tempfile::tempdir().unwrap();
        let fixture =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/binary-resolution");
        let source = std::fs::read_to_string(fixture.join("Resolution.java")).unwrap();
        let mut builder = FactBuilder::new();
        let context = builder.intern("normalized:concrete-this").unwrap();
        let path = builder.intern("Resolution.java").unwrap();
        let text = builder.intern(&source).unwrap();
        builder.facts.files.push(FileRecord {
            path,
            source: text,
            revision: StrId::NONE,
            context,
            source_hash: ContentHash(Sha256::digest(source.as_bytes()).into()),
            flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
        });
        let receiver = builder
            .ensure_global_symbol("fixture/ResolveLeaf#", context)
            .unwrap();
        let owner = builder
            .ensure_global_symbol("fixture/ResolveBase#", context)
            .unwrap();
        builder.facts.symbols[receiver.index()].kind = 13;
        builder.facts.symbols[receiver.index()].flags = SYMBOL_DEFINED;
        builder.facts.symbols[receiver.index()].file = FileId(0);
        builder.facts.symbols[owner.index()].kind = 13;
        let target = builder
            .ensure_global_symbol("fixture/ResolveBase#ping().", context)
            .unwrap();
        let unused = builder
            .ensure_global_symbol("fixture/ResolveBase#inherited().", context)
            .unwrap();
        for id in [target, unused] {
            builder.facts.symbols[id.index()].owner = owner;
        }
        builder.facts.operations.push(OperationRecord {
            body: BodyId(0),
            opcode: Opcode::VirtualCall,
            target,
            dest: ValueId(1),
            a: ValueId(0),
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span::default(),
            flags: 0,
        });
        builder.facts.bodies.push(BodyRecord {
            symbol: receiver,
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange { start: 0, len: 1 },
            parameters: IdRange::default(),
            body_hash: ContentHash([8; 32]),
            flags: if requested {
                BODY_INITIALIZER
            } else {
                BODY_DEFERRED
            },
        });
        let mut facts = builder.finish().unwrap();
        let jar = fixture.join("resolution.jar");
        let pin: serde_json::Value =
            serde_json::from_slice(&std::fs::read(fixture.join("manifest.json")).unwrap()).unwrap();
        let hash = pin["outputs"]
            .as_array()
            .unwrap()
            .iter()
            .find(|r| r["path"] == "resolution.jar")
            .unwrap()["sha256"]
            .clone();
        assert_eq!(
            ContentHash(Sha256::digest(std::fs::read(&jar).unwrap()).into()).to_string(),
            hash.as_str().unwrap()
        );
        let manifest = directory.path().join("binary.json");
        std::fs::write(&manifest,serde_json::to_vec(&serde_json::json!({"version":1,"facts_identity":facts.identity.to_string(),
            "contexts":[{"id":"normalized:concrete-this","entries":[{"path":jar,"kind":"jar","sha256":hash}]}],
            "types":[{"context":"normalized:concrete-this","compiler_symbol":"fixture/ResolveLeaf#","jvm_owner":"fixture/ResolveLeaf"},
                {"context":"normalized:concrete-this","compiler_symbol":"fixture/ResolveBase#","jvm_owner":"fixture/ResolveBase"}],
            "methods":[{"context":"normalized:concrete-this","compiler_symbol":"fixture/ResolveBase#ping().","jvm_owner":"fixture/ResolveBase","jvm_name":"ping","descriptor":"()Ljava/lang/Object;"},
                {"context":"normalized:concrete-this","compiler_symbol":"fixture/ResolveBase#inherited().","jvm_owner":"fixture/ResolveBase","jvm_name":"inherited","descriptor":"()Ljava/lang/Object;"}]
        })).unwrap()).unwrap();
        let mut inputs = load_binary_manifest(&manifest, &facts).unwrap();
        augment_binary_facts_with_limits(
            &mut facts,
            &mut inputs,
            NativeAdmissionLimits {
                methods: 3,
                ..Default::default()
            },
        )
        .unwrap();
        let nearer = facts.find_symbol("@jvm/18:fixture/ResolveMid4:ping20:()Ljava/lang/Object;");
        assert_eq!(
            nearer.is_some_and(|id| facts.bodies.iter().any(|b| b.symbol == id)),
            requested
        );
        assert_eq!(
            facts
                .relations
                .iter()
                .any(|r| r.kind == RelationKind::KnownReceiverDispatch
                    && r.source == receiver
                    && r.target == target),
            requested
        );
        assert!(
            !facts
                .relations
                .iter()
                .any(|r| r.kind == RelationKind::KnownReceiverDispatch
                    && r.source == receiver
                    && r.target == unused)
        );
        assert!(
            !facts
                .relations
                .iter()
                .any(|r| r.kind == RelationKind::Override && r.source == r.target)
        );
        assert_eq!(
            inputs.context_metrics().next().unwrap().derived_methods,
            usize::from(requested)
        );
        facts.validate().unwrap();
    }
}

/// A deliberately minimal source-identity projection over the frozen Scala/JVM
/// fixture. The actual generated lazy getter exists only in the pinned class.
#[test]
fn genuine_generated_getter_method_quota_is_receiver_contract_scoped() {
    let directory = tempfile::tempdir().unwrap();
    let fixture =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/selected-external-apply");
    let source = std::fs::read_to_string(fixture.join("src/selectedexternal/Calls.scala")).unwrap();
    let mut builder = FactBuilder::new();
    let context = builder.intern("scoped-native-context").unwrap();
    let path = builder.intern("selectedexternal/Calls.scala").unwrap();
    let source_id = builder.intern(&source).unwrap();
    builder.facts.files.push(FileRecord {
        path,
        source: source_id,
        revision: StrId::NONE,
        context,
        source_hash: ContentHash(Sha256::digest(source.as_bytes()).into()),
        flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
    });
    let receiver = builder
        .ensure_symbol("selectedexternal/Calls#", FileId(0))
        .unwrap();
    let owner = builder
        .ensure_symbol("selectedexternal/Configuration#", FileId::NONE)
        .unwrap();
    let contract = builder
        .ensure_symbol(
            "selectedexternal/Configuration#PatienceConfig.",
            FileId::NONE,
        )
        .unwrap();
    for symbol in [receiver, owner, contract] {
        builder.facts.symbols[symbol.index()].context = context;
    }
    builder.facts.symbols[receiver.index()].kind = 13;
    builder.facts.symbols[receiver.index()].flags = SYMBOL_DEFINED;
    builder.facts.symbols[receiver.index()].file = FileId(0);
    builder.facts.symbols[owner.index()].kind = 14;
    builder.facts.symbols[contract.index()].owner = owner;
    let mut facts = builder.finish().unwrap();
    let witness: serde_json::Value =
        serde_json::from_slice(&std::fs::read(fixture.join("manifest.json")).unwrap()).unwrap();
    let entries: Vec<_> = ["caller.jar", "library.jar"]
        .iter()
        .map(|name| {
            let path = fixture.join(name);
            let hash = ContentHash(Sha256::digest(std::fs::read(&path).unwrap()).into());
            let pinned = witness["files"]
                .as_array()
                .unwrap()
                .iter()
                .find(|row| row["path"].as_str() == Some(*name))
                .unwrap();
            assert_eq!(pinned["sha256"].as_str().unwrap(), hash.to_string());
            serde_json::json!({"path":path,"kind":"jar","sha256":hash.to_string()})
        })
        .collect();
    let manifest = directory.path().join("binary.json");
    std::fs::write(&manifest, serde_json::to_vec(&serde_json::json!({
        "version":1,
        "facts_identity":facts.identity.to_string(),
        "contexts":[{"id":"scoped-native-context","entries":entries}],
        "types":[
            {"context":"scoped-native-context","compiler_symbol":"selectedexternal/Calls#","jvm_owner":"selectedexternal/Calls"},
            {"context":"scoped-native-context","compiler_symbol":"selectedexternal/Configuration#","jvm_owner":"selectedexternal/Configuration"}
        ],
        "methods":[{"context":"scoped-native-context","compiler_symbol":"selectedexternal/Configuration#PatienceConfig.",
            "jvm_owner":"selectedexternal/Configuration","jvm_name":"PatienceConfig",
            "descriptor":"()Lselectedexternal/Configuration$PatienceConfig$;"}]
    })).unwrap()).unwrap();
    let mut inputs = load_binary_manifest(&manifest, &facts).unwrap();
    assert_eq!(Discovery::new(&facts, &inputs).classes.len(), 1);
    augment_binary_facts_with_limits(
        &mut facts,
        &mut inputs,
        NativeAdmissionLimits {
            methods: 1,
            ..Default::default()
        },
    )
    .unwrap();
    assert!(
        facts
            .relations
            .iter()
            .any(|row| row.kind == RelationKind::DeferredDispatch
                && row.source == receiver
                && row.target == contract
                && row.file == FileId(0)),
        "relations={:?}; issues={:?}; metrics={:?}",
        facts.relations,
        facts
            .issues
            .iter()
            .map(|i| (i.symbol, i.kind, facts.text(i.detail)))
            .collect::<Vec<_>>(),
        inputs.context_metrics().collect::<Vec<_>>()
    );
    assert!(
        !facts.issues.iter().any(|issue| issue.symbol == receiver
            && facts.text(issue.detail).contains("method admission budget")),
        "an unused compiler-generated getter does not poison its entire source class"
    );
    let metrics = inputs.context_metrics().next().unwrap();
    assert_eq!(metrics.scoped_dispatch_rows, 1);
    assert_eq!(metrics.method_guard_rows, 0);
    assert!(metrics.deferred_admissions > 0);
    facts.validate().unwrap();
}

fn fixture() -> (FactSnapshot, Registry, SymbolId) {
    let mut builder = FactBuilder::new();
    let context = builder.intern("compile-context").unwrap();
    let empty = builder.intern("").unwrap();
    for (path, source, flags, hash) in [
        (
            "Caller.scala",
            "class Caller extends Contract",
            SOURCE_VERIFIED | SYNTAX_VERIFIED,
            1,
        ),
        (
            "capture.jar!/fixture/Contract.class",
            "",
            FILE_BINARY_SOURCE,
            2,
        ),
    ] {
        let path = builder.intern(path).unwrap();
        let source = builder.intern(source).unwrap();
        builder.facts.files.push(FileRecord {
            path,
            source,
            revision: StrId::NONE,
            context,
            source_hash: ContentHash([hash; 32]),
            flags,
        });
    }
    let contract = builder
        .ensure_symbol("fixture/Contract#", FileId::NONE)
        .unwrap();
    let target = builder
        .ensure_symbol("fixture/Contract#value.", FileId::NONE)
        .unwrap();
    let root = builder.ensure_symbol("fixture/Caller#", FileId(0)).unwrap();
    for symbol in [contract, target, root] {
        builder.facts.symbols[symbol.index()].context = context;
    }
    builder.facts.symbols[contract.index()].kind = 14;
    builder.facts.symbols[target.index()].owner = contract;
    builder.facts.symbols[root.index()].kind = 13;
    builder.facts.symbols[root.index()].flags = SYMBOL_DEFINED;
    builder.facts.operations.push(OperationRecord {
        body: BodyId(0),
        opcode: Opcode::Call,
        target,
        dest: ValueId(1),
        a: ValueId(0),
        b: ValueId::NONE,
        arguments: IdRange::default(),
        span: Span { start: 0, end: 29 },
        flags: CALLBACK_ARGUMENT_PRESENT,
    });
    builder.facts.bodies.push(BodyRecord {
        symbol: root,
        file: FileId(0),
        span: Span { start: 0, end: 29 },
        name_span: Span::default(),
        operations: IdRange { start: 0, len: 1 },
        parameters: IdRange::default(),
        body_hash: ContentHash([3; 32]),
        flags: BODY_INITIALIZER,
    });
    let facts = builder.finish().unwrap();
    let registry = Registry {
        types: HashMap::new(),
        methods: HashMap::from([(
            MethodKey {
                context: 0,
                owner: "fixture/Contract".into(),
                name: "value".into(),
                descriptor: "()Ljava/lang/Object;".into(),
            },
            MethodData {
                symbol: target,
                owner: contract,
                flags: 0x0401,
                receiver_parameter: None,
            },
        )]),
        method_events: Vec::new(),
        synthetic_methods: 0,
        fields: HashMap::new(),
        accessors: accessors::State::default(),
        files: HashMap::from([((0, "fixture/Contract".into()), FileId(1))]),
        empty,
        initialized: HashSet::new(),
        static_phases: HashMap::new(),
        static_active: HashSet::new(),
        bootstrap: HashMap::new(),
    };
    (facts, registry, target)
}

#[test]
fn this_priority_is_exact_source_receiver_authority_not_capture_or_name_matching() {
    let (mut facts, _, target) = fixture();
    let receiver = facts.bodies[0].symbol;
    // ensure_symbol's file argument supplies context for globals; a verified
    // written definition separately owns its file, as Discovery::new requires.
    facts.symbols[receiver.index()].file = FileId(0);
    let class = ConcreteClass {
        context: 0,
        owner: "fixture/Caller".into(),
        symbol: receiver,
        source_product: true,
        inherited_owners: None,
        next_contract: 0,
        queued: true,
    };
    let classes = [class];
    assert_eq!(compiler_this_requests(&facts, &classes), [(target, 0)]);
    for case in 0..9 {
        let body_flags = facts.bodies[0].flags;
        let operation = facts.operations[0];
        let file = facts.files[0];
        let class = facts.symbols[receiver.index()];
        match case {
            0 => facts.bodies[0].flags |= BODY_DEFERRED,
            1 => facts.bodies[0].flags |= BODY_BINARY_RECIPE,
            2 => facts.bodies[0].flags |= BODY_STATIC_INITIALIZER,
            3 => facts.operations[0].a = ValueId(1),
            4 => facts.operations[0].flags |= OP_SUPER,
            5 => facts.files[0].context = StrId::NONE,
            6 => facts.files[0].flags = SOURCE_VERIFIED,
            7 => facts.symbols[receiver.index()].flags = 0,
            8 => facts.symbols[receiver.index()].file = FileId::NONE,
            _ => unreachable!(),
        }
        assert!(
            compiler_this_requests(&facts, &classes).is_empty(),
            "case {case}"
        );
        facts.bodies[0].flags = body_flags;
        facts.operations[0] = operation;
        facts.files[0] = file;
        facts.symbols[receiver.index()] = class;
    }
}

#[test]
fn exact_abstract_instance_metadata_repairs_source_call_and_preserves_callsite_identity() {
    let (mut facts, registry, target) = fixture();
    facts
        .bound_classes
        .push(facts.symbols[target.index()].owner);
    facts.result_bounds.push(ResultBoundRecord {
        symbol: target,
        operation: OperationId(0),
        classes: IdRange { start: 0, len: 1 },
    });
    let before = facts.bodies[0].body_hash;
    repair_dispatch(&mut facts, &registry).unwrap();
    let op = facts.operations[0];
    assert_eq!(
        (op.opcode, op.target, op.a, op.dest),
        (Opcode::VirtualCall, target, ValueId(0), ValueId(1))
    );
    assert_eq!(op.flags, CALLBACK_ARGUMENT_PRESENT);
    assert_eq!(facts.result_bounds[0].operation, OperationId(0));
    assert_ne!(facts.bodies[0].body_hash, before);
    let after = facts.bodies[0].body_hash;
    repair_dispatch(&mut facts, &registry).unwrap();
    assert_eq!(facts.bodies[0].body_hash, after);
}

#[test]
fn native_special_super_missing_receiver_and_wrong_arity_cannot_become_virtual() {
    for case in 0..7 {
        let (mut facts, registry, _) = fixture();
        match case {
            0 => facts.bodies[0].flags |= BODY_BINARY_RECIPE,
            1 => facts.operations[0].flags |= OP_SUPER,
            2 => facts.operations[0].flags |= OP_SUPER | OP_QUALIFIED_SUPER,
            3 => facts.operations[0].a = ValueId::NONE,
            4 => {
                facts.operations[0].arguments.len = 1;
                facts.operands.push(ValueId(2));
            }
            5 => facts.files[0].flags = SOURCE_VERIFIED,
            6 => facts.files[0].flags = SYNTAX_VERIFIED,
            _ => unreachable!(),
        }
        let before = facts.bodies[0].body_hash;
        repair_dispatch(&mut facts, &registry).unwrap();
        assert_eq!(facts.operations[0].opcode, Opcode::Call, "case{case}");
        assert_eq!(facts.bodies[0].body_hash, before);
    }
}

#[test]
fn private_static_concrete_source_defined_and_ambiguous_authorities_stay_direct() {
    for case in 0..8 {
        let (mut facts, mut registry, target) = fixture();
        match case {
            0 => registry.methods.values_mut().next().unwrap().flags |= 0x0002,
            1 => registry.methods.values_mut().next().unwrap().flags |= 0x0008,
            2 => registry.methods.values_mut().next().unwrap().flags &= !0x0400,
            3 => {
                registry
                    .methods
                    .values_mut()
                    .next()
                    .unwrap()
                    .receiver_parameter = Some(0)
            }
            4 => facts.symbols[target.index()].flags |= SYMBOL_DEFINED,
            5 => facts.symbols[target.index()].kind = 3,
            6 => registry.files.clear(),
            7 => {
                let (key, data) = registry.methods.iter().next().unwrap();
                let mut key = key.clone();
                let data = data.clone();
                key.descriptor = "(I)Ljava/lang/Object;".into();
                registry.methods.insert(key, data);
            }
            _ => unreachable!(),
        }
        repair_dispatch(&mut facts, &registry).unwrap();
        assert_eq!(facts.operations[0].opcode, Opcode::Call, "case{case}");
    }
}

#[test]
fn source_dispatch_hash_is_bound_to_exact_admitted_contract_class_hash() {
    let (mut first, registry, _) = fixture();
    let (mut second, _, _) = fixture();
    second.files[1].source_hash = ContentHash([4; 32]);
    repair_dispatch(&mut first, &registry).unwrap();
    repair_dispatch(&mut second, &registry).unwrap();
    assert_ne!(first.bodies[0].body_hash, second.bodies[0].body_hash);
    let (mut repeated, _, _) = fixture();
    repair_dispatch(&mut repeated, &registry).unwrap();
    assert_eq!(first.bodies[0].body_hash, repeated.bodies[0].body_hash);
}

fn fixture_class(root: &str, owner: &str) -> Option<Arc<ClassBytes>> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../fixtures")
        .join(root)
        .join("classes")
        .join(format!("{owner}.class"));
    let bytes = std::fs::read(&path).ok()?;
    let metadata =
        Arc::new(binary::ClassMetadata::new(Arc::from(bytes.clone()), Limits::default()).unwrap());
    Some(Arc::new(ClassBytes {
        metadata,
        hash: ContentHash(Sha256::digest(&bytes).into()),
        bytes: bytes.into(),
        origin: path.display().to_string(),
    }))
}

#[test]
fn genuine_class_chain_selects_exact_public_declaring_owner_and_nearest_override() {
    for (name, descriptor, expected) in [
        ("inherited", "()Ljava/lang/Object;", "fixture/ResolveBase"),
        ("ping", "()Ljava/lang/Object;", "fixture/ResolveMid"),
        ("overload", "(I)Ljava/lang/Object;", "fixture/ResolveBase"),
        (
            "overload",
            "(Ljava/lang/String;)Ljava/lang/Object;",
            "fixture/ResolveBase",
        ),
    ] {
        let owner = class_chain_member(
            "fixture/ResolveLeaf",
            name,
            descriptor,
            |owner| Ok(fixture_class("binary-resolution", owner)),
            |_, _| false,
        )
        .unwrap();
        assert_eq!(owner.as_deref(), Some(expected), "{name}{descriptor}");
    }
}

#[test]
fn concrete_lookup_keeps_missing_hierarchy_wrong_descriptor_and_source_overlays_open() {
    for case in 0..6 {
        let result = class_chain_member(
            "fixture/ResolveLeaf",
            "inherited",
            if case == 0 {
                "(I)Ljava/lang/Object;"
            } else {
                "()Ljava/lang/Object;"
            },
            |owner| {
                Ok(if case == 1 && owner == "fixture/ResolveMid" {
                    None
                } else if case == 5 && owner == "fixture/ResolveMid" {
                    // Structural malformed-header control: a provider supplies a
                    // different class. It must not authorize a superclass hop.
                    fixture_class("binary-resolution", "fixture/ResolveBase")
                } else {
                    fixture_class("binary-resolution", owner)
                })
            },
            |owner, name| {
                name == "inherited"
                    && match case {
                        2 => owner == "fixture/ResolveLeaf",
                        3 => owner == "fixture/ResolveMid",
                        4 => owner == "fixture/ResolveBase",
                        _ => false,
                    }
            },
        )
        .unwrap();
        assert!(result.is_none(), "case {case}");
    }
}

#[test]
fn genuine_private_static_and_interface_default_methods_are_not_concrete_bridges() {
    for (root, owner, name, descriptor) in [
        (
            "binary-resolution",
            "fixture/ResolveLeaf",
            "staticInherited",
            "()Ljava/lang/Object;",
        ),
        ("native-lambdas", "lambdacase/Probe", "next", "()V"),
        ("native-lambdas", "lambdacase/Probe", "runStatic", "()V"),
        (
            "binary-resolution",
            "fixture/DefaultLeaf",
            "choose",
            "()Ljava/lang/Object;",
        ),
        (
            "binary-resolution",
            "fixture/DefaultOne",
            "choose",
            "()Ljava/lang/Object;",
        ),
    ] {
        assert!(
            class_chain_member(
                owner,
                name,
                descriptor,
                |owner| Ok(fixture_class(root, owner)),
                |_, _| false,
            )
            .unwrap()
            .is_none(),
            "{owner}.{name}{descriptor}"
        );
    }
}

#[test]
fn concrete_lookup_uses_ordered_hash_verified_provider_without_fallback() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../fixtures/binary-resolution/resolution.jar");
    let digest = ContentHash(Sha256::digest(std::fs::read(&path).unwrap()).into());
    for case in 0..3 {
        let mut entries = Vec::new();
        if case == 1 {
            entries.push(ClasspathEntry {
                path: PathBuf::from("unavailable-before-provider.jar"),
                sha256: ContentHash::default(),
                kind: EntryKind::Unavailable,
            });
        }
        entries.push(ClasspathEntry {
            path: path.clone(),
            sha256: if case == 2 {
                ContentHash([123; 32])
            } else {
                digest
            },
            kind: EntryKind::Jar,
        });
        let mut loader = CapturedClasspath::new(entries.clone(), Limits::default()).unwrap();
        let mut context = AdmittedContext {
            id: StrId(0),
            name: "test-context".into(),
            cache_metrics: ClassCacheMetrics::default(),
            phase: "test",
            active_method: SymbolId::NONE,
            active_file: FileId::NONE,
            pending_methods: 0,
            admission: Admission::default(),
            entries,
            classes: HashMap::new(),
            shared_metadata: SharedMetadata::default(),
            java_feature: None,
            entries_at: Vec::new(),
        };
        let result = class_chain_member(
            "fixture/ResolveLeaf",
            "inherited",
            "()Ljava/lang/Object;",
            |owner| cache_class(&mut context, &mut loader, owner),
            |_, _| false,
        );
        match case {
            0 => assert_eq!(result.unwrap().as_deref(), Some("fixture/ResolveBase")),
            1 => assert!(
                result.unwrap().is_none(),
                "opaque earlier provider cannot be bypassed"
            ),
            2 => assert!(
                result.is_err(),
                "changed archive hash cannot authorize an implementation"
            ),
            _ => unreachable!(),
        }
        assert_eq!(
            context.cache_metrics.found,
            context
                .classes
                .values()
                .filter(|value| matches!(value, CachedClass::Found(_)))
                .count()
        );
        assert_eq!(
            context.cache_metrics.unknown,
            context
                .classes
                .values()
                .filter(|value| matches!(value, CachedClass::Unknown(_)))
                .count()
        );
        assert_eq!(
            context.cache_metrics.retained_bytes,
            context
                .classes
                .values()
                .map(|value| match value {
                    CachedClass::Found(class) => class.bytes.len(),
                    CachedClass::Unknown(_) => 0,
                })
                .sum::<usize>()
        );
    }
}

#[test]
fn allocation_candidates_require_admitted_native_header_and_preserve_source_authority() {
    let (mut facts, _, symbol) = fixture();
    let inputs = OwnedBinaryInputs {
        identity: ContentHash::default(),
        raw_identity: ContentHash::default(),
        contexts: Vec::new(),
        types: HashMap::new(),
        type_aliases: Vec::new(),
        methods: Vec::new(),
        admitted: Vec::new(),
        envelope_cache: binary::EnvelopeCache::new(0),
        platform_inputs: Vec::new(),
        platform_contexts: HashSet::new(),
    };
    let mut discovery = Discovery::new(&facts, &inputs);
    // This isolated classification test does not load a context.
    discovery.queues.push(VecDeque::new());
    for flags in [
        0,
        SYMBOL_NATIVE_BINARY,
        SYMBOL_DEFINED | SYMBOL_JVM_CLASS_HEADER_VERIFIED,
    ] {
        facts.symbols[symbol.index()].flags = flags;
        discovery.allocation(&facts, 0, "fixture/Concrete", symbol);
        assert!(discovery.classes.is_empty(), "flags {flags}");
    }
    facts.symbols[symbol.index()].flags = SYMBOL_NATIVE_BINARY | SYMBOL_JVM_CLASS_HEADER_VERIFIED;
    discovery.allocation(&facts, 0, "fixture/Concrete", symbol);
    discovery.allocation(&facts, 0, "fixture/Concrete", symbol);
    assert_eq!(
        discovery.classes.len(),
        1,
        "repeated allocations share one class candidate"
    );
    assert!(!discovery.classes[0].source_product);
    assert_eq!(
        discovery.queues[0],
        VecDeque::from([0]),
        "late allocations remain pending discovery"
    );
}

#[test]
fn a_contract_batch_loads_each_superclass_once() {
    let mut loads = HashMap::<String, usize>::new();
    let implementations = class_chain_members(
        "fixture/ResolveLeaf",
        &[
            ("inherited", "()Ljava/lang/Object;"),
            ("ping", "()Ljava/lang/Object;"),
            ("overload", "(I)Ljava/lang/Object;"),
        ],
        |owner| {
            *loads.entry(owner.to_owned()).or_default() += 1;
            Ok(fixture_class("binary-resolution", owner))
        },
        |_, _| false,
    )
    .unwrap();
    assert_eq!(
        implementations.owners,
        [
            "fixture/ResolveLeaf",
            "fixture/ResolveMid",
            "fixture/ResolveBase"
        ]
    );
    assert_eq!(implementations.targets, [Some(2), Some(1), Some(2)]);
    assert!(loads.values().all(|&count| count == 1));
}

#[test]
fn metadata_sharing_follows_each_context_provider_proof_and_keeps_origins_separate() {
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../fixtures/binary-resolution/resolution.jar");
    let content = std::fs::read(fixture).unwrap();
    let digest = ContentHash(Sha256::digest(&content).into());
    let directory = tempfile::tempdir().unwrap();
    let shared_metadata = SharedMetadata::default();
    let mut first = None;
    for case in 0..4 {
        let path = directory.path().join(format!("provider-{case}.jar"));
        std::fs::write(&path, &content).unwrap();
        let mut entries = Vec::new();
        if case == 3 {
            entries.push(ClasspathEntry {
                path: directory.path().join("opaque-before-same-content.jar"),
                sha256: ContentHash::default(),
                kind: EntryKind::Unavailable,
            });
        }
        entries.push(ClasspathEntry {
            path: path.clone(),
            kind: EntryKind::Jar,
            sha256: if case == 2 {
                ContentHash([42; 32])
            } else {
                digest
            },
        });
        let mut loader = CapturedClasspath::new(entries.clone(), Limits::default()).unwrap();
        let mut context = AdmittedContext {
            id: StrId(case),
            name: format!("context-{case}"),
            cache_metrics: ClassCacheMetrics::default(),
            phase: "test",
            active_method: SymbolId::NONE,
            active_file: FileId::NONE,
            pending_methods: 0,
            admission: Admission::default(),
            entries,
            classes: HashMap::new(),
            shared_metadata: shared_metadata.clone(),
            java_feature: None,
            entries_at: Vec::new(),
        };
        let found = cache_class(&mut context, &mut loader, "fixture/ResolveLeaf");
        match case {
            0 => first = found.unwrap(),
            1 => {
                let found = found.unwrap().unwrap();
                let first = first.as_ref().unwrap();
                assert!(Arc::ptr_eq(&first.metadata, &found.metadata));
                assert!(Arc::ptr_eq(&first.bytes, &found.bytes));
                assert_ne!(first.origin, found.origin);
                assert!(found.origin.starts_with(path.to_str().unwrap()));
            }
            2 => assert!(
                found.is_err(),
                "known content cannot waive a mismatched provider hash"
            ),
            3 => assert!(
                found.unwrap().is_none(),
                "known content cannot bypass an opaque earlier provider"
            ),
            _ => unreachable!(),
        }
    }
}

#[test]
fn cross_context_contract_requires_exact_native_header_method_and_file_authority() {
    let class = fixture_class("binary-resolution", "fixture/AbstractOne").unwrap();
    let method = class
        .metadata
        .methods()
        .find(|m| m.flags & 0x0401 == 0x0401)
        .unwrap();
    let (mut facts, _, target) = fixture();
    let owner = facts.symbols[target.index()].owner;
    facts.symbols[target.index()].file = FileId(1);
    facts.symbols[target.index()].flags = SYMBOL_NATIVE_BINARY;
    facts.files[1].source_hash = class.hash;
    let key = MethodKey {
        context: 0,
        owner: class.metadata.name().into(),
        name: method.name.into(),
        descriptor: method.descriptor.into(),
    };
    let data = MethodData {
        symbol: target,
        owner,
        flags: method.flags,
        receiver_parameter: None,
    };
    let mut context = AdmittedContext {
        id: facts.symbols[target.index()].context,
        name: "contract-context".into(),
        cache_metrics: ClassCacheMetrics::default(),
        phase: "test",
        active_method: SymbolId::NONE,
        active_file: FileId::NONE,
        pending_methods: 0,
        admission: Admission::default(),
        entries: Vec::new(),
        classes: HashMap::from([(key.owner.clone(), CachedClass::Found(class.clone()))]),
        shared_metadata: SharedMetadata::default(),
        java_feature: None,
        entries_at: Vec::new(),
    };
    assert!(contract_proof(&facts, &context, &key, &data, &HashSet::new()).is_some());
    for case in 0..10 {
        let mut data = data.clone();
        let mut key = key.clone();
        let old_symbol = facts.symbols[target.index()];
        let old_file = facts.files[1];
        let old_context = context.id;
        let mut conflicts = HashSet::new();
        match case {
            0 => data.flags |= 8,
            1 => data.receiver_parameter = Some(0),
            2 => key.descriptor = "(I)V".into(),
            3 => context.id = StrId::NONE,
            4 => facts.symbols[target.index()].flags |= SYMBOL_DEFINED,
            5 => facts.files[1].source_hash = ContentHash([9; 32]),
            6 => facts.files[1].flags = SOURCE_VERIFIED,
            7 => {
                conflicts.insert(target);
            }
            8 => {
                conflicts.insert(owner);
            }
            9 => facts.symbols[target.index()].file = FileId::NONE,
            _ => unreachable!(),
        }
        assert!(
            contract_proof(&facts, &context, &key, &data, &conflicts).is_none(),
            "case {case}"
        );
        facts.symbols[target.index()] = old_symbol;
        facts.files[1] = old_file;
        context.id = old_context;
    }
}
