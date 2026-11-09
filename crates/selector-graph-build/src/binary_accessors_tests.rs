use super::*;

const WORD: &[u8] = include_bytes!(
    "../../../fixtures/scalatest-execution/classes/org/scalatest/wordspec/AnyWordSpecLike.class"
);

// Normalized private provider receipt over unchanged genuine class bytes.
// Public acceptance separately exercises ordered archive admission.
fn fixture() -> (FactSnapshot, Registry, AdmittedContext, CapturedClasspath) {
    let mut builder = FactBuilder::new();
    let context = builder.intern("accessor-context").unwrap();
    let empty = builder.intern("").unwrap();
    let owner = builder
        .ensure_global_symbol("org/scalatest/wordspec/AnyWordSpecLike#", context)
        .unwrap();
    builder.facts.symbols[owner.index()].kind = 14;
    let slot = builder
        .ensure_global_symbol(
            &format!(
                "{}subjectRegistrationFunction",
                contract::ACCESSOR_NAMESPACE
            ),
            context,
        )
        .unwrap();
    builder.facts.symbols[slot.index()].kind = 20;
    let bytes: Arc<[u8]> = Arc::from(WORD);
    let class = Arc::new(ClassBytes {
        hash: ContentHash(Sha256::digest(&bytes).into()),
        metadata: Arc::new(binary::ClassMetadata::new(bytes.clone(), Limits::default()).unwrap()),
        bytes,
        origin: format!("/normalized/wordspec.jar!/{}.class", contract::WORDSPEC),
    });
    let mut state = State::default();
    state.slots.insert(0, [slot; 8]);
    let registry = Registry {
        types: [((0, contract::WORDSPEC.to_owned()), owner)].into(),
        methods: HashMap::new(),
        method_events: Vec::new(),
        synthetic_methods: 0,
        fields: HashMap::new(),
        accessors: state,
        files: HashMap::new(),
        empty,
        initialized: HashSet::new(),
        static_phases: HashMap::new(),
        static_active: HashSet::new(),
        bootstrap: HashMap::new(),
    };
    let context = AdmittedContext {
        id: context,
        name: "accessor-context".into(),
        cache_metrics: Default::default(),
        phase: "accessor-test",
        active_method: SymbolId::NONE,
        active_file: FileId::NONE,
        pending_methods: 0,
        admission: Admission::default(),
        entries: vec![ClasspathEntry {
            path: "/normalized/wordspec.jar".into(),
            sha256: ContentHash::from_hex(contract::WORDSPEC_ARCHIVE).unwrap(),
            kind: EntryKind::Jar,
        }],
        classes: [(contract::WORDSPEC.to_owned(), CachedClass::Found(class))].into(),
        shared_metadata: SharedMetadata::default(),
        java_feature: None,
        entries_at: Vec::new(),
    };
    (
        builder.facts,
        registry,
        context,
        CapturedClasspath::new(Vec::new(), Limits::default()).unwrap(),
    )
}

fn method(
    facts: &mut FactSnapshot,
    context: &AdmittedContext,
    registry: &Registry,
    kind: AccessorKind,
) -> (MethodKey, MethodData) {
    let spec = &contract::ACCESSORS[4];
    let (get, set) = descriptors(spec);
    let (name, descriptor) = if kind == AccessorKind::Get {
        (spec.getter, get)
    } else {
        (spec.setter, set)
    };
    let owner = registry.types[&(0, contract::WORDSPEC.to_owned())];
    let symbol = super::super::declare(
        facts,
        context.id,
        owner,
        &native_name(contract::WORDSPEC, name, &descriptor),
        3,
        FileId::NONE,
        1025,
    )
    .unwrap();
    (
        MethodKey {
            context: 0,
            owner: contract::WORDSPEC.into(),
            name: name.into(),
            descriptor,
        },
        MethodData {
            symbol,
            owner,
            flags: 1025,
            receiver_parameter: None,
        },
    )
}

#[test]
fn genuine_declared_pair_is_field_alias_transport_without_callback_execution() {
    let (mut facts, mut registry, mut context, mut loader) = fixture();
    let mut existing = HashSet::new();
    for kind in [AccessorKind::Get, AccessorKind::Set] {
        let (key, data) = method(&mut facts, &context, &registry, kind);
        assert!(
            materialize(
                &mut facts,
                &mut registry,
                0,
                &mut context,
                &mut loader,
                &key,
                &data,
                &existing
            )
            .unwrap()
        );
        existing.insert(data.symbol);
    }
    let get = &facts.bodies[0];
    let set = &facts.bodies[1];
    let load = &facts.operations[get.operations.range()][0];
    let store = &facts.operations[set.operations.range()][1];
    assert_eq!(
        (load.opcode, store.opcode),
        (Opcode::LoadField, Opcode::StoreField)
    );
    assert_eq!(load.target, store.target);
    assert_eq!(
        (load.a, store.a, store.b),
        (ValueId(0), ValueId(0), ValueId(1))
    );
    assert_eq!(facts.operands[set.parameters.range()], [ValueId(1)]);
    assert!(!facts.operations.iter().any(|op| matches!(
        op.opcode,
        Opcode::Call | Opcode::VirtualCall | Opcode::InvokeCallback | Opcode::Initialize
    )));
    assert_eq!(context.cache_metrics.trusted_runtime_models, 2);
    facts.validate().unwrap();
}

#[test]
fn written_body_and_value_initializer_are_never_replaced_by_property_law() {
    for initializer in [false, true] {
        let (mut facts, mut registry, mut context, mut loader) = fixture();
        let (key, data) = method(&mut facts, &context, &registry, AccessorKind::Get);
        if !initializer {
            facts.symbols[data.symbol.index()].flags |= SYMBOL_DEFINED;
        }
        let existing = if initializer {
            [data.symbol].into()
        } else {
            HashSet::new()
        };
        assert!(
            !materialize(
                &mut facts,
                &mut registry,
                0,
                &mut context,
                &mut loader,
                &key,
                &data,
                &existing
            )
            .unwrap()
        );
        assert!(facts.bodies.is_empty());
    }
}

#[test]
fn missing_source_owner_kind_is_not_absence_of_custom_property_logic() {
    let (mut facts, mut registry, mut context, mut loader) = fixture();
    let (key, data) = method(&mut facts, &context, &registry, AccessorKind::Get);
    facts.symbols[data.owner.index()].flags |= SYMBOL_DEFINED;
    facts.symbols[data.owner.index()].kind = 0;
    assert!(
        !materialize(
            &mut facts,
            &mut registry,
            0,
            &mut context,
            &mut loader,
            &key,
            &data,
            &HashSet::new()
        )
        .unwrap()
    );
    assert!(facts.bodies.is_empty());
    assert_eq!(
        facts.symbols[data.owner.index()].kind,
        0,
        "the model does not repair missing source authority"
    );
}

#[test]
fn source_getter_val_and_decoded_setter_names_block_the_same_slot() {
    for name in [
        "subjectRegistrationFunction",
        contract::ACCESSORS[4].setter,
        "org$scalatest$wordspec$AnyWordSpecLike$_setter_$subjectRegistrationFunction_=",
        "subjectRegistrationFunction_=",
    ] {
        let (mut facts, mut registry, context, _) = fixture();
        let owner = registry.types[&(0, contract::WORDSPEC.to_owned())];
        facts.symbols[owner.index()].flags |= SYMBOL_DEFINED;
        let name = format!("org/scalatest/wordspec/AnyWordSpecLike#`{name}`().");
        let symbol =
            super::super::declare(&mut facts, context.id, owner, &name, 3, FileId::NONE, 0)
                .unwrap();
        facts.symbols[symbol.index()].flags = SYMBOL_DEFINED;
        source_index(&facts, &mut registry.accessors);
        assert!(
            source_blocks(&registry.accessors, contract::WORDSPEC, 4),
            "{name}"
        );
        assert!(!source_blocks(&registry.accessors, contract::WORDSPEC, 0));
        assert_eq!(registry.accessors.source_members.len(), 1);
    }
}

#[test]
fn exact_backing_field_slot_alias_requires_instance_descriptor_and_provider() {
    let (facts, mut registry, mut context, mut loader) = fixture();
    let member = MemberRef {
        owner: contract::WORDSPEC,
        name: contract::ACCESSORS[4].getter,
        descriptor: contract::ACCESSORS[4].value_descriptor,
    };
    let slot = registry.accessors.slots[&0][4];
    assert_eq!(
        backing_field(
            &facts,
            &mut registry,
            0,
            &mut context,
            &mut loader,
            member,
            0
        )
        .unwrap(),
        Some(slot)
    );
    assert_eq!(
        backing_field(
            &facts,
            &mut registry,
            0,
            &mut context,
            &mut loader,
            member,
            8
        )
        .unwrap(),
        None
    );
    assert_eq!(
        backing_field(
            &facts,
            &mut registry,
            0,
            &mut context,
            &mut loader,
            MemberRef {
                descriptor: "Ljava/lang/Object;",
                ..member
            },
            0
        )
        .unwrap(),
        None
    );
    context.entries[0].sha256 = ContentHash([9; 32]);
    registry.accessors.owners.clear();
    assert_eq!(
        backing_field(
            &facts,
            &mut registry,
            0,
            &mut context,
            &mut loader,
            member,
            0
        )
        .unwrap(),
        None
    );
}

#[test]
fn global_context_and_symbol_conflicts_revoke_property_authority() {
    // Global, own file/context, exact member, exact owner, and unrelated file.
    for scope in 0..5 {
        let (mut facts, mut registry, mut context, mut loader) = fixture();
        let (key, data) = method(&mut facts, &context, &registry, AccessorKind::Get);
        let foreign = append_text(&mut facts, "foreign-context").unwrap();
        let conflict_file = FileId::checked(facts.files.len()).unwrap();
        facts.files.push(FileRecord {
            path: registry.empty,
            source: registry.empty,
            revision: StrId::NONE,
            context: if scope == 4 { foreign } else { context.id },
            source_hash: ContentHash([4; 32]),
            flags: FILE_BINARY_SOURCE,
        });
        facts.issues.push(IssueRecord {
            kind: IssueKind::ContextConflict,
            file: if matches!(scope, 1 | 4) {
                conflict_file
            } else {
                FileId::NONE
            },
            symbol: match scope {
                2 => data.symbol,
                3 => data.owner,
                _ => SymbolId::NONE,
            },
            detail: StrId::NONE,
        });
        source_index(&facts, &mut registry.accessors);
        let modeled = materialize(
            &mut facts,
            &mut registry,
            0,
            &mut context,
            &mut loader,
            &key,
            &data,
            &HashSet::new(),
        )
        .unwrap();
        assert_eq!(modeled, scope == 4, "scope {scope}");
        assert_eq!(facts.bodies.len(), usize::from(scope == 4));
        if scope != 4 {
            assert!(
                !trusted_receiver(
                    &facts,
                    &mut registry,
                    0,
                    &mut context,
                    &mut loader,
                    contract::WORDSPEC,
                    data.symbol,
                    &key.name,
                    &key.descriptor
                )
                .unwrap()
            );
            assert_eq!(
                backing_field(
                    &facts,
                    &mut registry,
                    0,
                    &mut context,
                    &mut loader,
                    MemberRef {
                        owner: contract::WORDSPEC,
                        name: contract::ACCESSORS[4].getter,
                        descriptor: contract::ACCESSORS[4].value_descriptor,
                    },
                    0
                )
                .unwrap(),
                if scope == 2 {
                    Some(registry.accessors.slots[&0][4])
                } else {
                    None
                }
            );
        }
    }
}
