use super::*;

fn fixture() -> (
    FactSnapshot,
    OwnedBinaryInputs,
    Registry,
    HashSet<(SymbolId, SymbolId)>,
) {
    let mut builder = FactBuilder::new();
    let context = builder.intern("verified-context").unwrap();
    let path = builder.intern("source.scala").unwrap();
    let empty = builder.intern("").unwrap();
    builder.facts.files.push(FileRecord {
        path,
        source: empty,
        revision: StrId::NONE,
        context,
        source_hash: ContentHash([1; 32]),
        flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
    });
    let root =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/binary-resolution/classes");
    let mut classes = HashMap::new();
    let mut types = HashMap::new();
    for owner in [
        "java/lang/Object",
        "fixture/ResolveBase",
        "fixture/ResolveMid",
        "fixture/ResolveLeaf",
    ] {
        let bytes: Arc<[u8]> = std::fs::read(root.join(format!("{owner}.class")))
            .unwrap()
            .into();
        let metadata =
            Arc::new(binary::ClassMetadata::new(bytes.clone(), Limits::default()).unwrap());
        let symbol = builder
            .ensure_symbol(&format!("{owner}#"), FileId(0))
            .unwrap();
        let declaration = &mut builder.facts.symbols[symbol.index()];
        declaration.context = context;
        declaration.kind = nominal_kind(metadata.flags());
        declaration.flags = SYMBOL_NATIVE_BINARY | SYMBOL_JVM_CLASS_HEADER_VERIFIED;
        types.insert((0, owner.to_owned()), symbol);
        classes.insert(
            owner.to_owned(),
            CachedClass::Found(Arc::new(ClassBytes {
                hash: metadata.hash(),
                metadata,
                bytes,
                origin: format!("verified.jar!/{owner}.class"),
            })),
        );
    }
    let mut parents = HashSet::new();
    for ((index, owner), source) in &types {
        let CachedClass::Found(class) = &classes[owner] else {
            unreachable!()
        };
        for parent in class
            .metadata
            .parent()
            .into_iter()
            .chain(class.metadata.interfaces())
        {
            let target = types[&(*index, parent.to_owned())];
            parents.insert((*source, target));
            builder.facts.relations.push(RelationRecord {
                source: *source,
                target,
                kind: RelationKind::Parent,
                file: FileId(0),
            });
        }
    }
    let registry = Registry {
        types: types.clone(),
        methods: HashMap::new(),
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
    let inputs = OwnedBinaryInputs {
        identity: ContentHash::default(),
        raw_identity: ContentHash::default(),
        contexts: vec![AdmittedContext {
            id: context,
            name: "verified-context".into(),
            cache_metrics: ClassCacheMetrics::default(),
            phase: "test",
            active_method: SymbolId::NONE,
            active_file: FileId::NONE,
            pending_methods: 0,
            admission: Admission::default(),
            entries: Vec::new(),
            classes,
            shared_metadata: SharedMetadata::default(),
            java_feature: None,
            entries_at: Vec::new(),
        }],
        types,
        type_aliases: Vec::new(),
        methods: Vec::new(),
        admitted: Vec::new(),
        envelope_cache: binary::EnvelopeCache::new(0),
        platform_inputs: Vec::new(),
        platform_contexts: HashSet::new(),
    };
    (builder.finish().unwrap(), inputs, registry, parents)
}
fn symbol(registry: &Registry, owner: &str) -> SymbolId {
    registry.types[&(0, format!("fixture/{owner}"))]
}
fn complete(facts: &FactSnapshot, symbol: SymbolId) -> bool {
    facts.symbols[symbol.index()].flags & SYMBOL_JVM_PARENTS_COMPLETE != 0
}
fn relations(facts: &FactSnapshot) -> Vec<(SymbolId, SymbolId, RelationKind, FileId)> {
    facts
        .relations
        .iter()
        .map(|r| (r.source, r.target, r.kind, r.file))
        .collect()
}

#[test]
fn exact_direct_headers_seal_unordered_inventory_without_order_or_finality() {
    let (mut facts, inputs, registry, parents) = fixture();
    let before = relations(&facts);
    seal(&mut facts, &inputs, &registry, &parents);
    for &source in registry.types.values() {
        assert!(complete(&facts, source));
        assert_eq!(
            facts.symbols[source.index()].flags & SYMBOL_SCALA_PARENTS_COMPLETE,
            0
        );
        assert_eq!(facts.symbols[source.index()].properties, 0);
    }
    assert_eq!(
        relations(&facts),
        before,
        "never reorder or replace parent relations"
    );
}

#[test]
fn missing_deferred_conflicting_or_wrong_context_parent_cannot_seal_inventory() {
    for control in 0..7 {
        let (mut facts, mut inputs, registry, parents) = fixture();
        let leaf = symbol(&registry, "ResolveLeaf");
        let mid = symbol(&registry, "ResolveMid");
        match control {
            0 => {
                inputs.contexts[0].classes.remove("fixture/ResolveMid");
            }
            1 => {
                inputs.contexts[0].classes.insert(
                    "fixture/ResolveMid".into(),
                    CachedClass::Unknown(binary::ErrorKind::ClassNotFound),
                );
            }
            2 => facts.issues.push(IssueRecord {
                kind: IssueKind::ContextConflict,
                symbol: mid,
                file: FileId::NONE,
                detail: StrId::NONE,
            }),
            3 => facts.symbols[mid.index()].context = StrId::NONE,
            4 => facts.symbols[mid.index()].kind = 3,
            5 => {
                let CachedClass::Found(class) = &inputs.contexts[0].classes["fixture/ResolveMid"]
                else {
                    unreachable!()
                };
                let changed = Arc::new(ClassBytes {
                    bytes: class.bytes.clone(),
                    metadata: class.metadata.clone(),
                    hash: ContentHash([7; 32]),
                    origin: class.origin.clone(),
                });
                inputs.contexts[0]
                    .classes
                    .insert("fixture/ResolveMid".into(), CachedClass::Found(changed));
            }
            6 => facts.issues.push(IssueRecord {
                kind: IssueKind::ContextConflict,
                symbol: SymbolId::NONE,
                file: FileId(0),
                detail: StrId::NONE,
            }),
            _ => unreachable!(),
        }
        facts.symbols[leaf.index()].flags |= SYMBOL_JVM_PARENTS_COMPLETE;
        seal(&mut facts, &inputs, &registry, &parents);
        assert!(
            !complete(&facts, leaf),
            "control {control} must revoke stale completeness"
        );
    }
}

#[test]
fn source_inventory_must_be_verified_and_match_every_jvm_parent() {
    for control in 0..5 {
        let (mut facts, inputs, registry, mut parents) = fixture();
        let leaf = symbol(&registry, "ResolveLeaf");
        let mid = symbol(&registry, "ResolveMid");
        facts.symbols[leaf.index()].flags = SYMBOL_DEFINED | SYMBOL_SCALA_PARENTS_COMPLETE;
        facts.symbols[leaf.index()].file = FileId(0);
        match control {
            0 => (),
            1 => facts.symbols[leaf.index()].flags &= !SYMBOL_SCALA_PARENTS_COMPLETE,
            2 => facts.files[0].flags = SOURCE_VERIFIED,
            3 => {
                parents.remove(&(leaf, mid));
            }
            4 => {
                parents.insert((leaf, symbol(&registry, "ResolveBase")));
            }
            _ => unreachable!(),
        }
        let before = relations(&facts);
        seal(&mut facts, &inputs, &registry, &parents);
        assert_eq!(complete(&facts, leaf), control == 0, "control {control}");
        assert_eq!(relations(&facts), before);
    }
}

#[test]
fn object_ancestry_axiom_never_installs_header_effect_or_finality_authority() {
    let (mut facts, mut inputs, registry, parents) = fixture();
    let object = registry.types[&(0, "java/lang/Object".into())];
    inputs.contexts[0].classes.insert(
        "java/lang/Object".into(),
        CachedClass::Unknown(binary::ErrorKind::ClassNotFound),
    );
    facts.symbols[object.index()].flags = 0;
    facts.symbols[object.index()].kind = 0;
    let before_bodies = facts.bodies.len();
    seal(&mut facts, &inputs, &registry, &parents);
    assert!(complete(&facts, object));
    assert!(complete(&facts, symbol(&registry, "ResolveBase")));
    assert_eq!(
        facts.symbols[object.index()].flags,
        SYMBOL_JVM_PARENTS_COMPLETE
    );
    assert_eq!(facts.symbols[object.index()].properties, 0);
    assert_eq!(facts.symbols[object.index()].kind, 0);
    assert_eq!(
        facts.bodies.len(),
        before_bodies,
        "ancestry creates no executable recipe"
    );
}

#[test]
fn required_platform_object_endpoint_has_only_native_identity_and_ancestry() {
    let (mut facts, mut inputs, mut registry, parents) = fixture();
    let prior = registry
        .types
        .remove(&(0, "java/lang/Object".into()))
        .unwrap();
    inputs.contexts[0].classes.remove("java/lang/Object");
    let context = inputs.contexts[0].id;
    let object = object_endpoint(&mut facts, &mut registry, 0, context).unwrap();
    assert_eq!(facts.symbols[object.index()].flags, SYMBOL_NATIVE_BINARY);
    assert_eq!(facts.symbols[object.index()].properties, 0);
    assert!(!facts.bodies.iter().any(|body| body.symbol == object));
    let parents = parents
        .into_iter()
        .map(|(source, target)| (source, if target == prior { object } else { target }))
        .collect();
    seal(&mut facts, &inputs, &registry, &parents);
    assert_eq!(
        facts.symbols[object.index()].flags,
        SYMBOL_NATIVE_BINARY | SYMBOL_JVM_PARENTS_COMPLETE
    );
    assert!(complete(&facts, symbol(&registry, "ResolveBase")));
}

#[test]
fn object_axiom_rejects_contradictions_conflicts_and_noncanonical_identities() {
    for control in 0..8 {
        let (mut facts, mut inputs, registry, mut parents) = fixture();
        let object = registry.types[&(0, "java/lang/Object".into())];
        let base = symbol(&registry, "ResolveBase");
        inputs.contexts[0].classes.remove("java/lang/Object");
        match control {
            0 => {
                parents.insert((object, base));
            }
            1 => facts.issues.push(IssueRecord {
                kind: IssueKind::ContextConflict,
                symbol: object,
                file: FileId::NONE,
                detail: StrId::NONE,
            }),
            2 => facts.symbols[object.index()].context = StrId::NONE,
            3 => facts.symbols[object.index()].kind = 14,
            4 => {
                facts.symbols[object.index()].name =
                    append_text(&mut facts, "p/SimilarObject#").unwrap();
            }
            5 => {
                let CachedClass::Found(class) = &inputs.contexts[0].classes["fixture/ResolveBase"]
                else {
                    unreachable!()
                };
                let class = class.clone();
                inputs.contexts[0]
                    .classes
                    .insert("java/lang/Object".into(), CachedClass::Found(class));
            }
            6 => {
                inputs.contexts[0].classes.insert(
                    "java/lang/Object".into(),
                    CachedClass::Unknown(binary::ErrorKind::InvalidClassName),
                );
            }
            7 => {
                inputs.contexts[0].classes.insert(
                    "java/lang/Object".into(),
                    CachedClass::Unknown(binary::ErrorKind::UnavailableInput),
                );
            }
            _ => unreachable!(),
        }
        seal(&mut facts, &inputs, &registry, &parents);
        assert!(!complete(&facts, object), "control {control}");
        assert!(!complete(&facts, base), "control {control}");
    }
}
