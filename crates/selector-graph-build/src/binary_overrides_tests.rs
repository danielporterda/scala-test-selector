use super::*;
use std::collections::BTreeSet;

type Edge = (SymbolId, SymbolId, FileId);
fn empty_registry(empty: StrId) -> Registry {
    Registry {
        types: HashMap::new(),
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
    }
}
fn fixture(owners: usize, methods: usize, parents: &[(usize, usize)]) -> (FactSnapshot, Registry) {
    let mut builder = FactBuilder::new();
    let context = builder.intern("native-context").unwrap();
    let path = builder.intern("capture.jar").unwrap();
    let empty = builder.intern("").unwrap();
    builder.facts.files.push(FileRecord {
        path,
        source: empty,
        revision: StrId::NONE,
        context,
        source_hash: ContentHash::default(),
        flags: FILE_BINARY_SOURCE,
    });
    let mut registry = empty_registry(empty);
    let mut classes = Vec::new();
    for index in 0..owners {
        let owner = builder
            .ensure_symbol(&format!("p/C{index}#"), FileId(0))
            .unwrap();
        builder.facts.symbols[owner.index()].kind = 13;
        classes.push(owner);
        for method in 0..methods {
            let name = match method {
                0 => "<init>".into(),
                1 => "toString".into(),
                _ => format!("m{method}"),
            };
            let symbol = builder
                .ensure_symbol(&format!("p/C{index}#{name}()."), FileId(0))
                .unwrap();
            builder.facts.symbols[symbol.index()].owner = owner;
            let key = MethodKey {
                context: 0,
                owner: format!("p/C{index}"),
                name,
                descriptor: "()V".into(),
            };
            registry.methods.insert(
                key,
                MethodData {
                    symbol,
                    owner,
                    flags: 1,
                    receiver_parameter: None,
                },
            );
        }
    }
    for &(child, parent) in parents {
        builder.facts.relations.push(RelationRecord {
            source: classes[child],
            target: classes[parent],
            file: FileId(0),
            kind: RelationKind::Parent,
        });
    }
    (builder.finish().unwrap(), registry)
}
// The previous pairwise implementation is retained only as a bounded oracle.
fn pairwise(facts: &FactSnapshot, registry: &Registry) -> BTreeSet<Edge> {
    fn subtype(
        types: &BinaryAdjacency,
        child: SymbolId,
        parent: SymbolId,
        seen: &mut HashSet<SymbolId>,
    ) -> bool {
        if child == parent {
            return true;
        }
        if !seen.insert(child) {
            return false;
        }
        types
            .get(child)
            .iter()
            .any(|p| subtype(types, *p, parent, seen))
    }
    let types = BinaryAdjacency::new(facts, RelationKind::Parent, false);
    let mut seen = HashSet::new();
    let mut edges = BTreeSet::new();
    for (key, child) in &registry.methods {
        if child.flags & (0x0002 | 0x0008) != 0 {
            continue;
        }
        for (parent_key, parent) in &registry.methods {
            if key.context != parent_key.context
                || key.name != parent_key.name
                || key.descriptor != parent_key.descriptor
                || child.owner == parent.owner
                || parent.flags & (0x0002 | 0x0008 | 0x0010) != 0
            {
                continue;
            }
            seen.clear();
            if subtype(&types, child.owner, parent.owner, &mut seen) {
                edges.insert((
                    child.symbol,
                    parent.symbol,
                    facts.symbols[child.symbol.index()].file,
                ));
            }
        }
    }
    edges
}
fn actual(facts: &FactSnapshot) -> Vec<Edge> {
    facts
        .relations
        .iter()
        .filter(|r| r.kind == RelationKind::Override)
        .map(|r| (r.source, r.target, r.file))
        .collect()
}
#[test]
fn branched_multilevel_context_flags_and_cycles_match_the_old_pairwise_oracle() {
    let parents = [(1, 0), (2, 0), (3, 1), (3, 2), (4, 3), (5, 4), (0, 5)];
    let (mut facts, mut registry) = fixture(7, 8, &parents);
    for (key, data) in &mut registry.methods {
        let owner = key.owner[3..].parse::<usize>().unwrap();
        data.flags = match (owner + key.name.len()) % 7 {
            0 => 1 | 0x0002,
            1 => 1 | 0x0008,
            2 => 1 | 0x0010,
            3 => 1 | 0x0400,
            _ => 1,
        };
    }
    let mut rows: Vec<_> = registry.methods.drain().collect();
    for (key, _) in &mut rows {
        if key.owner == "p/C2" {
            key.context = 1;
        }
        if key.owner == "p/C4" && key.name == "m3" {
            key.descriptor = "(I)V".into();
        }
    }
    registry.methods.extend(rows);
    let expected = pairwise(&facts, &registry);
    augment(&mut facts, &registry);
    assert_eq!(
        actual(&facts).into_iter().collect::<BTreeSet<_>>(),
        expected
    );
    assert_eq!(
        actual(&facts).len(),
        expected.len(),
        "new edges are deduplicated"
    );
    let mut permutation = empty_registry(empty_for(&facts));
    let mut rows: Vec<_> = registry.methods.iter().collect();
    rows.sort_unstable_by(|(a, _), (b, _)| b.owner.cmp(&a.owner));
    permutation.methods.extend(
        rows.into_iter()
            .map(|(key, data)| (key.clone(), data.clone())),
    );
    facts.relations.retain(|r| r.kind != RelationKind::Override);
    facts.relations.reverse();
    augment(&mut facts, &permutation);
    assert_eq!(actual(&facts), expected.into_iter().collect::<Vec<_>>());
}
fn empty_for(facts: &FactSnapshot) -> StrId {
    facts
        .strings
        .entries
        .iter()
        .enumerate()
        .find(|(_, r)| r.len == 0)
        .map(|(i, _)| StrId(i as u32))
        .unwrap()
}
#[test]
fn genuine_classfile_members_and_hierarchy_match_the_pairwise_oracle() {
    let root =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/binary-resolution/classes");
    let names = [
        "java/lang/Object",
        "fixture/ResolveBase",
        "fixture/ResolveMid",
        "fixture/ResolveLeaf",
        "fixture/DefaultTop",
        "fixture/DefaultOne",
        "fixture/DefaultTwo",
        "fixture/DefaultLeaf",
        "fixture/AbstractOne",
        "fixture/AbstractTwo",
        "fixture/AbstractLeaf",
    ];
    let mut builder = FactBuilder::new();
    let empty = builder.intern("").unwrap();
    let mut registry = empty_registry(empty);
    let mut classes = HashMap::new();
    for owner in names {
        let symbol = builder
            .ensure_symbol(&format!("{owner}#"), FileId::NONE)
            .unwrap();
        classes.insert(owner, symbol);
    }
    for owner in names {
        let bytes = std::fs::read(root.join(format!("{owner}.class"))).unwrap();
        let class = binary::parse_class(&bytes, Limits::default()).unwrap();
        for method in &class.methods {
            let symbol = builder
                .ensure_symbol(
                    &native_name(owner, method.name, method.descriptor),
                    FileId::NONE,
                )
                .unwrap();
            builder.facts.symbols[symbol.index()].owner = classes[owner];
            registry.methods.insert(
                MethodKey {
                    context: 0,
                    owner: owner.into(),
                    name: method.name.into(),
                    descriptor: method.descriptor.into(),
                },
                MethodData {
                    symbol,
                    owner: classes[owner],
                    flags: method.flags,
                    receiver_parameter: None,
                },
            );
        }
        for parent in class
            .parent
            .into_iter()
            .chain(class.interfaces.iter().copied())
        {
            if let Some(&target) = classes.get(parent) {
                builder.facts.relations.push(RelationRecord {
                    source: classes[owner],
                    target,
                    file: FileId::NONE,
                    kind: RelationKind::Parent,
                });
            }
        }
    }
    let mut facts = builder.finish().unwrap();
    let expected = pairwise(&facts, &registry);
    augment(&mut facts, &registry);
    assert!(!expected.is_empty());
    assert_eq!(
        actual(&facts).into_iter().collect::<BTreeSet<_>>(),
        expected
    );
}
#[test]
fn wide_same_abi_inventories_walk_each_owner_once_not_every_method_pair() {
    for owners in [64, 512] {
        let methods = 12;
        let parents: Vec<_> = (1..owners).map(|child| (child, 0)).collect();
        let (mut facts, registry) = fixture(owners, methods, &parents);
        let work = augment(&mut facts, &registry);
        assert_eq!(work.owner_walks, owners);
        assert_eq!(work.ancestor_visits, owners - 1);
        assert_eq!(work.abi_lookups, (owners - 1) * methods);
        assert_eq!(work.matching_members, (owners - 1) * methods);
        assert_eq!(actual(&facts).len(), (owners - 1) * methods);
        assert!(work.abi_lookups < owners * owners * methods / 8);
    }
}

#[test]
fn existing_compiler_override_edges_are_not_appended_again() {
    let (mut facts, registry) = fixture(3, 3, &[(1, 0), (2, 1)]);
    let expected = pairwise(&facts, &registry);
    let &(source, target, file) = expected.first().unwrap();
    facts.relations.push(RelationRecord {
        source,
        target,
        file,
        kind: RelationKind::Override,
    });
    augment(&mut facts, &registry);
    assert_eq!(actual(&facts).len(), expected.len());
    assert_eq!(
        actual(&facts).into_iter().collect::<BTreeSet<_>>(),
        expected
    );
}
