//! Bind source classes only to their verified exported compiler products. These
//! type rows enable real generated JVM members; they do not supply method bodies.
use super::*;

pub(super) struct Inputs<'a, 'b> {
    pub facts: &'a FactSnapshot,
    pub native_parents: &'a [(SymbolId, SymbolId)],
    pub contexts: &'a [Context],
    pub context_index: &'a HashMap<&'b str, usize>,
    pub snapshots: &'a [Snapshot],
    pub classpaths: &'a [Vec<usize>],
    pub java_feature: Option<u16>,
    pub max_bindings: usize,
}

pub(super) fn add(
    view: Inputs<'_, '_>,
    abstract_owners: &[SymbolId],
    types: &mut BTreeMap<(usize, String), SymbolId>,
    blocked: &mut HashSet<(usize, String)>,
    receipt: &mut MappingReceipt,
) -> Result<(), Error> {
    if abstract_owners.is_empty() {
        return Ok(());
    }
    let facts = view.facts;
    // One flat parent posting list, one visited bitmap. No per-symbol child Vec
    // or repeated whole-program scan for each demanded abstract method.
    let mut descendants: Vec<_> = facts
        .relations
        .iter()
        .filter(|r| r.kind == RelationKind::Parent)
        .map(|r| (r.target, r.source))
        .chain(
            view.native_parents
                .iter()
                .map(|&(source, target)| (target, source)),
        )
        .collect();
    descendants.sort_unstable();
    descendants.dedup();
    let mut pending = abstract_owners.to_vec();
    pending.sort_unstable();
    pending.dedup();
    let mut seen = vec![false; facts.symbols.len()];
    let mut source_classes = Vec::new();
    while let Some(symbol) = pending.pop() {
        if symbol.is_none() || std::mem::replace(&mut seen[symbol.index()], true) {
            continue;
        }
        let first = descendants.partition_point(|(parent, _)| *parent < symbol);
        pending.extend(
            descendants[first..]
                .iter()
                .take_while(|(parent, _)| *parent == symbol)
                .map(|(_, child)| *child),
        );
        let declaration = facts.symbols[symbol.index()];
        let Some(file) = facts.files.get(declaration.file.index()) else {
            continue;
        };
        if declaration.kind == 13
            && declaration.flags & SYMBOL_DEFINED != 0
            && file.flags & (SOURCE_VERIFIED | SYNTAX_VERIFIED | FILE_BINARY_SOURCE)
                == SOURCE_VERIFIED | SYNTAX_VERIFIED
            && !file.source.is_none()
            && declaration.context == file.context
        {
            source_classes.push(symbol);
        }
    }
    drop(descendants);
    drop(seen);
    drop(pending);
    if source_classes.is_empty() {
        return Ok(());
    }
    // A classpath directory is not necessarily this context's output. Match an
    // exact exported-product hash and a unique captured compiler-output origin.
    let mut own = Vec::new();
    for context in view.contexts {
        let Some(&index) = view.context_index.get(context.context_id.as_str()) else {
            continue;
        };
        for (offset, input) in context.full_classpath.iter().enumerate() {
            if input.project_output_origins.len() != 1
                || input.project_output_origins[0].context_id != context.context_id
            {
                continue;
            }
            // The explicit declared-runtime lane can prepend one verified
            // bootstrap archive. Compiler output ordinals still refer to the
            // original captured classpath, never to that new provider.
            let prefix = view.classpaths[index]
                .len()
                .checked_sub(context.full_classpath.len())
                .filter(|&prefix| prefix <= 1)
                .ok_or(Error::Invalid("native source product classpath prefix"))?;
            let entry = view.classpaths[index][offset + prefix];
            let snapshot = &view.snapshots[entry];
            if snapshot.names.is_none()
                || !matches!(
                    snapshot.entry.kind,
                    EntryKind::Directory { .. } | EntryKind::Jar
                )
            {
                continue;
            }
            let mut expected = None;
            let mut conflict = false;
            for product in context
                .exported_products
                .iter()
                .filter(|p| p.path == input.path)
            {
                let hash = product
                    .sha256
                    .as_deref()
                    .map(ContentHash::from_hex)
                    .transpose()?;
                if hash.is_none() || expected.is_some_and(|old| Some(old) != hash) {
                    conflict = true;
                } else {
                    expected = hash;
                }
            }
            if !conflict && expected == Some(snapshot.entry.sha256) {
                own.push((index, entry));
            }
        }
    }
    own.sort_unstable();
    own.dedup();
    let mut jobs = BTreeMap::new();
    for symbol in source_classes {
        let declaration = facts.symbols[symbol.index()];
        let Some(&context) = view.context_index.get(facts.text(declaration.context)) else {
            continue;
        };
        let Some(owner) = selector_types::symbol::jvm_owner(facts.symbol_name(symbol)) else {
            continue;
        };
        for &entry in &view.classpaths[context] {
            let Some(names) = &view.snapshots[entry].names else {
                reason(receipt, "source_type_unavailable_preceding_input");
                break;
            };
            if names.binary_search(&owner).is_err() {
                continue;
            }
            if own.binary_search(&(context, entry)).is_err() {
                reason(receipt, "source_type_shadow_or_unbound_product");
                break;
            }
            jobs.entry((entry, context, owner))
                .and_modify(|previous| {
                    if *previous != Some(symbol) {
                        *previous = None;
                    }
                })
                .or_insert(Some(symbol));
            break;
        }
    }
    let mut active = None;
    let mut loader = None;
    for ((entry, context, owner), symbol) in jobs {
        let Some(symbol) = symbol else {
            reason(receipt, "ambiguous_source_type_abi");
            continue;
        };
        if active != Some(entry) {
            active = Some(entry);
            loader = Some(
                CapturedClasspath::new(
                    vec![view.snapshots[entry].entry.clone()],
                    Limits::default(),
                )
                .and_then(|cp| cp.with_java_feature(view.java_feature))
                .map_err(error)?,
            );
        }
        let bytes = match loader.as_mut().unwrap().lookup(&owner).map_err(error)? {
            ClassLookup::Found(class) => class.bytes,
            ClassLookup::Absent(_) => {
                return Err(Error::Invalid("source type inventory class disappeared"));
            }
        };
        let class = binary::parse_class(&bytes, Limits::default()).map_err(error)?;
        if class.name != owner || class.flags & (0x0200 | 0x0400) != 0 {
            reason(receipt, "source_type_not_matching_concrete_header");
            continue;
        }
        let key = (context, owner);
        if blocked.contains(&key) {
            continue;
        }
        if types.get(&key).is_some_and(|previous| *previous != symbol) {
            types.remove(&key);
            blocked.insert(key);
            reason(receipt, "conflicting_source_type_abi");
            continue;
        }
        types.insert(key, symbol);
        if types.len() > view.max_bindings {
            return Err(Error::Limit("automatic binary type bindings"));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use selector_facts::{FactBuilder, FileRecord, RelationRecord};

    // Normalized authority controls isolate source type admission. The genuine
    // Scala source/member/field correspondence is exercised by acceptance tests.
    #[test]
    fn source_types_require_own_hash_bound_product_and_cannot_skip_shadows_or_gaps() {
        let jar = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../fixtures/binary/fixture-deflated.jar")
            .canonicalize()
            .unwrap();
        let manifest: Value =
            serde_json::from_str(include_str!("../../../fixtures/binary/manifest.json")).unwrap();
        let hash = ContentHash::from_hex(
            manifest["outputs"]
                .as_array()
                .unwrap()
                .iter()
                .find(|r| r["path"] == "fixture-deflated.jar")
                .unwrap()["sha256"]
                .as_str()
                .unwrap(),
        )
        .unwrap();
        let entry = ClasspathEntry {
            path: jar.clone(),
            sha256: hash,
            kind: EntryKind::Jar,
        };
        let names = CapturedClasspath::new(vec![entry.clone()], Limits::default())
            .unwrap()
            .class_names(0)
            .unwrap();
        for control in 0..11 {
            let mut builder = FactBuilder::new();
            let context = builder.intern("a").unwrap();
            let path = builder.intern("Probe.scala").unwrap();
            let source = builder.intern("class Probe").unwrap();
            builder.facts.files.push(FileRecord {
                path,
                source,
                context,
                revision: StrId::NONE,
                source_hash: ContentHash::default(),
                flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
            });
            let symbol = builder.ensure_symbol("fixture/Probe#", FileId(0)).unwrap();
            let record = &mut builder.facts.symbols[symbol.index()];
            record.file = FileId(0);
            record.flags = SYMBOL_DEFINED;
            record.kind = 13;
            let parent = builder
                .ensure_symbol("fixture/Abstract#", FileId(0))
                .unwrap();
            builder.facts.relations.push(RelationRecord {
                source: symbol,
                target: parent,
                file: FileId(0),
                kind: RelationKind::Parent,
            });
            if control == 5 {
                builder.facts.files[0].flags &= !SOURCE_VERIFIED;
            }
            if control == 6 {
                builder.facts.files[0].flags &= !SYNTAX_VERIFIED;
            }
            if control == 9 {
                builder.facts.relations.clear();
            }
            let mut native_parents = Vec::new();
            if control == 10 {
                let middle = builder
                    .ensure_symbol("fixture/Intermediate#", FileId(0))
                    .unwrap();
                builder.facts.relations[0].target = middle;
                native_parents.push((middle, parent));
            }
            // These deliberately malformed negative authorities are inspected
            // without admission: the helper must decline before mapping a type.
            let facts = builder.facts;
            let path = jar.to_str().unwrap().to_owned();
            let mut contexts = vec![Context {
                context_id: "a".into(),
                java_options: vec![],
                java_home: None,
                exported_products: vec![Product {
                    path: path.clone(),
                    sha256: Some(hash.to_string()),
                }],
                full_classpath: vec![Input {
                    index: 0,
                    path: path.clone(),
                    input_object: None,
                    sha256: Some(hash.to_string()),
                    project_output_origins: vec![Origin {
                        context_id: "a".into(),
                    }],
                }],
            }];
            if control == 1 {
                contexts[0].exported_products.clear();
            }
            if control == 2 {
                contexts[0].full_classpath[0].project_output_origins[0].context_id = "other".into();
            }
            if control == 3 {
                contexts[0].full_classpath[0]
                    .project_output_origins
                    .push(Origin {
                        context_id: "other".into(),
                    });
            }
            if control == 4 {
                contexts[0].exported_products[0].sha256 = Some(ContentHash::default().to_string());
            }
            let snapshot = |entry: ClasspathEntry, names| Snapshot {
                receipt: EntryReceipt {
                    captured_path: entry.path.display().to_string(),
                    physical_path: entry.path.clone(),
                    expected_sha256: entry.sha256.to_string(),
                    classes: 0,
                    admitted: true,
                    reason: None,
                },
                entry,
                names,
            };
            let mut snapshots = vec![snapshot(entry.clone(), Some(names.clone()))];
            let mut classpaths = vec![vec![0]];
            if matches!(control, 7 | 8) {
                let input = Input {
                    index: 0,
                    path: "prefix.jar".into(),
                    input_object: None,
                    sha256: None,
                    project_output_origins: vec![],
                };
                contexts[0].full_classpath.insert(0, input);
                contexts[0].full_classpath[1].index = 1;
                snapshots.push(snapshot(
                    ClasspathEntry {
                        path: "prefix.jar".into(),
                        sha256: ContentHash::default(),
                        kind: EntryKind::Unavailable,
                    },
                    if control == 7 {
                        Some(names.clone())
                    } else {
                        None
                    },
                ));
                classpaths[0].insert(0, 1);
            }
            let context_index = HashMap::from([("a", 0)]);
            let mut types = BTreeMap::new();
            let mut blocked = HashSet::new();
            let mut receipt = MappingReceipt {
                schema: "test",
                requested: 0,
                bound_methods: 0,
                bound_types: 0,
                skipped_source_recipes: 0,
                unresolved: BTreeMap::new(),
                entries: vec![],
            };
            add(
                Inputs {
                    facts: &facts,
                    native_parents: &native_parents,
                    contexts: &contexts,
                    context_index: &context_index,
                    snapshots: &snapshots,
                    classpaths: &classpaths,
                    java_feature: Some(21),
                    max_bindings: 10,
                },
                &[parent],
                &mut types,
                &mut blocked,
                &mut receipt,
            )
            .unwrap();
            assert_eq!(
                types.get(&(0, "fixture/Probe".into())).copied(),
                if matches!(control, 0 | 10) {
                    Some(symbol)
                } else {
                    None
                },
                "authority control {control}"
            );
        }
    }
}
