//! Classfile-backed publication controls. Compiler-bound native endpoints start
//! with flags zero, as do many real captured Scala library identities.
use super::*;

const BASE: &str = "fixture/ResolveBase";
const MID: &str = "fixture/ResolveMid";
const LEAF: &str = "fixture/ResolveLeaf";
const OBJECT: &str = "java/lang/Object";
type Method<'a> = (&'a str, &'a str, &'a str);

fn admitted(
    root_owner: &str,
    methods: &[Method<'_>],
    contexts: usize,
    workers: usize,
    method_limit: usize,
    source_order: bool,
) -> FactSnapshot {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/binary-resolution");
    let jar = directory.join("resolution.jar");
    let digest = ContentHash(Sha256::digest(std::fs::read(&jar).unwrap()).into());
    let witness: serde_json::Value =
        serde_json::from_slice(&std::fs::read(directory.join("manifest.json")).unwrap()).unwrap();
    assert!(
        witness["outputs"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| { row["path"] == "resolution.jar" && row["sha256"] == digest.to_string() })
    );
    let mut builder = FactBuilder::new();
    builder.facts.revision = builder.intern("native-parent-publication").unwrap();
    let mut context_rows = Vec::new();
    let mut type_rows = Vec::new();
    let mut method_rows = Vec::new();
    for index in 0..contexts {
        let name = format!("parent-context-{index}");
        let context = builder.intern(&name).unwrap();
        let mut classes = HashMap::new();
        for owner in [BASE, MID, LEAF, OBJECT] {
            let spelling = if owner == root_owner {
                "parentcase/Root#".to_owned()
            } else {
                format!("{owner}#")
            };
            let symbol = builder.ensure_global_symbol(&spelling, context).unwrap();
            builder.facts.symbols[symbol.index()].kind = 13;
            classes.insert(owner, symbol);
            type_rows.push(serde_json::json!({
                "context":name,"compiler_symbol":spelling,"jvm_owner":owner
            }));
        }
        if source_order {
            let path = builder.intern(&format!("Source{index}.scala")).unwrap();
            let source = builder.intern("").unwrap();
            let file = FileId::checked(builder.facts.files.len()).unwrap();
            builder.facts.files.push(FileRecord {
                path,
                source,
                revision: builder.facts.revision,
                context,
                source_hash: ContentHash(Sha256::digest(b"").into()),
                flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
            });
            let root = classes[root_owner];
            let declaration = &mut builder.facts.symbols[root.index()];
            declaration.file = file;
            declaration.flags = SYMBOL_DEFINED | SYMBOL_SCALA_PARENTS_COMPLETE;
            // Deliberately retain the compiler's ordered source inventory even
            // when erasure supplies a different JVM direct superclass list.
            for target in [classes[OBJECT], classes[MID]] {
                builder.facts.relations.push(RelationRecord {
                    source: root,
                    target,
                    kind: RelationKind::Parent,
                    file,
                });
            }
        }
        for &(owner, method, descriptor) in methods {
            let spelling = format!("parentcase/{}#{method}{descriptor}.", owner.len());
            let symbol = builder.ensure_global_symbol(&spelling, context).unwrap();
            let declaration = &mut builder.facts.symbols[symbol.index()];
            declaration.owner = classes[owner];
            declaration.kind = 3;
            method_rows.push(serde_json::json!({
                "context":name,"compiler_symbol":spelling,"jvm_owner":owner,
                "jvm_name":method,"descriptor":descriptor
            }));
        }
        context_rows.push(serde_json::json!({"id":name,"entries":[{
            "path":jar,"sha256":digest.to_string(),"kind":"jar"
        }]}));
    }
    let mut facts = builder.finish().unwrap();
    let manifest = serde_json::json!({
        "version":1,"revision":facts.text(facts.revision),
        "contexts":context_rows,"types":type_rows,"methods":method_rows
    });
    let temp = tempfile::tempdir().unwrap();
    let path = temp.path().join("binary.json");
    std::fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    let mut inputs = load_binary_manifest_with_options(
        &path,
        &facts,
        &BinaryInputOptions {
            workers,
            ..Default::default()
        },
    )
    .unwrap();
    augment_binary_facts_with_limits(
        &mut facts,
        &mut inputs,
        NativeAdmissionLimits {
            methods: method_limit,
            ..Default::default()
        },
    )
    .unwrap();
    facts
}

fn root(facts: &FactSnapshot, context: usize) -> SymbolId {
    facts
        .symbols
        .iter()
        .enumerate()
        .find(|(_, symbol)| {
            facts.text(symbol.name) == "parentcase/Root#"
                && facts.text(symbol.context) == format!("parent-context-{context}")
        })
        .map(|(index, _)| SymbolId(index as u32))
        .unwrap()
}

fn direct_parents(facts: &FactSnapshot, source: SymbolId) -> Vec<&str> {
    facts
        .relations
        .iter()
        .filter(|row| row.kind == RelationKind::Parent && row.source == source)
        .map(|row| facts.symbol_name(row.target))
        .collect()
}

fn parent_shape(facts: &FactSnapshot) -> Vec<(&str, &str, &str, u32)> {
    let mut ordinals = HashMap::<SymbolId, u32>::new();
    let mut rows: Vec<_> = facts
        .relations
        .iter()
        .filter(|row| row.kind == RelationKind::Parent)
        .map(|row| {
            let ordinal = ordinals.entry(row.source).or_default();
            let result = (
                facts.text(facts.symbols[row.source.index()].context),
                facts.symbol_name(row.source),
                facts.symbol_name(row.target),
                *ordinal,
            );
            *ordinal += 1;
            result
        })
        .collect();
    rows.sort_unstable();
    rows
}

#[test]
fn multiple_native_methods_publish_each_parent_once_for_flag_zero_compiler_types() {
    let methods = [
        (BASE, "inherited", "()Ljava/lang/Object;"),
        (BASE, "overload", "(I)Ljava/lang/Object;"),
        (BASE, "overload", "(Ljava/lang/String;)Ljava/lang/Object;"),
        (BASE, "ping", "()Ljava/lang/Object;"),
    ];
    let single = admitted(BASE, &methods[..1], 1, 1, 100, false);
    let multiple = admitted(BASE, &methods, 1, 1, 100, false);
    for facts in [&single, &multiple] {
        let source = root(facts, 0);
        assert_eq!(
            facts.symbols[source.index()].flags & SYMBOL_NATIVE_BINARY,
            0
        );
        assert_ne!(
            facts.symbols[source.index()].flags & SYMBOL_JVM_CLASS_HEADER_VERIFIED,
            0
        );
        assert_eq!(direct_parents(facts, source), ["java/lang/Object#"]);
    }
    assert_eq!(parent_shape(&single), parent_shape(&multiple));
    assert!(multiple.bodies.len() > single.bodies.len());
}

#[test]
fn optional_method_quota_changes_bodies_but_not_the_same_admitted_parent_shape() {
    // One root discovers both ResolveBase.<clinit> and staticInherited. A
    // larger quota therefore lowers several methods on the same native owner.
    let methods = [(LEAF, "invokeStatic", "()Ljava/lang/Object;")];
    let limited = admitted(LEAF, &methods, 1, 1, 1, false);
    let expanded = admitted(LEAF, &methods, 1, 1, 20, false);
    assert!(expanded.bodies.len() > limited.bodies.len());
    assert!(limited.issues.iter().any(|issue| {
        issue.kind.is_execution_boundary()
            && limited
                .text(issue.detail)
                .contains("method admission budget")
    }));
    assert_eq!(parent_shape(&limited), parent_shape(&expanded));
    assert_eq!(
        direct_parents(&expanded, root(&expanded, 0)),
        ["fixture/ResolveMid#"]
    );
}

#[test]
fn actual_changed_class_header_keeps_its_changed_parent_shape() {
    let before = admitted(
        BASE,
        &[(BASE, "ping", "()Ljava/lang/Object;")],
        1,
        1,
        100,
        false,
    );
    let after = admitted(
        MID,
        &[(MID, "ping", "()Ljava/lang/Object;")],
        1,
        1,
        100,
        false,
    );
    assert_eq!(
        direct_parents(&before, root(&before, 0)),
        ["java/lang/Object#"]
    );
    assert_eq!(
        direct_parents(&after, root(&after, 0)),
        ["fixture/ResolveBase#"]
    );
    assert_ne!(parent_shape(&before), parent_shape(&after));
    let hash = |facts: &FactSnapshot| {
        let row = facts
            .relations
            .iter()
            .find(|row| row.kind == RelationKind::Parent && row.source == root(facts, 0))
            .unwrap();
        facts.files[row.file.index()].source_hash
    };
    assert_ne!(
        hash(&before),
        hash(&after),
        "actual captured header bytes differ"
    );
}

#[test]
fn native_methods_never_reorder_or_replace_source_parent_rows() {
    let facts = admitted(
        LEAF,
        &[
            (LEAF, "invokeInherited", "()Ljava/lang/Object;"),
            (LEAF, "invokeSuper", "()Ljava/lang/Object;"),
        ],
        1,
        1,
        100,
        true,
    );
    assert_eq!(
        direct_parents(&facts, root(&facts, 0)),
        ["java/lang/Object#", "fixture/ResolveMid#"]
    );
    assert!(
        facts
            .relations
            .iter()
            .filter(|row| { row.kind == RelationKind::Parent && row.source == root(&facts, 0) })
            .all(|row| facts.files[row.file.index()].flags & FILE_BINARY_SOURCE == 0)
    );
}

#[test]
fn contextual_publication_is_distinct_and_identical_at_one_and_four_workers() {
    let methods = [
        (BASE, "inherited", "()Ljava/lang/Object;"),
        (BASE, "ping", "()Ljava/lang/Object;"),
    ];
    let single = admitted(BASE, &methods, 2, 1, 100, false);
    let parallel = admitted(BASE, &methods, 2, 4, 100, false);
    assert_ne!(root(&single, 0), root(&single, 1));
    for context in 0..2 {
        let source = root(&single, context);
        assert_eq!(direct_parents(&single, source), ["java/lang/Object#"]);
        assert!(
            single
                .relations
                .iter()
                .filter(|row| { row.kind == RelationKind::Parent && row.source == source })
                .all(|row| single.symbols[row.target.index()].context
                    == single.symbols[source.index()].context)
        );
    }
    let temp = tempfile::tempdir().unwrap();
    let first = temp.path().join("one.bin");
    let second = temp.path().join("four.bin");
    selector_facts::codec::write(&first, &single).unwrap();
    selector_facts::codec::write(&second, &parallel).unwrap();
    assert_eq!(
        std::fs::read(first).unwrap(),
        std::fs::read(second).unwrap()
    );
}
