//! Parent publication is class metadata, independent of the number of demanded
//! method bodies. These public-admission controls reuse frozen javac inputs;
//! the compiler endpoint rows and source-order control are explicitly synthetic.
use selector_facts::{FactBuilder, FactSnapshot, FileRecord, RelationRecord};
use selector_graph_build::binary_inputs::{augment_binary_facts, load_binary_manifest};
use selector_types::*;
use sha2::{Digest, Sha256};
use std::{collections::HashSet, path::PathBuf};

const A: &str = "hierarchycase/Factory$A";
const BASE: &str = "hierarchycase/Factory$Base";
const CONTRACT: &str = "hierarchycase/Factory$Contract";
const OBJECT: &str = "java/lang/Object";
const RUNNABLE: &str = "java/lang/Runnable";
const CONTEXTS: [&str; 2] = ["fixture:parent-shape-a", "fixture:parent-shape-b"];

fn directory() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/native-hierarchy")
}

fn type_name(owner: &str) -> String {
    format!("{owner}#")
}

fn method_name(name: &str) -> String {
    format!("{A}#{name}().")
}

fn symbol(facts: &FactSnapshot, context: &str, spelling: &str) -> SymbolId {
    let mut matches = facts.symbols.iter().enumerate().filter_map(|(i, row)| {
        (facts.text(row.context) == context && facts.text(row.name) == spelling)
            .then_some(SymbolId(i as u32))
    });
    let id = matches.next().expect("exact contextual endpoint");
    assert!(matches.next().is_none(), "unique contextual endpoint");
    id
}

fn parents(facts: &FactSnapshot, child: SymbolId) -> Vec<SymbolId> {
    facts
        .relations
        .iter()
        .filter(|row| row.kind == RelationKind::Parent && row.source == child)
        .map(|row| row.target)
        .collect()
}

fn fixture(
    constructor: bool,
    ordered_source: bool,
    shadow_second: bool,
) -> (FactSnapshot, serde_json::Value) {
    let receipt: serde_json::Value =
        serde_json::from_slice(&std::fs::read(directory().join("manifest.json")).unwrap()).unwrap();
    let jar = |name: &str| {
        let pin = receipt["files"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["path"] == name)
            .unwrap();
        serde_json::json!({"path":directory().join(name),"sha256":pin["sha256"],"kind":"jar"})
    };
    let mut builder = FactBuilder::new();
    builder.facts.revision = builder.intern("genuine-parent-shape-control-v1").unwrap();
    let mut types = Vec::new();
    let mut methods = Vec::new();
    let mut contexts = Vec::new();
    for (index, context) in CONTEXTS.iter().enumerate() {
        let context_id = builder.intern(context).unwrap();
        let mut ids = Vec::new();
        for owner in [A, BASE, CONTRACT, OBJECT, RUNNABLE] {
            let name = type_name(owner);
            let id = builder.ensure_global_symbol(&name, context_id).unwrap();
            let row = &mut builder.facts.symbols[id.index()];
            row.kind = if matches!(owner, CONTRACT | RUNNABLE) {
                14
            } else {
                13
            };
            // Deliberately no SYMBOL_NATIVE_BINARY: these are compiler-bound
            // external nominal endpoints, including the original flags0 case.
            assert_eq!(row.flags, 0);
            ids.push(id);
            types.push(
                serde_json::json!({"context":context,"compiler_symbol":name,"jvm_owner":owner}),
            );
        }
        for (name, descriptor) in [("value", "()I"), ("<init>", "()V")] {
            let spelling = method_name(name);
            let id = builder.ensure_global_symbol(&spelling, context_id).unwrap();
            let row = &mut builder.facts.symbols[id.index()];
            row.kind = 3;
            row.owner = ids[0];
            if name == "value" || constructor {
                methods.push(
                    serde_json::json!({"context":context,"compiler_symbol":spelling,
                    "jvm_owner":A,"jvm_name":name,"descriptor":descriptor}),
                );
            }
        }
        if ordered_source && index == 0 {
            let path = builder
                .intern("synthetic/compiler-ordered-A.scala")
                .unwrap();
            let source_text = "// synthetic source inventory control\n";
            let source = builder.intern(source_text).unwrap();
            let file = FileId(builder.facts.files.len() as u32);
            builder.facts.files.push(FileRecord {
                path,
                source,
                revision: builder.facts.revision,
                context: context_id,
                source_hash: ContentHash(Sha256::digest(source_text.as_bytes()).into()),
                flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
            });
            let child = &mut builder.facts.symbols[ids[0].index()];
            child.file = file;
            child.flags = SYMBOL_DEFINED | SYMBOL_SCALA_PARENTS_COMPLETE;
            // The order differs from the JVM header deliberately. Native
            // unordered validation may compare this set, but must not rewrite it.
            for parent in [ids[2], ids[1]] {
                builder.facts.relations.push(RelationRecord {
                    source: ids[0],
                    target: parent,
                    kind: RelationKind::Parent,
                    file,
                });
            }
        }
        let mut entries = Vec::new();
        if shadow_second && index == 1 {
            entries.push(jar("shadow.jar"));
        }
        entries.extend([jar("bytecode.jar"), jar("bootstrap.jar")]);
        contexts.push(serde_json::json!({"id":context,"entries":entries}));
    }
    let facts = builder.finish().unwrap();
    let manifest = serde_json::json!({"version":1,"revision":facts.text(facts.revision),
        "java_feature":21,"contexts":contexts,"types":types,"methods":methods});
    (facts, manifest)
}

fn admit(mut facts: FactSnapshot, manifest: &serde_json::Value) -> Result<FactSnapshot, Error> {
    let temp = tempfile::tempdir()?;
    let path = temp.path().join("binary.json");
    std::fs::write(&path, serde_json::to_vec(manifest).unwrap())?;
    let mut inputs = load_binary_manifest(&path, &facts)?;
    augment_binary_facts(&mut facts, &mut inputs)?;
    Ok(facts)
}

#[test]
fn native_parent_shape_does_not_depend_on_demanded_method_count() {
    let (one, one_manifest) = fixture(false, false, false);
    let (many, many_manifest) = fixture(true, false, false);
    let one = admit(one, &one_manifest).unwrap();
    let many = admit(many, &many_manifest).unwrap();
    for context in CONTEXTS {
        let a = symbol(&many, context, &type_name(A));
        assert_eq!(
            many.symbols[a.index()].flags & (SYMBOL_DEFINED | SYMBOL_NATIVE_BINARY),
            0
        );
        assert_ne!(
            many.symbols[a.index()].flags & SYMBOL_JVM_CLASS_HEADER_VERIFIED,
            0
        );
        let expected = vec![
            symbol(&many, context, &type_name(BASE)),
            symbol(&many, context, &type_name(CONTRACT)),
        ];
        assert_eq!(
            parents(&many, a),
            expected,
            "one exact row per native parent"
        );
        let before = symbol(&one, context, &type_name(A));
        let names = |facts: &FactSnapshot, child| {
            parents(facts, child)
                .into_iter()
                .map(|id| facts.symbol_name(id).to_owned())
                .collect::<Vec<_>>()
        };
        assert_eq!(names(&one, before), names(&many, a));
    }
    let mut pairs = HashSet::new();
    for row in many
        .relations
        .iter()
        .filter(|row| row.kind == RelationKind::Parent)
    {
        assert!(
            pairs.insert((row.source, row.target)),
            "no repeated native pair"
        );
        assert_eq!(
            many.symbols[row.source.index()].context,
            many.symbols[row.target.index()].context
        );
        assert_eq!(
            many.files[row.file.index()].flags & FILE_BINARY_SOURCE,
            FILE_BINARY_SOURCE
        );
    }
    let options = selector_graph_build::BuildOptions {
        workers: 2,
        include_models: false,
    };
    let before = selector_graph_build::build(&one, &options).unwrap();
    let after = selector_graph_build::build(&many, &options).unwrap();
    let seeds = selector_select::changed_seeds(&one, &before, &many, &after, &[]).unwrap();
    for (facts, graph, compile) in [
        (&one, &before, &seeds.base_compile),
        (&many, &after, &seeds.head_compile),
    ] {
        for context in CONTEXTS {
            let a = symbol(facts, context, &type_name(A));
            assert!(
                !compile.contains(&graph.node_for_symbol(a).unwrap()),
                "method demand must not fabricate an A hierarchy declaration delta"
            );
        }
    }
}

#[test]
fn source_parent_order_and_context_specific_shadow_headers_stay_authoritative() {
    let (facts, manifest) = fixture(true, true, true);
    let a = symbol(&facts, CONTEXTS[0], &type_name(A));
    let original: Vec<_> = facts
        .relations
        .iter()
        .map(|row| (row.source, row.target, row.kind, row.file))
        .collect();
    let facts = admit(facts, &manifest).unwrap();
    assert_eq!(
        parents(&facts, a),
        vec![
            symbol(&facts, CONTEXTS[0], &type_name(CONTRACT)),
            symbol(&facts, CONTEXTS[0], &type_name(BASE)),
        ]
    );
    assert_eq!(
        facts.relations[..original.len()]
            .iter()
            .map(|row| (row.source, row.target, row.kind, row.file))
            .collect::<Vec<_>>(),
        original
    );
    assert_ne!(
        facts.symbols[a.index()].flags & SYMBOL_SCALA_PARENTS_COMPLETE,
        0
    );
    let first = symbol(&facts, CONTEXTS[0], &type_name(CONTRACT));
    let second = symbol(&facts, CONTEXTS[1], &type_name(CONTRACT));
    assert_ne!(
        first, second,
        "identical compiler spelling remains contextual"
    );
    assert_eq!(
        parents(&facts, first),
        vec![symbol(&facts, CONTEXTS[0], &type_name(OBJECT))]
    );
    assert_eq!(
        parents(&facts, second),
        vec![
            symbol(&facts, CONTEXTS[1], &type_name(OBJECT)),
            symbol(&facts, CONTEXTS[1], &type_name(RUNNABLE)),
        ],
        "second context uses its actual earlier shadow provider"
    );
    assert_eq!(
        facts.symbols[second.index()].flags & SYMBOL_JVM_PARENTS_COMPLETE,
        0,
        "missing Runnable bytes cannot close ancestry"
    );
    assert!(
        facts
            .issues
            .iter()
            .any(|row| row.kind == IssueKind::IncompleteHierarchy && row.symbol == second)
    );
}

#[test]
fn source_ancestor_metadata_does_not_require_generated_contract_discovery() {
    // Only A.value is demanded. There is no constructor or abstract method
    // root to make generated-member discovery traverse A's native ancestry.
    let (facts, manifest) = fixture(false, true, false);
    assert_eq!(manifest["methods"].as_array().unwrap().len(), 2);
    let a = symbol(&facts, CONTEXTS[0], &type_name(A));
    let source_order = parents(&facts, a);
    let facts = admit(facts, &manifest).unwrap();
    assert_eq!(parents(&facts, a), source_order);
    for context in CONTEXTS {
        let contract = symbol(&facts, context, &type_name(CONTRACT));
        assert_eq!(
            parents(&facts, contract),
            vec![symbol(&facts, context, &type_name(OBJECT))]
        );
        let rows: Vec<_> = facts
            .relations
            .iter()
            .filter(|row| row.kind == RelationKind::Parent && row.source == contract)
            .collect();
        assert_eq!(rows.len(), 1);
        assert_ne!(
            facts.files[rows[0].file.index()].flags & FILE_BINARY_SOURCE,
            0
        );
    }
}

#[test]
fn stale_classpath_digest_cannot_publish_a_deduplicated_hierarchy_certificate() {
    let (facts, mut manifest) = fixture(true, false, false);
    manifest["contexts"][0]["entries"][0]["sha256"] = serde_json::json!("00".repeat(32));
    assert!(
        admit(facts, &manifest).is_err(),
        "hash mismatch rejects admission, not just duplicate rows"
    );
}
