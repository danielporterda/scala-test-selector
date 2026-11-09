//! Exact manifest aliases retain distinct compiler nodes; actual class bytes,
//! not the JVM spelling or a marker-interface allowlist, prove empty headers.
use selector_facts::{FactBuilder, FileRecord};
use selector_graph_build::binary_inputs::{augment_binary_facts, load_binary_manifest};
use selector_types::*;

fn fixture(
    owner: &str,
    repeated_compiler: bool,
    source_alias: bool,
) -> (
    tempfile::TempDir,
    std::path::PathBuf,
    selector_facts::FactSnapshot,
    SymbolId,
    SymbolId,
) {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../fixtures/constructor-forms/head");
    let mut manifest: serde_json::Value =
        serde_json::from_slice(&std::fs::read(root.join("binary.json")).unwrap()).unwrap();
    let context = manifest["contexts"][0]["id"].as_str().unwrap().to_owned();
    for row in manifest["contexts"][0]["entries"].as_array_mut().unwrap() {
        let path = std::path::Path::new(row["path"].as_str().unwrap());
        if path.is_relative() {
            row["path"] = root.join(path).to_string_lossy().into_owned().into();
        }
    }
    manifest["revision"] = "binary-alias-regression".into();
    manifest["methods"] = serde_json::json!([]);
    manifest["types"] = serde_json::json!([
        {"context":context,"compiler_symbol":"p/Canonical#","jvm_owner":owner},
        {"context":context,"compiler_symbol":if repeated_compiler {"p/Canonical#"} else {"p/Alias#"},"jvm_owner":owner}
    ]);
    let mut builder = FactBuilder::new();
    let revision = builder.intern("binary-alias-regression").unwrap();
    builder.facts.revision = revision;
    let context = builder.intern(&context).unwrap();
    let path = builder.intern("Context.scala").unwrap();
    let empty = builder.intern("").unwrap();
    builder.facts.files.push(FileRecord {
        path,
        source: empty,
        revision,
        context,
        source_hash: ContentHash::default(),
        flags: 0,
    });
    let canonical = builder.ensure_symbol("p/Canonical#", FileId(0)).unwrap();
    let alias = builder.ensure_symbol("p/Alias#", FileId(0)).unwrap();
    if source_alias {
        let declaration = &mut builder.facts.symbols[alias.index()];
        declaration.flags = SYMBOL_DEFINED;
        declaration.kind = 13;
        declaration.file = FileId(0);
    }
    let facts = builder.finish().unwrap();
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("binary.json");
    std::fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    (dir, path, facts, canonical, alias)
}

#[test]
fn verified_java_interface_aliases_keep_both_compiler_identities_and_empty_instance_recipes() {
    let (_dir, path, mut facts, canonical, alias) = fixture("java/io/Serializable", false, false);
    let mut inputs = load_binary_manifest(&path, &facts).unwrap();
    augment_binary_facts(&mut facts, &mut inputs).unwrap();
    assert_ne!(canonical, alias);
    assert_eq!(facts.symbol_name(canonical), "p/Canonical#");
    assert_eq!(facts.symbol_name(alias), "p/Alias#");
    let header = facts
        .bodies
        .iter()
        .find(|body| body.symbol == alias)
        .unwrap();
    assert_eq!(header.flags, BODY_BINARY_RECIPE | BODY_INITIALIZER);
    assert_eq!(header.operations.len, 0);
    assert_eq!(facts.files[header.file.index()].flags, FILE_BINARY_SOURCE);
    assert!(!facts.issues.iter().any(|issue| issue.symbol == alias));
    assert!(facts.bodies.iter().any(|body| body.symbol == canonical));
    assert_eq!(facts.symbols[alias.index()].flags & SYMBOL_DEFINED, 0);
    for id in [canonical, alias] {
        assert_ne!(
            facts.symbols[id.index()].flags & SYMBOL_JVM_CLASS_HEADER_VERIFIED,
            0
        );
        assert_eq!(
            facts.symbols[id.index()].flags
                & (SYMBOL_DEFINED | SYMBOL_NATIVE_BINARY | SYMBOL_SCALA_PARENTS_COMPLETE),
            0
        );
    }
}

#[test]
fn scala_trait_initializer_or_source_class_header_never_becomes_an_empty_alias_recipe() {
    for (owner, source_alias) in [("scala/Function1", false), ("java/io/Serializable", true)] {
        let (_dir, path, mut facts, _, alias) = fixture(owner, false, source_alias);
        let original = facts.symbols[alias.index()];
        let mut inputs = load_binary_manifest(&path, &facts).unwrap();
        augment_binary_facts(&mut facts, &mut inputs).unwrap();
        assert!(!facts.bodies.iter().any(|body| body.symbol == alias));
        assert!(
            facts
                .issues
                .iter()
                .any(|issue| issue.symbol == alias && issue.kind == IssueKind::UnsupportedModel)
        );
        if source_alias {
            assert_eq!(facts.symbols[alias.index()].kind, original.kind);
            assert_eq!(facts.symbols[alias.index()].flags, original.flags);
        } else {
            assert_eq!(facts.symbols[alias.index()].kind, 14);
            assert_eq!(
                facts.symbols[alias.index()].flags,
                SYMBOL_JVM_CLASS_HEADER_VERIFIED
            );
        }
    }
}

#[test]
fn missing_headers_and_nonclass_endpoints_do_not_gain_class_authority() {
    let (_dir, path, mut facts, canonical, alias) = fixture("not/captured/Header", false, false);
    let mut inputs = load_binary_manifest(&path, &facts).unwrap();
    augment_binary_facts(&mut facts, &mut inputs).unwrap();
    for id in [canonical, alias] {
        assert_eq!(
            facts.symbols[id.index()].flags & SYMBOL_JVM_CLASS_HEADER_VERIFIED,
            0
        );
    }
    for flags in [0, SYMBOL_NATIVE_BINARY] {
        let (_dir, path, mut facts, canonical, _) = fixture("java/io/Serializable", false, false);
        facts.symbols[canonical.index()].kind = 3;
        facts.symbols[canonical.index()].flags = flags;
        let mut inputs = load_binary_manifest(&path, &facts).unwrap();
        augment_binary_facts(&mut facts, &mut inputs).unwrap();
        assert_eq!(facts.symbols[canonical.index()].kind, 3);
        assert_eq!(
            facts.symbols[canonical.index()].flags & SYMBOL_JVM_CLASS_HEADER_VERIFIED,
            0
        );
    }
}

#[test]
fn duplicate_compiler_alias_does_not_create_a_second_mapping() {
    let (_dir, path, facts, _, _) = fixture("java/io/Serializable", true, false);
    assert!(matches!(
        load_binary_manifest(&path, &facts),
        Err(Error::Invalid("duplicate binary compiler type binding"))
    ));
}

#[test]
fn interface_instance_header_does_not_execute_its_genuine_static_initializer() {
    let (_dir, path, mut facts, canonical, alias) = fixture("fixture/FieldTop", false, false);
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../fixtures/binary-resolution");
    let witness: serde_json::Value =
        serde_json::from_slice(&std::fs::read(root.join("manifest.json")).unwrap()).unwrap();
    let digest = witness["outputs"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["path"] == "resolution.jar")
        .unwrap()["sha256"]
        .as_str()
        .unwrap();
    let mut manifest: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
    manifest["contexts"][0]["entries"] =
        serde_json::json!([{ "path":root.join("resolution.jar"), "kind":"jar", "sha256":digest }]);
    manifest["methods"] = serde_json::json!([{ "context":manifest["contexts"][0]["id"], "jvm_owner":"fixture/FieldTop", "jvm_name":"<clinit>", "descriptor":"()V" }]);
    std::fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    let mut inputs = load_binary_manifest(&path, &facts).unwrap();
    augment_binary_facts(&mut facts, &mut inputs).unwrap();
    let header = facts
        .bodies
        .iter()
        .find(|body| body.symbol == alias)
        .unwrap();
    assert_eq!(header.operations.len, 0);
    assert_eq!(header.flags & BODY_STATIC_INITIALIZER, 0);
    // Actual javac emits `new Object; putstatic shared` in FieldTop.<clinit>.
    // The captured static recipe is retained separately, including its effect.
    assert!(facts.bodies.iter().any(|body| {
        body.symbol != alias
            && facts.symbols[body.symbol.index()].owner == canonical
            && body.flags & BODY_STATIC_INITIALIZER != 0
            && facts.operations[body.operations.range()]
                .iter()
                .any(|op| op.opcode == Opcode::StoreField && op.flags & OP_STATIC_FIELD != 0)
    }));
}
