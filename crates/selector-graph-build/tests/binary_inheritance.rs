use selector_facts::{FactBuilder, FileRecord};
use selector_graph_build::binary_inputs::{augment_binary_facts, load_binary_manifest};
use selector_types::*;

fn native(owner: &str, name: &str, descriptor: &str) -> String {
    format!(
        "@jvm/{}:{owner}{}:{name}{}:{descriptor}",
        owner.len(),
        name.len(),
        descriptor.len()
    )
}

fn enriched(include_super: bool) -> selector_facts::FactSnapshot {
    let fixture = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../fixtures/binary-resolution");
    let witness: serde_json::Value =
        serde_json::from_slice(&std::fs::read(fixture.join("manifest.json")).unwrap()).unwrap();
    let digest = witness["outputs"]
        .as_array()
        .unwrap()
        .iter()
        .find(|r| r["path"] == "resolution.jar")
        .unwrap()["sha256"]
        .as_str()
        .unwrap();
    // The seed establishes only a compiler-context identity. All method recipes
    // and targets below come from the genuine hash-admitted JVM fixture.
    let mut builder = FactBuilder::new();
    let revision = builder.intern("binary-inheritance-test").unwrap();
    let context = builder.intern("captured-context").unwrap();
    let empty = builder.intern("").unwrap();
    let path = builder.intern("Context.scala").unwrap();
    builder.facts.revision = revision;
    builder.facts.files.push(FileRecord {
        path,
        source: empty,
        revision,
        context,
        source_hash: ContentHash::default(),
        flags: 0,
    });
    let mut facts = builder.finish().unwrap();
    let directory = tempfile::tempdir().unwrap();
    let manifest_path = directory.path().join("binary.json");
    let roots = [
        ("fixture/ResolveLeaf", "invokeInherited"),
        ("fixture/ResolveLeaf", "invokeStatic"),
        ("fixture/ResolveLeaf", "readInherited"),
        ("fixture/ResolveLeaf", "invokeSuper"),
        ("fixture/DefaultLeaf", "invokeDefault"),
    ];
    let manifest = serde_json::json!({
        "version":1, "revision":"binary-inheritance-test",
        "contexts":[{"id":"captured-context", "entries":[{
            "path":fixture.join("resolution.jar"), "kind":"jar", "sha256":digest
        }]}],
        "methods":roots.iter().filter(|(_,name)| include_super || *name != "invokeSuper").map(|(owner,name)| serde_json::json!({
            "context":"captured-context", "jvm_owner":owner, "jvm_name":name,
            "descriptor":"()Ljava/lang/Object;"
        })).collect::<Vec<_>>()
    });
    std::fs::write(&manifest_path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    let mut inputs = load_binary_manifest(&manifest_path, &facts).unwrap();
    augment_binary_facts(&mut facts, &mut inputs).unwrap();
    facts
}

#[test]
fn admitted_javac_symbolic_child_references_lower_to_real_inherited_declarations() {
    let facts = enriched(true);
    for (source_owner, source_method, opcode, target_owner, target_name, target_descriptor) in [
        (
            "fixture/ResolveLeaf",
            "invokeInherited",
            Opcode::VirtualCall,
            "fixture/ResolveBase",
            "inherited",
            "()Ljava/lang/Object;",
        ),
        (
            "fixture/ResolveLeaf",
            "invokeStatic",
            Opcode::Call,
            "fixture/ResolveBase",
            "staticInherited",
            "()Ljava/lang/Object;",
        ),
        (
            "fixture/ResolveLeaf",
            "readInherited",
            Opcode::LoadField,
            "fixture/ResolveBase",
            "shared",
            "Ljava/lang/Object;",
        ),
        (
            "fixture/ResolveLeaf",
            "invokeSuper",
            Opcode::Call,
            "fixture/ResolveMid",
            "ping",
            "()Ljava/lang/Object;",
        ),
        (
            "fixture/DefaultLeaf",
            "invokeDefault",
            Opcode::Call,
            "fixture/DefaultOne",
            "choose",
            "()Ljava/lang/Object;",
        ),
    ] {
        let source = facts
            .find_symbol(&native(source_owner, source_method, "()Ljava/lang/Object;"))
            .unwrap();
        let target = facts
            .find_symbol(&native(target_owner, target_name, target_descriptor))
            .unwrap();
        let body = facts
            .bodies
            .iter()
            .find(|body| body.symbol == source)
            .unwrap();
        let operations = &facts.operations[body.operations.range()];
        assert!(
            operations
                .iter()
                .any(|op| op.opcode == opcode && op.target == target),
            "{source_method}"
        );
        assert!(
            !operations.iter().any(|op| op.opcode == Opcode::Unknown),
            "{source_method}"
        );
        assert!(
            !facts.issues.iter().any(|issue| issue.symbol == source),
            "{source_method}"
        );
    }
    let phase = facts
        .find_symbol(&native("fixture/ResolveBase", "<class-init>", "()V"))
        .unwrap();
    let phase_body = facts
        .bodies
        .iter()
        .find(|body| body.symbol == phase)
        .unwrap();
    assert_ne!(phase_body.flags & BODY_STATIC_INITIALIZER, 0);
    assert_eq!(
        phase_body.flags & BODY_INITIALIZER,
        0,
        "JVM static phase must remain distinct from Scala instance/trait phases"
    );
    for name in ["invokeStatic", "readInherited"] {
        let source = facts
            .find_symbol(&native("fixture/ResolveLeaf", name, "()Ljava/lang/Object;"))
            .unwrap();
        let body = facts
            .bodies
            .iter()
            .find(|body| body.symbol == source)
            .unwrap();
        assert!(
            facts.operations[body.operations.range()]
                .iter()
                .any(|op| op.opcode == Opcode::Initialize && op.target == phase)
        );
    }
    let source = facts
        .find_symbol(&native(
            "fixture/DefaultLeaf",
            "invokeDefault",
            "()Ljava/lang/Object;",
        ))
        .unwrap();
    let body = facts
        .bodies
        .iter()
        .find(|body| body.symbol == source)
        .unwrap();
    assert!(
        !facts.operations[body.operations.range()]
            .iter()
            .any(|op| op.opcode == Opcode::Initialize),
        "invokespecial of an instance interface method does not trigger interface initialization"
    );
    facts.validate().unwrap();
}

#[test]
fn demanded_intermediate_class_publishes_parent_relation_without_a_member_body() {
    let facts = enriched(false);
    assert!(
        facts
            .find_symbol(&native(
                "fixture/ResolveMid",
                "ping",
                "()Ljava/lang/Object;"
            ))
            .is_none()
    );
    let leaf = facts
        .find_symbol(&native("fixture/ResolveLeaf", "<type>", ""))
        .unwrap();
    let mid = facts
        .find_symbol(&native("fixture/ResolveMid", "<type>", ""))
        .unwrap();
    let base = facts
        .find_symbol(&native("fixture/ResolveBase", "<type>", ""))
        .unwrap();
    for (source, target) in [(leaf, mid), (mid, base)] {
        assert!(
            facts
                .relations
                .iter()
                .any(|r| r.kind == RelationKind::Parent
                    && r.source == source
                    && r.target == target)
        );
    }
    facts.validate().unwrap();
}
