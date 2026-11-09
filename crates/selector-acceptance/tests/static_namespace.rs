//! Only a verified Java static namespace receiver is erased. Native initialization
//! and effects remain; Scala modules, instance receivers and missing authority do not qualify.
use selector_extract::{ExtractOptions, import_capture};
use selector_facts::{FactSnapshot, OperationRecord};
use selector_graph_build::binary_inputs::{augment_binary_facts, load_binary_manifest};
use selector_types::*;
use std::path::PathBuf;
fn directory() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/static-namespace")
}
fn raw() -> FactSnapshot {
    import_capture(
        &directory().join("documents.jsonl"),
        Some(&directory().join("syntax.jsonl")),
        &ExtractOptions {
            workers: 2,
            ..Default::default()
        },
    )
    .unwrap()
}
fn owned(owner: &str, name: &str, descriptor: &str) -> String {
    format!(
        "@jvm/{}:{owner}{}:{name}{}:{descriptor}",
        owner.len(),
        name.len(),
        descriptor.len()
    )
}
fn enriched(mode: &str) -> FactSnapshot {
    let mut facts = raw();
    let pins: serde_json::Value =
        serde_json::from_slice(&std::fs::read(directory().join("manifest.json")).unwrap()).unwrap();
    let jar = |name: &str| {
        let row = pins["files"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["path"] == name)
            .unwrap();
        serde_json::json!({"path":directory().join(name),"sha256":row["sha256"],"kind":"jar"})
    };
    let mut entries = Vec::new();
    if mode == "shadow" {
        entries.push(jar("shadow.jar"));
    }
    if mode == "unavailable" {
        entries.push(serde_json::json!({"path":"unprovided-prefix.jar","kind":"unavailable"}));
    }
    entries.push(jar("bytecode.jar"));
    let context = facts.text(facts.files[0].context);
    let manifest = serde_json::json!({"version":1,"revision":facts.text(facts.revision),"java_feature":21,
        "contexts":[{"id":context,"entries":entries}],
        "types":[{"context":context,"compiler_symbol":"namespacecase/JavaStaticHost#","jvm_owner":"namespacecase/JavaStaticHost"},
                 {"context":context,"compiler_symbol":"namespacecase/JavaInstanceHost#","jvm_owner":"namespacecase/JavaInstanceHost"}],
        "methods":[{"context":context,"compiler_symbol":"namespacecase/JavaStaticHost#ping().","jvm_owner":"namespacecase/JavaStaticHost","jvm_name":"ping","descriptor":"()I"},
                   {"context":context,"compiler_symbol":"namespacecase/JavaInstanceHost#`<init>`().","jvm_owner":"namespacecase/JavaInstanceHost","jvm_name":"<init>","descriptor":"()V"},
                   {"context":context,"compiler_symbol":"namespacecase/JavaInstanceHost#ping().","jvm_owner":"namespacecase/JavaInstanceHost","jvm_name":"ping","descriptor":"()I"}]});
    let temp = tempfile::tempdir().unwrap();
    let path = temp.path().join("binary.json");
    std::fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    let mut inputs = load_binary_manifest(&path, &facts).unwrap();
    augment_binary_facts(&mut facts, &mut inputs).unwrap();
    facts
}
fn operations<'a>(facts: &'a FactSnapshot, owner: &str) -> &'a [OperationRecord] {
    let symbol = facts.find_symbol(owner).unwrap();
    let body = facts.bodies.iter().find(|b| b.symbol == symbol).unwrap();
    &facts.operations[body.operations.range()]
}
#[test]
fn actual_jvm_static_module_instance_dormancy_and_class_literal_controls_are_pinned() {
    assert_eq!(
        std::fs::read_to_string(directory().join("execution.log"))
            .unwrap()
            .lines()
            .collect::<Vec<_>>(),
        [
            "class-only:0",
            "dormant-created:0",
            "active:7:1:1",
            "dormant-invoked:7:1:2",
            "module:8:1:1",
            "instance:9:1:1"
        ]
    );
    assert_eq!(
        std::fs::read_to_string(directory().join("shadow-execution.log")).unwrap(),
        "shadow-static:IncompatibleClassChangeError\n"
    );
}
#[test]
fn exact_static_class_namespace_is_empty_but_real_native_initialization_and_calls_remain() {
    let before = raw();
    let after = enriched("main");
    let host = after.find_symbol("namespacecase/JavaStaticHost#").unwrap();
    assert_ne!(
        after.symbols[host.index()].flags & SYMBOL_JVM_CLASS_HEADER_VERIFIED,
        0
    );
    assert_eq!(after.symbols[host.index()].flags & SYMBOL_DEFINED, 0);
    let ping = after
        .find_symbol("namespacecase/JavaStaticHost#ping().")
        .unwrap();
    let source_before = operations(&before, "namespacecase/ActiveSuite#observed.");
    let old = source_before
        .iter()
        .find(|op| {
            op.opcode == Opcode::LoadField
                && before.symbol_name(op.target) == "namespacecase/JavaStaticHost#"
        })
        .unwrap();
    let source_after = operations(&after, "namespacecase/ActiveSuite#observed.");
    let namespace = source_after.iter().find(|op| op.dest == old.dest).unwrap();
    assert_eq!(namespace.opcode, Opcode::Constant);
    assert!(namespace.target.is_none());
    let call = source_after.iter().find(|op| op.target == ping).unwrap();
    assert_eq!(call.opcode, Opcode::Call);
    assert_eq!(
        call.a, namespace.dest,
        "explicit EMPTY receiver, not enclosing this"
    );
    let init = after
        .find_symbol(&owned(
            "namespacecase/JavaStaticHost",
            "<class-init>",
            "()V",
        ))
        .unwrap();
    assert!(
        operations(&after, "namespacecase/JavaStaticHost#ping().")
            .iter()
            .any(|op| op.opcode == Opcode::Initialize && op.target == init)
    );
    assert!(
        after
            .operations
            .iter()
            .any(|op| op.opcode == Opcode::StoreField
                && after
                    .symbol_name(op.target)
                    .contains("staticInitializations")),
        "real <clinit> observable effect remains"
    );
    let changed = after
        .find_symbol(&owned("namespacecase/JavaStaticHost", "changed", "()I"))
        .unwrap();
    assert!(
        operations(&after, "namespacecase/JavaStaticHost#ping().")
            .iter()
            .any(|op| op.opcode == Opcode::Call && op.target == changed)
    );
}
#[test]
fn class_literal_and_dormant_source_never_eagerly_initialize_the_static_host() {
    let facts = enriched("main");
    let host = facts.find_symbol("namespacecase/JavaStaticHost#").unwrap();
    let init = facts
        .find_symbol(&owned(
            "namespacecase/JavaStaticHost",
            "<class-init>",
            "()V",
        ))
        .unwrap();
    for body in [
        "namespacecase/ClassOnlySuite#observed.",
        "namespacecase/DormantSuite#later.",
    ] {
        assert!(!operations(&facts, body).iter().any(|op| matches!(
            op.opcode,
            Opcode::Allocate | Opcode::Initialize
        ) && [host, init].contains(&op.target)));
    }
    let ping = facts
        .find_symbol("namespacecase/JavaStaticHost#ping().")
        .unwrap();
    let deferred: Vec<_> = facts
        .bodies
        .iter()
        .filter(|body| body.flags & BODY_DEFERRED != 0)
        .collect();
    assert_eq!(deferred.len(), 1);
    assert!(
        facts.operations[deferred[0].operations.range()]
            .iter()
            .any(|op| op.opcode == Opcode::Call && op.target == ping)
    );
    let instance = facts
        .find_symbol("namespacecase/JavaInstanceHost#ping().")
        .unwrap();
    assert!(
        facts
            .operations
            .iter()
            .any(|op| op.opcode == Opcode::VirtualCall && op.target == instance)
    );
    let module = facts
        .find_symbol("namespacecase/ScalaModule.ping().")
        .unwrap();
    assert!(
        operations(&facts, "namespacecase/ModuleSuite#observed.")
            .iter()
            .any(|op| op.target == module && op.opcode == Opcode::VirtualCall)
    );
}
#[test]
fn earlier_instance_shadow_or_unavailable_prefix_cannot_authorize_static_namespace_erasure() {
    for mode in ["shadow", "unavailable"] {
        let facts = enriched(mode);
        assert!(
            operations(&facts, "namespacecase/ActiveSuite#observed.")
                .iter()
                .any(|op| op.opcode == Opcode::LoadField
                    && facts.symbol_name(op.target) == "namespacecase/JavaStaticHost#"),
            "{mode} leaves original unknown receiver"
        );
    }
}

#[test]
fn source_static_call_proves_native_changed_body_and_real_class_initialization() {
    let facts = enriched("main");
    let graph = selector_graph_build::build(&facts, &Default::default()).unwrap();
    let node = |name: &str| {
        graph
            .node_for_symbol(facts.find_symbol(name).unwrap())
            .unwrap()
    };
    let options = selector_solve::SolveOptions {
        workers: 2,
        memory_budget_bytes: 64 * 1024 * 1024,
        max_contexts: 10_000,
        max_steps: 1_000_000,
        execution_roots: Some(
            ["ActiveSuite", "DormantSuite", "ClassOnlySuite"]
                .into_iter()
                .map(|name| {
                    let receiver = facts
                        .find_symbol(&format!("namespacecase/{name}#"))
                        .unwrap();
                    selector_solve::ExecutionRoot {
                        node: graph.node_for_symbol(receiver).unwrap(),
                        receiver,
                    }
                })
                .collect::<Vec<_>>()
                .into(),
        ),
        ..Default::default()
    };
    for target in [
        owned("namespacecase/JavaStaticHost", "changed", "()I"),
        owned("namespacecase/JavaStaticHost", "<class-init>", "()V"),
    ] {
        let result = selector_solve::analyze(&facts, &graph, &[node(&target)], &options).unwrap();
        assert_ne!(result.completion, Completion::ResourceLimited);
        assert!(
            result.contains(node("namespacecase/ActiveSuite#")),
            "actual static call executes {target}"
        );
        assert!(
            !result.contains(node("namespacecase/DormantSuite#")),
            "dormant callback creation does not execute {target}"
        );
        assert!(
            !result.contains(node("namespacecase/ClassOnlySuite#")),
            "class literal does not execute {target}"
        );
    }
}
