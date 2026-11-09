//! New declared-runtime authority, never a claim about the historical compiler
//! image or isolation of an executing JVM. Default rejection controls use tiny
//! normalized protocol inputs; the genuine complete-image gate is explicit.
use selector_facts::{FactBuilder, FactSnapshot};
use selector_graph_build::binary_inputs::{
    BinaryInputOptions, NativeAdmissionLimits, augment_binary_facts_with_limits,
    load_binary_manifest, load_binary_manifest_with_platform,
};
use selector_graph_build::binary_platform::PlatformOptions;
use selector_types::*;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::path::{Path, PathBuf};

const CONTEXT: &str = "fixture:declared-platform";
const OBJECT: &str = "java/lang/Object";
const SERIALIZABLE: &str = "java/io/Serializable";
const SYSTEM: &str = "java/lang/System";
const STRING: &str = "java/lang/String";

fn hash(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}
fn endpoint(owner: &str, name: &str, descriptor: &str) -> String {
    format!(
        "@jvm/{}:{owner}{}:{name}{}:{descriptor}",
        owner.len(),
        name.len(),
        descriptor.len()
    )
}
fn facts(context: &str) -> FactSnapshot {
    let mut builder = FactBuilder::new();
    builder.facts.revision = builder.intern("declared-runtime-acceptance").unwrap();
    let context = builder.intern(context).unwrap();
    // Explicitly normalized compiler-reference seam, not a captured declaration.
    // Without an explicit platform the legacy Object shortcut can use this
    // opaque endpoint; declared image authority must instead lower real bytes.
    builder
        .ensure_global_symbol("java/lang/Object#", context)
        .unwrap();
    for (owner, kind) in [(OBJECT, 13), (SERIALIZABLE, 14), (SYSTEM, 13), (STRING, 13)] {
        let class = builder
            .ensure_global_symbol(&endpoint(owner, "<type>", ""), context)
            .unwrap();
        let row = &mut builder.facts.symbols[class.index()];
        row.kind = kind;
        row.flags = SYMBOL_NATIVE_BINARY;
        for (name, descriptor) in if owner == OBJECT {
            vec![("<init>", "()V")]
        } else if owner == SYSTEM {
            vec![("nanoTime", "()J")]
        } else if owner == STRING {
            vec![("length", "()I")]
        } else {
            vec![]
        } {
            let method = builder
                .ensure_global_symbol(&endpoint(owner, name, descriptor), context)
                .unwrap();
            let row = &mut builder.facts.symbols[method.index()];
            row.owner = class;
            row.kind = 3;
            row.flags = SYMBOL_NATIVE_BINARY;
        }
    }
    builder.finish().unwrap()
}
fn binary_manifest(path: &Path, facts: &FactSnapshot, context: &str, feature: u64) {
    let methods: Vec<_> = [
        (OBJECT, "<init>", "()V"),
        (SYSTEM, "nanoTime", "()J"),
        (STRING, "length", "()I"),
    ]
    .into_iter()
    .map(|(owner, name, descriptor)| {
        json!({"context":context,
            "compiler_symbol":endpoint(owner,name,descriptor),
            "jvm_owner":owner,"jvm_name":name,"descriptor":descriptor})
    })
    .collect();
    let types = [OBJECT, SERIALIZABLE, SYSTEM, STRING].map(|owner| {
        json!({
        "context":context,"compiler_symbol":endpoint(owner,"<type>",""),"jvm_owner":owner})
    });
    std::fs::write(
        path,
        serde_json::to_vec(&json!({
            "version":1,"revision":facts.text(facts.revision),"java_feature":feature,
            "contexts":[{"id":context,"entries":[]}],
            "types":types,
            "methods":methods
        }))
        .unwrap(),
    )
    .unwrap();
}
fn file_ref(path: &Path) -> Value {
    let bytes = std::fs::read(path).unwrap();
    json!({"path":path,"sha256":hash(&bytes),"bytes":bytes.len()})
}
struct ProtocolControl {
    directory: tempfile::TempDir,
    contexts: PathBuf,
    binary: PathBuf,
    platform: Value,
    producer: ContentHash,
}
impl ProtocolControl {
    fn new() -> Self {
        let directory = tempfile::tempdir().unwrap();
        let contexts = directory.path().join("contexts.json");
        std::fs::write(
            &contexts,
            serde_json::to_vec(&json!({
                "schema_version":"sbt-compiler-context/v1","revision":"declared-runtime-acceptance",
                "source_root":directory.path(),"errors":[],
                "contexts":[{"context_id":CONTEXT,"full_classpath":[]}],"input_objects":[],
                "java_runtime":{"java_version":"21"}
            }))
            .unwrap(),
        )
        .unwrap();
        // A deliberately normalized trust-boundary fixture. These bytes are NOT
        // asserted to be a JVM image. Every use below must reject authority.
        let home = directory.path().join("not-a-runtime-image");
        std::fs::create_dir_all(home.join("bin")).unwrap();
        std::fs::create_dir_all(home.join("lib")).unwrap();
        let home = home.canonicalize().unwrap();
        for name in ["bin/java", "release", "lib/modules"] {
            std::fs::write(home.join(name), b"normalized protocol mutation control").unwrap();
        }
        let original = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../fixtures/native-hierarchy/bootstrap.jar");
        let archive = directory.path().join("java.base.jar");
        std::fs::copy(original, &archive).unwrap();
        let inventory = directory.path().join("inventory.json");
        let object =
            include_bytes!("../../../fixtures/native-hierarchy/classes/java/lang/Object.class");
        std::fs::write(
            &inventory,
            serde_json::to_vec(&json!([
                {"owner":OBJECT,"class_sha256":hash(object),"bytes":object.len()}
            ]))
            .unwrap(),
        )
        .unwrap();
        let producer = ContentHash::from_hex(&hash(b"normalized-platform-test-producer")).unwrap();
        let platform = json!({
            "schema":"selector-declared-runtime-platform/v1",
            "capture_sha256":hash(&std::fs::read(&contexts).unwrap()),
            "context_ids":[CONTEXT],"java_feature":21,
            "image":{"canonical_home":home.canonicalize().unwrap(),"launcher":file_ref(&home.join("bin/java")),
                "release":file_ref(&home.join("release")),"modules":file_ref(&home.join("lib/modules"))},
            "java_base":{"archive":file_ref(&archive),"inventory":file_ref(&inventory)},
            "producer_sha256":producer.to_string(),
            "policy":{"authority":"new_declared_runtime","module":"java.base",
                "complete_inventory":true,"historical_compiler_image_proven":false,
                "runtime_isolation_proven":false,
                "lookup":"jrt_filesystem_no_reflective_target_loading","java_options":[],
                "environment":{"JAVA_TOOL_OPTIONS":null,"JDK_JAVA_OPTIONS":null,"_JAVA_OPTIONS":null}}
        });
        let mut platform = platform;
        platform["java_base"]["archive"]["path"] = json!("java.base.jar");
        platform["java_base"]["inventory"]["path"] = json!("inventory.json");
        let binary = directory.path().join("binary.json");
        binary_manifest(&binary, &facts(CONTEXT), CONTEXT, 21);
        Self {
            directory,
            contexts,
            binary,
            platform,
            producer,
        }
    }
    fn rejected(&self, value: &Value) -> String {
        let path = self.directory.path().join("platform.json");
        std::fs::write(&path, serde_json::to_vec(value).unwrap()).unwrap();
        let platform = PlatformOptions {
            manifest: path,
            contexts: self.contexts.clone(),
            producer: self.producer,
        };
        match load_binary_manifest_with_platform(
            &self.binary,
            &facts(CONTEXT),
            &BinaryInputOptions::default(),
            Some(&platform),
        ) {
            Err(error) => error.to_string(),
            Ok(_) => panic!("malformed normalized platform authority was admitted"),
        }
    }
}

#[test]
fn absent_platform_preserves_unavailable_bootstrap_and_native_execution_guards() {
    let control = ProtocolControl::new();
    let mut facts = facts(CONTEXT);
    let mut inputs = load_binary_manifest(&control.binary, &facts).unwrap();
    augment_binary_facts_with_limits(&mut facts, &mut inputs, Default::default()).unwrap();
    for owner in [OBJECT, SERIALIZABLE, SYSTEM] {
        let symbol = facts.find_symbol(&endpoint(owner, "<type>", "")).unwrap();
        assert_eq!(
            facts.symbols[symbol.index()].flags & SYMBOL_JVM_CLASS_HEADER_VERIFIED,
            0
        );
    }
    let missing = facts
        .find_symbol(&endpoint(SYSTEM, "nanoTime", "()J"))
        .unwrap();
    assert!(
        facts
            .issues
            .iter()
            .any(|issue| issue.kind == IssueKind::MissingBinary && issue.symbol == missing)
    );
    facts.identity =
        selector_facts::codec::write(&control.directory.path().join("facts.bin"), &facts).unwrap();
    let graph = selector_graph_build::build(&facts, &Default::default()).unwrap();
    let root = graph.node_for_symbol(missing).unwrap();
    let options = selector_solve::SolveOptions {
        workers: 1,
        max_contexts: 100,
        max_steps: 10_000,
        memory_budget_bytes: 16 * 1024 * 1024,
        execution_roots: Some(
            vec![selector_solve::ExecutionRoot {
                node: root,
                receiver: SymbolId::NONE,
            }]
            .into(),
        ),
        ..Default::default()
    };
    let mut session = selector_solve::QuerySession::new(&facts, &graph, &options).unwrap();
    let result = session.analyze(&[]).unwrap();
    assert_ne!(result.completion, Completion::ResourceLimited);
    assert!(result.guarded_roots.contains(&root));
}

#[test]
fn malformed_protocol_scope_producer_hooks_and_image_hashes_fail_closed() {
    let control = ProtocolControl::new();
    let mut wrong = control.platform.clone();
    wrong["schema"] = json!("selector-declared-runtime-platform/v0");
    assert!(
        control
            .rejected(&wrong)
            .contains("unsupported authority/policy/producer")
    );
    wrong = control.platform.clone();
    wrong["capture_sha256"] = json!("00".repeat(32));
    assert!(
        control
            .rejected(&wrong)
            .contains("original context capture hash")
    );
    wrong = control.platform.clone();
    wrong["context_ids"] = json!(["foreign:context"]);
    assert!(
        control
            .rejected(&wrong)
            .contains("context scope/runtime options")
    );
    wrong = control.platform.clone();
    wrong["producer_sha256"] = json!("01".repeat(32));
    assert!(
        control
            .rejected(&wrong)
            .contains("unsupported authority/policy/producer")
    );
    for hook in [
        "--patch-module=java.base=/untrusted",
        "-Xbootclasspath/a:/untrusted",
        "-javaagent:/untrusted",
    ] {
        wrong = control.platform.clone();
        wrong["policy"]["java_options"] = json!([hook]);
        assert!(
            control
                .rejected(&wrong)
                .contains("unsupported authority/policy/producer")
        );
    }
    wrong = control.platform.clone();
    wrong["policy"]["environment"]["JAVA_TOOL_OPTIONS"] = json!("-javaagent:/untrusted");
    assert!(
        control
            .rejected(&wrong)
            .contains("unsupported authority/policy/producer")
    );
    for image in ["launcher", "release", "modules"] {
        wrong = control.platform.clone();
        wrong["image"][image]["sha256"] = json!("02".repeat(32));
        assert!(
            control.rejected(&wrong).contains("file hash/size mismatch"),
            "{}",
            control.rejected(&wrong)
        );
    }
}

#[test]
fn archive_inventory_and_per_class_digest_mismatch_cannot_publish_header_authority() {
    let control = ProtocolControl::new();
    for part in ["archive", "inventory"] {
        let mut wrong = control.platform.clone();
        wrong["java_base"][part]["sha256"] = json!("03".repeat(32));
        assert!(
            control.rejected(&wrong).contains("file hash/size mismatch"),
            "{}",
            control.rejected(&wrong)
        );
    }
    // Re-seal the envelope after changing ONLY a class digest; testing merely
    // the outer inventory checksum would miss the class-to-archive seam.
    let inventory = control.directory.path().join("wrong-class-inventory.json");
    std::fs::write(
        &inventory,
        serde_json::to_vec(&json!([
            {"owner":OBJECT,"class_sha256":"04".repeat(32),"bytes":2487}
        ]))
        .unwrap(),
    )
    .unwrap();
    let mut wrong = control.platform.clone();
    wrong["java_base"]["inventory"] = file_ref(&inventory);
    wrong["java_base"]["inventory"]["path"] = json!("wrong-class-inventory.json");
    assert!(
        control
            .rejected(&wrong)
            .contains("class inventory hash/size")
    );
}

#[test]
#[ignore = "requires an explicitly captured complete declared-runtime java.base image; no host-JDK fallback"]
fn genuine_complete_java_base_normal_admission_keeps_native_system_opaque() {
    let manifest = PathBuf::from(
        std::env::var_os("SELECTOR_PLATFORM_MANIFEST").expect("SELECTOR_PLATFORM_MANIFEST"),
    );
    let contexts = PathBuf::from(
        std::env::var_os("SELECTOR_PLATFORM_CONTEXTS").expect("SELECTOR_PLATFORM_CONTEXTS"),
    );
    let producer = ContentHash::from_hex(
        &std::env::var("SELECTOR_PLATFORM_PRODUCER").expect("SELECTOR_PLATFORM_PRODUCER"),
    )
    .unwrap();
    let declaration: Value = serde_json::from_slice(&std::fs::read(&manifest).unwrap()).unwrap();
    let inventory_path = manifest.parent().unwrap().join(
        declaration["java_base"]["inventory"]["path"]
            .as_str()
            .unwrap(),
    );
    let inventory: Vec<Value> =
        serde_json::from_slice(&std::fs::read(inventory_path).unwrap()).unwrap();
    assert_eq!(
        declaration["policy"]["historical_compiler_image_proven"],
        false
    );
    assert_eq!(declaration["policy"]["runtime_isolation_proven"], false);
    let context = declaration["context_ids"][0].as_str().unwrap();
    let temporary = tempfile::tempdir().unwrap();
    let mut facts = facts(context);
    let binary = temporary.path().join("binary.json");
    binary_manifest(
        &binary,
        &facts,
        context,
        declaration["java_feature"].as_u64().unwrap(),
    );
    let platform = PlatformOptions {
        manifest,
        contexts,
        producer,
    };
    // Seal the native-map lane to this exact admitted declaration. A platform
    // file is never an ambient fallback for an unrelated old binary map.
    let admitted = selector_graph_build::binary_platform::admit(&platform).unwrap();
    let mut map: Value = serde_json::from_slice(&std::fs::read(&binary).unwrap()).unwrap();
    map["declared_platform"] = serde_json::to_value(&admitted.binding).unwrap();
    map["contexts"][0]["entries"] = json!([{
        "path":admitted.entry.path,"sha256":admitted.entry.sha256.to_string(),"kind":"jar"
    }]);
    std::fs::write(&binary, serde_json::to_vec(&map).unwrap()).unwrap();
    let mut inputs = load_binary_manifest_with_platform(
        &binary,
        &facts,
        &BinaryInputOptions {
            workers: 2,
            ..Default::default()
        },
        Some(&platform),
    )
    .unwrap();
    augment_binary_facts_with_limits(
        &mut facts,
        &mut inputs,
        NativeAdmissionLimits {
            classes_per_context: 64,
            bytes_per_context: 8 * 1024 * 1024,
            methods: 32,
        },
    )
    .unwrap();
    for owner in [OBJECT, SERIALIZABLE] {
        let symbol = facts.find_symbol(&endpoint(owner, "<type>", "")).unwrap();
        let row = &facts.symbols[symbol.index()];
        assert_ne!(row.flags & SYMBOL_JVM_CLASS_HEADER_VERIFIED, 0, "{owner}");
        // An explicit endpoint keeps its original declaration facet (fileNONE).
        // The admitted class recipe owns the actual byte authority.
        let recipe = facts
            .bodies
            .iter()
            .find(|b| b.symbol == symbol && b.flags & BODY_BINARY_RECIPE != 0)
            .unwrap();
        assert!(!recipe.file.is_none());
        let file = &facts.files[recipe.file.index()];
        let selected = inventory.iter().find(|r| r["owner"] == owner).unwrap();
        assert_eq!(
            file.source_hash,
            ContentHash::from_hex(selected["class_sha256"].as_str().unwrap()).unwrap()
        );
        assert_eq!(file.context, row.context);
        assert_ne!(file.flags & FILE_BINARY_SOURCE, 0);
        assert!(facts.text(file.path).ends_with(&format!("!/{owner}.class")));
    }
    let init = facts
        .find_symbol(&endpoint(OBJECT, "<init>", "()V"))
        .unwrap();
    let body = facts.bodies.iter().find(|b| b.symbol == init).unwrap();
    assert_ne!(body.flags & BODY_BINARY_RECIPE, 0);
    assert!(
        facts.operations[body.operations.range()]
            .iter()
            .any(|op| op.opcode == Opcode::Return)
    );
    let placeholder = facts.find_symbol("java/lang/Object#").unwrap();
    assert_ne!(init, placeholder);
    assert!(facts.bodies.iter().all(|body| body.symbol != placeholder));
    let native = facts
        .find_symbol(&endpoint(SYSTEM, "nanoTime", "()J"))
        .unwrap();
    let body = facts.bodies.iter().find(|b| b.symbol == native).unwrap();
    let selected = inventory.iter().find(|row| row["owner"] == SYSTEM).unwrap();
    assert_eq!(
        facts.files[body.file.index()].source_hash,
        ContentHash::from_hex(selected["class_sha256"].as_str().unwrap()).unwrap()
    );
    assert!(
        facts.operations[body.operations.range()]
            .iter()
            .any(|op| op.opcode == Opcode::Unknown)
    );
    assert!(
        facts
            .issues
            .iter()
            .any(|issue| issue.kind == IssueKind::UnknownExecution && issue.symbol == native)
    );
    facts.identity =
        selector_facts::codec::write(&temporary.path().join("facts.bin"), &facts).unwrap();
    let graph = selector_graph_build::build(&facts, &Default::default()).unwrap();
    let root = graph.node_for_symbol(native).unwrap();
    let options = selector_solve::SolveOptions {
        workers: 1,
        max_contexts: 100,
        max_steps: 10_000,
        memory_budget_bytes: 16 * 1024 * 1024,
        execution_roots: Some(
            vec![selector_solve::ExecutionRoot {
                node: root,
                receiver: SymbolId::NONE,
            }]
            .into(),
        ),
        ..Default::default()
    };
    let mut session = selector_solve::QuerySession::new(&facts, &graph, &options).unwrap();
    let result = session.analyze(&[]).unwrap();
    assert_ne!(result.completion, Completion::ResourceLimited);
    assert!(result.guarded_roots.contains(&root));
}
