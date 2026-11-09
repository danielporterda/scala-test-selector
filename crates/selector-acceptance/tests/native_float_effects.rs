//! Genuine javac/JVM scalar controls, then ordinary public native admission and
//! execution. Explicit callable roots are not CI suite-discovery authority.
use selector_facts::{FactBuilder, FactSnapshot};
use selector_graph_build::binary_inputs::{augment_binary_facts, load_binary_manifest};
use selector_models::binary::{self, Limits};
use selector_types::*;
use std::path::PathBuf;

const OWNER: &str = "floatingcase/Probe";
const PURE: &str = "floatingcase/Probe$Pure";
const CONTEXT: &str = "fixture:native-float-effects";
const PURE_METHODS: [(&str, &str, u8, bool); 8] = [
    ("fdiv", "(FF)F", 110, false),
    ("frem", "(FF)F", 114, false),
    ("ddiv", "(DD)D", 111, false),
    ("drem", "(DD)D", 115, false),
    ("idiv", "(II)I", 108, true),
    ("irem", "(II)I", 112, true),
    ("ldiv", "(JJ)J", 109, true),
    ("lrem", "(JJ)J", 113, true),
];
const EFFECT_METHODS: [(&str, &str); 11] = [
    ("changed", "()I"),
    ("field", "(FF)F"),
    ("callback", "(FFLjava/lang/Runnable;)F"),
    ("nativeCall", "(FF)F"),
    ("reflected", "(FFLjava/lang/String;)F"),
    ("monitor", "(FFLjava/lang/Object;)F"),
    ("array", "(FF[F)F"),
    ("caught", "(FFZ)F"),
    ("caughtCallback", "(FFZLjava/lang/Runnable;)F"),
    ("dynamic", "(FF)Ljava/lang/String;"),
    ("mixedInteger", "(FFII)F"),
];

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/native-float-effects")
}

fn identity(owner: &str, name: &str, descriptor: &str) -> String {
    format!(
        "@jvm/{}:{owner}{}:{name}{}:{descriptor}",
        owner.len(),
        name.len(),
        descriptor.len()
    )
}

fn parsed(owner: &str) -> binary::ClassFile<'static> {
    binary::parse_class(
        if owner == PURE {
            include_bytes!(
                "../../../fixtures/native-float-effects/classes/floatingcase/Probe$Pure.class"
            )
        } else {
            include_bytes!(
                "../../../fixtures/native-float-effects/classes/floatingcase/Probe.class"
            )
        },
        Limits::default(),
    )
    .unwrap()
}

fn admitted() -> FactSnapshot {
    let mut builder = FactBuilder::new();
    builder.facts.revision = builder.intern("native-float-effects-v1").unwrap();
    let context = builder.intern(CONTEXT).unwrap();
    let mut types = Vec::new();
    let mut methods = Vec::new();
    for owner in [PURE, OWNER] {
        let name = identity(owner, "<type>", "");
        let class = builder.ensure_global_symbol(&name, context).unwrap();
        builder.facts.symbols[class.index()].kind = 13;
        builder.facts.symbols[class.index()].flags = SYMBOL_NATIVE_BINARY;
        types.push(serde_json::json!({"context":CONTEXT,"compiler_symbol":name,"jvm_owner":owner}));
        let entries: Vec<_> = if owner == PURE {
            PURE_METHODS
                .iter()
                .map(|&(name, descriptor, _, _)| (name, descriptor))
                .collect()
        } else {
            EFFECT_METHODS.to_vec()
        };
        for (name, descriptor) in entries {
            let spelling = identity(owner, name, descriptor);
            let method = builder.ensure_global_symbol(&spelling, context).unwrap();
            let row = &mut builder.facts.symbols[method.index()];
            row.kind = 3;
            row.owner = class;
            row.flags = SYMBOL_NATIVE_BINARY;
            methods.push(
                serde_json::json!({"context":CONTEXT,"compiler_symbol":spelling,
                "jvm_owner":owner,"jvm_name":name,"descriptor":descriptor}),
            );
        }
    }
    let mut facts = builder.finish().unwrap();
    let receipt: serde_json::Value =
        serde_json::from_slice(&std::fs::read(fixture().join("manifest.json")).unwrap()).unwrap();
    let jar = receipt["files"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["path"] == "bytecode.jar")
        .unwrap();
    let manifest = serde_json::json!({"version":1,"revision":facts.text(facts.revision),"java_feature":21,
        "contexts":[{"id":CONTEXT,"entries":[{"path":fixture().join("bytecode.jar"),"sha256":jar["sha256"],"kind":"jar"}]}],
        "types":types,"methods":methods});
    let temp = tempfile::tempdir().unwrap();
    let path = temp.path().join("binary.json");
    std::fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    let mut inputs = load_binary_manifest(&path, &facts).unwrap();
    augment_binary_facts(&mut facts, &mut inputs).unwrap();
    facts
}

#[test]
fn genuine_jvm_zero_divisor_and_independent_effect_observations_are_pinned() {
    let receipt: serde_json::Value =
        serde_json::from_slice(&std::fs::read(fixture().join("manifest.json")).unwrap()).unwrap();
    assert_eq!(
        std::fs::read_to_string(fixture().join("execution.stdout")).unwrap(),
        receipt["expected_stdout"].as_str().unwrap()
    );
    let observations = receipt["expected_stdout"].as_str().unwrap();
    assert!(
        observations.contains("float:Infinity:NaN\ndouble:Infinity:NaN\ninteger-zero-throws:4\n")
    );
    assert!(observations.contains("callback-hits:1\nnative:UnsatisfiedLinkError\n"));
    assert!(observations.contains("handler-callback-hits:2:3\n"));
    assert!(
        observations
            .contains("throw-identity:true\ndynamic:value=Infinity\nmixed:ArithmeticException\n")
    );
}

#[test]
fn exact_floating_div_rem_opcodes_close_only_scalar_data_and_integer_variants_remain_open() {
    let class = parsed(PURE);
    for (name, descriptor, opcode, throws) in PURE_METHODS {
        let method = class.method(name, Some(descriptor)).unwrap();
        // Independently known javac geometry: two width-correct local loads,
        // one arithmetic instruction at PC2, then the matching return.
        assert_eq!(method.code.unwrap().len(), 4);
        assert_eq!(method.code.unwrap()[2], opcode, "actual {name} instruction");
        let summary = binary::summarize_with_envelope(&class, method, Limits::default());
        assert_eq!(summary.complete(), !throws, "{name}: {:?}", summary.unknown);
        assert!(summary.calls.is_empty() && summary.field_writes.is_empty());
        assert!(
            summary
                .values
                .iter()
                .any(|row| matches!(row, binary::Value::UnknownData))
        );
        if throws {
            assert!(
                summary.unknown_offsets.contains(&2),
                "{name} remains a throwing frontier"
            );
        } else {
            assert!(
                summary.unknown_offsets.is_empty(),
                "{name} has no execution hole"
            );
        }
    }
}

#[test]
fn floating_data_does_not_erase_writes_callbacks_handlers_or_other_open_channels() {
    let class = parsed(OWNER);
    let summary = |name, descriptor| {
        binary::summarize_with_envelope(
            &class,
            class.method(name, Some(descriptor)).unwrap(),
            Limits::default(),
        )
    };
    let field = summary("field", "(FF)F");
    assert!(
        field
            .field_writes
            .iter()
            .any(|row| row.member.owner == OWNER
                && row.member.name == "stored"
                && row.receiver.is_none())
    );
    let callback = summary("callback", "(FFLjava/lang/Runnable;)F");
    assert!(
        callback
            .calls
            .iter()
            .any(|row| row.member.owner == "java/lang/Runnable" && row.member.name == "run")
    );
    let native = summary("nativeCall", "(FF)F");
    assert!(
        native
            .calls
            .iter()
            .any(|row| row.member.owner == OWNER && row.member.name == "opaque")
    );
    let caught = class.method("caught", Some("(FFZ)F")).unwrap();
    assert!(caught.exception_handlers > 0);
    let caught = binary::summarize_with_envelope(&class, caught, Limits::default());
    assert!(
        caught
            .calls
            .iter()
            .any(|row| row.member.owner == OWNER && row.member.name == "changed"),
        "handler call remains a may-effect"
    );
    let caught_callback = class
        .method("caughtCallback", Some("(FFZLjava/lang/Runnable;)F"))
        .unwrap();
    assert!(caught_callback.exception_handlers > 0);
    let caught_callback =
        binary::summarize_with_envelope(&class, caught_callback, Limits::default());
    assert!(
        caught_callback
            .calls
            .iter()
            .any(|row| row.member.owner == "java/lang/Runnable" && row.member.name == "run"),
        "callback in actual exception handler remains a may-effect"
    );
    for (name, descriptor) in [
        ("reflected", "(FFLjava/lang/String;)F"),
        ("monitor", "(FFLjava/lang/Object;)F"),
        ("array", "(FF[F)F"),
        ("dynamic", "(FF)Ljava/lang/String;"),
        ("mixedInteger", "(FFII)F"),
        ("opaque", "()V"),
    ] {
        assert!(
            !summary(name, descriptor).complete(),
            "{name} remains open independently of float division"
        );
    }
}

#[test]
fn public_native_execution_distinguishes_closed_floating_roots_from_throwing_and_opaque_effects() {
    let facts = admitted();
    let graph = selector_graph_build::build(
        &facts,
        &selector_graph_build::BuildOptions {
            workers: 2,
            include_models: false,
        },
    )
    .unwrap();
    let node = |owner, name, descriptor| {
        graph
            .node_for_symbol(
                facts
                    .find_symbol(&identity(owner, name, descriptor))
                    .unwrap(),
            )
            .unwrap()
    };
    let mut roots = Vec::new();
    for (owner, entries) in [
        (
            PURE,
            PURE_METHODS
                .iter()
                .map(|&(name, descriptor, _, _)| (name, descriptor))
                .collect::<Vec<_>>(),
        ),
        (OWNER, EFFECT_METHODS.to_vec()),
    ] {
        let receiver = facts.find_symbol(&identity(owner, "<type>", "")).unwrap();
        for (name, descriptor) in entries {
            roots.push(selector_solve::ExecutionRoot {
                node: node(owner, name, descriptor),
                receiver,
            });
        }
    }
    let changed = node(OWNER, "changed", "()I");
    let result = selector_solve::analyze(
        &facts,
        &graph,
        &[changed],
        &selector_solve::SolveOptions {
            workers: 2,
            memory_budget_bytes: 64 * 1024 * 1024,
            max_contexts: 10_000,
            max_steps: 1_000_000,
            execution_roots: Some(roots.into()),
            ..Default::default()
        },
    )
    .unwrap();
    assert_ne!(result.completion, Completion::ResourceLimited);
    for (name, descriptor, _, throws) in PURE_METHODS {
        let root = node(PURE, name, descriptor);
        assert_eq!(
            result.guarded_roots.contains(&root),
            throws,
            "actual {name} execution frontier"
        );
        assert!(
            !result.contains(root),
            "unrelated scalar caller has no changed-call proof"
        );
    }
    for (name, descriptor) in [
        ("callback", "(FFLjava/lang/Runnable;)F"),
        ("caughtCallback", "(FFZLjava/lang/Runnable;)F"),
        ("nativeCall", "(FF)F"),
        ("reflected", "(FFLjava/lang/String;)F"),
        ("monitor", "(FFLjava/lang/Object;)F"),
        ("array", "(FF[F)F"),
        ("dynamic", "(FF)Ljava/lang/String;"),
        ("mixedInteger", "(FFII)F"),
    ] {
        assert!(
            result
                .guarded_roots
                .contains(&node(OWNER, name, descriptor)),
            "{name} must retain its independent effect boundary"
        );
    }
    assert!(
        result.contains(node(OWNER, "caught", "(FFZ)F")),
        "actual handler changed call keeps its impact proof"
    );
    let field = facts
        .find_symbol(&identity(OWNER, "field", "(FF)F"))
        .unwrap();
    let body = facts
        .bodies
        .iter()
        .find(|body| body.symbol == field)
        .unwrap();
    assert!(
        facts.operations[body.operations.range()]
            .iter()
            .any(|row| row.opcode == Opcode::StoreField && row.flags & OP_STATIC_FIELD != 0),
        "static global effect survives normalized lowering"
    );
}
