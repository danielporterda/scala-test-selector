//! Actual javac LambdaMetafactory captures and independent JVM effect receipts.
//! Native endpoints below are explicit classfile metadata, not invented source
//! compiler occurrences or a claim that unknown bootstrap effects are pure.
use selector_facts::{FactBuilder, FactSnapshot};
use selector_graph_build::binary_inputs::{augment_binary_facts, load_binary_manifest};
use selector_types::*;
use std::path::PathBuf;

const OWNER: &str = "lambdacase/Probe";
const CONTEXT: &str = "fixture:native-lambdas";

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/native-lambdas")
}
fn native_name(name: &str, descriptor: &str) -> String {
    native_name_for(OWNER, name, descriptor)
}
fn native_name_for(owner: &str, name: &str, descriptor: &str) -> String {
    format!(
        "@jvm/{}:{owner}{}:{name}{}:{descriptor}",
        owner.len(),
        name.len(),
        descriptor.len()
    )
}
fn admitted() -> FactSnapshot {
    let mut builder = FactBuilder::new();
    builder.facts.revision = builder.intern("native-lambdas-fixture-v1").unwrap();
    let context = builder.intern(CONTEXT).unwrap();
    let class = builder
        .ensure_symbol(&native_name("<type>", ""), FileId::NONE)
        .unwrap();
    builder.facts.symbols[class.index()].kind = 13;
    builder.facts.symbols[class.index()].context = context;
    let mut facts = builder.finish().unwrap();
    let receipt: serde_json::Value =
        serde_json::from_slice(&std::fs::read(fixture().join("manifest.json")).unwrap()).unwrap();
    let jar = receipt["files"]
        .as_array()
        .unwrap()
        .iter()
        .find(|file| file["path"] == "bytecode.jar")
        .unwrap();
    let methods: Vec<_> = [
        ("<init>", "()V"),
        ("staticClosure", "(I)Ljava/lang/Runnable;"),
        ("receiverClosure", "(I)Ljava/lang/Runnable;"),
        ("boundClosure", "()Ljava/lang/Runnable;"),
        ("runStatic", "()V"),
        ("runReceiver", "()V"),
        ("runBound", "()V"),
        ("separateStaticClosure", "()Ljava/lang/Runnable;"),
        ("runSeparate", "()V"),
        ("unbound", "()Ljava/util/function/Consumer;"),
        ("unsupportedThenStore", "(I)V"),
    ]
    .into_iter()
    .map(|(name, descriptor)| {
        serde_json::json!({
            "context":CONTEXT, "jvm_owner":OWNER, "jvm_name":name, "descriptor":descriptor
        })
    })
    .collect();
    let manifest = serde_json::json!({"version":1,"revision":facts.text(facts.revision),
        "java_feature":21,
        "contexts":[{"id":CONTEXT,"entries":[{"path":fixture().join("bytecode.jar"),
            "sha256":jar["sha256"],"kind":"jar"}]}],
        "types":[{"context":CONTEXT,"compiler_symbol":native_name("<type>", ""),"jvm_owner":OWNER}],
        "methods":methods});
    let temporary = tempfile::tempdir().unwrap();
    let path = temporary.path().join("binary.json");
    std::fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    let mut inputs = load_binary_manifest(&path, &facts).unwrap();
    augment_binary_facts(&mut facts, &mut inputs).unwrap();
    facts
}
fn body<'a>(
    facts: &'a FactSnapshot,
    name: &str,
    descriptor: &str,
) -> &'a selector_facts::BodyRecord {
    let symbol = facts.find_symbol(&native_name(name, descriptor)).unwrap();
    facts
        .bodies
        .iter()
        .find(|body| body.symbol == symbol)
        .unwrap()
}

#[test]
fn actual_jvm_defers_all_three_lambda_shapes_until_invocation() {
    assert_eq!(
        std::fs::read_to_string(fixture().join("execution.log"))
            .unwrap()
            .lines()
            .collect::<Vec<_>>(),
        [
            "deferred:0:0",
            "static:3:0",
            "receiver:3:5",
            "bound:3:6",
            "opaque-followed-by-store:9",
            "native-wrappers:6:6",
            "target-created:0:0",
            "target-run:1:1",
            "target-wrapper:1:2",
            "unbound-created:6",
            "unbound-run:7"
        ]
    );
}

#[test]
fn genuine_bootstrap_handles_preserve_capture_order_without_eager_calls() {
    use selector_models::binary::{self, InvokeKind, Value};
    let class = binary::parse_class(
        include_bytes!("../../../fixtures/native-lambdas/classes/lambdacase/Probe.class"),
        binary::Limits::default(),
    )
    .unwrap();
    for (name, descriptor, kind, implementation, expected_captures) in [
        (
            "staticClosure",
            "(I)Ljava/lang/Runnable;",
            InvokeKind::Static,
            "lambda$staticClosure$0",
            vec![Value::Argument(0)],
        ),
        (
            "receiverClosure",
            "(I)Ljava/lang/Runnable;",
            InvokeKind::Virtual,
            "lambda$receiverClosure$1",
            vec![Value::Receiver, Value::Argument(0)],
        ),
        (
            "boundClosure",
            "()Ljava/lang/Runnable;",
            InvokeKind::Virtual,
            "next",
            vec![Value::Receiver],
        ),
    ] {
        let method = class.method(name, Some(descriptor)).unwrap();
        let summary = binary::summarize(&class, method, binary::Limits::default());
        assert!(summary.complete(), "{name}: {:?}", summary.unknown);
        assert_eq!(summary.lambdas.len(), 1);
        assert!(
            summary.calls.is_empty(),
            "creation cannot execute the implementation"
        );
        assert!(
            !summary.effects_complete(),
            "a callable value is not an empty effect summary"
        );
        let lambda = &summary.lambdas[0];
        assert_eq!(lambda.interface, "java/lang/Runnable");
        assert_eq!(lambda.sam_name, "run");
        assert_eq!(lambda.sam_descriptor, "()V");
        assert_eq!(lambda.kind, kind);
        assert_eq!(lambda.implementation.owner, OWNER);
        assert_eq!(lambda.implementation.name, implementation);
        let captures: Vec<_> = summary.arguments[lambda.captures.range()]
            .iter()
            .map(|value| summary.values[value.0 as usize])
            .collect();
        assert_eq!(captures, expected_captures);
        assert_eq!(
            summary.values[summary.returned.unwrap().0 as usize],
            Value::Lambda(0)
        );
    }
}

#[test]
fn pinned_scalatest_alt_metafactory_keeps_its_later_registration_setter() {
    use selector_models::binary::{self, CapturedClasspath, ClasspathEntry, EntryKind, InvokeKind};
    let curried = fixture()
        .parent()
        .unwrap()
        .join("curried-synthetics/binary.json");
    let capture: serde_json::Value =
        serde_json::from_slice(&std::fs::read(curried).unwrap()).unwrap();
    let entry = capture["contexts"][0]["entries"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| {
            row["path"]
                .as_str()
                .unwrap()
                .contains("scalatest-wordspec_2.13-3.2.19.jar")
        })
        .expect("independently pinned genuine WordSpec runtime input");
    let mut loader = CapturedClasspath::new(
        vec![ClasspathEntry {
            path: PathBuf::from(entry["path"].as_str().unwrap()),
            sha256: ContentHash::from_hex(entry["sha256"].as_str().unwrap()).unwrap(),
            kind: EntryKind::Jar,
        }],
        binary::Limits::default(),
    )
    .unwrap()
    .with_java_feature(Some(21))
    .unwrap();
    let resolved = loader
        .resolve("org/scalatest/wordspec/AnyWordSpecLike")
        .unwrap();
    assert!(resolved.proof.class_hash.is_some());
    let class = binary::parse_class(&resolved.bytes, binary::Limits::default()).unwrap();
    let method = class
        .method(
            "$init$",
            Some("(Lorg/scalatest/wordspec/AnyWordSpecLike;)V"),
        )
        .unwrap();
    let summary = binary::summarize(&class, method, binary::Limits::default());
    let engine = summary
        .lambdas
        .iter()
        .find(|lambda| lambda.offset == 5)
        .expect("actual altMetafactory flags5/redundant reference bridge at bytecode5");
    assert_eq!(engine.kind, InvokeKind::Static);
    assert_eq!(engine.interface, "scala/Function0");
    assert_eq!(engine.sam_descriptor, "()Ljava/lang/Object;");
    assert_eq!(engine.instantiated_descriptor, "()Ljava/lang/String;");
    assert_eq!(engine.implementation.name, "$anonfun$engine$1");
    assert_eq!(engine.captures.len, 0);
    assert!(!summary.unknown_offsets.contains(&5));
    assert!(
        summary.calls.iter().any(|call| call.offset > 5
            && call.member.name.contains("subjectRegistrationFunction")
            && call.member.name.contains("_setter_")),
        "the early lambda cannot discard the later real registration setter"
    );
}

#[test]
fn admitted_native_recipes_bind_then_forward_receiver_and_captured_values() {
    let facts = admitted();
    for (name, descriptor, captures, instance) in [
        (
            "staticClosure",
            "(I)Ljava/lang/Runnable;",
            vec![ValueId(1)],
            false,
        ),
        (
            "receiverClosure",
            "(I)Ljava/lang/Runnable;",
            vec![ValueId(0), ValueId(1)],
            true,
        ),
        (
            "boundClosure",
            "()Ljava/lang/Runnable;",
            vec![ValueId(0)],
            true,
        ),
    ] {
        let factory = body(&facts, name, descriptor);
        let ops = &facts.operations[factory.operations.range()];
        let bindings: Vec<_> = ops
            .iter()
            .filter(|op| op.opcode == Opcode::BindCallback)
            .collect();
        assert_eq!(bindings.len(), 1, "{name}");
        let binding = bindings[0];
        assert!(binding.a.is_none());
        assert_eq!(&facts.operands[binding.arguments.range()], captures);
        let recipe = facts
            .bodies
            .iter()
            .find(|body| body.symbol == binding.target)
            .unwrap();
        assert_eq!(
            recipe.flags & (BODY_BINARY_RECIPE | BODY_DEFERRED),
            BODY_BINARY_RECIPE | BODY_DEFERRED
        );
        assert_eq!(recipe.parameters.len as usize, captures.len());
        let forwarded: Vec<_> = facts.operations[recipe.operations.range()]
            .iter()
            .filter(|op| matches!(op.opcode, Opcode::Call | Opcode::VirtualCall))
            .collect();
        assert_eq!(forwarded.len(), 1);
        let call = forwarded[0];
        assert_eq!(
            call.opcode,
            if instance {
                Opcode::VirtualCall
            } else {
                Opcode::Call
            }
        );
        assert_eq!(call.a, if instance { ValueId(1) } else { ValueId::NONE });
        let expected_args: Vec<_> = ((1 + usize::from(instance))..=captures.len())
            .map(|index| ValueId(index as u32))
            .collect();
        assert_eq!(&facts.operands[call.arguments.range()], expected_args);
        assert!(
            !ops.iter()
                .any(|op| matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
                    && op.target == call.target),
            "the factory cannot execute the native implementation"
        );
        let implementation = facts
            .bodies
            .iter()
            .find(|body| body.symbol == call.target)
            .unwrap();
        assert_ne!(implementation.flags & BODY_BINARY_RECIPE, 0);
    }
}

#[test]
fn native_invocation_roots_reach_their_effects_and_factory_roots_do_not() {
    let facts = admitted();
    let graph = selector_graph_build::build(&facts, &Default::default()).unwrap();
    let receiver = facts.find_symbol(&native_name("<type>", "")).unwrap();
    let node = |name: &str, descriptor: &str| {
        graph
            .node_for_symbol(facts.find_symbol(&native_name(name, descriptor)).unwrap())
            .unwrap()
    };
    let root_names = [
        ("runStatic", "()V"),
        ("runReceiver", "()V"),
        ("runBound", "()V"),
        ("staticClosure", "(I)Ljava/lang/Runnable;"),
        ("receiverClosure", "(I)Ljava/lang/Runnable;"),
        ("boundClosure", "()Ljava/lang/Runnable;"),
    ];
    let roots: Vec<_> = root_names
        .iter()
        .map(|&(name, descriptor)| selector_solve::ExecutionRoot {
            node: node(name, descriptor),
            receiver,
        })
        .collect();
    let options = selector_solve::SolveOptions {
        workers: 2,
        memory_budget_bytes: 64 * 1024 * 1024,
        max_contexts: 10_000,
        max_steps: 1_000_000,
        execution_roots: Some(roots.into()),
        ..Default::default()
    };
    for (implementation, descriptor, expected_root) in [
        ("staticEffect", "(I)V", "runStatic"),
        ("receiverEffect", "(I)V", "runReceiver"),
        ("next", "()V", "runBound"),
    ] {
        let result = selector_solve::analyze(
            &facts,
            &graph,
            &[node(implementation, descriptor)],
            &options,
        )
        .unwrap();
        assert_ne!(result.completion, Completion::ResourceLimited);
        assert!(
            result.contains(node(expected_root, "()V")),
            "{expected_root} must reach {implementation}"
        );
        for &(factory, factory_descriptor) in &root_names[3..] {
            assert!(
                !result.contains(node(factory, factory_descriptor)),
                "creating {factory}'s callback cannot execute {implementation}"
            );
        }
    }
}

#[test]
fn distinct_static_target_initializes_only_when_its_reference_is_invoked() {
    let facts = admitted();
    let factory = body(&facts, "separateStaticClosure", "()Ljava/lang/Runnable;");
    let binding = facts.operations[factory.operations.range()]
        .iter()
        .find(|op| op.opcode == Opcode::BindCallback)
        .unwrap();
    let recipe = facts
        .bodies
        .iter()
        .find(|body| body.symbol == binding.target)
        .unwrap();
    let target = "lambdacase/Probe$DeferredTarget";
    let phase = facts
        .find_symbol(&native_name_for(target, "<class-init>", "()V"))
        .unwrap();
    let initializer = facts
        .find_symbol(&native_name_for(target, "<clinit>", "()V"))
        .unwrap();
    assert!(
        !facts.operations[factory.operations.range()]
            .iter()
            .any(|op| op.opcode == Opcode::Initialize && op.target == phase)
    );
    assert!(
        facts.operations[recipe.operations.range()]
            .iter()
            .any(|op| op.opcode == Opcode::Initialize && op.target == phase)
    );
    let graph = selector_graph_build::build(&facts, &Default::default()).unwrap();
    let factory_node = graph.node_for_symbol(factory.symbol).unwrap();
    let invoked_node = graph
        .node_for_symbol(body(&facts, "runSeparate", "()V").symbol)
        .unwrap();
    let receiver = facts.find_symbol(&native_name("<type>", "")).unwrap();
    let options = selector_solve::SolveOptions {
        workers: 2,
        memory_budget_bytes: 64 * 1024 * 1024,
        max_contexts: 10_000,
        max_steps: 1_000_000,
        execution_roots: Some(
            [
                selector_solve::ExecutionRoot {
                    node: factory_node,
                    receiver,
                },
                selector_solve::ExecutionRoot {
                    node: invoked_node,
                    receiver,
                },
            ]
            .into(),
        ),
        ..Default::default()
    };
    for seed in [phase, initializer] {
        let result = selector_solve::analyze(
            &facts,
            &graph,
            &[graph.node_for_symbol(seed).unwrap()],
            &options,
        )
        .unwrap();
        assert_ne!(result.completion, Completion::ResourceLimited);
        assert!(
            result.contains(invoked_node),
            "invocation must activate the target's native class initializer"
        );
        assert!(
            !result.contains(factory_node),
            "method-reference creation cannot initialize the target class"
        );
    }
}

#[test]
fn unsupported_unbound_consumer_keeps_a_guard_without_eager_target_execution() {
    let facts = admitted();
    let factory = body(&facts, "unbound", "()Ljava/util/function/Consumer;");
    let operations = &facts.operations[factory.operations.range()];
    assert!(operations.iter().any(|op| op.opcode == Opcode::Unknown));
    assert!(
        !operations
            .iter()
            .any(|op| op.opcode == Opcode::BindCallback)
    );
    let graph = selector_graph_build::build(&facts, &Default::default()).unwrap();
    let root = graph.node_for_symbol(factory.symbol).unwrap();
    let target = graph
        .node_for_symbol(facts.find_symbol(&native_name("next", "()V")).unwrap())
        .unwrap();
    let receiver = facts.find_symbol(&native_name("<type>", "")).unwrap();
    let result = selector_solve::analyze(
        &facts,
        &graph,
        &[target],
        &selector_solve::SolveOptions {
            workers: 2,
            memory_budget_bytes: 64 * 1024 * 1024,
            max_contexts: 10_000,
            max_steps: 1_000_000,
            execution_roots: Some(
                [selector_solve::ExecutionRoot {
                    node: root,
                    receiver,
                }]
                .into(),
            ),
            ..Default::default()
        },
    )
    .unwrap();
    assert_ne!(result.completion, Completion::ResourceLimited);
    assert!(
        !result.contains(root),
        "the unknown SAM cannot fabricate an eager target call"
    );
    assert!(
        result.guarded_roots.contains(&root),
        "unsupported unbound/SAM adaptation remains guarded"
    );
}

#[test]
fn unknown_bootstrap_preserves_a_later_actual_field_store() {
    let facts = admitted();
    let method = body(&facts, "unsupportedThenStore", "(I)V");
    let operations = &facts.operations[method.operations.range()];
    let unknown = operations
        .iter()
        .position(|op| op.opcode == Opcode::Unknown)
        .expect("unsupported StringConcatFactory effects remain explicit");
    let stored = facts.find_symbol(&native_name("stored", "I")).unwrap();
    let store = operations
        .iter()
        .position(|op| op.opcode == Opcode::StoreField && op.target == stored)
        .expect("known invokedynamic descriptor must permit the later real field store");
    assert!(unknown < store);
    let graph = selector_graph_build::build(&facts, &Default::default()).unwrap();
    let root = graph.node_for_symbol(method.symbol).unwrap();
    let receiver = facts.find_symbol(&native_name("<type>", "")).unwrap();
    let result = selector_solve::analyze(
        &facts,
        &graph,
        &[graph.node_for_symbol(stored).unwrap()],
        &selector_solve::SolveOptions {
            workers: 2,
            memory_budget_bytes: 64 * 1024 * 1024,
            max_contexts: 10_000,
            max_steps: 1_000_000,
            execution_roots: Some(
                [selector_solve::ExecutionRoot {
                    node: root,
                    receiver,
                }]
                .into(),
            ),
            ..Default::default()
        },
    )
    .unwrap();
    assert_ne!(result.completion, Completion::ResourceLimited);
    assert!(
        result.guarded_roots.contains(&root),
        "the retained store does not erase unknown bootstrap effects"
    );
}
