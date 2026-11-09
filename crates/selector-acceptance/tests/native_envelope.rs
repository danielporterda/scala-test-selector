//! Frozen javac effects, including branches which the precise interpreter stops
//! before. Callable roots here are engine fixtures, not a CI suite catalogue.
use selector_facts::{FactBuilder, FactSnapshot, SuiteRecord};
use selector_graph_build::binary_inputs::{
    BinaryInputOptions, NativeAdmissionLimits, augment_binary_facts,
    augment_binary_facts_with_limits, load_binary_manifest, load_binary_manifest_with_options,
};
use selector_models::binary::{self, Limits};
use selector_types::*;
use std::path::PathBuf;

const OWNER: &str = "envelopecase/Probe";
const SCALAR: &str = "envelopecase/Probe$Scalar";
fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/native-envelope")
}
fn identity(name: &str, descriptor: &str) -> String {
    owned_identity(OWNER, name, descriptor)
}
fn owned_identity(owner: &str, name: &str, descriptor: &str) -> String {
    format!(
        "@jvm/{}:{owner}{}:{name}{}:{descriptor}",
        owner.len(),
        name.len(),
        descriptor.len()
    )
}
fn admission_fixture(shadow: bool) -> (FactSnapshot, serde_json::Value) {
    let mut builder = FactBuilder::new();
    builder.facts.revision = builder.intern("native-envelope-fixture-v1").unwrap();
    let context = builder.intern("fixture:native-envelope").unwrap();
    let class = builder
        .ensure_symbol(&identity("<type>", ""), FileId::NONE)
        .unwrap();
    builder.facts.symbols[class.index()].kind = 13;
    builder.facts.symbols[class.index()].context = context;
    // Explicit no-argument native callable inventory, not compiler/CI discovery.
    // A separate no-field component avoids Probe's static counter heap frontier.
    let scalar = builder
        .ensure_symbol(&owned_identity(SCALAR, "<type>", ""), FileId::NONE)
        .unwrap();
    builder.facts.symbols[scalar.index()].kind = 13;
    builder.facts.symbols[scalar.index()].context = context;
    for (owner, class, name) in [
        (OWNER, class, "branchEntry"),
        (SCALAR, scalar, "disjointEntry"),
    ] {
        let symbol = builder
            .ensure_symbol(&owned_identity(owner, name, "()I"), FileId::NONE)
            .unwrap();
        builder.facts.symbols[symbol.index()].kind = 3;
        builder.facts.symbols[symbol.index()].owner = class;
        builder.facts.symbols[symbol.index()].context = context;
        builder.facts.suites.push(SuiteRecord {
            name: builder.facts.symbols[symbol.index()].name,
            symbol,
            file: FileId::NONE,
            flags: 0,
        });
    }
    let facts = builder.finish().unwrap();
    let receipt: serde_json::Value =
        serde_json::from_slice(&std::fs::read(fixture().join("manifest.json")).unwrap()).unwrap();
    let mut entries = Vec::new();
    for name in if shadow {
        vec!["shadow.jar", "bytecode.jar"]
    } else {
        vec!["bytecode.jar"]
    } {
        let row = receipt["files"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["path"] == name)
            .unwrap();
        entries.push(
            serde_json::json!({"path":fixture().join(name),"sha256":row["sha256"],"kind":"jar"}),
        );
    }
    let mut methods: Vec<_> = [
        ("changed", "()I"),
        ("branch", "(Z)I"),
        ("sparseSwitch", "(I)I"),
        ("denseSwitch", "(I)I"),
        ("caught", "(Z)I"),
        ("disjointScalar", "(I)I"),
        ("disjointEntry", "()I"),
        ("branchEntry", "()I"),
        ("escape", "(Ljava/lang/Runnable;)V"),
        ("invokeEscaped", "()V"),
        ("reflection", "(Ljava/lang/String;)Ljava/lang/Class;"),
        ("array", "([I)I"),
        ("monitor", "(Ljava/lang/Object;)V"),
        ("missing", "()V"),
        ("invokesMissing", "()V"),
    ]
    .into_iter()
    .map(|(name, descriptor)| {
        let mut row = serde_json::json!({"context":"fixture:native-envelope",
            "jvm_owner":OWNER,"jvm_name":name,"descriptor":descriptor});
        if name == "branchEntry" {
            row["compiler_symbol"] = identity(name, descriptor).into();
        }
        row
    })
    .collect();
    methods.push(serde_json::json!({"context":"fixture:native-envelope",
        "compiler_symbol":owned_identity(SCALAR,"disjointEntry","()I"),
        "jvm_owner":SCALAR,"jvm_name":"disjointEntry","descriptor":"()I"}));
    methods.push(serde_json::json!({"context":"fixture:native-envelope",
        "jvm_owner":SCALAR,"jvm_name":"disjointScalar","descriptor":"(I)I"}));
    let manifest = serde_json::json!({"version":1,"revision":facts.text(facts.revision),"java_feature":21,
        "contexts":[{"id":"fixture:native-envelope","entries":entries}],
        "types":[{"context":"fixture:native-envelope","compiler_symbol":identity("<type>",""),"jvm_owner":OWNER},
            {"context":"fixture:native-envelope","compiler_symbol":owned_identity(SCALAR,"<type>",""),"jvm_owner":SCALAR}],
        "methods":methods});
    (facts, manifest)
}
fn admitted(shadow: bool) -> FactSnapshot {
    let (mut facts, manifest) = admission_fixture(shadow);
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("binary.json");
    std::fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    let mut inputs = load_binary_manifest(&path, &facts).unwrap();
    augment_binary_facts(&mut facts, &mut inputs).unwrap();
    if !shadow {
        let metrics = inputs.envelope_metrics();
        assert!(metrics.fallback_methods > 0);
        assert!(metrics.complete_local_envelopes > 0);
        assert!(metrics.open_envelopes > 0);
    }
    facts
}

#[test]
fn actual_jvm_paths_and_callback_escape_observations_are_frozen() {
    assert_eq!(
        std::fs::read_to_string(fixture().join("execution.log"))
            .unwrap()
            .lines()
            .collect::<Vec<_>>(),
        [
            "branch-false:0:0",
            "branch-true:41:1",
            "sparse-hit:41:1",
            "sparse-miss:0:0",
            "dense-hit:41:1",
            "dense-miss:0:0",
            "catch-hit:41:1",
            "catch-miss:0:0",
            "scalar:4:0",
            "disjoint-entry:29:0",
            "branch-entry:41:1",
            "scalar-component-entry:29:0",
            "escape-before:0",
            "escape-after:100",
            "reflection:java.lang.String",
            "native-missing:UnsatisfiedLinkError",
            "array:9",
            "monitor:1"
        ]
    );
    assert_eq!(
        std::fs::read_to_string(fixture().join("shadow-execution.log")).unwrap(),
        "shadow:0\n"
    );
}

#[test]
fn complete_effect_envelopes_keep_hidden_calls_and_closed_scalar_data() {
    let class = binary::parse_class(
        include_bytes!("../../../fixtures/native-envelope/classes/envelopecase/Probe.class"),
        Limits::default(),
    )
    .unwrap();
    for (name, descriptor) in [
        ("branch", "(Z)I"),
        ("sparseSwitch", "(I)I"),
        ("denseSwitch", "(I)I"),
        ("caught", "(Z)I"),
    ] {
        let method = class.method(name, Some(descriptor)).unwrap();
        let summary = binary::summarize_with_envelope(&class, method, Limits::default());
        assert!(summary.complete(), "{name}: {:?}", summary.unknown);
        assert!(
            summary.calls.iter().any(|call| call.member.owner == OWNER
                && call.member.name == "changed"
                && call.member.descriptor == "()I"),
            "hidden {name} effect"
        );
    }
    let method = class.method("disjointScalar", Some("(I)I")).unwrap();
    let scalar = binary::summarize_with_envelope(&class, method, Limits::default());
    assert!(
        scalar.complete(),
        "opaque scalar data must not create an execution hole"
    );
    assert!(scalar.calls.is_empty() && scalar.field_writes.is_empty());
    assert!(
        scalar
            .values
            .iter()
            .any(|value| matches!(value, binary::Value::UnknownData))
    );
}

#[test]
fn public_native_pipeline_retains_hidden_impacts_and_disjoint_scalar_certainty() {
    let facts = admitted(false);
    let graph = selector_graph_build::build(&facts, &Default::default()).unwrap();
    let node = |name: &str, descriptor: &str| {
        graph
            .node_for_symbol(facts.find_symbol(&identity(name, descriptor)).unwrap())
            .unwrap()
    };
    let receiver = facts.find_symbol(&identity("<type>", "")).unwrap();
    let roots: Vec<_> = [
        ("branch", "(Z)I"),
        ("sparseSwitch", "(I)I"),
        ("denseSwitch", "(I)I"),
        ("caught", "(Z)I"),
        ("disjointScalar", "(I)I"),
    ]
    .into_iter()
    .map(|(name, descriptor)| selector_solve::ExecutionRoot {
        node: node(name, descriptor),
        receiver,
    })
    .collect();
    let result = selector_solve::analyze(
        &facts,
        &graph,
        &[node("changed", "()I")],
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
    for (name, descriptor) in [
        ("branch", "(Z)I"),
        ("sparseSwitch", "(I)I"),
        ("denseSwitch", "(I)I"),
        ("caught", "(Z)I"),
    ] {
        assert!(
            result.contains(node(name, descriptor)),
            "hidden {name} call needs an impact proof"
        );
    }
    let scalar = node("disjointScalar", "(I)I");
    assert!(!result.contains(scalar));
    assert!(
        !result.guarded_roots.contains(&scalar),
        "closed scalar data alone cannot guard an unrelated callable"
    );
}

#[test]
fn open_channels_and_static_callback_escape_remain_explicit() {
    let class = binary::parse_class(
        include_bytes!("../../../fixtures/native-envelope/classes/envelopecase/Probe.class"),
        Limits::default(),
    )
    .unwrap();
    for (name, descriptor) in [
        ("reflection", "(Ljava/lang/String;)Ljava/lang/Class;"),
        ("array", "([I)I"),
        ("monitor", "(Ljava/lang/Object;)V"),
        ("missing", "()V"),
    ] {
        let summary = binary::summarize_with_envelope(
            &class,
            class.method(name, Some(descriptor)).unwrap(),
            Limits::default(),
        );
        assert!(
            !summary.complete(),
            "{name} remains an explicit unsupported/open effect channel"
        );
    }
    let escaped = binary::summarize_with_envelope(
        &class,
        class
            .method("escape", Some("(Ljava/lang/Runnable;)V"))
            .unwrap(),
        Limits::default(),
    );
    assert!(
        escaped
            .field_writes
            .iter()
            .any(|write| write.member.name == "escaped" && write.receiver.is_none())
    );
    let invoked = binary::summarize_with_envelope(
        &class,
        class.method("invokeEscaped", Some("()V")).unwrap(),
        Limits::default(),
    );
    assert!(
        invoked
            .calls
            .iter()
            .any(|call| call.member.owner == "java/lang/Runnable" && call.member.name == "run")
    );
}

#[test]
fn genuine_earlier_shadow_and_truncated_classes_cannot_borrow_later_effects() {
    let bytes =
        include_bytes!("../../../fixtures/native-envelope/classes/envelopecase/Probe.class");
    assert!(binary::parse_class(&bytes[..bytes.len() / 2], Limits::default()).is_err());
    let facts = admitted(true);
    let branch = facts.find_symbol(&identity("branch", "(Z)I")).unwrap();
    let changed = facts.find_symbol(&identity("changed", "()I")).unwrap();
    let body = facts
        .bodies
        .iter()
        .find(|body| body.symbol == branch)
        .unwrap();
    assert!(
        !facts.operations[body.operations.range()]
            .iter()
            .any(|op| matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
                && op.target == changed)
    );
    let receipt: serde_json::Value =
        serde_json::from_slice(&std::fs::read(fixture().join("manifest.json")).unwrap()).unwrap();
    let shadow = receipt["files"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["path"] == "shadow-classes/envelopecase/Probe.class")
        .unwrap();
    assert_eq!(
        facts.files[body.file.index()].source_hash,
        ContentHash::from_hex(shadow["sha256"].as_str().unwrap()).unwrap()
    );
}

#[test]
fn public_planner_certifies_closed_scalar_root_and_retains_hidden_changed_call() {
    let facts = admitted(false);
    // These are explicit native callable surrogates, so framework suite-model
    // discovery is outside this gate. Native method effects are fully admitted.
    let graph = selector_graph_build::build(
        &facts,
        &selector_graph_build::BuildOptions {
            include_models: false,
            ..Default::default()
        },
    )
    .unwrap();
    let node = |name: &str| {
        graph
            .node_for_symbol(facts.find_symbol(&identity(name, "()I")).unwrap())
            .unwrap()
    };
    let plan = selector_plan::plan(
        &facts,
        &graph,
        selector_plan::PlanSeeds {
            execution: &[node("changed")],
            declarations: &[],
            unscoped: false,
        },
    )
    .unwrap();
    let scalar = graph
        .node_for_symbol(
            facts
                .find_symbol(&owned_identity(SCALAR, "disjointEntry", "()I"))
                .unwrap(),
        )
        .unwrap();
    assert_eq!(
        plan.roots.len() + plan.excluded_roots().len(),
        2,
        "explicit native callable surrogates only"
    );
    assert!(
        plan.certifies_unaffected(scalar),
        "closed scalar data has no changed-call channel: {:?}",
        plan.frontiers()
    );
    assert!(
        !plan.certifies_unaffected(node("branchEntry")),
        "hidden changed call must remain a candidate"
    );
}

fn bounded_admission(workers: usize, limits: NativeAdmissionLimits) -> FactSnapshot {
    let (mut facts, mut manifest) = admission_fixture(false);
    // Keep every explicit root fair; this real helper is discovered only from
    // Probe.disjointEntry, so a zero remaining method allowance defers it.
    manifest["methods"]
        .as_array_mut()
        .unwrap()
        .retain(|method| !(method["jvm_owner"] == OWNER && method["jvm_name"] == "disjointScalar"));
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("binary.json");
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
    augment_binary_facts_with_limits(&mut facts, &mut inputs, limits).unwrap();
    facts
}

#[test]
fn bounded_native_frontiers_keep_known_impacts_and_independent_scalar_certificate() {
    let limits = NativeAdmissionLimits {
        methods: 16,
        ..Default::default()
    };
    let first = bounded_admission(1, limits);
    let other = bounded_admission(4, limits);
    assert_eq!(
        first.identity, other.identity,
        "bounded admission deterministic across workers"
    );
    let saved = tempfile::tempdir().unwrap();
    let a = saved.path().join("one.bin");
    let b = saved.path().join("four.bin");
    selector_facts::codec::write(&a, &first).unwrap();
    selector_facts::codec::write(&b, &other).unwrap();
    assert_eq!(std::fs::read(a).unwrap(), std::fs::read(b).unwrap());
    let facts = first;
    let deferred: Vec<_> = facts
        .issues
        .iter()
        .filter(|issue| {
            !issue.detail.is_none() && facts.text(issue.detail).contains("budget deferred")
        })
        .collect();
    assert!(
        !deferred.is_empty(),
        "genuine low budget must encounter an explicit frontier"
    );
    assert!(
        deferred
            .iter()
            .all(|issue| issue.kind == IssueKind::UnknownExecution && !issue.symbol.is_none())
    );
    let graph = selector_graph_build::build(
        &facts,
        &selector_graph_build::BuildOptions {
            workers: 4,
            include_models: false,
        },
    )
    .unwrap();
    let node = |owner: &str, name: &str, descriptor: &str| {
        graph
            .node_for_symbol(
                facts
                    .find_symbol(&owned_identity(owner, name, descriptor))
                    .unwrap(),
            )
            .unwrap()
    };
    let branch = node(OWNER, "branchEntry", "()I");
    let scalar = node(SCALAR, "disjointEntry", "()I");
    let changed = node(OWNER, "changed", "()I");
    let plan = selector_plan::plan(
        &facts,
        &graph,
        selector_plan::PlanSeeds {
            execution: &[changed],
            declarations: &[],
            unscoped: false,
        },
    )
    .unwrap();
    assert!(
        plan.certifies_unaffected(scalar),
        "separate closed scalar component survives optional frontiers: {:?}",
        plan.frontiers()
    );
    assert!(!plan.certifies_unaffected(branch));
    let roots = vec![
        selector_solve::ExecutionRoot {
            node: branch,
            receiver: facts.find_symbol(&identity("<type>", "")).unwrap(),
        },
        selector_solve::ExecutionRoot {
            node: scalar,
            receiver: facts
                .find_symbol(&owned_identity(SCALAR, "<type>", ""))
                .unwrap(),
        },
        selector_solve::ExecutionRoot {
            node: node(OWNER, "disjointEntry", "()I"),
            receiver: facts.find_symbol(&identity("<type>", "")).unwrap(),
        },
        selector_solve::ExecutionRoot {
            node: node(OWNER, "caught", "(Z)I"),
            receiver: facts.find_symbol(&identity("<type>", "")).unwrap(),
        },
    ];
    let result = selector_solve::analyze(
        &facts,
        &graph,
        &[changed],
        &selector_solve::SolveOptions {
            workers: 4,
            memory_budget_bytes: 64 * 1024 * 1024,
            max_contexts: 10_000,
            max_steps: 1_000_000,
            execution_roots: Some(roots.into()),
            ..Default::default()
        },
    )
    .unwrap();
    assert_ne!(result.completion, Completion::ResourceLimited);
    assert!(result.contains(branch));
    assert!(
        result.contains(node(OWNER, "caught", "(Z)I")),
        "known call after guarded optional constructor must remain visible"
    );
    assert!(
        result
            .guarded_roots
            .contains(&node(OWNER, "caught", "(Z)I")),
        "native budget is an open execution frontier"
    );
    assert!(
        result
            .guarded_roots
            .contains(&node(OWNER, "disjointEntry", "()I")),
        "known but deferred helper body must remain an explicit guarded frontier"
    );
    assert!(!result.contains(scalar) && !result.guarded_roots.contains(&scalar));
}

#[test]
fn bounded_admission_does_not_convert_mandatory_provenance_failures_to_absence() {
    let (facts, mut manifest) = admission_fixture(false);
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("binary.json");
    manifest["contexts"][0]["entries"][0]["sha256"] = "00".repeat(32).into();
    std::fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    assert!(
        load_binary_manifest(&path, &facts).is_err(),
        "wrong mandatory JAR hash remains fatal before any optional work"
    );
    manifest["contexts"][0]["entries"][0]
        .as_object_mut()
        .unwrap()
        .remove("sha256");
    std::fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    assert!(
        load_binary_manifest(&path, &facts).is_err(),
        "missing mandatory provenance cannot become a class-absence proof"
    );
}

#[test]
fn native_policy_identity_binds_limits_even_when_projected_tables_match() {
    let one = bounded_admission(
        1,
        NativeAdmissionLimits {
            methods: 17,
            ..Default::default()
        },
    );
    let two = bounded_admission(
        1,
        NativeAdmissionLimits {
            methods: 18,
            ..Default::default()
        },
    );
    let directory = tempfile::tempdir().unwrap();
    let a = directory.path().join("one.bin");
    let b = directory.path().join("two.bin");
    selector_facts::codec::write(&a, &one).unwrap();
    selector_facts::codec::write(&b, &two).unwrap();
    assert_eq!(
        std::fs::read(a).unwrap(),
        std::fs::read(b).unwrap(),
        "same explicit map and projected fact tables under both nonbinding caps"
    );
    assert_ne!(
        one.identity, two.identity,
        "actual admission limits bind the enriched semantic stage identity"
    );
}
