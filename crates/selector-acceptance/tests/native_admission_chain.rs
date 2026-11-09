//! Genuine javac dependencies with a NORMALIZED demand inventory. Native
//! callable suite records exercise engine planning, not compiler/CI discovery.
use selector_facts::{FactBuilder, FactSnapshot, FileRecord, IssueRecord};
use selector_graph::ProgramGraph;
use selector_graph_build::binary_inputs::{
    BinaryInputOptions, NativeAdmissionLimits, augment_binary_facts_with_limits,
    load_binary_manifest_with_options,
};
use selector_types::*;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::path::PathBuf;

const CONTEXT: &str = "normalized:native-admission-pressure";
const CONTRACT: &str = "admissioncase/Contract";
const GETTER: &str = "admissioncase/Getter";
const BOX: &str = "admissioncase/Box";
const EFFECTS: &str = "admissioncase/Effects";
const CLOSED: &str = "admissioncase/Closed";
const FACTORY: &str = "admissioncase/Factory";
const BASE: &str = "admissioncase/Base";
const CHILD: &str = "admissioncase/Child";
const VIRTUAL: &str = "admissioncase/VirtualContract";
const BOX_DESC: &str = "()Ladmissioncase/Box;";

#[derive(Clone, Copy)]
enum Profile {
    Getter,
    ChildOverride,
}
#[derive(Clone, Copy)]
enum Control {
    None,
    Shadow,
    SourceOverlay,
    ContextConflict,
    Unavailable,
}
struct Admitted {
    facts: FactSnapshot,
    derived_methods: usize,
    mandatory_methods: usize,
    retries: usize,
}
fn directory() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/native-admission-chain")
}
fn fixture_json() -> Value {
    serde_json::from_slice(&std::fs::read(directory().join("manifest.json")).unwrap()).unwrap()
}
fn native(owner: &str, name: &str, descriptor: &str) -> String {
    format!(
        "@jvm/{}:{owner}{}:{name}{}:{descriptor}",
        owner.len(),
        name.len(),
        descriptor.len()
    )
}
fn class(facts: &FactSnapshot, owner: &str) -> SymbolId {
    facts.find_symbol(&format!("{owner}#")).unwrap()
}
fn method(facts: &FactSnapshot, owner: &str, name: &str, descriptor: &str) -> Option<SymbolId> {
    facts.find_symbol(&native(owner, name, descriptor))
}
fn body<'a>(
    facts: &'a FactSnapshot,
    owner: &str,
    name: &str,
    descriptor: &str,
) -> Option<&'a selector_facts::BodyRecord> {
    let symbol = method(facts, owner, name, descriptor)?;
    facts.bodies.iter().find(|body| body.symbol == symbol)
}
fn operators<'a>(
    facts: &'a FactSnapshot,
    owner: &str,
    name: &str,
    descriptor: &str,
) -> &'a [selector_facts::OperationRecord] {
    let body = body(facts, owner, name, descriptor).expect("actual admitted method body");
    &facts.operations[body.operations.range()]
}
fn pinned_jar(name: &str) -> Value {
    let receipt = fixture_json();
    let row = receipt["files"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["path"] == name)
        .unwrap();
    json!({"path":directory().join(name),"sha256":row["sha256"],"kind":"jar"})
}
fn object_jar() -> Value {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/binary-resolution");
    let receipt: Value =
        serde_json::from_slice(&std::fs::read(path.join("manifest.json")).unwrap()).unwrap();
    let row = receipt["outputs"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["path"] == "resolution.jar")
        .unwrap();
    json!({"path":path.join("resolution.jar"),"sha256":row["sha256"],"kind":"jar"})
}
fn admitted(
    profile: Profile,
    limit: usize,
    workers: usize,
    control: Control,
) -> Result<Admitted, Error> {
    let mut builder = FactBuilder::new();
    builder.facts.revision = builder.intern("genuine-native-admission-chain-v1")?;
    let context = builder.intern(CONTEXT)?;
    for owner in [
        CONTRACT, GETTER, BOX, EFFECTS, CLOSED, FACTORY, BASE, CHILD, VIRTUAL,
    ] {
        let symbol = builder.ensure_global_symbol(&format!("{owner}#"), context)?;
        builder.facts.symbols[symbol.index()].kind = if matches!(owner, CONTRACT | VIRTUAL) {
            14
        } else {
            13
        };
    }
    let mut requests = vec![
        (CLOSED, "scalar".to_owned(), "()I"),
        (EFFECTS, "changed".to_owned(), "()I"),
    ];
    match profile {
        Profile::Getter => {
            requests.push((FACTORY, "entry".into(), BOX_DESC));
            requests.push((CONTRACT, "aGet".into(), BOX_DESC));
            // Four known unused contracts are enough to exhaust a bulk batch,
            // while their scoped rows fit the unchanged diagnostic bound.
            for index in 0..4 {
                requests.push((CONTRACT, format!("unused{index:02}"), "()I"));
            }
        }
        Profile::ChildOverride => requests.extend([
            (FACTORY, "childEntry".into(), "()I"),
            (VIRTUAL, "m".into(), "()I"),
            (BASE, "m".into(), "()I"),
        ]),
    }
    let mandatory_methods = requests.len();
    let mut methods = Vec::new();
    for (owner, name, descriptor) in requests {
        // Abstract contracts are demanded native declarations, not invented
        // compiler aliases: ordinary admission supplies their actual file/hash.
        let spelling = if matches!(owner, CONTRACT | VIRTUAL) {
            None
        } else {
            let spelling = native(owner, &name, descriptor);
            let symbol = builder.ensure_global_symbol(&spelling, context)?;
            let owner = builder
                .lookup_global_symbol(&format!("{owner}#"), context)
                .unwrap();
            builder.facts.symbols[symbol.index()].kind = 3;
            builder.facts.symbols[symbol.index()].owner = owner;
            builder.facts.symbols[symbol.index()].flags = SYMBOL_NATIVE_BINARY;
            Some(spelling)
        };
        methods.push(json!({"context":CONTEXT,"compiler_symbol":spelling,
            "jvm_owner":owner,"jvm_name":name,"descriptor":descriptor}));
    }
    if matches!(control, Control::SourceOverlay) {
        // Normalized source-owned-name precedence control. This is not a
        // fabricated SemanticDB capture or a native body masquerading as source.
        let source_text =
            std::fs::read_to_string(directory().join("src/admissioncase/Fixture.java"))?;
        let source = builder.intern(&source_text)?;
        let path = builder.intern("normalized/source-overlay/Fixture.java")?;
        let file = FileId::checked(builder.facts.files.len())?;
        builder.facts.files.push(FileRecord {
            path,
            source,
            revision: builder.facts.revision,
            context,
            source_hash: ContentHash(Sha256::digest(source_text.as_bytes()).into()),
            flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
        });
        let owner = builder
            .lookup_global_symbol(&format!("{GETTER}#"), context)
            .unwrap();
        builder.facts.symbols[owner.index()].file = file;
        builder.facts.symbols[owner.index()].flags = SYMBOL_DEFINED;
        let own = builder.ensure_global_symbol(&format!("{GETTER}#aGet()."), context)?;
        let row = &mut builder.facts.symbols[own.index()];
        row.file = file;
        row.owner = owner;
        row.kind = 3;
        row.flags = SYMBOL_DEFINED;
    }
    if matches!(control, Control::ContextConflict) {
        let symbol = builder
            .lookup_global_symbol(&format!("{GETTER}#"), context)
            .unwrap();
        builder.facts.issues.push(IssueRecord {
            kind: IssueKind::ContextConflict,
            symbol,
            file: FileId::NONE,
            detail: StrId::NONE,
        });
    }
    // Explicit callable surrogates, used only for planner inventory coverage.
    for (owner, name, descriptor) in [
        (
            FACTORY,
            if matches!(profile, Profile::Getter) {
                "entry"
            } else {
                "childEntry"
            },
            if matches!(profile, Profile::Getter) {
                BOX_DESC
            } else {
                "()I"
            },
        ),
        (CLOSED, "scalar", "()I"),
    ] {
        let symbol = builder
            .lookup_global_symbol(&native(owner, name, descriptor), context)
            .unwrap();
        builder.facts.suites.push(selector_facts::SuiteRecord {
            name: builder.facts.symbols[symbol.index()].name,
            symbol,
            file: FileId::NONE,
            flags: 0,
        });
    }
    let mut facts = builder.finish()?;
    let mut entries = Vec::new();
    if matches!(control, Control::Shadow) {
        entries.push(pinned_jar("shadow.jar"));
    }
    if matches!(control, Control::Unavailable) {
        entries.push(json!({"path":directory().join("unavailable-declared-prefix.jar"),"kind":"unavailable"}));
    }
    entries.extend([pinned_jar("bytecode.jar"), object_jar()]);
    let types: Vec<_> = [
        CONTRACT, GETTER, BOX, EFFECTS, CLOSED, FACTORY, BASE, CHILD, VIRTUAL,
    ]
    .into_iter()
    .map(|owner| json!({"context":CONTEXT,"compiler_symbol":format!("{owner}#"),"jvm_owner":owner}))
    .collect();
    let manifest = json!({"version":1,"revision":facts.text(facts.revision),"java_feature":21,
        "contexts":[{"id":CONTEXT,"entries":entries}],"types":types,"methods":methods});
    let temporary = tempfile::tempdir()?;
    let path = temporary.path().join("binary.json");
    std::fs::write(&path, serde_json::to_vec(&manifest).unwrap())?;
    let mut inputs = load_binary_manifest_with_options(
        &path,
        &facts,
        &BinaryInputOptions {
            workers,
            ..Default::default()
        },
    )?;
    augment_binary_facts_with_limits(
        &mut facts,
        &mut inputs,
        NativeAdmissionLimits {
            methods: limit,
            ..Default::default()
        },
    )?;
    let metrics = inputs.context_metrics().next().unwrap();
    Ok(Admitted {
        facts,
        derived_methods: metrics.derived_methods,
        mandatory_methods,
        retries: metrics.retried_callers,
    })
}
fn graph(facts: &FactSnapshot, workers: usize) -> ProgramGraph {
    selector_graph_build::build(
        facts,
        &selector_graph_build::BuildOptions {
            workers,
            include_models: false,
        },
    )
    .unwrap()
}
fn analyze(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    profile: Profile,
    workers: usize,
) -> selector_result::AnalysisResult {
    let root = method(
        facts,
        FACTORY,
        if matches!(profile, Profile::Getter) {
            "entry"
        } else {
            "childEntry"
        },
        if matches!(profile, Profile::Getter) {
            BOX_DESC
        } else {
            "()I"
        },
    )
    .unwrap();
    let changed = method(facts, EFFECTS, "changed", "()I").unwrap();
    let scalar = method(facts, CLOSED, "scalar", "()I").unwrap();
    selector_solve::analyze(
        facts,
        graph,
        &[graph.node_for_symbol(changed).unwrap()],
        &selector_solve::SolveOptions {
            workers,
            max_contexts: 10_000,
            max_steps: 1_000_000,
            memory_budget_bytes: 64 * 1024 * 1024,
            execution_roots: Some(
                vec![
                    selector_solve::ExecutionRoot {
                        node: graph.node_for_symbol(root).unwrap(),
                        receiver: class(facts, FACTORY),
                    },
                    selector_solve::ExecutionRoot {
                        node: graph.node_for_symbol(scalar).unwrap(),
                        receiver: class(facts, CLOSED),
                    },
                ]
                .into(),
            ),
            ..Default::default()
        },
    )
    .unwrap()
}

#[test]
fn genuine_lazy_constructor_override_and_shadow_observations_are_pinned() {
    assert_eq!(
        std::fs::read_to_string(directory().join("execution.stdout")).unwrap(),
        "lazy:true:1:3\nentry:4:5\noverride:6:-1:6\nscalar:17:6\n"
    );
    assert_eq!(
        std::fs::read_to_string(directory().join("shadow-execution.stdout")).unwrap(),
        "shadow:true:0\n"
    );
}

#[test]
fn fixed_pressure_admits_getter_helper_and_constructor_before_unused_implementations() {
    let result = admitted(Profile::Getter, 15, 1, Control::None).unwrap();
    let facts = &result.facts;
    assert!(
        result.mandatory_methods + result.derived_methods <= 15,
        "unchanged declaration budget"
    );
    for (owner, name, descriptor) in [
        (GETTER, "aGet", BOX_DESC),
        (GETTER, "lazyHelper", BOX_DESC),
        (BOX, "<init>", "()V"),
    ] {
        let body = body(facts, owner, name, descriptor)
            .expect("dependency-first chain must fit the fixed fifteen-slot inventory");
        assert_ne!(body.flags & BODY_BINARY_RECIPE, 0);
        assert!(
            !operators(facts, owner, name, descriptor)
                .iter()
                .any(|op| op.opcode == Opcode::Unknown),
            "{name} body closed locally"
        );
        let file = &facts.files[body.file.index()];
        let pin = fixture_json();
        let path = format!("classes/{owner}.class");
        let expected = pin["files"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["path"] == path)
            .unwrap();
        assert_eq!(
            file.source_hash,
            ContentHash::from_hex(expected["sha256"].as_str().unwrap()).unwrap(),
            "actual class bytes bind body"
        );
    }
    let helper = operators(facts, GETTER, "lazyHelper", BOX_DESC);
    let constructor = method(facts, BOX, "<init>", "()V").unwrap();
    let changed = method(facts, EFFECTS, "changed", "()I").unwrap();
    assert!(
        helper
            .iter()
            .any(|op| matches!(op.opcode, Opcode::Call | Opcode::Allocate)
                && op.target == constructor)
    );
    assert!(helper.iter().any(|op| op.opcode == Opcode::StoreField));
    assert!(
        helper
            .iter()
            .any(|op| matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
                && op.target == changed),
        "later actual call retained"
    );
    assert!(
        operators(facts, BOX, "<init>", "()V")
            .iter()
            .any(|op| op.opcode == Opcode::StoreField),
        "constructor actual write retained"
    );
    assert!(
        facts
            .relations
            .iter()
            .any(|row| row.kind == RelationKind::DeferredDispatch),
        "unused contracts remain explicit frontiers"
    );
    let graph = graph(facts, 1);
    let analysis = analyze(facts, &graph, Profile::Getter, 1);
    assert_ne!(analysis.completion, Completion::ResourceLimited);
    let root = graph
        .node_for_symbol(method(facts, FACTORY, "entry", BOX_DESC).unwrap())
        .unwrap();
    assert!(
        analysis.contains(root),
        "real lazy/constructor call must retain the positive impact proof"
    );
    let scalar = graph
        .node_for_symbol(method(facts, CLOSED, "scalar", "()I").unwrap())
        .unwrap();
    assert!(!analysis.guarded_roots.contains(&scalar) && !analysis.contains(scalar));
    let plan = selector_plan::plan(
        facts,
        &graph,
        selector_plan::PlanSeeds {
            execution: &[graph.node_for_symbol(changed).unwrap()],
            declarations: &[],
            unscoped: false,
        },
    )
    .unwrap();
    assert!(
        plan.certifies_unaffected(scalar),
        "unused deferred contracts cannot erase a no-field scalar certificate"
    );
}

#[test]
fn too_small_chain_keeps_missing_constructor_guard_and_later_real_effects() {
    let admitted = admitted(Profile::Getter, 14, 1, Control::None).unwrap();
    let facts = &admitted.facts;
    assert!(admitted.mandatory_methods + admitted.derived_methods <= 14);
    assert!(
        body(facts, BOX, "<init>", "()V").is_none(),
        "fixed pressure must refuse the direct constructor"
    );
    let helper = operators(facts, GETTER, "lazyHelper", BOX_DESC);
    assert!(helper.iter().any(|op| op.opcode == Opcode::Unknown));
    assert!(helper.iter().any(|op| op.opcode == Opcode::StoreField));
    let changed = method(facts, EFFECTS, "changed", "()I").unwrap();
    assert!(
        helper
            .iter()
            .any(|op| op.target == changed
                && matches!(op.opcode, Opcode::Call | Opcode::VirtualCall))
    );
    assert!(
        facts
            .issues
            .iter()
            .any(|row| row.kind == IssueKind::UnknownExecution
                && facts.text(row.detail).contains("method admission budget"))
    );
    let graph = graph(facts, 1);
    let analysis = analyze(facts, &graph, Profile::Getter, 1);
    let root = graph
        .node_for_symbol(method(facts, FACTORY, "entry", BOX_DESC).unwrap())
        .unwrap();
    assert!(analysis.guarded_roots.contains(&root));
    assert!(
        analysis.contains(root),
        "known effects survive failed chain admission"
    );
}

#[test]
fn unadmitted_child_override_never_turns_an_available_base_body_into_complete_dispatch() {
    let admitted = admitted(Profile::ChildOverride, 9, 1, Control::None).unwrap();
    let facts = &admitted.facts;
    assert!(
        body(facts, BASE, "m", "()I").is_some(),
        "actual parent body available"
    );
    assert!(
        body(facts, CHILD, "m", "()I").is_none(),
        "pressure must omit actual override"
    );
    assert!(
        facts
            .relations
            .iter()
            .any(|row| row.kind == RelationKind::DeferredDispatch
                && row.source == class(facts, CHILD))
            || facts
                .issues
                .iter()
                .any(|row| row.kind.is_execution_boundary() && row.symbol == class(facts, CHILD)),
        "missing child remains explicit"
    );
    let graph = graph(facts, 1);
    let analysis = analyze(facts, &graph, Profile::ChildOverride, 1);
    assert_ne!(analysis.completion, Completion::ResourceLimited);
    let root = graph
        .node_for_symbol(method(facts, FACTORY, "childEntry", "()I").unwrap())
        .unwrap();
    assert!(
        analysis.guarded_roots.contains(&root),
        "Base.m cannot establish completion when actual Child.m is absent"
    );
}

#[test]
fn dependency_priority_has_identical_canonical_outputs_at_one_and_four_workers() {
    let first = admitted(Profile::Getter, 15, 1, Control::None).unwrap();
    let parallel = admitted(Profile::Getter, 15, 4, Control::None).unwrap();
    assert_eq!(first.facts.identity, parallel.facts.identity);
    assert_eq!(first.derived_methods, parallel.derived_methods);
    assert_eq!(first.retries, parallel.retries);
    assert!(
        first.retries <= first.mandatory_methods + first.derived_methods,
        "one final retry per admitted caller"
    );
    let tmp = tempfile::tempdir().unwrap();
    let a = tmp.path().join("one.bin");
    let b = tmp.path().join("four.bin");
    selector_facts::codec::write(&a, &first.facts).unwrap();
    selector_facts::codec::write(&b, &parallel.facts).unwrap();
    assert_eq!(std::fs::read(a).unwrap(), std::fs::read(b).unwrap());
    let before_graph = graph(&first.facts, 1);
    let after_graph = graph(&parallel.facts, 4);
    let before = analyze(&first.facts, &before_graph, Profile::Getter, 1);
    let after = analyze(&parallel.facts, &after_graph, Profile::Getter, 4);
    assert_eq!(before.completion, after.completion);
    assert_eq!(before.affected, after.affected);
    assert_eq!(before.guarded_roots, after.guarded_roots);
    assert_eq!(before.witnesses, after.witnesses);
    assert_eq!(before.derived_edges, after.derived_edges);
}

#[test]
fn ordered_provider_source_name_and_context_frontiers_cannot_borrow_a_later_chain() {
    let shadow = admitted(Profile::Getter, 15, 1, Control::Shadow).unwrap();
    let facts = &shadow.facts;
    assert!(body(facts, GETTER, "aGet", BOX_DESC).is_some());
    assert!(
        body(facts, GETTER, "lazyHelper", BOX_DESC).is_none(),
        "earlier provider has no lazy helper"
    );
    assert!(
        body(facts, BOX, "<init>", "()V").is_none(),
        "no borrowing later getter's constructor"
    );
    let pin = fixture_json();
    let expected = pin["files"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["path"] == "shadow-classes/admissioncase/Getter.class")
        .unwrap();
    let shadow_body = body(facts, GETTER, "aGet", BOX_DESC).unwrap();
    assert_eq!(
        facts.files[shadow_body.file.index()].source_hash,
        ContentHash::from_hex(expected["sha256"].as_str().unwrap()).unwrap()
    );
    for control in [
        Control::SourceOverlay,
        Control::ContextConflict,
        Control::Unavailable,
    ] {
        let admitted = admitted(Profile::Getter, 15, 1, control).unwrap();
        let facts = &admitted.facts;
        assert!(
            body(facts, GETTER, "aGet", BOX_DESC).is_none(),
            "no unjustified native override authority"
        );
        let graph = graph(facts, 1);
        let analysis = analyze(facts, &graph, Profile::Getter, 1);
        let root = graph
            .node_for_symbol(method(facts, FACTORY, "entry", BOX_DESC).unwrap())
            .unwrap();
        assert!(
            analysis.guarded_roots.contains(&root),
            "unproved provider/source/context cannot close getter dispatch"
        );
    }
}
