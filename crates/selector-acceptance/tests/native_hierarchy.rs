//! Genuine unordered native ancestry supports type exclusion, not Scala mixin
//! order or executable purity. Missing/deferred ancestors stay conservative.
use selector_domain::{Atom, Slot, Value, ValuePool};
use selector_facts::{FactBuilder, FactSnapshot, ResultBoundRecord};
use selector_graph_build::binary_inputs::{
    NativeAdmissionLimits, augment_binary_facts_with_limits, load_binary_manifest,
};
use selector_transfer::{SummaryRead, World};
use selector_types::*;
use std::path::PathBuf;
const FACTORY: &str = "hierarchycase/Factory";
const A: &str = "hierarchycase/Factory$A";
const B: &str = "hierarchycase/Factory$B";
const CONTRACT: &str = "hierarchycase/Factory$Contract";
const OBJECT: &str = "java/lang/Object";
fn directory() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/native-hierarchy")
}
fn endpoint(owner: &str, name: &str, descriptor: &str) -> String {
    format!(
        "@jvm/{}:{owner}{}:{name}{}:{descriptor}",
        owner.len(),
        name.len(),
        descriptor.len()
    )
}
fn admitted(mode: &str) -> FactSnapshot {
    // Public native input endpoints are opaque JVM identities, not fabricated
    // compiler declarations. The constraint comes from the real echo descriptor.
    let parsed = selector_models::binary::parse_class(
        include_bytes!("../../../fixtures/native-hierarchy/classes/hierarchycase/Factory.class"),
        Default::default(),
    )
    .unwrap();
    let echo_descriptor = "(Lhierarchycase/Factory$A;)Lhierarchycase/Factory$A;";
    assert!(parsed.method("echo", Some(echo_descriptor)).is_ok());
    let mut builder = FactBuilder::new();
    let context = builder.intern("fixture:native-hierarchy").unwrap();
    builder.facts.revision = builder.intern("genuine-native-hierarchy-v1").unwrap();
    let owners = [FACTORY, CONTRACT, A, B, OBJECT];
    let mut classes = std::collections::HashMap::new();
    for owner in owners {
        let id = builder
            .ensure_symbol(&endpoint(owner, "<type>", ""), FileId::NONE)
            .unwrap();
        let row = &mut builder.facts.symbols[id.index()];
        row.context = context;
        // Native identity classification only. Header8 and parent16 are
        // deliberately absent until ordinary hash-verified enrichment.
        row.flags = SYMBOL_NATIVE_BINARY;
        row.kind = if owner == CONTRACT { 14 } else { 13 };
        classes.insert(owner, id);
    }
    let mut methods = Vec::new();
    let mut echo = SymbolId::NONE;
    for (owner, name, descriptor) in [
        (FACTORY, "echo", echo_descriptor),
        (FACTORY, "caller", "(Lhierarchycase/Factory$A;)I"),
        (
            FACTORY,
            "objectText",
            "(Lhierarchycase/Factory$A;)Ljava/lang/String;",
        ),
        (CONTRACT, "value", "()I"),
        (A, "value", "()I"),
        (B, "value", "()I"),
        (OBJECT, "toString", "()Ljava/lang/String;"),
    ] {
        let spelling = endpoint(owner, name, descriptor);
        let id = builder.ensure_symbol(&spelling, FileId::NONE).unwrap();
        let row = &mut builder.facts.symbols[id.index()];
        row.context = context;
        row.owner = classes[owner];
        row.kind = 3;
        row.flags = SYMBOL_NATIVE_BINARY;
        if name == "echo" {
            echo = id;
        }
        methods.push(serde_json::json!({"context":"fixture:native-hierarchy","compiler_symbol":spelling,"jvm_owner":owner,"jvm_name":name,"descriptor":descriptor}));
    }
    builder.facts.bound_classes.push(classes[A]);
    builder.facts.result_bounds.push(ResultBoundRecord {
        symbol: echo,
        operation: OperationId::NONE,
        classes: IdRange { start: 0, len: 1 },
    });
    let mut facts = builder.finish().unwrap();
    let receipt: serde_json::Value =
        serde_json::from_slice(&std::fs::read(directory().join("manifest.json")).unwrap()).unwrap();
    let jar = |name: &str| {
        let row = receipt["files"]
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
    entries.push(jar(if mode == "missing" {
        "incomplete.jar"
    } else {
        "bytecode.jar"
    }));
    if mode != "axiom" {
        entries.push(jar("bootstrap.jar"));
    }
    let manifest = serde_json::json!({"version":1,"revision":facts.text(facts.revision),"java_feature":21,
        "contexts":[{"id":"fixture:native-hierarchy","entries":entries}],
        "types":owners.into_iter().map(|owner|serde_json::json!({"context":"fixture:native-hierarchy","compiler_symbol":endpoint(owner,"<type>",""),"jvm_owner":owner})).collect::<Vec<_>>(),"methods":methods});
    let temp = tempfile::tempdir().unwrap();
    let path = temp.path().join("binary.json");
    std::fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    let mut inputs = load_binary_manifest(&path, &facts).unwrap();
    let limits = if mode == "budget" {
        NativeAdmissionLimits {
            classes_per_context: 5,
            ..Default::default()
        }
    } else {
        Default::default()
    };
    augment_binary_facts_with_limits(&mut facts, &mut inputs, limits).unwrap();
    facts
}
struct OpaqueFrame(ValuePool);
impl World for OpaqueFrame {
    fn values(&self) -> &ValuePool {
        &self.0
    }
    fn summary(
        &self,
        node: NodeId,
        _: Value,
        _: &[Value],
        _: &ValuePool,
        _: &mut Vec<Value>,
    ) -> SummaryRead {
        SummaryRead {
            context: Some(ContextId(node.0)),
            value: Value::TOP,
            version: 1,
            present: true,
        }
    }
    fn slot(&self, _: Slot) -> (Value, u64, bool) {
        (Value::TOP, 1, true)
    }
    fn capture(&self, _: u32) -> Option<(Value, &[Value], u64)> {
        None
    }
    fn binding(
        &self,
        _: OperationId,
        _: Value,
        _: &[Value],
        _: &ValuePool,
        _: &mut Vec<Atom>,
        _: &mut Vec<Value>,
    ) -> Option<u32> {
        None
    }
}
fn targets(facts: &FactSnapshot) -> Vec<String> {
    let graph = selector_graph_build::build(
        facts,
        &selector_graph_build::BuildOptions {
            workers: 2,
            include_models: false,
        },
    )
    .unwrap();
    let node = graph
        .node_for_symbol(
            facts
                .find_symbol(&endpoint(FACTORY, "caller", "(Lhierarchycase/Factory$A;)I"))
                .unwrap(),
        )
        .unwrap();
    let types = selector_transfer::TypeIndex::new(facts);
    let world = OpaqueFrame(ValuePool::new(32));
    let mut scratch = selector_transfer::Scratch::new(32);
    let mut out = selector_transfer::Evaluation::default();
    selector_transfer::evaluate(
        facts,
        &graph,
        &types,
        &world,
        node,
        Value::EMPTY,
        &[Value::TOP],
        &mut scratch,
        &mut out,
    )
    .unwrap();
    out.calls
        .iter()
        .map(|call| {
            facts
                .symbol_name(graph.nodes[call.target.index()].symbol)
                .to_owned()
        })
        .collect()
}
#[test]
fn genuine_jvm_class_descriptor_and_provider_observations_are_frozen() {
    let expected =
        "caller:1\nB:2\nA-parent:hierarchycase.Factory$Base\nobject-method:class-name-prefix\n";
    assert_eq!(
        std::fs::read_to_string(directory().join("execution.log")).unwrap(),
        expected
    );
    assert_eq!(
        std::fs::read_to_string(directory().join("shadow-execution.log")).unwrap(),
        expected
    );
}
#[test]
fn verified_unordered_ancestry_excludes_unrelated_b_without_scala_order_authority() {
    let facts = admitted("full");
    let class = facts.find_symbol(&endpoint(A, "<type>", "")).unwrap();
    assert_ne!(
        facts.symbols[class.index()].flags & SYMBOL_JVM_PARENTS_COMPLETE,
        0,
        "producer proved admitted parents"
    );
    assert_eq!(
        facts.symbols[class.index()].flags & SYMBOL_SCALA_PARENTS_COMPLETE,
        0
    );
    let types = selector_transfer::TypeIndex::new(&facts);
    let mut work = Default::default();
    assert!(types.linearization(class, &mut work).is_none());
    let calls = targets(&facts);
    assert!(calls.contains(&endpoint(A, "value", "()I")));
    assert!(
        !calls.contains(&endpoint(B, "value", "()I")),
        "exact A upper bound cannot dispatch to unrelated verified B"
    );
}
#[test]
fn missing_deferred_or_shadowed_ancestor_keeps_unrelated_candidate_possible() {
    for mode in ["missing", "budget", "shadow"] {
        let facts = admitted(mode);
        let calls = targets(&facts);
        assert!(
            calls.contains(&endpoint(A, "value", "()I")),
            "{mode} retains actual A"
        );
        assert!(
            calls.contains(&endpoint(B, "value", "()I")),
            "{mode} lacks complete ancestry and cannot exclude B"
        );
        assert!(!facts.issues.is_empty(), "{mode} retains explicit boundary");
    }
}
#[test]
fn object_rootness_without_bytes_proves_ancestry_but_not_missing_method_purity() {
    let facts = admitted("axiom");
    let calls = targets(&facts);
    assert!(calls.contains(&endpoint(A, "value", "()I")));
    assert!(
        !calls.contains(&endpoint(B, "value", "()I")),
        "exact Object rootness is ancestry authority"
    );
    let object = facts.find_symbol(&endpoint(OBJECT, "<type>", "")).unwrap();
    assert_eq!(
        facts.symbols[object.index()].flags & SYMBOL_JVM_CLASS_HEADER_VERIFIED,
        0,
        "rootness does not forge class bytes"
    );
    let method = facts
        .find_symbol(&endpoint(OBJECT, "toString", "()Ljava/lang/String;"))
        .unwrap();
    assert!(
        !facts.bodies.iter().any(|body| body.symbol == method),
        "no executable method recipe from Object rootness"
    );
    assert!(
        facts.issues.iter().any(|issue| issue.symbol == method
            && matches!(
                issue.kind,
                IssueKind::MissingBinary | IssueKind::UnknownExecution
            )),
        "nonintrinsic missing Object method remains guarded"
    );
}
