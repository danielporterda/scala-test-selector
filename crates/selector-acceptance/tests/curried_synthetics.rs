//! Frozen compiler trees, JVM effects and admission controls for curried calls.
use selector_domain::{Atom, AtomKind, Slot, Value, ValuePool};
use selector_extract::{ExtractOptions, import_capture};
use selector_facts::{FactSnapshot, OperationRecord, TextRange};
use selector_graph_build::binary_inputs::{augment_binary_facts, load_binary_manifest};
use selector_issue::RuntimeIssueReason;
use selector_types::*;
use serde_json::Value as JsonValue;
use std::path::PathBuf;

struct WordFrame {
    pool: ValuePool,
}
impl selector_transfer::World for WordFrame {
    fn values(&self) -> &ValuePool {
        &self.pool
    }
    fn summary(
        &self,
        node: NodeId,
        _: Value,
        _: &[Value],
        _: &ValuePool,
        _: &mut Vec<Value>,
    ) -> selector_transfer::SummaryRead {
        selector_transfer::SummaryRead {
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

#[test]
fn real_word_scope_certificate_does_not_zero_invoke_its_opaque_implicit_carrier() {
    let mut facts = captured();
    enrich(&mut facts, None);
    let site = facts
        .operations
        .iter()
        .position(|op| {
            facts.symbol_name(op.target)
                == "org/scalatest/verbs/ShouldVerb#StringShouldWrapperForVerb#should(+2)."
                && op.arguments.len == 2
                && owner(&facts, facts.bodies[op.body.index()].symbol) == "curriedcase/WordSuite#"
        })
        .expect("actual compiler-bound WordSpec should(scope)(subjectRegistrationFunction)");
    let operation = OperationId(site as u32);
    let written = facts.operations[site];
    assert_eq!(callback_argument_slot(written.flags), Some(0));
    let args = &facts.operands[written.arguments.range()];
    let body = facts.bodies[written.body.index()];
    let scope = body
        .operations
        .range()
        .find(|&i| facts.operations[i].dest == args[0])
        .unwrap();
    let carrier = body
        .operations
        .range()
        .find(|&i| facts.operations[i].dest == args[1])
        .unwrap();
    assert_eq!(facts.operations[scope].opcode, Opcode::BindCallback);
    assert!(
        facts
            .symbol_name(facts.operations[carrier].target)
            .contains("subjectRegistrationFunction")
    );
    let scope_symbol = facts.operations[scope].target;
    let mut graph = selector_graph_build::build(&facts, &Default::default()).unwrap();
    let source = graph.node_for_symbol(body.symbol).unwrap();
    assert_eq!(graph.nodes[source.index()].body, written.body);
    let callee = graph.node_for_symbol(written.target).unwrap();
    let scope_node = graph.node_for_symbol(scope_symbol).unwrap();
    let modeled: Vec<_> = graph
        .edges
        .iter()
        .filter(|edge| {
            edge.source == source
                && edge.operation == operation
                && edge.target == callee
                && edge.flags & (EDGE_CALLBACK_IMMEDIATE | EDGE_TEST_REGISTRATION) != 0
        })
        .collect();
    assert!(!modeled.is_empty());
    assert!(
        modeled
            .iter()
            .all(|edge| callback_argument_slot(edge.flags) == Some(0))
    );
    assert_eq!(
        graph.nodes[callee.index()].flags & NODE_EFFECTS_COMPLETE,
        0,
        "the slot certificate must not declare the full native callee pure"
    );
    let mut pool = ValuePool::new(64);
    let receiver = pool
        .singleton(Atom {
            kind: AtomKind::Object,
            site: OperationId::NONE,
            symbol: facts.find_symbol("curriedcase/WordSuite#").unwrap(),
            binding: 0,
        })
        .unwrap();
    // The observed suite receiver is concrete; every external return and field
    // value remains opaque, including the wrapper and Function3 carrier.
    let world = WordFrame { pool };
    let original_scope = facts.operations[scope];
    let original_flags: Vec<_> = graph.edges.iter().map(|edge| edge.flags).collect();
    for control in 0..4 {
        facts.operations[site] = written;
        facts.operations[scope] = original_scope;
        for (edge, flags) in graph.edges.iter_mut().zip(&original_flags) {
            edge.flags = *flags;
        }
        if control == 1 || control == 2 {
            let certificate = if control == 1 {
                0
            } else {
                encode_callback_argument(7).unwrap()
            };
            facts.operations[site].flags = (facts.operations[site].flags
                & !(CALLBACK_ARGUMENT_PRESENT | CALLBACK_ARGUMENT_MASK))
                | certificate;
            for edge in &mut graph.edges {
                if edge.source == source
                    && edge.operation == operation
                    && edge.flags & (EDGE_CALLBACK_IMMEDIATE | EDGE_TEST_REGISTRATION) != 0
                {
                    edge.flags = (edge.flags
                        & !(CALLBACK_ARGUMENT_PRESENT | CALLBACK_ARGUMENT_MASK))
                        | certificate;
                }
            }
        } else if control == 3 {
            // Admission-negative frame: the actual callback slot is opaque too.
            // Reuse the genuine carrier load, retaining the scope's stable ID.
            facts.operations[scope] = selector_facts::OperationRecord {
                body: facts.operations[scope].body,
                dest: facts.operations[scope].dest,
                span: facts.operations[scope].span,
                ..facts.operations[carrier]
            };
        }
        let types = selector_transfer::TypeIndex::new(&facts);
        let mut scratch = selector_transfer::Scratch::new(64);
        let mut out = selector_transfer::Evaluation::default();
        selector_transfer::evaluate(
            &facts,
            &graph,
            &types,
            &world,
            source,
            receiver,
            &[],
            &mut scratch,
            &mut out,
        )
        .unwrap();
        let native = out
            .calls
            .iter()
            .find(|call| {
                call.target == callee
                    && call.operation == operation
                    && call.kind != EdgeKind::Callback
            })
            .expect("full native callee effect remains scheduled");
        assert!(out.arguments[native.arguments.range()][1].is_unknown());
        assert!(native.receiver.is_unknown());
        assert!(native.observe_return);
        if control == 0 {
            assert_eq!(
                out.calls
                    .iter()
                    .filter(|call| call.target == scope_node
                        && call.kind == EdgeKind::Callback
                        && call.operation == operation)
                    .count(),
                1
            );
            assert!(
                out.first_issue.is_none(),
                "known scope plus opaque non-callback carrier: {:?}",
                out.first_issue
            );
        } else {
            assert!(
                out.issues.contains(&IssueKind::UnknownExecution),
                "missing, malformed or opaque actual slot must remain guarded"
            );
            let issue = out.first_issue.expect("guard from actual modeled call");
            assert_eq!(issue.operation, operation);
            if control == 1 || control == 3 {
                assert_eq!(issue.reason, RuntimeIssueReason::UnknownCallbackValue);
            }
        }
    }
}

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/curried-synthetics")
}
fn captured() -> FactSnapshot {
    import_capture(
        &fixture().join("documents.jsonl"),
        Some(&fixture().join("syntax.jsonl")),
        &ExtractOptions {
            workers: 2,
            ..Default::default()
        },
    )
    .unwrap()
}
fn owner(facts: &FactSnapshot, mut symbol: SymbolId) -> &str {
    for _ in 0..128 {
        let record = facts.symbols[symbol.index()];
        if matches!(record.kind, 10 | 13 | 14) || record.owner.is_none() {
            return facts.symbol_name(symbol);
        }
        symbol = record.owner;
    }
    panic!("cyclic owner")
}
// Enrichment may insert eager-VAL stores in earlier bodies and reown the
// current RHS. Body identity, exact source span and local SSA definition survive;
// absolute operation IDs do not. Require one actual post-enrichment site.
fn enriched_site(facts: &FactSnapshot, written: OperationRecord) -> usize {
    let body = &facts.bodies[written.body.index()];
    let sites: Vec<_> = body
        .operations
        .range()
        .filter(|&index| {
            let op = facts.operations[index];
            op.body == written.body && op.span == written.span && op.dest == written.dest
        })
        .collect();
    assert_eq!(
        sites.len(),
        1,
        "unique source/SSA site in {} at {:?}",
        facts.symbol_name(body.symbol),
        written.span
    );
    sites[0]
}
const WRAPPER: &str = "org/scalatest/matchers/should/Matchers#convertToStringShouldWrapper().";
fn enrich(facts: &mut FactSnapshot, boundary: Option<&str>) {
    if boundary.is_none() {
        let mut inputs = load_binary_manifest(&fixture().join("binary.json"), facts).unwrap();
        augment_binary_facts(facts, &mut inputs).unwrap();
        return;
    }
    let mut manifest: JsonValue =
        serde_json::from_slice(&std::fs::read(fixture().join("binary.json")).unwrap()).unwrap();
    let entries = manifest["contexts"][0]["entries"].as_array_mut().unwrap();
    for entry in entries.iter_mut() {
        let path = PathBuf::from(entry["path"].as_str().unwrap());
        if path.is_relative() {
            entry["path"] = fixture().join(path).to_str().unwrap().into();
        }
    }
    if boundary == Some("shadow") {
        let receipt: JsonValue =
            serde_json::from_slice(&std::fs::read(fixture().join("manifest.json")).unwrap())
                .unwrap();
        let shadow = receipt["files"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["path"] == "shadow.jar")
            .unwrap();
        entries.insert(0, serde_json::json!({"path":fixture().join("shadow.jar"),"kind":"jar","sha256":shadow["sha256"]}));
    } else {
        entries.insert(
            0,
            serde_json::json!({"path":"not-admitted.jar","kind":"unavailable"}),
        );
    }
    let temporary = tempfile::tempdir().unwrap();
    let path = temporary.path().join("binary.json");
    std::fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    let mut inputs = load_binary_manifest(&path, facts).unwrap();
    augment_binary_facts(facts, &mut inputs).unwrap();
}

#[test]
fn exact_native_arity_folds_only_the_compiler_tagged_nonfunction_clause() {
    let mut facts = captured();
    let prefix = facts
        .operations
        .iter()
        .position(|op| {
            facts.symbol_name(op.target) == WRAPPER
                && matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
        })
        .unwrap();
    let result = facts.operations[prefix].dest;
    let stage = facts
        .operations
        .iter()
        .position(|op| {
            op.opcode == Opcode::InvokeCallback
                && op.flags == OP_SYNTHETIC_PARAMETER_APPLY
                && op.a == result
        })
        .unwrap();
    assert_eq!(facts.operations[prefix].arguments.len, 1);
    assert_eq!(facts.operations[stage].arguments.len, 2);
    let body = facts.operations[prefix].body;
    let original_body = facts.bodies[body.index()];
    let final_value = facts.operations[stage].dest;
    let prefix_written = facts.operations[prefix];
    let stage_written = facts.operations[stage];
    enrich(&mut facts, None);
    let prefix = enriched_site(&facts, prefix_written);
    let stage = enriched_site(&facts, stage_written);
    assert_eq!(facts.operations[prefix].opcode, Opcode::Constant);
    assert!(matches!(
        facts.operations[stage].opcode,
        Opcode::Call | Opcode::VirtualCall
    ));
    assert_eq!(facts.symbol_name(facts.operations[stage].target), WRAPPER);
    assert_eq!(facts.operations[stage].arguments.len, 3);
    assert_eq!(facts.operations[stage].dest, final_value);
    let enriched_body = facts.bodies[body.index()];
    assert_eq!(enriched_body.file, original_body.file);
    assert_eq!(enriched_body.name_span, original_body.name_span);
    let reowned = enriched_body.symbol != original_body.symbol;
    assert_eq!(
        enriched_body.operations.len,
        original_body.operations.len + u32::from(reowned),
        "folding preserves recipe length; eager VAL normalization alone adds its one store"
    );
    if reowned {
        assert_eq!(
            facts.operations[enriched_body.operations.range()]
                .iter()
                .filter(|op| op.opcode == Opcode::StoreField && op.target == original_body.symbol)
                .count(),
            1
        );
    }
    assert_ne!(
        facts.bodies[facts.operations[stage].body.index()].body_hash,
        original_body.body_hash
    );
    let mut unavailable = captured();
    enrich(&mut unavailable, Some("missing"));
    let stage = enriched_site(&unavailable, stage_written);
    assert_eq!(unavailable.operations[stage].opcode, Opcode::InvokeCallback);
    assert_eq!(
        unavailable.operations[stage].flags,
        OP_SYNTHETIC_PARAMETER_APPLY
    );
}

#[test]
fn an_extra_use_of_the_real_partial_result_disables_folding() {
    let mut facts = captured();
    let prefix = facts
        .operations
        .iter()
        .position(|op| {
            facts.symbol_name(op.target) == WRAPPER
                && matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
        })
        .unwrap();
    let result = facts.operations[prefix].dest;
    let stage = facts
        .operations
        .iter()
        .position(|op| {
            op.opcode == Opcode::InvokeCallback
                && op.flags == OP_SYNTHETIC_PARAMETER_APPLY
                && op.a == result
        })
        .unwrap();
    let body = facts.bodies[facts.operations[prefix].body.index()];
    let extra = body
        .operations
        .range()
        .rev()
        .find(|&id| id > stage && facts.operations[id].b.is_none())
        .unwrap();
    // Explicit admission-negative perturbation of genuine IR: even an otherwise
    // unused operand is counted conservatively, preventing a hidden extra use.
    facts.operations[extra].b = result;
    let prefix_written = facts.operations[prefix];
    let stage_written = facts.operations[stage];
    enrich(&mut facts, None);
    let prefix = enriched_site(&facts, prefix_written);
    let stage = enriched_site(&facts, stage_written);
    assert!(matches!(
        facts.operations[prefix].opcode,
        Opcode::Call | Opcode::VirtualCall
    ));
    assert_eq!(facts.operations[stage].opcode, Opcode::InvokeCallback);
    assert_eq!(facts.operations[stage].flags, OP_SYNTHETIC_PARAMETER_APPLY);
}

#[test]
fn an_actual_earlier_same_owner_class_cannot_fall_back_to_later_descriptors() {
    let mut admitted = captured();
    let original = admitted
        .find_symbol("curriedcase/Library.curried().")
        .unwrap();
    enrich(&mut admitted, None);
    assert!(admitted.bodies.iter().any(|body| body.symbol == original
        && body.flags & BODY_BINARY_RECIPE != 0
        && body.parameters.len == 3));
    let mut facts = captured();
    let method = facts.find_symbol("curriedcase/Library.curried().").unwrap();
    enrich(&mut facts, Some("shadow"));
    assert!(
        facts
            .bodies
            .iter()
            .all(|body| body.symbol != method || body.flags & BODY_BINARY_RECIPE == 0)
    );
    let shadow = std::fs::read_to_string(fixture().join("javap-shadow.log")).unwrap();
    assert!(shadow.contains("(ILorg/scalactic/source/Position;)I"));
    assert!(!shadow.contains("(ILorg/scalactic/source/Position;Lorg/scalactic/Prettifier;)I"));
}

#[test]
fn genuine_typed_tree_and_independent_jvm_effects_cover_the_external_wrapper() {
    let row: JsonValue =
        serde_json::from_slice(&std::fs::read(fixture().join("documents.jsonl")).unwrap()).unwrap();
    let synthetics = row["document"]["synthetics"].as_array().unwrap();
    let wrapper = synthetics.iter().find(|synthetic| {
        synthetic["tree"]["apply_tree"]["function"]["apply_tree"]["function"]["id_tree"]["symbol"]
            == "org/scalatest/matchers/should/Matchers#convertToStringShouldWrapper()."
    }).expect("original compiler-generated nested application");
    assert_eq!(
        wrapper["tree"]["apply_tree"]["arguments"]
            .as_array()
            .unwrap()
            .len(),
        2
    );
    let manifest: JsonValue =
        serde_json::from_slice(&std::fs::read(fixture().join("manifest.json")).unwrap()).unwrap();
    assert_eq!(
        manifest["independent_runtime_observations"],
        serde_json::json!([
            "external:1:1",
            "source:2:2",
            "returned:4:4",
            "reused:16:32:32",
            "registered:1:0",
            "executed:8"
        ])
    );
    assert_eq!(
        std::fs::read_to_string(fixture().join("execution.log"))
            .unwrap()
            .lines()
            .collect::<Vec<_>>(),
        [
            "external:1:1",
            "source:2:2",
            "returned:4:4",
            "reused:16:32:32",
            "registered:1:0",
            "executed:8"
        ]
    );
    assert!(
        std::fs::read_to_string(fixture().join("scalatest.log"))
            .unwrap()
            .contains("Tests: succeeded 1, failed 0")
    );
    let facts = captured();
    let external = facts
        .find_symbol("org/scalatest/matchers/should/Matchers#convertToStringShouldWrapper().")
        .unwrap();
    assert!(facts.symbols[external.index()].signature.is_none());
    let known = facts
        .find_symbol("curriedcase/SourceSuite#known().")
        .unwrap();
    assert!(!facts.symbols[known.index()].signature.is_none());
}

#[test]
fn source_known_clauses_and_true_function_results_remain_distinct() {
    let mut facts = captured();
    let mut callback_counts = Vec::new();
    for class in [
        "ExternalSuite",
        "SourceSuite",
        "CallbackSuite",
        "ReusedCallbackSuite",
        "WordSuite",
    ] {
        let symbol = format!("curriedcase/{class}#");
        let count = facts
            .operations
            .iter()
            .filter(|op| {
                op.opcode == Opcode::InvokeCallback
                    && owner(&facts, facts.bodies[op.body.index()].symbol) == symbol
            })
            .count();
        callback_counts.push((class, count));
    }
    assert_eq!(
        callback_counts[1].1, 0,
        "source-known implicit clauses do not invoke a function result"
    );
    assert!(
        callback_counts[2].1 >= 1,
        "a genuine returned function must remain executable"
    );
    assert!(
        callback_counts[3].1 >= 2,
        "both uses of a stored callback must remain executable"
    );
    let call = facts
        .operations
        .iter()
        .position(|op| {
            facts.symbol_name(op.target) == "curriedcase/Library.returned()."
                && matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
        })
        .unwrap();
    let invoked = facts
        .operations
        .iter()
        .position(|op| {
            op.opcode == Opcode::InvokeCallback
                && op.body == facts.operations[call].body
                && op.a == facts.operations[call].dest
        })
        .unwrap();
    assert_eq!(facts.operations[invoked].arguments.len, 0);
    assert_eq!(facts.operations[invoked].flags, 0);
    assert!(facts.operations.iter().any(|op| op.opcode == Opcode::Return
        && op.body == facts.operations[call].body
        && op.a == facts.operations[invoked].dest));
    let call_written = facts.operations[call];
    let invoked_written = facts.operations[invoked];
    enrich(&mut facts, None);
    let call = enriched_site(&facts, call_written);
    let invoked = enriched_site(&facts, invoked_written);
    assert_eq!(
        facts.symbol_name(facts.operations[call].target),
        "curriedcase/Library.returned()."
    );
    assert!(matches!(
        facts.operations[call].opcode,
        Opcode::Call | Opcode::VirtualCall
    ));
    assert_eq!(facts.operations[invoked].opcode, Opcode::InvokeCallback);
    assert_eq!(facts.operations[invoked].a, facts.operations[call].dest);
}

fn generated_word_inputs(facts: &FactSnapshot) -> selector_graph_build::binary_capture::Generated {
    use selector_graph_build::binary_capture::{CaptureOptions, generate};
    let word = facts.find_symbol("curriedcase/WordSuite#").unwrap();
    let context = facts.text(facts.symbols[word.index()].context).to_owned();
    let native: JsonValue =
        serde_json::from_slice(&std::fs::read(fixture().join("binary.json")).unwrap()).unwrap();
    let mut entries = Vec::new();
    let mut objects = Vec::new();
    let mut exported = None;
    for (index, entry) in native["contexts"][0]["entries"]
        .as_array()
        .unwrap()
        .iter()
        .enumerate()
    {
        let path = PathBuf::from(entry["path"].as_str().unwrap());
        let path = if path.is_absolute() {
            path
        } else {
            fixture().join(path)
        };
        let mut input = serde_json::json!({"index":index,"path":path,"sha256":entry["sha256"]});
        if index == 0 {
            // The fixture compiler emitted these exact own classes. The export
            // and context origin jointly authorize mapping a source class to
            // its actual generated JVM declarations; classpath presence alone
            // does not grant that authority.
            assert_eq!(path.file_name().unwrap(), "bytecode.jar");
            input["project_output_origins"] = serde_json::json!([{"context_id":context}]);
            exported = Some(serde_json::json!({"path":path,"sha256":entry["sha256"]}));
        }
        objects.push(
            serde_json::json!({"path":path,"kind":"file","sha256":entry["sha256"],
            "bytes":std::fs::metadata(&path).unwrap().len()}),
        );
        entries.push(input);
    }
    let temporary = tempfile::tempdir().unwrap();
    let contexts = temporary.path().join("compiler-contexts.json");
    std::fs::write(
        &contexts,
        serde_json::to_vec(&serde_json::json!({
            "schema_version":"sbt-compiler-context/v1", "revision":facts.text(facts.revision),
            "source_root":fixture(), "errors":[], "java_runtime":{"java_version":"21"},
            "contexts":[{"context_id":context,"full_classpath":entries,
                "exported_products":[exported.unwrap()]}], "input_objects":objects
        }))
        .unwrap(),
    )
    .unwrap();
    let generated = generate(
        &facts,
        &contexts,
        &fixture(),
        &CaptureOptions {
            workers: 2,
            ..Default::default()
        },
    )
    .unwrap();
    generated
}

#[test]
fn actual_exported_wordsuite_implements_an_exact_abstract_jvm_getter() {
    let mut facts = captured();
    let word = facts.find_symbol("curriedcase/WordSuite#").unwrap();
    let parent_targets = |facts: &FactSnapshot| {
        let mut parents: Vec<_> = facts
            .relations
            .iter()
            .filter(|relation| relation.source == word && relation.kind == RelationKind::Parent)
            .map(|relation| relation.target)
            .collect();
        parents.sort_unstable();
        parents
    };
    let parents_before = parent_targets(&facts);
    let context = facts.text(facts.symbols[word.index()].context).to_owned();
    let temporary = tempfile::tempdir().unwrap();
    let mut generated = generated_word_inputs(&facts);
    assert!(
        generated.manifest["types"].as_array().unwrap().iter().any(
            |mapping| mapping["compiler_symbol"] == "curriedcase/WordSuite#"
                && mapping["jvm_owner"] == "curriedcase/WordSuite"
        ),
        "an exact own-product declaration must bind the genuine source class"
    );
    let getter_name = "org$scalatest$matchers$should$Matchers$$ShouldMethodHelper";
    let getter_descriptor = "()Lorg/scalatest/matchers/should/Matchers$ShouldMethodHelperClass;";
    // This getter is independently visible in the frozen WordSuite javap output.
    // Explicitly request its real inherited abstract JVM contract. It is absent
    // from SemanticDB, so this metadata deliberately supplies no compiler ID or
    // invented source occurrence; the loader must verify the classfile ABI.
    generated.manifest["methods"]
        .as_array_mut()
        .unwrap()
        .push(serde_json::json!({
            "context":context, "jvm_owner":"org/scalatest/matchers/should/Matchers",
            "jvm_name":getter_name, "descriptor":getter_descriptor
        }));
    let binary = temporary.path().join("binary.json");
    std::fs::write(&binary, serde_json::to_vec(&generated.manifest).unwrap()).unwrap();
    let mut inputs = load_binary_manifest(&binary, &facts).unwrap();
    augment_binary_facts(&mut facts, &mut inputs).unwrap();
    assert_eq!(
        parent_targets(&facts),
        parents_before,
        "generated declarations must preserve compiler source parent relations"
    );
    let owner = "curriedcase/WordSuite";
    let name = getter_name;
    let descriptor = getter_descriptor;
    let identity = format!(
        "@jvm/{}:{owner}{}:{name}{}:{descriptor}",
        owner.len(),
        name.len(),
        descriptor.len()
    );
    let getter = facts
        .find_symbol(&identity)
        .expect("real public generated JVM getter");
    assert_eq!(facts.symbols[getter.index()].owner, word);
    let body = facts
        .bodies
        .iter()
        .find(|body| body.symbol == getter)
        .unwrap();
    assert_ne!(body.flags & BODY_BINARY_RECIPE, 0);
    let backing_field = facts.operations[body.operations.range()]
        .iter()
        .find(|op| {
            op.opcode == Opcode::LoadField
                && facts.symbols[op.target.index()].owner == word
                && facts.symbol_name(op.target).contains(name)
        })
        .expect("actual javap getter reads the receiver's exact generated backing field")
        .target;
    assert!(
        facts
            .relations
            .iter()
            .any(|relation| relation.source == getter
                && relation.kind == RelationKind::Override
                && facts.symbol_name(relation.target).contains(name)),
        "dispatch joins the inherited abstract contract by exact JVM descriptor"
    );
    // Matchers.$init$ discovers this setter while its native body is lowered;
    // unlike the otherwise-unused getter above, it was not an explicit root.
    // Admission must revisit newly discovered abstract contracts before sealing.
    let setter_name = "org$scalatest$matchers$should$Matchers$_setter_$org$scalatest$matchers$should$Matchers$$ShouldMethodHelper_$eq";
    let setter_descriptor = "(Lorg/scalatest/matchers/should/Matchers$ShouldMethodHelperClass;)V";
    let setter_identity = format!(
        "@jvm/{}:{owner}{}:{setter_name}{}:{setter_descriptor}",
        owner.len(),
        setter_name.len(),
        setter_descriptor.len()
    );
    let setter = facts
        .find_symbol(&setter_identity)
        .expect("real generated setter discovered through native initializer");
    assert_eq!(facts.symbols[setter.index()].owner, word);
    let setter_body = facts
        .bodies
        .iter()
        .find(|body| body.symbol == setter)
        .unwrap();
    assert_ne!(setter_body.flags & BODY_BINARY_RECIPE, 0);
    assert!(
        facts.operations[setter_body.operations.range()]
            .iter()
            .any(|op| op.opcode == Opcode::StoreField && op.target == backing_field),
        "actual generated setter writes the same receiver backing field"
    );
    assert!(
        facts
            .relations
            .iter()
            .any(|relation| relation.source == setter
                && relation.kind == RelationKind::Override
                && facts.symbol_name(relation.target).contains(setter_name))
    );
    // ABI-negative metadata: the real inherited getter does not return Object.
    // A same-name lookup must not invent a matching descriptor or own member.
    let mut wrong_manifest = generated.manifest.clone();
    let wrong_descriptor = "()Ljava/lang/Object;";
    wrong_manifest["methods"]
        .as_array_mut()
        .unwrap()
        .last_mut()
        .unwrap()["descriptor"] = wrong_descriptor.into();
    let wrong_path = temporary.path().join("wrong-getter.json");
    std::fs::write(&wrong_path, serde_json::to_vec(&wrong_manifest).unwrap()).unwrap();
    let mut wrong_facts = captured();
    let mut wrong_inputs = load_binary_manifest(&wrong_path, &wrong_facts).unwrap();
    augment_binary_facts(&mut wrong_facts, &mut wrong_inputs).unwrap();
    let wrong_identity = format!(
        "@jvm/{}:{owner}{}:{name}{}:{wrong_descriptor}",
        owner.len(),
        name.len(),
        wrong_descriptor.len()
    );
    assert!(
        wrong_facts.find_symbol(&wrong_identity).is_none(),
        "a forged same-name ABI cannot create a generated source-class method"
    );

    // Structural admission-negative overlay, not a second compiler capture:
    // retain the actual source-defined known() body but give its declaration
    // this member name on WordSuite. Even an unsupported/conflicting source
    // signature must win over an inferred generated implementation.
    let mut shadow_facts = captured();
    let custom = shadow_facts
        .find_symbol("curriedcase/SourceSuite#known().")
        .unwrap();
    let custom_body = *shadow_facts
        .bodies
        .iter()
        .find(|body| body.symbol == custom)
        .unwrap();
    let custom_name = format!("curriedcase/WordSuite#{name}().");
    let text = StrId(shadow_facts.strings.entries.len() as u32);
    shadow_facts.strings.entries.push(TextRange {
        start: shadow_facts.strings.bytes.len() as u64,
        len: custom_name.len() as u32,
    });
    shadow_facts
        .strings
        .bytes
        .extend_from_slice(custom_name.as_bytes());
    shadow_facts.symbols[custom.index()].name = text;
    shadow_facts.symbols[custom.index()].owner = word;
    assert_ne!(
        shadow_facts.symbols[custom.index()].flags & SYMBOL_DEFINED,
        0
    );
    let mut shadow_inputs = load_binary_manifest(&binary, &shadow_facts).unwrap();
    augment_binary_facts(&mut shadow_facts, &mut shadow_inputs).unwrap();
    assert!(
        shadow_facts.find_symbol(&identity).is_none(),
        "a source-defined member name blocks generated getter admission"
    );
    let retained = shadow_facts
        .bodies
        .iter()
        .find(|body| body.symbol == custom)
        .unwrap();
    assert_eq!(retained.body_hash, custom_body.body_hash);
    assert_eq!(retained.flags & BODY_BINARY_RECIPE, 0);
    assert!(
        shadow_facts.operations[retained.operations.range()]
            .iter()
            .any(|op| shadow_facts.symbol_name(op.target) == "curriedcase/Effects.note()."),
        "the original source-defined effect body remains intact"
    );
}

#[test]
fn actual_wordsuite_uses_declared_property_slots_and_allocated_registration_body() {
    use selector_models::binary::{self, CapturedClasspath, ClasspathEntry, EntryKind};
    let mut facts = captured();
    let word = facts.find_symbol("curriedcase/WordSuite#").unwrap();
    let source_parents = |facts: &FactSnapshot| {
        facts
            .relations
            .iter()
            .filter(|relation| relation.source == word && relation.kind == RelationKind::Parent)
            .map(|relation| relation.target)
            .collect::<Vec<_>>()
    };
    let parents_before = source_parents(&facts);
    let generated = generated_word_inputs(&facts);
    let temporary = tempfile::tempdir().unwrap();
    let augment = |facts: &mut FactSnapshot, manifest: &JsonValue, name: &str| {
        let path = temporary.path().join(name);
        std::fs::write(&path, serde_json::to_vec(manifest).unwrap()).unwrap();
        let mut inputs = load_binary_manifest(&path, facts).unwrap();
        augment_binary_facts(facts, &mut inputs).unwrap();
    };
    let identity = |owner: &str, name: &str, descriptor: &str| {
        format!(
            "@jvm/{}:{owner}{}:{name}{}:{descriptor}",
            owner.len(),
            name.len(),
            descriptor.len()
        )
    };
    augment(&mut facts, &generated.manifest, "inherited.json");
    assert_eq!(source_parents(&facts), parents_before);
    // Under the declared-property contract, use the existing exact trait
    // getter identity. Optional concrete implementation admission is unnecessary.
    let owner = "org/scalatest/wordspec/AnyWordSpecLike";
    let getter_name = "subjectRegistrationFunction";
    let getter_descriptor = "()Lorg/scalatest/verbs/StringVerbBlockRegistration;";
    let getter_identity = "org/scalatest/wordspec/AnyWordSpecLike#subjectRegistrationFunction.";
    let getter = facts
        .find_symbol(getter_identity)
        .expect("exact compiler trait getter retained");
    let parent = facts
        .find_symbol("org/scalatest/wordspec/AnyWordSpecLike#")
        .unwrap();
    assert_eq!(facts.symbols[getter.index()].owner, parent);
    assert!(
        facts
            .find_symbol(&identity(
                "curriedcase/WordSuite",
                getter_name,
                getter_descriptor
            ))
            .is_none(),
        "the model does not invent an own source implementation"
    );
    let getter_body = facts
        .bodies
        .iter()
        .find(|body| body.symbol == getter)
        .unwrap();
    assert_ne!(getter_body.flags & BODY_BINARY_RECIPE, 0);
    let field = facts.operations[getter_body.operations.range()]
        .iter()
        .find(|op| op.opcode == Opcode::LoadField)
        .unwrap()
        .target;
    assert_eq!(facts.symbols[field.index()].owner, parent);
    assert_eq!(
        facts.symbol_name(field),
        "@selector:accessor:org/scalatest/wordspec/AnyWordSpecLike:subjectRegistrationFunction"
    );
    assert_eq!(
        facts.symbols[field.index()].flags,
        0,
        "logical storage is not a JVM backing-field claim"
    );
    let setter_name =
        "org$scalatest$wordspec$AnyWordSpecLike$_setter_$subjectRegistrationFunction_$eq";
    let setter_descriptor = "(Lorg/scalatest/verbs/StringVerbBlockRegistration;)V";
    let setter = facts
        .find_symbol(&identity(owner, setter_name, setter_descriptor))
        .unwrap();
    assert_eq!(facts.symbols[setter.index()].owner, parent);
    let setter_body = facts
        .bodies
        .iter()
        .find(|body| body.symbol == setter)
        .unwrap();
    assert!(
        facts.operations[setter_body.operations.range()]
            .iter()
            .any(|op| op.opcode == Opcode::StoreField && op.target == field)
    );
    assert!(
        !facts.operations[setter_body.operations.range()]
            .iter()
            .any(|op| matches!(
                op.opcode,
                Opcode::Call | Opcode::VirtualCall | Opcode::InvokeCallback
            )),
        "storing a callback does not execute it"
    );
    // This historical no-JDK fixture does not assert whole-hierarchy closure.
    // The paired logical recipes are independent of optional native bodies;
    // unresolved ancestors retain their ordinary initialization/dispatch guards.

    // Compare provenance with the selected, checksum-admitted class bytes.
    let jar = generated.manifest["contexts"][0]["entries"]
        .as_array()
        .unwrap()
        .iter()
        .find(|entry| {
            entry["path"]
                .as_str()
                .unwrap()
                .contains("scalatest-wordspec_2.13-3.2.19.jar")
        })
        .unwrap();
    let mut loader = CapturedClasspath::new(
        vec![ClasspathEntry {
            path: PathBuf::from(jar["path"].as_str().unwrap()),
            sha256: ContentHash::from_hex(jar["sha256"].as_str().unwrap()).unwrap(),
            kind: EntryKind::Jar,
        }],
        binary::Limits::default(),
    )
    .unwrap()
    .with_java_feature(Some(21))
    .unwrap();
    let declared = loader.resolve(owner).unwrap();
    assert_eq!(
        facts.files[getter_body.file.index()].source_hash,
        declared.proof.class_hash.unwrap()
    );
    assert_eq!(
        facts.files[getter_body.file.index()].context,
        facts.symbols[word.index()].context
    );
    assert_eq!(getter_body.file, setter_body.file);

    // This particular class is allocated by the real native trait initializer;
    // discovering an arbitrary class with a matching method is insufficient.
    let registration_owner = "org/scalatest/wordspec/AnyWordSpecLike$$anon$1";
    let apply_descriptor =
        "(Ljava/lang/String;Ljava/lang/String;Lorg/scalactic/source/Position;Lscala/Function0;)V";
    let registration = facts
        .find_symbol(&identity(registration_owner, "<type>", ""))
        .unwrap();
    assert!(
        facts
            .operations
            .iter()
            .any(|op| op.opcode == Opcode::Allocate
                && !op.target.is_none()
                && (op.target == registration
                    || (facts.symbols[op.target.index()].kind == 21
                        && facts.symbols[op.target.index()].owner == registration)))
    );
    let apply = facts
        .find_symbol(&identity(registration_owner, "apply", apply_descriptor))
        .expect("actual allocated registration object's concrete apply body");
    assert_eq!(facts.symbols[apply.index()].owner, registration);
    let apply_body = facts
        .bodies
        .iter()
        .find(|body| body.symbol == apply)
        .unwrap();
    assert_ne!(apply_body.flags & BODY_BINARY_RECIPE, 0);
    assert!(
        facts.operations[apply_body.operations.range()]
            .iter()
            .any(|op| matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)),
        "retain ordinary registration effects rather than declaring this native body pure"
    );
    let abstract_apply = identity(
        "org/scalatest/verbs/StringVerbBlockRegistration",
        "apply",
        apply_descriptor,
    );
    assert!(
        facts
            .relations
            .iter()
            .any(|relation| relation.kind == RelationKind::Override
                && relation.source == apply
                && facts.symbol_name(relation.target) == abstract_apply)
    );
    let class = loader.resolve(registration_owner).unwrap();
    assert_eq!(
        facts.files[apply_body.file.index()].source_hash,
        class.proof.class_hash.unwrap()
    );

    // Wrong-descriptor metadata cannot authorize a same-name implementation.
    let mut wrong = generated.manifest.clone();
    let wrong_descriptor = "()Ljava/lang/Object;";
    let row = wrong["methods"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|row| {
            row["compiler_symbol"]
                == "org/scalatest/wordspec/AnyWordSpecLike#subjectRegistrationFunction."
        })
        .unwrap();
    row["descriptor"] = wrong_descriptor.into();
    let mut wrong_facts = captured();
    augment(&mut wrong_facts, &wrong, "wrong-inherited.json");
    assert!(
        wrong_facts
            .find_symbol(&identity(owner, getter_name, wrong_descriptor))
            .is_none()
    );

    // An opaque prefix before the hierarchy bytes must block later lookup.
    let mut unavailable = generated.manifest.clone();
    unavailable["contexts"][0]["entries"]
        .as_array_mut()
        .unwrap()
        .insert(
            1,
            serde_json::json!({"path":"unavailable-superclasses.jar","kind":"unavailable"}),
        );
    let mut unavailable_facts = captured();
    augment(
        &mut unavailable_facts,
        &unavailable,
        "unavailable-inherited.json",
    );
    assert!(!unavailable_facts.bodies.iter().any(|body| {
        body.symbol == unavailable_facts.find_symbol(getter_identity).unwrap()
            && unavailable_facts.operations[body.operations.range()]
                .iter()
                .any(|op| {
                    op.opcode == Opcode::LoadField
                        && !op.target.is_none()
                        && unavailable_facts
                            .symbol_name(op.target)
                            .starts_with("@selector:accessor:")
                })
    }));
    assert!(
        unavailable_facts
            .find_symbol(&identity(registration_owner, "apply", apply_descriptor))
            .is_none()
    );

    // Structural source-overlay control: preserve the actual custom source body
    // when a source-defined same-name declaration makes inherited admission unsafe.
    let mut custom_facts = captured();
    let custom = custom_facts
        .find_symbol("curriedcase/SourceSuite#known().")
        .unwrap();
    let custom_body = *custom_facts
        .bodies
        .iter()
        .find(|body| body.symbol == custom)
        .unwrap();
    let spelling = "curriedcase/WordSuite#subjectRegistrationFunction().";
    let name = StrId(custom_facts.strings.entries.len() as u32);
    custom_facts.strings.entries.push(TextRange {
        start: custom_facts.strings.bytes.len() as u64,
        len: spelling.len() as u32,
    });
    custom_facts
        .strings
        .bytes
        .extend_from_slice(spelling.as_bytes());
    custom_facts.symbols[custom.index()].name = name;
    custom_facts.symbols[custom.index()].owner = word;
    augment(
        &mut custom_facts,
        &generated.manifest,
        "custom-inherited.json",
    );
    let retained = custom_facts
        .bodies
        .iter()
        .find(|body| body.symbol == custom)
        .unwrap();
    assert!(
        !custom_facts.relations.iter().any(|relation| relation.kind
            == RelationKind::KnownReceiverDispatch
            && relation.source == word
            && relation.target == getter),
        "source custom override blocks trusted coverage"
    );
    assert!(
        custom_facts
            .relations
            .iter()
            .any(|relation| relation.kind == RelationKind::DeferredDispatch
                && relation.source == word
                && relation.target == getter),
        "an unbound custom source override cannot fall back to the trait model"
    );
    let custom_graph = selector_graph_build::build(&custom_facts, &Default::default()).unwrap();
    assert!(
        custom_graph
            .edges
            .iter()
            .any(|edge| edge.kind == EdgeKind::Guard
                && edge.flags & EDGE_DEFERRED_DISPATCH != 0
                && edge.receiver == word
                && !edge.operation.is_none()
                && custom_facts.operations[edge.operation.index()].target == getter),
        "the open override frontier is projected at the actual getter operation"
    );
    assert_eq!(retained.body_hash, custom_body.body_hash);
    assert_eq!(retained.flags & BODY_BINARY_RECIPE, 0);
    assert!(
        custom_facts.operations[retained.operations.range()]
            .iter()
            .any(|op| custom_facts.symbol_name(op.target) == "curriedcase/Effects.note().")
    );
    assert!(
        custom_facts
            .find_symbol(&identity(
                "curriedcase/WordSuite",
                getter_name,
                getter_descriptor
            ))
            .is_none()
    );
}
