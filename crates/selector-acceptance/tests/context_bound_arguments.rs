//! Genuine context-bound/default clauses and compiler implicit wrappers. JVM
//! observations are independent; normalized metadata perturbations are negative controls.
use selector_extract::{ExtractOptions, import_capture};
use selector_facts::{BodyRecord, FactSnapshot, OperationRecord};
use selector_types::*;
use std::path::{Path, PathBuf};

const PARAM: &str = "contextboundcase/Api.param().";
const EVIDENCE: &str = "contextboundcase/Api.param().(evidence$1)";
const WRAPPER: &str = "contextboundcase/Syntax.RenderOps().";
fn directory() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/context-bound-arguments")
}
fn captured_from(documents: &Path) -> FactSnapshot {
    import_capture(
        documents,
        Some(&directory().join("syntax.jsonl")),
        &ExtractOptions {
            workers: 2,
            ..Default::default()
        },
    )
    .unwrap()
}
fn captured() -> FactSnapshot {
    captured_from(&directory().join("documents.jsonl"))
}
fn body<'a>(facts: &'a FactSnapshot, symbol: &str) -> &'a BodyRecord {
    let id = facts.find_symbol(symbol).unwrap();
    facts.bodies.iter().find(|body| body.symbol == id).unwrap()
}
fn ops<'a>(facts: &'a FactSnapshot, body: &BodyRecord) -> &'a [OperationRecord] {
    &facts.operations[body.operations.range()]
}
fn callback<'a>(facts: &'a FactSnapshot, parent: &str) -> &'a BodyRecord {
    let outer = body(facts, parent);
    // A written local val has its own source initializer; follow only the
    // exact Initialize endpoint within this same verified method envelope.
    let mut owners = vec![outer];
    for op in ops(facts, outer) {
        if op.opcode == Opcode::Initialize {
            if let Some(inner) = facts.bodies.iter().find(|body| {
                body.symbol == op.target
                    && body.file == outer.file
                    && outer.span.contains(body.span)
            }) {
                owners.push(inner);
            }
        }
    }
    let target = owners
        .iter()
        .find_map(|owner| {
            ops(facts, owner)
                .iter()
                .find(|op| op.opcode == Opcode::BindCallback)
                .map(|op| op.target)
        })
        .unwrap_or_else(|| {
            panic!(
                "{parent}: missing callback in local initializer; bodies {:?}",
                owners
                    .iter()
                    .map(|owner| (
                        facts.symbol_name(owner.symbol),
                        ops(facts, owner)
                            .iter()
                            .map(|op| (op.opcode, facts.symbol_name(op.target), op.arguments.len))
                            .collect::<Vec<_>>()
                    ))
                    .collect::<Vec<_>>()
            )
        });
    facts
        .bodies
        .iter()
        .find(|body| body.symbol == target)
        .unwrap()
}
#[test]
fn genuine_jvm_default_evidence_and_deferred_execution_observations_are_frozen() {
    for (mode, expected) in [
        ("omitted", "created:1:0:0\ninvoked:10:1:1:2\n"),
        ("explicit", "created:0:0:0\ninvoked:10:0:1:2\n"),
        ("named", "created:1:0:0\ninvoked:10:1:1:2\n"),
        ("evidence", "created:1:0:0\ninvoked:15:1:1:3\n"),
        ("never", "created:1:0:0\n"),
        ("immediate", "immediate:21:1:1:3\n"),
        ("lambda-named", "lambda-named:6:0:1:2\n"),
        ("lambda-placeholder", "lambda-placeholder:6:0:1:2\n"),
    ] {
        assert_eq!(
            std::fs::read_to_string(directory().join(format!("{mode}.log"))).unwrap(),
            expected
        );
    }
    let javap = std::fs::read_to_string(directory().join("javap.log")).unwrap();
    assert!(javap.contains("(Ljava/lang/String;Lscala/Function1;Lscala/Function1;Lcontextboundcase/Render;)Lscala/Function1;"));
}
#[test]
fn generated_evidence_is_a_fourth_formal_and_a_real_deferred_capture() {
    let facts = captured();
    let method = body(&facts, PARAM);
    assert_eq!(
        method.parameters.len, 4,
        "compiler signature declares three written arguments plus generated evidence"
    );
    let parameters: Vec<_> = ops(&facts, method)
        .iter()
        .filter(|op| op.opcode == Opcode::Parameter && op.flags & 1 == 0)
        .map(|op| facts.symbol_name(op.target))
        .collect();
    assert_eq!(
        parameters,
        [
            "contextboundcase/Api.param().(name)",
            "contextboundcase/Api.param().(get)",
            "contextboundcase/Api.param().(cond)",
            EVIDENCE
        ]
    );
    let evidence = facts.find_symbol(EVIDENCE).unwrap();
    let deferred = callback(&facts, PARAM);
    let formal = ops(&facts, method)
        .iter()
        .find(|op| op.opcode == Opcode::Parameter && op.target == evidence && op.flags & 1 == 0)
        .unwrap();
    let binding = ops(&facts, method)
        .iter()
        .find(|op| op.opcode == Opcode::BindCallback && op.target == deferred.symbol)
        .unwrap();
    assert!(
        facts.operands[binding.arguments.range()].contains(&formal.dest),
        "the actual BindCallback capture operand forwards the generated formal"
    );
    assert!(
        ops(&facts, deferred)
            .iter()
            .any(|op| op.opcode == Opcode::Parameter && op.flags & 1 != 0 && op.target == evidence),
        "compiler-generated evidence is captured like other lexical formals"
    );
    assert!(
        !facts
            .operations
            .iter()
            .any(|op| op.opcode == Opcode::LoadField && op.target == evidence),
        "an evidence formal is not a field on this"
    );
}
#[test]
fn defaults_and_inserted_or_explicit_implicits_fill_exactly_four_actuals() {
    let facts = captured();
    let target = facts.find_symbol(PARAM).unwrap();
    for (name, default) in [
        ("omitted", true),
        ("explicitCondition", false),
        ("namedArguments", true),
        ("explicitEvidence", true),
        ("immediatelyApplied", true),
    ] {
        let caller = format!("contextboundcase/Calls.{name}().");
        let operations = ops(&facts, body(&facts, &caller));
        let calls: Vec<_> = operations
            .iter()
            .filter(|op| {
                op.target == target && matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
            })
            .collect();
        assert_eq!(calls.len(), 1, "{name}: exactly one factory call");
        assert_eq!(
            calls[0].arguments.len, 4,
            "{name}: generated evidence fills the fourth formal, never a fifth argument"
        );
        let defaults: Vec<_> = operations
            .iter()
            .filter(|op| {
                !op.target.is_none()
                    && facts.symbol_name(op.target) == "contextboundcase/Api.param$default$3()."
            })
            .collect();
        assert_eq!(
            defaults.len(),
            usize::from(default),
            "{name}: actual generated default call count; operations {:?}",
            operations
                .iter()
                .map(|op| (
                    op.opcode,
                    facts.symbol_name(op.target),
                    op.arguments.len,
                    op.dest.0
                ))
                .collect::<Vec<_>>()
        );
        assert!(
            defaults.iter().all(|op| op.arguments.len == 0),
            "the compiler's default getter has no value parameters"
        );
        if name == "immediatelyApplied" {
            assert!(
                operations
                    .iter()
                    .any(|op| op.opcode == Opcode::InvokeCallback),
                "application beyond both declared clauses invokes the returned function"
            );
        }
    }
}
#[test]
fn named_and_placeholder_lambdas_each_use_the_compiler_implicit_wrapper_once() {
    let facts = captured();
    let wrapper = facts.find_symbol(WRAPPER).unwrap();
    for (name, evidence) in [("named", "evidence$2"), ("placeholder", "evidence$3")] {
        let parent = format!("contextboundcase/Api.{name}().");
        let deferred = callback(&facts, &parent);
        let operations = ops(&facts, deferred);
        let wrappers: Vec<_> = operations
            .iter()
            .filter(|op| {
                op.target == wrapper && matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
            })
            .collect();
        assert_eq!(
            wrappers.len(),
            1,
            "{name}: actual compiler conversion runs once within the deferred body; operations {:?}",
            operations
                .iter()
                .map(|op| (
                    op.opcode,
                    facts.symbol_name(op.target),
                    op.arguments.len,
                    op.a.0,
                    op.dest.0
                ))
                .collect::<Vec<_>>()
        );
        assert_eq!(
            wrappers[0].arguments.len, 2,
            "written receiver and compiler-inserted evidence"
        );
        let evidence = facts.find_symbol(&format!("{parent}({evidence})")).unwrap();
        let captured = operations
            .iter()
            .find(|op| op.opcode == Opcode::Parameter && op.target == evidence && op.flags & 1 != 0)
            .expect("exact captured evidence parameter");
        assert!(facts.operands[wrappers[0].arguments.range()].contains(&captured.dest));
        let outer = body(&facts, &parent);
        let formal = ops(&facts, outer)
            .iter()
            .find(|op| op.opcode == Opcode::Parameter && op.target == evidence && op.flags & 1 == 0)
            .unwrap();
        let (initialize, local) = ops(&facts, outer)
            .iter()
            .filter(|op| op.opcode == Opcode::Initialize)
            .find_map(|op| {
                facts
                    .bodies
                    .iter()
                    .find(|body| {
                        body.symbol == op.target
                            && body.file == outer.file
                            && outer.span.contains(body.span)
                            && ops(&facts, body).iter().any(|binding| {
                                binding.opcode == Opcode::BindCallback
                                    && binding.target == deferred.symbol
                            })
                    })
                    .map(|local| (op, local))
            })
            .expect("actual local-val initializer producing the deferred callback");
        assert!(
            facts.operands[initialize.arguments.range()].contains(&formal.dest),
            "{name}: Initialize.arguments forwards the method's actual evidence value"
        );
        let local_capture = ops(&facts, local)
            .iter()
            .find(|op| op.opcode == Opcode::Parameter && op.target == evidence && op.flags & 1 != 0)
            .expect("local initializer's lexical evidence parameter");
        let binding = ops(&facts, local)
            .iter()
            .find(|op| op.opcode == Opcode::BindCallback && op.target == deferred.symbol)
            .unwrap();
        assert!(
            facts.operands[binding.arguments.range()].contains(&local_capture.dest),
            "{name}: BindCallback.arguments forwards evidence from the intervening initializer"
        );
    }
}

fn factory_analysis(facts: &FactSnapshot) -> (selector_result::AnalysisResult, NodeId) {
    factory_analysis_at(facts, "explicitCondition")
}
fn factory_analysis_at(
    facts: &FactSnapshot,
    method: &str,
) -> (selector_result::AnalysisResult, NodeId) {
    let graph = selector_graph_build::build(
        facts,
        &selector_graph_build::BuildOptions {
            workers: 2,
            include_models: false,
        },
    )
    .unwrap();
    let symbol = facts
        .find_symbol(&format!("contextboundcase/Calls.{method}()."))
        .unwrap();
    let root = graph.node_for_symbol(symbol).unwrap();
    let receiver = facts.find_symbol("contextboundcase/Calls.").unwrap();
    let options = selector_solve::SolveOptions {
        workers: 2,
        memory_budget_bytes: 64 * 1024 * 1024,
        max_contexts: 10_000,
        max_steps: 1_000_000,
        execution_roots: Some(
            vec![selector_solve::ExecutionRoot {
                node: root,
                receiver,
            }]
            .into(),
        ),
        ..Default::default()
    };
    let result = selector_solve::analyze(facts, &graph, &[], &options).unwrap();
    assert_ne!(result.completion, Completion::ResourceLimited);
    (result, root)
}
#[test]
fn missing_or_duplicate_generated_formal_metadata_cannot_admit_a_closed_factory() {
    let original = captured();
    let (baseline, _) = factory_analysis(&original);
    assert!(
        baseline.guarded_roots.is_empty(),
        "complete compiler formals provide a closed factory control: {:?}",
        baseline.evidence.guard_causes
    );
    for mode in [
        "missing-evidence-info",
        "duplicate-evidence-slot",
        "same-count-clause-conflict",
        "missing-implicit-authority",
    ] {
        let mut document: serde_json::Value =
            serde_json::from_slice(&std::fs::read(directory().join("documents.jsonl")).unwrap())
                .unwrap();
        let symbols = document["document"]["symbols"].as_array_mut().unwrap();
        if mode == "missing-evidence-info" {
            symbols.retain(|symbol| symbol["symbol"] != EVIDENCE);
        } else if mode == "missing-implicit-authority" {
            let evidence = symbols
                .iter_mut()
                .find(|symbol| symbol["symbol"] == EVIDENCE)
                .unwrap();
            evidence["properties"] = 0.into();
        } else {
            let method = symbols
                .iter_mut()
                .find(|symbol| symbol["symbol"] == PARAM)
                .unwrap();
            let clauses = &mut method["signature"]["method_signature"]["parameter_lists"];
            if mode == "duplicate-evidence-slot" {
                clauses[1]["symlinks"]
                    .as_array_mut()
                    .unwrap()
                    .push(EVIDENCE.into());
            } else {
                clauses[0]["symlinks"][2] = EVIDENCE.into();
                clauses[1]["symlinks"][0] = "contextboundcase/Api.param().(cond)".into();
            }
        }
        // Explicit admission-negative perturbations of compiler metadata. The
        // independently pinned source and syntax are unchanged; these documents
        // are not represented as genuine newly emitted compiler output.
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("documents.jsonl");
        std::fs::write(&path, serde_json::to_vec(&document).unwrap()).unwrap();
        let facts = import_capture(
            &path,
            Some(&directory().join("syntax.jsonl")),
            &ExtractOptions {
                workers: 2,
                ..Default::default()
            },
        );
        match facts {
            Err(_) => {} // Hard admission rejection also prevents exclusion authority.
            Ok(facts) => {
                let caller = body(&facts, "contextboundcase/Calls.explicitCondition().");
                assert!(
                    ops(&facts, caller).iter().any(|op| !op.target.is_none()
                        && facts.symbol_name(op.target) == "contextboundcase/Evidence.first."),
                    "{mode}: compiler-inserted provider evaluation is preserved when its tail proof is rejected"
                );
                let (result, root) = factory_analysis(&facts);
                assert!(
                    result.guarded_roots.contains(&root),
                    "{mode}: incomplete/ambiguous formal metadata must retain execution uncertainty"
                );
            }
        }
    }
}

#[test]
fn public_query_reaches_actual_defaults_and_render_effects_only_after_callback_invocation() {
    let mut facts = captured();
    selector_graph_build::source_recipes::augment_source_recipes(&mut facts).unwrap();
    let mut manifest: serde_json::Value =
        serde_json::from_slice(&std::fs::read(directory().join("binary.json")).unwrap()).unwrap();
    let context = "project:context-bound-arguments/configuration:test";
    // Explicit cross-member adapter bindings, checked against the genuine class
    // descriptors by ordinary admission. These connect generated bytecode to
    // existing source-owned bodies; they do not supply a pure-effect contract.
    manifest["methods"].as_array_mut().unwrap().extend([
        serde_json::json!({"context":context,"compiler_symbol":"contextboundcase/Api.defaultCond().",
            "jvm_owner":"contextboundcase/Api$","jvm_name":"defaultCond","descriptor":"()Lscala/Function1;"}),
        serde_json::json!({"context":context,"compiler_symbol":"contextboundcase/Syntax.RenderOps#",
            "jvm_owner":"contextboundcase/Syntax$RenderOps","jvm_name":"<init>",
            "descriptor":"(Ljava/lang/Object;Lcontextboundcase/Render;)V"}),
    ]);
    for entry in manifest["contexts"][0]["entries"].as_array_mut().unwrap() {
        let path = PathBuf::from(entry["path"].as_str().unwrap());
        if !path.is_absolute() {
            entry["path"] = directory().join(path).to_str().unwrap().into();
        }
    }
    let temporary = tempfile::tempdir().unwrap();
    let path = temporary.path().join("binary.json");
    std::fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    let mut native =
        selector_graph_build::binary_inputs::load_binary_manifest(&path, &facts).unwrap();
    selector_graph_build::binary_inputs::augment_binary_facts(&mut facts, &mut native).unwrap();
    let graph = selector_graph_build::build(
        &facts,
        &selector_graph_build::BuildOptions {
            workers: 2,
            include_models: false,
        },
    )
    .unwrap();
    let node = |symbol: &str| {
        graph
            .node_for_symbol(facts.find_symbol(symbol).unwrap())
            .unwrap()
    };
    let receiver = facts.find_symbol("contextboundcase/Calls.").unwrap();
    let reached = |root_name: &str, target: &str| {
        let root = node(&format!("contextboundcase/Calls.{root_name}()."));
        let options = selector_solve::SolveOptions {
            workers: 2,
            memory_budget_bytes: 128 * 1024 * 1024,
            max_contexts: 20_000,
            max_steps: 2_000_000,
            execution_roots: Some(
                vec![selector_solve::ExecutionRoot {
                    node: root,
                    receiver,
                }]
                .into(),
            ),
            ..Default::default()
        };
        let result = selector_solve::analyze(&facts, &graph, &[node(target)], &options).unwrap();
        assert_ne!(result.completion, Completion::ResourceLimited);
        result.contains(root)
    };
    assert!(reached(
        "omitted",
        "contextboundcase/Effects.defaultMade()."
    ));
    assert!(!reached(
        "explicitCondition",
        "contextboundcase/Effects.defaultMade()."
    ));
    for root in ["omitted", "explicitCondition"] {
        assert!(
            !reached(root, "contextboundcase/Effects.rendered()."),
            "{root}: creating a deferred callback does not render"
        );
    }
    for root in ["immediatelyApplied", "renderedNamed", "renderedPlaceholder"] {
        assert!(
            reached(root, "contextboundcase/Effects.rendered()."),
            "{root}: actual callback invocation retains the renderer effect"
        );
    }
}

#[test]
fn historical_unsupported_ast_remains_guarded_while_current_exporter_binds_the_exact_default() {
    let historical = import_capture(
        &directory().join("documents.jsonl"),
        Some(&directory().join("historical-syntax.jsonl")),
        &ExtractOptions {
            workers: 2,
            ..Default::default()
        },
    )
    .unwrap();
    let getter = "contextboundcase/Api.param$default$3().";
    let before = body(&historical, getter);
    assert!(
        ops(&historical, before)
            .iter()
            .any(|op| op.opcode == Opcode::Unknown)
    );
    assert!(
        historical
            .issues
            .iter()
            .any(|issue| issue.symbol == before.symbol
                && historical.text(issue.detail) == "unsupported_result_expression:Term.ApplyType")
    );
    let (result, root) = factory_analysis_at(&historical, "omitted");
    assert!(
        result.guarded_roots.contains(&root),
        "legacy exporter opacity cannot provide execution absence authority"
    );
    let current = captured();
    let actual = current
        .find_symbol("contextboundcase/Api.defaultCond().")
        .unwrap();
    let after = ops(&current, body(&current, getter));
    assert!(
        after
            .iter()
            .any(|op| op.opcode == Opcode::Call && op.target == actual && op.arguments.len == 0)
    );
    assert!(!after.iter().any(|op| op.opcode == Opcode::Unknown));
    // The independent public-query test proves actual defaultMade reachability
    // and deferred render behavior. This does not erase unrelated native/data
    // guards or assume completeness from the older unsupported AST.
}
