//! Normalized protocol callers over the actual pinned WordSpec accessor ABI.
//! Native admission/materialization is real; these callers are engine controls,
//! not a new JVM-executed CI catalogue or an isolation claim.
//! The unrelated empty protocol root has no admitted ScalaTest ancestry and
//! stays Unknown/UnsupportedModel; these controls make no suite-exclusion claim.
use selector_facts::{
    BodyRecord, FactBuilder, FactSnapshot, FileRecord, OperationRecord, RelationRecord, SuiteRecord,
};
use selector_graph::ProgramGraph;
use selector_graph_build::binary_inputs::{augment_binary_facts, load_binary_manifest};
use selector_plan::{CandidatePlan, PlanSeeds, plan_guarded_with_semantics};
use selector_result::{AnalysisResult, SuiteDecisionStatus};
use selector_select::{changed_seeds, select_with_plan};
use selector_solve::{AnalysisSeeds, ExecutionRoot, QuerySession, SolveOptions};
use selector_types::*;

const OWNER: &str = "org/scalatest/wordspec/AnyWordSpecLike#";
const JVM_OWNER: &str = "org/scalatest/wordspec/AnyWordSpecLike";
const GET: &str = "org/scalatest/wordspec/AnyWordSpecLike#subjectRegistrationFunction.";
const SET_NAME: &str =
    "org$scalatest$wordspec$AnyWordSpecLike$_setter_$subjectRegistrationFunction_$eq";
const SET: &str = "org/scalatest/wordspec/AnyWordSpecLike#org$scalatest$wordspec$AnyWordSpecLike$_setter_$subjectRegistrationFunction_$eq().";
const VALUE_DESC: &str = "Lorg/scalatest/verbs/StringVerbBlockRegistration;";
const SLOT: &str =
    "@selector:accessor:org/scalatest/wordspec/AnyWordSpecLike:subjectRegistrationFunction";

#[derive(Clone, Copy)]
enum Mode {
    Stored,
    Uninitialized,
    Custom,
}
struct Fixture {
    b: FactBuilder,
    context: StrId,
    file: FileId,
}
impl Fixture {
    fn symbol(&mut self, name: &str, kind: u32, owner: SymbolId, defined: bool) -> SymbolId {
        let id = self.b.ensure_symbol(name, self.file).unwrap();
        let s = &mut self.b.facts.symbols[id.index()];
        s.kind = kind;
        s.owner = owner;
        s.context = self.context;
        // External ABI endpoints belong to the captured compiler context, not
        // to the caller's source file. Native admission supplies their binary
        // provenance; attaching them to the dirty source falsely makes native
        // admission issues unscoped source-capture failures.
        s.file = if defined { self.file } else { FileId::NONE };
        s.flags = if defined { SYMBOL_DEFINED } else { 0 };
        if defined && matches!(kind, 13 | 14) {
            s.flags |= SYMBOL_SCALA_PARENTS_COMPLETE;
        }
        id
    }
    fn body(
        &mut self,
        symbol: SymbolId,
        flags: u32,
        parameters: &[ValueId],
        rows: Vec<(OperationRecord, Vec<ValueId>)>,
        hash: u8,
    ) {
        let body = BodyId(self.b.facts.bodies.len() as u32);
        let pstart = self.b.facts.operands.len() as u32;
        self.b.facts.operands.extend_from_slice(parameters);
        let start = self.b.facts.operations.len() as u32;
        for (mut row, args) in rows {
            row.body = body;
            row.arguments = IdRange {
                start: self.b.facts.operands.len() as u32,
                len: args.len() as u32,
            };
            self.b.facts.operands.extend(args);
            self.b.facts.operations.push(row);
        }
        self.b.facts.bodies.push(BodyRecord {
            symbol,
            file: self.file,
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange {
                start,
                len: self.b.facts.operations.len() as u32 - start,
            },
            parameters: IdRange {
                start: pstart,
                len: parameters.len() as u32,
            },
            body_hash: ContentHash([hash; 32]),
            flags,
        });
    }
}
fn op(opcode: Opcode) -> OperationRecord {
    OperationRecord {
        body: BodyId::NONE,
        opcode,
        target: SymbolId::NONE,
        dest: ValueId::NONE,
        a: ValueId::NONE,
        b: ValueId::NONE,
        arguments: IdRange::default(),
        span: Span::default(),
        flags: 0,
    }
}
fn call(target: SymbolId, dest: ValueId) -> OperationRecord {
    OperationRecord {
        target,
        dest,
        a: ValueId(0),
        ..op(Opcode::Call)
    }
}
fn callback(target: SymbolId) -> OperationRecord {
    OperationRecord {
        target,
        dest: ValueId(1),
        a: ValueId(0),
        ..op(Opcode::BindCallback)
    }
}

fn cohort(head: bool, mode: Mode, contexts: usize) -> (FactSnapshot, ProgramGraph) {
    let mut f = Fixture {
        b: FactBuilder::new(),
        context: StrId::NONE,
        file: FileId::NONE,
    };
    f.b.facts.revision =
        f.b.intern(if head {
            "accessor-head"
        } else {
            "accessor-base"
        })
        .unwrap();
    let mut context_rows = Vec::new();
    let mut types = Vec::new();
    let mut methods = Vec::new();
    let archive = serde_json::json!({
        "path": std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../fixtures/scalatest-execution/scalatest-wordspec_2.13-3.2.19.jar"),
        "sha256": "08050f3d05c72575cac29a1483185b443d5f9f34c1fcf80c683083330385ef93",
        "kind": "jar",
    });
    for index in 0..contexts {
        let context_name = format!("fixture:accessor-contract:{index}");
        f.context = f.b.intern(&context_name).unwrap();
        let path = f.b.intern(&format!("Accessor{index}.scala")).unwrap();
        let source =
            f.b.intern("// Explicit normalized protocol caller.\n")
                .unwrap();
        f.file = FileId(f.b.facts.files.len() as u32);
        f.b.facts.files.push(FileRecord {
            path,
            source,
            revision: f.b.facts.revision,
            context: f.context,
            source_hash: ContentHash([11; 32]),
            flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
        });
        let owner = f.symbol(OWNER, 14, SymbolId::NONE, false);
        let get = f.symbol(GET, 3, owner, false);
        let set = f.symbol(SET, 3, owner, false);
        f.b.facts.symbols[get.index()].properties = 4;
        f.b.facts.symbols[set.index()].properties = 4;
        let affected = f.symbol("accessorcase/AffectedSuite#", 13, SymbolId::NONE, true);
        let covered = f.symbol("accessorcase/CoveredSuite#", 13, SymbolId::NONE, true);
        let closed = f.symbol("accessorcase/ClosedSuite#", 13, SymbolId::NONE, true);
        for class in [affected, covered] {
            f.b.facts.relations.push(RelationRecord {
                source: class,
                target: owner,
                kind: RelationKind::Parent,
                file: f.file,
            });
        }
        let changed = f.symbol("accessorcase/changed().", 3, SymbolId::NONE, true);
        let safe = f.symbol("accessorcase/safe().", 3, SymbolId::NONE, true);
        f.body(
            changed,
            BODY_DEFERRED,
            &[],
            vec![],
            if head && index == 0 { 42 } else { 41 },
        );
        f.body(safe, BODY_DEFERRED, &[], vec![], 51);
        let (mut actual_get, mut actual_set) = (get, set);
        if matches!(mode, Mode::Custom) {
            actual_get = f.symbol(
                "accessorcase/AffectedSuite#subjectRegistrationFunction.",
                3,
                affected,
                true,
            );
            actual_set = f.symbol(
                "accessorcase/AffectedSuite#subjectRegistrationFunction_=().",
                3,
                affected,
                true,
            );
            f.body(
                actual_get,
                BODY_DEFERRED,
                &[],
                vec![
                    (call(changed, ValueId::NONE), vec![]),
                    (
                        OperationRecord {
                            a: ValueId(0),
                            ..op(Opcode::Return)
                        },
                        vec![],
                    ),
                ],
                61,
            );
            f.body(
                actual_set,
                BODY_DEFERRED,
                &[ValueId(1)],
                vec![
                    (
                        OperationRecord {
                            dest: ValueId(1),
                            ..op(Opcode::Parameter)
                        },
                        vec![],
                    ),
                    (call(changed, ValueId::NONE), vec![]),
                ],
                62,
            );
        }
        let mut rows = Vec::new();
        if !matches!(mode, Mode::Uninitialized) {
            rows.push((callback(changed), vec![]));
            rows.push((call(actual_set, ValueId::NONE), vec![ValueId(1)]));
        }
        rows.push((call(actual_get, ValueId(2)), vec![]));
        if !matches!(mode, Mode::Custom) {
            rows.push((
                OperationRecord {
                    a: ValueId(2),
                    ..op(Opcode::InvokeCallback)
                },
                vec![],
            ));
        }
        let affected_entry = f.symbol("accessorcase/AffectedSuite#exercise().", 3, affected, true);
        let covered_entry = f.symbol("accessorcase/CoveredSuite#exercise().", 3, covered, true);
        f.body(affected_entry, BODY_DEFERRED, &[], rows, 71);
        f.body(
            covered_entry,
            BODY_DEFERRED,
            &[],
            vec![
                (callback(safe), vec![]),
                (call(set, ValueId::NONE), vec![ValueId(1)]),
                (call(get, ValueId(2)), vec![]),
                (
                    OperationRecord {
                        a: ValueId(2),
                        ..op(Opcode::InvokeCallback)
                    },
                    vec![],
                ),
            ],
            72,
        );
        let mut initializer = vec![(call(affected_entry, ValueId::NONE), vec![])];
        if matches!(mode, Mode::Custom) {
            initializer.push((op(Opcode::Unknown), vec![]));
        }
        f.body(affected, BODY_INITIALIZER, &[], initializer, 73);
        f.body(
            covered,
            BODY_INITIALIZER,
            &[],
            vec![(call(covered_entry, ValueId::NONE), vec![])],
            74,
        );
        f.body(closed, BODY_INITIALIZER, &[], vec![], 75);
        for (class, name) in [
            (affected, "AffectedSuite"),
            (covered, "CoveredSuite"),
            (closed, "ClosedSuite"),
        ] {
            let name = f.b.intern(&format!("accessorcase.{index}.{name}")).unwrap();
            f.b.facts.suites.push(SuiteRecord {
                name,
                symbol: class,
                file: f.file,
                flags: 0,
            });
        }
        context_rows.push(serde_json::json!({"id":context_name,"entries":[archive.clone()]}));
        types.push(serde_json::json!({"context":context_name,"compiler_symbol":OWNER,"jvm_owner":JVM_OWNER}));
        methods.push(serde_json::json!({"context":context_name,"compiler_symbol":GET,"jvm_owner":JVM_OWNER,"jvm_name":"subjectRegistrationFunction","descriptor":format!("(){VALUE_DESC}")}));
        methods.push(serde_json::json!({"context":context_name,"compiler_symbol":SET,"jvm_owner":JVM_OWNER,"jvm_name":SET_NAME,"descriptor":format!("({VALUE_DESC})V")}));
    }
    let mut facts = f.b.finish().unwrap();
    let directory = tempfile::tempdir().unwrap();
    let manifest = serde_json::json!({"version":1,"revision":facts.text(facts.revision),"java_feature":21,"contexts":context_rows,"types":types,"methods":methods});
    let path = directory.path().join("binary.json");
    std::fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    let mut inputs = load_binary_manifest(&path, &facts).unwrap();
    augment_binary_facts(&mut facts, &mut inputs).unwrap();
    let graph = selector_graph_build::build(&facts, &Default::default()).unwrap();
    (facts, graph)
}

fn analysis(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    plan: &CandidatePlan,
    workers: usize,
) -> AnalysisResult {
    QuerySession::new(
        facts,
        graph,
        &SolveOptions {
            workers,
            max_contexts: 20_000,
            max_steps: 500_000,
            memory_budget_bytes: 64 * 1024 * 1024,
            execution_roots: Some(
                plan.roots
                    .iter()
                    .map(|r| ExecutionRoot {
                        node: r.node,
                        receiver: r.receiver,
                    })
                    .collect(),
            ),
            ..Default::default()
        },
    )
    .unwrap()
    .analyze_typed(AnalysisSeeds {
        execution: plan.execution_seeds(),
        declarations: plan.declaration_seeds(),
    })
    .unwrap()
}
fn selected(mode: Mode, contexts: usize, workers: usize) -> selector_result::SelectionResult {
    let (base, bg) = cohort(false, mode, contexts);
    let (head, hg) = cohort(true, mode, contexts);
    let seeds = changed_seeds(&base, &bg, &head, &hg, &["Accessor0.scala"]).unwrap();
    assert!(!seeds.conservative, "{:#?}", seeds.guard_causes);
    let make = |facts: &FactSnapshot,
                graph: &ProgramGraph,
                execution: &[NodeId],
                declarations: &[NodeId]| {
        plan_guarded_with_semantics(
            facts,
            graph,
            PlanSeeds {
                execution,
                declarations,
                unscoped: false,
            },
            &[],
            SuiteSemantics::Independent,
        )
        .unwrap()
    };
    let bp = make(&base, &bg, &seeds.base, &seeds.base_compile);
    let hp = make(&head, &hg, &seeds.head, &seeds.head_compile);
    let before = analysis(&base, &bg, &bp, workers);
    let after = analysis(&head, &hg, &hp, workers);
    assert_ne!(before.completion, Completion::ResourceLimited);
    assert_ne!(after.completion, Completion::ResourceLimited);
    select_with_plan(
        &base,
        &bg,
        &head,
        &hg,
        seeds,
        Some(before),
        after,
        Some(&bp),
        &hp,
    )
    .unwrap()
}

fn symbol_in(facts: &FactSnapshot, name: &str, index: usize) -> SymbolId {
    let context = format!("fixture:accessor-contract:{index}");
    SymbolId(
        facts
            .symbols
            .iter()
            .position(|symbol| {
                facts.text(symbol.name) == name && facts.text(symbol.context) == context
            })
            .unwrap() as u32,
    )
}

// Callable entries start with an explicit existing receiver; this intentionally
// does not certify the enclosing ScalaTest parent/trait initialization path.
fn entry_analysis(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    contexts: usize,
) -> (AnalysisResult, Vec<selector_issue::RuntimeIssueSite>) {
    let mut roots = Vec::new();
    for index in 0..contexts {
        for class in ["AffectedSuite", "CoveredSuite"] {
            roots.push(ExecutionRoot {
                node: graph
                    .node_for_symbol(symbol_in(
                        facts,
                        &format!("accessorcase/{class}#exercise()."),
                        index,
                    ))
                    .unwrap(),
                receiver: symbol_in(facts, &format!("accessorcase/{class}#"), index),
            });
        }
    }
    let options = SolveOptions {
        workers: 1,
        max_contexts: 20_000,
        max_steps: 500_000,
        memory_budget_bytes: 64 * 1024 * 1024,
        execution_roots: Some(roots.into()),
        ..Default::default()
    };
    let mut session = QuerySession::new(facts, graph, &options).unwrap();
    let result = session
        .analyze(&[graph
            .node_for_symbol(symbol_in(facts, "accessorcase/changed().", 0))
            .unwrap()])
        .unwrap();
    let sites = session
        .first_runtime_issue_sites()
        .map(|(_, _, site)| site)
        .collect();
    (result, sites)
}

fn assert_unsupported_framework_root(result: &selector_result::SelectionResult, index: usize) {
    let decision = &result.decisions[index];
    assert_eq!(decision.status, SuiteDecisionStatus::Unknown);
    assert!(decision.guarded);
    assert_ne!(decision.reasons & selector_result::DECISION_SCOPED_GUARD, 0);
    assert!(
        result.head.evidence.guard_causes.iter().any(|cause| {
            cause.root == decision.node
                && cause.node == decision.node
                && cause.kind == IssueKind::UnsupportedModel
                && cause.runtime.is_none()
        }),
        "the real unsupported-framework obligation remains attached to this root"
    );
}

#[test]
fn materialized_setter_getter_share_state_and_changed_callback_is_required() {
    let (facts, _) = cohort(false, Mode::Stored, 1);
    let get = facts.find_symbol(GET).unwrap();
    let set = facts.find_symbol(SET).unwrap();
    let getter = facts
        .bodies
        .iter()
        .find(|b| b.symbol == get)
        .expect("actual materialized getter");
    let setter = facts
        .bodies
        .iter()
        .find(|b| b.symbol == set)
        .expect("actual materialized setter");
    let read = facts.operations[getter.operations.range()]
        .iter()
        .find(|o| o.opcode == Opcode::LoadField)
        .expect("getter uses ordinary heap read");
    let write = facts.operations[setter.operations.range()]
        .iter()
        .find(|o| o.opcode == Opcode::StoreField)
        .expect("setter uses ordinary heap write");
    assert_eq!(read.target, write.target);
    assert_eq!(facts.symbol_name(read.target), SLOT);
    assert_eq!(read.a, ValueId(0));
    assert_eq!(write.a, ValueId(0));
    for workers in [1, 4] {
        let result = selected(Mode::Stored, 1, workers);
        assert_eq!(result.suite_semantics, SuiteSemantics::Independent);
        assert_eq!(result.decisions[0].status, SuiteDecisionStatus::Required);
        assert_ne!(result.decisions[1].status, SuiteDecisionStatus::Required);
        assert_unsupported_framework_root(&result, 2);
    }
}

#[test]
fn unset_value_is_unknown_data_and_invoking_it_remains_guarded() {
    let (facts, graph) = cohort(false, Mode::Uninitialized, 1);
    let (analysis, sites) = entry_analysis(&facts, &graph, 1);
    assert_ne!(analysis.completion, Completion::ResourceLimited);
    assert!(
        sites
            .iter()
            .any(|site| site.reason == selector_issue::RuntimeIssueReason::UnknownFieldValue)
    );
    assert!(
        sites
            .iter()
            .any(|site| site.reason == selector_issue::RuntimeIssueReason::UnknownCallbackValue)
    );
    let result = selected(Mode::Uninitialized, 1, 1);
    assert_eq!(result.decisions[0].status, SuiteDecisionStatus::Unknown);
    assert_unsupported_framework_root(&result, 2);
    assert!(
        !result.head.guarded_roots.is_empty(),
        "missing slot must not become empty callback"
    );
}

#[test]
fn custom_source_accessors_and_val_initializer_effects_are_preserved() {
    let (facts, graph) = cohort(false, Mode::Custom, 1);
    for name in [
        "accessorcase/AffectedSuite#subjectRegistrationFunction.",
        "accessorcase/AffectedSuite#subjectRegistrationFunction_=().",
    ] {
        let symbol = facts.find_symbol(name).unwrap();
        let body = facts.bodies.iter().find(|b| b.symbol == symbol).unwrap();
        assert!(
            facts.operations[body.operations.range()]
                .iter()
                .any(|o| o.opcode == Opcode::Call
                    && facts.symbol_name(o.target) == "accessorcase/changed().")
        );
        assert_eq!(body.flags, BODY_DEFERRED);
    }
    let suite = facts.find_symbol("accessorcase/AffectedSuite#").unwrap();
    let body = graph.nodes[graph.node_for_symbol(suite).unwrap().index()].body;
    assert!(
        facts.operations[facts.bodies[body.index()].operations.range()]
            .iter()
            .any(|o| o.opcode == Opcode::Unknown)
    );
    let result = selected(Mode::Custom, 1, 1);
    assert_eq!(result.decisions[0].status, SuiteDecisionStatus::Required);
    assert!(!result.head.guarded_roots.is_empty());
}

#[test]
fn identical_accessor_spellings_in_distinct_contexts_keep_distinct_slots() {
    let (facts, graph) = cohort(false, Mode::Stored, 2);
    let slots: Vec<_> = facts
        .symbols
        .iter()
        .enumerate()
        .filter(|(i, _)| facts.symbol_name(SymbolId(*i as u32)) == SLOT)
        .collect();
    assert_eq!(slots.len(), 2);
    assert_ne!(slots[0].1.context, slots[1].1.context);
    let (analysis, _) = entry_analysis(&facts, &graph, 2);
    let entry = |index, class| {
        graph
            .node_for_symbol(symbol_in(
                &facts,
                &format!("accessorcase/{class}#exercise()."),
                index,
            ))
            .unwrap()
    };
    assert!(analysis.contains(entry(0, "AffectedSuite")));
    for (index, class) in [
        (0, "CoveredSuite"),
        (1, "AffectedSuite"),
        (1, "CoveredSuite"),
    ] {
        assert!(
            !analysis.contains(entry(index, class)),
            "receiver/context-specific slots do not import the changed payload"
        );
    }
    let result = selected(Mode::Stored, 2, 1);
    assert_eq!(result.decisions[0].status, SuiteDecisionStatus::Required);
    for decision in &result.decisions[1..] {
        assert_ne!(decision.status, SuiteDecisionStatus::Required);
    }
}
