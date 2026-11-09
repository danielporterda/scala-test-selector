//! Admitted-IR protocol controls, with real hash-bound native scalar recipes.
//! The cohort is deliberately not presented as a JVM-executed ScalaTest capture.
//! A separate unchanged compiler capture below checks actual registration work.
use selector_facts::{
    BodyRecord, FactBuilder, FactSnapshot, FileRecord, OperationRecord, RelationRecord, SuiteRecord,
};
use selector_graph::ProgramGraph;
use selector_plan::{CandidatePlan, PlanSeeds, plan};
use selector_result::{AnalysisResult, DECISION_OPAQUE_SHARED_HEAP, SuiteDecisionStatus};
use selector_select::{ChangeSeeds, changed_seeds, select_with_plan};
use selector_solve::{AnalysisSeeds, ExecutionRoot, QuerySession, SolveOptions};
use selector_types::*;
use std::path::PathBuf;

const CONTEXT: &str = "fixture:scoped-deferred-dispatch";
const CHANGED: &str = "scopedcase/changed().";
const COVERED: &str = "scopedcase/Child#covered().";
const MISSING: &str = "scopedcase/Parent#other().";
const CHILD: &str = "scopedcase/Child#";
const SCALAR: &str = "envelopecase/Probe$Scalar";

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
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

struct Fixture {
    builder: FactBuilder,
    context: StrId,
}
impl Fixture {
    fn symbol(&mut self, name: &str, kind: u32, owner: SymbolId) -> SymbolId {
        let id = self.builder.ensure_symbol(name, FileId(0)).unwrap();
        let symbol = &mut self.builder.facts.symbols[id.index()];
        symbol.kind = kind;
        symbol.owner = owner;
        symbol.file = FileId(0);
        symbol.context = self.context;
        symbol.flags = SYMBOL_DEFINED;
        if matches!(kind, 10 | 13 | 14) {
            symbol.flags |= SYMBOL_SCALA_PARENTS_COMPLETE;
        }
        id
    }
    fn relation(&mut self, source: SymbolId, target: SymbolId, kind: RelationKind) {
        self.builder.facts.relations.push(RelationRecord {
            source,
            target,
            kind,
            file: FileId(0),
        });
    }
    fn body(&mut self, symbol: SymbolId, flags: u32, operations: &[OperationRecord]) {
        let id = BodyId(self.builder.facts.bodies.len() as u32);
        let start = self.builder.facts.operations.len() as u32;
        self.builder
            .facts
            .operations
            .extend(operations.iter().copied().map(|mut operation| {
                operation.body = id;
                operation
            }));
        self.builder.facts.bodies.push(BodyRecord {
            symbol,
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange {
                start,
                len: operations.len() as u32,
            },
            parameters: IdRange::default(),
            body_hash: ContentHash([3; 32]),
            flags,
        });
    }
    fn arguments(&mut self, values: &[ValueId]) -> IdRange {
        let start = self.builder.facts.operands.len() as u32;
        self.builder.facts.operands.extend_from_slice(values);
        IdRange {
            start,
            len: values.len() as u32,
        }
    }
}

fn cohort(head: bool, deferred_called_contract: bool) -> (FactSnapshot, ProgramGraph) {
    let mut builder = FactBuilder::new();
    let context = builder.intern(CONTEXT).unwrap();
    let path = builder.intern("AdmittedProtocol.scala").unwrap();
    let text = builder
        .intern(if head {
            "// Explicit admitted IR protocol: changed leaf revision 2.\n"
        } else {
            "// Explicit admitted IR protocol: changed leaf revision 1.\n"
        })
        .unwrap();
    builder.facts.revision = builder
        .intern(if head {
            "protocol-head"
        } else {
            "protocol-base"
        })
        .unwrap();
    builder.facts.files.push(FileRecord {
        path,
        source: text,
        revision: builder.facts.revision,
        context,
        source_hash: ContentHash([if head { 2 } else { 1 }; 32]),
        flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
    });
    let mut f = Fixture { builder, context };
    let changed = f.symbol(CHANGED, 3, SymbolId::NONE);
    let parent = f.symbol("scopedcase/Parent#", 13, SymbolId::NONE);
    let child = f.symbol(CHILD, 13, SymbolId::NONE);
    f.relation(child, parent, RelationKind::Parent);
    let covered = f.symbol(COVERED, 3, child);
    let other = f.symbol(MISSING, 3, parent);
    let register = f.symbol("scopedcase/register().", 3, SymbolId::NONE);
    let native_type = f.symbol("scopedcase/NativeScalar#", 13, SymbolId::NONE);
    let native = f.symbol("scopedcase/NativeScalar.disjointEntry().", 3, native_type);
    for symbol in [native_type, native] {
        f.builder.facts.symbols[symbol.index()].flags = 0;
        f.builder.facts.symbols[symbol.index()].file = FileId::NONE;
    }
    f.body(changed, BODY_DEFERRED, &[]);
    let changed_body = f.builder.facts.bodies.last_mut().unwrap();
    changed_body.body_hash = ContentHash([if head { 7 } else { 6 }; 32]);
    f.body(parent, BODY_INITIALIZER, &[]);
    f.body(child, BODY_INITIALIZER, &[]);
    f.body(other, BODY_DEFERRED, &[]);
    f.body(
        covered,
        BODY_DEFERRED,
        &[
            OperationRecord {
                target: native,
                dest: ValueId(1),
                ..op(Opcode::Call)
            },
            OperationRecord {
                a: ValueId(1),
                ..op(Opcode::Return)
            },
        ],
    );
    f.body(
        register,
        BODY_DEFERRED,
        &[
            OperationRecord {
                dest: ValueId(1),
                ..op(Opcode::Parameter)
            },
            OperationRecord {
                a: ValueId(1),
                ..op(Opcode::InvokeCallback)
            },
        ],
    );
    for (name, call) in [
        ("AffectedSuite", changed),
        ("CoveredSuite", covered),
        ("MissingOverrideSuite", other),
    ] {
        let suite = f.symbol(&format!("scopedcase/{name}#"), 13, SymbolId::NONE);
        let callback = f.symbol(&format!("scopedcase/{name}#registered()."), 3, suite);
        let suite_name = f.builder.intern(&format!("scopedcase.{name}")).unwrap();
        f.builder.facts.suites.push(SuiteRecord {
            name: suite_name,
            symbol: suite,
            file: FileId(0),
            flags: 0,
        });
        let arguments = f.arguments(&[ValueId(1)]);
        f.body(
            suite,
            BODY_INITIALIZER,
            &[
                OperationRecord {
                    target: callback,
                    dest: ValueId(1),
                    ..op(Opcode::BindCallback)
                },
                OperationRecord {
                    target: register,
                    arguments,
                    ..op(Opcode::RegisterTest)
                },
            ],
        );
        let operations = if call == changed {
            vec![OperationRecord {
                target: changed,
                ..op(Opcode::Call)
            }]
        } else {
            vec![
                OperationRecord {
                    target: child,
                    dest: ValueId(1),
                    ..op(Opcode::Allocate)
                },
                OperationRecord {
                    target: call,
                    a: ValueId(1),
                    ..op(Opcode::VirtualCall)
                },
            ]
        };
        f.body(callback, BODY_DEFERRED, &operations);
    }
    // The receiver's optional OTHER implementation was not admitted. A covered
    // call on the same receiver must not inherit an unconditional class guard.
    f.relation(child, other, RelationKind::DeferredDispatch);
    if !deferred_called_contract {
        // The negative control defers a contract which no registered body calls.
        let unused = f.symbol("scopedcase/Parent#unused().", 3, parent);
        f.body(unused, BODY_DEFERRED, &[]);
        let last = f.builder.facts.relations.last_mut().unwrap();
        last.target = unused;
    }
    let mut facts = f.builder.finish().unwrap();
    let directory = tempfile::tempdir().unwrap();
    let manifest: serde_json::Value = serde_json::from_slice(
        &std::fs::read(root().join("fixtures/native-envelope/manifest.json")).unwrap(),
    )
    .unwrap();
    let jar = manifest["files"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["path"] == "bytecode.jar")
        .unwrap();
    let binary = serde_json::json!({
        "version":1,"revision":facts.text(facts.revision),"java_feature":21,
        "contexts":[{"id":CONTEXT,"entries":[{"path":root().join("fixtures/native-envelope/bytecode.jar"),"sha256":jar["sha256"],"kind":"jar"}]}],
        "types":[{"context":CONTEXT,"compiler_symbol":"scopedcase/NativeScalar#","jvm_owner":SCALAR}],
        "methods":[{"context":CONTEXT,"compiler_symbol":"scopedcase/NativeScalar.disjointEntry().","jvm_owner":SCALAR,"jvm_name":"disjointEntry","descriptor":"()I"}]
    });
    let binary_path = directory.path().join("binary.json");
    std::fs::write(&binary_path, serde_json::to_vec(&binary).unwrap()).unwrap();
    let mut inputs =
        selector_graph_build::binary_inputs::load_binary_manifest(&binary_path, &facts).unwrap();
    selector_graph_build::binary_inputs::augment_binary_facts(&mut facts, &mut inputs).unwrap();
    let native_body = facts
        .bodies
        .iter()
        .find(|body| body.symbol == native)
        .unwrap();
    assert_ne!(
        native_body.flags & BODY_BINARY_RECIPE,
        0,
        "the covered path uses actual admitted class bytes"
    );
    let facts_path = directory.path().join("facts.bin");
    facts.identity = selector_facts::codec::write(&facts_path, &facts).unwrap();
    let graph = selector_graph_build::build(
        &facts,
        &selector_graph_build::BuildOptions {
            workers: 1,
            include_models: false,
        },
    )
    .unwrap();
    (facts, graph)
}

fn planned_analysis(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    candidate: &CandidatePlan,
    workers: usize,
) -> AnalysisResult {
    let options = SolveOptions {
        workers,
        max_contexts: 10_000,
        max_steps: 100_000,
        memory_budget_bytes: 32 * 1024 * 1024,
        execution_roots: Some(
            candidate
                .roots
                .iter()
                .map(|root| ExecutionRoot {
                    node: root.node,
                    receiver: root.receiver,
                })
                .collect(),
        ),
        ..Default::default()
    };
    QuerySession::new(facts, graph, &options)
        .unwrap()
        .analyze_typed(AnalysisSeeds {
            execution: candidate.execution_seeds(),
            declarations: candidate.declaration_seeds(),
        })
        .unwrap()
}

#[test]
fn paired_native_backed_cohort_separates_required_covered_and_missing_override() {
    for workers in [1, 4] {
        let (base, base_graph) = cohort(false, true);
        let (head, head_graph) = cohort(true, true);
        let seeds = changed_seeds(
            &base,
            &base_graph,
            &head,
            &head_graph,
            &["AdmittedProtocol.scala"],
        )
        .unwrap();
        assert!(!seeds.conservative);
        let make_plan = |facts: &FactSnapshot,
                         graph: &ProgramGraph,
                         execution: &[NodeId],
                         declarations: &[NodeId]| {
            plan(
                facts,
                graph,
                PlanSeeds {
                    execution,
                    declarations,
                    unscoped: false,
                },
            )
            .unwrap()
        };
        let before_plan = make_plan(&base, &base_graph, &seeds.base, &seeds.base_compile);
        let after_plan = make_plan(&head, &head_graph, &seeds.head, &seeds.head_compile);
        let before = planned_analysis(&base, &base_graph, &before_plan, workers);
        let after = planned_analysis(&head, &head_graph, &after_plan, workers);
        assert_ne!(before.completion, Completion::ResourceLimited);
        assert_ne!(after.completion, Completion::ResourceLimited);
        let result = select_with_plan(
            &base,
            &base_graph,
            &head,
            &head_graph,
            seeds,
            Some(before),
            after,
            Some(&before_plan),
            &after_plan,
        )
        .unwrap();
        let decision = |name| {
            result
                .decisions
                .iter()
                .find(|row| head.text(head.suites[row.suite.index()].name) == name)
                .unwrap()
        };
        assert_eq!(
            decision("scopedcase.AffectedSuite").status,
            SuiteDecisionStatus::Required
        );
        assert_eq!(
            decision("scopedcase.CoveredSuite").status,
            SuiteDecisionStatus::Excluded
        );
        assert_eq!(
            decision("scopedcase.MissingOverrideSuite").status,
            SuiteDecisionStatus::Unknown
        );
        assert!(!decision("scopedcase.CoveredSuite").guarded);
        assert!(decision("scopedcase.MissingOverrideSuite").guarded);
        let required = head_graph
            .node_for_symbol(head.find_symbol("scopedcase/AffectedSuite#").unwrap())
            .unwrap();
        assert!(
            result.head.contains(required),
            "Required needs an execution proof through the registered callback"
        );
        assert!(
            result
                .head
                .evidence
                .witnesses
                .iter()
                .any(|witness| witness.binding != u32::MAX),
            "the protocol registration callback must actually execute"
        );
        let mut output = Vec::new();
        selector_report::write_compact_json(
            &mut output,
            &selector_report::ReportSnapshots {
                base_facts: &base,
                base_graph: &base_graph,
                head_facts: &head,
                head_graph: &head_graph,
            },
            &result,
        )
        .unwrap();
        let saved: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(
            saved["decisions"]
                .as_array()
                .unwrap()
                .iter()
                .filter(|row| row["status"] == "excluded")
                .count(),
            1
        );
    }
}

#[test]
fn unused_deferred_contract_does_not_guard_an_admitted_parent_fallback() {
    let (facts, graph) = cohort(false, false);
    let candidate = plan(
        &facts,
        &graph,
        PlanSeeds {
            execution: &[],
            declarations: &[],
            unscoped: false,
        },
    )
    .unwrap();
    let result = planned_analysis(&facts, &graph, &candidate, 1);
    assert_eq!(result.completion, Completion::Complete);
    assert!(result.guarded_roots.is_empty());
}

#[test]
fn missing_child_override_retains_admitted_parent_effects_and_the_guard() {
    let (facts, graph) = cohort(false, true);
    let fallback = graph
        .node_for_symbol(facts.find_symbol(MISSING).unwrap())
        .unwrap();
    let candidate = plan(
        &facts,
        &graph,
        PlanSeeds {
            execution: &[fallback],
            declarations: &[],
            unscoped: false,
        },
    )
    .unwrap();
    let result = planned_analysis(&facts, &graph, &candidate, 1);
    let root = graph
        .node_for_symbol(
            facts
                .find_symbol("scopedcase/MissingOverrideSuite#")
                .unwrap(),
        )
        .unwrap();
    assert!(
        result.contains(root),
        "a scoped refusal must not erase the admitted fallback's possible effects"
    );
    assert!(
        result.guarded_roots.contains(&root),
        "admitted fallback effects do not prove the missing child override is complete"
    );
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum FieldCase {
    UnrelatedChange,
    ChangedDormantWriter,
    OpaqueSibling,
}

fn field_cohort(head: bool, case: FieldCase) -> (FactSnapshot, ProgramGraph) {
    let mut builder = FactBuilder::new();
    let context = builder.intern(CONTEXT).unwrap();
    let path = builder.intern("KnownFieldProtocol.scala").unwrap();
    let source = builder
        .intern("// Explicit admitted-IR noninterference control.\n")
        .unwrap();
    builder.facts.files.push(FileRecord {
        path,
        source,
        context,
        revision: StrId::NONE,
        source_hash: ContentHash([if head { 12 } else { 11 }; 32]),
        flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
    });
    let mut f = Fixture { builder, context };
    let reader = f.symbol("fieldcase/ReaderSuite#", 13, SymbolId::NONE);
    let field = f.symbol("fieldcase/ReaderSuite#known.", 3, reader);
    f.builder.facts.symbols[field.index()].properties = 1024;
    let changed = f.symbol(CHANGED, 3, SymbolId::NONE);
    f.body(
        reader,
        BODY_INITIALIZER,
        &[OperationRecord {
            target: field,
            dest: ValueId(1),
            flags: OP_STATIC_FIELD,
            ..op(Opcode::LoadField)
        }],
    );
    f.body(field, BODY_DEFERRED, &[]);
    let writes = [OperationRecord {
        target: field,
        b: ValueId(1),
        flags: OP_STATIC_FIELD,
        ..op(Opcode::StoreField)
    }];
    f.body(
        changed,
        BODY_DEFERRED,
        if case == FieldCase::ChangedDormantWriter {
            &writes
        } else {
            &[]
        },
    );
    f.builder.facts.bodies.last_mut().unwrap().body_hash =
        ContentHash([if head { 22 } else { 21 }; 32]);
    let name = f.builder.intern("fieldcase.ReaderSuite").unwrap();
    f.builder.facts.suites.push(SuiteRecord {
        name,
        symbol: reader,
        file: FileId(0),
        flags: 0,
    });
    if case == FieldCase::OpaqueSibling {
        let opaque = f.symbol("fieldcase/OpaqueSuite#", 13, SymbolId::NONE);
        f.body(opaque, BODY_INITIALIZER, &[op(Opcode::Unknown)]);
        let name = f.builder.intern("fieldcase.OpaqueSuite").unwrap();
        f.builder.facts.suites.push(SuiteRecord {
            name,
            symbol: opaque,
            file: FileId(0),
            flags: 0,
        });
    }
    let mut facts = f.builder.finish().unwrap();
    let directory = tempfile::tempdir().unwrap();
    facts.identity =
        selector_facts::codec::write(&directory.path().join("facts.bin"), &facts).unwrap();
    let graph = selector_graph_build::build(
        &facts,
        &selector_graph_build::BuildOptions {
            workers: 1,
            include_models: false,
        },
    )
    .unwrap();
    (facts, graph)
}

#[test]
fn paired_known_field_exclusion_needs_noninterference_not_a_known_initial_value() {
    for case in [
        FieldCase::UnrelatedChange,
        FieldCase::ChangedDormantWriter,
        FieldCase::OpaqueSibling,
    ] {
        let (base, before_graph) = field_cohort(false, case);
        let (head, after_graph) = field_cohort(true, case);
        let seeds = changed_seeds(
            &base,
            &before_graph,
            &head,
            &after_graph,
            &["KnownFieldProtocol.scala"],
        )
        .unwrap();
        assert!(!seeds.conservative);
        let before_plan = plan(
            &base,
            &before_graph,
            PlanSeeds {
                execution: &seeds.base,
                declarations: &seeds.base_compile,
                unscoped: false,
            },
        )
        .unwrap();
        let after_plan = plan(
            &head,
            &after_graph,
            PlanSeeds {
                execution: &seeds.head,
                declarations: &seeds.head_compile,
                unscoped: false,
            },
        )
        .unwrap();
        let reader = after_graph
            .node_for_symbol(head.find_symbol("fieldcase/ReaderSuite#").unwrap())
            .unwrap();
        assert_eq!(
            after_plan.certifies_unaffected(reader),
            case == FieldCase::UnrelatedChange
        );
        if case == FieldCase::UnrelatedChange {
            let forced = selector_solve::analyze(
                &head,
                &after_graph,
                &[],
                &SolveOptions {
                    workers: 1,
                    ..Default::default()
                },
            )
            .unwrap();
            assert!(
                forced.guarded_roots.contains(&reader),
                "executing the read really has an unknown initial value; the certificate is only noninterference"
            );
        }
        let before = planned_analysis(&base, &before_graph, &before_plan, 1);
        let after = planned_analysis(&head, &after_graph, &after_plan, 1);
        let result = select_with_plan(
            &base,
            &before_graph,
            &head,
            &after_graph,
            seeds,
            Some(before),
            after,
            Some(&before_plan),
            &after_plan,
        )
        .unwrap();
        let decision = result
            .decisions
            .iter()
            .find(|row| row.node == reader)
            .unwrap();
        if case == FieldCase::UnrelatedChange {
            assert_eq!(decision.status, SuiteDecisionStatus::Excluded);
            assert!(decision.base_exclusion.is_some() && decision.head_exclusion.is_some());
        } else {
            assert_ne!(
                decision.status,
                SuiteDecisionStatus::Excluded,
                "matching dormant writers and opaque siblings cannot disappear behind a scalar read"
            );
            if case == FieldCase::OpaqueSibling {
                assert_eq!(decision.status, SuiteDecisionStatus::Unknown);
                assert_ne!(decision.reasons & DECISION_OPAQUE_SHARED_HEAP, 0);
            }
        }
    }
}

#[test]
fn genuine_compiler_registration_still_proves_deferred_body_impact_without_erasing_library_guards()
{
    let directory = root().join("fixtures/registration-smoke");
    assert!(
        std::fs::read_to_string(directory.join("execution.log"))
            .unwrap()
            .lines()
            .any(|line| line == "suite:registrationcase.DirectSuite:tests=1:observed=41")
    );
    let facts = selector_extract::import_capture(
        &directory.join("documents.jsonl"),
        Some(&directory.join("syntax.jsonl")),
        &selector_extract::ExtractOptions {
            workers: 1,
            catalogue: Some(directory.join("catalogue.json")),
            ..Default::default()
        },
    )
    .unwrap();
    let graph = selector_graph_build::build(&facts, &Default::default()).unwrap();
    let changed = graph
        .node_for_symbol(
            facts
                .find_symbol("registrationcase/Effects.changed().")
                .unwrap(),
        )
        .unwrap();
    let analysis = selector_solve::analyze(
        &facts,
        &graph,
        &[changed],
        &SolveOptions {
            workers: 1,
            max_contexts: 10_000,
            max_steps: 500_000,
            memory_budget_bytes: 64 * 1024 * 1024,
            ..Default::default()
        },
    )
    .unwrap();
    let result = selector_select::select(
        &facts,
        &graph,
        &facts,
        &graph,
        ChangeSeeds {
            head: vec![changed],
            ..Default::default()
        },
        None,
        analysis,
    )
    .unwrap();
    let direct = result
        .decisions
        .iter()
        .find(|row| {
            facts.text(facts.suites[row.suite.index()].name) == "registrationcase.DirectSuite"
        })
        .unwrap();
    assert_eq!(direct.status, SuiteDecisionStatus::Required);
    assert!(
        !result.head.obligations.is_empty(),
        "actual external framework effects remain honest open boundaries"
    );
    let direct_symbol = facts.find_symbol("registrationcase/DirectSuite#").unwrap();
    let changed_symbol = facts
        .find_symbol("registrationcase/Effects.changed().")
        .unwrap();
    assert!(
        facts
            .operations
            .iter()
            .any(|operation| operation.target == changed_symbol
                && facts.bodies[operation.body.index()].flags & BODY_DEFERRED != 0
                && facts.symbols[facts.bodies[operation.body.index()].symbol.index()].owner
                    == direct_symbol)
    );
}
