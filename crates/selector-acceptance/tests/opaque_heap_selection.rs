//! A known heap value is not a proof that another opaque runnable root cannot
//! mutate it. Exercise the real planner, transfer solver and selection policy.
use selector_facts::{
    BodyRecord, FactBuilder, FactSnapshot, FileRecord, OperationRecord, SuiteRecord, SymbolRecord,
    TextRange,
};
use selector_graph::{EdgeRecord, NodeRecord, ProgramGraph};
use selector_plan::{CandidatePlan, PlanSeeds, plan};
use selector_result::{
    AnalysisResult, DECISION_COMPLETE_UNAFFECTED, DECISION_OPAQUE_SHARED_HEAP, EffectClosure,
    SuiteDecisionStatus,
};
use selector_select::{ChangeSeeds, select_with_plan};
use selector_solve::{AnalysisSeeds, ExecutionRoot, QuerySession, SolveOptions};
use selector_types::*;

const INITIALIZE: NodeId = NodeId(0);
const READER: NodeId = NodeId(1);
const OPAQUE_ROOT: NodeId = NodeId(2);
const SCALAR: NodeId = NodeId(3);
const CHANGED: NodeId = NodeId(4);

fn operation(opcode: Opcode) -> OperationRecord {
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

fn snapshot(opaque: bool) -> (FactSnapshot, ProgramGraph) {
    let mut b = FactBuilder::new();
    let path = b.intern("Shared.scala").unwrap();
    let source = b.intern(&" ".repeat(128)).unwrap();
    b.facts.files.push(FileRecord {
        path,
        source,
        context: StrId::NONE,
        revision: StrId::NONE,
        source_hash: ContentHash([1; 32]),
        flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
    });
    b.facts.identity = ContentHash([1; 32]);
    let mut graph = ProgramGraph {
        identity: ContentHash([if opaque { 2 } else { 3 }; 32]),
        facts_identity: b.facts.identity,
        ..Default::default()
    };
    for (i, name) in [
        "p/InitializerSuite#",
        "p/ReaderSuite#",
        "p/OpaqueSuite#",
        "p/ScalarSuite#",
        "external/mutate().",
        "p/safe().",
        "p/State.shared.",
    ]
    .into_iter()
    .enumerate()
    {
        let file = if i == 4 { FileId::NONE } else { FileId(0) };
        let symbol = b.ensure_symbol(name, file).unwrap();
        let record = &mut b.facts.symbols[symbol.index()];
        record.kind = if i <= 3 { 13 } else { 3 };
        record.flags = if i == 4 { 0 } else { SYMBOL_DEFINED };
        if i == 6 {
            record.properties = 1024;
        }
        graph.nodes.push(NodeRecord {
            symbol,
            file,
            body: BodyId::NONE,
            flags: if i == 4 && !opaque {
                NODE_EFFECTS_COMPLETE
            } else {
                0
            },
        });
        graph.symbol_nodes.push(NodeId(i as u32));
    }
    let mut body = |node: u32, operations: Vec<OperationRecord>| {
        let id = BodyId(b.facts.bodies.len() as u32);
        let start = b.facts.operations.len() as u32;
        for mut op in operations {
            op.body = id;
            b.facts.operations.push(op);
        }
        b.facts.bodies.push(BodyRecord {
            symbol: SymbolId(node),
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange {
                start,
                len: b.facts.operations.len() as u32 - start,
            },
            parameters: IdRange::default(),
            body_hash: ContentHash([4; 32]),
            flags: if node <= 3 {
                BODY_INITIALIZER
            } else {
                BODY_DEFERRED
            },
        });
        graph.nodes[node as usize].body = id;
    };
    body(
        0,
        vec![
            OperationRecord {
                target: SymbolId(5),
                dest: ValueId(1),
                ..operation(Opcode::BindCallback)
            },
            OperationRecord {
                target: SymbolId(6),
                b: ValueId(1),
                flags: OP_STATIC_FIELD,
                ..operation(Opcode::StoreField)
            },
        ],
    );
    body(
        1,
        vec![
            OperationRecord {
                target: SymbolId(6),
                dest: ValueId(1),
                flags: OP_STATIC_FIELD,
                ..operation(Opcode::LoadField)
            },
            OperationRecord {
                a: ValueId(1),
                ..operation(Opcode::Return)
            },
        ],
    );
    body(
        2,
        vec![OperationRecord {
            target: SymbolId(4),
            dest: ValueId(1),
            ..operation(Opcode::Call)
        }],
    );
    body(3, vec![]);
    body(5, vec![]);
    graph.edges.push(EdgeRecord {
        source: OPAQUE_ROOT,
        target: CHANGED,
        kind: EdgeKind::Call,
        occurrence: OccurrenceId::NONE,
        operation: OperationId(4),
        receiver: SymbolId::NONE,
        flags: 0,
    });
    for (symbol, name) in [
        (1, "p.ReaderSuite"),
        (2, "p.OpaqueSuite"),
        (3, "p.ScalarSuite"),
        (0, "p.InitializerSuite"),
    ] {
        let name = b.intern(name).unwrap();
        b.facts.suites.push(SuiteRecord {
            name,
            symbol: SymbolId(symbol),
            file: FileId(0),
            flags: 0,
        });
    }
    let facts = b.finish().unwrap();
    graph.index().unwrap();
    (facts, graph)
}

fn analyze(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    plan: &CandidatePlan,
    workers: usize,
) -> AnalysisResult {
    // A whole-catalogue selection needs effect coverage for certified-pruned
    // roots too; a changed-dependency certificate is not an effect certificate.
    let complete_frontier: Vec<_> = facts
        .suites
        .iter()
        .filter_map(|suite| {
            graph
                .node_for_symbol(suite.symbol)
                .map(|node| ExecutionRoot {
                    node,
                    receiver: suite.symbol,
                })
        })
        .collect();
    analyze_extra(facts, graph, plan, workers, &complete_frontier)
}

fn analyze_extra(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    plan: &CandidatePlan,
    workers: usize,
    extra: &[ExecutionRoot],
) -> AnalysisResult {
    let options = SolveOptions {
        workers,
        execution_roots: Some(
            plan.roots
                .iter()
                .map(|root| ExecutionRoot {
                    node: root.node,
                    receiver: root.receiver,
                })
                .collect(),
        ),
        max_steps: 10_000,
        max_contexts: 100,
        memory_budget_bytes: 16 * 1024 * 1024,
        ..Default::default()
    };
    let mut session = QuerySession::new(facts, graph, &options).unwrap();
    // Establish an actual, non-TOP shared value before the reader executes. A
    // missing field value would already guard the reader and conceal the gap.
    session
        .execute(&[ExecutionRoot {
            node: INITIALIZE,
            receiver: SymbolId(INITIALIZE.0),
        }])
        .unwrap();
    session.execute(extra).unwrap();
    session
        .analyze_typed(AnalysisSeeds {
            execution: plan.execution_seeds(),
            declarations: &[],
        })
        .unwrap()
}

/// A complete known-slot read has data uncertainty, followed by a callback whose
/// actual target is closed. The callback keeps the planner's potential opaque
/// frontier: without exhaustive effect evidence, the other known reader widens.
/// A later optional unknown callee must keep that frontier open even though the
/// first issue in this runnable context is still the data read.
fn data_boundary_snapshot(later_opaque_call: bool) -> (FactSnapshot, ProgramGraph) {
    let (mut facts, mut graph) = snapshot(true);
    let mut append_symbol = |name: &str, field: bool| {
        let name_id = StrId(facts.strings.entries.len() as u32);
        facts.strings.entries.push(TextRange {
            start: facts.strings.bytes.len() as u64,
            len: name.len() as u32,
        });
        facts.strings.bytes.extend_from_slice(name.as_bytes());
        let symbol = SymbolId(facts.symbols.len() as u32);
        facts.symbols.push(SymbolRecord {
            name: name_id,
            display: StrId::NONE,
            owner: SymbolId::NONE,
            file: if field { FileId(0) } else { FileId::NONE },
            context: StrId::NONE,
            kind: 3,
            properties: if field { 1024 } else { 0 },
            signature: StrId::NONE,
            span: Span::default(),
            flags: if field { SYMBOL_DEFINED } else { 0 },
        });
        let node = NodeId(graph.nodes.len() as u32);
        graph.symbol_nodes.push(node);
        graph.nodes.push(NodeRecord {
            symbol,
            file: facts.symbols[symbol.index()].file,
            body: BodyId::NONE,
            flags: facts.symbols[symbol.index()].flags,
        });
        (symbol, node)
    };
    let (field, field_node) = append_symbol("p/State.uninitialized.", true);
    let (opaque_callee, opaque_node) = append_symbol("external/opaque().", false);
    let body = graph.nodes[OPAQUE_ROOT.index()].body;
    let first = facts.bodies[body.index()].operations.start;
    assert_eq!(first as usize + 1, facts.operations.len());
    facts.operations[first as usize] = OperationRecord {
        body,
        target: field,
        dest: ValueId(1),
        flags: OP_STATIC_FIELD,
        ..operation(Opcode::LoadField)
    };
    graph.edges.retain(|edge| edge.source != OPAQUE_ROOT);
    graph.edges.push(EdgeRecord {
        source: OPAQUE_ROOT,
        target: field_node,
        kind: EdgeKind::Field,
        occurrence: OccurrenceId::NONE,
        operation: OperationId(first),
        receiver: SymbolId::NONE,
        flags: 0,
    });
    for mut op in [
        OperationRecord {
            target: SymbolId(5),
            dest: ValueId(2),
            ..operation(Opcode::BindCallback)
        },
        OperationRecord {
            a: ValueId(2),
            ..operation(Opcode::InvokeCallback)
        },
    ] {
        op.body = body;
        facts.operations.push(op);
        facts.bodies[body.index()].operations.len += 1;
    }
    if later_opaque_call {
        let call = OperationId(facts.operations.len() as u32);
        facts.operations.push(OperationRecord {
            body,
            target: opaque_callee,
            ..operation(Opcode::Call)
        });
        facts.bodies[body.index()].operations.len += 1;
        graph.edges.push(EdgeRecord {
            source: OPAQUE_ROOT,
            target: opaque_node,
            kind: EdgeKind::Call,
            occurrence: OccurrenceId::NONE,
            operation: call,
            receiver: SymbolId::NONE,
            flags: 0,
        });
    }
    let directory = tempfile::tempdir().unwrap();
    facts.identity =
        selector_facts::codec::write(&directory.path().join("facts.bin"), &facts).unwrap();
    graph.facts_identity = facts.identity;
    graph.index().unwrap();
    graph.identity =
        selector_graph::codec::write(&directory.path().join("graph.bin"), &graph).unwrap();
    (facts, graph)
}

#[test]
fn paired_data_only_guard_keeps_its_suite_without_poisoning_an_unrelated_known_reader() {
    for workers in [1, 4] {
        for planned in [false, true] {
            let (base, bg) = data_boundary_snapshot(false);
            let (head, hg) = data_boundary_snapshot(false);
            let make_plan = |facts: &FactSnapshot, graph: &ProgramGraph| {
                plan(
                    facts,
                    graph,
                    PlanSeeds {
                        execution: &[CHANGED],
                        declarations: &[],
                        unscoped: false,
                    },
                )
                .unwrap()
            };
            let bp = make_plan(&base, &bg);
            let hp = make_plan(&head, &hg);
            assert!(bp.shared_heap_guarded_roots().contains(&READER));
            assert!(hp.shared_heap_guarded_roots().contains(&READER));
            let before = analyze(&base, &bg, &bp, workers);
            let after = analyze(&head, &hg, &hp, workers);
            for analysis in [&before, &after] {
                assert_eq!(analysis.completion, Completion::Conservative);
                assert!(analysis.guarded_roots.contains(&OPAQUE_ROOT));
                assert!(!analysis.guarded_roots.contains(&READER));
                assert_eq!(
                    analysis.validate_execution_effects().unwrap(),
                    EffectClosure::Closed
                );
            }
            let seeds = ChangeSeeds {
                base: vec![CHANGED],
                head: vec![CHANGED],
                ..Default::default()
            };
            let selected = if planned {
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
            } else {
                selector_select::select(&base, &bg, &head, &hg, seeds, Some(before), after)
            }
            .unwrap();
            assert_eq!(selected.decisions[0].status, SuiteDecisionStatus::Excluded);
            assert!(!selected.decisions[0].guarded);
            assert_eq!(
                selected.decisions[0].reasons & DECISION_OPAQUE_SHARED_HEAP,
                0
            );
            assert_eq!(selected.decisions[1].status, SuiteDecisionStatus::Unknown);
            assert!(
                selected.decisions[1].guarded,
                "exhaustive effect closure must not erase the data-only root's own uncertainty"
            );
            assert_eq!(selected.decisions[2].status, SuiteDecisionStatus::Excluded);
        }
    }
}

#[test]
fn later_opaque_effect_on_either_side_cannot_hide_behind_a_first_data_issue() {
    for workers in [1, 4] {
        for (base_opaque, head_opaque) in [(true, false), (false, true), (true, true)] {
            let (base, bg) = data_boundary_snapshot(base_opaque);
            let (head, hg) = data_boundary_snapshot(head_opaque);
            let make_plan = |facts: &FactSnapshot, graph: &ProgramGraph| {
                plan(
                    facts,
                    graph,
                    PlanSeeds {
                        execution: &[CHANGED],
                        declarations: &[],
                        unscoped: false,
                    },
                )
                .unwrap()
            };
            let bp = make_plan(&base, &bg);
            let hp = make_plan(&head, &hg);
            let before = analyze(&base, &bg, &bp, workers);
            let after = analyze(&head, &hg, &hp, workers);
            for (analysis, opaque) in [(&before, base_opaque), (&after, head_opaque)] {
                assert_eq!(
                    analysis.validate_execution_effects().unwrap(),
                    if opaque {
                        EffectClosure::Open
                    } else {
                        EffectClosure::Closed
                    }
                );
                assert!(
                    analysis
                        .evidence
                        .guard_causes
                        .iter()
                        .any(|cause| cause.root == OPAQUE_ROOT
                            && cause.runtime.is_some_and(|site| site.reason
                                == selector_issue::RuntimeIssueReason::UnknownFieldValue)),
                    "the chosen first-site exemplar remains data-only and cannot certify the later call's effects"
                );
            }
            let selected = select_with_plan(
                &base,
                &bg,
                &head,
                &hg,
                ChangeSeeds {
                    base: vec![CHANGED],
                    head: vec![CHANGED],
                    ..Default::default()
                },
                Some(before),
                after,
                Some(&bp),
                &hp,
            )
            .unwrap();
            assert_eq!(selected.decisions[0].status, SuiteDecisionStatus::Unknown);
            assert_ne!(
                selected.decisions[0].reasons & DECISION_OPAQUE_SHARED_HEAP,
                0
            );
            assert_eq!(selected.decisions[1].status, SuiteDecisionStatus::Unknown);
            assert_eq!(selected.decisions[2].status, SuiteDecisionStatus::Excluded);
        }
    }
}

#[test]
fn unverified_legacy_effect_evidence_preserves_the_old_shared_reader_guard() {
    for planned in [false, true] {
        let (facts, graph) = data_boundary_snapshot(false);
        let candidate = plan(
            &facts,
            &graph,
            PlanSeeds {
                execution: &[CHANGED],
                declarations: &[],
                unscoped: false,
            },
        )
        .unwrap();
        let mut before = analyze(&facts, &graph, &candidate, 1);
        let mut after = analyze(&facts, &graph, &candidate, 1);
        for analysis in [&mut before, &mut after] {
            assert_eq!(
                analysis.validate_execution_effects().unwrap(),
                EffectClosure::Closed
            );
            // Reconstruct an actual legacy-shaped result from its old public
            // fields. Deleting only a new token is tampering and must fail its
            // separate issuer binding, rather than impersonating legacy input.
            let old = std::mem::take(&mut analysis.evidence);
            analysis.evidence.requested_roots = old.requested_roots;
            analysis.evidence.guard_causes = old.guard_causes;
            analysis.evidence.atoms = old.atoms;
            analysis.evidence.values = old.values;
            analysis.evidence.value_ids = old.value_ids;
            analysis.evidence.contexts = old.contexts;
            analysis.evidence.captures = old.captures;
            analysis.evidence.witnesses = old.witnesses;
            analysis.evidence.root_contexts = old.root_contexts;
            assert_eq!(
                analysis.validate_execution_effects().unwrap(),
                EffectClosure::Unverified
            );
        }
        let seeds = ChangeSeeds {
            base: vec![CHANGED],
            head: vec![CHANGED],
            ..Default::default()
        };
        let selected = if planned {
            select_with_plan(
                &facts,
                &graph,
                &facts,
                &graph,
                seeds,
                Some(before),
                after,
                Some(&candidate),
                &candidate,
            )
        } else {
            selector_select::select(&facts, &graph, &facts, &graph, seeds, Some(before), after)
        }
        .unwrap();
        assert_eq!(selected.decisions[0].status, SuiteDecisionStatus::Unknown);
        assert_ne!(
            selected.decisions[0].reasons & DECISION_OPAQUE_SHARED_HEAP,
            0
        );
    }
}

#[test]
fn locally_closed_candidate_frontier_cannot_waive_whole_catalogue_shared_effects() {
    let (facts, graph) = data_boundary_snapshot(false);
    let candidate = plan(
        &facts,
        &graph,
        PlanSeeds {
            execution: &[CHANGED],
            declarations: &[],
            unscoped: false,
        },
    )
    .unwrap();
    assert!(candidate.certifies_unaffected(SCALAR));
    let before = analyze_extra(&facts, &graph, &candidate, 1, &[]);
    let after = analyze_extra(&facts, &graph, &candidate, 1, &[]);
    for result in [&before, &after] {
        assert_eq!(
            result.validate_execution_effects().unwrap(),
            EffectClosure::Closed
        );
        assert!(
            !result
                .evidence
                .requested_roots
                .iter()
                .any(|root| root.node == SCALAR)
        );
    }
    let selected = select_with_plan(
        &facts,
        &graph,
        &facts,
        &graph,
        ChangeSeeds {
            base: vec![CHANGED],
            head: vec![CHANGED],
            ..Default::default()
        },
        Some(before),
        after,
        Some(&candidate),
        &candidate,
    )
    .unwrap();
    assert_eq!(selected.decisions[0].status, SuiteDecisionStatus::Unknown);
    assert_ne!(
        selected.decisions[0].reasons & DECISION_OPAQUE_SHARED_HEAP,
        0
    );
    assert_eq!(
        selected.decisions[2].status,
        SuiteDecisionStatus::Excluded,
        "the unchanged scalar's selection certificate remains valid, but is not an effect-closure certificate for the whole catalogue"
    );
    assert!(
        selector_select::select(
            &facts,
            &graph,
            &facts,
            &graph,
            ChangeSeeds {
                base: vec![CHANGED],
                head: vec![CHANGED],
                ..Default::default()
            },
            Some(analyze_extra(&facts, &graph, &candidate, 1, &[])),
            analyze_extra(&facts, &graph, &candidate, 1, &[])
        )
        .is_err(),
        "the plain API has no authority for omitted catalogue suites"
    );
}

#[test]
fn selection_time_obligation_overlay_downgrades_effect_authority_and_preserves_valid_binding() {
    for planned in [false, true] {
        let (facts, graph) = data_boundary_snapshot(false);
        let candidate = plan(
            &facts,
            &graph,
            PlanSeeds {
                execution: &[CHANGED],
                declarations: &[],
                unscoped: false,
            },
        )
        .unwrap();
        let before = analyze(&facts, &graph, &candidate, 1);
        let after = analyze(&facts, &graph, &candidate, 1);
        assert_eq!(
            after.validate_execution_effects().unwrap(),
            EffectClosure::Closed
        );
        let issue = selector_result::Obligation {
            kind: IssueKind::UnknownExecution,
            file: FileId(0),
            symbol: SymbolId(OPAQUE_ROOT.0),
            detail: StrId::NONE,
        };
        let seeds = ChangeSeeds {
            base: vec![CHANGED],
            head: vec![CHANGED],
            base_obligations: vec![issue],
            head_obligations: vec![issue],
            ..Default::default()
        };
        let selected = if planned {
            select_with_plan(
                &facts,
                &graph,
                &facts,
                &graph,
                seeds,
                Some(before),
                after,
                Some(&candidate),
                &candidate,
            )
        } else {
            selector_select::select(&facts, &graph, &facts, &graph, seeds, Some(before), after)
        }
        .unwrap();
        for result in [selected.base.as_ref().unwrap(), &selected.head] {
            assert_eq!(
                result.validate_execution_effects().unwrap(),
                EffectClosure::Open
            );
            assert!(result.obligations.iter().any(|row| row.kind == issue.kind
                && row.file == issue.file
                && row.symbol == issue.symbol));
        }
        assert_eq!(selected.decisions[0].status, SuiteDecisionStatus::Unknown);
        assert_ne!(
            selected.decisions[0].reasons & DECISION_OPAQUE_SHARED_HEAP,
            0
        );
    }
}

#[test]
fn opaque_runnable_effect_keeps_known_heap_reader_and_excludes_closed_scalar() {
    for workers in [1, 4] {
        let (facts, graph) = snapshot(true);
        let plan = plan(
            &facts,
            &graph,
            PlanSeeds {
                execution: &[CHANGED],
                declarations: &[],
                unscoped: false,
            },
        )
        .unwrap();
        assert_eq!(plan.metrics().heap_roots, 1);
        assert!(plan.roots.iter().any(|root| root.node == READER));
        assert!(plan.certifies_unaffected(SCALAR));
        let head = analyze(&facts, &graph, &plan, workers);
        assert!(!head.contains(READER));
        assert!(
            !head.guarded_roots.contains(&READER),
            "known slot must isolate the selection boundary"
        );
        assert!(head.guarded_roots.contains(&OPAQUE_ROOT));
        let selected = select_with_plan(
            &facts,
            &graph,
            &facts,
            &graph,
            ChangeSeeds {
                base: vec![CHANGED],
                head: vec![CHANGED],
                ..Default::default()
            },
            Some(analyze(&facts, &graph, &plan, workers)),
            head,
            Some(&plan),
            &plan,
        )
        .unwrap();
        assert_eq!(
            selected.decisions[0].status,
            SuiteDecisionStatus::Unknown,
            "an opaque runnable effect may mutate the known shared slot"
        );
        assert!(selected.decisions[0].guarded);
        assert!(selected.decisions[0].head_exclusion.is_none());
        assert_ne!(
            selected.decisions[0].reasons & DECISION_OPAQUE_SHARED_HEAP,
            0
        );
        assert_eq!(
            selected.decisions[0].reasons & DECISION_COMPLETE_UNAFFECTED,
            0
        );
        assert_eq!(selected.decisions[1].status, SuiteDecisionStatus::Required);
        assert_eq!(selected.decisions[2].status, SuiteDecisionStatus::Excluded);
        assert!(selected.decisions[2].head_exclusion.is_some());
        let snapshots = selector_report::ReportSnapshots {
            base_facts: &facts,
            base_graph: &graph,
            head_facts: &facts,
            head_graph: &graph,
        };
        let mut compact = Vec::new();
        selector_report::write_compact_json(&mut compact, &snapshots, &selected).unwrap();
        let compact: serde_json::Value = serde_json::from_slice(&compact).unwrap();
        assert_eq!(
            compact["decisions"][0]["reasons"],
            serde_json::json!(["opaque_shared_heap"])
        );
        assert_eq!(compact["decisions"][0]["proofs"], serde_json::json!([]));
        let mut full = Vec::new();
        selector_report::write_json(&mut full, &snapshots, &selected).unwrap();
        let full: serde_json::Value = serde_json::from_slice(&full).unwrap();
        assert_eq!(full["suites"][0]["opaque_shared_heap"], true);
    }
}

#[test]
fn completed_known_heap_reader_remains_excluded_without_an_opaque_runnable_effect() {
    let (facts, graph) = snapshot(false);
    let plan = plan(
        &facts,
        &graph,
        PlanSeeds {
            execution: &[CHANGED],
            declarations: &[],
            unscoped: false,
        },
    )
    .unwrap();
    assert_eq!(plan.metrics().heap_roots, 0);
    assert!(plan.certifies_unaffected(READER));
    let head = analyze(&facts, &graph, &plan, 1);
    assert_eq!(head.completion, Completion::Complete);
    let selected = select_with_plan(
        &facts,
        &graph,
        &facts,
        &graph,
        ChangeSeeds {
            base: vec![CHANGED],
            head: vec![CHANGED],
            ..Default::default()
        },
        Some(analyze(&facts, &graph, &plan, 1)),
        head,
        Some(&plan),
        &plan,
    )
    .unwrap();
    assert_eq!(selected.decisions[0].status, SuiteDecisionStatus::Excluded);
    assert!(selected.decisions[0].base_exclusion.is_some());
    assert!(selected.decisions[0].head_exclusion.is_some());
    assert_eq!(selected.decisions[2].status, SuiteDecisionStatus::Excluded);
}

#[test]
fn fully_resolved_callback_closes_potential_opaque_effects_for_shared_reader() {
    let (mut facts, mut graph) = snapshot(false);
    let body = graph.nodes[OPAQUE_ROOT.index()].body;
    assert_eq!(
        facts.bodies[body.index()].operations.range().end,
        facts.operations.len()
    );
    for mut op in [
        OperationRecord {
            target: SymbolId(5),
            dest: ValueId(2),
            ..operation(Opcode::BindCallback)
        },
        OperationRecord {
            a: ValueId(2),
            ..operation(Opcode::InvokeCallback)
        },
    ] {
        op.body = body;
        facts.operations.push(op);
        facts.bodies[body.index()].operations.len += 1;
    }
    graph.identity = ContentHash([5; 32]);
    let plan = plan(
        &facts,
        &graph,
        PlanSeeds {
            execution: &[CHANGED],
            declarations: &[],
            unscoped: false,
        },
    )
    .unwrap();
    assert_eq!(
        plan.metrics().heap_roots,
        1,
        "the planner intentionally retains open callback possibilities"
    );
    for workers in [1, 4] {
        let head = analyze(&facts, &graph, &plan, workers);
        assert_eq!(head.completion, Completion::Complete);
        assert!(head.guarded_roots.is_empty() && !head.unscoped_uncertainty);
        let plain = selector_select::select(
            &facts,
            &graph,
            &facts,
            &graph,
            ChangeSeeds {
                base: vec![CHANGED],
                head: vec![CHANGED],
                ..Default::default()
            },
            Some(analyze(&facts, &graph, &plan, workers)),
            analyze(&facts, &graph, &plan, workers),
        )
        .unwrap();
        assert_eq!(plain.decisions[0].status, SuiteDecisionStatus::Excluded);
        assert_eq!(plain.decisions[0].reasons, DECISION_COMPLETE_UNAFFECTED);
        let selected = select_with_plan(
            &facts,
            &graph,
            &facts,
            &graph,
            ChangeSeeds {
                base: vec![CHANGED],
                head: vec![CHANGED],
                ..Default::default()
            },
            Some(analyze(&facts, &graph, &plan, workers)),
            head,
            Some(&plan),
            &plan,
        )
        .unwrap();
        assert_eq!(selected.decisions[0].status, SuiteDecisionStatus::Excluded);
        assert_eq!(selected.decisions[0].reasons, DECISION_COMPLETE_UNAFFECTED);
        assert_eq!(selected.decisions[2].status, SuiteDecisionStatus::Excluded);
    }
}

#[test]
fn either_snapshot_can_expose_a_shared_reader_without_canceling_independent_certificates() {
    for (base_opaque, head_opaque) in [(true, false), (false, true)] {
        let (base, bg) = snapshot(base_opaque);
        let (head, hg) = snapshot(head_opaque);
        let make_plan = |facts: &FactSnapshot, graph: &ProgramGraph| {
            plan(
                facts,
                graph,
                PlanSeeds {
                    execution: &[CHANGED],
                    declarations: &[],
                    unscoped: false,
                },
            )
            .unwrap()
        };
        let bp = make_plan(&base, &bg);
        let hp = make_plan(&head, &hg);
        let selected = select_with_plan(
            &base,
            &bg,
            &head,
            &hg,
            ChangeSeeds {
                base: vec![CHANGED],
                head: vec![CHANGED],
                ..Default::default()
            },
            Some(analyze(&base, &bg, &bp, 1)),
            analyze(&head, &hg, &hp, 1),
            Some(&bp),
            &hp,
        )
        .unwrap();
        assert_eq!(selected.decisions[0].status, SuiteDecisionStatus::Unknown);
        assert_eq!(selected.decisions[0].reasons, DECISION_OPAQUE_SHARED_HEAP);
        assert_eq!(selected.decisions[2].status, SuiteDecisionStatus::Excluded);
        assert!(selected.decisions[2].base_exclusion.is_some());
        assert!(selected.decisions[2].head_exclusion.is_some());
    }
}

#[test]
fn positive_execution_evidence_keeps_priority_over_shared_heap_uncertainty() {
    let (facts, graph) = snapshot(true);
    let seeds = [READER, CHANGED];
    let plan = plan(
        &facts,
        &graph,
        PlanSeeds {
            execution: &seeds,
            declarations: &[],
            unscoped: false,
        },
    )
    .unwrap();
    let selected = select_with_plan(
        &facts,
        &graph,
        &facts,
        &graph,
        ChangeSeeds {
            base: seeds.to_vec(),
            head: seeds.to_vec(),
            ..Default::default()
        },
        Some(analyze(&facts, &graph, &plan, 1)),
        analyze(&facts, &graph, &plan, 1),
        Some(&plan),
        &plan,
    )
    .unwrap();
    assert_eq!(selected.decisions[0].status, SuiteDecisionStatus::Required);
    assert!(selected.decisions[0].guarded);
    assert_ne!(
        selected.decisions[0].reasons & DECISION_OPAQUE_SHARED_HEAP,
        0
    );
}

#[test]
fn mutated_public_candidate_list_cannot_bypass_shared_heap_selection() {
    let (facts, graph) = snapshot(true);
    let mut plan = plan(
        &facts,
        &graph,
        PlanSeeds {
            execution: &[CHANGED],
            declarations: &[],
            unscoped: false,
        },
    )
    .unwrap();
    let head = analyze(&facts, &graph, &plan, 1);
    let base = analyze(&facts, &graph, &plan, 1);
    plan.roots.clear();
    assert!(
        select_with_plan(
            &facts,
            &graph,
            &facts,
            &graph,
            ChangeSeeds {
                base: vec![CHANGED],
                head: vec![CHANGED],
                ..Default::default()
            },
            Some(base),
            head,
            Some(&plan),
            &plan,
        )
        .is_err()
    );
}

#[test]
fn plain_selection_cannot_omit_a_shared_reader_behind_an_opaque_other_root() {
    for (base_opaque, head_opaque) in [(true, true), (true, false), (false, true)] {
        let (base, bg) = snapshot(base_opaque);
        let (head, hg) = snapshot(head_opaque);
        let make_plan = |facts: &FactSnapshot, graph: &ProgramGraph| {
            plan(
                facts,
                graph,
                PlanSeeds {
                    execution: &[CHANGED],
                    declarations: &[],
                    unscoped: false,
                },
            )
            .unwrap()
        };
        let bp = make_plan(&base, &bg);
        let hp = make_plan(&head, &hg);
        for workers in [1, 4] {
            let selected = selector_select::select(
                &base,
                &bg,
                &head,
                &hg,
                ChangeSeeds {
                    base: vec![CHANGED],
                    head: vec![CHANGED],
                    ..Default::default()
                },
                Some(analyze(&base, &bg, &bp, workers)),
                analyze(&head, &hg, &hp, workers),
            )
            .unwrap();
            assert_eq!(selected.decisions[0].status, SuiteDecisionStatus::Unknown);
            assert_ne!(
                selected.decisions[0].reasons & DECISION_OPAQUE_SHARED_HEAP,
                0
            );
            assert_eq!(selected.decisions[2].status, SuiteDecisionStatus::Excluded);
        }
    }
}

#[test]
fn plain_selection_keeps_shared_reader_when_catalogue_execution_is_unresolved() {
    let (mut facts, mut graph) = snapshot(false);
    facts.suites.push(SuiteRecord {
        name: facts.symbols[4].name,
        symbol: SymbolId::NONE,
        file: FileId::NONE,
        flags: 0,
    });
    facts.identity = ContentHash([8; 32]);
    graph.facts_identity = facts.identity;
    graph.identity = ContentHash([9; 32]);
    let plan = plan(
        &facts,
        &graph,
        PlanSeeds {
            execution: &[CHANGED],
            declarations: &[],
            unscoped: false,
        },
    )
    .unwrap();
    let head = analyze(&facts, &graph, &plan, 1);
    assert_eq!(head.completion, Completion::Complete);
    assert!(head.guarded_roots.is_empty());
    let selected = selector_select::select(
        &facts,
        &graph,
        &facts,
        &graph,
        ChangeSeeds {
            base: vec![CHANGED],
            head: vec![CHANGED],
            ..Default::default()
        },
        Some(analyze(&facts, &graph, &plan, 1)),
        head,
    )
    .unwrap();
    assert_eq!(selected.decisions[0].status, SuiteDecisionStatus::Unknown);
    assert_ne!(
        selected.decisions[0].reasons & DECISION_OPAQUE_SHARED_HEAP,
        0
    );
    assert_eq!(selected.decisions[2].status, SuiteDecisionStatus::Excluded);
    assert_eq!(selected.decisions[4].status, SuiteDecisionStatus::Unknown);
}

#[test]
fn an_opaque_executed_root_removed_from_the_catalogue_cannot_authorize_omission() {
    let (mut facts, mut graph) = snapshot(true);
    facts
        .suites
        .retain(|suite| suite.symbol != SymbolId(OPAQUE_ROOT.0));
    facts.identity = ContentHash([10; 32]);
    graph.facts_identity = facts.identity;
    graph.identity = ContentHash([11; 32]);
    let plan = plan(
        &facts,
        &graph,
        PlanSeeds {
            execution: &[CHANGED],
            declarations: &[],
            unscoped: false,
        },
    )
    .unwrap();
    assert_eq!(
        plan.metrics().heap_roots,
        0,
        "the plan's declared execution universe omits the opaque writer"
    );
    assert!(plan.certifies_unaffected(SCALAR));
    let extra = [ExecutionRoot {
        node: OPAQUE_ROOT,
        receiver: SymbolId(OPAQUE_ROOT.0),
    }];
    for base_extra in [false, true] {
        for planned in [false, true] {
            let base = analyze_extra(
                &facts,
                &graph,
                &plan,
                1,
                if base_extra { &extra } else { &[] },
            );
            let head = analyze_extra(
                &facts,
                &graph,
                &plan,
                1,
                if base_extra { &[] } else { &extra },
            );
            let actual = if base_extra { &base } else { &head };
            assert!(actual.guarded_roots.contains(&OPAQUE_ROOT));
            let seeds = ChangeSeeds {
                base: vec![CHANGED],
                head: vec![CHANGED],
                ..Default::default()
            };
            let result = if planned {
                select_with_plan(
                    &facts,
                    &graph,
                    &facts,
                    &graph,
                    seeds,
                    Some(base),
                    head,
                    Some(&plan),
                    &plan,
                )
            } else {
                selector_select::select(&facts, &graph, &facts, &graph, seeds, Some(base), head)
            };
            assert!(
                result.is_err(),
                "base_extra={base_extra}, planned={planned}"
            );
        }
    }
}

#[test]
fn declared_roots_allow_all_root_execution_but_not_another_receiver_identity() {
    let (facts, graph) = snapshot(true);
    let plan = plan(
        &facts,
        &graph,
        PlanSeeds {
            execution: &[CHANGED],
            declarations: &[],
            unscoped: false,
        },
    )
    .unwrap();
    assert!(plan.certifies_unaffected(SCALAR));
    for planned in [false, true] {
        for wrong_receiver in [false, true] {
            let extra = [ExecutionRoot {
                node: SCALAR,
                receiver: SymbolId(if wrong_receiver { READER.0 } else { SCALAR.0 }),
            }];
            let base = analyze(&facts, &graph, &plan, 1);
            let head = analyze_extra(&facts, &graph, &plan, 1, &extra);
            let seeds = ChangeSeeds {
                base: vec![CHANGED],
                head: vec![CHANGED],
                ..Default::default()
            };
            let result = if planned {
                select_with_plan(
                    &facts,
                    &graph,
                    &facts,
                    &graph,
                    seeds,
                    Some(base),
                    head,
                    Some(&plan),
                    &plan,
                )
            } else {
                selector_select::select(&facts, &graph, &facts, &graph, seeds, Some(base), head)
            };
            if wrong_receiver {
                assert!(result.is_err(), "wrong receiver, planned={planned}");
            } else {
                assert_eq!(
                    result.unwrap().decisions[2].status,
                    SuiteDecisionStatus::Excluded
                );
            }
        }
    }
}
