//! Normalized IR controls: two concrete scalar stores may both abstract to TOP.
//! Heap subscriptions can wake a reader without creating an affected call edge.
use super::*;
use selector_facts::{BodyRecord, FactBuilder, FileRecord, OperationRecord, SuiteRecord};
use selector_graph::{EdgeRecord, NodeRecord};
use selector_plan::{CandidatePlan, PlanSeeds, plan_guarded_with_semantics};
use selector_solve::{AnalysisSeeds, ExecutionRoot, QuerySession, SolveOptions};

const WRITER: NodeId = NodeId(0);
const READER: NodeId = NodeId(1);
const SCALAR: NodeId = NodeId(2);
const FIELD: SymbolId = SymbolId(3);

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

fn fixture(revision: u8) -> (FactSnapshot, ProgramGraph) {
    let mut builder = FactBuilder::new();
    let path = builder.intern("ScalarState.scala").unwrap();
    let source = builder
        .intern("class Writer; class Reader; class Scalar")
        .unwrap();
    builder.facts.files.push(FileRecord {
        path,
        source,
        context: StrId::NONE,
        revision: StrId::NONE,
        source_hash: ContentHash([1; 32]),
        flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
    });
    builder.facts.identity = ContentHash([revision; 32]);
    let mut graph = ProgramGraph {
        identity: ContentHash([revision + 10; 32]),
        facts_identity: builder.facts.identity,
        ..Default::default()
    };
    for (index, name) in ["p/Writer#", "p/Reader#", "p/Scalar#", "p/State.value."]
        .into_iter()
        .enumerate()
    {
        let symbol = builder.ensure_symbol(name, FileId(0)).unwrap();
        let record = &mut builder.facts.symbols[symbol.index()];
        record.kind = if index < 3 { 13 } else { 3 };
        record.flags = SYMBOL_DEFINED;
        if index == 3 {
            record.properties = 2048;
        }
        graph.nodes.push(NodeRecord {
            symbol,
            file: FileId(0),
            body: BodyId::NONE,
            flags: if index == 3 { NODE_EFFECTS_COMPLETE } else { 0 },
        });
        graph.symbol_nodes.push(NodeId(index as u32));
    }
    for (node, operations) in [
        (
            WRITER,
            vec![
                OperationRecord {
                    dest: ValueId(1),
                    ..op(Opcode::Assign)
                },
                OperationRecord {
                    target: FIELD,
                    b: ValueId(1),
                    flags: OP_STATIC_FIELD,
                    ..op(Opcode::StoreField)
                },
            ],
        ),
        (
            READER,
            vec![
                OperationRecord {
                    target: FIELD,
                    dest: ValueId(1),
                    flags: OP_STATIC_FIELD,
                    ..op(Opcode::LoadField)
                },
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::Return)
                },
            ],
        ),
        (SCALAR, vec![]),
    ] {
        let body = BodyId(builder.facts.bodies.len() as u32);
        let start = builder.facts.operations.len() as u32;
        for mut operation in operations {
            operation.body = body;
            builder.facts.operations.push(operation);
        }
        builder.facts.bodies.push(BodyRecord {
            symbol: SymbolId(node.0),
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange {
                start,
                len: builder.facts.operations.len() as u32 - start,
            },
            parameters: IdRange::default(),
            body_hash: ContentHash([if node == WRITER { revision } else { 9 }; 32]),
            flags: BODY_INITIALIZER,
        });
        graph.nodes[node.index()].body = body;
        let name = builder
            .intern(["p.Writer", "p.Reader", "p.Scalar"][node.index()])
            .unwrap();
        builder.facts.suites.push(SuiteRecord {
            name,
            symbol: SymbolId(node.0),
            file: FileId(0),
            flags: 0,
        });
    }
    for (source, operation) in [(WRITER, OperationId(1)), (READER, OperationId(2))] {
        graph.edges.push(EdgeRecord {
            source,
            target: NodeId(FIELD.0),
            kind: EdgeKind::Field,
            occurrence: OccurrenceId::NONE,
            operation,
            receiver: SymbolId::NONE,
            flags: 0,
        });
    }
    let facts = builder.finish().unwrap();
    graph.index().unwrap();
    (facts, graph)
}

fn make_plan(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    changed: &[NodeId],
    semantics: SuiteSemantics,
) -> CandidatePlan {
    plan_guarded_with_semantics(
        facts,
        graph,
        PlanSeeds {
            execution: changed,
            declarations: &[],
            unscoped: false,
        },
        &[],
        semantics,
    )
    .unwrap()
}

fn analyze(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    changed: &[NodeId],
    workers: usize,
) -> AnalysisResult {
    let roots: Vec<_> = [WRITER, READER, SCALAR]
        .into_iter()
        .map(|node| ExecutionRoot {
            node,
            receiver: SymbolId(node.0),
        })
        .collect();
    let options = SolveOptions {
        workers,
        execution_roots: Some(roots.clone().into()),
        max_contexts: 100,
        max_steps: 10_000,
        memory_budget_bytes: 16 * 1024 * 1024,
        ..Default::default()
    };
    let mut session = QuerySession::new(facts, graph, &options).unwrap();
    // Establish TOP as an actual value, not a missing-slot guard, before reading.
    session.execute(&roots[..1]).unwrap();
    session.execute(&roots).unwrap();
    let result = session
        .analyze_typed(AnalysisSeeds {
            execution: changed,
            declarations: &[],
        })
        .unwrap();
    assert_eq!(
        result.validate_execution_effects().unwrap(),
        EffectClosure::Closed
    );
    assert!(result.guarded_roots.is_empty());
    assert!(
        !result.affected.contains(&READER),
        "potential heap data influence is not an observed call witness"
    );
    result
}

fn decision(result: &SelectionResult, node: NodeId) -> &SuiteDecision {
    result
        .decisions
        .iter()
        .find(|decision| decision.node == node)
        .unwrap()
}

#[test]
fn closed_scalar_writes_retain_shared_readers_in_both_public_selection_paths() {
    for workers in [1, 2] {
        for semantics in [SuiteSemantics::SharedState, SuiteSemantics::Independent] {
            for planned in [false, true] {
                let (base, bg) = fixture(1);
                let (head, hg) = fixture(2);
                let bp = make_plan(&base, &bg, &[WRITER], semantics);
                let hp = make_plan(&head, &hg, &[WRITER], semantics);
                assert_eq!(
                    hp.potential_changed_heap_read_roots(&head, &hg).unwrap(),
                    vec![READER]
                );
                assert!(hp.certifies_unaffected(SCALAR));
                let before = analyze(&base, &bg, &[WRITER], workers);
                let after = analyze(&head, &hg, &[WRITER], workers);
                let seeds = ChangeSeeds {
                    base: vec![WRITER],
                    head: vec![WRITER],
                    ..Default::default()
                };
                let result = if planned {
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
                    select_with_semantics(
                        &base,
                        &bg,
                        &head,
                        &hg,
                        seeds,
                        Some(before),
                        after,
                        semantics,
                    )
                }
                .unwrap();
                assert_eq!(
                    decision(&result, WRITER).status,
                    SuiteDecisionStatus::Required
                );
                assert_eq!(
                    decision(&result, SCALAR).status,
                    SuiteDecisionStatus::Excluded
                );
                let reader = decision(&result, READER);
                if semantics == SuiteSemantics::SharedState {
                    assert_eq!(reader.status, SuiteDecisionStatus::Unknown);
                    assert!(reader.guarded);
                    assert_ne!(reader.reasons & DECISION_OPAQUE_SHARED_HEAP, 0);
                } else {
                    assert_eq!(reader.status, SuiteDecisionStatus::Excluded);
                    assert!(!reader.guarded);
                }
            }
        }
    }
}

#[test]
fn either_snapshot_changed_writer_retains_reader_but_no_change_has_no_heap_guard() {
    for (base_changed, head_changed) in [(true, false), (false, true), (false, false)] {
        let (base, bg) = fixture(1);
        let (head, hg) = fixture(2);
        let bseed = if base_changed { vec![WRITER] } else { vec![] };
        let hseed = if head_changed { vec![WRITER] } else { vec![] };
        let bp = make_plan(&base, &bg, &bseed, SuiteSemantics::SharedState);
        let hp = make_plan(&head, &hg, &hseed, SuiteSemantics::SharedState);
        let before = analyze(&base, &bg, &bseed, 1);
        let after = analyze(&head, &hg, &hseed, 1);
        let selected = select_with_plan(
            &base,
            &bg,
            &head,
            &hg,
            ChangeSeeds {
                base: bseed,
                head: hseed,
                ..Default::default()
            },
            Some(before),
            after,
            Some(&bp),
            &hp,
        )
        .unwrap();
        assert_eq!(
            decision(&selected, READER).status,
            if base_changed || head_changed {
                SuiteDecisionStatus::Unknown
            } else {
                SuiteDecisionStatus::Excluded
            }
        );
        assert_eq!(
            decision(&selected, SCALAR).status,
            SuiteDecisionStatus::Excluded
        );
    }
}

#[test]
fn changed_heap_retention_requires_sealed_plan_and_exact_snapshot() {
    let (facts, graph) = fixture(1);
    let mut plan = make_plan(&facts, &graph, &[WRITER], SuiteSemantics::SharedState);
    let (_, wrong_graph) = fixture(2);
    assert!(
        plan.potential_changed_heap_read_roots(&facts, &wrong_graph)
            .is_err()
    );
    plan.roots.clear();
    assert!(
        plan.potential_changed_heap_read_roots(&facts, &graph)
            .is_err()
    );
}
