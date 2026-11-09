use super::*;
use selector_facts::{
    BodyRecord, FactBuilder, FileRecord, IssueRecord, OperationRecord, SuiteRecord,
};
use selector_graph::{GraphIssue, NodeRecord};
use selector_plan::classpath_absence::{
    Evidence, Side, SourceProduct, StableCompilation, SuiteClasspath,
};

struct Fixture {
    facts: FactSnapshot,
    graph: ProgramGraph,
}
impl Fixture {
    fn new() -> Self {
        let mut b = FactBuilder::new();
        for (path, context, name, kind) in [
            ("Changed.scala", "changed:compile", "p/Changed#", 13),
            ("Suite.scala", "owner:test", "p/Suite#", 13),
            ("Other.scala", "owner:test", "p/Other#", 13),
        ] {
            let path = b.intern(path).unwrap();
            let context = b.intern(context).unwrap();
            let source = b.intern("class C").unwrap();
            let file = FileId(b.facts.files.len() as u32);
            b.facts.files.push(FileRecord {
                path,
                context,
                source,
                revision: StrId::NONE,
                source_hash: ContentHash([3; 32]),
                flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
            });
            let id = b.ensure_symbol(name, file).unwrap();
            let row = &mut b.facts.symbols[id.index()];
            row.file = file;
            row.context = context;
            row.flags = SYMBOL_DEFINED;
            row.kind = kind;
            if file.0 > 0 {
                let name = b
                    .intern(if file.0 == 1 { "p.Suite" } else { "p.Other" })
                    .unwrap();
                b.facts.suites.push(SuiteRecord {
                    name,
                    symbol: id,
                    file,
                    flags: 0,
                });
            }
        }
        b.facts.identity = ContentHash([1; 32]);
        let facts = b.finish().unwrap();
        let mut graph = ProgramGraph {
            facts_identity: facts.identity,
            identity: ContentHash([2; 32]),
            ..Default::default()
        };
        for (i, symbol) in facts.symbols.iter().enumerate() {
            graph.nodes.push(NodeRecord {
                symbol: SymbolId(i as u32),
                file: symbol.file,
                body: BodyId::NONE,
                flags: 0,
            });
            graph.symbol_nodes.push(NodeId(i as u32));
        }
        graph.index().unwrap();
        Self { facts, graph }
    }
    fn seeds(&self) -> ChangeSeeds {
        ChangeSeeds {
            base: vec![NodeId(0)],
            head: vec![NodeId(0)],
            base_compile: vec![NodeId(0)],
            head_compile: vec![NodeId(0)],
            change_scope: Some(SourceChangeScope {
                mode: SourceChangeMode::RequestedPaths,
                requested_paths: vec!["Changed.scala".into()],
                outside_count: 1,
                outside: vec![SourceFileDelta {
                    base_file: FileId(2),
                    head_file: FileId(2),
                }],
            }),
            ..Default::default()
        }
    }
    fn source_issue(&mut self) -> Obligation {
        self.facts.operations.push(OperationRecord {
            body: BodyId(0),
            opcode: Opcode::Unknown,
            target: SymbolId::NONE,
            dest: ValueId::NONE,
            a: ValueId::NONE,
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span::default(),
            flags: 0,
        });
        self.facts.bodies.push(BodyRecord {
            symbol: SymbolId(0),
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange { start: 0, len: 1 },
            parameters: IdRange::default(),
            body_hash: ContentHash([11; 32]),
            flags: 0,
        });
        self.graph.nodes[0].body = BodyId(0);
        self.facts.issues.push(IssueRecord {
            kind: IssueKind::UnknownExecution,
            file: FileId(0),
            symbol: SymbolId(0),
            detail: StrId::NONE,
        });
        self.graph.issues.push(GraphIssue {
            kind: IssueKind::UnknownExecution,
            node: NodeId(0),
            file: FileId(0),
            symbol: SymbolId(0),
            detail: StrId::NONE,
        });
        Obligation {
            kind: IssueKind::UnknownExecution,
            file: FileId(0),
            symbol: SymbolId(0),
            detail: StrId::NONE,
        }
    }
    fn plan(&self, seeds: &ChangeSeeds) -> Plan {
        self.plan_with_compilation(seeds, &[], SelectionContract::owning_test_classpath())
    }
    fn plan_with_compilation(
        &self,
        seeds: &ChangeSeeds,
        stable_compilation: &[StableCompilation],
        contract: SelectionContract,
    ) -> Plan {
        // Normalized records represent an already independently verified issuer;
        // actual product/classpath scanning has separate producer controls.
        let sources = [SourceProduct {
            file: FileId(0),
            owner_context: self.facts.files[0].context,
            products_identity: ContentHash([4; 32]),
            product_count: 32,
        }];
        let suites: Vec<_> = (0..2)
            .map(|i| SuiteClasspath {
                suite: SuiteId(i),
                owner_context: self.facts.files[1].context,
                classpath_identity: ContentHash([5; 32]),
                source_products_identity: ContentHash([6; 32]),
                absence_identity: ContentHash([7; 32]),
            })
            .collect();
        let evidence = Evidence {
            identity: ContentHash([8; 32]),
            facts_identity: self.facts.identity,
            capture_identity: ContentHash([9; 32]),
            runtime_contract_identity: ContentHash([10; 32]),
            source_products_identity: ContentHash([6; 32]),
            sources: &sources,
            product_files: &[],
            stable_compilation,
            suites: &suites,
        };
        Plan::new(
            Side {
                facts: &self.facts,
                graph: &self.graph,
                seeds: selector_plan::PlanSeeds {
                    execution: &seeds.base,
                    declarations: &seeds.base_compile,
                    unscoped: seeds.conservative,
                },
                evidence,
            },
            Side {
                facts: &self.facts,
                graph: &self.graph,
                seeds: selector_plan::PlanSeeds {
                    execution: &seeds.head,
                    declarations: &seeds.head_compile,
                    unscoped: seeds.conservative,
                },
                evidence,
            },
            classpath_absence_scope(&self.facts, &self.graph, &self.facts, &self.graph, seeds)
                .unwrap(),
            contract,
        )
        .unwrap()
    }
    fn analysis(&self, affected: Vec<NodeId>, capped: bool) -> AnalysisResult {
        AnalysisResult {
            snapshot: self.graph.identity,
            completion: if capped {
                Completion::ResourceLimited
            } else {
                Completion::Conservative
            },
            affected,
            witnesses: vec![],
            derived_edges: vec![],
            obligations: vec![],
            guarded_roots: vec![NodeId(1), NodeId(2)],
            unscoped_uncertainty: capped,
            evidence: Default::default(),
            compilation: Default::default(),
            metrics: Default::default(),
        }
    }
    fn select(
        &self,
        seeds: ChangeSeeds,
        p: &Plan,
        head: AnalysisResult,
    ) -> Result<SelectionResult, Error> {
        select_with_classpath_absence(
            &self.facts,
            &self.graph,
            &self.facts,
            &self.graph,
            seeds,
            Some(self.analysis(vec![], true)),
            head,
            p,
        )
    }
}

#[test]
fn paired_cp_proof_excludes_without_relabeling_capped_guarded_execution() {
    let f = Fixture::new();
    let seeds = f.seeds();
    let p = f.plan(&seeds);
    let selected = f.select(seeds, &p, f.analysis(vec![], true)).unwrap();
    assert!(selected.suites.is_empty());
    assert_eq!(selected.completion, Completion::ResourceLimited);
    assert_eq!(selected.head.completion, Completion::ResourceLimited);
    assert!(selected.head.unscoped_uncertainty);
    assert_eq!(selected.head.guarded_roots, [NodeId(1), NodeId(2)]);
    assert_eq!(selected.selection_contract.bits(), 1008);
    assert_eq!(selected.change_scope.as_ref().unwrap().outside_count, 1);
    for d in &selected.decisions {
        assert_eq!(d.status, SuiteDecisionStatus::Excluded);
        assert!(!d.guarded);
        assert_ne!(d.reasons & DECISION_CLASSPATH_ABSENCE, 0);
        assert_ne!(d.reasons & DECISION_RESOURCE_LIMIT, 0);
        assert_ne!(d.reasons & DECISION_SCOPED_GUARD, 0);
        assert_eq!(
            d.reasons & (DECISION_COMPLETE_UNAFFECTED | DECISION_CERTIFIED_EXCLUSION),
            0
        );
        assert_eq!(d.head_exclusion.unwrap().assumptions, 1008);
        assert_eq!(d.base_exclusion.unwrap().assumptions, 1008);
    }
}

#[test]
fn observed_source_callback_impact_always_wins_over_unavailable_product_proof() {
    let f = Fixture::new();
    let seeds = f.seeds();
    let p = f.plan(&seeds);
    let selected = f
        .select(seeds, &p, f.analysis(vec![NodeId(1)], true))
        .unwrap();
    assert_eq!(selected.decisions[0].status, SuiteDecisionStatus::Required);
    assert_eq!(
        selected.decisions[0].reasons & DECISION_CLASSPATH_ABSENCE,
        0
    );
    assert!(selected.decisions[0].head_exclusion.is_none());
    assert_eq!(selected.decisions[1].status, SuiteDecisionStatus::Excluded);
    let seeds = f.seeds();
    let p = f.plan(&seeds);
    let base = f.analysis(vec![NodeId(2)], true);
    let selected = select_with_classpath_absence(
        &f.facts,
        &f.graph,
        &f.facts,
        &f.graph,
        seeds,
        Some(base),
        f.analysis(vec![], true),
        &p,
    )
    .unwrap();
    assert_eq!(selected.decisions[1].status, SuiteDecisionStatus::Required);
}

#[test]
fn additional_input_uncertainty_and_native_resource_seeds_block_reuse() {
    let f = Fixture::new();
    let seeds = f.seeds();
    let p = f.plan(&seeds);
    let mut extra = f.seeds();
    extra.head.push(NodeId(1));
    assert!(f.select(extra, &p, f.analysis(vec![], true)).is_err());
    let mut extra = f.seeds();
    extra.conservative = true;
    assert!(f.select(extra, &p, f.analysis(vec![], true)).is_err());
    let mut extra = f.seeds();
    extra.head_obligations.push(Obligation {
        kind: IssueKind::UnknownExecution,
        file: FileId::NONE,
        symbol: SymbolId::NONE,
        detail: StrId::NONE,
    });
    assert!(f.select(extra, &p, f.analysis(vec![], true)).is_err());
    let mut extra = f.seeds();
    extra.change_scope.as_mut().unwrap().outside_count = 2;
    assert!(f.select(extra, &p, f.analysis(vec![], true)).is_err());
    let mut extra = f.seeds();
    extra.change_scope.as_mut().unwrap().mode = SourceChangeMode::SnapshotDelta;
    assert!(f.select(extra, &p, f.analysis(vec![], true)).is_err());
    assert!(
        select_with_classpath_absence(
            &f.facts,
            &f.graph,
            &f.facts,
            &f.graph,
            f.seeds(),
            None,
            f.analysis(vec![], true),
            &p
        )
        .is_err()
    );
}

fn retention(f: &Fixture) -> ChangeGuardCause {
    ChangeGuardCause {
        side: SnapshotSide::Head,
        reason: ChangeGuardReason::ExternalInput,
        kind: IssueKind::UnsupportedModel,
        file: FileId(1),
        symbol: SymbolId(1),
        detail: StrId::NONE,
        path: None,
        external: Some(Box::new(ExternalGuardDetail {
            reason: "explicit_suite_retention".into(),
            message: "outside functional contract".into(),
            suite_name: Some(f.facts.text(f.facts.suites[0].name).to_owned()),
            schema_path: None,
            operation_path: None,
            verb: None,
        })),
    }
}

#[test]
fn explicit_retention_is_not_overridden_while_other_suite_can_be_excluded() {
    let f = Fixture::new();
    let mut seeds = f.seeds();
    seeds.guard_causes.push(retention(&f));
    let p = f.plan(&seeds);
    let selected = f.select(seeds, &p, f.analysis(vec![], true)).unwrap();
    assert_eq!(selected.decisions[0].status, SuiteDecisionStatus::Unknown);
    assert!(selected.decisions[0].guarded);
    assert!(selected.decisions[0].head_exclusion.is_none());
    assert_eq!(selected.decisions[1].status, SuiteDecisionStatus::Excluded);
    let mut seeds = f.seeds();
    let mut cause = retention(&f);
    cause.symbol = SymbolId(2);
    seeds.guard_causes.push(cause);
    assert!(f.select(seeds, &p, f.analysis(vec![], true)).is_err());
    let mut seeds = f.seeds();
    let mut cause = retention(&f);
    cause.external.as_mut().unwrap().reason = "changed_schema".into();
    seeds.guard_causes.push(cause);
    assert!(classpath_absence_scope(&f.facts, &f.graph, &f.facts, &f.graph, &seeds).is_err());
}

#[test]
fn strict_independent_selection_remains_guarded_without_optin_certificate() {
    let f = Fixture::new();
    let selected = select_with_semantics(
        &f.facts,
        &f.graph,
        &f.facts,
        &f.graph,
        f.seeds(),
        Some(f.analysis(vec![], true)),
        f.analysis(vec![], true),
        SuiteSemantics::Independent,
    )
    .unwrap();
    assert!(
        !selected
            .selection_contract
            .contains(SelectionContract::OWNING_TEST_CLASSPATH)
    );
    assert!(
        selected
            .decisions
            .iter()
            .all(|d| d.status == SuiteDecisionStatus::Unknown && d.head_exclusion.is_none())
    );
}

#[test]
fn exact_changed_source_recipe_issues_remain_visible_under_product_absence() {
    let mut f = Fixture::new();
    let issue = f.source_issue();
    let mut seeds = f.seeds();
    seeds.base_obligations.push(issue);
    seeds.head_obligations.push(issue);
    let p = f.plan(&seeds);
    let selected = f.select(seeds, &p, f.analysis(vec![], true)).unwrap();
    assert!(
        selected
            .decisions
            .iter()
            .all(|d| d.status == SuiteDecisionStatus::Excluded)
    );
    assert_eq!(selected.head.obligations, [issue]);
    assert_eq!(selected.base.as_ref().unwrap().obligations, [issue]);
    assert_eq!(
        selected.head.validate_execution_effects().unwrap(),
        EffectClosure::Open
    );
    assert_eq!(selected.head.completion, Completion::ResourceLimited);
    assert_eq!(selected.change_scope.as_ref().unwrap().outside_count, 1);
}

#[test]
fn unknown_native_unscoped_or_forged_input_issues_never_gain_source_scope() {
    for case in 0..9 {
        let mut f = Fixture::new();
        let mut issue = f.source_issue();
        match case {
            0 => issue.file = FileId::NONE,
            1 => issue.symbol = SymbolId::NONE,
            2 => issue.kind = IssueKind::InvalidInput,
            3 => issue.detail = f.facts.files[0].path,
            4 => f.graph.issues.clear(),
            5 => f.facts.issues.clear(),
            6 => f.facts.files[0].flags |= FILE_BINARY_SOURCE,
            7 => {
                // This is a genuine recipe issue, but in another source file.
                issue.file = FileId(1);
                issue.symbol = SymbolId(1);
                f.facts.bodies[0].file = FileId(1);
                f.facts.bodies[0].symbol = SymbolId(1);
                f.graph.nodes[0].body = BodyId::NONE;
                f.graph.nodes[1].body = BodyId(0);
                f.facts.issues[0].file = issue.file;
                f.facts.issues[0].symbol = issue.symbol;
                f.graph.issues[0].file = issue.file;
                f.graph.issues[0].symbol = issue.symbol;
                f.graph.issues[0].node = NodeId(1);
            }
            8 => f.facts.symbols[0].context = f.facts.files[1].context,
            _ => unreachable!(),
        }
        let mut seeds = f.seeds();
        seeds.head_obligations.push(issue);
        assert!(
            classpath_absence_scope(&f.facts, &f.graph, &f.facts, &f.graph, &seeds).is_err(),
            "case {case}"
        );
    }
}

#[test]
fn ordinary_compilation_keeps_required_precedence_and_all_original_seeds_sealed() {
    let f = Fixture::new();
    let mut seeds = f.seeds();
    // Normalized producer witness: Other.scala's recorded source and complete
    // compile inputs are paired-stable, despite an extra declaration seed.
    // This does not claim byte identity or suppress an observed execution hit.
    seeds.base_compile.push(NodeId(2));
    seeds.head_compile.push(NodeId(2));
    let stable = [StableCompilation {
        file: FileId(2),
        owner_context: f.facts.files[2].context,
        source_sha256: f.facts.files[2].source_hash,
        inputs_identity: ContentHash([31; 32]),
        paired_identity: ContentHash([32; 32]),
    }];
    let p = f.plan_with_compilation(
        &seeds,
        &stable,
        SelectionContract::owning_test_classpath_with_compilation(),
    );
    let pruned = f.seeds();
    assert!(f.select(pruned, &p, f.analysis(vec![], true)).is_err());
    let selected = f
        .select(seeds, &p, f.analysis(vec![NodeId(1)], true))
        .unwrap();
    assert_eq!(selected.selection_contract.bits(), 2032);
    assert_eq!(selected.decisions[0].status, SuiteDecisionStatus::Required);
    assert_eq!(
        selected.decisions[0].reasons & DECISION_CLASSPATH_ABSENCE,
        0
    );
    assert!(selected.decisions[0].head_exclusion.is_none());
    assert_eq!(selected.decisions[1].status, SuiteDecisionStatus::Excluded);
    assert_eq!(
        selected.decisions[1].head_exclusion.unwrap().assumptions,
        2032
    );
    assert_eq!(
        selected.decisions[1].base_exclusion.unwrap().assumptions,
        2032
    );
    assert_eq!(selected.head.completion, Completion::ResourceLimited);
    assert_eq!(selected.change_scope.as_ref().unwrap().outside_count, 1);
}
