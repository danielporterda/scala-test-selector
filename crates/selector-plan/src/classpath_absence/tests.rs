use super::*;
use selector_facts::{FactBuilder, FileRecord, SuiteRecord};
use selector_graph::NodeRecord;

struct Fixture {
    facts: FactSnapshot,
    graph: ProgramGraph,
    sources: Vec<SourceProduct>,
    product_files: Vec<ProductFile>,
    stable_compilation: Vec<StableCompilation>,
    suites: Vec<SuiteClasspath>,
}
impl Fixture {
    fn new() -> Self {
        let mut b = FactBuilder::new();
        for (path, context) in [
            ("Changed.scala", "changed:compile"),
            ("Suite.scala", "owner:test"),
        ] {
            let path = b.intern(path).unwrap();
            let context = b.intern(context).unwrap();
            let source = b.intern("class C").unwrap();
            b.facts.files.push(FileRecord {
                path,
                context,
                source,
                revision: StrId::NONE,
                source_hash: ContentHash([3; 32]),
                flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
            });
        }
        for (name, file, kind) in [("p/Changed#", FileId(0), 13), ("p/Suite#", FileId(1), 13)] {
            let id = b.ensure_symbol(name, file).unwrap();
            let context = b.facts.files[file.index()].context;
            let row = &mut b.facts.symbols[id.index()];
            row.file = file;
            row.context = context;
            row.kind = kind;
            row.flags = SYMBOL_DEFINED;
        }
        // Normalized binary views model separately verified issuer records.
        for (path, name, hash) in [
            ("out!/p/Changed.class", "p/Native.m().", 11),
            ("duplicate-out!/p/Changed.class", "p/Native.alias().", 11),
            ("out!/p/Other.class", "p/Native.other().", 12),
        ] {
            let file = FileId(b.facts.files.len() as u32);
            let path = b.intern(path).unwrap();
            let context = b.facts.files[0].context;
            b.facts.files.push(FileRecord {
                path,
                context,
                source: StrId::NONE,
                revision: StrId::NONE,
                source_hash: ContentHash([hash; 32]),
                flags: FILE_BINARY_SOURCE,
            });
            let symbol = b.ensure_symbol(name, file).unwrap();
            let row = &mut b.facts.symbols[symbol.index()];
            row.file = file;
            row.context = context;
            row.kind = 3;
            row.flags = SYMBOL_NATIVE_BINARY;
        }
        let path = b.intern("Extra.scala").unwrap();
        let context = b.intern("extra:compile").unwrap();
        let source = b.intern("class Extra").unwrap();
        let file = FileId(b.facts.files.len() as u32);
        b.facts.files.push(FileRecord {
            path,
            context,
            source,
            revision: StrId::NONE,
            source_hash: ContentHash([20; 32]),
            flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
        });
        let symbol = b.ensure_symbol("p/Extra#", file).unwrap();
        let row = &mut b.facts.symbols[symbol.index()];
        row.file = file;
        row.context = context;
        row.kind = 13;
        row.flags = SYMBOL_DEFINED;
        let name = b.intern("p.Suite").unwrap();
        b.facts.suites.push(SuiteRecord {
            name,
            symbol: SymbolId(1),
            file: FileId(1),
            flags: 0,
        });
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
        Self {
            product_files: vec![],
            stable_compilation: vec![],
            sources: vec![SourceProduct {
                file: FileId(0),
                owner_context: facts.files[0].context,
                products_identity: ContentHash([4; 32]),
                product_count: 32,
            }],
            suites: vec![SuiteClasspath {
                suite: SuiteId(0),
                owner_context: facts.files[1].context,
                classpath_identity: ContentHash([5; 32]),
                source_products_identity: ContentHash([6; 32]),
                absence_identity: ContentHash([7; 32]),
            }],
            facts,
            graph,
        }
    }
    fn bind_products(&mut self) {
        self.product_files = (2..5)
            .map(|i| ProductFile {
                file: FileId(i),
                source_file: FileId(0),
                owner_context: self.facts.files[0].context,
                class_sha256: self.facts.files[i as usize].source_hash,
            })
            .collect();
    }
    fn side(&self) -> Side<'_> {
        Side {
            facts: &self.facts,
            graph: &self.graph,
            seeds: PlanSeeds {
                execution: &[NodeId(0)],
                declarations: &[NodeId(0)],
                unscoped: false,
            },
            evidence: Evidence {
                identity: ContentHash([8; 32]),
                facts_identity: self.facts.identity,
                capture_identity: ContentHash([9; 32]),
                runtime_contract_identity: ContentHash([10; 32]),
                source_products_identity: ContentHash([6; 32]),
                sources: &self.sources,
                product_files: &self.product_files,
                stable_compilation: &self.stable_compilation,
                suites: &self.suites,
            },
        }
    }
}
fn scope() -> SourceScope {
    SourceScope {
        requested_paths: vec!["Changed.scala".into()],
        outside_count: 0,
        outside: vec![],
    }
}

#[test]
fn added_source_absence_requires_the_paired_product_and_keeps_seed_checks() {
    let mut before = Fixture::new();
    let after = Fixture::new();
    before.facts.identity = ContentHash([20; 32]);
    before.graph.facts_identity = before.facts.identity;
    before.facts.files[0].path = before.facts.files[5].path;
    before.sources.clear();
    let mut base = before.side();
    base.seeds = PlanSeeds {
        execution: &[],
        declarations: &[],
        unscoped: false,
    };
    let contract = SelectionContract::owning_test_classpath();
    let mut absence = AbsentSource {
        path: "Changed.scala".into(),
        opposite_facts: after.facts.identity,
        absence_identity: ContentHash([21; 32]),
    };
    let issue = |base, row: &AbsentSource| {
        Plan::new_with_source_absence(
            base,
            after.side(),
            scope(),
            contract,
            std::slice::from_ref(row),
            &[],
        )
    };
    assert!(Plan::new(base, after.side(), scope(), contract).is_err());
    let plan = issue(base, &absence).unwrap();
    assert!(plan.certificate(false, SuiteId(0), NodeId(1)).is_some());
    assert!(plan.certificate(true, SuiteId(0), NodeId(1)).is_some());

    let mut unaccounted = base;
    unaccounted.seeds.execution = &[NodeId(0)];
    assert!(issue(unaccounted, &absence).is_err());
    absence.opposite_facts = before.facts.identity;
    assert!(issue(base, &absence).is_err());
    absence.opposite_facts = after.facts.identity;
    assert!(issue(after.side(), &absence).is_err());
}

#[test]
fn paired_certificate_binds_catalogue_seed_scope_and_preserves_strict_defaults() {
    let f = Fixture::new();
    let p = Plan::new(
        f.side(),
        f.side(),
        scope(),
        SelectionContract::owning_test_classpath(),
    )
    .unwrap();
    p.validate(
        &f.facts,
        &f.graph,
        &f.facts,
        &f.graph,
        f.side().seeds,
        f.side().seeds,
        &scope(),
    )
    .unwrap();
    assert!(p.certificate(true, SuiteId(0), NodeId(1)).is_some());
    assert_ne!(
        p.certificate(true, SuiteId(0), NodeId(1)),
        p.certificate(false, SuiteId(0), NodeId(1))
    );
    assert!(p.certificate(true, SuiteId(0), NodeId(0)).is_none());
    assert!(!SelectionContract::current(SuiteSemantics::Independent).contains(512));
    assert_eq!(p.contract().bits(), 1008);
    assert!(
        Plan::new(
            f.side(),
            f.side(),
            scope(),
            SelectionContract::current(SuiteSemantics::Independent)
        )
        .is_err()
    );
    assert!(
        Plan::new(
            f.side(),
            f.side(),
            scope(),
            SelectionContract::current(SuiteSemantics::SharedState)
        )
        .is_err()
    );
}

#[test]
fn stale_seed_scope_snapshot_and_private_content_transplants_fail() {
    let mut f = Fixture::new();
    let mut p = Plan::new(
        f.side(),
        f.side(),
        scope(),
        SelectionContract::owning_test_classpath(),
    )
    .unwrap();
    let mut changed = scope();
    changed.outside_count = 1;
    assert!(
        p.validate(
            &f.facts,
            &f.graph,
            &f.facts,
            &f.graph,
            f.side().seeds,
            f.side().seeds,
            &changed
        )
        .is_err()
    );
    let mut seeds = f.side().seeds;
    seeds.execution = &[];
    assert!(
        p.validate(
            &f.facts,
            &f.graph,
            &f.facts,
            &f.graph,
            seeds,
            f.side().seeds,
            &scope()
        )
        .is_err()
    );
    let original = f.graph.identity;
    f.graph.identity = ContentHash([44; 32]);
    assert!(
        p.validate(
            &f.facts,
            &f.graph,
            &f.facts,
            &f.graph,
            f.side().seeds,
            f.side().seeds,
            &scope()
        )
        .is_err()
    );
    f.graph.identity = original;
    p.head.suites[0].absence = ContentHash([55; 32]);
    assert!(
        p.validate(
            &f.facts,
            &f.graph,
            &f.facts,
            &f.graph,
            f.side().seeds,
            f.side().seeds,
            &scope()
        )
        .is_err()
    );
}

#[test]
fn unknown_ownership_empty_products_and_other_effective_seeds_are_not_absence() {
    let mut f = Fixture::new();
    f.sources[0].product_count = 0;
    assert!(
        Plan::new(
            f.side(),
            f.side(),
            scope(),
            SelectionContract::owning_test_classpath()
        )
        .is_err()
    );
    f.sources[0].product_count = 32;
    f.sources[0].owner_context = f.facts.files[1].context;
    assert!(
        Plan::new(
            f.side(),
            f.side(),
            scope(),
            SelectionContract::owning_test_classpath()
        )
        .is_err()
    );
    f.sources[0].owner_context = f.facts.files[0].context;
    let mut side = f.side();
    side.seeds.execution = &[NodeId(0), NodeId(1)];
    assert!(
        Plan::new(
            side,
            f.side(),
            scope(),
            SelectionContract::owning_test_classpath()
        )
        .is_err()
    );
    let mut side = f.side();
    side.seeds.unscoped = true;
    assert!(
        Plan::new(
            side,
            f.side(),
            scope(),
            SelectionContract::owning_test_classpath()
        )
        .is_err()
    );
}

#[test]
fn missing_suite_is_unproved_and_wrong_owner_or_source_aggregate_is_rejected() {
    let mut f = Fixture::new();
    f.suites.clear();
    let p = Plan::new(
        f.side(),
        f.side(),
        scope(),
        SelectionContract::owning_test_classpath(),
    )
    .unwrap();
    assert!(p.certificate(true, SuiteId(0), NodeId(1)).is_none());
    let other = Fixture::new();
    f.suites = other.suites;
    f.suites[0].owner_context = f.facts.files[0].context;
    assert!(
        Plan::new(
            f.side(),
            f.side(),
            scope(),
            SelectionContract::owning_test_classpath()
        )
        .is_err()
    );
    f.suites[0].owner_context = f.facts.files[1].context;
    f.suites[0].source_products_identity = ContentHash([88; 32]);
    assert!(
        Plan::new(
            f.side(),
            f.side(),
            scope(),
            SelectionContract::owning_test_classpath()
        )
        .is_err()
    );
}

#[test]
fn every_contextual_source_owner_and_outside_scope_qualifier_is_bound() {
    let mut f = Fixture::new();
    f.facts.files.push(f.facts.files[0].clone());
    let context = f.facts.files[1].context;
    f.facts.files.last_mut().unwrap().context = context;
    assert!(
        Plan::new(
            f.side(),
            f.side(),
            scope(),
            SelectionContract::owning_test_classpath()
        )
        .is_err()
    );
    let f = Fixture::new();
    let mut s = scope();
    s.outside_count = 2;
    s.outside.push((FileId(1), FileId(1)));
    let p = Plan::new(
        f.side(),
        f.side(),
        s.clone(),
        SelectionContract::owning_test_classpath(),
    )
    .unwrap();
    assert_eq!(p.scope().outside_count, 2);
    s.outside[0].0 = FileId::NONE;
    assert!(
        p.validate(
            &f.facts,
            &f.graph,
            &f.facts,
            &f.graph,
            f.side().seeds,
            f.side().seeds,
            &s
        )
        .is_err()
    );
}

#[test]
fn native_materializations_and_duplicate_views_need_exact_source_product_rows() {
    let mut f = Fixture::new();
    f.bind_products();
    // A compiler declaration still has the source file; its execution recipe
    // uses the independently verified class product file.
    f.graph.nodes[0].file = FileId(2);
    let p = Plan::new(
        f.side(),
        f.side(),
        scope(),
        SelectionContract::owning_test_classpath(),
    )
    .unwrap();
    assert!(p.certificate(true, SuiteId(0), NodeId(1)).is_some());
    // A native declaration uses the product file for both views.
    let mut side = f.side();
    side.seeds.execution = &[NodeId(2)];
    side.seeds.declarations = &[NodeId(2)];
    Plan::new(
        side,
        side,
        scope(),
        SelectionContract::owning_test_classpath(),
    )
    .unwrap();
    // Duplicate fact file IDs are admissible only for the same source, class
    // digest and context. This is not a different-class or cross-context alias.
    f.facts.symbols[2].file = FileId(3);
    let mut side = f.side();
    side.seeds.execution = &[NodeId(2)];
    side.seeds.declarations = &[NodeId(2)];
    Plan::new(
        side,
        side,
        scope(),
        SelectionContract::owning_test_classpath(),
    )
    .unwrap();
    f.facts.symbols[2].file = FileId(4);
    let mut side = f.side();
    side.seeds.execution = &[NodeId(2)];
    side.seeds.declarations = &[NodeId(2)];
    let error = Plan::new(
        side,
        side,
        scope(),
        SelectionContract::owning_test_classpath(),
    )
    .unwrap_err()
    .to_string();
    assert!(
        error.contains("node=2")
            && error.contains("node_file=2")
            && error.contains("symbol_file=4")
    );
}

#[test]
fn absent_unknown_wrong_hash_context_or_source_product_rows_cannot_cover_native_seeds() {
    for case in 0..7 {
        let mut f = Fixture::new();
        f.bind_products();
        f.graph.nodes[0].file = FileId(2);
        match case {
            0 => f.product_files.clear(),
            1 => f.product_files[0].class_sha256 = ContentHash([99; 32]),
            2 => f.product_files[0].owner_context = f.facts.files[1].context,
            3 => f.product_files[0].source_file = FileId(1),
            4 => f.facts.files[2].flags = 0,
            5 => f.product_files.push(f.product_files[0]),
            6 => f.facts.symbols[0].context = f.facts.files[1].context,
            _ => unreachable!(),
        }
        assert!(
            Plan::new(
                f.side(),
                f.side(),
                scope(),
                SelectionContract::owning_test_classpath()
            )
            .is_err(),
            "case {case}"
        );
    }
}

#[test]
fn product_inventory_is_part_of_the_private_paired_content_seal() {
    let mut f = Fixture::new();
    f.bind_products();
    f.graph.nodes[0].file = FileId(2);
    let mut p = Plan::new(
        f.side(),
        f.side(),
        scope(),
        SelectionContract::owning_test_classpath(),
    )
    .unwrap();
    p.head.product_files[0].source_file = FileId(1);
    assert!(
        p.validate(
            &f.facts,
            &f.graph,
            &f.facts,
            &f.graph,
            f.side().seeds,
            f.side().seeds,
            &scope()
        )
        .is_err()
    );
}

#[test]
fn verified_source_superset_can_cover_additional_effective_seeds() {
    let mut f = Fixture::new();
    let source = SourceProduct {
        file: FileId(5),
        owner_context: f.facts.files[5].context,
        products_identity: ContentHash([21; 32]),
        product_count: 1,
    };
    let mut side = f.side();
    side.seeds.execution = &[NodeId(0), NodeId(5)];
    side.seeds.declarations = &[NodeId(0), NodeId(5)];
    // The requested-source-only inventory cannot cover the additional input.
    assert!(
        Plan::new(
            side,
            side,
            scope(),
            SelectionContract::owning_test_classpath()
        )
        .is_err()
    );
    f.sources.push(source);
    let mut side = f.side();
    side.seeds.execution = &[NodeId(0), NodeId(5)];
    side.seeds.declarations = &[NodeId(0), NodeId(5)];
    let p = Plan::new(
        side,
        side,
        scope(),
        SelectionContract::owning_test_classpath(),
    )
    .unwrap();
    assert_eq!(p.scope().requested_paths, ["Changed.scala"]);
    assert_eq!(p.head.sources.len(), 2);
    assert!(p.certificate(true, SuiteId(0), NodeId(1)).is_some());
    // Every effective seed remains part of the paired seal.
    assert!(
        p.validate(
            &f.facts,
            &f.graph,
            &f.facts,
            &f.graph,
            f.side().seeds,
            side.seeds,
            &scope()
        )
        .is_err()
    );
}

#[test]
fn extra_source_inventory_cannot_replace_requested_coverage_or_admit_binary_inputs() {
    for case in 0..5 {
        let mut f = Fixture::new();
        f.sources.push(SourceProduct {
            file: FileId(5),
            owner_context: f.facts.files[5].context,
            products_identity: ContentHash([21; 32]),
            product_count: 1,
        });
        match case {
            0 => {
                f.sources.remove(0);
            }
            1 => f.facts.files[5].flags = SOURCE_VERIFIED,
            2 => f.sources[1].owner_context = f.facts.files[0].context,
            3 => f.sources[1].product_count = 0,
            4 => {
                f.sources[1].file = FileId(2);
                f.sources[1].owner_context = f.facts.files[2].context;
            }
            _ => unreachable!(),
        }
        assert!(
            Plan::new(
                f.side(),
                f.side(),
                scope(),
                SelectionContract::owning_test_classpath()
            )
            .is_err(),
            "case {case}"
        );
    }
}

fn stable_extra(f: &Fixture) -> StableCompilation {
    StableCompilation {
        file: FileId(5),
        owner_context: f.facts.files[5].context,
        source_sha256: f.facts.files[5].source_hash,
        inputs_identity: ContentHash([31; 32]),
        paired_identity: ContentHash([32; 32]),
    }
}

#[test]
fn explicit_compilation_premise_accounts_for_stable_extra_sources_without_seed_drops() {
    let mut f = Fixture::new();
    let stable = stable_extra(&f);
    f.stable_compilation.push(stable);
    let mut side = f.side();
    side.seeds.execution = &[NodeId(0), NodeId(5)];
    side.seeds.declarations = &[NodeId(0), NodeId(5)];
    assert!(
        Plan::new(
            side,
            side,
            scope(),
            SelectionContract::owning_test_classpath()
        )
        .is_err()
    );
    let p = Plan::new(
        side,
        side,
        scope(),
        SelectionContract::owning_test_classpath_with_compilation(),
    )
    .unwrap();
    // Only requested Changed.scala is in the runtime absence inventory. The
    // ordinary-compilation witness accounts for Extra.scala independently.
    assert_eq!(p.head.sources.len(), 1);
    assert_eq!(p.head.stable_compilation.len(), 1);
    assert_eq!(p.head.execution, [NodeId(0), NodeId(5)]);
    assert_eq!(p.head.declarations, [NodeId(0), NodeId(5)]);
    assert!(p.certificate(true, SuiteId(0), NodeId(1)).is_some());
    assert!(
        p.validate(
            &f.facts,
            &f.graph,
            &f.facts,
            &f.graph,
            f.side().seeds,
            side.seeds,
            &scope()
        )
        .is_err()
    );
}

#[test]
fn paired_compilation_requires_identical_source_input_and_pair_bindings() {
    for case in 0..6 {
        let mut before = Fixture::new();
        let stable = stable_extra(&before);
        before.stable_compilation.push(stable);
        let mut after = Fixture::new();
        let stable = stable_extra(&after);
        after.stable_compilation.push(stable);
        match case {
            0 => {
                after.facts.files[5].source_hash = ContentHash([44; 32]);
                after.stable_compilation[0].source_sha256 = ContentHash([44; 32]);
            }
            1 => after.stable_compilation[0].inputs_identity = ContentHash([45; 32]),
            2 => after.stable_compilation[0].paired_identity = ContentHash([46; 32]),
            3 => after.stable_compilation.clear(),
            4 => after.facts.files[5].path = after.facts.files[1].path,
            5 => after.stable_compilation[0].owner_context = after.facts.files[0].context,
            _ => unreachable!(),
        }
        assert!(
            Plan::new(
                before.side(),
                after.side(),
                scope(),
                SelectionContract::owning_test_classpath_with_compilation()
            )
            .is_err(),
            "case {case}"
        );
    }
}

#[test]
fn compilation_contract_never_waives_requested_sources_or_arbitrary_native_inputs() {
    for case in 0..5 {
        let mut f = Fixture::new();
        let stable = stable_extra(&f);
        f.stable_compilation.push(stable);
        match case {
            0 => {
                let r = &mut f.stable_compilation[0];
                r.file = FileId(0);
                r.owner_context = f.facts.files[0].context;
                r.source_sha256 = f.facts.files[0].source_hash;
            }
            1 => f.facts.files[5].flags = SOURCE_VERIFIED,
            2 => {
                let r = &mut f.stable_compilation[0];
                r.file = FileId(2);
                r.owner_context = f.facts.files[2].context;
                r.source_sha256 = f.facts.files[2].source_hash;
            }
            3 => f.stable_compilation[0].inputs_identity = ContentHash::default(),
            4 => f.stable_compilation.push(f.stable_compilation[0]),
            _ => unreachable!(),
        }
        assert!(
            Plan::new(
                f.side(),
                f.side(),
                scope(),
                SelectionContract::owning_test_classpath_with_compilation()
            )
            .is_err(),
            "case {case}"
        );
    }
    let mut f = Fixture::new();
    let stable = stable_extra(&f);
    f.stable_compilation.push(stable);
    let mut side = f.side();
    side.seeds.execution = &[NodeId(2)];
    assert!(
        Plan::new(
            side,
            side,
            scope(),
            SelectionContract::owning_test_classpath_with_compilation()
        )
        .is_err()
    );
}

#[test]
fn stable_compilation_rows_are_in_the_private_paired_seal() {
    let mut f = Fixture::new();
    let stable = stable_extra(&f);
    f.stable_compilation.push(stable);
    let mut p = Plan::new(
        f.side(),
        f.side(),
        scope(),
        SelectionContract::owning_test_classpath_with_compilation(),
    )
    .unwrap();
    p.head.stable_compilation[0].inputs_identity = ContentHash([99; 32]);
    assert!(
        p.validate(
            &f.facts,
            &f.graph,
            &f.facts,
            &f.graph,
            f.side().seeds,
            f.side().seeds,
            &scope()
        )
        .is_err()
    );
}
