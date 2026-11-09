//! Eager VAL storage over frozen compiler captures and explicitly normalized
//! compiler-shaped controls. These controls do not certify framework support or
//! claim that an unrelated ScalaTest suite can be excluded.
use selector_extract::{ExtractOptions, import_capture};
use selector_facts::{
    BodyRecord, FactBuilder, FactSnapshot, FileRecord, OccurrenceRecord, OperationRecord,
    ResultBoundRecord, SuiteRecord,
};
use selector_graph::ProgramGraph;
use selector_graph_build::source_recipes::augment_eager_val_accessors;
use selector_plan::{PlanSeeds, plan_guarded_with_semantics};
use selector_result::SuiteDecisionStatus;
use selector_select::{changed_seeds, select_with_plan};
use selector_solve::replay::{ReplayBundle, ReplayLimits, ReplayOptions, ReplayValue};
use selector_solve::{AnalysisSeeds, ExecutionRoot, QuerySession, SolveOptions};
use selector_types::*;
use sha2::{Digest, Sha256};
use std::path::PathBuf;

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/curried-synthetics")
}
fn operations(facts: &FactSnapshot, symbol: SymbolId) -> &[OperationRecord] {
    let bodies: Vec<_> = facts.bodies.iter().filter(|b| b.symbol == symbol).collect();
    assert_eq!(
        bodies.len(),
        1,
        "one recipe for {}",
        facts.symbol_name(symbol)
    );
    &facts.operations[bodies[0].operations.range()]
}
fn initializer(facts: &FactSnapshot, original: SymbolId) -> SymbolId {
    let name = facts.symbol_name(original);
    let path = facts.text(facts.files[facts.symbols[original.index()].file.index()].path);
    let expected = format!(
        "@selector:source-val-initializer/1:{}:{name}{}:{path}",
        name.len(),
        path.len()
    );
    let context = facts.symbols[original.index()].context;
    SymbolId(
        facts
            .symbols
            .iter()
            .position(|s| facts.text(s.name) == expected && s.context == context)
            .expect("distinct eager RHS initializer") as u32,
    )
}
fn assert_getter(facts: &FactSnapshot, symbol: SymbolId) {
    let rows = operations(facts, symbol);
    assert_eq!(rows.len(), 2);
    assert_eq!(rows[0].opcode, Opcode::LoadField);
    assert_eq!(
        rows[0].target, symbol,
        "the original compiler identity is the slot"
    );
    assert_eq!(rows[0].a, ValueId(0));
    assert_eq!(rows[1].opcode, Opcode::Return);
    assert_eq!(rows[1].a, rows[0].dest);
    let body = &facts.bodies[rows[0].body.index()];
    assert_eq!(body.flags & (BODY_INITIALIZER | BODY_LAZY), 0);
}

#[test]
fn frozen_compiler_val_stores_callback_and_both_reads_remain_getter_calls() {
    // This log was produced by the fixture's independent JVM validation. No
    // compiler or JVM is launched here, and no execution count is inferred from
    // the abstract solver's reevaluation counters.
    let log = std::fs::read_to_string(fixture().join("execution.log")).unwrap();
    assert!(log.lines().any(|line| line == "reused:16:32:32"));
    for workers in [1, 4] {
        let mut facts = import_capture(
            &fixture().join("documents.jsonl"),
            Some(&fixture().join("syntax.jsonl")),
            &ExtractOptions {
                workers,
                ..Default::default()
            },
        )
        .unwrap();
        let callback = facts
            .find_symbol("curriedcase/ReusedCallbackSuite#callback.")
            .unwrap();
        let actual = facts
            .find_symbol("curriedcase/SourceSuite#actual.")
            .unwrap();
        let original_callback = facts.symbols[callback.index()];
        let original_actual = facts.symbols[actual.index()];
        let old_bindings: Vec<_> = operations(&facts, callback)
            .iter()
            .filter(|o| o.opcode == Opcode::BindCallback)
            .map(|o| o.target)
            .collect();
        assert_eq!(old_bindings.len(), 1, "actual captured callback creation");
        let known = facts
            .find_symbol("curriedcase/SourceSuite#known().")
            .unwrap();
        assert!(operations(&facts, actual).iter().any(|o| o.target == known));
        assert!(augment_eager_val_accessors(&mut facts).unwrap() >= 2);
        for (symbol, original) in [(callback, original_callback), (actual, original_actual)] {
            assert_getter(&facts, symbol);
            assert_eq!(facts.symbols[symbol.index()].span, original.span);
            let init = initializer(&facts, symbol);
            let init_symbol = facts.symbols[init.index()];
            assert_eq!(
                (init_symbol.file, init_symbol.context, init_symbol.owner),
                (original.file, original.context, original.owner)
            );
            let rhs = operations(&facts, init);
            assert_ne!(
                facts.bodies[rhs[0].body.index()].flags & BODY_INITIALIZER,
                0
            );
            assert_eq!(
                rhs.iter()
                    .filter(|o| o.opcode == Opcode::StoreField && o.target == symbol)
                    .count(),
                1
            );
            assert!(
                rhs.iter()
                    .any(|o| o.opcode == Opcode::StoreField && o.a == ValueId(0))
            );
        }
        let rhs = operations(&facts, initializer(&facts, callback));
        assert_eq!(
            rhs.iter()
                .filter(|o| o.opcode == Opcode::BindCallback && o.target == old_bindings[0])
                .count(),
            1
        );
        assert!(
            operations(&facts, initializer(&facts, actual))
                .iter()
                .any(|o| o.target == known)
        );
        for name in ["first", "second"] {
            let reader = facts
                .find_symbol(&format!("curriedcase/ReusedCallbackSuite#{name}."))
                .unwrap();
            let rhs = operations(&facts, initializer(&facts, reader));
            assert!(
                rhs.iter()
                    .any(|o| matches!(o.opcode, Opcode::Call | Opcode::VirtualCall)
                        && o.target == callback)
            );
            assert!(
                !rhs.iter()
                    .any(|o| o.opcode == Opcode::BindCallback && o.target == old_bindings[0])
            );
        }
        let graph = selector_graph_build::build(&facts, &Default::default()).unwrap();
        for symbol in [callback, actual] {
            let owner = facts.symbols[symbol.index()].owner;
            let init = initializer(&facts, symbol);
            let init_node = graph.node_for_symbol(init).unwrap();
            let getter_node = graph.node_for_symbol(symbol).unwrap();
            assert!(
                graph
                    .edges
                    .iter()
                    .any(|edge| edge.source == graph.node_for_symbol(owner).unwrap()
                        && edge.target == init_node
                        && edge.kind == EdgeKind::Initialize)
            );
            assert!(
                !graph.edges.iter().any(|edge| edge.source == getter_node
                    && edge.target == init_node
                    && matches!(
                        edge.kind,
                        EdgeKind::Call | EdgeKind::Initialize | EdgeKind::VirtualCall
                    )),
                "reading the stored value must not execute its RHS again"
            );
        }
        assert_eq!(
            augment_eager_val_accessors(&mut facts).unwrap(),
            0,
            "idempotent storage normalization"
        );
        facts.validate().unwrap();
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
fn target(opcode: Opcode, symbol: SymbolId, dest: ValueId) -> OperationRecord {
    OperationRecord {
        target: symbol,
        dest,
        a: ValueId(0),
        ..op(opcode)
    }
}
struct Builder {
    b: FactBuilder,
    file: FileId,
    context: StrId,
}
impl Builder {
    fn symbol(&mut self, name: &str, kind: u32, owner: SymbolId, token: &str) -> SymbolId {
        let symbol = self.b.ensure_symbol(name, self.file).unwrap();
        let source = self
            .b
            .facts
            .text(self.b.facts.files[self.file.index()].source);
        let pattern = if kind == 13 {
            format!("class {token}")
        } else if token == "value" {
            format!("val {token}")
        } else {
            format!("def {token}")
        };
        let start = (source.find(&pattern).unwrap() + pattern.len() - token.len()) as u32;
        let row = &mut self.b.facts.symbols[symbol.index()];
        row.kind = kind;
        row.owner = owner;
        row.context = self.context;
        // Global ensure_symbol intentionally has no source-file authority.
        // These explicitly Defined normalized declarations own this document.
        row.file = self.file;
        row.flags = SYMBOL_DEFINED
            | if kind == 13 {
                SYMBOL_SCALA_PARENTS_COMPLETE
            } else {
                0
            };
        row.span = Span {
            start,
            end: start + token.len() as u32,
        };
        self.b.facts.occurrences.push(OccurrenceRecord {
            file: self.file,
            symbol,
            span: row.span,
            role: 2,
            ordinal: self.b.facts.occurrences.len() as u32,
        });
        symbol
    }
    fn body(&mut self, symbol: SymbolId, flags: u32, rows: Vec<OperationRecord>, hash: u8) {
        let body = BodyId(self.b.facts.bodies.len() as u32);
        let start = self.b.facts.operations.len() as u32;
        let len = self
            .b
            .facts
            .text(self.b.facts.files[self.file.index()].source)
            .len() as u32;
        self.b
            .facts
            .operations
            .extend(rows.into_iter().map(|mut row| {
                row.body = body;
                row
            }));
        self.b.facts.bodies.push(BodyRecord {
            symbol,
            file: self.file,
            span: Span { start: 0, end: len },
            name_span: self.b.facts.symbols[symbol.index()].span,
            operations: IdRange {
                start,
                len: self.b.facts.operations.len() as u32 - start,
            },
            parameters: IdRange::default(),
            body_hash: ContentHash([hash; 32]),
            flags,
        });
    }
}
#[derive(Clone, Copy)]
enum Payload {
    Callback,
    Object,
    Unknown,
}
struct Control {
    facts: FactSnapshot,
    owners: Vec<SymbolId>,
    vals: Vec<SymbolId>,
    changed: Vec<SymbolId>,
    readers: Vec<[SymbolId; 2]>,
}

fn control(head: bool, payload: Payload, contexts: usize, guarded: bool) -> Control {
    let mut f = Builder {
        b: FactBuilder::new(),
        file: FileId::NONE,
        context: StrId::NONE,
    };
    f.b.facts.revision =
        f.b.intern(if head { "val-head" } else { "val-base" })
            .unwrap();
    let mut owners = Vec::new();
    let mut vals = Vec::new();
    let mut changed = Vec::new();
    let mut readers = Vec::new();
    for index in 0..contexts {
        f.context =
            f.b.intern(&format!("normalized:source-val:{index}"))
                .unwrap();
        let source_text = format!(
            "// Normalized compiler-proof control, not a compiler capture.\nclass Owner {{ val value = () => {}(); def changed = (); def stable = (); def note = (); def first = value; def second = value; def flag = (); }} class Product {{ def run = (); }}",
            if head && index == 0 {
                "changed"
            } else {
                "stable"
            }
        );
        let source = f.b.intern(&source_text).unwrap();
        let path = f.b.intern(&format!("SourceVal{index}.scala")).unwrap();
        f.file = FileId(f.b.facts.files.len() as u32);
        f.b.facts.files.push(FileRecord {
            path,
            source,
            context: f.context,
            revision: f.b.facts.revision,
            source_hash: ContentHash(Sha256::digest(source_text.as_bytes()).into()),
            flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
        });
        let owner = f.symbol("valcase/Owner#", 13, SymbolId::NONE, "Owner");
        let val = f.symbol("valcase/Owner#value.", 3, owner, "value");
        f.b.facts.symbols[val.index()].properties = 1024;
        let ch = f.symbol("valcase/Owner#changed().", 3, owner, "changed");
        let st = f.symbol("valcase/Owner#stable().", 3, owner, "stable");
        let note = f.symbol("valcase/Owner#note().", 3, owner, "note");
        let flag = f.symbol("valcase/Owner#flag.", 20, owner, "flag");
        let first = f.symbol("valcase/Owner#first().", 3, owner, "first");
        let second = f.symbol("valcase/Owner#second().", 3, owner, "second");
        let product = f.symbol("valcase/Product#", 13, SymbolId::NONE, "Product");
        let run = f.symbol("valcase/Product#run().", 3, product, "run");
        f.body(ch, BODY_DEFERRED, vec![], 11);
        f.body(st, BODY_DEFERRED, vec![], 13);
        f.body(
            note,
            BODY_DEFERRED,
            vec![OperationRecord {
                target: flag,
                a: ValueId(0),
                b: ValueId::NONE,
                ..op(Opcode::StoreField)
            }],
            14,
        );
        f.body(
            run,
            BODY_DEFERRED,
            vec![target(Opcode::Call, ch, ValueId::NONE)],
            15,
        );
        let producer = match payload {
            Payload::Callback => target(
                Opcode::BindCallback,
                if head && index == 0 { ch } else { st },
                ValueId(1),
            ),
            Payload::Object => target(Opcode::Allocate, product, ValueId(1)),
            Payload::Unknown => OperationRecord {
                dest: ValueId(1),
                ..op(Opcode::Assign)
            },
        };
        f.body(
            val,
            BODY_INITIALIZER,
            vec![
                target(Opcode::Call, note, ValueId::NONE),
                producer,
                OperationRecord {
                    a: ValueId(1),
                    ..op(Opcode::Return)
                },
            ],
            if head && index == 0 { 24 } else { 21 },
        );
        for reader in [first, second] {
            f.body(
                reader,
                BODY_DEFERRED,
                vec![
                    target(Opcode::Call, val, ValueId(1)),
                    OperationRecord {
                        a: ValueId(1),
                        ..op(Opcode::Return)
                    },
                ],
                22,
            );
        }
        let mut rows = vec![
            target(Opcode::Initialize, val, ValueId::NONE),
            target(Opcode::Call, first, ValueId(2)),
            target(Opcode::Call, second, ValueId(3)),
        ];
        for value in [ValueId(2), ValueId(3)] {
            rows.push(match payload {
                Payload::Object => OperationRecord {
                    target: run,
                    a: value,
                    ..op(Opcode::VirtualCall)
                },
                _ => OperationRecord {
                    a: value,
                    ..op(Opcode::InvokeCallback)
                },
            });
        }
        if guarded {
            rows.insert(0, op(Opcode::Unknown));
        }
        f.body(owner, BODY_INITIALIZER, rows, 23);
        let name =
            f.b.intern(&format!("normalized.valcase.{index}.Owner"))
                .unwrap();
        f.b.facts.suites.push(SuiteRecord {
            name,
            symbol: owner,
            file: f.file,
            flags: 0,
        });
        owners.push(owner);
        vals.push(val);
        changed.push(ch);
        readers.push([first, second]);
    }
    Control {
        facts: f.b.finish().unwrap(),
        owners,
        vals,
        changed,
        readers,
    }
}

fn seal_build(facts: &mut FactSnapshot) -> ProgramGraph {
    let directory = tempfile::tempdir().unwrap();
    facts.identity =
        selector_facts::codec::write(&directory.path().join("facts.bin"), facts).unwrap();
    selector_graph_build::build(facts, &Default::default()).unwrap()
}
fn options(graph: &ProgramGraph, owners: &[SymbolId], workers: usize) -> SolveOptions {
    SolveOptions {
        workers,
        max_contexts: 20_000,
        max_steps: 500_000,
        memory_budget_bytes: 64 * 1024 * 1024,
        execution_roots: Some(
            owners
                .iter()
                .map(|&receiver| ExecutionRoot {
                    node: graph.node_for_symbol(receiver).unwrap(),
                    receiver,
                })
                .collect(),
        ),
        ..Default::default()
    }
}
fn returned(session: &QuerySession<'_>, graph: &ProgramGraph, symbol: SymbolId) -> ReplayValue {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("replay");
    let limits = ReplayLimits::default();
    session
        .export_replay(graph.node_for_symbol(symbol).unwrap(), None, &path, &limits)
        .unwrap();
    let bundle = ReplayBundle::read(&path, &limits).unwrap();
    let comparison = bundle.compare(&ReplayOptions::default()).unwrap();
    assert!(comparison.equal);
    comparison.expected.value
}

#[test]
fn actual_adapter_preserves_callback_and_object_payload_identity_across_two_reads() {
    for payload in [Payload::Callback, Payload::Object] {
        for workers in [1, 4] {
            let mut c = control(true, payload, 1, true);
            assert_eq!(augment_eager_val_accessors(&mut c.facts).unwrap(), 1);
            let val = c.vals[0];
            let init = initializer(&c.facts, val);
            assert_getter(&c.facts, val);
            let rhs = operations(&c.facts, init);
            assert_eq!(
                rhs.iter().filter(|o| o.opcode == Opcode::Call).count(),
                1,
                "one effectful RHS recipe; getter reads never contain that call"
            );
            let store = rhs
                .iter()
                .find(|o| o.opcode == Opcode::StoreField && o.target == val)
                .unwrap();
            assert_eq!((store.a, store.b), (ValueId(0), ValueId(1)));
            let owner_rows = operations(&c.facts, c.owners[0]);
            assert!(
                owner_rows
                    .iter()
                    .any(|o| o.opcode == Opcode::Initialize && o.target == init)
            );
            assert!(
                !owner_rows
                    .iter()
                    .any(|o| o.opcode == Opcode::Initialize && o.target == val)
            );
            assert_eq!(
                owner_rows[0].opcode,
                Opcode::Unknown,
                "existing initialization guard and order retained"
            );
            let graph = seal_build(&mut c.facts);
            let mut session =
                QuerySession::new(&c.facts, &graph, &options(&graph, &c.owners, workers)).unwrap();
            let result = session
                .analyze(&[graph.node_for_symbol(c.changed[0]).unwrap()])
                .unwrap();
            assert_ne!(result.completion, Completion::ResourceLimited);
            assert!(result.contains(graph.node_for_symbol(c.owners[0]).unwrap()));
            assert!(
                result
                    .guarded_roots
                    .contains(&graph.node_for_symbol(c.owners[0]).unwrap()),
                "storage precision must not erase the existing initialization guard"
            );
            let first = returned(&session, &graph, c.readers[0][0]);
            let second = returned(&session, &graph, c.readers[0][1]);
            assert_eq!(
                first, second,
                "both getters return the same stored payload, including its allocation/capture identity"
            );
            assert!(first.atoms.iter().any(|a| a.kind
                == if matches!(payload, Payload::Callback) {
                    2
                } else {
                    1
                }));
            let getter_value = returned(&session, &graph, val);
            assert_eq!(first, getter_value);
        }
    }
}

#[test]
fn changed_rhs_is_required_with_workers_one_and_four_without_merging_context_slots() {
    for workers in [1, 4] {
        let mut base = control(false, Payload::Callback, 2, false);
        let mut head = control(true, Payload::Callback, 2, false);
        assert_eq!(augment_eager_val_accessors(&mut base.facts).unwrap(), 2);
        assert_eq!(augment_eager_val_accessors(&mut head.facts).unwrap(), 2);
        assert_ne!(head.vals[0], head.vals[1]);
        assert_eq!(
            head.facts.symbol_name(head.vals[0]),
            head.facts.symbol_name(head.vals[1])
        );
        assert_ne!(
            head.facts.symbols[head.vals[0].index()].context,
            head.facts.symbols[head.vals[1].index()].context
        );
        let bg = seal_build(&mut base.facts);
        let hg = seal_build(&mut head.facts);
        let seeds =
            changed_seeds(&base.facts, &bg, &head.facts, &hg, &["SourceVal0.scala"]).unwrap();
        assert!(!seeds.conservative, "{:#?}", seeds.guard_causes);
        let bp = plan_guarded_with_semantics(
            &base.facts,
            &bg,
            PlanSeeds {
                execution: &seeds.base,
                declarations: &seeds.base_compile,
                unscoped: false,
            },
            &[],
            SuiteSemantics::Independent,
        )
        .unwrap();
        let hp = plan_guarded_with_semantics(
            &head.facts,
            &hg,
            PlanSeeds {
                execution: &seeds.head,
                declarations: &seeds.head_compile,
                unscoped: false,
            },
            &[],
            SuiteSemantics::Independent,
        )
        .unwrap();
        let analyze = |facts: &FactSnapshot,
                       graph: &ProgramGraph,
                       owners: &[SymbolId],
                       execution: &[NodeId],
                       declarations: &[NodeId]| {
            QuerySession::new(facts, graph, &options(graph, owners, workers))
                .unwrap()
                .analyze_typed(AnalysisSeeds {
                    execution,
                    declarations,
                })
                .unwrap()
        };
        let before = analyze(
            &base.facts,
            &bg,
            &base.owners,
            bp.execution_seeds(),
            bp.declaration_seeds(),
        );
        let after = analyze(
            &head.facts,
            &hg,
            &head.owners,
            hp.execution_seeds(),
            hp.declaration_seeds(),
        );
        assert_ne!(after.completion, Completion::ResourceLimited);
        assert!(after.contains(hg.node_for_symbol(head.owners[0]).unwrap()));
        assert!(
            !after.contains(hg.node_for_symbol(head.owners[1]).unwrap()),
            "different compiler contexts/receivers must not share a stored callback"
        );
        let selection = select_with_plan(
            &base.facts,
            &bg,
            &head.facts,
            &hg,
            seeds,
            Some(before),
            after,
            Some(&bp),
            &hp,
        )
        .unwrap();
        assert_eq!(selection.decisions[0].status, SuiteDecisionStatus::Required);
        // The second normalized root has no framework-support certificate. It
        // is deliberately not asserted Excluded to manufacture a positive.
    }
}

#[test]
fn unknown_rhs_stays_unknown_data_and_its_actual_callback_consumer_stays_guarded() {
    let mut c = control(false, Payload::Unknown, 1, false);
    assert_eq!(augment_eager_val_accessors(&mut c.facts).unwrap(), 1);
    let graph = seal_build(&mut c.facts);
    let mut session = QuerySession::new(&c.facts, &graph, &options(&graph, &c.owners, 1)).unwrap();
    let result = session.analyze(&[]).unwrap();
    assert_ne!(result.completion, Completion::ResourceLimited);
    assert!(
        result
            .guarded_roots
            .contains(&graph.node_for_symbol(c.owners[0]).unwrap())
    );
    let value = returned(&session, &graph, c.vals[0]);
    assert_ne!(
        value.unknown, 0,
        "unknown RHS is TOP, not an empty initialized field"
    );
    assert!(
        session
            .first_runtime_issue_sites()
            .any(
                |(_, node, site)| node == graph.node_for_symbol(c.owners[0]).unwrap()
                    && site.reason == selector_issue::RuntimeIssueReason::UnknownCallbackValue
            )
    );
}

#[test]
fn unsupported_source_shapes_are_not_rewritten_or_claimed_as_backing_storage() {
    for case in 0..15 {
        let mut c = control(false, Payload::Callback, 1, false);
        let val = c.vals[0];
        let bid = c.facts.bodies.iter().position(|b| b.symbol == val).unwrap();
        match case {
            0 => c.facts.symbols[val.index()].properties = 0, // custom def
            1 => c.facts.symbols[val.index()].properties |= 64, // lazy val
            2 => c.facts.symbols[val.index()].properties |= 2048, // var
            3 => c.facts.symbols[val.index()].properties |= 4, // abstract
            4 => c.facts.bodies[bid].flags |= BODY_LAZY,
            5 => c.facts.occurrences.retain(|o| o.symbol != val),
            6 => {
                let row = *c
                    .facts
                    .occurrences
                    .iter()
                    .find(|o| o.symbol == val)
                    .unwrap();
                c.facts.occurrences.push(row);
            }
            7 => c.facts.files[0].flags &= !(SOURCE_VERIFIED | SYNTAX_VERIFIED),
            8 => c.facts.symbols[val.index()].flags &= !SYMBOL_DEFINED,
            9 => c.facts.symbols[c.owners[0].index()].flags &= !SYMBOL_DEFINED,
            10 => {
                let end = c.facts.bodies[bid].operations.range().end - 1;
                c.facts.operations[end].a = ValueId::NONE;
            }
            11 => {
                // An extra recipe must not be silently picked by first match.
                let mut body = c.facts.bodies[bid];
                body.operations = IdRange {
                    start: c.facts.operations.len() as u32,
                    len: 0,
                };
                c.facts.bodies.push(body);
            }
            12 => {
                c.facts.issues.push(selector_facts::IssueRecord {
                    kind: IssueKind::ContextConflict,
                    file: c.facts.symbols[val.index()].file,
                    symbol: val,
                    detail: StrId::NONE,
                });
            }
            13 => {
                let owner_bid = c
                    .facts
                    .bodies
                    .iter()
                    .position(|b| b.symbol == c.owners[0])
                    .unwrap();
                let parameter_start = c.facts.operands.len() as u32;
                c.facts.operands.push(ValueId(1));
                c.facts.bodies[owner_bid].parameters = IdRange {
                    start: parameter_start,
                    len: 1,
                };
                let first = c.facts.bodies[owner_bid].operations.start as usize;
                c.facts.operations[first] = OperationRecord {
                    body: c.facts.operations[first].body,
                    target: val,
                    dest: ValueId(1),
                    span: c.facts.symbols[val.index()].span,
                    ..op(Opcode::Parameter)
                };
            }
            14 => {
                let first = c.facts.bodies[bid].operations.start as usize;
                c.facts.operations[first] = OperationRecord {
                    body: BodyId(bid as u32),
                    a: ValueId(1),
                    ..op(Opcode::Return)
                };
            }
            _ => unreachable!(),
        }
        c.facts.validate().unwrap();
        let before_ops = format!("{:?}", c.facts.operations);
        let before_bodies = format!("{:?}", c.facts.bodies);
        assert_eq!(
            augment_eager_val_accessors(&mut c.facts).unwrap(),
            0,
            "case {case}"
        );
        assert_eq!(
            format!("{:?}", c.facts.operations),
            before_ops,
            "case {case}"
        );
        assert_eq!(
            format!("{:?}", c.facts.bodies),
            before_bodies,
            "case {case}"
        );
    }
}

#[test]
fn initializer_capture_parameters_and_forwarded_actuals_are_not_mistaken_for_getter_abi() {
    let mut c = control(false, Payload::Callback, 1, false);
    let val = c.vals[0];
    let bid = c.facts.bodies.iter().position(|b| b.symbol == val).unwrap();
    let start = c.facts.operands.len() as u32;
    c.facts.operands.extend([ValueId(3), ValueId(5)]);
    c.facts.bodies[bid].parameters = IdRange { start, len: 1 };
    let first = c.facts.bodies[bid].operations.start as usize;
    c.facts.operations[first] = OperationRecord {
        body: BodyId(bid as u32),
        dest: ValueId(3),
        flags: 1,
        ..op(Opcode::Parameter)
    };
    let end = c.facts.bodies[bid].operations.range().end - 1;
    c.facts.operations[end].a = ValueId(3);
    let owner = c
        .facts
        .bodies
        .iter()
        .find(|b| b.symbol == c.owners[0])
        .unwrap();
    let initialization = owner.operations.start as usize;
    c.facts.operations[initialization].arguments = IdRange {
        start: start + 1,
        len: 1,
    };
    assert_eq!(augment_eager_val_accessors(&mut c.facts).unwrap(), 1);
    let init = initializer(&c.facts, val);
    let rhs = c.facts.bodies.iter().find(|b| b.symbol == init).unwrap();
    assert_eq!(&c.facts.operands[rhs.parameters.range()], &[ValueId(3)]);
    let rows = operations(&c.facts, init);
    assert_eq!(
        (rows[0].opcode, rows[0].dest, rows[0].flags),
        (Opcode::Parameter, ValueId(3), 1)
    );
    assert!(
        rows.iter()
            .any(|o| o.opcode == Opcode::StoreField && o.target == val && o.b == ValueId(3))
    );
    let owner = operations(&c.facts, c.owners[0]);
    assert_eq!(
        (owner[0].opcode, owner[0].target),
        (Opcode::Initialize, init)
    );
    assert_eq!(&c.facts.operands[owner[0].arguments.range()], &[ValueId(5)]);
    let getter = c.facts.bodies.iter().find(|b| b.symbol == val).unwrap();
    assert_eq!(
        getter.parameters.len, 0,
        "RHS capture frame must not become a getter formal"
    );
    assert_getter(&c.facts, val);
    c.facts.validate().unwrap();
}

#[test]
fn operation_result_bounds_follow_actual_calls_across_initializer_and_getter_rebuild() {
    let mut c = control(false, Payload::Callback, 1, false);
    let val = c.vals[0];
    let first = c.readers[0][0];
    let old_body = c.facts.bodies.iter().find(|b| b.symbol == first).unwrap();
    let old = OperationId(old_body.operations.start);
    assert_eq!(c.facts.operations[old.index()].target, val);
    c.facts.bound_classes.push(c.owners[0]);
    c.facts.result_bounds.push(ResultBoundRecord {
        symbol: val,
        operation: old,
        classes: IdRange { start: 0, len: 1 },
    });
    assert_eq!(augment_eager_val_accessors(&mut c.facts).unwrap(), 1);
    c.facts.validate().unwrap();
    let remapped = c.facts.result_bounds[0].operation;
    let body = c.facts.bodies.iter().find(|b| b.symbol == first).unwrap();
    assert_eq!(remapped, OperationId(body.operations.start));
    assert_ne!(
        old, remapped,
        "inserted RHS store shifts the real later call site"
    );
    let actual = c.facts.operations[remapped.index()];
    assert_eq!(
        (
            actual.opcode,
            actual.target,
            c.facts.bodies[actual.body.index()].symbol
        ),
        (Opcode::Call, val, first)
    );
    assert_eq!(
        c.facts.bound_classes[c.facts.result_bounds[0].classes.range()],
        [c.owners[0]]
    );
}
