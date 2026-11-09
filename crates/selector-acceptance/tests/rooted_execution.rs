//! Behavioral controls over normalized IR, mapped to retained rooted-execution
//! regressions. These are intentionally synthetic solver inputs, separate from
//! the actual compiler/JVM registration captures.
use selector_facts::*;
use selector_graph::{EdgeRecord, NodeRecord, ProgramGraph};
use selector_result::AnalysisResult;
use selector_solve::{ExecutionRoot, QuerySession, SolveOptions};
use selector_types::*;

struct Control {
    facts: FactSnapshot,
    graph: ProgramGraph,
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
fn call(target: u32) -> OperationRecord {
    OperationRecord {
        target: SymbolId(target),
        ..op(Opcode::Call)
    }
}
fn callback(target: u32, dest: u32) -> OperationRecord {
    OperationRecord {
        target: SymbolId(target),
        dest: ValueId(dest),
        ..op(Opcode::BindCallback)
    }
}
impl Control {
    fn new(names: &[&str]) -> Self {
        let mut builder = FactBuilder::new();
        for name in names {
            builder.ensure_symbol(name, FileId::NONE).unwrap();
        }
        let path = builder.intern("synthetic-rooted-control.scala").unwrap();
        let source = builder.intern("").unwrap();
        builder.facts.files.push(FileRecord {
            path,
            source,
            revision: StrId::NONE,
            context: StrId::NONE,
            source_hash: ContentHash::default(),
            flags: SOURCE_VERIFIED,
        });
        let facts = builder.finish().unwrap();
        let mut graph = ProgramGraph {
            facts_identity: facts.identity,
            ..Default::default()
        };
        for (i, _) in names.iter().enumerate() {
            graph.symbol_nodes.push(NodeId(i as u32));
            graph.nodes.push(NodeRecord {
                symbol: SymbolId(i as u32),
                file: FileId(0),
                body: BodyId::NONE,
                flags: 0,
            });
        }
        Self { facts, graph }
    }
    fn args(&mut self, values: &[u32]) -> IdRange {
        let start = self.facts.operands.len() as u32;
        self.facts
            .operands
            .extend(values.iter().map(|value| ValueId(*value)));
        IdRange {
            start,
            len: values.len() as u32,
        }
    }
    fn body(&mut self, node: u32, parameters: &[u32], mut operations: Vec<OperationRecord>) {
        let body = BodyId(self.facts.bodies.len() as u32);
        let parameters = self.args(parameters);
        let start = self.facts.operations.len() as u32;
        for operation in &mut operations {
            operation.body = body;
        }
        self.facts.bodies.push(BodyRecord {
            symbol: SymbolId(node),
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange {
                start,
                len: operations.len() as u32,
            },
            parameters,
            body_hash: ContentHash::default(),
            flags: 0,
        });
        self.facts.operations.extend(operations);
        self.graph.nodes[node as usize].body = body;
    }
    fn seal(&mut self) {
        for (source, node) in self.graph.nodes.iter().enumerate() {
            if node.body.is_none() {
                continue;
            }
            let body = self.facts.bodies[node.body.index()];
            for (offset, operation) in self.facts.operations[body.operations.range()]
                .iter()
                .enumerate()
            {
                let kind = match operation.opcode {
                    Opcode::Call => EdgeKind::Call,
                    Opcode::Allocate => EdgeKind::Construct,
                    _ => continue,
                };
                self.graph.edges.push(EdgeRecord {
                    source: NodeId(source as u32),
                    target: NodeId(operation.target.0),
                    kind,
                    operation: OperationId(body.operations.start + offset as u32),
                    occurrence: OccurrenceId::NONE,
                    receiver: SymbolId::NONE,
                    flags: 0,
                });
            }
        }
        self.graph.index().unwrap();
        self.facts.validate().unwrap();
        self.graph.validate().unwrap();
    }
}
fn root(node: u32) -> ExecutionRoot {
    ExecutionRoot {
        node: NodeId(node),
        receiver: SymbolId::NONE,
    }
}
fn active(result: &AnalysisResult, node: u32) -> bool {
    result
        .evidence
        .contexts
        .iter()
        .any(|context| context.node == NodeId(node))
}

#[test]
fn inventory_and_empty_execution_do_not_activate_unrequested_recipes() {
    let mut control = Control::new(&[
        "p/C.run().",
        "p/C.middle().",
        "p/C.changed().",
        "p/C.never().",
    ]);
    control.body(0, &[], vec![call(1)]);
    control.body(1, &[], vec![call(2)]);
    control.body(2, &[], vec![]);
    control.body(3, &[], vec![call(2)]);
    control.seal();
    let static_edges = control.graph.edges.clone();
    for workers in [1, 4] {
        let mut query = QuerySession::new(
            &control.facts,
            &control.graph,
            &SolveOptions {
                workers,
                ..Default::default()
            },
        )
        .unwrap();
        assert_eq!(query.context_count(), 0);
        assert_eq!(query.metrics().states, 0);
        query.execute(&[]).unwrap();
        assert_eq!(query.context_count(), 0);
        assert_eq!(query.metrics().states, 0);
        query.execute(&[root(0)]).unwrap();
        let result = query.analyze(&[NodeId(2)]).unwrap();
        assert!(result.contains(NodeId(0)));
        assert!(!result.contains(NodeId(3)));
        assert_eq!(query.context_count(), 3);
        assert!(!active(&result, 3));
        assert!(result.guarded_roots.is_empty());
        assert_eq!(
            control.graph.edges, static_edges,
            "query activation must not mutate inventory"
        );
    }
}

#[test]
fn stored_callback_capture_keeps_its_allocation_and_field_effects_dormant_until_invoked() {
    // stored/execute each construct Box(callback). Box stores the callback;
    // only execute reads and invokes it. The callback allocates Hidden, writes
    // a callback into Hidden.field, and calls changed.
    let mut control = Control::new(&[
        "p/C.stored().",
        "p/C.execute().",
        "@callback:changed",
        "p/Box#",
        "p/Hidden#",
        "p/Box#callback.",
        "p/Hidden#field.",
        "p/C.changed().",
    ]);
    control.facts.symbols[3].kind = 13;
    control.facts.symbols[4].kind = 13;
    for node in [0, 1] {
        let arguments = control.args(&[1]);
        let mut operations = vec![
            callback(2, 1),
            OperationRecord {
                target: SymbolId(3),
                dest: ValueId(2),
                arguments,
                ..op(Opcode::Allocate)
            },
        ];
        if node == 1 {
            operations.push(OperationRecord {
                target: SymbolId(5),
                a: ValueId(2),
                dest: ValueId(3),
                ..op(Opcode::LoadField)
            });
            operations.push(OperationRecord {
                a: ValueId(3),
                ..op(Opcode::InvokeCallback)
            });
        }
        control.body(node, &[], operations);
    }
    control.body(
        2,
        &[],
        vec![
            OperationRecord {
                target: SymbolId(4),
                dest: ValueId(1),
                ..op(Opcode::Allocate)
            },
            callback(7, 2),
            OperationRecord {
                target: SymbolId(6),
                a: ValueId(1),
                b: ValueId(2),
                ..op(Opcode::StoreField)
            },
            call(7),
        ],
    );
    control.body(
        3,
        &[1],
        vec![OperationRecord {
            target: SymbolId(5),
            a: ValueId(0),
            b: ValueId(1),
            ..op(Opcode::StoreField)
        }],
    );
    control.body(4, &[], vec![]);
    control.body(7, &[], vec![]);
    control.seal();
    for workers in [1, 4] {
        let mut query = QuerySession::new(
            &control.facts,
            &control.graph,
            &SolveOptions {
                workers,
                ..Default::default()
            },
        )
        .unwrap();
        query.execute(&[root(0)]).unwrap();
        let stored = query.analyze(&[NodeId(7)]).unwrap();
        assert!(!stored.contains(NodeId(0)));
        assert!(stored.guarded_roots.is_empty());
        // Detached evidence contains only paths relevant to the change seeds.
        // Request all inventory nodes to inspect every active context. Merely
        // naming an unexecuted seed does not create its execution context.
        let all_nodes: Vec<_> = (0..8).map(NodeId).collect();
        let stored_inventory = query.analyze(&all_nodes).unwrap();
        assert!(
            !stored_inventory.evidence.captures.is_empty(),
            "callback capture itself is retained"
        );
        assert!(!active(&stored_inventory, 2) && !active(&stored_inventory, 4));
        assert!(
            !stored_inventory
                .evidence
                .atoms
                .iter()
                .any(|atom| atom.kind == 1 && atom.symbol == SymbolId(4)),
            "dormant callback must not allocate Hidden"
        );
        query.execute(&[root(1)]).unwrap();
        let invoked = query.analyze(&[NodeId(7)]).unwrap();
        assert!(invoked.contains(NodeId(1)));
        assert!(!invoked.contains(NodeId(0)));
        let invoked_inventory = query.analyze(&all_nodes).unwrap();
        assert!(active(&invoked_inventory, 2) && active(&invoked_inventory, 4));
        assert!(
            invoked_inventory
                .evidence
                .atoms
                .iter()
                .any(|atom| atom.kind == 1 && atom.symbol == SymbolId(4))
        );
        assert!(invoked.guarded_roots.is_empty());
    }
}

#[test]
fn runtime_bridge_waits_for_its_source_to_become_reachable_in_a_later_execution() {
    let mut control = Control::new(&[
        "p/C.idle().",
        "p/C.run().",
        "p/Client#request().",
        "p/Client#helper().",
        "p/Handler#handle().",
        "p/Handler#changed().",
    ]);
    control.body(0, &[], vec![]);
    control.body(1, &[], vec![call(2)]);
    control.body(2, &[], vec![call(3)]);
    control.body(3, &[], vec![]);
    control.body(4, &[], vec![call(5)]);
    control.body(5, &[], vec![]);
    control.seal();
    // Exact normalized bridge supplied by a separately admitted runtime model.
    control.graph.edges.push(EdgeRecord {
        source: NodeId(2),
        target: NodeId(4),
        kind: EdgeKind::RuntimeBridge,
        operation: OperationId::NONE,
        occurrence: OccurrenceId::NONE,
        receiver: SymbolId::NONE,
        flags: 0,
    });
    control.graph.index().unwrap();
    for workers in [1, 4] {
        let mut query = QuerySession::new(
            &control.facts,
            &control.graph,
            &SolveOptions {
                workers,
                ..Default::default()
            },
        )
        .unwrap();
        query.execute(&[root(0)]).unwrap();
        assert_eq!(query.context_count(), 1);
        let before = query.analyze(&[NodeId(5)]).unwrap();
        assert!(!before.contains(NodeId(0)));
        assert!(!active(&before, 2) && !active(&before, 4));
        query.execute(&[root(1)]).unwrap();
        assert_eq!(query.context_count(), 6);
        let after = query.analyze(&[NodeId(5)]).unwrap();
        assert!(after.contains(NodeId(1)));
        assert!(!after.contains(NodeId(0)));
        assert!(active(&after, 2) && active(&after, 4));
        assert!(after.guarded_roots.is_empty());
        assert!(
            after
                .witnesses
                .iter()
                .any(|witness| witness.node == NodeId(2)
                    && witness.next == NodeId(4)
                    && control.graph.edges[witness.edge.index()].kind == EdgeKind::RuntimeBridge)
        );
    }
}
