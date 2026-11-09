use super::*;
use selector_facts::{FactBuilder, FileRecord, OccurrenceRecord, ResultBoundRecord};

fn fixture() -> FactSnapshot {
    let mut b = FactBuilder::new();
    let context = b.intern("source-val-test").unwrap();
    let path = b.intern("Vals.scala").unwrap();
    let source = b.intern("class C { val value = effect() }").unwrap();
    b.facts.files.push(FileRecord {
        path,
        source,
        revision: StrId::NONE,
        context,
        source_hash: ContentHash([1; 32]),
        flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
    });
    let owner = b.ensure_symbol("vals/C#", FileId(0)).unwrap();
    let property = b.ensure_symbol("vals/C#value.", FileId(0)).unwrap();
    let effect = b.ensure_symbol("vals/effect().", FileId(0)).unwrap();
    for (symbol, kind) in [(owner, 13), (property, 3), (effect, 3)] {
        b.facts.symbols[symbol.index()].kind = kind;
        b.facts.symbols[symbol.index()].flags = SYMBOL_DEFINED;
        b.facts.symbols[symbol.index()].file = FileId(0);
    }
    b.facts.symbols[property.index()].owner = owner;
    b.facts.symbols[property.index()].properties = 1024;
    b.facts.symbols[property.index()].span = Span { start: 14, end: 19 };
    b.facts.occurrences.push(OccurrenceRecord {
        file: FileId(0),
        symbol: property,
        span: Span { start: 14, end: 19 },
        role: 2,
        ordinal: 0,
    });
    let rhs = Span { start: 22, end: 30 };
    b.facts
        .operands
        .extend([ValueId(3), ValueId(3), ValueId(3)]);
    let operation = |body, opcode, target, dest, a, args| OperationRecord {
        body: BodyId(body),
        opcode,
        target,
        dest,
        a,
        b: ValueId::NONE,
        arguments: args,
        span: rhs,
        flags: 0,
    };
    b.facts.operations.extend([
        operation(
            0,
            Opcode::Parameter,
            SymbolId::NONE,
            ValueId(3),
            ValueId::NONE,
            IdRange::default(),
        ),
        operation(
            0,
            Opcode::Call,
            effect,
            ValueId(1),
            ValueId(0),
            IdRange { start: 1, len: 1 },
        ),
        operation(
            0,
            Opcode::Unknown,
            SymbolId::NONE,
            ValueId(2),
            ValueId::NONE,
            IdRange::default(),
        ),
        operation(
            0,
            Opcode::Return,
            SymbolId::NONE,
            ValueId::NONE,
            ValueId(1),
            IdRange::default(),
        ),
        operation(
            1,
            Opcode::Initialize,
            property,
            ValueId(7),
            ValueId(0),
            IdRange { start: 2, len: 1 },
        ),
        operation(
            1,
            Opcode::Call,
            property,
            ValueId(2),
            ValueId(0),
            IdRange::default(),
        ),
        operation(
            1,
            Opcode::VirtualCall,
            property,
            ValueId(3),
            ValueId(0),
            IdRange::default(),
        ),
    ]);
    b.facts.bodies.push(BodyRecord {
        symbol: property,
        file: FileId(0),
        span: rhs,
        name_span: Span { start: 14, end: 19 },
        operations: IdRange { start: 0, len: 4 },
        parameters: IdRange { start: 0, len: 1 },
        body_hash: ContentHash([2; 32]),
        flags: BODY_INITIALIZER,
    });
    b.facts.bodies.push(BodyRecord {
        symbol: owner,
        file: FileId(0),
        span: Span { start: 0, end: 31 },
        name_span: Span::default(),
        operations: IdRange { start: 4, len: 3 },
        parameters: IdRange::default(),
        body_hash: ContentHash([3; 32]),
        flags: BODY_INITIALIZER,
    });
    b.facts.bound_classes.push(owner);
    for op in [OperationId(4), OperationId(5), OperationId::NONE] {
        b.facts.result_bounds.push(ResultBoundRecord {
            symbol: property,
            operation: op,
            classes: IdRange { start: 0, len: 1 },
        });
    }
    b.facts
        .result_bounds
        .sort_unstable_by_key(|bound| (bound.symbol, bound.operation));
    b.finish().unwrap()
}

#[test]
fn rhs_keeps_capture_effects_and_init_arguments_while_getters_read_the_stored_slot() {
    let mut facts = fixture();
    let original = facts.bodies[0];
    let init = facts.operations[4];
    let property = original.symbol;
    assert_eq!(augment_eager_val_accessors(&mut facts).unwrap(), 1);
    let rhs = facts.bodies[0];
    let getter = facts.bodies.last().unwrap();
    assert_ne!(rhs.symbol, property);
    assert_eq!(facts.symbols[rhs.symbol.index()].flags, 0);
    assert_eq!(rhs.parameters, original.parameters);
    assert_eq!(rhs.span, original.span);
    assert_eq!(getter.symbol, property);
    assert_eq!(getter.span, facts.symbols[property.index()].span);
    assert_eq!(getter.flags, BODY_SOURCE_RECIPE);
    let ops = &facts.operations[rhs.operations.range()];
    assert_eq!(
        ops.iter().map(|op| op.opcode).collect::<Vec<_>>(),
        [
            Opcode::Parameter,
            Opcode::Call,
            Opcode::Unknown,
            Opcode::StoreField,
            Opcode::Return
        ]
    );
    assert_eq!(
        (ops[3].target, ops[3].a, ops[3].b),
        (property, ValueId(0), ValueId(1))
    );
    let owner_ops = &facts.operations[facts.bodies[1].operations.range()];
    assert_eq!(owner_ops[0].target, rhs.symbol);
    assert_eq!(
        (owner_ops[0].a, owner_ops[0].dest, owner_ops[0].arguments),
        (init.a, init.dest, init.arguments)
    );
    assert!(owner_ops[1..].iter().all(|op| op.target == property));
    assert_eq!(
        facts
            .result_bounds
            .iter()
            .filter(|b| b.symbol == property)
            .count(),
        2
    );
    let init_bound = facts
        .result_bounds
        .iter()
        .find(|b| b.symbol == rhs.symbol)
        .unwrap();
    assert_eq!(
        facts.operations[init_bound.operation.index()].opcode,
        Opcode::Initialize
    );
    assert_eq!(augment_eager_val_accessors(&mut facts).unwrap(), 0);
    facts.validate().unwrap();
}

#[test]
fn rhs_diagnostics_follow_initialization_without_weakening_the_original_guard() {
    let mut facts = fixture();
    let property = facts.bodies[0].symbol;
    facts.issues.push(selector_facts::IssueRecord {
        kind: IssueKind::UnknownExecution,
        file: FileId(0),
        symbol: property,
        detail: StrId::NONE,
    });
    assert_eq!(augment_eager_val_accessors(&mut facts).unwrap(), 1);
    let init = facts.bodies[0].symbol;
    assert!(facts.issues.iter().any(|issue| issue.symbol == property));
    assert!(
        facts
            .issues
            .iter()
            .any(|issue| issue.symbol == init && issue.kind == IssueKind::UnknownExecution)
    );
}

#[test]
fn unsupported_compiler_scope_return_and_conflict_shapes_remain_unchanged() {
    for mutation in 0..12 {
        let mut facts = fixture();
        let property = facts.bodies[0].symbol;
        match mutation {
            0 => facts.symbols[property.index()].properties |= 64,
            1 => facts.symbols[property.index()].properties |= 2048,
            2 => facts.symbols[property.index()].properties |= 4,
            3 => facts.symbols[property.index()].properties = 0,
            4 => facts.occurrences.clear(),
            5 => facts.occurrences.push(facts.occurrences[0]),
            6 => facts.operations[2].opcode = Opcode::Return,
            7 => facts.symbols[property.index()].owner = SymbolId(2),
            8 => facts.issues.push(selector_facts::IssueRecord {
                kind: IssueKind::ContextConflict,
                file: FileId::NONE,
                symbol: SymbolId::NONE,
                detail: StrId::NONE,
            }),
            9 => facts.operations[0].target = property,
            10 => facts.operations[1].dest = ValueId(0),
            _ => {
                facts.operations[4] = OperationRecord {
                    body: BodyId(1),
                    opcode: Opcode::Parameter,
                    target: property,
                    dest: ValueId(1),
                    a: ValueId::NONE,
                    b: ValueId::NONE,
                    arguments: IdRange::default(),
                    span: facts.symbols[property.index()].span,
                    flags: 0,
                };
                facts.bodies[1].parameters = IdRange {
                    start: facts.operands.len() as u32,
                    len: 1,
                };
                facts.operands.push(ValueId(1));
            }
        }
        let before = (
            facts.symbols.len(),
            facts.bodies.len(),
            facts.operations.len(),
        );
        assert_eq!(
            augment_eager_val_accessors(&mut facts).unwrap(),
            0,
            "mutation {mutation}"
        );
        assert_eq!(
            (
                facts.symbols.len(),
                facts.bodies.len(),
                facts.operations.len()
            ),
            before
        );
    }
}
