//! Explicit element carriers share the ordinary finite receiver-root heap
//! partitions. They never claim a concrete runtime class or execute elements.
use super::*;

pub(super) fn pack<W: World>(
    world: &W,
    facts: &FactSnapshot,
    s: &mut Scratch,
    out: &mut Evaluation,
    operation: OperationId,
    op: &OperationRecord,
) -> Result<Value, Error> {
    if op.target.is_none() || facts.symbol_name(op.target) != SEQUENCE_ELEMENTS_SYMBOL {
        add_issue(
            out,
            IssueKind::UnknownExecution,
            operation,
            RuntimeIssueReason::UnknownOperation,
        );
        return Ok(Value::TOP);
    }
    let mut elements = Value::EMPTY;
    for argument in &facts.operands[op.arguments.range()] {
        elements = s.pool.join(elements, s.get(*argument))?;
    }
    let receiver = s.get(ValueId(0));
    s.atoms.clear();
    s.atoms.extend_from_slice(s.pool.members(receiver));
    s.receiver_atoms.clear();
    for atom in &s.atoms {
        if atom.kind != AtomKind::Object {
            continue;
        }
        let binding = if atom.binding != 0 {
            atom.binding
        } else if atom.site.is_none() {
            root_binding(atom.symbol)?
        } else {
            0
        };
        s.receiver_atoms.push(Atom {
            kind: AtomKind::Container,
            site: operation,
            symbol: op.target,
            binding,
        });
    }
    if receiver.is_unknown() || s.receiver_atoms.is_empty() {
        s.receiver_atoms.push(Atom {
            kind: AtomKind::Container,
            site: operation,
            symbol: op.target,
            binding: 0,
        });
    }
    s.receiver_atoms.sort_unstable();
    s.receiver_atoms.dedup();
    let result = s.pool.intern(&s.receiver_atoms, 0)?;
    s.atoms.clear();
    s.atoms.extend_from_slice(s.pool.members(result));
    for index in 0..s.atoms.len() {
        let atom = s.atoms[index];
        let mut slot = heap_field(world, s, out, atom, atom.symbol, facts.operations.len())?;
        if slot.kind == SlotKind::FieldAll {
            slot.kind = SlotKind::FieldWildcard;
        }
        out.stores.push(StoreEffect {
            slot,
            value: elements,
        });
    }
    Ok(result)
}

pub(super) fn read<W: World>(
    world: &W,
    facts: &FactSnapshot,
    s: &mut Scratch,
    out: &mut Evaluation,
    operation: OperationId,
    containers: Value,
) -> Result<Value, Error> {
    let mut value = Value::EMPTY;
    let mut unknown = containers.is_unknown();
    s.atoms.clear();
    s.atoms.extend_from_slice(s.pool.members(containers));
    for index in 0..s.atoms.len() {
        let atom = s.atoms[index];
        if atom.kind != AtomKind::Container {
            unknown = true;
            continue;
        }
        let slot = heap_field(world, s, out, atom, atom.symbol, facts.operations.len())?;
        if !out.field_reads.contains(&slot) {
            out.field_reads.push(slot);
        }
        let (v, version, present) = world.slot(slot);
        issue_read(out, slot, version, present);
        let v = s.pool.import(world.values(), v)?;
        value = s.pool.join(value, v)?;
        let mut any_present = present;
        if slot.kind == SlotKind::Field {
            let wildcard = Slot {
                kind: SlotKind::FieldWildcard,
                owner: atom.site.0,
                member: atom.symbol.0,
            };
            let (v, version, present) = world.slot(wildcard);
            issue_read(out, wildcard, version, present);
            any_present |= present;
            let v = s.pool.import(world.values(), v)?;
            value = s.pool.join(value, v)?;
        }
        if !any_present {
            let missing = Slot {
                kind: SlotKind::FieldMissing,
                ..slot
            };
            let (v, version, present) = world.slot(missing);
            issue_read(out, missing, version, present);
            let v = s.pool.import(world.values(), v)?;
            value = s.pool.join(value, v)?;
        }
        let wildcard = Slot {
            kind: SlotKind::Field,
            owner: u32::MAX,
            member: atom.symbol.0,
        };
        let (v, version, present) = world.slot(wildcard);
        issue_read(out, wildcard, version, present);
        let v = s.pool.import(world.values(), v)?;
        value = s.pool.join(value, v)?;
    }
    if unknown {
        value = s.pool.join(
            value,
            Value {
                set: SetId(0),
                unknown: UNKNOWN_FIELD,
            },
        )?;
    }
    if value.unknown & UNKNOWN_FIELD != 0 {
        add_issue(
            out,
            IssueKind::UnknownExecution,
            operation,
            RuntimeIssueReason::UnknownFieldValue,
        );
    }
    Ok(value)
}

#[cfg(test)]
mod tests {
    use super::*;
    struct NativeTop {
        pool: ValuePool,
        elements: Value,
    }
    impl World for NativeTop {
        fn values(&self) -> &ValuePool {
            &self.pool
        }
        fn summary(
            &self,
            _: NodeId,
            _: Value,
            _: &[Value],
            _: &ValuePool,
            _: &mut Vec<Value>,
        ) -> SummaryRead {
            SummaryRead {
                context: None,
                value: Value::TOP,
                version: 1,
                present: true,
            }
        }
        fn slot(&self, _: Slot) -> (Value, u64, bool) {
            (self.elements, 1, true)
        }
        fn capture(&self, _: u32) -> Option<(Value, &[Value], u64)> {
            None
        }
        fn binding(
            &self,
            _: OperationId,
            _: Value,
            _: &[Value],
            _: &ValuePool,
            _: &mut Vec<Atom>,
            _: &mut Vec<Value>,
        ) -> Option<u32> {
            None
        }
    }
    #[test]
    fn additive_view_preserves_native_top_and_call_subscription_with_known_elements() {
        for certified in [false, true] {
            let (mut facts, mut graph) =
                crate::callback_model_tests::fixture_for(0, "scala/collection/SeqOps#apply().");
            let text = StrId(facts.strings.entries.len() as u32);
            facts.strings.entries.push(selector_facts::TextRange {
                start: facts.strings.bytes.len() as u64,
                len: SEQUENCE_ELEMENTS_SYMBOL.len() as u32,
            });
            facts
                .strings
                .bytes
                .extend_from_slice(SEQUENCE_ELEMENTS_SYMBOL.as_bytes());
            let tag = SymbolId(facts.symbols.len() as u32);
            let mut record = facts.symbols[0];
            record.name = text;
            record.display = text;
            record.kind = 0;
            record.flags = 0;
            record.file = FileId::NONE;
            facts.symbols.push(record);
            let template = facts.operations[0];
            let mut pack = facts.operations[1];
            pack.opcode = Opcode::PackSequence;
            pack.target = tag;
            pack.a = ValueId::NONE;
            pack.arguments = IdRange { start: 0, len: 1 };
            let mut constant = template;
            constant.opcode = Opcode::Constant;
            constant.dest = ValueId(4);
            let mut call = facts.operations[2];
            call.a = ValueId(1);
            call.arguments = IdRange {
                start: facts.operands.len() as u32,
                len: 1,
            };
            call.flags = if certified {
                OP_SEQUENCE_ELEMENT_VIEW
            } else {
                0
            };
            facts.operands.push(ValueId(4));
            let mut returned = template;
            returned.opcode = Opcode::Return;
            returned.dest = ValueId::NONE;
            returned.a = ValueId(3);
            facts.operations = vec![template, pack, constant, call, returned];
            facts.bodies[0].operations.len = 5;
            facts.bodies[1].operations.start = 5;
            graph.nodes.push(selector_graph::NodeRecord {
                symbol: tag,
                file: FileId::NONE,
                body: BodyId::NONE,
                flags: 0,
            });
            graph.symbol_nodes.push(NodeId(3));
            graph.edges[0].operation = OperationId(3);
            graph.index().unwrap();
            facts.validate().unwrap();
            let mut pool = ValuePool::new(16);
            let callback = Atom {
                kind: AtomKind::Callback,
                site: OperationId::NONE,
                symbol: SymbolId(2),
                binding: 0,
            };
            let elements = pool.singleton(callback).unwrap();
            let world = NativeTop { pool, elements };
            let types = TypeIndex::new(&facts);
            let mut scratch = Scratch::new(16);
            let mut out = Evaluation::default();
            evaluate(
                &facts,
                &graph,
                &types,
                &world,
                NodeId(0),
                Value::EMPTY,
                &[elements],
                &mut scratch,
                &mut out,
            )
            .unwrap();
            assert!(
                out.value.is_unknown(),
                "native TOP is never replaced by the element view"
            );
            assert_eq!(
                scratch.pool.members(out.value).contains(&callback),
                certified
            );
            assert!(
                out.calls
                    .iter()
                    .any(|call| call.target == NodeId(1) && call.observe_return),
                "native return subscription/effects remain"
            );
            if certified {
                assert_eq!(
                    out.first_issue.unwrap().reason,
                    RuntimeIssueReason::UnknownOperation
                );
            }
        }
    }
}
