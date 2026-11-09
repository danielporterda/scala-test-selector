//! Lower admitted JVM summaries into the ordinary immutable operation schema.
//! Bytecode offsets remain summary provenance; zero source spans never pretend
//! that external binary code was written in an arbitrary Scala caller file.

use selector_facts::{BodyRecord, FactSnapshot, IssueRecord, OperationRecord};
use selector_models::binary::{InvokeKind, MethodSummary, Value, method_descriptor};
use selector_types::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Initialization {
    Unknown,
    KnownEmpty,
    /// Exact JVM static phase, distinct from the type's instance/trait phase.
    Target(SymbolId),
}
pub struct Targets<'a> {
    pub call_targets: &'a [SymbolId],
    pub allocation_classes: &'a [SymbolId],
    pub field_targets: &'a [SymbolId],
    pub write_targets: &'a [SymbolId],
    /// Deferred recipes for exact admitted LambdaMetafactory sites.
    pub lambda_targets: &'a [SymbolId],
    pub call_initializers: &'a [Initialization],
    pub value_initializers: &'a [Initialization],
    pub write_initializers: &'a [Initialization],
    /// The synthetic first argument of Scala trait `$init$` is the actual
    /// execution receiver, not an extra caller-supplied argument.
    pub receiver_parameter: Option<u16>,
}

#[derive(Clone, Copy)]
enum EventKind {
    Value,
    Call,
    Write,
    Unknown,
}
struct Event {
    offset: u32,
    order: u8,
    index: usize,
    kind: EventKind,
}

pub(crate) fn callback_call(owner: &str, name: &str) -> bool {
    ((owner == "java/lang/Runnable" && name == "run")
        || (owner == "java/util/concurrent/Callable" && name == "call"))
        || (owner
            .strip_prefix("scala/Function")
            .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
            && (name == "apply" || (name.starts_with("apply$mc") && name.ends_with("$sp"))))
}

pub fn lower_summary(
    facts: &mut FactSnapshot,
    symbol: SymbolId,
    file: FileId,
    summary: &MethodSummary<'_>,
    targets: &Targets<'_>,
    body_hash: ContentHash,
    body_flags: u32,
) -> Result<BodyId, Error> {
    let valid = |id: SymbolId| id.is_none() || id.index() < facts.symbols.len();
    if symbol.is_none()
        || !valid(symbol)
        || file.is_none()
        || file.index() >= facts.files.len()
        || facts.files[file.index()].flags & FILE_BINARY_SOURCE == 0
        || targets.call_targets.len() != summary.calls.len()
        || targets.allocation_classes.len() != summary.values.len()
        || targets.field_targets.len() != summary.values.len()
        || targets.write_targets.len() != summary.field_writes.len()
        || targets.lambda_targets.len() != summary.lambdas.len()
        || targets.call_initializers.len() != summary.calls.len()
        || targets.value_initializers.len() != summary.values.len()
        || targets.write_initializers.len() != summary.field_writes.len()
        || summary.value_offsets.len() != summary.values.len()
        || !targets
            .call_targets
            .iter()
            .chain(targets.allocation_classes)
            .chain(targets.field_targets)
            .chain(targets.write_targets)
            .chain(targets.lambda_targets)
            .all(|id| valid(*id))
        || !targets
            .call_initializers
            .iter()
            .chain(targets.value_initializers)
            .chain(targets.write_initializers)
            .all(|init| match init {
                Initialization::Target(id) => !id.is_none() && valid(*id),
                _ => true,
            })
    {
        return Err(Error::Invalid("binary lowering binding"));
    }
    let descriptor = method_descriptor(summary.descriptor)
        .map_err(|_| Error::Invalid("binary method descriptor"))?;
    let valid_value =
        |id: selector_models::binary::BinaryValueId| (id.0 as usize) < summary.values.len();
    if summary.returned.is_some_and(|id| !valid_value(id))
        || summary.arguments.iter().any(|id| !valid_value(*id))
        || summary.calls.iter().any(|call| {
            call.receiver.is_some_and(|id| !valid_value(id))
                || call.arguments.range().end > summary.arguments.len()
        })
        || summary.field_writes.iter().any(|write| {
            !valid_value(write.value) || write.receiver.is_some_and(|id| !valid_value(id))
        })
        || summary
            .lambdas
            .iter()
            .any(|lambda| lambda.captures.range().end > summary.arguments.len())
        || summary.values.iter().any(|value| match value {
            Value::Field { receiver, .. } => !valid_value(*receiver),
            Value::CallResult(call) => *call as usize >= summary.calls.len(),
            Value::Lambda(lambda) => *lambda as usize >= summary.lambdas.len(),
            Value::Alternatives(range) => range.range().end > summary.arguments.len(),
            Value::Allocation {
                constructor: Some(call),
                ..
            } => *call as usize >= summary.calls.len(),
            _ => false,
        })
    {
        return Err(Error::Invalid("binary summary references"));
    }
    if targets
        .receiver_parameter
        .is_some_and(|p| p as usize >= descriptor.parameter_count)
    {
        return Err(Error::Invalid("binary receiver argument"));
    }
    let parameters = descriptor.parameter_count - usize::from(targets.receiver_parameter.is_some());
    let body = BodyId::checked(facts.bodies.len())?;
    let mut values = Vec::with_capacity(summary.values.len());
    let mut next = parameters + 1;
    for value in &summary.values {
        values.push(match value {
            Value::Receiver => ValueId(0),
            Value::Argument(index) => {
                let index = *index as usize;
                if index >= descriptor.parameter_count {
                    return Err(Error::Invalid("binary argument index"));
                }
                if targets.receiver_parameter == Some(index as u16) {
                    ValueId(0)
                } else {
                    ValueId::checked(
                        index + 1
                            - usize::from(
                                targets
                                    .receiver_parameter
                                    .is_some_and(|p| index > p as usize),
                            ),
                    )?
                }
            }
            _ => {
                let id = ValueId::checked(next)?;
                next += 1;
                id
            }
        });
    }
    let value = |id: selector_models::binary::BinaryValueId| {
        values
            .get(id.0 as usize)
            .copied()
            .ok_or(Error::Invalid("binary value reference"))
    };
    let mut events =
        Vec::with_capacity(summary.values.len() + summary.calls.len() + summary.field_writes.len());
    for (index, v) in summary.values.iter().enumerate() {
        if !matches!(
            v,
            Value::Receiver | Value::Argument(_) | Value::CallResult(_)
        ) {
            events.push(Event {
                offset: summary.value_offsets[index],
                order: if matches!(v, Value::Alternatives(_)) {
                    0
                } else {
                    1
                },
                index,
                kind: EventKind::Value,
            });
        }
    }
    for (index, call) in summary.calls.iter().enumerate() {
        events.push(Event {
            offset: call.offset,
            order: 2,
            index,
            kind: EventKind::Call,
        });
    }
    for (index, write) in summary.field_writes.iter().enumerate() {
        events.push(Event {
            offset: write.offset,
            order: 3,
            index,
            kind: EventKind::Write,
        });
    }
    for (index, &offset) in summary.unknown_offsets.iter().enumerate() {
        // Non-void dynamic results already carry their unknown at this PC.
        if !summary
            .values
            .iter()
            .zip(&summary.value_offsets)
            .any(|(value, pc)| matches!(value, Value::UnknownDynamic) && *pc == offset)
        {
            events.push(Event {
                offset,
                order: 0,
                index,
                kind: EventKind::Unknown,
            });
        }
    }
    events.sort_unstable_by_key(|e| (e.offset, e.order, e.index));
    let mut call_results = vec![ValueId::NONE; summary.calls.len()];
    for (i, v) in summary.values.iter().enumerate() {
        if let Value::CallResult(call) = v {
            let slot = call_results
                .get_mut(*call as usize)
                .ok_or(Error::Invalid("binary call result"))?;
            if !slot.is_none() {
                return Err(Error::Invalid("duplicate binary call result"));
            }
            *slot = values[i];
        }
    }
    let operation_start =
        u32::try_from(facts.operations.len()).map_err(|_| Error::Limit("binary operations"))?;
    let parameter_start =
        u32::try_from(facts.operands.len()).map_err(|_| Error::Limit("binary operands"))?;
    for index in 0..parameters {
        facts.operands.push(ValueId::checked(index + 1)?);
    }
    let mut emit =
        |opcode, target, dest, a, b, arguments: &[ValueId], flags| -> Result<(), Error> {
            let start =
                u32::try_from(facts.operands.len()).map_err(|_| Error::Limit("binary operands"))?;
            let len =
                u32::try_from(arguments.len()).map_err(|_| Error::Limit("binary arguments"))?;
            facts.operands.extend_from_slice(arguments);
            facts.operations.push(OperationRecord {
                body,
                opcode,
                target,
                dest,
                a,
                b,
                arguments: IdRange { start, len },
                span: Span::default(),
                flags,
            });
            Ok(())
        };
    for index in 0..parameters {
        emit(
            Opcode::Parameter,
            SymbolId::NONE,
            ValueId::checked(index + 1)?,
            ValueId::NONE,
            ValueId::NONE,
            &[],
            0,
        )?;
    }
    let mut unknown = summary.unknown.is_some();
    macro_rules! initialize {
        ($init:expr) => {
            match $init {
                Initialization::Unknown => {
                    unknown = true;
                }
                Initialization::KnownEmpty => {}
                Initialization::Target(target) => emit(
                    Opcode::Initialize,
                    target,
                    ValueId::NONE,
                    ValueId::NONE,
                    ValueId::NONE,
                    &[],
                    0,
                )?,
            }
        };
    }
    let mut arguments = Vec::new();
    for event in events {
        match event.kind {
            EventKind::Unknown => {
                unknown = true;
                emit(
                    Opcode::Unknown,
                    SymbolId::NONE,
                    ValueId::NONE,
                    ValueId::NONE,
                    ValueId::NONE,
                    &[],
                    0,
                )?;
            }
            EventKind::Value => {
                let dest = values[event.index];
                if matches!(
                    summary.values[event.index],
                    Value::Allocation { .. } | Value::MayAllocation { .. }
                ) {
                    // NEW triggers class initialization before evaluation of
                    // constructor arguments, even though Allocate is emitted
                    // at invokespecial after its arguments are available.
                    initialize!(targets.value_initializers[event.index]);
                }
                match summary.values[event.index] {
                    Value::Alternatives(range) => {
                        arguments.clear();
                        for &id in &summary.arguments[range.range()] {
                            arguments.push(value(id)?);
                        }
                        emit(
                            Opcode::Join,
                            SymbolId::NONE,
                            dest,
                            ValueId::NONE,
                            ValueId::NONE,
                            &arguments,
                            0,
                        )?;
                    }
                    Value::UnknownData => emit(
                        Opcode::Assign,
                        SymbolId::NONE,
                        dest,
                        ValueId::NONE,
                        ValueId::NONE,
                        &[],
                        0,
                    )?,
                    Value::MayAllocation { .. } => {
                        let target = targets.allocation_classes[event.index];
                        if target.is_none() {
                            unknown = true;
                        }
                        emit(
                            if target.is_none() {
                                Opcode::Unknown
                            } else {
                                Opcode::Allocate
                            },
                            target,
                            dest,
                            ValueId::NONE,
                            ValueId::NONE,
                            &[],
                            0,
                        )?;
                    }
                    Value::Null | Value::Constant { .. } | Value::Void => emit(
                        Opcode::Constant,
                        SymbolId::NONE,
                        dest,
                        ValueId::NONE,
                        ValueId::NONE,
                        &[],
                        0,
                    )?,
                    Value::Field { receiver, .. } => {
                        let target = targets.field_targets[event.index];
                        if target.is_none() {
                            unknown = true;
                            emit(
                                Opcode::Unknown,
                                target,
                                dest,
                                ValueId::NONE,
                                ValueId::NONE,
                                &[],
                                0,
                            )?;
                        } else {
                            emit(
                                Opcode::LoadField,
                                target,
                                dest,
                                value(receiver)?,
                                ValueId::NONE,
                                &[],
                                0,
                            )?;
                        }
                    }
                    Value::StaticField(_) => {
                        let target = targets.field_targets[event.index];
                        initialize!(targets.value_initializers[event.index]);
                        emit(
                            if target.is_none() {
                                Opcode::Unknown
                            } else {
                                Opcode::LoadField
                            },
                            target,
                            dest,
                            ValueId::NONE,
                            ValueId::NONE,
                            &[],
                            OP_STATIC_FIELD,
                        )?;
                    }
                    Value::Lambda(index) => {
                        let lambda = &summary.lambdas[index as usize];
                        let target = targets.lambda_targets[index as usize];
                        arguments.clear();
                        for &capture in &summary.arguments[lambda.captures.range()] {
                            arguments.push(value(capture)?);
                        }
                        if target.is_none() {
                            unknown = true;
                        }
                        emit(
                            if target.is_none() {
                                Opcode::Unknown
                            } else {
                                Opcode::BindCallback
                            },
                            target,
                            dest,
                            ValueId::NONE,
                            ValueId::NONE,
                            &arguments,
                            0,
                        )?;
                    }
                    Value::UnknownDynamic
                    | Value::UnknownLocal(_)
                    | Value::Allocation {
                        constructor: None, ..
                    } => {
                        unknown = true;
                        emit(
                            Opcode::Unknown,
                            SymbolId::NONE,
                            dest,
                            ValueId::NONE,
                            ValueId::NONE,
                            &[],
                            0,
                        )?;
                    }
                    _ => (),
                }
            }
            EventKind::Call => {
                let call = &summary.calls[event.index];
                let target = targets.call_targets[event.index];
                if call.kind == InvokeKind::Static && call.member.name != "<clinit>" {
                    initialize!(targets.call_initializers[event.index]);
                }
                arguments.clear();
                for &argument in summary
                    .arguments
                    .get(call.arguments.range())
                    .ok_or(Error::Invalid("binary call arguments"))?
                {
                    arguments.push(value(argument)?);
                }
                let receiver = call
                    .receiver
                    .map(value)
                    .transpose()?
                    .unwrap_or(ValueId::NONE);
                let allocation =
                    call.receiver
                        .and_then(|id| match summary.values.get(id.0 as usize) {
                            Some(Value::Allocation {
                                constructor: Some(constructor),
                                ..
                            }) if *constructor as usize == event.index => Some(id),
                            _ => None,
                        });
                if let Some(allocation) = allocation {
                    let class = targets.allocation_classes[allocation.0 as usize];
                    if target.is_none() {
                        unknown = true;
                    }
                    if target.is_none() && class.is_none() {
                        emit(
                            Opcode::Unknown,
                            SymbolId::NONE,
                            value(allocation)?,
                            ValueId::NONE,
                            ValueId::NONE,
                            &[],
                            0,
                        )?;
                    } else {
                        emit(
                            Opcode::Allocate,
                            if target.is_none() { class } else { target },
                            value(allocation)?,
                            ValueId::NONE,
                            ValueId::NONE,
                            &arguments,
                            0,
                        )?;
                    }
                } else if callback_call(call.member.owner, call.member.name) {
                    emit(
                        Opcode::InvokeCallback,
                        target,
                        call_results[event.index],
                        receiver,
                        ValueId::NONE,
                        &arguments,
                        0,
                    )?;
                } else {
                    if target.is_none() {
                        unknown = true;
                    }
                    emit(
                        if call.kind == InvokeKind::Virtual || call.kind == InvokeKind::Interface {
                            Opcode::VirtualCall
                        } else {
                            Opcode::Call
                        },
                        target,
                        call_results[event.index],
                        receiver,
                        ValueId::NONE,
                        &arguments,
                        if matches!(call.kind, InvokeKind::Static | InvokeKind::Special) {
                            OP_JVM_NONVIRTUAL
                        } else {
                            0
                        },
                    )?;
                }
            }
            EventKind::Write => {
                let write = &summary.field_writes[event.index];
                let target = targets.write_targets[event.index];
                if let Some(receiver) = write.receiver {
                    if target.is_none() {
                        unknown = true;
                    }
                    emit(
                        Opcode::StoreField,
                        target,
                        ValueId::NONE,
                        value(receiver)?,
                        value(write.value)?,
                        &[],
                        0,
                    )?;
                } else {
                    initialize!(targets.write_initializers[event.index]);
                    emit(
                        Opcode::StoreField,
                        target,
                        ValueId::NONE,
                        ValueId::NONE,
                        value(write.value)?,
                        &[],
                        OP_STATIC_FIELD,
                    )?;
                }
            }
        }
    }
    if let Some(returned) = summary.returned {
        emit(
            Opcode::Return,
            SymbolId::NONE,
            ValueId::NONE,
            value(returned)?,
            ValueId::NONE,
            &[],
            0,
        )?;
    }
    if unknown {
        let unknown_value = ValueId::checked(next)?;
        emit(
            Opcode::Unknown,
            SymbolId::NONE,
            unknown_value,
            ValueId::NONE,
            ValueId::NONE,
            &[],
            0,
        )?;
        emit(
            Opcode::Return,
            SymbolId::NONE,
            ValueId::NONE,
            unknown_value,
            ValueId::NONE,
            &[],
            0,
        )?;
    }
    drop(emit);
    if unknown {
        facts.issues.push(IssueRecord {
            kind: IssueKind::UnknownExecution,
            file,
            symbol,
            detail: StrId::NONE,
        });
    }
    let len = u32::try_from(facts.operations.len())
        .map_err(|_| Error::Limit("binary operations"))?
        - operation_start;
    facts.bodies.push(BodyRecord {
        symbol,
        file,
        span: Span::default(),
        name_span: Span::default(),
        operations: IdRange {
            start: operation_start,
            len,
        },
        parameters: IdRange {
            start: parameter_start,
            len: parameters as u32,
        },
        body_hash,
        flags: body_flags | BODY_BINARY_RECIPE,
    });
    Ok(body)
}

#[cfg(test)]
mod tests {
    use super::*;
    use selector_facts::{FactBuilder, FileRecord, SymbolRecord};
    use selector_models::binary::{Limits, parse_class, summarize};
    fn facts() -> FactSnapshot {
        let mut builder = FactBuilder::new();
        let empty = builder.intern("").unwrap();
        let path = builder.intern("@binary:fixture").unwrap();
        builder.facts.files.push(FileRecord {
            path,
            source: empty,
            revision: empty,
            context: empty,
            source_hash: ContentHash::default(),
            flags: FILE_BINARY_SOURCE,
        });
        for name in [
            "fixture/Probe#make().",
            "fixture/Made#",
            "fixture/Made#`<init>`().",
            "fixture/Made#callback.",
        ] {
            let name = builder.intern(name).unwrap();
            builder.facts.symbols.push(SymbolRecord {
                name,
                display: empty,
                owner: SymbolId::NONE,
                file: FileId(0),
                context: empty,
                kind: 3,
                properties: 0,
                signature: empty,
                span: Span::default(),
                flags: SYMBOL_NATIVE_BINARY,
            });
        }
        builder.facts
    }
    #[test]
    fn allocation_constructor_arguments_lower_to_ordinary_owned_operations() {
        let bytes = include_bytes!("../../../fixtures/binary/classes/fixture/Probe.class");
        let class = parse_class(bytes, Limits::default()).unwrap();
        let s = summarize(
            &class,
            class.method("make", None).unwrap(),
            Limits::default(),
        );
        let mut f = facts();
        let target = Targets {
            call_targets: &vec![SymbolId(2); s.calls.len()],
            allocation_classes: &vec![SymbolId(1); s.values.len()],
            field_targets: &vec![SymbolId(3); s.values.len()],
            lambda_targets: &[],
            write_targets: &[],
            call_initializers: &vec![Initialization::KnownEmpty; s.calls.len()],
            value_initializers: &vec![Initialization::KnownEmpty; s.values.len()],
            write_initializers: &vec![Initialization::KnownEmpty; s.field_writes.len()],
            receiver_parameter: None,
        };
        let body = lower_summary(
            &mut f,
            SymbolId(0),
            FileId(0),
            &s,
            &target,
            ContentHash([7; 32]),
            0,
        )
        .unwrap();
        let b = f.bodies[body.index()];
        let ops = &f.operations[b.operations.range()];
        assert_eq!(
            ops.iter().map(|o| o.opcode).collect::<Vec<_>>(),
            [Opcode::Parameter, Opcode::Allocate, Opcode::Return]
        );
        assert_eq!(f.operands[ops[1].arguments.range()], [ValueId(1)]);
        assert_eq!(ops[1].target, SymbolId(2));
        assert_eq!(ops[2].a, ops[1].dest);
        assert!(f.issues.is_empty());
        f.validate().unwrap();
    }

    #[test]
    fn genuine_nonvirtual_bytecodes_keep_exact_call_effects_and_do_not_certify_virtuals() {
        for (bytes, name, expected) in [
            (
                include_bytes!(
                    "../../../fixtures/binary-resolution/classes/fixture/ResolveLeaf.class"
                )
                .as_slice(),
                "invokeStatic",
                InvokeKind::Static,
            ),
            (
                include_bytes!(
                    "../../../fixtures/binary-resolution/classes/fixture/ResolveLeaf.class"
                )
                .as_slice(),
                "invokeSuper",
                InvokeKind::Special,
            ),
            (
                include_bytes!(
                    "../../../fixtures/binary-resolution/classes/fixture/ResolveLeaf.class"
                )
                .as_slice(),
                "invokeInherited",
                InvokeKind::Virtual,
            ),
            (
                include_bytes!(
                    "../../../fixtures/native-admission-chain/classes/admissioncase/Factory.class"
                )
                .as_slice(),
                "invoke",
                InvokeKind::Interface,
            ),
        ] {
            let class = parse_class(bytes, Limits::default()).unwrap();
            let summary = summarize(&class, class.method(name, None).unwrap(), Limits::default());
            assert!(summary.complete());
            assert_eq!(summary.calls.len(), 1);
            assert_eq!(summary.calls[0].kind, expected);
            for target in [SymbolId(2), SymbolId::NONE] {
                let mut facts = facts();
                let targets = Targets {
                    call_targets: &[target],
                    allocation_classes: &vec![SymbolId::NONE; summary.values.len()],
                    field_targets: &vec![SymbolId::NONE; summary.values.len()],
                    write_targets: &[],
                    lambda_targets: &[],
                    call_initializers: &[Initialization::KnownEmpty],
                    value_initializers: &vec![Initialization::KnownEmpty; summary.values.len()],
                    write_initializers: &[],
                    receiver_parameter: None,
                };
                let body = lower_summary(
                    &mut facts,
                    SymbolId(0),
                    FileId(0),
                    &summary,
                    &targets,
                    ContentHash([21; 32]),
                    0,
                )
                .unwrap();
                let body = facts.bodies[body.index()];
                assert_ne!(body.flags & BODY_BINARY_RECIPE, 0);
                let ops = &facts.operations[body.operations.range()];
                let call = ops
                    .iter()
                    .find(|o| matches!(o.opcode, Opcode::Call | Opcode::VirtualCall))
                    .unwrap();
                let nonvirtual = matches!(expected, InvokeKind::Static | InvokeKind::Special);
                assert_eq!(
                    call.opcode,
                    if nonvirtual {
                        Opcode::Call
                    } else {
                        Opcode::VirtualCall
                    }
                );
                assert_eq!(call.flags & OP_JVM_NONVIRTUAL != 0, nonvirtual);
                assert_eq!(call.flags & (OP_SUPER | OP_QUALIFIED_SUPER), 0);
                assert_eq!(call.target, target);
                assert_eq!(call.a.is_none(), expected == InvokeKind::Static);
                assert_eq!(
                    ops.iter()
                        .filter(|o| o.flags & OP_JVM_NONVIRTUAL != 0)
                        .count(),
                    usize::from(nonvirtual)
                );
                assert!(
                    ops.iter()
                        .any(|o| o.opcode == Opcode::Return && o.a == call.dest)
                );
                assert_eq!(
                    !facts.issues.is_empty(),
                    target.is_none(),
                    "missing targets stay guarded"
                );
                facts.validate().unwrap();
            }
        }
    }
    #[test]
    fn binary_parameter_callback_invocation_remains_deferred_until_called() {
        let class = parse_class(
            include_bytes!("../../../fixtures/binary/classes/fixture/Probe.class"),
            Limits::default(),
        )
        .unwrap();
        let s = summarize(
            &class,
            class.method("invoke", None).unwrap(),
            Limits::default(),
        );
        let mut f = facts();
        let target = Targets {
            call_targets: &vec![SymbolId::NONE; s.calls.len()],
            allocation_classes: &vec![SymbolId::NONE; s.values.len()],
            field_targets: &vec![SymbolId::NONE; s.values.len()],
            lambda_targets: &[],
            write_targets: &[],
            call_initializers: &vec![Initialization::KnownEmpty; s.calls.len()],
            value_initializers: &vec![Initialization::KnownEmpty; s.values.len()],
            write_initializers: &vec![Initialization::KnownEmpty; s.field_writes.len()],
            receiver_parameter: None,
        };
        let body = lower_summary(
            &mut f,
            SymbolId(0),
            FileId(0),
            &s,
            &target,
            ContentHash([8; 32]),
            0,
        )
        .unwrap();
        let ops = &f.operations[f.bodies[body.index()].operations.range()];
        assert!(
            ops.iter()
                .any(|o| o.opcode == Opcode::InvokeCallback && o.a == ValueId(1))
        );
        assert!(!ops.iter().any(|o| o.opcode == Opcode::VirtualCall));
        assert!(f.issues.is_empty());
    }
    #[test]
    fn explicit_trait_receiver_argument_is_not_an_extra_call_parameter() {
        let class = parse_class(
            include_bytes!("../../../fixtures/binary/classes/fixture/Probe.class"),
            Limits::default(),
        )
        .unwrap();
        // A named ABI control uses genuine static argument-forwarding bytecode;
        // the facade supplies the same explicit receiver mapping for Scala $init$.
        let s = summarize(
            &class,
            class.method("forward", None).unwrap(),
            Limits::default(),
        );
        let mut f = facts();
        let targets = Targets {
            call_targets: &[],
            allocation_classes: &vec![SymbolId::NONE; s.values.len()],
            field_targets: &vec![SymbolId::NONE; s.values.len()],
            lambda_targets: &[],
            write_targets: &[],
            call_initializers: &vec![Initialization::KnownEmpty; s.calls.len()],
            value_initializers: &vec![Initialization::KnownEmpty; s.values.len()],
            write_initializers: &vec![Initialization::KnownEmpty; s.field_writes.len()],
            receiver_parameter: Some(0),
        };
        let body = lower_summary(
            &mut f,
            SymbolId(0),
            FileId(0),
            &s,
            &targets,
            ContentHash([9; 32]),
            0,
        )
        .unwrap();
        assert_eq!(f.bodies[body.index()].parameters.len, 0);
        assert!(
            f.operations[f.bodies[body.index()].operations.range()]
                .iter()
                .any(|o| o.opcode == Opcode::Return && o.a == ValueId(0))
        );
    }
    #[test]
    fn unsupported_branch_keeps_callback_prefix_and_unknown_return_alternative() {
        let class = parse_class(
            include_bytes!("../../../fixtures/binary/classes/fixture/Probe.class"),
            Limits::default(),
        )
        .unwrap();
        let s = summarize(
            &class,
            class.method("partial", None).unwrap(),
            Limits::default(),
        );
        let mut f = facts();
        let targets = Targets {
            call_targets: &vec![SymbolId::NONE; s.calls.len()],
            allocation_classes: &vec![SymbolId::NONE; s.values.len()],
            field_targets: &vec![SymbolId::NONE; s.values.len()],
            lambda_targets: &[],
            write_targets: &[],
            call_initializers: &vec![Initialization::KnownEmpty; s.calls.len()],
            value_initializers: &vec![Initialization::KnownEmpty; s.values.len()],
            write_initializers: &vec![Initialization::KnownEmpty; s.field_writes.len()],
            receiver_parameter: None,
        };
        let body = lower_summary(
            &mut f,
            SymbolId(0),
            FileId(0),
            &s,
            &targets,
            ContentHash([10; 32]),
            0,
        )
        .unwrap();
        let ops = &f.operations[f.bodies[body.index()].operations.range()];
        assert!(ops.iter().any(|o| o.opcode == Opcode::InvokeCallback));
        let unknown = ops.iter().find(|o| o.opcode == Opcode::Unknown).unwrap();
        assert!(!unknown.dest.is_none());
        assert_eq!(ops.last().unwrap().opcode, Opcode::Return);
        assert_eq!(ops.last().unwrap().a, unknown.dest);
        assert!(
            f.issues
                .iter()
                .any(|i| i.kind == IssueKind::UnknownExecution)
        );
        f.validate().unwrap();
    }

    #[test]
    fn genuine_scala_module_static_slots_initialize_exact_owner_and_preserve_values() {
        for (bytes, method) in [
            (
                include_bytes!(
                    "../../../fixtures/execution-smoke/head/bytecode/executioncase/Changed.class"
                )
                .as_slice(),
                "value",
            ),
            (
                include_bytes!(
                    "../../../fixtures/execution-smoke/head/bytecode/executioncase/Changed$.class"
                )
                .as_slice(),
                "<clinit>",
            ),
        ] {
            let class = parse_class(bytes, Limits::default()).unwrap();
            let summary = summarize(
                &class,
                class.method(method, None).unwrap(),
                Limits::default(),
            );
            assert!(summary.complete(), "{method}: {:?}", summary.unknown);
            let mut facts = facts();
            facts.symbols[3].owner = SymbolId(1);
            let targets = Targets {
                call_targets: &vec![SymbolId(2); summary.calls.len()],
                allocation_classes: &vec![SymbolId(1); summary.values.len()],
                field_targets: &vec![SymbolId(3); summary.values.len()],
                lambda_targets: &[],
                write_targets: &vec![SymbolId(3); summary.field_writes.len()],
                call_initializers: &vec![Initialization::KnownEmpty; summary.calls.len()],
                value_initializers: &vec![
                    Initialization::Target(SymbolId(1));
                    summary.values.len()
                ],
                write_initializers: &vec![
                    Initialization::Target(SymbolId(1));
                    summary.field_writes.len()
                ],
                receiver_parameter: None,
            };
            let body = lower_summary(
                &mut facts,
                SymbolId(0),
                FileId(0),
                &summary,
                &targets,
                ContentHash([11; 32]),
                0,
            )
            .unwrap();
            let operations = &facts.operations[facts.bodies[body.index()].operations.range()];
            assert!(
                operations
                    .iter()
                    .any(|o| o.opcode == Opcode::Initialize && o.target == SymbolId(1))
            );
            let slot = operations
                .iter()
                .find(|o| matches!(o.opcode, Opcode::LoadField | Opcode::StoreField))
                .unwrap();
            assert_eq!(slot.target, SymbolId(3));
            assert_eq!(slot.flags, OP_STATIC_FIELD);
            assert!(slot.a.is_none());
            if method == "<clinit>" {
                let allocation = operations
                    .iter()
                    .find(|o| o.opcode == Opcode::Allocate)
                    .unwrap();
                assert_eq!(slot.opcode, Opcode::StoreField);
                assert_eq!(slot.b, allocation.dest);
            } else {
                assert_eq!(slot.opcode, Opcode::LoadField);
                assert!(!slot.dest.is_none());
            }
            assert!(facts.issues.is_empty());
            facts.validate().unwrap();
        }
    }
    #[test]
    fn inherited_static_call_initializes_resolved_declaring_owner_before_execution() {
        let class = parse_class(
            include_bytes!("../../../fixtures/binary-resolution/classes/fixture/ResolveLeaf.class"),
            Limits::default(),
        )
        .unwrap();
        let summary = summarize(
            &class,
            class.method("invokeStatic", None).unwrap(),
            Limits::default(),
        );
        assert!(summary.complete());
        assert_eq!(summary.calls[0].member.owner, "fixture/ResolveLeaf");
        let mut facts = facts();
        facts.symbols[2].owner = SymbolId(1);
        let targets = Targets {
            call_targets: &[SymbolId(2)],
            allocation_classes: &vec![SymbolId::NONE; summary.values.len()],
            field_targets: &vec![SymbolId::NONE; summary.values.len()],
            lambda_targets: &[],
            write_targets: &[],
            call_initializers: &vec![Initialization::Target(SymbolId(1)); summary.calls.len()],
            value_initializers: &vec![Initialization::KnownEmpty; summary.values.len()],
            write_initializers: &vec![Initialization::KnownEmpty; summary.field_writes.len()],
            receiver_parameter: None,
        };
        let body = lower_summary(
            &mut facts,
            SymbolId(0),
            FileId(0),
            &summary,
            &targets,
            ContentHash([12; 32]),
            0,
        )
        .unwrap();
        let ops = &facts.operations[facts.bodies[body.index()].operations.range()];
        assert_eq!(
            ops.iter().map(|o| o.opcode).collect::<Vec<_>>(),
            [Opcode::Initialize, Opcode::Call, Opcode::Return]
        );
        assert_eq!(ops[0].target, SymbolId(1));
        assert_eq!(ops[1].target, SymbolId(2));
        assert_eq!(ops[2].a, ops[1].dest);
        assert!(facts.issues.is_empty());
        facts.validate().unwrap();
    }
    #[test]
    fn new_initializes_before_constructor_argument_effects_and_unknown_keeps_value_flow() {
        let class = parse_class(
            include_bytes!("../../../fixtures/binary-resolution/classes/fixture/ResolveLeaf.class"),
            Limits::default(),
        )
        .unwrap();
        let summary = summarize(
            &class,
            class.method("allocateWithCall", None).unwrap(),
            Limits::default(),
        );
        assert!(summary.complete());
        assert_eq!(summary.calls.len(), 2);
        assert_eq!(summary.calls[0].kind, InvokeKind::Static);
        assert_eq!(summary.calls[1].member.name, "<init>");
        for allocation_init in [Initialization::Target(SymbolId(1)), Initialization::Unknown] {
            let mut facts = facts();
            let mut value_initializers = vec![Initialization::KnownEmpty; summary.values.len()];
            for (index, value) in summary.values.iter().enumerate() {
                if matches!(value, Value::Allocation { .. }) {
                    value_initializers[index] = allocation_init;
                }
            }
            let targets = Targets {
                call_targets: &[SymbolId(0), SymbolId(2)],
                allocation_classes: &vec![SymbolId(1); summary.values.len()],
                field_targets: &vec![SymbolId::NONE; summary.values.len()],
                lambda_targets: &[],
                write_targets: &[],
                call_initializers: &[
                    Initialization::Target(SymbolId(3)),
                    Initialization::KnownEmpty,
                ],
                value_initializers: &value_initializers,
                write_initializers: &[],
                receiver_parameter: None,
            };
            let body = lower_summary(
                &mut facts,
                SymbolId(0),
                FileId(0),
                &summary,
                &targets,
                ContentHash([13; 32]),
                0,
            )
            .unwrap();
            let ops = &facts.operations[facts.bodies[body.index()].operations.range()];
            let allocation = ops.iter().find(|o| o.opcode == Opcode::Allocate).unwrap();
            let argument = ops.iter().find(|o| o.opcode == Opcode::Call).unwrap();
            assert_eq!(
                facts.operands[allocation.arguments.range()],
                [argument.dest]
            );
            assert!(
                ops.iter()
                    .any(|o| o.opcode == Opcode::Return && o.a == allocation.dest)
            );
            if allocation_init == Initialization::Unknown {
                assert!(
                    facts
                        .issues
                        .iter()
                        .any(|i| i.kind == IssueKind::UnknownExecution)
                );
                assert!(ops.iter().any(|o| o.opcode == Opcode::Unknown));
            } else {
                assert_eq!(ops[0].opcode, Opcode::Initialize);
                assert_eq!(ops[0].target, SymbolId(1));
                assert_eq!(ops[1].opcode, Opcode::Initialize);
                assert_eq!(ops[1].target, SymbolId(3));
                assert_eq!(ops[2].opcode, Opcode::Call);
                assert!(facts.issues.is_empty());
            }
            facts.validate().unwrap();
        }
    }
}
