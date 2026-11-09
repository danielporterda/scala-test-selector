//! Exact standard metafactory closures become ordinary deferred native recipes.
use super::*;

const VERSION: &[u8] = b"binary-lambda-metafactory/1";

fn callable(lambda: &binary::Lambda<'_>) -> bool {
    let Ok(sam) = binary::method_descriptor(lambda.sam_descriptor) else {
        return false;
    };
    match (lambda.interface, lambda.sam_name) {
        ("java/lang/Runnable", "run") => lambda.sam_descriptor == "()V",
        ("java/util/concurrent/Callable", "call") => {
            lambda.sam_descriptor == "()Ljava/lang/Object;"
        }
        (owner, "apply") => owner
            .strip_prefix("scala/Function")
            .and_then(|n| n.parse::<usize>().ok())
            .is_some_and(|arity| {
                arity == sam.parameter_count
                    && sam.parameters().all(|p| p == "Ljava/lang/Object;")
                    && sam.return_type == "Ljava/lang/Object;"
            }),
        _ => false,
    }
}

pub(super) fn declare(
    facts: &mut FactSnapshot,
    registry: &mut Registry,
    context_index: usize,
    context: &mut AdmittedContext,
    loader: &mut CapturedClasspath,
    enclosing: &MethodKey,
    owner: SymbolId,
    file: FileId,
    class_hash: ContentHash,
    lambda: &binary::Lambda<'_>,
    pending: &mut VecDeque<MethodKey>,
) -> Result<SymbolId, Error> {
    if !callable(lambda) {
        return Ok(SymbolId::NONE);
    }
    let Ok(sam) = binary::method_descriptor(lambda.sam_descriptor) else {
        return Ok(SymbolId::NONE);
    };
    let Ok(implementation) = binary::method_descriptor(lambda.implementation.descriptor) else {
        return Ok(SymbolId::NONE);
    };
    let captures = lambda.captures.len as usize;
    let instance = match lambda.kind {
        binary::InvokeKind::Static => false,
        binary::InvokeKind::Virtual | binary::InvokeKind::Interface => true,
        _ => return Ok(SymbolId::NONE),
    };
    let Some(total) = sam.parameter_count.checked_add(captures) else {
        return Err(Error::Limit("binary lambda parameters"));
    };
    if total != implementation.parameter_count + usize::from(instance)
        // Unbound instance references need a separately evidenced SAM receiver
        // adaptation. Keep them opaque until that path has a genuine fixture.
        || (instance && captures == 0)
        || (sam.return_type != "V" && implementation.return_type == "V")
        || total > 510
    {
        return Ok(SymbolId::NONE);
    }
    let (target, initialization) = registry.call(
        facts,
        context_index,
        context,
        loader,
        lambda.implementation,
        lambda.kind,
        &enclosing.owner,
        pending,
    )?;
    if target.is_none() {
        return Ok(SymbolId::NONE);
    }
    context.admission.check_method(
        registry
            .methods
            .len()
            .saturating_add(registry.synthetic_methods),
    )?;
    let name = format!(
        "@jvm-lambda/{}:{}{}:{}{}:{}:{}:{}",
        enclosing.owner.len(),
        enclosing.owner,
        enclosing.name.len(),
        enclosing.name,
        enclosing.descriptor.len(),
        enclosing.descriptor,
        lambda.offset,
        class_hash
    );
    let symbol = super::declare(facts, context.id, owner, &name, 3, file, 0)?;
    registry.synthetic_methods += 1;
    context.admission.admitted_method();
    let body = BodyId::checked(facts.bodies.len())?;
    let parameters_start =
        u32::try_from(facts.operands.len()).map_err(|_| Error::Limit("binary lambda operands"))?;
    facts
        .operands
        .extend((1..=total).map(|id| ValueId(id as u32)));
    let operations_start = u32::try_from(facts.operations.len())
        .map_err(|_| Error::Limit("binary lambda operations"))?;
    let mut emit = |opcode, dest, a, target, arguments: &[ValueId], flags| -> Result<(), Error> {
        let start = u32::try_from(facts.operands.len())
            .map_err(|_| Error::Limit("binary lambda operands"))?;
        facts.operands.extend_from_slice(arguments);
        facts.operations.push(OperationRecord {
            body,
            opcode,
            target,
            dest,
            a,
            b: ValueId::NONE,
            arguments: IdRange {
                start,
                len: arguments.len() as u32,
            },
            span: Span::default(),
            flags,
        });
        Ok(())
    };
    // The solver supplies invocation actuals before lexical captures.
    for index in 0..total {
        emit(
            Opcode::Parameter,
            ValueId(index as u32 + 1),
            ValueId::NONE,
            SymbolId::NONE,
            &[],
            u32::from(index >= sam.parameter_count),
        )?;
    }
    match initialization {
        Initialization::KnownEmpty => (),
        Initialization::Target(phase) => emit(
            Opcode::Initialize,
            ValueId::NONE,
            ValueId::NONE,
            phase,
            &[],
            0,
        )?,
        Initialization::Unknown => emit(
            Opcode::Unknown,
            ValueId::NONE,
            ValueId::NONE,
            SymbolId::NONE,
            &[],
            0,
        )?,
    }
    // Method-handle arguments are capture-prefix then invocation actuals.
    // For a bound instance handle the first capture is its receiver.
    let mut arguments = Vec::with_capacity(total);
    arguments.extend((0..captures).map(|i| ValueId((sam.parameter_count + i + 1) as u32)));
    arguments.extend((0..sam.parameter_count).map(|i| ValueId((i + 1) as u32)));
    let receiver = if instance {
        arguments.remove(0)
    } else {
        ValueId::NONE
    };
    let result = ValueId::checked(total + 1)?;
    emit(
        if instance {
            Opcode::VirtualCall
        } else {
            Opcode::Call
        },
        if implementation.return_type == "V" {
            ValueId::NONE
        } else {
            result
        },
        receiver,
        target,
        &arguments,
        0,
    )?;
    if sam.return_type == "V" {
        emit(
            Opcode::Constant,
            result,
            ValueId::NONE,
            SymbolId::NONE,
            &[],
            0,
        )?;
    }
    emit(
        Opcode::Return,
        ValueId::NONE,
        result,
        SymbolId::NONE,
        &[],
        0,
    )?;
    drop(emit);
    let mut hash = Sha256::new();
    hash.update(VERSION);
    hash.update(class_hash.0);
    hash.update(lambda.offset.to_le_bytes());
    for text in [
        enclosing.owner.as_str(),
        enclosing.name.as_str(),
        enclosing.descriptor.as_str(),
        lambda.interface,
        lambda.sam_name,
        lambda.sam_descriptor,
        lambda.instantiated_descriptor,
        lambda.implementation.owner,
        lambda.implementation.name,
        lambda.implementation.descriptor,
    ] {
        hash.update((text.len() as u64).to_le_bytes());
        hash.update(text.as_bytes());
    }
    hash.update((captures as u64).to_le_bytes());
    hash.update([instance as u8, lambda.serializable as u8]);
    facts.bodies.push(BodyRecord {
        symbol,
        file,
        span: Span::default(),
        name_span: Span::default(),
        operations: IdRange {
            start: operations_start,
            len: facts.operations.len() as u32 - operations_start,
        },
        parameters: IdRange {
            start: parameters_start,
            len: total as u32,
        },
        body_hash: ContentHash(hash.finalize().into()),
        flags: BODY_BINARY_RECIPE | BODY_DEFERRED,
    });
    Ok(symbol)
}
