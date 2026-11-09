//! One explicit compiler macro contract, admitted by the existing ordered JVM
//! classpath owner. No compile-time macro is called during runtime analysis.
use super::*;

const MACRO: &str = "org/scalactic/source/Position.here().";
const RESULT: &str = "org/scalactic/source/Position#";
const OWNER: &str = "org/scalactic/source/Position";
const DESCRIPTOR: &str = "(Ljava/lang/String;Ljava/lang/String;I)V";
const GUARD: &str = "compiler macro expansion runtime effects require explicit model";
const JAR: &str = "c27c33de17d450e29e66c16c5af4cfa33e8ffcf03c124f0a3d249d848cccd4af";
const CLASSES: &[(&str, &str)] = &[
    (
        "org/scalactic/source/Position",
        "73c7d395c3a765256b47b90c545fcf46338472b9d39ffd340f268652477a0bde",
    ),
    (
        "org/scalactic/source/Position$",
        "0be50d4fe2afcea7181cbdcec4d5df04c40cf9adfc79fd2aed469a7bf083b9f3",
    ),
    (
        "org/scalactic/source/PositionMacro",
        "f09c5976f1b11460270b2784baf01a1d64fda2d25fdb7d97026f13c68e69d72e",
    ),
    (
        "org/scalactic/source/PositionMacro$",
        "a544e7e29b6bbaffa4e66083cdf11b1067bc9e59643466c57b43f46402a95f14",
    ),
    (
        "org/scalactic/source/PositionMacro$$typecreator1$1",
        "97c27b0370356fe4ac36f166ba9c2f7b723b856fde2da47d64fb456778a13050",
    ),
    (
        "org/scalactic/source/PositionMacro$PositionMacroImpl",
        "ff9b43780c75fe29869740f671c489d406537b0079c5b5759d90ace3792e52ac",
    ),
    (
        "org/scalactic/source/PositionMacro$sourceCompatHack$",
        "b0e52f74b9f701d6abbd50582663adece83f337b7283352de4ad25e14d6d9c97",
    ),
    (
        "org/scalactic/source/PositionMacro$sourceCompatHack$internal$",
        "1bb7a31598f40a201d711d0c3824082ad0ff3295f101d9547c69f9c9707ea5ee",
    ),
    (
        "org/scalactic/source/PositionMacro$sourceCompatHack$internal$decorators$",
        "f14ec9e421da010c216d513471514adfb29605e059f9d72d25045e8b387351b1",
    ),
];

fn bind_position(hash: &mut Sha256, path: &str, source: &str, span: Span) {
    hash.update(span.start.to_le_bytes());
    hash.update(span.end.to_le_bytes());
    hash.update((path.len() as u64).to_le_bytes());
    hash.update(path.as_bytes());
    hash.update(
        (source.as_bytes()[..span.start as usize]
            .iter()
            .filter(|&&b| b == b'\n')
            .count() as u64)
            .to_le_bytes(),
    );
}

fn authority(
    context: &AdmittedContext,
    loader: &mut CapturedClasspath,
) -> Result<Option<ContentHash>, Error> {
    let mut digest = Sha256::new();
    digest.update(b"scalactic-3.2.19/position-here/1");
    for &(owner, expected) in CLASSES {
        let class = match loader.lookup(owner) {
            Ok(ClassLookup::Found(class)) => class,
            Ok(ClassLookup::Absent(_)) => return Ok(None),
            Err(error) if provenance_failure(error.kind) => return Err(convert_error(error)),
            Err(_) => return Ok(None),
        };
        let Some(index) = class.proof.selected_entry else {
            return Ok(None);
        };
        if context.entries[index].sha256 != ContentHash::from_hex(JAR)?
            || class.proof.class_hash != Some(ContentHash::from_hex(expected)?)
        {
            return Ok(None);
        }
        digest.update(class.proof.class_hash.unwrap().0);
    }
    Ok(Some(ContentHash(digest.finalize().into())))
}

pub(super) fn augment(
    facts: &mut FactSnapshot,
    inputs: &mut OwnedBinaryInputs,
    registry: &mut Registry,
    pending: &mut VecDeque<MethodKey>,
) -> Result<(), Error> {
    let contexts: HashMap<_, _> = inputs
        .contexts
        .iter()
        .enumerate()
        .map(|(i, c)| (c.id, i))
        .collect();
    let mut authorities = HashMap::new();
    let mut resolved = HashSet::new();
    // One reusable, body-local value-use index. Never allocate per macro or
    // inspect arbitrary forged ValueIds as heap sizes.
    let mut counts = Vec::<(u8, u8)>::new();
    let initial_bodies = facts.bodies.len();
    for body_id in 0..initial_bodies {
        let body = facts.bodies[body_id];
        if body.file.is_none() || facts.files[body.file.index()].flags & SOURCE_VERIFIED == 0 {
            continue;
        }
        let Some(&context_id) = contexts.get(&facts.files[body.file.index()].context) else {
            continue;
        };
        if !facts.operations[body.operations.range()]
            .iter()
            .any(|op| op.opcode == Opcode::Unknown && op.flags & OP_MACRO_EXPANSION != 0)
        {
            continue;
        }
        let max_value = facts.operations[body.operations.range()]
            .iter()
            .flat_map(|op| {
                [op.dest, op.a, op.b]
                    .into_iter()
                    .chain(facts.operands[op.arguments.range()].iter().copied())
            })
            .filter(|id| !id.is_none())
            .map(|id| id.0 as usize)
            .max()
            .unwrap_or(0);
        if max_value > body.operations.len as usize * 4 + body.parameters.len as usize + 16 {
            continue;
        }
        counts.resize(max_value + 1, (0, 0));
        counts.fill((0, 0));
        for op in &facts.operations[body.operations.range()] {
            if !op.dest.is_none() {
                let count = &mut counts[op.dest.0 as usize].0;
                *count = count.saturating_add(1);
            }
            for id in [op.a, op.b]
                .into_iter()
                .chain(facts.operands[op.arguments.range()].iter().copied())
            {
                if !id.is_none() {
                    let count = &mut counts[id.0 as usize].1;
                    *count = count.saturating_add(1);
                }
            }
        }
        let mut changed = Sha256::new();
        changed.update(b"source-owned-position-macro/1");
        changed.update(body.body_hash.0);
        let mut count = 0u32;
        for operation in body.operations.range() {
            let op = facts.operations[operation];
            if op.opcode != Opcode::Unknown
                || op.flags != EDGE_UNKNOWN | OP_MACRO_EXPANSION | OP_MACRO_DIRECT_TREE
                || op.target.is_none()
                || op.dest.is_none()
                || op.a.is_none()
                || !op.b.is_none()
                || op.arguments.len != 0
                || facts.symbol_name(op.target) != MACRO
                || facts.symbols[op.target.index()].context != inputs.contexts[context_id].id
                || facts.symbols[op.target.index()].flags & SYMBOL_DEFINED != 0
            {
                continue;
            }
            let Some(metadata) = operation
                .checked_sub(1)
                .filter(|&previous| previous >= body.operations.start as usize)
            else {
                continue;
            };
            let result = facts.operations[metadata];
            if result.opcode != Opcode::Constant
                || result.dest != op.a
                || result.flags != OP_MACRO_RESULT_TYPE
                || result.target.is_none()
                || facts.symbol_name(result.target) != RESULT
                || facts.symbols[result.target.index()].context != inputs.contexts[context_id].id
                || facts.symbols[result.target.index()].flags & SYMBOL_DEFINED != 0
                || !result.a.is_none()
                || !result.b.is_none()
                || result.arguments.len != 0
                || result.span.start != op.span.start
                || result.span.end != result.span.start
                || !body.span.contains(op.span)
            {
                continue;
            }
            // An opaque metadata value may only serve this exact macro input;
            // forged/orphan/type constants never become primitive certificates.
            if counts[op.a.0 as usize] != (1, 1) {
                continue;
            }
            let admitted = if let Some(admitted) = authorities.get(&context_id) {
                *admitted
            } else {
                let context = &mut inputs.contexts[context_id];
                let mut loader = context_loader(context, &inputs.admitted)?;
                let admitted = if let Some(proof) = authority(context, &mut loader)? {
                    let key = (context_id, OWNER.to_owned());
                    if registry
                        .types
                        .get(&key)
                        .is_some_and(|&canonical| canonical != result.target)
                    {
                        None
                    } else {
                        registry.types.insert(key, result.target);
                        let ctor = registry.method(
                            facts,
                            context_id,
                            context,
                            &mut loader,
                            MemberRef {
                                owner: OWNER,
                                name: "<init>",
                                descriptor: DESCRIPTOR,
                            },
                            None,
                            None,
                            pending,
                        )?;
                        (!ctor.is_none()).then_some((proof, ctor, result.target))
                    }
                } else {
                    None
                };
                authorities.insert(context_id, admitted);
                admitted
            };
            let Some((proof, ctor, result_type)) = admitted else {
                continue;
            };
            if result_type != result.target {
                continue;
            }
            let start =
                u32::try_from(facts.operands.len()).map_err(|_| Error::Limit("macro operands"))?;
            facts.operands.extend_from_slice(&[op.a; 3]);
            facts.operations[metadata].target = SymbolId::NONE;
            facts.operations[metadata].flags = 0;
            facts.operations[operation] = OperationRecord {
                opcode: Opcode::Allocate,
                target: ctor,
                a: ValueId::NONE,
                b: ValueId::NONE,
                arguments: IdRange { start, len: 3 },
                flags: 0,
                ..op
            };
            changed.update(proof.0);
            let source = facts.text(facts.files[body.file.index()].source);
            bind_position(&mut changed, facts.path(body.file), source, op.span);
            count += 1;
        }
        if count > 0 {
            changed.update(count.to_le_bytes());
            facts.bodies[body_id].body_hash = ContentHash(changed.finalize().into());
            resolved.insert((body.file, body.symbol));
        }
    }
    let unresolved: HashSet<_> = facts
        .bodies
        .iter()
        .filter(|body| {
            facts.operations[body.operations.range()]
                .iter()
                .any(|op| op.flags & OP_MACRO_EXPANSION != 0)
        })
        .map(|body| (body.file, body.symbol))
        .collect();
    let remove: Vec<_> = facts
        .issues
        .iter()
        .map(|issue| {
            issue.kind == IssueKind::UnknownExecution
                && resolved.contains(&(issue.file, issue.symbol))
                && !unresolved.contains(&(issue.file, issue.symbol))
                && facts.text(issue.detail) == GUARD
        })
        .collect();
    let mut index = 0;
    facts.issues.retain(|_| {
        let keep = !remove[index];
        index += 1;
        keep
    });
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn macro_metadata_hash_binds_prefix_line_even_with_equal_offset_and_total_lines() {
        let before = "ab cd\nef Position.here\n";
        let after = "ab\ncd\nef Position.here ";
        assert_eq!(before.len(), after.len());
        assert_eq!(
            before.bytes().filter(|&b| b == b'\n').count(),
            after.bytes().filter(|&b| b == b'\n').count()
        );
        let start = before.find("Position.here").unwrap();
        assert_eq!(Some(start), after.find("Position.here"));
        let span = Span {
            start: start as u32,
            end: (start + "Position.here".len()) as u32,
        };
        let digest = |source| {
            let mut hash = Sha256::new();
            hash.update(b"same-owned-body-and-pinned-contract");
            bind_position(&mut hash, "PositionSuite.scala", source, span);
            ContentHash(hash.finalize().into())
        };
        assert_ne!(digest(before), digest(after));
    }
}
