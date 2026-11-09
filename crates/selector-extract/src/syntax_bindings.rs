//! Compiler-only value references have no written occurrence. Assign them once
//! to lexical execution regions, then carry only compact capture identities.
use super::*;

pub(super) fn synthetic_captures(
    facts: &FactSnapshot,
    file: FileId,
    bodies: &[Body],
    synthetics: &Synthetics,
) -> Vec<(usize, SymbolId)> {
    let mut functions: Vec<_> = bodies
        .iter()
        .enumerate()
        .filter_map(|(index, body)| body.synthetic.map(|s| (s.function, index)))
        .collect();
    functions.sort_unstable();
    let mut symbols: Vec<_> = bodies
        .iter()
        .enumerate()
        .map(|(i, b)| (b.symbol, i))
        .collect();
    symbols.sort_unstable();
    let parents: Vec<_> = bodies
        .iter()
        .map(|body| {
            let parent = facts.symbols[body.symbol.index()].owner;
            symbols
                .binary_search_by_key(&parent, |&(symbol, _)| symbol)
                .ok()
                .map(|i| symbols[i].1)
        })
        .collect();
    let mut regions: Vec<_> = bodies
        .iter()
        .enumerate()
        .filter(|(_, body)| body.synthetic.is_none())
        .map(|(index, body)| (body.span, index))
        .collect();
    regions.sort_unstable_by_key(|&(span, index)| (span.start, std::cmp::Reverse(span.end), index));
    let mut max_end = Vec::with_capacity(regions.len());
    let mut max = 0;
    for &(span, _) in &regions {
        max = max.max(span.end);
        max_end.push(max);
    }
    let mut pending = Vec::new();
    let mut uses = Vec::new();
    for root in synthetics.file_roots(file) {
        let mut cursor = regions.partition_point(|&(span, _)| span.start <= root.span.start);
        let mut owner: Option<usize> = None;
        while cursor != 0 {
            cursor -= 1;
            if max_end[cursor] < root.span.end {
                break;
            }
            let (span, index) = regions[cursor];
            if span.contains(root.span)
                && owner.is_none_or(|previous| {
                    (
                        span.end - span.start,
                        bodies[index].flags & BODY_DEFERRED == 0,
                        index,
                    ) < (
                        bodies[previous].span.end - bodies[previous].span.start,
                        bodies[previous].flags & BODY_DEFERRED == 0,
                        previous,
                    )
                })
            {
                owner = Some(index);
            }
        }
        pending.push((root.node, owner));
        while let Some((id, mut owner)) = pending.pop() {
            let node = synthetics.nodes[id as usize];
            if node.kind == SyntheticKind::Function {
                owner = functions
                    .binary_search_by_key(&id, |&(node, _)| node)
                    .ok()
                    .map(|i| functions[i].1);
                if owner.is_none() {
                    continue;
                }
            }
            if let Some(owner) = owner {
                if matches!(node.kind, SyntheticKind::Reference | SyntheticKind::Select)
                    && !node.target.is_none()
                    && matches!(facts.symbols[node.target.index()].kind, 8 | 19)
                {
                    uses.push((owner, node.target));
                }
            }
            pending.extend(
                synthetics
                    .children(node)
                    .iter()
                    .rev()
                    .map(|&child| (child, owner)),
            );
        }
    }
    uses.sort_unstable();
    uses.dedup();
    let mut captures = Vec::new();
    let mut chain = Vec::new();
    for (owner, symbol) in uses {
        chain.clear();
        let declaration = facts.symbols[symbol.index()];
        let mut cursor = Some(owner);
        let mut bound = false;
        // No scope inference from spelling: stop at the exact declared formal
        // or an owned source-local definition. Cyclic/missing owners fail closed.
        for _ in 0..bodies.len() {
            let Some(index) = cursor else {
                break;
            };
            let body = &bodies[index];
            if body.parameters.iter().any(|p| p.symbol == symbol)
                || (declaration.file == file
                    && declaration.flags & SYMBOL_DEFINED != 0
                    && body.span.contains(declaration.span)
                    && (body.synthetic.is_none()
                        || body.regions.iter().any(|s| s.contains(declaration.span))))
            {
                bound = true;
                break;
            }
            chain.push(index);
            cursor = parents[index];
        }
        if bound {
            captures.extend(
                chain
                    .iter()
                    .filter(|&&index| {
                        bodies[index].flags & BODY_DEFERRED != 0
                            || (bodies[index].flags & BODY_INITIALIZER != 0
                                && selector_types::symbol::is_local(
                                    facts.symbol_name(bodies[index].symbol),
                                ))
                    })
                    .map(|&index| (index, symbol)),
            );
        }
    }
    captures.sort_unstable();
    captures.dedup();
    captures
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn fixture() -> (FactBuilder, FileId, SymbolId, Vec<Parameter>) {
        let mut builder = FactBuilder::new();
        let context = builder.intern("provider").unwrap();
        let text = builder.intern(&" ".repeat(100)).unwrap();
        builder.facts.files.push(FileRecord {
            path: text,
            source: text,
            revision: StrId::NONE,
            context,
            source_hash: ContentHash([1; 32]),
            flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
        });
        let file = FileId(0);
        let method = builder.ensure_symbol("p/A#m().", file).unwrap();
        let mut formals = Vec::new();
        for name in ["a", "b", "evidence"] {
            let symbol = builder
                .ensure_symbol(&format!("p/A#m().({name})"), file)
                .unwrap();
            let signature = builder
                .intern(r#"{"value_signature":{"tpe":{"type_ref":{"symbol":"scala/Int#"}}}}"#)
                .unwrap();
            let declaration = &mut builder.facts.symbols[symbol.index()];
            declaration.owner = method;
            declaration.kind = 8;
            declaration.signature = signature;
            declaration.properties = if name == "evidence" { 32 } else { 0 };
            formals.push(symbol);
        }
        let signature = builder
            .intern(
                &json!({"method_signature":{"parameter_lists":[
            {"symlinks":["p/A#m().(a)","p/A#m().(b)"]},{"symlinks":["p/A#m().(evidence)"]}]}})
                .to_string(),
            )
            .unwrap();
        let declaration = &mut builder.facts.symbols[method.index()];
        declaration.kind = 3;
        declaration.file = file;
        declaration.signature = signature;
        let written = formals[..2]
            .iter()
            .enumerate()
            .map(|(i, &symbol)| Parameter {
                symbol,
                span: Span {
                    start: i as u32,
                    end: i as u32 + 1,
                },
                capture: false,
                by_name: false,
            })
            .collect();
        (builder, file, method, written)
    }

    #[test]
    fn generated_formals_use_compiler_order_and_missing_or_foreign_modes_guard() {
        for control in 0..5 {
            let (mut builder, file, method, mut written) = fixture();
            let evidence = builder.lookup_symbol("p/A#m().(evidence)", file).unwrap();
            match control {
                0 => written.reverse(),
                1 => builder.facts.symbols[method.index()].signature = StrId::NONE,
                2 => builder.facts.symbols[evidence.index()].signature = StrId::NONE,
                3 => builder.facts.symbols[evidence.index()].owner = SymbolId::NONE,
                4 => {
                    let signature=builder.intern(r#"{"method_signature":{"parameter_lists":[{"symlinks":["p/A#m().(a)","p/A#m().(b)"]},{"symlinks":["p/A#m().(evidence)","p/A#m().(evidence)"]}]}}"#).unwrap();
                    builder.facts.symbols[method.index()].signature = signature;
                }
                _ => unreachable!(),
            }
            let parameters = method_parameters(
                &mut builder,
                file,
                method,
                written,
                Span { start: 4, end: 5 },
                true,
            )
            .unwrap();
            if control == 0 {
                assert_eq!(parameters.len(), 3);
                assert_eq!(
                    builder.facts.symbol_name(parameters[0].symbol),
                    "p/A#m().(a)"
                );
                assert_eq!(parameters[2].symbol, evidence);
                assert_eq!(parameters[2].span, Span { start: 4, end: 4 });
                assert!(builder.facts.issues.is_empty());
            } else {
                assert!(
                    builder
                        .facts
                        .issues
                        .iter()
                        .any(|issue| issue.kind == IssueKind::UnknownExecution
                            && issue.symbol == method),
                    "control {control}"
                );
            }
        }
    }

    #[test]
    fn value_signature_field_initializers_are_not_missing_method_metadata() {
        let (mut builder, file, method, _) = fixture();
        builder.facts.symbols[method.index()].signature = StrId::NONE;
        assert!(
            method_parameters(
                &mut builder,
                file,
                method,
                Vec::new(),
                Span::default(),
                false
            )
            .unwrap()
            .is_empty()
        );
        assert!(builder.facts.issues.is_empty());
    }

    #[test]
    fn synthetic_only_uses_bind_to_deferred_scope_and_thread_local_initializer_environment() {
        let (mut builder, file, method, parameters) = fixture();
        let evidence = builder.lookup_symbol("p/A#m().(evidence)", file).unwrap();
        let local = builder.ensure_symbol("local0", file).unwrap();
        let closure = builder.ensure_symbol("@closure:test", file).unwrap();
        builder.facts.symbols[local.index()].owner = method;
        builder.facts.symbols[closure.index()].owner = local;
        let foreign = builder.ensure_symbol("p/Other#m().(e)", file).unwrap();
        builder.facts.symbols[foreign.index()].kind = 8;
        let make = |symbol, span, lexical, flags, parameters| Body {
            id: BodyId::NONE,
            symbol,
            span,
            lexical,
            name: span,
            flags,
            parameters,
            captures: Vec::new(),
            regions: vec![span],
            returns: Vec::new(),
            synthetic: None,
        };
        let mut formals = parameters;
        formals.push(Parameter {
            symbol: evidence,
            span: Span::default(),
            capture: false,
            by_name: false,
        });
        let bodies = vec![
            make(
                method,
                Span { start: 0, end: 100 },
                Span { start: 0, end: 100 },
                0,
                formals,
            ),
            make(
                local,
                Span { start: 20, end: 50 },
                Span { start: 18, end: 50 },
                BODY_INITIALIZER,
                Vec::new(),
            ),
            make(
                closure,
                Span { start: 20, end: 50 },
                Span { start: 20, end: 50 },
                BODY_DEFERRED,
                Vec::new(),
            ),
        ];
        let mut synthetics = Synthetics::default();
        for (target, start) in [
            (evidence, 25),
            (evidence, 26),
            (foreign, 27),
            (evidence, 10),
        ] {
            let span = Span {
                start,
                end: start + 1,
            };
            let node = synthetics.nodes.len() as u32;
            synthetics.nodes.push(crate::synthetics::Node {
                kind: SyntheticKind::Reference,
                target,
                span,
                children: IdRange::default(),
                parameters: IdRange::default(),
            });
            synthetics
                .roots
                .push(crate::synthetics::Root { file, span, node });
        }
        let captures = synthetic_captures(&builder.facts, file, &bodies, &synthetics);
        assert_eq!(
            captures,
            [(1, evidence), (2, evidence)],
            "duplicate uses dedup; sibling/foreign references do not manufacture captures"
        );
    }
}
