//! A compiler-only type application cannot add a second term invocation to a
//! complete written call. Match its exact Original function range to one AST
//! application, then reuse that application under the same executable owner.
use super::*;

#[derive(Clone, Copy)]
struct Entry {
    prefix: Span,
    call: Option<Span>,
    owner: Option<usize>,
}
#[derive(Clone, Copy)]
struct Application {
    whole: Span,
    name: Span,
    target: SymbolId,
}
#[derive(Default)]
pub(super) struct Index {
    roots: HashMap<u32, Entry>,
}
impl Index {
    pub fn new(
        ast: AstValue<'_>,
        coords: &SourceCoordinates,
        lookup: &Lookup,
        facts: &FactSnapshot,
        synthetics: &Synthetics,
        file: FileId,
        calls: &HashMap<Span, AstValue<'_>>,
    ) -> Result<Self, Error> {
        let mut applications = HashMap::<Span, Option<Application>>::new();
        for site in rows(ast, "call_sites") {
            if field(site, "kind") != "apply" {
                continue;
            }
            let Ok(prefix) = range(site, "function_start", "function_end", coords) else {
                continue;
            };
            let whole = span(site, coords)?;
            if prefix == whole || !whole.contains(prefix) {
                continue;
            }
            let name = range(site, "name_start", "name_end", coords)?;
            let application = prefix
                .contains(name)
                .then(|| {
                    lookup
                        .resolve(name, 1, facts, true)
                        .map(|target| Application {
                            whole,
                            name,
                            target,
                        })
                })
                .flatten();
            applications
                .entry(prefix)
                .and_modify(|entry| *entry = None)
                .or_insert(application);
        }
        let mut roots = HashMap::new();
        for root in synthetics.file_roots(file) {
            let node = synthetics.nodes[root.node as usize];
            if node.kind != SyntheticKind::TypeApply {
                continue;
            }
            let children = synthetics.children(node);
            if children.len() != 1 {
                continue;
            }
            let original = synthetics.nodes[children[0] as usize];
            if original.kind != SyntheticKind::Original {
                continue;
            }
            if applications.contains_key(&original.span) {
                let call = complete_application(
                    original.span,
                    &applications,
                    calls,
                    coords,
                    lookup,
                    facts,
                );
                roots.insert(
                    root.node,
                    Entry {
                        prefix: original.span,
                        call: call.filter(|_| node.span == original.span),
                        owner: None,
                    },
                );
            }
        }
        Ok(Self { roots })
    }
    pub fn bind_owners(&mut self, bodies: &[Body]) {
        for entry in self.roots.values_mut() {
            entry.owner = entry
                .call
                .and_then(|call| smallest_owner(bodies, call, None))
                .filter(|owner| Some(*owner) == smallest_owner(bodies, entry.prefix, None));
        }
    }
    /// Missing entry keeps the existing bare/eta/unsupported recipe. An entry
    /// without a unique owner must explicitly guard rather than choose a call.
    pub fn binding(&self, root: u32, owner: usize) -> Option<Option<Span>> {
        self.roots
            .get(&root)
            .map(|entry| entry.call.filter(|_| entry.owner == Some(owner)))
    }
}

/// The written-call index coalesces the structural prefixes of `f(a)(b)`.
/// Follow exact AST function ranges to its first retained application. A
/// returned function's first real call remains a boundary when the index keeps
/// it separately. Nothing here chooses a callee or infers a parameter clause.
fn complete_application(
    prefix: Span,
    applications: &HashMap<Span, Option<Application>>,
    calls: &HashMap<Span, AstValue<'_>>,
    coords: &SourceCoordinates,
    lookup: &Lookup,
    facts: &FactSnapshot,
) -> Option<Span> {
    const MAX_APPLICATIONS: usize = 128;
    let first = (*applications.get(&prefix)?)?;
    let mut cursor = prefix;
    for _ in 0..MAX_APPLICATIONS {
        let application = (*applications.get(&cursor)?)?;
        if application.name != first.name
            || application.target != first.target
            || application.whole == cursor
            || !application.whole.contains(cursor)
        {
            return None;
        }
        if let Some(site) = calls.get(&application.whole) {
            let name = range(*site, "name_start", "name_end", coords).ok()?;
            return (field(*site, "kind") == "apply"
                && name == first.name
                && lookup.resolve(name, 1, facts, true) == Some(first.target))
            .then_some(application.whole);
        }
        cursor = application.whole;
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    fn body(span: Span, symbol: u32) -> Body {
        Body {
            id: BodyId(symbol),
            symbol: SymbolId(symbol),
            span,
            lexical: span,
            name: span,
            flags: 0,
            parameters: Vec::new(),
            captures: Vec::new(),
            regions: vec![span],
            returns: vec![],
            synthetic: None,
        }
    }
    fn fixture(control: u8) -> Index {
        let mut builder = FactBuilder::new();
        let target = builder.ensure_symbol("p/A#map().", FileId::NONE).unwrap();
        builder.facts.symbols[target.index()].kind = 3;
        let prefix = Span { start: 1, end: 4 };
        let whole = Span { start: 1, end: 10 };
        let name = Span { start: 2, end: 3 };
        let site = json!({"start":1,"end":10,"function_start":1,"function_end":4,
            "name_start":2,"name_end":3,"kind":if control==1 {"type_apply"} else {"apply"},"arguments":[]});
        let input = json!({"call_sites":if control==2 {vec![site.clone(),site]} else {vec![site]}})
            .to_string();
        let tree = AstTree::parse(&input).unwrap();
        let ast = tree.root();
        let calls = if control == 4 {
            HashMap::new()
        } else {
            HashMap::from([(whole, rows(ast, "call_sites").first().unwrap())])
        };
        let lookup = Lookup {
            occurrences: vec![OccurrenceRecord {
                file: FileId(0),
                span: name,
                symbol: target,
                role: if control == 3 { 2 } else { 1 },
                ordinal: 0,
            }],
        };
        let mut synthetics = Synthetics::default();
        synthetics.nodes.push(crate::synthetics::Node {
            kind: SyntheticKind::Original,
            target: SymbolId::NONE,
            span: if control == 6 {
                Span { start: 6, end: 8 }
            } else {
                prefix
            },
            children: IdRange::default(),
            parameters: IdRange::default(),
        });
        synthetics.links.push(0);
        synthetics.nodes.push(crate::synthetics::Node {
            kind: if control == 7 {
                SyntheticKind::Apply
            } else {
                SyntheticKind::TypeApply
            },
            target: SymbolId::NONE,
            span: if control == 5 { whole } else { prefix },
            children: IdRange { start: 0, len: 1 },
            parameters: IdRange::default(),
        });
        synthetics.roots.push(crate::synthetics::Root {
            file: FileId(0),
            span: prefix,
            node: 1,
        });
        let mut index = Index::new(
            ast,
            &SourceCoordinates::new("                                ").unwrap(),
            &lookup,
            &builder.facts,
            &synthetics,
            FileId(0),
            &calls,
        )
        .unwrap();
        let mut bodies = vec![body(Span { start: 0, end: 32 }, 0)];
        if control == 8 {
            bodies.push(body(prefix, 1));
        }
        index.bind_owners(&bodies);
        index
    }
    #[test]
    fn only_unique_complete_same_body_type_only_prefixes_reuse_source_calls() {
        for control in 0..9 {
            let index = fixture(control);
            let expected = match control {
                0 => Some(Some(Span { start: 1, end: 10 })),
                1 | 6 | 7 => None,
                _ => Some(None),
            };
            assert_eq!(index.binding(1, 0), expected, "control {control}");
        }
    }
    #[test]
    fn a_compiler_prefix_cannot_execute_in_another_body() {
        assert_eq!(fixture(0).binding(1, 1), Some(None));
    }

    fn curried_fixture(control: u8) -> Index {
        let mut builder = FactBuilder::new();
        let target = builder
            .ensure_symbol("p/A#curried().", FileId::NONE)
            .unwrap();
        let foreign = builder.ensure_symbol("p/A#other().", FileId::NONE).unwrap();
        builder.facts.symbols[target.index()].kind = 3;
        builder.facts.symbols[foreign.index()].kind = 3;
        let prefix = Span { start: 1, end: 4 };
        let name = Span { start: 2, end: 3 };
        let application = |function_end, end, foreign| {
            json!({"start":1,"end":end,"function_start":1,
                "function_end":function_end,"name_start":if foreign {5} else {2},
                "name_end":if foreign {6} else {3},"kind":"apply","arguments":[]})
        };
        let mut sites = if control == 7 {
            (0..129)
                .map(|index| application(4 + index, 5 + index, false))
                .collect::<Vec<_>>()
        } else {
            vec![
                application(4, 10, false),
                application(if control == 2 { 11 } else { 10 }, 20, control == 1),
                application(20, if control == 4 { 15 } else { 30 }, false),
            ]
        };
        if control == 3 {
            sites.push(sites[1].clone());
        }
        if control == 8 {
            sites.push(application(4, 12, false));
        }
        let input = json!({"call_sites":sites}).to_string();
        let tree = AstTree::parse(&input).unwrap();
        let ast = tree.root();
        let rows = rows(ast, "call_sites");
        let retained = if control == 7 { 128 } else { 2 };
        let whole = if control == 7 {
            Span { start: 1, end: 133 }
        } else {
            Span { start: 1, end: 30 }
        };
        let mut calls = HashMap::from([(whole, rows.get(retained).unwrap())]);
        if control == 5 {
            calls.insert(Span { start: 1, end: 10 }, rows.first().unwrap());
        }
        let lookup = Lookup {
            occurrences: vec![
                OccurrenceRecord {
                    file: FileId(0),
                    span: name,
                    symbol: target,
                    role: 1,
                    ordinal: 0,
                },
                OccurrenceRecord {
                    file: FileId(0),
                    span: Span { start: 5, end: 6 },
                    symbol: foreign,
                    role: 1,
                    ordinal: 1,
                },
            ],
        };
        let synthetics = Synthetics {
            nodes: vec![
                crate::synthetics::Node {
                    kind: SyntheticKind::Original,
                    target: SymbolId::NONE,
                    span: prefix,
                    children: IdRange::default(),
                    parameters: IdRange::default(),
                },
                crate::synthetics::Node {
                    kind: SyntheticKind::TypeApply,
                    target: SymbolId::NONE,
                    span: prefix,
                    children: IdRange { start: 0, len: 1 },
                    parameters: IdRange::default(),
                },
            ],
            links: vec![0],
            roots: vec![crate::synthetics::Root {
                file: FileId(0),
                span: prefix,
                node: 1,
            }],
            ..Default::default()
        };
        let mut index = Index::new(
            ast,
            &SourceCoordinates::new(&" ".repeat(256)).unwrap(),
            &lookup,
            &builder.facts,
            &synthetics,
            FileId(0),
            &calls,
        )
        .unwrap();
        let mut bodies = vec![body(Span { start: 0, end: 256 }, 0)];
        if control == 6 {
            let mut deferred = body(prefix, 1);
            deferred.flags = BODY_DEFERRED;
            bodies.push(deferred);
        }
        index.bind_owners(&bodies);
        index
    }

    #[test]
    fn coalesced_curried_prefix_reuses_only_the_exact_indexed_application() {
        assert_eq!(
            curried_fixture(0).binding(1, 0),
            Some(Some(Span { start: 1, end: 30 }))
        );
        // An actually retained first call can return a function; never jump
        // across that invocation boundary to flatten its returned callback.
        assert_eq!(
            curried_fixture(5).binding(1, 0),
            Some(Some(Span { start: 1, end: 10 }))
        );
        for control in [1, 2, 3, 4, 6, 7, 8] {
            assert_eq!(
                curried_fixture(control).binding(1, 0),
                Some(None),
                "control {control}"
            );
        }
        assert_eq!(curried_fixture(0).binding(1, 1), Some(None));
    }
}
