//! Exact compiler method selection consumed by a written Apply.
//! No source spelling, overload count, argument count, or label chooses a method.
use super::*;

#[derive(Clone, Copy, Debug)]
pub(super) struct Selection {
    pub target: SymbolId,
}
#[derive(Clone, Copy)]
pub(super) struct Binding {
    pub selection: Option<Selection>,
    /// Validated written qualifier, independent of the selected target. A
    /// rejected target cannot erase receiver evaluation or choose its identity.
    pub qualifier: Span,
}
#[derive(Clone, Copy)]
struct Entry {
    selection: Option<Selection>,
    token: Span,
    owner: Option<usize>,
    receiver: Option<SymbolId>,
}

/// A compiler Select over the exact written stable term can select an apply
/// owned by its aliased value. The owner IDs need not be equal (for example,
/// scala.package.Left and scala.util.Left). This proves only method selection;
/// evaluating the original qualifier and all invocation guards remains required.
fn stable_alias_selection(
    facts: &FactSnapshot,
    file: FileId,
    written: SymbolId,
    selected: SymbolId,
) -> bool {
    let qualifier = &facts.symbols[written.index()];
    let method = &facts.symbols[selected.index()];
    let name = facts.symbol_name(written);
    let stable = match qualifier.kind {
        0 => qualifier.flags & SYMBOL_DEFINED == 0 && qualifier.signature.is_none(),
        3 => qualifier.properties & 1024 != 0 && qualifier.properties & (4 | 64 | 2048) == 0,
        10 => true,
        _ => false,
    };
    stable
        && name.ends_with('.')
        && !name.ends_with(").")
        && selector_types::symbol::global_owner(name).is_some()
        && matches!(method.kind, 0 | 3)
        && selector_types::symbol::global_owner(facts.symbol_name(selected)).is_some()
        && selector_types::symbol::member_name(facts.symbol_name(selected)) == Some("apply")
        && !method.owner.is_none()
        && qualifier.context == facts.files[file.index()].context
        && method.context == qualifier.context
        && facts.symbols[method.owner.index()].context == qualifier.context
}

fn reject_conflicted_aliases(
    index: &mut Index,
    facts: &FactSnapshot,
    file: FileId,
    aliases: &[(Span, [SymbolId; 3])],
) {
    if aliases.is_empty() {
        return;
    }
    // Only wanted numeric IDs are retained. Scan the shared issue table once,
    // rather than cloning it or rescanning it for each selected invocation.
    let mut wanted: Vec<_> = aliases.iter().flat_map(|(_, ids)| *ids).collect();
    wanted.sort_unstable();
    wanted.dedup();
    let mut conflicted = vec![false; wanted.len()];
    let mut context_conflict = false;
    for issue in &facts.issues {
        if issue.kind != IssueKind::ContextConflict {
            continue;
        }
        if issue.symbol.is_none() {
            context_conflict |= issue.file.is_none()
                || facts.files[issue.file.index()].context == facts.files[file.index()].context;
        } else if let Ok(position) = wanted.binary_search(&issue.symbol) {
            conflicted[position] = true;
        }
    }
    for &(span, ids) in aliases {
        if (context_conflict
            || ids
                .iter()
                .any(|id| conflicted[wanted.binary_search(id).unwrap()]))
            && let Some(entry) = index.calls.get_mut(&span)
        {
            entry.selection = None;
        }
    }
}
/// Type arguments affect compilation, not the selected term invocation. Only
/// a single function spine at the same compiler range is transparent here.
fn selected_function(
    synthetics: &Synthetics,
    root: crate::synthetics::Root,
) -> Option<crate::synthetics::Node> {
    let mut id = root.node;
    for _ in 0..128 {
        let node = *synthetics.nodes.get(id as usize)?;
        if node.span != root.span {
            return None;
        }
        if node.kind != SyntheticKind::TypeApply {
            return Some(node);
        }
        let [function] = synthetics.children(node) else {
            return None;
        };
        id = *function;
    }
    None
}
#[derive(Default)]
pub(super) struct Index {
    calls: HashMap<Span, Entry>,
    roots: HashMap<u32, Span>,
    qualifiers: Vec<Span>,
}
impl Index {
    pub fn new(
        ast: AstValue<'_>,
        coordinates: &SourceCoordinates,
        lookup: &Lookup,
        facts: &FactSnapshot,
        synthetics: &Synthetics,
        file: FileId,
    ) -> Result<Self, Error> {
        // First retain the complete application per exact written name anchor.
        // Admit a single written application only. Curried or
        // returned-function applications keep their existing, separate recipe.
        let mut complete: HashMap<Span, (Span, Span, bool)> = HashMap::new();
        for site in rows(ast, "call_sites") {
            let name = range(site, "name_start", "name_end", coordinates)?;
            let whole = span(site, coordinates)?;
            let function =
                range(site, "function_start", "function_end", coordinates).unwrap_or(name);
            let direct =
                field(site, "kind") == "apply" && function != whole && function.contains(name);
            complete
                .entry(name)
                .and_modify(|previous| {
                    if whole.contains(previous.0) && whole != previous.0 {
                        *previous = (whole, function, direct);
                    } else if !previous.0.contains(whole) {
                        previous.2 = false;
                    }
                })
                .or_insert((whole, function, direct));
        }
        let applications: HashMap<_, _> = complete
            .into_iter()
            .filter_map(|(name, (whole, function, direct))| {
                direct.then_some((function, (whole, name)))
            })
            .collect();
        // A compiler-selected method can belong to a lexical parameter's
        // value rather than to a companion. Admit only exact source formals
        // whose declaration scope contains this application. The eventual body
        // must also have the same formal/capture slot.
        let mut formals = HashMap::<SymbolId, Option<Span>>::new();
        for member in rows(ast, "members") {
            let Some(owner) = range(member, "name_start", "name_end", coordinates)
                .ok()
                .and_then(|name| lookup.resolve(name, 2, facts, false))
            else {
                continue;
            };
            for parameter in rows(member, "parameters") {
                let Some(symbol) = range(parameter, "name_start", "name_end", coordinates)
                    .ok()
                    .and_then(|name| lookup.resolve(name, 2, facts, false))
                else {
                    continue;
                };
                let record = facts.symbols[symbol.index()];
                if record.kind == 8
                    && record.owner == owner
                    && record.file == file
                    && record.context == facts.symbols[owner.index()].context
                {
                    formals
                        .entry(symbol)
                        .and_modify(|scope| *scope = None)
                        .or_insert(Some(span(member, coordinates)?));
                }
            }
        }
        let mut lexical = HashMap::<Span, (Span, Span, SymbolId, bool)>::new();
        for site in rows(ast, "call_sites") {
            if field(site, "kind") != "apply" {
                continue;
            }
            let name = range(site, "name_start", "name_end", coordinates)?;
            let function =
                range(site, "function_start", "function_end", coordinates).unwrap_or(name);
            if function != name {
                continue;
            }
            let whole = span(site, coordinates)?;
            let Some(receiver) = lookup.resolve(name, 1, facts, false) else {
                continue;
            };
            if formals
                .get(&receiver)
                .is_some_and(|scope| scope.is_some_and(|scope| scope.contains(whole)))
            {
                lexical
                    .entry(function)
                    .and_modify(|entry| entry.3 = false)
                    .or_insert((whole, name, receiver, true));
            }
        }
        let mut index = Self::default();
        let mut aliases = Vec::new();
        for root in synthetics.file_roots(file) {
            let Some(node) = selected_function(synthetics, *root) else {
                continue;
            };
            let children = synthetics.children(node);
            if node.kind != SyntheticKind::Select
                || node.target.is_none()
                || function_apply(facts, node.target)
            {
                continue;
            }
            let (whole, name, receiver, unique) =
                if let Some(&(whole, name, receiver, unique)) = lexical.get(&root.span) {
                    (whole, name, Some(receiver), unique)
                } else if let Some(&(whole, name)) = applications.get(&root.span) {
                    (whole, name, None, true)
                } else {
                    continue;
                };
            // A method descriptor is compiler identity syntax. It does not
            // infer which overload was selected or grant invocation metadata.
            if !facts.symbol_name(node.target).ends_with(").") {
                continue;
            }
            let written = lookup.resolve(name, 1, facts, false);
            let alias = written.filter(|&written| {
                facts.symbols[node.target.index()].owner != written
                    && stable_alias_selection(facts, file, written, node.target)
            });
            let valid = unique
                && children.len() == 1
                && synthetics.nodes[children[0] as usize].kind == SyntheticKind::Original
                && synthetics.nodes[children[0] as usize].span == root.span
                && (receiver.is_some()
                    || written.is_some_and(|written| {
                        facts.symbols[node.target.index()].owner == written
                    })
                    || alias.is_some());
            let selection = valid.then_some(Selection {
                target: node.target,
            });
            index.roots.insert(root.node, whole);
            index
                .calls
                .entry(whole)
                .and_modify(|entry| entry.selection = None)
                .or_insert(Entry {
                    selection,
                    token: root.span,
                    owner: None,
                    receiver,
                });
            if valid && let Some(written) = alias {
                aliases.push((
                    whole,
                    [
                        written,
                        node.target,
                        facts.symbols[node.target.index()].owner,
                    ],
                ));
            }
        }
        reject_conflicted_aliases(&mut index, facts, file, &aliases);
        index
            .qualifiers
            .extend(index.calls.values().map(|entry| entry.token));
        index
            .qualifiers
            .sort_unstable_by_key(|span| (span.start, span.end));
        index.qualifiers.dedup();
        Ok(index)
    }
    pub fn retain_qualifiers<'a>(
        &self,
        ast: AstValue<'a>,
        coordinates: &SourceCoordinates,
        index: &mut AstIndex<'a>,
    ) -> Result<(), Error> {
        // A selected member's qualifier is an actual source selection such as
        // qualifier().Factory. Its prefix row must survive the general rule
        // that folds structural prefixes into a complete source invocation.
        for site in rows(ast, "call_sites") {
            let key = span(site, coordinates)?;
            if field(site, "kind") == "select"
                && self
                    .qualifiers
                    .binary_search_by_key(&(key.start, key.end), |span| (span.start, span.end))
                    .is_ok()
            {
                if let std::collections::hash_map::Entry::Vacant(entry) = index.calls.entry(key) {
                    entry.insert(site);
                    index.call_spans.push(key);
                }
            }
        }
        index
            .call_spans
            .sort_unstable_by_key(|span| (span.start, span.end));
        Ok(())
    }
    pub fn bind_owners(&mut self, bodies: &[Body]) {
        for (&whole, entry) in &mut self.calls {
            let call_owner = smallest_owner(bodies, whole, None);
            entry.owner = call_owner
                .filter(|owner| smallest_owner(bodies, entry.token, None) == Some(*owner))
                .filter(|owner| {
                    entry.receiver.is_none_or(|receiver| {
                        bodies[*owner]
                            .parameters
                            .iter()
                            .any(|parameter| parameter.symbol == receiver)
                    })
                });
        }
    }
    /// Outer None: no compiler selection. Inner None: conflicting/rejected
    /// selection, which must retain uncertainty rather than falling back.
    pub fn target(&self, whole: Span) -> Option<Option<SymbolId>> {
        self.calls
            .get(&whole)
            .map(|entry| entry.selection.map(|selection| selection.target))
    }
    pub fn binding(&self, whole: Span, owner: usize) -> Option<Binding> {
        self.calls.get(&whole).map(|entry| Binding {
            selection: entry.selection.filter(|_| entry.owner == Some(owner)),
            qualifier: entry.token,
        })
    }
    pub fn root_call(&self, root: u32) -> Option<(Span, Option<usize>)> {
        let whole = *self.roots.get(&root)?;
        Some((whole, self.calls.get(&whole)?.owner))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use md5::{Digest as _, Md5};
    use serde_json::{Value, json};

    const SOURCE: &str = "def f = Factory(second = right(), first = left())";
    const FACTORY: &str = "p/Holder#Factory.";
    const APPLY: &str = "p/Holder#Factory.apply().";
    const ALTERNATIVE: &str = "p/Holder#Factory.apply(+1).";
    const WRONG: &str = "p/Foreign#Factory.apply().";

    fn span_of(text: &str) -> Span {
        let start = SOURCE.find(text).unwrap() as u32;
        Span {
            start,
            end: start + text.len() as u32,
        }
    }
    fn range_value(s: Span) -> Value {
        json!({"start":s.start,"end":s.end})
    }
    fn semantic_range(s: Span) -> Value {
        json!({"start_line":0,"start_character":s.start,"end_line":0,"end_character":s.end})
    }
    fn fixture(control: u8) -> FactSnapshot {
        let name = span_of("Factory");
        let right = span_of("right");
        let left = span_of("left");
        let whole = Span {
            start: name.start,
            end: SOURCE.len() as u32,
        };
        let first = format!("{APPLY}(first)");
        let second = format!("{APPLY}(second)");
        let scalar = json!({"type_ref":{"symbol":"scala/Int#"}});
        let nullary = json!({"method_signature":{"return_type":scalar}});
        let mut apply = json!({"symbol":APPLY,"kind":3,"display_name":"apply","signature":{"method_signature":{
            "parameter_lists":[{"symlinks":[first,second]}],"return_type":scalar}}});
        if control == 1 {
            apply.as_object_mut().unwrap().remove("signature");
        }
        let symbols = json!([
            {"symbol":"p/A#f().","kind":3,"signature":nullary},
            {"symbol":FACTORY,"kind":3,"signature":nullary}, apply,
            {"symbol":ALTERNATIVE,"kind":3,"display_name":"apply","signature":nullary},
            {"symbol":WRONG,"kind":3,"signature":nullary},
            {"symbol":first,"kind":8,"signature":{"value_signature":{"tpe":if control==13 {json!({"by_name_type":{"tpe":scalar}})} else {scalar.clone()}}}},
            {"symbol":second,"kind":8,"signature":{"value_signature":{"tpe":scalar}}},
            {"symbol":"p/Effects.right().","kind":3,"signature":nullary},
            {"symbol":"p/Effects.left().","kind":3,"signature":nullary}
        ]);
        let occurrences = json!([
            {"symbol":"p/A#f().","role":2,"range":semantic_range(Span {start:4,end:5})},
            {"symbol":FACTORY,"role":1,"range":semantic_range(name)},
            {"symbol":second,"role":1,"range":semantic_range(span_of("second"))},
            {"symbol":first,"role":1,"range":semantic_range(span_of("first"))},
            {"symbol":"p/Effects.right().","role":1,"range":semantic_range(right)},
            {"symbol":"p/Effects.left().","role":1,"range":semantic_range(left)}
        ]);
        let target = if matches!(control, 2 | 7) {
            WRONG
        } else {
            APPLY
        };
        let original = if matches!(control, 4 | 9) {
            right
        } else {
            name
        };
        let mut function = json!({"select_tree":{
            "qualifier":{"original_tree":{"range":semantic_range(original)}},"id":{"symbol":target}}});
        for _ in 0..if control >= 5 {
            if control == 6 { 2 } else { 1 }
        } else {
            0
        } {
            function = json!({"type_apply_tree":{"function":function,
                "type_arguments":[{"type_ref":{"symbol":"p/CompileOnly#"}}]}});
        }
        let tree = json!({"range":semantic_range(name),"tree":function});
        let synthetics = if matches!(control, 3 | 8) {
            json!([tree, tree])
        } else {
            json!([tree])
        };
        let argument = |label: &str, call: Span, ordinal| {
            json!({
            "start":span_of(label).start,"end":call.end+2,"expression_start":call.start,
            "expression_end":call.end+2,"clause_index":0,"argument_index":ordinal,
            "label_range":range_value(span_of(label))})
        };
        let site = |name: Span| {
            json!({"start":name.start,"end":name.end+2,
            "name_start":name.start,"name_end":name.end,"function_start":name.start,
            "function_end":name.end,"kind":"apply","arguments":[]})
        };
        let ast = json!({"members":[{"executable":true,"kind":"def","start":0,
            "end":SOURCE.len(),"name_start":4,"name_end":5,"body_start":8,"body_end":SOURCE.len()}],
            "call_sites":[{"start":whole.start,"end":whole.end,"name_start":name.start,
                "name_end":name.end,"function_start":name.start,"function_end":name.end,
                "kind":"apply","arguments":[argument("second",right,0),argument("first",left,1)]},
                site(right),site(left)],"value_expressions":[
                {"start":name.start,"end":name.end,"kind":"reference"}]});
        let input = json!({"path":"A.scala","revision":"r1","source_text":SOURCE,
            "source_sha256":sha(SOURCE.as_bytes()).to_string(),"source_contexts":["a"],"input_target_contexts":["a"],
            "document":{"schema":4,"language":1,"uri":"A.scala",
                "md5":Md5::digest(SOURCE.as_bytes()).iter().map(|v|format!("{v:02x}")).collect::<String>(),
                "symbols":symbols,"occurrences":occurrences,"synthetics":synthetics}});
        let syntax = json!({"path":"A.scala","source_sha256":sha(SOURCE.as_bytes()).to_string(),
            "producer_sha256":ContentHash([1;32]).to_string(),"ast":ast});
        let directory = tempfile::tempdir().unwrap();
        let documents = directory.path().join("documents.jsonl");
        let syntax_path = directory.path().join("syntax.jsonl");
        std::fs::write(&documents, format!("{input}\n")).unwrap();
        std::fs::write(&syntax_path, format!("{syntax}\n")).unwrap();
        crate::import_capture(&documents, Some(&syntax_path), &ExtractOptions::default()).unwrap()
    }
    fn calls<'a>(facts: &'a FactSnapshot, symbol: &str) -> Vec<(usize, &'a OperationRecord)> {
        facts
            .operations
            .iter()
            .enumerate()
            .filter(|(_, op)| {
                matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
                    && facts.symbol_name(op.target) == symbol
            })
            .collect()
    }

    fn genuine_aliases(workers: usize) -> FactSnapshot {
        let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../fixtures/selected-apply-aliases");
        crate::import_capture(
            &directory.join("documents.jsonl"),
            Some(&directory.join("syntax.jsonl")),
            &ExtractOptions {
                workers,
                ..Default::default()
            },
        )
        .unwrap()
    }

    #[test]
    fn genuine_package_alias_selections_preserve_qualifier_actuals_and_missing_metadata() {
        let facts = genuine_aliases(1);
        let file = FileId(0);
        let source = facts.text(facts.files[file.index()].source);
        for (text, alias, selected) in [
            (
                "Left(InvalidScheme)",
                "scala/package.Left.",
                "scala/util/Left.apply().",
            ),
            (
                "Left(InvalidHost)",
                "scala/package.Left.",
                "scala/util/Left.apply().",
            ),
            (
                "Right(url.toString)",
                "scala/package.Right.",
                "scala/util/Right.apply().",
            ),
        ] {
            let start = source.find(text).unwrap() as u32;
            let whole = Span {
                start,
                end: start + text.len() as u32,
            };
            let selected: Vec<_> = calls(&facts, selected)
                .into_iter()
                .filter(|(_, operation)| operation.span == whole)
                .collect();
            assert_eq!(selected.len(), 1, "{text}");
            let (at, operation) = selected[0];
            assert_eq!(operation.arguments.len, 1);
            let qualifier: Vec<_> = facts
                .operations
                .iter()
                .enumerate()
                .filter(|(_, candidate)| {
                    candidate.body == operation.body
                        && candidate.opcode == Opcode::LoadField
                        && facts.symbol_name(candidate.target) == alias
                        && candidate.span.start == whole.start
                })
                .collect();
            assert_eq!(qualifier.len(), 1, "{text}");
            assert!(qualifier[0].0 < at);
            assert_eq!(operation.a, qualifier[0].1.dest);
            let actual = facts.operands[operation.arguments.start as usize];
            assert!(
                facts.operations[qualifier[0].0 + 1..at]
                    .iter()
                    .any(|provider| { provider.body == operation.body && provider.dest == actual }),
                "strict actual provider remains after the qualifier: {text}"
            );
            assert!(!facts.operations.iter().any(|unknown| {
                unknown.body == operation.body
                    && unknown.span == whole
                    && unknown.opcode == Opcode::Unknown
            }));
            assert!(facts.issues.iter().any(|issue| {
                issue.symbol == facts.bodies[operation.body.index()].symbol
                    && facts.text(issue.detail) == "compiler-selected method has no authoritative source argument signature"
            }), "selection does not invent formal metadata: {text}");
        }
        for method in [
            "java/net/URI#getScheme().",
            "java/net/URI#getHost().",
            "java/net/URI#toString().",
        ] {
            assert!(!calls(&facts, method).is_empty());
        }
        let four = genuine_aliases(4);
        let directory = tempfile::tempdir().unwrap();
        let one_path = directory.path().join("one.bin");
        let four_path = directory.path().join("four.bin");
        selector_facts::codec::write(&one_path, &facts).unwrap();
        selector_facts::codec::write(&four_path, &four).unwrap();
        assert_eq!(
            std::fs::read(one_path).unwrap(),
            std::fs::read(four_path).unwrap()
        );
    }

    #[test]
    fn stable_alias_eligibility_is_contextual_and_never_a_method_or_package_guess() {
        for control in 0..13 {
            let mut facts = genuine_aliases(1);
            let written = facts.find_symbol("scala/package.Left.").unwrap();
            let selected = facts.find_symbol("scala/util/Left.apply().").unwrap();
            match control {
                1 => facts.symbols[written.index()].kind = 11,
                2 => facts.symbols[written.index()].kind = 13,
                3 => facts.symbols[written.index()].kind = 8,
                4 => {
                    facts.symbols[written.index()].kind = 3;
                    facts.symbols[written.index()].properties = 0;
                }
                5 | 6 | 7 | 8 => {
                    facts.symbols[written.index()].kind = 3;
                    facts.symbols[written.index()].properties = 1024
                        | match control {
                            5 => 64,
                            6 => 2048,
                            7 => 4,
                            _ => 0,
                        };
                }
                9 => facts.symbols[written.index()].flags |= SYMBOL_DEFINED,
                10 => facts.symbols[selected.index()].context = StrId::NONE,
                11 => facts.symbols[written.index()].context = StrId::NONE,
                12 => facts.symbols[selected.index()].kind = 6,
                _ => (),
            }
            assert_eq!(
                stable_alias_selection(&facts, FileId(0), written, selected),
                matches!(control, 0 | 8),
                "control {control}"
            );
        }
    }

    #[test]
    fn alias_context_conflicts_reject_only_selection_and_keep_qualifier_binding() {
        for control in 0..6 {
            let mut facts = genuine_aliases(1);
            let written = facts.find_symbol("scala/package.Left.").unwrap();
            let selected = facts.find_symbol("scala/util/Left.apply().").unwrap();
            let owner = facts.symbols[selected.index()].owner;
            let whole = Span {
                start: 780,
                end: 799,
            };
            let qualifier = Span {
                start: 780,
                end: 784,
            };
            let mut index = Index::default();
            index.calls.insert(
                whole,
                Entry {
                    selection: Some(Selection { target: selected }),
                    token: qualifier,
                    owner: Some(0),
                    receiver: None,
                },
            );
            facts.issues.push(IssueRecord {
                kind: IssueKind::ContextConflict,
                file: if control == 4 {
                    FileId(0)
                } else {
                    FileId::NONE
                },
                symbol: match control {
                    0 => written,
                    1 => selected,
                    2 => owner,
                    3 | 4 => SymbolId::NONE,
                    _ => facts.find_symbol("java/net/URI#getHost().").unwrap(),
                },
                detail: StrId::NONE,
            });
            reject_conflicted_aliases(
                &mut index,
                &facts,
                FileId(0),
                &[(whole, [written, selected, owner])],
            );
            let binding = index.binding(whole, 0).unwrap();
            assert_eq!(binding.selection.is_some(), control == 5);
            assert_eq!(binding.qualifier, qualifier);
        }
    }

    #[test]
    fn normalized_alias_tree_mutations_reject_duplicate_span_and_non_apply_targets() {
        let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../fixtures/selected-apply-aliases");
        for control in 0..3 {
            // Labeled mutations of the frozen genuine compiler record. These
            // controls are not presented as additional compiler observations.
            let mut document: Value =
                serde_json::from_slice(&std::fs::read(directory.join("documents.jsonl")).unwrap())
                    .unwrap();
            let roots = document["document"]["synthetics"].as_array_mut().unwrap();
            let first = roots
                .iter()
                .position(|root| {
                    root["range"]["start_line"] == 24 && root["range"]["start_character"] == 10
                })
                .unwrap();
            match control {
                0 => roots.push(roots[first].clone()),
                1 => {
                    roots[first]["tree"]["type_apply_tree"]["function"]["select_tree"]["qualifier"]
                        ["original_tree"]["range"]["end_character"] = json!(15);
                }
                _ => {
                    roots[first]["tree"]["type_apply_tree"]["function"]["select_tree"]["id"]["symbol"] =
                        json!("java/net/URI#toString().");
                }
            }
            let temporary = tempfile::tempdir().unwrap();
            let path = temporary.path().join("documents.jsonl");
            std::fs::write(&path, format!("{document}\n")).unwrap();
            let facts = crate::import_capture(
                &path,
                Some(&directory.join("syntax.jsonl")),
                &ExtractOptions::default(),
            )
            .unwrap();
            let whole = Span {
                start: 780,
                end: 799,
            };
            assert!(
                !calls(&facts, "scala/util/Left.apply().")
                    .iter()
                    .any(|(_, op)| op.span == whole)
            );
            assert!(facts.operations.iter().any(|op| {
                op.opcode == Opcode::Unknown && op.span == whole && op.arguments.len == 1
            }));
            let receiver: Vec<_> = facts
                .operations
                .iter()
                .filter(|op| {
                    facts.symbol_name(op.target) == "scala/package.Left."
                        && op.opcode == Opcode::LoadField
                        && op.span
                            == Span {
                                start: 780,
                                end: 784,
                            }
                })
                .collect();
            assert_eq!(receiver.len(), 1);
            assert_eq!(
                facts
                    .operations
                    .iter()
                    .filter(|op| {
                        facts.symbol_name(op.target)
                            == "org/lfdecentralizedtrust/splice/http/UrlValidator.InvalidScheme."
                            && op.span
                                == Span {
                                    start: 785,
                                    end: 798,
                                }
                    })
                    .count(),
                1
            );
            assert!(facts.issues.iter().any(|issue| {
                matches!(
                    issue.kind,
                    IssueKind::UnknownExecution | IssueKind::UnresolvedSymbol
                )
            }));
        }
    }

    #[test]
    fn exact_compiler_selection_calls_once_after_receiver_and_source_ordered_providers() {
        let facts = fixture(0);
        let receiver = calls(&facts, FACTORY);
        let right = calls(&facts, "p/Effects.right().");
        let left = calls(&facts, "p/Effects.left().");
        let selected = calls(&facts, APPLY);
        assert_eq!(
            (receiver.len(), right.len(), left.len(), selected.len()),
            (1, 1, 1, 1)
        );
        assert!(receiver[0].0 < right[0].0 && right[0].0 < left[0].0 && left[0].0 < selected[0].0);
        assert_eq!(selected[0].1.a, receiver[0].1.dest);
        assert_eq!(
            &facts.operands[selected[0].1.arguments.range()],
            &[left[0].1.dest, right[0].1.dest]
        );
        assert_eq!(
            selected[0].1.span,
            Span {
                start: 8,
                end: SOURCE.len() as u32
            }
        );
        assert!(
            calls(&facts, ALTERNATIVE).is_empty(),
            "competing declaration never selects an overload"
        );
        assert!(
            facts.issues.is_empty(),
            "{:?}",
            facts
                .issues
                .iter()
                .map(|i| facts.text(i.detail))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn type_arguments_preserve_one_compiler_selected_complete_invocation() {
        for control in [5, 6] {
            let facts = fixture(control);
            let receiver = calls(&facts, FACTORY);
            let right = calls(&facts, "p/Effects.right().");
            let left = calls(&facts, "p/Effects.left().");
            let selected = calls(&facts, APPLY);
            assert_eq!(
                (receiver.len(), right.len(), left.len(), selected.len()),
                (1, 1, 1, 1)
            );
            assert!(
                receiver[0].0 < right[0].0 && right[0].0 < left[0].0 && left[0].0 < selected[0].0
            );
            assert_eq!(selected[0].1.arguments.len, 2);
            assert_eq!(
                &facts.operands[selected[0].1.arguments.range()],
                &[left[0].1.dest, right[0].1.dest]
            );
            assert!(facts.issues.is_empty());
            assert!(
                facts
                    .operations
                    .iter()
                    .all(|op| facts.symbol_name(op.target) != "p/CompileOnly#")
            );
        }
        for control in [7, 8, 9] {
            let facts = fixture(control);
            assert!(calls(&facts, APPLY).is_empty());
            assert!(calls(&facts, WRONG).is_empty());
            assert_eq!(calls(&facts, "p/Effects.right().").len(), 1);
            assert_eq!(calls(&facts, "p/Effects.left().").len(), 1);
            assert!(
                facts
                    .issues
                    .iter()
                    .any(|issue| issue.kind == IssueKind::UnknownExecution)
            );
        }
    }

    #[test]
    fn typed_selection_uses_declared_by_name_mode_and_preserves_strict_provider_order() {
        let facts = fixture(13);
        let selected = calls(&facts, APPLY);
        assert_eq!(selected.len(), 1);
        let left = calls(&facts, "p/Effects.left().");
        let right = calls(&facts, "p/Effects.right().");
        assert_eq!((left.len(), right.len()), (1, 1));
        assert_ne!(left[0].1.body, selected[0].1.body);
        assert_eq!(right[0].1.body, selected[0].1.body);
        let deferred = facts.bodies[left[0].1.body.index()];
        assert_ne!(deferred.flags & BODY_DEFERRED, 0);
        let binding = facts
            .operations
            .iter()
            .enumerate()
            .find(|(_, op)| op.opcode == Opcode::BindCallback && op.target == deferred.symbol)
            .unwrap();
        assert_eq!(
            &facts.operands[selected[0].1.arguments.range()],
            &[binding.1.dest, right[0].1.dest]
        );
        assert!(right[0].0 < binding.0 && binding.0 < selected[0].0);
        let strict = fixture(14);
        let selected = calls(&strict, APPLY);
        let left = calls(&strict, "p/Effects.left().");
        assert_eq!(
            left[0].1.body, selected[0].1.body,
            "type arguments alone never create deferral"
        );
    }

    #[test]
    fn genuine_compiler_type_applied_try_is_one_complete_written_call() {
        let directory =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/compiler-smoke");
        let facts = crate::import_capture(
            &directory.join("documents.jsonl"),
            Some(&directory.join("syntax.jsonl")),
            &ExtractOptions::default(),
        )
        .unwrap();
        let file = facts
            .files
            .iter()
            .enumerate()
            .find(|(_, file)| facts.text(file.path).ends_with("/Clock.scala"))
            .unwrap();
        let source = facts.text(file.1.source);
        let text = "Try(UnlessShutdown.Outcome(action(now)))";
        let start = source.find(text).unwrap() as u32;
        let whole = Span {
            start,
            end: start + text.len() as u32,
        };
        let selected: Vec<_> = facts
            .operations
            .iter()
            .filter(|op| {
                facts.bodies[op.body.index()].file == FileId(file.0 as u32)
                    && facts.symbol_name(op.target) == "scala/util/Try.apply()."
                    && op.span == whole
            })
            .collect();
        assert_eq!(selected.len(), 1);
        assert_eq!(selected[0].arguments.len, 1);
        assert!(
            !facts
                .operations
                .iter()
                .any(
                    |op| facts.bodies[op.body.index()].file == FileId(file.0 as u32)
                        && facts.symbol_name(op.target) == "scala/util/Try.apply()."
                        && op.span
                            == Span {
                                start,
                                end: start + 3
                            }
                )
        );
        assert!(
            !facts
                .operations
                .iter()
                .any(
                    |op| facts.bodies[op.body.index()].file == FileId(file.0 as u32)
                        && facts.symbol_name(op.target) == "scala/util/Try."
                        && op.span == whole
                        && op.arguments.len != 0
                )
        );
    }

    #[test]
    fn transparent_type_spines_require_unique_same_range_function_children_and_are_bounded() {
        let same = Span { start: 4, end: 9 };
        for control in 0..6 {
            let mut trees = Synthetics::default();
            trees.nodes.push(crate::synthetics::Node {
                kind: SyntheticKind::Select,
                target: SymbolId(1),
                span: if control == 2 {
                    Span { start: 4, end: 8 }
                } else {
                    same
                },
                children: IdRange::default(),
                parameters: IdRange::default(),
            });
            trees.links.push(if control == 4 { 1 } else { 0 });
            if control == 3 {
                trees.links.push(0);
            }
            trees.nodes.push(crate::synthetics::Node {
                kind: SyntheticKind::TypeApply,
                target: SymbolId::NONE,
                span: if control == 1 {
                    Span { start: 3, end: 9 }
                } else {
                    same
                },
                children: IdRange {
                    start: 0,
                    len: if control == 5 {
                        0
                    } else if control == 3 {
                        2
                    } else {
                        1
                    },
                },
                parameters: IdRange::default(),
            });
            let root = crate::synthetics::Root {
                file: FileId(0),
                span: same,
                node: 1,
            };
            assert_eq!(
                selected_function(&trees, root).is_some(),
                control == 0,
                "control{control}"
            );
        }
    }

    #[test]
    fn missing_signature_and_rejected_targets_keep_receiver_and_all_providers() {
        for control in 1..=4 {
            let facts = fixture(control);
            let receiver = calls(&facts, FACTORY);
            let right = calls(&facts, "p/Effects.right().");
            let left = calls(&facts, "p/Effects.left().");
            assert_eq!(
                (receiver.len(), right.len(), left.len()),
                (1, 1, 1),
                "control{control}"
            );
            assert!(
                receiver[0].0 < right[0].0 && right[0].0 < left[0].0,
                "control{control}"
            );
            assert!(
                facts
                    .issues
                    .iter()
                    .any(|i| i.kind == IssueKind::UnknownExecution),
                "control{control}"
            );
            assert!(calls(&facts, WRONG).is_empty());
            if control == 1 {
                let selected = calls(&facts, APPLY);
                assert_eq!(selected.len(), 1);
                assert_eq!(selected[0].1.arguments.len, 2);
            } else {
                assert!(
                    calls(&facts, APPLY).is_empty(),
                    "rejected selection never executes a zero-argument callee"
                );
                let unknown = facts
                    .operations
                    .iter()
                    .find(|op| op.opcode == Opcode::Unknown && op.arguments.len == 2)
                    .unwrap();
                assert_eq!(
                    &facts.operands[unknown.arguments.range()],
                    &[right[0].1.dest, left[0].1.dest]
                );
            }
        }
    }

    #[test]
    fn partial_external_information_cannot_claim_a_complete_apply_inventory() {
        let mut facts = fixture(0);
        let selected = facts.find_symbol(APPLY).unwrap();
        let alternative = facts.find_symbol(ALTERNATIVE).unwrap();
        let owner = facts.symbols[selected.index()].owner;
        facts.symbols[selected.index()].flags &= !SYMBOL_DEFINED;
        facts.symbols[alternative.index()].flags &= !SYMBOL_DEFINED;
        assert!(ApplyMethods::new(&facts).target(owner).is_none());
        facts.symbols[selected.index()].flags |= SYMBOL_DEFINED;
        assert_eq!(ApplyMethods::new(&facts).target(owner), Some(selected));
        facts.symbols[alternative.index()].flags |= SYMBOL_DEFINED;
        assert!(ApplyMethods::new(&facts).target(owner).is_none());
    }

    #[test]
    fn partial_external_information_cannot_infer_default_getter_or_companion_inventory() {
        let mut facts = fixture(0);
        let selected = facts.find_symbol(APPLY).unwrap();
        let owner = facts.symbols[selected.index()].owner;
        let name = "apply$default$1";
        let display = StrId(facts.strings.entries.len() as u32);
        facts.strings.entries.push(TextRange {
            start: facts.strings.bytes.len() as u64,
            len: name.len() as u32,
        });
        facts.strings.bytes.extend_from_slice(name.as_bytes());
        facts.symbols[selected.index()].display = display;
        facts.symbols[selected.index()].flags &= !SYMBOL_DEFINED;
        facts.symbols[owner.index()].kind = 10;
        facts.symbols[owner.index()].flags &= !SYMBOL_DEFINED;
        let partial = DefaultGetters::new(&facts);
        assert!(partial.by_owner.is_empty());
        assert!(partial.objects.is_empty());
        facts.symbols[selected.index()].flags |= SYMBOL_DEFINED;
        facts.symbols[owner.index()].flags |= SYMBOL_DEFINED;
        let source = DefaultGetters::new(&facts);
        assert_eq!(
            source.by_owner.get(&(owner, display)),
            Some(&vec![selected])
        );
        assert_eq!(
            source.objects.get(&(
                facts.symbols[owner.index()].name,
                facts.symbols[owner.index()].context
            )),
            Some(&owner)
        );
    }

    fn indexed_control(kind: &str, direct: bool) -> (FactSnapshot, Index) {
        let facts = fixture(0);
        let target = facts.find_symbol(APPLY).unwrap();
        let token = span_of("Factory");
        let ast = json!({"call_sites":[{"start":token.start,"end":SOURCE.len(),
            "name_start":token.start,"name_end":token.end,"function_start":token.start,
            "function_end":if direct {token.end} else {SOURCE.len() as u32-1},"kind":kind,"arguments":[]}]})
            .to_string();
        let tree = AstTree::parse(&ast).unwrap();
        let mut synthetics = Synthetics::default();
        synthetics.nodes.push(crate::synthetics::Node {
            kind: SyntheticKind::Original,
            target: SymbolId::NONE,
            span: token,
            children: IdRange::default(),
            parameters: IdRange::default(),
        });
        synthetics.links.push(0);
        synthetics.nodes.push(crate::synthetics::Node {
            kind: SyntheticKind::Select,
            target,
            span: token,
            children: IdRange { start: 0, len: 1 },
            parameters: IdRange::default(),
        });
        synthetics.roots.push(crate::synthetics::Root {
            file: FileId(0),
            span: token,
            node: 1,
        });
        let index = Index::new(
            tree.root(),
            &SourceCoordinates::new(SOURCE).unwrap(),
            &Lookup::new(&facts, FileId(0)),
            &facts,
            &synthetics,
            FileId(0),
        )
        .unwrap();
        (facts, index)
    }

    #[test]
    fn selected_call_and_original_must_have_the_same_executable_owner() {
        let (facts, mut index) = indexed_control("apply", true);
        let full = Span {
            start: 8,
            end: SOURCE.len() as u32,
        };
        let token = span_of("Factory");
        let source = facts.find_symbol("p/A#f().").unwrap();
        let make = |symbol, span, flags| Body {
            id: BodyId::NONE,
            symbol,
            span,
            lexical: span,
            name: span,
            flags,
            parameters: Vec::new(),
            captures: Vec::new(),
            regions: vec![span],
            returns: Vec::new(),
            synthetic: None,
        };
        let bodies = vec![make(source, full, 0), make(source, token, BODY_DEFERRED)];
        index.bind_owners(&bodies);
        let binding = index.binding(full, 0).unwrap();
        assert!(binding.selection.is_none());
        assert_eq!(
            binding.qualifier, token,
            "receiver identity never comes from the rejected method"
        );
        assert_eq!(index.root_call(1), Some((full, None)));
        index.bind_owners(&bodies[..1]);
        assert!(index.binding(full, 0).unwrap().selection.is_some());
    }

    #[test]
    fn bare_eta_and_applications_of_a_returned_function_are_not_selected_calls() {
        for (kind, direct) in [("select", true), ("type_apply", true), ("apply", false)] {
            let (_, index) = indexed_control(kind, direct);
            assert!(
                index
                    .target(Span {
                        start: 8,
                        end: SOURCE.len() as u32
                    })
                    .is_none()
            );
            assert!(index.root_call(1).is_none());
        }
    }
    #[test]
    fn lexical_parameter_selection_binds_the_inner_call_and_rejects_foreign_or_missing_slots() {
        for control in 0..5 {
            let mut builder = FactBuilder::new();
            let owner = builder.ensure_symbol("p/A#f().", FileId::NONE).unwrap();
            let parameter = builder.ensure_symbol("p/A#f().(xs)", FileId::NONE).unwrap();
            let target = builder
                .ensure_symbol("p/Callable#apply().", FileId::NONE)
                .unwrap();
            builder.facts.symbols[owner.index()].kind = 3;
            let p = &mut builder.facts.symbols[parameter.index()];
            p.kind = 8;
            p.file = FileId(0);
            p.owner = if control == 1 { SymbolId::NONE } else { owner };
            let inner = Span { start: 20, end: 24 };
            let token = Span { start: 20, end: 21 };
            let site = json!({"start":20,"end":24,"name_start":20,"name_end":21,"function_start":20,"function_end":21,"kind":"apply","arguments":[]});
            let mut calls = vec![
                site.clone(),
                json!({"start":20,"end":26,"name_start":20,"name_end":21,"function_start":20,"function_end":24,"kind":"apply","arguments":[]}),
            ];
            if control == 3 {
                calls.push(site);
            }
            let raw=json!({"members":[{"start":0,"end":40,"name_start":4,"name_end":5,"parameters":[{"name_start":6,"name_end":7}]}],"call_sites":calls}).to_string();
            let tree = AstTree::parse(&raw).unwrap();
            let occurrence = |span, symbol, role| OccurrenceRecord {
                file: FileId(0),
                span,
                symbol,
                role,
                ordinal: 0,
            };
            let lookup = Lookup {
                occurrences: vec![
                    occurrence(Span { start: 4, end: 5 }, owner, 2),
                    occurrence(Span { start: 6, end: 7 }, parameter, 2),
                    occurrence(token, parameter, 1),
                ],
            };
            let mut synthetics = Synthetics::default();
            synthetics.nodes.push(crate::synthetics::Node {
                kind: SyntheticKind::Original,
                target: SymbolId::NONE,
                span: token,
                children: IdRange::default(),
                parameters: IdRange::default(),
            });
            synthetics.links.push(0);
            synthetics.nodes.push(crate::synthetics::Node {
                kind: SyntheticKind::Select,
                target,
                span: token,
                children: IdRange { start: 0, len: 1 },
                parameters: IdRange::default(),
            });
            synthetics.roots.push(crate::synthetics::Root {
                file: FileId(0),
                span: token,
                node: 1,
            });
            let mut index = Index::new(
                tree.root(),
                &SourceCoordinates::new("                                        ").unwrap(),
                &lookup,
                &builder.facts,
                &synthetics,
                FileId(0),
            )
            .unwrap();
            let span = Span { start: 0, end: 40 };
            let body = Body {
                id: BodyId(0),
                symbol: owner,
                span,
                lexical: span,
                name: span,
                flags: 0,
                parameters: if control == 2 {
                    vec![]
                } else {
                    vec![Parameter {
                        symbol: parameter,
                        span: Span { start: 6, end: 7 },
                        capture: false,
                        by_name: false,
                    }]
                },
                captures: vec![],
                regions: vec![span],
                returns: vec![],
                synthetic: None,
            };
            let mut bodies = vec![body];
            if control == 4 {
                bodies.push(Body {
                    id: BodyId(1),
                    symbol: owner,
                    span: token,
                    lexical: token,
                    name: token,
                    flags: 0,
                    parameters: vec![],
                    captures: vec![],
                    regions: vec![token],
                    returns: vec![],
                    synthetic: None,
                });
            }
            index.bind_owners(&bodies);
            let selected = index
                .binding(inner, 0)
                .and_then(|binding| binding.selection)
                .map(|selection| selection.target);
            assert_eq!(
                selected,
                (control == 0).then_some(target),
                "control {control}"
            );
            assert!(
                index.binding(Span { start: 20, end: 26 }, 0).is_none(),
                "outer returned invocation remains separate"
            );
        }
    }
}
