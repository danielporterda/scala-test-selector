//! Compiler-certified conversion of a callable value prefix. Signatures provide
//! argument evaluation modes; source spelling never supplies those semantics.
use super::*;
use serde::Deserialize;
use serde_json::value::RawValue;

#[derive(Clone, Copy)]
struct FunctionMode {
    arity: usize,
    by_name: u32,
}
#[derive(Deserialize)]
struct MethodSignature<'a> {
    #[serde(default, borrow)]
    method_signature: Option<MethodReturn<'a>>,
    #[serde(default, borrow)]
    value_signature: Option<Typed<'a>>,
}
#[derive(Deserialize)]
struct MethodReturn<'a> {
    #[serde(default, borrow)]
    return_type: Option<&'a RawValue>,
}
#[derive(Deserialize)]
struct Typed<'a> {
    #[serde(default, borrow)]
    tpe: Option<&'a RawValue>,
}
#[derive(Deserialize)]
struct TypeNode<'a> {
    #[serde(default, borrow)]
    type_ref: Option<Reference<'a>>,
    #[serde(default, borrow)]
    by_name_type: Option<Typed<'a>>,
    #[serde(default, borrow)]
    annotated_type: Option<Typed<'a>>,
    #[serde(default, borrow)]
    existential_type: Option<Typed<'a>>,
    #[serde(default, borrow)]
    universal_type: Option<Typed<'a>>,
}
#[derive(Deserialize)]
struct Reference<'a> {
    #[serde(default, borrow)]
    symbol: Cow<'a, str>,
    #[serde(default, borrow)]
    type_arguments: Vec<&'a RawValue>,
}
fn arity(symbol: &str) -> Option<usize> {
    symbol
        .strip_prefix("scala/Function")?
        .strip_suffix('#')?
        .parse::<usize>()
        .ok()
        .filter(|&n| n <= 22)
}
fn evaluation(raw: &RawValue) -> Result<Option<bool>, Error> {
    let node: TypeNode<'_> = crate::from_json(raw.get())?;
    let arms = usize::from(node.type_ref.is_some())
        + usize::from(node.by_name_type.is_some())
        + usize::from(node.annotated_type.is_some())
        + usize::from(node.existential_type.is_some())
        + usize::from(node.universal_type.is_some());
    if arms != 1 {
        return Ok(None);
    }
    if let Some(value) = node.by_name_type {
        return Ok(value.tpe.map(|_| true));
    }
    if let Some(reference) = node.type_ref {
        return Ok((!reference.symbol.is_empty()).then_some(false));
    }
    for wrapper in [
        node.annotated_type,
        node.existential_type,
        node.universal_type,
    ]
    .into_iter()
    .flatten()
    {
        if let Some(inner) = wrapper.tpe {
            return evaluation(inner);
        }
    }
    Ok(None)
}
fn returned_function(raw: &RawValue) -> Result<Option<FunctionMode>, Error> {
    let node: TypeNode<'_> = crate::from_json(raw.get())?;
    let arms = usize::from(node.type_ref.is_some())
        + usize::from(node.by_name_type.is_some())
        + usize::from(node.annotated_type.is_some())
        + usize::from(node.existential_type.is_some())
        + usize::from(node.universal_type.is_some());
    if arms != 1 {
        return Ok(None);
    }
    if let Some(reference) = node.type_ref {
        let Some(arity) = arity(&reference.symbol) else {
            return Ok(None);
        };
        if reference.type_arguments.len() != arity + 1 {
            return Ok(None);
        }
        let mut by_name = 0;
        for (index, raw) in reference.type_arguments[..arity].iter().enumerate() {
            match evaluation(raw)? {
                Some(true) => by_name |= 1 << index,
                Some(false) => (),
                None => return Ok(None),
            }
        }
        return Ok(Some(FunctionMode { arity, by_name }));
    }
    for wrapper in [
        node.annotated_type,
        node.existential_type,
        node.universal_type,
    ]
    .into_iter()
    .flatten()
    {
        if let Some(inner) = wrapper.tpe {
            return returned_function(inner);
        }
    }
    Ok(None)
}
#[derive(Clone, Copy)]
struct Conversion {
    root: u32,
    original: u32,
    target: SymbolId,
}
#[derive(Clone, Copy)]
struct Proof {
    mode: FunctionMode,
    conversion: Conversion,
    converter_by_name: bool,
}
struct Entry {
    prefix: Span,
    proof: Option<Proof>,
    arguments: IdRange,
    thunk: Option<usize>,
}
#[derive(Default)]
pub(super) struct Index {
    entries: HashMap<Span, Entry>,
    arguments: Vec<Span>,
    thunks: HashMap<(u32, u32), usize>,
}
fn converter(
    builder: &FactBuilder,
    conversion: Conversion,
) -> Result<Option<(FunctionMode, bool)>, Error> {
    let facts = &builder.facts;
    let record = facts.symbols[conversion.target.index()];
    if record.kind != 3 || record.signature.is_none() {
        return Ok(None);
    }
    let metadata = crate::callable::project(facts.text(record.signature))?;
    if !metadata.shape.known_method || metadata.shape.clauses != 1 || metadata.parameters.len() != 1
    {
        return Ok(None);
    }
    let name = &metadata.parameters[0].0;
    // The parameter is a compiler identity in exactly this contextual method.
    let Some(parameter) = builder.lookup_global_symbol(name, record.context) else {
        return Ok(None);
    };
    let parameter = &facts.symbols[parameter.index()];
    if parameter.context != record.context || parameter.owner != conversion.target {
        return Ok(None);
    }
    if parameter.kind != 8 || parameter.signature.is_none() {
        return Ok(None);
    }
    let parameter: MethodSignature<'_> = crate::from_json(facts.text(parameter.signature))?;
    let Some(raw) = parameter.value_signature.and_then(|value| value.tpe) else {
        return Ok(None);
    };
    let Some(by_name) = evaluation(raw)? else {
        return Ok(None);
    };
    let signature: MethodSignature<'_> = crate::from_json(facts.text(record.signature))?;
    let Some(returned) = signature
        .method_signature
        .and_then(|method| method.return_type)
    else {
        return Ok(None);
    };
    Ok(returned_function(returned)?.map(|mode| (mode, by_name)))
}
fn unique<T>(index: &mut HashMap<Span, Option<T>>, span: Span, value: T) {
    index
        .entry(span)
        .and_modify(|entry| *entry = None)
        .or_insert(Some(value));
}
impl Index {
    pub fn new(
        builder: &FactBuilder,
        file: FileId,
        ast: AstValue<'_>,
        coordinates: &SourceCoordinates,
        lookup: &Lookup,
        synthetics: &Synthetics,
    ) -> Result<Self, Error> {
        let facts = &builder.facts;
        let mut selections = HashMap::<Span, Option<usize>>::new();
        let mut conversions = HashMap::<Span, Option<Conversion>>::new();
        let mut pending = Vec::new();
        for root in synthetics.file_roots(file) {
            let node = synthetics.nodes[root.node as usize];
            let children = synthetics.children(node);
            if node.kind == SyntheticKind::Apply && children.len() == 2 {
                let original = synthetics.nodes[children[1] as usize];
                if original.kind == SyntheticKind::Original && original.span == root.span {
                    if let Some((target, _)) = synthetic_callee(synthetics, children[0]) {
                        conversions
                            .entry(root.span)
                            .and_modify(|entry| *entry = None)
                            .or_insert(Some(Conversion {
                                root: root.node,
                                original: children[1],
                                target,
                            }));
                    }
                }
            }
            pending.push(root.node);
        }
        while let Some(id) = pending.pop() {
            let node = synthetics.nodes[id as usize];
            pending.extend_from_slice(synthetics.children(node));
            if node.kind != SyntheticKind::Select || !function_apply(facts, node.target) {
                continue;
            }
            let Some(owner) = selector_types::symbol::global_owner(facts.symbol_name(node.target))
            else {
                continue;
            };
            let Some(arity) = arity(owner) else { continue };
            let children = synthetics.children(node);
            if children.len() != 1 {
                continue;
            }
            let original = synthetics.nodes[children[0] as usize];
            if original.kind != SyntheticKind::Original {
                continue;
            }
            selections
                .entry(original.span)
                .and_modify(|entry| *entry = None)
                .or_insert(Some(arity));
        }
        // Duplicate source rows are ambiguous authority, even if the last row
        // happens to name a valid method. Retain no representative provider.
        let mut source_calls = HashMap::<Span, Option<AstValue<'_>>>::new();
        for site in rows(ast, "call_sites") {
            if let Ok(span) = span(site, coordinates) {
                unique(&mut source_calls, span, site);
            }
        }
        let mut values = HashMap::<Span, Option<AstValue<'_>>>::new();
        for value in rows(ast, "value_expressions") {
            if let Ok(span) = span(value, coordinates) {
                unique(&mut values, span, value);
            }
        }
        let mut result = Self::default();
        for site in rows(ast, "call_sites") {
            if field(site, "kind") != "apply" {
                continue;
            }
            let Ok(prefix) = range(site, "function_start", "function_end", coordinates) else {
                continue;
            };
            let Some(selected) = selections.get(&prefix) else {
                continue;
            };
            let Some(conversion) = conversions.get(&prefix) else {
                continue;
            };
            let whole = span(site, coordinates)?;
            if whole == prefix {
                continue;
            }
            let source = source_calls.get(&prefix);
            let getter = match source {
                Some(Some(source)) => range(*source, "name_start", "name_end", coordinates)
                    .ok()
                    .and_then(|name| lookup.resolve(name, 1, facts, true)),
                Some(None) => None,
                None if values.get(&prefix).is_some_and(|value| {
                    value.is_some_and(|value| field(value, "kind") == "reference")
                }) =>
                {
                    lookup.resolve(prefix, 1, facts, true)
                }
                None => None,
            };
            let mut valid = false;
            if let Some(getter) = getter {
                let record = facts.symbols[getter.index()];
                if record.kind == 3 && !record.signature.is_none() {
                    let method = crate::callable::project(facts.text(record.signature))?;
                    valid = method.shape.known_method
                        && (source.is_some_and(Option::is_some)
                            || (method.shape.clauses == 0 && method.parameters.is_empty()));
                }
            }
            let proof = match (*selected, *conversion) {
                (Some(selected), Some(conversion)) if valid => converter(builder, conversion)?
                    .filter(|(mode, _)| mode.arity == selected)
                    .map(|(mode, by_name)| Proof {
                        mode,
                        conversion,
                        converter_by_name: by_name,
                    }),
                _ => None,
            };
            let start = u32::try_from(result.arguments.len())
                .map_err(|_| Error::Limit("callable arguments"))?;
            let mut positional = true;
            for argument in rows(site, "arguments") {
                let actual = range(argument, "expression_start", "expression_end", coordinates)
                    .or_else(|_| span(argument, coordinates))?;
                if !prefix.contains(actual) {
                    positional &= argument
                        .get("label_range")
                        .is_none_or(|label| label.is_null());
                    positional &= !result.arguments[start as usize..].contains(&actual);
                    result.arguments.push(actual);
                }
            }
            let count = result.arguments.len() - start as usize;
            let proof = proof.filter(|proof| positional && count == proof.mode.arity);
            let entry = Entry {
                prefix,
                proof,
                arguments: IdRange {
                    start,
                    len: count as u32,
                },
                thunk: None,
            };
            if result.entries.insert(whole, entry).is_some() {
                result.entries.get_mut(&whole).unwrap().proof = None;
            }
        }
        Ok(result)
    }
    pub fn mode(&self, whole: Span, actual: Span) -> Option<bool> {
        let entry = self.entries.get(&whole)?;
        let proof = entry.proof?;
        self.arguments[entry.arguments.range()]
            .iter()
            .position(|span| *span == actual)
            .map(|index| proof.mode.by_name & (1 << index) != 0)
    }
    pub fn add_thunks(
        &mut self,
        builder: &mut FactBuilder,
        file: FileId,
        bodies: &mut Vec<Body>,
    ) -> Result<(), Error> {
        let mut keys: Vec<_> = self.entries.keys().copied().collect();
        keys.sort_unstable_by_key(|span| (span.start, span.end));
        let mut ordinal = HashMap::<SymbolId, usize>::new();
        for whole in keys {
            let entry = self.entries.get_mut(&whole).unwrap();
            let owner = smallest_owner(bodies, whole, None)
                .map(|i| bodies[i].symbol)
                .unwrap_or(SymbolId::NONE);
            if smallest_owner(bodies, entry.prefix, None).map(|i| bodies[i].symbol) != Some(owner)
                || owner.is_none()
            {
                entry.proof = None;
            }
            let Some(proof) = entry.proof else {
                builder.issue(
                    IssueKind::UnknownExecution,
                    file,
                    owner,
                    "callable value conversion lacks unique compiler parameter evaluation metadata",
                )?;
                continue;
            };
            if !proof.converter_by_name {
                continue;
            }
            let number = ordinal.entry(owner).or_default();
            let symbol = synthetic_symbol(
                builder,
                file,
                owner,
                "conversion-byname",
                *number,
                entry.prefix,
            )?;
            *number += 1;
            let index = bodies.len();
            bodies.push(Body {
                id: BodyId::NONE,
                symbol,
                span: entry.prefix,
                lexical: entry.prefix,
                name: entry.prefix,
                flags: BODY_DEFERRED | BODY_SOURCE_RECIPE,
                parameters: Vec::new(),
                captures: Vec::new(),
                regions: vec![entry.prefix],
                returns: vec![entry.prefix],
                synthetic: None,
            });
            self.thunks
                .insert((proof.conversion.root, proof.conversion.original), index);
            entry.thunk = Some(index);
        }
        Ok(())
    }
    pub fn bind(
        &mut self,
        index: &mut AstIndex<'_>,
        bodies: &[Body],
        builder: &mut FactBuilder,
        file: FileId,
    ) -> Result<(), Error> {
        let mut keys: Vec<_> = self.entries.keys().copied().collect();
        keys.sort_unstable_by_key(|span| (span.start, span.end));
        for whole in keys {
            let entry = self.entries.get_mut(&whole).unwrap();
            let owner = smallest_owner(bodies, whole, None);
            if owner.is_none() || owner != smallest_owner(bodies, entry.prefix, None) {
                if entry.proof.take().is_some() {
                    if let Some(proof) = entry.thunk.take() {
                        self.thunks.retain(|_, body| *body != proof);
                    }
                    builder.issue(
                        IssueKind::UnknownExecution,
                        file,
                        owner.map(|i| bodies[i].symbol).unwrap_or(SymbolId::NONE),
                        "callable value prefix crosses executable body ownership",
                    )?;
                }
                continue;
            }
            if entry.proof.is_some() {
                index.returned_calls.insert(whole, entry.prefix);
            }
        }
        Ok(())
    }
    pub fn thunk(&self, stage: u32, argument: u32) -> Option<usize> {
        self.thunks.get(&(stage, argument)).copied()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn raw(value: serde_json::Value) -> Box<RawValue> {
        RawValue::from_string(value.to_string()).unwrap()
    }
    fn integer() -> serde_json::Value {
        json!({"type_ref":{"symbol":"scala/Int#"}})
    }
    #[test]
    fn duplicate_prefix_rows_never_choose_a_representative_provider() {
        let prefix = Span { start: 1, end: 4 };
        let mut index = HashMap::new();
        unique(&mut index, prefix, SymbolId(1));
        assert_eq!(index[&prefix], Some(SymbolId(1)));
        unique(&mut index, prefix, SymbolId(2));
        assert_eq!(index[&prefix], None);
        unique(&mut index, prefix, SymbolId(1));
        assert_eq!(index[&prefix], None);
    }
    #[test]
    fn returned_modes_require_exact_function_arity_and_unambiguous_type_arms() {
        let strict = integer();
        let deferred = json!({"by_name_type":{"tpe":integer()}});
        let signature = |arguments| json!({"type_ref":{"symbol":"scala/Function2#","type_arguments":arguments}});
        let mode = returned_function(&raw(signature(json!([strict, deferred, integer()]))))
            .unwrap()
            .unwrap();
        assert_eq!((mode.arity, mode.by_name), (2, 2));
        for invalid in [
            signature(json!([integer(), integer()])),
            signature(json!([{"repeated_type":{"tpe":integer()}},integer(),integer()])),
            json!({"type_ref":{"symbol":"scala/Function1#","type_arguments":[integer(),integer()]},"by_name_type":{"tpe":integer()}}),
            json!({"type_ref":{"symbol":"user/Function1#","type_arguments":[integer(),integer()]}}),
        ] {
            assert!(returned_function(&raw(invalid)).unwrap().is_none());
        }
    }
    #[test]
    fn converter_modes_require_exact_context_owned_formal_and_one_complete_clause() {
        for control in 0..6 {
            let mut builder = FactBuilder::new();
            let context = builder.intern("a").unwrap();
            let other = builder.intern("b").unwrap();
            let target = builder
                .ensure_global_symbol("p/Api#convert().", context)
                .unwrap();
            let name = "p/Api#convert().(gate)";
            let parameter = builder
                .ensure_global_symbol(name, if control == 1 { other } else { context })
                .unwrap();
            let signature=builder.intern(&json!({"method_signature":{
                "parameter_lists":if control==5 {json!([{"symlinks":[name]},{}])} else {json!([{"symlinks":[name]}])},
                "return_type":{"type_ref":{"symbol":"scala/Function1#","type_arguments":[{"by_name_type":{"tpe":integer()}},integer()]}}}}).to_string()).unwrap();
            builder.facts.symbols[target.index()].kind = 3;
            builder.facts.symbols[target.index()].signature = signature;
            let p_signature = builder
                .intern(
                    &json!({"value_signature":{"tpe":if control==4 {json!({})} else {integer()}}})
                        .to_string(),
                )
                .unwrap();
            let p = &mut builder.facts.symbols[parameter.index()];
            p.kind = if control == 2 { 9 } else { 8 };
            p.owner = if control == 3 { SymbolId::NONE } else { target };
            p.signature = p_signature;
            let result = converter(
                &builder,
                Conversion {
                    root: 0,
                    original: 1,
                    target,
                },
            )
            .unwrap();
            if control == 0 {
                let (mode, by_name) = result.unwrap();
                assert_eq!((mode.arity, mode.by_name, by_name), (1, 1, false));
            } else {
                assert!(result.is_none(), "control {control}");
            }
        }
    }
}
