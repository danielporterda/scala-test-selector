//! Compact temporary compiler-expression IR. Raw synthetic JSON is dropped with
//! its decode batch; only typed nodes survive until executable ownership joins.
use crate::SourceCoordinates;
use crate::buffer::Buffer;
use selector_facts::FactBuilder;
use selector_types::*;
use serde_json::Value;

fn macro_identity(tree: &Value, depth: usize) -> Option<&str> {
    if depth >= 128 {
        return None;
    }
    tree.pointer("/id_tree/symbol")
        .or_else(|| tree.pointer("/select_tree/id/symbol"))
        .and_then(Value::as_str)
        .or_else(|| {
            tree.pointer("/type_apply_tree/function")
                .or_else(|| tree.pointer("/apply_tree/function"))
                .and_then(|function| macro_identity(function, depth + 1))
        })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    Original,
    Reference,
    Select,
    Apply,
    TypeApply,
    Function,
    Constant,
    Assign,
    Macro,
    MacroDirect,
    Unknown,
}
#[derive(Clone, Copy)]
pub(crate) struct Node {
    pub kind: Kind,
    pub target: SymbolId,
    pub span: Span,
    pub children: IdRange,
    pub parameters: IdRange,
}
#[derive(Clone, Copy)]
pub(crate) struct Root {
    pub file: FileId,
    pub span: Span,
    pub node: u32,
}
#[derive(Default)]
pub(crate) struct Synthetics {
    pub nodes: Vec<Node>,
    pub links: Vec<u32>,
    pub parameters: Vec<SymbolId>,
    pub roots: Vec<Root>,
}
#[derive(Default)]
pub(crate) struct FunctionScratch {
    pending: Vec<u32>,
    preceding: Vec<Span>,
    region_pending: Vec<u32>,
}
pub(crate) struct Function {
    pub node: u32,
    pub root: u32,
    pub regions: Vec<Span>,
}
impl Synthetics {
    pub fn children(&self, node: Node) -> &[u32] {
        &self.links[node.children.range()]
    }
    /// Written expression regions owned by one compiler-created function. Root
    /// synthetic ranges can cover the entire enclosing comprehension; using
    /// that range would incorrectly defer its generator/receiver evaluation too.
    fn function_regions(
        &self,
        function: u32,
        preceding: &[Span],
        pending: &mut Vec<u32>,
    ) -> Vec<Span> {
        pending.clear();
        pending.extend_from_slice(self.children(self.nodes[function as usize]));
        let mut regions = Vec::new();
        while let Some(id) = pending.pop() {
            let node = self.nodes[id as usize];
            match node.kind {
                Kind::Original => regions.push(node.span),
                Kind::Function => (),
                _ => pending.extend_from_slice(self.children(node)),
            }
        }
        regions.sort_unstable_by_key(|r| (r.start, r.end));
        regions.dedup();
        // In a desugared comprehension, OriginalTree can denote the source
        // suffix beginning at `_ <- receiver`, although receiver was already
        // evaluated on the enclosing Apply's qualifier spine. Those source
        // bytes do not belong to the callback. Keep the remaining pieces;
        // trimming the entire prefix would lose unrelated written effects.
        for &previous in preceding {
            let mut index = 0;
            while index < regions.len() {
                let region = regions[index];
                if previous.end <= region.start || previous.start >= region.end {
                    index += 1;
                    continue;
                }
                if previous.start <= region.start {
                    if previous.end >= region.end {
                        regions.remove(index);
                        continue;
                    }
                    regions[index].start = previous.end;
                } else {
                    regions[index].end = previous.start;
                    if previous.end < region.end {
                        regions.push(Span {
                            start: previous.end,
                            end: region.end,
                        });
                    }
                }
                index += 1;
            }
        }
        regions.sort_unstable_by_key(|r| (r.start, r.end));
        regions.dedup();
        regions
    }
    /// Function regions in compiler child order, excluding originals already
    /// represented by preceding siblings. No range or callee is guessed from
    /// source spelling, and nested Function children remain deferred.
    pub fn append_functions(
        &self,
        root: u32,
        functions: &mut Vec<Function>,
        scratch: &mut FunctionScratch,
    ) {
        scratch.pending.clear();
        scratch.preceding.clear();
        scratch.pending.push(root);
        while let Some(id) = scratch.pending.pop() {
            let node = self.nodes[id as usize];
            if node.kind == Kind::Function {
                functions.push(Function {
                    node: id,
                    root,
                    regions: self.function_regions(
                        id,
                        &scratch.preceding,
                        &mut scratch.region_pending,
                    ),
                });
            } else if node.kind == Kind::Original {
                scratch.preceding.push(node.span);
            }
            scratch
                .pending
                .extend(self.children(node).iter().rev().copied());
        }
    }
    pub fn file_roots(&self, file: FileId) -> &[Root] {
        let start = self.roots.partition_point(|r| r.file.0 < file.0);
        let end = start + self.roots[start..].partition_point(|r| r.file == file);
        &self.roots[start..end]
    }
    pub fn parse(
        &mut self,
        builder: &mut FactBuilder,
        file: FileId,
        tree: &Value,
        span: Span,
        coordinates: &SourceCoordinates,
    ) -> Result<u32, Error> {
        let mut target = SymbolId::NONE;
        let mut child_nodes = Buffer::<u32>::new();
        let mut params = Buffer::<SymbolId>::new();
        let mut own_span = span;
        let kind;
        if let Some(id) = tree.get("id_tree") {
            kind = Kind::Reference;
            if let Some(symbol) = id.get("symbol").and_then(Value::as_str) {
                target = builder.ensure_symbol(symbol, file)?;
            }
        } else if let Some(select) = tree.get("select_tree") {
            kind = Kind::Select;
            if let Some(symbol) = select.pointer("/id/symbol").and_then(Value::as_str) {
                target = builder.ensure_symbol(symbol, file)?;
            }
            if let Some(qualifier) = select.get("qualifier") {
                child_nodes.push(self.parse(builder, file, qualifier, span, coordinates)?);
            }
        } else if let Some(apply) = tree.get("apply_tree") {
            kind = Kind::Apply;
            if let Some(function) = apply.get("function") {
                child_nodes.push(self.parse(builder, file, function, span, coordinates)?);
            }
            if let Some(args) = apply.get("arguments").and_then(Value::as_array) {
                for arg in args {
                    child_nodes.push(self.parse(builder, file, arg, span, coordinates)?);
                }
            }
        } else if let Some(apply) = tree.get("type_apply_tree") {
            kind = Kind::TypeApply;
            if let Some(function) = apply.get("function") {
                child_nodes.push(self.parse(builder, file, function, span, coordinates)?);
            }
            // type_arguments are dependencies/type constraints, never execution.
        } else if let Some(function) = tree.get("function_tree") {
            kind = Kind::Function;
            if let Some(parameters) = function.get("parameters").and_then(Value::as_array) {
                for parameter in parameters {
                    if let Some(symbol) = parameter.get("symbol").and_then(Value::as_str) {
                        params.push(builder.ensure_symbol(symbol, file)?);
                    }
                }
            }
            if let Some(body) = function.get("body") {
                child_nodes.push(self.parse(builder, file, body, span, coordinates)?);
            }
        } else if let Some(original) = tree.get("original_tree") {
            if let Some(r) = original.get("range") {
                let coord = |key| r.get(key).and_then(Value::as_i64).unwrap_or(-1);
                match coordinates.semantic_span([
                    coord("start_line"),
                    coord("start_character"),
                    coord("end_line"),
                    coord("end_character"),
                ]) {
                    Ok(source) => {
                        own_span = source;
                        kind = Kind::Original;
                    }
                    Err(_) => {
                        builder.issue(
                            IssueKind::InvalidInput,
                            file,
                            SymbolId::NONE,
                            "invalid original-tree range in compiler synthetic",
                        )?;
                        kind = Kind::Unknown;
                    }
                }
            } else {
                kind = Kind::Unknown;
                builder.issue(
                    IssueKind::InvalidInput,
                    file,
                    SymbolId::NONE,
                    "original-tree compiler synthetic has no validated source range",
                )?;
            }
        } else if tree.get("literal_tree").is_some() {
            kind = Kind::Constant;
        } else if let Some(assign) = tree.get("assign_tree") {
            kind = Kind::Assign;
            for key in ["lhs", "rhs"] {
                if let Some(child) = assign.get(key) {
                    child_nodes.push(self.parse(builder, file, child, span, coordinates)?);
                }
            }
        } else if let Some(expansion) = tree.get("macro_expansion_tree") {
            // Preserve compiler identities as metadata, without executing the
            // compile-time macro or pretending its result type is an allocation.
            if let Some(symbol) = expansion
                .get("before_expansion")
                .and_then(|tree| macro_identity(tree, 0))
            {
                target = builder.ensure_symbol(symbol, file)?;
            }
            if let Some(symbol) = expansion
                .pointer("/tpe/type_ref/symbol")
                .and_then(Value::as_str)
            {
                params.push(builder.ensure_symbol(symbol, file)?);
            }
            let exact_object = |node: Option<&Value>, fields: usize| {
                node.and_then(Value::as_object)
                    .is_some_and(|o| o.len() == fields)
            };
            kind = if !target.is_none()
                && params.len() == 1
                && exact_object(Some(tree), 1)
                && exact_object(Some(expansion), 2)
                && exact_object(expansion.get("before_expansion"), 1)
                && exact_object(expansion.pointer("/before_expansion/id_tree"), 1)
                && exact_object(expansion.get("tpe"), 1)
                && exact_object(expansion.pointer("/tpe/type_ref"), 1)
            {
                Kind::MacroDirect
            } else {
                Kind::Macro
            };
        } else {
            kind = Kind::Unknown;
        }
        let children = IdRange {
            start: u32::try_from(self.links.len()).map_err(|_| Error::Limit("synthetic links"))?,
            len: child_nodes.len() as u32,
        };
        self.links.extend_from_slice(&child_nodes);
        let parameters = IdRange {
            start: u32::try_from(self.parameters.len())
                .map_err(|_| Error::Limit("synthetic parameters"))?,
            len: params.len() as u32,
        };
        self.parameters.extend_from_slice(&params);
        let id = u32::try_from(self.nodes.len()).map_err(|_| Error::Limit("synthetic nodes"))?;
        self.nodes.push(Node {
            kind,
            target,
            span: own_span,
            children,
            parameters,
        });
        Ok(id)
    }
    pub fn bind_root(&mut self, file: FileId, span: Span, node: u32) {
        self.roots.push(Root { file, span, node });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn node(tree: &mut Synthetics, kind: Kind, start: u32, end: u32, children: &[u32]) -> u32 {
        let links = IdRange {
            start: tree.links.len() as u32,
            len: children.len() as u32,
        };
        tree.links.extend_from_slice(children);
        let id = tree.nodes.len() as u32;
        tree.nodes.push(Node {
            kind,
            target: SymbolId::NONE,
            span: Span { start, end },
            children: links,
            parameters: IdRange::default(),
        });
        id
    }
    fn regions(functions: &[Function]) -> Vec<(u32, Vec<Span>)> {
        functions
            .iter()
            .map(|function| (function.node, function.regions.clone()))
            .collect()
    }

    #[test]
    fn overlapping_comprehension_originals_keep_discontiguous_callback_regions() {
        let mut tree = Synthetics::default();
        let receiver = node(&mut tree, Kind::Original, 12, 20, &[]);
        let check = node(&mut tree, Kind::Original, 30, 40, &[]);
        let check_function = node(&mut tree, Kind::Function, 0, 60, &[check]);
        let receiver_map = node(&mut tree, Kind::Apply, 0, 60, &[receiver, check_function]);
        let suffix = node(&mut tree, Kind::Original, 10, 60, &[]);
        let continuation = node(&mut tree, Kind::Function, 0, 60, &[suffix]);
        let root = node(&mut tree, Kind::Apply, 0, 60, &[receiver_map, continuation]);
        let mut functions = Vec::new();
        let mut scratch = FunctionScratch::default();
        tree.append_functions(root, &mut functions, &mut scratch);
        assert_eq!(
            regions(&functions),
            vec![
                (check_function, vec![Span { start: 30, end: 40 }]),
                (
                    continuation,
                    vec![
                        Span { start: 10, end: 12 },
                        Span { start: 20, end: 30 },
                        Span { start: 40, end: 60 },
                    ]
                ),
            ]
        );
        // A different root must not inherit the previous root's source prefix.
        functions.clear();
        tree.append_functions(continuation, &mut functions, &mut scratch);
        assert_eq!(
            regions(&functions),
            vec![(continuation, vec![Span { start: 10, end: 60 }])]
        );
    }

    #[test]
    fn nested_functions_and_later_originals_do_not_become_eager_callback_regions() {
        let mut tree = Synthetics::default();
        let first = node(&mut tree, Kind::Original, 10, 15, &[]);
        let nested_original = node(&mut tree, Kind::Original, 20, 30, &[]);
        let nested = node(&mut tree, Kind::Function, 0, 50, &[nested_original]);
        let last = node(&mut tree, Kind::Original, 35, 40, &[]);
        let body = node(&mut tree, Kind::Apply, 0, 50, &[first, nested, last]);
        let outer = node(&mut tree, Kind::Function, 0, 50, &[body]);
        let later = node(&mut tree, Kind::Original, 0, 50, &[]);
        let root = node(&mut tree, Kind::Apply, 0, 50, &[outer, later]);
        let mut functions = Vec::new();
        tree.append_functions(root, &mut functions, &mut FunctionScratch::default());
        assert_eq!(
            regions(&functions),
            vec![
                (
                    outer,
                    vec![Span { start: 10, end: 15 }, Span { start: 35, end: 40 }]
                ),
                (nested, vec![Span { start: 20, end: 30 }]),
            ]
        );
    }
}
