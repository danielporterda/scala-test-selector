use crate::buffer::Buffer;
use crate::callable::Shape as CallShape;
use crate::syntax_tree::{Array as AstArray, Node as AstValue, Tree as AstTree};
use crate::synthetics::{Kind as SyntheticKind, Synthetics};
use crate::{ExtractOptions, Input, SourceCoordinates, json_error, sha};
use rayon::prelude::*;
use selector_facts::*;
use selector_types::*;
use serde::Deserialize;
use serde_json::value::RawValue;
use sha2::{Digest, Sha256};
use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::path::Path;
#[path = "syntax_callable_value.rs"]
mod callable_value;
#[path = "syntax_bindings.rs"]
mod compiler_bindings;
#[path = "syntax_constructor.rs"]
mod constructor;
#[path = "syntax_repeated.rs"]
mod repeated;
#[path = "syntax_selected_apply.rs"]
mod selected_apply;
#[path = "syntax_type_prefix.rs"]
mod type_prefix;

const PARAM_CAPTURE: u32 = 1;

// A registration remains the exact compiler-selected invocation even after its
// callback scheduling is represented by a dedicated opcode. Its later implicit
// clause must still be evaluated before the registration. This certificate says
// where the callback actual lives; it grants no purity or callee-body authority.
fn certified_registration_completion(op: &OperationRecord, facts: &FactSnapshot) -> bool {
    op.opcode == Opcode::RegisterTest
        && !op.target.is_none()
        && selector_framework::scalatest_callback_argument(facts.symbol_name(op.target))
            .is_some_and(|call| call.kind == selector_framework::ScalaTestCall::Registration)
        && op.arguments.range().end <= facts.operands.len()
        && callback_argument_slot(op.flags).is_some_and(|slot| slot < op.arguments.len as usize)
}

#[derive(Clone, Copy)]
struct CallbackParameter {
    clause: u32,
    argument: u32,
    by_name: bool,
    function_arity: Option<usize>,
}
fn callback_parameter(symbol: &str) -> Option<CallbackParameter> {
    if matches!(
        symbol,
        "scala/concurrent/Future#map()." | "scala/concurrent/Future#flatMap()."
    ) {
        // This records one exact argument position, not scheduling, purity or
        // result behavior. The transfer stage retains deferred execution guards.
        return Some(CallbackParameter {
            clause: 0,
            argument: 0,
            by_name: false,
            function_arity: Some(1),
        });
    }
    selector_framework::scalatest_callback_argument(symbol).map(|callback| CallbackParameter {
        clause: callback.clause,
        argument: callback.argument,
        by_name: callback.by_name,
        function_arity: None,
    })
}

fn synthetic_callee(synthetics: &Synthetics, mut id: u32) -> Option<(SymbolId, Option<u32>)> {
    for _ in 0..128 {
        let node = synthetics.nodes[id as usize];
        match node.kind {
            SyntheticKind::Reference if !node.target.is_none() => return Some((node.target, None)),
            SyntheticKind::Select if !node.target.is_none() => {
                return Some((node.target, synthetics.children(node).first().copied()));
            }
            SyntheticKind::TypeApply => id = *synthetics.children(node).first()?,
            _ => return None,
        }
    }
    None
}

/// Compiler Apply clauses in evaluation order, stopping at an exact callee.
/// An intervening Select (including FunctionN.apply) starts its own invocation.
fn synthetic_spine(
    synthetics: &Synthetics,
    mut id: u32,
) -> Option<(SymbolId, Option<u32>, Buffer<u32>)> {
    let mut stages = Buffer::new();
    for _ in 0..128 {
        let node = synthetics.nodes[id as usize];
        match node.kind {
            SyntheticKind::Apply => {
                stages.push(id);
                id = *synthetics.children(node).first()?;
            }
            SyntheticKind::TypeApply => id = *synthetics.children(node).first()?,
            _ => {
                let (target, receiver) = synthetic_callee(synthetics, id)?;
                stages.reverse();
                return Some((target, receiver, stages));
            }
        }
    }
    None
}

fn function_apply(facts: &FactSnapshot, target: SymbolId) -> bool {
    if target.is_none() {
        return false;
    }
    let symbol = facts.symbol_name(target);
    selector_types::symbol::member_name(symbol) == Some("apply")
        && selector_types::symbol::global_owner(symbol)
            .and_then(|owner| owner.strip_prefix("scala/Function"))
            .and_then(|arity| arity.strip_suffix('#'))
            .is_some_and(|arity| !arity.is_empty() && arity.bytes().all(|b| b.is_ascii_digit()))
}

fn synthetic_wrappers(
    synthetics: &Synthetics,
    file: FileId,
    bodies: &[Body],
) -> HashMap<Span, Option<(u32, usize)>> {
    let mut result = HashMap::new();
    let mut pending = Vec::new();
    for root in synthetics.file_roots(file) {
        if synthetics.nodes[root.node as usize].kind != SyntheticKind::Apply {
            continue;
        }
        pending.clear();
        pending.push(root.node);
        let mut originals = 0;
        let mut exact = false;
        while let Some(id) = pending.pop() {
            let node = synthetics.nodes[id as usize];
            if node.kind == SyntheticKind::Original {
                originals += 1;
                exact = node.span == root.span;
            } else {
                pending.extend_from_slice(synthetics.children(node));
            }
            if originals > 1 {
                break;
            }
        }
        if originals == 1 && exact {
            if let Some(owner) = smallest_owner(bodies, root.span, None) {
                result
                    .entry(root.span)
                    .and_modify(|entry| *entry = None)
                    .or_insert(Some((root.node, owner)));
            }
        }
    }
    result
}

fn is_package(facts: &FactSnapshot, target: SymbolId) -> bool {
    !target.is_none()
        && (facts.symbols[target.index()].kind == 11 || facts.symbol_name(target).ends_with('/'))
}

#[derive(Default, Deserialize)]
#[serde(deny_unknown_fields)]
struct EmptyScope<'a> {
    #[serde(default, borrow)]
    symlinks: Option<&'a RawValue>,
    #[serde(default, borrow)]
    hardlinks: Option<&'a RawValue>,
}
impl EmptyScope<'_> {
    fn is_empty(&self) -> bool {
        [self.symlinks, self.hardlinks]
            .into_iter()
            .all(|links| links.is_none_or(|links| links.get().trim() == "[]"))
    }
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct AnonymousParent<'a> {
    #[serde(borrow)]
    type_ref: AnonymousParentName<'a>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct AnonymousParentName<'a> {
    symbol: &'a str,
}
#[derive(Deserialize)]
struct AnonymousSignature<'a> {
    #[serde(borrow)]
    parents: [AnonymousParent<'a>; 2],
    #[serde(borrow)]
    declarations: EmptyScope<'a>,
    #[serde(borrow)]
    type_parameters: EmptyScope<'a>,
}
#[derive(Deserialize)]
struct AnonymousClassSignature<'a> {
    #[serde(borrow)]
    class_signature: AnonymousSignature<'a>,
}

/// Empty anonymous subclasses of a single trait still execute both their JVM
/// superclass and the trait initializer. Exact compiler local identity and its
/// complete ordered parent signature are required; a trait reference is never
/// itself an allocation class or an anonymous constructor overload.
fn empty_anonymous_trait(
    builder: &FactBuilder,
    lookup: &Lookup,
    coords: &SourceCoordinates,
    file: FileId,
    ctor: AstValue<'_>,
) -> Option<(SymbolId, [SymbolId; 2])> {
    let facts = &builder.facts;
    if field(ctor, "kind") != "anonymous_allocation" || rows(ctor, "arguments").len() != 0 {
        return None;
    }
    let name = range(ctor, "name_start", "name_end", coords).ok()?;
    let init = span(ctor, coords).ok()?;
    let allocation = range(ctor, "allocation_start", "allocation_end", coords).ok()?;
    let source = facts.text(facts.files[file.index()].source);
    if !allocation.contains(init)
        || !init.contains(name)
        || source
            .get(allocation.start as usize..init.start as usize)?
            .trim()
            != "new"
    {
        return None;
    }
    let braces = source
        .get(init.end as usize..allocation.end as usize)?
        .trim();
    if !braces
        .strip_prefix('{')?
        .strip_suffix('}')?
        .trim()
        .is_empty()
    {
        return None;
    }
    let brace_start = u32::try_from(braces.as_ptr() as usize - source.as_ptr() as usize).ok()?;
    let object_constructor = lookup.resolve(
        Span {
            start: brace_start,
            end: brace_start,
        },
        1,
        facts,
        true,
    )?;
    if !matches!(
        facts.symbol_name(object_constructor),
        "java/lang/Object#`<init>`()." | "java/lang/Object#<init>()."
    ) {
        return None;
    }
    let class = lookup.resolve(
        Span {
            start: name.start,
            end: name.start,
        },
        2,
        facts,
        false,
    )?;
    let record = facts.symbols[class.index()];
    if record.kind != 13
        || record.file != file
        || record.context != facts.files[file.index()].context
        || record.flags & (SYMBOL_DEFINED | SYMBOL_SCALA_PARENTS_COMPLETE)
            != SYMBOL_DEFINED | SYMBOL_SCALA_PARENTS_COMPLETE
        || !selector_types::symbol::is_local(facts.symbol_name(class))
        || record.signature.is_none()
    {
        return None;
    }
    let proof: AnonymousClassSignature<'_> =
        serde_json::from_str(facts.text(record.signature)).ok()?;
    let signature = proof.class_signature;
    let names = signature.parents.map(|parent| parent.type_ref.symbol);
    if !signature.declarations.is_empty()
        || !signature.type_parameters.is_empty()
        || !matches!(names[0], "scala/AnyRef#" | "java/lang/Object#")
        || names[0] == names[1]
    {
        return None;
    }
    let written = lookup.resolve(name, 1, facts, false)?;
    if facts.symbol_name(written) != names[1]
        || !matches!(facts.symbols[written.index()].kind, 0 | 14)
    {
        return None;
    }
    Some((class, [object_constructor, written]))
}

#[derive(Deserialize)]
struct SyntaxRow<'a> {
    #[serde(borrow)]
    path: Cow<'a, str>,
    #[serde(borrow)]
    source_sha256: Cow<'a, str>,
    #[serde(default, borrow)]
    producer_sha256: Option<Cow<'a, str>>,
    #[serde(borrow)]
    ast: &'a RawValue,
}

pub(crate) fn import(
    builder: &mut FactBuilder,
    path: &Path,
    options: &ExtractOptions,
    consumed: u64,
    pool: &rayon::ThreadPool,
    identity: &mut Sha256,
    synthetics: &Synthetics,
) -> Result<(), Error> {
    let mut input = Input::open(path, options, consumed)?;
    let mut paths: HashMap<StrId, Vec<FileId>> = HashMap::new();
    for (i, file) in builder.facts.files.iter().enumerate() {
        paths.entry(file.path).or_default().push(FileId(i as u32));
    }
    let mut seen = HashMap::new();
    let default_getters = DefaultGetters::new(&builder.facts);
    let applies = ApplyMethods::new(&builder.facts);
    identity.update(b"\0syntax/v1\0");
    loop {
        let lines = input.batch(options.batch_bytes)?;
        if lines.is_empty() {
            break;
        }
        for line in &lines {
            identity.update(line);
        }
        let decoded: Vec<_> = pool.install(|| {
            lines
                .par_iter()
                .map(|line| -> Result<_, Error> {
                    let row: SyntaxRow<'_> = serde_json::from_slice(line).map_err(json_error)?;
                    let tree = AstTree::parse(row.ast.get()).map_err(json_error)?;
                    Ok((row, tree))
                })
                .collect()
        });
        for row in decoded {
            let (row, tree) = row?;
            let ast = tree.root();
            let pooled_path = builder.intern(&row.path)?;
            let Some(files) = paths.get(&pooled_path) else {
                builder.issue(
                    IssueKind::MissingSource,
                    FileId::NONE,
                    SymbolId::NONE,
                    &format!("syntax path absent from compiler capture: {}", row.path),
                )?;
                continue;
            };
            let source_hash = ContentHash::from_hex(&row.source_sha256)?;
            let producer = row
                .producer_sha256
                .as_deref()
                .and_then(|s| ContentHash::from_hex(s).ok());
            for &file in files {
                let f = builder.facts.files[file.index()];
                if f.flags & SOURCE_VERIFIED == 0 {
                    continue;
                }
                if f.source_hash != source_hash {
                    builder.issue(
                        IssueKind::StaleSource,
                        file,
                        SymbolId::NONE,
                        "syntax source SHA256 mismatch",
                    )?;
                    continue;
                }
                if producer.is_none()
                    || options
                        .expected_syntax_producer
                        .is_some_and(|expected| producer != Some(expected))
                {
                    builder.issue(
                        IssueKind::UnsupportedSchema,
                        file,
                        SymbolId::NONE,
                        "missing or mismatched syntax producer SHA256",
                    )?;
                    continue;
                }
                if ast
                    .get("sha256")
                    .and_then(AstValue::as_str)
                    .is_some_and(|hash| ContentHash::from_hex(hash).ok() != Some(source_hash))
                {
                    builder.issue(
                        IssueKind::StaleSource,
                        file,
                        SymbolId::NONE,
                        "AST source SHA256 mismatch",
                    )?;
                    continue;
                }
                if ast
                    .get("path")
                    .and_then(AstValue::as_str)
                    .is_some_and(|p| p != row.path.as_ref())
                {
                    builder.issue(
                        IssueKind::InvalidInput,
                        file,
                        SymbolId::NONE,
                        "AST path mismatch",
                    )?;
                    continue;
                }
                let ast_hash = sha(row.ast.get().as_bytes());
                if let Some(previous) = seen.insert(file, ast_hash) {
                    if previous != ast_hash {
                        builder.issue(
                            IssueKind::ContextConflict,
                            file,
                            SymbolId::NONE,
                            "conflicting syntax documents for one source/context",
                        )?;
                    }
                    continue;
                }
                lower(builder, file, ast, synthetics, &default_getters, &applies)?;
            }
        }
    }
    Ok(())
}

fn rows<'a>(v: AstValue<'a>, name: &str) -> AstArray<'a> {
    v.rows(name)
}
fn number(v: AstValue<'_>, name: &str) -> Option<i64> {
    v.get(name).and_then(AstValue::as_i64)
}
fn flag(v: AstValue<'_>, name: &str) -> bool {
    v.get(name).and_then(AstValue::as_bool).unwrap_or(false)
}
fn field<'a>(v: AstValue<'a>, name: &str) -> &'a str {
    v.get(name).and_then(AstValue::as_str).unwrap_or("")
}
fn range(
    v: AstValue<'_>,
    start: &str,
    end: &str,
    coordinates: &SourceCoordinates,
) -> Result<Span, Error> {
    coordinates.span(
        number(v, start).ok_or(Error::Invalid("missing syntax position"))?,
        number(v, end).ok_or(Error::Invalid("missing syntax position"))?,
    )
}
fn span(v: AstValue<'_>, coordinates: &SourceCoordinates) -> Result<Span, Error> {
    range(v, "start", "end", coordinates)
}

#[derive(Clone)]
struct Parameter {
    symbol: SymbolId,
    span: Span,
    capture: bool,
    by_name: bool,
}

fn parameter_by_name(facts: &FactSnapshot, symbol: SymbolId) -> Result<bool, Error> {
    if symbol.is_none() {
        return Ok(false);
    }
    let signature = facts.symbols[symbol.index()].signature;
    if signature.is_none() {
        Ok(false)
    } else {
        Ok(crate::callable::project(facts.text(signature))?.by_name)
    }
}
struct Body {
    id: BodyId,
    symbol: SymbolId,
    span: Span,
    lexical: Span,
    name: Span,
    flags: u32,
    parameters: Vec<Parameter>,
    captures: Vec<SymbolId>,
    regions: Vec<Span>,
    returns: Vec<Span>,
    synthetic: Option<SyntheticBody>,
}
#[derive(Clone, Copy)]
struct SyntheticBody {
    function: u32,
    root: u32,
}
struct Lookup {
    occurrences: Vec<OccurrenceRecord>,
}
impl Lookup {
    fn new(facts: &FactSnapshot, file: FileId) -> Self {
        let first = facts.occurrences.partition_point(|o| o.file.0 < file.0);
        let end = facts.occurrences[first..].partition_point(|o| o.file == file) + first;
        let mut occurrences = facts.occurrences[first..end].to_vec();
        occurrences.sort_unstable_by_key(|o| (o.span.start, o.span.end, o.role, o.symbol));
        Self { occurrences }
    }
    fn exact(&self, span: Span, role: u32) -> impl Iterator<Item = SymbolId> + '_ {
        let start = self
            .occurrences
            .partition_point(|o| o.span.start < span.start);
        self.occurrences[start..]
            .iter()
            .take_while(move |o| o.span.start == span.start)
            .filter(move |o| o.span == span && o.role == role)
            .map(|o| o.symbol)
    }
    fn resolve(
        &self,
        span: Span,
        role: u32,
        facts: &FactSnapshot,
        method: bool,
    ) -> Option<SymbolId> {
        let mut matches = self.exact(span, role).filter(|s| {
            !method
                || matches!(facts.symbols[s.index()].kind, 3 | 6 | 21)
                || facts.symbol_name(*s).ends_with(").")
        });
        let first = matches.next()?;
        matches.all(|s| s == first).then_some(first)
    }
    fn constructor(&self, name: Span, end: u32, facts: &FactSnapshot) -> Option<SymbolId> {
        constructor::target(self, name, end, facts)
    }
}

/// Scala callable-object syntax is admitted only for a unique compiler-owned
/// `apply` declaration. Overload selection is never guessed from source arity.
struct ApplyMethods(HashMap<SymbolId, SymbolId>);
impl ApplyMethods {
    fn new(facts: &FactSnapshot) -> Self {
        let mut methods = HashMap::new();
        for (i, symbol) in facts.symbols.iter().enumerate() {
            if symbol.kind == 3
                && symbol.flags & SYMBOL_DEFINED != 0
                && !symbol.owner.is_none()
                && facts.text(symbol.display) == "apply"
            {
                methods
                    .entry(symbol.owner)
                    .and_modify(|id| *id = SymbolId::NONE)
                    .or_insert(SymbolId(i as u32));
            }
        }
        Self(methods)
    }
    fn target(&self, owner: SymbolId) -> Option<SymbolId> {
        self.0.get(&owner).copied().filter(|id| !id.is_none())
    }
}

fn call_target(
    lookup: &Lookup,
    name: Span,
    kind: &str,
    facts: &FactSnapshot,
    applies: &ApplyMethods,
) -> Option<SymbolId> {
    let target = lookup
        .resolve(name, 1, facts, true)
        .or_else(|| lookup.resolve(name, 1, facts, false))?;
    if facts.symbols[target.index()].kind == 10 && kind != "select" {
        applies.target(target)
    } else {
        Some(target)
    }
}

fn super_flags(
    source: &str,
    receiver: Span,
    lookup: &Lookup,
    facts: &FactSnapshot,
) -> Result<Option<u32>, &'static str> {
    let text = source
        .get(receiver.start as usize..receiver.end as usize)
        .ok_or("invalid super receiver range")?
        .trim();
    let Some(rest) = text.strip_prefix("super") else {
        if text
            .rsplit_once('.')
            .is_some_and(|(_, tail)| tail == "super" || tail.starts_with("super["))
        {
            return Err("outer-instance super receiver requires an explicit receiver binding");
        }
        return Ok(None);
    };
    if !rest.is_empty() && !rest.starts_with('[') && !rest.starts_with(char::is_whitespace) {
        return Ok(None);
    }
    let rest = rest.trim();
    if rest.is_empty() {
        return Ok(Some(OP_SUPER));
    }
    let Some(qualifier) = rest
        .strip_prefix('[')
        .and_then(|s| s.strip_suffix(']'))
        .map(str::trim)
        .filter(|s| !s.is_empty())
    else {
        return Err("unsupported Scala super receiver form");
    };
    let start = qualifier.as_ptr() as usize - source.as_ptr() as usize;
    let qualifier_span = Span {
        start: start as u32,
        end: (start + qualifier.len()) as u32,
    };
    let bound = lookup
        .resolve(qualifier_span, 1, facts, false)
        .is_some_and(|symbol| {
            matches!(facts.symbols[symbol.index()].kind, 13 | 14)
                || facts.symbol_name(symbol).ends_with('#')
        });
    if !bound {
        return Err("qualified super has no exact compiler type binding");
    }
    Ok(Some(OP_SUPER | OP_QUALIFIED_SUPER))
}

fn parameters(
    row: AstValue<'_>,
    coordinates: &SourceCoordinates,
    lookup: &Lookup,
    facts: &FactSnapshot,
) -> Result<Vec<Parameter>, Error> {
    rows(row, "parameters")
        .iter()
        .map(|p| {
            let name = range(p, "name_start", "name_end", coordinates)?;
            let symbol = lookup
                .resolve(name, 2, facts, false)
                .unwrap_or(SymbolId::NONE);
            Ok(Parameter {
                symbol,
                span: name,
                capture: false,
                by_name: parameter_by_name(facts, symbol)?,
            })
        })
        .collect()
}

/// MethodSignature owns the callable slots, including context-bound/using
/// parameters with no written token. AST rows supply source anchors only.
fn method_parameters(
    builder: &mut FactBuilder,
    file: FileId,
    symbol: SymbolId,
    written: Vec<Parameter>,
    anchor: Span,
    callable_declaration: bool,
) -> Result<Vec<Parameter>, Error> {
    let (formals, shape, missing) = call_metadata(builder, file, symbol)?;
    if !shape.known_method {
        if callable_declaration {
            builder.issue(
                IssueKind::UnknownExecution,
                file,
                symbol,
                "source callable has no authoritative compiler method signature",
            )?;
        }
        return Ok(written);
    }
    let mut ambiguous = missing;
    let mut formal_ids = Buffer::<SymbolId>::with_capacity(formals.len());
    for formal in formals.iter() {
        formal_ids.push(formal.symbol);
    }
    formal_ids.sort_unstable();
    ambiguous |= formal_ids.windows(2).any(|pair| pair[0] == pair[1]);
    let mut written_ids = Buffer::<SymbolId>::with_capacity(written.len());
    for parameter in &written {
        written_ids.push(parameter.symbol);
    }
    written_ids.sort_unstable();
    ambiguous |= written_ids.windows(2).any(|pair| pair[0] == pair[1]);
    for parameter in &written {
        ambiguous |= parameter.symbol.is_none()
            || formals
                .iter()
                .filter(|formal| formal.symbol == parameter.symbol)
                .count()
                != 1;
    }
    let mut result = Vec::with_capacity(formals.len());
    for formal in formals.iter() {
        ambiguous |= formal.symbol.is_none() || !formal.mode_known;
        result.push(Parameter {
            symbol: formal.symbol,
            span: written
                .iter()
                .find(|parameter| parameter.symbol == formal.symbol)
                .map_or(
                    Span {
                        start: anchor.start,
                        end: anchor.start,
                    },
                    |parameter| parameter.span,
                ),
            capture: false,
            by_name: formal.by_name,
        });
    }
    if ambiguous {
        builder.issue(
            IssueKind::UnknownExecution,
            file,
            symbol,
            "compiler method formals have no complete unique source/context binding",
        )?;
    }
    Ok(result)
}
fn synthetic_symbol(
    builder: &mut FactBuilder,
    file: FileId,
    owner: SymbolId,
    kind: &str,
    ordinal: usize,
    range: Span,
) -> Result<SymbolId, Error> {
    // Compiler local spellings (and owner-less scopes) repeat across documents.
    // A logical source path is stable across edits and worker publication, while
    // compact SymbolIds and byte offsets are not stable semantic identities.
    let path = builder.facts.path(file);
    let owner_name = builder.facts.symbol_name(owner);
    let name = format!(
        "@{kind}:{}:{path}:{}:{owner_name}:{ordinal}",
        path.len(),
        owner_name.len()
    );
    let id = builder.ensure_symbol(&name, file)?;
    let record = &mut builder.facts.symbols[id.index()];
    record.owner = owner;
    record.file = file;
    record.span = range;
    record.kind = 3;
    record.flags |= SYMBOL_DEFINED;
    Ok(id)
}
fn smallest_owner(bodies: &[Body], span: Span, except: Option<usize>) -> Option<usize> {
    bodies
        .iter()
        .enumerate()
        .filter(|(i, b)| {
            Some(*i) != except
                && b.synthetic.is_none()
                && b.flags & BODY_SOURCE_RECIPE == 0
                && b.span.contains(span)
        })
        .min_by_key(|(index, b)| {
            (
                b.span.end - b.span.start,
                b.flags & BODY_DEFERRED == 0,
                *index,
            )
        })
        .map(|(i, _)| i)
}

#[derive(Default)]
struct CallParameter {
    symbol: SymbolId,
    by_name: bool,
    mode_known: bool,
    function_arity: Option<usize>,
    clause: u32,
    argument: u32,
    has_default: bool,
    repeated: bool,
    prior_repeated: bool,
}

#[derive(Clone, Copy)]
struct EtaCall {
    target: SymbolId,
    virtual_dispatch: bool,
    flags: u32,
}

fn implicit_virtual(facts: &FactSnapshot, target: SymbolId) -> bool {
    let record = facts.symbols[target.index()];
    record.kind == 3
        && record.properties & (8 | 4096) == 0
        && !record.owner.is_none()
        && matches!(facts.symbols[record.owner.index()].kind, 13 | 14)
}
fn call_metadata(
    builder: &FactBuilder,
    file: FileId,
    target: SymbolId,
) -> Result<(Buffer<CallParameter>, CallShape, bool), Error> {
    let target_record = builder.facts.symbols[target.index()];
    let file = if target_record.file.is_none() {
        file
    } else {
        target_record.file
    };
    let signature = target_record.signature;
    if signature.is_none() {
        return Ok((Buffer::new(), CallShape::default(), false));
    }
    let metadata = crate::callable::project(builder.facts.text(signature))?;
    let mut result = Buffer::with_capacity(metadata.parameters.len());
    let mut missing = false;
    let mut clause = 0;
    let mut prior_repeated = false;
    for (index, name) in metadata.parameters.iter().enumerate() {
        while metadata
            .clause_starts
            .get(clause + 1)
            .is_some_and(|&start| start <= index)
        {
            clause += 1;
        }
        let symbol = builder
            .lookup_symbol(&name.0, file)
            .unwrap_or(SymbolId::NONE);
        let owned = !symbol.is_none()
            && builder.facts.symbols[symbol.index()].kind == 8
            && builder.facts.symbols[symbol.index()].owner == target
            && builder.facts.symbols[symbol.index()].context == target_record.context;
        missing |= !owned;
        let (by_name, mode_known, function_arity, repeated) = if symbol.is_none() {
            missing = true;
            (false, false, None, false)
        } else {
            let signature = builder.facts.symbols[symbol.index()].signature;
            if signature.is_none() {
                (false, false, None, false)
            } else {
                let parameter = crate::callable::project(builder.facts.text(signature))?;
                (
                    parameter.by_name,
                    true,
                    parameter.function_arity,
                    parameter.repeated,
                )
            }
        };
        result.push(CallParameter {
            symbol,
            by_name,
            mode_known,
            function_arity,
            clause: clause as u32,
            argument: (index - metadata.clause_starts.get(clause).copied().unwrap_or(0)) as u32,
            has_default: !symbol.is_none()
                && builder.facts.symbols[symbol.index()].properties & 32768 != 0,
            repeated,
            prior_repeated,
        });
        prior_repeated |= repeated;
    }
    Ok((result, metadata.shape, missing))
}
fn named_position(
    builder: &FactBuilder,
    lookup: &Lookup,
    coordinates: &SourceCoordinates,
    argument: AstValue<'_>,
    parameters: &[CallParameter],
) -> Option<usize> {
    let label = argument.get("label_range").filter(|v| !v.is_null())?;
    let label = span(label, coordinates).ok()?;
    let symbol = lookup.resolve(label, 1, &builder.facts, false)?;
    parameters.iter().position(|p| p.symbol == symbol)
}

/// Exact compiler metadata for generated default getters. Source names never
/// choose a callee: only a unique declared compiler owner/display pair is admitted.
struct DefaultGetters {
    by_owner: HashMap<(SymbolId, StrId), Vec<SymbolId>>,
    objects: HashMap<(StrId, StrId), SymbolId>,
}
impl DefaultGetters {
    fn new(facts: &FactSnapshot) -> Self {
        let mut by_owner: HashMap<_, Vec<_>> = HashMap::new();
        for (i, symbol) in facts.symbols.iter().enumerate() {
            if symbol.kind == 3
                && symbol.flags & SYMBOL_DEFINED != 0
                && facts.text(symbol.display).contains("$default$")
            {
                by_owner
                    .entry((symbol.owner, symbol.display))
                    .or_default()
                    .push(SymbolId(i as u32));
            }
        }
        let objects = facts
            .symbols
            .iter()
            .enumerate()
            .filter(|(_, symbol)| symbol.kind == 10 && symbol.flags & SYMBOL_DEFINED != 0)
            .map(|(i, symbol)| ((symbol.name, symbol.context), SymbolId(i as u32)))
            .collect();
        Self { by_owner, objects }
    }
    fn lookup(
        &self,
        builder: &mut FactBuilder,
        _file: FileId,
        method: SymbolId,
        index: usize,
    ) -> Result<Option<SymbolId>, Error> {
        let record = builder.facts.symbols[method.index()];
        let is_constructor = matches!(record.kind, 10 | 13 | 14) || record.kind == 21;
        let (owner, name) = if is_constructor {
            let class = if record.kind == 21 {
                record.owner
            } else {
                method
            };
            if class.is_none() {
                return Ok(None);
            }
            let class_name = builder.facts.symbol_name(class);
            // Local compiler IDs are scoped to their document, and carry no
            // class/companion spelling correspondence. They need an explicit
            // compiler expression recipe rather than a global name lookup.
            if selector_types::symbol::is_local(class_name) {
                return Ok(None);
            }
            let companion = if let Some(prefix) = class_name.strip_suffix('#') {
                format!("{prefix}.")
            } else {
                class_name.to_owned()
            };
            let name = builder.intern(&companion)?;
            (
                match self
                    .objects
                    .get(&(name, builder.facts.symbols[class.index()].context))
                    .copied()
                {
                    Some(id) => id,
                    None => return Ok(None),
                },
                "<init>".to_owned(),
            )
        } else {
            let name = selector_types::symbol::member_name(builder.facts.symbol_name(method))
                .unwrap_or("")
                .to_owned();
            (record.owner, name)
        };
        let display = builder.intern(&format!("{name}$default${index}"))?;
        Ok(self
            .by_owner
            .get(&(owner, display))
            .and_then(|ids| (ids.len() == 1).then_some(ids[0])))
    }
}

fn lower(
    builder: &mut FactBuilder,
    file: FileId,
    ast: AstValue<'_>,
    synthetics: &Synthetics,
    default_getters: &DefaultGetters,
    applies: &ApplyMethods,
) -> Result<(), Error> {
    let coordinates =
        SourceCoordinates::new(builder.facts.text(builder.facts.files[file.index()].source))?;
    let lookup = Lookup::new(&builder.facts, file);
    let mut selections =
        selected_apply::Index::new(ast, &coordinates, &lookup, &builder.facts, synthetics, file)?;
    let mut parameter_index = HashMap::new();
    let mut call_shapes = HashMap::new();
    for site in rows(ast, "call_sites") {
        let name = range(site, "name_start", "name_end", &coordinates)?;
        if let Some(target) = selections
            .target(span(site, &coordinates)?)
            .unwrap_or_else(|| {
                call_target(&lookup, name, field(site, "kind"), &builder.facts, applies)
            })
        {
            if let std::collections::hash_map::Entry::Vacant(entry) = parameter_index.entry(target)
            {
                let (parameters, shape, missing) = call_metadata(builder, file, target)?;
                entry.insert(parameters);
                call_shapes.insert(target, shape);
                if missing {
                    builder.issue(
                        IssueKind::UnresolvedSymbol,
                        file,
                        SymbolId::NONE,
                        "compiler callable parameter is absent from its exact provider context",
                    )?;
                }
            }
        }
    }
    for constructor in rows(ast, "constructors") {
        let name = range(constructor, "name_start", "name_end", &coordinates)?;
        let end =
            range(constructor, "type_start", "type_end", &coordinates).map_or(name.end, |s| s.end);
        if let Some(target) = lookup.constructor(name, end, &builder.facts) {
            if let std::collections::hash_map::Entry::Vacant(entry) = parameter_index.entry(target)
            {
                let (parameters, shape, _) = call_metadata(builder, file, target)?;
                entry.insert(parameters);
                call_shapes.insert(target, shape);
            }
        }
    }
    let mut bodies = Vec::new();
    let mut parse_failed = false;
    for diagnostic in rows(ast, "diagnostics") {
        if field(diagnostic, "kind") != "dialect_fallback" {
            builder.issue(
                IssueKind::UnknownExecution,
                file,
                SymbolId::NONE,
                &format!("syntax diagnostic: {}", field(diagnostic, "message")),
            )?;
            parse_failed = true;
        }
    }
    if parse_failed {
        return Ok(());
    }
    for member in rows(ast, "members") {
        if !flag(member, "executable") {
            continue;
        }
        let parsed = (|| -> Result<Body, Error> {
            let name = range(member, "name_start", "name_end", &coordinates)?;
            let symbol = lookup
                .resolve(name, 2, &builder.facts, false)
                .ok_or(Error::Invalid(
                    "executable member has no unique compiler definition",
                ))?;
            let body = range(member, "body_start", "body_end", &coordinates)?;
            let mut flags = if matches!(field(member, "kind"), "val" | "var" | "constructor") {
                BODY_INITIALIZER
            } else {
                0
            };
            if flag(member, "lazy") {
                flags = BODY_LAZY;
            }
            let mut returns = vec![body];
            for row in rows(member, "return_ranges") {
                returns.push(span(row, &coordinates)?);
            }
            Ok(Body {
                id: BodyId::NONE,
                symbol,
                span: body,
                lexical: span(member, &coordinates)?,
                name,
                flags,
                parameters: {
                    let written = parameters(member, &coordinates, &lookup, &builder.facts)?;
                    method_parameters(
                        builder,
                        file,
                        symbol,
                        written,
                        name,
                        matches!(field(member, "kind"), "def" | "constructor"),
                    )?
                },
                captures: Vec::new(),
                regions: vec![body],
                returns,
                synthetic: None,
            })
        })();
        match parsed {
            Ok(body) => bodies.push(body),
            Err(e) => builder.issue(
                IssueKind::UnknownExecution,
                file,
                SymbolId::NONE,
                &e.to_string(),
            )?,
        }
        for unknown in rows(member, "return_unknowns")
            .iter()
            .filter_map(AstValue::as_str)
        {
            builder.issue(IssueKind::UnknownExecution, file, SymbolId::NONE, unknown)?;
        }
    }
    // Owner initialization is a separate executable body. Method declarations and
    // deferred/lazy bodies are excluded from its ordinary execution regions.
    for owner in rows(ast, "owners") {
        let name = match range(owner, "name_start", "name_end", &coordinates) {
            Ok(v) => v,
            Err(_) => continue,
        };
        let Some(symbol) = lookup.resolve(name, 2, &builder.facts, false) else {
            builder.issue(
                IssueKind::UnknownExecution,
                file,
                SymbolId::NONE,
                "owner has no unique compiler definition",
            )?;
            continue;
        };
        let lexical = match span(owner, &coordinates) {
            Ok(v) => v,
            Err(_) => continue,
        };
        let mut regions = Vec::new();
        for init in rows(owner, "initializer_ranges") {
            if flag(init, "eager") {
                regions.push(span(init, &coordinates)?);
            }
        }
        for ctor in rows(ast, "constructors") {
            let s = span(ctor, &coordinates)?;
            if field(ctor, "kind") == "parent_constructor"
                && lexical.contains(s)
                && !rows(ast, "owners")
                    .iter()
                    .filter_map(|o| span(o, &coordinates).ok())
                    .any(|other| other != lexical && lexical.contains(other) && other.contains(s))
            {
                regions.push(s);
            }
        }
        bodies.push(Body {
            id: BodyId::NONE,
            symbol,
            span: lexical,
            lexical,
            name,
            flags: BODY_INITIALIZER,
            parameters: parameters(owner, &coordinates, &lookup, &builder.facts)?,
            captures: Vec::new(),
            regions,
            returns: Vec::new(),
            synthetic: None,
        });
    }
    let mut anonymous_allocations = HashMap::new();
    let mut anonymous_entries = HashMap::new();
    for ctor in rows(ast, "constructors") {
        let Some((symbol, parents)) =
            empty_anonymous_trait(builder, &lookup, &coordinates, file, ctor)
        else {
            continue;
        };
        let allocation = range(ctor, "allocation_start", "allocation_end", &coordinates)?;
        let name = range(ctor, "name_start", "name_end", &coordinates)?;
        if rows(ast, "constructors")
            .iter()
            .filter_map(|other| {
                range(other, "allocation_start", "allocation_end", &coordinates).ok()
            })
            .filter(|other| *other == allocation)
            .count()
            != 1
        {
            continue;
        }
        if bodies.iter().any(|body| body.symbol == symbol)
            || anonymous_allocations.contains_key(&allocation)
        {
            continue;
        }
        anonymous_allocations.insert(allocation, symbol);
        anonymous_entries.insert(symbol, parents);
        bodies.push(Body {
            id: BodyId::NONE,
            symbol,
            span: allocation,
            lexical: allocation,
            name: Span {
                start: name.start,
                end: name.start,
            },
            flags: BODY_INITIALIZER | BODY_SOURCE_RECIPE,
            parameters: Vec::new(),
            captures: Vec::new(),
            regions: Vec::new(),
            returns: Vec::new(),
            synthetic: None,
        });
    }
    // A by-name actual is a deferred recipe even without a written lambda.
    // Declared compiler parameter modes are authoritative. When those external
    // declarations are absent, a versioned exact framework ABI may prove only
    // the argument's deferral boundary, not complete library effects.
    let mut callable_values =
        callable_value::Index::new(builder, file, ast, &coordinates, &lookup, synthetics)?;
    callable_values.add_thunks(builder, file, &mut bodies)?;
    let mut by_name_ranges = HashSet::new();
    let mut by_name_ordinals = HashMap::<SymbolId, usize>::new();
    for site in rows(ast, "call_sites") {
        let name = range(site, "name_start", "name_end", &coordinates)?;
        let Some(target) = selections
            .target(span(site, &coordinates)?)
            .unwrap_or_else(|| {
                call_target(&lookup, name, field(site, "kind"), &builder.facts, applies)
            })
        else {
            continue;
        };
        let metadata = parameter_index
            .get(&target)
            .map(|parameters| &**parameters)
            .unwrap_or(&[]);
        let contract =
            selector_framework::scalatest_deferred_argument(builder.facts.symbol_name(target));
        for (index, argument) in rows(site, "arguments").iter().enumerate() {
            let named = argument.get("label_range").is_some_and(|v| !v.is_null());
            let parameter = if named {
                named_position(builder, &lookup, &coordinates, argument, metadata)
                    .and_then(|position| metadata.get(position))
            } else if let (Some(clause), Some(argument)) = (
                number(argument, "clause_index"),
                number(argument, "argument_index"),
            ) {
                metadata
                    .iter()
                    .find(|p| p.clause as i64 == clause && p.argument as i64 == argument)
            } else {
                metadata.get(index)
            };
            let actual = range(argument, "expression_start", "expression_end", &coordinates)
                .or_else(|_| span(argument, &coordinates))?;
            let declared = callable_values
                .mode(span(site, &coordinates)?, actual)
                .or_else(|| {
                    parameter
                        .filter(|p| p.mode_known)
                        .map(|p| p.by_name)
                        .or_else(|| {
                            (parameter.is_none()
                                && call_shapes.get(&target).is_some_and(|s| s.known_method))
                            .then_some(false)
                        })
                });
            let deferred = declared.unwrap_or_else(|| {
                contract.is_some_and(|c| {
                    if named {
                        parameter.is_some_and(|p| p.clause == c.clause && p.argument == c.argument)
                    } else {
                        number(argument, "clause_index") == Some(c.clause as i64)
                            && number(argument, "argument_index") == Some(c.argument as i64)
                    }
                })
            });
            if !deferred {
                continue;
            }
            if !by_name_ranges.insert(actual) {
                continue;
            }
            let owner = smallest_owner(&bodies, actual, None)
                .map(|i| bodies[i].symbol)
                .unwrap_or(SymbolId::NONE);
            let ordinal = by_name_ordinals.entry(owner).or_default();
            let kind = if declared.is_none() {
                "framework-byname"
            } else {
                "byname"
            };
            let symbol = synthetic_symbol(builder, file, owner, kind, *ordinal, actual)?;
            *ordinal += 1;
            bodies.push(Body {
                id: BodyId::NONE,
                symbol,
                span: actual,
                lexical: actual,
                name: actual,
                flags: BODY_DEFERRED,
                parameters: Vec::new(),
                captures: Vec::new(),
                regions: vec![actual],
                returns: vec![actual],
                synthetic: None,
            });
        }
    }
    let mut closure_ordinals = HashMap::<SymbolId, usize>::new();
    for deferred in rows(ast, "deferred_ranges") {
        let whole = span(deferred, &coordinates)?;
        let body = range(deferred, "body_start", "body_end", &coordinates)?;
        let owner = smallest_owner(&bodies, whole, None)
            .map(|i| bodies[i].symbol)
            .unwrap_or(SymbolId::NONE);
        let ordinal = closure_ordinals.entry(owner).or_default();
        let symbol = synthetic_symbol(builder, file, owner, "closure", *ordinal, whole)?;
        *ordinal += 1;
        let mut parameters = Vec::new();
        for p in rows(deferred, "parameter_ranges")
            .iter()
            .chain(rows(deferred, "placeholder_ranges"))
        {
            let p = span(p, &coordinates)?;
            parameters.push(Parameter {
                symbol: lookup
                    .resolve(p, 2, &builder.facts, false)
                    .unwrap_or(SymbolId::NONE),
                span: p,
                capture: false,
                by_name: false,
            });
        }
        for unknown in rows(deferred, "parameter_unknowns")
            .iter()
            .filter_map(AstValue::as_str)
        {
            builder.issue(IssueKind::UnknownExecution, file, symbol, unknown)?;
        }
        bodies.push(Body {
            id: BodyId::NONE,
            symbol,
            span: body,
            lexical: whole,
            name: whole,
            flags: BODY_DEFERRED,
            parameters,
            captures: Vec::new(),
            regions: vec![body],
            returns: vec![body],
            synthetic: None,
        });
    }
    // Scala can eta-expand a bare method without exporting a synthetic
    // function tree. Admit the simple case only when the enclosing compiler
    // signature proves FunctionN and every target parameter is explicit/strict.
    let mut eta_calls = HashMap::new();
    let mut eta_receivers = HashMap::new();
    let mut eta_ordinals = HashMap::<SymbolId, usize>::new();
    // Bare references are numerous. Index existing return anchors once rather
    // than scanning every executable body for each reference expression.
    let mut eta_owners = Vec::new();
    for (index, body) in bodies
        .iter()
        .enumerate()
        .filter(|(_, body)| body.synthetic.is_none())
    {
        for &returned in &body.returns {
            eta_owners.push((returned, body.span.end - body.span.start, index));
        }
    }
    eta_owners.sort_unstable_by_key(|entry| (entry.0.start, entry.0.end, entry.1, entry.2));
    eta_owners.dedup_by_key(|entry| entry.0);
    let written_applications: HashSet<_> = rows(ast, "call_sites")
        .iter()
        .filter(|site| field(*site, "kind") == "apply")
        .map(|site| range(site, "name_start", "name_end", &coordinates))
        .collect::<Result<_, _>>()?;
    let eta_candidates = rows(ast, "call_sites")
        .iter()
        .filter(|site| matches!(field(*site, "kind"), "type_apply" | "select"))
        .map(|site| -> Result<_, Error> {
            Ok((
                span(site, &coordinates)?,
                range(site, "name_start", "name_end", &coordinates)?,
                range(site, "receiver_start", "receiver_end", &coordinates).ok(),
            ))
        })
        .chain(
            rows(ast, "value_expressions")
                .iter()
                .filter(|expression| field(*expression, "kind") == "reference")
                .map(|expression| -> Result<_, Error> {
                    let whole = span(expression, &coordinates)?;
                    Ok((whole, whole, None))
                }),
        );
    for candidate in eta_candidates {
        let (whole, name, receiver) = candidate?;
        if written_applications.contains(&name) {
            continue;
        }
        let Ok(owner_index) = eta_owners.binary_search_by_key(&(whole.start, whole.end), |entry| {
            (entry.0.start, entry.0.end)
        }) else {
            continue;
        };
        let owner = bodies[eta_owners[owner_index].2].symbol;
        let signature = builder.facts.symbols[owner.index()].signature;
        if signature.is_none() {
            continue;
        }
        let expected = crate::callable::project(builder.facts.text(signature))?.function_arity;
        if expected.is_none() {
            continue;
        }
        let Some(target) = lookup.resolve(name, 1, &builder.facts, true) else {
            continue;
        };
        // A Term.Name has no source call-site row. Project its exact compiler
        // method once, without manufacturing a call or materializing a type DOM.
        if let std::collections::hash_map::Entry::Vacant(entry) = parameter_index.entry(target) {
            let (parameters, shape, _) = call_metadata(builder, file, target)?;
            entry.insert(parameters);
            call_shapes.insert(target, shape);
        }
        let parameters = &parameter_index[&target];
        if parameters.iter().any(|parameter| {
            parameter.symbol.is_none()
                || parameter.by_name
                || !parameter.mode_known
                || builder.facts.symbols[parameter.symbol.index()].properties & 32 != 0
        }) {
            continue;
        }
        if !crate::source_forms::direct_eta(
            call_shapes.get(&target).copied().unwrap_or_default(),
            parameters.len(),
            expected,
        ) {
            continue;
        }
        let flags = match receiver {
            Some(receiver) => match super_flags(
                builder.facts.text(builder.facts.files[file.index()].source),
                receiver,
                &lookup,
                &builder.facts,
            ) {
                Ok(flags) => flags.unwrap_or(0),
                Err(_) => continue,
            },
            None => 0,
        };
        let callback_parameters = parameters
            .iter()
            .map(|parameter| Parameter {
                symbol: parameter.symbol,
                span: whole,
                capture: false,
                by_name: false,
            })
            .collect();
        let ordinal = eta_ordinals.entry(owner).or_default();
        let symbol = synthetic_symbol(builder, file, owner, "eta", *ordinal, whole)?;
        *ordinal += 1;
        eta_calls.insert(
            symbol,
            EtaCall {
                target,
                virtual_dispatch: flags == 0
                    && (receiver.is_some() || implicit_virtual(&builder.facts, target)),
                flags,
            },
        );
        if let Some(receiver) = receiver {
            eta_receivers.insert(whole, receiver);
        }
        bodies.push(Body {
            id: BodyId::NONE,
            symbol,
            span: whole,
            lexical: whole,
            name: whole,
            flags: BODY_DEFERRED,
            parameters: callback_parameters,
            captures: Vec::new(),
            regions: vec![whole],
            returns: Vec::new(),
            synthetic: None,
        });
    }
    // Defaults are deferred executable recipes. Bind to a compiler getter only
    // where its exact identity is available; never guess by source spelling.
    for member in rows(ast, "members").iter().chain(rows(ast, "owners")) {
        let name = range(member, "name_start", "name_end", &coordinates)?;
        let Some(owner) = lookup.resolve(name, 2, &builder.facts, false) else {
            continue;
        };
        for (parameter_index, p) in rows(member, "parameters").iter().enumerate() {
            if let Some(default) = p.get("default").filter(|d| !d.is_null()) {
                let body = span(default, &coordinates)?;
                let symbol =
                    match default_getters.lookup(builder, file, owner, parameter_index + 1)? {
                        Some(getter) => getter,
                        None => {
                            let symbol = synthetic_symbol(
                                builder,
                                file,
                                owner,
                                "default",
                                parameter_index,
                                body,
                            )?;
                            builder.issue(
                                IssueKind::UnresolvedSymbol,
                                file,
                                symbol,
                                "default expression has no unique compiler getter identity",
                            )?;
                            symbol
                        }
                    };
                builder.facts.relations.push(RelationRecord {
                    source: owner,
                    target: symbol,
                    kind: RelationKind::Member,
                    file,
                });
                let (getter_parameters, getter_shape, _) = call_metadata(builder, file, symbol)?;
                let mut preceding = parameters(member, &coordinates, &lookup, &builder.facts)?;
                if getter_shape.known_method && preceding.len() >= getter_parameters.len() {
                    preceding.truncate(getter_parameters.len());
                } else {
                    preceding.clear();
                }
                bodies.push(Body {
                    id: BodyId::NONE,
                    symbol,
                    span: body,
                    lexical: body,
                    name: body,
                    flags: BODY_DEFERRED,
                    parameters: preceding,
                    captures: Vec::new(),
                    regions: vec![body],
                    returns: vec![body],
                    synthetic: None,
                });
            }
        }
    }
    // Compiler-inserted function trees are execution boundaries, including eta
    // expansions with no written lambda. Their child trees are lowered only
    // when the resulting callback is invoked.
    let mut primary_entries = HashMap::new();
    for owner in rows(ast, "owners") {
        let name = range(owner, "name_start", "name_end", &coordinates)?;
        let Some(class) = lookup.resolve(name, 2, &builder.facts, false) else {
            continue;
        };
        if builder.facts.symbols[class.index()].kind != 13 {
            continue;
        }
        let lexical = span(owner, &coordinates)?;
        let mut definitions = lookup.occurrences.iter().filter(|occurrence| {
            occurrence.role == 2
                && occurrence.span.start == occurrence.span.end
                && lexical.contains(occurrence.span)
                && builder.facts.symbols[occurrence.symbol.index()].kind == 21
                && builder.facts.symbols[occurrence.symbol.index()].owner == class
        });
        let Some(definition) = definitions.next() else {
            continue;
        };
        let constructor = definition.symbol;
        let anchor = definition.span;
        if definitions.any(|other| other.symbol != constructor)
            || bodies.iter().any(|body| body.symbol == constructor)
        {
            continue;
        }
        let (parameters, _, missing) = call_metadata(builder, file, constructor)?;
        if missing {
            continue;
        }
        primary_entries.insert(constructor, class);
        bodies.push(Body {
            id: BodyId::NONE,
            symbol: constructor,
            span: lexical,
            lexical,
            name: anchor,
            flags: BODY_SOURCE_RECIPE,
            parameters: parameters
                .iter()
                .map(|parameter| Parameter {
                    symbol: parameter.symbol,
                    span: anchor,
                    capture: false,
                    by_name: parameter.by_name,
                })
                .collect(),
            captures: Vec::new(),
            regions: Vec::new(),
            returns: Vec::new(),
            synthetic: None,
        });
    }
    let mut function_nodes = Vec::new();
    let mut function_scratch = crate::synthetics::FunctionScratch::default();
    for root in synthetics.file_roots(file) {
        synthetics.append_functions(root.node, &mut function_nodes, &mut function_scratch);
    }
    function_nodes.sort_unstable_by_key(|function| function.node);
    function_nodes.dedup_by_key(|function| function.node);
    let mut synthetic_ordinals = HashMap::<SymbolId, usize>::new();
    for function in function_nodes {
        let node_id = function.node;
        let node = synthetics.nodes[node_id as usize];
        let owner = bodies
            .iter()
            .filter(|b| {
                b.synthetic.is_none()
                    && b.flags & BODY_SOURCE_RECIPE == 0
                    && b.span.contains(node.span)
            })
            .min_by_key(|b| b.span.end - b.span.start)
            .map(|b| b.symbol)
            .unwrap_or(SymbolId::NONE);
        let ordinal = synthetic_ordinals.entry(owner).or_default();
        let symbol = synthetic_symbol(
            builder,
            file,
            owner,
            "synthetic-closure",
            *ordinal,
            node.span,
        )?;
        *ordinal += 1;
        let parameters = synthetics.parameters[node.parameters.range()]
            .iter()
            .map(|&symbol| Parameter {
                symbol,
                span: node.span,
                capture: false,
                by_name: false,
            })
            .collect();
        bodies.push(Body {
            id: BodyId::NONE,
            symbol,
            span: node.span,
            lexical: node.span,
            name: node.span,
            flags: BODY_DEFERRED,
            parameters,
            captures: Vec::new(),
            regions: function.regions,
            returns: Vec::new(),
            synthetic: Some(SyntheticBody {
                function: node_id,
                root: function.root,
            }),
        });
    }
    // A compiler local spelling carries no global owner descriptor. Preserve
    // its lexical AST scope so closures nested in a registered block retain
    // the block's concrete receiver instead of becoming ownerless bodies.
    for (index, body) in bodies.iter().enumerate() {
        if selector_types::symbol::is_local(builder.facts.symbol_name(body.symbol))
            && builder.facts.symbols[body.symbol.index()].owner.is_none()
        {
            if let Some(parent) = smallest_owner(&bodies, body.lexical, Some(index)) {
                let owner = bodies[parent].symbol;
                if owner != body.symbol {
                    builder.facts.symbols[body.symbol.index()].owner = owner;
                    builder.facts.relations.push(RelationRecord {
                        source: owner,
                        target: body.symbol,
                        kind: RelationKind::Member,
                        file,
                    });
                }
            }
        }
    }
    let named_labels: HashSet<_> = rows(ast, "call_sites")
        .iter()
        .flat_map(|site| rows(site, "arguments"))
        .filter_map(|arg| arg.get("label_range").filter(|v| !v.is_null()))
        .filter_map(|label| span(label, &coordinates).ok())
        .collect();
    let synthetic_captures =
        compiler_bindings::synthetic_captures(&builder.facts, file, &bodies, synthetics);
    // Capture only compiler-bound local values. Each deferred body owns its
    // capture parameter slots; no per-operation string or environment map survives.
    for i in 0..bodies.len() {
        if bodies[i].flags & BODY_DEFERRED == 0
            && !(bodies[i].flags & BODY_INITIALIZER != 0
                && selector_types::symbol::is_local(builder.facts.symbol_name(bodies[i].symbol)))
        {
            continue;
        }
        if eta_calls.contains_key(&bodies[i].symbol) {
            // An eta wrapper captures its receiver, not the source references
            // occurring inside that receiver's eagerly evaluated expression.
            continue;
        }
        let mut captures = Vec::new();
        let begin = synthetic_captures.partition_point(|&(body, _)| body < i);
        let end = synthetic_captures.partition_point(|&(body, _)| body <= i);
        captures.extend(
            synthetic_captures[begin..end]
                .iter()
                .map(|&(_, symbol)| symbol),
        );
        for occurrence in &lookup.occurrences {
            if occurrence.role != 1
                || !bodies[i].span.contains(occurrence.span)
                || (bodies[i].synthetic.is_some()
                    && !bodies[i].regions.is_empty()
                    && !bodies[i]
                        .regions
                        .iter()
                        .any(|r| r.contains(occurrence.span)))
                || named_labels.contains(&occurrence.span)
            {
                continue;
            }
            let symbol = &builder.facts.symbols[occurrence.symbol.index()];
            if matches!(symbol.kind, 8 | 19)
                && !bodies[i]
                    .parameters
                    .iter()
                    .any(|p| p.symbol == occurrence.symbol)
                && (symbol.file != file || !bodies[i].span.contains(symbol.span))
            {
                captures.push(occurrence.symbol);
            }
        }
        captures.sort_unstable();
        captures.dedup();
        let capture_span = bodies[i].span;
        for &symbol in &captures {
            if builder.facts.symbols[symbol.index()].properties & 2048 != 0 {
                builder.issue(
                    IssueKind::UnknownExecution,
                    file,
                    bodies[i].symbol,
                    "mutable lexical capture requires an explicit shared cell recipe",
                )?;
            }
            bodies[i].parameters.push(Parameter {
                symbol,
                // Capture slots are bindings in this deferred body. The captured
                // declaration can live in another source/context after binding.
                span: capture_span,
                capture: true,
                by_name: parameter_by_name(&builder.facts, symbol)?,
            });
            builder.facts.relations.push(RelationRecord {
                source: bodies[i].symbol,
                target: symbol,
                kind: RelationKind::Capture,
                file,
            });
        }
        bodies[i].captures = captures;
    }
    for body in &mut bodies {
        body.id = BodyId::checked(builder.facts.bodies.len())?;
        builder.facts.bodies.push(BodyRecord {
            symbol: body.symbol,
            file,
            span: body.span,
            name_span: body.name,
            operations: IdRange::default(),
            parameters: IdRange::default(),
            body_hash: ContentHash::default(),
            flags: body.flags,
        });
    }
    let mut pending = Vec::new();
    pending.extend(synthetics.file_roots(file).iter().map(|root| root.node));
    while let Some(id) = pending.pop() {
        let node = synthetics.nodes[id as usize];
        if node.kind == SyntheticKind::Apply {
            if let Some((target, _, _)) = synthetic_spine(synthetics, id) {
                if let std::collections::hash_map::Entry::Vacant(entry) = call_shapes.entry(target)
                {
                    let (parameters, shape, _) = call_metadata(builder, file, target)?;
                    parameter_index.entry(target).or_insert(parameters);
                    entry.insert(shape);
                }
            }
        }
        pending.extend_from_slice(synthetics.children(node));
    }
    let mut index = AstIndex::new(
        ast,
        &coordinates,
        parameter_index,
        call_shapes,
        eta_calls,
        eta_receivers,
        primary_entries,
        anonymous_allocations,
        anonymous_entries,
        &lookup,
        &builder.facts,
        synthetics,
        file,
    )?;
    index.synthetic_wrappers = synthetic_wrappers(synthetics, file, &bodies);
    selections.bind_owners(&bodies);
    selections.retain_qualifiers(ast, &coordinates, &mut index)?;
    index.selected_calls = selections;
    callable_values.bind(&mut index, &bodies, builder, file)?;
    index.callable_values = callable_values;
    index.type_prefixes.bind_owners(&bodies);
    for i in 0..bodies.len() {
        BodyLowerer::new(
            builder,
            file,
            &coordinates,
            &lookup,
            ast,
            &index,
            &bodies,
            synthetics,
            default_getters,
            applies,
            i,
        )?
        .run()?;
    }
    builder.facts.files[file.index()].flags |= SYNTAX_VERIFIED;
    Ok(())
}

struct AstIndex<'a> {
    expressions: HashMap<Span, AstValue<'a>>,
    calls: HashMap<Span, AstValue<'a>>,
    call_spans: Vec<Span>,
    constructors: HashMap<Span, AstValue<'a>>,
    parameters: HashMap<SymbolId, Buffer<CallParameter>>,
    shapes: HashMap<SymbolId, CallShape>,
    returned_calls: HashMap<Span, Span>,
    eta_receivers: HashMap<Span, Span>,
    eta_calls: HashMap<SymbolId, EtaCall>,
    primary_entries: HashMap<SymbolId, SymbolId>,
    anonymous_allocations: HashMap<Span, SymbolId>,
    anonymous_entries: HashMap<SymbolId, [SymbolId; 2]>,
    synthetic_wrappers: HashMap<Span, Option<(u32, usize)>>,
    selected_calls: selected_apply::Index,
    callable_values: callable_value::Index,
    type_prefixes: type_prefix::Index,
}
impl<'a> AstIndex<'a> {
    fn new(
        ast: AstValue<'a>,
        coords: &SourceCoordinates,
        parameters: HashMap<SymbolId, Buffer<CallParameter>>,
        shapes: HashMap<SymbolId, CallShape>,
        eta_calls: HashMap<SymbolId, EtaCall>,
        mut eta_receivers: HashMap<Span, Span>,
        primary_entries: HashMap<SymbolId, SymbolId>,
        anonymous_allocations: HashMap<Span, SymbolId>,
        anonymous_entries: HashMap<SymbolId, [SymbolId; 2]>,
        lookup: &Lookup,
        facts: &FactSnapshot,
        synthetics: &Synthetics,
        file: FileId,
    ) -> Result<Self, Error> {
        let mut expressions = HashMap::new();
        for row in rows(ast, "value_expressions") {
            expressions.insert(span(row, coords)?, row);
        }
        // Scalameta emits the selected callee, each curried Apply prefix, and
        // the complete application. The exporter already flattens all clauses
        // on the outer application. One compiler name-token anchor must produce
        // one invocation, rather than executing every structural prefix again.
        let mut complete_calls: HashMap<Span, Span> = HashMap::new();
        for row in rows(ast, "call_sites") {
            let name = range(row, "name_start", "name_end", coords)?;
            let whole = span(row, coords)?;
            complete_calls
                .entry(name)
                .and_modify(|previous| {
                    if whole.contains(*previous) {
                        *previous = whole;
                    }
                })
                .or_insert(whole);
        }
        let mut calls = HashMap::new();
        for row in rows(ast, "call_sites") {
            let key = span(row, coords)?;
            let name = range(row, "name_start", "name_end", coords)?;
            if complete_calls.get(&name) != Some(&key) {
                continue;
            }
            if field(row, "kind") == "type_apply"
                && !lookup
                    .resolve(name, 1, facts, true)
                    .and_then(|target| shapes.get(&target).copied())
                    .is_some_and(crate::source_forms::nullary_type_application)
            {
                // A bare parameterized method can eta-expand instead of
                // executing. Leave it explicit unknown until a compiler recipe
                // proves how its remaining value arguments are supplied.
                continue;
            }
            if !calls.contains_key(&key) || field(row, "kind") != "select" {
                calls.insert(key, row);
            }
        }
        let mut returned_calls = HashMap::new();
        let mut by_name: HashMap<Span, Vec<AstValue<'_>>> = HashMap::new();
        for site in rows(ast, "call_sites") {
            if field(site, "kind") == "apply" {
                by_name
                    .entry(range(site, "name_start", "name_end", coords)?)
                    .or_default()
                    .push(site);
            }
        }
        for (name, mut applications) in by_name {
            let Some(target) = lookup.resolve(name, 1, facts, true) else {
                continue;
            };
            let shape = shapes.get(&target).copied().unwrap_or_default();
            if !shape.known_method || !shape.returns_function {
                continue;
            }
            applications.sort_unstable_by_key(|row| {
                (
                    number(*row, "end"),
                    std::cmp::Reverse(number(*row, "start")),
                )
            });
            applications.dedup_by_key(|row| (number(*row, "start"), number(*row, "end")));
            if applications.len() <= shape.clauses {
                continue;
            }
            for index in shape.clauses..applications.len() {
                let outer = applications[index];
                let whole = span(outer, coords)?;
                let previous = if index == 0 {
                    range(outer, "function_start", "function_end", coords)?
                } else {
                    span(applications[index - 1], coords)?
                };
                returned_calls.insert(whole, previous);
                calls.insert(whole, outer);
                if index > 0 {
                    calls.insert(previous, applications[index - 1]);
                }
            }
        }
        // An exact compiler FunctionN.apply selection proves a returned
        // function application even when an external factory has no captured
        // MethodSignature. Keep its source prefix as a separate invocation.
        let source_calls: HashMap<_, _> = rows(ast, "call_sites")
            .iter()
            .filter_map(|row| span(row, coords).ok().map(|span| (span, row)))
            .collect();
        let applied: HashMap<_, _> = rows(ast, "call_sites")
            .iter()
            .filter(|row| field(*row, "kind") == "apply")
            .filter_map(|row| {
                range(row, "function_start", "function_end", coords)
                    .ok()
                    .map(|span| (span, row))
            })
            .collect();
        let mut pending: Vec<_> = synthetics
            .file_roots(file)
            .iter()
            .map(|root| root.node)
            .collect();
        while let Some(id) = pending.pop() {
            let node = synthetics.nodes[id as usize];
            pending.extend_from_slice(synthetics.children(node));
            if node.kind != SyntheticKind::Select || !function_apply(facts, node.target) {
                continue;
            }
            let Some(&qualifier) = synthetics.children(node).first() else {
                continue;
            };
            let prefix = synthetics.nodes[qualifier as usize];
            if prefix.kind != SyntheticKind::Original {
                continue;
            }
            if let Some(&outer) = applied.get(&prefix.span) {
                let whole = span(outer, coords)?;
                if whole == prefix.span {
                    continue;
                }
                if let Some(&written) = source_calls.get(&prefix.span) {
                    returned_calls.insert(whole, prefix.span);
                    calls.insert(whole, outer);
                    calls.insert(prefix.span, written);
                }
            }
        }
        let mut constructors = HashMap::new();
        for row in rows(ast, "constructors") {
            let key = range(row, "allocation_start", "allocation_end", coords)
                .or_else(|_| span(row, coords))?;
            constructors.insert(key, row);
        }
        for deferred in rows(ast, "deferred_ranges") {
            if field(deferred, "kind") != "eta" {
                continue;
            }
            let body = range(deferred, "body_start", "body_end", coords)?;
            if let Some(site) = calls.get(&body) {
                if let Ok(receiver) = range(*site, "receiver_start", "receiver_end", coords) {
                    eta_receivers.insert(span(deferred, coords)?, receiver);
                }
            }
        }
        let mut call_spans: Vec<_> = calls.keys().copied().collect();
        call_spans.sort_unstable_by_key(|span| (span.start, span.end));
        let type_prefixes =
            type_prefix::Index::new(ast, coords, lookup, facts, synthetics, file, &calls)?;
        Ok(Self {
            expressions,
            calls,
            call_spans,
            constructors,
            parameters,
            shapes,
            returned_calls,
            eta_receivers,
            eta_calls,
            primary_entries,
            anonymous_allocations,
            anonymous_entries,
            synthetic_wrappers: HashMap::new(),
            selected_calls: selected_apply::Index::default(),
            callable_values: callable_value::Index::default(),
            type_prefixes,
        })
    }
}

#[derive(Clone, Copy)]
struct ExpressionValues {
    written: ValueId,
    effective: ValueId,
}

struct BodyLowerer<'a> {
    builder: &'a mut FactBuilder,
    file: FileId,
    coords: &'a SourceCoordinates,
    lookup: &'a Lookup,
    ast: AstValue<'a>,
    bodies: &'a [Body],
    index: usize,
    values: HashMap<Span, ExpressionValues>,
    definitions: Vec<usize>,
    locals: HashMap<SymbolId, ValueId>,
    ast_index: &'a AstIndex<'a>,
    next_value: u32,
    visiting: HashSet<Span>,
    synthetics: &'a Synthetics,
    synthetic_values: HashMap<u32, ValueId>,
    defaults: &'a DefaultGetters,
    applies: &'a ApplyMethods,
}
impl<'a> BodyLowerer<'a> {
    fn new(
        builder: &'a mut FactBuilder,
        file: FileId,
        coords: &'a SourceCoordinates,
        lookup: &'a Lookup,
        ast: AstValue<'a>,
        ast_index: &'a AstIndex<'a>,
        bodies: &'a [Body],
        synthetics: &'a Synthetics,
        defaults: &'a DefaultGetters,
        applies: &'a ApplyMethods,
        index: usize,
    ) -> Result<Self, Error> {
        Ok(Self {
            builder,
            file,
            coords,
            lookup,
            ast,
            bodies,
            index,
            values: HashMap::new(),
            definitions: Vec::new(),
            locals: HashMap::new(),
            ast_index,
            next_value: 1,
            visiting: HashSet::new(),
            synthetics,
            synthetic_values: HashMap::new(),
            defaults,
            applies,
        })
    }
    fn value(&mut self) -> Result<ValueId, Error> {
        let value = ValueId(self.next_value);
        self.next_value = self
            .next_value
            .checked_add(1)
            .ok_or(Error::Limit("body value IDs"))?;
        Ok(value)
    }
    fn emit(
        &mut self,
        opcode: Opcode,
        target: SymbolId,
        dest: ValueId,
        a: ValueId,
        b: ValueId,
        arguments: &[ValueId],
        span: Span,
        flags: u32,
    ) -> Result<(), Error> {
        let start = u32::try_from(self.builder.facts.operands.len())
            .map_err(|_| Error::Limit("operand IDs"))?;
        self.builder.facts.operands.extend_from_slice(arguments);
        if !dest.is_none() {
            self.definitions
                .resize(self.definitions.len().max(dest.index() + 1), usize::MAX);
            self.definitions[dest.index()] = self.builder.facts.operations.len();
        }
        self.builder.facts.operations.push(OperationRecord {
            body: self.bodies[self.index].id,
            opcode,
            target,
            dest,
            a,
            b,
            arguments: IdRange {
                start,
                len: arguments.len() as u32,
            },
            span,
            flags,
        });
        Ok(())
    }
    fn unknown(&mut self, span: Span, detail: &str) -> Result<ValueId, Error> {
        let dest = self.value()?;
        self.emit(
            Opcode::Unknown,
            SymbolId::NONE,
            dest,
            ValueId::NONE,
            ValueId::NONE,
            &[],
            span,
            EDGE_UNKNOWN,
        )?;
        self.builder.issue(
            IssueKind::UnknownExecution,
            self.file,
            self.bodies[self.index].symbol,
            detail,
        )?;
        Ok(dest)
    }
    fn allowed(&self, span: Span) -> bool {
        let body = &self.bodies[self.index];
        body.regions.iter().any(|r| r.contains(span))
            && !self.bodies.iter().enumerate().any(|(i, b)| {
                i != self.index
                    && b.flags & BODY_SOURCE_RECIPE == 0
                    && body.span.contains(b.lexical)
                    && if b.synthetic.is_some() {
                        b.regions.iter().any(|region| region.contains(span))
                    } else {
                        b.lexical.contains(span)
                    }
                    && (b.synthetic.is_some() || b.lexical != body.lexical)
            })
    }
    // Expressions such as a strict block must finish their owned statements
    // before their result is supplied to an enclosing call. Deferred recipes
    // remain excluded by the same ownership predicate used for whole bodies.
    fn source_events(&self, regions: &[Span]) -> Result<Vec<(Span, u32)>, Error> {
        let mut events: Vec<(Span, u32)> = Vec::new();
        // A synthetic body usually owns only a short continuation. Slice one
        // per-file flat index instead of rescanning every call in the document
        // for every compiler-created callback.
        for region in regions {
            let spans = &self.ast_index.call_spans;
            let start = spans.partition_point(|span| span.start < region.start);
            let end = start + spans[start..].partition_point(|span| span.start <= region.end);
            for &span in &spans[start..end] {
                if region.contains(span) && self.allowed(span) {
                    events.push((span, 1));
                }
            }
        }
        for ctor in rows(self.ast, "constructors") {
            let span = range(ctor, "allocation_start", "allocation_end", self.coords)
                .or_else(|_| span(ctor, self.coords))?;
            if regions.iter().any(|region| region.contains(span)) && self.allowed(span) {
                events.push((span, 1));
            }
        }
        for (i, child) in self.bodies.iter().enumerate() {
            if i == self.index
                || child.synthetic.is_some()
                || !regions.iter().any(|region| region.contains(child.lexical))
            {
                continue;
            }
            if smallest_owner(self.bodies, child.lexical, Some(i)) != Some(self.index) {
                continue;
            }
            if child.flags & BODY_DEFERRED != 0 {
                // Closure creation is eager, its body is not. Defaults have no
                // creation effect and are invoked only by omitted-argument binding.
                if self
                    .builder
                    .facts
                    .symbol_name(child.symbol)
                    .starts_with("@closure:")
                {
                    events.push((child.lexical, 2));
                }
            } else if child.flags & BODY_INITIALIZER != 0
                && child.flags & BODY_LAZY == 0
                && !matches!(
                    self.builder.facts.symbols[child.symbol.index()].kind,
                    10 | 12 | 13 | 14 | 18 | 21
                )
            {
                events.push((child.lexical, 3));
            }
        }
        events.sort_unstable_by_key(|(s, kind)| (s.start, std::cmp::Reverse(s.end), *kind));
        events.dedup();
        Ok(events)
    }
    fn evaluate_events(&mut self, events: Vec<(Span, u32)>) -> Result<(), Error> {
        for (span, kind) in events {
            if kind == 3 {
                if let Some(child) = self
                    .bodies
                    .iter()
                    .find(|b| b.lexical == span && b.flags & BODY_INITIALIZER != 0)
                {
                    let target = child.symbol;
                    if self.locals.contains_key(&target) {
                        continue;
                    }
                    let mut captures = Buffer::<ValueId>::with_capacity(child.captures.len());
                    for &symbol in &child.captures {
                        captures.push(match self.locals.get(&symbol) {
                            Some(&value) => value,
                            None => self.unknown(
                                span,
                                "local initializer capture has no lexical binding",
                            )?,
                        });
                    }
                    let dest = self.value()?;
                    self.emit(
                        Opcode::Initialize,
                        target,
                        dest,
                        ValueId(0),
                        ValueId::NONE,
                        &captures,
                        span,
                        0,
                    )?;
                    self.locals.insert(target, dest);
                }
            } else {
                self.expression(span)?;
            }
        }
        Ok(())
    }
    fn run(mut self) -> Result<(), Error> {
        let body = &self.bodies[self.index];
        let op_start = self.builder.facts.operations.len() as u32;
        let parameter_start = self.builder.facts.operands.len() as u32;
        // Reserve parameter list contiguously before any operation argument lists.
        let mut parameter_values = Vec::with_capacity(body.parameters.len());
        for _ in &body.parameters {
            parameter_values.push(self.value()?);
        }
        self.builder
            .facts
            .operands
            .extend_from_slice(&parameter_values);
        for (p, &dest) in body.parameters.iter().zip(&parameter_values) {
            if !p.symbol.is_none() {
                self.locals.insert(p.symbol, dest);
            }
            if let Some(span) =
                crate::source_forms::anonymous_parameter_span(p.symbol, p.span, p.capture)
            {
                self.values.insert(
                    span,
                    ExpressionValues {
                        written: dest,
                        effective: ValueId::NONE,
                    },
                );
            }
            self.emit(
                Opcode::Parameter,
                p.symbol,
                dest,
                ValueId::NONE,
                ValueId::NONE,
                &[],
                p.span,
                if p.capture { PARAM_CAPTURE } else { 0 },
            )?;
        }
        if let Some(class) = self.ast_index.primary_entries.get(&body.symbol).copied() {
            self.emit(
                Opcode::Initialize,
                class,
                ValueId::NONE,
                ValueId(0),
                ValueId::NONE,
                &parameter_values,
                body.span,
                0,
            )?;
            self.emit(
                Opcode::Return,
                SymbolId::NONE,
                ValueId::NONE,
                ValueId(0),
                ValueId::NONE,
                &[],
                body.span,
                0,
            )?;
            self.seal_body(op_start, parameter_start, parameter_values.len());
            return Ok(());
        }
        if let Some(parents) = self.ast_index.anonymous_entries.get(&body.symbol).copied() {
            for parent in parents {
                self.emit(
                    Opcode::Initialize,
                    parent,
                    ValueId::NONE,
                    ValueId(0),
                    ValueId::NONE,
                    &[],
                    body.span,
                    0,
                )?;
            }
            self.seal_body(op_start, parameter_start, parameter_values.len());
            return Ok(());
        }
        if let Some(eta) = self.ast_index.eta_calls.get(&body.symbol).copied() {
            let dest = self.value()?;
            self.emit(
                if eta.virtual_dispatch {
                    Opcode::VirtualCall
                } else {
                    Opcode::Call
                },
                eta.target,
                dest,
                ValueId(0),
                ValueId::NONE,
                &parameter_values,
                body.span,
                eta.flags,
            )?;
            self.emit(
                Opcode::Return,
                SymbolId::NONE,
                ValueId::NONE,
                dest,
                ValueId::NONE,
                &[],
                body.span,
                0,
            )?;
            self.seal_body(op_start, parameter_start, parameter_values.len());
            return Ok(());
        }
        self.evaluate_events(self.source_events(&body.regions)?)?;
        for root in self.synthetics.file_roots(self.file) {
            if self.allowed(root.span)
                && !body.synthetic.is_some_and(|body| body.root == root.node)
                && (body.synthetic.is_some()
                    || smallest_owner(self.bodies, root.span, None) == Some(self.index))
                && !rows(self.ast, "type_ranges")
                    .iter()
                    .filter_map(|r| span(r, self.coords).ok())
                    .any(|s| s.contains(root.span))
            {
                if let Some((call, owner)) = self.ast_index.selected_calls.root_call(root.node) {
                    if owner == Some(self.index) {
                        self.expression(call)?;
                    } else {
                        self.unknown(
                            root.span,
                            "compiler-selected source call has conflicting execution ownership",
                        )?;
                    }
                    continue;
                }
                if self
                    .ast_index
                    .synthetic_wrappers
                    .get(&root.span)
                    .copied()
                    .flatten()
                    == Some((root.node, self.index))
                {
                    self.expression(root.span)?;
                } else {
                    self.synthetic_expression(root.node)?;
                }
            }
        }
        if let Some(synthetic) = body.synthetic {
            let function = self.synthetics.nodes[synthetic.function as usize];
            if let Some(&child) = self.synthetics.children(function).first() {
                let value = self.synthetic_expression(child)?;
                self.emit(
                    Opcode::Return,
                    SymbolId::NONE,
                    ValueId::NONE,
                    value,
                    ValueId::NONE,
                    &[],
                    body.span,
                    0,
                )?;
            }
        }
        for &returned in &body.returns {
            let value = self.expression(returned)?;
            self.emit(
                Opcode::Return,
                SymbolId::NONE,
                ValueId::NONE,
                value,
                ValueId::NONE,
                &[],
                returned,
                0,
            )?;
        }
        self.seal_body(op_start, parameter_start, parameter_values.len());
        Ok(())
    }
    fn seal_body(&mut self, start: u32, parameters: u32, parameter_len: usize) {
        let body = &self.bodies[self.index];
        // Hash the owned executable recipe. Deferred body contents belong to
        // their own summaries: merely returning a closure must not make a
        // dormant closure edit look like an eager factory execution change.
        let facts = &self.builder.facts;
        let mut hash = Sha256::new();
        hash.update(b"owned-execution/v2");
        for op in &facts.operations[start as usize..] {
            for number in [op.opcode as u32, op.dest.0, op.a.0, op.b.0, op.flags] {
                hash.update(number.to_le_bytes());
            }
            let target = facts.symbol_name(op.target).as_bytes();
            hash.update((target.len() as u64).to_le_bytes());
            hash.update(target);
            let context = if op.target.is_none() {
                &[][..]
            } else {
                facts
                    .text(facts.symbols[op.target.index()].context)
                    .as_bytes()
            };
            hash.update((context.len() as u64).to_le_bytes());
            hash.update(context);
            hash.update(op.arguments.len.to_le_bytes());
            for argument in &facts.operands[op.arguments.range()] {
                hash.update(argument.0.to_le_bytes());
            }
            if matches!(op.opcode, Opcode::Constant | Opcode::Unknown) {
                let source = facts.text(facts.files[self.file.index()].source);
                let constant = &source.as_bytes()[op.span.start as usize..op.span.end as usize];
                hash.update((constant.len() as u64).to_le_bytes());
                hash.update(constant);
            }
            hash.update([0xff]);
        }
        let execution_hash = ContentHash(hash.finalize().into());
        let record = &mut self.builder.facts.bodies[body.id.index()];
        record.body_hash = execution_hash;
        record.operations = IdRange {
            start,
            len: self.builder.facts.operations.len() as u32 - start,
        };
        record.parameters = IdRange {
            start: parameters,
            len: parameter_len as u32,
        };
    }
    fn synthetic_callee(&self, id: u32) -> Option<(SymbolId, Option<u32>)> {
        synthetic_callee(self.synthetics, id)
    }
    fn callback_mode_allowed(&self, target: SymbolId, callback: CallbackParameter) -> bool {
        let shape = self
            .ast_index
            .shapes
            .get(&target)
            .copied()
            .unwrap_or_default();
        if callback.function_arity.is_some()
            && !self.builder.facts.symbols[target.index()]
                .signature
                .is_none()
            && !shape.known_method
        {
            // A recorded value/unsupported signature is competing metadata,
            // not an absent declaration that licenses the external fallback.
            return false;
        }
        let parameters = self
            .ast_index
            .parameters
            .get(&target)
            .map(|p| &**p)
            .unwrap_or(&[]);
        if let Some(parameter) = parameters
            .iter()
            .find(|p| p.clause == callback.clause && p.argument == callback.argument)
        {
            if parameter.mode_known {
                return parameter.by_name == callback.by_name
                    && (callback.by_name
                        || match callback.function_arity {
                            Some(arity) => parameter.function_arity == Some(arity),
                            None => parameter.function_arity.is_some(),
                        });
            }
            // An absent parameter declaration supplies no competing mode; the
            // exact versioned ABI remains the same fallback used for deferral.
            return true;
        }
        !shape.known_method
    }
    fn source_callback_flags(&self, site: AstValue<'_>, target: SymbolId) -> u32 {
        let Some(callback) = callback_parameter(self.builder.facts.symbol_name(target)) else {
            return 0;
        };
        if !self.callback_mode_allowed(target, callback) {
            return 0;
        }
        let parameters = self
            .ast_index
            .parameters
            .get(&target)
            .map(|p| &**p)
            .unwrap_or(&[]);
        let mut slot = None;
        for (index, argument) in rows(site, "arguments").iter().enumerate() {
            let named = argument.get("label_range").is_some_and(|v| !v.is_null());
            let position = if named {
                named_position(self.builder, self.lookup, self.coords, argument, parameters)
            } else {
                Some(index)
            };
            let Some(position) = position else {
                return 0;
            };
            let selected = if named {
                parameters
                    .get(position)
                    .is_some_and(|p| p.clause == callback.clause && p.argument == callback.argument)
            } else {
                number(argument, "clause_index") == Some(callback.clause as i64)
                    && number(argument, "argument_index") == Some(callback.argument as i64)
            };
            if selected {
                if slot.replace(position).is_some() {
                    return 0;
                }
            }
        }
        let Some(slot) = slot else {
            return 0;
        };
        // Duplicate output bindings are not an exact argument certificate,
        // even when only one written row has the callback's clause coordinates.
        let mut bindings = 0;
        for (index, argument) in rows(site, "arguments").iter().enumerate() {
            let position = if argument.get("label_range").is_some_and(|v| !v.is_null()) {
                named_position(self.builder, self.lookup, self.coords, argument, parameters)
            } else {
                Some(index)
            };
            if position == Some(slot) {
                bindings += 1;
            }
        }
        if bindings == 1 {
            encode_callback_argument(slot).unwrap_or(0)
        } else {
            0
        }
    }
    fn synthetic_callback_flags(&self, target: SymbolId, stages: &[u32]) -> u32 {
        let Some(callback) = callback_parameter(self.builder.facts.symbol_name(target)) else {
            return 0;
        };
        if !self.callback_mode_allowed(target, callback) {
            return 0;
        }
        let mut before: usize = 0;
        for (clause, &id) in stages.iter().enumerate() {
            let count = self
                .synthetics
                .children(self.synthetics.nodes[id as usize])
                .len()
                .saturating_sub(1);
            if clause == callback.clause as usize {
                return if (callback.argument as usize) < count {
                    before
                        .checked_add(callback.argument as usize)
                        .and_then(encode_callback_argument)
                        .unwrap_or(0)
                } else {
                    0
                };
            }
            before += count;
        }
        0
    }
    fn bind_callable_value_thunk(&mut self, body: usize, span: Span) -> Result<ValueId, Error> {
        let recipe = &self.bodies[body];
        let target = recipe.symbol;
        let mut arguments = Buffer::<ValueId>::with_capacity(recipe.captures.len());
        for &captured in &recipe.captures {
            arguments.push(if let Some(&value) = self.locals.get(&captured) {
                value
            } else {
                self.unknown(
                    span,
                    "deferred conversion argument capture has no local binding",
                )?
            });
        }
        let dest = self.value()?;
        self.emit(
            Opcode::BindCallback,
            target,
            dest,
            ValueId(0),
            ValueId::NONE,
            &arguments,
            span,
            0,
        )?;
        Ok(dest)
    }
    fn synthetic_method(
        &mut self,
        target: SymbolId,
        receiver: Option<u32>,
        stages: &[u32],
        span: Span,
    ) -> Result<ValueId, Error> {
        let receiver_value = match receiver {
            Some(child) => self.synthetic_expression(child)?,
            None => ValueId(0),
        };
        let mut args = Buffer::<ValueId>::new();
        for &stage_id in stages {
            let stage = self.synthetics.nodes[stage_id as usize];
            for &child in &self.synthetics.children(stage)[1..] {
                args.push(
                    if let Some(body) = self.ast_index.callable_values.thunk(stage_id, child) {
                        self.bind_callable_value_thunk(body, stage.span)?
                    } else {
                        self.synthetic_expression(child)?
                    },
                );
            }
        }
        let first = self.synthetics.nodes[stages[0] as usize];
        let first_children = self.synthetics.children(first);
        let exact_original = self.synthetics.nodes[first_children[0] as usize].kind
            == SyntheticKind::Reference
            && first_children.len() == 2
            && self.synthetics.nodes[first_children[1] as usize].kind == SyntheticKind::Original
            && self.synthetics.nodes[first_children[1] as usize].span == first.span;
        let dest = self.value()?;
        self.emit(
            if function_apply(&self.builder.facts, target) {
                Opcode::InvokeCallback
            } else if receiver.is_some() {
                Opcode::VirtualCall
            } else {
                Opcode::Call
            },
            target,
            dest,
            receiver_value,
            ValueId::NONE,
            &args,
            span,
            self.synthetic_callback_flags(target, stages)
                | if exact_original {
                    OP_SYNTHETIC_EXACT_ORIGINAL_ARGUMENT
                } else {
                    0
                },
        )?;
        Ok(dest)
    }
    fn synthetic_expression(&mut self, id: u32) -> Result<ValueId, Error> {
        if let Some(&value) = self.synthetic_values.get(&id) {
            return Ok(value);
        }
        let node = self.synthetics.nodes[id as usize];
        let children = self.synthetics.children(node);
        let value = match node.kind {
            SyntheticKind::Original => {
                if self.bodies[self.index].synthetic.is_some() && !self.allowed(node.span) {
                    // A compiler suffix sentinel may overlap the qualifier
                    // already evaluated before this callback. Its exact owned
                    // continuation root supplies the value; uncovered fragments
                    // retain an explicit unknown rather than executing siblings.
                    let mut continuation: Option<(u32, u32)> = None;
                    let mut ambiguous = false;
                    for root in self.synthetics.file_roots(self.file).iter().filter(|root| {
                        node.span.contains(root.span)
                            && root.span.end == node.span.end
                            && self.allowed(root.span)
                            && !self.bodies[self.index]
                                .synthetic
                                .is_some_and(|body| body.root == root.node)
                    }) {
                        match continuation {
                            Some((start, _)) if start < root.span.start => (),
                            Some((start, _)) if start == root.span.start => ambiguous = true,
                            _ => {
                                continuation = Some((root.span.start, root.node));
                                ambiguous = false;
                            }
                        }
                    }
                    match continuation.filter(|_| !ambiguous) {
                        Some((_, root)) => self.synthetic_expression(root)?,
                        None => self.unknown(
                            node.span,
                            "compiler original fragment has no supported owned result binding",
                        )?,
                    }
                } else if self.visiting.contains(&node.span) {
                    self.written_expression(node.span)?
                } else {
                    self.expression(node.span)?
                }
            }
            SyntheticKind::Constant => {
                let dest = self.value()?;
                self.emit(
                    Opcode::Constant,
                    SymbolId::NONE,
                    dest,
                    ValueId::NONE,
                    ValueId::NONE,
                    &[],
                    node.span,
                    0,
                )?;
                dest
            }
            SyntheticKind::Reference | SyntheticKind::Select => {
                if node.kind == SyntheticKind::Select
                    && function_apply(&self.builder.facts, node.target)
                {
                    // Selecting FunctionN.apply does not execute it. The exact
                    // enclosing source/synthetic Apply performs that invocation.
                    match children.first() {
                        Some(&child) => self.synthetic_expression(child)?,
                        None => {
                            self.unknown(node.span, "compiler function selection lacks receiver")?
                        }
                    }
                } else if is_package(&self.builder.facts, node.target) {
                    ValueId::NONE
                } else if let Some(&value) = self.locals.get(&node.target) {
                    if self.bodies[self.index]
                        .parameters
                        .iter()
                        .any(|parameter| parameter.symbol == node.target && parameter.by_name)
                    {
                        let dest = self.value()?;
                        self.emit(
                            Opcode::InvokeCallback,
                            SymbolId::NONE,
                            dest,
                            value,
                            ValueId::NONE,
                            &[],
                            node.span,
                            0,
                        )?;
                        dest
                    } else {
                        value
                    }
                } else if !node.target.is_none()
                    && self.builder.facts.symbols[node.target.index()].kind == 8
                {
                    self.unknown(node.span, "compiler parameter has no lexical value binding")?
                } else {
                    let receiver = if let Some(&child) = children.first() {
                        self.synthetic_expression(child)?
                    } else {
                        ValueId(0)
                    };
                    let dest = self.value()?;
                    let kind = if node.target.is_none() {
                        0
                    } else {
                        self.builder.facts.symbols[node.target.index()].kind
                    };
                    let opcode = if node.target.is_none() {
                        Opcode::Unknown
                    } else if matches!(kind, 10 | 12) {
                        Opcode::Allocate
                    } else if matches!(kind, 8 | 19 | 20) {
                        Opcode::LoadField
                    } else {
                        Opcode::Call
                    };
                    self.emit(
                        opcode,
                        node.target,
                        dest,
                        receiver,
                        ValueId::NONE,
                        &[],
                        node.span,
                        0,
                    )?;
                    dest
                }
            }
            SyntheticKind::TypeApply
                if self
                    .ast_index
                    .type_prefixes
                    .binding(id, self.index)
                    .is_some() =>
            {
                match self.ast_index.type_prefixes.binding(id,self.index).flatten() {
                    Some(call)=>self.expression(call)?,
                    None=>self.unknown(node.span,"compiler type-only function prefix has no unique same-body complete application")?,
                }
            }
            SyntheticKind::TypeApply => match children.first() {
                Some(&child) => self.synthetic_expression(child)?,
                None => self.unknown(node.span, "compiler type application lacks function")?,
            },
            SyntheticKind::Apply => {
                let spine = synthetic_spine(self.synthetics, id);
                let complete_method = spine.as_ref().is_some_and(|(target, _, stages)| {
                    let shape = self
                        .ast_index
                        .shapes
                        .get(target)
                        .copied()
                        .unwrap_or_default();
                    shape.known_method && stages.len() > 1 && stages.len() == shape.clauses
                });
                if complete_method {
                    let (target, receiver, stages) = spine.unwrap();
                    self.synthetic_method(target, receiver, &stages, node.span)?
                } else if let Some((&function, rest)) = children.split_first() {
                    if let Some((target, receiver)) = self.synthetic_callee(function) {
                        self.synthetic_method(target, receiver, &[id], node.span)?
                    } else {
                        let written = self.synthetics.nodes[function as usize];
                        let value = self.synthetic_expression(function)?;
                        let mut args = Buffer::<ValueId>::with_capacity(rest.len());
                        for &child in rest {
                            args.push(self.synthetic_expression(child)?);
                        }
                        if written.kind == SyntheticKind::Original {
                            self.complete_written_call(value, written.span, &args)?;
                            value
                        } else {
                            // A compiler Apply-over-Apply can be an additional
                            // method clause. Keep it conservative until exact
                            // captured method or admitted JVM arity proves it.
                            let parameter_stage =
                                spine.as_ref().is_some_and(|(target, _, stages)| {
                                    let shape = self
                                        .ast_index
                                        .shapes
                                        .get(target)
                                        .copied()
                                        .unwrap_or_default();
                                    let name = self.builder.facts.symbol_name(*target);
                                    stages.len() > 1
                                        && !shape.known_method
                                        && name.ends_with(").")
                                        && selector_types::symbol::global_owner(name).is_some()
                                });
                            let dest = self.value()?;
                            self.emit(
                                Opcode::InvokeCallback,
                                SymbolId::NONE,
                                dest,
                                value,
                                ValueId::NONE,
                                &args,
                                node.span,
                                if parameter_stage {
                                    OP_SYNTHETIC_PARAMETER_APPLY
                                } else {
                                    0
                                },
                            )?;
                            dest
                        }
                    }
                } else {
                    self.unknown(node.span, "compiler apply tree lacks function")?
                }
            }
            SyntheticKind::Function => {
                if let Some(body) = self
                    .bodies
                    .iter()
                    .find(|body| body.synthetic.is_some_and(|body| body.function == id))
                {
                    let target = body.symbol;
                    let mut captures = Buffer::<ValueId>::with_capacity(body.captures.len());
                    for symbol in &body.captures {
                        captures.push(if let Some(value) = self.locals.get(symbol) {
                            *value
                        } else {
                            self.unknown(
                                node.span,
                                "synthetic callback capture lacks local binding",
                            )?
                        });
                    }
                    let dest = self.value()?;
                    self.emit(
                        Opcode::BindCallback,
                        target,
                        dest,
                        ValueId(0),
                        ValueId::NONE,
                        &captures,
                        node.span,
                        0,
                    )?;
                    dest
                } else {
                    self.unknown(node.span, "synthetic function body missing")?
                }
            }
            SyntheticKind::Assign => {
                if children.len() == 2 {
                    let target = self.synthetics.nodes[children[0] as usize].target;
                    let value = self.synthetic_expression(children[1])?;
                    if !target.is_none() {
                        self.emit(
                            Opcode::StoreField,
                            target,
                            ValueId::NONE,
                            ValueId(0),
                            value,
                            &[],
                            node.span,
                            0,
                        )?;
                        self.locals.insert(target, value);
                    } else {
                        self.builder.issue(
                            IssueKind::UnknownExecution,
                            self.file,
                            self.bodies[self.index].symbol,
                            "unresolved synthetic assignment target",
                        )?;
                    }
                    value
                } else {
                    self.unknown(node.span, "incomplete synthetic assignment")?
                }
            }
            SyntheticKind::Macro | SyntheticKind::MacroDirect => {
                let result_type = self.synthetics.parameters[node.parameters.range()]
                    .first()
                    .copied()
                    .unwrap_or(SymbolId::NONE);
                let metadata = if result_type.is_none() {
                    ValueId::NONE
                } else {
                    let metadata = self.value()?;
                    self.emit(
                        Opcode::Constant,
                        result_type,
                        metadata,
                        ValueId::NONE,
                        ValueId::NONE,
                        &[],
                        Span {
                            start: node.span.start,
                            end: node.span.start,
                        },
                        OP_MACRO_RESULT_TYPE,
                    )?;
                    metadata
                };
                let dest = self.value()?;
                self.emit(
                    Opcode::Unknown,
                    node.target,
                    dest,
                    metadata,
                    ValueId::NONE,
                    &[],
                    node.span,
                    EDGE_UNKNOWN
                        | OP_MACRO_EXPANSION
                        | if node.kind == SyntheticKind::MacroDirect {
                            OP_MACRO_DIRECT_TREE
                        } else {
                            0
                        },
                )?;
                self.builder.issue(
                    IssueKind::UnknownExecution,
                    self.file,
                    self.bodies[self.index].symbol,
                    "compiler macro expansion runtime effects require explicit model",
                )?;
                dest
            }
            SyntheticKind::Unknown => {
                self.unknown(node.span, "unsupported compiler synthetic tree")?
            }
        };
        self.synthetic_values.insert(id, value);
        Ok(value)
    }
    fn written_expression(&mut self, requested: Span) -> Result<ValueId, Error> {
        if let Some(value) = self
            .values
            .get(&requested)
            .map(|v| v.written)
            .filter(|v| !v.is_none())
        {
            return Ok(value);
        }
        let value = self.expression_inner(requested)?;
        self.values
            .entry(requested)
            .or_insert(ExpressionValues {
                written: ValueId::NONE,
                effective: ValueId::NONE,
            })
            .written = value;
        Ok(value)
    }
    fn expression(&mut self, requested: Span) -> Result<ValueId, Error> {
        if let Some(value) = self
            .values
            .get(&requested)
            .map(|v| v.effective)
            .filter(|v| !v.is_none())
        {
            return Ok(value);
        }
        if !self.visiting.insert(requested) {
            return self.unknown(requested, "cyclic syntax expression");
        }
        let wrapper = self
            .ast_index
            .synthetic_wrappers
            .get(&requested)
            .copied()
            .flatten()
            .filter(|(_, owner)| *owner == self.index);
        let result = match wrapper {
            Some((root, _)) => self.synthetic_expression(root)?,
            None => self.written_expression(requested)?,
        };
        self.visiting.remove(&requested);
        self.values
            .entry(requested)
            .or_insert(ExpressionValues {
                written: ValueId::NONE,
                effective: ValueId::NONE,
            })
            .effective = result;
        Ok(result)
    }
    // Compiler-inserted arguments belong to this exact written result. A
    // same-span getter can never replace the invocation being completed.
    fn complete_written_call(
        &mut self,
        value: ValueId,
        span: Span,
        args: &[ValueId],
    ) -> Result<(), Error> {
        let index = if value.is_none() {
            usize::MAX
        } else {
            self.definitions
                .get(value.index())
                .copied()
                .unwrap_or(usize::MAX)
        };
        let valid = self.builder.facts.operations.get(index).is_some_and(|op| {
            op.body == self.bodies[self.index].id
                && op.dest == value
                && op.span == span
                && (matches!(
                    op.opcode,
                    Opcode::Call | Opcode::VirtualCall | Opcode::Allocate
                ) || certified_registration_completion(op, &self.builder.facts))
        });
        if !valid {
            self.builder.issue(
                IssueKind::UnknownExecution,
                self.file,
                self.bodies[self.index].symbol,
                "compiler inserted arguments have no written invocation binding",
            )?;
            return Ok(());
        }
        // The callee may execute only after all argument providers. Reordering
        // an already-consumed result would change source effects, so reject it.
        if self.builder.facts.operations[index + 1..].iter().any(|op| {
            op.a == value
                || op.b == value
                || self.builder.facts.operands[op.arguments.range()].contains(&value)
        }) {
            self.builder.issue(
                IssueKind::UnknownExecution,
                self.file,
                self.bodies[self.index].symbol,
                "compiler inserted arguments follow an already consumed invocation",
            )?;
            return Ok(());
        }
        let old = self.builder.facts.operations[index].arguments;
        let target = self.builder.facts.operations[index].target;
        if self
            .ast_index
            .shapes
            .get(&target)
            .is_some_and(|shape| shape.known_method)
            && self
                .ast_index
                .parameters
                .get(&target)
                .is_some_and(|parameters| old.len as usize + args.len() != parameters.len())
        {
            self.builder.issue(
                IssueKind::UnknownExecution,
                self.file,
                self.bodies[self.index].symbol,
                "compiler inserted arguments do not fill the exact declared formal slots",
            )?;
        }
        let start = u32::try_from(self.builder.facts.operands.len())
            .map_err(|_| Error::Limit("operand IDs"))?;
        self.builder.facts.operands.extend_from_within(old.range());
        self.builder.facts.operands.extend_from_slice(args);
        self.builder.facts.operations[index].arguments = IdRange {
            start,
            len: old
                .len
                .checked_add(args.len() as u32)
                .ok_or(Error::Limit("call operands"))?,
        };
        self.builder.facts.operations[index..].rotate_left(1);
        for (offset, op) in self.builder.facts.operations[index..].iter().enumerate() {
            if !op.dest.is_none() {
                self.definitions[op.dest.index()] = index + offset;
            }
        }
        Ok(())
    }
    fn expression_inner(&mut self, requested: Span) -> Result<ValueId, Error> {
        if let Some(child) = self.bodies.iter().find(|b| {
            b.id != self.bodies[self.index].id
                && b.lexical == requested
                && b.flags & BODY_DEFERRED != 0
                && (self
                    .builder
                    .facts
                    .symbol_name(b.symbol)
                    .starts_with("@closure:")
                    || self
                        .builder
                        .facts
                        .symbol_name(b.symbol)
                        .starts_with("@byname:")
                    || self
                        .builder
                        .facts
                        .symbol_name(b.symbol)
                        .starts_with("@framework-byname:")
                    || self
                        .builder
                        .facts
                        .symbol_name(b.symbol)
                        .starts_with("@eta:"))
        }) {
            let target = child.symbol;
            let captures = &child.captures;
            let mut arguments = Buffer::<ValueId>::with_capacity(captures.len());
            for &captured in captures {
                let value = if let Some(value) = self.locals.get(&captured) {
                    *value
                } else {
                    self.unknown(requested, "closure capture has no local binding")?
                };
                arguments.push(value);
            }
            let dest = self.value()?;
            let receiver = if let Some(&receiver) = self.ast_index.eta_receivers.get(&requested) {
                self.expression(receiver)?
            } else {
                ValueId(0)
            };
            self.emit(
                Opcode::BindCallback,
                target,
                dest,
                receiver,
                ValueId::NONE,
                &arguments,
                requested,
                0,
            )?;
            return Ok(dest);
        }
        if let Some(&ctor) = self.ast_index.constructors.get(&requested) {
            if field(ctor, "kind") == "anonymous_allocation" {
                if let Some(&class) = self.ast_index.anonymous_allocations.get(&requested) {
                    let dest = self.value()?;
                    self.emit(
                        Opcode::Allocate,
                        class,
                        dest,
                        ValueId::NONE,
                        ValueId::NONE,
                        &[],
                        requested,
                        0,
                    )?;
                    return Ok(dest);
                }
                return self.unknown(
                    requested,
                    "anonymous construction lacks a complete compiler-owned initializer recipe",
                );
            }
            let name = range(ctor, "name_start", "name_end", self.coords)?;
            let end =
                range(ctor, "type_start", "type_end", self.coords).map_or(name.end, |s| s.end);
            let exact_constructor = self.lookup.constructor(name, end, &self.builder.facts);
            let target = exact_constructor
                .or_else(|| self.lookup.resolve(name, 1, &self.builder.facts, false));
            if exact_constructor.is_none()
                && target.is_some()
                && field(ctor, "kind") != "parent_constructor"
            {
                self.builder.issue(
                    IssueKind::UnresolvedSymbol,
                    self.file,
                    self.bodies[self.index].symbol,
                    "constructor overload has no exact compiler occurrence",
                )?;
            }
            if exact_constructor.is_some_and(|target| {
                !self
                    .ast_index
                    .shapes
                    .get(&target)
                    .is_some_and(|shape| shape.known_method)
            }) {
                self.builder.issue(
                    IssueKind::UnknownExecution,
                    self.file,
                    self.bodies[self.index].symbol,
                    "compiler-selected constructor has no authoritative source argument signature",
                )?;
            }
            let arguments = self.arguments(ctor, target, ValueId(0))?;
            let dest = self.value()?;
            match target {
                Some(target) => {
                    let kind = field(ctor, "kind");
                    let opcode = if kind == "parent_constructor" {
                        Opcode::Initialize
                    } else if kind == "constructor_delegation" {
                        Opcode::Call
                    } else {
                        Opcode::Allocate
                    };
                    self.emit(
                        opcode,
                        target,
                        dest,
                        if opcode == Opcode::Allocate {
                            ValueId::NONE
                        } else {
                            ValueId(0)
                        },
                        ValueId::NONE,
                        &arguments,
                        requested,
                        0,
                    )?;
                }
                None => {
                    self.emit(
                        Opcode::Unknown,
                        SymbolId::NONE,
                        dest,
                        ValueId::NONE,
                        ValueId::NONE,
                        &arguments,
                        requested,
                        EDGE_UNKNOWN,
                    )?;
                    self.builder.issue(
                        IssueKind::UnresolvedSymbol,
                        self.file,
                        self.bodies[self.index].symbol,
                        "constructor has no unique compiler occurrence",
                    )?;
                }
            }
            return Ok(dest);
        }
        if let Some(&function) = self.ast_index.returned_calls.get(&requested) {
            let callable = self.expression(function)?;
            let mut arguments = Buffer::<ValueId>::new();
            if let Some(&site) = self.ast_index.calls.get(&requested) {
                for argument in rows(site, "arguments") {
                    let actual = range(argument, "expression_start", "expression_end", self.coords)
                        .or_else(|_| span(argument, self.coords))?;
                    if !function.contains(actual) {
                        arguments.push(self.expression(actual)?);
                    }
                }
            }
            let dest = self.value()?;
            self.emit(
                Opcode::InvokeCallback,
                SymbolId::NONE,
                dest,
                callable,
                ValueId::NONE,
                &arguments,
                requested,
                0,
            )?;
            return Ok(dest);
        }
        if let Some(&site) = self.ast_index.calls.get(&requested) {
            let name = range(site, "name_start", "name_end", self.coords)?;
            let written = self.lookup.resolve(name, 1, &self.builder.facts, false);
            let selected_call = self.ast_index.selected_calls.binding(requested, self.index);
            let selection = selected_call.map(|binding| binding.selection);
            let target = selection
                .map(|selection| selection.map(|selection| selection.target))
                .unwrap_or_else(|| {
                    call_target(
                        self.lookup,
                        name,
                        field(site, "kind"),
                        &self.builder.facts,
                        self.applies,
                    )
                });
            if let Some(selection) = selection {
                if selection.is_none() {
                    self.builder.issue(
                        IssueKind::UnknownExecution,
                        self.file,
                        self.bodies[self.index].symbol,
                        "compiler-selected source method is ambiguous or has conflicting ownership",
                    )?;
                } else if !target
                    .and_then(|target| self.ast_index.shapes.get(&target))
                    .is_some_and(|shape| shape.known_method)
                {
                    self.builder.issue(
                        IssueKind::UnknownExecution,
                        self.file,
                        self.bodies[self.index].symbol,
                        "compiler-selected method has no authoritative source argument signature",
                    )?;
                }
            }
            if target.is_some_and(|target| is_package(&self.builder.facts, target)) {
                // A qualified type/name can have Term.Select prefix rows in
                // Scalameta. Compiler package descriptors are namespaces, not
                // object receiver evaluation or executable field accesses.
                return Ok(ValueId::NONE);
            }
            let mut dispatch_flags = 0;
            let receiver = if let Some(binding) = selected_call {
                // Receiver authority comes from the actual written expression,
                // including when the selected method is rejected. Evaluate it
                // before every argument provider and retain its effects once.
                if self.allowed(binding.qualifier) {
                    self.expression(binding.qualifier)?
                } else {
                    self.unknown(
                        binding.qualifier,
                        "compiler-selected qualifier belongs to another executable body",
                    )?
                }
            } else {
                if written.is_some_and(|id| self.builder.facts.symbols[id.index()].kind == 10) {
                    if field(site, "kind") == "select" {
                        return self.reference(name);
                    }
                    self.reference(name)?
                } else {
                    match range(site, "receiver_start", "receiver_end", self.coords) {
                        Ok(receiver) if receiver != requested => {
                            let source = self
                                .builder
                                .facts
                                .text(self.builder.facts.files[self.file.index()].source);
                            match super_flags(source, receiver, self.lookup, &self.builder.facts) {
                                Ok(Some(flags)) => {
                                    dispatch_flags = flags;
                                    ValueId(0)
                                }
                                Ok(None) => self.expression(receiver)?,
                                Err(detail) => self.unknown(receiver, detail)?,
                            }
                        }
                        _ => ValueId(0),
                    }
                }
            };
            if field(site, "kind") == "select"
                && target.is_some_and(|target| {
                    self.ast_index
                        .parameters
                        .get(&target)
                        .is_some_and(|parameters| !parameters.is_empty())
                })
            {
                return self.unknown(
                    requested,
                    "parameterized method selection has no complete compiler eta or argument recipe",
                );
            }
            let arguments = self.arguments(site, target, receiver)?;
            let dest = self.value()?;
            if let Some(target) = target {
                let record = self.builder.facts.symbols[target.index()];
                if self
                    .ast_index
                    .shapes
                    .get(&target)
                    .is_some_and(|shape| shape.value_function)
                    && field(site, "kind") != "select"
                {
                    let callable = if let Some(&value) = self.locals.get(&target) {
                        value
                    } else {
                        let value = self.value()?;
                        self.emit(
                            Opcode::LoadField,
                            target,
                            value,
                            receiver,
                            ValueId::NONE,
                            &[],
                            name,
                            0,
                        )?;
                        value
                    };
                    self.emit(
                        Opcode::InvokeCallback,
                        SymbolId::NONE,
                        dest,
                        callable,
                        ValueId::NONE,
                        &arguments,
                        requested,
                        0,
                    )?;
                    return Ok(dest);
                }
                let framework = selector_framework::scalatest_callback_argument(
                    self.builder.facts.symbol_name(target),
                );
                let opcode = if framework
                    .is_some_and(|c| c.kind == selector_framework::ScalaTestCall::Registration)
                {
                    // Registration is an explicit compiler-bound framework
                    // effect. A missing implicit wrapper's receiver recipe
                    // cannot turn the registered body into dormant inventory.
                    // The external method's other effects remain unresolved.
                    Opcode::RegisterTest
                } else if framework
                    .is_some_and(|c| c.kind == selector_framework::ScalaTestCall::Scope)
                {
                    Opcode::Call
                } else if matches!(record.kind, 8 | 19 | 20) {
                    Opcode::LoadField
                } else if dispatch_flags == 0
                    && (selection.is_some_and(|selection| selection.is_some())
                        || number(site, "receiver_start").is_some()
                        || implicit_virtual(&self.builder.facts, target))
                {
                    Opcode::VirtualCall
                } else {
                    Opcode::Call
                };
                self.emit(
                    opcode,
                    target,
                    dest,
                    receiver,
                    ValueId::NONE,
                    &arguments,
                    requested,
                    dispatch_flags | self.source_callback_flags(site, target),
                )?;
            } else {
                self.emit(
                    Opcode::Unknown,
                    SymbolId::NONE,
                    dest,
                    receiver,
                    ValueId::NONE,
                    &arguments,
                    requested,
                    EDGE_UNKNOWN,
                )?;
                self.builder.issue(
                    IssueKind::UnresolvedSymbol,
                    self.file,
                    self.bodies[self.index].symbol,
                    "call has no unique compiler occurrence",
                )?;
            }
            return Ok(dest);
        }
        let expression = self.ast_index.expressions.get(&requested).copied();
        if let Some(expression) = expression {
            match field(expression, "kind") {
                "interpolation" => {
                    for r in rows(expression, "effect_ranges") {
                        let pair = r
                            .as_array()
                            .ok_or(Error::Invalid("interpolation argument range"))?;
                        let start = pair
                            .first()
                            .and_then(AstValue::as_i64)
                            .ok_or(Error::Invalid("interpolation argument start"))?;
                        let end = pair
                            .get(1)
                            .and_then(AstValue::as_i64)
                            .ok_or(Error::Invalid("interpolation argument end"))?;
                        let argument = self.coords.span(start, end)?;
                        if argument != requested {
                            self.expression(argument)?;
                        }
                    }
                    return self.unknown(
                        requested,
                        "interpolator execution requires a compiler-bound receiver recipe",
                    );
                }
                "literal" => {
                    let dest = self.value()?;
                    self.emit(
                        Opcode::Constant,
                        SymbolId::NONE,
                        dest,
                        ValueId::NONE,
                        ValueId::NONE,
                        &[],
                        requested,
                        0,
                    )?;
                    return Ok(dest);
                }
                "reference" => return self.reference(requested),
                "block" | "if" | "match" | "return" | "ascribe" | "try" => {
                    if field(expression, "kind") == "block" {
                        self.evaluate_events(self.source_events(&[requested])?)?;
                    }
                    let mut values = Buffer::<ValueId>::new();
                    for r in rows(expression, "result_ranges") {
                        let s = if let Some(pair) = r.as_array() {
                            self.coords.span(
                                pair.first()
                                    .and_then(AstValue::as_i64)
                                    .ok_or(Error::Invalid("result start"))?,
                                pair.get(1)
                                    .and_then(AstValue::as_i64)
                                    .ok_or(Error::Invalid("result end"))?,
                            )?
                        } else {
                            span(r, self.coords)?
                        };
                        if s != requested {
                            values.push(self.expression(s)?);
                        }
                    }
                    if values.len() == 1 {
                        return Ok(values[0]);
                    }
                    if !values.is_empty() {
                        let dest = self.value()?;
                        self.emit(
                            Opcode::Join,
                            SymbolId::NONE,
                            dest,
                            ValueId::NONE,
                            ValueId::NONE,
                            &values,
                            requested,
                            0,
                        )?;
                        return Ok(dest);
                    }
                }
                _ => (),
            }
            for unknown in rows(expression, "unknown")
                .iter()
                .filter_map(AstValue::as_str)
            {
                self.builder.issue(
                    IssueKind::UnknownExecution,
                    self.file,
                    self.bodies[self.index].symbol,
                    unknown,
                )?;
            }
        }
        if self
            .lookup
            .resolve(requested, 1, &self.builder.facts, false)
            .is_some()
        {
            return self.reference(requested);
        }
        self.unknown(
            requested,
            "expression value has no supported compiler/syntax binding",
        )
    }
    fn reference(&mut self, requested: Span) -> Result<ValueId, Error> {
        let source = self
            .builder
            .facts
            .text(self.builder.facts.files[self.file.index()].source);
        if source
            .get(requested.start as usize..requested.end as usize)
            .is_some_and(|s| matches!(s, "this" | "super"))
        {
            return Ok(ValueId(0));
        }
        let Some(target) = self
            .lookup
            .resolve(requested, 1, &self.builder.facts, false)
        else {
            return self.unknown(requested, "reference has no unique compiler occurrence");
        };
        if is_package(&self.builder.facts, target) {
            return Ok(ValueId::NONE);
        }
        if let Some(value) = self.locals.get(&target) {
            let value = *value;
            if self.bodies[self.index]
                .parameters
                .iter()
                .any(|parameter| parameter.symbol == target && parameter.by_name)
            {
                let dest = self.value()?;
                self.emit(
                    Opcode::InvokeCallback,
                    SymbolId::NONE,
                    dest,
                    value,
                    ValueId::NONE,
                    &[],
                    requested,
                    0,
                )?;
                return Ok(dest);
            }
            return Ok(value);
        }
        let kind = self.builder.facts.symbols[target.index()].kind;
        if matches!(kind, 3 | 6 | 21) {
            let signature = self.builder.facts.symbols[target.index()].signature;
            if !signature.is_none()
                && !crate::callable::project(self.builder.facts.text(signature))?
                    .parameters
                    .is_empty()
            {
                return self.unknown(
                    requested,
                    "parameterized method reference has no complete compiler eta or argument recipe",
                );
            }
        }
        let dest = self.value()?;
        let opcode = if matches!(kind, 3 | 6 | 21) {
            if implicit_virtual(&self.builder.facts, target) {
                Opcode::VirtualCall
            } else {
                Opcode::Call
            }
        } else if matches!(kind, 10 | 12) {
            Opcode::Allocate
        } else {
            Opcode::LoadField
        };
        self.emit(
            opcode,
            target,
            dest,
            ValueId(0),
            ValueId::NONE,
            &[],
            requested,
            0,
        )?;
        Ok(dest)
    }
    fn arguments(
        &mut self,
        site: AstValue<'_>,
        target: Option<SymbolId>,
        receiver: ValueId,
    ) -> Result<Buffer<ValueId>, Error> {
        let metadata = target
            .and_then(|target| self.ast_index.parameters.get(&target))
            .map(|parameters| &**parameters)
            .unwrap_or(&[]);
        if repeated::admitted(site, metadata, &self.builder.facts) {
            return self.packed_arguments(site, target, receiver, metadata);
        }
        if metadata.iter().any(|formal| formal.repeated) {
            self.builder.issue(IssueKind::UnknownExecution,self.file,self.bodies[self.index].symbol,
                "repeated actual evaluations are retained without an exact argument-container recipe")?;
        }
        let mut arguments = Buffer::<ValueId>::with_capacity(rows(site, "arguments").len());
        for (index, argument) in rows(site, "arguments").iter().enumerate() {
            let coordinates = number(argument, "clause_index")
                .zip(number(argument, "argument_index"))
                .and_then(|(clause, argument)| {
                    Some((u32::try_from(clause).ok()?, u32::try_from(argument).ok()?))
                });
            if let Some((clause, _)) = coordinates {
                let completed = metadata.partition_point(|parameter| parameter.clause < clause);
                // Defaults in earlier clauses execute before actual providers
                // from this later clause, preserving curried evaluation order.
                self.fill_defaults(site, target, receiver, metadata, &mut arguments, completed)?;
            }
            let span = range(argument, "expression_start", "expression_end", self.coords)
                .or_else(|_| span(argument, self.coords))?;
            let value = self.expression(span)?;
            let named = argument.get("label_range").is_some_and(|v| !v.is_null());
            let position = if named {
                named_position(self.builder, self.lookup, self.coords, argument, metadata)
                    .map(|formal| self.formal_slot(site, metadata, formal))
            } else if let Some((clause, argument)) = coordinates.filter(|_| !metadata.is_empty()) {
                match metadata.iter().position(|formal| {
                    formal.clause == clause
                        && (formal.argument == argument
                            || (formal.repeated && formal.argument < argument))
                }) {
                    Some(formal) => Some(
                        self.formal_slot(site, metadata, formal)
                            + (argument - metadata[formal].argument) as usize,
                    ),
                    None => {
                        self.builder.issue(
                            IssueKind::UnknownExecution,
                            self.file,
                            self.bodies[self.index].symbol,
                            "actual clause coordinates have no exact compiler formal binding",
                        )?;
                        // Preserve the evaluated provider in an explicit spare
                        // slot; the guard forbids interpreting this as a proof
                        // of a valid flattened method application.
                        Some(arguments.len().max(metadata.len()))
                    }
                }
            } else {
                Some(index)
            };
            let Some(position) = position else {
                self.builder.issue(
                    IssueKind::UnknownExecution,
                    self.file,
                    self.bodies[self.index].symbol,
                    "named argument has no exact compiler parameter binding",
                )?;
                arguments.push(value);
                continue;
            };
            if arguments.len() <= position {
                arguments.resize(position + 1, ValueId::NONE);
            }
            if !arguments[position].is_none() {
                self.builder.issue(
                    IssueKind::InvalidInput,
                    self.file,
                    self.bodies[self.index].symbol,
                    "duplicate actual binding for compiler parameter",
                )?;
                arguments.push(value);
                continue;
            }
            arguments[position] = value;
        }
        // Written arguments are evaluated first in source order. Missing formal
        // slots are filled only by an exact compiler-owned default getter.
        let formal_end = self
            .pending_implicit_clause(site, target, metadata)
            .unwrap_or(metadata.len());
        self.fill_defaults(site, target, receiver, metadata, &mut arguments, formal_end)?;
        Ok(arguments)
    }
    fn fill_defaults(
        &mut self,
        site: AstValue<'_>,
        target: Option<SymbolId>,
        receiver: ValueId,
        metadata: &[CallParameter],
        arguments: &mut Buffer<ValueId>,
        formal_end: usize,
    ) -> Result<(), Error> {
        for index in 0..formal_end {
            let position = self.formal_slot(site, metadata, index);
            if arguments
                .get(position)
                .is_some_and(|value| !value.is_none())
            {
                continue;
            }
            if arguments.len() <= position {
                arguments.resize(position + 1, ValueId::NONE);
            }
            if !metadata[index].mode_known {
                arguments[position] = self.unknown(
                    span(site, self.coords)?,
                    "omitted argument has no compiler parameter evaluation mode",
                )?;
                continue;
            }
            if !metadata[index].has_default {
                arguments[position] = self.unknown(
                    span(site, self.coords)?,
                    "omitted argument has no compiler default parameter proof",
                )?;
                continue;
            }
            let getter = match target {
                Some(target) => self
                    .defaults
                    .lookup(self.builder, self.file, target, index + 1)?,
                None => None,
            };
            let Some(getter) = getter else {
                arguments[position] = self.unknown(
                    span(site, self.coords)?,
                    "omitted argument has no exact compiler default getter",
                )?;
                continue;
            };
            let (getter_parameters, _, missing) = call_metadata(self.builder, self.file, getter)?;
            if missing
                || getter_parameters.len() > index
                || (getter_parameters.len() != 0
                    && metadata[..index].iter().any(|formal| formal.repeated))
            {
                arguments[position] = self.unknown(
                    span(site, self.coords)?,
                    "default getter requires unavailable preceding compiler arguments",
                )?;
                continue;
            }
            let owner = self.builder.facts.symbols[getter.index()].owner;
            let getter_receiver = if !owner.is_none()
                && self.builder.facts.symbols[owner.index()].kind == 10
                && target
                    .is_none_or(|target| self.builder.facts.symbols[target.index()].owner != owner)
            {
                let value = self.value()?;
                self.emit(
                    Opcode::Allocate,
                    owner,
                    value,
                    ValueId::NONE,
                    ValueId::NONE,
                    &[],
                    span(site, self.coords)?,
                    0,
                )?;
                value
            } else {
                receiver
            };
            let value = self.value()?;
            self.emit(
                if metadata[index].by_name {
                    Opcode::BindCallback
                } else {
                    Opcode::DefaultArgument
                },
                getter,
                value,
                getter_receiver,
                ValueId::NONE,
                &arguments[..getter_parameters.len()],
                span(site, self.coords)?,
                0,
            )?;
            arguments[position] = value;
        }
        Ok(())
    }

    /// Existing operation ABI retains each repeated actual. Shift later-clause
    /// slots by that compiler-proven expansion; never confuse the repeated
    /// tail with a default/implicit hole in a different declared clause.
    fn formal_slot(&self, site: AstValue<'_>, metadata: &[CallParameter], formal: usize) -> usize {
        if !metadata[formal].prior_repeated
            || repeated::admitted(site, metadata, &self.builder.facts)
        {
            return formal;
        }
        let mut shift = 0;
        for parameter in metadata[..formal]
            .iter()
            .filter(|parameter| parameter.repeated && parameter.clause < metadata[formal].clause)
        {
            let actuals = rows(site, "arguments")
                .iter()
                .filter(|argument| {
                    number(*argument, "clause_index") == Some(parameter.clause as i64)
                })
                .count();
            let declared = metadata
                .iter()
                .filter(|formal| formal.clause == parameter.clause)
                .count();
            shift += actuals.saturating_sub(declared);
        }
        formal + shift
    }

    /// Only a unique compiler Apply(OriginalTree(exact written call), actuals)
    /// can defer an implicit clause. Defaults still fill the written clauses;
    /// no Unknown placeholder is emitted for a slot that this exact tree binds.
    fn pending_implicit_clause(
        &self,
        site: AstValue<'_>,
        target: Option<SymbolId>,
        parameters: &[CallParameter],
    ) -> Option<usize> {
        let target = target?;
        let whole = span(site, self.coords).ok()?;
        let (root, owner) = self
            .ast_index
            .synthetic_wrappers
            .get(&whole)
            .copied()
            .flatten()?;
        if owner != self.index {
            return None;
        }
        let root = self.synthetics.nodes[root as usize];
        let children = self.synthetics.children(root);
        let original = self.synthetics.nodes[*children.first()? as usize];
        if root.kind != SyntheticKind::Apply
            || original.kind != SyntheticKind::Original
            || original.span != whole
        {
            return None;
        }
        let shape = self.ast_index.shapes.get(&target)?;
        let mut clauses = usize::from(field(site, "kind") == "apply");
        for argument in rows(site, "arguments") {
            clauses = clauses.max(
                usize::try_from(number(argument, "clause_index")?)
                    .ok()?
                    .checked_add(1)?,
            );
        }
        if !shape.known_method || shape.clauses != clauses + 1 {
            return None;
        }
        let end = parameters.partition_point(|parameter| (parameter.clause as usize) < clauses);
        let implicit = &parameters[end..];
        if implicit.is_empty()
            || implicit.len() != children.len() - 1
            || rows(site, "arguments").len() > end
            || implicit.iter().any(|parameter| {
                parameter.symbol.is_none()
                    || parameter.clause as usize != clauses
                    || self.builder.facts.symbols[parameter.symbol.index()].properties & 32 == 0
                    || !parameter.mode_known
                    || self.builder.facts.symbols[parameter.symbol.index()].owner != target
            })
        {
            return None;
        }
        Some(end)
    }
}

#[cfg(test)]
mod synthetic_application_tests {
    use super::*;
    use md5::{Digest as _, Md5};
    use serde_json::{Value, json};

    fn import(
        source: &str,
        symbols: Value,
        occurrences: Value,
        synthetics: Value,
        calls: Value,
        expressions: Value,
    ) -> FactSnapshot {
        import_tree(
            source,
            symbols,
            occurrences,
            synthetics,
            json!({
            "members":[{"executable":true,"kind":"def","start":0,"end":source.len(),"name_start":4,"name_end":5,"body_start":8,"body_end":source.len()}],
            "call_sites":calls,"value_expressions":expressions}),
        )
    }
    fn import_tree(
        source: &str,
        symbols: Value,
        occurrences: Value,
        synthetics: Value,
        ast: Value,
    ) -> FactSnapshot {
        let input = json!({"path":"A.scala","revision":"r1","source_text":source,
            "source_sha256":sha(source.as_bytes()).to_string(),"source_contexts":["a"],"input_target_contexts":["a"],
            "document":{"schema":4,"language":1,"uri":"A.scala","md5":Md5::digest(source.as_bytes()).iter().map(|byte| format!("{byte:02x}")).collect::<String>(),
                "symbols":symbols,"occurrences":occurrences,"synthetics":synthetics}});
        let syntax = json!({"path":"A.scala","source_sha256":sha(source.as_bytes()).to_string(),
            "producer_sha256":ContentHash([1;32]).to_string(),"ast":ast});
        let directory = tempfile::tempdir().unwrap();
        let documents = directory.path().join("documents.jsonl");
        let syntax_path = directory.path().join("syntax.jsonl");
        std::fs::write(&documents, format!("{input}\n")).unwrap();
        std::fs::write(&syntax_path, format!("{syntax}\n")).unwrap();
        crate::import_capture(&documents, Some(&syntax_path), &ExtractOptions::default()).unwrap()
    }
    fn original(start: u32, end: u32) -> Value {
        json!({"original_tree":{"range":{"start_line":0,"start_character":start,"end_line":0,"end_character":end}}})
    }
    fn root(start: u32, end: u32, tree: Value) -> Value {
        json!({"range":{"start_line":0,"start_character":start,"end_line":0,"end_character":end},"tree":tree})
    }
    fn method(facts: &FactSnapshot, name: &str) -> usize {
        facts
            .operations
            .iter()
            .position(|op| {
                facts.symbol_name(op.target) == name
                    && matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
            })
            .unwrap()
    }

    #[test]
    fn repeated_pack_finishes_before_next_curried_clause_provider() {
        let source = "def f = use(provider(), provider())(later())";
        let provider_ranges: Vec<_> = source
            .match_indices("provider()")
            .map(|(start, text)| (start, start + text.len()))
            .collect();
        let later_start = source.find("later()").unwrap();
        let use_start = source.find("use(").unwrap();
        let mut arguments: Vec<Value> = provider_ranges.iter().enumerate().map(|(index, &(start,end))| json!({"start":start,"end":end,"expression_start":start,"expression_end":end,"clause_index":0,"argument_index":index,"repeated_spread":false})).collect();
        arguments.push(json!({"start":later_start,"end":later_start+7,"expression_start":later_start,"expression_end":later_start+7,"clause_index":1,"argument_index":0,"repeated_spread":false}));
        let mut calls = vec![
            json!({"start":use_start,"end":source.len(),"name_start":use_start,"name_end":use_start+3,"kind":"apply","arguments":arguments}),
        ];
        let mut occurrences = vec![
            json!({"symbol":"p/f().","role":2,"range":{"start_line":0,"start_character":4,"end_line":0,"end_character":5}}),
            json!({"symbol":"p/use().","role":1,"range":{"start_line":0,"start_character":use_start,"end_line":0,"end_character":use_start+3}}),
        ];
        for &(start, end) in &provider_ranges {
            calls.push(json!({"start":start,"end":end,"name_start":start,"name_end":start+8,"kind":"apply","arguments":[]}));
            occurrences.push(json!({"symbol":"p/provider().","role":1,"range":{"start_line":0,"start_character":start,"end_line":0,"end_character":start+8}}));
        }
        calls.push(json!({"start":later_start,"end":later_start+7,"name_start":later_start,"name_end":later_start+5,"kind":"apply","arguments":[]}));
        occurrences.push(json!({"symbol":"p/later().","role":1,"range":{"start_line":0,"start_character":later_start,"end_line":0,"end_character":later_start+5}}));
        let facts = import(
            source,
            json!([
                {"symbol":"p/f().","kind":3,"signature":{"method_signature":{"parameter_lists":[]}}},
                {"symbol":"p/use().","kind":3,"signature":{"method_signature":{"parameter_lists":[{"symlinks":["p/use().(xs)"]},{"symlinks":["p/use().(next)"]}]}}},
                {"symbol":"p/use().(xs)","kind":8,"signature":{"value_signature":{"tpe":{"repeated_type":{"tpe":{"type_ref":{"symbol":"scala/Function0#"}}}}}}},
                {"symbol":"p/use().(next)","kind":8,"signature":{"value_signature":{"tpe":{"type_ref":{"symbol":"scala/Int#"}}}}},
                {"symbol":"p/provider().","kind":3,"signature":{"method_signature":{"parameter_lists":[]}}},
                {"symbol":"p/later().","kind":3,"signature":{"method_signature":{"parameter_lists":[]}}}
            ]),
            Value::Array(occurrences),
            json!([]),
            Value::Array(calls),
            json!([]),
        );
        let use_index = method(&facts, "p/use().");
        let later_index = method(&facts, "p/later().");
        let pack_index = facts
            .operations
            .iter()
            .position(|op| op.opcode == Opcode::PackSequence)
            .unwrap();
        let providers: Vec<_> = facts
            .operations
            .iter()
            .enumerate()
            .filter(|(_, op)| {
                !op.target.is_none() && facts.symbol_name(op.target) == "p/provider()."
            })
            .collect();
        assert_eq!(providers.len(), 2);
        assert!(providers[1].0 < pack_index && pack_index < later_index && later_index < use_index);
        let call = facts.operations[use_index];
        assert_eq!(call.arguments.len, 2);
        assert_eq!(
            facts.operands[call.arguments.start as usize],
            facts.operations[pack_index].dest
        );
        assert_eq!(
            facts.operands[call.arguments.start as usize + 1],
            facts.operations[later_index].dest
        );
        assert!(facts.issues.iter().any(|issue| facts.text(issue.detail)
            == "repeated argument container backend effects remain unverified"));
    }

    #[test]
    fn anonymous_trait_allocation_requires_complete_unique_compiler_and_empty_source_proof() {
        for control in 0..9 {
            let source = if control == 1 {
                "def f = new T { g() }"
            } else {
                "def f = new T {}"
            };
            let constructor = if control == 7 {
                "p/Wrong#`<init>`()."
            } else {
                "java/lang/Object#`<init>`()."
            };
            let signature = json!({"class_signature":{"type_parameters":{},"parents":[
                {"type_ref":{"symbol":"scala/AnyRef#"}},
                {"type_ref":{"symbol":if control == 4 {"scala/AnyRef#"} else {"p/T#"}}}],
                "declarations":if control == 3 {json!({"symlinks":["local2"]})} else {json!({})}}});
            let mut local = json!({"symbol":"local0","kind":13,"signature":signature});
            if control == 5 {
                local.as_object_mut().unwrap().remove("signature");
            }
            let mut symbols = vec![json!({"symbol":"p/A#f().","kind":3}), local];
            let mut occurrences = vec![
                json!({"symbol":"p/A#f().","role":2,"range":{"start_character":4,"end_character":5}}),
                json!({"symbol":"local0","role":2,"range":{"start_character":12,"end_character":12}}),
                json!({"symbol":"p/T#","role":1,"range":{"start_character":12,"end_character":13}}),
            ];
            if control != 2 {
                occurrences.push(json!({"symbol":constructor,"role":1,"range":{"start_character":14,"end_character":14}}));
            }
            if control == 6 {
                symbols.push(json!({"symbol":"local1","kind":13,"signature":signature}));
                occurrences.push(json!({"symbol":"local1","role":2,"range":{"start_character":12,"end_character":12}}));
            }
            let ctor = json!({"start":12,"end":13,"name_start":12,"name_end":13,"allocation_start":8,"allocation_end":source.len(),"kind":"anonymous_allocation","arguments":[]});
            let facts = import_tree(
                source,
                json!(symbols),
                json!(occurrences),
                json!([]),
                json!({
                "members":[{"executable":true,"kind":"def","start":0,"end":source.len(),"name_start":4,"name_end":5,"body_start":8,"body_end":source.len()}],
                "constructors": if control == 8 {json!([ctor,ctor])} else {json!([ctor])}}),
            );
            let allocations: Vec<_> = facts
                .operations
                .iter()
                .filter(|op| op.opcode == Opcode::Allocate)
                .collect();
            if control == 0 {
                assert_eq!(allocations.len(), 1);
                assert_eq!(facts.symbol_name(allocations[0].target), "local0");
                let body = facts
                    .bodies
                    .iter()
                    .find(|body| body.symbol == allocations[0].target)
                    .unwrap();
                assert_eq!(body.flags, BODY_SOURCE_RECIPE | BODY_INITIALIZER);
                let parents: Vec<_> = facts.operations[body.operations.range()]
                    .iter()
                    .map(|op| {
                        assert_eq!(op.opcode, Opcode::Initialize);
                        assert_eq!(op.a, ValueId(0));
                        facts.symbol_name(op.target)
                    })
                    .collect();
                assert_eq!(parents, ["java/lang/Object#`<init>`().", "p/T#"]);
            } else {
                assert!(allocations.is_empty(), "control{control}");
                assert!(facts.issues.iter().any(|issue|facts.text(issue.detail)=="anonymous construction lacks a complete compiler-owned initializer recipe"),"control{control}");
            }
        }
    }

    #[test]
    fn exact_future_callback_slots_respect_declared_modes_in_written_and_inserted_calls() {
        for synthetic in [false, true] {
            for target in [
                "scala/concurrent/Future#map().",
                "scala/concurrent/Future#flatMap().",
                "scala/concurrent/Future#map(+1).",
                "scala/concurrent/Future.map().",
                "scala/concurrent/Promise#map().",
                "user/Future#map().",
            ] {
                for mode in 0..7 {
                    let parameter = format!("{target}(f)");
                    let tpe = match mode {
                        2 => json!({"type_ref":{"symbol":"scala/Function0#"}}),
                        3 => {
                            json!({"by_name_type":{"tpe":{"type_ref":{"symbol":"scala/Function1#"}}}})
                        }
                        4 => json!({"type_ref":{"symbol":"scala/Int#"}}),
                        _ => json!({"type_ref":{"symbol":"scala/Function1#"}}),
                    };
                    let mut declaration = json!({"symbol":target,"kind":3});
                    if mode != 0 {
                        declaration["signature"] = if mode == 6 {
                            json!({"value_signature":{"tpe":{"type_ref":{"symbol":"scala/Function1#"}}}})
                        } else {
                            json!({"method_signature":{"parameter_lists":
                                if mode == 5 { json!([]) } else { json!([{"symlinks":[parameter]}]) }}})
                        };
                    }
                    let facts = import(
                        "def f = map(cb)",
                        json!([{"symbol":"p/A#f().","kind":3},declaration,
                            {"symbol":parameter,"kind":8,"signature":{"value_signature":{"tpe":tpe}}},
                            {"symbol":"p/A#cb.","kind":20}]),
                        json!([{"symbol":"p/A#f().","role":2,"range":{"start_character":4,"end_character":5}},
                            {"symbol":target,"role":1,"range":{"start_character":8,"end_character":11}},
                            {"symbol":"p/A#cb.","role":1,"range":{"start_character":12,"end_character":14}}]),
                        if synthetic {
                            json!([root(
                                8,
                                15,
                                json!({"apply_tree":{"function":{"id_tree":{"symbol":target}},"arguments":[original(12,14)]}})
                            )])
                        } else {
                            json!([])
                        },
                        if synthetic {
                            json!([])
                        } else {
                            json!([{"start":8,"end":15,"name_start":8,"name_end":11,"kind":"apply",
                                "arguments":[{"start":12,"end":14,"clause_index":0,"argument_index":0}]}])
                        },
                        json!([]),
                    );
                    if mode == 6 {
                        assert!(
                            facts
                                .operations
                                .iter()
                                .all(|op| callback_argument_slot(op.flags).is_none())
                        );
                        continue;
                    }
                    let call = &facts.operations[method(&facts, target)];
                    let exact = matches!(
                        target,
                        "scala/concurrent/Future#map()." | "scala/concurrent/Future#flatMap()."
                    );
                    assert_eq!(
                        callback_argument_slot(call.flags),
                        (exact && mode <= 1).then_some(0),
                        "synthetic={synthetic}, target={target}, mode={mode}"
                    );
                }
            }
        }
    }

    #[test]
    fn a_synthetic_function_does_not_execute_or_rebind_its_own_root() {
        let facts = import(
            "def f = g()",
            json!([{"symbol":"p/A#f().","kind":3},{"symbol":"p/A#g().","kind":3}]),
            json!([{"symbol":"p/A#f().","role":2,"range":{"start_character":4,"end_character":5}},
                {"symbol":"p/A#g().","role":1,"range":{"start_character":8,"end_character":9}}]),
            json!([root(
                8,
                11,
                json!({"function_tree":{"parameters":[],"body":original(8,11)}})
            )]),
            json!([{"start":8,"end":11,"name_start":8,"name_end":9,"kind":"apply","arguments":[]}]),
            json!([]),
        );
        let deferred = facts
            .bodies
            .iter()
            .find(|body| body.flags & BODY_DEFERRED != 0)
            .unwrap();
        assert!(
            !facts.operations[deferred.operations.range()]
                .iter()
                .any(|op| op.opcode == Opcode::BindCallback && op.target == deferred.symbol)
        );
        assert_eq!(
            facts.operations[deferred.operations.range()]
                .iter()
                .filter(|op| facts.symbol_name(op.target) == "p/A#g()."
                    && matches!(op.opcode, Opcode::Call | Opcode::VirtualCall))
                .count(),
            1
        );
    }

    #[test]
    fn receiver_wrapper_is_evaluated_before_its_written_consumer_once() {
        let facts = import(
            "def f = 1.g()",
            json!([{"symbol":"p/A#f().","kind":3},{"symbol":"p/A#g().","kind":3}]),
            json!([{"symbol":"p/A#f().","role":2,"range":{"start_character":4,"end_character":5}},
                {"symbol":"p/A#g().","role":1,"range":{"start_character":10,"end_character":11}}]),
            json!([root(
                8,
                9,
                json!({"apply_tree":{"function":{"apply_tree":{
                "function":{"id_tree":{"symbol":"p/Convert.apply()."}},"arguments":[original(8,9)]}},
                "arguments":[{"id_tree":{"symbol":"p/Implicit.get()."}}]}})
            )]),
            json!([{"start":8,"end":13,"name_start":10,"name_end":11,"receiver_start":8,"receiver_end":9,"kind":"apply","arguments":[]}]),
            json!([{"start":8,"end":9,"kind":"literal"}]),
        );
        let converter = method(&facts, "p/Convert.apply().");
        let provider = method(&facts, "p/Implicit.get().");
        let call = method(&facts, "p/A#g().");
        let stage = facts
            .operations
            .iter()
            .position(|op| op.opcode == Opcode::InvokeCallback)
            .unwrap();
        assert!(converter < provider && provider < stage && stage < call);
        assert_eq!(facts.operations[stage].flags, OP_SYNTHETIC_PARAMETER_APPLY);
        assert_eq!(facts.operations[stage].a, facts.operations[converter].dest);
        assert_eq!(facts.operations[call].a, facts.operations[stage].dest);
        assert_eq!(
            facts
                .operations
                .iter()
                .filter(|op| facts.symbol_name(op.target) == "p/Convert.apply().")
                .count(),
            1
        );
        assert_eq!(
            facts
                .operations
                .iter()
                .filter(|op| facts.symbol_name(op.target) == "p/Implicit.get().")
                .count(),
            1
        );
    }

    #[test]
    fn inserted_arguments_patch_exact_written_result_after_explicit_argument_effects() {
        let facts = import(
            "def f = g(h())",
            json!([{"symbol":"p/A#f().","kind":3},{"symbol":"p/A#g().","kind":3},{"symbol":"p/A#h().","kind":3}]),
            json!([{"symbol":"p/A#f().","role":2,"range":{"start_character":4,"end_character":5}},
                {"symbol":"p/A#g().","role":1,"range":{"start_character":8,"end_character":9}},
                {"symbol":"p/A#h().","role":1,"range":{"start_character":10,"end_character":11}}]),
            json!([root(
                8,
                14,
                json!({"apply_tree":{"function":original(8,14),
                "arguments":[{"id_tree":{"symbol":"p/Implicit.get()."}}]}})
            )]),
            json!([{"start":8,"end":14,"name_start":8,"name_end":9,"kind":"apply",
                "arguments":[{"start":10,"end":13,"expression_start":10,"expression_end":13}]},
                {"start":10,"end":13,"name_start":10,"name_end":11,"kind":"apply","arguments":[]}]),
            json!([]),
        );
        let explicit = method(&facts, "p/A#h().");
        let provider = method(&facts, "p/Implicit.get().");
        let call = method(&facts, "p/A#g().");
        assert!(explicit < provider && provider < call);
        assert_eq!(
            &facts.operands[facts.operations[call].arguments.range()],
            &[
                facts.operations[explicit].dest,
                facts.operations[provider].dest
            ]
        );
        assert_eq!(
            facts.operations[provider].arguments.len, 0,
            "same-span provider must not patch itself"
        );
        assert_eq!(
            facts
                .operations
                .iter()
                .filter(|op| facts.symbol_name(op.target) == "p/A#h().")
                .count(),
            1
        );
        assert_eq!(
            facts
                .operations
                .iter()
                .filter(|op| facts.symbol_name(op.target) == "p/A#g().")
                .count(),
            1
        );
        assert!(
            !facts
                .operations
                .iter()
                .any(|op| op.opcode == Opcode::Unknown)
        );
    }

    fn registration_with_inserted_actual(ambiguous: bool, synthetic_end: u32) -> FactSnapshot {
        let target = "org/scalatest/wordspec/AnyWordSpecLike#WordSpecStringWrapper#in().";
        let callback = format!("{target}(body)");
        let position = format!("{target}(pos)");
        let mut occurrences = vec![
            json!({"symbol":"p/A#f().","role":2,"range":{"start_character":4,"end_character":5}}),
            json!({"symbol":target,"role":1,"range":{"start_character":8,"end_character":10}}),
            json!({"symbol":"p/A#body().","role":1,"range":{"start_character":11,"end_character":15}}),
        ];
        if ambiguous {
            occurrences.push(json!({"symbol":"p/otherIn().","role":1,"range":{"start_character":8,"end_character":10}}));
        }
        import(
            "def f = in(body())",
            json!([
                {"symbol":"p/A#f().","kind":3},
                {"symbol":"p/A#body().","kind":3},
                {"symbol":"p/position().","kind":3,"signature":{"method_signature":{"parameter_lists":[]}}},
                {"symbol":"p/otherIn().","kind":3},
                {"symbol":target,"kind":3,"signature":{"method_signature":{"parameter_lists":[{"symlinks":[callback]},{"symlinks":[position]}]}}},
                {"symbol":callback,"kind":8,"signature":{"value_signature":{"tpe":{"by_name_type":{"tpe":{"type_ref":{"symbol":"scala/Unit#"}}}}}}},
                {"symbol":position,"kind":8,"properties":32,"signature":{"value_signature":{"tpe":{"type_ref":{"symbol":"org/scalactic/source/Position#"}}}}}
            ]),
            Value::Array(occurrences),
            json!([root(
                8,
                synthetic_end,
                json!({"apply_tree":{"function":original(8,synthetic_end),"arguments":[{"id_tree":{"symbol":"p/position()."}}]}})
            )]),
            json!([
                {"start":8,"end":18,"name_start":8,"name_end":10,"kind":"apply","arguments":[{"start":11,"end":17,"expression_start":11,"expression_end":17,"clause_index":0,"argument_index":0}]},
                {"start":11,"end":17,"name_start":11,"name_end":15,"kind":"apply","arguments":[]}
            ]),
            json!([]),
        )
    }

    #[test]
    fn compiler_inserted_actual_completes_certified_registration_after_provider_effects() {
        let facts = registration_with_inserted_actual(false, 18);
        let registration = facts
            .operations
            .iter()
            .position(|op| op.opcode == Opcode::RegisterTest)
            .unwrap();
        let provider = method(&facts, "p/position().");
        let op = facts.operations[registration];
        assert!(
            provider < registration,
            "strict implicit provider precedes actual registration"
        );
        assert_eq!(callback_argument_slot(op.flags), Some(0));
        let actuals = &facts.operands[op.arguments.range()];
        assert_eq!(actuals.len(), 2);
        assert_eq!(actuals[1], facts.operations[provider].dest);
        let bound = facts
            .operations
            .iter()
            .find(|candidate| candidate.body == op.body && candidate.dest == actuals[0])
            .unwrap();
        assert_eq!(bound.opcode, Opcode::BindCallback);
        assert_ne!(
            facts.operations[method(&facts, "p/A#body().")].body,
            op.body,
            "test body remains deferred; completing strict metadata is not executing its callback"
        );
        assert!(!facts.issues.iter().any(|issue| facts.text(issue.detail)
            == "compiler inserted arguments have no written invocation binding"));
        facts.validate().unwrap();
    }

    #[test]
    fn registration_completion_rejects_foreign_span_and_ambiguous_compiler_target() {
        for facts in [
            registration_with_inserted_actual(false, 17),
            registration_with_inserted_actual(true, 18),
        ] {
            assert!(
                facts
                    .issues
                    .iter()
                    .any(|issue| issue.kind.is_execution_boundary()
                        && facts.text(issue.detail)
                            == "compiler inserted arguments have no written invocation binding")
            );
            for registration in facts
                .operations
                .iter()
                .filter(|op| op.opcode == Opcode::RegisterTest)
            {
                for provider in facts.operations.iter().filter(|op| {
                    op.body == registration.body && facts.symbol_name(op.target) == "p/position()."
                }) {
                    assert!(
                        !facts.operands[registration.arguments.range()].contains(&provider.dest),
                        "an unmatched compiler provider must not complete a different invocation"
                    );
                }
            }
        }
    }

    #[test]
    fn registration_completion_requires_exact_registration_target_and_callback_certificate() {
        let mut builder = FactBuilder::new();
        let target = builder
            .ensure_symbol(
                "org/scalatest/wordspec/AnyWordSpecLike#WordSpecStringWrapper#in().",
                FileId::NONE,
            )
            .unwrap();
        let other = builder
            .ensure_symbol("p/WordSpecStringWrapper#in().", FileId::NONE)
            .unwrap();
        builder.facts.operands.push(ValueId(1));
        let op = OperationRecord {
            body: BodyId(0),
            opcode: Opcode::RegisterTest,
            target,
            dest: ValueId(2),
            a: ValueId(0),
            b: ValueId::NONE,
            arguments: IdRange { start: 0, len: 1 },
            span: Span { start: 8, end: 18 },
            flags: encode_callback_argument(0).unwrap(),
        };
        assert!(certified_registration_completion(&op, &builder.facts));
        for bad in [
            OperationRecord {
                target: other,
                ..op
            },
            OperationRecord {
                target: SymbolId::NONE,
                ..op
            },
            OperationRecord { flags: 0, ..op },
            OperationRecord {
                flags: encode_callback_argument(1).unwrap(),
                ..op
            },
            OperationRecord {
                opcode: Opcode::BindCallback,
                ..op
            },
            OperationRecord {
                arguments: IdRange { start: 99, len: 1 },
                ..op
            },
        ] {
            assert!(!certified_registration_completion(&bad, &builder.facts));
        }
    }
    #[test]
    fn callback_slot_after_repeated_actuals_uses_declared_clause_modes() {
        let target = "org/scalatest/funsuite/AnyFunSuiteLike#test().";
        let name = format!("{target}(name)");
        let tags = format!("{target}(tags)");
        let body = format!("{target}(body)");
        let facts = import(
            "def f = test(1, 2, 3)(body())",
            json!([{"symbol":"p/A#f().","kind":3},{"symbol":"p/A#body().","kind":3},
                {"symbol":target,"kind":3,"signature":{"method_signature":{"parameter_lists":[{"symlinks":[name,tags]},{"symlinks":[body]}]}}},
                {"symbol":name,"kind":8,"signature":{"value_signature":{"tpe":{"type_ref":{"symbol":"scala/Int#"}}}}},
                {"symbol":tags,"kind":8,"signature":{"value_signature":{"tpe":{"repeated_type":{"tpe":{"type_ref":{"symbol":"scala/Int#"}}}}}}},
                {"symbol":body,"kind":8,"signature":{"value_signature":{"tpe":{"by_name_type":{"tpe":{"type_ref":{"symbol":"scala/Unit#"}}}}}}}]),
            json!([{"symbol":"p/A#f().","role":2,"range":{"start_character":4,"end_character":5}},
                {"symbol":target,"role":1,"range":{"start_character":8,"end_character":12}},
                {"symbol":"p/A#body().","role":1,"range":{"start_character":22,"end_character":26}}]),
            json!([]),
            json!([{"start":8,"end":29,"name_start":8,"name_end":12,"kind":"apply","arguments":[
                {"start":13,"end":14,"clause_index":0,"argument_index":0},
                {"start":16,"end":17,"clause_index":0,"argument_index":1},
                {"start":19,"end":20,"clause_index":0,"argument_index":2},
                {"start":22,"end":28,"clause_index":1,"argument_index":0}]},
                {"start":22,"end":28,"name_start":22,"name_end":26,"kind":"apply","arguments":[]}]),
            json!([{"start":13,"end":14,"kind":"literal"},{"start":16,"end":17,"kind":"literal"},{"start":19,"end":20,"kind":"literal"}]),
        );
        let call = facts
            .operations
            .iter()
            .find(|op| facts.symbol_name(op.target) == target && op.opcode == Opcode::RegisterTest)
            .unwrap();
        assert_eq!(callback_argument_slot(call.flags), Some(3));
        let actuals = &facts.operands[call.arguments.range()];
        assert_eq!(actuals.len(), 4);
        for &value in &actuals[..3] {
            assert!(
                facts
                    .operations
                    .iter()
                    .any(|op| op.dest == value && op.opcode == Opcode::Constant)
            );
        }
        assert!(
            facts
                .operations
                .iter()
                .any(|op| op.dest == actuals[3] && op.opcode == Opcode::BindCallback)
        );
        let deferred = facts
            .operations
            .iter()
            .find(|op| facts.symbol_name(op.target) == "p/A#body().")
            .unwrap();
        assert_ne!(
            deferred.body, call.body,
            "repeated tags cannot shift the deferred callback onto a scalar"
        );
    }

    #[test]
    fn named_callback_slot_obeys_formal_binding_and_rejects_conflicting_modes_or_labels() {
        let target = "org/scalatest/verbs/ShouldVerb#StringShouldWrapperForVerb#should(+2).";
        let block = format!("{target}(block)");
        let carrier = format!("{target}(carrier)");
        for control in 0..3 {
            let block_type = if control == 1 {
                json!({"type_ref":{"symbol":"scala/Int#"}})
            } else {
                json!({"by_name_type":{"tpe":{"type_ref":{"symbol":"scala/Unit#"}}}})
            };
            let facts = import(
                "def f = should(carrier = carrier(), block = body())",
                json!([{"symbol":"p/A#f().","kind":3},{"symbol":"p/A#body().","kind":3},{"symbol":"p/A#carrier().","kind":3},
                    {"symbol":target,"kind":3,"signature":{"method_signature":{"parameter_lists":[{"symlinks":[block,carrier]}]}}},
                    {"symbol":block,"kind":8,"signature":{"value_signature":{"tpe":block_type}}},
                    {"symbol":carrier,"kind":8,"signature":{"value_signature":{"tpe":{"type_ref":{"symbol":"scala/Function3#"}}}}}]),
                json!([{"symbol":"p/A#f().","role":2,"range":{"start_character":4,"end_character":5}},
                    {"symbol":target,"role":1,"range":{"start_character":8,"end_character":14}},
                    {"symbol":if control == 2 {&block} else {&carrier},"role":1,"range":{"start_character":15,"end_character":22}},
                    {"symbol":block,"role":1,"range":{"start_character":36,"end_character":41}},
                    {"symbol":"p/A#carrier().","role":1,"range":{"start_character":25,"end_character":32}},
                    {"symbol":"p/A#body().","role":1,"range":{"start_character":44,"end_character":48}}]),
                json!([]),
                json!([{"start":8,"end":51,"name_start":8,"name_end":14,"kind":"apply","arguments":[
                    {"start":15,"end":34,"expression_start":25,"expression_end":34,"label_range":{"start":15,"end":22},"clause_index":0,"argument_index":0},
                    {"start":36,"end":50,"expression_start":44,"expression_end":50,"label_range":{"start":36,"end":41},"clause_index":0,"argument_index":1}]},
                    {"start":25,"end":34,"name_start":25,"name_end":32,"kind":"apply","arguments":[]},
                    {"start":44,"end":50,"name_start":44,"name_end":48,"kind":"apply","arguments":[]}]),
                json!([]),
            );
            let call = facts
                .operations
                .iter()
                .find(|op| {
                    facts.symbol_name(op.target) == target
                        && matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
                })
                .unwrap();
            assert_eq!(
                callback_argument_slot(call.flags),
                if control == 0 { Some(0) } else { None }
            );
            if control == 0 {
                let actuals = &facts.operands[call.arguments.range()];
                assert!(
                    facts
                        .operations
                        .iter()
                        .any(|op| op.dest == actuals[0] && op.opcode == Opcode::BindCallback)
                );
                assert_eq!(
                    facts.operations[method(&facts, "p/A#carrier().")].dest,
                    actuals[1]
                );
            }
        }
    }
}
