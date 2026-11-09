//! Revision comparison and conservative suite policy over immutable snapshots.
//!
//! This crate does not parse sources or call the solver. Comparison indexes borrow
//! snapshot strings and retain integer IDs; they disappear before query execution.
use selector_facts::{FactSnapshot, SymbolRecord};
use selector_graph::{EdgeRecord, ProgramGraph};
use selector_result::*;
use selector_types::*;
use std::collections::{HashMap, HashSet};
mod classpath_absence;
pub use classpath_absence::{classpath_absence_scope, select_with_classpath_absence};

#[derive(Debug, Default)]
pub struct ChangeSeeds {
    pub base: Vec<NodeId>,
    pub head: Vec<NodeId>,
    pub base_compile: Vec<NodeId>,
    pub head_compile: Vec<NodeId>,
    /// A changed input has no admitted source/identity scope. No omission is safe.
    pub conservative: bool,
    pub base_obligations: Vec<Obligation>,
    pub head_obligations: Vec<Obligation>,
    pub guard_causes: Vec<ChangeGuardCause>,
    pub change_scope: Option<SourceChangeScope>,
}

impl ChangeSeeds {
    pub fn record_unscoped(&mut self, cause: ChangeGuardCause) {
        self.conservative = true;
        self.guard_causes.push(cause);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SuiteRoot {
    pub suite: SuiteId,
    pub node: NodeId,
    /// Exact compiler class identity; never a companion guessed from display text.
    pub receiver: SymbolId,
}

type SymbolKey<'a> = (&'a str, &'a str, &'a str);

fn symbol_key(facts: &FactSnapshot, id: SymbolId) -> SymbolKey<'_> {
    if id.is_none() {
        return ("", "", "");
    }
    let s = &facts.symbols[id.index()];
    let name = facts.text(s.name);
    (
        name,
        facts.text(s.context),
        if selector_types::symbol::is_local(name) || name.starts_with("@local:") {
            facts.path(s.file)
        } else {
            ""
        },
    )
}

fn symbols(facts: &FactSnapshot) -> Result<HashMap<SymbolKey<'_>, SymbolId>, Error> {
    let mut index = HashMap::with_capacity(facts.symbols.len());
    for i in 0..facts.symbols.len() {
        let id = SymbolId::checked(i)?;
        let key = symbol_key(facts, id);
        if let Some(previous) = index.insert(key, id) {
            let old = facts.symbols[previous.index()].file;
            let new = facts.symbols[id.index()].file;
            return Err(Error::Message(format!(
                "duplicate contextual compiler symbol {:?} in context {:?}, local scope {:?}: symbol {} file {} {:?}; symbol {} file {} {:?}",
                key.0,
                key.1,
                key.2,
                previous.0,
                old.0,
                facts.path(old),
                id.0,
                new.0,
                facts.path(new)
            )));
        }
    }
    Ok(index)
}

/// Cross-revision ranks are assigned once from exact compiler identities. Every
/// relationship comparison then touches compact integers instead of repeatedly
/// decoding and sorting long symbol/context/path strings. NONE keeps its sentinel.
struct SymbolRanks {
    base: Vec<u32>,
    head: Vec<u32>,
}

impl SymbolRanks {
    fn new(
        base: &FactSnapshot,
        base_index: &HashMap<SymbolKey<'_>, SymbolId>,
        head: &FactSnapshot,
    ) -> Result<Self, Error> {
        let mut base_ranks = Vec::new();
        base_ranks
            .try_reserve_exact(base.symbols.len())
            .map_err(|_| Error::Limit("symbol rank allocation"))?;
        for i in 0..base.symbols.len() {
            base_ranks.push(SymbolId::checked(i)?.0);
        }
        let mut head_ranks = Vec::new();
        head_ranks
            .try_reserve_exact(head.symbols.len())
            .map_err(|_| Error::Limit("symbol rank allocation"))?;
        let mut next = base.symbols.len();
        for i in 0..head.symbols.len() {
            let id = SymbolId::checked(i)?;
            let rank = match base_index.get(&symbol_key(head, id)) {
                Some(base) => base.0,
                None => {
                    let rank = SymbolId::checked(next)?.0;
                    next += 1;
                    rank
                }
            };
            head_ranks.push(rank);
        }
        Ok(Self {
            base: base_ranks,
            head: head_ranks,
        })
    }
}

fn rank(ranks: &[u32], symbol: SymbolId) -> u32 {
    if symbol.is_none() {
        u32::MAX
    } else {
        ranks[symbol.index()]
    }
}

fn declared_equal(
    a: &FactSnapshot,
    sa: &SymbolRecord,
    a_ranks: &[u32],
    b: &FactSnapshot,
    sb: &SymbolRecord,
    b_ranks: &[u32],
) -> bool {
    a.text(sa.signature) == b.text(sb.signature)
        && sa.kind == sb.kind
        && sa.properties == sb.properties
        && sa.flags == sb.flags
        && rank(a_ranks, sa.owner) == rank(b_ranks, sb.owner)
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
struct EdgeKey {
    target: u32,
    receiver: u32,
    kind: EdgeKind,
    flags: u32,
}

fn edge_key(ranks: &[u32], graph: &ProgramGraph, edge: &EdgeRecord) -> EdgeKey {
    EdgeKey {
        target: rank(ranks, graph.nodes[edge.target.index()].symbol),
        receiver: rank(ranks, edge.receiver),
        kind: edge.kind,
        flags: edge.flags,
    }
}

fn add_seed(graph: &ProgramGraph, symbol: SymbolId, output: &mut Vec<NodeId>) {
    if let Some(node) = graph.node_for_symbol(symbol) {
        output.push(node);
    }
}

fn executable(facts: &FactSnapshot, graph: &ProgramGraph, symbol: SymbolId) -> bool {
    graph.node_for_symbol(symbol).is_some_and(|node| {
        !graph.nodes[node.index()].body.is_none()
            || graph.successors(node).any(|(_, e)| e.kind.is_execution())
            || facts.suites.iter().any(|suite| suite.symbol == symbol)
    })
}

fn runtime_owner<'a>(facts: &'a FactSnapshot, symbol: SymbolId) -> SymbolKey<'a> {
    let s = &facts.symbols[symbol.index()];
    if !s.owner.is_none() {
        return symbol_key(facts, s.owner);
    }
    let owner = selector_types::symbol::global_owner(facts.text(s.name)).unwrap_or("");
    (owner, facts.text(s.context), "")
}

/// Find receiver families through independent hierarchy directions. Construction
/// follows descendants only: changing a child cannot change an ancestor's own
/// initialization. Virtual dispatch also admits ancestors as receiver bounds.
fn runtime_family(
    facts: &FactSnapshot,
    index: &HashMap<SymbolKey<'_>, SymbolId>,
    roots: &HashSet<SymbolKey<'_>>,
    include_ancestors: bool,
) -> HashSet<SymbolId> {
    let roots: Vec<_> = roots
        .iter()
        .filter_map(|key| index.get(key).copied())
        .collect();
    let mut family = HashSet::with_capacity(roots.len());
    let mut edges = Vec::new();
    let mut visited = HashSet::new();
    let mut queue = Vec::new();
    for reverse in [false, true] {
        if !reverse && !include_ancestors {
            continue;
        }
        edges.clear();
        edges.extend(
            facts
                .relations
                .iter()
                .filter(|r| r.kind == RelationKind::Parent)
                .map(|r| {
                    if reverse {
                        (r.target, r.source)
                    } else {
                        (r.source, r.target)
                    }
                }),
        );
        edges.sort_unstable();
        visited.clear();
        queue.clear();
        for root in &roots {
            if visited.insert(*root) {
                queue.push(*root);
            }
        }
        let mut cursor = 0;
        while cursor < queue.len() {
            let node = queue[cursor];
            cursor += 1;
            let start = edges.partition_point(|(source, _)| *source < node);
            let end = edges.partition_point(|(source, _)| *source <= node);
            for (_, target) in &edges[start..end] {
                if visited.insert(*target) {
                    queue.push(*target);
                }
            }
        }
        family.extend(visited.iter().copied());
    }
    family
}

/// An exact final target cannot be redirected by receiver shape alone. This
/// applies to one dispatch edge; the body, other candidates, initialization,
/// changed classpath inputs and open boundaries retain their own seeds.
fn fixed_shape_dispatch(facts: &FactSnapshot, graph: &ProgramGraph, edge: &EdgeRecord) -> bool {
    let Some(op) = facts.operations.get(edge.operation.index()) else {
        return false;
    };
    let source = graph.nodes[edge.source.index()];
    let target = graph.nodes[edge.target.index()].symbol;
    if op.opcode != Opcode::VirtualCall
        || op.target != target
        || op.body != source.body
        || op.flags & (OP_SUPER | OP_QUALIFIED_SUPER) != 0
        || edge.flags != 0
    {
        return false;
    }
    let method = &facts.symbols[target.index()];
    if method.owner.is_none() || method.owner != edge.receiver {
        return false;
    }
    let owner = &facts.symbols[method.owner.index()];
    if method.context != owner.context {
        return false;
    }
    // The bootstrap method is final even when no source body was captured.
    if op.arguments.len == 0
        && facts.text(method.name) == "java/lang/Object#getClass()."
        && facts.text(owner.name) == "java/lang/Object#"
    {
        return true;
    }
    const ABSTRACT: u64 = 4;
    const FINAL: u64 = 8;
    const DEFINED_SOURCE: u32 = SYMBOL_DEFINED | SYMBOL_NATIVE_BINARY;
    if method.kind != 3
        || owner.kind != 13
        || method.properties & ABSTRACT != 0
        || (method.properties | owner.properties) & FINAL == 0
        || method.flags & DEFINED_SOURCE != SYMBOL_DEFINED
        || owner.flags & (DEFINED_SOURCE | SYMBOL_SCALA_PARENTS_COMPLETE)
            != SYMBOL_DEFINED | SYMBOL_SCALA_PARENTS_COMPLETE
        || method.file != owner.file
        || method.context.is_none()
    {
        return false;
    }
    let body = &facts.bodies[op.body.index()];
    if !body.operations.range().contains(&edge.operation.index()) {
        return false;
    }
    let caller_file = body.file;
    [method.file, caller_file].into_iter().all(|file| {
        facts.files.get(file.index()).is_some_and(|file| {
            file.context == method.context
                && file.flags & (SOURCE_VERIFIED | SYNTAX_VERIFIED | FILE_BINARY_SOURCE)
                    == SOURCE_VERIFIED | SYNTAX_VERIFIED
                && file.source_hash != ContentHash::default()
                && facts.text(file.path).ends_with(".scala")
        })
    })
}

fn shape_seeds(
    base_facts: &FactSnapshot,
    base_graph: &ProgramGraph,
    base_index: &HashMap<SymbolKey<'_>, SymbolId>,
    head_facts: &FactSnapshot,
    head_graph: &ProgramGraph,
    head_index: &HashMap<SymbolKey<'_>, SymbolId>,
    ranks: &SymbolRanks,
    outside: &HashSet<(&str, &str)>,
    result: &mut ChangeSeeds,
) {
    struct Row {
        source: SymbolId,
        target: SymbolId,
        kind: RelationKind,
        ordinal: u32,
    }
    fn key(ranks: &[u32], row: &Row) -> (u32, u32, u32, u32) {
        (
            rank(ranks, row.source),
            row.kind as u32,
            row.ordinal,
            rank(ranks, row.target),
        )
    }
    fn relations(facts: &FactSnapshot, ranks: &[u32], outside: &HashSet<(&str, &str)>) -> Vec<Row> {
        let mut ordinals = HashMap::<SymbolId, u32>::new();
        let mut native_parents = HashSet::new();
        let mut rows: Vec<_> = facts
            .relations
            .iter()
            .filter(|r| {
                matches!(r.kind, RelationKind::Parent | RelationKind::Override)
                    && !outside_declaration(facts, r.source, outside)
            })
            .filter(|r| {
                // Older enriched snapshots may republish the same verified
                // JVM header while admitting different methods. Repeating an
                // identical native parent does not move the ordinal of the
                // next distinct parent. Keep source order and all distinct
                // JVM parents exact; unverified metadata stays conservative.
                const NATIVE_HEADER: u32 = SYMBOL_NATIVE_BINARY | SYMBOL_JVM_CLASS_HEADER_VERIFIED;
                const AUTHORITY: u32 =
                    NATIVE_HEADER | SYMBOL_DEFINED | SYMBOL_SCALA_PARENTS_COMPLETE;
                r.kind != RelationKind::Parent
                    || facts.symbols[r.source.index()].flags & AUTHORITY != NATIVE_HEADER
                    || native_parents.insert((r.source, r.target))
            })
            .map(|r| {
                let ordinal = if r.kind == RelationKind::Parent {
                    let next = ordinals.entry(r.source).or_default();
                    let ordinal = *next;
                    *next = next.saturating_add(1);
                    ordinal
                } else {
                    0
                };
                Row {
                    source: r.source,
                    target: r.target,
                    kind: r.kind,
                    ordinal,
                }
            })
            .collect();
        rows.sort_unstable_by_key(|r| key(ranks, r));
        rows.dedup_by(|a, b| key(ranks, a) == key(ranks, b));
        rows
    }
    // Compact numeric sort runs are released before hierarchy scratch is built.
    let before = relations(base_facts, &ranks.base, outside);
    let after = relations(head_facts, &ranks.head, outside);
    let mut roots = HashSet::new();
    let mut initialization_roots = HashSet::new();
    let mut declarations = HashSet::new();
    let new_or_removed_owner = |key: &SymbolKey<'_>| {
        let declaration = match (base_index.get(key), head_index.get(key)) {
            (Some(id), None) => Some(&base_facts.symbols[id.index()]),
            (None, Some(id)) => Some(&head_facts.symbols[id.index()]),
            _ => None,
        };
        declaration.is_some_and(|s| {
            matches!(s.kind, 10 | 13 | 14) && s.flags & (SYMBOL_DEFINED | SYMBOL_NATIVE_BINARY) != 0
        })
    };
    let mut changed = |facts, r: &Row| {
        declarations.insert(symbol_key(facts, r.source));
        let declaring_owner = if r.kind == RelationKind::Parent {
            symbol_key(facts, r.source)
        } else {
            runtime_owner(facts, r.source)
        };
        // A new runtime class cannot change dispatch on an existing object.
        // Its creation, discovery and changed factory/dataflow remain seeds;
        // unknown/external receiver frontiers keep their normal guards. Missing
        // or placeholder owners cannot establish this distinction.
        let existing_owner = !new_or_removed_owner(&declaring_owner);
        if existing_owner {
            roots.insert(declaring_owner);
        }
        initialization_roots.insert(declaring_owner);
        if existing_owner && r.kind == RelationKind::Override {
            // The overridden declaration is a possible dispatch bound, but
            // adding/removing a child's override never changes that parent's
            // own construction or the construction of an unrelated sibling.
            roots.insert(runtime_owner(facts, r.target));
        }
    };
    let (mut b, mut h) = (0, 0);
    while b < before.len() || h < after.len() {
        match (before.get(b), after.get(h)) {
            (Some(old), Some(new)) => match key(&ranks.base, old).cmp(&key(&ranks.head, new)) {
                std::cmp::Ordering::Equal => {
                    b += 1;
                    h += 1;
                }
                std::cmp::Ordering::Less => {
                    changed(base_facts, old);
                    b += 1;
                }
                std::cmp::Ordering::Greater => {
                    changed(head_facts, new);
                    h += 1;
                }
            },
            (Some(old), None) => {
                changed(base_facts, old);
                b += 1;
            }
            (None, Some(new)) => {
                changed(head_facts, new);
                h += 1;
            }
            (None, None) => break,
        }
    }
    drop(changed);
    drop(before);
    drop(after);
    // Scala linearization is usable only with an admitted ordered parent list.
    // Losing or gaining that proof changes dispatch even if all edges match.
    for (key, base) in base_index {
        if let Some(head) = head_index.get(key) {
            if outside_declaration(base_facts, *base, outside)
                && outside_declaration(head_facts, *head, outside)
            {
                continue;
            }
            if (base_facts.symbols[base.index()].flags ^ head_facts.symbols[head.index()].flags)
                & SYMBOL_SCALA_PARENTS_COMPLETE
                != 0
            {
                roots.insert(*key);
                initialization_roots.insert(*key);
                declarations.insert(*key);
            }
        }
    }
    if roots.is_empty() && initialization_roots.is_empty() {
        return;
    }
    for key in declarations {
        if let Some(symbol) = base_index.get(&key) {
            add_seed(base_graph, *symbol, &mut result.base_compile);
        }
        if let Some(symbol) = head_index.get(&key) {
            add_seed(head_graph, *symbol, &mut result.head_compile);
        }
    }
    let base_family = runtime_family(base_facts, base_index, &roots, true);
    let head_family = runtime_family(head_facts, head_index, &roots, true);
    let mut family = HashSet::with_capacity(base_family.len() + head_family.len());
    family.extend(base_family.iter().map(|id| rank(&ranks.base, *id)));
    family.extend(head_family.iter().map(|id| rank(&ranks.head, *id)));
    drop(base_family);
    drop(head_family);
    let base_initialization = runtime_family(base_facts, base_index, &initialization_roots, false);
    let head_initialization = runtime_family(head_facts, head_index, &initialization_roots, false);
    let mut initialization_family =
        HashSet::with_capacity(base_initialization.len() + head_initialization.len());
    initialization_family.extend(base_initialization.iter().map(|id| rank(&ranks.base, *id)));
    initialization_family.extend(head_initialization.iter().map(|id| rank(&ranks.head, *id)));
    drop(base_initialization);
    drop(head_initialization);
    for (facts, graph, ranks, seeds) in [
        (base_facts, base_graph, &ranks.base, &mut result.base),
        (head_facts, head_graph, &ranks.head, &mut result.head),
    ] {
        let related = |symbol: SymbolId| !symbol.is_none() && family.contains(&rank(ranks, symbol));
        for edge in &graph.edges {
            if !roots.is_empty()
                && edge.kind == EdgeKind::VirtualCall
                && (edge.receiver.is_none()
                    || related(edge.receiver)
                    || related(
                        facts.symbols[graph.nodes[edge.target.index()].symbol.index()].owner,
                    ))
                && !fixed_shape_dispatch(facts, graph, edge)
            {
                seeds.push(edge.source);
            }
            if matches!(edge.kind, EdgeKind::Construct | EdgeKind::Initialize)
                && initialization_family
                    .contains(&rank(ranks, graph.nodes[edge.target.index()].symbol))
            {
                seeds.push(edge.source);
            }
        }
    }
}

fn admitted(facts: &FactSnapshot, graph: &ProgramGraph) -> Result<(), Error> {
    facts.validate()?;
    graph.validate()?;
    if graph.facts_identity != facts.identity {
        return Err(Error::Invalid("graph fact identity"));
    }
    for n in &graph.nodes {
        if n.symbol.index() >= facts.symbols.len()
            || (!n.file.is_none() && n.file.index() >= facts.files.len())
            || (!n.body.is_none() && n.body.index() >= facts.bodies.len())
        {
            return Err(Error::Invalid("graph fact reference"));
        }
    }
    for e in &graph.edges {
        if !e.receiver.is_none() && e.receiver.index() >= facts.symbols.len() {
            return Err(Error::Invalid("graph receiver symbol"));
        }
    }
    Ok(())
}

type IssueKey = (u32, FileId, SymbolId, StrId);

/// A source-owned recipe boundary can be handled by the solver's reached-context
/// guards. Admission failures and passive compiler-reference conflicts cannot:
/// their executable owner has not been established by an admitted body.
fn recipe_issue_node(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    kind: IssueKind,
    file: FileId,
    symbol: SymbolId,
) -> Option<NodeId> {
    if !matches!(
        kind,
        IssueKind::UnknownExecution
            | IssueKind::UnresolvedSymbol
            | IssueKind::MissingBinary
            | IssueKind::UnsupportedModel
            | IssueKind::ContextConflict
    ) || file.is_none()
        || symbol.is_none()
    {
        return None;
    }
    let declaration = facts.symbols.get(symbol.index())?;
    if declaration.file != file || declaration.flags & SYMBOL_DEFINED == 0 {
        return None;
    }
    let node = graph.node_for_symbol(symbol)?;
    let record = &graph.nodes[node.index()];
    let body = facts.bodies.get(record.body.index())?;
    (record.symbol == symbol && record.file == file && body.symbol == symbol && body.file == file)
        .then_some(node)
}

fn scoped_recipe_issues(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    dirty: &HashSet<(&str, &str)>,
) -> HashSet<IssueKey> {
    // Index only dirty-file boundaries. Exact detail IDs are part of admission:
    // a different graph diagnostic must not stand in for this fact's uncertainty.
    graph
        .issues
        .iter()
        .filter(|issue| {
            let Some(file) = facts.files.get(issue.file.index()) else {
                return false;
            };
            dirty.contains(&(facts.path(issue.file), facts.text(file.context)))
                && recipe_issue_node(facts, graph, issue.kind, issue.file, issue.symbol)
                    == Some(issue.node)
                && !issue.node.is_none()
        })
        .map(|issue| (issue.kind as u32, issue.file, issue.symbol, issue.detail))
        .collect()
}

fn verified_source(file: &selector_facts::FileRecord) -> bool {
    file.flags & SOURCE_VERIFIED != 0
        && file.flags & FILE_BINARY_SOURCE == 0
        && !file.source.is_none()
}
fn outside_file(facts: &FactSnapshot, file: FileId, outside: &HashSet<(&str, &str)>) -> bool {
    facts.files.get(file.index()).is_some_and(|record| {
        verified_source(record) && outside.contains(&(facts.path(file), facts.text(record.context)))
    })
}
fn outside_declaration(
    facts: &FactSnapshot,
    symbol: SymbolId,
    outside: &HashSet<(&str, &str)>,
) -> bool {
    let record = &facts.symbols[symbol.index()];
    record.flags & SYMBOL_DEFINED != 0 && outside_file(facts, record.file, outside)
}
fn outside_node(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    node: NodeId,
    outside: &HashSet<(&str, &str)>,
) -> bool {
    let record = &graph.nodes[node.index()];
    facts.bodies.get(record.body.index()).map_or_else(
        || outside_declaration(facts, record.symbol, outside),
        |body| outside_file(facts, body.file, outside),
    )
}

/// Compare semantic declarations, executable bodies, and resolved relationships.
///
/// An empty `changed_paths` discovers changes from file hashes. A supplied path
/// missing from both snapshots yields conservative selection. Bodies are compared
/// independently: editing a deferred/lazy body seeds that body, not its enclosing
/// initializer. New/removed dispatch edges seed the affected caller in both graphs.
/// With requested paths, physically changed source files outside that request are
/// reported separately; their direct source deltas are not additional seeds.
/// Compiler binding changes in unchanged source and native/runtime deltas remain
/// global. This is a requested-source result, not whole-checkout authority.
pub fn changed_seeds(
    base_facts: &FactSnapshot,
    base_graph: &ProgramGraph,
    head_facts: &FactSnapshot,
    head_graph: &ProgramGraph,
    changed_paths: &[&str],
) -> Result<ChangeSeeds, Error> {
    changed_seeds_with_mode(
        base_facts,
        base_graph,
        head_facts,
        head_graph,
        changed_paths,
        if changed_paths.is_empty() {
            SourceChangeMode::SnapshotDelta
        } else {
            SourceChangeMode::RequestedPaths
        },
    )
}

/// Explicit source scope also supports runtime-only requests whose effective
/// source path list is empty. Unknown source identity never certifies an omission.
pub fn changed_seeds_with_mode(
    base_facts: &FactSnapshot,
    base_graph: &ProgramGraph,
    head_facts: &FactSnapshot,
    head_graph: &ProgramGraph,
    changed_paths: &[&str],
    mode: SourceChangeMode,
) -> Result<ChangeSeeds, Error> {
    if mode == SourceChangeMode::SnapshotDelta && !changed_paths.is_empty() {
        return Err(Error::Invalid("snapshot-delta source paths"));
    }
    admitted(base_facts, base_graph)?;
    admitted(head_facts, head_graph)?;
    let base_symbols = symbols(base_facts)?;
    let head_symbols = symbols(head_facts)?;
    let ranks = SymbolRanks::new(base_facts, &base_symbols, head_facts)?;
    let mut result = ChangeSeeds::default();
    let requested: HashSet<&str> = changed_paths.iter().copied().collect();
    let mut found = HashSet::with_capacity(requested.len());
    let mut dirty = HashSet::new();
    let mut base_files = HashMap::with_capacity(base_facts.files.len());
    for (i, f) in base_facts.files.iter().enumerate() {
        base_files.insert(
            (
                base_facts.path(FileId(i as u32)),
                base_facts.text(f.context),
            ),
            FileId(i as u32),
        );
    }
    let head_files: HashMap<_, _> = head_facts
        .files
        .iter()
        .enumerate()
        .map(|(i, f)| {
            (
                (
                    head_facts.path(FileId(i as u32)),
                    head_facts.text(f.context),
                ),
                FileId(i as u32),
            )
        })
        .collect();
    // A missing (path, context) can be a compiler-context move/addition rather
    // than a physical file delta. Any opposite-side context keeps it global.
    let sorted_paths = |facts: &FactSnapshot| {
        let mut files: Vec<_> = if mode == SourceChangeMode::RequestedPaths {
            (0..facts.files.len())
                .map(|index| FileId(index as u32))
                .collect()
        } else {
            Vec::new()
        };
        files.sort_unstable_by(|a, b| facts.path(*a).cmp(facts.path(*b)));
        files
    };
    let base_paths = sorted_paths(base_facts);
    let head_paths = sorted_paths(head_facts);
    let mut outside = HashSet::new();
    let mut sample = Vec::with_capacity(MAX_OUTSIDE_SOURCE_DELTAS);
    let mut outside_count = 0u64;
    let mut record_outside = |key, delta| {
        outside.insert(key);
        outside_count += 1;
        let index = sample
            .binary_search_by_key(&key, |(key, _)| *key)
            .unwrap_or_else(|i| i);
        if index < MAX_OUTSIDE_SOURCE_DELTAS {
            if sample.len() == MAX_OUTSIDE_SOURCE_DELTAS {
                sample.pop();
            }
            sample.insert(index, (key, delta));
        }
    };
    for (i, f) in head_facts.files.iter().enumerate() {
        let path = head_facts.path(FileId(i as u32));
        if requested.contains(path) {
            found.insert(path);
        }
        let key = (path, head_facts.text(f.context));
        if requested.contains(path)
            || (mode == SourceChangeMode::SnapshotDelta
                && f.flags & FILE_BINARY_SOURCE == 0
                && base_files
                    .get(&key)
                    .is_none_or(|old| base_facts.files[old.index()].source_hash != f.source_hash))
        {
            dirty.insert(key);
        }
        if mode == SourceChangeMode::RequestedPaths
            && !requested.contains(path)
            && verified_source(f)
        {
            let old = base_files.get(&key).copied();
            let physical_delta = old.map_or_else(
                || {
                    base_paths
                        .binary_search_by(|id| base_facts.path(*id).cmp(path))
                        .is_err()
                },
                |id| {
                    verified_source(&base_facts.files[id.index()])
                        && base_facts.files[id.index()].source_hash != f.source_hash
                },
            );
            if physical_delta {
                record_outside(
                    key,
                    SourceFileDelta {
                        base_file: old.unwrap_or(FileId::NONE),
                        head_file: FileId(i as u32),
                    },
                );
            }
        }
    }
    for (i, f) in base_facts.files.iter().enumerate() {
        let path = base_facts.path(FileId(i as u32));
        if requested.contains(path) {
            found.insert(path);
        }
        let key = (path, base_facts.text(f.context));
        if requested.contains(path)
            || (mode == SourceChangeMode::SnapshotDelta
                && f.flags & FILE_BINARY_SOURCE == 0
                && !head_files.contains_key(&key))
        {
            dirty.insert(key);
        }
        if mode == SourceChangeMode::RequestedPaths
            && !requested.contains(path)
            && !head_files.contains_key(&key)
            && head_paths
                .binary_search_by(|id| head_facts.path(*id).cmp(path))
                .is_err()
            && verified_source(f)
        {
            record_outside(
                key,
                SourceFileDelta {
                    base_file: FileId(i as u32),
                    head_file: FileId::NONE,
                },
            );
        }
    }
    drop(record_outside);
    let mut requested_paths: Vec<_> = requested.iter().map(|path| (*path).to_owned()).collect();
    requested_paths.sort_unstable();
    result.change_scope = Some(SourceChangeScope {
        mode,
        requested_paths,
        outside_count,
        outside: sample.into_iter().map(|(_, row)| row).collect(),
    });
    result.conservative = found.len() != requested.len();
    if result.conservative {
        let mut absent: Vec<_> = requested.difference(&found).copied().collect();
        absent.sort_unstable();
        for path in absent {
            result.guard_causes.push(ChangeGuardCause {
                side: SnapshotSide::Head,
                reason: ChangeGuardReason::UncapturedChangedPath,
                kind: IssueKind::UnknownExecution,
                file: FileId::NONE,
                symbol: SymbolId::NONE,
                detail: StrId::NONE,
                path: Some(path.to_owned()),
                external: None,
            });
        }
        result.head_obligations.push(Obligation {
            kind: IssueKind::UnknownExecution,
            file: FileId::NONE,
            symbol: SymbolId::NONE,
            detail: StrId::NONE,
        });
    }

    for (side, facts, graph, obligations) in [
        (
            SnapshotSide::Base,
            base_facts,
            base_graph,
            &mut result.base_obligations,
        ),
        (
            SnapshotSide::Head,
            head_facts,
            head_graph,
            &mut result.head_obligations,
        ),
    ] {
        let scoped_issues = scoped_recipe_issues(facts, graph, &dirty);
        let mut defined = vec![0usize; facts.files.len()];
        let mut missing = Vec::new();
        for (j, s) in facts
            .symbols
            .iter()
            .enumerate()
            .filter(|(_, s)| !s.file.is_none() && s.flags & SYMBOL_DEFINED != 0)
        {
            defined[s.file.index()] += 1;
            if graph.node_for_symbol(SymbolId(j as u32)).is_none() {
                missing.push((s.file, SymbolId(j as u32)));
            }
        }
        for (i, f) in facts.files.iter().enumerate() {
            let file = FileId(i as u32);
            if !dirty.contains(&(facts.path(file), facts.text(f.context))) {
                continue;
            }
            if f.flags & (SOURCE_VERIFIED | SYNTAX_VERIFIED) != SOURCE_VERIFIED | SYNTAX_VERIFIED {
                result.conservative = true;
                result.guard_causes.push(ChangeGuardCause {
                    side,
                    reason: if f.flags & SOURCE_VERIFIED == 0 {
                        ChangeGuardReason::UnverifiedSource
                    } else {
                        ChangeGuardReason::UnverifiedSyntax
                    },
                    kind: if f.flags & SOURCE_VERIFIED == 0 {
                        IssueKind::MissingSource
                    } else {
                        IssueKind::MissingSyntax
                    },
                    file,
                    symbol: SymbolId::NONE,
                    detail: StrId::NONE,
                    path: None,
                    external: None,
                });
                obligations.push(Obligation {
                    kind: if f.flags & SOURCE_VERIFIED == 0 {
                        IssueKind::MissingSource
                    } else {
                        IssueKind::MissingSyntax
                    },
                    file,
                    symbol: SymbolId::NONE,
                    detail: StrId::NONE,
                });
            }
            // An admitted file may have no executable bodies (e.g. declarations).
            // Source-only input without any normalized declaration cannot establish
            // that a changed source has no effect.
            if defined[i] == 0 {
                result.conservative = true;
                result.guard_causes.push(ChangeGuardCause {
                    side,
                    reason: ChangeGuardReason::NoDeclarations,
                    kind: IssueKind::MissingSyntax,
                    file,
                    symbol: SymbolId::NONE,
                    detail: StrId::NONE,
                    path: None,
                    external: None,
                });
                obligations.push(Obligation {
                    kind: IssueKind::MissingSyntax,
                    file,
                    symbol: SymbolId::NONE,
                    detail: StrId::NONE,
                });
            }
            for issue in facts
                .issues
                .iter()
                .filter(|issue| issue.file == file && issue.kind.is_execution_boundary())
            {
                obligations.push(Obligation {
                    kind: issue.kind,
                    file: issue.file,
                    symbol: issue.symbol,
                    detail: issue.detail,
                });
                let unscoped = !scoped_issues.contains(&(
                    issue.kind as u32,
                    issue.file,
                    issue.symbol,
                    issue.detail,
                ));
                result.conservative |= unscoped;
                if unscoped {
                    result.guard_causes.push(ChangeGuardCause {
                        side,
                        reason: ChangeGuardReason::UnscopedFactIssue,
                        kind: issue.kind,
                        file: issue.file,
                        symbol: issue.symbol,
                        detail: issue.detail,
                        path: None,
                        external: None,
                    });
                }
            }
        }
        // Missing declaration graph nodes are also an incomplete input scope.
        for (file, symbol) in missing {
            let f = &facts.files[file.index()];
            if dirty.contains(&(facts.path(file), facts.text(f.context))) {
                result.conservative = true;
                result.guard_causes.push(ChangeGuardCause {
                    side,
                    reason: ChangeGuardReason::MissingDeclarationNode,
                    kind: IssueKind::InvalidInput,
                    file,
                    symbol,
                    detail: StrId::NONE,
                    path: None,
                    external: None,
                });
                obligations.push(Obligation {
                    kind: IssueKind::InvalidInput,
                    file,
                    symbol,
                    detail: StrId::NONE,
                });
            }
        }
    }

    let mut base_edges = Vec::new();
    let mut head_edges = Vec::new();
    for (&key, &base_id) in &base_symbols {
        let Some(&head_id) = head_symbols.get(&key) else {
            if outside_declaration(base_facts, base_id, &outside) {
                continue;
            }
            add_seed(base_graph, base_id, &mut result.base_compile);
            if executable(base_facts, base_graph, base_id) {
                add_seed(base_graph, base_id, &mut result.base);
            }
            continue;
        };
        let old = &base_facts.symbols[base_id.index()];
        let new = &head_facts.symbols[head_id.index()];
        if !(outside_declaration(base_facts, base_id, &outside)
            && outside_declaration(head_facts, head_id, &outside))
            && !declared_equal(base_facts, old, &ranks.base, head_facts, new, &ranks.head)
        {
            add_seed(base_graph, base_id, &mut result.base_compile);
            add_seed(head_graph, head_id, &mut result.head_compile);
            if old.kind != new.kind
                || old.properties != new.properties
                || old.flags != new.flags
                || rank(&ranks.base, old.owner) != rank(&ranks.head, new.owner)
            {
                if executable(base_facts, base_graph, base_id) {
                    add_seed(base_graph, base_id, &mut result.base);
                }
                if executable(head_facts, head_graph, head_id) {
                    add_seed(head_graph, head_id, &mut result.head);
                }
            }
        }
        let bn = base_graph.node_for_symbol(base_id);
        let hn = head_graph.node_for_symbol(head_id);
        match (bn, hn) {
            (Some(bn), Some(hn)) => {
                if outside_node(base_facts, base_graph, bn, &outside)
                    && outside_node(head_facts, head_graph, hn, &outside)
                {
                    continue;
                }
                let body = |facts: &FactSnapshot, graph: &ProgramGraph, node: NodeId| {
                    let n = &graph.nodes[node.index()];
                    facts
                        .bodies
                        .get(n.body.index())
                        .map(|body| (body.body_hash, body.flags))
                };
                if body(base_facts, base_graph, bn) != body(head_facts, head_graph, hn) {
                    result.base.push(bn);
                    result.head.push(hn);
                }
                for execution in [true, false] {
                    base_edges.clear();
                    head_edges.clear();
                    base_edges.extend(
                        base_graph
                            .successors(bn)
                            .filter(|(_, e)| e.kind.is_execution() == execution)
                            .map(|(_, e)| edge_key(&ranks.base, base_graph, e)),
                    );
                    head_edges.extend(
                        head_graph
                            .successors(hn)
                            .filter(|(_, e)| e.kind.is_execution() == execution)
                            .map(|(_, e)| edge_key(&ranks.head, head_graph, e)),
                    );
                    base_edges.sort_unstable();
                    head_edges.sort_unstable();
                    if base_edges != head_edges {
                        if execution {
                            result.base.push(bn);
                            result.head.push(hn);
                        } else {
                            result.base_compile.push(bn);
                            result.head_compile.push(hn);
                        }
                    }
                }
            }
            (Some(bn), None) => {
                if outside_node(base_facts, base_graph, bn, &outside) {
                    continue;
                }
                result.base_compile.push(bn);
                if executable(base_facts, base_graph, base_id) {
                    result.base.push(bn);
                }
            }
            (None, Some(hn)) => {
                if outside_node(head_facts, head_graph, hn, &outside) {
                    continue;
                }
                result.head_compile.push(hn);
                if executable(head_facts, head_graph, head_id) {
                    result.head.push(hn);
                }
            }
            (None, None) => {}
        }
    }
    for (&key, &head_id) in &head_symbols {
        if !base_symbols.contains_key(&key) {
            if outside_declaration(head_facts, head_id, &outside) {
                continue;
            }
            add_seed(head_graph, head_id, &mut result.head_compile);
            if executable(head_facts, head_graph, head_id) {
                add_seed(head_graph, head_id, &mut result.head);
            }
        }
    }
    shape_seeds(
        base_facts,
        base_graph,
        &base_symbols,
        head_facts,
        head_graph,
        &head_symbols,
        &ranks,
        &outside,
        &mut result,
    );
    // Discovery is an execution input: newly runnable suites and changed
    // discovery flags must run even when their class and body already existed.
    let before_suites: HashMap<_, _> = base_facts
        .suites
        .iter()
        .map(|s| {
            (
                (base_facts.text(s.name), rank(&ranks.base, s.symbol)),
                s.flags,
            )
        })
        .collect();
    for suite in &head_facts.suites {
        let key = (head_facts.text(suite.name), rank(&ranks.head, suite.symbol));
        if before_suites.get(&key) != Some(&suite.flags) {
            add_seed(head_graph, suite.symbol, &mut result.head);
        }
    }
    result.base.sort_unstable();
    result.base.dedup();
    result.head.sort_unstable();
    result.head.dedup();
    result.base_compile.sort_unstable();
    result.base_compile.dedup();
    result.head_compile.sort_unstable();
    result.head_compile.dedup();
    Ok(result)
}

/// Resolve admitted suites without conflating their class and companion.
pub fn suite_roots(facts: &FactSnapshot, graph: &ProgramGraph) -> Result<Vec<SuiteRoot>, Error> {
    admitted(facts, graph)?;
    let mut roots = Vec::with_capacity(facts.suites.len());
    for (i, suite) in facts.suites.iter().enumerate() {
        if let Some(node) = graph.node_for_symbol(suite.symbol) {
            roots.push(SuiteRoot {
                suite: SuiteId::checked(i)?,
                node,
                receiver: suite.symbol,
            });
        }
    }
    Ok(roots)
}

fn merge_completion(a: Completion, b: Completion) -> Completion {
    match (a, b) {
        (Completion::ResourceLimited, _) | (_, Completion::ResourceLimited) => {
            Completion::ResourceLimited
        }
        (Completion::Conservative, _) | (_, Completion::Conservative) => Completion::Conservative,
        _ => Completion::Complete,
    }
}

fn validate_analysis(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    analysis: &AnalysisResult,
) -> Result<(), Error> {
    if graph.identity != analysis.snapshot {
        return Err(Error::Invalid("analysis snapshot identity"));
    }
    if analysis.root_impacts().is_some() {
        analysis.validate_execution_effects()?;
    }
    if analysis
        .obligations
        .iter()
        .any(|issue| !issue.kind.is_execution_boundary())
    {
        return Err(Error::Invalid(
            "metadata issue in analysis execution obligations",
        ));
    }
    if analysis
        .evidence
        .guard_causes
        .windows(2)
        .any(|w| w[0].root >= w[1].root)
    {
        return Err(Error::Invalid("analysis guard evidence order"));
    }
    for cause in &analysis.evidence.guard_causes {
        if !cause.kind.is_execution_boundary() {
            return Err(Error::Invalid("metadata issue used as analysis guard"));
        }
        if cause.node.index() >= graph.nodes.len()
            || analysis.guarded_roots.binary_search(&cause.root).is_err()
            || (!cause.file.is_none() && cause.file.index() >= facts.files.len())
            || (!cause.symbol.is_none() && cause.symbol.index() >= facts.symbols.len())
            || (!cause.detail.is_none() && cause.detail.index() >= facts.strings.len())
        {
            return Err(Error::Invalid("analysis guard evidence scope"));
        }
    }
    for nodes in [&analysis.affected, &analysis.guarded_roots] {
        if nodes.windows(2).any(|w| w[0] >= w[1])
            || nodes.iter().any(|n| n.index() >= graph.nodes.len())
        {
            return Err(Error::Invalid("analysis node index"));
        }
    }
    Ok(())
}

fn covers_runnable_catalogue(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    analysis: &AnalysisResult,
) -> bool {
    facts.suites.iter().all(|suite| {
        graph.node_for_symbol(suite.symbol).is_none_or(|node| {
            analysis
                .evidence
                .requested_roots
                .binary_search(&AnalyzedRoot {
                    node,
                    receiver: suite.symbol,
                })
                .is_ok()
        })
    })
}

fn open_effects(
    analysis: &AnalysisResult,
    unresolved_roots: bool,
    covers_catalogue: bool,
) -> Result<bool, Error> {
    // A root may retain a value/initialization guard after all of its possible
    // execution effects have closed. Only the solver's bound, exhaustive proof
    // can distinguish that case from an opaque shared writer. An exemplar or
    // the first recorded issue is insufficient; legacy results retain policy.
    let closure = analysis.validate_execution_effects()?;
    Ok(analysis.completion == Completion::ResourceLimited
        || analysis.unscoped_uncertainty
        || unresolved_roots
        || match closure {
            EffectClosure::Closed => !covers_catalogue,
            EffectClosure::Open => true,
            EffectClosure::Unverified => !analysis.guarded_roots.is_empty(),
        })
}

fn validate_root_universe(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    analysis: &AnalysisResult,
) -> Result<(), Error> {
    let requested = &analysis.evidence.requested_roots;
    if requested.is_empty() {
        return Ok(());
    }
    if requested.windows(2).any(|w| w[0] >= w[1])
        || requested.iter().any(|root| {
            root.node.index() >= graph.nodes.len()
                || (!root.receiver.is_none() && root.receiver.index() >= facts.symbols.len())
        })
    {
        return Err(Error::Invalid("analysis requested root scope"));
    }
    let mut declared = Vec::with_capacity(facts.suites.len());
    declared.extend(facts.suites.iter().filter_map(|suite| {
        graph
            .node_for_symbol(suite.symbol)
            .map(|node| AnalyzedRoot {
                node,
                receiver: suite.symbol,
            })
    }));
    declared.sort_unstable();
    declared.dedup();
    if requested
        .iter()
        .any(|root| declared.binary_search(root).is_err())
    {
        return Err(Error::Invalid(
            "analysis requested root outside declared suite universe",
        ));
    }
    Ok(())
}

fn retain_shared_reader(decision: &mut SuiteDecision) {
    if decision.status != SuiteDecisionStatus::Required {
        decision.status = SuiteDecisionStatus::Unknown;
    }
    decision.guarded = true;
    decision.reasons =
        (decision.reasons & !DECISION_COMPLETE_UNAFFECTED) | DECISION_OPAQUE_SHARED_HEAP;
}

fn selected_decisions(decisions: &[SuiteDecision]) -> Vec<SelectedSuite> {
    decisions
        .iter()
        .filter(|decision| decision.status != SuiteDecisionStatus::Excluded)
        .map(|decision| SelectedSuite {
            suite: decision.suite,
            node: decision.node,
            guarded: decision.guarded,
        })
        .collect()
}

/// Consume query results, dropping query state before callers render output.
/// Base suite IDs are mapped by exact compiler identity and context to runnable
/// head suites. Deleted suites are not emitted as runnable tests.
/// Shared readers remain conservative while other runnable effects are unknown.
/// Recorded execution roots must belong to the declared suite catalogue with
/// their exact compiler receiver; execution outside that universe is rejected.
/// Verified runtime evidence must cover every resolved catalogue root. A probe
/// or candidate-only frontier cannot grant whole-catalogue omission authority.
/// Call `select_with_plan` to reuse existing potential-dependency scopes instead
/// of computing them here when a shared-state guard is necessary.
pub fn select(
    base_facts: &FactSnapshot,
    base_graph: &ProgramGraph,
    head_facts: &FactSnapshot,
    head_graph: &ProgramGraph,
    seeds: ChangeSeeds,
    base: Option<AnalysisResult>,
    head: AnalysisResult,
) -> Result<SelectionResult, Error> {
    select_with_semantics(
        base_facts,
        base_graph,
        head_facts,
        head_graph,
        seeds,
        base,
        head,
        SuiteSemantics::SharedState,
    )
}

/// Select under an explicit suite-independence assumption. This changes only
/// hidden cross-suite interference; observed impacts, reached local guards,
/// input coverage and catalogue checks retain their ordinary behavior.
pub fn select_with_semantics(
    base_facts: &FactSnapshot,
    base_graph: &ProgramGraph,
    head_facts: &FactSnapshot,
    head_graph: &ProgramGraph,
    seeds: ChangeSeeds,
    base: Option<AnalysisResult>,
    head: AnalysisResult,
    suite_semantics: SuiteSemantics,
) -> Result<SelectionResult, Error> {
    for (facts, graph, analysis) in [
        (head_facts, head_graph, Some(&head)),
        (base_facts, base_graph, base.as_ref()),
    ] {
        if let Some(analysis) = analysis {
            if analysis.evidence.execution_effects.state() != EffectClosure::Unverified
                && !covers_runnable_catalogue(facts, graph, analysis)
            {
                return Err(Error::Invalid(
                    "plain selection omitted a declared suite root",
                ));
            }
        }
    }
    let head_declarations = if suite_semantics == SuiteSemantics::SharedState {
        seeds.head_compile.clone()
    } else {
        Vec::new()
    };
    let base_declarations = if suite_semantics == SuiteSemantics::SharedState {
        seeds.base_compile.clone()
    } else {
        Vec::new()
    };
    let mut result = select_observed(
        base_facts, base_graph, head_facts, head_graph, seeds, base, head,
    )?;
    result.suite_semantics = suite_semantics;
    result.selection_contract = SelectionContract::current(suite_semantics);
    if suite_semantics == SuiteSemantics::Independent
        || result.decisions.iter().all(|decision| decision.guarded)
    {
        return Ok(result);
    }
    let guard_scope = |facts: &FactSnapshot,
                       graph: &ProgramGraph,
                       analysis: &AnalysisResult,
                       execution: &[NodeId],
                       declarations: &[NodeId]|
     -> Result<Vec<NodeId>, Error> {
        let unresolved = facts
            .suites
            .iter()
            .any(|suite| graph.node_for_symbol(suite.symbol).is_none());
        let opaque = open_effects(
            analysis,
            unresolved,
            covers_runnable_catalogue(facts, graph, analysis),
        )?;
        if (!opaque && execution.is_empty() && declarations.is_empty())
            || !graph.nodes.iter().any(|node| {
                !node.body.is_none()
                    && facts.operations[facts.bodies[node.body.index()].operations.range()]
                        .iter()
                        .any(|op| matches!(op.opcode, Opcode::LoadField | Opcode::ReadElements))
            })
        {
            return Ok(Vec::new());
        }
        // Reuse one temporary plan for opaque exposure and known changed-state
        // reads. A stable abstract TOP value is not a no-change proof. Drop this
        // plan before building the other snapshot's; no execution is invented.
        let plan = selector_plan::plan(
            facts,
            graph,
            selector_plan::PlanSeeds {
                execution,
                declarations,
                unscoped: false,
            },
        )?;
        let mut roots = plan.potential_changed_heap_read_roots(facts, graph)?;
        if opaque {
            roots.extend_from_slice(plan.shared_heap_guarded_roots());
        }
        roots.sort_unstable();
        roots.dedup();
        Ok(roots)
    };
    let head_guards = guard_scope(
        head_facts,
        head_graph,
        &result.head,
        &result.head_seeds,
        &head_declarations,
    )?;
    let base_guards = result
        .base
        .as_ref()
        .map(|analysis| {
            guard_scope(
                base_facts,
                base_graph,
                analysis,
                &result.base_seeds,
                &base_declarations,
            )
        })
        .transpose()?
        .unwrap_or_default();
    let mut retained = false;
    for decision in &mut result.decisions {
        if head_guards.binary_search(&decision.node).is_ok()
            || base_guards.binary_search(&decision.base_node).is_ok()
        {
            retain_shared_reader(decision);
            retained = true;
        }
    }
    if retained {
        result.completion = merge_completion(result.completion, Completion::Conservative);
        result.suites = selected_decisions(&result.decisions);
    }
    Ok(result)
}

// Observed execution alone does not account for opaque cross-root heap effects.
// Both public entry points add their potential shared-state scope before return.
fn select_observed(
    base_facts: &FactSnapshot,
    base_graph: &ProgramGraph,
    head_facts: &FactSnapshot,
    head_graph: &ProgramGraph,
    seeds: ChangeSeeds,
    mut base: Option<AnalysisResult>,
    mut head: AnalysisResult,
) -> Result<SelectionResult, Error> {
    admitted(base_facts, base_graph)?;
    admitted(head_facts, head_graph)?;
    if seeds
        .base_obligations
        .iter()
        .chain(&seeds.head_obligations)
        .any(|issue| !issue.kind.is_execution_boundary())
        || seeds
            .guard_causes
            .iter()
            .any(|cause| !cause.kind.is_execution_boundary())
    {
        return Err(Error::Invalid("metadata issue used as change guard"));
    }
    validate_analysis(head_facts, head_graph, &head)?;
    validate_root_universe(head_facts, head_graph, &head)?;
    if let Some(analysis) = &base {
        validate_analysis(base_facts, base_graph, analysis)?;
        validate_root_universe(base_facts, base_graph, analysis)?;
    }
    if base.is_none() && (!seeds.base.is_empty() || !seeds.base_compile.is_empty()) {
        return Err(Error::Invalid(
            "missing base analysis for changed base nodes",
        ));
    }
    let mut guard_causes = seeds.guard_causes;
    if seeds.conservative && guard_causes.is_empty() {
        guard_causes.push(ChangeGuardCause {
            side: SnapshotSide::Head,
            reason: ChangeGuardReason::UnspecifiedFallback,
            kind: IssueKind::UnknownExecution,
            file: FileId::NONE,
            symbol: SymbolId::NONE,
            detail: StrId::NONE,
            path: None,
            external: None,
        });
    }
    fn append_change_obligations(
        analysis: &mut AnalysisResult,
        issues: Vec<Obligation>,
    ) -> Result<(), Error> {
        if !issues.is_empty() {
            analysis.validate_execution_effects()?;
            analysis.obligations.extend(issues);
            // The solver did not classify this selection-time overlay. Keep its
            // side-specific evidence, but never carry Closed authority across it.
            analysis.mark_execution_effects_open()?;
        }
        Ok(())
    }
    if let Some(analysis) = &mut base {
        append_change_obligations(analysis, seeds.base_obligations)?;
    }
    append_change_obligations(&mut head, seeds.head_obligations)?;
    let mut completion = base.as_ref().map_or(head.completion, |b| {
        merge_completion(b.completion, head.completion)
    });
    if seeds.conservative {
        completion = merge_completion(completion, Completion::Conservative);
    }
    let unscoped = seeds.conservative
        || head.unscoped_uncertainty
        || head.completion == Completion::ResourceLimited
        || base
            .as_ref()
            .is_some_and(|b| b.unscoped_uncertainty || b.completion == Completion::ResourceLimited);
    if unscoped
        || !head.guarded_roots.is_empty()
        || base.as_ref().is_some_and(|b| !b.guarded_roots.is_empty())
    {
        completion = merge_completion(completion, Completion::Conservative);
    }
    let mut base_hits = HashSet::new();
    let mut base_guarded = HashSet::new();
    let mut base_nodes = HashMap::new();
    for suite in &base_facts.suites {
        if let Some(node) = base_graph.node_for_symbol(suite.symbol) {
            base_nodes.insert(
                (
                    base_facts.text(suite.name),
                    symbol_key(base_facts, suite.symbol),
                ),
                node,
            );
        }
    }
    if let Some(analysis) = &base {
        for suite in &base_facts.suites {
            if let Some(node) = base_graph.node_for_symbol(suite.symbol) {
                let key = (
                    base_facts.text(suite.name),
                    symbol_key(base_facts, suite.symbol),
                );
                if analysis.root_reached(node, suite.symbol) {
                    base_hits.insert(key);
                }
                if analysis.guarded_roots.binary_search(&node).is_ok() {
                    base_guarded.insert(key);
                }
            }
        }
    }
    let mut suites = Vec::with_capacity(head_facts.suites.len());
    let mut decisions = Vec::with_capacity(head_facts.suites.len());
    let mut obligations = Vec::new();
    for (i, suite) in head_facts.suites.iter().enumerate() {
        let node = head_graph.node_for_symbol(suite.symbol);
        let key = (
            head_facts.text(suite.name),
            symbol_key(head_facts, suite.symbol),
        );
        let head_hit = node.is_some_and(|n| head.root_reached(n, suite.symbol));
        let base_hit = base_hits.contains(&key);
        let reached = head_hit || base_hit;
        let guarded = unscoped
            || node.is_none()
            || node.is_some_and(|n| head.guarded_roots.binary_search(&n).is_ok())
            || base_guarded.contains(&key);
        if node.is_none() {
            completion = merge_completion(completion, Completion::Conservative);
            obligations.push(Obligation {
                kind: IssueKind::InvalidInput,
                file: suite.file,
                symbol: suite.symbol,
                detail: StrId::NONE,
            });
        }
        if reached || guarded {
            suites.push(SelectedSuite {
                suite: SuiteId::checked(i)?,
                node: node.unwrap_or(NodeId::NONE),
                guarded,
            });
        }
        let mut reasons = 0;
        if head_hit {
            reasons |= DECISION_HEAD_IMPACT;
        }
        if base_hit {
            reasons |= DECISION_BASE_IMPACT;
        }
        if node.is_some_and(|n| head.guarded_roots.binary_search(&n).is_ok())
            || base_guarded.contains(&key)
        {
            reasons |= DECISION_SCOPED_GUARD;
        }
        if seeds.conservative {
            reasons |= DECISION_CHANGED_INPUT_GUARD;
        }
        if head.unscoped_uncertainty || base.as_ref().is_some_and(|b| b.unscoped_uncertainty) {
            reasons |= DECISION_QUERY_UNSCOPED;
        }
        if head.completion == Completion::ResourceLimited
            || base
                .as_ref()
                .is_some_and(|b| b.completion == Completion::ResourceLimited)
        {
            reasons |= DECISION_RESOURCE_LIMIT;
        }
        if node.is_none() {
            reasons |= DECISION_MISSING_ROOT;
        }
        if !reached && !guarded {
            reasons |= DECISION_COMPLETE_UNAFFECTED;
        }
        decisions.push(SuiteDecision {
            suite: SuiteId::checked(i)?,
            node: node.unwrap_or(NodeId::NONE),
            base_node: base_nodes.get(&key).copied().unwrap_or(NodeId::NONE),
            status: if reached {
                SuiteDecisionStatus::Required
            } else if guarded {
                SuiteDecisionStatus::Unknown
            } else {
                SuiteDecisionStatus::Excluded
            },
            guarded,
            reasons,
            head_exclusion: None,
            base_exclusion: None,
        });
    }
    Ok(SelectionResult {
        base_snapshot: base_graph.identity,
        head_snapshot: head_graph.identity,
        suite_semantics: SuiteSemantics::SharedState,
        selection_contract: SelectionContract::current(SuiteSemantics::SharedState),
        completion,
        suites,
        base,
        head,
        obligations,
        guard_causes,
        decisions,
        base_seeds: seeds.base,
        head_seeds: seeds.head,
        change_scope: seeds.change_scope,
    })
}

/// Apply only seed-bound closed-component certificates. Observed impacts and
/// reached unknown boundaries refute exclusion; an unrelated solver budget stop
/// cannot invalidate an independently proved closed component.
pub fn select_with_plan(
    base_facts: &FactSnapshot,
    base_graph: &ProgramGraph,
    head_facts: &FactSnapshot,
    head_graph: &ProgramGraph,
    seeds: ChangeSeeds,
    base: Option<AnalysisResult>,
    head: AnalysisResult,
    base_plan: Option<&selector_plan::CandidatePlan>,
    head_plan: &selector_plan::CandidatePlan,
) -> Result<SelectionResult, Error> {
    if base_plan.is_some_and(|plan| plan.suite_semantics() != head_plan.suite_semantics()) {
        return Err(Error::Invalid("paired suite independence contract"));
    }
    fn check(
        plan: &selector_plan::CandidatePlan,
        facts: &FactSnapshot,
        graph: &ProgramGraph,
        execution: &[NodeId],
        declarations: &[NodeId],
        unscoped: bool,
    ) -> Result<(), Error> {
        plan.validate_seal()?;
        if plan.snapshot() != graph.identity
            || plan.facts_identity() != facts.identity
            || plan.execution_seeds() != execution
            || plan.declaration_seeds() != declarations
            || plan.unscoped() != unscoped
        {
            return Err(Error::Invalid(
                "selection planner certificate input binding",
            ));
        }
        Ok(())
    }
    fn coverage(
        plan: &selector_plan::CandidatePlan,
        analysis: &AnalysisResult,
        facts: &FactSnapshot,
        graph: &ProgramGraph,
    ) -> Result<(), Error> {
        let requested = &analysis.evidence.requested_roots;
        if requested.windows(2).any(|w| w[0] >= w[1])
            || requested.iter().any(|root| {
                root.node.index() >= graph.nodes.len()
                    || (!root.receiver.is_none() && root.receiver.index() >= facts.symbols.len())
            })
        {
            return Err(Error::Invalid("analysis requested root scope"));
        }
        for root in &plan.roots {
            if requested
                .binary_search(&AnalyzedRoot {
                    node: root.node,
                    receiver: root.receiver,
                })
                .is_err()
            {
                return Err(Error::Invalid("analysis omitted a planner candidate root"));
            }
        }
        Ok(())
    }
    check(
        head_plan,
        head_facts,
        head_graph,
        &seeds.head,
        &seeds.head_compile,
        seeds.conservative,
    )?;
    validate_analysis(head_facts, head_graph, &head)?;
    coverage(head_plan, &head, head_facts, head_graph)?;
    if let Some(plan) = base_plan {
        check(
            plan,
            base_facts,
            base_graph,
            &seeds.base,
            &seeds.base_compile,
            seeds.conservative,
        )?;
        if let Some(base) = &base {
            validate_analysis(base_facts, base_graph, base)?;
        }
        if let Some(base) = &base {
            coverage(plan, base, base_facts, base_graph)?;
        } else if !plan.roots.is_empty() {
            return Err(Error::Invalid(
                "missing base analysis for planner candidate roots",
            ));
        }
    }
    fn refuted(
        plan: &selector_plan::CandidatePlan,
        facts: &FactSnapshot,
        graph: &ProgramGraph,
        analysis: &AnalysisResult,
    ) -> Result<Vec<NodeId>, Error> {
        let mut observed = analysis.affected.clone();
        observed.extend_from_slice(&analysis.guarded_roots);
        observed.extend(
            analysis
                .evidence
                .guard_causes
                .iter()
                .map(|cause| cause.node)
                .filter(|node| !node.is_none()),
        );
        observed.sort_unstable();
        observed.dedup();
        let edges: Vec<_> = analysis
            .derived_edges
            .iter()
            .map(|edge| (edge.source, edge.target))
            .collect();
        let mut roots = plan.refuted_roots(facts, graph, &observed, &edges)?;
        roots.sort_unstable();
        roots.dedup();
        Ok(roots)
    }
    let head_refuted = refuted(head_plan, head_facts, head_graph, &head)?;
    let base_refuted = match (base_plan, base.as_ref()) {
        (Some(plan), Some(analysis)) => refuted(plan, base_facts, base_graph, analysis)?,
        _ => Vec::new(),
    };
    let head_open_effects = !seeds.head_obligations.is_empty()
        || open_effects(
            &head,
            head_plan.metrics().unresolved_roots != 0,
            covers_runnable_catalogue(head_facts, head_graph, &head),
        )?;
    let base_open_effects = base_plan
        .zip(base.as_ref())
        .map(|(plan, analysis)| -> Result<bool, Error> {
            Ok(!seeds.base_obligations.is_empty()
                || open_effects(
                    analysis,
                    plan.metrics().unresolved_roots != 0,
                    covers_runnable_catalogue(base_facts, base_graph, analysis),
                )?)
        })
        .transpose()?
        .unwrap_or(false);
    let head_changed_heap = if head_plan.suite_semantics() == SuiteSemantics::SharedState {
        head_plan.potential_changed_heap_read_roots(head_facts, head_graph)?
    } else {
        Vec::new()
    };
    let base_changed_heap = match base_plan {
        Some(plan) if plan.suite_semantics() == SuiteSemantics::SharedState => {
            plan.potential_changed_heap_read_roots(base_facts, base_graph)?
        }
        _ => Vec::new(),
    };
    let global_changed_input = seeds.conservative;
    let mut result = select_observed(
        base_facts, base_graph, head_facts, head_graph, seeds, base, head,
    )?;
    result.suite_semantics = head_plan.suite_semantics();
    result.selection_contract = SelectionContract::current(head_plan.suite_semantics());
    if global_changed_input {
        return Ok(result);
    }
    for decision in &mut result.decisions {
        let shared_heap_exposed = head_changed_heap.binary_search(&decision.node).is_ok()
            || base_changed_heap.binary_search(&decision.base_node).is_ok()
            || (head_open_effects
                && head_plan
                    .shared_heap_guarded_roots()
                    .binary_search(&decision.node)
                    .is_ok())
            || (base_open_effects
                && base_plan.is_some_and(|plan| {
                    plan.shared_heap_guarded_roots()
                        .binary_search(&decision.base_node)
                        .is_ok()
                }));
        if shared_heap_exposed {
            // Potential writes can change scalar data without changing TOP or
            // creating a changed call target. Keep both known changed-state and
            // opaque exposure separate from actual execution/solver guards.
            retain_shared_reader(decision);
            result.completion = merge_completion(result.completion, Completion::Conservative);
            continue;
        }
        if decision.status != SuiteDecisionStatus::Required
            && (head_refuted.binary_search(&decision.node).is_ok()
                || base_refuted.binary_search(&decision.base_node).is_ok())
        {
            decision.status = SuiteDecisionStatus::Unknown;
            decision.guarded = true;
            decision.reasons =
                (decision.reasons & !DECISION_COMPLETE_UNAFFECTED) | DECISION_PLAN_REFUTED;
            result.completion = merge_completion(result.completion, Completion::Conservative);
            continue;
        }
        if decision.status == SuiteDecisionStatus::Required
            || decision.node.is_none()
            || decision.base_node.is_none()
            || decision.reasons & DECISION_SCOPED_GUARD != 0
        {
            continue;
        }
        let Some(base_plan) = base_plan else {
            continue;
        };
        if !head_plan.certifies_unaffected(decision.node)
            || !base_plan.certifies_unaffected(decision.base_node)
        {
            continue;
        }
        decision.status = SuiteDecisionStatus::Excluded;
        decision.guarded = false;
        decision.reasons = DECISION_CERTIFIED_EXCLUSION;
        decision.head_exclusion = Some(RootExclusion {
            snapshot: head_plan.snapshot(),
            root: decision.node,
            certificate: head_plan
                .cert_identity(decision.node)
                .ok_or(Error::Invalid("missing head exclusion certificate"))?,
            assumptions: head_plan.assumptions(),
        });
        decision.base_exclusion = Some(RootExclusion {
            snapshot: base_plan.snapshot(),
            root: decision.base_node,
            certificate: base_plan
                .cert_identity(decision.base_node)
                .ok_or(Error::Invalid("missing base exclusion certificate"))?,
            assumptions: base_plan.assumptions(),
        });
    }
    result.suites = selected_decisions(&result.decisions);
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use selector_facts::{BodyRecord, FactBuilder, FileRecord, SuiteRecord};
    use selector_graph::{EdgeRecord, NodeRecord};

    fn fixture() -> (FactSnapshot, ProgramGraph) {
        let mut b = FactBuilder::new();
        let path = b.intern("Suite.scala").unwrap();
        let context = b.intern("test:scala-2.13").unwrap();
        let source = b.intern("class Suite { def f = 1 }").unwrap();
        b.facts.files.push(FileRecord {
            path,
            context,
            source,
            revision: StrId::NONE,
            source_hash: ContentHash([1; 32]),
            flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
        });
        for name in [
            "p/Suite#",
            "p/Suite.",
            "p/Suite#deferred().",
            "p/Suite#eager.",
        ] {
            let id = b.ensure_symbol(name, FileId(0)).unwrap();
            let record = &mut b.facts.symbols[id.index()];
            record.file = FileId(0);
            record.flags = SYMBOL_DEFINED;
        }
        let name = b.intern("p.Suite").unwrap();
        b.facts.suites.push(SuiteRecord {
            name,
            symbol: SymbolId(0),
            file: FileId(0),
            flags: 0,
        });
        for symbol in [SymbolId(2), SymbolId(3)] {
            b.facts.bodies.push(BodyRecord {
                symbol,
                file: FileId(0),
                span: Span { start: 0, end: 0 },
                name_span: Span::default(),
                operations: IdRange::default(),
                parameters: IdRange::default(),
                body_hash: ContentHash([1; 32]),
                flags: if symbol.0 == 2 {
                    BODY_DEFERRED | BODY_LAZY
                } else {
                    BODY_INITIALIZER
                },
            });
        }
        let facts = b.finish().unwrap();
        let mut graph = ProgramGraph {
            facts_identity: facts.identity,
            ..Default::default()
        };
        for i in 0..facts.symbols.len() {
            graph.nodes.push(NodeRecord {
                symbol: SymbolId(i as u32),
                file: FileId(0),
                body: if i < 2 {
                    BodyId::NONE
                } else {
                    BodyId(i as u32 - 2)
                },
                flags: 0,
            });
            graph.symbol_nodes.push(NodeId(i as u32));
        }
        graph.edges.push(EdgeRecord {
            source: NodeId(0),
            target: NodeId(3),
            kind: EdgeKind::Initialize,
            occurrence: OccurrenceId::NONE,
            operation: OperationId::NONE,
            receiver: SymbolId::NONE,
            flags: 0,
        });
        graph.index().unwrap();
        (facts, graph)
    }
    fn analysis(
        graph: &ProgramGraph,
        mut affected: Vec<NodeId>,
        completion: Completion,
    ) -> AnalysisResult {
        affected.sort_unstable();
        AnalysisResult {
            snapshot: graph.identity,
            completion,
            affected,
            witnesses: Vec::new(),
            derived_edges: Vec::new(),
            obligations: Vec::new(),
            guarded_roots: Vec::new(),
            unscoped_uncertainty: false,
            evidence: Default::default(),
            compilation: Default::default(),
            metrics: Default::default(),
        }
    }
    #[test]
    fn node_projection_does_not_promote_an_unhit_root_to_required() {
        let (facts, graph) = fixture();
        let root = AnalyzedRoot {
            node: graph.node_for_symbol(facts.suites[0].symbol).unwrap(),
            receiver: facts.suites[0].symbol,
        };
        let mut head = analysis(&graph, vec![root.node], Completion::ResourceLimited);
        head.evidence.requested_roots.push(root);
        head.record_root_impacts(vec![]).unwrap();
        let result = select_observed(
            &facts,
            &graph,
            &facts,
            &graph,
            ChangeSeeds::default(),
            None,
            head,
        )
        .unwrap();
        assert!(result.head.contains(root.node));
        let decision = &result.decisions[0];
        assert_eq!(decision.status, SuiteDecisionStatus::Unknown);
        assert_eq!(decision.reasons & DECISION_HEAD_IMPACT, 0);
        assert_ne!(decision.reasons & DECISION_RESOURCE_LIMIT, 0);
    }

    #[test]
    fn exhaustive_effect_authority_never_overrides_missing_scope_or_global_limits() {
        let (_, graph) = fixture();
        let coverage = EffectClosureCoverage {
            contexts: 1,
            evaluated_contexts: 1,
            open_contexts: 0,
            pending_work: 0,
            external_open: false,
        };
        let mut complete = analysis(&graph, vec![], Completion::Conservative);
        complete.guarded_roots.push(NodeId(0));
        complete.record_execution_effects(coverage).unwrap();
        assert!(!open_effects(&complete, false, true).unwrap());
        assert!(open_effects(&complete, true, true).unwrap());
        assert!(open_effects(&complete, false, false).unwrap());
        for (completion, unscoped) in [
            (Completion::ResourceLimited, false),
            (Completion::Complete, true),
        ] {
            let mut limited = analysis(&graph, vec![], completion);
            limited.unscoped_uncertainty = unscoped;
            limited.record_execution_effects(coverage).unwrap();
            assert!(open_effects(&limited, false, true).unwrap());
        }
        let mut open = analysis(&graph, vec![], Completion::Complete);
        open.record_execution_effects(EffectClosureCoverage {
            external_open: true,
            ..coverage
        })
        .unwrap();
        assert!(
            open_effects(&open, false, true).unwrap(),
            "Open is broad even without a chosen guarded root"
        );
    }
    #[test]
    fn public_selection_rejects_metadata_issues_in_runtime_and_change_evidence() {
        let (facts, graph) = fixture();
        for control in 0..4 {
            let mut head = analysis(&graph, vec![NodeId(0)], Completion::Conservative);
            let mut seeds = ChangeSeeds::default();
            let issue = Obligation {
                kind: IssueKind::IncompleteHierarchy,
                file: FileId::NONE,
                symbol: SymbolId::NONE,
                detail: StrId::NONE,
            };
            match control {
                0 => head.obligations.push(issue),
                1 => {
                    head.guarded_roots.push(NodeId(0));
                    head.evidence
                        .guard_causes
                        .push(selector_result::RootGuardEvidence {
                            root: NodeId(0),
                            node: NodeId(0),
                            kind: issue.kind,
                            file: issue.file,
                            symbol: issue.symbol,
                            detail: issue.detail,
                            runtime: None,
                        });
                }
                2 => seeds.record_unscoped(ChangeGuardCause {
                    side: SnapshotSide::Head,
                    reason: ChangeGuardReason::UnscopedFactIssue,
                    kind: issue.kind,
                    file: issue.file,
                    symbol: issue.symbol,
                    detail: issue.detail,
                    path: None,
                    external: None,
                }),
                _ => seeds.head_obligations.push(issue),
            }
            assert!(
                select(&facts, &graph, &facts, &graph, seeds, None, head).is_err(),
                "metadata runtime evidence {control}"
            );
        }
    }
    fn independent_regions() -> (FactSnapshot, ProgramGraph) {
        let mut b = FactBuilder::new();
        let path = b.intern("Regions.scala").unwrap();
        let source = b.intern(&" ".repeat(128)).unwrap();
        b.facts.files.push(FileRecord {
            path,
            source,
            revision: StrId::NONE,
            context: StrId::NONE,
            source_hash: ContentHash([1; 32]),
            flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
        });
        b.facts.identity = ContentHash([1; 32]);
        let mut graph = ProgramGraph {
            identity: ContentHash([2; 32]),
            facts_identity: ContentHash([1; 32]),
            ..Default::default()
        };
        for (i, (name, kind)) in [
            ("p/A#", 13),
            ("p/B#", 13),
            ("p/changed().", 3),
            ("p/stable().", 3),
        ]
        .into_iter()
        .enumerate()
        {
            let symbol = b.ensure_symbol(name, FileId(0)).unwrap();
            let record = &mut b.facts.symbols[symbol.index()];
            record.kind = kind;
            record.flags = SYMBOL_DEFINED;
            let start = b.facts.operations.len() as u32;
            if i < 2 {
                b.facts.operations.push(selector_facts::OperationRecord {
                    body: BodyId(i as u32),
                    opcode: Opcode::Call,
                    target: SymbolId(i as u32 + 2),
                    dest: ValueId(1),
                    a: ValueId(0),
                    b: ValueId::NONE,
                    arguments: IdRange::default(),
                    span: Span::default(),
                    flags: 0,
                });
            }
            b.facts.bodies.push(BodyRecord {
                symbol,
                file: FileId(0),
                span: Span::default(),
                name_span: Span::default(),
                operations: IdRange {
                    start,
                    len: u32::from(i < 2),
                },
                parameters: IdRange::default(),
                body_hash: ContentHash([3; 32]),
                flags: if i < 2 { BODY_INITIALIZER } else { 0 },
            });
            graph.nodes.push(NodeRecord {
                symbol,
                file: FileId(0),
                body: BodyId(i as u32),
                flags: 0,
            });
            graph.symbol_nodes.push(NodeId(i as u32));
            if i < 2 {
                b.facts.suites.push(SuiteRecord {
                    name: b.facts.symbols[symbol.index()].name,
                    symbol,
                    file: FileId(0),
                    flags: 0,
                });
                graph.edges.push(EdgeRecord {
                    source: NodeId(i as u32),
                    target: NodeId(i as u32 + 2),
                    kind: EdgeKind::Call,
                    occurrence: OccurrenceId::NONE,
                    operation: OperationId(i as u32),
                    receiver: SymbolId::NONE,
                    flags: 0,
                });
            }
        }
        graph.index().unwrap();
        (b.finish().unwrap(), graph)
    }
    #[test]
    fn independent_suite_contract_is_paired_and_preserves_observed_local_guards() {
        let (facts, graph) = independent_regions();
        let nodes = [NodeId(2)];
        let seeds = || ChangeSeeds {
            base: nodes.to_vec(),
            head: nodes.to_vec(),
            ..Default::default()
        };
        let plan = |semantics| {
            selector_plan::plan_guarded_with_semantics(
                &facts,
                &graph,
                selector_plan::PlanSeeds {
                    execution: &nodes,
                    declarations: &[],
                    unscoped: false,
                },
                &[],
                semantics,
            )
            .unwrap()
        };
        let strict = plan(SuiteSemantics::SharedState);
        let independent = plan(SuiteSemantics::Independent);
        let run = || {
            let options = selector_solve::SolveOptions::default();
            let runtime = selector_solve::SolverRuntime::new(&options).unwrap();
            selector_solve::analyze_typed_with_runtime(
                &facts,
                &graph,
                selector_solve::AnalysisSeeds {
                    execution: &nodes,
                    declarations: &[],
                },
                &options,
                &runtime,
            )
            .unwrap()
        };
        let selected = select_with_plan(
            &facts,
            &graph,
            &facts,
            &graph,
            seeds(),
            Some(run()),
            run(),
            Some(&independent),
            &independent,
        )
        .unwrap();
        assert_eq!(selected.suite_semantics, SuiteSemantics::Independent);
        assert_eq!(selected.decisions[1].status, SuiteDecisionStatus::Excluded);
        for certificate in [
            selected.decisions[1].base_exclusion.unwrap(),
            selected.decisions[1].head_exclusion.unwrap(),
        ] {
            assert_ne!(
                certificate.assumptions & SuiteSemantics::Independent.assumption_bit(),
                0
            );
        }
        let mismatch = select_with_plan(
            &facts,
            &graph,
            &facts,
            &graph,
            seeds(),
            Some(run()),
            run(),
            Some(&strict),
            &independent,
        )
        .unwrap_err();
        assert_eq!(
            mismatch.to_string(),
            "invalid paired suite independence contract"
        );

        let mut head = run();
        head.guarded_roots.push(NodeId(1));
        head.mark_execution_effects_open().unwrap();
        let guarded = select_with_plan(
            &facts,
            &graph,
            &facts,
            &graph,
            seeds(),
            Some(run()),
            head,
            Some(&independent),
            &independent,
        )
        .unwrap();
        assert_eq!(guarded.suite_semantics, SuiteSemantics::Independent);
        assert_eq!(guarded.decisions[1].status, SuiteDecisionStatus::Unknown);
        assert!(guarded.decisions[1].guarded);
        assert!(guarded.decisions[1].head_exclusion.is_none());
        assert!(guarded.decisions[1].base_exclusion.is_none());
    }

    #[test]
    fn limited_candidate_preserves_paired_independent_exclusion_and_observations_refute_it() {
        let (facts, graph) = independent_regions();
        let nodes = [NodeId(2)];
        let plan = selector_plan::plan(
            &facts,
            &graph,
            selector_plan::PlanSeeds {
                execution: &nodes,
                declarations: &[],
                unscoped: false,
            },
        )
        .unwrap();
        assert!(plan.certifies_unaffected(NodeId(1)));
        let options = selector_solve::SolveOptions {
            execution_roots: Some(
                plan.roots
                    .iter()
                    .map(|root| selector_solve::ExecutionRoot {
                        node: root.node,
                        receiver: root.receiver,
                    })
                    .collect(),
            ),
            ..Default::default()
        };
        let run = |options: &selector_solve::SolveOptions| {
            let runtime = selector_solve::SolverRuntime::new(options).unwrap();
            selector_solve::analyze_typed_with_runtime(
                &facts,
                &graph,
                selector_solve::AnalysisSeeds {
                    execution: &nodes,
                    declarations: &[],
                },
                options,
                &runtime,
            )
            .unwrap()
        };
        let seeds = || ChangeSeeds {
            base: nodes.to_vec(),
            head: nodes.to_vec(),
            ..Default::default()
        };
        let base = run(&options);
        let mut limited = options.clone();
        limited.max_steps = 1;
        let head = run(&limited);
        assert_eq!(head.completion, Completion::ResourceLimited);
        let selected = select_with_plan(
            &facts,
            &graph,
            &facts,
            &graph,
            seeds(),
            Some(base),
            head,
            Some(&plan),
            &plan,
        )
        .unwrap();
        assert_eq!(selected.decisions[1].status, SuiteDecisionStatus::Excluded);
        assert_eq!(selected.decisions[1].reasons, DECISION_CERTIFIED_EXCLUSION);
        assert!(
            selected.decisions[1].head_exclusion.is_some()
                && selected.decisions[1].base_exclusion.is_some()
        );
        assert!(
            !selected
                .suites
                .iter()
                .any(|suite| suite.suite == SuiteId(1))
        );
        let mut head = run(&options);
        head.derived_edges.push(DerivedEdge {
            source: NodeId(3),
            target: NodeId(2),
            kind: EdgeKind::Call,
            operation: OperationId::NONE,
            receiver: SymbolId::NONE,
        });
        // This explicit new observation refutes the static certificate. It was
        // not part of the solver's closed result, so retain only Open authority.
        head.mark_execution_effects_open().unwrap();
        let selected = select_with_plan(
            &facts,
            &graph,
            &facts,
            &graph,
            seeds(),
            Some(run(&options)),
            head,
            Some(&plan),
            &plan,
        )
        .unwrap();
        assert_eq!(selected.decisions[1].status, SuiteDecisionStatus::Unknown);
        assert_ne!(selected.decisions[1].reasons & DECISION_PLAN_REFUTED, 0);
        assert!(
            selected
                .suites
                .iter()
                .any(|suite| suite.suite == SuiteId(1))
        );
    }

    #[test]
    fn lazy_deferred_body_does_not_seed_its_owner_or_eager_neighbor() {
        let (base, bg) = fixture();
        let (mut head, hg) = fixture();
        head.files[0].source_hash = ContentHash([2; 32]);
        head.bodies[0].body_hash = ContentHash([2; 32]);
        let seeds = changed_seeds(&base, &bg, &head, &hg, &["Suite.scala"]).unwrap();
        assert_eq!(seeds.base, vec![NodeId(2)]);
        assert_eq!(seeds.head, vec![NodeId(2)]);
        assert!(!seeds.conservative);
        let selected = select(
            &base,
            &bg,
            &head,
            &hg,
            seeds,
            Some(analysis(&bg, vec![NodeId(2)], Completion::Complete)),
            analysis(&hg, vec![NodeId(2)], Completion::Complete),
        )
        .unwrap();
        assert!(selected.suites.is_empty());
    }
    #[test]
    fn eager_change_and_declaration_change_have_distinct_seeds() {
        let (base, bg) = fixture();
        let (mut head, hg) = fixture();
        head.bodies[1].body_hash = ContentHash([9; 32]);
        let seeds = changed_seeds(&base, &bg, &head, &hg, &[]).unwrap();
        assert_eq!(seeds.head, vec![NodeId(3)]);
        let selected = select(
            &base,
            &bg,
            &head,
            &hg,
            seeds,
            Some(analysis(
                &bg,
                vec![NodeId(0), NodeId(3)],
                Completion::Complete,
            )),
            analysis(&hg, vec![NodeId(0), NodeId(3)], Completion::Complete),
        )
        .unwrap();
        assert_eq!(selected.suites.len(), 1);
        assert!(!selected.suites[0].guarded);
        head.symbols[2].properties = 7;
        let seeds = changed_seeds(&base, &bg, &head, &hg, &[]).unwrap();
        assert_eq!(seeds.head, vec![NodeId(2), NodeId(3)]);
    }
    #[test]
    fn compiler_class_and_companion_are_not_conflated() {
        let (facts, graph) = fixture();
        let roots = suite_roots(&facts, &graph).unwrap();
        assert_eq!(roots[0].node, NodeId(0));
        assert_eq!(roots[0].receiver, SymbolId(0));
        let selected = select(
            &facts,
            &graph,
            &facts,
            &graph,
            ChangeSeeds::default(),
            None,
            analysis(&graph, vec![NodeId(1)], Completion::Complete),
        )
        .unwrap();
        assert!(selected.suites.is_empty());
    }
    #[test]
    fn removed_definition_and_edge_are_evaluated_against_base() {
        let (base, bg) = fixture();
        let (mut head, mut hg) = fixture();
        head.symbols.pop();
        head.bodies.pop();
        hg.nodes.pop();
        hg.symbol_nodes.pop();
        hg.edges.clear();
        hg.index().unwrap();
        let seeds = changed_seeds(&base, &bg, &head, &hg, &["Suite.scala"]).unwrap();
        assert!(seeds.base.contains(&NodeId(3)));
        assert!(seeds.base.contains(&NodeId(0)));
        let selected = select(
            &base,
            &bg,
            &head,
            &hg,
            seeds,
            Some(analysis(
                &bg,
                vec![NodeId(0), NodeId(3)],
                Completion::Complete,
            )),
            analysis(&hg, vec![], Completion::Complete),
        )
        .unwrap();
        assert_eq!(selected.suites.len(), 1);
    }
    #[test]
    fn changed_dispatch_seeds_the_caller_even_outside_changed_file() {
        let (base, bg) = fixture();
        let (head, mut hg) = fixture();
        hg.edges[0].target = NodeId(2);
        hg.index().unwrap();
        let seeds = changed_seeds(&base, &bg, &head, &hg, &[]).unwrap();
        assert_eq!(seeds.base, vec![NodeId(0)]);
        assert_eq!(seeds.head, vec![NodeId(0)]);
    }
    #[test]
    fn missing_source_and_unknown_callbacks_cannot_omit_suites() {
        let (base, bg) = fixture();
        let (mut head, hg) = fixture();
        head.files[0].flags = 0;
        let seeds = changed_seeds(&base, &bg, &head, &hg, &["Suite.scala"]).unwrap();
        assert!(seeds.conservative);
        let selected = select(
            &base,
            &bg,
            &head,
            &hg,
            seeds,
            None,
            analysis(&hg, vec![], Completion::Complete),
        )
        .unwrap();
        assert_eq!(selected.suites.len(), 1);
        assert!(selected.suites[0].guarded);
        let mut unknown = analysis(&bg, vec![], Completion::Conservative);
        unknown.guarded_roots.push(NodeId(0));
        let selected = select(
            &base,
            &bg,
            &base,
            &bg,
            ChangeSeeds::default(),
            None,
            unknown,
        )
        .unwrap();
        assert_eq!(selected.suites.len(), 1);
    }
    #[test]
    fn unknown_changed_path_has_an_explicit_obligation() {
        let (facts, graph) = fixture();
        let seeds = changed_seeds(&facts, &graph, &facts, &graph, &["missing.scala"]).unwrap();
        assert!(seeds.conservative);
        assert_eq!(seeds.head_obligations.len(), 1);
        assert_eq!(seeds.guard_causes.len(), 1);
        assert_eq!(
            seeds.guard_causes[0].reason,
            ChangeGuardReason::UncapturedChangedPath
        );
        assert_eq!(seeds.guard_causes[0].path.as_deref(), Some("missing.scala"));
    }
    #[test]
    fn changed_input_causes_preserve_each_admission_branch_and_scope() {
        let (base, bg) = fixture();
        let (mut head, hg) = fixture();
        head.files[0].flags = 0;
        let seeds = changed_seeds(&base, &bg, &head, &hg, &["Suite.scala"]).unwrap();
        assert!(
            seeds
                .guard_causes
                .iter()
                .any(|c| c.side == SnapshotSide::Head
                    && c.reason == ChangeGuardReason::UnverifiedSource
                    && c.file == FileId(0))
        );
        head.files[0].flags = SOURCE_VERIFIED;
        let seeds = changed_seeds(&base, &bg, &head, &hg, &["Suite.scala"]).unwrap();
        assert!(
            seeds
                .guard_causes
                .iter()
                .any(|c| c.reason == ChangeGuardReason::UnverifiedSyntax)
        );
        head.files[0].flags = SOURCE_VERIFIED | SYNTAX_VERIFIED;
        head.issues.push(selector_facts::IssueRecord {
            kind: IssueKind::ContextConflict,
            file: FileId(0),
            symbol: SymbolId(2),
            detail: StrId::NONE,
        });
        let seeds = changed_seeds(&base, &bg, &head, &hg, &["Suite.scala"]).unwrap();
        assert!(
            seeds
                .guard_causes
                .iter()
                .any(|c| c.reason == ChangeGuardReason::UnscopedFactIssue
                    && c.kind == IssueKind::ContextConflict
                    && c.symbol == SymbolId(2))
        );
        head.issues.clear();
        for symbol in &mut head.symbols {
            symbol.flags &= !SYMBOL_DEFINED;
        }
        let seeds = changed_seeds(&base, &bg, &head, &hg, &["Suite.scala"]).unwrap();
        assert!(
            seeds
                .guard_causes
                .iter()
                .any(|c| c.reason == ChangeGuardReason::NoDeclarations && c.file == FileId(0))
        );
        let (head, mut hg) = fixture();
        hg.nodes.pop();
        hg.symbol_nodes[3] = NodeId::NONE;
        hg.edges.clear();
        hg.index().unwrap();
        let seeds = changed_seeds(&base, &bg, &head, &hg, &["Suite.scala"]).unwrap();
        assert!(
            seeds
                .guard_causes
                .iter()
                .any(|c| c.reason == ChangeGuardReason::MissingDeclarationNode
                    && c.symbol == SymbolId(3))
        );
    }
    #[test]
    fn decisions_distinguish_proven_impact_from_guard_only_and_complete_absence() {
        let (facts, graph) = fixture();
        let required = select(
            &facts,
            &graph,
            &facts,
            &graph,
            ChangeSeeds::default(),
            None,
            analysis(&graph, vec![NodeId(0)], Completion::Complete),
        )
        .unwrap();
        assert_eq!(required.decisions[0].status, SuiteDecisionStatus::Required);
        assert_eq!(required.decisions[0].reasons, DECISION_HEAD_IMPACT);
        let mut uncertain = analysis(&graph, vec![], Completion::Conservative);
        uncertain.guarded_roots.push(NodeId(0));
        let unknown = select(
            &facts,
            &graph,
            &facts,
            &graph,
            ChangeSeeds::default(),
            None,
            uncertain,
        )
        .unwrap();
        assert_eq!(unknown.decisions[0].status, SuiteDecisionStatus::Unknown);
        assert_eq!(unknown.decisions[0].reasons, DECISION_SCOPED_GUARD);
        let excluded = select(
            &facts,
            &graph,
            &facts,
            &graph,
            ChangeSeeds::default(),
            None,
            analysis(&graph, vec![], Completion::Complete),
        )
        .unwrap();
        assert_eq!(excluded.decisions[0].status, SuiteDecisionStatus::Excluded);
        assert_eq!(excluded.decisions[0].reasons, DECISION_COMPLETE_UNAFFECTED);
    }
    #[test]
    fn planned_selection_binds_exact_seeds_and_requested_receiver_frontier() {
        let (facts, graph) = fixture();
        let plan = selector_plan::plan(
            &facts,
            &graph,
            selector_plan::PlanSeeds {
                execution: &[],
                declarations: &[],
                unscoped: true,
            },
        )
        .unwrap();
        let seeds = || ChangeSeeds {
            conservative: true,
            ..Default::default()
        };
        let absent = analysis(&graph, vec![], Completion::Complete);
        assert!(
            select_with_plan(
                &facts,
                &graph,
                &facts,
                &graph,
                seeds(),
                None,
                absent,
                None,
                &plan
            )
            .is_err()
        );
        let mut wrong = analysis(&graph, vec![], Completion::Complete);
        wrong.evidence.requested_roots = vec![AnalyzedRoot {
            node: NodeId(0),
            receiver: SymbolId(1),
        }];
        assert!(
            select_with_plan(
                &facts,
                &graph,
                &facts,
                &graph,
                seeds(),
                None,
                wrong,
                None,
                &plan
            )
            .is_err()
        );
        let mut complete = analysis(&graph, vec![], Completion::Complete);
        complete.evidence.requested_roots = plan
            .roots
            .iter()
            .map(|root| AnalyzedRoot {
                node: root.node,
                receiver: root.receiver,
            })
            .collect();
        let selected = select_with_plan(
            &facts,
            &graph,
            &facts,
            &graph,
            seeds(),
            None,
            complete,
            None,
            &plan,
        )
        .unwrap();
        assert_eq!(selected.decisions[0].status, SuiteDecisionStatus::Unknown);
        assert_eq!(
            selected.guard_causes[0].reason,
            ChangeGuardReason::UnspecifiedFallback
        );
        let mut changed = seeds();
        changed.head.push(NodeId(2));
        let mut complete = analysis(&graph, vec![], Completion::Complete);
        complete.evidence.requested_roots = plan
            .roots
            .iter()
            .map(|root| AnalyzedRoot {
                node: root.node,
                receiver: root.receiver,
            })
            .collect();
        assert!(
            select_with_plan(
                &facts, &graph, &facts, &graph, changed, None, complete, None, &plan
            )
            .is_err()
        );
    }
    #[test]
    fn base_suite_hit_does_not_cross_compiler_contexts() {
        let (base, bg) = fixture();
        let (mut head, hg) = fixture();
        head.symbols[0].context = StrId::NONE;
        let selected = select(
            &base,
            &bg,
            &head,
            &hg,
            ChangeSeeds::default(),
            Some(analysis(&bg, vec![NodeId(0)], Completion::Complete)),
            analysis(&hg, vec![], Completion::Complete),
        )
        .unwrap();
        assert!(selected.suites.is_empty());
    }
    #[test]
    fn inherited_fixture_reachability_selects_the_concrete_suite() {
        let (facts, mut graph) = fixture();
        graph.edges.push(EdgeRecord {
            source: NodeId(0),
            target: NodeId(2),
            kind: EdgeKind::Fixture,
            occurrence: OccurrenceId::NONE,
            operation: OperationId::NONE,
            receiver: SymbolId(0),
            flags: 0,
        });
        graph.index().unwrap();
        let selected = select(
            &facts,
            &graph,
            &facts,
            &graph,
            ChangeSeeds::default(),
            None,
            analysis(&graph, vec![NodeId(0), NodeId(2)], Completion::Complete),
        )
        .unwrap();
        assert_eq!(selected.suites[0].node, NodeId(0));
        assert!(!selected.suites[0].guarded);
    }
    #[test]
    fn dormant_uncertainty_does_not_widen_unrelated_suites() {
        let (mut facts, graph) = fixture();
        facts.suites.push(SuiteRecord {
            name: facts.symbols[1].name,
            symbol: SymbolId(1),
            file: FileId(0),
            flags: 0,
        });
        let dormant = analysis(&graph, vec![], Completion::Conservative);
        let result = select(
            &facts,
            &graph,
            &facts,
            &graph,
            ChangeSeeds::default(),
            None,
            dormant,
        )
        .unwrap();
        assert!(result.suites.is_empty());
        let mut relevant = analysis(&graph, vec![], Completion::Conservative);
        relevant.guarded_roots.push(NodeId(0));
        let result = select(
            &facts,
            &graph,
            &facts,
            &graph,
            ChangeSeeds::default(),
            None,
            relevant,
        )
        .unwrap();
        assert_eq!(result.suites.len(), 1);
        assert_eq!(result.suites[0].suite, SuiteId(0));
        assert!(result.suites[0].guarded);
    }
    #[test]
    fn unscoped_uncertainty_and_budget_exhaustion_retain_all_roots() {
        let (mut facts, graph) = fixture();
        facts.suites.push(SuiteRecord {
            name: facts.symbols[1].name,
            symbol: SymbolId(1),
            file: FileId(0),
            flags: 0,
        });
        let mut unscoped = analysis(&graph, vec![], Completion::Conservative);
        unscoped.unscoped_uncertainty = true;
        let result = select(
            &facts,
            &graph,
            &facts,
            &graph,
            ChangeSeeds::default(),
            None,
            unscoped,
        )
        .unwrap();
        assert_eq!(result.suites.len(), 2);
        assert!(result.suites.iter().all(|s| s.guarded));
        let exhausted = analysis(&graph, vec![], Completion::ResourceLimited);
        let result = select(
            &facts,
            &graph,
            &facts,
            &graph,
            ChangeSeeds::default(),
            None,
            exhausted,
        )
        .unwrap();
        assert_eq!(result.suites.len(), 2);
        assert_eq!(result.completion, Completion::ResourceLimited);
    }
    #[test]
    fn signature_and_compile_reference_changes_have_separate_seeds() {
        let (base, bg) = fixture();
        let (mut head, mut hg) = fixture();
        head.symbols[2].signature = head.symbols[0].name;
        hg.edges.push(EdgeRecord {
            source: NodeId(0),
            target: NodeId(2),
            kind: EdgeKind::Compile,
            occurrence: OccurrenceId::NONE,
            operation: OperationId::NONE,
            receiver: SymbolId::NONE,
            flags: 0,
        });
        hg.index().unwrap();
        let seeds = changed_seeds(&base, &bg, &head, &hg, &[]).unwrap();
        assert!(seeds.base.is_empty());
        assert!(seeds.head.is_empty());
        assert_eq!(seeds.base_compile, vec![NodeId(0), NodeId(2)]);
        assert_eq!(seeds.head_compile, seeds.base_compile);
        let mut compilation_only = analysis(&hg, vec![], Completion::Complete);
        compilation_only.compilation.affected = vec![NodeId(0), NodeId(2)];
        let result = select(
            &base,
            &bg,
            &head,
            &hg,
            seeds,
            Some(analysis(&bg, vec![], Completion::Complete)),
            compilation_only,
        )
        .unwrap();
        assert!(result.suites.is_empty());
    }
    #[test]
    fn named_catalogue_suite_without_compiler_definition_is_scoped_uncertainty() {
        let (mut facts, graph) = fixture();
        facts.suites[0].symbol = SymbolId::NONE;
        facts.suites[0].file = FileId::NONE;
        let result = select(
            &facts,
            &graph,
            &facts,
            &graph,
            ChangeSeeds::default(),
            None,
            analysis(&graph, vec![], Completion::Complete),
        )
        .unwrap();
        assert_eq!(result.suites.len(), 1);
        assert!(result.suites[0].guarded);
        assert!(result.suites[0].node.is_none());
        assert_eq!(result.completion, Completion::Conservative);
    }

    fn source_scope_fixture(changed: bool) -> (FactSnapshot, ProgramGraph) {
        let mut builder = FactBuilder::new();
        let source = builder
            .intern("class Requested; class Incidental; def stable = ()")
            .unwrap();
        for (index, path) in [
            "Requested.scala",
            "Incidental.scala",
            "Stable.scala",
            "library.class",
        ]
        .into_iter()
        .enumerate()
        {
            let path = builder.intern(path).unwrap();
            builder.facts.files.push(FileRecord {
                path,
                context: StrId::NONE,
                source: if index == 3 { StrId::NONE } else { source },
                revision: StrId::NONE,
                source_hash: ContentHash([if changed && index != 2 { 2 } else { 1 }; 32]),
                flags: if index == 3 {
                    FILE_BINARY_SOURCE
                } else {
                    SOURCE_VERIFIED | SYNTAX_VERIFIED
                },
            });
        }
        for (index, name) in [
            "p/Requested#",
            "p/Incidental#",
            "p/stable().",
            "p/native().",
        ]
        .into_iter()
        .enumerate()
        {
            let symbol = builder.ensure_symbol(name, FileId(index as u32)).unwrap();
            let record = &mut builder.facts.symbols[symbol.index()];
            record.file = FileId(index as u32);
            record.kind = if index < 2 { 13 } else { 3 };
            record.flags = if index == 3 {
                SYMBOL_NATIVE_BINARY
            } else {
                SYMBOL_DEFINED
            };
            record.properties = u64::from(changed && index == 1);
            builder.facts.bodies.push(BodyRecord {
                symbol,
                file: FileId(index as u32),
                span: Span::default(),
                name_span: Span::default(),
                operations: IdRange::default(),
                parameters: IdRange::default(),
                body_hash: ContentHash([if changed && index != 2 { 2 } else { 1 }; 32]),
                flags: if index == 3 {
                    BODY_BINARY_RECIPE | BODY_DEFERRED
                } else {
                    BODY_DEFERRED
                },
            });
        }
        if changed {
            builder
                .facts
                .relations
                .push(selector_facts::RelationRecord {
                    source: SymbolId(1),
                    target: SymbolId(0),
                    kind: RelationKind::Parent,
                    file: FileId(1),
                });
        }
        let facts = builder.finish().unwrap();
        let mut graph = ProgramGraph {
            facts_identity: facts.identity,
            ..Default::default()
        };
        for index in 0..4 {
            graph.nodes.push(NodeRecord {
                symbol: SymbolId(index),
                file: FileId(index),
                body: BodyId(index),
                flags: 0,
            });
            graph.symbol_nodes.push(NodeId(index));
        }
        // Same physical source, different compiler-resolved binding: this must
        // remain globally compared even in a request for another source file.
        graph.edges.push(EdgeRecord {
            source: NodeId(2),
            target: NodeId(u32::from(changed)),
            kind: EdgeKind::Initialize,
            occurrence: OccurrenceId::NONE,
            operation: OperationId::NONE,
            receiver: SymbolId::NONE,
            flags: 0,
        });
        graph.index().unwrap();
        (facts, graph)
    }

    #[test]
    fn requested_sources_report_outside_physical_changes_and_keep_global_binding_native_deltas() {
        let (base, bg) = source_scope_fixture(false);
        let (head, hg) = source_scope_fixture(true);
        let seeds = changed_seeds(
            &base,
            &bg,
            &head,
            &hg,
            &["Requested.scala", "Requested.scala"],
        )
        .unwrap();
        assert_eq!(seeds.base, vec![NodeId(0), NodeId(2), NodeId(3)]);
        assert_eq!(seeds.head, seeds.base);
        assert!(!seeds.base_compile.contains(&NodeId(1)));
        let scope = seeds.change_scope.as_ref().unwrap();
        assert_eq!(scope.mode, SourceChangeMode::RequestedPaths);
        assert_eq!(scope.requested_paths, ["Requested.scala"]);
        assert_eq!(scope.outside_count, 1);
        assert_eq!(
            scope.outside,
            [SourceFileDelta {
                base_file: FileId(1),
                head_file: FileId(1)
            }]
        );
        let selected = select(
            &base,
            &bg,
            &head,
            &hg,
            seeds,
            Some(analysis(&bg, vec![], Completion::Complete)),
            analysis(&hg, vec![], Completion::Complete),
        )
        .unwrap();
        assert_eq!(selected.change_scope.unwrap().outside_count, 1);
        for paths in [&[][..], &["Requested.scala", "Incidental.scala"][..]] {
            let seeds = changed_seeds(&base, &bg, &head, &hg, paths).unwrap();
            assert_eq!(seeds.base, vec![NodeId(0), NodeId(1), NodeId(2), NodeId(3)]);
            assert_eq!(seeds.head, seeds.base);
            assert!(
                !seeds.conservative,
                "native recipes are not unverified Scala source inputs"
            );
            assert_eq!(seeds.change_scope.unwrap().outside_count, 0);
        }
    }

    #[test]
    fn explicit_empty_source_request_is_not_snapshot_delta_and_unverified_counterpart_stays_global()
    {
        let (mut base, bg) = source_scope_fixture(false);
        let (head, hg) = source_scope_fixture(true);
        let seeds = changed_seeds_with_mode(
            &base,
            &bg,
            &head,
            &hg,
            &[],
            SourceChangeMode::RequestedPaths,
        )
        .unwrap();
        assert_eq!(seeds.base, vec![NodeId(2), NodeId(3)]);
        assert_eq!(seeds.change_scope.unwrap().outside_count, 2);
        base.files[1].flags = 0;
        base.files[1].source = StrId::NONE;
        let seeds = changed_seeds(&base, &bg, &head, &hg, &["Requested.scala"]).unwrap();
        assert!(seeds.base.contains(&NodeId(1)));
        assert!(seeds.head.contains(&NodeId(1)));
        assert_eq!(seeds.change_scope.unwrap().outside_count, 0);
    }

    #[test]
    fn same_source_path_moved_or_added_compiler_context_keeps_semantic_changes_global() {
        for additional_context in [false, true] {
            let (base, bg) = source_scope_fixture(false);
            let (mut head, mut hg) = source_scope_fixture(false);
            let text = "project:additional-classpath:compile";
            let context = StrId(head.strings.entries.len() as u32);
            head.strings.entries.push(selector_facts::TextRange {
                start: head.strings.bytes.len() as u64,
                len: text.len() as u32,
            });
            head.strings.bytes.extend_from_slice(text.as_bytes());
            let changed_node = if additional_context {
                let file = FileId(head.files.len() as u32);
                let mut declaration = head.files[1];
                declaration.context = context;
                head.files.push(declaration);
                let symbol = SymbolId(head.symbols.len() as u32);
                let mut declaration = head.symbols[1];
                declaration.context = context;
                declaration.file = file;
                head.symbols.push(declaration);
                let body = BodyId(head.bodies.len() as u32);
                let mut recipe = head.bodies[1];
                recipe.symbol = symbol;
                recipe.file = file;
                recipe.body_hash = ContentHash([2; 32]);
                head.bodies.push(recipe);
                let node = NodeId(hg.nodes.len() as u32);
                hg.nodes.push(NodeRecord {
                    symbol,
                    file,
                    body,
                    flags: 0,
                });
                hg.symbol_nodes.push(node);
                node
            } else {
                head.files[1].context = context;
                head.symbols[1].context = context;
                head.bodies[1].body_hash = ContentHash([2; 32]);
                NodeId(1)
            };
            // The source bytes/hash remain identical. A different compiler
            // classpath/context changes the recipe and an unchanged consumer's binding.
            assert_eq!(
                base.files[1].source_hash,
                head.files[hg.nodes[changed_node.index()].file.index()].source_hash
            );
            hg.edges[0].target = changed_node;
            hg.index().unwrap();
            for (base, bg, head, hg) in [(&base, &bg, &head, &hg), (&head, &hg, &base, &bg)] {
                let seeds = changed_seeds(base, bg, head, hg, &["Requested.scala"]).unwrap();
                assert_eq!(seeds.change_scope.as_ref().unwrap().outside_count, 0);
                assert!(seeds.base.contains(&NodeId(2)));
                assert!(seeds.head.contains(&NodeId(2)));
                assert!(seeds.base.contains(&changed_node) || seeds.head.contains(&changed_node));
                assert!(!seeds.conservative);
            }
        }
    }

    #[test]
    fn snapshot_source_admission_keeps_native_delta_and_reached_binary_guard() {
        let (base, bg) = source_scope_fixture(false);
        let (head, mut hg) = source_scope_fixture(true);
        hg.issues.push(selector_graph::GraphIssue {
            kind: IssueKind::MissingBinary,
            node: NodeId(3),
            file: FileId(3),
            symbol: SymbolId(3),
            detail: StrId::NONE,
        });
        let seeds = changed_seeds(&base, &bg, &head, &hg, &[]).unwrap();
        assert!(!seeds.conservative);
        assert!(seeds.head.contains(&NodeId(3)));
        let run = selector_solve::analyze(
            &head,
            &hg,
            &seeds.head,
            &selector_solve::SolveOptions {
                workers: 1,
                execution_roots: Some(
                    vec![selector_solve::ExecutionRoot {
                        node: NodeId(3),
                        receiver: SymbolId(0),
                    }]
                    .into(),
                ),
                ..Default::default()
            },
        )
        .unwrap();
        assert!(run.guarded_roots.contains(&NodeId(3)));
        assert!(
            run.obligations
                .iter()
                .any(|obligation| obligation.kind == IssueKind::MissingBinary
                    && obligation.file == FileId(3))
        );
    }

    #[test]
    fn changed_native_input_keeps_admission_and_execution_guards_without_metadata_obligations() {
        let (base, bg) = source_scope_fixture(false);
        let (mut head, hg) = source_scope_fixture(false);
        head.issues.push(selector_facts::IssueRecord {
            kind: IssueKind::IncompleteHierarchy,
            file: FileId(3),
            symbol: SymbolId(3),
            detail: StrId::NONE,
        });
        let metadata = changed_seeds(&base, &bg, &head, &hg, &["library.class"]).unwrap();
        assert!(
            metadata.conservative,
            "unverified native input admission remains guarded"
        );
        assert!(
            metadata
                .guard_causes
                .iter()
                .any(|cause| cause.reason == ChangeGuardReason::UnverifiedSource)
        );
        assert!(
            !metadata
                .head_obligations
                .iter()
                .any(|issue| issue.kind == IssueKind::IncompleteHierarchy)
        );
        assert!(
            !metadata
                .guard_causes
                .iter()
                .any(|cause| cause.kind == IssueKind::IncompleteHierarchy)
        );
        head.issues[0].kind = IssueKind::UnknownExecution;
        let execution = changed_seeds(&base, &bg, &head, &hg, &["library.class"]).unwrap();
        assert!(execution.conservative);
        assert!(
            execution
                .head_obligations
                .iter()
                .any(|issue| issue.kind == IssueKind::UnknownExecution)
        );
        assert!(
            execution
                .guard_causes
                .iter()
                .any(|cause| cause.kind == IssueKind::UnknownExecution
                    && cause.reason == ChangeGuardReason::UnscopedFactIssue)
        );
    }

    #[test]
    fn outside_source_delta_sample_is_bounded_canonical_and_preserves_add_remove_ids() {
        fn append_file(facts: &mut FactSnapshot, path: &str, hash: u8) -> FileId {
            let id = StrId(facts.strings.entries.len() as u32);
            facts.strings.entries.push(selector_facts::TextRange {
                start: facts.strings.bytes.len() as u64,
                len: path.len() as u32,
            });
            facts.strings.bytes.extend_from_slice(path.as_bytes());
            let file = FileId(facts.files.len() as u32);
            facts.files.push(FileRecord {
                path: id,
                context: StrId::NONE,
                source: facts.files[0].source,
                revision: StrId::NONE,
                source_hash: ContentHash([hash; 32]),
                flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
            });
            file
        }
        let (mut base, bg) = source_scope_fixture(false);
        let (mut head, hg) = source_scope_fixture(true);
        for index in (0..80).rev() {
            let path = format!("outside/{index:03}.scala");
            append_file(&mut base, &path, 1);
            append_file(&mut head, &path, 2);
        }
        let added = append_file(&mut head, "Added.scala", 2);
        let removed = append_file(&mut base, "Removed.scala", 1);
        let seeds = changed_seeds(&base, &bg, &head, &hg, &["Requested.scala"]).unwrap();
        let scope = seeds.change_scope.unwrap();
        assert_eq!(scope.outside_count, 83);
        assert_eq!(scope.outside.len(), MAX_OUTSIDE_SOURCE_DELTAS);
        assert!(scope.outside.capacity() <= MAX_OUTSIDE_SOURCE_DELTAS);
        assert_eq!(
            scope.outside[0],
            SourceFileDelta {
                base_file: FileId::NONE,
                head_file: added
            }
        );
        assert_eq!(
            scope.outside[2],
            SourceFileDelta {
                base_file: removed,
                head_file: FileId::NONE
            }
        );
        assert_eq!(head.path(scope.outside[3].head_file), "outside/000.scala");
        assert_eq!(
            head.path(scope.outside.last().unwrap().head_file),
            "outside/060.scala"
        );
    }

    #[test]
    fn changed_parent_shape_invalidates_dispatch_even_with_identical_potential_edges() {
        let (base, mut bg) = fixture();
        let (mut head, mut hg) = fixture();
        head.relations.push(selector_facts::RelationRecord {
            source: SymbolId(1),
            target: SymbolId(0),
            kind: RelationKind::Parent,
            file: FileId(0),
        });
        for graph in [&mut bg, &mut hg] {
            graph.edges.push(EdgeRecord {
                source: NodeId(2),
                target: NodeId(3),
                kind: EdgeKind::VirtualCall,
                occurrence: OccurrenceId::NONE,
                operation: OperationId::NONE,
                receiver: SymbolId(0),
                flags: 0,
            });
            graph.index().unwrap();
        }
        let seeds = changed_seeds(&base, &bg, &head, &hg, &[]).unwrap();
        assert_eq!(seeds.base, vec![NodeId(2)]);
        assert_eq!(seeds.head, vec![NodeId(2)]);
        assert_eq!(seeds.base_compile, vec![NodeId(1)]);
        assert_eq!(seeds.head_compile, vec![NodeId(1)]);
    }

    // The first five symbols are a parent, changed child, sibling, descendant,
    // and separate parent. Callers 8..12 construct those first four classes;
    // 12..16 initialize them. The final three calls dispatch through the first
    // parent, the separate parent, and an unknown receiver bound respectively.
    fn hierarchy_construction_fixture(
        child_parent: u32,
        root_parent: Option<u32>,
        child_override: bool,
    ) -> (FactSnapshot, ProgramGraph) {
        hierarchy_fixture(child_parent, root_parent, child_override, true)
    }
    fn hierarchy_fixture(
        child_parent: u32,
        root_parent: Option<u32>,
        child_override: bool,
        child_present: bool,
    ) -> (FactSnapshot, ProgramGraph) {
        hierarchy_member_fixture(
            child_parent,
            root_parent,
            child_override,
            child_present,
            child_present,
        )
    }
    fn hierarchy_member_fixture(
        child_parent: u32,
        root_parent: Option<u32>,
        child_override: bool,
        child_present: bool,
        child_method_present: bool,
    ) -> (FactSnapshot, ProgramGraph) {
        let mut builder = FactBuilder::new();
        let path = builder.intern("Hierarchy.scala").unwrap();
        let source = builder
            .intern("class Root; class Child; class Sibling; class Descendant")
            .unwrap();
        builder.facts.files.push(FileRecord {
            path,
            source,
            revision: StrId::NONE,
            context: StrId::NONE,
            source_hash: ContentHash([1; 32]),
            flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
        });
        let mut ids = [SymbolId::NONE; 19];
        for (i, name) in [
            "p/Root#",
            "p/Child#",
            "p/Sibling#",
            "p/Descendant#",
            "p/Other#",
            "p/Root#f().",
            "p/Child#f().",
            "p/Other#f().",
            "p/constructRoot().",
            "p/constructSibling().",
            "p/constructChild().",
            "p/constructDescendant().",
            "p/initializeRoot().",
            "p/initializeSibling().",
            "p/initializeChild().",
            "p/initializeDescendant().",
            "p/dispatchRoot().",
            "p/dispatchOther().",
            "p/dispatchUnknown().",
        ]
        .into_iter()
        .enumerate()
        {
            if (!child_present && matches!(i, 1 | 3)) || (!child_method_present && i == 6) {
                continue;
            }
            let id = builder.ensure_symbol(name, FileId(0)).unwrap();
            ids[i] = id;
            let record = &mut builder.facts.symbols[id.index()];
            record.file = FileId(0);
            record.kind = if i < 5 { 13 } else { 3 };
            record.flags = SYMBOL_DEFINED;
        }
        for (method, owner) in [(5, 0), (6, 1), (7, 4)] {
            if !ids[method].is_none() {
                builder.facts.symbols[ids[method].index()].owner = ids[owner];
            }
        }
        for (child, parent) in [(1, child_parent), (2, 0), (3, 1)]
            .into_iter()
            .chain(root_parent.map(|parent| (0, parent)))
        {
            if ids[child as usize].is_none() || ids[parent as usize].is_none() {
                continue;
            }
            builder
                .facts
                .relations
                .push(selector_facts::RelationRecord {
                    source: ids[child as usize],
                    target: ids[parent as usize],
                    kind: RelationKind::Parent,
                    file: FileId(0),
                });
        }
        if child_method_present && child_override {
            builder
                .facts
                .relations
                .push(selector_facts::RelationRecord {
                    source: ids[6],
                    target: ids[5],
                    kind: RelationKind::Override,
                    file: FileId(0),
                });
        }
        for symbol in [ids[1], ids[3]].into_iter().filter(|id| !id.is_none()) {
            builder.facts.bodies.push(BodyRecord {
                symbol,
                file: FileId(0),
                span: Span::default(),
                name_span: Span::default(),
                operations: IdRange::default(),
                parameters: IdRange::default(),
                body_hash: ContentHash([1; 32]),
                flags: BODY_INITIALIZER,
            });
        }
        let facts = builder.finish().unwrap();
        let mut graph = ProgramGraph {
            facts_identity: facts.identity,
            ..Default::default()
        };
        for i in 0..facts.symbols.len() {
            graph.nodes.push(NodeRecord {
                symbol: SymbolId(i as u32),
                file: FileId(0),
                body: facts
                    .bodies
                    .iter()
                    .position(|body| body.symbol.index() == i)
                    .map(|i| BodyId(i as u32))
                    .unwrap_or(BodyId::NONE),
                flags: 0,
            });
            graph.symbol_nodes.push(NodeId(i as u32));
        }
        for (source, target, kind, receiver) in [
            (8, 0, EdgeKind::Construct, SymbolId::NONE),
            (9, 2, EdgeKind::Construct, SymbolId::NONE),
            (10, 1, EdgeKind::Construct, SymbolId::NONE),
            (11, 3, EdgeKind::Construct, SymbolId::NONE),
            (12, 0, EdgeKind::Initialize, SymbolId::NONE),
            (13, 2, EdgeKind::Initialize, SymbolId::NONE),
            (14, 1, EdgeKind::Initialize, SymbolId::NONE),
            (15, 3, EdgeKind::Initialize, SymbolId::NONE),
            (16, 5, EdgeKind::VirtualCall, SymbolId(0)),
            (17, 7, EdgeKind::VirtualCall, SymbolId(4)),
            (18, 5, EdgeKind::VirtualCall, SymbolId::NONE),
        ] {
            if ids[target as usize].is_none() {
                continue;
            }
            graph.edges.push(EdgeRecord {
                source: NodeId(ids[source as usize].0),
                target: NodeId(ids[target as usize].0),
                kind,
                occurrence: OccurrenceId::NONE,
                operation: OperationId::NONE,
                receiver: if receiver.is_none() {
                    receiver
                } else {
                    ids[receiver.index()]
                },
                flags: 0,
            });
        }
        graph.index().unwrap();
        (facts, graph)
    }

    #[test]
    fn added_and_removed_override_do_not_change_ancestor_or_sibling_construction() {
        let (before, before_graph) = hierarchy_construction_fixture(0, None, false);
        let (after, after_graph) = hierarchy_construction_fixture(0, None, true);
        for (base, bg, head, hg) in [
            (&before, &before_graph, &after, &after_graph),
            (&after, &after_graph, &before, &before_graph),
        ] {
            let seeds = changed_seeds(base, bg, head, hg, &[]).unwrap();
            // Construction of Child and its descendant remains affected, and
            // dispatch through Root or an unknown bound is still invalidated.
            let expected = vec![
                NodeId(10),
                NodeId(11),
                NodeId(14),
                NodeId(15),
                NodeId(16),
                NodeId(18),
            ];
            assert_eq!(seeds.base, expected);
            assert_eq!(seeds.head, expected);
            assert!(!seeds.conservative);
        }
    }

    #[test]
    fn changed_child_parent_retains_own_and_descendant_initialization() {
        let (base, bg) = hierarchy_construction_fixture(0, None, false);
        let (head, hg) = hierarchy_construction_fixture(4, None, false);
        let seeds = changed_seeds(&base, &bg, &head, &hg, &[]).unwrap();
        let expected = vec![
            NodeId(10),
            NodeId(11),
            NodeId(14),
            NodeId(15),
            NodeId(16),
            NodeId(17),
            NodeId(18),
        ];
        assert_eq!(seeds.base, expected);
        assert_eq!(seeds.head, expected);
    }

    #[test]
    fn repeated_verified_native_parents_are_one_ordered_header() {
        fn scenario(
            repeated: bool,
            reordered: bool,
            verified: bool,
        ) -> (FactSnapshot, ProgramGraph) {
            let (mut facts, graph) = hierarchy_construction_fixture(0, None, false);
            let child = facts.find_symbol("p/Child#").unwrap();
            let other = facts.find_symbol("p/Other#").unwrap();
            facts.symbols[child.index()].flags = SYMBOL_NATIVE_BINARY
                | if verified {
                    SYMBOL_JVM_CLASS_HEADER_VERIFIED
                } else {
                    0
                };
            facts.symbols[other.index()].kind = 14;
            let position = facts
                .relations
                .iter()
                .position(|r| r.source == child)
                .unwrap();
            let parent = facts.relations[position];
            let interface = selector_facts::RelationRecord {
                target: other,
                ..parent
            };
            facts
                .relations
                .insert(position + usize::from(!reordered), interface);
            if repeated {
                facts.relations.extend([parent, interface]);
            }
            (facts, graph)
        }
        for (reordered, verified) in [(false, true), (false, false), (true, true)] {
            let (base, bg) = scenario(true, false, verified);
            let (head, hg) = scenario(false, reordered, verified);
            let seeds = changed_seeds(&base, &bg, &head, &hg, &[]).unwrap();
            let changed = reordered || !verified;
            assert_eq!(!seeds.base.is_empty(), changed);
            assert_eq!(!seeds.head.is_empty(), changed);
            assert_eq!(!seeds.base_compile.is_empty(), changed);
            assert_eq!(!seeds.head_compile.is_empty(), changed);
        }
    }

    #[test]
    fn changed_parent_retains_construction_of_parent_and_all_descendants() {
        let (base, bg) = hierarchy_construction_fixture(0, None, false);
        let (mut head, hg) = hierarchy_construction_fixture(0, Some(4), false);
        let seeds = changed_seeds(&base, &bg, &head, &hg, &[]).unwrap();
        let expected: Vec<_> = (8..=18).map(NodeId).collect();
        assert_eq!(seeds.base, expected);
        assert_eq!(seeds.head, expected);
        head.issues.push(selector_facts::IssueRecord {
            kind: IssueKind::ContextConflict,
            file: FileId(0),
            symbol: SymbolId(1),
            detail: StrId::NONE,
        });
        let seeds = changed_seeds(&base, &bg, &head, &hg, &["Hierarchy.scala"]).unwrap();
        assert!(seeds.conservative);
        assert!(
            seeds.guard_causes.iter().any(
                |cause| cause.kind == IssueKind::ContextConflict && cause.symbol == SymbolId(1)
            )
        );
    }

    fn named_node(facts: &FactSnapshot, graph: &ProgramGraph, name: &str) -> NodeId {
        graph
            .node_for_symbol(facts.find_symbol(name).unwrap())
            .unwrap()
    }

    #[test]
    fn new_and_removed_subtypes_keep_creation_and_discovery_without_global_dispatch_seeds() {
        let (before, before_graph) = hierarchy_fixture(0, None, false, false);
        let (mut after, after_graph) = hierarchy_fixture(0, None, true, true);
        let child = after.find_symbol("p/Child#").unwrap();
        after.suites.push(SuiteRecord {
            name: after.symbols[child.index()].name,
            symbol: child,
            file: FileId(0),
            flags: 0,
        });
        for (base, bg, head, hg) in [
            (&before, &before_graph, &after, &after_graph),
            (&after, &after_graph, &before, &before_graph),
        ] {
            let seeds = changed_seeds(base, bg, head, hg, &[]).unwrap();
            for (facts, graph, execution, compilation) in [
                (base, bg, &seeds.base, &seeds.base_compile),
                (head, hg, &seeds.head, &seeds.head_compile),
            ] {
                for name in [
                    "p/dispatchRoot().",
                    "p/dispatchUnknown().",
                    "p/constructRoot().",
                    "p/initializeRoot().",
                ] {
                    assert!(
                        !execution.contains(&named_node(facts, graph, name)),
                        "{name}"
                    );
                }
                // Changed factories/initializers remain affected on both sides,
                // including the base path when its formerly constructed type is removed.
                for name in [
                    "p/constructChild().",
                    "p/constructDescendant().",
                    "p/initializeChild().",
                    "p/initializeDescendant().",
                ] {
                    assert!(
                        execution.contains(&named_node(facts, graph, name)),
                        "{name}"
                    );
                }
                if let Some(child) = facts.find_symbol("p/Child#") {
                    assert!(execution.contains(&graph.node_for_symbol(child).unwrap()));
                    assert!(compilation.contains(&graph.node_for_symbol(child).unwrap()));
                    assert!(compilation.contains(&named_node(facts, graph, "p/Child#f().")));
                }
            }
            assert!(!seeds.conservative);
        }
    }

    #[test]
    fn incomplete_or_common_owner_keeps_conservative_dispatch_invalidation() {
        let (base, bg) = hierarchy_fixture(0, None, false, false);
        let (mut head, hg) = hierarchy_fixture(0, None, true, true);
        head.symbols[1].flags = 0;
        head.symbols[3].flags = 0;
        let seeds = changed_seeds(&base, &bg, &head, &hg, &[]).unwrap();
        assert!(
            seeds
                .head
                .contains(&named_node(&head, &hg, "p/dispatchRoot()."))
        );
        // An added override on a known existing class is still a global
        // dispatch delta, even when its parent list and caller edges match.
        let (base, bg) = hierarchy_member_fixture(0, None, false, true, false);
        let (head, hg) = hierarchy_fixture(0, None, true, true);
        assert!(base.find_symbol("p/Child#f().").is_none());
        let seeds = changed_seeds(&base, &bg, &head, &hg, &[]).unwrap();
        assert!(
            seeds
                .base
                .contains(&named_node(&base, &bg, "p/dispatchRoot()."))
        );
        assert!(
            seeds
                .head
                .contains(&named_node(&head, &hg, "p/dispatchUnknown()."))
        );
    }

    fn add_test_body(
        facts: &mut FactSnapshot,
        graph: &mut ProgramGraph,
        name: &str,
        hash: u8,
        ops: &[(Opcode, SymbolId, ValueId, ValueId)],
    ) -> OperationId {
        let symbol = facts.find_symbol(name).unwrap();
        let node = graph.node_for_symbol(symbol).unwrap();
        let body = BodyId(facts.bodies.len() as u32);
        let start = facts.operations.len() as u32;
        for &(opcode, target, dest, a) in ops {
            facts.operations.push(selector_facts::OperationRecord {
                body,
                opcode,
                target,
                dest,
                a,
                b: ValueId::NONE,
                arguments: IdRange::default(),
                span: Span::default(),
                flags: 0,
            });
        }
        facts.bodies.push(BodyRecord {
            symbol,
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange {
                start,
                len: ops.len() as u32,
            },
            parameters: IdRange::default(),
            body_hash: ContentHash([hash; 32]),
            flags: BODY_DEFERRED,
        });
        graph.nodes[node.index()].body = body;
        OperationId(start)
    }

    #[test]
    fn object_get_class_does_not_inherit_unrelated_dispatch_invalidation() {
        fn scenario(child_parent: u32, call_hash: u8, exact: bool) -> (FactSnapshot, ProgramGraph) {
            let (mut facts, mut graph) = hierarchy_construction_fixture(child_parent, None, false);
            for (old, new) in [
                ("p/Root#", "java/lang/Object#"),
                ("p/Root#f().", "java/lang/Object#getClass()."),
            ] {
                let symbol = facts.find_symbol(old).unwrap();
                let id = StrId(facts.strings.entries.len() as u32);
                facts.strings.entries.push(selector_facts::TextRange {
                    start: facts.strings.bytes.len() as u64,
                    len: new.len() as u32,
                });
                facts.strings.bytes.extend_from_slice(new.as_bytes());
                facts.symbols[symbol.index()].name = id;
            }
            let method = facts.find_symbol("java/lang/Object#getClass().").unwrap();
            let caller = named_node(&facts, &graph, "p/dispatchRoot().");
            let op = add_test_body(
                &mut facts,
                &mut graph,
                "p/dispatchRoot().",
                call_hash,
                &[(Opcode::VirtualCall, method, ValueId(1), ValueId(0))],
            );
            let edge = graph.edges.iter_mut().find(|e| e.source == caller).unwrap();
            if exact {
                edge.operation = op;
            }
            graph.index().unwrap();
            (facts, graph)
        }
        for (exact, call_changed) in [(true, false), (false, false), (true, true)] {
            let (base, bg) = scenario(0, 1, exact);
            let (head, hg) = scenario(4, if call_changed { 2 } else { 1 }, exact);
            let seeds = changed_seeds(&base, &bg, &head, &hg, &[]).unwrap();
            for (facts, graph, execution, compilation) in [
                (&base, &bg, &seeds.base, &seeds.base_compile),
                (&head, &hg, &seeds.head, &seeds.head_compile),
            ] {
                assert_eq!(
                    execution.contains(&named_node(facts, graph, "p/dispatchRoot().")),
                    !exact || call_changed
                );
                assert!(execution.contains(&named_node(facts, graph, "p/dispatchUnknown().")));
                assert!(execution.contains(&named_node(facts, graph, "p/constructChild().")));
                assert!(compilation.contains(&named_node(facts, graph, "p/Child#")));
            }
        }
    }

    #[test]
    fn exact_final_scala_dispatch_skips_only_shape_invalidation() {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        enum Control {
            FinalMethod,
            FinalClass,
            Overridable,
            MissingOperation,
            UnverifiedSource,
            DifferentContext,
            Trait,
            CallerEdit,
            Super,
            AlternateTarget,
        }
        use Control::*;
        fn scenario(change_parent: bool, control: Control) -> (FactSnapshot, ProgramGraph) {
            let (mut facts, mut graph) =
                hierarchy_construction_fixture(0, change_parent.then_some(4), false);
            let context = facts.files[0].path;
            facts.files[0].context = context;
            for declaration in &mut facts.symbols {
                declaration.context = context;
            }
            let method = facts.find_symbol("p/Root#f().").unwrap();
            let root = facts.find_symbol("p/Root#").unwrap();
            facts.symbols[root.index()].flags |= SYMBOL_SCALA_PARENTS_COMPLETE;
            if control == FinalClass {
                facts.symbols[root.index()].properties |= 8;
                facts.relations.retain(|r| r.target != root);
            } else if control != Overridable {
                facts.symbols[method.index()].properties |= 8;
            }
            let caller = named_node(&facts, &graph, "p/dispatchRoot().");
            let op = add_test_body(
                &mut facts,
                &mut graph,
                "p/dispatchRoot().",
                if control == CallerEdit && change_parent {
                    2
                } else {
                    1
                },
                &[(Opcode::VirtualCall, method, ValueId(1), ValueId(0))],
            );
            let edge = graph.edges.iter_mut().find(|e| e.source == caller).unwrap();
            if control != MissingOperation {
                edge.operation = op;
            }
            match control {
                UnverifiedSource => facts.files[0].flags &= !SYNTAX_VERIFIED,
                DifferentContext => {
                    let mut file = facts.files[0];
                    file.context = file.source;
                    facts.bodies[facts.operations[op.index()].body.index()].file = FileId(1);
                    facts.files.push(file);
                }
                Trait => facts.symbols[root.index()].kind = 14,
                Super => facts.operations[op.index()].flags |= OP_SUPER,
                AlternateTarget => {
                    let alternate = *edge;
                    let other = facts.find_symbol("p/Other#").unwrap();
                    graph.edges.push(EdgeRecord {
                        target: named_node(&facts, &graph, "p/Other#f()."),
                        receiver: other,
                        ..alternate
                    });
                }
                _ => {}
            }
            graph.index().unwrap();
            (facts, graph)
        }
        for control in [
            FinalMethod,
            FinalClass,
            Overridable,
            MissingOperation,
            UnverifiedSource,
            DifferentContext,
            Trait,
            CallerEdit,
            Super,
            AlternateTarget,
        ] {
            let (base, bg) = scenario(false, control);
            let (head, hg) = scenario(true, control);
            let seeds = changed_seeds(&base, &bg, &head, &hg, &[]).unwrap();
            let caller = named_node(&base, &bg, "p/dispatchRoot().");
            let affected = !matches!(control, FinalMethod | FinalClass);
            assert_eq!(seeds.base.contains(&caller), affected, "{control:?}");
            assert_eq!(seeds.head.contains(&caller), affected, "{control:?}");
            assert!(
                seeds
                    .base
                    .contains(&named_node(&base, &bg, "p/dispatchUnknown()."))
            );
        }
    }

    #[test]
    fn new_subtype_factory_flow_still_affects_an_unchanged_consumer() {
        let (mut base, mut bg) = hierarchy_fixture(0, None, false, false);
        let (mut head, mut hg) = hierarchy_fixture(0, None, true, true);
        for (facts, graph, new_class) in [(&mut base, &mut bg, false), (&mut head, &mut hg, true)] {
            let child = facts.find_symbol("p/Child#").unwrap_or(SymbolId::NONE);
            let factory = facts.find_symbol("p/constructChild().").unwrap();
            let operation = add_test_body(
                facts,
                graph,
                "p/constructChild().",
                if new_class { 2 } else { 1 },
                &[(
                    if new_class {
                        Opcode::Allocate
                    } else {
                        Opcode::Constant
                    },
                    child,
                    ValueId(1),
                    ValueId::NONE,
                )],
            );
            if new_class {
                let node = graph.node_for_symbol(factory).unwrap();
                for edge in graph.edges.iter_mut().filter(|e| e.source == node) {
                    edge.operation = operation;
                }
            }
            let call = add_test_body(
                facts,
                graph,
                "p/dispatchRoot().",
                1,
                &[(Opcode::Call, factory, ValueId(1), ValueId::NONE)],
            );
            graph.edges.push(EdgeRecord {
                source: named_node(facts, graph, "p/dispatchRoot()."),
                target: graph.node_for_symbol(factory).unwrap(),
                kind: EdgeKind::Call,
                occurrence: OccurrenceId::NONE,
                operation: call,
                receiver: SymbolId::NONE,
                flags: 0,
            });
            graph.index().unwrap();
        }
        let seeds = changed_seeds(&base, &bg, &head, &hg, &[]).unwrap();
        for (facts, graph, seeds) in [(&base, &bg, &seeds.base), (&head, &hg, &seeds.head)] {
            let consumer = named_node(facts, graph, "p/dispatchRoot().");
            assert!(!seeds.contains(&consumer));
            let run = selector_solve::analyze(
                facts,
                graph,
                seeds,
                &selector_solve::SolveOptions {
                    workers: 1,
                    execution_roots: Some(
                        vec![selector_solve::ExecutionRoot {
                            node: consumer,
                            receiver: facts.find_symbol("p/Root#").unwrap(),
                        }]
                        .into(),
                    ),
                    ..Default::default()
                },
            )
            .unwrap();
            assert!(
                run.affected.contains(&consumer),
                "changed factory flow must reach the consumer"
            );
        }
    }

    #[test]
    fn new_subtype_does_not_remove_unknown_receiver_guard() {
        let (mut base, mut bg) = hierarchy_fixture(0, None, false, false);
        let (mut head, mut hg) = hierarchy_fixture(0, None, true, true);
        for (facts, graph) in [(&mut base, &mut bg), (&mut head, &mut hg)] {
            let target = facts.find_symbol("p/Root#f().").unwrap();
            add_test_body(
                facts,
                graph,
                "p/Root#f().",
                1,
                &[
                    (Opcode::Constant, SymbolId::NONE, ValueId(1), ValueId::NONE),
                    (Opcode::Return, SymbolId::NONE, ValueId::NONE, ValueId(1)),
                ],
            );
            let op = add_test_body(
                facts,
                graph,
                "p/dispatchUnknown().",
                1,
                &[
                    (Opcode::Unknown, SymbolId::NONE, ValueId(1), ValueId::NONE),
                    (Opcode::VirtualCall, target, ValueId(2), ValueId(1)),
                ],
            );
            let node = named_node(facts, graph, "p/dispatchUnknown().");
            for edge in graph.edges.iter_mut().filter(|e| e.source == node) {
                edge.operation = OperationId(op.0 + 1);
            }
            graph.index().unwrap();
        }
        let seeds = changed_seeds(&base, &bg, &head, &hg, &[]).unwrap();
        for (facts, graph, seeds) in [(&base, &bg, &seeds.base), (&head, &hg, &seeds.head)] {
            let root = named_node(facts, graph, "p/dispatchUnknown().");
            assert!(!seeds.contains(&root));
            let run = selector_solve::analyze(
                facts,
                graph,
                seeds,
                &selector_solve::SolveOptions {
                    workers: 1,
                    execution_roots: Some(
                        vec![selector_solve::ExecutionRoot {
                            node: root,
                            receiver: facts.find_symbol("p/Root#").unwrap(),
                        }]
                        .into(),
                    ),
                    ..Default::default()
                },
            )
            .unwrap();
            assert!(run.guarded_roots.contains(&root));
            assert!(
                run.obligations
                    .iter()
                    .any(|o| o.kind == IssueKind::UnknownExecution)
            );
        }
    }

    #[test]
    fn discovery_of_existing_class_and_changed_discovery_flags_seed_the_suite_root() {
        let (mut base, bg) = fixture();
        let (mut head, hg) = fixture();
        base.suites.clear();
        let seeds = changed_seeds(&base, &bg, &head, &hg, &[]).unwrap();
        assert_eq!(seeds.head, vec![NodeId(0)]);
        assert!(seeds.base.is_empty());
        base.suites.push(head.suites[0]);
        head.suites[0].flags = 1;
        let seeds = changed_seeds(&base, &bg, &head, &hg, &[]).unwrap();
        assert_eq!(seeds.head, vec![NodeId(0)]);
    }
    #[test]
    fn contextual_collision_error_identifies_both_compiler_records() {
        let (mut facts, _) = fixture();
        let mut duplicate = facts.symbols[0];
        duplicate.file = FileId::NONE;
        facts.symbols.push(duplicate);
        let message = symbols(&facts).unwrap_err().to_string();
        assert!(message.contains("p/Suite#"));
        assert!(message.contains("test:scala-2.13"));
        assert!(message.contains("symbol 0 file 0 \"Suite.scala\""));
        assert!(message.contains("symbol 4 file 4294967295"));
    }
    #[test]
    fn ordered_scala_parent_reorder_and_provenance_change_invalidate_dispatch() {
        fn shape(parents: &[u32], complete: bool) -> (FactSnapshot, ProgramGraph) {
            let mut b = FactBuilder::new();
            let path = b.intern("D.scala").unwrap();
            let source = b
                .intern("class Base; trait A; trait B; class D extends Base with A with B")
                .unwrap();
            b.facts.files.push(FileRecord {
                path,
                source,
                revision: StrId::NONE,
                context: StrId::NONE,
                source_hash: ContentHash::default(),
                flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
            });
            for name in [
                "p/D#",
                "p/Base#",
                "p/A#",
                "p/B#",
                "p/Caller#run().",
                "p/D#f().",
            ] {
                let id = b.ensure_symbol(name, FileId(0)).unwrap();
                b.facts.symbols[id.index()].file = FileId(0);
                b.facts.symbols[id.index()].flags = SYMBOL_DEFINED;
            }
            if complete {
                b.facts.symbols[0].flags |= SYMBOL_SCALA_PARENTS_COMPLETE;
            }
            b.facts.symbols[5].owner = SymbolId(0);
            for parent in parents {
                b.facts.relations.push(selector_facts::RelationRecord {
                    source: SymbolId(0),
                    target: SymbolId(*parent),
                    kind: RelationKind::Parent,
                    file: FileId(0),
                });
            }
            b.facts.relations.push(selector_facts::RelationRecord {
                source: SymbolId(2),
                target: SymbolId(1),
                kind: RelationKind::Parent,
                file: FileId(0),
            });
            let facts = b.finish().unwrap();
            let mut graph = ProgramGraph {
                facts_identity: facts.identity,
                ..Default::default()
            };
            for i in 0..facts.symbols.len() {
                graph.nodes.push(NodeRecord {
                    symbol: SymbolId(i as u32),
                    file: FileId(0),
                    body: BodyId::NONE,
                    flags: 0,
                });
                graph.symbol_nodes.push(NodeId(i as u32));
            }
            graph.edges.push(EdgeRecord {
                source: NodeId(4),
                target: NodeId(5),
                kind: EdgeKind::VirtualCall,
                occurrence: OccurrenceId::NONE,
                operation: OperationId::NONE,
                receiver: SymbolId(0),
                flags: 0,
            });
            graph.index().unwrap();
            (facts, graph)
        }
        let (base, bg) = shape(&[1, 2, 3], true);
        let (head, hg) = shape(&[1, 3, 2], true);
        let seeds = changed_seeds(&base, &bg, &head, &hg, &[]).unwrap();
        assert_eq!(seeds.base, vec![NodeId(4)]);
        assert_eq!(seeds.head, vec![NodeId(4)]);
        let (head, hg) = shape(&[1, 2, 3], false);
        let seeds = changed_seeds(&base, &bg, &head, &hg, &[]).unwrap();
        assert_eq!(seeds.base, vec![NodeId(4)]);
        assert_eq!(seeds.head, vec![NodeId(4)]);
        let (mut head, hg) = shape(&[1, 2, 3], true);
        let other = head.relations.pop().unwrap();
        head.relations.insert(1, other);
        let seeds = changed_seeds(&base, &bg, &head, &hg, &[]).unwrap();
        assert!(seeds.base.is_empty());
        assert!(seeds.head.is_empty());
    }

    #[test]
    fn numeric_ranks_preserve_permuted_unicode_context_and_local_identities() {
        fn snapshot(order: &[usize], changed: bool) -> (FactSnapshot, ProgramGraph) {
            let mut b = FactBuilder::new();
            let prefix = "包/長い名前空間/".repeat(64);
            let names = [
                format!("{prefix}型#"),
                format!("{prefix}型."),
                format!("{prefix}型#`長い.名`(+1)."),
                format!("{prefix}型#`長い.名`(+2)."),
                format!("{prefix}型#"),
                "local12".to_owned(),
                "local12".to_owned(),
                format!("{prefix}特性#"),
                format!("{prefix}新しい型#"),
            ];
            let context = "コンパイル設定:test:scala-2.13/".repeat(64);
            for (path, context) in [
                ("日本語/一.scala", context.clone()),
                ("日本語/二.scala", context.clone()),
                ("日本語/一.scala", format!("{context}別設定")),
            ] {
                let path = b.intern(path).unwrap();
                let context = b.intern(&context).unwrap();
                let source = b.intern("class 型 { def f = 1 }").unwrap();
                b.facts.files.push(FileRecord {
                    path,
                    context,
                    source,
                    revision: StrId::NONE,
                    source_hash: ContentHash([1; 32]),
                    flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
                });
            }
            let file = |logical| {
                FileId(if logical == 4 {
                    2
                } else if logical == 6 {
                    1
                } else {
                    0
                })
            };
            let mut ids = [SymbolId::NONE; 9];
            for &logical in order {
                let id = b.ensure_symbol(&names[logical], file(logical)).unwrap();
                ids[logical] = id;
                b.facts.symbols[id.index()].file = file(logical);
                b.facts.symbols[id.index()].flags = SYMBOL_DEFINED;
            }
            for (logical, owner) in [(2, 0), (3, 1), (5, 0), (6, 0)] {
                b.facts.symbols[ids[logical].index()].owner = ids[owner];
            }
            for logical in [2, 3] {
                b.facts.bodies.push(BodyRecord {
                    symbol: ids[logical],
                    file: file(logical),
                    span: Span::default(),
                    name_span: Span::default(),
                    operations: IdRange::default(),
                    parameters: IdRange::default(),
                    body_hash: ContentHash([if changed && logical == 2 { 2 } else { 1 }; 32]),
                    flags: BODY_DEFERRED,
                });
            }
            for (source, target, kind) in
                [(0, 7, RelationKind::Parent), (2, 3, RelationKind::Override)]
            {
                b.facts.relations.push(selector_facts::RelationRecord {
                    source: ids[source],
                    target: ids[target],
                    kind,
                    file: file(source),
                });
            }
            let name = b.intern("日本語.型Suite").unwrap();
            b.facts.suites.push(SuiteRecord {
                name,
                symbol: ids[0],
                file: file(0),
                flags: 0,
            });
            let facts = b.finish().unwrap();
            let mut graph = ProgramGraph {
                facts_identity: facts.identity,
                ..Default::default()
            };
            for (i, symbol) in facts.symbols.iter().enumerate() {
                graph.nodes.push(NodeRecord {
                    symbol: SymbolId(i as u32),
                    file: symbol.file,
                    body: if SymbolId(i as u32) == ids[2] {
                        BodyId(0)
                    } else if SymbolId(i as u32) == ids[3] {
                        BodyId(1)
                    } else {
                        BodyId::NONE
                    },
                    flags: 0,
                });
                graph.symbol_nodes.push(NodeId(i as u32));
            }
            for (source, target, receiver, kind, flags) in [
                (0, 1, SymbolId::NONE, EdgeKind::Compile, u32::from(changed)),
                (
                    3,
                    if changed { 6 } else { 5 },
                    ids[0],
                    EdgeKind::Callback,
                    0,
                ),
                (4, 2, ids[4], EdgeKind::VirtualCall, 0),
            ] {
                graph.edges.push(EdgeRecord {
                    source: NodeId(ids[source].0),
                    target: NodeId(ids[target].0),
                    receiver,
                    kind,
                    flags,
                    occurrence: OccurrenceId::NONE,
                    operation: OperationId::NONE,
                });
            }
            graph.index().unwrap();
            (facts, graph)
        }
        fn identities(
            facts: &FactSnapshot,
            graph: &ProgramGraph,
            nodes: &[NodeId],
        ) -> Vec<(String, String, String)> {
            let mut result: Vec<_> = nodes
                .iter()
                .map(|node| {
                    let (name, context, path) = symbol_key(facts, graph.nodes[node.index()].symbol);
                    (name.to_owned(), context.to_owned(), path.to_owned())
                })
                .collect();
            result.sort_unstable();
            result
        }
        assert_eq!(std::mem::size_of::<EdgeKey>(), 16);
        let (base, bg) = snapshot(&[0, 1, 2, 3, 4, 5, 6, 7], false);
        let (same, sg) = snapshot(&[6, 3, 7, 0, 4, 1, 5, 2], false);
        let unchanged = changed_seeds(&base, &bg, &same, &sg, &[]).unwrap();
        assert!(unchanged.base.is_empty() && unchanged.head.is_empty());
        assert!(unchanged.base_compile.is_empty() && unchanged.head_compile.is_empty());
        assert!(!unchanged.conservative);

        let (head, hg) = snapshot(&[0, 1, 2, 3, 4, 5, 6, 7, 8], true);
        let (permuted, pg) = snapshot(&[8, 6, 3, 7, 0, 4, 1, 5, 2], true);
        let expected = changed_seeds(&base, &bg, &head, &hg, &[]).unwrap();
        let actual = changed_seeds(&base, &bg, &permuted, &pg, &[]).unwrap();
        assert_eq!(expected.base, vec![NodeId(2), NodeId(3)]);
        assert_eq!(expected.base_compile, vec![NodeId(0)]);
        assert_eq!(expected.head_compile, vec![NodeId(0), NodeId(8)]);
        assert_eq!(actual.base, expected.base);
        assert_eq!(actual.base_compile, expected.base_compile);
        assert_eq!(
            identities(&permuted, &pg, &actual.head),
            identities(&head, &hg, &expected.head)
        );
        assert_eq!(
            identities(&permuted, &pg, &actual.head_compile),
            identities(&head, &hg, &expected.head_compile)
        );
        assert_eq!(actual.conservative, expected.conservative);
        assert!(actual.base_obligations.is_empty() && actual.head_obligations.is_empty());
    }
}

#[cfg(test)]
#[path = "heap_reader_retention_tests.rs"]
mod heap_reader_retention_tests;
