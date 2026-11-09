//! Versioned runtime contracts over compiler identities, never source spelling.
pub mod binary;
pub mod binary_jdk;
pub mod runtime;
pub mod runtime_routes;
pub mod runtime_schema;
use selector_facts::{BodyRecord, FactSnapshot, SuiteRecord};
use selector_graph::{EdgeRecord, GraphIssue};
use selector_types::*;

pub const MODEL_VERSION: &str = "scala-runtime-models/4:explicit-constructor-entry:declared-java21-primitive-data";
pub const FRAMEWORK_MODEL_VERSION: &str = selector_framework::VERSION;

/// Enter ordinary eager scopes through their owner. Constructor overloads are
/// callable entry points; their receiver and arguments belong to the actual
/// construction call, not to a blanket class initialization fanout.
pub fn implicit_initializer(facts: &FactSnapshot, body: &BodyRecord) -> bool {
    body.flags & BODY_INITIALIZER != 0
        && body.flags & (BODY_LAZY | BODY_DEFERRED) == 0
        && facts.symbols[body.symbol.index()].kind != 21
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CallbackBehavior {
    None,
    Immediate,
    Deferred,
    TestRegistration,
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExternalContract {
    pub callbacks: CallbackBehavior,
    pub effects_complete: bool,
}

/// Selects a contract family, while exact overload identities remain untouched.
fn member_name(symbol: &str) -> &str {
    selector_types::symbol::member_name(symbol).unwrap_or("")
}

pub fn classify_external(symbol: &str) -> ExternalContract {
    let member = member_name(symbol);
    let registration = symbol.starts_with("org/scalatest/")
        && matches!(
            member,
            "test"
                | "ignore"
                | "registerTest"
                | "registerIgnoredTest"
                | "in"
                | "is"
                | "it"
                | "they"
                | "property"
                | "scenario"
        );
    let immediate = (symbol.starts_with("scala/collection/")
        || symbol.starts_with("scala/Option#")
        || symbol.starts_with("scala/util/Try#"))
        && matches!(
            member,
            "map"
                | "flatMap"
                | "foreach"
                | "filter"
                | "filterNot"
                | "exists"
                | "forall"
                | "find"
                | "fold"
                | "foldLeft"
                | "foldRight"
                | "collect"
                | "getOrElse"
                | "orElse"
                | "withFilter"
                | "tapEach"
        );
    let framework_scope = selector_framework::scalatest_deferred_argument(symbol)
        .is_some_and(|c| c.kind == selector_framework::ScalaTestCall::Scope);
    let deferred = symbol.starts_with("scala/concurrent/")
        && matches!(
            member,
            "map" | "flatMap" | "foreach" | "onComplete" | "transform" | "transformWith" | "apply"
        );
    let locally = symbol.starts_with("scala/Predef.") && member == "locally";
    let bootstrap = bootstrap_initialization(symbol);
    let value_only = bootstrap
        || (symbol.starts_with("scala/Predef.") && matches!(member, "identity" | "implicitly"))
        || (symbol.starts_with("java/lang/String#")
            && matches!(
                member,
                "length" | "isEmpty" | "charAt" | "equals" | "hashCode"
            ));
    ExternalContract {
        callbacks: if registration {
            CallbackBehavior::TestRegistration
        } else if immediate || locally || framework_scope {
            CallbackBehavior::Immediate
        } else if deferred {
            CallbackBehavior::Deferred
        } else if value_only {
            CallbackBehavior::None
        } else {
            CallbackBehavior::Unknown
        },
        // Callback policy alone never implies a complete library effect summary.
        effects_complete: value_only,
    }
}

/// Bootstrap class loading fixes Object identity independently of user classpath
/// shadowing. No arbitrary ScalaTest/library constructor is declared empty.
pub fn bootstrap_initialization(symbol: &str) -> bool {
    matches!(
        symbol,
        "java/lang/Object#"
            | "scala/AnyRef#"
            | "java/lang/Object#`<init>`()."
            | "java/lang/Object#<init>()."
    )
}

#[derive(Debug, Default)]
pub struct ModelContributions {
    pub edges: Vec<EdgeRecord>,
    pub issues: Vec<GraphIssue>,
}

/// Two flat buffers replace one heap allocation per populated symbol bucket.
struct RelationIndex {
    offsets: Vec<usize>,
    targets: Vec<SymbolId>,
}
impl RelationIndex {
    fn new(facts: &FactSnapshot, kind: RelationKind) -> Self {
        let mut offsets = vec![0; facts.symbols.len() + 1];
        for r in &facts.relations {
            if r.kind == kind {
                offsets[r.source.index() + 1] += 1;
            }
        }
        for i in 1..offsets.len() {
            offsets[i] += offsets[i - 1];
        }
        let mut targets = vec![SymbolId::NONE; *offsets.last().unwrap()];
        let mut cursors = offsets[..facts.symbols.len()].to_vec();
        for r in &facts.relations {
            if r.kind == kind {
                targets[cursors[r.source.index()]] = r.target;
                cursors[r.source.index()] += 1;
            }
        }
        Self { offsets, targets }
    }
    fn get(&self, symbol: SymbolId) -> &[SymbolId] {
        &self.targets[self.offsets[symbol.index()]..self.offsets[symbol.index() + 1]]
    }
}

fn fixture_contract(symbol: &str) -> bool {
    symbol.starts_with("org/scalatest/")
        && matches!(
            member_name(symbol),
            "beforeEach"
                | "afterEach"
                | "beforeAll"
                | "afterAll"
                | "withFixture"
                | "run"
                | "runTest"
                | "runTests"
                | "runNestedSuites"
        )
}

/// Suite lifecycle and captured generated/runtime bridge contributions. Workers
/// read immutable facts and emit flat records; no source strings are copied.
pub fn contribute(
    facts: &FactSnapshot,
    symbol_nodes: &[NodeId],
    body_nodes: &[NodeId],
) -> ModelContributions {
    let model = PreparedModels::new(facts, symbol_nodes, body_nodes);
    let mut out = ModelContributions::default();
    model.contribute_bridges(&mut out);
    model.contribute_suites(&facts.suites, &mut ModelScratch::default(), &mut out);
    out
}

/// Shared once per graph build, then borrowed by independent suite partitions.
/// Index memory is O(symbols + relations + bodies), not O(workers * symbols).
pub struct PreparedModels<'a> {
    facts: &'a FactSnapshot,
    symbol_nodes: &'a [NodeId],
    body_nodes: &'a [NodeId],
    parents: RelationIndex,
    overrides: RelationIndex,
    owned_bodies: Vec<(SymbolId, BodyId)>,
}
#[derive(Default)]
pub struct ModelScratch {
    seen: std::collections::HashSet<SymbolId>,
    overridden: std::collections::HashSet<SymbolId>,
    visited: std::collections::HashSet<SymbolId>,
    stack: Vec<SymbolId>,
    ancestry: Vec<SymbolId>,
    pending: Vec<SymbolId>,
}
impl<'a> PreparedModels<'a> {
    pub fn new(
        facts: &'a FactSnapshot,
        symbol_nodes: &'a [NodeId],
        body_nodes: &'a [NodeId],
    ) -> Self {
        let parents = RelationIndex::new(facts, RelationKind::Parent);
        let overrides = RelationIndex::new(facts, RelationKind::Override);
        let mut owned_bodies = Vec::with_capacity(facts.bodies.len());
        for (i, b) in facts.bodies.iter().enumerate() {
            if b.symbol.is_none() {
                continue;
            }
            let s = &facts.symbols[b.symbol.index()];
            let owner = if s.owner.is_none() || matches!(s.kind, 10 | 13 | 14) {
                b.symbol
            } else {
                s.owner
            };
            owned_bodies.push((owner, BodyId(i as u32)));
        }
        owned_bodies.sort_unstable();
        Self {
            facts,
            symbol_nodes,
            body_nodes,
            parents,
            overrides,
            owned_bodies,
        }
    }
    pub fn contribute_bridges(&self, out: &mut ModelContributions) {
        for r in &self.facts.relations {
            if r.kind == RelationKind::RuntimeBridge {
                out.edges.push(edge(
                    self.symbol_nodes[r.source.index()],
                    self.symbol_nodes[r.target.index()],
                    EdgeKind::RuntimeBridge,
                ));
            }
        }
    }
    /// Scratch retains only hierarchy members touched by this partition. It is
    /// cleared between suites and freed after the graph stage completes.
    pub fn contribute_suites(
        &self,
        suites: &[SuiteRecord],
        scratch: &mut ModelScratch,
        out: &mut ModelContributions,
    ) {
        let facts = self.facts;
        let symbol_nodes = self.symbol_nodes;
        let body_nodes = self.body_nodes;
        let parents = &self.parents;
        let overrides = &self.overrides;
        let owned_bodies = &self.owned_bodies;
        let ModelScratch {
            seen,
            overridden,
            visited,
            stack,
            ancestry,
            pending,
        } = scratch;
        for suite in suites {
            if suite.symbol.is_none() {
                continue;
            }
            seen.clear();
            overridden.clear();
            stack.clear();
            ancestry.clear();
            stack.push(suite.symbol);
            let mut scalatest = false;
            while let Some(s) = stack.pop() {
                if !seen.insert(s) {
                    continue;
                }
                scalatest |= facts.symbol_name(s).starts_with("org/scalatest/");
                ancestry.push(s);
                stack.extend(parents.get(s).iter().copied());
            }
            let root = symbol_nodes[suite.symbol.index()];
            if !scalatest {
                out.issues.push(GraphIssue {
                    kind: IssueKind::UnsupportedModel,
                    node: root,
                    file: suite.file,
                    symbol: suite.symbol,
                    detail: StrId::NONE,
                });
            }
            // More specific compiler overrides hide ancestor fixture bodies. Super
            // calls remain ordinary explicit call operations in the overriding body.
            for &ancestor in ancestry.iter() {
                let start = owned_bodies.partition_point(|&(owner, _)| owner < ancestor);
                let end = owned_bodies.partition_point(|&(owner, _)| owner <= ancestor);
                if facts.symbols[ancestor.index()].flags & SYMBOL_DEFINED != 0
                    && !owned_bodies[start..end].iter().any(|&(_, bid)| {
                        let b = &facts.bodies[bid.index()];
                        b.symbol == ancestor && implicit_initializer(facts, b)
                    })
                {
                    out.issues.push(GraphIssue {
                        kind: IssueKind::MissingSyntax,
                        node: root,
                        file: suite.file,
                        symbol: ancestor,
                        detail: StrId::NONE,
                    });
                }
                for &(_, bid) in &owned_bodies[start..end] {
                    let symbol = facts.bodies[bid.index()].symbol;
                    pending.clear();
                    pending.extend(overrides.get(symbol).iter().copied());
                    while let Some(target) = pending.pop() {
                        if !overridden.insert(target) {
                            continue;
                        }
                        pending.extend(overrides.get(target).iter().copied());
                    }
                }
            }
            // Instantiation runs ancestor initialization, never every method, lazy
            // member or uninvoked closure in the containing class.
            for &ancestor in ancestry.iter() {
                let start = owned_bodies.partition_point(|&(owner, _)| owner < ancestor);
                let end = owned_bodies.partition_point(|&(owner, _)| owner <= ancestor);
                for &(_, bid) in &owned_bodies[start..end] {
                    let body = &facts.bodies[bid.index()];
                    if implicit_initializer(facts, body) {
                        out.edges
                            .push(edge(root, body_nodes[bid.index()], EdgeKind::Initialize));
                    }
                    if !scalatest || body.symbol.is_none() || overridden.contains(&body.symbol) {
                        continue;
                    }
                    pending.clear();
                    visited.clear();
                    pending.extend(overrides.get(body.symbol).iter().copied());
                    let mut fixture = fixture_contract(facts.symbol_name(body.symbol));
                    while let Some(target) = pending.pop() {
                        if !visited.insert(target) {
                            continue;
                        }
                        fixture |= fixture_contract(facts.symbol_name(target));
                        pending.extend(overrides.get(target).iter().copied());
                    }
                    if fixture {
                        out.edges
                            .push(edge(root, body_nodes[bid.index()], EdgeKind::Fixture));
                    }
                }
            }
        }
    }
}

fn edge(source: NodeId, target: NodeId, kind: EdgeKind) -> EdgeRecord {
    EdgeRecord {
        source,
        target,
        kind,
        occurrence: OccurrenceId::NONE,
        operation: OperationId::NONE,
        receiver: SymbolId::NONE,
        flags: 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn runtime_contracts_require_compiler_names() {
        assert_eq!(
            classify_external("scala/collection/IterableOnceOps#foreach().").callbacks,
            CallbackBehavior::Immediate
        );
        assert_eq!(
            classify_external("example/IterableOnceOps#foreach().").callbacks,
            CallbackBehavior::Unknown
        );
        assert_eq!(
            classify_external("org/scalatest/funsuite/AnyFunSuiteLike#test().").callbacks,
            CallbackBehavior::TestRegistration
        );
        assert!(!classify_external("scala/collection/IterableOnceOps#foreach().").effects_complete);
        assert_eq!(
            classify_external("scala/concurrent/Future.apply().").callbacks,
            CallbackBehavior::Deferred
        );
        assert_eq!(
            classify_external("scala/Predef.identity().").callbacks,
            CallbackBehavior::None
        );
    }
}
