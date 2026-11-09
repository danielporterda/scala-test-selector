//! Conditional absence of requested source products from owning test classpaths.
//!
//! This proof does not close execution, callbacks, heap effects or JVM behavior.
//! Its producer must verify complete source-to-product ownership and scan every
//! effective classpath provider, including alternate/MR entries, for those
//! products. The explicit owning-Test/fullClasspath contract excludes hidden
//! runtime providers. Existing declared-input contracts cover compiler/build inputs
//! and ordinary code generation; unrecorded source generators reading arbitrary
//! unrelated inputs are unsupported. Available native/resource/generated change
//! seeds are never waived.
//! Missing producer evidence is never an empty product set or an absence proof.
use crate::PlanSeeds;
use selector_facts::FactSnapshot;
use selector_graph::ProgramGraph;
use selector_types::*;
use sha2::{Digest, Sha256};

pub const VERSION: &str = "selector-classpath-absence/5";
pub const REQUIRED_CONTRACT_BITS: u32 = SelectionContract::CURRENT_BASE_BITS
    | SelectionContract::SUITE_INDEPENDENCE
    | SelectionContract::OWNING_TEST_CLASSPATH;

/// Exact requested scope, including visible out-of-scope physical deltas. The
/// latter are report qualifiers, never effective changes covered by this proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceScope {
    pub requested_paths: Vec<String>,
    pub outside_count: u64,
    pub outside: Vec<(FileId, FileId)>,
}

/// An independently verified complete product inventory for one contextual
/// source record. A digest binds actual product names, bytes and ownership.
/// Additional verified source records may widen the absence proof to cover
/// effective compiler/runtime seeds; they never remove requested source inputs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceProduct {
    pub file: FileId,
    pub owner_context: StrId,
    pub products_identity: ContentHash,
    pub product_count: u32,
}

/// The producer verified a one-sided source's absence in the captured source
/// roster and checkout, ruled out stale output, and checked the other side's
/// verified product names against this side's providers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AbsentSource {
    pub path: String,
    pub opposite_facts: ContentHash,
    pub absence_identity: ContentHash,
}

/// Exact binary fact file positively attributed to a requested source. The
/// independent issuer verifies unique compiler SourceFile attribution, owning
/// exported-product path/inventory and bytes; unknown attribution grants no row.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProductFile {
    pub file: FileId,
    pub source_file: FileId,
    pub owner_context: StrId,
    pub class_sha256: ContentHash,
}

/// Independently verified stable ordinary compilation for an extra source.
/// Identities bind the paired source/compiler input closure, not byte-for-byte
/// output equality. Only the explicit ordinary-compilation contract gives this
/// functional interpretation. Requested sources always require runtime absence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StableCompilation {
    pub file: FileId,
    pub owner_context: StrId,
    pub source_sha256: ContentHash,
    pub inputs_identity: ContentHash,
    pub paired_identity: ContentHash,
}

/// A producer's positive proof that every requested source product is absent
/// from this exact catalogue suite's owning captured Test/fullClasspath.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SuiteClasspath {
    pub suite: SuiteId,
    pub owner_context: StrId,
    pub classpath_identity: ContentHash,
    pub source_products_identity: ContentHash,
    pub absence_identity: ContentHash,
}

/// Borrowed output of an independently verified provider/product issuer. These
/// are a producer trust boundary, not untrusted report JSON. The issuer must
/// bind capture, classpath, product ownership, all-provider scan and policy
/// content in `identity`. This module checks contextual geometry and seals the
/// exact records; it cannot discover missing products from a digest alone.
#[derive(Clone, Copy)]
pub struct Evidence<'a> {
    pub identity: ContentHash,
    pub facts_identity: ContentHash,
    pub capture_identity: ContentHash,
    pub runtime_contract_identity: ContentHash,
    pub source_products_identity: ContentHash,
    pub sources: &'a [SourceProduct],
    pub product_files: &'a [ProductFile],
    pub stable_compilation: &'a [StableCompilation],
    pub suites: &'a [SuiteClasspath],
}

#[derive(Clone, Copy)]
pub struct Side<'a> {
    pub facts: &'a FactSnapshot,
    pub graph: &'a ProgramGraph,
    pub seeds: PlanSeeds<'a>,
    pub evidence: Evidence<'a>,
}

#[derive(Clone, Debug)]
struct SideSeal {
    facts: ContentHash,
    graph: ContentHash,
    issuer: ContentHash,
    capture: ContentHash,
    runtime: ContentHash,
    products: ContentHash,
    execution: Vec<NodeId>,
    declarations: Vec<NodeId>,
    sources: Vec<SourceProduct>,
    absent_sources: Vec<AbsentSource>,
    product_files: Vec<ProductFile>,
    stable_compilation: Vec<StableCompilation>,
    suites: Vec<CertifiedRoot>,
}

#[derive(Clone, Copy, Debug)]
struct CertifiedRoot {
    suite: SuiteId,
    root: NodeId,
    symbol: SymbolId,
    file: FileId,
    context: StrId,
    classpath: ContentHash,
    absence: ContentHash,
}

/// Immutable paired proof. Public input mutations and stale snapshot/seed/scope
/// reuse are rejected before any conditional exclusion can be consumed.
#[derive(Debug)]
pub struct Plan {
    contract: SelectionContract,
    scope: SourceScope,
    base: SideSeal,
    head: SideSeal,
    identity: ContentHash,
}

impl Plan {
    pub fn new(
        base: Side<'_>,
        head: Side<'_>,
        scope: SourceScope,
        contract: SelectionContract,
    ) -> Result<Self, Error> {
        Self::new_with_source_absence(base, head, scope, contract, &[], &[])
    }

    pub fn new_with_source_absence(
        base: Side<'_>,
        head: Side<'_>,
        scope: SourceScope,
        contract: SelectionContract,
        base_absent: &[AbsentSource],
        head_absent: &[AbsentSource],
    ) -> Result<Self, Error> {
        if !contract.contains(REQUIRED_CONTRACT_BITS)
            || contract.suite_semantics() != SuiteSemantics::Independent
        {
            return Err(Error::Invalid(
                "classpath absence requires explicit independent owning-test contract",
            ));
        }
        if scope.requested_paths.is_empty()
            || scope.requested_paths.len() > 4096
            || scope.requested_paths.windows(2).any(|p| p[0] >= p[1])
            || scope
                .requested_paths
                .iter()
                .any(|p| p.is_empty() || p.len() > 16384)
            || scope.requested_paths.iter().map(|p| p.len()).sum::<usize>() > 1024 * 1024
            || scope.outside.len() > 64
            || scope.outside.len() as u64 > scope.outside_count
        {
            return Err(Error::Invalid("classpath absence requested source scope"));
        }
        for &(b, h) in &scope.outside {
            if (b.is_none() && h.is_none())
                || (!b.is_none() && b.index() >= base.facts.files.len())
                || (!h.is_none() && h.index() >= head.facts.files.len())
            {
                return Err(Error::Invalid("classpath absence outside-scope file"));
            }
        }
        let mut plan = Self {
            contract,
            base: seal_side(base, &scope, contract, base_absent)?,
            head: seal_side(head, &scope, contract, head_absent)?,
            scope,
            identity: ContentHash::default(),
        };
        for (side, opposite, facts) in [
            (&plan.base, &plan.head, head.facts),
            (&plan.head, &plan.base, base.facts),
        ] {
            if side.absent_sources.iter().any(|row| {
                row.opposite_facts != opposite.facts
                    || !opposite
                        .sources
                        .iter()
                        .any(|present| facts.path(present.file) == row.path)
            }) {
                return Err(Error::Invalid(
                    "classpath absence one-sided product binding",
                ));
            }
        }
        // A suite pair is matched by its immutable compiler identity by the
        // selector. Each side separately binds the exact catalogue and context.
        validate_compilation_pair(&plan.base, &plan.head, base.facts, head.facts)?;
        plan.identity = content_identity(&plan);
        Ok(plan)
    }

    pub fn identity(&self) -> ContentHash {
        self.identity
    }
    pub fn contract(&self) -> SelectionContract {
        self.contract
    }
    pub fn scope(&self) -> &SourceScope {
        &self.scope
    }

    pub fn validate(
        &self,
        base_facts: &FactSnapshot,
        base_graph: &ProgramGraph,
        head_facts: &FactSnapshot,
        head_graph: &ProgramGraph,
        base_seeds: PlanSeeds<'_>,
        head_seeds: PlanSeeds<'_>,
        scope: &SourceScope,
    ) -> Result<(), Error> {
        if content_identity(self) != self.identity || scope != &self.scope {
            return Err(Error::Invalid(
                "classpath absence paired content/scope seal",
            ));
        }
        for (seal, facts, graph, seeds) in [
            (&self.base, base_facts, base_graph, base_seeds),
            (&self.head, head_facts, head_graph, head_seeds),
        ] {
            if facts.identity != seal.facts
                || graph.identity != seal.graph
                || graph.facts_identity != facts.identity
                || seeds.unscoped
                || seeds.execution != seal.execution
                || seeds.declarations != seal.declarations
            {
                return Err(Error::Invalid("classpath absence snapshot/seed seal"));
            }
        }
        Ok(())
    }

    /// None means no proof, including unissued suites and mismatched root IDs.
    pub fn certificate(&self, head: bool, suite: SuiteId, root: NodeId) -> Option<ContentHash> {
        let side = if head { &self.head } else { &self.base };
        let row = side
            .suites
            .binary_search_by_key(&suite, |r| r.suite)
            .ok()
            .map(|i| side.suites[i])?;
        if row.root != root {
            return None;
        }
        let mut hash = Sha256::new();
        hash.update(VERSION);
        hash.update(self.identity.0);
        hash.update([u8::from(head)]);
        hash.update(suite.0.to_le_bytes());
        hash.update(root.0.to_le_bytes());
        Some(ContentHash(hash.finalize().into()))
    }
}

fn nonzero(hash: ContentHash) -> bool {
    hash != ContentHash::default()
}

fn seal_side(
    side: Side<'_>,
    scope: &SourceScope,
    contract: SelectionContract,
    absent_sources: &[AbsentSource],
) -> Result<SideSeal, Error> {
    let Side {
        facts,
        graph,
        seeds,
        evidence,
    } = side;
    facts.validate()?;
    graph.validate()?;
    if graph.facts_identity != facts.identity
        || seeds.unscoped
        || ![
            facts.identity,
            graph.identity,
            evidence.identity,
            evidence.capture_identity,
            evidence.runtime_contract_identity,
            evidence.source_products_identity,
        ]
        .into_iter()
        .all(nonzero)
        || evidence.facts_identity != facts.identity
        || (evidence.sources.is_empty() && absent_sources.is_empty())
        || evidence.sources.len() > 16384
        || evidence.sources.windows(2).any(|p| p[0].file >= p[1].file)
        || evidence.product_files.len() > 65536
        || evidence
            .product_files
            .windows(2)
            .any(|p| p[0].file >= p[1].file)
        || evidence.stable_compilation.len() > 16384
        || evidence
            .stable_compilation
            .windows(2)
            .any(|p| p[0].file >= p[1].file)
        || (!evidence.stable_compilation.is_empty()
            && contract != SelectionContract::owning_test_classpath_with_compilation())
        || evidence.suites.len() > facts.suites.len()
        || evidence.suites.len() > 32768
        || evidence.suites.windows(2).any(|p| p[0].suite >= p[1].suite)
    {
        return Err(Error::Invalid("classpath absence issued evidence"));
    }
    // Every contextual source record for each requested path must be covered.
    // A single convenient owning context is not enough when another product may
    // have been compiled for the same physical source.
    let mut found = vec![false; scope.requested_paths.len()];
    for source in evidence.sources {
        let file = facts
            .files
            .get(source.file.index())
            .ok_or(Error::Invalid("classpath absence source file"))?;
        if file.flags & (SOURCE_VERIFIED | SYNTAX_VERIFIED | FILE_BINARY_SOURCE)
            != SOURCE_VERIFIED | SYNTAX_VERIFIED
            || file.context.is_none()
            || source.owner_context != file.context
            || file.source_hash == ContentHash::default()
            || source.product_count == 0
            || !nonzero(source.products_identity)
        {
            return Err(Error::Invalid("classpath absence source product authority"));
        }
    }
    for (i, file) in facts.files.iter().enumerate() {
        let Ok(path) = scope
            .requested_paths
            .binary_search_by(|p| p.as_str().cmp(facts.path(FileId(i as u32))))
        else {
            continue;
        };
        if file.flags & FILE_BINARY_SOURCE != 0 {
            continue;
        }
        found[path] = true;
        let id = FileId::checked(i)?;
        let row = evidence
            .sources
            .binary_search_by_key(&id, |r| r.file)
            .ok()
            .map(|index| evidence.sources[index])
            .ok_or(Error::Invalid("classpath absence missing source ownership"))?;
        if file.flags & (SOURCE_VERIFIED | SYNTAX_VERIFIED) != SOURCE_VERIFIED | SYNTAX_VERIFIED
            || file.context.is_none()
            || row.owner_context != file.context
            || row.product_count == 0
            || !nonzero(row.products_identity)
        {
            return Err(Error::Invalid("classpath absence source product authority"));
        }
    }
    if found.iter().any(|value| !value) {
        if absent_sources.len() > scope.requested_paths.len()
            || absent_sources.windows(2).any(|p| p[0].path >= p[1].path)
        {
            return Err(Error::Invalid("classpath absence source absence rows"));
        }
        for row in absent_sources {
            let index = scope
                .requested_paths
                .binary_search(&row.path)
                .map_err(|_| Error::Invalid("classpath absence unrequested absent source"))?;
            if found[index] || !nonzero(row.absence_identity) || !nonzero(row.opposite_facts) {
                return Err(Error::Invalid("classpath absence source absence authority"));
            }
            found[index] = true;
        }
        if found.iter().any(|value| !value) {
            return Err(Error::Invalid("classpath absence incomplete source scope"));
        }
    } else if !absent_sources.is_empty() {
        return Err(Error::Invalid(
            "classpath absence source absence overlaps present source",
        ));
    }
    for stable in evidence.stable_compilation {
        let file = facts
            .files
            .get(stable.file.index())
            .ok_or(Error::Invalid("stable compilation source file"))?;
        if file.flags & (SOURCE_VERIFIED | SYNTAX_VERIFIED | FILE_BINARY_SOURCE)
            != SOURCE_VERIFIED | SYNTAX_VERIFIED
            || file.context.is_none()
            || file.context != stable.owner_context
            || !nonzero(stable.source_sha256)
            || file.source_hash != stable.source_sha256
            || !nonzero(stable.inputs_identity)
            || !nonzero(stable.paired_identity)
            || scope
                .requested_paths
                .binary_search_by(|path| path.as_str().cmp(facts.path(stable.file)))
                .is_ok()
        {
            return Err(Error::Invalid("stable compilation source authority"));
        }
    }
    for product in evidence.product_files {
        let source = evidence
            .sources
            .binary_search_by_key(&product.source_file, |row| row.file)
            .ok()
            .map(|index| evidence.sources[index])
            .ok_or(Error::Invalid("classpath absence binary product source"))?;
        let file = facts
            .files
            .get(product.file.index())
            .ok_or(Error::Invalid("classpath absence binary product file"))?;
        if file.flags & FILE_BINARY_SOURCE == 0
            || file.context != product.owner_context
            || source.owner_context != product.owner_context
            || !nonzero(product.class_sha256)
            || file.source_hash != product.class_sha256
        {
            return Err(Error::Invalid("classpath absence binary product authority"));
        }
    }
    for nodes in [seeds.execution, seeds.declarations] {
        if nodes.len() > 262144 || nodes.windows(2).any(|p| p[0] >= p[1]) {
            return Err(Error::Invalid("classpath absence seed order"));
        }
        for node in nodes {
            let record = graph
                .nodes
                .get(node.index())
                .ok_or(Error::Invalid("classpath absence seed node"))?;
            let source_seed = evidence
                .sources
                .binary_search_by_key(&record.file, |r| r.file)
                .is_ok()
                && facts
                    .symbols
                    .get(record.symbol.index())
                    .is_some_and(|symbol| {
                        symbol.file == record.file
                            && symbol.context == facts.files[record.file.index()].context
                    });
            let product_seed = evidence
                .product_files
                .binary_search_by_key(&record.file, |r| r.file)
                .ok()
                .is_some_and(|index| {
                    let product = evidence.product_files[index];
                    facts
                        .symbols
                        .get(record.symbol.index())
                        .is_some_and(|symbol| {
                            if symbol.context != product.owner_context {
                                return false;
                            }
                            if symbol.file == product.file || symbol.file == product.source_file {
                                return true;
                            }
                            // Duplicate binary views may identify the same admitted
                            // class; another class or context is never an alias.
                            evidence
                                .product_files
                                .binary_search_by_key(&symbol.file, |row| row.file)
                                .ok()
                                .is_some_and(|other| {
                                    let alias = evidence.product_files[other];
                                    alias.source_file == product.source_file
                                        && alias.owner_context == product.owner_context
                                        && alias.class_sha256 == product.class_sha256
                                })
                        })
                });
            let stable_seed = evidence
                .stable_compilation
                .binary_search_by_key(&record.file, |row| row.file)
                .ok()
                .is_some_and(|index| {
                    let stable = evidence.stable_compilation[index];
                    facts
                        .symbols
                        .get(record.symbol.index())
                        .is_some_and(|symbol| {
                            symbol.file == stable.file && symbol.context == stable.owner_context
                        })
                });
            if !source_seed && !product_seed && !stable_seed {
                let file = facts.files.get(record.file.index());
                let symbol = facts.symbols.get(record.symbol.index());
                let bounded = |text: &str| text.chars().take(256).collect::<String>();
                return Err(Error::Message(format!(
                    "classpath absence extra effective input seed: node={} node_file={} path={:?} symbol={} symbol_file={} symbol_context={:?} file_context={:?}",
                    node.0,
                    record.file.0,
                    bounded(file.map_or("<none>", |file| facts.text(file.path))),
                    record.symbol.0,
                    symbol.map_or(FileId::NONE.0, |symbol| symbol.file.0),
                    bounded(symbol.map_or("<none>", |symbol| facts.text(symbol.context))),
                    bounded(file.map_or("<none>", |file| facts.text(file.context))),
                )));
            }
        }
    }
    let mut suites = Vec::with_capacity(evidence.suites.len());
    for row in evidence.suites {
        let suite = facts
            .suites
            .get(row.suite.index())
            .ok_or(Error::Invalid("classpath absence catalogue suite"))?;
        let symbol = facts
            .symbols
            .get(suite.symbol.index())
            .ok_or(Error::Invalid("classpath absence suite symbol"))?;
        let root = graph
            .node_for_symbol(suite.symbol)
            .ok_or(Error::Invalid("classpath absence suite root"))?;
        if graph
            .nodes
            .get(root.index())
            .is_none_or(|node| node.symbol != suite.symbol || node.file != suite.file)
            || suite.file.is_none()
            || symbol.file != suite.file
            || symbol.flags & SYMBOL_DEFINED == 0
            || row.owner_context.is_none()
            || symbol.context != row.owner_context
            || facts.files[suite.file.index()].context != row.owner_context
            || row.source_products_identity != evidence.source_products_identity
            || !nonzero(row.classpath_identity)
            || !nonzero(row.absence_identity)
        {
            return Err(Error::Invalid("classpath absence owning test context"));
        }
        suites.push(CertifiedRoot {
            suite: row.suite,
            root,
            symbol: suite.symbol,
            file: suite.file,
            context: row.owner_context,
            classpath: row.classpath_identity,
            absence: row.absence_identity,
        });
    }
    Ok(SideSeal {
        facts: facts.identity,
        graph: graph.identity,
        issuer: evidence.identity,
        capture: evidence.capture_identity,
        runtime: evidence.runtime_contract_identity,
        products: evidence.source_products_identity,
        execution: seeds.execution.to_vec(),
        declarations: seeds.declarations.to_vec(),
        sources: evidence.sources.to_vec(),
        absent_sources: absent_sources.to_vec(),
        product_files: evidence.product_files.to_vec(),
        stable_compilation: evidence.stable_compilation.to_vec(),
        suites,
    })
}

fn validate_compilation_pair(
    base: &SideSeal,
    head: &SideSeal,
    bf: &FactSnapshot,
    hf: &FactSnapshot,
) -> Result<(), Error> {
    if base.stable_compilation.len() != head.stable_compilation.len() {
        return Err(Error::Invalid("stable compilation paired source coverage"));
    }
    fn keys<'a>(
        side: &SideSeal,
        facts: &'a FactSnapshot,
    ) -> Vec<((&'a str, &'a str), StableCompilation)> {
        side.stable_compilation
            .iter()
            .map(|row| ((facts.path(row.file), facts.text(row.owner_context)), *row))
            .collect()
    }
    let mut before = keys(base, bf);
    let mut after = keys(head, hf);
    before.sort_unstable_by_key(|(key, _)| *key);
    after.sort_unstable_by_key(|(key, _)| *key);
    if before.windows(2).any(|pair| pair[0].0 == pair[1].0)
        || after.windows(2).any(|pair| pair[0].0 == pair[1].0)
        || before.iter().zip(&after).any(|((bk, b), (hk, h))| {
            bk != hk
                || b.source_sha256 != h.source_sha256
                || b.inputs_identity != h.inputs_identity
                || b.paired_identity != h.paired_identity
        })
    {
        return Err(Error::Invalid(
            "stable compilation paired source/input binding",
        ));
    }
    Ok(())
}

fn content_identity(plan: &Plan) -> ContentHash {
    let mut hash = Sha256::new();
    hash.update(VERSION);
    hash.update(SelectionContract::VERSION);
    hash.update(plan.contract.bits().to_le_bytes());
    hash.update((plan.scope.requested_paths.len() as u64).to_le_bytes());
    for path in &plan.scope.requested_paths {
        hash.update((path.len() as u64).to_le_bytes());
        hash.update(path.as_bytes());
    }
    hash.update(plan.scope.outside_count.to_le_bytes());
    hash.update((plan.scope.outside.len() as u64).to_le_bytes());
    for (b, h) in &plan.scope.outside {
        hash.update(b.0.to_le_bytes());
        hash.update(h.0.to_le_bytes());
    }
    for side in [&plan.base, &plan.head] {
        for value in [
            side.facts,
            side.graph,
            side.issuer,
            side.capture,
            side.runtime,
            side.products,
        ] {
            hash.update(value.0);
        }
        for nodes in [&side.execution, &side.declarations] {
            hash.update((nodes.len() as u64).to_le_bytes());
            for n in nodes {
                hash.update(n.0.to_le_bytes());
            }
        }
        hash.update((side.sources.len() as u64).to_le_bytes());
        for row in &side.sources {
            hash.update(row.file.0.to_le_bytes());
            hash.update(row.owner_context.0.to_le_bytes());
            hash.update(row.products_identity.0);
            hash.update(row.product_count.to_le_bytes());
        }
        hash.update((side.absent_sources.len() as u64).to_le_bytes());
        for row in &side.absent_sources {
            hash.update((row.path.len() as u64).to_le_bytes());
            hash.update(row.path.as_bytes());
            hash.update(row.opposite_facts.0);
            hash.update(row.absence_identity.0);
        }
        hash.update((side.product_files.len() as u64).to_le_bytes());
        for row in &side.product_files {
            hash.update(row.file.0.to_le_bytes());
            hash.update(row.source_file.0.to_le_bytes());
            hash.update(row.owner_context.0.to_le_bytes());
            hash.update(row.class_sha256.0);
        }
        hash.update((side.stable_compilation.len() as u64).to_le_bytes());
        for row in &side.stable_compilation {
            hash.update(row.file.0.to_le_bytes());
            hash.update(row.owner_context.0.to_le_bytes());
            hash.update(row.source_sha256.0);
            hash.update(row.inputs_identity.0);
            hash.update(row.paired_identity.0);
        }
        hash.update((side.suites.len() as u64).to_le_bytes());
        for row in &side.suites {
            for id in [
                row.suite.0,
                row.root.0,
                row.symbol.0,
                row.file.0,
                row.context.0,
            ] {
                hash.update(id.to_le_bytes());
            }
            hash.update(row.classpath.0);
            hash.update(row.absence.0);
        }
    }
    ContentHash(hash.finalize().into())
}

#[cfg(test)]
mod tests;
