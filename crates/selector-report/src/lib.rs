//! Checked, streaming output over compact IDs; no cloned explanation trees.
use selector_facts::FactSnapshot;
use selector_graph::{GraphDiagnostic, ProgramGraph};
use selector_issue::RuntimeIssueReason;
#[cfg(test)]
use selector_issue::RuntimeIssueSite;
use selector_result::{
    AnalysisEvidence, AnalysisResult, AnalyzedRoot, Obligation, SelectionResult, WitnessStep,
};
use selector_types::*;
use std::collections::{HashMap, HashSet};
use std::io::Write;

mod compact;
mod source_scope;
pub use compact::{write_compact_json, write_compact_json_with_evidence, write_compact_text};

pub struct ReportEvidenceRef<'a> {
    pub path: &'a str,
    pub sha256: ContentHash,
    pub bytes: u64,
}

pub const OUTPUT_SCHEMA_VERSION: u32 = 1;

/// The assumption remains visible even when a report contains no exclusions.
pub fn write_suite_semantics_text<W: Write>(mut out: W, mode: SuiteSemantics) -> Result<(), Error> {
    writeln!(out, "Suite semantics: {}", mode.as_str())?;
    if mode == SuiteSemantics::Independent {
        writeln!(
            out,
            "  Conditional assumption: suites are independent; JVM or process isolation has not been verified."
        )?;
    }
    Ok(())
}

pub fn write_selection_contract_text<W: Write>(
    mut out: W,
    contract: SelectionContract,
) -> Result<(), Error> {
    write_suite_semantics_text(&mut out, contract.suite_semantics())?;
    writeln!(
        out,
        "Selection contract: {} (conditional assumptions)",
        SelectionContract::VERSION
    )?;
    for name in contract.assumptions() {
        writeln!(out, "  Assumption: {name}")?;
    }
    if contract.contains(SelectionContract::FUNCTIONAL_BEHAVIOR) {
        writeln!(
            out,
            "  Ordinary suites are assumed functional; explicitly retained timing/performance-sensitive suites remain selected."
        )?;
    }
    if contract.contains(SelectionContract::TRUSTED_RUNTIME_CONTRACTS) {
        writeln!(
            out,
            "  Trusted models preserve application callbacks, initialization, exceptions and observable effects."
        )?;
    }
    if contract.contains(SelectionContract::OWNING_TEST_CLASSPATH) {
        writeln!(
            out,
            "  Conditional runner premise: each suite uses its owning captured Test/fullClasspath, with no undeclared provider or loader injection."
        )?;
        writeln!(
            out,
            "  Classpath-absence proofs concern only the requested changes; kernel completion and execution uncertainty remain separate diagnostics."
        )?;
    }
    if contract.contains(SelectionContract::ORDINARY_COMPILATION) {
        writeln!(
            out,
            "  Conditional compiler premise: ordinary compilation preserves behavior under the same captured complete source, dependencies and toolchain abstraction; this is not a raw-bytecode equivalence proof."
        )?;
        writeln!(
            out,
            "  Historical JDK evidence records labels and versions, not a hash of the complete JDK image. Requested source paths and kernel diagnostics remain unchanged."
        )?;
    }
    Ok(())
}

fn write_selection_contract_json<W: Write>(
    out: &mut W,
    contract: SelectionContract,
) -> Result<(), Error> {
    out.write_all(b"{\"version\":")?;
    json_string(out, SelectionContract::VERSION)?;
    write!(out, ",\"bits\":{},\"assumptions\":[", contract.bits())?;
    for (i, name) in contract.assumptions().enumerate() {
        if i != 0 {
            out.write_all(b",")?;
        }
        json_string(out, name)?;
    }
    out.write_all(b"]}")?;
    Ok(())
}

fn is_classpath_contract(contract: SelectionContract) -> bool {
    contract == SelectionContract::owning_test_classpath()
        || contract == SelectionContract::owning_test_classpath_with_compilation()
}

fn validate_suite_semantics(result: &SelectionResult) -> Result<(), Error> {
    if result.selection_contract.suite_semantics() != result.suite_semantics {
        return Err(Error::Invalid("selection contract suite semantics"));
    }
    if (result
        .selection_contract
        .contains(SelectionContract::OWNING_TEST_CLASSPATH)
        || result
            .selection_contract
            .contains(SelectionContract::ORDINARY_COMPILATION))
        && !is_classpath_contract(result.selection_contract)
    {
        return Err(Error::Invalid("owning classpath selection contract"));
    }
    let mask = SelectionContract::KNOWN_MASK;
    for decision in &result.decisions {
        classpath_absence(result, decision)?;
        for certificate in [decision.head_exclusion, decision.base_exclusion]
            .into_iter()
            .flatten()
        {
            if certificate.assumptions & mask != result.selection_contract.bits() {
                return Err(Error::Invalid("exclusion selection-contract assumptions"));
            }
            if is_classpath_contract(result.selection_contract)
                && certificate.assumptions == result.selection_contract.bits()
                && decision.reasons & selector_result::DECISION_CLASSPATH_ABSENCE == 0
            {
                return Err(Error::Invalid("classpath proof reason absent"));
            }
        }
    }
    Ok(())
}

/// Check the distinct conditional proof before allowing it to coexist with
/// unresolved kernel execution. Ordinary planner certificates keep their prior
/// validation rules; a reason bit alone never creates this exception.
fn classpath_absence(
    result: &SelectionResult,
    decision: &selector_result::SuiteDecision,
) -> Result<bool, Error> {
    use selector_result::*;
    if decision.reasons & DECISION_CLASSPATH_ABSENCE == 0 {
        return Ok(false);
    }
    let contract = result.selection_contract;
    if !is_classpath_contract(contract)
        || decision.status != SuiteDecisionStatus::Excluded
        || decision.guarded
        || decision.node.is_none()
        || decision.base_node.is_none()
        || result.base.is_none()
        || decision.reasons
            & (DECISION_HEAD_IMPACT
                | DECISION_BASE_IMPACT
                | DECISION_COMPLETE_UNAFFECTED
                | DECISION_CERTIFIED_EXCLUSION)
            != 0
    {
        return Err(Error::Invalid("classpath absence decision contract"));
    }
    for (proof, snapshot, root) in [
        (decision.head_exclusion, result.head_snapshot, decision.node),
        (
            decision.base_exclusion,
            result.base_snapshot,
            decision.base_node,
        ),
    ] {
        let proof = proof.ok_or(Error::Invalid("paired classpath absence proof"))?;
        if proof.snapshot != snapshot
            || proof.root != root
            || proof.assumptions != contract.bits()
            || proof.certificate == ContentHash::default()
        {
            return Err(Error::Invalid("classpath absence proof binding"));
        }
    }
    Ok(true)
}

/// The suite receiver is its declared compiler symbol. A projected hit at the
/// same node from a different execution binding is diagnostic only.
fn suite_root_reached(a: &AnalysisResult, graph: &ProgramGraph, node: NodeId) -> bool {
    graph
        .nodes
        .get(node.index())
        .is_some_and(|row| a.root_reached(node, row.symbol))
}

pub struct ReportSnapshots<'a> {
    pub base_facts: &'a FactSnapshot,
    pub base_graph: &'a ProgramGraph,
    pub head_facts: &'a FactSnapshot,
    pub head_graph: &'a ProgramGraph,
}

/// Stream checked source scope for change audits without running analysis.
/// A missing scope is serialized as null and grants no omission authority.
pub fn write_source_change_scope<W: Write>(
    mut out: W,
    snapshots: &ReportSnapshots<'_>,
    scope: Option<&selector_result::SourceChangeScope>,
) -> Result<(), Error> {
    source_scope::validate(snapshots, scope)?;
    source_scope::write_json(&mut out, snapshots, scope)
}

#[derive(Clone, Copy, Debug)]
pub struct ResolvedWitness {
    pub source: NodeId,
    pub target: NodeId,
    pub kind: EdgeKind,
    pub operation: OperationId,
    pub occurrence: OccurrenceId,
    pub receiver: SymbolId,
    pub derived: bool,
}

/// Validate graph/derived edge identity before expanding evidence. Derived edge
/// numbers are offsets from the immutable graph's static edge count.
pub fn resolve_witness(
    graph: &ProgramGraph,
    analysis: &AnalysisResult,
    step: &WitnessStep,
) -> Result<ResolvedWitness, Error> {
    let resolved = if let Some(edge) = graph.edges.get(step.edge.index()) {
        ResolvedWitness {
            source: edge.source,
            target: edge.target,
            kind: edge.kind,
            operation: edge.operation,
            occurrence: edge.occurrence,
            receiver: edge.receiver,
            derived: false,
        }
    } else {
        let index = step
            .edge
            .index()
            .checked_sub(graph.edges.len())
            .ok_or(Error::Invalid("witness edge"))?;
        let edge = analysis
            .derived_edges
            .get(index)
            .ok_or(Error::Invalid("derived witness edge"))?;
        ResolvedWitness {
            source: edge.source,
            target: edge.target,
            kind: edge.kind,
            operation: edge.operation,
            occurrence: OccurrenceId::NONE,
            receiver: edge.receiver,
            derived: true,
        }
    };
    if resolved.source != step.node
        || resolved.target != step.next
        || step.node.index() >= graph.nodes.len()
        || step.next.index() >= graph.nodes.len()
    {
        return Err(Error::Invalid("witness edge endpoints"));
    }
    Ok(resolved)
}

/// One compact index over affected nodes is shared across all explanations.
/// It borrows the already sorted affected IDs, so reporting a small answer never
/// allocates an entire-program node table. Iteration allocates nothing per step.
pub struct WitnessIndex<'a> {
    graph: &'a ProgramGraph,
    analysis: &'a AnalysisResult,
    affected: &'a [NodeId],
    witnesses: &'a [WitnessStep],
    by_node: Vec<ProofId>,
}
impl<'a> WitnessIndex<'a> {
    pub fn owned_bytes(&self) -> usize {
        self.by_node.capacity() * std::mem::size_of::<ProofId>()
    }

    pub fn new(graph: &'a ProgramGraph, analysis: &'a AnalysisResult) -> Result<Self, Error> {
        Self::from_parts(graph, analysis, &analysis.affected, &analysis.witnesses)
    }
    pub fn compilation(
        graph: &'a ProgramGraph,
        analysis: &'a AnalysisResult,
    ) -> Result<Self, Error> {
        Self::from_parts(
            graph,
            analysis,
            &analysis.compilation.affected,
            &analysis.compilation.witnesses,
        )
    }
    fn from_parts(
        graph: &'a ProgramGraph,
        analysis: &'a AnalysisResult,
        affected: &'a [NodeId],
        witnesses: &'a [WitnessStep],
    ) -> Result<Self, Error> {
        if graph.identity != analysis.snapshot {
            return Err(Error::Invalid("witness snapshot identity"));
        }
        if affected.windows(2).any(|w| w[0] >= w[1])
            || affected
                .iter()
                .any(|node| node.index() >= graph.nodes.len())
        {
            return Err(Error::Invalid("witness affected node index"));
        }
        let mut by_node = vec![ProofId::NONE; affected.len()];
        for (i, step) in witnesses.iter().enumerate() {
            resolve_witness(graph, analysis, step)?;
            let Ok(slot) = affected.binary_search(&step.node) else {
                return Err(Error::Invalid("witness outside affected nodes"));
            };
            if affected.binary_search(&step.next).is_err() {
                return Err(Error::Invalid("witness outside affected nodes"));
            }
            let previous = by_node[slot];
            if !previous.is_none() && witnesses[previous.index()] != *step {
                return Err(Error::Invalid("conflicting witness for node"));
            }
            by_node[slot] = ProofId::checked(i)?;
        }
        let index = Self {
            graph,
            analysis,
            affected,
            witnesses,
            by_node,
        };
        // Three colors validate all chains once, avoiding O(suites * nodes) walks.
        let mut colors = vec![0u8; affected.len()];
        let mut path = Vec::new();
        for start in 0..affected.len() {
            path.clear();
            let mut node = start;
            while colors[node] == 0 {
                colors[node] = 1;
                path.push(ProofId::checked(node)?);
                let i = index.by_node[node];
                if i.is_none() {
                    break;
                }
                node = affected
                    .binary_search(&witnesses[i.index()].next)
                    .map_err(|_| Error::Invalid("witness outside affected nodes"))?;
                if colors[node] == 1 {
                    return Err(Error::Invalid("cyclic witness chain"));
                }
            }
            for node in path.iter().copied() {
                colors[node.index()] = 2;
            }
        }
        Ok(index)
    }
    pub fn chain(&self, root: NodeId) -> Result<WitnessChain<'_>, Error> {
        if root.index() >= self.graph.nodes.len() || self.affected.binary_search(&root).is_err() {
            return Err(Error::Invalid("explanation root"));
        }
        Ok(WitnessChain {
            index: self,
            next: ProofId::checked(
                self.affected
                    .binary_search(&root)
                    .map_err(|_| Error::Invalid("explanation root"))?,
            )?,
            remaining: self.affected.len(),
        })
    }
}

pub struct WitnessChain<'a> {
    index: &'a WitnessIndex<'a>,
    next: ProofId,
    remaining: usize,
}
impl<'a> Iterator for WitnessChain<'a> {
    type Item = Result<&'a WitnessStep, Error>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.next.is_none() {
            return None;
        }
        let i = self.index.by_node[self.next.index()];
        if i.is_none() {
            self.next = ProofId::NONE;
            return None;
        }
        if self.remaining == 0 {
            self.next = ProofId::NONE;
            return Some(Err(Error::Invalid("cyclic witness chain")));
        }
        self.remaining -= 1;
        let step = &self.index.witnesses[i.index()];
        self.next = match self.index.affected.binary_search(&step.next) {
            Ok(slot) => ProofId(slot as u32),
            Err(_) => {
                self.next = ProofId::NONE;
                return Some(Err(Error::Invalid("witness outside affected nodes")));
            }
        };
        Some(Ok(step))
    }
}

fn completion(value: Completion) -> &'static str {
    match value {
        Completion::Complete => "complete",
        Completion::Conservative => "conservative",
        Completion::ResourceLimited => "resource_limited",
    }
}
fn issue_name(value: IssueKind) -> &'static str {
    match value {
        IssueKind::MissingSource => "missing_source",
        IssueKind::StaleSource => "stale_source",
        IssueKind::UnsupportedSchema => "unsupported_schema",
        IssueKind::MissingSyntax => "missing_syntax",
        IssueKind::UnresolvedSymbol => "unresolved_symbol",
        IssueKind::UnknownExecution => "unknown_execution",
        IssueKind::MissingBinary => "missing_binary",
        IssueKind::UnsupportedModel => "unsupported_model",
        IssueKind::ContextConflict => "context_conflict",
        IssueKind::ResourceLimit => "resource_limit",
        IssueKind::InvalidInput => "invalid_input",
        IssueKind::IncompleteHierarchy => "incomplete_hierarchy",
    }
}
fn edge_name(value: EdgeKind) -> &'static str {
    match value {
        EdgeKind::Compile => "compile",
        EdgeKind::Call => "call",
        EdgeKind::VirtualCall => "virtual_call",
        EdgeKind::Initialize => "initialize",
        EdgeKind::Callback => "callback",
        EdgeKind::Fixture => "fixture",
        EdgeKind::RuntimeBridge => "runtime_bridge",
        EdgeKind::Guard => "guard",
        EdgeKind::Return => "return",
        EdgeKind::Field => "field",
        EdgeKind::Construct => "construct",
        EdgeKind::Default => "default",
    }
}

fn json_string<W: Write>(out: &mut W, value: &str) -> Result<(), Error> {
    serde_json::to_writer(out, value).map_err(|e| Error::Message(e.to_string()))
}
fn json_id<W: Write>(out: &mut W, value: u32) -> Result<(), Error> {
    if value == u32::MAX {
        out.write_all(b"null")?;
    } else {
        write!(out, "{value}")?;
    }
    Ok(())
}
fn validate_obligation(facts: &FactSnapshot, o: &Obligation) -> Result<(), Error> {
    if !o.kind.is_execution_boundary() {
        return Err(Error::Invalid("metadata issue used as runtime obligation"));
    }
    if (!o.file.is_none() && o.file.index() >= facts.files.len())
        || (!o.symbol.is_none() && o.symbol.index() >= facts.symbols.len())
        || (!o.detail.is_none() && o.detail.index() >= facts.strings.len())
    {
        return Err(Error::Invalid("obligation reference"));
    }
    Ok(())
}
fn validate_analysis(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    a: &AnalysisResult,
) -> Result<(), Error> {
    a.validate_execution_effects()?;
    if a.snapshot != graph.identity || graph.facts_identity != facts.identity {
        return Err(Error::Invalid("report snapshot identity"));
    }
    if a.affected.windows(2).any(|w| w[0] >= w[1])
        || a.affected.iter().any(|n| n.index() >= graph.nodes.len())
    {
        return Err(Error::Invalid("report affected node index"));
    }
    if a.guarded_roots.windows(2).any(|w| w[0] >= w[1])
        || a.guarded_roots
            .iter()
            .any(|n| n.index() >= graph.nodes.len())
    {
        return Err(Error::Invalid("report guarded root index"));
    }
    for o in &a.obligations {
        validate_obligation(facts, o)?;
    }
    for node in &graph.nodes {
        if node.symbol.index() >= facts.symbols.len()
            || (!node.file.is_none() && node.file.index() >= facts.files.len())
            || (!node.body.is_none() && node.body.index() >= facts.bodies.len())
        {
            return Err(Error::Invalid("report graph fact reference"));
        }
    }
    for edge in &graph.edges {
        if (!edge.receiver.is_none() && edge.receiver.index() >= facts.symbols.len())
            || (!edge.operation.is_none() && edge.operation.index() >= facts.operations.len())
            || (!edge.occurrence.is_none() && edge.occurrence.index() >= facts.occurrences.len())
        {
            return Err(Error::Invalid("report graph edge fact reference"));
        }
    }
    for e in &a.derived_edges {
        if e.source.index() >= graph.nodes.len()
            || e.target.index() >= graph.nodes.len()
            || (!e.operation.is_none() && e.operation.index() >= facts.operations.len())
            || (!e.receiver.is_none() && e.receiver.index() >= facts.symbols.len())
        {
            return Err(Error::Invalid("derived edge reference"));
        }
    }
    for d in &graph.diagnostics {
        if (!d.file.is_none() && d.file.index() >= facts.files.len())
            || (!d.symbol.is_none() && d.symbol.index() >= facts.symbols.len())
        {
            return Err(Error::Invalid("runtime diagnostic fact scope"));
        }
        if !d.node.is_none() && d.node.index() >= graph.nodes.len() {
            return Err(Error::Invalid("runtime diagnostic node scope"));
        }
        for range in [d.reason, d.metadata_path] {
            let bytes = graph
                .diagnostic_bytes
                .get(range.range())
                .ok_or(Error::Invalid("runtime diagnostic text range"))?;
            std::str::from_utf8(bytes).map_err(|_| Error::Invalid("runtime diagnostic UTF-8"))?;
        }
        if d.reason.len == 0 {
            return Err(Error::Invalid("empty runtime diagnostic reason"));
        }
    }
    for step in &a.compilation.witnesses {
        if resolve_witness(graph, a, step)?.kind != EdgeKind::Compile {
            return Err(Error::Invalid("non-compilation witness"));
        }
    }
    WitnessIndex::compilation(graph, a)?;
    validate_evidence(facts, graph, a)?;
    Ok(())
}

/// Effect coverage is separate from a root's data/impact guards. Closed covers
/// only the exact requested frontier; selection still checks catalogue coverage.
fn write_execution_effects<W: Write>(out: &mut W, a: &AnalysisResult) -> Result<(), Error> {
    out.write_all(b"{\"scope\":\"requested_execution_frontier\",\"state\":")?;
    json_string(out, a.evidence.execution_effects.state().as_str())?;
    out.write_all(b",\"coverage\":")?;
    if let Some(c) = a.evidence.execution_effects.coverage() {
        write!(
            out,
            "{{\"contexts\":{},\"evaluated_contexts\":{},\"open_contexts\":{},\"pending_work\":{},\"external_open\":{}}}",
            c.contexts, c.evaluated_contexts, c.open_contexts, c.pending_work, c.external_open
        )?;
    } else {
        out.write_all(b"null")?;
    }
    out.write_all(b"}")?;
    Ok(())
}

fn validate_evidence(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    a: &AnalysisResult,
) -> Result<(), Error> {
    let e = &a.evidence;
    validate_guard_evidence(facts, graph, a)?;
    if e.requested_roots.windows(2).any(|w| w[0] >= w[1])
        || e.requested_roots.iter().any(|root| {
            root.node.index() >= graph.nodes.len()
                || (!root.receiver.is_none() && root.receiver.index() >= facts.symbols.len())
        })
    {
        return Err(Error::Invalid("evidence requested root scope"));
    }
    for atom in &e.atoms {
        if !matches!(atom.kind, 1 | 2 | 3 | 4)
            || (!atom.site.is_none() && atom.site.index() >= facts.operations.len())
            || (!atom.symbol.is_none() && atom.symbol.index() >= facts.symbols.len())
        {
            return Err(Error::Invalid("evidence atom"));
        }
        if atom.kind == 3
            && (atom.binding != 0 || facts.result_bound(atom.symbol, atom.site).is_none())
        {
            return Err(Error::Invalid("static result constraint evidence"));
        }
        if atom.kind == 4
            && (atom.site.is_none()
                || atom.symbol.is_none()
                || facts.symbol_name(atom.symbol) != SEQUENCE_ELEMENTS_SYMBOL
                || facts
                    .operations
                    .get(atom.site.index())
                    .is_none_or(|op| op.opcode != Opcode::PackSequence || op.target != atom.symbol))
        {
            return Err(Error::Invalid("sequence carrier evidence"));
        }
        if matches!(atom.kind, 1 | 4) && atom.binding != 0 {
            let origin = SymbolId(atom.binding - 1);
            // A retained cache family can carry a receiver origin from a prior
            // frontier. This is a finite symbol identity, not authority that
            // its root is requested or executed by the current query.
            if origin.index() >= facts.symbols.len()
                || atom.symbol.is_none()
                || facts.symbol_name(origin).is_empty()
            {
                return Err(Error::Invalid("object heap origin evidence"));
            }
        }
    }
    for value in &e.values {
        if value.atoms.range().end > e.atoms.len() {
            return Err(Error::Invalid("evidence value atom range"));
        }
    }
    if e.value_ids.iter().any(|id| *id as usize >= e.values.len()) {
        return Err(Error::Invalid("evidence argument value"));
    }
    if e.contexts.windows(2).any(|w| w[0].id >= w[1].id)
        || e.captures.windows(2).any(|w| w[0].binding >= w[1].binding)
        || e.witnesses.windows(2).any(|w| w[0].context >= w[1].context)
    {
        return Err(Error::Invalid("evidence contextual identity order"));
    }
    for context in &e.contexts {
        if context.id.is_none()
            || context.node.index() >= graph.nodes.len()
            || context.receiver as usize >= e.values.len()
            || context.arguments.range().end > e.value_ids.len()
        {
            return Err(Error::Invalid("evidence context"));
        }
    }
    for capture in &e.captures {
        if capture.receiver as usize >= e.values.len()
            || capture.arguments.range().end > e.value_ids.len()
        {
            return Err(Error::Invalid("evidence capture"));
        }
    }
    let find = |id: ContextId| {
        e.contexts
            .binary_search_by_key(&id, |c| c.id)
            .map_err(|_| Error::Invalid("evidence context reference"))
    };
    let mut next = vec![ContextId::NONE; e.contexts.len()];
    for witness in &e.witnesses {
        if witness.binding != u32::MAX
            && e.captures
                .binary_search_by_key(&witness.binding, |c| c.binding)
                .is_err()
        {
            return Err(Error::Invalid("context witness capture binding"));
        }
        let source = find(witness.context)?;
        let target = find(witness.next)?;
        resolve_witness(
            graph,
            a,
            &WitnessStep {
                node: e.contexts[source].node,
                next: e.contexts[target].node,
                edge: witness.edge,
            },
        )?;
        if !next[source].is_none() && next[source] != witness.next {
            return Err(Error::Invalid("conflicting context witness"));
        }
        next[source] = witness.next;
    }
    for root in &e.root_contexts {
        find(*root)?;
    }
    for atom in e.atoms.iter().filter(|atom| atom.kind == 2) {
        if e.captures
            .binary_search_by_key(&atom.binding, |c| c.binding)
            .is_err()
        {
            return Err(Error::Invalid("callback atom capture binding"));
        }
    }
    let mut colors = vec![0u8; e.contexts.len()];
    let mut path = Vec::new();
    for start in 0..e.contexts.len() {
        path.clear();
        let mut at = start;
        while colors[at] == 0 {
            colors[at] = 1;
            path.push(at);
            if next[at].is_none() {
                break;
            }
            at = find(next[at])?;
            if colors[at] == 1 {
                return Err(Error::Invalid("cyclic context witness"));
            }
        }
        for at in path.iter().copied() {
            colors[at] = 2;
        }
    }
    Ok(())
}

fn validate_guard_evidence(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    a: &AnalysisResult,
) -> Result<(), Error> {
    if a.evidence
        .guard_causes
        .windows(2)
        .any(|w| w[0].root >= w[1].root)
    {
        return Err(Error::Invalid("guard evidence root order"));
    }
    for cause in &a.evidence.guard_causes {
        if cause.root.index() >= graph.nodes.len()
            || cause.node.index() >= graph.nodes.len()
            || a.guarded_roots.binary_search(&cause.root).is_err()
        {
            return Err(Error::Invalid("guard evidence root or boundary"));
        }
        validate_obligation(
            facts,
            &Obligation {
                kind: cause.kind,
                file: cause.file,
                symbol: cause.symbol,
                detail: cause.detail,
            },
        )?;
        let boundary = &graph.nodes[cause.node.index()];
        if boundary.symbol.index() >= facts.symbols.len()
            || (!boundary.file.is_none() && boundary.file.index() >= facts.files.len())
        {
            return Err(Error::Invalid("guard evidence boundary fact reference"));
        }
        runtime_guard_operation(facts, graph, cause)?;
    }
    Ok(())
}

fn runtime_guard_operation<'a>(
    facts: &'a FactSnapshot,
    graph: &ProgramGraph,
    cause: &selector_result::RootGuardEvidence,
) -> Result<Option<&'a selector_facts::OperationRecord>, Error> {
    let Some(site) = cause.runtime else {
        return Ok(None);
    };
    site.validate()?;
    if site.kind != cause.kind {
        return Err(Error::Invalid("runtime guard issue kind"));
    }
    let node = graph
        .nodes
        .get(cause.node.index())
        .ok_or(Error::Invalid("runtime guard node"))?;
    if site.reason == RuntimeIssueReason::ExecutionGuard
        && !graph.successors(cause.node).any(|(_, edge)| {
            edge.operation == site.operation
                && (edge.kind == EdgeKind::Guard || edge.flags & EDGE_UNKNOWN != 0)
        })
    {
        return Err(Error::Invalid("runtime guard execution edge"));
    }
    if site.operation.is_none() {
        if site.reason == RuntimeIssueReason::MissingExecutableBody
            && (!node.body.is_none() || node.flags & NODE_EFFECTS_COMPLETE != 0)
        {
            return Err(Error::Invalid("runtime guard missing body"));
        }
        return Ok(None);
    }
    let op = facts
        .operations
        .get(site.operation.index())
        .ok_or(Error::Invalid("runtime guard operation"))?;
    if node.body.is_none() || op.body != node.body || !site.reason.accepts_opcode(op.opcode) {
        return Err(Error::Invalid("runtime guard operation ownership"));
    }
    let body = facts
        .bodies
        .get(op.body.index())
        .ok_or(Error::Invalid("runtime guard body"))?;
    if !body.operations.range().contains(&site.operation.index()) {
        return Err(Error::Invalid("runtime guard body operation range"));
    }
    if !body.file.is_none() {
        let file = facts
            .files
            .get(body.file.index())
            .ok_or(Error::Invalid("runtime guard operation file"))?;
        let source = facts.text(file.source);
        if file.flags & SOURCE_VERIFIED != 0
            && (op.span.start > op.span.end
                || op.span.end as usize > source.len()
                || !source.is_char_boundary(op.span.start as usize)
                || !source.is_char_boundary(op.span.end as usize))
        {
            return Err(Error::Invalid("runtime guard source span"));
        }
    }
    Ok(Some(op))
}

fn opcode_name(opcode: Opcode) -> &'static str {
    match opcode {
        Opcode::Call => "call",
        Opcode::VirtualCall => "virtual_call",
        Opcode::Allocate => "allocate",
        Opcode::Assign => "assign",
        Opcode::Parameter => "parameter",
        Opcode::Return => "return",
        Opcode::BindCallback => "bind_callback",
        Opcode::InvokeCallback => "invoke_callback",
        Opcode::LoadField => "load_field",
        Opcode::StoreField => "store_field",
        Opcode::Initialize => "initialize",
        Opcode::Unknown => "unknown",
        Opcode::Constant => "constant",
        Opcode::Join => "join",
        Opcode::DefaultArgument => "default_argument",
        Opcode::RegisterTest => "register_test",
        Opcode::PackSequence => "pack_sequence",
        Opcode::ReadElements => "read_elements",
    }
}

fn write_runtime_guard_text<W: Write>(
    out: &mut W,
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    cause: &selector_result::RootGuardEvidence,
) -> Result<(), Error> {
    let Some(site) = cause.runtime else {
        return Ok(());
    };
    write!(out, "      runtime reason: {}", site.reason.as_str())?;
    if let Some(op) = runtime_guard_operation(facts, graph, cause)? {
        write!(
            out,
            "; operation {} ({})",
            site.operation.0,
            opcode_name(op.opcode)
        )?;
        let file = facts.bodies[op.body.index()].file;
        if !file.is_none() {
            write!(out, "; {}", facts.path(file))?;
            if facts.files[file.index()].flags & SOURCE_VERIFIED != 0 {
                write!(out, " bytes {}..{}", op.span.start, op.span.end)?;
            }
        }
    }
    out.write_all(b"\n")?;
    Ok(())
}

fn write_guard_evidence<W: Write>(
    out: &mut W,
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    cause: &selector_result::RootGuardEvidence,
) -> Result<(), Error> {
    write!(
        out,
        "{{\"root\":{},\"node\":{},\"kind\":",
        cause.root.0, cause.node.0
    )?;
    json_string(out, issue_name(cause.kind))?;
    out.write_all(b",\"boundary_symbol\":")?;
    json_string(
        out,
        facts.symbol_name(graph.nodes[cause.node.index()].symbol),
    )?;
    out.write_all(b",\"file_id\":")?;
    json_id(out, cause.file.0)?;
    out.write_all(b",\"path\":")?;
    json_string(out, facts.path(cause.file))?;
    out.write_all(b",\"symbol_id\":")?;
    json_id(out, cause.symbol.0)?;
    out.write_all(b",\"symbol\":")?;
    json_string(out, facts.symbol_name(cause.symbol))?;
    out.write_all(b",\"detail\":")?;
    json_string(out, facts.text(cause.detail))?;
    if let Some(site) = cause.runtime {
        let op = runtime_guard_operation(facts, graph, cause)?;
        out.write_all(b",\"runtime_reason\":")?;
        json_string(out, site.reason.as_str())?;
        out.write_all(b",\"operation\":")?;
        json_id(out, site.operation.0)?;
        out.write_all(b",\"opcode\":")?;
        if let Some(op) = op {
            json_string(out, opcode_name(op.opcode))?
        } else {
            out.write_all(b"null")?
        }
        out.write_all(b",\"operation_path\":")?;
        let file = op
            .map(|op| facts.bodies[op.body.index()].file)
            .filter(|file| !file.is_none());
        if let Some(file) = file {
            json_string(out, facts.path(file))?
        } else {
            out.write_all(b"null")?
        }
        out.write_all(b",\"span\":")?;
        if let (Some(op), Some(_)) = (
            op,
            file.filter(|file| facts.files[file.index()].flags & SOURCE_VERIFIED != 0),
        ) {
            write!(
                out,
                "{{\"start\":{},\"end\":{}}}",
                op.span.start, op.span.end
            )?;
        } else {
            out.write_all(b"null")?
        }
    }
    out.write_all(b"}")?;
    Ok(())
}

/// Validate complete output before writing its first byte. Semantic validity of
/// witness identities and chains is checked in addition to JSON schema shape.
fn checked<'a>(
    s: &ReportSnapshots<'a>,
    result: &'a SelectionResult,
) -> Result<(WitnessIndex<'a>, Option<WitnessIndex<'a>>), Error> {
    s.base_facts.validate()?;
    s.head_facts.validate()?;
    s.base_graph.validate()?;
    s.head_graph.validate()?;
    source_scope::validate(s, result.change_scope.as_ref())?;
    validate_suite_semantics(result)?;
    if result
        .selection_contract
        .contains(SelectionContract::OWNING_TEST_CLASSPATH)
    {
        compact::check_decisions(s, result)?;
    }
    if result.base_snapshot != s.base_graph.identity
        || result.head_snapshot != s.head_graph.identity
    {
        return Err(Error::Invalid("selection snapshot identity"));
    }
    validate_analysis(s.head_facts, s.head_graph, &result.head)?;
    if let Some(base) = &result.base {
        validate_analysis(s.base_facts, s.base_graph, base)?;
    }
    for o in &result.obligations {
        validate_obligation(s.head_facts, o)?;
    }
    for cause in &result.guard_causes {
        let facts = match cause.side {
            selector_result::SnapshotSide::Base => s.base_facts,
            selector_result::SnapshotSide::Head => s.head_facts,
        };
        validate_obligation(
            facts,
            &Obligation {
                kind: cause.kind,
                file: cause.file,
                symbol: cause.symbol,
                detail: cause.detail,
            },
        )?;
    }
    for (i, decision) in result.decisions.iter().enumerate() {
        if decision.reasons & selector_result::DECISION_OPAQUE_SHARED_HEAP != 0
            && !classpath_absence(result, decision)?
            && (decision.suite.index() != i
                || !decision.guarded
                || decision.status == selector_result::SuiteDecisionStatus::Excluded
                || decision.reasons
                    & (selector_result::DECISION_COMPLETE_UNAFFECTED
                        | selector_result::DECISION_CERTIFIED_EXCLUSION)
                    != 0
                || decision.head_exclusion.is_some()
                || decision.base_exclusion.is_some()
                || !result
                    .suites
                    .binary_search_by_key(&decision.suite, |s| s.suite)
                    .ok()
                    .is_some_and(|index| {
                        let selected = &result.suites[index];
                        selected.node == decision.node && selected.guarded
                    }))
        {
            return Err(Error::Invalid("opaque shared-heap selection decision"));
        }
    }
    let mut previous = None;
    for selected in &result.suites {
        if previous.is_some_and(|id| id >= selected.suite) {
            return Err(Error::Invalid("selected suite order"));
        }
        previous = Some(selected.suite);
        let suite = s
            .head_facts
            .suites
            .get(selected.suite.index())
            .ok_or(Error::Invalid("selected suite identity"))?;
        let expected = s
            .head_graph
            .node_for_symbol(suite.symbol)
            .unwrap_or(NodeId::NONE);
        if selected.node != expected {
            return Err(Error::Invalid("selected suite node"));
        }
        if selected.node.is_none() && !selected.guarded {
            return Err(Error::Invalid("unresolved unguarded suite"));
        }
    }
    let head = WitnessIndex::new(s.head_graph, &result.head)?;
    let base = result
        .base
        .as_ref()
        .map(|base| WitnessIndex::new(s.base_graph, base))
        .transpose()?;
    Ok((head, base))
}

pub fn validate(s: &ReportSnapshots<'_>, result: &SelectionResult) -> Result<(), Error> {
    checked(s, result).map(|_| ())
}

fn write_obligation<W: Write>(
    out: &mut W,
    facts: &FactSnapshot,
    o: &Obligation,
) -> Result<(), Error> {
    out.write_all(b"{\"kind\":")?;
    json_string(out, issue_name(o.kind))?;
    out.write_all(b",\"file_id\":")?;
    json_id(out, o.file.0)?;
    out.write_all(b",\"path\":")?;
    json_string(out, facts.path(o.file))?;
    out.write_all(b",\"symbol_id\":")?;
    json_id(out, o.symbol.0)?;
    out.write_all(b",\"symbol\":")?;
    json_string(out, facts.symbol_name(o.symbol))?;
    out.write_all(b",\"detail\":")?;
    json_string(out, facts.text(o.detail))?;
    out.write_all(b"}")?;
    Ok(())
}
fn write_obligations<W: Write>(
    out: &mut W,
    facts: &FactSnapshot,
    obligations: &[Obligation],
) -> Result<(), Error> {
    out.write_all(b"[")?;
    for (i, o) in obligations.iter().enumerate() {
        if i > 0 {
            out.write_all(b",")?;
        }
        write_obligation(out, facts, o)?;
    }
    out.write_all(b"]")?;
    Ok(())
}
fn write_step<W: Write>(
    out: &mut W,
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    a: &AnalysisResult,
    step: &WitnessStep,
) -> Result<(), Error> {
    let edge = resolve_witness(graph, a, step)?;
    write!(
        out,
        "{{\"node\":{},\"next\":{},\"edge\":{},\"kind\":",
        step.node.0, step.next.0, step.edge.0
    )?;
    json_string(out, edge_name(edge.kind))?;
    out.write_all(b",\"source\":")?;
    json_string(
        out,
        facts.symbol_name(graph.nodes[step.node.index()].symbol),
    )?;
    out.write_all(b",\"target\":")?;
    json_string(
        out,
        facts.symbol_name(graph.nodes[step.next.index()].symbol),
    )?;
    write!(out, ",\"derived\":{},\"operation\":", edge.derived)?;
    json_id(out, edge.operation.0)?;
    out.write_all(b",\"occurrence\":")?;
    json_id(out, edge.occurrence.0)?;
    out.write_all(b",\"receiver\":")?;
    json_string(out, facts.symbol_name(edge.receiver))?;
    out.write_all(b"}")?;
    Ok(())
}
fn write_range<W: Write>(out: &mut W, range: IdRange) -> Result<(), Error> {
    write!(out, "{{\"start\":{},\"len\":{}}}", range.start, range.len)?;
    Ok(())
}
fn write_evidence<W: Write>(
    out: &mut W,
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    e: &AnalysisEvidence,
) -> Result<(), Error> {
    out.write_all(b"{\"requested_roots\":")?;
    write_root_bindings(out, facts, &e.requested_roots)?;
    if let Some(roots) = e.root_impacts() {
        out.write_all(b",\"root_impacts\":")?;
        write_root_bindings(out, facts, roots)?;
    }
    out.write_all(b",\"guard_causes\":[")?;
    for (i, cause) in e.guard_causes.iter().enumerate() {
        if i != 0 {
            out.write_all(b",")?;
        }
        write_guard_evidence(out, facts, graph, cause)?;
    }
    out.write_all(b"],\"heap_origins\":[")?;
    // One sparse dictionary per detached proof, rather than repeated origin
    // names and contexts on every object atom.
    let mut origins = HashSet::new();
    for atom in &e.atoms {
        if matches!(atom.kind, 1 | 4) && atom.binding != 0 {
            origins.insert(atom.binding - 1);
        }
    }
    let mut origins: Vec<_> = origins.into_iter().collect();
    origins.sort_unstable();
    for (i, id) in origins.into_iter().enumerate() {
        if i != 0 {
            out.write_all(b",")?;
        }
        let origin = SymbolId(id);
        write!(out, "{{\"symbol_id\":{id},\"symbol\":")?;
        json_string(out, facts.symbol_name(origin))?;
        out.write_all(b",\"context\":")?;
        json_string(out, facts.text(facts.symbols[origin.index()].context))?;
        out.write_all(b"}")?;
    }
    out.write_all(b"],\"atoms\":[")?;
    for (i, atom) in e.atoms.iter().enumerate() {
        if i > 0 {
            out.write_all(b",")?;
        }
        write!(out, "{{\"kind\":{},\"site\":", atom.kind)?;
        json_id(out, atom.site.0)?;
        out.write_all(b",\"symbol_id\":")?;
        json_id(out, atom.symbol.0)?;
        out.write_all(b",\"symbol\":")?;
        json_string(out, facts.symbol_name(atom.symbol))?;
        write!(out, ",\"binding\":{}", atom.binding)?;
        if atom.kind == 4 {
            out.write_all(
                b",\"carrier\":\"sequence_elements\",\"identity\":\"pack_site_and_receiver_root\"",
            )?;
        }
        if atom.kind == 3 {
            out.write_all(b",\"constraint\":\"static_result_constraint\",\"constraint_identity\":\"exact_class_conjunction\",\"origin_role\":\"representative_clause\",\"upper_bounds\":[")?;
            for (i, class) in facts
                .result_bound(atom.symbol, atom.site)
                .ok_or(Error::Invalid("static result constraint evidence"))?
                .iter()
                .enumerate()
            {
                if i > 0 {
                    out.write_all(b",")?;
                }
                json_string(out, facts.symbol_name(*class))?;
            }
            out.write_all(b"]")?;
        }
        out.write_all(b"}")?;
    }
    out.write_all(b"],\"values\":[")?;
    for (i, value) in e.values.iter().enumerate() {
        if i > 0 {
            out.write_all(b",")?;
        }
        out.write_all(b"{\"atoms\":")?;
        write_range(out, value.atoms)?;
        write!(out, ",\"unknown\":{}}}", value.unknown)?;
    }
    out.write_all(b"],\"value_ids\":[")?;
    for (i, id) in e.value_ids.iter().enumerate() {
        if i > 0 {
            out.write_all(b",")?;
        }
        write!(out, "{id}")?;
    }
    out.write_all(b"],\"contexts\":[")?;
    for (i, c) in e.contexts.iter().enumerate() {
        if i > 0 {
            out.write_all(b",")?;
        }
        write!(out, "{{\"id\":{},\"node\":{},\"symbol\":", c.id.0, c.node.0)?;
        json_string(out, facts.symbol_name(graph.nodes[c.node.index()].symbol))?;
        out.write_all(b",\"path\":")?;
        json_string(out, facts.path(graph.nodes[c.node.index()].file))?;
        write!(out, ",\"receiver\":{},\"arguments\":", c.receiver)?;
        write_range(out, c.arguments)?;
        out.write_all(b"}")?;
    }
    out.write_all(b"],\"captures\":[")?;
    for (i, c) in e.captures.iter().enumerate() {
        if i > 0 {
            out.write_all(b",")?;
        }
        write!(
            out,
            "{{\"binding\":{},\"receiver\":{},\"arguments\":",
            c.binding, c.receiver
        )?;
        write_range(out, c.arguments)?;
        out.write_all(b"}")?;
    }
    out.write_all(b"],\"witnesses\":[")?;
    for (i, w) in e.witnesses.iter().enumerate() {
        if i > 0 {
            out.write_all(b",")?;
        }
        write!(
            out,
            "{{\"context\":{},\"next\":{},\"edge\":{},\"binding\":",
            w.context.0, w.next.0, w.edge.0
        )?;
        json_id(out, w.binding)?;
        out.write_all(b"}")?;
    }
    out.write_all(b"],\"root_contexts\":[")?;
    for (i, c) in e.root_contexts.iter().enumerate() {
        if i > 0 {
            out.write_all(b",")?;
        }
        write!(out, "{}", c.0)?;
    }
    out.write_all(b"]}")?;
    Ok(())
}

fn write_root_bindings<W: Write>(
    out: &mut W,
    facts: &FactSnapshot,
    roots: &[AnalyzedRoot],
) -> Result<(), Error> {
    out.write_all(b"[")?;
    for (i, root) in roots.iter().enumerate() {
        if i != 0 {
            out.write_all(b",")?;
        }
        write!(out, "{{\"node\":{},\"receiver\":", root.node.0)?;
        json_id(out, root.receiver.0)?;
        out.write_all(b",\"receiver_symbol\":")?;
        json_string(out, facts.symbol_name(root.receiver))?;
        out.write_all(b",\"receiver_context\":")?;
        json_string(
            out,
            if root.receiver.is_none() {
                ""
            } else {
                facts.text(facts.symbols[root.receiver.index()].context)
            },
        )?;
        out.write_all(b"}")?;
    }
    out.write_all(b"]")?;
    Ok(())
}

fn write_analysis<W: Write>(
    out: &mut W,
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    a: &AnalysisResult,
) -> Result<(), Error> {
    write!(out, "{{\"snapshot\":\"{}\",\"completion\":", a.snapshot)?;
    json_string(out, completion(a.completion))?;
    out.write_all(b",\"execution_effects\":")?;
    write_execution_effects(out, a)?;
    out.write_all(b",\"affected\":[")?;
    for (i, node) in a.affected.iter().enumerate() {
        if i > 0 {
            out.write_all(b",")?;
        }
        write!(out, "{}", node.0)?;
    }
    out.write_all(b"],\"witnesses\":[")?;
    for (i, step) in a.witnesses.iter().enumerate() {
        if i > 0 {
            out.write_all(b",")?;
        }
        write_step(out, facts, graph, a, step)?;
    }
    out.write_all(b"],\"guarded_roots\":[")?;
    for (i, node) in a.guarded_roots.iter().enumerate() {
        if i > 0 {
            out.write_all(b",")?;
        }
        write!(out, "{}", node.0)?;
    }
    write!(
        out,
        "],\"unscoped_uncertainty\":{},\"compilation\":{{\"affected\":[",
        a.unscoped_uncertainty
    )?;
    for (i, node) in a.compilation.affected.iter().enumerate() {
        if i > 0 {
            out.write_all(b",")?;
        }
        write!(out, "{}", node.0)?;
    }
    out.write_all(b"],\"witnesses\":[")?;
    for (i, step) in a.compilation.witnesses.iter().enumerate() {
        if i > 0 {
            out.write_all(b",")?;
        }
        write_step(out, facts, graph, a, step)?;
    }
    out.write_all(b"]},\"evidence\":")?;
    write_evidence(out, facts, graph, &a.evidence)?;
    out.write_all(b",\"derived_edges\":[")?;
    for (i, e) in a.derived_edges.iter().enumerate() {
        if i > 0 {
            out.write_all(b",")?;
        }
        write!(
            out,
            "{{\"source\":{},\"target\":{},\"kind\":",
            e.source.0, e.target.0
        )?;
        json_string(out, edge_name(e.kind))?;
        out.write_all(b",\"operation\":")?;
        json_id(out, e.operation.0)?;
        out.write_all(b",\"receiver\":")?;
        json_string(out, facts.symbol_name(e.receiver))?;
        out.write_all(b"}")?;
    }
    out.write_all(b"],\"obligations\":")?;
    write_obligations(out, facts, &a.obligations)?;
    out.write_all(b",\"runtime_diagnostics\":[")?;
    let mut first = true;
    let context_nodes = diagnostic_node_index(graph, a);
    for d in &graph.diagnostics {
        if !diagnostic_relevant(graph, a, d, &context_nodes) {
            continue;
        }
        if !first {
            out.write_all(b",")?;
        }
        first = false;
        out.write_all(b"{\"kind\":")?;
        json_string(out, issue_name(d.kind))?;
        out.write_all(b",\"scope\":")?;
        json_string(
            out,
            if !d.node.is_none() {
                "node"
            } else if !d.symbol.is_none() {
                "symbol"
            } else if !d.file.is_none() {
                "file"
            } else {
                "unscoped"
            },
        )?;
        out.write_all(b",\"node\":")?;
        json_id(out, d.node.0)?;
        out.write_all(b",\"file_id\":")?;
        json_id(out, d.file.0)?;
        out.write_all(b",\"path\":")?;
        json_string(out, facts.path(d.file))?;
        out.write_all(b",\"symbol_id\":")?;
        json_id(out, d.symbol.0)?;
        out.write_all(b",\"symbol\":")?;
        json_string(out, facts.symbol_name(d.symbol))?;
        out.write_all(b",\"reason\":")?;
        json_string(out, graph.diagnostic_text(d.reason))?;
        out.write_all(b",\"metadata_path\":")?;
        json_string(out, graph.diagnostic_text(d.metadata_path))?;
        out.write_all(b"}")?;
    }
    out.write_all(b"]")?;
    let m = &a.metrics;
    write!(
        out,
        ",\"metrics\":{{\"states\":{},\"edge_visits\":{},\"novel_facts\":{},\"repeated_facts\":{},\"summary_hits\":{},\"invalidations\":{},\"queued_peak\":{},\"owned_bytes\":{},\"workers\":{},\"elapsed_ns\":{}}}}}",
        m.states,
        m.edge_visits,
        m.novel_facts,
        m.repeated_facts,
        m.summary_hits,
        m.invalidations,
        m.queued_peak,
        m.owned_bytes,
        m.workers,
        m.elapsed_ns
    )?;
    Ok(())
}

fn diagnostic_node_index(graph: &ProgramGraph, a: &AnalysisResult) -> Vec<NodeId> {
    if graph.diagnostics.is_empty() {
        return Vec::new();
    }
    let mut nodes: Vec<_> = a.evidence.contexts.iter().map(|c| c.node).collect();
    nodes.sort_unstable();
    nodes.dedup();
    nodes
}
fn diagnostic_relevant(
    graph: &ProgramGraph,
    a: &AnalysisResult,
    d: &GraphDiagnostic,
    contexts: &[NodeId],
) -> bool {
    let relevant_node = |node: NodeId| {
        a.contains(node)
            || a.guarded_roots.binary_search(&node).is_ok()
            || contexts.binary_search(&node).is_ok()
    };
    if !d.node.is_none() {
        relevant_node(d.node)
    } else if !d.symbol.is_none() {
        graph.node_for_symbol(d.symbol).is_some_and(relevant_node)
            || a.obligations.iter().any(|o| o.symbol == d.symbol)
    } else if !d.file.is_none() {
        a.obligations.iter().any(|o| o.file == d.file)
            || contexts
                .iter()
                .any(|node| graph.nodes[node.index()].file == d.file)
    } else {
        true
    }
}
fn diagnostic_text<W: Write>(
    out: &mut W,
    label: &str,
    graph: &ProgramGraph,
    d: &GraphDiagnostic,
) -> Result<(), Error> {
    writeln!(
        out,
        "  runtime diagnostic [{label}] {}: {}",
        issue_name(d.kind),
        graph.diagnostic_text(d.reason)
    )?;
    let path = graph.diagnostic_text(d.metadata_path);
    if !path.is_empty() {
        writeln!(out, "    metadata: {path}")?;
    }
    Ok(())
}

/// Stream every selected suite and all retained flat evidence. Callers normally
/// pass a `BufWriter`; no complete JSON value or formatted proof tree is built.
pub fn write_json<W: Write>(
    mut out: W,
    s: &ReportSnapshots<'_>,
    result: &SelectionResult,
) -> Result<(), Error> {
    validate(s, result)?;
    let base_suites = base_suite_index(s);
    write!(
        out,
        "{{\"schema_version\":{},\"base_snapshot\":\"{}\",\"head_snapshot\":\"{}\",\"completion\":",
        OUTPUT_SCHEMA_VERSION, result.base_snapshot, result.head_snapshot
    )?;
    json_string(&mut out, completion(result.completion))?;
    out.write_all(b",\"suite_semantics\":")?;
    json_string(&mut out, result.suite_semantics.as_str())?;
    out.write_all(b",\"selection_contract\":")?;
    write_selection_contract_json(&mut out, result.selection_contract)?;
    out.write_all(b",\"change_scope\":")?;
    source_scope::write_json(&mut out, s, result.change_scope.as_ref())?;
    out.write_all(b",\"suites\":[")?;
    for (i, selected) in result.suites.iter().enumerate() {
        if i > 0 {
            out.write_all(b",")?;
        }
        let suite = &s.head_facts.suites[selected.suite.index()];
        write!(out, "{{\"suite_id\":{},\"node\":", selected.suite.0)?;
        json_id(&mut out, selected.node.0)?;
        out.write_all(b",\"base_node\":")?;
        json_id(
            &mut out,
            indexed_base_suite_node(s, selected.suite, &base_suites)
                .unwrap_or(NodeId::NONE)
                .0,
        )?;
        out.write_all(b",\"name\":")?;
        json_string(&mut out, s.head_facts.text(suite.name))?;
        out.write_all(b",\"symbol\":")?;
        json_string(&mut out, s.head_facts.symbol_name(suite.symbol))?;
        out.write_all(b",\"context\":")?;
        let context = s
            .head_facts
            .symbols
            .get(suite.symbol.index())
            .map_or("", |s_| s.head_facts.text(s_.context));
        json_string(&mut out, context)?;
        out.write_all(b",\"path\":")?;
        json_string(&mut out, s.head_facts.path(suite.file))?;
        write!(out, ",\"guarded\":{}", selected.guarded)?;
        if result
            .decisions
            .get(selected.suite.index())
            .is_some_and(|d| d.reasons & selector_result::DECISION_OPAQUE_SHARED_HEAP != 0)
        {
            out.write_all(b",\"opaque_shared_heap\":true")?;
        }
        out.write_all(b"}")?;
    }
    out.write_all(b"]")?;
    if result
        .selection_contract
        .contains(SelectionContract::OWNING_TEST_CLASSPATH)
    {
        out.write_all(b",\"classpath_exclusions\":")?;
        compact::write_classpath_exclusions(&mut out, s, result)?;
    }
    out.write_all(b",\"obligations\":")?;
    write_obligations(&mut out, s.head_facts, &result.obligations)?;
    out.write_all(b",\"guard_causes\":")?;
    compact::write_guard_causes(&mut out, s, &result.guard_causes)?;
    out.write_all(b",\"base\":")?;
    if let Some(base) = &result.base {
        write_analysis(&mut out, s.base_facts, s.base_graph, base)?;
    } else {
        out.write_all(b"null")?;
    }
    out.write_all(b",\"head\":")?;
    write_analysis(&mut out, s.head_facts, s.head_graph, &result.head)?;
    out.write_all(b"}\n")?;
    Ok(())
}

fn base_suite_node(s: &ReportSnapshots<'_>, suite: SuiteId) -> Option<NodeId> {
    let suite = s.head_facts.suites.get(suite.index())?;
    let symbol = s.head_facts.symbols.get(suite.symbol.index())?;
    s.base_facts
        .suites
        .iter()
        .find(|candidate| {
            let Some(old) = s.base_facts.symbols.get(candidate.symbol.index()) else {
                return false;
            };
            s.base_facts.text(candidate.name) == s.head_facts.text(suite.name)
                && s.base_facts.text(old.name) == s.head_facts.text(symbol.name)
                && s.base_facts.text(old.context) == s.head_facts.text(symbol.context)
                && suite_local_scope(s.base_facts, old) == suite_local_scope(s.head_facts, symbol)
        })
        .and_then(|suite| s.base_graph.node_for_symbol(suite.symbol))
}

type SuiteKey<'a> = (&'a str, &'a str, &'a str, &'a str);
fn suite_local_scope<'a>(
    facts: &'a FactSnapshot,
    symbol: &selector_facts::SymbolRecord,
) -> &'a str {
    let name = facts.text(symbol.name);
    if selector_types::symbol::is_local(name) || name.starts_with("@local:") {
        facts.path(symbol.file)
    } else {
        ""
    }
}
fn base_suite_index<'a>(s: &ReportSnapshots<'a>) -> HashMap<SuiteKey<'a>, NodeId> {
    s.base_facts
        .suites
        .iter()
        .filter_map(|suite| {
            let symbol = s.base_facts.symbols.get(suite.symbol.index())?;
            let node = s.base_graph.node_for_symbol(suite.symbol)?;
            Some((
                (
                    s.base_facts.text(suite.name),
                    s.base_facts.text(symbol.name),
                    s.base_facts.text(symbol.context),
                    suite_local_scope(s.base_facts, symbol),
                ),
                node,
            ))
        })
        .collect()
}
fn indexed_base_suite_node(
    s: &ReportSnapshots<'_>,
    suite: SuiteId,
    index: &HashMap<SuiteKey<'_>, NodeId>,
) -> Option<NodeId> {
    let suite = s.head_facts.suites.get(suite.index())?;
    let symbol = s.head_facts.symbols.get(suite.symbol.index())?;
    index
        .get(&(
            s.head_facts.text(suite.name),
            s.head_facts.text(symbol.name),
            s.head_facts.text(symbol.context),
            suite_local_scope(s.head_facts, symbol),
        ))
        .copied()
}

fn explain_chain<W: Write>(
    out: &mut W,
    facts: &FactSnapshot,
    index: &WitnessIndex<'_>,
    root: NodeId,
) -> Result<(), Error> {
    let evidence = &index.analysis.evidence;
    if let Ok(at) = evidence
        .guard_causes
        .binary_search_by_key(&root, |cause| cause.root)
    {
        let cause = &evidence.guard_causes[at];
        writeln!(
            out,
            "    reached boundary {} [node {}]: {} {} {}",
            facts.symbol_name(index.graph.nodes[cause.node.index()].symbol),
            cause.node.0,
            issue_name(cause.kind),
            facts.path(cause.file),
            facts.text(cause.detail)
        )?;
        write_runtime_guard_text(out, facts, index.graph, cause)?;
    }
    let mut contextual = false;
    for id in &evidence.root_contexts {
        let mut current = evidence
            .contexts
            .binary_search_by_key(id, |c| c.id)
            .map_err(|_| Error::Invalid("explanation context root"))?;
        if evidence.contexts[current].node != root {
            continue;
        }
        contextual = true;
        for _ in 0..=evidence.contexts.len() {
            let context = &evidence.contexts[current];
            write!(
                out,
                "    context {} {} receiver=",
                context.id.0,
                facts.symbol_name(index.graph.nodes[context.node.index()].symbol)
            )?;
            explain_value(out, facts, evidence, context.receiver)?;
            out.write_all(b" arguments=[")?;
            for (i, value) in evidence.value_ids[context.arguments.range()]
                .iter()
                .enumerate()
            {
                if i > 0 {
                    out.write_all(b", ")?;
                }
                explain_value(out, facts, evidence, *value)?;
            }
            out.write_all(b"]\n")?;
            let Ok(at) = evidence
                .witnesses
                .binary_search_by_key(&context.id, |w| w.context)
            else {
                break;
            };
            let witness = evidence.witnesses[at];
            let target = evidence
                .contexts
                .binary_search_by_key(&witness.next, |c| c.id)
                .map_err(|_| Error::Invalid("explanation next context"))?;
            let edge = resolve_witness(
                index.graph,
                index.analysis,
                &WitnessStep {
                    node: context.node,
                    next: evidence.contexts[target].node,
                    edge: witness.edge,
                },
            )?;
            write!(out, "      --{}", edge_name(edge.kind))?;
            if witness.binding != u32::MAX {
                write!(out, " capture{}", witness.binding)?;
            }
            writeln!(out, "--> context {}", witness.next.0)?;
            current = target;
        }
    }
    if contextual {
        return Ok(());
    }
    if !suite_root_reached(index.analysis, index.graph, root) {
        writeln!(out, "    scoped unresolved execution boundary")?;
        return Ok(());
    }
    if index.analysis.root_impacts().is_some() {
        writeln!(out, "    Node projection of reached execution contexts:")?;
    }
    for step in index.chain(root)? {
        let step = step?;
        let edge = resolve_witness(index.graph, index.analysis, step)?;
        writeln!(
            out,
            "    {} --{}--> {}",
            facts.symbol_name(index.graph.nodes[step.node.index()].symbol),
            edge_name(edge.kind),
            facts.symbol_name(index.graph.nodes[step.next.index()].symbol)
        )?;
    }
    Ok(())
}

fn explain_value<W: Write>(
    out: &mut W,
    facts: &FactSnapshot,
    e: &AnalysisEvidence,
    id: u32,
) -> Result<(), Error> {
    let value = e
        .values
        .get(id as usize)
        .ok_or(Error::Invalid("explanation value"))?;
    write!(out, "value{id}[")?;
    for (i, atom) in e.atoms[value.atoms.range()].iter().enumerate() {
        if i > 0 {
            out.write_all(b", ")?;
        }
        write!(
            out,
            "{} {}",
            match atom.kind {
                1 => "object",
                2 => "callback",
                3 => "static result constraint",
                4 => "sequence element carrier",
                _ => return Err(Error::Invalid("evidence atom kind")),
            },
            facts.symbol_name(atom.symbol)
        )?;
        if atom.kind == 2 {
            write!(out, " capture{}", atom.binding)?;
        }
        if matches!(atom.kind, 1 | 4) && atom.binding != 0 {
            write!(
                out,
                " with receiver origin {}",
                facts.symbol_name(SymbolId(atom.binding - 1))
            )?;
        }
        if atom.kind == 3 {
            out.write_all(b" <= [")?;
            for (i, class) in facts
                .result_bound(atom.symbol, atom.site)
                .ok_or(Error::Invalid("static result constraint evidence"))?
                .iter()
                .enumerate()
            {
                if i > 0 {
                    out.write_all(b" & ")?;
                }
                out.write_all(facts.symbol_name(*class).as_bytes())?;
            }
            out.write_all(b"] (representative compiler clause)")?;
        }
    }
    if value.unknown != 0 {
        write!(out, " unknown={}", value.unknown)?;
    }
    out.write_all(b"]")?;
    Ok(())
}

fn explain_diagnostics<W: Write>(
    out: &mut W,
    label: &str,
    index: &WitnessIndex<'_>,
    root: NodeId,
) -> Result<(), Error> {
    if index.graph.diagnostics.is_empty() {
        return Ok(());
    }
    let mut nodes = Vec::new();
    if !root.is_none() {
        nodes.push(root);
    }
    let e = &index.analysis.evidence;
    if let Ok(at) = e
        .guard_causes
        .binary_search_by_key(&root, |cause| cause.root)
    {
        nodes.push(e.guard_causes[at].node);
    }
    let mut contextual = false;
    for id in &e.root_contexts {
        let mut at = e
            .contexts
            .binary_search_by_key(id, |c| c.id)
            .map_err(|_| Error::Invalid("diagnostic root context"))?;
        if e.contexts[at].node != root {
            continue;
        }
        contextual = true;
        for _ in 0..=e.contexts.len() {
            let c = e.contexts[at];
            nodes.push(c.node);
            let Ok(w) = e.witnesses.binary_search_by_key(&c.id, |w| w.context) else {
                break;
            };
            at = e
                .contexts
                .binary_search_by_key(&e.witnesses[w].next, |c| c.id)
                .map_err(|_| Error::Invalid("diagnostic context chain"))?;
        }
    }
    if !contextual && suite_root_reached(index.analysis, index.graph, root) {
        for step in index.chain(root)? {
            let step = step?;
            nodes.push(step.node);
            nodes.push(step.next);
        }
    }
    nodes.sort_unstable();
    nodes.dedup();
    for d in &index.graph.diagnostics {
        let relevant = if !d.node.is_none() {
            nodes.binary_search(&d.node).is_ok()
        } else if !d.symbol.is_none() {
            nodes
                .iter()
                .any(|n| index.graph.nodes[n.index()].symbol == d.symbol)
        } else if !d.file.is_none() {
            nodes
                .iter()
                .any(|n| index.graph.nodes[n.index()].file == d.file)
        } else {
            true
        };
        if relevant {
            diagnostic_text(out, label, index.graph, d)?;
        }
    }
    Ok(())
}

/// Explain one selected suite against both revisions, preserving base evidence
/// for removed definitions and removed relationships.
pub fn explain_suite<W: Write>(
    mut out: W,
    s: &ReportSnapshots<'_>,
    result: &SelectionResult,
    suite_id: SuiteId,
) -> Result<(), Error> {
    let (head_index, base_index) = checked(s, result)?;
    if let Some(decision) = result.decisions.get(suite_id.index()) {
        if classpath_absence(result, decision)? {
            write_selection_contract_text(&mut out, result.selection_contract)?;
            source_scope::write_text(&mut out, s, result.change_scope.as_ref())?;
            return compact::write_classpath_exclusion_text(&mut out, s, result, decision);
        }
    }
    let selected = result
        .suites
        .iter()
        .find(|suite| suite.suite == suite_id)
        .ok_or(Error::Invalid("suite not selected"))?;
    let suite = &s.head_facts.suites[suite_id.index()];
    write_selection_contract_text(&mut out, result.selection_contract)?;
    source_scope::write_text(&mut out, s, result.change_scope.as_ref())?;
    writeln!(
        out,
        "{}{}",
        s.head_facts.text(suite.name),
        if selected.guarded {
            " (conservative)"
        } else {
            ""
        }
    )?;
    if result
        .decisions
        .get(suite_id.index())
        .is_some_and(|d| d.reasons & selector_result::DECISION_OPAQUE_SHARED_HEAP != 0)
    {
        writeln!(
            out,
            "  This root may read shared state that a changed or unresolved writer can mutate; observed execution does not establish that it is unaffected."
        )?;
    }
    if !selected.node.is_none()
        && (suite_root_reached(&result.head, s.head_graph, selected.node)
            || result
                .head
                .guarded_roots
                .binary_search(&selected.node)
                .is_ok())
    {
        writeln!(out, "  head:")?;
        explain_chain(&mut out, s.head_facts, &head_index, selected.node)?;
    }
    if let (Some(index), Some(node)) = (&base_index, base_suite_node(s, suite_id)) {
        if suite_root_reached(index.analysis, index.graph, node)
            || index.analysis.guarded_roots.binary_search(&node).is_ok()
        {
            writeln!(out, "  base:")?;
            explain_chain(&mut out, s.base_facts, index, node)?;
        }
    }
    if selected.guarded {
        explain_diagnostics(&mut out, "head", &head_index, selected.node)?;
        if let Some(index) = &base_index {
            explain_diagnostics(
                &mut out,
                "base",
                index,
                base_suite_node(s, suite_id).unwrap_or(NodeId::NONE),
            )?;
        }
        writeln!(
            out,
            "  Retained because analysis has an unresolved or incomplete scope."
        )?;
    }
    Ok(())
}

/// Human output contains the complete selected catalogue, obligations, and one
/// validated witness chain per suite and revision. Formatting uses borrowed text.
pub fn write_text<W: Write>(
    mut out: W,
    s: &ReportSnapshots<'_>,
    result: &SelectionResult,
) -> Result<(), Error> {
    let (head, base) = checked(s, result)?;
    let base_suites = base_suite_index(s);
    write_selection_contract_text(&mut out, result.selection_contract)?;
    source_scope::write_text(&mut out, s, result.change_scope.as_ref())?;
    writeln!(
        out,
        "{}: {} selected suites",
        completion(result.completion),
        result.suites.len()
    )?;
    for selected in &result.suites {
        let suite = &s.head_facts.suites[selected.suite.index()];
        writeln!(
            out,
            "  {}{}",
            s.head_facts.text(suite.name),
            if selected.guarded {
                " [conservative]"
            } else {
                ""
            }
        )?;
        if result
            .decisions
            .get(selected.suite.index())
            .is_some_and(|d| d.reasons & selector_result::DECISION_OPAQUE_SHARED_HEAP != 0)
        {
            writeln!(
                out,
                "    This root may read shared state that a changed or unresolved writer can mutate; observed execution does not establish that it is unaffected."
            )?;
        }
        if !selected.node.is_none()
            && (suite_root_reached(&result.head, s.head_graph, selected.node)
                || result
                    .head
                    .guarded_roots
                    .binary_search(&selected.node)
                    .is_ok())
        {
            writeln!(out, "    head:")?;
            explain_chain(&mut out, s.head_facts, &head, selected.node)?;
        }
        let base_node = indexed_base_suite_node(s, selected.suite, &base_suites);
        if let (Some(index), Some(node)) = (&base, base_node) {
            if suite_root_reached(index.analysis, index.graph, node)
                || index.analysis.guarded_roots.binary_search(&node).is_ok()
            {
                writeln!(out, "    base:")?;
                explain_chain(&mut out, s.base_facts, index, node)?;
            }
        }
    }
    for decision in &result.decisions {
        if classpath_absence(result, decision)? {
            compact::write_classpath_exclusion_text(&mut out, s, result, decision)?;
        }
    }
    for (label, facts, obligations) in [
        ("selection", s.head_facts, result.obligations.as_slice()),
        ("head", s.head_facts, result.head.obligations.as_slice()),
        (
            "base",
            s.base_facts,
            result
                .base
                .as_ref()
                .map_or(&[], |b| b.obligations.as_slice()),
        ),
    ] {
        for o in obligations {
            writeln!(
                out,
                "  obligation [{label}] {}: {} {} {}",
                issue_name(o.kind),
                facts.path(o.file),
                facts.symbol_name(o.symbol),
                facts.text(o.detail)
            )?;
        }
    }
    let context_nodes = diagnostic_node_index(s.head_graph, &result.head);
    for d in &s.head_graph.diagnostics {
        if diagnostic_relevant(s.head_graph, &result.head, d, &context_nodes) {
            diagnostic_text(&mut out, "head", s.head_graph, d)?;
        }
    }
    if let Some(base) = &result.base {
        let context_nodes = diagnostic_node_index(s.base_graph, base);
        for d in &s.base_graph.diagnostics {
            if diagnostic_relevant(s.base_graph, base, d, &context_nodes) {
                diagnostic_text(&mut out, "base", s.base_graph, d)?;
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use selector_facts::{FactBuilder, FileRecord, SuiteRecord};
    use selector_graph::{EdgeRecord, NodeRecord};
    use selector_result::{DerivedEdge, SelectedSuite};

    fn fixture() -> (FactSnapshot, ProgramGraph, SelectionResult) {
        let mut b = FactBuilder::new();
        let path = b.intern("a\"b.scala").unwrap();
        let source = b.intern("class Suite").unwrap();
        b.facts.files.push(FileRecord {
            path,
            source,
            revision: StrId::NONE,
            context: StrId::NONE,
            source_hash: ContentHash::default(),
            flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
        });
        for name in ["p/Suite#", "p/Suite#test().", "p/Target#f()."] {
            let id = b.ensure_symbol(name, FileId(0)).unwrap();
            b.facts.symbols[id.index()].file = FileId(0);
        }
        let name = b.intern("Suite \"quoted\"\nname").unwrap();
        b.facts.suites.push(SuiteRecord {
            name,
            symbol: SymbolId(0),
            file: FileId(0),
            flags: 0,
        });
        let facts = b.finish().unwrap();
        let mut graph = ProgramGraph {
            facts_identity: facts.identity,
            ..Default::default()
        };
        for i in 0..3 {
            graph.nodes.push(NodeRecord {
                symbol: SymbolId(i),
                file: FileId(0),
                body: BodyId::NONE,
                flags: 0,
            });
            graph.symbol_nodes.push(NodeId(i));
        }
        graph.edges.push(EdgeRecord {
            source: NodeId(0),
            target: NodeId(1),
            kind: EdgeKind::Call,
            occurrence: OccurrenceId::NONE,
            operation: OperationId::NONE,
            receiver: SymbolId::NONE,
            flags: 0,
        });
        graph.index().unwrap();
        let head = AnalysisResult {
            snapshot: graph.identity,
            completion: Completion::Complete,
            affected: vec![NodeId(0), NodeId(1), NodeId(2)],
            witnesses: vec![
                WitnessStep {
                    node: NodeId(0),
                    next: NodeId(1),
                    edge: EdgeId(0),
                },
                WitnessStep {
                    node: NodeId(1),
                    next: NodeId(2),
                    edge: EdgeId(1),
                },
            ],
            derived_edges: vec![DerivedEdge {
                source: NodeId(1),
                target: NodeId(2),
                kind: EdgeKind::Callback,
                operation: OperationId::NONE,
                receiver: SymbolId::NONE,
            }],
            obligations: Vec::new(),
            guarded_roots: Vec::new(),
            unscoped_uncertainty: false,
            evidence: Default::default(),
            compilation: Default::default(),
            metrics: Default::default(),
        };
        let result = SelectionResult {
            suite_semantics: SuiteSemantics::SharedState,
            selection_contract: SelectionContract::current(SuiteSemantics::SharedState),
            base_snapshot: graph.identity,
            head_snapshot: graph.identity,
            completion: Completion::Complete,
            suites: vec![SelectedSuite {
                suite: SuiteId(0),
                node: NodeId(0),
                guarded: false,
            }],
            base: None,
            head,
            obligations: Vec::new(),
            guard_causes: Vec::new(),
            decisions: vec![selector_result::SuiteDecision {
                suite: SuiteId(0),
                node: NodeId(0),
                base_node: NodeId(0),
                status: selector_result::SuiteDecisionStatus::Required,
                guarded: false,
                reasons: selector_result::DECISION_HEAD_IMPACT,
                head_exclusion: None,
                base_exclusion: None,
            }],
            base_seeds: Vec::new(),
            head_seeds: vec![NodeId(2)],
            change_scope: None,
        };
        (facts, graph, result)
    }
    #[test]
    fn compact_decisions_retain_checked_chains_without_expanding_value_tables() {
        let (facts, graph, mut result) = fixture();
        result.head.evidence.values.resize(
            10_000,
            selector_result::EvidenceValue {
                atoms: IdRange::default(),
                unknown: 1,
            },
        );
        let snapshots = ReportSnapshots {
            base_facts: &facts,
            base_graph: &graph,
            head_facts: &facts,
            head_graph: &graph,
        };
        let mut compact = Vec::new();
        write_compact_json(&mut compact, &snapshots, &result).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&compact).unwrap();
        assert_eq!(json["schema_version"], 2);
        assert_eq!(json["decisions"][0]["status"], "required");
        assert_eq!(
            json["decisions"][0]["proofs"][0]["chain"]
                .as_array()
                .unwrap()
                .len(),
            2
        );
        assert_eq!(json["decisions"][0]["proofs"][0]["seed"], 2);
        assert!(compact.len() < 4096);
        assert!(json.get("head").is_none());
        let mut full = Vec::new();
        write_json(&mut full, &snapshots, &result).unwrap();
        assert!(full.len() > compact.len() * 50);
    }
    #[test]
    fn suite_semantics_are_visible_without_exclusions_in_full_compact_and_text() {
        let (facts, graph, mut result) = fixture();
        let snapshots = ReportSnapshots {
            base_facts: &facts,
            base_graph: &graph,
            head_facts: &facts,
            head_graph: &graph,
        };
        for mode in [SuiteSemantics::SharedState, SuiteSemantics::Independent] {
            result.suite_semantics = mode;
            result.selection_contract = SelectionContract::current(mode);
            for compact in [false, true] {
                let mut json = Vec::new();
                if compact {
                    write_compact_json(&mut json, &snapshots, &result).unwrap();
                } else {
                    write_json(&mut json, &snapshots, &result).unwrap();
                }
                let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
                assert_eq!(json["suite_semantics"], mode.as_str());
                assert_eq!(
                    json["selection_contract"]["version"],
                    SelectionContract::VERSION
                );
                assert_eq!(
                    json["selection_contract"]["bits"],
                    result.selection_contract.bits()
                );
                assert_eq!(
                    json["selection_contract"]["assumptions"]
                        .as_array()
                        .unwrap()
                        .len(),
                    if mode == SuiteSemantics::Independent {
                        5
                    } else {
                        4
                    }
                );
                let mut text = Vec::new();
                if compact {
                    write_compact_text(&mut text, &snapshots, &result).unwrap();
                } else {
                    write_text(&mut text, &snapshots, &result).unwrap();
                }
                let text = String::from_utf8(text).unwrap();
                assert!(text.contains(&format!("Suite semantics: {}", mode.as_str())));
                assert_eq!(
                    text.contains("suites are independent"),
                    mode == SuiteSemantics::Independent
                );
                assert!(text.contains("Assumption: functional_behavior"));
                assert!(text.contains(
                    "explicitly retained timing/performance-sensitive suites remain selected"
                ));
                if mode == SuiteSemantics::Independent {
                    assert!(text.contains("isolation has not been verified"));
                }
            }
        }
    }
    fn classpath_fixture() -> (FactSnapshot, ProgramGraph, SelectionResult) {
        let (facts, graph, mut result) = fixture();
        result.suite_semantics = SuiteSemantics::Independent;
        result.selection_contract = SelectionContract::owning_test_classpath();
        result.completion = Completion::ResourceLimited;
        result.head.completion = Completion::ResourceLimited;
        result.head.affected.clear();
        result.head.witnesses.clear();
        result.head.derived_edges.clear();
        result.head.guarded_roots = vec![NodeId(0)];
        result.head.unscoped_uncertainty = true;
        result.head.evidence.guard_causes = vec![selector_result::RootGuardEvidence {
            root: NodeId(0),
            node: NodeId(0),
            kind: IssueKind::UnsupportedModel,
            file: FileId(0),
            symbol: SymbolId(0),
            detail: StrId::NONE,
            runtime: None,
        }];
        // Build the same bound fixture independently; analysis/results are
        // intentionally not Clone because detached evidence can be large.
        let mut base = fixture().2.head;
        base.completion = result.head.completion;
        base.affected.clear();
        base.witnesses.clear();
        base.derived_edges.clear();
        base.guarded_roots = vec![NodeId(0)];
        base.unscoped_uncertainty = true;
        base.evidence.guard_causes = vec![selector_result::RootGuardEvidence {
            root: NodeId(0),
            node: NodeId(0),
            kind: IssueKind::UnsupportedModel,
            file: FileId(0),
            symbol: SymbolId(0),
            detail: StrId::NONE,
            runtime: None,
        }];
        result.base = Some(base);
        result.suites.clear();
        result.decisions[0].status = selector_result::SuiteDecisionStatus::Excluded;
        result.decisions[0].reasons = selector_result::DECISION_CLASSPATH_ABSENCE
            | selector_result::DECISION_SCOPED_GUARD
            | selector_result::DECISION_QUERY_UNSCOPED
            | selector_result::DECISION_RESOURCE_LIMIT;
        result.decisions[0].head_exclusion = Some(selector_result::RootExclusion {
            snapshot: graph.identity,
            root: NodeId(0),
            certificate: ContentHash([7; 32]),
            assumptions: result.selection_contract.bits(),
        });
        result.decisions[0].base_exclusion = Some(selector_result::RootExclusion {
            certificate: ContentHash([8; 32]),
            ..result.decisions[0].head_exclusion.unwrap()
        });
        (facts, graph, result)
    }
    #[test]
    fn conditional_report_does_not_treat_a_projected_node_as_a_root_hit() {
        let (facts, graph, mut result) = classpath_fixture();
        let projected = fixture().2.head;
        result.head.affected = projected.affected;
        result.head.witnesses = projected.witnesses;
        result.head.derived_edges = projected.derived_edges;
        let snapshots = ReportSnapshots {
            base_facts: &facts,
            base_graph: &graph,
            head_facts: &facts,
            head_graph: &graph,
        };
        let mut compact = Vec::new();
        assert!(write_compact_json(&mut compact, &snapshots, &result).is_err());
        assert!(compact.is_empty(), "legacy projection cannot be overridden");
        result.head.record_root_impacts(vec![]).unwrap();
        write_compact_json(&mut compact, &snapshots, &result).unwrap();
        let compact: serde_json::Value = serde_json::from_slice(&compact).unwrap();
        assert_eq!(compact["decisions"][0]["status"], "excluded");
        assert_eq!(compact["decisions"][0]["proofs"], serde_json::json!([]));
        let mut full = Vec::new();
        write_json(&mut full, &snapshots, &result).unwrap();
        let full: serde_json::Value = serde_json::from_slice(&full).unwrap();
        assert_eq!(
            full["head"]["evidence"]["root_impacts"],
            serde_json::json!([])
        );
        assert_eq!(full["head"]["affected"], serde_json::json!([0, 1, 2]));
    }

    #[test]
    fn owning_classpath_premise_is_visible_with_zero_exclusions_without_changing_strict_shape() {
        let (facts, graph, mut result) = fixture();
        let s = ReportSnapshots {
            base_facts: &facts,
            base_graph: &graph,
            head_facts: &facts,
            head_graph: &graph,
        };
        let mut strict = Vec::new();
        write_json(&mut strict, &s, &result).unwrap();
        let strict: serde_json::Value = serde_json::from_slice(&strict).unwrap();
        assert!(strict.get("classpath_exclusions").is_none());
        assert!(
            !strict["selection_contract"]["assumptions"]
                .as_array()
                .unwrap()
                .iter()
                .any(|value| value == "owning_test_full_classpath")
        );
        result.suite_semantics = SuiteSemantics::Independent;
        result.selection_contract = SelectionContract::owning_test_classpath();
        for compact in [false, true] {
            let mut bytes = Vec::new();
            if compact {
                write_compact_json(&mut bytes, &s, &result).unwrap();
            } else {
                write_json(&mut bytes, &s, &result).unwrap();
            }
            let json: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
            assert_eq!(json["selection_contract"]["bits"], 1008);
            assert_eq!(
                json["selection_contract"]["assumptions"]
                    .as_array()
                    .unwrap()
                    .last()
                    .unwrap(),
                "owning_test_full_classpath"
            );
            if !compact {
                assert_eq!(json["classpath_exclusions"], serde_json::json!([]));
            }
            let mut text = Vec::new();
            if compact {
                write_compact_text(&mut text, &s, &result).unwrap();
            } else {
                write_text(&mut text, &s, &result).unwrap();
            }
            assert!(
                String::from_utf8(text)
                    .unwrap()
                    .contains("owning captured Test/fullClasspath")
            );
        }
    }
    #[test]
    fn classpath_absence_preserves_open_kernel_evidence_and_distinct_paired_proofs() {
        let (facts, graph, result) = classpath_fixture();
        let s = ReportSnapshots {
            base_facts: &facts,
            base_graph: &graph,
            head_facts: &facts,
            head_graph: &graph,
        };
        for compact in [false, true] {
            let mut bytes = Vec::new();
            if compact {
                write_compact_json(&mut bytes, &s, &result).unwrap();
            } else {
                write_json(&mut bytes, &s, &result).unwrap();
            }
            let json: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
            assert_eq!(json["completion"], "resource_limited");
            let row = if compact {
                &json["decisions"][0]
            } else {
                &json["classpath_exclusions"][0]
            };
            assert_eq!(row["exclusions"].as_array().unwrap().len(), 2);
            assert_eq!(row["exclusions"][0]["assumptions"], 1008);
            if compact {
                assert!(
                    row["reasons"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .any(|value| value == "classpath_absence")
                );
                assert_eq!(row["uncertainty"].as_array().unwrap().len(), 2);
            } else {
                assert_eq!(row["reason"], "classpath_absence");
                assert_eq!(json["head"]["guarded_roots"], serde_json::json!([0]));
                assert_eq!(json["base"]["guarded_roots"], serde_json::json!([0]));
            }
            let mut text = Vec::new();
            if compact {
                write_compact_text(&mut text, &s, &result).unwrap();
            } else {
                write_text(&mut text, &s, &result).unwrap();
            }
            let text = String::from_utf8(text).unwrap();
            assert!(text.contains("classpath-absence certificate"));
            assert!(text.to_ascii_lowercase().contains("kernel diagnostic"));
            assert!(!text.contains("closed-component certificate"));
        }
        let mut text = Vec::new();
        explain_suite(&mut text, &s, &result, SuiteId(0)).unwrap();
        assert!(
            String::from_utf8(text)
                .unwrap()
                .contains("excluded (classpath absence)")
        );
        assert_eq!(result.head.guarded_roots, vec![NodeId(0)]);
    }
    #[test]
    fn ordinary_compilation_is_explicit_in_zero_and_paired_classpath_outputs() {
        let contract = SelectionContract::owning_test_classpath_with_compilation();
        for excluded in [false, true] {
            let (facts, graph, mut result) = if excluded {
                classpath_fixture()
            } else {
                fixture()
            };
            result.suite_semantics = SuiteSemantics::Independent;
            result.selection_contract = contract;
            if excluded {
                result.decisions[0]
                    .head_exclusion
                    .as_mut()
                    .unwrap()
                    .assumptions = contract.bits();
                result.decisions[0]
                    .base_exclusion
                    .as_mut()
                    .unwrap()
                    .assumptions = contract.bits();
            }
            let s = ReportSnapshots {
                base_facts: &facts,
                base_graph: &graph,
                head_facts: &facts,
                head_graph: &graph,
            };
            for compact in [false, true] {
                let mut bytes = Vec::new();
                let mut text = Vec::new();
                if compact {
                    write_compact_json(&mut bytes, &s, &result).unwrap();
                    write_compact_text(&mut text, &s, &result).unwrap();
                } else {
                    write_json(&mut bytes, &s, &result).unwrap();
                    write_text(&mut text, &s, &result).unwrap();
                }
                let json: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
                assert_eq!(json["selection_contract"]["bits"], 2032);
                assert_eq!(
                    json["selection_contract"]["assumptions"]
                        .as_array()
                        .unwrap()
                        .len(),
                    7
                );
                assert_eq!(
                    json["selection_contract"]["assumptions"][6],
                    "ordinary_compilation"
                );
                if excluded {
                    let row = if compact {
                        &json["decisions"][0]
                    } else {
                        &json["classpath_exclusions"][0]
                    };
                    assert_eq!(json["completion"], "resource_limited");
                    assert_eq!(row["exclusions"][0]["assumptions"], 2032);
                    assert_eq!(row["exclusions"][1]["assumptions"], 2032);
                } else if !compact {
                    assert_eq!(json["classpath_exclusions"], serde_json::json!([]));
                }
                let text = String::from_utf8(text).unwrap();
                assert!(text.contains("Assumption: ordinary_compilation"));
                assert!(text.contains("not a raw-bytecode equivalence proof"));
                assert!(text.contains("not a hash of the complete JDK image"));
            }
        }
    }
    #[test]
    fn ordinary_compilation_rejects_partial_contracts_and_cross_contract_certificates() {
        for bits in [1024, 1024 | 16, 1024 | 480, 1024 | 512] {
            let (facts, graph, mut result) = fixture();
            result.selection_contract = SelectionContract::from_bits(bits).unwrap();
            result.suite_semantics = result.selection_contract.suite_semantics();
            let s = ReportSnapshots {
                base_facts: &facts,
                base_graph: &graph,
                head_facts: &facts,
                head_graph: &graph,
            };
            for compact in [false, true] {
                let mut bytes = Vec::new();
                let rendered = if compact {
                    write_compact_json(&mut bytes, &s, &result)
                } else {
                    write_json(&mut bytes, &s, &result)
                };
                assert!(rendered.is_err(), "partial contract {bits}");
                assert!(bytes.is_empty());
            }
        }
        for contract in [
            SelectionContract::owning_test_classpath(),
            SelectionContract::owning_test_classpath_with_compilation(),
        ] {
            for stale_side in [false, true] {
                let (facts, graph, mut result) = classpath_fixture();
                result.selection_contract = contract;
                let other = if contract.bits() == 1008 { 2032 } else { 1008 };
                result.decisions[0]
                    .head_exclusion
                    .as_mut()
                    .unwrap()
                    .assumptions = if stale_side { other } else { contract.bits() };
                result.decisions[0]
                    .base_exclusion
                    .as_mut()
                    .unwrap()
                    .assumptions = if stale_side { contract.bits() } else { other };
                let s = ReportSnapshots {
                    base_facts: &facts,
                    base_graph: &graph,
                    head_facts: &facts,
                    head_graph: &graph,
                };
                for compact in [false, true] {
                    let mut bytes = Vec::new();
                    let rendered = if compact {
                        write_compact_json(&mut bytes, &s, &result)
                    } else {
                        write_json(&mut bytes, &s, &result)
                    };
                    assert!(rendered.is_err(), "cross-contract paired proof");
                    assert!(bytes.is_empty());
                }
            }
        }
    }
    #[test]
    fn classpath_absence_rejects_missing_mutated_or_relabelled_proofs_before_any_output() {
        let (facts, graph, _) = classpath_fixture();
        let s = ReportSnapshots {
            base_facts: &facts,
            base_graph: &graph,
            head_facts: &facts,
            head_graph: &graph,
        };
        for change in 0..12 {
            let (_, _, mut bad) = classpath_fixture();
            match change {
                0 => bad.decisions[0].base_exclusion = None,
                1 => {
                    bad.decisions[0]
                        .head_exclusion
                        .as_mut()
                        .unwrap()
                        .assumptions |= 15
                }
                2 => {
                    bad.decisions[0].head_exclusion.as_mut().unwrap().snapshot =
                        ContentHash([9; 32])
                }
                3 => bad.decisions[0].head_exclusion.as_mut().unwrap().root = NodeId(1),
                4 => {
                    bad.decisions[0]
                        .head_exclusion
                        .as_mut()
                        .unwrap()
                        .certificate = ContentHash::default()
                }
                5 => {
                    bad.selection_contract = SelectionContract::current(SuiteSemantics::Independent)
                }
                6 => bad.decisions[0].guarded = true,
                7 => bad.decisions[0].reasons |= selector_result::DECISION_COMPLETE_UNAFFECTED,
                8 => bad.base = None,
                9 => bad.decisions[0].base_node = NodeId::NONE,
                10 => bad.decisions[0].reasons &= !selector_result::DECISION_CLASSPATH_ABSENCE,
                _ => bad.decisions[0].status = selector_result::SuiteDecisionStatus::Required,
            }
            for compact in [false, true] {
                let mut bytes = Vec::new();
                let rendered = if compact {
                    write_compact_json(&mut bytes, &s, &bad)
                } else {
                    write_json(&mut bytes, &s, &bad)
                };
                assert!(rendered.is_err(), "case {change}, compact {compact}");
                assert!(bytes.is_empty());
            }
        }
        let schema: serde_json::Value =
            serde_json::from_str(include_str!("../output.schema.json")).unwrap();
        assert_eq!(
            schema["$defs"]["selectionContract"]["properties"]["bits"]["maximum"],
            2032
        );
        assert_eq!(
            schema["$defs"]["classpathExclusion"]["properties"]["exclusions"]["minItems"],
            2
        );
    }
    #[test]
    fn report_rejects_suite_mode_and_exclusion_assumption_disagreement_before_output() {
        let (facts, graph, mut result) = fixture();
        let snapshots = ReportSnapshots {
            base_facts: &facts,
            base_graph: &graph,
            head_facts: &facts,
            head_graph: &graph,
        };
        let certificate = selector_result::RootExclusion {
            snapshot: graph.identity,
            root: NodeId(0),
            certificate: ContentHash([7; 32]),
            assumptions: 1 | 16,
        };
        result.decisions[0].head_exclusion = Some(certificate);
        let mut bytes = Vec::new();
        assert!(write_json(&mut bytes, &snapshots, &result).is_err());
        assert!(bytes.is_empty());
        assert!(write_compact_json(&mut bytes, &snapshots, &result).is_err());
        assert!(bytes.is_empty());
        result.suite_semantics = SuiteSemantics::Independent;
        result.selection_contract = SelectionContract::from_bits(16).unwrap();
        assert!(validate_suite_semantics(&result).is_ok());
        result.decisions[0]
            .head_exclusion
            .as_mut()
            .unwrap()
            .assumptions = 1;
        assert!(validate_suite_semantics(&result).is_err());
        result.suite_semantics = SuiteSemantics::SharedState;
        result.selection_contract = SelectionContract::from_bits(0).unwrap();
        assert!(validate_suite_semantics(&result).is_ok());
        result.selection_contract = SelectionContract::current(SuiteSemantics::SharedState);
        assert!(validate_suite_semantics(&result).is_err());
        result.decisions[0]
            .head_exclusion
            .as_mut()
            .unwrap()
            .assumptions = 1 | SelectionContract::CURRENT_BASE_BITS;
        assert!(validate_suite_semantics(&result).is_ok());
    }
    #[test]
    fn effect_coverage_is_visible_separate_from_impact_and_rejects_stale_content() {
        let (facts, graph, mut result) = fixture();
        let snapshots = ReportSnapshots {
            base_facts: &facts,
            base_graph: &graph,
            head_facts: &facts,
            head_graph: &graph,
        };
        let render = |result: &SelectionResult| {
            let mut bytes = Vec::new();
            write_compact_json(&mut bytes, &snapshots, result).unwrap();
            serde_json::from_slice::<serde_json::Value>(&bytes).unwrap()
        };
        let json = render(&result);
        assert_eq!(json["execution_effects"]["head"]["state"], "unverified");
        assert!(json["execution_effects"]["head"]["coverage"].is_null());
        assert!(json["execution_effects"]["base"].is_null());
        let mut coverage = selector_result::EffectClosureCoverage {
            contexts: 2,
            evaluated_contexts: 2,
            open_contexts: 1,
            pending_work: 0,
            external_open: false,
        };
        result.head.record_execution_effects(coverage).unwrap();
        let json = render(&result);
        assert_eq!(json["execution_effects"]["head"]["state"], "open");
        assert_eq!(
            json["execution_effects"]["head"]["coverage"]["open_contexts"],
            1
        );
        coverage.open_contexts = 0;
        result.head.record_execution_effects(coverage).unwrap();
        let json = render(&result);
        assert_eq!(json["execution_effects"]["head"]["state"], "closed");
        assert_eq!(json["decisions"][0]["status"], "required");
        let mut full = Vec::new();
        write_json(&mut full, &snapshots, &result).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&full).unwrap();
        assert_eq!(json["head"]["execution_effects"]["state"], "closed");
        result.head.unscoped_uncertainty = true;
        assert!(write_compact_json(&mut Vec::new(), &snapshots, &result).is_err());
        assert!(write_json(&mut Vec::new(), &snapshots, &result).is_err());
    }
    #[test]
    fn compact_invalid_seed_and_decision_are_rejected_before_output() {
        let (facts, graph, mut result) = fixture();
        let snapshots = ReportSnapshots {
            base_facts: &facts,
            base_graph: &graph,
            head_facts: &facts,
            head_graph: &graph,
        };
        result.head_seeds = vec![NodeId(1)];
        let mut output = Vec::new();
        assert!(write_compact_json(&mut output, &snapshots, &result).is_err());
        assert!(output.is_empty());
        result.head_seeds = vec![NodeId(2)];
        result.decisions[0].status = selector_result::SuiteDecisionStatus::Excluded;
        assert!(write_compact_json(&mut output, &snapshots, &result).is_err());
        assert!(output.is_empty());
    }
    #[test]
    fn shared_heap_reason_is_checked_and_preserved_without_a_fabricated_runtime_boundary() {
        let (facts, graph, mut result) = fixture();
        let snapshots = ReportSnapshots {
            base_facts: &facts,
            base_graph: &graph,
            head_facts: &facts,
            head_graph: &graph,
        };
        result.completion = Completion::Conservative;
        result.decisions[0].guarded = true;
        result.suites[0].guarded = true;
        result.decisions[0].reasons |= selector_result::DECISION_OPAQUE_SHARED_HEAP;
        let mut compact = Vec::new();
        write_compact_json(&mut compact, &snapshots, &result).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&compact).unwrap();
        assert_eq!(json["decisions"][0]["status"], "required");
        assert_eq!(json["decisions"][0]["reasons"][1], "opaque_shared_heap");
        assert_eq!(json["decisions"][0]["uncertainty"], serde_json::json!([]));
        let mut full = Vec::new();
        write_json(&mut full, &snapshots, &result).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&full).unwrap();
        assert_eq!(json["suites"][0]["opaque_shared_heap"], true);
        let mut text = Vec::new();
        explain_suite(&mut text, &snapshots, &result, SuiteId(0)).unwrap();
        assert!(String::from_utf8(text).unwrap().contains("shared state"));
        result.decisions[0].guarded = false;
        result.suites[0].guarded = false;
        let mut output = Vec::new();
        assert!(write_compact_json(&mut output, &snapshots, &result).is_err());
        assert!(write_json(&mut output, &snapshots, &result).is_err());
        assert!(output.is_empty());
    }
    #[test]
    fn compact_scoped_unknown_names_actual_boundary_and_only_its_metadata() {
        let (facts, mut graph, mut result) = fixture();
        result.head.guarded_roots.push(NodeId(0));
        result.head.completion = Completion::Conservative;
        result.completion = Completion::Conservative;
        result.suites[0].guarded = true;
        result.decisions[0].guarded = true;
        result.decisions[0].reasons |= selector_result::DECISION_SCOPED_GUARD;
        result
            .head
            .evidence
            .guard_causes
            .push(selector_result::RootGuardEvidence {
                root: NodeId(0),
                node: NodeId(1),
                kind: IssueKind::UnsupportedModel,
                file: FileId(0),
                symbol: SymbolId(1),
                detail: StrId::NONE,
                runtime: None,
            });
        let mut add_text = |value: &str| {
            let start = graph.diagnostic_bytes.len() as u32;
            graph.diagnostic_bytes.extend_from_slice(value.as_bytes());
            IdRange {
                start,
                len: value.len() as u32,
            }
        };
        let reason = add_text("actual_router_join_missing");
        let path = add_text("src/métadata.ts");
        let unrelated = add_text("UNRELATED_BOUNDARY_METADATA");
        for (node, reason) in [(NodeId(1), reason), (NodeId(2), unrelated)] {
            graph.diagnostics.push(GraphDiagnostic {
                kind: IssueKind::UnsupportedModel,
                node,
                file: FileId(0),
                symbol: SymbolId(node.0),
                reason,
                metadata_path: path,
            });
        }
        let snapshots = ReportSnapshots {
            base_facts: &facts,
            base_graph: &graph,
            head_facts: &facts,
            head_graph: &graph,
        };
        let mut bytes = Vec::new();
        write_compact_json(&mut bytes, &snapshots, &result).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        let cause = &json["decisions"][0]["uncertainty"][0];
        assert_eq!(cause["boundary"]["node"], 1);
        assert_eq!(cause["boundary"]["kind"], "unsupported_model");
        assert_eq!(cause["metadata"].as_array().unwrap().len(), 1);
        assert_eq!(cause["metadata"][0]["reason"], "actual_router_join_missing");
        assert!(
            !String::from_utf8(bytes)
                .unwrap()
                .contains("UNRELATED_BOUNDARY_METADATA")
        );
        let mut text = Vec::new();
        write_compact_text(&mut text, &snapshots, &result).unwrap();
        let text = String::from_utf8(text).unwrap();
        assert!(text.contains("actual_router_join_missing"));
        assert!(text.contains("métadata.ts"));
        assert!(!text.contains("UNRELATED_BOUNDARY_METADATA"));
        result.head.evidence.guard_causes[0].root = NodeId(2);
        let mut invalid = Vec::new();
        assert!(write_compact_json(&mut invalid, &snapshots, &result).is_err());
        assert!(invalid.is_empty());
    }
    #[test]
    fn public_report_rejects_metadata_boundary_evidence_before_writing() {
        for control in 0..4 {
            let (facts, graph, mut result) = fixture();
            let issue = Obligation {
                kind: IssueKind::IncompleteHierarchy,
                file: FileId::NONE,
                symbol: SymbolId::NONE,
                detail: StrId::NONE,
            };
            match control {
                0 => result.head.obligations.push(issue),
                1 => result.obligations.push(issue),
                2 => {
                    result.head.guarded_roots.push(NodeId(0));
                    result
                        .head
                        .evidence
                        .guard_causes
                        .push(selector_result::RootGuardEvidence {
                            root: NodeId(0),
                            node: NodeId(1),
                            kind: issue.kind,
                            file: issue.file,
                            symbol: issue.symbol,
                            detail: issue.detail,
                            runtime: None,
                        });
                }
                _ => result.guard_causes.push(selector_result::ChangeGuardCause {
                    side: selector_result::SnapshotSide::Head,
                    reason: selector_result::ChangeGuardReason::UnscopedFactIssue,
                    kind: issue.kind,
                    file: issue.file,
                    symbol: issue.symbol,
                    detail: issue.detail,
                    path: None,
                    external: None,
                }),
            }
            let snapshots = ReportSnapshots {
                base_facts: &facts,
                base_graph: &graph,
                head_facts: &facts,
                head_graph: &graph,
            };
            let mut bytes = Vec::new();
            assert!(write_json(&mut bytes, &snapshots, &result).is_err());
            assert!(bytes.is_empty(), "full JSON {control}");
            assert!(write_compact_json(&mut bytes, &snapshots, &result).is_err());
            assert!(bytes.is_empty(), "compact JSON {control}");
            assert!(write_compact_text(&mut bytes, &snapshots, &result).is_err());
            assert!(bytes.is_empty(), "compact text {control}");
        }
    }
    #[test]
    fn requested_source_scope_reports_generated_delta_and_rejects_wrong_file_ids() {
        use selector_result::{SourceChangeMode, SourceChangeScope, SourceFileDelta};
        fn generated(facts: &mut FactSnapshot, hash: u8) {
            let mut intern = |value: &str| {
                let id = StrId(facts.strings.entries.len() as u32);
                facts.strings.entries.push(selector_facts::TextRange {
                    start: facts.strings.bytes.len() as u64,
                    len: value.len() as u32,
                });
                facts.strings.bytes.extend_from_slice(value.as_bytes());
                id
            };
            let path = intern("target/src_managed/BuildInfo.scala");
            let source = intern("object BuildInfo");
            let context = intern("project:generated:compile");
            facts.files.push(FileRecord {
                path,
                source,
                context,
                revision: StrId::NONE,
                source_hash: ContentHash([hash; 32]),
                flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
            });
        }
        let (mut base, graph, mut result) = fixture();
        let (mut head, _, _) = fixture();
        base.files[0].source_hash = ContentHash([1; 32]);
        head.files[0].source_hash = ContentHash([2; 32]);
        generated(&mut base, 3);
        generated(&mut head, 4);
        result.change_scope = Some(SourceChangeScope {
            mode: SourceChangeMode::RequestedPaths,
            requested_paths: vec!["a\"b.scala".into()],
            outside_count: 1,
            outside: vec![SourceFileDelta {
                base_file: FileId(1),
                head_file: FileId(1),
            }],
        });
        let snapshots = ReportSnapshots {
            base_facts: &base,
            base_graph: &graph,
            head_facts: &head,
            head_graph: &graph,
        };
        let mut bytes = Vec::new();
        write_compact_json(&mut bytes, &snapshots, &result).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        let scope = &json["change_scope"];
        assert_eq!(
            scope["effective_requested_source_paths"],
            serde_json::json!(["a\"b.scala"])
        );
        assert_eq!(scope["covers_captured_source_delta"], false);
        assert_eq!(scope["whole_checkout_omission_authority"], false);
        assert_eq!(
            scope["outside"][0]["path"],
            "target/src_managed/BuildInfo.scala"
        );
        assert_eq!(scope["outside"][0]["context"], "project:generated:compile");
        assert_eq!(
            scope["outside"][0]["base_source_sha256"],
            ContentHash([3; 32]).to_string()
        );
        assert_eq!(
            scope["outside"][0]["head_source_sha256"],
            ContentHash([4; 32]).to_string()
        );
        assert!(
            scope["notice"]
                .as_str()
                .unwrap()
                .contains("separate selection")
        );
        let mut audit = Vec::new();
        write_source_change_scope(&mut audit, &snapshots, result.change_scope.as_ref()).unwrap();
        assert_eq!(
            &serde_json::from_slice::<serde_json::Value>(&audit).unwrap(),
            scope
        );
        bytes.clear();
        write_json(&mut bytes, &snapshots, &result).unwrap();
        let full: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(scope, &full["change_scope"]);
        result.change_scope.as_mut().unwrap().outside[0].head_file = FileId(0);
        let mut invalid = Vec::new();
        assert!(write_compact_json(&mut invalid, &snapshots, &result).is_err());
        assert!(invalid.is_empty());
        result.change_scope.as_mut().unwrap().outside[0].head_file = FileId(1);
        result.change_scope.as_mut().unwrap().outside_count = 0;
        assert!(write_json(&mut Vec::new(), &snapshots, &result).is_err());
    }
    #[test]
    fn runtime_guard_sites_stream_checked_operation_and_source_span() {
        let (mut facts, mut graph, mut result) = fixture();
        facts.bodies.push(selector_facts::BodyRecord {
            symbol: SymbolId(1),
            file: FileId(0),
            span: Span { start: 0, end: 11 },
            name_span: Span::default(),
            operations: IdRange { start: 0, len: 1 },
            parameters: IdRange::default(),
            body_hash: ContentHash::default(),
            flags: 0,
        });
        facts.operations.push(selector_facts::OperationRecord {
            body: BodyId(0),
            opcode: Opcode::Unknown,
            target: SymbolId::NONE,
            dest: ValueId(1),
            a: ValueId::NONE,
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span { start: 6, end: 11 },
            flags: 0,
        });
        graph.nodes[1].body = BodyId(0);
        result.head.guarded_roots.push(NodeId(0));
        result.head.completion = Completion::Conservative;
        result.completion = Completion::Conservative;
        result.suites[0].guarded = true;
        result.decisions[0].guarded = true;
        result.decisions[0].reasons |= selector_result::DECISION_SCOPED_GUARD;
        result
            .head
            .evidence
            .guard_causes
            .push(selector_result::RootGuardEvidence {
                root: NodeId(0),
                node: NodeId(1),
                kind: IssueKind::UnknownExecution,
                file: FileId(0),
                symbol: SymbolId(1),
                detail: StrId::NONE,
                runtime: Some(RuntimeIssueSite {
                    kind: IssueKind::UnknownExecution,
                    operation: OperationId(0),
                    reason: RuntimeIssueReason::UnknownOperation,
                }),
            });
        let snapshots = ReportSnapshots {
            base_facts: &facts,
            base_graph: &graph,
            head_facts: &facts,
            head_graph: &graph,
        };
        let mut bytes = Vec::new();
        write_compact_json(&mut bytes, &snapshots, &result).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        let boundary = &json["decisions"][0]["uncertainty"][0]["boundary"];
        assert_eq!(boundary["runtime_reason"], "unknown_operation");
        assert_eq!(boundary["operation"], 0);
        assert_eq!(boundary["opcode"], "unknown");
        assert_eq!(boundary["operation_path"], "a\"b.scala");
        assert_eq!(boundary["span"], serde_json::json!({"start":6,"end":11}));
        bytes.clear();
        write_compact_text(&mut bytes, &snapshots, &result).unwrap();
        assert!(String::from_utf8(bytes).unwrap().contains(
            "runtime reason: unknown_operation; operation 0 (unknown); a\"b.scala bytes 6..11"
        ));
        bytes = Vec::new();
        write_json(&mut bytes, &snapshots, &result).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(json["head"]["evidence"]["guard_causes"][0]["operation"], 0);
        result.head.evidence.guard_causes[0]
            .runtime
            .as_mut()
            .unwrap()
            .operation = OperationId(1);
        let mut invalid = Vec::new();
        assert!(write_compact_json(&mut invalid, &snapshots, &result).is_err());
        assert!(invalid.is_empty());
        result.head.evidence.guard_causes[0]
            .runtime
            .as_mut()
            .unwrap()
            .operation = OperationId(0);
        graph.nodes[1].body = BodyId::NONE;
        let snapshots = ReportSnapshots {
            base_facts: &facts,
            base_graph: &graph,
            head_facts: &facts,
            head_graph: &graph,
        };
        assert!(write_compact_json(&mut Vec::new(), &snapshots, &result).is_err());
        result.head.evidence.guard_causes[0].runtime = Some(RuntimeIssueSite {
            kind: IssueKind::UnknownExecution,
            operation: OperationId::NONE,
            reason: RuntimeIssueReason::MissingExecutableBody,
        });
        let mut bytes = Vec::new();
        write_compact_json(&mut bytes, &snapshots, &result).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        let boundary = &json["decisions"][0]["uncertainty"][0]["boundary"];
        assert_eq!(boundary["runtime_reason"], "missing_executable_body");
        for field in ["operation", "opcode", "operation_path", "span"] {
            assert!(boundary[field].is_null());
        }
        graph.nodes[1].body = BodyId(0);
        facts.operations[0].opcode = Opcode::Call;
        facts.operations[0].target = SymbolId(0);
        result.head.evidence.guard_causes[0].runtime = Some(RuntimeIssueSite {
            kind: IssueKind::UnknownExecution,
            operation: OperationId(0),
            reason: RuntimeIssueReason::IncompleteDeferredCallback,
        });
        let snapshots = ReportSnapshots {
            base_facts: &facts,
            base_graph: &graph,
            head_facts: &facts,
            head_graph: &graph,
        };
        bytes.clear();
        write_compact_json(&mut bytes, &snapshots, &result).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(
            json["decisions"][0]["uncertainty"][0]["boundary"]["runtime_reason"],
            "incomplete_deferred_callback"
        );
        let schema: serde_json::Value =
            serde_json::from_str(include_str!("../output.schema.json")).unwrap();
        assert!(
            schema["$defs"]["guardBoundary"]["properties"]["runtime_reason"]["enum"]
                .as_array()
                .unwrap()
                .iter()
                .any(|reason| reason == "incomplete_deferred_callback")
        );
    }
    #[test]
    fn typed_constraints_are_reported_as_bounds_without_object_or_capture_identity() {
        let (mut facts, graph, mut result) = fixture();
        facts.bound_classes = vec![SymbolId(0), SymbolId(2)];
        facts.result_bounds.push(selector_facts::ResultBoundRecord {
            symbol: SymbolId(1),
            operation: OperationId::NONE,
            classes: IdRange { start: 0, len: 2 },
        });
        result
            .head
            .evidence
            .atoms
            .push(selector_result::EvidenceAtom {
                kind: 3,
                site: OperationId::NONE,
                symbol: SymbolId(1),
                binding: 0,
            });
        result
            .head
            .evidence
            .values
            .push(selector_result::EvidenceValue {
                atoms: IdRange { start: 0, len: 1 },
                unknown: 16,
            });
        validate_evidence(&facts, &graph, &result.head).unwrap();
        let mut bytes = Vec::new();
        write_evidence(&mut bytes, &facts, &graph, &result.head.evidence).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(json["atoms"][0]["constraint"], "static_result_constraint");
        assert_eq!(
            json["atoms"][0]["constraint_identity"],
            "exact_class_conjunction"
        );
        assert_eq!(json["atoms"][0]["origin_role"], "representative_clause");
        assert_eq!(
            json["atoms"][0]["upper_bounds"],
            serde_json::json!(["p/Suite#", "p/Target#f()."])
        );
        assert_eq!(json["atoms"][0]["site"], serde_json::Value::Null);
        assert_eq!(json["atoms"][0]["symbol_id"], 1);
        assert_eq!(json["values"][0]["unknown"], 16);
        assert!(json["captures"].as_array().unwrap().is_empty());
        let schema: serde_json::Value =
            serde_json::from_str(include_str!("../output.schema.json")).unwrap();
        for field in ["constraint_identity", "origin_role"] {
            assert_eq!(
                json["atoms"][0][field],
                schema["$defs"]["atom"]["properties"][field]["const"]
            );
        }
        bytes.clear();
        explain_value(&mut bytes, &facts, &result.head.evidence, 0).unwrap();
        let text = String::from_utf8(bytes).unwrap();
        assert!(
            text.contains("static result constraint p/Suite#test(). <= [p/Suite# & p/Target#f().]")
        );
        assert!(!text.contains("object "));
        assert!(!text.contains("capture"));
        assert!(text.contains("representative compiler clause"));
        result.head.evidence.atoms[0].binding = 1;
        assert!(validate_evidence(&facts, &graph, &result.head).is_err());
        result.head.evidence.atoms[0].binding = 0;
        result.head.evidence.atoms[0].site = OperationId(0);
        assert!(validate_evidence(&facts, &graph, &result.head).is_err());
        result.head.evidence.atoms[0].site = OperationId::NONE;
        facts.result_bounds.clear();
        assert!(validate_evidence(&facts, &graph, &result.head).is_err());
    }
    #[test]
    fn streaming_json_retains_full_evidence_and_escapes_text() {
        let (facts, graph, result) = fixture();
        let s = ReportSnapshots {
            base_facts: &facts,
            base_graph: &graph,
            head_facts: &facts,
            head_graph: &graph,
        };
        let mut output = Vec::new();
        write_json(&mut output, &s, &result).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(json["schema_version"], 1);
        assert_eq!(json["suites"][0]["name"], "Suite \"quoted\"\nname");
        assert_eq!(json["head"]["witnesses"].as_array().unwrap().len(), 2);
        assert_eq!(json["head"]["witnesses"][1]["derived"], true);
        assert_eq!(json["head"]["witnesses"][1]["kind"], "callback");
        let schema: serde_json::Value =
            serde_json::from_str(include_str!("../output.schema.json")).unwrap();
        for field in schema["oneOf"][0]["required"].as_array().unwrap() {
            assert!(json.get(field.as_str().unwrap()).is_some());
        }
    }
    #[test]
    fn explanation_iterates_static_and_derived_edges_without_tree_copy() {
        let (facts, graph, result) = fixture();
        let index = WitnessIndex::new(&graph, &result.head).unwrap();
        assert_eq!(index.owned_bytes(), result.head.affected.len() * 4);
        let chain: Vec<_> = index
            .chain(NodeId(0))
            .unwrap()
            .map(|s| s.unwrap().next)
            .collect();
        assert_eq!(chain, vec![NodeId(1), NodeId(2)]);
        let s = ReportSnapshots {
            base_facts: &facts,
            base_graph: &graph,
            head_facts: &facts,
            head_graph: &graph,
        };
        let mut output = Vec::new();
        explain_suite(&mut output, &s, &result, SuiteId(0)).unwrap();
        let text = String::from_utf8(output).unwrap();
        assert!(text.contains("--callback--> p/Target#f()."));
    }
    #[test]
    fn invalid_next_is_rejected_before_any_json_is_written() {
        let (facts, graph, mut result) = fixture();
        result.head.witnesses[0].next = NodeId(2);
        let s = ReportSnapshots {
            base_facts: &facts,
            base_graph: &graph,
            head_facts: &facts,
            head_graph: &graph,
        };
        let mut output = Vec::new();
        assert!(write_json(&mut output, &s, &result).is_err());
        assert!(output.is_empty());
    }
    #[test]
    fn cycles_and_out_of_range_derived_edge_ids_are_rejected() {
        let (_, graph, mut result) = fixture();
        result.head.derived_edges[0].target = NodeId(0);
        result.head.witnesses[1].next = NodeId(0);
        assert!(WitnessIndex::new(&graph, &result.head).is_err());
        result.head.witnesses[1].edge = EdgeId(2);
        assert!(WitnessIndex::new(&graph, &result.head).is_err());
    }
    #[test]
    fn human_output_lists_obligations_in_their_snapshot_scope() {
        let (facts, graph, mut result) = fixture();
        result.head.obligations.push(Obligation {
            kind: IssueKind::UnknownExecution,
            file: FileId(0),
            symbol: SymbolId(2),
            detail: StrId::NONE,
        });
        let s = ReportSnapshots {
            base_facts: &facts,
            base_graph: &graph,
            head_facts: &facts,
            head_graph: &graph,
        };
        let mut output = Vec::new();
        write_text(&mut output, &s, &result).unwrap();
        let text = String::from_utf8(output).unwrap();
        assert!(text.contains("obligation [head] unknown_execution"));
        assert!(text.contains("--callback-->"));
    }
    #[test]
    fn flat_context_evidence_is_checked_and_streamed_with_capture_bindings() {
        use selector_result::{
            CaptureEvidence, ContextEvidence, ContextWitness, EvidenceAtom, EvidenceValue,
        };
        let (facts, graph, mut result) = fixture();
        result.head.evidence.values.push(EvidenceValue {
            atoms: IdRange { start: 0, len: 1 },
            unknown: 0,
        });
        result.head.evidence.atoms.push(EvidenceAtom {
            kind: 2,
            site: OperationId::NONE,
            symbol: SymbolId(2),
            binding: 9,
        });
        result.head.evidence.captures.push(CaptureEvidence {
            binding: 9,
            receiver: 0,
            arguments: IdRange::default(),
        });
        for (id, node) in [(3, 0), (7, 1), (11, 2)] {
            result.head.evidence.contexts.push(ContextEvidence {
                id: ContextId(id),
                node: NodeId(node),
                receiver: 0,
                arguments: IdRange::default(),
            });
        }
        result.head.evidence.witnesses = vec![
            ContextWitness {
                context: ContextId(3),
                next: ContextId(7),
                edge: EdgeId(0),
                binding: u32::MAX,
            },
            ContextWitness {
                context: ContextId(7),
                next: ContextId(11),
                edge: EdgeId(1),
                binding: 9,
            },
        ];
        result.head.evidence.root_contexts.push(ContextId(3));
        let s = ReportSnapshots {
            base_facts: &facts,
            base_graph: &graph,
            head_facts: &facts,
            head_graph: &graph,
        };
        let mut out = Vec::new();
        write_json(&mut out, &s, &result).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&out).unwrap();
        assert_eq!(json["head"]["evidence"]["witnesses"][1]["binding"], 9);
        let mut text = Vec::new();
        explain_suite(&mut text, &s, &result, SuiteId(0)).unwrap();
        assert!(
            String::from_utf8(text)
                .unwrap()
                .contains("callback capture9")
        );
        result.head.evidence.witnesses[1].binding = 99;
        assert!(write_json(&mut Vec::new(), &s, &result).is_err());
    }
    #[test]
    fn object_origin_dictionary_preserves_prior_receivers_and_rejects_invalid_ids() {
        use selector_result::{AnalyzedRoot, EvidenceAtom};
        let (facts, graph, mut result) = fixture();
        result.head.evidence.requested_roots.push(AnalyzedRoot {
            node: NodeId(0),
            receiver: SymbolId(0),
        });
        for binding in [2, 1, 2, 0] {
            result.head.evidence.atoms.push(EvidenceAtom {
                kind: 1,
                site: OperationId::NONE,
                symbol: SymbolId(0),
                binding,
            });
        }
        let snapshots = ReportSnapshots {
            base_facts: &facts,
            base_graph: &graph,
            head_facts: &facts,
            head_graph: &graph,
        };
        let mut out = Vec::new();
        write_json(&mut out, &snapshots, &result).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&out).unwrap();
        let evidence = &json["head"]["evidence"];
        assert_eq!(evidence["heap_origins"].as_array().unwrap().len(), 2);
        assert_eq!(evidence["heap_origins"][0]["symbol_id"], 0);
        assert_eq!(evidence["heap_origins"][1]["symbol_id"], 1);
        assert_eq!(
            evidence["requested_roots"][0]["receiver_symbol"],
            "p/Suite#"
        );
        result.head.evidence.atoms[0].binding = u32::MAX;
        assert!(write_json(&mut Vec::new(), &snapshots, &result).is_err());
        result.head.evidence.atoms[0].binding = 1;
        result.head.evidence.atoms[0].symbol = SymbolId::NONE;
        assert!(write_json(&mut Vec::new(), &snapshots, &result).is_err());
    }
    #[test]
    fn unresolved_named_suite_is_reported_without_invented_node_or_witness() {
        let (mut facts, graph, mut result) = fixture();
        facts.suites[0].symbol = SymbolId::NONE;
        facts.suites[0].file = FileId::NONE;
        result.suites[0].node = NodeId::NONE;
        result.suites[0].guarded = true;
        result.completion = Completion::Conservative;
        let s = ReportSnapshots {
            base_facts: &facts,
            base_graph: &graph,
            head_facts: &facts,
            head_graph: &graph,
        };
        let mut out = Vec::new();
        write_json(&mut out, &s, &result).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&out).unwrap();
        assert!(json["suites"][0]["node"].is_null());
        assert_eq!(json["suites"][0]["name"], "Suite \"quoted\"\nname");
    }
    #[test]
    fn runtime_metadata_causes_preserve_scope_and_exclude_dormant_nodes() {
        let (facts, mut graph, mut result) = fixture();
        result.head.affected = vec![NodeId(0)];
        result.head.witnesses.clear();
        result.head.derived_edges.clear();
        result.head.guarded_roots.push(NodeId(0));
        result.head.completion = Completion::Conservative;
        result.suites[0].guarded = true;
        result.completion = Completion::Conservative;
        fn text(graph: &mut ProgramGraph, value: &str) -> IdRange {
            let start = graph.diagnostic_bytes.len() as u32;
            graph.diagnostic_bytes.extend_from_slice(value.as_bytes());
            IdRange {
                start,
                len: value.len() as u32,
            }
        }
        for (node, symbol, reason, path) in [
            (
                NodeId(0),
                SymbolId(0),
                "missing OpenAPI operation binding",
                "runtime/openapi.json",
            ),
            (
                NodeId(1),
                SymbolId(1),
                "unrelated dormant binding",
                "runtime/dormant.json",
            ),
            (
                NodeId::NONE,
                SymbolId::NONE,
                "runtime manifest unavailable",
                "runtime/manifest.json",
            ),
        ] {
            let reason = text(&mut graph, reason);
            let metadata_path = text(&mut graph, path);
            graph.diagnostics.push(selector_graph::GraphDiagnostic {
                kind: IssueKind::UnsupportedModel,
                node,
                file: FileId::NONE,
                symbol,
                reason,
                metadata_path,
            });
        }
        let s = ReportSnapshots {
            base_facts: &facts,
            base_graph: &graph,
            head_facts: &facts,
            head_graph: &graph,
        };
        let mut out = Vec::new();
        write_json(&mut out, &s, &result).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&out).unwrap();
        let diagnostics = json["head"]["runtime_diagnostics"].as_array().unwrap();
        assert_eq!(diagnostics.len(), 2);
        assert_eq!(
            diagnostics[0]["reason"],
            "missing OpenAPI operation binding"
        );
        assert_eq!(diagnostics[0]["metadata_path"], "runtime/openapi.json");
        assert_eq!(diagnostics[1]["scope"], "unscoped");
        let mut explained = Vec::new();
        explain_suite(&mut explained, &s, &result, SuiteId(0)).unwrap();
        let explained = String::from_utf8(explained).unwrap();
        assert!(explained.contains("missing OpenAPI operation binding"));
        assert!(explained.contains("runtime/openapi.json"));
        assert!(!explained.contains("unrelated dormant binding"));
        let valid = graph.diagnostics[0].reason;
        graph.diagnostics[0].reason.len = u32::MAX;
        let s = ReportSnapshots {
            base_facts: &facts,
            base_graph: &graph,
            head_facts: &facts,
            head_graph: &graph,
        };
        assert!(write_json(&mut Vec::new(), &s, &result).is_err());
        graph.diagnostics[0].reason = valid;
        graph.diagnostics[0].file = FileId(99);
        let s = ReportSnapshots {
            base_facts: &facts,
            base_graph: &graph,
            head_facts: &facts,
            head_graph: &graph,
        };
        assert!(write_json(&mut Vec::new(), &s, &result).is_err());
    }
}
