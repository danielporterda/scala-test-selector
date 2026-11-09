//! Compact query outputs independent of the solver implementation.
use selector_issue::RuntimeIssueSite;
use selector_types::*;
mod effects;
pub use effects::{EffectClosure, EffectClosureCoverage, ExecutionEffectEvidence};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WitnessStep {
    pub node: NodeId,
    pub next: NodeId,
    pub edge: EdgeId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Obligation {
    pub kind: IssueKind,
    pub file: FileId,
    pub symbol: SymbolId,
    pub detail: StrId,
}

/// Query-derived edges retain callsite provenance without mutating static graphs.
/// Their witness IDs start at the static graph's edge count.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct DerivedEdge {
    pub source: NodeId,
    pub target: NodeId,
    pub kind: EdgeKind,
    pub operation: OperationId,
    pub receiver: SymbolId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EvidenceAtom {
    pub kind: u32,
    pub site: OperationId,
    pub symbol: SymbolId,
    /// Object: finite receiver-origin SymbolId + 1, or zero for a coarse
    /// object. Container: the same finite receiver origin, without a class
    /// identity. Callback: capture binding ID. Static constraint: zero.
    /// An origin describes retained identity, not current root membership.
    pub binding: u32,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EvidenceValue {
    pub atoms: IdRange,
    pub unknown: u32,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ContextEvidence {
    pub id: ContextId,
    pub node: NodeId,
    pub receiver: u32,
    pub arguments: IdRange,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CaptureEvidence {
    pub binding: u32,
    pub receiver: u32,
    pub arguments: IdRange,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ContextWitness {
    pub context: ContextId,
    pub next: ContextId,
    pub edge: EdgeId,
    pub binding: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct AnalyzedRoot {
    pub node: NodeId,
    pub receiver: SymbolId,
}

/// One actual reached unresolved boundary per guarded root. This is an exemplar,
/// not a claim that the root has no other uncertainty. IDs bind to this analysis.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RootGuardEvidence {
    pub root: NodeId,
    pub node: NodeId,
    pub kind: IssueKind,
    pub file: FileId,
    pub symbol: SymbolId,
    pub detail: StrId,
    /// Present only for an actual runtime issue in the chosen boundary context.
    pub runtime: Option<RuntimeIssueSite>,
}

/// Flat detached proof data; references neither the mutable solver nor its pools.
#[derive(Debug, Default)]
pub struct AnalysisEvidence {
    /// Separately certified effect coverage. Data uncertainty can still leave
    /// the same root guarded; this is never an execution-impact certificate.
    pub execution_effects: ExecutionEffectEvidence,
    // Separate issuer binding rejects transplanting a public closure token,
    // even when two runs have identical detached guards but different histories.
    execution_effect_binding: Option<ContentHash>,
    /// Canonical exact requested execution frontier, including pending roots on
    /// budget stop. This binds result scope; observed reachability is no absence proof.
    pub requested_roots: Vec<AnalyzedRoot>,
    // A rooted solver records these directly from its context call graph.
    // None is legacy/projected analysis; Some(empty) is a rooted run with no hit.
    root_impacts: Option<Vec<AnalyzedRoot>>,
    pub guard_causes: Vec<RootGuardEvidence>,
    pub atoms: Vec<EvidenceAtom>,
    pub values: Vec<EvidenceValue>,
    /// Context/capture argument ranges index this array of canonical value IDs.
    pub value_ids: Vec<u32>,
    pub contexts: Vec<ContextEvidence>,
    pub captures: Vec<CaptureEvidence>,
    pub witnesses: Vec<ContextWitness>,
    pub root_contexts: Vec<ContextId>,
}
impl AnalysisEvidence {
    pub fn root_impacts(&self) -> Option<&[AnalyzedRoot]> {
        self.root_impacts.as_deref()
    }
}

#[derive(Debug, Default)]
pub struct CompilationImpact {
    pub affected: Vec<NodeId>,
    pub witnesses: Vec<WitnessStep>,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct AnalysisMetrics {
    pub states: u64,
    pub edge_visits: u64,
    pub novel_facts: u64,
    pub repeated_facts: u64,
    pub summary_hits: u64,
    pub invalidations: u64,
    pub queued_peak: u64,
    pub owned_bytes: u64,
    pub workers: usize,
    pub elapsed_ns: u64,
}

#[derive(Debug)]
pub struct AnalysisResult {
    pub snapshot: ContentHash,
    pub completion: Completion,
    pub affected: Vec<NodeId>,
    pub witnesses: Vec<WitnessStep>,
    pub derived_edges: Vec<DerivedEdge>,
    pub obligations: Vec<Obligation>,
    /// Suite/root nodes that can reach a scoped unresolved execution boundary.
    pub guarded_roots: Vec<NodeId>,
    /// The uncertainty has no complete root/source scope (including budget stop).
    pub unscoped_uncertainty: bool,
    pub evidence: AnalysisEvidence,
    /// Compilation relationships are reported independently from execution impact.
    pub compilation: CompilationImpact,
    pub metrics: AnalysisMetrics,
}
impl AnalysisResult {
    pub fn contains(&self, node: NodeId) -> bool {
        self.affected.binary_search(&node).is_ok()
    }

    /// Observed impact of the requested binding, rather than of an arbitrary
    /// invocation of the same compiler node under a different receiver/frame.
    pub fn root_reached(&self, node: NodeId, receiver: SymbolId) -> bool {
        self.root_impacts().map_or_else(
            || self.contains(node),
            |roots| {
                roots
                    .binary_search(&AnalyzedRoot { node, receiver })
                    .is_ok()
            },
        )
    }

    pub fn root_impacts(&self) -> Option<&[AnalyzedRoot]> {
        self.evidence.root_impacts()
    }

    /// Trusted rooted-producer boundary. These rows are positive impact
    /// evidence only: pending roots and unresolved effects still guard selection.
    pub fn record_root_impacts(&mut self, roots: Vec<AnalyzedRoot>) -> Result<(), Error> {
        if self.evidence.root_impacts.is_some()
            || self.evidence.execution_effects.state() != EffectClosure::Unverified
            || roots.windows(2).any(|pair| pair[0] >= pair[1])
            || roots.iter().any(|root| {
                !self.contains(root.node)
                    || self.evidence.requested_roots.binary_search(root).is_err()
            })
        {
            return Err(Error::Invalid("observed execution root impact"));
        }
        self.evidence.root_impacts = Some(roots);
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SelectedSuite {
    pub suite: SuiteId,
    pub node: NodeId,
    pub guarded: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SnapshotSide {
    Base,
    Head,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChangeGuardReason {
    UncapturedChangedPath,
    UnverifiedSource,
    UnverifiedSyntax,
    NoDeclarations,
    UnscopedFactIssue,
    MissingDeclarationNode,
    ExternalInput,
    UnspecifiedFallback,
}

/// Exact cause of a changed-input guard. IDs belong to `side`; only paths absent
/// from the snapshot need owned text. This survives dropping comparison indexes.
#[derive(Debug)]
pub struct ChangeGuardCause {
    pub side: SnapshotSide,
    pub reason: ChangeGuardReason,
    pub kind: IssueKind,
    pub file: FileId,
    pub symbol: SymbolId,
    pub detail: StrId,
    pub path: Option<String>,
    pub external: Option<Box<ExternalGuardDetail>>,
}

#[derive(Debug)]
pub struct ExternalGuardDetail {
    pub reason: String,
    pub message: String,
    pub suite_name: Option<String>,
    pub schema_path: Option<String>,
    pub operation_path: Option<String>,
    pub verb: Option<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SuiteDecisionStatus {
    Required,
    Unknown,
    Excluded,
}

pub const DECISION_HEAD_IMPACT: u32 = 1;
pub const DECISION_BASE_IMPACT: u32 = 2;
pub const DECISION_SCOPED_GUARD: u32 = 4;
pub const DECISION_CHANGED_INPUT_GUARD: u32 = 8;
pub const DECISION_QUERY_UNSCOPED: u32 = 16;
pub const DECISION_RESOURCE_LIMIT: u32 = 32;
pub const DECISION_MISSING_ROOT: u32 = 64;
pub const DECISION_COMPLETE_UNAFFECTED: u32 = 128;
pub const DECISION_CERTIFIED_EXCLUSION: u32 = 256;
pub const DECISION_PLAN_REFUTED: u32 = 512;
/// A changed or unresolved writer may mutate shared state read by this root.
/// This is potential cross-root exposure, not an observed execution boundary.
pub const DECISION_OPAQUE_SHARED_HEAP: u32 = 1024;
/// Paired source products are absent from the suite's owning captured test classpath.
/// This conditional certificate is independent of runtime execution completion.
pub const DECISION_CLASSPATH_ABSENCE: u32 = 2048;

/// An exclusion certificate bound to immutable snapshots, roots, scoped inputs
/// and explicit assumptions. Decision reasons distinguish ordinary potential-plan
/// proofs from paired owning-classpath absence proofs; neither is an observed
/// execution-coverage claim.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RootExclusion {
    pub snapshot: ContentHash,
    pub root: NodeId,
    pub certificate: ContentHash,
    pub assumptions: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SuiteDecision {
    pub suite: SuiteId,
    pub node: NodeId,
    pub base_node: NodeId,
    pub status: SuiteDecisionStatus,
    pub guarded: bool,
    pub reasons: u32,
    pub head_exclusion: Option<RootExclusion>,
    pub base_exclusion: Option<RootExclusion>,
}

#[derive(Debug)]
pub struct SelectionResult {
    pub base_snapshot: ContentHash,
    pub head_snapshot: ContentHash,
    /// Explicit isolation assumption, independently of physical runner mode.
    pub suite_semantics: SuiteSemantics,
    pub selection_contract: SelectionContract,
    pub completion: Completion,
    pub suites: Vec<SelectedSuite>,
    pub base: Option<AnalysisResult>,
    pub head: AnalysisResult,
    pub obligations: Vec<Obligation>,
    pub guard_causes: Vec<ChangeGuardCause>,
    pub decisions: Vec<SuiteDecision>,
    pub base_seeds: Vec<NodeId>,
    pub head_seeds: Vec<NodeId>,
    /// None for legacy/manual seeds whose requested source scope is unknown.
    pub change_scope: Option<SourceChangeScope>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceChangeMode {
    RequestedPaths,
    SnapshotDelta,
}

/// Exact contextual file identities; a missing revision uses FileId::NONE.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceFileDelta {
    pub base_file: FileId,
    pub head_file: FileId,
}

pub const MAX_OUTSIDE_SOURCE_DELTAS: usize = 64;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceChangeScope {
    pub mode: SourceChangeMode,
    /// Canonical effective source paths after auxiliary runtime input handling.
    pub requested_paths: Vec<String>,
    pub outside_count: u64,
    /// Canonical first MAX_OUTSIDE_SOURCE_DELTAS contextual physical deltas.
    pub outside: Vec<SourceFileDelta>,
}
