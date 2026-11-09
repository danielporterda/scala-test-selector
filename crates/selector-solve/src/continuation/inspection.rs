//! Validated read-only paused state. Recorded solver identities are descriptive
//! here: this view cannot resume execution or certify a selection outcome.
mod root_frontier;
pub use root_frontier::RootFrontier;

use super::*;
use std::cmp::{Ordering as Compare, Reverse};
use std::collections::BinaryHeap;

#[derive(Clone, Debug)]
pub struct InspectionLimits {
    pub memory_budget_bytes: usize,
    pub max_artifact_bytes: u64,
    pub max_contexts: usize,
    pub max_set_members: usize,
    pub max_rows: usize,
}
impl Default for InspectionLimits {
    fn default() -> Self {
        Self {
            memory_budget_bytes: 2 * 1024 * 1024 * 1024,
            max_artifact_bytes: 1024 * 1024 * 1024,
            max_contexts: 1_000_000,
            max_set_members: 65_536,
            max_rows: 1024,
        }
    }
}

#[derive(Clone, Debug)]
pub struct CheckpointHeader {
    pub version: u32,
    pub artifact: ContentHash,
    pub producer: ContentHash,
    pub facts: ContentHash,
    pub graph: ContentHash,
    pub content_seal: ContentHash,
    /// The declaration digest is retained as recorded metadata. It is never
    /// accepted as a caller's execution frontier for a resumable session.
    pub execution_roots: ContentHash,
    pub max_set_members: usize,
    pub quantum: usize,
    pub context_policy: ContextPolicy,
    pub contexts: usize,
    pub frames: usize,
    pub value_sets: usize,
    pub runtime_issue_sites: usize,
    /// Receiver-origin owner rows; legacy checkpoints retain coarse state.
    pub heap_owners: usize,
    /// Immutable callback-code shapes are recorded only by checkpoint 4+.
    pub callback_shapes: usize,
    /// Includes all contexts for legacy snapshots without closure evidence.
    pub effects_open_contexts: usize,
    pub rounds: u64,
    pub completion: Completion,
    pub stop: Option<StopReason>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct NodeInventory {
    pub node: NodeId,
    pub contexts: u64,
    pub receiver_variants: u64,
    pub max_argument_frames_per_receiver: u64,
    pub largest_receiver_context: ContextId,
    pub largest_receiver_variants: u64,
    pub evaluated_contexts: u64,
    pub widened_contexts: u64,
    /// Sum of saved context publication versions, not evaluations or time.
    pub publication_versions: u64,
}
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct InventorySummary {
    pub contexts: usize,
    pub nodes: usize,
    pub rows: usize,
    pub retained_bytes: usize,
    pub scratch_bytes: usize,
}
#[derive(Clone, Debug)]
pub struct ContextInventory {
    pub summary: InventorySummary,
    pub rows: Vec<NodeInventory>,
}

/// The private session is an implementation detail. In particular, no mutable
/// session, resume, selection, or completed-summary publication API is exposed.
///
/// ```compile_fail
/// use selector_solve::continuation::inspection::CheckpointView;
/// fn cannot_resume(view: &mut CheckpointView<'_>) {
///     view.resume().unwrap();
/// }
/// ```
/// ```compile_fail
/// use selector_solve::continuation::inspection::CheckpointView;
/// fn cannot_publish(view: &CheckpointView<'_>) {
///     view.persist_completed().unwrap();
/// }
/// ```
pub struct CheckpointView<'a> {
    session: QuerySession<'a>,
    header: CheckpointHeader,
    limits: InspectionLimits,
}
impl<'a> CheckpointView<'a> {
    pub fn open(
        facts: &'a FactSnapshot,
        graph: &'a ProgramGraph,
        path: &Path,
        limits: &InspectionLimits,
    ) -> Result<Self, Error> {
        if limits.memory_budget_bytes == 0
            || limits.max_artifact_bytes == 0
            || limits.max_contexts == 0
            || limits.max_set_members == 0
            || limits.max_rows > 65_536
        {
            return Err(Error::Invalid("checkpoint inspection limits"));
        }
        let artifact = selector_artifacts::open_bounded(
            path,
            ArtifactKind::Continuation,
            limits
                .max_artifact_bytes
                .min(limits.memory_budget_bytes as u64),
        )
        .map_err(artifact_error)?;
        if artifact.count(1).map_err(artifact_error)? != 1
            || artifact.section(1).map_err(artifact_error)?.len() != META_BYTES
        {
            return Err(Error::Invalid("checkpoint inspection header"));
        }
        let mut decoder = Decoder::new(artifact.section(1).map_err(artifact_error)?);
        let version = decoder.n()?;
        let sections = section_count(version).ok_or(Error::Invalid("checkpoint version"))?;
        if artifact.section_ids().ne(1..=sections) {
            return Err(Error::Invalid("checkpoint inspection header"));
        }
        let producer = ContentHash(decoder.take()?);
        let recorded_facts = ContentHash(decoder.take()?);
        let recorded_graph = ContentHash(decoder.take()?);
        let content_seal = ContentHash(decoder.take()?);
        let max_set_members =
            usize::try_from(decoder.q()?).map_err(|_| Error::Limit("inspection set size"))?;
        let quantum =
            usize::try_from(decoder.q()?).map_err(|_| Error::Limit("inspection quantum"))?;
        let tag = decoder.n()?;
        let cap =
            usize::try_from(decoder.q()?).map_err(|_| Error::Limit("inspection context policy"))?;
        let context_policy = match (tag, cap) {
            (0, 0) => ContextPolicy::Exact,
            (1, cap) if cap > 0 => ContextPolicy::BoundedArguments {
                max_variants_per_receiver: cap,
            },
            _ => return Err(Error::Invalid("checkpoint context policy")),
        };
        let execution_roots = ContentHash(decoder.take()?);
        if max_set_members == 0 || max_set_members > limits.max_set_members || quantum == 0 {
            return Err(Error::Limit("checkpoint inspection semantic limits"));
        }
        let count = |id| {
            usize::try_from(artifact.count(id).map_err(artifact_error)?)
                .map_err(|_| Error::Limit("checkpoint inspection count"))
        };
        let contexts = count(6)?;
        if contexts > limits.max_contexts {
            return Err(Error::Limit("checkpoint retained context limit"));
        }
        // Charge initial program indexes before constructing their input-sized
        // vectors. The shared decoder separately preflights every saved table.
        let parents = facts
            .relations
            .iter()
            .filter(|row| row.kind == RelationKind::Parent)
            .count();
        let initial_peak = [
            (facts.symbols.len(), 128usize), // TypeIndex and reusable DFS peak
            (parents, 8),
            (facts.bodies.len(), 16),
            (facts.result_bounds.len(), 64),
            (graph.nodes.len(), 24),
            (facts.files.len(), 24),
            (graph.issues.len(), 48),
            (graph.edges.len(), 2), // CSR validation bit sets
        ]
        .into_iter()
        .try_fold(artifact.byte_len(), |sum, (count, width)| {
            count.checked_mul(width).and_then(|n| sum.checked_add(n))
        })
        .and_then(|n| n.checked_add(16 * 1024))
        .ok_or(Error::Limit("checkpoint inspection memory"))?;
        if initial_peak > limits.memory_budget_bytes {
            return Err(Error::Limit("checkpoint inspection memory"));
        }
        let mut header = CheckpointHeader {
            version,
            artifact: ContentHash(artifact.identity()),
            producer,
            facts: recorded_facts,
            graph: recorded_graph,
            content_seal,
            execution_roots,
            max_set_members,
            quantum,
            context_policy,
            contexts,
            frames: count(4)?,
            value_sets: count(2)?,
            runtime_issue_sites: if version == 1 { 0 } else { count(20)? },
            heap_owners: if version < 3 { 0 } else { count(21)? },
            callback_shapes: if version < 4 { 0 } else { count(23)? },
            effects_open_contexts: 0,
            rounds: 0,
            completion: Completion::ResourceLimited,
            stop: None,
        };
        let options = SolveOptions {
            workers: 1,
            memory_budget_bytes: limits.memory_budget_bytes,
            max_contexts: limits.max_contexts,
            max_set_members,
            quantum,
            context_policy,
            scratch_bytes_per_worker: 4096,
            census: CensusOptions {
                capacity: 0,
                evaluation_stride: 1,
            },
            retain_context_evidence: false,
            ..Default::default()
        };
        let runtime = SolverRuntime::new(&options)?;
        let session = QuerySession::restore_checkpoint(
            facts,
            graph,
            &options,
            &runtime,
            path,
            producer,
            Some(artifact),
            Some(execution_roots.0),
        )?;
        header.rounds = session.rounds;
        header.completion = session.completion;
        header.stop = session.stop_reason;
        header.effects_open_contexts = session.contexts.iter().filter(|c| c.effects_open).count();
        Ok(Self {
            session,
            header,
            limits: limits.clone(),
        })
    }
    pub fn header(&self) -> &CheckpointHeader {
        &self.header
    }
    pub fn owned_bytes(&self) -> usize {
        self.session.owned_bytes()
    }
    pub fn counters(&self) -> WorkCounters {
        self.session.counters
    }

    pub fn context_inventory(&self, top_rows: usize) -> Result<ContextInventory, Error> {
        if top_rows > self.limits.max_rows {
            return Err(Error::Limit("checkpoint inventory rows"));
        }
        let scratch_bytes = self
            .session
            .contexts
            .len()
            .checked_mul(std::mem::size_of::<u32>())
            .and_then(|n| {
                top_rows
                    .checked_mul(2 * std::mem::size_of::<Ranked>())
                    .and_then(|m| n.checked_add(m))
            })
            .ok_or(Error::Limit("checkpoint inventory memory"))?;
        if self
            .owned_bytes()
            .checked_add(scratch_bytes)
            .is_none_or(|n| n > self.limits.memory_budget_bytes)
        {
            return Err(Error::Limit("checkpoint inventory memory"));
        }
        let mut order = Vec::new();
        order
            .try_reserve_exact(self.session.contexts.len())
            .map_err(|_| Error::Limit("checkpoint inventory allocation"))?;
        order.extend(0..self.session.contexts.len() as u32);
        order.sort_unstable_by_key(|id| {
            let key = self.session.contexts[*id as usize].key;
            (
                key.node.0,
                key.receiver.set.0,
                key.receiver.unknown,
                key.arguments.0,
            )
        });
        let mut top = BinaryHeap::new();
        top.try_reserve_exact(top_rows)
            .map_err(|_| Error::Limit("checkpoint inventory allocation"))?;
        let mut nodes = 0usize;
        let mut at = 0;
        while at < order.len() {
            let node = self.session.contexts[order[at] as usize].key.node;
            let mut row = NodeInventory {
                node,
                largest_receiver_context: ContextId::NONE,
                ..Default::default()
            };
            while at < order.len() && self.session.contexts[order[at] as usize].key.node == node {
                let receiver = self.session.contexts[order[at] as usize].key.receiver;
                row.receiver_variants += 1;
                let mut frames = 0u64;
                let mut receiver_contexts = 0u64;
                let mut anchor = ContextId(order[at]);
                let mut last = None;
                while at < order.len() {
                    let c = self.session.contexts[order[at] as usize];
                    if c.key.node != node || c.key.receiver != receiver {
                        break;
                    }
                    row.contexts += 1;
                    receiver_contexts += 1;
                    anchor = anchor.min(ContextId(order[at]));
                    row.evaluated_contexts += u64::from(c.evaluated);
                    row.widened_contexts += u64::from(c.widened);
                    row.publication_versions = row
                        .publication_versions
                        .checked_add(c.version)
                        .ok_or(Error::Invalid("checkpoint publication count overflow"))?;
                    if last != Some(c.key.arguments) {
                        frames += 1;
                        last = Some(c.key.arguments);
                    }
                    at += 1;
                }
                row.max_argument_frames_per_receiver =
                    row.max_argument_frames_per_receiver.max(frames);
                if (receiver_contexts, Reverse(anchor))
                    > (
                        row.largest_receiver_variants,
                        Reverse(row.largest_receiver_context),
                    )
                {
                    row.largest_receiver_variants = receiver_contexts;
                    row.largest_receiver_context = anchor;
                }
            }
            nodes += 1;
            if top_rows > 0 {
                if top.len() < top_rows {
                    top.push(Reverse(Ranked(row)));
                } else if top.peek().is_some_and(|least| Ranked(row) > least.0) {
                    *top.peek_mut().unwrap() = Reverse(Ranked(row));
                }
            }
        }
        let rows = top
            .into_sorted_vec()
            .into_iter()
            .map(|row| row.0.0)
            .collect::<Vec<_>>();
        Ok(ContextInventory {
            summary: InventorySummary {
                contexts: order.len(),
                nodes,
                rows: rows.len(),
                retained_bytes: self.owned_bytes(),
                scratch_bytes,
            },
            rows,
        })
    }
    pub fn visit_inventory(
        &self,
        top_rows: usize,
        mut visit: impl FnMut(NodeInventory, WorkOrigin<'_>),
    ) -> Result<InventorySummary, Error> {
        let inventory = self.context_inventory(top_rows)?;
        for row in inventory.rows {
            let node = self.session.graph.nodes[row.node.index()];
            let symbol = self.session.facts.symbols[node.symbol.index()];
            visit(
                row,
                WorkOrigin {
                    symbol: self.session.facts.symbol_name(node.symbol),
                    context: self.session.facts.text(symbol.context),
                    path: self.session.facts.path(node.file),
                },
            );
        }
        Ok(inventory.summary)
    }
    pub fn export_replay(
        &self,
        node: NodeId,
        context: Option<ContextId>,
        directory: &Path,
        limits: &replay::ReplayLimits,
    ) -> Result<replay::ReplayExportReport, Error> {
        self.check_export_budget(limits)?;
        self.session.export_replay(node, context, directory, limits)
    }
    /// Export every recorded frame in the selected method/receiver family,
    /// including pending inputs. This is a diagnostic publication snapshot,
    /// never a fixed-point or selection certificate.
    pub fn export_replay_family(
        &self,
        node: NodeId,
        receiver_context: Option<ContextId>,
        directory: &Path,
        limits: &replay::ReplayLimits,
        max_contexts: usize,
    ) -> Result<replay::ReplayFamilyReport, Error> {
        self.check_export_budget(limits)?;
        self.session
            .export_replay_family(node, receiver_context, directory, limits, max_contexts)
    }
    fn check_export_budget(&self, limits: &replay::ReplayLimits) -> Result<(), Error> {
        if self.header.version < VERSION {
            return Err(Error::Invalid(
                "legacy checkpoint replay requires frozen legacy operator",
            ));
        }
        if self
            .owned_bytes()
            .checked_add(limits.max_bytes)
            .and_then(|n| n.checked_add(limits.scratch_bytes))
            .is_none_or(|n| n > self.limits.memory_budget_bytes)
        {
            return Err(Error::Limit("checkpoint replay export memory"));
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Ranked(NodeInventory);
impl Ord for Ranked {
    fn cmp(&self, other: &Self) -> Compare {
        (
            self.0.contexts,
            self.0.publication_versions,
            Reverse(self.0.node),
        )
            .cmp(&(
                other.0.contexts,
                other.0.publication_versions,
                Reverse(other.0.node),
            ))
    }
}
impl PartialOrd for Ranked {
    fn partial_cmp(&self, other: &Self) -> Option<Compare> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use selector_artifacts::Section;

    /// An opt-in observation of the current reader over the original retained
    /// legacy publication. It never evaluates a context or exports a replay.
    #[test]
    #[ignore = "requires retained PR7743 artifacts and SELECTOR_LEGACY_MARKER_CONTROL_OUTPUT"]
    fn legacy_read_world_missing_marker_control() {
        let output = std::env::var_os("SELECTOR_LEGACY_MARKER_CONTROL_OUTPUT")
            .map(PathBuf::from)
            .expect("set SELECTOR_LEGACY_MARKER_CONTROL_OUTPUT to the control JSON path");
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .canonicalize()
            .unwrap();
        let facts_path = root.join("artifacts/pr7743-final/head/enriched.bin");
        let graph_path = root.join("artifacts/pr7743-final/head/graph.bin");
        let checkpoint_path =
            root.join("benchmark-output/phase2-work-census/pr7743-exact/checkpoints/head.bin");
        let facts = selector_facts::codec::read(&facts_path).unwrap();
        let graph = selector_graph::codec::read_bound(&graph_path, facts.identity).unwrap();
        assert_eq!(facts.operations.len(), 2_658_360);
        let view = CheckpointView::open(
            &facts,
            &graph,
            &checkpoint_path,
            &InspectionLimits {
                memory_budget_bytes: 4 * 1024 * 1024 * 1024,
                ..Default::default()
            },
        )
        .unwrap();
        assert_eq!(view.header.version, 1);
        assert_eq!(view.header.completion, Completion::ResourceLimited);
        assert_eq!(view.header.stop, Some(StopReason::StepLimit));
        assert!(!view.session.ready.is_empty());
        let s = &view.session;
        let world = ReadWorld {
            facts: s.facts,
            graph: s.graph,
            types: &s.types,
            pool: &s.pool,
            frames: &s.frames,
            contexts: &s.contexts,
            index: &s.index,
            callback_shapes: &s.callback_shapes,
            slots: &s.slots,
            heap_owners: &s.heap_owners,
            captures: &s.captures,
            families: &s.closure_families,
            capture_origins: &s.capture_origins,
            context_policy: s.options.context_policy,
            provider_scope: None,
        };
        let source_root = SymbolId(31_621);
        let owner = 2_689_981;
        assert_eq!(owner as usize, facts.operations.len() + source_root.index());
        let mut observed = Vec::new();
        let mut rows = Vec::new();
        for member in [822_064, 821_757, 821_992, 821_756] {
            for kind in [SlotKind::Field, SlotKind::FieldMissing] {
                let slot = Slot {
                    kind,
                    owner,
                    member,
                };
                // This calls the production World implementation, using only
                // the tables admitted by the public read-only checkpoint view.
                let (value, version, present) = World::slot(&world, slot);
                observed.push((slot, value, version, present));
                let members = world
                    .values()
                    .members(value)
                    .iter()
                    .map(|atom| {
                        serde_json::json!({
                            "kind": format!("{:?}", atom.kind),
                            "site": atom.site.0,
                            "symbol": atom.symbol.0,
                            "binding": atom.binding,
                        })
                    })
                    .collect::<Vec<_>>();
                rows.push(serde_json::json!({
                    "kind": format!("{kind:?}"),
                    "owner": owner,
                    "member": member,
                    "set": value.set.0,
                    "unknown": value.unknown,
                    "members": members,
                    "version": version,
                    "present": present,
                }));
            }
        }
        let report = serde_json::json!({
            "schema": "selector-legacy-read-world-marker-control/v1",
            "basis": "current ReadWorld over explicitly legacy-adapted read-only state",
            "receiver_origin_precision": false,
            "facts": {"path": facts_path, "identity": facts.identity.to_string(), "operations": facts.operations.len(), "symbols": facts.symbols.len()},
            "graph": {"path": graph_path, "identity": graph.identity.to_string()},
            "checkpoint": {
                "path": checkpoint_path,
                "artifact": view.header.artifact.to_string(),
                "version": view.header.version,
                "producer": view.header.producer.to_string(),
                "facts": view.header.facts.to_string(),
                "graph": view.header.graph.to_string(),
                "content_seal": view.header.content_seal.to_string(),
                "completion": format!("{:?}", view.header.completion),
                "stop": format!("{:?}", view.header.stop),
                "rounds": view.header.rounds,
                "contexts": view.header.contexts,
                "ready": s.ready.len(),
                "retained_bytes": view.owned_bytes(),
            },
            "source_root_symbol": source_root.0,
            "source_root_name": facts.symbol_name(source_root),
            "current_solve_producer": std::env::var("SELECTOR_CURRENT_SOLVE_PRODUCER").ok(),
            "compiled_read_world_source_sha256": ContentHash(Sha256::digest(include_bytes!("../lib.rs")).into()).to_string(),
            "compiled_transfer_source_sha256": ContentHash(Sha256::digest(include_bytes!("../../../selector-transfer/src/lib.rs")).into()).to_string(),
            "rows": rows,
        });
        let file = std::fs::File::create(&output).unwrap();
        serde_json::to_writer_pretty(file, &report).unwrap();
        for (slot, value, version, present) in observed {
            if slot.kind == SlotKind::FieldMissing {
                assert_eq!(
                    (value, version, present),
                    (Value::EMPTY, 0, false),
                    "actual current ReadWorld response for {slot:?}"
                );
            }
        }
    }

    fn fixture() -> (FactSnapshot, ProgramGraph) {
        let mut builder = FactBuilder::new();
        for name in ["first", "second"] {
            builder.ensure_symbol(name, FileId::NONE).unwrap();
        }
        let path = builder.intern("inspection.scala").unwrap();
        let source = builder
            .intern("def first(argument: Any): Any = argument")
            .unwrap();
        builder.facts.files.push(FileRecord {
            path,
            source,
            revision: StrId::NONE,
            context: StrId::NONE,
            source_hash: ContentHash::default(),
            flags: SOURCE_VERIFIED,
        });
        builder.facts.symbols[0].file = FileId(0);
        // The first method must observe its parameter: body-less boundaries
        // correctly project every ignored argument frame to FrameId(0).
        builder.facts.operands.push(ValueId(0));
        builder.facts.bodies.push(BodyRecord {
            symbol: SymbolId(0),
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange { start: 0, len: 1 },
            parameters: IdRange { start: 0, len: 1 },
            body_hash: ContentHash::default(),
            flags: 0,
        });
        builder.facts.operations.push(OperationRecord {
            body: BodyId(0),
            opcode: Opcode::Return,
            target: SymbolId::NONE,
            dest: ValueId::NONE,
            a: ValueId(0),
            b: ValueId::NONE,
            arguments: IdRange::default(),
            span: Span::default(),
            flags: 0,
        });
        let facts = builder.finish().unwrap();
        let mut graph = ProgramGraph {
            facts_identity: facts.identity,
            ..Default::default()
        };
        for id in 0..2 {
            graph.nodes.push(NodeRecord {
                symbol: SymbolId(id),
                file: if id == 0 { FileId(0) } else { FileId::NONE },
                body: if id == 0 { BodyId(0) } else { BodyId::NONE },
                flags: 0,
            });
            graph.symbol_nodes.push(NodeId(id));
        }
        graph.index().unwrap();
        (facts, graph)
    }
    fn options() -> SolveOptions {
        SolveOptions {
            workers: 1,
            quantum: 1,
            scratch_bytes_per_worker: 4096,
            memory_budget_bytes: 16 * 1024 * 1024,
            execution_roots: Some(Arc::from([ExecutionRoot {
                node: NodeId(0),
                receiver: SymbolId::NONE,
            }])),
            ..Default::default()
        }
    }
    #[test]
    fn allocated_module_identity_is_retained_only_by_legacy_read_only_admission() {
        let (mut facts, graph) = fixture();
        let text = facts.strings.bytes.len() as u64;
        let name = facts.strings.len() as u32;
        facts.strings.bytes.extend_from_slice(b"p/Module.");
        facts.strings.entries.push(TextRange {
            start: text,
            len: 9,
        });
        facts.symbols[1].name = StrId(name);
        facts.symbols[1].kind = 10;
        facts.operations[0].opcode = Opcode::Allocate;
        facts.operations[0].target = SymbolId(1);
        facts.operations[0].a = ValueId::NONE;
        facts.operations[0].dest = ValueId(1);
        let mut original = QuerySession::new(&facts, &graph, &options()).unwrap();
        assert_eq!(
            original.types.global_module_owner(SymbolId(1)),
            Some(SymbolId(1))
        );
        let retained = Atom {
            kind: AtomKind::Object,
            site: OperationId(0),
            symbol: SymbolId(1),
            binding: 0,
        };
        let value = original.pool.singleton(retained).unwrap();
        let dir = tempfile::tempdir().unwrap();
        let current = dir.path().join("current-module.bin");
        let producer = ContentHash([95; 32]);
        original.save_checkpoint(&current, producer).unwrap();
        let runtime = SolverRuntime::new(&options()).unwrap();
        assert!(matches!(
            QuerySession::from_checkpoint(&facts, &graph, &options(), &runtime, &current, producer),
            Err(Error::Invalid("checkpoint module object identity"))
        ));
        let artifact = selector_artifacts::open(&current, ArtifactKind::Continuation).unwrap();
        let mut metadata = artifact.section(1).unwrap().to_vec();
        metadata[..4].copy_from_slice(&1u32.to_le_bytes());
        let sections = (1..=19)
            .map(|id| Section {
                id,
                count: artifact.count(id).unwrap(),
                bytes: if id == 1 {
                    &metadata
                } else {
                    artifact.section(id).unwrap()
                },
            })
            .collect::<Vec<_>>();
        let legacy = dir.path().join("legacy-module.bin");
        selector_artifacts::write(&legacy, ArtifactKind::Continuation, &sections).unwrap();
        let view =
            CheckpointView::open(&facts, &graph, &legacy, &InspectionLimits::default()).unwrap();
        assert_eq!(view.session.pool.members(value), &[retained]);
    }
    fn checkpoint(facts: &FactSnapshot, graph: &ProgramGraph, path: &Path) -> ContentHash {
        let mut session = QuerySession::new(facts, graph, &options()).unwrap();
        let frame = session.frames.intern(&[Value::EMPTY]).unwrap();
        for (node, receiver, arguments, version) in [
            (NodeId(0), Value::TOP, FrameId(0), 1),
            (NodeId(0), Value::TOP, frame, 3),
            (NodeId(0), Value::EMPTY, FrameId(0), 0),
            (NodeId(1), Value::EMPTY, FrameId(0), 5),
        ] {
            let id = session
                .context(ContextKey {
                    node,
                    receiver,
                    arguments,
                })
                .unwrap();
            session.contexts[id.index()].version = version;
            session.contexts[id.index()].evaluated = version > 0;
        }
        let producer = ContentHash([93; 32]);
        session.save_checkpoint(path, producer).unwrap();
        producer
    }
    #[test]
    fn rooted_frontier_does_not_splice_unreachable_contexts_of_same_node() {
        let (facts, graph) = fixture();
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("rooted.bin");
        let mut session = QuerySession::new(&facts, &graph, &options()).unwrap();
        let mut context = |node, receiver| {
            let id = session
                .context(ContextKey {
                    node,
                    receiver,
                    arguments: FrameId(0),
                })
                .unwrap();
            session.contexts[id.index()].evaluated = true;
            session.contexts[id.index()].version = 1;
            id
        };
        let root = context(NodeId(0), Value::TOP);
        let target = context(NodeId(1), Value::EMPTY);
        let other = context(NodeId(1), Value::TOP);
        session.roots.push(root);
        session.ready = vec![target];
        session.calls.push(ContextCall {
            source: root,
            target,
            operation: OperationId::NONE,
            kind: EdgeKind::Call,
            edge: EdgeId::NONE,
            binding: u32::MAX,
        });
        session.obligation(IssueKind::UnknownExecution, NodeId(1));
        for id in [target, other] {
            session.contexts[id.index()].effects_open = true;
            session.issue_contexts.insert(id);
            session
                .record_runtime_issue_site(
                    id,
                    RuntimeIssueSite {
                        kind: IssueKind::UnknownExecution,
                        reason: RuntimeIssueReason::MissingExecutableBody,
                        operation: OperationId::NONE,
                    },
                )
                .unwrap();
        }
        session
            .save_checkpoint(&path, ContentHash([93; 32]))
            .unwrap();
        let view =
            CheckpointView::open(&facts, &graph, &path, &InspectionLimits::default()).unwrap();
        let report =
            serde_json::to_value(view.root_frontier(NodeId(0), Some(NodeId(1)), 1).unwrap())
                .unwrap();
        assert_eq!(report["reachable_contexts"], 2);
        assert_eq!(report["reachable_pending_contexts"], 1);
        assert_eq!(report["reachable_runtime_site_contexts"], 1);
        assert_eq!(report["top_runtime_sites"][0]["contexts"], 1);
        assert_eq!(
            report["top_runtime_sites"][0]["reason"],
            "missing_executable_body"
        );
        assert_eq!(report["target"]["calls"][0]["from"]["context_id"], root.0);
        assert_eq!(report["target"]["calls"][0]["to"]["context_id"], target.0);
        assert!(view.root_frontier(NodeId(1), None, 1).is_err());
    }

    #[test]
    fn version_three_inventory_retains_saved_state_without_inventing_creation_shapes() {
        let (facts, graph) = fixture();
        let dir = tempfile::tempdir().unwrap();
        let current = dir.path().join("current.bin");
        let producer = checkpoint(&facts, &graph, &current);
        let artifact = selector_artifacts::open(&current, ArtifactKind::Continuation).unwrap();
        let mut metadata = artifact.section(1).unwrap().to_vec();
        metadata[..4].copy_from_slice(&3u32.to_le_bytes());
        let sections = (1..=21)
            .map(|id| Section {
                id,
                count: artifact.count(id).unwrap(),
                bytes: if id == 1 {
                    &metadata
                } else {
                    artifact.section(id).unwrap()
                },
            })
            .collect::<Vec<_>>();
        let prior = dir.path().join("prior.bin");
        selector_artifacts::write(&prior, ArtifactKind::Continuation, &sections).unwrap();
        let runtime = SolverRuntime::new(&options()).unwrap();
        assert!(matches!(
            QuerySession::from_checkpoint(&facts, &graph, &options(), &runtime, &prior, producer),
            Err(Error::Invalid("checkpoint version"))
        ));
        let view =
            CheckpointView::open(&facts, &graph, &prior, &InspectionLimits::default()).unwrap();
        assert_eq!(view.header.version, 3);
        assert_eq!(view.header.callback_shapes, 0);
        assert_eq!(view.header.contexts, 4);
        assert!(
            view.session
                .contexts
                .iter()
                .all(|c| c.callback_shape == CallbackShapeId(0))
        );
        let original =
            CheckpointView::open(&facts, &graph, &current, &InspectionLimits::default()).unwrap();
        assert_eq!(
            view.context_inventory(2).unwrap().rows,
            original.context_inventory(2).unwrap().rows
        );
        assert!(matches!(
            view.export_replay(
                NodeId(0),
                None,
                &dir.path().join("replay"),
                &replay::ReplayLimits::default()
            ),
            Err(Error::Invalid(
                "legacy checkpoint replay requires frozen legacy operator"
            ))
        ));
    }
    #[test]
    fn old_producer_is_read_only_and_inventory_counts_exact_saved_publications() {
        let (facts, graph) = fixture();
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("state.bin");
        let producer = checkpoint(&facts, &graph, &path);
        let runtime = SolverRuntime::new(&options()).unwrap();
        assert!(matches!(
            QuerySession::from_checkpoint(
                &facts,
                &graph,
                &options(),
                &runtime,
                &path,
                ContentHash([94; 32])
            ),
            Err(Error::Invalid("checkpoint producer"))
        ));
        let limits = InspectionLimits {
            memory_budget_bytes: 16 * 1024 * 1024,
            max_rows: 2,
            ..Default::default()
        };
        let view = CheckpointView::open(&facts, &graph, &path, &limits).unwrap();
        assert_eq!(view.header().producer, producer);
        assert_eq!(view.header().execution_roots.0, root_identity(&options()));
        let inventory = view.context_inventory(2).unwrap();
        assert_eq!(
            (inventory.summary.contexts, inventory.summary.nodes),
            (4, 2)
        );
        assert_eq!(
            inventory.rows[0],
            NodeInventory {
                node: NodeId(0),
                contexts: 3,
                receiver_variants: 2,
                max_argument_frames_per_receiver: 2,
                largest_receiver_context: ContextId(0),
                largest_receiver_variants: 2,
                evaluated_contexts: 2,
                widened_contexts: 0,
                publication_versions: 4
            }
        );
        assert_eq!(inventory.rows[1].publication_versions, 5);
        let mut visited = Vec::new();
        view.visit_inventory(1, |row, origin| {
            visited.push((row.node, origin.symbol.to_owned()))
        })
        .unwrap();
        assert_eq!(visited, vec![(NodeId(0), "first".to_owned())]);
        let family = view
            .export_replay_family(
                NodeId(0),
                None,
                &directory.path().join("family"),
                &replay::ReplayLimits {
                    max_bytes: 1024 * 1024,
                    scratch_bytes: 4096,
                    max_records: 100,
                    ..Default::default()
                },
                64,
            )
            .unwrap();
        assert_eq!(family.inventory.selected_variants, 3);
        assert_eq!(family.inventory.selected_evaluated, 2);
        assert_eq!(view.header().contexts, 4);
        let mut changed_roots = options();
        changed_roots.execution_roots = None;
        assert!(matches!(
            QuerySession::from_checkpoint(
                &facts,
                &graph,
                &changed_roots,
                &runtime,
                &path,
                producer
            ),
            Err(Error::Invalid("checkpoint execution roots"))
        ));
    }
    #[test]
    fn malformed_wire_and_changed_logical_content_are_never_inspected() {
        let (facts, graph) = fixture();
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("state.bin");
        checkpoint(&facts, &graph, &path);
        let original = selector_artifacts::open(&path, ArtifactKind::Continuation).unwrap();
        let mut data: Vec<Vec<u8>> = (1..=SECTION_COUNT)
            .map(|id| original.section(id).unwrap().to_vec())
            .collect();
        // Correctly checksummed artifact, invalid context argument-frame ID.
        data[5][12..16].copy_from_slice(&u32::MAX.to_le_bytes());
        let sections: Vec<_> = data
            .iter()
            .enumerate()
            .map(|(i, bytes)| Section {
                id: i as u32 + 1,
                count: original.count(i as u32 + 1).unwrap(),
                bytes,
            })
            .collect();
        let malformed = directory.path().join("malformed.bin");
        selector_artifacts::write(&malformed, ArtifactKind::Continuation, &sections).unwrap();
        assert!(matches!(
            CheckpointView::open(&facts, &graph, &malformed, &InspectionLimits::default()),
            Err(Error::Invalid("checkpoint context frame"))
        ));
        let (mut changed, _) = fixture();
        changed.symbols[0].properties ^= 1;
        assert!(matches!(
            CheckpointView::open(&changed, &graph, &path, &InspectionLimits::default()),
            Err(Error::Invalid("checkpoint snapshot content seal"))
        ));
    }
    #[test]
    fn memory_and_top_rows_are_preflighted_and_inventory_does_not_retain_scratch() {
        let (facts, graph) = fixture();
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("state.bin");
        checkpoint(&facts, &graph, &path);
        assert!(
            CheckpointView::open(
                &facts,
                &graph,
                &path,
                &InspectionLimits {
                    memory_budget_bytes: 1,
                    ..Default::default()
                }
            )
            .is_err()
        );
        assert!(matches!(
            CheckpointView::open(
                &facts,
                &graph,
                &path,
                &InspectionLimits {
                    max_contexts: 1,
                    ..Default::default()
                }
            ),
            Err(Error::Limit("checkpoint retained context limit"))
        ));
        let mut view = CheckpointView::open(
            &facts,
            &graph,
            &path,
            &InspectionLimits {
                max_rows: 2,
                ..Default::default()
            },
        )
        .unwrap();
        let retained = view.owned_bytes();
        for _ in 0..20 {
            assert_eq!(view.context_inventory(1).unwrap().rows.len(), 1);
        }
        assert_eq!(view.owned_bytes(), retained);
        assert!(matches!(
            view.context_inventory(3),
            Err(Error::Limit("checkpoint inventory rows"))
        ));
        view.limits.memory_budget_bytes = retained;
        assert!(matches!(
            view.context_inventory(1),
            Err(Error::Limit("checkpoint inventory memory"))
        ));
        assert!(matches!(
            view.export_replay(
                NodeId(0),
                Some(ContextId(0)),
                &directory.path().join("export"),
                &replay::ReplayLimits::default()
            ),
            Err(Error::Limit("checkpoint replay export memory"))
        ));
    }
}
