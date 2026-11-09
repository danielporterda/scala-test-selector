use selector_facts::{BodyRecord, FactSnapshot, OperationRecord};
use selector_graph::ProgramGraph;
use selector_types::*;

/// Artifact-local IDs. This index borrows the original sealed input owners.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SubjectState {
    SourceRecipe,
    SourceMissing,
    ForeignPending,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GuardOrigin {
    FactIssue(u32),
    GraphIssue(u32),
    UnknownOperation(OperationId),
    InputAuthority(FileId),
    MissingRecipe(NodeId),
    GraphGuard(EdgeId),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Guard {
    /// NONE is a global input scope, not an unnamed successful recipe.
    pub node: NodeId,
    pub origin: GuardOrigin,
    pub kind: IssueKind,
    pub execution: bool,
}
#[derive(Clone, Copy, Debug)]
pub struct SourceSubject {
    pub node: NodeId,
    pub body: BodyId,
    pub state: SubjectState,
    pub has_execution_guard: bool,
}
#[derive(Clone, Debug)]
pub struct IndexLimits {
    pub max_nodes: usize,
    pub max_operations: usize,
    pub max_guard_rows: usize,
    pub max_bytes: usize,
}
impl Default for IndexLimits {
    fn default() -> Self {
        Self {
            max_nodes: 2_000_000,
            max_operations: 10_000_000,
            max_guard_rows: 2_000_000,
            max_bytes: 128 << 20,
        }
    }
}
/// Full graph-node universe, including pending native subjects. A second
/// producer can replace a pending row only after its own authority admission.
pub struct SourceIndex<'a> {
    pub facts: &'a FactSnapshot,
    pub graph: &'a ProgramGraph,
    pub subjects: Vec<SourceSubject>,
    pub guards: Vec<Guard>,
    pub global_execution_guard: bool,
}
impl<'a> SourceIndex<'a> {
    pub fn new(
        facts: &'a FactSnapshot,
        graph: &'a ProgramGraph,
        limits: &IndexLimits,
    ) -> Result<Self, Error> {
        if graph.facts_identity != facts.identity {
            return Err(Error::Invalid("source capsule facts/graph binding"));
        }
        if graph.nodes.len() > limits.max_nodes || facts.operations.len() > limits.max_operations {
            return Err(Error::Limit("source capsule inventory"));
        }
        facts.validate()?;
        graph.validate()?;
        check_graph_fact_references(facts, graph)?;
        let missing = graph
            .nodes
            .iter()
            .filter(|node| {
                node.body.is_none()
                    || facts.bodies[node.body.index()].flags & BODY_BINARY_RECIPE != 0
            })
            .count();
        let unverified = graph
            .nodes
            .iter()
            .filter(|node| {
                !node.body.is_none()
                    && facts.bodies[node.body.index()].flags & BODY_BINARY_RECIPE == 0
            })
            .filter(|node| {
                let file = facts.files[facts.bodies[node.body.index()].file.index()];
                file.flags & (SOURCE_VERIFIED | SYNTAX_VERIFIED)
                    != SOURCE_VERIFIED | SYNTAX_VERIFIED
                    || file.flags & FILE_BINARY_SOURCE != 0
            })
            .count();
        let guard_count = facts
            .issues
            .len()
            .checked_add(graph.issues.len())
            .and_then(|n| n.checked_add(missing))
            .and_then(|n| n.checked_add(unverified))
            .and_then(|n| {
                n.checked_add(
                    facts
                        .operations
                        .iter()
                        .filter(|op| op.opcode == Opcode::Unknown)
                        .count(),
                )
            })
            .and_then(|n| {
                n.checked_add(
                    graph
                        .edges
                        .iter()
                        .filter(|e| e.kind == EdgeKind::Guard || e.flags & EDGE_UNKNOWN != 0)
                        .count(),
                )
            })
            .ok_or(Error::Limit("source index geometry"))?;
        let bytes = graph
            .nodes
            .len()
            .checked_mul(std::mem::size_of::<SourceSubject>())
            .and_then(|n| n.checked_add(facts.bodies.len().checked_mul(4)?))
            .and_then(|n| n.checked_add(facts.files.len()))
            .and_then(|n| n.checked_add(facts.symbols.len()))
            .and_then(|n| n.checked_add(guard_count.checked_mul(std::mem::size_of::<Guard>())?))
            .ok_or(Error::Limit("source index bytes"))?;
        if guard_count > limits.max_guard_rows || bytes > limits.max_bytes {
            return Err(Error::Limit("source index preflight"));
        }
        let mut subjects = Vec::new();
        subjects
            .try_reserve_exact(graph.nodes.len())
            .map_err(|_| Error::Limit("source subjects"))?;
        let mut body_nodes = vec![NodeId::NONE; facts.bodies.len()];
        let mut file_guard = vec![false; facts.files.len()];
        let mut symbol_guard = vec![false; facts.symbols.len()];
        let mut guards = Vec::new();
        guards
            .try_reserve_exact(guard_count)
            .map_err(|_| Error::Limit("source guard preflight allocation"))?;
        let mut global = false;
        let push = |rows: &mut Vec<Guard>, row| -> Result<(), Error> {
            if rows.len() >= limits.max_guard_rows {
                return Err(Error::Limit("source guard rows"));
            }
            rows.try_reserve(1)
                .map_err(|_| Error::Limit("source guards"))?;
            rows.push(row);
            Ok(())
        };
        for (i, issue) in facts.issues.iter().enumerate() {
            let execution = issue.kind.is_execution_boundary();
            let node = if issue.symbol.is_none() {
                NodeId::NONE
            } else {
                graph.node_for_symbol(issue.symbol).unwrap_or(NodeId::NONE)
            };
            push(
                &mut guards,
                Guard {
                    node,
                    origin: GuardOrigin::FactIssue(i as u32),
                    kind: issue.kind,
                    execution,
                },
            )?;
            if !execution {
                continue;
            }
            if !issue.symbol.is_none() {
                symbol_guard[issue.symbol.index()] = true;
            } else if !issue.file.is_none() {
                file_guard[issue.file.index()] = true;
            } else {
                global = true;
            }
        }
        for (i, record) in graph.nodes.iter().enumerate() {
            let node = NodeId(i as u32);
            let source_body = !record.body.is_none()
                && facts.bodies[record.body.index()].flags & BODY_BINARY_RECIPE == 0;
            let source_defined = !record.symbol.is_none()
                && facts.symbols[record.symbol.index()].flags & SYMBOL_DEFINED != 0;
            let state = if source_body {
                SubjectState::SourceRecipe
            } else if source_defined {
                SubjectState::SourceMissing
            } else {
                SubjectState::ForeignPending
            };
            if source_body {
                if !body_nodes[record.body.index()].is_none() {
                    return Err(Error::Invalid("source body has multiple graph owners"));
                }
                body_nodes[record.body.index()] = node;
            }
            let mut guarded = global
                || (!record.symbol.is_none() && symbol_guard[record.symbol.index()])
                || (!record.file.is_none() && file_guard[record.file.index()]);
            if source_body {
                let body = facts.bodies[record.body.index()];
                let file = facts.files[body.file.index()];
                if file.flags & (SOURCE_VERIFIED | SYNTAX_VERIFIED)
                    != SOURCE_VERIFIED | SYNTAX_VERIFIED
                    || file.flags & FILE_BINARY_SOURCE != 0
                {
                    guarded = true;
                    push(
                        &mut guards,
                        Guard {
                            node,
                            origin: GuardOrigin::InputAuthority(body.file),
                            kind: IssueKind::MissingSyntax,
                            execution: true,
                        },
                    )?;
                }
                for (offset, operation) in
                    facts.operations[body.operations.range()].iter().enumerate()
                {
                    if operation.opcode == Opcode::Unknown {
                        guarded = true;
                        push(
                            &mut guards,
                            Guard {
                                node,
                                origin: GuardOrigin::UnknownOperation(OperationId(
                                    body.operations.start + offset as u32,
                                )),
                                kind: IssueKind::UnknownExecution,
                                execution: true,
                            },
                        )?;
                    }
                }
            } else {
                // Even NODE_EFFECTS_COMPLETE is not source authority here. The
                // native/model publisher must supply its own complete capsule.
                push(
                    &mut guards,
                    Guard {
                        node,
                        origin: GuardOrigin::MissingRecipe(node),
                        kind: IssueKind::MissingSyntax,
                        execution: true,
                    },
                )?;
                guarded = true;
            }
            subjects.push(SourceSubject {
                node,
                body: if source_body {
                    record.body
                } else {
                    BodyId::NONE
                },
                state,
                has_execution_guard: guarded,
            });
        }
        for (i, issue) in graph.issues.iter().enumerate() {
            let execution = issue.kind.is_execution_boundary();
            push(
                &mut guards,
                Guard {
                    node: issue.node,
                    origin: GuardOrigin::GraphIssue(i as u32),
                    kind: issue.kind,
                    execution,
                },
            )?;
            if execution {
                if issue.node.is_none() {
                    global = true;
                } else {
                    subjects[issue.node.index()].has_execution_guard = true;
                }
            }
        }
        for (i, edge) in graph.edges.iter().enumerate() {
            if edge.kind == EdgeKind::Guard || edge.flags & EDGE_UNKNOWN != 0 {
                subjects[edge.source.index()].has_execution_guard = true;
                push(
                    &mut guards,
                    Guard {
                        node: edge.source,
                        origin: GuardOrigin::GraphGuard(EdgeId(i as u32)),
                        kind: IssueKind::UnknownExecution,
                        execution: true,
                    },
                )?;
            }
        }
        if global {
            for subject in &mut subjects {
                subject.has_execution_guard = true;
            }
        }
        // A recipe omitted from the execution graph must remain pending, not
        // silently vanish from the producer's body universe.
        for (i, body) in facts.bodies.iter().enumerate() {
            if body.flags & BODY_BINARY_RECIPE == 0 && body_nodes[i].is_none() {
                return Err(Error::Invalid("source recipe missing from graph universe"));
            }
        }
        Ok(Self {
            facts,
            graph,
            subjects,
            guards,
            global_execution_guard: global,
        })
    }
    pub fn operations(&self, node: NodeId) -> Result<&[OperationRecord], Error> {
        let subject = self
            .subjects
            .get(node.index())
            .ok_or(Error::Invalid("source subject ID"))?;
        Ok(if subject.body.is_none() {
            &[]
        } else {
            &self.facts.operations[self.facts.bodies[subject.body.index()].operations.range()]
        })
    }
    pub fn body(&self, node: NodeId) -> Result<Option<BodyRecord>, Error> {
        let subject = self
            .subjects
            .get(node.index())
            .ok_or(Error::Invalid("source subject ID"))?;
        Ok((!subject.body.is_none()).then(|| self.facts.bodies[subject.body.index()]))
    }
}

// Graph geometry validation cannot know the bounds of another artifact. Check
// every cross-artifact ID before source indexing, even when its content hash is
// the expected value: identity equality does not make malformed geometry safe.
fn check_graph_fact_references(facts: &FactSnapshot, graph: &ProgramGraph) -> Result<(), Error> {
    let symbol = |id: SymbolId| id.is_none() || id.index() < facts.symbols.len();
    let file = |id: FileId| id.is_none() || id.index() < facts.files.len();
    for node in &graph.nodes {
        if !symbol(node.symbol) || !file(node.file) {
            return Err(Error::Invalid("source graph fact reference"));
        }
        if !node.body.is_none() {
            let body = facts
                .bodies
                .get(node.body.index())
                .ok_or(Error::Invalid("source graph body reference"))?;
            if body.symbol != node.symbol || body.file != node.file {
                return Err(Error::Invalid("source graph body owner"));
            }
        }
    }
    for edge in &graph.edges {
        if !symbol(edge.receiver)
            || (!edge.operation.is_none() && edge.operation.index() >= facts.operations.len())
            || (!edge.occurrence.is_none() && edge.occurrence.index() >= facts.occurrences.len())
        {
            return Err(Error::Invalid("source graph edge fact reference"));
        }
    }
    for issue in &graph.issues {
        if !symbol(issue.symbol)
            || !file(issue.file)
            || (!issue.detail.is_none() && issue.detail.index() >= facts.strings.len())
        {
            return Err(Error::Invalid("source graph issue fact reference"));
        }
    }
    for diagnostic in &graph.diagnostics {
        if !symbol(diagnostic.symbol) || !file(diagnostic.file) {
            return Err(Error::Invalid("source graph diagnostic fact reference"));
        }
    }
    if graph.symbol_nodes.len() > facts.symbols.len() {
        return Err(Error::Invalid("source graph symbol map reference"));
    }
    Ok(())
}
