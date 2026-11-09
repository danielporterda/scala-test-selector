//! Compiler-bound Guardrail route certificates and finite generator metadata.
//!
//! Literal paths/verbs identify wire operations, never Scala targets. Targets,
//! routes definitions, and override descendants always come from admitted compiler
//! IDs. A successful operation proof narrows method guards only; shared router
//! execution remains a file guard, as in helper-shadow/api_support.py.

use selector_facts::FactSnapshot;
use selector_types::*;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

pub const VERSION: &str = "guardrail-route-evidence/rust-v1";
#[path = "runtime_transport.rs"]
mod transport;
#[derive(Debug, Clone, Copy)]
pub struct WireOperation<'a> {
    pub schema_path: &'a str,
    pub path: &'a str,
    pub verb: &'a str,
    pub operation_id: &'a str,
    pub server_urls: &'a [&'a str],
}
#[derive(Debug, Clone, Copy)]
pub struct RouteCandidates<'a> {
    pub clients: &'a [SymbolId],
    pub handlers: &'a [SymbolId],
    /// Full package identities, certified by finite paired generation mappings.
    pub literal_packages: &'a [&'a str],
    pub inventory_complete: bool,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RouteEvidence {
    pub file: FileId,
    pub routes_symbol: SymbolId,
    pub definition_occurrence: OccurrenceId,
    pub handler_symbol: SymbolId,
    pub handler_occurrence: OccurrenceId,
    pub line: u32,
    pub span: Span,
    pub source_sha256: ContentHash,
}
#[derive(Debug, Clone)]
pub struct OperationProof {
    pub complete: bool,
    pub reason: &'static str,
    pub client: SymbolId,
    pub handler: SymbolId,
    pub clients: Vec<SymbolId>,
    pub handlers: Vec<SymbolId>,
    pub context_equivalences: Vec<u32>,
    pub handwritten_transport_proofs: Vec<TransportProof>,
    pub symbols: Vec<SymbolId>,
    pub positive_route_symbols: Vec<SymbolId>,
    pub evidence: Vec<RouteEvidence>,
    pub compiler_operation_name: String,
    pub recovered_compiler_name: bool,
}
impl OperationProof {
    fn incomplete(reason: &'static str) -> Self {
        Self {
            complete: false,
            reason,
            client: SymbolId::NONE,
            handler: SymbolId::NONE,
            clients: Vec::new(),
            handlers: Vec::new(),
            context_equivalences: Vec::new(),
            handwritten_transport_proofs: Vec::new(),
            symbols: Vec::new(),
            positive_route_symbols: Vec::new(),
            evidence: Vec::new(),
            compiler_operation_name: String::new(),
            recovered_compiler_name: false,
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GuardScope {
    File,
    Methods,
}
#[derive(Debug, Clone)]
pub struct OperationGuard {
    pub file: FileId,
    pub scope: GuardScope,
    pub symbols: Vec<SymbolId>,
    pub reason: &'static str,
}

struct Definition {
    file: FileId,
    symbol: SymbolId,
    occurrence: OccurrenceId,
}
struct Reference {
    file: FileId,
    symbol: SymbolId,
    occurrence: OccurrenceId,
    span: Span,
}
struct Branch<'a> {
    operation: &'a str,
    definition: usize,
    line: u32,
    start: u32,
    end: u32,
}
/// One immutable compiler/source scan per graph build. Postings preserve duplicate
/// references and ordinals; repeated operations borrow sparse sorted slices.
pub struct RouterReferences<'a> {
    facts: &'a FactSnapshot,
    definitions: Vec<Definition>,
    references: Vec<Reference>,
    branches: Vec<Branch<'a>>,
    reverse: Vec<(SymbolId, SymbolId)>,
    invalid_override_sources: Vec<SymbolId>,
    conflicts: HashSet<SymbolId>,
    router_files: Vec<FileId>,
    context_equivalences: Vec<ContextEquivalence>,
    canonical: HashMap<SymbolId, SymbolId>,
    transport_files: Vec<FileId>,
    transport_occurrences: Vec<OccurrenceId>,
    transport_operations: Vec<OperationId>,
}
impl<'a> RouterReferences<'a> {
    pub fn new(facts: &'a FactSnapshot) -> Self {
        let mut definitions = Vec::new();
        let mut references = Vec::new();
        let mut branches = Vec::new();
        let transport_mask: Vec<_> = facts
            .files
            .iter()
            .enumerate()
            .map(|(index, _)| {
                let path = facts.path(FileId(index as u32));
                path.contains("/src/main/scala/") && path.ends_with("Client.scala")
            })
            .collect();
        let transport_files = transport_mask
            .iter()
            .enumerate()
            .filter(|(_, value)| **value)
            .map(|(index, _)| FileId(index as u32))
            .collect();
        let mut transport_occurrences = Vec::new();
        let conflicts: HashSet<_> = facts
            .issues
            .iter()
            .filter(|issue| issue.kind == IssueKind::ContextConflict && !issue.symbol.is_none())
            .map(|issue| issue.symbol)
            .collect();
        let (context_equivalences, canonical) = context_equivalences(facts);
        for (index, occurrence) in facts.occurrences.iter().enumerate() {
            if occurrence.file.is_none() || occurrence.symbol.is_none() {
                continue;
            }
            if transport_mask[occurrence.file.index()] {
                transport_occurrences.push(OccurrenceId(index as u32));
            }
            let file = &facts.files[occurrence.file.index()];
            let information = &facts.symbols[occurrence.symbol.index()];
            if file.flags & SOURCE_VERIFIED == 0 || information.kind != 3 {
                continue;
            }
            let source = facts.text(file.source);
            if occurrence.role == 2
                && display(facts, occurrence.symbol) == "routes"
                && (!conflicts.contains(&occurrence.symbol)
                    || canonical.contains_key(&occurrence.symbol))
            {
                let Some((start, end, line)) = route_region(source, occurrence.span) else {
                    continue;
                };
                let definition = definitions.len();
                definitions.push(Definition {
                    file: occurrence.file,
                    symbol: occurrence.symbol,
                    occurrence: OccurrenceId(index as u32),
                });
                let body = &source[start as usize..end as usize];
                let mut offset = start as usize;
                for (relative, full_line) in body.split_inclusive('\n').enumerate() {
                    let line_text = full_line.trim_end_matches(['\n', '\r']);
                    let marker = "customExtract(\"";
                    let mut at = 0;
                    while let Some(found) = line_text[at..].find(marker) {
                        let value = at + found + marker.len();
                        let Some(close) = line_text[value..].find('"') else {
                            break;
                        };
                        let operation = &line_text[value..value + close];
                        branches.push(Branch {
                            operation,
                            definition,
                            line: line + relative as u32,
                            start: offset as u32,
                            end: (offset + line_text.len()) as u32,
                        });
                        at = value + close + 1;
                    }
                    offset += full_line.len();
                }
            }
            if occurrence.role == 1
                && !information.owner.is_none()
                && display(facts, information.owner).ends_with("Handler")
            {
                references.push(Reference {
                    file: occurrence.file,
                    symbol: occurrence.symbol,
                    occurrence: OccurrenceId(index as u32),
                    span: occurrence.span,
                });
            }
        }
        references.sort_unstable_by_key(|reference| {
            (
                reference.symbol,
                reference.file,
                reference.span.start,
                reference.span.end,
                reference.occurrence,
            )
        });
        transport_occurrences.sort_unstable_by_key(|id| {
            let row = &facts.occurrences[id.index()];
            (row.file, row.role, row.span.start, row.ordinal)
        });
        let mut transport_operations: Vec<_> = facts
            .operations
            .iter()
            .enumerate()
            .filter(|(_, op)| {
                op.flags & OP_SYNTHETIC_EXACT_ORIGINAL_ARGUMENT != 0
                    && !op.body.is_none()
                    && transport_mask[facts.bodies[op.body.index()].file.index()]
            })
            .map(|(index, _)| OperationId(index as u32))
            .collect();
        transport_operations.sort_unstable_by_key(|id| {
            facts.bodies[facts.operations[id.index()].body.index()].file
        });
        branches.sort_unstable_by(|a, b| {
            (a.operation, a.definition, a.start).cmp(&(b.operation, b.definition, b.start))
        });
        let mut reverse = Vec::new();
        let mut invalid_override_sources = Vec::new();
        for relation in facts
            .relations
            .iter()
            .filter(|relation| relation.kind == RelationKind::Override)
        {
            reverse.push((relation.target, relation.source));
            if relation.target.is_none() || facts.symbols[relation.target.index()].kind == 0 {
                invalid_override_sources.push(relation.source);
            }
        }
        reverse.sort_unstable();
        reverse.dedup();
        invalid_override_sources.sort_unstable();
        invalid_override_sources.dedup();
        let mut router_files: Vec<_> = definitions
            .iter()
            .map(|definition| definition.file)
            .collect();
        router_files.sort_unstable();
        router_files.dedup();
        Self {
            facts,
            definitions,
            references,
            branches,
            reverse,
            invalid_override_sources,
            conflicts,
            router_files,
            context_equivalences,
            canonical,
            transport_files,
            transport_occurrences,
            transport_operations,
        }
    }
    pub fn context_equivalences(&self) -> &[ContextEquivalence] {
        &self.context_equivalences
    }
    fn canonical(&self, symbol: SymbolId) -> SymbolId {
        self.canonical.get(&symbol).copied().unwrap_or(symbol)
    }
    fn blocked(&self, symbol: SymbolId) -> bool {
        self.conflicts.contains(&symbol) && !self.canonical.contains_key(&symbol)
    }
    pub fn retained_occurrences(&self) -> usize {
        self.definitions.len() + self.references.len()
    }
    pub fn router_files(&self) -> &[FileId] {
        &self.router_files
    }
    fn references(&self, handler: SymbolId) -> &[Reference] {
        let first = self.references.partition_point(|row| row.symbol < handler);
        let last = self.references.partition_point(|row| row.symbol <= handler);
        &self.references[first..last]
    }
    fn operation_branches(&self, operation: &str) -> &[Branch<'a>] {
        let first = self
            .branches
            .partition_point(|row| row.operation < operation);
        let last = self
            .branches
            .partition_point(|row| row.operation <= operation);
        &self.branches[first..last]
    }
    fn closure(&self, roots: impl IntoIterator<Item = SymbolId>) -> Vec<SymbolId> {
        let mut pending: Vec<_> = roots.into_iter().collect();
        let mut visited = HashSet::new();
        while let Some(symbol) = pending.pop() {
            if !visited.insert(symbol) {
                continue;
            }
            let first = self.reverse.partition_point(|&(parent, _)| parent < symbol);
            let last = self
                .reverse
                .partition_point(|&(parent, _)| parent <= symbol);
            pending.extend(self.reverse[first..last].iter().map(|&(_, child)| child));
        }
        let mut result: Vec<_> = visited.into_iter().collect();
        result.sort_unstable();
        result
    }
    pub fn evidence(
        &self,
        operation: WireOperation<'_>,
        handler: SymbolId,
        literal_packages: &[&str],
    ) -> Vec<RouteEvidence> {
        let facts = self.facts;
        if handler.is_none() || handler.index() >= facts.symbols.len() {
            return Vec::new();
        }
        let method = &facts.symbols[handler.index()];
        if method.owner.is_none() {
            return Vec::new();
        }
        let owner = &facts.symbols[method.owner.index()];
        let resource = display(facts, method.owner)
            .strip_suffix("Handler")
            .unwrap_or("");
        let handler_package = package(facts.symbol_name(method.owner));
        let mut result = Vec::new();
        let branches = self.operation_branches(operation.operation_id);
        for branch in branches {
            if branches
                .iter()
                .filter(|candidate| candidate.definition == branch.definition)
                .count()
                != 1
            {
                continue;
            }
            let definition = &self.definitions[branch.definition];
            let file = &facts.files[definition.file.index()];
            let path = facts.path(definition.file);
            let same_module = operation
                .schema_path
                .split_once("/src/main/openapi/")
                .is_some_and(|(module, _)| path.starts_with(&format!("{module}/target/")));
            let mapped = literal_packages.contains(&handler_package.as_str())
                && path.split('/').any(|part| part == "target")
                && path.split('/').any(|part| part == "src_managed");
            if !same_module && !mapped {
                continue;
            }
            let route = &facts.symbols[definition.symbol.index()];
            if route.owner.is_none() {
                continue;
            }
            let route_owner = &facts.symbols[route.owner.index()];
            if route_owner.kind != 10
                || display(facts, route.owner) != format!("{resource}Resource")
                || package(facts.symbol_name(route.owner))
                    != package(facts.symbol_name(method.owner))
                || owner.kind != 14 && owner.kind != 18
            {
                continue;
            }
            let source = facts.text(file.source);
            let Some(line) = source.get(branch.start as usize..branch.end as usize) else {
                continue;
            };
            if !route_matches_wire_identity(line, operation) {
                continue;
            }
            if line.matches("customExtract(\"").count() != 1 {
                continue;
            }
            let mut references = self
                .references(handler)
                .iter()
                .filter(|reference| {
                    reference.file == definition.file
                        && reference.span.start >= branch.start
                        && reference.span.end <= branch.end
                })
                .filter(|reference| {
                    let left = (reference.span.start - branch.start) as usize;
                    let right = (reference.span.end - branch.start) as usize;
                    line.get(..left)
                        .is_some_and(|prefix| prefix.ends_with("handler."))
                        && line
                            .get(right..)
                            .is_some_and(|suffix| suffix.starts_with('('))
                });
            let Some(reference) = references.next() else {
                continue;
            };
            if references.next().is_some() {
                continue;
            }
            result.push(RouteEvidence {
                file: definition.file,
                routes_symbol: definition.symbol,
                definition_occurrence: definition.occurrence,
                handler_symbol: handler,
                handler_occurrence: reference.occurrence,
                line: branch.line + 1,
                span: reference.span,
                source_sha256: file.source_hash,
            });
        }
        result.sort_unstable_by_key(|row| {
            (
                row.file,
                row.routes_symbol,
                row.line,
                row.handler_symbol,
                row.span.start,
                row.span.end,
            )
        });
        result.dedup_by_key(|row| {
            (
                row.file,
                row.routes_symbol,
                row.line,
                row.handler_symbol,
                row.span.start,
                row.span.end,
            )
        });
        result
    }
    pub fn prove_operation(
        &self,
        operation: WireOperation<'_>,
        candidates: RouteCandidates<'_>,
    ) -> OperationProof {
        self.prove_operation_inner(operation, candidates, &[])
    }
    /// The handwritten branch is available only for an exact finite server-only
    /// producer. Its targets still require the independent compiler-bound Pekko
    /// request certificate; a task or Scala spelling cannot create a target.
    pub fn prove_operation_with_tasks(
        &self,
        operation: WireOperation<'_>,
        candidates: RouteCandidates<'_>,
        tasks: &[GenerationTask],
        namespace: Option<&str>,
    ) -> OperationProof {
        let normal = self.prove_operation(operation, candidates);
        if normal.complete
            || !candidates.inventory_complete
            || tasks.is_empty()
            || candidates
                .clients
                .iter()
                .any(|&symbol| display(self.facts, symbol) == operation.operation_id)
        {
            return normal;
        }
        let handlers: Vec<_> = candidates
            .handlers
            .iter()
            .copied()
            .filter(|&symbol| display(self.facts, symbol) == operation.operation_id)
            .collect();
        if handlers.len() != 1 {
            return normal;
        }
        let owner = self.facts.symbols[handlers[0].index()].owner;
        if owner.is_none() {
            return normal;
        }
        let owner_package = package(self.facts.symbol_name(owner));
        let Some(namespace) = namespace.filter(|value| value.split('.').all(identifier)) else {
            return normal;
        };
        let modes: BTreeSet<_> = tasks
            .iter()
            .filter(|task| {
                task.schema_path == operation.schema_path
                    && format!("{}.{}", task.package, namespace) == owner_package
            })
            .map(|task| task.mode)
            .collect();
        if modes != BTreeSet::from([GenerationMode::ScalaServer]) {
            return normal;
        }
        let transports = self.handwritten_transport_clients(operation);
        if transports.len() != 1 {
            return normal;
        }
        let clients = [transports[0].symbol];
        let mut result = self.prove_operation_inner(
            operation,
            RouteCandidates {
                clients: &clients,
                ..candidates
            },
            &transports,
        );
        if result.complete {
            result.handwritten_transport_proofs = transports;
        }
        result
    }
    fn prove_operation_inner(
        &self,
        operation: WireOperation<'_>,
        candidates: RouteCandidates<'_>,
        transports: &[TransportProof],
    ) -> OperationProof {
        if !candidates.inventory_complete {
            return OperationProof::incomplete("closed_compiler_inventory_unavailable");
        }
        if !identifier(operation.operation_id) {
            return OperationProof::incomplete(
                "operation_generator_namespace_or_identity_unavailable",
            );
        }
        let facts = self.facts;
        let mut proof =
            OperationProof::incomplete("generated_client_handler_pair_missing_or_ambiguous");
        let mut names = BTreeSet::new();
        for &symbol in candidates.clients.iter().chain(candidates.handlers) {
            if symbol.is_none() || symbol.index() >= facts.symbols.len() {
                return proof;
            }
            if display(facts, symbol) == operation.operation_id {
                names.insert(operation.operation_id.to_owned());
            }
        }
        if names.is_empty() {
            let proved: Vec<_> = candidates
                .handlers
                .iter()
                .copied()
                .filter(|&handler| {
                    !self
                        .evidence(operation, handler, candidates.literal_packages)
                        .is_empty()
                })
                .collect();
            proof.positive_route_symbols = self.closure(
                candidates
                    .clients
                    .iter()
                    .chain(candidates.handlers)
                    .copied()
                    .filter(|&symbol| {
                        proved
                            .iter()
                            .any(|&handler| display(facts, symbol) == display(facts, handler))
                    }),
            );
            let mut groups: Vec<_> = proved
                .iter()
                .map(|&symbol| self.canonical(symbol))
                .collect();
            groups.sort_unstable();
            groups.dedup();
            if groups.len() != 1 {
                return proof;
            }
            names.insert(display(facts, proved[0]).to_owned());
            proof.recovered_compiler_name = true;
        }
        let name = names.into_iter().next().unwrap();
        proof.positive_route_symbols = self.closure(
            candidates
                .clients
                .iter()
                .chain(candidates.handlers)
                .copied()
                .filter(|&symbol| display(facts, symbol) == name),
        );
        proof.compiler_operation_name = name.clone();
        let mut clients = Vec::new();
        let mut handlers = Vec::new();
        for (symbols, client) in [(candidates.clients, true), (candidates.handlers, false)] {
            for &symbol in symbols {
                if display(facts, symbol) != name {
                    continue;
                }
                let information = &facts.symbols[symbol.index()];
                if information.owner.is_none() {
                    proof.reason = "generated_candidate_owner_not_verified";
                    return proof;
                }
                let owner = &facts.symbols[information.owner.index()];
                let owner_name = display(facts, information.owner);
                let transport = client && transports.iter().any(|proof| proof.symbol == symbol);
                let valid_owner = if client {
                    owner.kind == 13 && (transport || owner_name.ends_with("Client"))
                } else {
                    matches!(owner.kind, 14 | 18)
                        && owner_name.ends_with("Handler")
                        && information.properties & 4 != 0
                };
                if !transport
                    && !candidates.literal_packages.is_empty()
                    && !candidates
                        .literal_packages
                        .contains(&package(facts.symbol_name(information.owner)).as_str())
                {
                    proof.reason = "generated_candidate_owner_not_verified";
                    return proof;
                }
                if information.kind != 3
                    || information.flags & SYMBOL_DEFINED == 0
                    || information.file.is_none()
                    || facts.files[information.file.index()].flags & SOURCE_VERIFIED == 0
                    || !valid_owner
                    || self.blocked(symbol)
                    || self.blocked(information.owner)
                {
                    proof.reason = "generated_candidate_owner_not_verified";
                    return proof;
                }
                if client {
                    clients.push(symbol);
                } else {
                    handlers.push(symbol);
                }
            }
        }
        clients.sort_unstable();
        clients.dedup();
        handlers.sort_unstable();
        handlers.dedup();
        let mut client_groups: Vec<_> = clients
            .iter()
            .map(|&symbol| self.canonical(symbol))
            .collect();
        client_groups.sort_unstable();
        client_groups.dedup();
        let mut handler_groups: Vec<_> = handlers
            .iter()
            .map(|&symbol| self.canonical(symbol))
            .collect();
        handler_groups.sort_unstable();
        handler_groups.dedup();
        let mut client_owners: Vec<_> = clients
            .iter()
            .map(|&symbol| self.canonical(facts.symbols[symbol.index()].owner))
            .collect();
        client_owners.sort_unstable();
        client_owners.dedup();
        let mut handler_owners: Vec<_> = handlers
            .iter()
            .map(|&symbol| self.canonical(facts.symbols[symbol.index()].owner))
            .collect();
        handler_owners.sort_unstable();
        handler_owners.dedup();
        if client_groups.len() != 1
            || handler_groups.len() != 1
            || client_owners.len() != 1
            || handler_owners.len() != 1
        {
            return proof;
        }

        let client = clients[0];
        let handler = handlers[0];
        let client_owner = facts.symbols[client.index()].owner;
        let handler_owner = facts.symbols[handler.index()].owner;
        if transports.is_empty()
            && (display(facts, client_owner).strip_suffix("Client")
                != display(facts, handler_owner).strip_suffix("Handler")
                || package(facts.symbol_name(client_owner))
                    != package(facts.symbol_name(handler_owner)))
        {
            return proof;
        }
        let symbols = self.closure(clients.iter().chain(&handlers).copied());
        for &symbol in &symbols {
            let information = &facts.symbols[symbol.index()];
            if information.kind != 3
                || information.flags & SYMBOL_DEFINED == 0
                || information.file.is_none()
                || facts.files[information.file.index()].flags & SOURCE_VERIFIED == 0
                || self.blocked(symbol)
            {
                proof.reason = "operation_override_inventory_missing_or_conflicting";
                return proof;
            }
            if self.invalid_override_sources.binary_search(&symbol).is_ok() {
                proof.reason = "operation_override_inventory_missing_or_conflicting";
                return proof;
            }
        }
        let mut evidence = Vec::new();
        for &handler in &handlers {
            evidence.extend(self.evidence(operation, handler, candidates.literal_packages));
        }
        if evidence.is_empty() {
            proof.reason = "generated_route_operation_reference_unproved";
            return proof;
        }
        proof.complete = true;
        proof.reason = "compiler_bound_generated_operation_and_override_closure";
        proof.client = client;
        proof.handler = handler;
        proof.clients = clients;
        proof.handlers = handlers;
        proof.context_equivalences = self
            .context_equivalences
            .iter()
            .enumerate()
            .filter(|(_, group)| {
                group.symbols.iter().any(|symbol| {
                    symbols.contains(symbol)
                        || proof
                            .clients
                            .iter()
                            .chain(&proof.handlers)
                            .any(|&root| self.facts.symbols[root.index()].owner == *symbol)
                })
            })
            .map(|(index, _)| index as u32)
            .collect();
        proof.symbols = symbols;
        proof.evidence = evidence;
        proof
    }
    pub fn guards(&self, proof: &OperationProof) -> Vec<OperationGuard> {
        let mut files: BTreeMap<FileId, Vec<SymbolId>> = BTreeMap::new();
        for &symbol in proof.symbols.iter().chain(&proof.positive_route_symbols) {
            let file = self.facts.symbols[symbol.index()].file;
            if !file.is_none() {
                files.entry(file).or_default().push(symbol);
            }
        }
        for evidence in &proof.evidence {
            files.entry(evidence.file).or_default();
        }
        files
            .into_iter()
            .map(|(file, mut symbols)| {
                symbols.sort_unstable();
                symbols.dedup();
                let router = self.router_files.binary_search(&file).is_ok()
                    || (self
                        .facts
                        .path(file)
                        .split('/')
                        .any(|part| part == "src_managed")
                        && self.facts.path(file).ends_with("/Routes.scala"));
                let precise = proof.complete && !router && !symbols.is_empty();
                OperationGuard {
                    file,
                    scope: if precise {
                        GuardScope::Methods
                    } else {
                        GuardScope::File
                    },
                    symbols: if precise { symbols } else { Vec::new() },
                    reason: if router {
                        "shared_generated_router_requires_file_guard"
                    } else if precise {
                        "compiler_bound_operation_methods"
                    } else {
                        "operation_scope_not_proved"
                    },
                }
            })
            .collect()
    }
}
fn display(facts: &FactSnapshot, symbol: SymbolId) -> &str {
    if symbol.is_none() {
        ""
    } else {
        let information = &facts.symbols[symbol.index()];
        let value = facts.text(information.display);
        if value.is_empty() {
            selector_types::symbol::member_name(facts.symbol_name(symbol)).unwrap_or("")
        } else {
            value
        }
    }
}
fn package(owner: &str) -> String {
    selector_types::symbol::global_owner(owner)
        .unwrap_or("")
        .trim_end_matches('/')
        .replace('/', ".")
}
fn route_region(source: &str, name: Span) -> Option<(u32, u32, u32)> {
    let start = source
        .get(..name.start as usize)?
        .rfind('\n')
        .map_or(0, |at| at + 1);
    let line_end = source[start..]
        .find('\n')
        .map_or(source.len(), |at| start + at);
    let line = source[start..line_end].trim_end_matches('\r');
    if !line.starts_with("  def routes")
        || !line.ends_with(" = {")
        || !matches!(line.as_bytes().get(12), Some(b'[' | b'('))
        || name.start as usize != start + 6
        || name.end as usize != start + 12
    {
        return None;
    }
    let mut offset = line_end + usize::from(line_end < source.len());
    for next in source.get(offset..)?.split_inclusive('\n') {
        if next.trim_end_matches(['\n', '\r']) == "  }" {
            let number = source[..start]
                .bytes()
                .filter(|&byte| byte == b'\n')
                .count() as u32;
            return Some((
                start as u32,
                (offset + next.trim_end_matches(['\n', '\r']).len()) as u32,
                number,
            ));
        }
        offset += next.len();
    }
    None
}

#[derive(Clone, Copy)]
struct Token<'a> {
    text: &'a str,
    start: usize,
    end: usize,
}
fn tokens(source: &str) -> Option<Vec<Token<'_>>> {
    let bytes = source.as_bytes();
    let mut result = Vec::new();
    let mut at = 0;
    while at < bytes.len() {
        let byte = bytes[at];
        if byte.is_ascii_whitespace() {
            at += 1;
            continue;
        }
        if source[at..].starts_with("//") {
            at = source[at..].find('\n').map_or(bytes.len(), |end| at + end);
            continue;
        }
        if source[at..].starts_with("/*") {
            let mut depth = 1;
            at += 2;
            while at < bytes.len() && depth > 0 {
                if source[at..].starts_with("/*") {
                    depth += 1;
                    at += 2;
                } else if source[at..].starts_with("*/") {
                    depth -= 1;
                    at += 2;
                } else {
                    at += source[at..].chars().next()?.len_utf8();
                }
            }
            if depth != 0 {
                return None;
            }
            continue;
        }
        let start = at;
        if byte == b'"' {
            if source[at..].starts_with("\"\"\"") {
                return None;
            }
            at += 1;
            while at < bytes.len() {
                match bytes[at] {
                    b'\\' => {
                        at += 2;
                        if at > bytes.len() {
                            return None;
                        }
                    }
                    b'"' => {
                        at += 1;
                        break;
                    }
                    b'\n' | b'\r' => return None,
                    _ => at += 1,
                }
            }
            if at > bytes.len() || bytes.get(at - 1) != Some(&b'"') {
                return None;
            }
        } else if byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'$' {
            at += 1;
            while at < bytes.len()
                && (bytes[at].is_ascii_alphanumeric() || bytes[at] == b'_' || bytes[at] == b'$')
            {
                at += 1;
            }
        } else if byte.is_ascii() {
            at += 1;
        } else {
            return None;
        }
        result.push(Token {
            text: &source[start..at],
            start,
            end: at,
        });
        if result.len() > 1_000_000 {
            return None;
        }
    }
    Some(result)
}
fn identifier(value: &str) -> bool {
    !value.is_empty()
        && value.bytes().enumerate().all(|(index, byte)| {
            byte.is_ascii_alphabetic() || byte == b'_' || (index > 0 && byte.is_ascii_digit())
        })
}
/// Bounded emitted path DSL: literal segments and Segment/IntNumber/LongNumber,
/// with one direct matching HTTP verb/customExtract call outside strings/comments.
pub fn route_matches_wire_identity(line: &str, operation: WireOperation<'_>) -> bool {
    if !matches!(
        operation.verb,
        "get" | "post" | "put" | "patch" | "delete" | "options" | "head" | "trace"
    ) {
        return false;
    }
    let Some(tokens) = tokens(line) else {
        return false;
    };
    let texts: Vec<_> = tokens.iter().map(|token| token.text).collect();
    if texts.get(..2) != Some(&["path", "("]) {
        return false;
    }
    let Some(close) = texts[2..]
        .iter()
        .position(|&token| token == ")")
        .map(|index| index + 2)
    else {
        return false;
    };
    if texts[2..close].contains(&"(") {
        return false;
    }
    let mut bases = BTreeSet::new();
    let urls = if operation.server_urls.is_empty() {
        &[""][..]
    } else {
        operation.server_urls
    };
    for url in urls {
        if url.contains(['{', '}', '?', '#']) {
            return false;
        }
        let path = if let Some((_, rest)) = url.split_once("://") {
            rest.find('/').map_or("", |at| &rest[at..])
        } else if let Some(rest) = url.strip_prefix("//") {
            rest.find('/').map_or("", |at| &rest[at..])
        } else {
            url
        };
        bases.insert(path.trim_end_matches('/'));
    }
    if bases.len() != 1 {
        return false;
    }
    let expected = format!("{}{}", bases.into_iter().next().unwrap(), operation.path);
    let expected: Vec<_> = expected.trim_matches('/').split('/').collect();
    let segments: Vec<_> = texts[2..close].split(|&token| token == "/").collect();
    if segments.len() != expected.len() {
        return false;
    }
    for (actual, expected) in segments.into_iter().zip(expected) {
        if actual.len() != 1 {
            return false;
        }
        if expected.starts_with('{')
            && expected.ends_with('}')
            && expected.len() > 2
            && !expected[1..expected.len() - 1].contains(['{', '}'])
        {
            if !matches!(actual[0], "Segment" | "IntNumber" | "LongNumber") {
                return false;
            }
        } else if serde_json::from_str::<String>(actual[0]).ok().as_deref() != Some(expected) {
            return false;
        }
    }
    let operation_literal = serde_json::to_string(operation.operation_id).unwrap();
    texts
        .windows(5)
        .filter(|window| {
            window[0] == operation.verb
                && window[1] == "("
                && window[2] == "customExtract"
                && window[3] == "("
                && window[4] == operation_literal
        })
        .count()
        == 1
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum GenerationMode {
    ScalaClient,
    ScalaServer,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenerationTask {
    pub schema_path: String,
    pub package: String,
    pub mode: GenerationMode,
}

fn arguments<'t, 's>(
    tokens: &'t [Token<'s>],
    offset: usize,
) -> Option<(Vec<&'t [Token<'s>]>, usize)> {
    let close = match tokens.get(offset)?.text {
        "(" => ")",
        "{" => "}",
        _ => return None,
    };
    let mut stack = vec![close];
    let mut result = Vec::new();
    let mut start = offset + 1;
    for index in start..tokens.len() {
        let token = tokens[index].text;
        match token {
            "(" => stack.push(")"),
            "[" => stack.push("]"),
            "{" => stack.push("}"),
            ")" | "]" | "}" => {
                if stack.pop()? != token {
                    return None;
                }
                if stack.is_empty() {
                    if start < index {
                        result.push(&tokens[start..index]);
                    }
                    return Some((result, index + 1));
                }
            }
            "," if stack.len() == 1 => {
                if start == index {
                    return None;
                }
                result.push(&tokens[start..index]);
                start = index + 1;
            }
            _ => {}
        }
        if stack.len() > 256 {
            return None;
        }
    }
    None
}
fn literal(tokens: &[Token<'_>], environment: Option<(&str, &str)>) -> Option<String> {
    let (interpolated, tokens) = if tokens.first()?.text == "s" {
        (true, &tokens[1..])
    } else {
        (false, tokens)
    };
    if tokens.len() != 1 {
        return None;
    }
    let value = serde_json::from_str::<String>(tokens[0].text).ok()?;
    if value.len() > 64 * 1024 {
        return None;
    }
    if !value.contains('$') {
        return Some(value);
    }
    if !interpolated {
        return None;
    }
    let (variable, replacement) = environment?;
    let mut result = String::with_capacity(value.len());
    let mut at = 0;
    while let Some(found) = value[at..].find('$') {
        let start = at + found;
        result.push_str(&value[at..start]);
        let rest = &value[start + 1..];
        if let Some(rest) = rest.strip_prefix('{') {
            let close = rest.find('}')?;
            if &rest[..close] != variable {
                return None;
            }
            result.push_str(replacement);
            at = start + close + 3;
        } else {
            if !rest.starts_with(variable)
                || rest.as_bytes().get(variable.len()).is_some_and(|byte| {
                    byte.is_ascii_alphanumeric() || *byte == b'_' || *byte == b'$'
                })
            {
                return None;
            }
            result.push_str(replacement);
            at = start + 1 + variable.len();
        }
    }
    result.push_str(&value[at..]);
    if result.contains('$') {
        None
    } else {
        Some(result)
    }
}
fn api_path(path: &str) -> bool {
    let parts: Vec<_> = path.split('/').collect();
    if parts
        .iter()
        .any(|part| part.is_empty() || *part == "." || *part == "..")
        || !matches!(
            parts
                .last()
                .and_then(|part| part.rsplit_once('.'))
                .map(|(_, extension)| extension),
            Some("yaml" | "yml")
        )
    {
        return false;
    }
    (path.starts_with("apps/") && path.contains("/src/main/openapi/"))
        || (path.starts_with("token-standard/") && path.contains("/openapi/"))
}
fn task(tokens: &[Token<'_>], environment: Option<(&str, &str)>) -> Option<GenerationTask> {
    let mode = match tokens.first()?.text {
        "ScalaClient" => GenerationMode::ScalaClient,
        "ScalaServer" => GenerationMode::ScalaServer,
        _ => return None,
    };
    let (arguments, end) = arguments(tokens, 1)?;
    if end != tokens.len() {
        return None;
    }
    let file = *arguments.first()?;
    if file.len() < 5
        || file[0].text != "new"
        || file[1].text != "File"
        || file[2].text != "("
        || file.last()?.text != ")"
    {
        return None;
    }
    let schema_path = literal(&file[3..file.len() - 1], environment)?;
    let mut package = None;
    for argument in &arguments[1..] {
        if argument
            .get(..2)
            .is_some_and(|tokens| tokens[0].text == "pkg" && tokens[1].text == "=")
        {
            if package.is_some() {
                return None;
            }
            package = Some(literal(&argument[2..], environment)?);
        }
    }
    let package = package?;
    if !api_path(&schema_path) || !package.split('.').all(identifier) {
        return None;
    }
    Some(GenerationTask {
        schema_path,
        package,
        mode,
    })
}
/// Finite metadata adapter, never SBT evaluation. Unsupported writes, unknown
/// expressions, unbound interpolation, producer collisions and scope changes fail
/// closed. At most32 literal flatMap values and4096 emitted tasks are admitted.
pub fn literal_generation_tasks(build_text: &str) -> Option<Vec<GenerationTask>> {
    if build_text.len() > 4 * 1024 * 1024 {
        return None;
    }
    let tokens = tokens(build_text)?;
    let prefix = ["Compile", "/", "guardrailTasks", ":", "="];
    for (index, token) in tokens.iter().enumerate() {
        if token.text == "guardrailTasks"
            && tokens
                .get(index + 1)
                .is_some_and(|token| matches!(token.text, "+" | "~" | ":"))
        {
            if index < 2
                || tokens
                    .get(index - 2..index + 3)
                    .is_none_or(|tokens| !tokens.iter().map(|token| token.text).eq(prefix))
            {
                return None;
            }
        }
    }
    let mut result = Vec::new();
    let mut offset = 0;
    while offset + prefix.len() <= tokens.len() {
        if !tokens[offset..offset + prefix.len()]
            .iter()
            .map(|token| token.text)
            .eq(prefix)
        {
            offset += 1;
            continue;
        }
        let expression = offset + prefix.len();
        if tokens.get(expression)?.text != "List" {
            return None;
        }
        let (initial, mut end) = arguments(&tokens, expression + 1)?;
        if tokens
            .get(end..end + 2)
            .is_some_and(|tokens| tokens[0].text == "." && tokens[1].text == "flatMap")
        {
            let (lambda, lambda_end) = arguments(&tokens, end + 2)?;
            if lambda.len() != 1 {
                return None;
            }
            let body = lambda[0];
            if body.len() < 5
                || !identifier(body[0].text)
                || body[1].text != "="
                || body[2].text != ">"
                || body[3].text != "List"
            {
                return None;
            }
            let variable = body[0].text;
            let values: Vec<_> = initial
                .iter()
                .map(|argument| literal(argument, None))
                .collect::<Option<_>>()?;
            if values.is_empty() || values.len() > 32 {
                return None;
            }
            let (tasks, body_end) = arguments(body, 4)?;
            if body_end != body.len() {
                return None;
            }
            let mut uses_variable = false;
            for value in values {
                for tokens in &tasks {
                    let row = task(tokens, Some((variable, &value)))?;
                    uses_variable |= tokens.iter().any(|token| {
                        token.text.contains(&format!("${variable}"))
                            || token.text.contains(&format!("${{{variable}}}"))
                    });
                    result.push(row);
                    if result.len() > 4096 {
                        return None;
                    }
                }
            }
            if !uses_variable {
                return None;
            }
            end = lambda_end;
        } else {
            for tokens in initial {
                result.push(task(tokens, None)?);
                if result.len() > 4096 {
                    return None;
                }
            }
        }
        if tokens
            .get(end)
            .is_some_and(|token| !matches!(token.text, "," | ")"))
        {
            return None;
        }
        offset = end;
    }
    Some(result)
}
/// Pair client/server packages only when no other schema produces that package.
pub fn literal_generation_mappings(tasks: &[GenerationTask]) -> BTreeMap<String, Vec<String>> {
    let mut modes: BTreeMap<(&str, &str), BTreeSet<GenerationMode>> = BTreeMap::new();
    let mut producers: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    for task in tasks {
        modes
            .entry((&task.schema_path, &task.package))
            .or_default()
            .insert(task.mode);
        producers
            .entry(&task.package)
            .or_default()
            .insert(&task.schema_path);
    }
    let mut result: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for ((schema, package), modes) in modes {
        result.entry(schema.to_owned()).or_default();
        if modes.len() == 2 && producers[package].len() == 1 {
            result.get_mut(schema).unwrap().push(package.to_owned());
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use selector_facts::{FactBuilder, FileRecord, OccurrenceRecord, RelationRecord};
    use sha2::{Digest, Sha256};
    pub(super) fn operation<'a>() -> WireOperation<'a> {
        WireOperation {
            schema_path: "apps/wallet/src/main/openapi/wallet.yaml",
            path: "/offer",
            verb: "post",
            operation_id: "acceptOffer",
            server_urls: &[],
        }
    }
    fn file(builder: &mut FactBuilder, path: &str, source: &str) -> FileId {
        let id = FileId(builder.facts.files.len() as u32);
        let path = builder.intern(path).unwrap();
        let source_id = builder.intern(source).unwrap();
        let context = builder.intern("project:wallet/compile").unwrap();
        builder.facts.files.push(FileRecord {
            path,
            source: source_id,
            revision: StrId::NONE,
            context,
            source_hash: ContentHash(Sha256::digest(source.as_bytes()).into()),
            flags: SOURCE_VERIFIED,
        });
        id
    }
    fn symbol(
        builder: &mut FactBuilder,
        name: &str,
        display: &str,
        owner: SymbolId,
        file: FileId,
        kind: u32,
        properties: u64,
    ) -> SymbolId {
        let id = builder.ensure_symbol(name, file).unwrap();
        let display = builder.intern(display).unwrap();
        let record = &mut builder.facts.symbols[id.index()];
        record.display = display;
        record.owner = owner;
        record.kind = kind;
        record.properties = properties;
        record.flags = SYMBOL_DEFINED;
        record.file = file;
        id
    }
    pub(super) struct Fixture {
        pub(super) facts: FactSnapshot,
        pub(super) client: SymbolId,
        pub(super) handler: SymbolId,
        pub(super) implementation: SymbolId,
        pub(super) router: FileId,
    }
    pub(super) fn fixture(literal: &str) -> Fixture {
        let mut builder = FactBuilder::new();
        let client_file = file(
            &mut builder,
            "apps/wallet/target/scala-2.13/src_managed/main/Client.scala",
            "class WalletClient",
        );
        let text = format!(
            "trait WalletHandler[E] {{\n  def acceptOffer(): Unit\n}}\nobject WalletResource {{\n  def routes[E](handler: WalletHandler[E], customExtract: String => Directive1[E]): Route = {{\n    {{\n      path(\"offer\")(post(customExtract(\"{literal}\").apply(extracted => complete(handler.acceptOffer()))))\n    }}\n  }}\n}}\n"
        );
        let router = file(
            &mut builder,
            "apps/wallet/target/scala-2.13/src_managed/main/Routes.scala",
            &text,
        );
        let implementation_file = file(
            &mut builder,
            "apps/wallet/src/main/scala/Handler.scala",
            "class ConcreteHandler",
        );
        let owner = symbol(
            &mut builder,
            "example/http/v0/wallet/WalletClient#",
            "WalletClient",
            SymbolId::NONE,
            client_file,
            13,
            0,
        );
        let client = symbol(
            &mut builder,
            "example/http/v0/wallet/WalletClient#acceptOffer().",
            "acceptOffer",
            owner,
            client_file,
            3,
            0,
        );
        let owner = symbol(
            &mut builder,
            "example/http/v0/wallet/WalletHandler#",
            "WalletHandler",
            SymbolId::NONE,
            router,
            14,
            0,
        );
        let handler = symbol(
            &mut builder,
            "example/http/v0/wallet/WalletHandler#acceptOffer().",
            "acceptOffer",
            owner,
            router,
            3,
            4,
        );
        let owner = symbol(
            &mut builder,
            "example/http/v0/wallet/WalletResource.",
            "WalletResource",
            SymbolId::NONE,
            router,
            10,
            0,
        );
        let routes = symbol(
            &mut builder,
            "example/http/v0/wallet/WalletResource.routes().",
            "routes",
            owner,
            router,
            3,
            0,
        );
        let owner = symbol(
            &mut builder,
            "example/ConcreteHandler#",
            "ConcreteHandler",
            SymbolId::NONE,
            implementation_file,
            13,
            0,
        );
        let implementation = symbol(
            &mut builder,
            "example/ConcreteHandler#acceptOffer().",
            "acceptOffer",
            owner,
            implementation_file,
            3,
            0,
        );
        builder.facts.relations.push(RelationRecord {
            source: implementation,
            target: handler,
            kind: RelationKind::Override,
            file: implementation_file,
        });
        let at = text.find("routes[E]").unwrap();
        builder.facts.occurrences.push(OccurrenceRecord {
            file: router,
            symbol: routes,
            span: Span::new(at, at + 6).unwrap(),
            role: 2,
            ordinal: 0,
        });
        let at = text.find("handler.acceptOffer").unwrap() + "handler.".len();
        builder.facts.occurrences.push(OccurrenceRecord {
            file: router,
            symbol: handler,
            span: Span::new(at, at + "acceptOffer".len()).unwrap(),
            role: 1,
            ordinal: 1,
        });
        Fixture {
            facts: builder.facts,
            client,
            handler,
            implementation,
            router,
        }
    }
    #[test]
    fn exact_wire_identity_checks_verb_segments_base_and_literal_extraction() {
        let line = " path(\"offer\")(post(customExtract(\"acceptOffer\").apply(x => complete(handler.acceptOffer()))))";
        assert!(route_matches_wire_identity(line, operation()));
        assert!(!route_matches_wire_identity(
            line,
            WireOperation {
                verb: "get",
                ..operation()
            }
        ));
        assert!(!route_matches_wire_identity(
            line,
            WireOperation {
                path: "/other",
                ..operation()
            }
        ));
        assert!(!route_matches_wire_identity(
            line,
            WireOperation {
                server_urls: &["https://host/api"],
                ..operation()
            }
        ));
        assert!(route_matches_wire_identity(
            "path(\"api\" / \"offer\" / Segment)(post(customExtract(\"acceptOffer\")))",
            WireOperation {
                path: "/offer/{id}",
                server_urls: &["https://host/api"],
                ..operation()
            }
        ));
        assert!(!route_matches_wire_identity(
            "path(\"offer\")(get(\"post(customExtract(\\\"acceptOffer\\\"))\"))",
            operation()
        ));
        assert!(!route_matches_wire_identity(
            line,
            WireOperation {
                server_urls: &["https://host/api?unknown=1"],
                ..operation()
            }
        ));
    }
    #[test]
    fn compiler_route_proof_scopes_methods_but_keeps_shared_router_file_guard() {
        let fixture = fixture("acceptOffer");
        let index = RouterReferences::new(&fixture.facts);
        let proof = index.prove_operation(
            operation(),
            RouteCandidates {
                clients: &[fixture.client],
                handlers: &[fixture.handler],
                literal_packages: &[],
                inventory_complete: true,
            },
        );
        assert!(proof.complete, "{}", proof.reason);
        assert_eq!(proof.evidence.len(), 1);
        assert!(proof.symbols.contains(&fixture.implementation));
        assert_eq!(
            proof.evidence[0].source_sha256,
            fixture.facts.files[fixture.router.index()].source_hash
        );
        assert!(
            index
                .guards(&proof)
                .iter()
                .any(|guard| guard.file == fixture.router
                    && guard.scope == GuardScope::File
                    && guard.symbols.is_empty())
        );
        assert!(
            index
                .guards(&proof)
                .iter()
                .any(|guard| guard.scope == GuardScope::Methods
                    && guard.symbols.contains(&fixture.implementation))
        );
    }
    #[test]
    fn renamed_operation_requires_exact_compiler_reference_wire_proof() {
        let fixture = fixture("AcceptOffer");
        let index = RouterReferences::new(&fixture.facts);
        let proof = index.prove_operation(
            WireOperation {
                operation_id: "AcceptOffer",
                ..operation()
            },
            RouteCandidates {
                clients: &[fixture.client],
                handlers: &[fixture.handler],
                literal_packages: &[],
                inventory_complete: true,
            },
        );
        assert!(proof.complete, "{}", proof.reason);
        assert!(proof.recovered_compiler_name);
        assert_eq!(proof.compiler_operation_name, "acceptOffer");
    }
    #[test]
    fn partial_missing_duplicate_and_wrong_schema_never_certify_scope() {
        let mut fixture = fixture("acceptOffer");
        let check = |facts: &FactSnapshot, operation| {
            RouterReferences::new(facts).prove_operation(
                operation,
                RouteCandidates {
                    clients: &[fixture.client],
                    handlers: &[fixture.handler],
                    literal_packages: &[],
                    inventory_complete: true,
                },
            )
        };
        assert!(
            !check(
                &fixture.facts,
                WireOperation {
                    schema_path: "apps/other/src/main/openapi/other.yaml",
                    ..operation()
                }
            )
            .complete
        );
        assert!(
            !RouterReferences::new(&fixture.facts)
                .prove_operation(
                    operation(),
                    RouteCandidates {
                        clients: &[fixture.client],
                        handlers: &[fixture.handler],
                        literal_packages: &[],
                        inventory_complete: false
                    }
                )
                .complete
        );
        fixture.facts.occurrences.push(fixture.facts.occurrences[1]);
        let proof = check(&fixture.facts, operation());
        assert!(!proof.complete);
        assert_eq!(proof.reason, "generated_route_operation_reference_unproved");
        assert!(
            RouterReferences::new(&fixture.facts)
                .guards(&proof)
                .iter()
                .all(|guard| guard.scope == GuardScope::File)
        );
        fixture.facts.occurrences.truncate(1);
        assert!(!check(&fixture.facts, operation()).complete);
    }
    #[test]
    fn missing_override_parent_and_unverified_source_preserve_unknown_scope() {
        let mut fixture = fixture("acceptOffer");
        let missing = SymbolId(fixture.facts.symbols.len() as u32);
        fixture.facts.symbols.push(selector_facts::SymbolRecord {
            name: StrId::NONE,
            display: StrId::NONE,
            owner: SymbolId::NONE,
            file: FileId::NONE,
            context: StrId::NONE,
            kind: 0,
            properties: 0,
            signature: StrId::NONE,
            span: Span::default(),
            flags: 0,
        });
        fixture.facts.relations.push(RelationRecord {
            source: fixture.implementation,
            target: missing,
            kind: RelationKind::Override,
            file: fixture.facts.symbols[fixture.implementation.index()].file,
        });
        let proof = RouterReferences::new(&fixture.facts).prove_operation(
            operation(),
            RouteCandidates {
                clients: &[fixture.client],
                handlers: &[fixture.handler],
                literal_packages: &[],
                inventory_complete: true,
            },
        );
        assert!(!proof.complete);
        assert_eq!(
            proof.reason,
            "operation_override_inventory_missing_or_conflicting"
        );
        fixture.facts.files[fixture.router.index()].flags = 0;
        assert!(
            RouterReferences::new(&fixture.facts)
                .evidence(operation(), fixture.handler, &[])
                .is_empty()
        );
    }
    #[test]
    fn finite_generation_tasks_pair_and_retain_collisions() {
        let paired = r#"Compile / guardrailTasks := List(ScalaClient(new File("apps/wallet/src/main/openapi/wallet.yaml"), pkg = "example.http"), ScalaServer(new File("apps/wallet/src/main/openapi/wallet.yaml"), pkg = "example.http"))"#;
        let mut tasks = literal_generation_tasks(paired).unwrap();
        assert_eq!(tasks.len(), 2);
        assert_eq!(
            literal_generation_mappings(&tasks)["apps/wallet/src/main/openapi/wallet.yaml"],
            ["example.http"]
        );
        tasks.push(GenerationTask {
            schema_path: "apps/other/src/main/openapi/other.yaml".into(),
            package: "example.http".into(),
            mode: GenerationMode::ScalaClient,
        });
        assert!(
            literal_generation_mappings(&tasks)["apps/wallet/src/main/openapi/wallet.yaml"]
                .is_empty()
        );
        assert!(literal_generation_tasks("Compile / guardrailTasks += unknownTask").is_none());
        assert!(literal_generation_tasks("Test / guardrailTasks := List()").is_none());
        assert!(literal_generation_tasks("Compile / guardrailTasks := unknownTask").is_none());
    }
    #[test]
    fn finite_flatmap_interpolates_only_its_bound_variable() {
        let build = r#"Compile / guardrailTasks := List("wallet", "scan").flatMap { name => List(ScalaClient(new File(s"apps/$name/src/main/openapi/api.yaml"), pkg = s"example.${name}"), ScalaServer(new File(s"apps/$name/src/main/openapi/api.yaml"), pkg = s"example.${name}")) }"#;
        let tasks = literal_generation_tasks(build).unwrap();
        assert_eq!(tasks.len(), 4);
        assert_eq!(literal_generation_mappings(&tasks).len(), 2);
        assert!(literal_generation_tasks(&build.replace("${name}", "${other}")).is_none());
        assert!(
            literal_generation_tasks(
                &build
                    .replace("$name", "wallet")
                    .replace("${name}", "wallet")
            )
            .is_none()
        );
    }
}

#[cfg(test)]
mod finite_mapping_tests {
    use super::tests::{Fixture, fixture, operation};
    use super::*;
    use selector_facts::FileRecord;
    #[test]
    fn generated_literal_packages_do_not_license_unbound_interpolation() {
        let build = r#"Compile / guardrailTasks := List(ScalaClient(new File("apps/app/src/main/openapi/app.yaml"), pkg = s"example.${unknown}"))"#;
        assert!(literal_generation_tasks(build).is_none());
    }
    fn intern_facts(facts: &mut FactSnapshot, text: &str) -> StrId {
        let id = StrId(facts.strings.entries.len() as u32);
        facts.strings.entries.push(selector_facts::TextRange {
            start: facts.strings.bytes.len() as u64,
            len: text.len() as u32,
        });
        facts.strings.bytes.extend_from_slice(text.as_bytes());
        id
    }
    fn duplicated_context_fixture() -> (Fixture, SymbolId, SymbolId) {
        let mut fixture = fixture("acceptOffer");
        let facts = &mut fixture.facts;
        let method = intern_facts(
            facts,
            r#"{"method_signature":{"parameter_lists":[],"return_type":{"type_ref":{"symbol":"scala/Unit#"}}}}"#,
        );
        let class = intern_facts(
            facts,
            r#"{"class_signature":{"parents":[{"type_ref":{"symbol":"scala/AnyRef#"}}],"declarations":{"symlinks":[]}}}"#,
        );
        let other_class = intern_facts(
            facts,
            r#"{"class_signature":{"parents":[{"type_ref":{"symbol":"scala/AnyRef#"}}],"declarations":{"symlinks":["other/Extra#"]}}}"#,
        );
        for symbol in &mut facts.symbols {
            symbol.signature = if symbol.kind == 3 { method } else { class };
        }
        let mut files = HashMap::new();
        for file in [facts.symbols[fixture.client.index()].file, fixture.router] {
            let old = facts.files[file.index()];
            let header = "/* This file was generated by guardrail. */\n";
            let source = format!("{header}{}", facts.text(old.source));
            let source_id = intern_facts(facts, &source);
            facts.files[file.index()].source = source_id;
            facts.files[file.index()].source_hash =
                ContentHash(Sha256::digest(source.as_bytes()).into());
            for occurrence in facts
                .occurrences
                .iter_mut()
                .filter(|occurrence| occurrence.file == file)
            {
                occurrence.span.start += header.len() as u32;
                occurrence.span.end += header.len() as u32;
            }
            let path = facts.path(file).replace("apps/wallet/", "apps/other/");
            let path = intern_facts(facts, &path);
            let context = intern_facts(facts, "project:other/compile");
            let source = format!("{source}// unrelated generated endpoint\n");
            let hash = ContentHash(Sha256::digest(source.as_bytes()).into());
            let source = intern_facts(facts, &source);
            let copy = FileId(facts.files.len() as u32);
            facts.files.push(FileRecord {
                path,
                context,
                source,
                source_hash: hash,
                ..old
            });
            files.insert(file, copy);
        }
        let originals: Vec<_> = facts
            .symbols
            .iter()
            .copied()
            .enumerate()
            .filter(|(_, info)| files.contains_key(&info.file))
            .collect();
        let mapping: HashMap<_, _> = originals
            .iter()
            .enumerate()
            .map(|(offset, (index, _))| {
                (
                    SymbolId(*index as u32),
                    SymbolId((facts.symbols.len() + offset) as u32),
                )
            })
            .collect();
        for (_, mut info) in originals {
            info.file = files[&info.file];
            info.context = facts.files[info.file.index()].context;
            info.owner = mapping.get(&info.owner).copied().unwrap_or(info.owner);
            if info.kind != 3 {
                info.signature = other_class;
            }
            facts.symbols.push(info);
        }
        let occurrences: Vec<_> = facts
            .occurrences
            .iter()
            .copied()
            .filter(|occurrence| files.contains_key(&occurrence.file))
            .collect();
        for mut occurrence in occurrences {
            occurrence.file = files[&occurrence.file];
            occurrence.symbol = mapping[&occurrence.symbol];
            facts.occurrences.push(occurrence);
        }
        let detail = intern_facts(facts, "global generated context declarations differ");
        facts.issues.push(selector_facts::IssueRecord {
            kind: IssueKind::ContextConflict,
            file: FileId::NONE,
            symbol: fixture.client,
            detail,
        });
        let client = mapping[&fixture.client];
        let handler = mapping[&fixture.handler];
        (fixture, client, handler)
    }
    #[test]
    fn generated_context_contracts_keep_all_copies_and_global_conflict() {
        let (fixture, client, handler) = duplicated_context_fixture();
        let index = RouterReferences::new(&fixture.facts);
        let proof = index.prove_operation(
            operation(),
            RouteCandidates {
                clients: &[fixture.client, client],
                handlers: &[fixture.handler, handler],
                literal_packages: &["example.http.v0.wallet"],
                inventory_complete: true,
            },
        );
        assert!(proof.complete, "{}", proof.reason);
        assert_eq!(proof.clients.len(), 2);
        assert_eq!(proof.handlers.len(), 2);
        assert_eq!(proof.evidence.len(), 2);
        assert!(!proof.context_equivalences.is_empty());
        assert!(
            index
                .context_equivalences()
                .iter()
                .all(|row| row.global_conflict_retained && row.files.len() == 2)
        );
        assert_eq!(
            fixture
                .facts
                .issues
                .iter()
                .filter(|issue| issue.kind == IssueKind::ContextConflict)
                .count(),
            1
        );
        assert!(proof.symbols.contains(&fixture.implementation));
    }
    #[test]
    fn changed_method_contract_or_unverified_context_cannot_merge_generated_endpoints() {
        let (mut fixture, client, handler) = duplicated_context_fixture();
        let signature = intern_facts(
            &mut fixture.facts,
            r#"{"method_signature":{"parameter_lists":[],"return_type":{"type_ref":{"symbol":"other/Type#"}}}}"#,
        );
        fixture.facts.symbols[client.index()].signature = signature;
        let candidates = RouteCandidates {
            clients: &[fixture.client, client],
            handlers: &[fixture.handler, handler],
            literal_packages: &[],
            inventory_complete: true,
        };
        assert!(
            !RouterReferences::new(&fixture.facts)
                .prove_operation(operation(), candidates)
                .complete
        );
        fixture.facts.symbols[client.index()].signature =
            fixture.facts.symbols[fixture.client.index()].signature;
        let file = fixture.facts.symbols[client.index()].file;
        fixture.facts.files[file.index()].flags = 0;
        assert!(
            !RouterReferences::new(&fixture.facts)
                .prove_operation(operation(), candidates)
                .complete
        );
    }
}

/// Source-verified contract equivalence is local to HTTP binding. It never
/// deletes or rewrites the ordinary compiler conflict inventory.
#[derive(Debug, Clone)]
pub struct ContextEquivalence {
    pub compiler_symbol: String,
    pub symbols: Vec<SymbolId>,
    pub files: Vec<FileId>,
    pub source_sha256s: Vec<ContentHash>,
    pub contract_sha256: ContentHash,
    pub global_conflict_retained: bool,
}
#[derive(Debug, Clone)]
pub struct TransportProof {
    pub symbol: SymbolId,
    pub file: FileId,
    pub request_helper_symbol: SymbolId,
    pub source_sha256: ContentHash,
    pub method_tokens_sha256: ContentHash,
    pub verb: String,
    pub base_path: String,
    pub uri_template: String,
}
fn context_equivalences(
    facts: &FactSnapshot,
) -> (Vec<ContextEquivalence>, HashMap<SymbolId, SymbolId>) {
    let generated_files: Vec<_> = facts
        .files
        .iter()
        .enumerate()
        .map(|(index, file)| {
            let path = facts.path(FileId(index as u32));
            let source = facts.text(file.source);
            file.flags & SOURCE_VERIFIED != 0
                && path.split('/').any(|part| part == "src_managed")
                && (path.ends_with("/Routes.scala") || path.ends_with("Client.scala"))
                && source.as_bytes()[..source.len().min(512)]
                    .windows(b"This file was generated by guardrail".len())
                    .any(|window| window == b"This file was generated by guardrail")
        })
        .collect();
    // Index only generated HTTP identities; a program-wide per-symbol duplicate
    // map would allocate far more than the small control-plane proof needs.
    let mut grouped: HashMap<&str, Vec<SymbolId>> = HashMap::new();
    for info in &facts.symbols {
        if info.flags & SYMBOL_DEFINED != 0
            && !info.file.is_none()
            && generated_files[info.file.index()]
        {
            grouped.entry(facts.text(info.name)).or_default();
        }
    }
    for (index, symbol) in facts.symbols.iter().enumerate() {
        if symbol.flags & SYMBOL_DEFINED != 0 && !symbol.file.is_none() {
            if let Some(rows) = grouped.get_mut(facts.text(symbol.name)) {
                rows.push(SymbolId(index as u32));
            }
        }
    }
    let mut result = Vec::new();
    let mut canonical = HashMap::new();
    let mut grouped: Vec<_> = grouped.into_iter().collect();
    grouped.retain(|(_, rows)| rows.len() > 1);
    if grouped.is_empty() {
        return (result, canonical);
    }
    grouped.sort_unstable_by_key(|(name, _)| *name);
    let candidates: HashSet<_> = grouped
        .iter()
        .flat_map(|(_, symbols)| symbols.iter().copied())
        .collect();
    let mut overridden: HashMap<SymbolId, Vec<&str>> = HashMap::new();
    for relation in facts.relations.iter().filter(|relation| {
        relation.kind == RelationKind::Override && candidates.contains(&relation.source)
    }) {
        overridden
            .entry(relation.source)
            .or_default()
            .push(facts.symbol_name(relation.target));
    }
    for parents in overridden.values_mut() {
        parents.sort_unstable();
        parents.dedup();
    }
    let within_context: HashSet<_> = facts
        .issues
        .iter()
        .filter(|issue| {
            issue.kind == IssueKind::ContextConflict
                && (facts.text(issue.detail).contains("one context")
                    || facts.text(issue.detail).contains("same context"))
        })
        .map(|issue| issue.symbol)
        .collect();
    for (name, symbols) in grouped {
        let mut expected = None;
        let mut files = BTreeSet::new();
        let mut valid = true;
        for &symbol in &symbols {
            let info = &facts.symbols[symbol.index()];
            if !generated_files[info.file.index()] || !files.insert(info.file) {
                valid = false;
                break;
            }
            if within_context.contains(&symbol) {
                valid = false;
                break;
            }
            let Some(hash) = contract(
                facts,
                symbol,
                overridden.get(&symbol).map_or(&[], Vec::as_slice),
            ) else {
                valid = false;
                break;
            };
            if expected.is_some_and(|expected| expected != hash) {
                valid = false;
                break;
            }
            expected = Some(hash);
        }
        if !valid {
            continue;
        }
        let representative = symbols[0];
        for &symbol in &symbols {
            canonical.insert(symbol, representative);
        }
        let files: Vec<_> = files.into_iter().collect();
        let mut source_sha256s: Vec<_> = files
            .iter()
            .map(|file| facts.files[file.index()].source_hash)
            .collect();
        source_sha256s.sort_unstable_by_key(|hash| hash.0);
        source_sha256s.dedup();
        result.push(ContextEquivalence {
            compiler_symbol: name.to_owned(),
            symbols,
            files,
            source_sha256s,
            contract_sha256: expected.unwrap(),
            global_conflict_retained: true,
        });
    }
    (result, canonical)
}
fn contract(facts: &FactSnapshot, symbol: SymbolId, overridden: &[&str]) -> Option<ContentHash> {
    let info = &facts.symbols[symbol.index()];
    let mut signature: serde_json::Value = serde_json::from_str(facts.text(info.signature)).ok()?;
    if matches!(info.kind, 10 | 13 | 14 | 18) {
        signature
            .get_mut("class_signature")?
            .as_object_mut()?
            .remove("declarations");
    } else if info.kind != 3
        || !signature
            .get("method_signature")
            .is_some_and(serde_json::Value::is_object)
    {
        return None;
    }
    #[derive(serde::Serialize)]
    struct Contract<'a> {
        kind: u32,
        display_name: &'a str,
        signature: &'a serde_json::Value,
        properties: u64,
        overridden_symbols: &'a [&'a str],
    }
    let bytes = serde_json::to_vec(&Contract {
        kind: info.kind,
        display_name: display(facts, symbol),
        signature: &signature,
        properties: info.properties,
        overridden_symbols: overridden,
    })
    .ok()?;
    Some(ContentHash(Sha256::digest(bytes).into()))
}
