//! Compiler-resolved runtime bridges. Metadata joins existing compiler records;
//! it never manufactures a Scala symbol or resolves a source identifier.
use crate::runtime_routes::{
    RouteCandidates, RouterReferences, WireOperation, literal_generation_mappings,
    literal_generation_tasks,
};
use crate::runtime_schema::{SchemaOperation, SchemaTree};
use crate::{ModelContributions, member_name};
use selector_facts::FactSnapshot;
use selector_graph::{EdgeRecord, GraphIssue};
use selector_types::*;
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::collections::{BTreeSet, HashMap, HashSet};

pub const VERSION: &str = "compiler-runtime-bridges/rust-v1";
pub const ASSIGNED_PROTOCOL: &str =
    "org/lfdecentralizedtrust/splice/automation/OnAssignedContractTrigger#";
pub const LEDGER_SUBMIT_OWNER: &str =
    "org/lfdecentralizedtrust/splice/environment/SpliceLedgerConnection#";
pub const LEDGER_EXTENSIONS_PREFIX: &str =
    "org/lfdecentralizedtrust/splice/console/LedgerApiExtensions.";

#[derive(Clone, Copy, Debug)]
pub struct RuntimeSource<'a> {
    pub path: &'a str,
    pub text: &'a str,
}
#[derive(Default)]
pub struct RuntimeInputs<'a> {
    pub sources: Vec<RuntimeSource<'a>>,
    /// Authoritative exported generator package settings. Literal pkg="..."
    /// assignments from supplied build.sbt are supported as a bounded adapter.
    pub generator_packages: Vec<&'a str>,
    /// Optional compiler-runtime-bridges/v1 compatibility overlay. Endpoints
    /// must resolve uniquely, including explicit context qualifiers if needed.
    pub overlay_json: Option<&'a str>,
    pub manifest_identity: ContentHash,
    /// Captured exporter assertion: all relevant compiler documents were admitted.
    /// Needed for operation-scope certificates and route-based name recovery.
    pub compiler_inventory_complete: bool,
}
#[derive(Clone, Debug)]
pub struct RuntimeDiagnostic {
    pub reason: &'static str,
    pub metadata_path: String,
    pub symbol: SymbolId,
}
pub struct RuntimeContributions {
    pub model: ModelContributions,
    pub identity: ContentHash,
    pub diagnostics: Vec<RuntimeDiagnostic>,
    pub http_bindings: Vec<HttpBinding>,
}
/// Ephemeral operation binding certificate. Kept only for delta seed generation;
/// graph edges retain IDs, never copies of YAML or per-edge metadata strings.
#[derive(Debug, Clone)]
pub struct HttpBinding {
    pub schema_path: String,
    pub path: String,
    pub verb: String,
    pub symbols: Vec<SymbolId>,
    pub guard_files: Vec<FileId>,
    pub scope_complete: bool,
}

/// Identity of explicitly supplied auxiliary inputs. A verified manifest owns
/// its declared identity; direct API inputs receive a canonical content key.
/// Implicit facts-derived models are represented by ZERO at the builder facade.
pub fn runtime_identity(inputs: &RuntimeInputs<'_>) -> ContentHash {
    if inputs.manifest_identity != ContentHash::default() {
        return inputs.manifest_identity;
    }
    if inputs.sources.is_empty()
        && inputs.generator_packages.is_empty()
        && inputs.overlay_json.is_none()
        && !inputs.compiler_inventory_complete
    {
        return ContentHash::default();
    }
    let mut hash = Sha256::new();
    hash.update(b"runtime-direct-inputs/1");
    hash.update([u8::from(inputs.compiler_inventory_complete)]);
    let mut sources: Vec<_> = inputs.sources.iter().copied().collect();
    sources.sort_unstable_by(|a, b| (a.path, a.text).cmp(&(b.path, b.text)));
    for source in sources {
        hash.update((source.path.len() as u64).to_le_bytes());
        hash.update(source.path);
        hash.update((source.text.len() as u64).to_le_bytes());
        hash.update(source.text);
    }
    let mut packages = inputs.generator_packages.clone();
    packages.sort_unstable();
    packages.dedup();
    for package in packages {
        hash.update((package.len() as u64).to_le_bytes());
        hash.update(package);
    }
    if let Some(overlay) = inputs.overlay_json {
        hash.update([1]);
        hash.update((overlay.len() as u64).to_le_bytes());
        hash.update(overlay);
    } else {
        hash.update([0]);
    }
    ContentHash(hash.finalize().into())
}

pub fn contribute(
    facts: &FactSnapshot,
    nodes: &[NodeId],
    inputs: &RuntimeInputs<'_>,
) -> Result<RuntimeContributions, Error> {
    let mut out = RuntimeContributions {
        model: ModelContributions::default(),
        identity: ContentHash::default(),
        diagnostics: Vec::new(),
        http_bindings: Vec::new(),
    };
    let mut hash = Sha256::new();
    hash.update(VERSION);
    hash.update(inputs.manifest_identity.0);
    hash.update([u8::from(inputs.compiler_inventory_complete)]);
    let mut sources: Vec<_> = inputs.sources.iter().copied().collect();
    sources.sort_unstable_by_key(|s| s.path);
    for source in &sources {
        hash.update((source.path.len() as u64).to_le_bytes());
        hash.update(source.path);
        hash.update((source.text.len() as u64).to_le_bytes());
        hash.update(source.text);
    }
    let mut packages: BTreeSet<String> = inputs
        .generator_packages
        .iter()
        .filter(|s| package_literal(s))
        .map(|s| (*s).to_owned())
        .collect();
    for source in &sources {
        if source.path.ends_with("build.sbt") {
            package_roots(source.text, &mut packages);
        }
    }
    for package in &packages {
        hash.update(package);
        hash.update([0]);
    }
    http_bridges(
        facts,
        nodes,
        &sources,
        &packages,
        inputs.compiler_inventory_complete,
        &mut out,
    );
    event_bridges(facts, nodes, &mut out);
    for source in &sources {
        if source.path.ends_with(".ts") || source.path.ends_with(".tsx") {
            diagnostic(
                &mut out,
                facts,
                nodes,
                SymbolId::NONE,
                IssueKind::UnsupportedModel,
                source.path,
                "frontend_string_selector_runtime_join_not_supported",
            );
        }
    }
    if let Some(json) = inputs.overlay_json {
        hash.update(json);
        import_overlay(facts, nodes, json, &mut out)?;
    }
    out.identity = ContentHash(hash.finalize().into());
    Ok(out)
}

/// Rebuild only HTTP operation certificates for a metadata delta. This avoids
/// rerunning event/ledger models or hashing unrelated runtime overlays during
/// selection; all source/compiler proof checks are shared with graph building.
pub fn operation_bindings(
    facts: &FactSnapshot,
    nodes: &[NodeId],
    inputs: &RuntimeInputs<'_>,
) -> Vec<HttpBinding> {
    let mut sources: Vec<_> = inputs.sources.iter().copied().collect();
    sources.sort_unstable_by_key(|source| source.path);
    let mut packages: BTreeSet<_> = inputs
        .generator_packages
        .iter()
        .filter(|package| package_literal(package))
        .map(|package| (*package).to_owned())
        .collect();
    for source in &sources {
        if source.path.ends_with("build.sbt") {
            package_roots(source.text, &mut packages);
        }
    }
    let mut out = RuntimeContributions {
        model: ModelContributions::default(),
        identity: ContentHash::default(),
        diagnostics: Vec::new(),
        http_bindings: Vec::new(),
    };
    http_bridges(
        facts,
        nodes,
        &sources,
        &packages,
        inputs.compiler_inventory_complete,
        &mut out,
    );
    out.http_bindings
}

fn diagnostic(
    out: &mut RuntimeContributions,
    facts: &FactSnapshot,
    nodes: &[NodeId],
    symbol: SymbolId,
    kind: IssueKind,
    path: &str,
    reason: &'static str,
) {
    let (node, file) = if symbol.is_none() {
        (NodeId::NONE, FileId::NONE)
    } else {
        (nodes[symbol.index()], facts.symbols[symbol.index()].file)
    };
    out.model.issues.push(GraphIssue {
        kind,
        node,
        file,
        symbol,
        detail: StrId::NONE,
    });
    out.diagnostics.push(RuntimeDiagnostic {
        reason,
        metadata_path: path.to_owned(),
        symbol,
    });
}
fn bridge(nodes: &[NodeId], source: SymbolId, target: SymbolId, guarded: bool) -> EdgeRecord {
    EdgeRecord {
        source: nodes[source.index()],
        target: nodes[target.index()],
        kind: EdgeKind::RuntimeBridge,
        occurrence: OccurrenceId::NONE,
        operation: OperationId::NONE,
        receiver: SymbolId::NONE,
        flags: if guarded { EDGE_UNKNOWN } else { 0 },
    }
}
fn package_literal(text: &str) -> bool {
    !text.is_empty()
        && text.split('.').all(|part| {
            !part.is_empty()
                && part.bytes().enumerate().all(|(i, b)| {
                    b.is_ascii_alphabetic() || b == b'_' || (i > 0 && b.is_ascii_digit())
                })
        })
}
fn package_roots(text: &str, roots: &mut BTreeSet<String>) {
    // Bounded literal build-setting adapter, not Scala parsing or name lookup.
    for (at, _) in text.match_indices("pkg") {
        if at > 0 && text.as_bytes()[at - 1].is_ascii_alphanumeric() {
            continue;
        }
        let rest = text[at + 3..].trim_start();
        let Some(rest) = rest.strip_prefix('=') else {
            continue;
        };
        let Some(rest) = rest.trim_start().strip_prefix('"') else {
            continue;
        };
        let Some(end) = rest.find('"') else {
            continue;
        };
        let package = &rest[..end];
        if package_literal(package) {
            roots.insert(package.to_owned());
        }
    }
}
fn schema_operations(sources: &[RuntimeSource<'_>]) -> Result<Vec<SchemaOperation>, Error> {
    let yaml: Vec<_> = sources
        .iter()
        .copied()
        .filter(|source| source.path.ends_with(".yaml") || source.path.ends_with(".yml"))
        .collect();
    SchemaTree::new(&yaml)?.binding_operations()
}

struct Generated<'a> {
    symbol: SymbolId,
    method: &'a str,
    owner: &'a str,
    package: String,
}
fn http_bridges(
    facts: &FactSnapshot,
    nodes: &[NodeId],
    sources: &[RuntimeSource<'_>],
    packages: &BTreeSet<String>,
    inventory_complete: bool,
    out: &mut RuntimeContributions,
) {
    let operations = match schema_operations(sources) {
        Ok(operations) => operations,
        Err(_) => {
            for source in sources
                .iter()
                .filter(|source| source.path.ends_with(".yaml") || source.path.ends_with(".yml"))
            {
                diagnostic(
                    out,
                    facts,
                    nodes,
                    SymbolId::NONE,
                    IssueKind::UnsupportedModel,
                    source.path,
                    "unsupported_openapi_metadata",
                );
            }
            return;
        }
    };
    let tasks: Vec<_> = sources
        .iter()
        .filter(|source| source.path.ends_with("build.sbt"))
        .filter_map(|source| literal_generation_tasks(source.text))
        .flatten()
        .collect();
    let mappings = literal_generation_mappings(&tasks);
    let mut generated = Vec::new();
    for (i, symbol) in facts.symbols.iter().enumerate() {
        if symbol.flags & SYMBOL_DEFINED == 0
            || symbol.file.is_none()
            || symbol.owner.is_none()
            || !facts
                .path(symbol.file)
                .split('/')
                .any(|part| part == "src_managed")
            || facts.files[symbol.file.index()].flags & SOURCE_VERIFIED == 0
        {
            continue;
        }
        let owner = facts.symbol_name(symbol.owner);
        let Some(package) = selector_types::symbol::global_owner(owner) else {
            continue;
        };
        generated.push(Generated {
            symbol: SymbolId(i as u32),
            method: member_name(facts.symbol_name(SymbolId(i as u32))),
            owner: member_name(owner),
            package: package.trim_end_matches('/').replace('/', "."),
        });
    }
    // Package postings cover all generated methods for compiler-bound recovery;
    // this avoids rescanning the full inventory for each operation.
    generated.sort_unstable_by(|a, b| {
        (&a.package, a.owner, a.method, a.symbol).cmp(&(&b.package, b.owner, b.method, b.symbol))
    });
    let mut generated_names: Vec<_> = generated
        .iter()
        .map(|declaration| (declaration.method, declaration.symbol))
        .collect();
    generated_names.sort_unstable();
    let router = RouterReferences::new(facts);
    let mut reverse: Vec<_> = facts
        .relations
        .iter()
        .filter(|r| r.kind == RelationKind::Override)
        .map(|r| (r.target, r.source))
        .collect();
    reverse.sort_unstable();
    let conflicts: HashSet<_> = facts
        .issues
        .iter()
        .filter(|issue| issue.kind == IssueKind::ContextConflict)
        .filter_map(|issue| (!issue.symbol.is_none()).then_some(issue.symbol))
        .collect();
    let mut pending = Vec::new();
    let mut visited = HashSet::new();
    for op in operations {
        let metadata = op
            .namespace
            .as_deref()
            .filter(|namespace| package_literal(namespace));
        let stems: BTreeSet<_> = op
            .tags
            .iter()
            .filter(|tag| {
                !tag.is_empty()
                    && tag.bytes().enumerate().all(|(i, b)| {
                        b.is_ascii_alphabetic() || (i > 0 && (b == b'_' || b.is_ascii_digit()))
                    })
            })
            .map(|tag| {
                let mut stem = tag.clone();
                stem[..1].make_ascii_uppercase();
                stem
            })
            .collect();
        let defaults = metadata.is_none() && op.namespace.is_none() && op.tags.is_empty();
        let operation_packages: BTreeSet<_> = if defaults {
            mappings
                .get(&op.schema_path)
                .filter(|packages| packages.len() == 1)
                .into_iter()
                .flatten()
                .cloned()
                .collect()
        } else if let Some(namespace) = metadata {
            packages
                .iter()
                .map(|root| format!("{root}.{namespace}"))
                .collect()
        } else {
            BTreeSet::new()
        };
        let mut clients = Vec::new();
        let mut handlers = Vec::new();
        let mut route_clients = Vec::new();
        let mut route_handlers = Vec::new();
        for package in &operation_packages {
            let first = generated.partition_point(|g| g.package < *package);
            let last = generated.partition_point(|g| g.package <= *package);
            for declaration in &generated[first..last] {
                let client = declaration.owner.strip_suffix("Client");
                let handler = declaration.owner.strip_suffix("Handler");
                if client.is_some() {
                    route_clients.push(declaration.symbol);
                }
                if handler.is_some() {
                    route_handlers.push(declaration.symbol);
                }
                if declaration.method != op.operation_id {
                    continue;
                }
                if client.is_some_and(|stem| stems.contains(stem)) {
                    clients.push(declaration.symbol);
                }
                if handler.is_some_and(|stem| stems.contains(stem)) {
                    handlers.push(declaration.symbol);
                }
            }
        }
        clients.sort_unstable();
        clients.dedup();
        handlers.sort_unstable();
        handlers.dedup();
        let urls: Vec<_> = op.server_urls.iter().map(String::as_str).collect();
        let literal_packages: Vec<_> = if defaults {
            operation_packages.iter().map(String::as_str).collect()
        } else {
            Vec::new()
        };
        let proof = router.prove_operation_with_tasks(
            WireOperation {
                schema_path: &op.schema_path,
                path: &op.path,
                verb: &op.verb,
                operation_id: &op.operation_id,
                server_urls: &urls,
            },
            RouteCandidates {
                clients: &route_clients,
                handlers: &route_handlers,
                literal_packages: &literal_packages,
                inventory_complete,
            },
            &tasks,
            op.namespace.as_deref(),
        );
        let direct = clients.len() == 1
            && handlers.len() == 1
            && {
                let client_owner = facts.symbols[clients[0].index()].owner;
                let handler_owner = facts.symbols[handlers[0].index()].owner;
                let client = facts.symbol_name(client_owner);
                let handler = facts.symbol_name(handler_owner);
                member_name(client).strip_suffix("Client")
                    == member_name(handler).strip_suffix("Handler")
                    && selector_types::symbol::global_owner(client)
                        == selector_types::symbol::global_owner(handler)
                    && facts.symbols[client_owner.index()].context
                        == facts.symbols[handler_owner.index()].context
            }
            && !clients.iter().chain(&handlers).any(|symbol| {
                conflicts.contains(symbol)
                    || conflicts.contains(&facts.symbols[symbol.index()].owner)
            });
        let recovery = !direct
            && proof.complete
            && proof.evidence.iter().all(|evidence| {
                facts
                    .text(facts.files[evidence.file.index()].source)
                    .get(..512)
                    .unwrap_or_else(|| facts.text(facts.files[evidence.file.index()].source))
                    .contains("This file was generated by guardrail")
            });
        if recovery {
            clients.clear();
            clients.extend_from_slice(&proof.clients);
            handlers.clear();
            handlers.extend_from_slice(&proof.handlers);
        }
        let mut symbols: Vec<_> = clients
            .iter()
            .chain(&handlers)
            .copied()
            .chain(proof.positive_route_symbols.iter().copied())
            .collect();
        let mut guard_files: Vec<_> = proof
            .evidence
            .iter()
            .map(|evidence| evidence.file)
            .collect();
        if direct || recovery {
            pending.clear();
            visited.clear();
            pending.extend(handlers.iter().copied());
            let mut implementations = 0;
            while let Some(parent) = pending.pop() {
                if !visited.insert(parent) {
                    continue;
                }
                symbols.push(parent);
                let start = reverse.partition_point(|&(p, _)| p < parent);
                let end = reverse.partition_point(|&(p, _)| p <= parent);
                for &(_, candidate) in &reverse[start..end] {
                    pending.push(candidate);
                    let symbol = &facts.symbols[candidate.index()];
                    if symbol.flags & SYMBOL_DEFINED != 0
                        && symbol.properties & 4 == 0
                        && !conflicts.contains(&candidate)
                    {
                        for &client in &clients {
                            out.model
                                .edges
                                .push(bridge(nodes, client, candidate, false));
                        }
                        implementations += 1;
                    }
                }
            }
            if implementations == 0 {
                for &client in &clients {
                    diagnostic(
                        out,
                        facts,
                        nodes,
                        client,
                        IssueKind::UnresolvedSymbol,
                        &op.schema_path,
                        "unresolved_concrete_http_handler",
                    );
                }
            }
        } else {
            // Failed tag/package metadata cannot exclude positive compiler
            // declarations elsewhere. This spelling lookup only broadens an
            // unknown frontier; it never chooses an executable endpoint.
            let first =
                generated_names.partition_point(|&(name, _)| name < op.operation_id.as_str());
            let last =
                generated_names.partition_point(|&(name, _)| name <= op.operation_id.as_str());
            pending.clear();
            visited.clear();
            pending.extend(
                generated_names[first..last]
                    .iter()
                    .map(|&(_, symbol)| symbol),
            );
            while let Some(symbol) = pending.pop() {
                if !visited.insert(symbol) {
                    continue;
                }
                symbols.push(symbol);
                let first = reverse.partition_point(|&(target, _)| target < symbol);
                let last = reverse.partition_point(|&(target, _)| target <= symbol);
                pending.extend(reverse[first..last].iter().map(|&(_, child)| child));
            }
            symbols.sort_unstable();
            symbols.dedup();
            let reason = if metadata.is_none() || stems.is_empty() {
                "unsupported_openapi_metadata"
            } else {
                "ambiguous_or_missing_generated_http_endpoint"
            };
            if symbols.is_empty() {
                diagnostic(
                    out,
                    facts,
                    nodes,
                    SymbolId::NONE,
                    IssueKind::UnresolvedSymbol,
                    &op.schema_path,
                    reason,
                );
            }
            for &symbol in &symbols {
                diagnostic(
                    out,
                    facts,
                    nodes,
                    symbol,
                    IssueKind::ContextConflict,
                    &op.schema_path,
                    reason,
                );
            }
        }
        symbols.extend(proof.symbols.iter().copied());
        symbols.sort_unstable();
        symbols.dedup();
        guard_files.sort_unstable();
        guard_files.dedup();
        out.http_bindings.push(HttpBinding {
            schema_path: op.schema_path,
            path: op.path,
            verb: op.verb,
            symbols,
            guard_files,
            scope_complete: proof.complete,
        });
    }
}

fn resolve(
    facts: &FactSnapshot,
    name: &str,
    context: Option<&str>,
    path: Option<&str>,
) -> Result<SymbolId, IssueKind> {
    let mut found = None;
    for (i, s) in facts.symbols.iter().enumerate() {
        if facts.text(s.name) != name {
            continue;
        }
        if context.is_some_and(|context| facts.text(s.context) != context) {
            continue;
        }
        if path.is_some_and(|path| facts.path(s.file) != path) {
            continue;
        }
        // Runtime endpoints must be compiler definitions, not unresolved refs.
        if s.flags & SYMBOL_DEFINED == 0 {
            continue;
        }
        if found.is_some() {
            return Err(IssueKind::ContextConflict);
        }
        found = Some(SymbolId(i as u32));
    }
    found.ok_or(IssueKind::UnresolvedSymbol)
}
fn expand_alias(
    facts: &FactSnapshot,
    value: Value,
    context: &str,
    seen: &mut HashSet<SymbolId>,
    depth: usize,
) -> Value {
    if depth >= 32 {
        return value;
    }
    let Some(reference) = value.get("type_ref") else {
        return value;
    };
    let Some(name) = reference.get("symbol").and_then(Value::as_str) else {
        return value;
    };
    let Ok(symbol) = resolve(facts, name, Some(context), None) else {
        return value;
    };
    if !seen.insert(symbol) {
        return value;
    }
    let signature = facts.text(facts.symbols[symbol.index()].signature);
    let Ok(signature) = serde_json::from_str::<Value>(signature) else {
        return value;
    };
    let Some(alias) = signature.get("type_signature") else {
        return value;
    };
    let Some(upper) = alias.get("upper_bound") else {
        return value;
    };
    let parameters = alias
        .pointer("/type_parameters/symlinks")
        .and_then(Value::as_array)
        .map_or(&[][..], Vec::as_slice);
    let arguments = reference
        .get("type_arguments")
        .and_then(Value::as_array)
        .map_or(&[][..], Vec::as_slice);
    if parameters.len() != arguments.len() {
        return value;
    }
    let substitutions: HashMap<_, _> = parameters
        .iter()
        .filter_map(Value::as_str)
        .zip(arguments.iter())
        .collect();
    fn substitute(value: &Value, substitutions: &HashMap<&str, &Value>) -> Value {
        if let Some(name) = value.pointer("/type_ref/symbol").and_then(Value::as_str) {
            if let Some(replacement) = substitutions.get(name) {
                return (*replacement).clone();
            }
        }
        match value {
            Value::Array(items) => {
                Value::Array(items.iter().map(|x| substitute(x, substitutions)).collect())
            }
            Value::Object(fields) => Value::Object(
                fields
                    .iter()
                    .map(|(k, v)| (k.clone(), substitute(v, substitutions)))
                    .collect(),
            ),
            _ => value.clone(),
        }
    }
    expand_alias(
        facts,
        substitute(upper, &substitutions),
        context,
        seen,
        depth + 1,
    )
}
fn is_submission(facts: &FactSnapshot, target: SymbolId) -> bool {
    if target.is_none() {
        return false;
    }
    let s = &facts.symbols[target.index()];
    let name = facts.symbol_name(target);
    (!s.owner.is_none()
        && facts.symbol_name(s.owner) == LEDGER_SUBMIT_OWNER
        && member_name(name) == "submit")
        || (name.starts_with(LEDGER_EXTENSIONS_PREFIX)
            && matches!(
                member_name(name),
                "submitJava" | "submitJavaExternalOrLocal" | "submitJavaExternal"
            ))
}
fn event_bridges(facts: &FactSnapshot, nodes: &[NodeId], out: &mut RuntimeContributions) {
    // Alias candidates use exact compiler reference IDs and context. Build one
    // reverse posting list so a chain of type aliases is traversed once.
    let alias_ids: HashMap<_, _> = facts
        .symbols
        .iter()
        .enumerate()
        .filter(|(_, symbol)| symbol.kind == 7 && !symbol.signature.is_none())
        .map(|(index, symbol)| {
            (
                (symbol.context, facts.symbol_name(SymbolId(index as u32))),
                SymbolId(index as u32),
            )
        })
        .collect();
    let mut alias_reverse = Vec::new();
    let mut alias_pending = Vec::new();
    for &symbol in alias_ids.values() {
        let record = &facts.symbols[symbol.index()];
        if let Ok(signature) = serde_json::from_str::<Value>(facts.text(record.signature)) {
            if let Some(target) = signature
                .pointer("/type_signature/upper_bound/type_ref/symbol")
                .and_then(Value::as_str)
            {
                if target == ASSIGNED_PROTOCOL {
                    alias_pending.push(symbol);
                } else if let Some(parent) = alias_ids.get(&(record.context, target)) {
                    alias_reverse.push((*parent, symbol));
                }
            }
        }
    }
    alias_reverse.sort_unstable();
    let mut alias_seen = HashSet::new();
    while let Some(parent) = alias_pending.pop() {
        if !alias_seen.insert(parent) {
            continue;
        }
        let first = alias_reverse.partition_point(|&(target, _)| target < parent);
        let last = alias_reverse.partition_point(|&(target, _)| target <= parent);
        alias_pending.extend(alias_reverse[first..last].iter().map(|&(_, child)| child));
    }
    let aliases: HashSet<_> = alias_seen
        .into_iter()
        .map(|id| facts.symbol_name(id))
        .collect();
    let mut seen = HashSet::new();
    let mut callback_bindings = Vec::new();
    for (owner_index, s) in facts.symbols.iter().enumerate() {
        if s.flags & SYMBOL_DEFINED == 0 || !matches!(s.kind, 10 | 13 | 14) || s.signature.is_none()
        {
            continue;
        }
        let raw = facts.text(s.signature);
        if !raw.contains(ASSIGNED_PROTOCOL) && !aliases.iter().any(|name| raw.contains(*name)) {
            continue;
        }
        let owner = SymbolId(owner_index as u32);
        let Ok(signature) = serde_json::from_str::<Value>(raw) else {
            diagnostic(
                out,
                facts,
                nodes,
                owner,
                IssueKind::InvalidInput,
                "",
                "invalid_protocol_signature",
            );
            continue;
        };
        let Some(parents) = signature
            .pointer("/class_signature/parents")
            .and_then(Value::as_array)
        else {
            continue;
        };
        for parent in parents {
            seen.clear();
            let parent = expand_alias(facts, parent.clone(), facts.text(s.context), &mut seen, 0);
            if parent.pointer("/type_ref/symbol").and_then(Value::as_str) != Some(ASSIGNED_PROTOCOL)
            {
                continue;
            }
            let arguments = parent
                .pointer("/type_ref/type_arguments")
                .and_then(Value::as_array);
            let template = arguments
                .filter(|a| a.len() == 3)
                .and_then(|a| a[2].pointer("/type_ref/symbol"))
                .and_then(Value::as_str);
            let Some(template) = template else {
                diagnostic(
                    out,
                    facts,
                    nodes,
                    owner,
                    IssueKind::UnsupportedModel,
                    "",
                    "unresolved_assigned_contract_type_arguments",
                );
                continue;
            };
            let callbacks: Vec<_> = facts
                .symbols
                .iter()
                .enumerate()
                .filter(|(i, m)| {
                    m.owner == owner
                        && m.flags & SYMBOL_DEFINED != 0
                        && member_name(facts.symbol_name(SymbolId(*i as u32))) == "completeTask"
                })
                .map(|(i, _)| SymbolId(i as u32))
                .collect();
            if callbacks.len() != 1 {
                diagnostic(
                    out,
                    facts,
                    nodes,
                    owner,
                    IssueKind::ContextConflict,
                    "",
                    "unresolved_assigned_contract_callback",
                );
                continue;
            }
            match resolve(facts, template, Some(facts.text(s.context)), None) {
                Ok(template) => callback_bindings.push((callbacks[0], template)),
                Err(kind) => diagnostic(
                    out,
                    facts,
                    nodes,
                    owner,
                    kind,
                    "",
                    "unresolved_assigned_contract_template",
                ),
            }
        }
    }
    if callback_bindings.is_empty() {
        return;
    }
    // Scan compiler operations once, rather than once per protocol callback.
    let templates: HashSet<_> = callback_bindings.iter().map(|(_, t)| *t).collect();
    let mut producers = Vec::new();
    let mut submissions = vec![false; facts.bodies.len()];
    for op in &facts.operations {
        if op.target.is_none() {
            continue;
        }
        submissions[op.body.index()] |= matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
            && is_submission(facts, op.target);
        let target = &facts.symbols[op.target.index()];
        if target.owner.is_none() {
            continue;
        }
        let template = target.owner;
        if templates.contains(&template)
            && matches!(
                member_name(facts.symbol_name(op.target)),
                "<init>" | "create"
            )
            && matches!(
                op.opcode,
                Opcode::Allocate | Opcode::Call | Opcode::VirtualCall
            )
        {
            producers.push((template, op.body));
        }
    }
    producers.sort_unstable();
    producers.dedup();
    for (callback, template) in &callback_bindings {
        let start = producers.partition_point(|(t, _)| t < template);
        let end = producers.partition_point(|(t, _)| t <= template);
        if start == end {
            diagnostic(
                out,
                facts,
                nodes,
                *callback,
                IssueKind::UnknownExecution,
                "",
                "no_captured_assigned_contract_producer",
            );
        }
        for &(_, body) in &producers[start..end] {
            let source = facts.bodies[body.index()].symbol;
            if !submissions[body.index()] {
                diagnostic(
                    out,
                    facts,
                    nodes,
                    source,
                    IssueKind::UnknownExecution,
                    "",
                    "constructor_observed_submission_not_established",
                );
                continue;
            }
            out.model.edges.push(bridge(nodes, source, *callback, true));
            diagnostic(
                out,
                facts,
                nodes,
                source,
                IssueKind::UnknownExecution,
                "",
                "store_predicate_and_registration_config_require_dataflow",
            );
        }
    }
}

fn import_overlay(
    facts: &FactSnapshot,
    nodes: &[NodeId],
    json: &str,
    out: &mut RuntimeContributions,
) -> Result<(), Error> {
    let value: Value = serde_json::from_str(json)
        .map_err(|e| Error::Message(format!("runtime overlay JSON: {e}")))?;
    if value.get("schema_version").and_then(Value::as_str) != Some("compiler-runtime-bridges/v1")
        || value.get("edge_direction").and_then(Value::as_str)
            != Some("caller_or_producer_to_callee_or_callback")
    {
        return Err(Error::Invalid("runtime overlay schema or direction"));
    }
    let edges = value
        .get("edges")
        .and_then(Value::as_array)
        .ok_or(Error::Invalid("runtime overlay edges"))?;
    for edge in edges {
        if edge.get("effect").and_then(Value::as_str) != Some("execution") {
            continue;
        }
        let source = edge
            .get("from_symbol")
            .and_then(Value::as_str)
            .ok_or(Error::Invalid("runtime source endpoint"))?;
        let target = edge
            .get("to_symbol")
            .and_then(Value::as_str)
            .ok_or(Error::Invalid("runtime target endpoint"))?;
        let source = resolve(
            facts,
            source,
            edge.get("from_context").and_then(Value::as_str),
            edge.pointer("/evidence/client_definition/path")
                .and_then(Value::as_str),
        );
        let target = resolve(
            facts,
            target,
            edge.get("to_context").and_then(Value::as_str),
            edge.pointer("/evidence/concrete_definition/path")
                .and_then(Value::as_str),
        );
        match (source, target) {
            (Ok(source), Ok(target)) => {
                let guarded = edge.get("status").and_then(Value::as_str) != Some("resolved");
                out.model.edges.push(bridge(nodes, source, target, guarded));
                if guarded {
                    diagnostic(
                        out,
                        facts,
                        nodes,
                        source,
                        IssueKind::UnknownExecution,
                        "",
                        "guarded_imported_runtime_bridge",
                    );
                }
            }
            (source, target) => {
                let symbol = source
                    .as_ref()
                    .ok()
                    .copied()
                    .or_else(|| target.as_ref().ok().copied())
                    .unwrap_or(SymbolId::NONE);
                let kind = source
                    .err()
                    .or_else(|| target.err())
                    .unwrap_or(IssueKind::UnresolvedSymbol);
                diagnostic(
                    out,
                    facts,
                    nodes,
                    symbol,
                    kind,
                    "",
                    "unresolved_or_ambiguous_overlay_endpoint",
                );
            }
        }
    }
    if let Some(issues) = value.get("unresolved").and_then(Value::as_array) {
        for unresolved in issues {
            let names = unresolved.get("affected_symbols").and_then(Value::as_array);
            let mut scoped = false;
            if let Some(names) = names {
                for name in names.iter().filter_map(Value::as_str) {
                    if let Ok(symbol) = resolve(facts, name, None, None) {
                        diagnostic(
                            out,
                            facts,
                            nodes,
                            symbol,
                            IssueKind::UnknownExecution,
                            "",
                            "imported_runtime_obligation",
                        );
                        scoped = true;
                    }
                }
            }
            if !scoped {
                diagnostic(
                    out,
                    facts,
                    nodes,
                    SymbolId::NONE,
                    IssueKind::UnknownExecution,
                    "",
                    "unscoped_imported_runtime_obligation",
                );
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use selector_facts::*;
    const SCHEMA: &str = "openapi: 3.0.0\npaths:\n  /accept:\n    post:\n      tags: [wallet]\n      x-jvm-package: wallet\n      operationId: \"acceptTransferOffer\"\n";
    struct Fixture {
        builder: FactBuilder,
        file: FileId,
    }
    impl Fixture {
        fn new(path: &str) -> Self {
            let mut builder = FactBuilder::new();
            let file = Self::add_file(&mut builder, path, "project:test");
            Self { builder, file }
        }
        fn add_file(builder: &mut FactBuilder, path: &str, context: &str) -> FileId {
            let path = builder.intern(path).unwrap();
            let context = builder.intern(context).unwrap();
            let id = FileId(builder.facts.files.len() as u32);
            builder.facts.files.push(FileRecord {
                path,
                context,
                source: StrId::NONE,
                revision: StrId::NONE,
                source_hash: ContentHash::default(),
                flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
            });
            id
        }
        fn symbol(&mut self, name: &str, owner: SymbolId, kind: u32) -> SymbolId {
            let id = self.builder.ensure_symbol(name, self.file).unwrap();
            let s = &mut self.builder.facts.symbols[id.index()];
            s.owner = owner;
            s.kind = kind;
            s.file = self.file;
            s.flags = SYMBOL_DEFINED;
            id
        }
        fn body(&mut self, symbol: SymbolId, operations: &[(Opcode, SymbolId)]) {
            let id = BodyId(self.builder.facts.bodies.len() as u32);
            let start = self.builder.facts.operations.len() as u32;
            for &(opcode, target) in operations {
                self.builder.facts.operations.push(OperationRecord {
                    body: id,
                    opcode,
                    target,
                    dest: ValueId::NONE,
                    a: ValueId::NONE,
                    b: ValueId::NONE,
                    arguments: IdRange::default(),
                    span: Span { start: 1, end: 2 },
                    flags: 0,
                });
            }
            self.builder.facts.bodies.push(BodyRecord {
                symbol,
                file: self.file,
                span: Span { start: 0, end: 20 },
                name_span: Span::default(),
                operations: IdRange {
                    start,
                    len: operations.len() as u32,
                },
                parameters: IdRange::default(),
                body_hash: ContentHash::default(),
                flags: 0,
            });
        }
        fn run(&self, inputs: RuntimeInputs<'_>) -> RuntimeContributions {
            let nodes = (0..self.builder.facts.symbols.len())
                .map(|i| NodeId(i as u32))
                .collect::<Vec<_>>();
            contribute(&self.builder.facts, &nodes, &inputs).unwrap()
        }
    }
    fn http_case() -> (Fixture, SymbolId, SymbolId, SymbolId) {
        let mut f = Fixture::new("apps/wallet/target/scala-2.13/src_managed/main/Wallet.scala");
        let client_owner = f.symbol("example/http/v0/wallet/WalletClient#", SymbolId::NONE, 13);
        let handler_owner = f.symbol("example/http/v0/wallet/WalletHandler#", SymbolId::NONE, 14);
        let client = f.symbol(
            "example/http/v0/wallet/WalletClient#acceptTransferOffer().",
            client_owner,
            3,
        );
        let handler = f.symbol(
            "example/http/v0/wallet/WalletHandler#acceptTransferOffer().",
            handler_owner,
            3,
        );
        f.file = Fixture::add_file(&mut f.builder, "Server.scala", "project:test");
        let owner = f.symbol("example/HttpWalletHandler#", SymbolId::NONE, 13);
        let implementation = f.symbol("example/HttpWalletHandler#acceptTransferOffer().", owner, 3);
        f.builder.facts.relations.push(RelationRecord {
            source: implementation,
            target: handler,
            kind: RelationKind::Override,
            file: f.file,
        });
        (f, client, handler, implementation)
    }
    fn http_inputs(schema: &str) -> RuntimeInputs<'_> {
        RuntimeInputs {
            sources: vec![RuntimeSource {
                path: "wallet.yaml",
                text: schema,
            }],
            generator_packages: vec!["example.http.v0"],
            ..Default::default()
        }
    }
    #[test]
    fn openapi_joins_only_generated_compiler_declarations_and_overrides() {
        let (mut f, client, _, implementation) = http_case();
        let unrelated = f.symbol("unrelated/Noise#acceptTransferOffer().", SymbolId::NONE, 3);
        let out = f.run(http_inputs(SCHEMA));
        assert_eq!(out.model.edges.len(), 1);
        let e = out.model.edges[0];
        assert_eq!(
            (e.source, e.target),
            (NodeId(client.0), NodeId(implementation.0))
        );
        assert_ne!(e.target, NodeId(unrelated.0));
        assert!(out.diagnostics.is_empty());
    }
    #[test]
    fn all_documentation_tags_are_considered_but_mismatched_resource_pair_is_rejected() {
        let (f, _, _, _) = http_case();
        let schema = SCHEMA.replace("tags: [wallet]", "tags: [public, wallet, internal]");
        assert_eq!(f.run(http_inputs(&schema)).model.edges.len(), 1);
        let (mut f, _, handler, _) = http_case();
        let other = f.symbol("example/http/v0/wallet/OtherHandler#", SymbolId::NONE, 14);
        f.builder.facts.symbols[handler.index()].owner = other;
        let name = f
            .builder
            .intern("example/http/v0/wallet/OtherHandler#acceptTransferOffer().")
            .unwrap();
        f.builder.facts.symbols[handler.index()].name = name;
        let schema = SCHEMA.replace("tags: [wallet]", "tags: [wallet, other]");
        let out = f.run(http_inputs(&schema));
        assert!(out.model.edges.is_empty());
        assert!(!out.diagnostics.is_empty());
    }
    #[test]
    fn ambiguous_generated_overload_remains_unknown() {
        let (mut f, client, _, _) = http_case();
        let owner = f.builder.facts.symbols[client.index()].owner;
        f.file = FileId(0);
        f.symbol(
            "example/http/v0/wallet/WalletClient#acceptTransferOffer(+1).",
            owner,
            3,
        );
        let out = f.run(http_inputs(SCHEMA));
        assert!(out.model.edges.is_empty());
        assert!(!out.diagnostics.is_empty());
    }
    #[test]
    fn unsupported_yaml_and_description_injection_are_not_runtime_links() {
        let (f, _, _, _) = http_case();
        let injected = format!("{SCHEMA}components:\n  description: \"operationId: injected\"\n");
        assert_eq!(f.run(http_inputs(&injected)).model.edges.len(), 1);
        let unsupported = SCHEMA.replace("tags: [wallet]", "tags: *sharedTags");
        let out = f.run(http_inputs(&unsupported));
        assert!(out.model.edges.is_empty());
        assert!(
            out.diagnostics
                .iter()
                .any(|d| d.reason == "unsupported_openapi_metadata")
        );
    }
    #[test]
    fn build_generator_literal_controls_namespace() {
        let (f, _, _, _) = http_case();
        let out = f.run(RuntimeInputs {
            sources: vec![
                RuntimeSource {
                    path: "wallet.yaml",
                    text: SCHEMA,
                },
                RuntimeSource {
                    path: "build.sbt",
                    text: "ScalaClient(file, pkg = \"example.http.v0\")",
                },
            ],
            ..Default::default()
        });
        assert_eq!(out.model.edges.len(), 1);
    }
    fn event_case(submit: bool) -> (Fixture, SymbolId, SymbolId) {
        let mut f = Fixture::new("Trigger.scala");
        let owner = f.symbol("example/Trigger#", SymbolId::NONE, 13);
        let callback = f.symbol("example/Trigger#completeTask().", owner, 3);
        let template = f.symbol("example/Proposal#", SymbolId::NONE, 13);
        let constructor = f.symbol("example/Proposal#`<init>`().", template, 21);
        let ledger = f.symbol(LEDGER_SUBMIT_OWNER, SymbolId::NONE, 13);
        let submission = f.symbol(&format!("{LEDGER_SUBMIT_OWNER}submit()."), ledger, 3);
        let producer = f.symbol("example/Producer#make().", SymbolId::NONE, 3);
        let signature=serde_json::json!({"class_signature":{"parents":[{"type_ref":{"symbol":ASSIGNED_PROTOCOL,"type_arguments":[{"type_ref":{"symbol":"example/Companion#"}},{"type_ref":{"symbol":"example/Proposal#ContractId#"}},{"type_ref":{"symbol":"example/Proposal#"}}]}}]}}).to_string();
        let signature = f.builder.intern(&signature).unwrap();
        f.builder.facts.symbols[owner.index()].signature = signature;
        let mut operations = vec![(Opcode::Allocate, constructor)];
        if submit {
            operations.push((Opcode::Call, submission));
        }
        f.body(producer, &operations);
        (f, producer, callback)
    }
    #[test]
    fn template_creation_plus_same_executable_submission_is_guarded_delivery() {
        let (f, producer, callback) = event_case(true);
        let out = f.run(RuntimeInputs::default());
        assert_eq!(out.model.edges.len(), 1);
        let edge = out.model.edges[0];
        assert_eq!(
            (edge.source, edge.target),
            (NodeId(producer.0), NodeId(callback.0))
        );
        assert_ne!(edge.flags & EDGE_UNKNOWN, 0);
        assert!(!out.diagnostics.is_empty());
    }
    #[test]
    fn constructor_only_does_not_execute_registered_callback() {
        let (f, _, _) = event_case(false);
        let out = f.run(RuntimeInputs::default());
        assert!(out.model.edges.is_empty());
        assert!(
            out.diagnostics
                .iter()
                .any(|d| d.reason == "constructor_observed_submission_not_established")
        );
    }
    #[test]
    fn same_spelling_wrong_submission_owner_is_not_a_ledger_join() {
        let (mut f, _, _) = event_case(false);
        let owner = f.symbol("example/Database#", SymbolId::NONE, 13);
        let wrong = f.symbol("example/Database#submit().", owner, 3);
        let other = f.symbol("example/Other#run().", SymbolId::NONE, 3);
        f.body(other, &[(Opcode::Call, wrong)]);
        assert!(f.run(RuntimeInputs::default()).model.edges.is_empty());
    }
    #[test]
    fn protocol_type_alias_substitution_uses_compiler_signature() {
        let (mut f, _, _) = event_case(true);
        let owner = f.builder.facts.find_symbol("example/Trigger#").unwrap();
        let original = f
            .builder
            .facts
            .text(f.builder.facts.symbols[owner.index()].signature);
        let mut signature: Value = serde_json::from_str(original).unwrap();
        let mut upper = signature["class_signature"]["parents"][0].clone();
        upper["type_ref"]["type_arguments"][2] =
            serde_json::json!({"type_ref":{"symbol":"example/Templates.Template#[T]"}});
        let alias = f.symbol("example/Templates.Template#", SymbolId::NONE, 7);
        let alias_signature=serde_json::json!({"type_signature":{"type_parameters":{"symlinks":["example/Templates.Template#[T]"]},"upper_bound":upper}}).to_string();
        let id = f.builder.intern(&alias_signature).unwrap();
        f.builder.facts.symbols[alias.index()].signature = id;
        signature["class_signature"]["parents"][0] = serde_json::json!({"type_ref":{"symbol":"example/Templates.Template#","type_arguments":[{"type_ref":{"symbol":"example/Proposal#"}}]}});
        let id = f.builder.intern(&signature.to_string()).unwrap();
        f.builder.facts.symbols[owner.index()].signature = id;
        assert_eq!(f.run(RuntimeInputs::default()).model.edges.len(), 1);
    }
    #[test]
    fn nested_protocol_aliases_are_discovered_without_cross_context_template_join() {
        let (mut f, _, _) = event_case(true);
        let owner = f.builder.facts.find_symbol("example/Trigger#").unwrap();
        let signature: Value = serde_json::from_str(
            f.builder
                .facts
                .text(f.builder.facts.symbols[owner.index()].signature),
        )
        .unwrap();
        let inner = f.symbol("example/Inner#", SymbolId::NONE, 7);
        let outer = f.symbol("example/Outer#", SymbolId::NONE, 7);
        let first=serde_json::json!({"type_signature":{"upper_bound":signature["class_signature"]["parents"][0]}}).to_string();
        let second=serde_json::json!({"type_signature":{"upper_bound":{"type_ref":{"symbol":"example/Inner#"}}}}).to_string();
        for (symbol, text) in [(inner, first), (outer, second)] {
            let id = f.builder.intern(&text).unwrap();
            f.builder.facts.symbols[symbol.index()].signature = id;
        }
        let owner_signature=serde_json::json!({"class_signature":{"parents":[{"type_ref":{"symbol":"example/Outer#"}}]}}).to_string();
        let id = f.builder.intern(&owner_signature).unwrap();
        f.builder.facts.symbols[owner.index()].signature = id;
        assert_eq!(f.run(RuntimeInputs::default()).model.edges.len(), 1);
        let template = f.builder.facts.find_symbol("example/Proposal#").unwrap();
        let other = f.builder.intern("project:other").unwrap();
        f.builder.facts.symbols[template.index()].context = other;
        let out = f.run(RuntimeInputs::default());
        assert!(out.model.edges.is_empty());
        assert!(
            out.diagnostics
                .iter()
                .any(|diagnostic| diagnostic.reason == "unresolved_assigned_contract_template")
        );
    }
    #[test]
    fn overlay_endpoint_context_ambiguity_is_explicit() {
        let (mut f, client, _, implementation) = http_case();
        let duplicate_file = Fixture::add_file(&mut f.builder, "Other.scala", "project:other");
        f.file = duplicate_file;
        f.symbol(
            "example/http/v0/wallet/WalletClient#acceptTransferOffer().",
            SymbolId::NONE,
            3,
        );
        let value = serde_json::json!({"schema_version":"compiler-runtime-bridges/v1","edge_direction":"caller_or_producer_to_callee_or_callback","edges":[{"from_symbol":f.builder.facts.symbol_name(client),"to_symbol":f.builder.facts.symbol_name(implementation),"effect":"execution","status":"resolved"}]});
        let json = value.to_string();
        let out = f.run(RuntimeInputs {
            overlay_json: Some(&json),
            ..Default::default()
        });
        assert!(out.model.edges.is_empty());
        assert!(
            out.model
                .issues
                .iter()
                .any(|i| i.kind == IssueKind::ContextConflict)
        );
        let mut value = value;
        value["edges"][0]["from_context"] = Value::String("project:test".to_owned());
        let json = value.to_string();
        assert_eq!(
            f.run(RuntimeInputs {
                overlay_json: Some(&json),
                ..Default::default()
            })
            .model
            .edges
            .len(),
            1
        );
    }
}
