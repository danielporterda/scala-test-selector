//! Resolve consumer-context placeholders through captured ordered classpaths.
//! Provider definitions remain separate; this is reference binding, not global
//! name merging. Unknown or shadowed origins remain conservative obligations.
use crate::buffer::Buffer;
use crate::compiler_inputs::ProductInventory;
use crate::{ExtractOptions, json_error, synthetics::Synthetics};
use flate2::read::MultiGzDecoder;
use selector_facts::*;
use selector_types::*;
use serde::Deserialize;
use sha2::{Digest, Sha256};
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::Read;
use std::path::Path;

#[derive(Deserialize)]
struct Manifest {
    schema_version: String,
    revision: String,
    #[serde(default)]
    errors: Vec<serde_json::Value>,
    contexts: Vec<Context>,
}
#[derive(Deserialize)]
struct Context {
    context_id: String,
    source_revision: Option<String>,
    compiler_environment_fingerprint: String,
    #[serde(default)]
    source_records: Vec<Source>,
    #[serde(default)]
    full_classpath: Vec<Entry>,
    #[serde(default)]
    exported_products: Vec<Product>,
}
#[derive(Deserialize)]
struct Source {
    repo_relative_path: Option<String>,
    sha256: Option<String>,
}
#[derive(Deserialize)]
struct Product {
    path: String,
    sha256: Option<String>,
}
#[derive(Deserialize)]
struct Origin {
    context_id: String,
}
#[derive(Deserialize)]
struct Entry {
    index: usize,
    path: String,
    sha256: Option<String>,
    input_object: Option<String>,
    #[serde(default)]
    project_output_origins: Vec<Origin>,
}
struct BoundEntry<'a> {
    providers: Vec<StrId>,
    opaque: bool,
    inventory: Option<&'a ProductInventory>,
}
struct BoundContext<'a> {
    entries: Vec<BoundEntry<'a>>,
}

/// Positive source candidates behind an earlier project output remain possible
/// targets. A source list is not a complete class inventory: Java and generated
/// classes can shadow a later Scala definition. Keep this uncertainty in the
/// consumer recipe rather than attaching it to the shared provider definition.
#[derive(Default)]
pub(crate) struct QualifiedBindings {
    occurrences: Vec<OccurrenceRecord>,
    declaration_scopes: Vec<(FileId, SymbolId)>,
}
impl QualifiedBindings {
    pub(crate) fn attach(mut self, builder: &mut FactBuilder) -> Result<(), Error> {
        if self.occurrences.is_empty() && self.declaration_scopes.is_empty() {
            return Ok(());
        }
        // Flat per-file body postings avoid one allocation per file or reference.
        let mut offsets = vec![0usize; builder.facts.files.len() + 1];
        for body in &builder.facts.bodies {
            offsets[body.file.index() + 1] += 1;
        }
        for i in 1..offsets.len() {
            offsets[i] += offsets[i - 1];
        }
        let mut cursor = offsets[..offsets.len() - 1].to_vec();
        let mut bodies = vec![BodyId::NONE; builder.facts.bodies.len()];
        for (i, body) in builder.facts.bodies.iter().enumerate() {
            bodies[cursor[body.file.index()]] = BodyId(i as u32);
            cursor[body.file.index()] += 1;
        }
        for occurrence in self.occurrences {
            let ids =
                &bodies[offsets[occurrence.file.index()]..offsets[occurrence.file.index() + 1]];
            // The narrowest executable scope owns deferred callback references;
            // an enclosing initializer must not inherit their uncertainty.
            let owner = ids
                .iter()
                .map(|id| &builder.facts.bodies[id.index()])
                .filter(|body| body.span.contains(occurrence.span))
                .min_by_key(|body| body.span.end - body.span.start)
                .map_or(SymbolId::NONE, |body| body.symbol);
            self.declaration_scopes.push((occurrence.file, owner));
        }
        self.declaration_scopes
            .sort_unstable_by_key(|&(file, symbol)| (file.0, symbol.0));
        self.declaration_scopes.dedup();
        for (file, symbol) in self.declaration_scopes {
            builder.issue(IssueKind::ContextConflict, file, symbol,
                "possible source binding: an earlier project output lacks a hash-bound complete JVM class inventory")?;
        }
        Ok(())
    }
}

pub(crate) fn bind(
    builder: &mut FactBuilder,
    pending: Option<&mut Synthetics>,
    path: Option<&Path>,
    options: &ExtractOptions,
    identity: &mut Sha256,
) -> Result<QualifiedBindings, Error> {
    let mut definitions: HashMap<StrId, Buffer<SymbolId, 2>> = HashMap::new();
    let mut types = HashSet::new();
    let mut type_owners = HashMap::new();
    for (i, s) in builder.facts.symbols.iter().enumerate() {
        if s.kind == 11
            || s.flags & SYMBOL_DEFINED == 0
            || s.file.is_none()
            || builder.facts.files[s.file.index()].flags & SOURCE_VERIFIED == 0
        {
            continue;
        }
        let name = builder.facts.text(s.name);
        // A package can span several compiler products. SemanticDB may omit
        // its SymbolInformation, leaving kind=0 even when its package-clause
        // occurrence is a definition. Its descriptor still proves namespace
        // identity; there is no single source provider or JVM class to bind.
        // Child class/member references retain their own compiler identities
        // and still require the ordered product/shadowing proof below.
        if name.ends_with('/') || selector_types::symbol::is_local(name) || name.starts_with('@') {
            continue;
        }
        definitions
            .entry(s.name)
            .or_insert_with(Buffer::new)
            .push(SymbolId(i as u32));
        if matches!(s.kind, 10 | 12 | 13 | 14 | 18) {
            types.insert(s.name);
            type_owners
                .entry(s.name)
                .or_insert_with(|| selector_types::symbol::jvm_owner(name));
        }
    }
    let mut first_file = HashMap::new();
    for (i, f) in builder.facts.files.iter().enumerate() {
        first_file.entry(f.context).or_insert(FileId(i as u32));
    }
    // Consumer context sets are shared by all of their symbol references. Split
    // and intern once per build context, never once per graph edge/reference.
    let mut consumer_contexts = HashMap::new();
    let mut consumer_order: Vec<_> = first_file.keys().copied().collect();
    consumer_order.sort_unstable();
    for context in consumer_order {
        let text = builder.facts.text(context).to_owned();
        let mut components = Buffer::<StrId, 2>::new();
        for component in text.split('\0') {
            components.push(builder.intern(component)?);
        }
        consumer_contexts.insert(context, components);
    }
    let contexts = path
        .map(|path| load(builder, path, options, identity))
        .transpose()?;
    let mut remap: Vec<_> = (0..builder.facts.symbols.len())
        .map(|i| SymbolId(i as u32))
        .collect();
    let mut qualified = vec![false; remap.len()];
    for i in 0..remap.len() {
        let reference = builder.facts.symbols[i];
        if reference.flags & SYMBOL_DEFINED != 0 {
            continue;
        }
        let Some(candidates) = definitions.get(&reference.name) else {
            continue;
        };
        let name = builder.facts.text(reference.name);
        if selector_types::symbol::is_local(name) || name.starts_with('@') {
            continue;
        }
        let file = first_file
            .get(&reference.context)
            .copied()
            .unwrap_or(FileId::NONE);
        let Some(contexts) = &contexts else {
            builder.issue(
                IssueKind::UnresolvedSymbol,
                file,
                SymbolId(i as u32),
                "cross-context source identity requires captured ordered compiler classpaths",
            )?;
            continue;
        };
        // Shadowing is determined by the nearest source-defined enclosing type,
        // not by searching later providers for a matching method overload.
        let mut anchor = SymbolId(i as u32);
        let mut seen = 0;
        while !anchor.is_none()
            && !types.contains(&builder.facts.symbols[anchor.index()].name)
            && seen < 128
        {
            anchor = builder.facts.symbols[anchor.index()].owner;
            seen += 1;
        }
        let anchors = if anchor.is_none() {
            &**candidates
        } else {
            definitions
                .get(&builder.facts.symbols[anchor.index()].name)
                .map(|ids| &**ids)
                .unwrap_or(&**candidates)
        };
        let consumer_ids = &consumer_contexts[&reference.context];
        let mut selected = None;
        let mut bad = false;
        for &consumer in &**consumer_ids {
            let Some(context) = contexts.get(&consumer) else {
                bad = true;
                break;
            };
            let anchor_name = if anchor.is_none() {
                reference.name
            } else {
                builder.facts.symbols[anchor.index()].name
            };
            let owner = type_owners.get(&anchor_name).and_then(|o| o.as_deref());
            let candidate = resolve(&builder.facts, context, anchors, candidates, owner);
            let Some(candidate) = candidate else {
                bad = true;
                break;
            };
            if selected.is_some_and(|previous: Resolved| previous.symbol != candidate.symbol) {
                bad = true;
                break;
            }
            selected = Some(Resolved {
                symbol: candidate.symbol,
                preceding_unindexed: candidate.preceding_unindexed
                    || selected.is_some_and(|previous| previous.preceding_unindexed),
            });
        }
        if !bad {
            if let Some(target) = selected {
                remap[i] = target.symbol;
                qualified[i] = target.preceding_unindexed;
            }
        } else {
            builder.issue(IssueKind::ContextConflict, file, SymbolId(i as u32), "source reference is inaccessible, ambiguous, or shadowed by an unindexed compiler input")?;
        }
    }
    let mut qualification = QualifiedBindings::default();
    let count = builder
        .facts
        .occurrences
        .iter()
        .filter(|o| o.role != 2 && qualified[o.symbol.index()])
        .count();
    qualification.occurrences.reserve_exact(count);
    for &occurrence in &builder.facts.occurrences {
        if occurrence.role != 2 && qualified[occurrence.symbol.index()] {
            qualification.occurrences.push(occurrence);
        }
    }
    for relation in &builder.facts.relations {
        if qualified[relation.target.index()] {
            qualification
                .declaration_scopes
                .push((relation.file, remap[relation.source.index()]));
        }
    }
    for s in &mut builder.facts.symbols {
        if !s.owner.is_none() {
            s.owner = remap[s.owner.index()];
        }
    }
    for o in &mut builder.facts.occurrences {
        o.symbol = remap[o.symbol.index()];
    }
    for r in &mut builder.facts.relations {
        r.source = remap[r.source.index()];
        r.target = remap[r.target.index()];
    }
    if let Some(pending) = pending {
        for node in &mut pending.nodes {
            if !node.target.is_none() {
                node.target = remap[node.target.index()];
            }
        }
        for parameter in &mut pending.parameters {
            *parameter = remap[parameter.index()];
        }
    }
    Ok(qualification)
}

#[derive(Clone, Copy)]
struct Resolved {
    symbol: SymbolId,
    preceding_unindexed: bool,
}
fn resolve(
    facts: &FactSnapshot,
    context: &BoundContext<'_>,
    anchors: &[SymbolId],
    candidates: &[SymbolId],
    owner: Option<&str>,
) -> Option<Resolved> {
    let mut preceding_unindexed = false;
    for entry in &context.entries {
        if entry.opaque {
            return None;
        }
        let belongs = |symbol: SymbolId| {
            let context = facts.symbols[symbol.index()].context;
            if entry.providers.contains(&context) {
                return true;
            }
            let text = facts.text(context);
            text.contains('\0')
                && text.split('\0').any(|id| {
                    entry
                        .providers
                        .iter()
                        .any(|&provider| facts.text(provider) == id)
                })
        };
        if anchors.iter().copied().any(belongs) {
            let mut matches = candidates.iter().copied().filter(|&s| belongs(s));
            let first = matches.next()?;
            return matches.all(|s| s == first).then_some(Resolved {
                symbol: first,
                preceding_unindexed,
            });
        }
        match owner.and_then(|owner| entry.inventory.and_then(|p| p.contains(owner))) {
            Some(true) => return None, // A Java/uncovered class shadows the later source.
            Some(false) => (),         // Complete hash-bound inventory proves earlier absence.
            None => preceding_unindexed = true,
        }
    }
    None
}
fn load<'a>(
    builder: &mut FactBuilder,
    path: &Path,
    options: &'a ExtractOptions,
    identity: &mut Sha256,
) -> Result<HashMap<StrId, BoundContext<'a>>, Error> {
    let file = File::open(path)?;
    let reader: Box<dyn Read> = if path.extension().is_some_and(|s| s == "gz") {
        Box::new(MultiGzDecoder::new(file))
    } else {
        Box::new(file)
    };
    let limit = options.max_document_bytes as u64;
    let mut bytes = Vec::new();
    reader.take(limit + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 > limit {
        return Err(Error::Limit("compiler-context manifest bytes"));
    }
    identity.update(b"\0compiler-contexts/v1\0");
    identity.update(&bytes);
    if let Some(inputs) = &options.compiler_inputs {
        if !inputs.matches_manifest(&bytes) {
            return Err(Error::Invalid("compiler inventory capture identity"));
        }
        identity.update(b"\0verified-product-inventories\0");
        identity.update(inputs.identity.0);
    }
    let manifest: Manifest = serde_json::from_slice(&bytes).map_err(json_error)?;
    if manifest.schema_version != "sbt-compiler-context/v1" {
        return Err(Error::Invalid("compiler-context manifest schema"));
    }
    if manifest.revision != builder.facts.text(builder.facts.revision) {
        return Err(Error::Invalid("compiler-context manifest revision"));
    }
    if !manifest.errors.is_empty() {
        return Err(Error::Invalid("compiler-context capture errors"));
    }
    let mut contexts = HashMap::new();
    let mut source_hashes = HashMap::new();
    let mut products = HashMap::new();
    let mut context_ids = HashMap::new();
    for context in &manifest.contexts {
        if context.source_revision.as_deref() != Some(manifest.revision.as_str()) {
            return Err(Error::Invalid("compiler context source revision"));
        }
        ContentHash::from_hex(&context.compiler_environment_fingerprint)?;
        let context_id = builder.intern(&context.context_id)?;
        if contexts
            .insert(
                context_id,
                BoundContext {
                    entries: Vec::new(),
                },
            )
            .is_some()
        {
            return Err(Error::Invalid("duplicate compiler context"));
        }
        context_ids.insert(context.context_id.as_str(), context_id);
    }
    // This lookup borrows already admitted paths. Manifest-only Java/unselected
    // paths must not bloat the persistent string pool simply to validate Scala.
    let file_paths: HashMap<_, _> = builder
        .facts
        .files
        .iter()
        .map(|f| (builder.facts.text(f.path), f.path))
        .collect();
    for context in &manifest.contexts {
        let context_id = context_ids[context.context_id.as_str()];
        for source in &context.source_records {
            if let (Some(path), Some(hash)) = (&source.repo_relative_path, &source.sha256) {
                if let Some(&path_id) = file_paths.get(path.as_str()) {
                    let hash = ContentHash::from_hex(hash)?;
                    if source_hashes
                        .insert((context_id, path_id), hash)
                        .is_some_and(|previous| previous != hash)
                    {
                        return Err(Error::Invalid("conflicting compiler source hashes"));
                    }
                }
            }
        }
        for product in &context.exported_products {
            if let Some(hash) = &product.sha256 {
                let hash = ContentHash::from_hex(hash)?;
                if products
                    .insert((context_id, product.path.as_str()), hash)
                    .is_some_and(|previous| previous != hash)
                {
                    return Err(Error::Invalid("conflicting compiler product hashes"));
                }
            }
        }
    }
    for file in &builder.facts.files {
        if file.flags & SOURCE_VERIFIED == 0 {
            continue;
        }
        for context in builder.facts.text(file.context).split('\0') {
            let context_id = context_ids.get(context).copied();
            if context_id.and_then(|id| source_hashes.get(&(id, file.path)))
                != Some(&file.source_hash)
            {
                return Err(Error::Invalid(
                    "source hash is absent or stale in its compiler context",
                ));
            }
        }
    }
    for context in &manifest.contexts {
        let mut entries = Vec::with_capacity(context.full_classpath.len());
        for (index, entry) in context.full_classpath.iter().enumerate() {
            if entry.index != index {
                return Err(Error::Invalid("compiler classpath order"));
            }
            let hash = entry
                .sha256
                .as_deref()
                .map(ContentHash::from_hex)
                .transpose()?;
            let mut providers = Vec::new();
            let mut opaque = entry.project_output_origins.is_empty() || hash.is_none();
            for origin in &entry.project_output_origins {
                let provider = context_ids
                    .get(origin.context_id.as_str())
                    .copied()
                    .unwrap_or(StrId::NONE);
                if !contexts.contains_key(&provider)
                    || products.get(&(provider, entry.path.as_str())) != hash.as_ref()
                {
                    opaque = true;
                }
                providers.push(provider);
            }
            let inventory = hash.and_then(|hash| {
                options.compiler_inputs.as_ref().and_then(|inputs| {
                    inputs.product(entry.input_object.as_deref().unwrap_or(&entry.path), hash)
                })
            });
            entries.push(BoundEntry {
                providers,
                opaque,
                inventory,
            });
        }
        let id = context_ids[context.context_id.as_str()];
        contexts.get_mut(&id).unwrap().entries = entries;
    }
    Ok(contexts)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    struct Fixture {
        builder: FactBuilder,
        files: Vec<FileId>,
    }
    impl Fixture {
        fn new(contexts: &[&str]) -> Self {
            let mut builder = FactBuilder::new();
            builder.facts.revision = builder.intern("r").unwrap();
            let mut files = Vec::new();
            for &context in contexts {
                let file = FileId(builder.facts.files.len() as u32);
                let path = builder.intern(&format!("{context}.scala")).unwrap();
                let source = builder.intern("x").unwrap();
                let context = builder.intern(context).unwrap();
                builder.facts.files.push(FileRecord {
                    path,
                    source,
                    revision: builder.facts.revision,
                    context,
                    source_hash: crate::sha(b"x"),
                    flags: SOURCE_VERIFIED,
                });
                files.push(file);
            }
            Self { builder, files }
        }
        fn definition(&mut self, name: &str, file: usize, kind: u32) -> SymbolId {
            let id = self.builder.ensure_symbol(name, self.files[file]).unwrap();
            let record = &mut self.builder.facts.symbols[id.index()];
            record.kind = kind;
            record.file = self.files[file];
            record.flags |= SYMBOL_DEFINED;
            record.span = Span { start: 0, end: 1 };
            id
        }
        fn reference(&mut self, name: &str, file: usize) -> SymbolId {
            let id = self.builder.ensure_symbol(name, self.files[file]).unwrap();
            self.builder.facts.occurrences.push(OccurrenceRecord {
                file: self.files[file],
                symbol: id,
                span: Span { start: 0, end: 1 },
                role: 1,
                ordinal: 0,
            });
            id
        }
        fn manifest(&self, orders: &[&[&str]]) -> serde_json::Value {
            let hash = crate::sha(b"product").to_string();
            let contexts:Vec<_>=self.files.iter().enumerate().map(|(i,&file)|{
                let name=self.builder.facts.text(self.builder.facts.files[file.index()].context);
                let entries:Vec<_>=orders[i].iter().enumerate().map(|(index,&origin)|{
                    if origin=="opaque" {json!({"index":index,"path":"/opaque.jar","sha256":hash})}
                    else {json!({"index":index,"path":format!("/{origin}"),"sha256":hash,
                        "project_output_origins":[{"context_id":origin}]})}
                }).collect();
                json!({"context_id":name,"source_revision":"r","compiler_environment_fingerprint":ContentHash([1;32]).to_string(),
                    "source_records":[{"repo_relative_path":format!("{name}.scala"),"sha256":self.builder.facts.files[file.index()].source_hash.to_string()}],
                    "exported_products":[{"path":format!("/{name}"),"sha256":hash}],"full_classpath":entries})
            }).collect();
            json!({"schema_version":"sbt-compiler-context/v1","revision":"r","errors":[],"contexts":contexts})
        }
        fn bind(&mut self, manifest: serde_json::Value) -> Result<(), Error> {
            self.bind_options(manifest, &ExtractOptions::default())
        }
        fn bind_options(
            &mut self,
            manifest: serde_json::Value,
            options: &ExtractOptions,
        ) -> Result<(), Error> {
            let directory = tempfile::tempdir().unwrap();
            let path = directory.path().join("contexts.json");
            std::fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
            let qualification = super::bind(
                &mut self.builder,
                None,
                Some(&path),
                options,
                &mut Sha256::new(),
            )?;
            qualification.attach(&mut self.builder)
        }
    }
    #[test]
    fn ordered_explicit_origins_bind_references_without_merging_provider_definitions() {
        let mut f = Fixture::new(&["a", "b", "c", "d"]);
        let b = f.definition("p/C#", 1, 13);
        let c = f.definition("p/C#", 2, 13);
        f.reference("p/C#", 0);
        f.reference("p/C#", 3);
        let manifest = f.manifest(&[&["a", "b", "c"], &["b"], &["c"], &["d", "c", "b"]]);
        f.bind(manifest).unwrap();
        assert_eq!(f.builder.facts.occurrences[0].symbol, b);
        assert_eq!(f.builder.facts.occurrences[1].symbol, c);
        assert_ne!(b, c);
        assert_eq!(f.builder.facts.symbols[b.index()].file, f.files[1]);
        assert_eq!(f.builder.facts.symbols[c.index()].file, f.files[2]);
        assert!(
            f.builder
                .facts
                .issues
                .iter()
                .any(|issue| issue.file == f.files[0] && issue.kind == IssueKind::ContextConflict)
        );
    }
    #[test]
    fn earlier_project_inventory_gap_guards_only_the_owning_deferred_body() {
        let mut f = Fixture::new(&["a", "b"]);
        let source = " ".repeat(100);
        f.builder.facts.files[0].source = f.builder.intern(&source).unwrap();
        f.builder.facts.files[0].source_hash = crate::sha(source.as_bytes());
        let provider = f.definition("p/C#", 1, 13);
        let outer = f.definition("p/A#factory().", 0, 3);
        let closure = f.definition("@closure:p/A#factory().:0", 0, 3);
        let dormant = f.definition("p/A#dormant().", 0, 3);
        f.reference("p/C#", 0);
        f.builder.facts.occurrences[0].span = Span { start: 25, end: 26 };
        for (symbol, span, flags) in [
            (outer, Span { start: 0, end: 100 }, 0),
            (closure, Span { start: 20, end: 40 }, BODY_DEFERRED),
            (dormant, Span { start: 50, end: 80 }, 0),
        ] {
            f.builder.facts.bodies.push(BodyRecord {
                symbol,
                file: f.files[0],
                span,
                name_span: Span::default(),
                operations: IdRange::default(),
                parameters: IdRange::default(),
                body_hash: ContentHash::default(),
                flags,
            });
        }
        // /a is a valid project product with a valid source inventory. That
        // still cannot prove an absent Java/generated p.C class in /a.
        let manifest = f.manifest(&[&["a", "b"], &["b"]]);
        f.bind(manifest).unwrap();
        assert_eq!(f.builder.facts.occurrences[0].symbol, provider);
        let issues: Vec<_> = f
            .builder
            .facts
            .issues
            .iter()
            .filter(|i| i.kind == IssueKind::ContextConflict)
            .collect();
        assert_eq!(issues.len(), 1);
        assert_eq!(issues[0].symbol, closure);
        assert_eq!(issues[0].file, f.files[0]);
        assert!(
            f.builder
                .facts
                .text(issues[0].detail)
                .contains("complete JVM class inventory")
        );
    }
    #[test]
    fn first_classpath_product_candidate_needs_no_absence_proof() {
        let mut f = Fixture::new(&["a", "b"]);
        let provider = f.definition("p/C#", 1, 13);
        f.reference("p/C#", 0);
        let manifest = f.manifest(&[&["b", "a"], &["b"]]);
        f.bind(manifest).unwrap();
        assert_eq!(f.builder.facts.occurrences[0].symbol, provider);
        assert!(f.builder.facts.issues.is_empty());
    }
    #[test]
    fn compiler_package_definition_without_symbol_information_is_not_a_source_provider() {
        let mut f = Fixture::new(&["consumer", "provider"]);
        let package = f.definition("org/lfdecentralizedtrust/splice/environment/", 1, 0);
        let package_ref = f.reference("org/lfdecentralizedtrust/splice/environment/", 0);
        let class = f.definition(
            "org/lfdecentralizedtrust/splice/environment/RetryFor.",
            1,
            10,
        );
        let class_ref = f.reference("org/lfdecentralizedtrust/splice/environment/RetryFor.", 0);
        f.builder.facts.symbols[class.index()].owner = package;
        f.builder.facts.symbols[class_ref.index()].owner = package_ref;
        let manifest = f.manifest(&[&["consumer", "provider"], &["provider"]]);
        f.bind(manifest).unwrap();
        assert_eq!(f.builder.facts.occurrences[0].symbol, package_ref);
        assert_ne!(package_ref, package);
        assert_eq!(f.builder.facts.occurrences[1].symbol, class);
        let issues: Vec<_> = f
            .builder
            .facts
            .issues
            .iter()
            .filter(|issue| issue.kind == IssueKind::ContextConflict)
            .collect();
        assert_eq!(issues.len(), 1);
        assert!(issues[0].symbol.is_none());
        // The class still carries the real earlier-product inventory gap.
        // An otherwise identical package-only import must carry none.
        f.builder.facts.occurrences.pop();
        f.builder.facts.issues.clear();
        let manifest = f.manifest(&[&["consumer", "provider"], &["provider"]]);
        f.bind(manifest).unwrap();
        assert!(f.builder.facts.issues.is_empty());
    }
    #[test]
    fn complete_earlier_product_inventory_proves_absence_or_blocks_a_java_shadow() {
        for shadow in [false, true] {
            let mut f = Fixture::new(&["a", "b"]);
            let provider = f.definition("p/C#", 1, 13);
            let reference = f.reference("p/C#", 0);
            let mut manifest = f.manifest(&[&["a", "b"], &["b"]]);
            let directory = tempfile::tempdir().unwrap();
            let captured = directory.path().join("contexts.json");
            let (kind, hash, files, bytes) = if shadow {
                std::fs::create_dir_all(directory.path().join("a/p")).unwrap();
                std::fs::write(directory.path().join("a/p/C.class"), b"java").unwrap();
                let inventory = format!(
                    "[{{\"bytes\":4,\"path\":\"p/C.class\",\"sha256\":\"{}\"}}]",
                    crate::sha(b"java")
                );
                ("directory", crate::sha(inventory.as_bytes()), Some(1), 4)
            } else {
                (
                    "absent_empty_project_output",
                    crate::sha(b"{\"kind\":\"absent_empty_project_output\"}"),
                    None,
                    0,
                )
            };
            manifest["source_root"] = json!("/");
            manifest["contexts"][0]["exported_products"][0]["sha256"] = json!(hash.to_string());
            manifest["contexts"][0]["full_classpath"][0]["sha256"] = json!(hash.to_string());
            manifest["input_objects"] = json!([
                {"path":"/a","kind":kind,"sha256":hash.to_string(),"files":files,"bytes":bytes},
                {"path":"/b","kind":"directory","sha256":crate::sha(b"product").to_string(),"files":1,"bytes":1}
            ]);
            std::fs::write(&captured, serde_json::to_vec(&manifest).unwrap()).unwrap();
            let inventory =
                crate::compiler_inputs::admit(&captured, directory.path(), &Default::default())
                    .unwrap();
            f.bind_options(
                manifest,
                &ExtractOptions {
                    compiler_inputs: Some(std::sync::Arc::new(inventory)),
                    ..Default::default()
                },
            )
            .unwrap();
            if shadow {
                assert_eq!(f.builder.facts.occurrences[0].symbol, reference);
                assert!(
                    f.builder
                        .facts
                        .issues
                        .iter()
                        .any(|i| i.kind == IssueKind::ContextConflict)
                );
            } else {
                assert_eq!(f.builder.facts.occurrences[0].symbol, provider);
                assert!(
                    f.builder.facts.issues.is_empty(),
                    "exact empty inventory proves earlier absence"
                );
            }
        }
    }
    #[test]
    fn opaque_earlier_binary_and_absent_origin_preserve_unknown_identity() {
        for order in [&["a", "opaque", "b"][..], &["a"][..]] {
            let mut f = Fixture::new(&["a", "b"]);
            f.definition("p/C#", 1, 13);
            let reference = f.reference("p/C#", 0);
            let manifest = f.manifest(&[order, &["b"]]);
            f.bind(manifest).unwrap();
            assert_eq!(f.builder.facts.occurrences[0].symbol, reference);
            assert!(
                f.builder
                    .facts
                    .issues
                    .iter()
                    .any(|i| i.symbol == reference && i.kind == IssueKind::ContextConflict)
            );
        }
    }
    #[test]
    fn earlier_class_shadows_later_overload_and_stale_manifest_is_rejected() {
        let mut f = Fixture::new(&["a", "b", "c"]);
        f.definition("p/C#", 1, 13);
        let c = f.definition("p/C#", 2, 13);
        let method = f.definition("p/C#f(+2).", 2, 3);
        f.builder.facts.symbols[method.index()].owner = c;
        let class_ref = f.builder.ensure_symbol("p/C#", f.files[0]).unwrap();
        let reference = f.reference("p/C#f(+2).", 0);
        f.builder.facts.symbols[reference.index()].owner = class_ref;
        let manifest = f.manifest(&[&["a", "b", "c"], &["b"], &["c"]]);
        f.bind(manifest).unwrap();
        assert_eq!(f.builder.facts.occurrences[0].symbol, reference);
        let mut stale = f.manifest(&[&["a", "c"], &["b"], &["c"]]);
        stale["contexts"][0]["source_records"][0]["sha256"] =
            json!(ContentHash([8; 32]).to_string());
        assert!(f.bind(stale).is_err());
    }
}
