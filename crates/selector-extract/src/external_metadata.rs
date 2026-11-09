//! Optional compiler metadata for exact external method identities. Provider
//! proofs authorize signatures only; they never authorize executable effects.
use crate::{callable, from_json, json_error, semantic_wire, sha, signature, synthetics};
use selector_facts::*;
use selector_types::*;
use serde::{Deserialize, Serialize};
use serde_json::value::RawValue;
use sha2::{Digest, Sha256};
use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::sync::Arc;

pub const MANIFEST_SCHEMA: &str = "compiler-external-metadata/v1";

/// Implementations must resolve the first hash-admitted provider in captured
/// order. An unavailable preceding entry must not permit a later provider.
/// Context is one exact compiler context, never a representative of a composite.
pub trait MetadataProviderAuthority: Send + Sync {
    fn identity(&self) -> ContentHash;
    /// SHA256 of the original physical compiler-contexts input, including gzip.
    fn contexts_identity(&self) -> ContentHash;
    fn resolve(
        &self,
        context: &str,
        outer_class: &str,
    ) -> Result<Option<ProviderResolution>, Error>;
}
pub struct ProviderResolution {
    pub classpath_identity: ContentHash,
    pub provider_index: u32,
    pub provider_sha256: ContentHash,
    /// Immutable admitted bytes; admission recomputes their class digest.
    pub class_bytes: Arc<[u8]>,
}
#[derive(Clone, Debug)]
pub struct MetadataRequestLimits {
    pub max_requests: usize,
    pub max_name_bytes: usize,
}
impl Default for MetadataRequestLimits {
    fn default() -> Self {
        Self {
            max_requests: 200_000,
            max_name_bytes: 32 * 1024 * 1024,
        }
    }
}
#[derive(Clone, Copy, Debug)]
pub struct MetadataRequest<'a> {
    pub context: &'a str,
    pub symbol: &'a str,
}
/// One numeric ID per requested method or candidate module term. Names borrow the pool.
/// A candidate term grants no module authority until an OBJECT header is admitted.
pub struct MetadataRequests<'a> {
    facts: &'a FactSnapshot,
    symbols: Vec<SymbolId>,
    identity: ContentHash,
    capture_identity: ContentHash,
    contexts_identity: Option<ContentHash>,
}
impl MetadataRequests<'_> {
    pub fn len(&self) -> usize {
        self.symbols.len()
    }
    pub fn is_empty(&self) -> bool {
        self.symbols.is_empty()
    }
    pub fn identity(&self) -> ContentHash {
        self.identity
    }
    pub fn contexts_identity(&self) -> Option<ContentHash> {
        self.contexts_identity
    }
    pub fn iter(&self) -> impl ExactSizeIterator<Item = MetadataRequest<'_>> + '_ {
        self.symbols.iter().map(|&id| {
            let record = self.facts.symbols[id.index()];
            MetadataRequest {
                context: self.facts.text(record.context),
                symbol: self.facts.text(record.name),
            }
        })
    }
    fn contains(&self, context: &str, symbol: &str) -> bool {
        self.symbols
            .binary_search_by(|&id| {
                let record = self.facts.symbols[id.index()];
                (
                    self.facts.text(record.context),
                    self.facts.text(record.name),
                )
                    .cmp(&(context, symbol))
            })
            .is_ok()
    }
}
fn hash_text(hash: &mut Sha256, value: &str) {
    hash.update((value.len() as u64).to_le_bytes());
    hash.update(value.as_bytes());
}
fn method_name(name: &str) -> bool {
    !name.starts_with('@')
        && name.ends_with(").")
        && selector_types::symbol::global_owner(name).is_some()
}
fn module_name(name: &str) -> bool {
    let mut quoted = false;
    for byte in name.bytes() {
        if byte == b'`' {
            quoted = !quoted;
        } else if !quoted && matches!(byte, b'(' | b')' | b'[' | b']') {
            return false;
        }
    }
    !name.starts_with('@')
        && !name.starts_with("_root_/")
        && !name.starts_with("_empty_/")
        && name.ends_with('.')
        && !name.ends_with(").")
        && selector_types::symbol::global_owner(name).is_some()
}
pub(crate) fn requests<'a>(
    builder: &'a FactBuilder,
    _pending: Option<&synthetics::Synthetics>,
    limits: &MetadataRequestLimits,
    capture_identity: ContentHash,
    contexts_identity: Option<ContentHash>,
) -> Result<MetadataRequests<'a>, Error> {
    let facts = &builder.facts;
    let mut symbols = Vec::new();
    let mut bytes = 0usize;
    for (index, record) in facts.symbols.iter().enumerate() {
        let name = facts.text(record.name);
        if record.flags & SYMBOL_DEFINED != 0 || record.context.is_none() {
            continue;
        }
        let missing = if module_name(name) && matches!(record.kind, 0 | 10) {
            record.kind == 0
        } else if !method_name(name) {
            false
        } else if record.signature.is_none() {
            true
        } else {
            let metadata = callable::project(facts.text(record.signature))?;
            !metadata.shape.known_method
                || metadata.parameters.iter().any(|parameter| {
                    builder
                        .lookup_global_symbol(&parameter.0, record.context)
                        .is_none_or(|id| {
                            let p = facts.symbols[id.index()];
                            p.kind != 8
                                || p.owner != SymbolId(index as u32)
                                || p.signature.is_none()
                        })
                })
        };
        if !missing {
            continue;
        }
        if symbols.len() >= limits.max_requests {
            return Err(Error::Limit("external metadata requests"));
        }
        bytes = bytes
            .checked_add(name.len())
            .and_then(|n| n.checked_add(facts.text(record.context).len()))
            .ok_or(Error::Limit("external metadata request bytes"))?;
        if bytes > limits.max_name_bytes {
            return Err(Error::Limit("external metadata request bytes"));
        }
        symbols.push(SymbolId::checked(index)?);
    }
    symbols.sort_unstable_by(|&a, &b| {
        let a = facts.symbols[a.index()];
        let b = facts.symbols[b.index()];
        (facts.text(a.context), facts.text(a.name))
            .cmp(&(facts.text(b.context), facts.text(b.name)))
    });
    let mut identity = Sha256::new();
    identity.update(b"external-method-and-module-requests/v2\0");
    identity.update(capture_identity.0);
    if let Some(contexts) = contexts_identity {
        identity.update(contexts.0);
    }
    for &id in &symbols {
        let record = facts.symbols[id.index()];
        hash_text(&mut identity, facts.text(record.context));
        hash_text(&mut identity, facts.text(record.name));
    }
    Ok(MetadataRequests {
        facts,
        symbols,
        identity: ContentHash(identity.finalize().into()),
        capture_identity,
        contexts_identity,
    })
}

#[derive(Clone, Debug)]
pub struct ExternalMetadataLimits {
    pub max_manifest_bytes: usize,
    pub max_payload_bytes: usize,
    pub max_total_payload_bytes: usize,
    pub max_json_bytes: usize,
    /// Sum of unique retained decoded signature tables; decoder scratch has its own caps.
    pub max_decoded_bytes: usize,
    pub max_provider_class_bytes: usize,
    pub max_symbols: usize,
    pub max_signature_bytes: usize,
    pub max_depth: usize,
    pub max_fields: u64,
}
impl Default for ExternalMetadataLimits {
    fn default() -> Self {
        Self {
            max_manifest_bytes: 8 * 1024 * 1024,
            max_payload_bytes: 16 * 1024 * 1024,
            max_total_payload_bytes: 64 * 1024 * 1024,
            max_json_bytes: 64 * 1024 * 1024,
            max_decoded_bytes: 128 * 1024 * 1024,
            max_provider_class_bytes: 16 * 1024 * 1024,
            max_symbols: 200_000,
            max_signature_bytes: 1024 * 1024,
            max_depth: 128,
            max_fields: 4_000_000,
        }
    }
}
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExternalMetadataManifest {
    pub schema: String,
    pub producer_sha256: String,
    pub authority_sha256: String,
    pub contexts_sha256: String,
    pub payloads: Vec<MetadataPayload>,
    pub bindings: Vec<MetadataBinding>,
    /// Separate header-only authority. Method payloads remain signature-only.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub module_headers: Vec<MetadataBinding>,
}
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MetadataPayload {
    pub path: PathBuf,
    pub sha256: String,
}
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MetadataBinding {
    /// Exact normalized source context key. Composite keys contain NUL separators.
    pub context: String,
    pub roots: Vec<String>,
    pub projections: Vec<MetadataProjection>,
}
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MetadataProjection {
    pub context: String,
    pub payload: u32,
    /// JVM internal class identity, without a .class suffix.
    pub outer_class: String,
    pub outer_class_sha256: String,
    pub classpath_sha256: String,
    pub provider_index: u32,
    pub provider_sha256: String,
}
/// Immutable pooled metadata. Publication retains compiler declarations but
/// deliberately grants no source/native execution authority.
pub struct AdmittedExternalMetadata {
    facts: FactSnapshot,
    roots: Vec<SymbolId>,
    identity: ContentHash,
    capture_identity: ContentHash,
    contexts_identity: ContentHash,
}
impl AdmittedExternalMetadata {
    pub fn identity(&self) -> ContentHash {
        self.identity
    }
    pub fn methods(&self) -> usize {
        self.roots
            .iter()
            .filter(|id| self.facts.symbols[id.index()].kind != 10)
            .count()
    }
    pub(crate) fn validate_scope(
        &self,
        capture: ContentHash,
        contexts: Option<ContentHash>,
    ) -> Result<(), Error> {
        if self.capture_identity != capture || contexts != Some(self.contexts_identity) {
            return Err(Error::Invalid(
                "external metadata belongs to another compiler capture",
            ));
        }
        Ok(())
    }
    pub(crate) fn publish(&self, builder: &mut FactBuilder) -> Result<(), Error> {
        for &root in &self.roots {
            let record = self.facts.symbols[root.index()];
            let context = builder.intern(self.facts.text(record.context))?;
            if builder
                .lookup_global_symbol(self.facts.text(record.name), context)
                .is_none()
            {
                return Err(Error::Invalid(
                    "external metadata root absent from compiler capture",
                ));
            }
        }
        let mut symbols = Vec::with_capacity(self.facts.symbols.len());
        for record in &self.facts.symbols {
            let context = builder.intern(self.facts.text(record.context))?;
            symbols.push(builder.ensure_global_symbol(self.facts.text(record.name), context)?);
        }
        let mut is_root = vec![false; symbols.len()];
        for &root in &self.roots {
            is_root[root.index()] = true;
        }
        let mut owners = vec![SymbolId::NONE; symbols.len()];
        let mut usable = vec![true; symbols.len()];
        // Decide the entire method/formal contract before publishing any part.
        // A conflicting formal must not leave an apparently complete new method.
        for (index, external) in self.facts.symbols.iter().enumerate() {
            if external.kind == 0 {
                continue;
            }
            let mut root = SymbolId(index as u32);
            let mut depth = 0;
            while !root.is_none() && !is_root[root.index()] && depth < 128 {
                root = self.facts.symbols[root.index()].owner;
                depth += 1;
            }
            if root.is_none() || depth == 128 {
                return Err(Error::Invalid(
                    "external declaration outside requested method",
                ));
            }
            owners[index] = root;
            let previous = builder.facts.symbols[symbols[index].index()];
            let header = external.kind == 10;
            let conflict = previous.kind != 0
                && (previous.kind != external.kind
                    || (!header && previous.properties != external.properties)
                    || (!header
                        && !previous.signature.is_none()
                        && builder.facts.text(previous.signature)
                            != self.facts.text(external.signature)));
            if conflict {
                let root_id = symbols[root.index()];
                let file = builder.facts.symbols[root_id.index()].file;
                if usable[root.index()] {
                    builder.issue(
                        IssueKind::ContextConflict,
                        file,
                        root_id,
                        "admitted external metadata conflicts with existing compiler information",
                    )?;
                }
                usable[root.index()] = false;
            }
            if previous.flags & SYMBOL_DEFINED != 0 || (header && previous.kind == 10) {
                usable[root.index()] = false;
            }
        }
        let mut published = vec![false; symbols.len()];
        for (index, external) in self.facts.symbols.iter().enumerate() {
            let root = owners[index];
            if root.is_none() || !usable[root.index()] {
                continue;
            }
            let display = builder.intern(self.facts.text(external.display))?;
            let signature = if external.signature.is_none() {
                StrId::NONE
            } else {
                builder.intern(self.facts.text(external.signature))?
            };
            let owner = if external.owner.is_none() {
                SymbolId::NONE
            } else {
                symbols[external.owner.index()]
            };
            let record = &mut builder.facts.symbols[symbols[index].index()];
            record.display = display;
            record.signature = signature;
            record.kind = external.kind;
            record.properties = external.properties;
            record.owner = owner;
            published[index] = true;
        }
        for relation in &self.facts.relations {
            let relevant = match relation.kind {
                RelationKind::Member => published[relation.target.index()],
                RelationKind::Signature => published[relation.source.index()],
                _ => return Err(Error::Invalid("external metadata executable relation")),
            };
            if relevant {
                builder.facts.relations.push(RelationRecord {
                    source: symbols[relation.source.index()],
                    target: symbols[relation.target.index()],
                    kind: relation.kind,
                    file: FileId::NONE,
                });
            }
        }
        Ok(())
    }
}

#[derive(Deserialize)]
struct Documents<'a> {
    #[serde(borrow)]
    documents: Vec<Document<'a>>,
}
#[derive(Deserialize)]
struct Document<'a> {
    #[serde(borrow)]
    uri: Cow<'a, str>,
    schema: u32,
    language: u32,
    #[serde(default, borrow)]
    symbols: Vec<Information<'a>>,
    #[serde(default, borrow)]
    occurrences: Vec<&'a RawValue>,
    #[serde(default, borrow)]
    synthetics: Vec<&'a RawValue>,
    #[serde(default, borrow)]
    diagnostics: Vec<&'a RawValue>,
    #[serde(default, borrow)]
    text: Cow<'a, str>,
}
#[derive(Deserialize)]
struct Information<'a> {
    #[serde(borrow)]
    symbol: Cow<'a, str>,
    #[serde(default, borrow)]
    display_name: Cow<'a, str>,
    kind: u32,
    language: u32,
    #[serde(default)]
    properties: u64,
    #[serde(default, borrow)]
    signature: Option<&'a RawValue>,
    #[serde(default, borrow)]
    overridden_symbols: Vec<Cow<'a, str>>,
}

#[derive(Deserialize)]
struct SignatureForm<'a> {
    #[serde(default, borrow)]
    method_signature: Option<&'a RawValue>,
    #[serde(default, borrow)]
    value_signature: Option<&'a RawValue>,
    #[serde(default, borrow)]
    type_signature: Option<&'a RawValue>,
}
#[derive(Deserialize)]
struct TypedValue<'a> {
    #[serde(borrow)]
    tpe: &'a RawValue,
}
#[derive(Deserialize)]
struct MethodResult<'a> {
    #[serde(borrow)]
    return_type: &'a RawValue,
}
fn signature_form(info: &Information<'_>) -> Result<(), Error> {
    let form: SignatureForm<'_> = from_json(
        info.signature
            .ok_or(Error::Invalid("external signature absent"))?
            .get(),
    )?;
    let present = usize::from(form.method_signature.is_some())
        + usize::from(form.value_signature.is_some())
        + usize::from(form.type_signature.is_some());
    if present != 1 {
        return Err(Error::Invalid("external signature form"));
    }
    match info.kind {
        3 | 21 => {
            let method: MethodResult<'_> = from_json(
                form.method_signature
                    .ok_or(Error::Invalid("external method signature form"))?
                    .get(),
            )?;
            if method.return_type.get() == "{}" {
                return Err(Error::Invalid("external method result type absent"));
            }
        }
        8 => {
            let value: TypedValue<'_> = from_json(
                form.value_signature
                    .ok_or(Error::Invalid("external parameter signature form"))?
                    .get(),
            )?;
            if value.tpe.get() == "{}" {
                return Err(Error::Invalid("external parameter type absent"));
            }
        }
        9 if form.type_signature.is_some() => (),
        _ => return Err(Error::Invalid("external signature declaration form")),
    }
    Ok(())
}

struct DecodedPayload {
    facts: FactSnapshot,
    declared: HashSet<SymbolId>,
    by_name: Vec<SymbolId>,
    origins: Vec<StrId>,
}
struct BoundedJson {
    bytes: Vec<u8>,
    maximum: usize,
}
impl Write for BoundedJson {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        if self
            .bytes
            .len()
            .checked_add(bytes.len())
            .is_none_or(|n| n > self.maximum)
        {
            return Err(std::io::Error::other("external metadata JSON byte limit"));
        }
        let required = self.bytes.len() + bytes.len();
        if required > self.bytes.capacity() {
            let capacity = required
                .max(self.bytes.capacity().saturating_mul(2))
                .min(self.maximum);
            self.bytes
                .try_reserve_exact(capacity - self.bytes.len())
                .map_err(|_| std::io::Error::other("external metadata JSON allocation"))?;
        }
        self.bytes.extend_from_slice(bytes);
        Ok(bytes.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}
fn read_bounded(path: &Path, maximum: usize) -> Result<Vec<u8>, Error> {
    let mut file = File::open(path)?;
    let length = usize::try_from(file.metadata()?.len())
        .map_err(|_| Error::Limit("external metadata bytes"))?;
    if length > maximum {
        return Err(Error::Limit("external metadata bytes"));
    }
    let mut bytes = Vec::new();
    bytes
        .try_reserve_exact(length)
        .map_err(|_| Error::Limit("external metadata allocation"))?;
    bytes.resize(length, 0);
    file.read_exact(&mut bytes)?;
    if file.read(&mut [0])? != 0 {
        return Err(Error::Invalid("external metadata grew during admission"));
    }
    Ok(bytes)
}
fn check_symbols(builder: &FactBuilder, limits: &ExternalMetadataLimits) -> Result<(), Error> {
    if builder.facts.symbols.len() > limits.max_symbols {
        Err(Error::Limit("external metadata symbols"))
    } else if builder.facts.owned_bytes() > limits.max_decoded_bytes {
        Err(Error::Limit("external metadata decoded bytes"))
    } else {
        Ok(())
    }
}
fn global(builder: &mut FactBuilder, name: &str, context: StrId) -> Result<SymbolId, Error> {
    if name.is_empty()
        || name.starts_with('@')
        || selector_types::symbol::is_local(name)
        || selector_types::symbol::global_owner(name).is_none() && !name.ends_with('/')
    {
        return Err(Error::Invalid("external metadata global identity"));
    }
    let id = builder.ensure_global_symbol(name, context)?;
    if let Some(owner) = selector_types::symbol::global_owner(name) {
        let owner = builder.ensure_global_symbol(owner, context)?;
        if builder.facts.symbols[id.index()].owner.is_none() {
            builder.facts.symbols[id.index()].owner = owner;
        }
    }
    Ok(id)
}
#[cfg(test)]
fn decode_payload(raw: &[u8], limits: &ExternalMetadataLimits) -> Result<DecodedPayload, Error> {
    decode_payload_scoped(raw, limits, false)
}
fn decode_payload_scoped(
    raw: &[u8],
    limits: &ExternalMetadataLimits,
    header: bool,
) -> Result<DecodedPayload, Error> {
    if header {
        for document in semantic_wire::Wire::new(raw) {
            let document = document?;
            if document.number != 1 {
                continue;
            }
            for info in semantic_wire::Wire::new(document.bytes()?) {
                let info = info?;
                if info.number != 5 {
                    continue;
                }
                for field in semantic_wire::Wire::new(info.bytes()?) {
                    let field = field?;
                    if !matches!(field.number, 1 | 3 | 4 | 5 | 16 | 17) {
                        return Err(Error::Invalid(
                            "external module header contains non-header metadata",
                        ));
                    }
                }
            }
        }
    }
    let mut fields = 0;
    semantic_wire::validate(
        "TextDocuments",
        raw,
        &semantic_wire::Limits {
            max_depth: limits.max_depth,
            max_fields: limits.max_fields,
        },
        0,
        &mut fields,
    )?;
    let mut json = BoundedJson {
        bytes: Vec::new(),
        maximum: limits.max_json_bytes,
    };
    serde_json::to_writer(
        &mut json,
        &semantic_wire::Message {
            name: "TextDocuments",
            bytes: raw,
        },
    )
    .map_err(json_error)?;
    let text = std::str::from_utf8(&json.bytes)
        .map_err(|_| Error::Invalid("external metadata JSON UTF8"))?;
    let documents: Documents<'_> = from_json(text)?;
    if documents.documents.is_empty() {
        return Err(Error::Invalid("external metadata has no documents"));
    }
    let mut builder = FactBuilder::new();
    let mut declared = HashSet::new();
    let mut origins = Vec::new();
    for document in documents.documents {
        if document.schema != 4
            || document.language != 1
            || !document.text.is_empty()
            || !document.occurrences.is_empty()
            || !document.synthetics.is_empty()
            || !document.diagnostics.is_empty()
        {
            return Err(Error::Invalid(
                "external metadata requires signature-only SCALA documents",
            ));
        }
        if document.uri.is_empty() || !document.uri.ends_with(".class") {
            return Err(Error::Invalid("external metadata owning class URI"));
        }
        let origin = builder.intern(&document.uri)?;
        for info in document.symbols {
            if info.language != 1
                || if header {
                    info.kind != 10
                } else {
                    !matches!(info.kind, 3 | 8 | 9 | 21)
                }
                || !info.overridden_symbols.is_empty()
            {
                return Err(Error::Invalid(
                    "external metadata declaration kind or language",
                ));
            }
            let raw_signature = info.signature.map_or("{}", RawValue::get);
            if raw_signature.len() > limits.max_signature_bytes {
                return Err(Error::Limit("external metadata signature bytes"));
            }
            if header {
                // This projected header contains no declaration scope or effects.
                if !module_name(&info.symbol)
                    || selector_types::symbol::jvm_owner(&info.symbol).is_none()
                    || info.properties != 0
                    || raw_signature != "{}"
                {
                    return Err(Error::Invalid("external module header form"));
                }
            } else {
                signature_form(&info)?;
            }
            let id = global(&mut builder, &info.symbol, StrId::NONE)?;
            origins.resize(builder.facts.symbols.len(), StrId::NONE);
            origins[id.index()] = origin;
            if !declared.insert(id) {
                return Err(Error::Invalid("duplicate external metadata declaration"));
            }
            let projection = signature::project(raw_signature)?;
            if !projection.hardlinks.is_empty() {
                return Err(Error::Invalid(
                    "external metadata requires explicit formal rows",
                ));
            }
            let display = builder.intern(&info.display_name)?;
            let signature = if header {
                StrId::NONE
            } else {
                builder.intern(raw_signature)?
            };
            let record = &mut builder.facts.symbols[id.index()];
            record.display = display;
            record.kind = info.kind;
            record.properties = info.properties;
            record.signature = signature;
            for reference in projection
                .references
                .iter()
                .chain(projection.scoped_links.iter())
            {
                if !reference.0.is_empty() {
                    global(&mut builder, &reference.0, StrId::NONE)?;
                }
            }
            check_symbols(&builder, limits)?;
        }
    }
    origins.resize(builder.facts.symbols.len(), StrId::NONE);
    let facts = builder.finish()?;
    let mut by_name: Vec<_> = (0..facts.symbols.len())
        .map(|i| SymbolId(i as u32))
        .collect();
    by_name.sort_unstable_by(|&a, &b| facts.symbol_name(a).cmp(facts.symbol_name(b)));
    Ok(DecodedPayload {
        facts,
        declared,
        by_name,
        origins,
    })
}
fn payload_symbol(payload: &DecodedPayload, name: &str) -> Option<SymbolId> {
    payload
        .by_name
        .binary_search_by(|&id| payload.facts.symbol_name(id).cmp(name))
        .ok()
        .map(|i| payload.by_name[i])
}
#[derive(Deserialize)]
struct DeclarationTypeParameters<'a> {
    #[serde(default, borrow)]
    type_parameters: Option<DeclarationScope<'a>>,
}
#[derive(Deserialize)]
struct DeclarationScope<'a> {
    #[serde(default, borrow)]
    symlinks: Vec<Cow<'a, str>>,
}
fn declared_children(
    payload: &DecodedPayload,
    id: SymbolId,
) -> Result<crate::buffer::Buffer<SymbolId>, Error> {
    let record = payload.facts.symbols[id.index()];
    let raw = payload.facts.text(record.signature);
    let form: SignatureForm<'_> = from_json(raw)?;
    let mut children = crate::buffer::Buffer::new();
    let mut admit = |name: &str, kind: u32| -> Result<(), Error> {
        let child = payload_symbol(payload, name)
            .ok_or(Error::Invalid("external formal closure incomplete"))?;
        let formal = payload.facts.symbols[child.index()];
        if !payload.declared.contains(&child) || formal.kind != kind || formal.owner != id {
            return Err(Error::Invalid(
                "external formal declaration role or owner mismatch",
            ));
        }
        children.push(child);
        Ok(())
    };
    if matches!(record.kind, 3 | 21) {
        let method = callable::project(raw)?;
        for parameter in method.parameters.iter() {
            admit(&parameter.0, 8)?;
        }
    }
    if let Some(declaration) = form.method_signature.or(form.type_signature) {
        let declaration: DeclarationTypeParameters<'_> = from_json(declaration.get())?;
        if let Some(scope) = declaration.type_parameters {
            for parameter in scope.symlinks {
                admit(&parameter, 9)?;
            }
        }
    }
    children.sort_unstable();
    if children.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err(Error::Invalid(
            "external formal appears in multiple declaration slots",
        ));
    }
    // Other nested scopes need their own typed declaration contract. Never let
    // the generic signature walk silently promote an untyped scoped link.
    let projection = signature::project(raw)?;
    let mut projected = crate::buffer::Buffer::<SymbolId>::new();
    for link in projection.scoped_links.iter() {
        projected.push(
            payload_symbol(payload, &link.0)
                .ok_or(Error::Invalid("external formal closure incomplete"))?,
        );
    }
    projected.sort_unstable();
    if &*projected != &*children {
        return Err(Error::Invalid(
            "unsupported nested external declaration scope",
        ));
    }
    Ok(children)
}
fn closure(payload: &DecodedPayload, roots: &[String]) -> Result<Vec<SymbolId>, Error> {
    let mut pending = Vec::new();
    for root in roots {
        let id = payload_symbol(payload, root)
            .ok_or(Error::Invalid("requested external method absent"))?;
        if !method_name(root) || !matches!(payload.facts.symbols[id.index()].kind, 3 | 21) {
            return Err(Error::Invalid("requested external method identity"));
        }
        if !callable::project(
            payload
                .facts
                .text(payload.facts.symbols[id.index()].signature),
        )?
        .shape
        .known_method
        {
            return Err(Error::Invalid("external method signature missing"));
        }
        pending.push(id);
    }
    let mut result = Vec::new();
    let mut seen = HashSet::new();
    while let Some(id) = pending.pop() {
        if !seen.insert(id) {
            continue;
        }
        if !payload.declared.contains(&id) {
            return Err(Error::Invalid("external formal closure incomplete"));
        }
        result.push(id);
        pending.extend(declared_children(payload, id)?.iter().copied());
    }
    result.sort_unstable_by(|&a, &b| {
        payload
            .facts
            .symbol_name(a)
            .cmp(payload.facts.symbol_name(b))
    });
    Ok(result)
}
fn header_closure(payload: &DecodedPayload, roots: &[String]) -> Result<Vec<SymbolId>, Error> {
    let mut ids = Vec::with_capacity(roots.len());
    for name in roots {
        let id = payload_symbol(payload, name)
            .ok_or(Error::Invalid("requested external module absent"))?;
        let record = payload.facts.symbols[id.index()];
        if !module_name(name)
            || record.kind != 10
            || !record.signature.is_none()
            || !payload.declared.contains(&id)
        {
            return Err(Error::Invalid("requested external module header identity"));
        }
        ids.push(id);
    }
    ids.sort_unstable_by(|&a, &b| {
        payload
            .facts
            .symbol_name(a)
            .cmp(payload.facts.symbol_name(b))
    });
    Ok(ids)
}
fn semantic_identity(payload: &DecodedPayload, ids: &[SymbolId]) -> ContentHash {
    let mut hash = Sha256::new();
    hash.update(b"external-selected-signatures/v1\0");
    for &id in ids {
        let record = payload.facts.symbols[id.index()];
        hash_text(&mut hash, payload.facts.text(record.name));
        hash_text(&mut hash, payload.facts.text(record.display));
        hash.update(record.kind.to_le_bytes());
        hash.update(record.properties.to_le_bytes());
        hash_text(&mut hash, payload.facts.text(record.signature));
    }
    ContentHash(hash.finalize().into())
}
fn append(
    builder: &mut FactBuilder,
    payload: &DecodedPayload,
    ids: &[SymbolId],
    context: &str,
    limits: &ExternalMetadataLimits,
) -> Result<(), Error> {
    let context = builder.intern(context)?;
    for &id in ids {
        let external = payload.facts.symbols[id.index()];
        let target = global(builder, payload.facts.text(external.name), context)?;
        let previous = builder.facts.symbols[target.index()];
        let display = builder.intern(payload.facts.text(external.display))?;
        let signature = if external.signature.is_none() {
            StrId::NONE
        } else {
            builder.intern(payload.facts.text(external.signature))?
        };
        if previous.kind != 0
            && (previous.kind != external.kind
                || previous.properties != external.properties
                || previous.signature != signature)
        {
            return Err(Error::Invalid("conflicting external metadata projections"));
        }
        let record = &mut builder.facts.symbols[target.index()];
        record.display = display;
        record.signature = signature;
        record.kind = external.kind;
        record.properties = external.properties;
        let owner = record.owner;
        if external.kind == 10 {
            check_symbols(builder, limits)?;
            continue;
        }
        if !owner.is_none() {
            builder.facts.relations.push(RelationRecord {
                source: owner,
                target,
                kind: RelationKind::Member,
                file: FileId::NONE,
            });
        }
        let projection = signature::project(payload.facts.text(external.signature))?;
        for reference in projection.references.iter() {
            if reference.0.is_empty() {
                continue;
            }
            let reference = global(builder, &reference.0, context)?;
            builder.facts.relations.push(RelationRecord {
                source: target,
                target: reference,
                kind: RelationKind::Signature,
                file: FileId::NONE,
            });
        }
        check_symbols(builder, limits)?;
    }
    Ok(())
}

/// Admit a selected signature artifact against actual contextual provider bytes.
/// Missing requested roots may be omitted; supplied roots and closures must be exact.
pub fn admit(
    path: &Path,
    requests: &MetadataRequests<'_>,
    authority: &dyn MetadataProviderAuthority,
    expected_producer: ContentHash,
    limits: &ExternalMetadataLimits,
) -> Result<AdmittedExternalMetadata, Error> {
    let bytes = read_bounded(path, limits.max_manifest_bytes)?;
    let manifest: ExternalMetadataManifest = serde_json::from_slice(&bytes).map_err(json_error)?;
    if manifest.schema != MANIFEST_SCHEMA
        || expected_producer == ContentHash::default()
        || ContentHash::from_hex(&manifest.producer_sha256)? != expected_producer
        || ContentHash::from_hex(&manifest.authority_sha256)? != authority.identity()
    {
        return Err(Error::Invalid("external metadata producer or authority"));
    }
    let contexts_identity = requests.contexts_identity.ok_or(Error::Invalid(
        "external metadata requires captured compiler contexts",
    ))?;
    if contexts_identity != authority.contexts_identity()
        || contexts_identity != ContentHash::from_hex(&manifest.contexts_sha256)?
    {
        return Err(Error::Invalid(
            "external metadata compiler context input mismatch",
        ));
    }
    let mut identity = Sha256::new();
    identity.update(b"admitted-external-metadata/v1\0");
    identity.update(&bytes);
    identity.update(requests.identity().0);
    let mut payloads = Vec::new();
    let mut decoded = HashMap::<(ContentHash, bool), Arc<DecodedPayload>>::new();
    let mut total = 0usize;
    let mut retained_decoded = 0usize;
    let mut scopes = vec![None; manifest.payloads.len()];
    for (header, bindings) in [
        (false, &manifest.bindings),
        (true, &manifest.module_headers),
    ] {
        for projection in bindings.iter().flat_map(|b| &b.projections) {
            let scope = scopes
                .get_mut(projection.payload as usize)
                .ok_or(Error::Invalid("external metadata payload index"))?;
            if scope.is_some_and(|old| old != header) {
                return Err(Error::Invalid(
                    "external metadata payload mixes authority scopes",
                ));
            }
            *scope = Some(header);
        }
    }
    for (index, payload) in manifest.payloads.into_iter().enumerate() {
        let header = scopes[index].unwrap_or(false);
        let raw = read_bounded(
            &path.parent().unwrap_or(Path::new(".")).join(&payload.path),
            limits.max_payload_bytes,
        )?;
        total = total
            .checked_add(raw.len())
            .ok_or(Error::Limit("external metadata payload bytes"))?;
        if total > limits.max_total_payload_bytes {
            return Err(Error::Limit("external metadata payload bytes"));
        }
        let hash = sha(&raw);
        if hash != ContentHash::from_hex(&payload.sha256)? {
            return Err(Error::Invalid("external metadata payload hash"));
        }
        identity.update(hash.0);
        let value = if let Some(value) = decoded.get(&(hash, header)) {
            value.clone()
        } else {
            let mut remaining = limits.clone();
            remaining.max_decoded_bytes = limits.max_decoded_bytes.saturating_sub(retained_decoded);
            remaining.max_json_bytes = remaining.max_json_bytes.min(remaining.max_decoded_bytes);
            let value = Arc::new(decode_payload_scoped(&raw, &remaining, header)?);
            retained_decoded = retained_decoded
                .checked_add(value.facts.owned_bytes())
                .ok_or(Error::Limit("external metadata decoded bytes"))?;
            decoded.insert((hash, header), value.clone());
            value
        };
        payloads.push(value);
    }
    let mut builder = FactBuilder::new();
    let mut roots = Vec::new();
    let mut bound = HashSet::new();
    let mut providers =
        HashMap::<(&str, &str), (ContentHash, u32, ContentHash, ContentHash)>::new();
    for (header, binding) in manifest
        .bindings
        .iter()
        .map(|b| (false, b))
        .chain(manifest.module_headers.iter().map(|b| (true, b)))
    {
        let components: Vec<_> = binding.context.split('\0').collect();
        if binding.context.is_empty()
            || components.windows(2).any(|pair| pair[0] >= pair[1])
            || components.iter().any(|c| c.is_empty())
            || binding.roots.is_empty()
            || binding.projections.len() != components.len()
        {
            return Err(Error::Invalid("external metadata context components"));
        }
        for root in &binding.roots {
            if !requests.contains(&binding.context, root)
                || !bound.insert((binding.context.as_str(), root.as_str()))
            {
                return Err(Error::Invalid(
                    "external metadata root not uniquely requested",
                ));
            }
        }
        let mut first = None;
        let mut projected = HashSet::new();
        for projection in &binding.projections {
            if !components.contains(&projection.context.as_str())
                || !projected.insert(projection.context.as_str())
            {
                return Err(Error::Invalid("external metadata projection context"));
            }
            let key = (projection.context.as_str(), projection.outer_class.as_str());
            if !providers.contains_key(&key) {
                let resolved = authority
                    .resolve(key.0, key.1)?
                    .ok_or(Error::Invalid("external metadata provider unavailable"))?;
                if resolved.class_bytes.len() > limits.max_provider_class_bytes {
                    return Err(Error::Limit("external metadata provider class bytes"));
                }
                providers.insert(
                    key,
                    (
                        resolved.classpath_identity,
                        resolved.provider_index,
                        resolved.provider_sha256,
                        sha(&resolved.class_bytes),
                    ),
                );
            }
            let provider = &providers[&key];
            if provider.0 != ContentHash::from_hex(&projection.classpath_sha256)?
                || provider.1 != projection.provider_index
                || provider.2 != ContentHash::from_hex(&projection.provider_sha256)?
                || provider.3 != ContentHash::from_hex(&projection.outer_class_sha256)?
            {
                return Err(Error::Invalid("external metadata provider proof mismatch"));
            }
            let payload = payloads
                .get(projection.payload as usize)
                .ok_or(Error::Invalid("external metadata payload index"))?;
            let ids =
                if header {
                    if payload.declared.iter().any(|&id| {
                        !requests.contains(&binding.context, payload.facts.symbol_name(id))
                    }) {
                        return Err(Error::Invalid("unrequested external module header"));
                    }
                    header_closure(payload, &binding.roots)?
                } else {
                    closure(payload, &binding.roots)?
                };
            if ids.iter().any(|id| {
                payload
                    .facts
                    .text(payload.origins[id.index()])
                    .strip_suffix(".class")
                    != Some(projection.outer_class.as_str())
            }) {
                return Err(Error::Invalid(
                    "external metadata owning class differs from provider",
                ));
            }
            let semantic = semantic_identity(payload, &ids);
            if let Some(previous) = first {
                if previous != semantic {
                    return Err(Error::Invalid("composite context metadata differs"));
                }
            } else {
                first = Some(semantic);
                append(&mut builder, payload, &ids, &binding.context, limits)?;
            }
        }
        let context = builder.intern(&binding.context)?;
        for root in &binding.roots {
            roots.push(
                builder
                    .lookup_global_symbol(root, context)
                    .ok_or(Error::Invalid("external metadata root publication"))?,
            );
        }
    }
    Ok(AdmittedExternalMetadata {
        facts: builder.finish()?,
        roots,
        identity: ContentHash(identity.finalize().into()),
        capture_identity: requests.capture_identity,
        contexts_identity,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
    static NEXT: AtomicU64 = AtomicU64::new(0);
    const APPLY: &str = "selectedexternal/Configuration#PatienceConfig.apply(+1).";
    struct Temporary(PathBuf);
    impl Temporary {
        fn new() -> Self {
            let path = std::env::temp_dir().join(format!(
                "selector-external-metadata-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            std::fs::create_dir(&path).unwrap();
            Self(path)
        }
    }
    impl Drop for Temporary {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    struct Authority {
        calls: AtomicUsize,
        unavailable: bool,
    }
    impl MetadataProviderAuthority for Authority {
        fn identity(&self) -> ContentHash {
            sha(b"test-authority")
        }
        fn contexts_identity(&self) -> ContentHash {
            sha(b"test-contexts")
        }
        fn resolve(&self, context: &str, class: &str) -> Result<Option<ProviderResolution>, Error> {
            self.calls.fetch_add(1, Ordering::Relaxed);
            assert!(matches!(context, "a" | "b"));
            assert_eq!(class, "selectedexternal/Configuration");
            Ok((!self.unavailable).then(|| ProviderResolution {
                classpath_identity: sha(context.as_bytes()),
                provider_index: 2,
                provider_sha256: sha(b"test-provider"),
                class_bytes: Arc::from(&b"test-class"[..]),
            }))
        }
    }
    fn fixture() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/selected-external-apply")
    }
    fn builder(context: &str) -> FactBuilder {
        let mut builder = FactBuilder::new();
        let context = builder.intern(context).unwrap();
        builder.ensure_global_symbol(APPLY, context).unwrap();
        builder
    }
    fn manifest(context: &str) -> ExternalMetadataManifest {
        ExternalMetadataManifest {
            schema: MANIFEST_SCHEMA.to_owned(),
            producer_sha256: sha(b"test-converter").to_string(),
            authority_sha256: sha(b"test-authority").to_string(),
            contexts_sha256: sha(b"test-contexts").to_string(),
            payloads: vec![MetadataPayload {
                path: fixture().join("external-signatures.semanticdb"),
                sha256: sha(
                    &std::fs::read(fixture().join("external-signatures.semanticdb")).unwrap(),
                )
                .to_string(),
            }],
            module_headers: Vec::new(),
            bindings: vec![MetadataBinding {
                context: context.to_owned(),
                roots: vec![APPLY.to_owned()],
                projections: context
                    .split('\0')
                    .map(|context| MetadataProjection {
                        context: context.to_owned(),
                        payload: 0,
                        outer_class: "selectedexternal/Configuration".to_owned(),
                        outer_class_sha256: sha(b"test-class").to_string(),
                        classpath_sha256: sha(context.as_bytes()).to_string(),
                        provider_index: 2,
                        provider_sha256: sha(b"test-provider").to_string(),
                    })
                    .collect(),
            }],
        }
    }
    fn run(
        context: &str,
        change: impl FnOnce(&mut ExternalMetadataManifest),
    ) -> Result<AdmittedExternalMetadata, Error> {
        let source = builder(context);
        let requests = requests(
            &source,
            None,
            &MetadataRequestLimits::default(),
            sha(b"test-capture"),
            Some(sha(b"test-contexts")),
        )
        .unwrap();
        let temp = Temporary::new();
        let path = temp.0.join("manifest.json");
        let mut manifest = manifest(context);
        change(&mut manifest);
        std::fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
        admit(
            &path,
            &requests,
            &Authority {
                calls: AtomicUsize::new(0),
                unavailable: false,
            },
            sha(b"test-converter"),
            &ExternalMetadataLimits::default(),
        )
    }
    #[test]
    fn selected_formals_publish_without_source_parent_or_runtime_authority() {
        let admitted = run("a", |_| {}).unwrap();
        let mut source = builder("a");
        admitted.publish(&mut source).unwrap();
        let context = source.intern("a").unwrap();
        let root = source.lookup_global_symbol(APPLY, context).unwrap();
        let root_info = source.facts.symbols[root.index()];
        assert_eq!(root_info.kind, 3);
        assert!(root_info.file.is_none());
        assert_eq!(root_info.flags, 0);
        let metadata = callable::project(source.facts.text(root_info.signature)).unwrap();
        assert_eq!(metadata.parameters.len(), 2);
        for name in &*metadata.parameters {
            let formal = source.lookup_global_symbol(&name.0, context).unwrap();
            let formal = source.facts.symbols[formal.index()];
            assert_eq!(formal.owner, root);
            assert_eq!(formal.properties & 32768, 32768);
            assert!(formal.file.is_none());
            assert_eq!(formal.flags, 0);
        }
        assert!(source.facts.bodies.is_empty());
        assert!(
            source
                .facts
                .relations
                .iter()
                .all(|r| matches!(r.kind, RelationKind::Member | RelationKind::Signature))
        );
        assert!(
            source
                .lookup_global_symbol(
                    "selectedexternal/Configuration#PatienceConfig.apply().",
                    context
                )
                .is_none()
        );
        source.finish().unwrap();
    }
    #[test]
    fn authority_and_exact_requested_ids_fail_closed() {
        assert!(
            run("a", |m| m.bindings[0].roots[0] =
                APPLY.replace("Config.apply", "Config##apply"))
            .is_err()
        );
        assert!(run("a", |m| m.bindings[0].projections[0].provider_index = 1).is_err());
        assert!(
            run("a", |m| m.bindings[0].projections[0].classpath_sha256 =
                sha(b"changed-index").to_string())
            .is_err()
        );
        assert!(
            run("a", |m| m.bindings[0].projections[0].outer_class_sha256 =
                sha(b"wrong-class").to_string())
            .is_err()
        );
        assert!(
            run("a", |m| m.bindings[0].projections[0].provider_sha256 =
                sha(b"wrong-provider").to_string())
            .is_err()
        );
        assert!(
            run("a", |m| m.bindings[0].projections[0].context =
                "b".to_owned())
            .is_err()
        );
        assert!(run("a", |m| m.producer_sha256 = sha(b"wrong-tool").to_string()).is_err());
    }
    #[test]
    fn every_composite_component_is_required_without_representative_context() {
        assert!(run("a\0b", |_| {}).is_ok());
        assert!(
            run("a\0b", |m| {
                m.bindings[0].projections.pop();
            })
            .is_err()
        );
        assert!(
            run("a\0b", |m| m.bindings[0].projections[1].context =
                "a".to_owned())
            .is_err()
        );
    }
    #[test]
    fn source_information_and_relations_win_over_conflicting_external_closure() {
        let admitted = run("a", |_| {}).unwrap();
        let mut source = builder("a");
        let context = source.intern("a").unwrap();
        let root = source.lookup_global_symbol(APPLY, context).unwrap();
        let original = source.intern("{\"method_signature\":{}}").unwrap();
        source.facts.symbols[root.index()].kind = 3;
        source.facts.symbols[root.index()].flags = SYMBOL_DEFINED;
        source.facts.symbols[root.index()].signature = original;
        admitted.publish(&mut source).unwrap();
        assert_eq!(source.facts.symbols[root.index()].signature, original);
        assert!(
            source
                .facts
                .issues
                .iter()
                .any(|issue| issue.kind == IssueKind::ContextConflict && issue.symbol == root)
        );
        assert!(source.facts.relations.is_empty());
    }
    #[test]
    fn numeric_request_plan_is_sorted_contextual_and_bounded() {
        let mut source = builder("b");
        let a = source.intern("a").unwrap();
        source.ensure_global_symbol(APPLY, a).unwrap();
        let plan = requests(
            &source,
            None,
            &MetadataRequestLimits::default(),
            sha(b"test-capture"),
            Some(sha(b"test-contexts")),
        )
        .unwrap();
        assert_eq!(
            plan.iter().map(|r| r.context).collect::<Vec<_>>(),
            ["a", "b"]
        );
        assert!(
            requests(
                &source,
                None,
                &MetadataRequestLimits {
                    max_requests: 1,
                    max_name_bytes: usize::MAX
                },
                sha(b"test-capture"),
                Some(sha(b"test-contexts"))
            )
            .is_err()
        );
    }
    #[test]
    fn signature_payload_language_and_formal_closure_are_checked() {
        let raw = std::fs::read(fixture().join("external-signatures.semanticdb")).unwrap();
        let mut decoded = decode_payload(&raw, &ExternalMetadataLimits::default()).unwrap();
        let formal = payload_symbol(&decoded, &format!("{APPLY}(timeout)")).unwrap();
        decoded.declared.remove(&formal);
        assert!(closure(&decoded, &[APPLY.to_owned()]).is_err());
        // A minimal JAVA document remains valid protobuf but has no compiler authority.
        let java_document = [0x0a, 0x04, 0x08, 0x04, 0x50, 0x02];
        assert!(decode_payload(&java_document, &ExternalMetadataLimits::default()).is_err());
        assert!(
            decode_payload(
                &raw,
                &ExternalMetadataLimits {
                    max_fields: 1,
                    ..ExternalMetadataLimits::default()
                }
            )
            .is_err()
        );
        assert!(
            decode_payload(
                &raw,
                &ExternalMetadataLimits {
                    max_json_bytes: 1,
                    ..ExternalMetadataLimits::default()
                }
            )
            .is_err()
        );
    }
    fn varint(mut value: u64, output: &mut Vec<u8>) {
        while value >= 128 {
            output.push(value as u8 | 128);
            value >>= 7;
        }
        output.push(value as u8);
    }
    fn bytes_field(number: u32, bytes: &[u8], output: &mut Vec<u8>) {
        varint((u64::from(number) << 3) | 2, output);
        varint(bytes.len() as u64, output);
        output.extend_from_slice(bytes);
    }
    fn map_message(
        bytes: &[u8],
        number: u32,
        mut transform: impl FnMut(&[u8]) -> Vec<u8>,
    ) -> Vec<u8> {
        let mut output = Vec::new();
        for field in semantic_wire::Wire::new(bytes) {
            let field = field.unwrap();
            match field.value {
                semantic_wire::Value::Bytes(bytes) => {
                    if field.number == number {
                        bytes_field(field.number, &transform(bytes), &mut output);
                    } else {
                        bytes_field(field.number, bytes, &mut output);
                    }
                }
                semantic_wire::Value::Integer(value) => {
                    varint(u64::from(field.number) << 3, &mut output);
                    varint(value, &mut output);
                }
                semantic_wire::Value::Fixed(bytes) => {
                    varint(
                        (u64::from(field.number) << 3) | if bytes.len() == 4 { 5 } else { 1 },
                        &mut output,
                    );
                    output.extend_from_slice(bytes);
                }
            }
        }
        output
    }
    #[test]
    fn genuine_payload_rejects_reused_value_slots_and_value_parameters_in_type_slots() {
        let original = std::fs::read(fixture().join("external-signatures.semanticdb")).unwrap();
        for mode in 0..3 {
            let malformed = map_message(&original, 1, |document| {
                map_message(document, 5, |information| {
                    if semantic_wire::text_field(information, 1).unwrap() != Some(APPLY) {
                        return information.to_vec();
                    }
                    map_message(information, 17, |signature| {
                        map_message(signature, 2, |method| {
                            let scope = semantic_wire::Wire::new(method)
                                .map(Result::unwrap)
                                .find(|field| field.number == 2)
                                .unwrap()
                                .bytes()
                                .unwrap();
                            let parameter = semantic_wire::text_field(scope, 1).unwrap().unwrap();
                            match mode {
                                0 => map_message(method, 2, |scope| {
                                    let mut changed = scope.to_vec();
                                    bytes_field(1, parameter.as_bytes(), &mut changed);
                                    changed
                                }),
                                1 => {
                                    let mut changed = method.to_vec();
                                    bytes_field(2, scope, &mut changed);
                                    changed
                                }
                                _ => map_message(method, 1, |scope| {
                                    let mut changed = scope.to_vec();
                                    bytes_field(1, parameter.as_bytes(), &mut changed);
                                    changed
                                }),
                            }
                        })
                    })
                })
            });
            let temporary = Temporary::new();
            let path = temporary.0.join("malformed.semanticdb");
            std::fs::write(&path, &malformed).unwrap();
            let result = run("a", |manifest| {
                manifest.payloads[0] = MetadataPayload {
                    path,
                    sha256: sha(&malformed).to_string(),
                }
            });
            assert!(matches!(
                result,
                Err(Error::Invalid(
                    "external formal appears in multiple declaration slots"
                )) | Err(Error::Invalid(
                    "external formal declaration role or owner mismatch"
                ))
            ));
        }
    }
    const MODULE: &str = "selectedexternal/Configuration#PatienceConfig.";
    fn module_payload(kind: u64, signature: &[u8], extra: bool) -> Vec<u8> {
        let mut info = Vec::new();
        bytes_field(1, MODULE.as_bytes(), &mut info);
        varint(3 << 3, &mut info);
        varint(kind, &mut info);
        bytes_field(5, b"PatienceConfig", &mut info);
        varint(16 << 3, &mut info);
        varint(1, &mut info);
        if !signature.is_empty() {
            bytes_field(17, signature, &mut info);
        }
        if extra {
            bytes_field(18, &[], &mut info);
        }
        let mut doc = Vec::new();
        varint(1 << 3, &mut doc);
        varint(4, &mut doc);
        bytes_field(2, b"selectedexternal/Configuration.class", &mut doc);
        bytes_field(5, &info, &mut doc);
        varint(10 << 3, &mut doc);
        varint(1, &mut doc);
        let mut raw = Vec::new();
        bytes_field(1, &doc, &mut raw);
        raw
    }
    fn module_run(
        change: impl FnOnce(&mut ExternalMetadataManifest),
        raw: &[u8],
    ) -> Result<AdmittedExternalMetadata, Error> {
        let mut source = builder("a");
        let context = source.intern("a")?;
        source.ensure_global_symbol(MODULE, context)?;
        let requests = requests(
            &source,
            None,
            &MetadataRequestLimits::default(),
            sha(b"test-capture"),
            Some(sha(b"test-contexts")),
        )?;
        let temp = Temporary::new();
        let payload = temp.0.join("module.semanticdb");
        std::fs::write(&payload, raw)?;
        let mut manifest = manifest("a");
        let mut binding = manifest.bindings.remove(0);
        binding.roots = vec![MODULE.to_owned()];
        manifest.module_headers.push(binding);
        manifest.payloads[0] = MetadataPayload {
            path: payload,
            sha256: sha(raw).to_string(),
        };
        change(&mut manifest);
        let path = temp.0.join("manifest.json");
        std::fs::write(&path, serde_json::to_vec(&manifest).unwrap())?;
        admit(
            &path,
            &requests,
            &Authority {
                calls: AtomicUsize::new(0),
                unavailable: false,
            },
            sha(b"test-converter"),
            &ExternalMetadataLimits::default(),
        )
    }
    #[test]
    fn module_header_publishes_only_exact_contextual_object_identity() {
        let raw = module_payload(10, &[], false);
        assert!(decode_payload(&raw, &ExternalMetadataLimits::default()).is_err()); // method contract unchanged
        let admitted = module_run(|_| {}, &raw).unwrap();
        assert_eq!(admitted.methods(), 0);
        let mut source = builder("a");
        let context = source.intern("a").unwrap();
        let id = source.ensure_global_symbol(MODULE, context).unwrap();
        let before = source.facts.owned_bytes();
        let plan = requests(
            &source,
            None,
            &MetadataRequestLimits::default(),
            sha(b"test-capture"),
            Some(sha(b"test-contexts")),
        )
        .unwrap();
        assert!(plan.iter().any(|r| r.symbol == MODULE));
        drop(plan);
        assert_eq!(source.facts.owned_bytes(), before);
        assert!(source.facts.issues.is_empty());
        admitted.publish(&mut source).unwrap();
        let info = source.facts.symbols[id.index()];
        assert_eq!(info.kind, 10);
        assert_eq!(info.flags, 0);
        assert_eq!(info.properties, 0);
        assert!(info.signature.is_none());
        assert!(info.file.is_none());
        assert_eq!(
            source.facts.symbol_name(info.owner),
            "selectedexternal/Configuration#"
        );
        assert!(source.facts.relations.is_empty());
        assert!(source.facts.bodies.is_empty());
        assert!(source.lookup_global_symbol(MODULE, StrId::NONE).is_none());
        // A compiler-owned source declaration keeps its complete information.
        let signature = source.intern("{\"class_signature\":{}}").unwrap();
        source.facts.symbols[id.index()].flags = SYMBOL_DEFINED;
        source.facts.symbols[id.index()].signature = signature;
        source.facts.symbols[id.index()].properties = 136;
        admitted.publish(&mut source).unwrap();
        assert_eq!(source.facts.symbols[id.index()].signature, signature);
        assert_eq!(source.facts.symbols[id.index()].properties, 136);
    }
    #[test]
    fn module_headers_reject_wrong_kind_signature_scope_context_and_provider() {
        for raw in [
            module_payload(14, &[], false),
            module_payload(10, &[0x0a, 0], false),
            module_payload(10, &[], true),
        ] {
            assert!(module_run(|_| {}, &raw).is_err());
        }
        let raw = module_payload(10, &[], false);
        for duplicate in [true, false] {
            let extra = map_message(&raw, 1, |document| {
                let information = semantic_wire::Wire::new(document)
                    .map(Result::unwrap)
                    .find(|field| field.number == 5)
                    .unwrap()
                    .bytes()
                    .unwrap();
                let information = if duplicate {
                    information.to_vec()
                } else {
                    map_message(information, 1, |_| b"selectedexternal/Unexpected.".to_vec())
                };
                let mut changed = document.to_vec();
                bytes_field(5, &information, &mut changed);
                changed
            });
            assert!(module_run(|_| {}, &extra).is_err());
        }

        assert!(
            module_run(
                |m| m.module_headers[0].roots[0] = "selectedexternal/Other.".to_owned(),
                &raw
            )
            .is_err()
        );
        assert!(module_run(|m| m.module_headers[0].context = "a\0a".to_owned(), &raw).is_err());
        assert!(
            module_run(
                |m| m.module_headers[0].projections[0].outer_class_sha256 =
                    sha(b"wrong").to_string(),
                &raw
            )
            .is_err()
        );
        assert!(
            module_run(
                |m| m.bindings.push(MetadataBinding {
                    context: "a".to_owned(),
                    roots: vec![APPLY.to_owned()],
                    projections: vec![MetadataProjection {
                        context: "a".to_owned(),
                        payload: 0,
                        outer_class: "selectedexternal/Configuration".to_owned(),
                        outer_class_sha256: sha(b"test-class").to_string(),
                        classpath_sha256: sha(b"a").to_string(),
                        provider_index: 2,
                        provider_sha256: sha(b"test-provider").to_string()
                    }]
                }),
                &raw
            )
            .is_err()
        );
    }
}
