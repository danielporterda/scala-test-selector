//! Exact pinned compiler-classpath resolution, independent from effect closure.
use crate::{ClassDemand, ClassProvider, ProvidedClass};
use flate2::read::MultiGzDecoder;
use selector_compiled_products::{ClassId, VerifiedBinding};
use selector_models::binary::{
    self, AdmittedEntry, CapturedClasspath, ClassLookup, ClasspathEntry, EntryKind,
};
use selector_runtime_platform::{self as platform, PlatformOptions};
use selector_types::ContentHash;
use serde::Deserialize;
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::io::Read;
use std::path::{Component, Path, PathBuf};
use std::sync::Arc;

pub type Hash = [u8; 32];

fn budget(
    phase: &'static str,
    observed: usize,
    limit: usize,
    authority: Option<u32>,
    owner: Option<&str>,
    cached: (usize, usize),
) -> Error {
    eprintln!(
        "{}",
        serde_json::json!({
            "event":"native_provider_budget", "phase":phase,
            "observed":observed, "limit":limit, "authority":authority,
            "owner":owner, "cached_class_bytes":cached.0, "cached_class_count":cached.1
        })
    );
    Error::Budget
}
#[derive(Clone, Debug)]
pub struct InputPin {
    pub path: PathBuf,
    pub sha256: Hash,
    pub bytes: u64,
}
#[derive(Clone, Debug)]
pub struct ProviderLimits {
    pub manifest_bytes: u64,
    pub contexts: usize,
    pub entries: usize,
    pub retained_archives: usize,
    pub cached_class_bytes: usize,
    pub cached_classes: usize,
    pub binary: binary::Limits,
}
impl Default for ProviderLimits {
    fn default() -> Self {
        Self {
            manifest_bytes: 64 << 20,
            contexts: 1024,
            entries: 65_535,
            retained_archives: 768 << 20,
            cached_class_bytes: 64 << 20,
            cached_classes: 65_535,
            binary: Default::default(),
        }
    }
}
pub struct ProviderOptions {
    pub contexts: InputPin,
    pub binary_map: InputPin,
    pub relocated_root: PathBuf,
    pub facts_identity: Option<Hash>,
    pub source_products_identity: Option<Hash>,
    pub platform: Option<PlatformOptions>,
    pub limits: ProviderLimits,
}
#[derive(Debug)]
pub enum Error {
    Io(std::io::Error),
    Json(serde_json::Error),
    Invalid(&'static str),
    Budget,
    Native(binary::BinaryError),
    Platform(String),
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "native provider {self:?}")
    }
}
impl std::error::Error for Error {}
impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}
impl From<serde_json::Error> for Error {
    fn from(e: serde_json::Error) -> Self {
        Self::Json(e)
    }
}
impl From<binary::BinaryError> for Error {
    fn from(e: binary::BinaryError) -> Self {
        Self::Native(e)
    }
}

#[derive(Deserialize)]
struct Capture {
    schema_version: String,
    revision: String,
    source_root: PathBuf,
    #[serde(default)]
    errors: Vec<serde_json::Value>,
    contexts: Vec<CaptureContext>,
    input_objects: Vec<CapturedObject>,
    java_runtime: Option<CapturedRuntime>,
}
#[derive(Deserialize)]
struct CapturedRuntime {
    java_version: String,
}
#[derive(Deserialize)]
struct CaptureContext {
    context_id: String,
    class_directory: Option<PathBuf>,
    full_classpath: Vec<CapturedInput>,
    #[serde(default)]
    java_options: Vec<String>,
    java_home: Option<PathBuf>,
    #[serde(default)]
    exported_products: Vec<CapturedProduct>,
}
#[derive(Deserialize)]
struct CapturedProduct {
    path: PathBuf,
}
#[derive(Deserialize)]
struct CapturedInput {
    index: usize,
    path: String,
    input_object: Option<String>,
    sha256: Option<String>,
    #[serde(default)]
    project_output_origins: Vec<serde_json::Value>,
}
#[derive(Deserialize)]
struct CapturedObject {
    path: String,
    kind: String,
    sha256: String,
    files: Option<u64>,
    bytes: Option<u64>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct NativeMap {
    version: u32,
    revision: Option<String>,
    facts_identity: Option<String>,
    java_feature: Option<u16>,
    declared_platform: Option<platform::PlatformBinding>,
    contexts: Vec<NativeContext>,
    #[serde(default)]
    types: Vec<serde_json::Value>,
    methods: Vec<serde_json::Value>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct NativeContext {
    id: String,
    entries: Vec<NativeEntry>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct NativeEntry {
    path: PathBuf,
    sha256: Option<String>,
    kind: String,
    files: Option<u64>,
    bytes: Option<u64>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResolutionState {
    Found,
    VerifiedClasspathMiss,
    OpaquePrefix,
}
#[derive(Clone, Debug)]
pub struct ResolutionReceipt {
    pub authority: u32,
    pub owner: Arc<str>,
    pub state: ResolutionState,
    pub selected_entry: Option<u32>,
    pub provider: Option<u32>,
    pub class_sha256: Option<Hash>,
    pub examined_prefix: u32,
    pub prefix_sha256: Hash,
    pub binding_sha256: Hash,
    pub own_product: Option<ClassId>,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MemberInvocation {
    Static,
    Special,
    Virtual,
    Interface,
    StaticField,
    InstanceField,
}
impl MemberInvocation {
    fn invoke(self) -> Option<binary::InvokeKind> {
        Some(match self {
            Self::Static => binary::InvokeKind::Static,
            Self::Special => binary::InvokeKind::Special,
            Self::Virtual => binary::InvokeKind::Virtual,
            Self::Interface => binary::InvokeKind::Interface,
            _ => return None,
        })
    }
}
#[derive(Debug)]
pub struct MemberResolution {
    pub authority: u32,
    pub owner: Arc<str>,
    pub name: Arc<str>,
    pub descriptor: Arc<str>,
    pub caller: Option<Arc<str>>,
    pub invocation: MemberInvocation,
    pub resolution: selector_jvm_resolve::Resolution,
    pub declared_owner: Option<Arc<str>>,
    next: u32,
}
#[derive(Clone)]
struct Cached {
    bytes: Option<Arc<[u8]>>,
    receipt: Arc<ResolutionReceipt>,
    metadata: Option<Arc<binary::ClassMetadata>>,
}
struct Context<'a> {
    name: Arc<str>,
    entries: Vec<usize>,
    own_entry: Option<usize>,
    application_entries: Vec<usize>,
    own: HashMap<&'a str, ClassId>,
    loader: Option<CapturedClasspath>,
    cache: HashMap<Arc<str>, Cached>,
}
pub struct VerifiedProvider<'a> {
    identity: Hash,
    capture: Hash,
    map: Hash,
    source_root: PathBuf,
    relocated_root: PathBuf,
    products: Option<&'a VerifiedBinding>,
    contexts: Vec<Context<'a>>,
    context_ids: HashMap<Arc<str>, u32>,
    entries: Vec<ClasspathEntry>,
    admitted: Vec<AdmittedEntry>,
    java_feature: Option<u16>,
    limits: ProviderLimits,
    class_bytes: usize,
    class_count: usize,
    retained_archives: usize,
    inventory_only: bool,
    inputs: Vec<InputPin>,
    declared_platform: Option<(Hash, usize)>,
    member_heads: HashMap<Hash, u32>,
    members: Vec<MemberResolution>,
}

/// Preserve the ordinary ordered first-provider proof while holding only one
/// archive/directory inventory at a time. Failed prefixes never become misses.
fn inventory_lookup(
    entries: &[ClasspathEntry],
    order: &[usize],
    limits: binary::Limits,
    java_feature: Option<u16>,
    owner: &str,
) -> Result<ClassLookup, binary::BinaryError> {
    let mut examined = Vec::with_capacity(order.len());
    for (ordinal, &entry) in order.iter().enumerate() {
        let mut loader = CapturedClasspath::new(vec![entries[entry].clone()], limits)?
            .with_java_feature(java_feature)?;
        match loader.lookup(owner)? {
            ClassLookup::Found(mut found) => {
                for mut proof in found.proof.examined {
                    proof.entry_index = ordinal;
                    examined.push(proof);
                }
                found.proof.examined = examined;
                found.proof.selected_entry = Some(ordinal);
                return Ok(ClassLookup::Found(found));
            }
            ClassLookup::Absent(proof) => {
                for mut proof in proof.examined {
                    proof.entry_index = ordinal;
                    examined.push(proof);
                }
            }
        }
    }
    Ok(ClassLookup::Absent(binary::ResolutionProof {
        selected_entry: None,
        class_hash: None,
        examined,
    }))
}

fn hash(bytes: &[u8]) -> Hash {
    Sha256::digest(bytes).into()
}
fn hash_text(text: &str) -> Result<Hash, Error> {
    ContentHash::from_hex(text)
        .map(|h| h.0)
        .map_err(|_| Error::Invalid("hash spelling"))
}
fn normal(path: &Path) -> bool {
    path.is_absolute()
        && path
            .components()
            .all(|c| matches!(c, Component::RootDir | Component::Normal(_)))
}
fn no_symlinks(path: &Path, missing: bool) -> Result<(), Error> {
    if !normal(path) {
        return Err(Error::Invalid("noncanonical input path"));
    }
    let mut current = PathBuf::new();
    for component in path.components() {
        current.push(component.as_os_str());
        match std::fs::symlink_metadata(&current) {
            Ok(meta) if meta.file_type().is_symlink() => {
                return Err(Error::Invalid("symlink input closure"));
            }
            Ok(_) => (),
            Err(e) if missing && e.kind() == std::io::ErrorKind::NotFound => return Ok(()),
            Err(e) => return Err(e.into()),
        }
    }
    Ok(())
}
fn read_pin(pin: &InputPin, maximum: u64) -> Result<Vec<u8>, Error> {
    no_symlinks(&pin.path, false)?;
    let meta = std::fs::metadata(&pin.path)?;
    if !meta.is_file() || meta.len() != pin.bytes || pin.bytes > maximum {
        return Err(Error::Invalid("input pin size/type"));
    }
    let mut bytes = Vec::new();
    std::fs::File::open(&pin.path)?
        .take(maximum + 1)
        .read_to_end(&mut bytes)?;
    if bytes.len() as u64 != pin.bytes || hash(&bytes) != pin.sha256 {
        return Err(Error::Invalid("input pin hash"));
    }
    Ok(bytes)
}
fn observe_pin(path: &Path) -> Result<InputPin, Error> {
    no_symlinks(path, false)?;
    let mut file = std::fs::File::open(path)?;
    let mut digest = Sha256::new();
    let mut bytes = 0u64;
    let mut buffer = [0u8; 65_536];
    loop {
        let n = file.read(&mut buffer)?;
        if n == 0 {
            break;
        }
        digest.update(&buffer[..n]);
        bytes = bytes.checked_add(n as u64).ok_or(Error::Budget)?;
    }
    Ok(InputPin {
        path: path.to_owned(),
        sha256: digest.finalize().into(),
        bytes,
    })
}
fn physical(captured: &Path, source_root: &Path, root: &Path) -> Result<PathBuf, Error> {
    let path = match captured.strip_prefix(source_root) {
        Ok(relative) => {
            if !relative
                .components()
                .all(|c| matches!(c, Component::Normal(_)))
            {
                return Err(Error::Invalid("relocated input path"));
            }
            root.join(relative)
        }
        Err(_) => captured.to_owned(),
    };
    if !normal(&path) {
        return Err(Error::Invalid("captured input path"));
    }
    Ok(path)
}
fn feature(version: &str) -> Option<u16> {
    version
        .split(['.', '-', '+'])
        .next()?
        .parse()
        .ok()
        .filter(|&v| v > 0 && v <= 255)
}
fn native_entry(row: NativeEntry, base: &Path) -> Result<ClasspathEntry, Error> {
    let kind = match row.kind.as_str() {
        "jar" => EntryKind::Jar,
        "directory" => EntryKind::Directory {
            files: row.files.ok_or(Error::Invalid("directory files"))?,
            bytes: row.bytes.ok_or(Error::Invalid("directory bytes"))?,
        },
        "absent_empty_output" => EntryKind::AbsentEmptyOutput,
        "unavailable" => EntryKind::Unavailable,
        _ => return Err(Error::Invalid("entry kind")),
    };
    let path = if row.path.is_absolute() {
        row.path
    } else {
        base.join(row.path)
    };
    if !normal(&path) {
        return Err(Error::Invalid("native entry path"));
    }
    let sha256 = row
        .sha256
        .as_deref()
        .map(hash_text)
        .transpose()?
        .unwrap_or_default();
    if sha256 == [0; 32] && !matches!(kind, EntryKind::Unavailable) {
        return Err(Error::Invalid("entry digest"));
    }
    Ok(ClasspathEntry {
        path,
        sha256: ContentHash(sha256),
        kind,
    })
}
fn object_matches(entry: &ClasspathEntry, object: &CapturedObject) -> Result<bool, Error> {
    if entry.sha256.0 != hash_text(&object.sha256)? {
        return Ok(false);
    }
    Ok(match entry.kind {
        EntryKind::Unavailable => true,
        EntryKind::Jar => {
            object.kind == "file" && entry.path.extension().is_some_and(|x| x == "jar")
        }
        EntryKind::Directory { files, bytes } => {
            object.kind == "directory" && object.files == Some(files) && object.bytes == Some(bytes)
        }
        EntryKind::AbsentEmptyOutput => object.kind == "absent_empty_project_output",
    })
}
fn provenance_failure(kind: binary::ErrorKind) -> bool {
    matches!(
        kind,
        binary::ErrorKind::HashMismatch
            | binary::ErrorKind::DirectoryFingerprintMismatch
            | binary::ErrorKind::Io
            | binary::ErrorKind::BadCrc
            | binary::ErrorKind::SymlinkInput
    )
}

impl<'a> VerifiedProvider<'a> {
    pub fn admit(
        options: &ProviderOptions,
        products: Option<&'a VerifiedBinding>,
    ) -> Result<Self, Error> {
        Self::admit_inner(options, products, false)
    }
    /// Verify the same capture, provider order and platform bindings without
    /// retaining the union of archive payloads. Each metadata scan or lookup
    /// independently hash-admits one bounded entry and drops it afterward.
    pub fn admit_inventory(options: &ProviderOptions) -> Result<Self, Error> {
        Self::admit_inner(options, None, true)
    }
    fn admit_inner(
        options: &ProviderOptions,
        products: Option<&'a VerifiedBinding>,
        inventory_only: bool,
    ) -> Result<Self, Error> {
        if products.map(VerifiedBinding::identity) != options.source_products_identity
            || products.is_some_and(|p| p.contexts_identity() != options.contexts.sha256)
        {
            return Err(Error::Invalid("source-product capture binding"));
        }
        let raw = read_pin(&options.contexts, options.limits.manifest_bytes)?;
        let bytes = if options.contexts.path.extension().is_some_and(|x| x == "gz") {
            let mut out = Vec::new();
            MultiGzDecoder::new(raw.as_slice())
                .take(options.limits.manifest_bytes + 1)
                .read_to_end(&mut out)?;
            if out.len() as u64 > options.limits.manifest_bytes {
                return Err(budget(
                    "context_decompression",
                    out.len(),
                    options.limits.manifest_bytes as usize,
                    None,
                    None,
                    (0, 0),
                ));
            }
            out
        } else {
            raw
        };
        let capture: Capture = serde_json::from_slice(&bytes)?;
        let map_bytes = read_pin(&options.binary_map, options.limits.manifest_bytes)?;
        let native: NativeMap = serde_json::from_slice(&map_bytes)?;
        if capture.schema_version != "sbt-compiler-context/v1"
            || !capture.errors.is_empty()
            || !normal(&capture.source_root)
            || native.version != 1
            || native.revision.as_deref() != Some(capture.revision.as_str())
            || native
                .facts_identity
                .as_deref()
                .map(hash_text)
                .transpose()?
                != options.facts_identity
            || native.java_feature
                != capture
                    .java_runtime
                    .as_ref()
                    .and_then(|r| feature(&r.java_version))
            || native.contexts.is_empty()
            || native.contexts.len() > options.limits.contexts
        {
            return Err(Error::Invalid("capture/native generation binding"));
        }
        let _ = (&native.types, &native.methods); // bindings are not guessed aliases
        let root = std::fs::canonicalize(&options.relocated_root)?;
        no_symlinks(&root, false)?;
        let base = options
            .binary_map
            .path
            .parent()
            .ok_or(Error::Invalid("map parent"))?;
        let declared = options
            .platform
            .as_ref()
            .map(|p| {
                if p.contexts != options.contexts.path {
                    return Err(Error::Invalid("platform original capture path"));
                }
                platform::admit(p).map_err(|e| Error::Platform(e.to_string()))
            })
            .transpose()?;
        if native.declared_platform.as_ref() != declared.as_ref().map(|p| &p.binding)
            || declared
                .as_ref()
                .is_some_and(|p| Some(p.java_feature) != native.java_feature)
        {
            return Err(Error::Invalid("explicit platform/native binding"));
        }
        let mut captured_contexts = HashMap::new();
        for context in &capture.contexts {
            if captured_contexts
                .insert(context.context_id.as_str(), context)
                .is_some()
            {
                return Err(Error::Invalid("duplicate captured context"));
            }
        }
        let mut objects = HashMap::new();
        for object in &capture.input_objects {
            if objects.insert(object.path.as_str(), object).is_some() {
                return Err(Error::Invalid("duplicate captured object"));
            }
        }
        let mut contexts = Vec::new();
        let mut context_ids = HashMap::new();
        let mut entries = Vec::<ClasspathEntry>::new();
        let mut entry_ids = HashMap::new();
        for row in native.contexts {
            let source = *captured_contexts
                .get(row.id.as_str())
                .ok_or(Error::Invalid("uncaptured native context"))?;
            if source.java_home.is_some() || !source.java_options.is_empty() {
                return Err(Error::Invalid("unsupported compiler provider override"));
            }
            let prefix = usize::from(
                declared
                    .as_ref()
                    .is_some_and(|p| p.contains_context(&row.id)),
            );
            if row.entries.len() != source.full_classpath.len() + prefix {
                return Err(Error::Invalid("native classpath length"));
            }
            let rows = row
                .entries
                .into_iter()
                .map(|e| native_entry(e, base))
                .collect::<Result<Vec<_>, _>>()?;
            if prefix == 1 && rows.first() != declared.as_ref().map(|p| &p.entry) {
                return Err(Error::Invalid("bootstrap provider order"));
            }
            let mut ids = Vec::with_capacity(rows.len());
            let mut application_entries = Vec::new();
            for (ordinal, entry) in rows.into_iter().enumerate() {
                let mut application = false;
                if ordinal >= prefix {
                    let index = ordinal - prefix;
                    let input = &source.full_classpath[index];
                    application = !input.project_output_origins.is_empty()
                        || source
                            .exported_products
                            .iter()
                            .any(|p| p.path == Path::new(&input.path))
                        || source.class_directory.as_deref() == Some(Path::new(&input.path));
                    if input.index != index {
                        return Err(Error::Invalid("captured classpath ordinal"));
                    }
                    let key = input.input_object.as_deref().unwrap_or(&input.path);
                    let object = *objects
                        .get(key)
                        .ok_or(Error::Invalid("uncaptured native entry"))?;
                    if input.sha256.as_deref() != Some(object.sha256.as_str())
                        || entry.path != physical(Path::new(key), &capture.source_root, &root)?
                        || !object_matches(&entry, object)?
                    {
                        return Err(Error::Invalid(
                            "native first-provider capture correspondence",
                        ));
                    }
                    if declared.as_ref().is_some_and(|p| entry == p.entry) {
                        return Err(Error::Invalid("duplicate/foreign platform provider"));
                    }
                }
                no_symlinks(
                    &entry.path,
                    matches!(
                        entry.kind,
                        EntryKind::Unavailable | EntryKind::AbsentEmptyOutput
                    ),
                )?;
                let id = if let Some(&id) = entry_ids.get(&entry) {
                    id
                } else {
                    if entries.len() >= options.limits.entries {
                        return Err(budget(
                            "provider_entries",
                            entries.len().saturating_add(1),
                            options.limits.entries,
                            None,
                            None,
                            (0, 0),
                        ));
                    }
                    let id = entries.len();
                    entry_ids.insert(entry.clone(), id);
                    entries.push(entry);
                    id
                };
                if application {
                    application_entries.push(id);
                }
                ids.push(id);
            }
            application_entries.sort_unstable();
            application_entries.dedup();
            let own_entry = source.class_directory.as_ref().and_then(|directory| {
                source
                    .full_classpath
                    .first()
                    .filter(|input| input.index == 0 && Path::new(&input.path) == directory)
                    .map(|_| ids[prefix])
            });
            let authority = contexts.len() as u32;
            let name: Arc<str> = row.id.into();
            if context_ids.insert(name.clone(), authority).is_some() {
                return Err(Error::Invalid("duplicate native context"));
            }
            contexts.push(Context {
                name,
                entries: ids,
                own_entry,
                application_entries,
                own: HashMap::new(),
                loader: None,
                cache: HashMap::new(),
            });
        }
        if let Some(products) = products {
            for index in 0..products.class_count() {
                let id = ClassId(index as u32);
                let class = products
                    .class(id)
                    .ok_or(Error::Invalid("compiled class reference"))?;
                let Some(&authority) = context_ids.get(class.context) else {
                    continue;
                };
                let context = &mut contexts[authority as usize];
                let Some(own) = context.own_entry else {
                    return Err(Error::Invalid(
                        "compiled output missing captured ordinal zero",
                    ));
                };
                if !matches!(entries[own].kind, EntryKind::Directory { .. }) {
                    return Err(Error::Invalid(
                        "compiled output lacks full directory authority",
                    ));
                }
                if context.own.insert(class.owner, id).is_some() {
                    return Err(Error::Invalid("ambiguous compiled class ownership"));
                }
            }
        }
        let mut admitted = Vec::with_capacity(entries.len());
        let mut retained = 0usize;
        for entry in entries.iter().filter(|_| !inventory_only) {
            let mut limits = options.limits.binary;
            limits.max_retained_bytes = options
                .limits
                .retained_archives
                .checked_sub(retained)
                .ok_or(Error::Budget)?;
            let snapshot = AdmittedEntry::admit(entry.clone(), limits, native.java_feature)?;
            if snapshot.error().is_some_and(|e| provenance_failure(e.kind)) {
                return Err(Error::Native(snapshot.error().unwrap()));
            }
            if snapshot
                .error()
                .is_some_and(|e| e.kind == binary::ErrorKind::ResourceLimit)
            {
                return Err(Error::Budget);
            }
            retained = retained
                .checked_add(snapshot.retained_bytes())
                .ok_or(Error::Budget)?;
            if retained > options.limits.retained_archives {
                return Err(Error::Budget);
            }
            admitted.push(snapshot);
        }
        let mut identity = Sha256::new();
        identity.update(b"verified-native-class-provider/1\0");
        identity.update(options.contexts.sha256);
        identity.update(options.binary_map.sha256);
        identity.update(products.map(VerifiedBinding::identity).unwrap_or_default());
        if let Some(p) = &declared {
            identity.update(p.binding.identity.0);
        }
        let declared_platform = declared
            .as_ref()
            .map(|platform| {
                entry_ids
                    .get(&platform.entry)
                    .copied()
                    .map(|entry| (platform.binding.identity.0, entry))
                    .ok_or(Error::Invalid("platform has no admitted context"))
            })
            .transpose()?;
        let mut inputs = vec![options.contexts.clone(), options.binary_map.clone()];
        if let Some(p) = declared {
            for path in p.input_files() {
                inputs.push(observe_pin(path)?);
            }
        }
        Ok(Self {
            identity: identity.finalize().into(),
            capture: options.contexts.sha256,
            map: options.binary_map.sha256,
            source_root: capture.source_root,
            relocated_root: root,
            products,
            contexts,
            context_ids,
            entries,
            admitted,
            java_feature: native.java_feature,
            limits: options.limits.clone(),
            class_bytes: 0,
            class_count: 0,
            retained_archives: retained,
            inventory_only,
            inputs,
            declared_platform,
            member_heads: HashMap::new(),
            members: Vec::new(),
        })
    }
    pub fn identity(&self) -> Hash {
        self.identity
    }
    pub(crate) fn java_feature(&self) -> Option<u16> {
        self.java_feature
    }
    pub fn context(&self, authority: u32) -> Option<&str> {
        self.contexts
            .get(authority as usize)
            .map(|c| c.name.as_ref())
    }
    pub fn authority(&self, context: &str) -> Option<u32> {
        self.context_ids.get(context).copied()
    }
    pub fn input_files(&self) -> &[InputPin] {
        &self.inputs
    }
    pub(crate) fn capture_document(&self) -> Result<Vec<u8>, Error> {
        let raw = read_pin(&self.inputs[0], self.limits.manifest_bytes)?;
        if self.inputs[0].path.extension().is_some_and(|x| x == "gz") {
            let mut decoded = Vec::new();
            MultiGzDecoder::new(raw.as_slice())
                .take(self.limits.manifest_bytes + 1)
                .read_to_end(&mut decoded)?;
            if decoded.len() as u64 > self.limits.manifest_bytes {
                return Err(budget(
                    "capture_document_decompression",
                    decoded.len(),
                    self.limits.manifest_bytes as usize,
                    None,
                    None,
                    (self.class_bytes, self.class_count),
                ));
            }
            Ok(decoded)
        } else {
            Ok(raw)
        }
    }
    pub(crate) fn captured_path(&self, path: &Path) -> Result<PathBuf, Error> {
        physical(path, &self.source_root, &self.relocated_root)
    }
    pub(crate) fn context_entries(&self, authority: u32) -> Option<&[usize]> {
        self.contexts
            .get(authority as usize)
            .map(|c| c.entries.as_slice())
    }
    pub(crate) fn entry_metadata(&self, index: usize) -> Result<(Vec<String>, Vec<String>), Error> {
        let mut loader = self.entry_snapshot(index)?;
        Ok((loader.class_names(0)?, loader.manifest_class_path(0)?))
    }
    pub(crate) fn entry_snapshot(&self, index: usize) -> Result<CapturedClasspath, Error> {
        let entry = self
            .entries
            .get(index)
            .ok_or(Error::Invalid("entry metadata index"))?;
        if self.inventory_only {
            return Ok(
                CapturedClasspath::new(vec![entry.clone()], self.inventory_limits())?
                    .with_java_feature(self.java_feature)?,
            );
        }
        Ok(CapturedClasspath::from_admitted(
            vec![entry.clone()],
            &[&self.admitted[index]],
            self.limits.binary,
            self.java_feature,
        )?)
    }
    fn inventory_limits(&self) -> binary::Limits {
        let mut limits = self.limits.binary;
        limits.max_retained_bytes = limits.max_retained_bytes.min(self.limits.retained_archives);
        limits
    }
    pub fn retained_archive_bytes(&self) -> usize {
        self.retained_archives
    }
    pub fn classpath_entries(&self) -> &[ClasspathEntry] {
        &self.entries
    }
    /// A receipt alone cannot select a different provider or erase ownership.
    /// Only the issuer uses this borrowed view; it grants no method semantics.
    pub(crate) fn inventory_entry(
        &self,
        receipt: &ResolutionReceipt,
    ) -> Result<(&ClasspathEntry, bool, Option<Hash>), Error> {
        let context = self
            .contexts
            .get(receipt.authority as usize)
            .ok_or(Error::Invalid("inventory context"))?;
        let selected = receipt
            .selected_entry
            .ok_or(Error::Invalid("inventory selection"))? as usize;
        let global = *context
            .entries
            .get(selected)
            .ok_or(Error::Invalid("inventory ordinal"))?;
        if receipt.state != ResolutionState::Found || receipt.provider != Some(global as u32) {
            return Err(Error::Invalid("inventory provider receipt"));
        }
        let application = receipt.own_product.is_some()
            || context.own_entry == Some(global)
            || context.application_entries.binary_search(&global).is_ok();
        let declared = self
            .declared_platform
            .filter(|&(_, entry)| entry == global)
            .map(|(identity, _)| identity);
        Ok((&self.entries[global], application, declared))
    }
    pub fn receipt(&self, authority: u32, owner: &str) -> Option<&ResolutionReceipt> {
        self.contexts
            .get(authority as usize)?
            .cache
            .get(owner)
            .map(|c| c.receipt.as_ref())
    }
    /// Reuses the exact first-provider bytes and one immutable header index.
    pub fn metadata(
        &mut self,
        authority: u32,
        owner: &str,
    ) -> Result<Option<Arc<binary::ClassMetadata>>, Error> {
        let (bytes, _) = self.resolve(authority, owner)?;
        let Some(bytes) = bytes else { return Ok(None) };
        let cached = self.contexts[authority as usize]
            .cache
            .get(owner)
            .expect("resolved entry");
        if let Some(metadata) = &cached.metadata {
            return Ok(Some(metadata.clone()));
        }
        let metadata = Arc::new(binary::ClassMetadata::new(bytes, self.limits.binary)?);
        let charge = metadata.metadata_bytes();
        if self
            .class_bytes
            .checked_add(charge)
            .is_none_or(|n| n > self.limits.cached_class_bytes)
        {
            return Err(budget(
                "class_metadata_bytes",
                self.class_bytes.saturating_add(charge),
                self.limits.cached_class_bytes,
                Some(authority),
                Some(owner),
                (self.class_bytes, self.class_count),
            ));
        }
        self.class_bytes += charge;
        self.contexts[authority as usize]
            .cache
            .get_mut(owner)
            .expect("resolved entry")
            .metadata = Some(metadata.clone());
        Ok(Some(metadata))
    }
    /// Cached by contextual raw ABI, invocation kind and caller. A returned
    /// declaration is member-resolution authority, never dispatch completeness.
    pub fn resolve_member(
        &mut self,
        authority: u32,
        member: binary::MemberRef<'_>,
        invocation: MemberInvocation,
        caller: Option<&str>,
    ) -> Result<&MemberResolution, Error> {
        if [
            member.owner,
            member.name,
            member.descriptor,
            caller.unwrap_or(""),
        ]
        .iter()
        .any(|text| text.len() > u16::MAX as usize)
        {
            return Err(Error::Invalid("member ABI bound"));
        }
        if self.context(authority).is_none() {
            return Err(Error::Invalid("unknown native authority"));
        }
        let mut hash = Sha256::new();
        hash.update(authority.to_le_bytes());
        hash.update([invocation as u8]);
        for text in [
            member.owner,
            member.name,
            member.descriptor,
            caller.unwrap_or(""),
        ] {
            hash.update((text.len() as u64).to_le_bytes());
            hash.update(text.as_bytes());
        }
        let key: Hash = hash.finalize().into();
        let mut next = self.member_heads.get(&key).copied().unwrap_or(u32::MAX);
        while next != u32::MAX {
            let row = &self.members[next as usize];
            if row.authority == authority
                && row.invocation == invocation
                && row.owner.as_ref() == member.owner
                && row.name.as_ref() == member.name
                && row.descriptor.as_ref() == member.descriptor
                && row.caller.as_deref() == caller
            {
                return Ok(&self.members[next as usize]);
            }
            next = row.next;
        }
        if self.members.len() >= self.limits.cached_classes {
            return Err(budget(
                "member_count",
                self.members.len().saturating_add(1),
                self.limits.cached_classes,
                Some(authority),
                Some(member.owner),
                (self.class_bytes, self.class_count),
            ));
        }
        let mut failure = None;
        let mut loader = |owner: &str| match self.metadata(authority, owner) {
            Ok(row) => Ok(row),
            Err(error) => {
                failure = Some(error);
                Err(selector_types::Error::Invalid(
                    "native provider resolution input",
                ))
            }
        };
        let resolution = match invocation {
            MemberInvocation::StaticField => {
                selector_jvm_resolve::resolve_field_metadata(member, true, &mut loader)
            }
            MemberInvocation::InstanceField => {
                selector_jvm_resolve::resolve_field_metadata(member, false, &mut loader)
            }
            other => selector_jvm_resolve::resolve_method_metadata(
                member,
                other.invoke().expect("method invocation"),
                caller,
                &mut loader,
            ),
        };
        if let Some(error) = failure {
            return Err(error);
        }
        let resolution =
            resolution.map_err(|_| Error::Invalid("native member resolution input"))?;
        let charge = member.owner.len()
            + member.name.len()
            + member.descriptor.len()
            + caller.map_or(0, str::len)
            + 256;
        if self
            .class_bytes
            .checked_add(charge)
            .is_none_or(|n| n > self.limits.cached_class_bytes)
        {
            return Err(budget(
                "member_cache_bytes",
                self.class_bytes.saturating_add(charge),
                self.limits.cached_class_bytes,
                Some(authority),
                Some(member.owner),
                (self.class_bytes, self.class_count),
            ));
        }
        self.class_bytes += charge;
        let id = self.members.len() as u32;
        self.members.push(MemberResolution {
            authority,
            owner: Arc::from(member.owner),
            name: Arc::from(member.name),
            descriptor: Arc::from(member.descriptor),
            caller: caller.map(Arc::from),
            invocation,
            declared_owner: match &resolution {
                selector_jvm_resolve::Resolution::Found(member) => {
                    Some(Arc::from(member.declared_owner.as_str()))
                }
                _ => None,
            },
            resolution,
            next: self.member_heads.insert(key, id).unwrap_or(u32::MAX),
        });
        Ok(&self.members[id as usize])
    }
    /// Private issuer seam for the separately versioned standard bootstrap
    /// contract. A classpath class with the same name never satisfies this.
    pub(crate) fn declared_java21_class(
        &mut self,
        authority: u32,
        owner: &str,
    ) -> Result<(ProvidedClass, Hash), Error> {
        let (identity, entry) = self
            .declared_platform
            .ok_or(Error::Invalid("declared Java21 platform required"))?;
        if self.java_feature != Some(21) {
            return Err(Error::Invalid("declared Java21 platform required"));
        }
        let (bytes, receipt) = self.resolve(authority, owner)?;
        if receipt.state != ResolutionState::Found
            || receipt.provider != Some(entry as u32)
            || receipt.selected_entry != Some(0)
            || receipt.own_product.is_some()
        {
            return Err(Error::Invalid(
                "bootstrap class not selected from declared java.base",
            ));
        }
        Ok((
            ProvidedClass {
                bytes: bytes.ok_or(Error::Invalid("bootstrap class unavailable"))?,
                class_sha256: receipt
                    .class_sha256
                    .ok_or(Error::Invalid("bootstrap class hash"))?,
                authority,
                provider: entry as u32,
                binding_sha256: receipt.binding_sha256,
            },
            identity,
        ))
    }
    pub fn resolve(
        &mut self,
        authority: u32,
        owner: &str,
    ) -> Result<(Option<Arc<[u8]>>, Arc<ResolutionReceipt>), Error> {
        if owner.is_empty() || owner.len() > u16::MAX as usize {
            return Err(Error::Invalid("class owner bound"));
        }
        let inventory_limits = self.inventory_limits();
        let context = self
            .contexts
            .get_mut(authority as usize)
            .ok_or(Error::Invalid("unknown native authority"))?;
        if let Some(cached) = context.cache.get(owner) {
            return Ok((cached.bytes.clone(), cached.receipt.clone()));
        }
        if self.class_count >= self.limits.cached_classes {
            return Err(budget(
                "class_count",
                self.class_count.saturating_add(1),
                self.limits.cached_classes,
                Some(authority),
                Some(owner),
                (self.class_bytes, self.class_count),
            ));
        }
        if !self.inventory_only && context.loader.is_none() {
            let entries = context
                .entries
                .iter()
                .map(|&i| self.entries[i].clone())
                .collect();
            let snapshots: Vec<_> = context.entries.iter().map(|&i| &self.admitted[i]).collect();
            context.loader = Some(CapturedClasspath::from_admitted(
                entries,
                &snapshots,
                self.limits.binary,
                self.java_feature,
            )?);
        }
        let lookup = if self.inventory_only {
            inventory_lookup(
                &self.entries,
                &context.entries,
                inventory_limits,
                self.java_feature,
                owner,
            )
        } else {
            context.loader.as_mut().unwrap().lookup(owner)
        };
        let mut prefix = Sha256::new();
        let mut class_sha = None;
        let mut selected = None;
        let mut provider = None;
        let mut own_product = None;
        let (bytes, state, count) = match lookup {
            Ok(ClassLookup::Found(found)) => {
                for proof in &found.proof.examined {
                    prefix.update((proof.entry_index as u64).to_le_bytes());
                    prefix.update(proof.sha256.0);
                    prefix.update([u8::from(proof.absent)]);
                }
                let ordinal = found
                    .proof
                    .selected_entry
                    .ok_or(Error::Invalid("selected provider missing"))?;
                let global = context.entries[ordinal];
                let sha = found
                    .proof
                    .class_hash
                    .ok_or(Error::Invalid("selected class hash missing"))?
                    .0;
                selected = Some(ordinal as u32);
                provider = Some(global as u32);
                class_sha = Some(sha);
                let bytes = if context.own_entry == Some(global) {
                    if let Some(&class) = context.own.get(owner) {
                        let products = self
                            .products
                            .ok_or(Error::Invalid("compiled proof missing"))?;
                        let view = products
                            .class(class)
                            .ok_or(Error::Invalid("compiled class missing"))?;
                        if view.class_sha256 != sha {
                            return Err(Error::Invalid("compiled first-provider class mismatch"));
                        }
                        own_product = Some(class);
                        products
                            .class_bytes_arc(class)
                            .ok_or(Error::Invalid("compiled class bytes missing"))?
                    } else {
                        Arc::from(found.bytes)
                    }
                } else {
                    Arc::from(found.bytes)
                };
                (
                    Some(bytes),
                    ResolutionState::Found,
                    found.proof.examined.len() as u32,
                )
            }
            Ok(ClassLookup::Absent(proof)) => {
                for row in &proof.examined {
                    prefix.update((row.entry_index as u64).to_le_bytes());
                    prefix.update(row.sha256.0);
                    prefix.update([u8::from(row.absent)]);
                }
                (
                    None,
                    ResolutionState::VerifiedClasspathMiss,
                    proof.examined.len() as u32,
                )
            }
            Err(error) if provenance_failure(error.kind) => return Err(error.into()),
            Err(error) if self.inventory_only && error.kind == binary::ErrorKind::ResourceLimit => {
                eprintln!(
                    "{}",
                    serde_json::json!({
                        "event":"native_provider_budget", "phase":"inventory_binary_limit",
                        "authority":authority, "owner":owner, "binary_offset":error.offset,
                        "max_retained_bytes":inventory_limits.max_retained_bytes,
                        "max_archive_bytes":inventory_limits.max_archive_bytes,
                        "max_class_bytes":inventory_limits.max_class_bytes,
                        "max_directory_files":inventory_limits.max_directory_files,
                        "max_directory_bytes":inventory_limits.max_directory_bytes,
                        "cached_class_bytes":self.class_bytes, "cached_class_count":self.class_count
                    })
                );
                return Err(Error::Budget);
            }
            Err(error) => {
                prefix.update(format!("{:?}", error.kind).as_bytes());
                (None, ResolutionState::OpaquePrefix, 0)
            }
        };
        // Cache owns one owner string and bounded proof metadata per distinct
        // lookup, including misses. No unbounded negative-entry side table.
        let charge = bytes.as_ref().map_or(0, |b| b.len()) + owner.len() + 256;
        let proposed_bytes = self.class_bytes.checked_add(charge).ok_or_else(|| {
            budget(
                "class_cache_bytes_overflow",
                usize::MAX,
                self.limits.cached_class_bytes,
                Some(authority),
                Some(owner),
                (self.class_bytes, self.class_count),
            )
        })?;
        if proposed_bytes > self.limits.cached_class_bytes {
            return Err(budget(
                "class_cache_bytes",
                proposed_bytes,
                self.limits.cached_class_bytes,
                Some(authority),
                Some(owner),
                (self.class_bytes, self.class_count),
            ));
        }
        self.class_bytes = proposed_bytes;
        let prefix_sha256: Hash = prefix.finalize().into();
        let mut binding = Sha256::new();
        binding.update(self.identity);
        binding.update(self.capture);
        binding.update(self.map);
        binding.update(authority.to_le_bytes());
        binding.update((owner.len() as u64).to_le_bytes());
        binding.update(owner.as_bytes());
        binding.update(prefix_sha256);
        binding.update(selected.unwrap_or(u32::MAX).to_le_bytes());
        binding.update(class_sha.unwrap_or_default());
        let receipt = Arc::new(ResolutionReceipt {
            authority,
            owner: Arc::from(owner),
            state,
            selected_entry: selected,
            provider,
            class_sha256: class_sha,
            examined_prefix: count,
            prefix_sha256,
            binding_sha256: binding.finalize().into(),
            own_product,
        });
        context.cache.insert(
            receipt.owner.clone(),
            Cached {
                bytes: bytes.clone(),
                receipt: receipt.clone(),
                metadata: None,
            },
        );
        self.class_count += 1;
        Ok((bytes, receipt))
    }
}
impl ClassProvider for VerifiedProvider<'_> {
    fn declaration(
        &mut self,
        authority: u32,
        member: binary::MemberRef<'_>,
        kind: binary::InvokeKind,
        caller: Option<&str>,
    ) -> Result<Option<Arc<str>>, crate::Error> {
        let invocation = match kind {
            binary::InvokeKind::Static => MemberInvocation::Static,
            binary::InvokeKind::Special => MemberInvocation::Special,
            binary::InvokeKind::Virtual => MemberInvocation::Virtual,
            binary::InvokeKind::Interface => MemberInvocation::Interface,
        };
        let result = self
            .resolve_member(authority, member, invocation, caller)
            .map_err(|e| crate::Error::Provider(Box::new(e)))?;
        Ok(result.declared_owner.clone())
    }
    fn class(&mut self, demand: ClassDemand<'_>) -> Result<Option<ProvidedClass>, crate::Error> {
        let (bytes, proof) = self
            .resolve(demand.authority, demand.owner)
            .map_err(|e| crate::Error::Provider(Box::new(e)))?;
        Ok(bytes.map(|bytes| ProvidedClass {
            bytes,
            class_sha256: proof.class_sha256.expect("found hash"),
            authority: demand.authority,
            provider: proof.provider.expect("found provider"),
            binding_sha256: proof.binding_sha256,
        }))
    }
}
