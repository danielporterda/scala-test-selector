//! Compiler-context-bound, immutable external metadata providers.
//!
//! A binary map supplies physical locations and conservative unavailable rows;
//! its compiler-symbol mappings never establish classpath authority. The exact
//! original compiler capture, pinned by the prepared extraction owner, does.
use flate2::read::MultiGzDecoder;
use selector_extract::external_metadata::{MetadataProviderAuthority, ProviderResolution};
use selector_models::binary::{
    AdmittedEntry, CapturedClasspath, ClassLookup, ClasspathEntry, EntryKind, EntryProof, Limits,
};
use selector_types::{ContentHash, Error};
use serde::de::IgnoredAny;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, HashMap};
use std::fs::{Metadata, OpenOptions};
use std::io::Read;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::{Component, Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

#[derive(Clone, Debug)]
pub struct AuthorityLimits {
    pub max_manifest_bytes: usize,
    pub max_contexts: usize,
    pub max_entries_per_context: usize,
    pub max_total_entries: usize,
    pub max_unique_entries: usize,
    pub max_name_bytes: usize,
    pub max_retained_input_bytes: usize,
    /// Class payloads, compact memo rows, and bounded concurrent lookup scratch.
    pub max_cached_bytes: usize,
    pub max_cached_lookups: usize,
    pub binary: Limits,
}
impl Default for AuthorityLimits {
    fn default() -> Self {
        Self {
            max_manifest_bytes: 64 * 1024 * 1024,
            max_contexts: 1024,
            max_entries_per_context: 65_535,
            max_total_entries: 1_000_000,
            max_unique_entries: 65_535,
            max_name_bytes: 4096,
            max_retained_input_bytes: 768 * 1024 * 1024,
            max_cached_bytes: 256 * 1024 * 1024,
            max_cached_lookups: 200_000,
            binary: Limits::default(),
        }
    }
}

/// Physical provenance is separate from the semantic ordered-classpath key.
#[derive(Debug, Serialize)]
pub struct AuthorityReceipt {
    pub schema: &'static str,
    pub contexts_path: PathBuf,
    pub contexts_sha256: String,
    pub binary_map_path: PathBuf,
    pub binary_map_sha256: String,
    pub authority_sha256: String,
    pub relocated_root: PathBuf,
    pub retained_input_bytes: usize,
    pub entries: Vec<ProviderLocation>,
}
#[derive(Debug, Serialize)]
pub struct ProviderLocation {
    pub captured_path: String,
    pub physical_path: PathBuf,
    pub sha256: String,
    pub kind: &'static str,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct BinaryMap {
    version: u32,
    revision: Option<String>,
    // These fields intentionally do not participate in provider authority.
    facts_identity: Option<IgnoredAny>,
    #[serde(default)]
    types: Option<IgnoredAny>,
    methods: IgnoredAny,
    java_feature: Option<u16>,
    contexts: Vec<MapContext>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct MapContext {
    id: String,
    entries: Vec<MapEntry>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct MapEntry {
    path: PathBuf,
    sha256: Option<String>,
    kind: String,
    files: Option<u64>,
    bytes: Option<u64>,
}
#[derive(Deserialize)]
struct Capture {
    schema_version: String,
    revision: String,
    source_root: PathBuf,
    #[serde(default)]
    errors: Vec<IgnoredAny>,
    contexts: Vec<CapturedContext>,
    input_objects: Vec<CapturedObject>,
    java_runtime: Option<JavaRuntime>,
}
#[derive(Deserialize)]
struct JavaRuntime {
    java_version: String,
}
#[derive(Deserialize)]
struct CapturedContext {
    context_id: String,
    source_revision: Option<String>,
    compiler_environment_fingerprint: String,
    full_classpath: Vec<CapturedInput>,
    #[serde(default)]
    java_options: Vec<String>,
    java_home: Option<PathBuf>,
}
#[derive(Deserialize)]
struct CapturedInput {
    index: usize,
    path: String,
    input_object: Option<String>,
    sha256: Option<String>,
}
#[derive(Deserialize)]
struct CapturedObject {
    path: String,
    kind: String,
    sha256: String,
    files: Option<u64>,
    bytes: u64,
}

#[derive(Clone)]
enum Memo {
    Absent,
    Found {
        index: u32,
        sha256: ContentHash,
        bytes: Arc<[u8]>,
    },
}
impl Memo {
    fn resolution(&self, classpath: ContentHash) -> Option<ProviderResolution> {
        match self {
            Self::Absent => None,
            Self::Found {
                index,
                sha256,
                bytes,
            } => Some(ProviderResolution {
                classpath_identity: classpath,
                provider_index: *index,
                provider_sha256: *sha256,
                class_bytes: bytes.clone(),
            }),
        }
    }
}
struct ContextState {
    loader: CapturedClasspath,
    memo: HashMap<String, Memo>,
}
struct Context {
    identity: ContentHash,
    state: Mutex<ContextState>,
}

struct Budget {
    used: AtomicUsize,
    limit: usize,
}
struct Reservation<'a> {
    budget: &'a Budget,
    bytes: usize,
}
impl Budget {
    fn reserve(&self, bytes: usize) -> Result<Reservation<'_>, Error> {
        self.used
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |used| {
                used.checked_add(bytes).filter(|&total| total <= self.limit)
            })
            .map_err(|_| Error::Limit("metadata authority cache"))?;
        Ok(Reservation {
            budget: self,
            bytes,
        })
    }
}
impl Reservation<'_> {
    fn retain(mut self, bytes: usize) {
        debug_assert!(bytes <= self.bytes);
        self.budget
            .used
            .fetch_sub(self.bytes - bytes, Ordering::Relaxed);
        self.bytes = 0;
    }
}
impl Drop for Reservation<'_> {
    fn drop(&mut self) {
        self.budget.used.fetch_sub(self.bytes, Ordering::Relaxed);
    }
}

pub struct CapturedMetadataAuthority {
    identity: ContentHash,
    contexts_identity: ContentHash,
    contexts: HashMap<String, Context>,
    // Owners are shared by exact path/hash/kind/runtime across every context.
    _admitted: Vec<AdmittedEntry>,
    payloads: Mutex<HashMap<ContentHash, Arc<[u8]>>>,
    cache_budget: Budget,
    lookup_budget: Budget,
    limits: AuthorityLimits,
    receipt: AuthorityReceipt,
}
impl CapturedMetadataAuthority {
    pub fn open(
        binary_map: &Path,
        contexts: &Path,
        expected_contexts_identity: ContentHash,
        relocated_root: &Path,
        limits: &AuthorityLimits,
    ) -> Result<Self, Error> {
        validate_limits(limits)?;
        let raw_capture = read_regular(contexts, limits.max_manifest_bytes)?;
        let contexts_identity = hash(&raw_capture);
        if contexts_identity != expected_contexts_identity {
            return Err(Error::Invalid("metadata original compiler-context pin"));
        }
        let expanded;
        let capture_bytes = if contexts
            .extension()
            .is_some_and(|extension| extension == "gz")
        {
            expanded = read_bounded(
                MultiGzDecoder::new(raw_capture.as_slice()),
                limits.max_manifest_bytes,
            )?;
            expanded.as_slice()
        } else {
            raw_capture.as_slice()
        };
        let capture: Capture = serde_json::from_slice(capture_bytes).map_err(json_error)?;
        let map_bytes = read_regular(binary_map, limits.max_manifest_bytes)?;
        let map: BinaryMap = serde_json::from_slice(&map_bytes).map_err(json_error)?;
        let _ = (&map.facts_identity, &map.types, &map.methods);
        if capture.schema_version != "sbt-compiler-context/v1"
            || !capture.errors.is_empty()
            || capture.revision.is_empty()
            || map.version != 1
            || map.revision.as_deref() != Some(&capture.revision)
        {
            return Err(Error::Invalid("metadata capture schema/revision"));
        }
        absolute_normal(&capture.source_root)?;
        if capture.contexts.len() > limits.max_contexts
            || map.contexts.len() > limits.max_contexts
            || capture.input_objects.len() > limits.max_unique_entries
        {
            return Err(Error::Limit("metadata compiler contexts/objects"));
        }
        let java_feature = capture
            .java_runtime
            .as_ref()
            .map(|runtime| java_feature(&runtime.java_version))
            .transpose()?;
        if map.java_feature != java_feature {
            return Err(Error::Invalid("metadata captured Java runtime"));
        }
        let root = std::fs::canonicalize(relocated_root)?;
        absolute_normal(&root)?;
        let mut objects = HashMap::new();
        for object in &capture.input_objects {
            absolute_normal(Path::new(&object.path))?;
            ContentHash::from_hex(&object.sha256)?;
            if objects.insert(object.path.as_str(), object).is_some() {
                return Err(Error::Invalid("duplicate metadata capture object"));
            }
        }
        let mut captured_contexts = HashMap::new();
        let mut total = 0usize;
        for context in &capture.contexts {
            valid_context(&context.context_id, limits)?;
            if context.source_revision.as_deref() != Some(&capture.revision) {
                return Err(Error::Invalid("metadata compiler context source revision"));
            }
            ContentHash::from_hex(&context.compiler_environment_fingerprint)?;
            if context.java_home.is_some()
                || context.java_options.iter().any(|option| {
                    option.starts_with("-Djdk.util.jar.version")
                        || option.starts_with("-Djdk.util.jar.enableMultiRelease")
                })
            {
                return Err(Error::Invalid("metadata captured Java override"));
            }
            total = total
                .checked_add(context.full_classpath.len())
                .ok_or(Error::Limit("metadata classpath entries"))?;
            if context.full_classpath.len() > limits.max_entries_per_context
                || total > limits.max_total_entries
            {
                return Err(Error::Limit("metadata classpath entries"));
            }
            if captured_contexts
                .insert(context.context_id.as_str(), context)
                .is_some()
            {
                return Err(Error::Invalid("duplicate metadata captured context"));
            }
            for (index, input) in context.full_classpath.iter().enumerate() {
                if input.index != index {
                    return Err(Error::Invalid("metadata captured classpath order"));
                }
                absolute_normal(Path::new(&input.path))?;
                let object = objects
                    .get(input.input_object.as_deref().unwrap_or(&input.path))
                    .ok_or(Error::Invalid("metadata classpath object absent"))?;
                if input
                    .sha256
                    .as_deref()
                    .map(ContentHash::from_hex)
                    .transpose()?
                    != Some(ContentHash::from_hex(&object.sha256)?)
                {
                    return Err(Error::Invalid("metadata classpath object digest"));
                }
            }
        }
        let base = std::fs::canonicalize(binary_map.parent().unwrap_or(Path::new(".")))?;
        let mut pending = BTreeMap::new();
        let mut unique = HashMap::new();
        let mut entries = Vec::new();
        let mut locations = Vec::new();
        for context in map.contexts {
            valid_context(&context.id, limits)?;
            let captured = captured_contexts
                .get(context.id.as_str())
                .ok_or(Error::Invalid("metadata map context absent from capture"))?;
            if context.entries.len() != captured.full_classpath.len() {
                return Err(Error::Invalid("metadata map classpath length"));
            }
            let mut cp_hash = Sha256::new();
            cp_hash.update(b"selector-metadata-classpath/v1\0");
            cp_hash.update(java_feature.unwrap_or(0).to_le_bytes());
            cp_hash.update((context.entries.len() as u64).to_le_bytes());
            let mut at = Vec::with_capacity(context.entries.len());
            for (mapped, input) in context.entries.into_iter().zip(&captured.full_classpath) {
                let captured_path = input.input_object.as_deref().unwrap_or(&input.path);
                let object = objects[captured_path];
                let expected_path =
                    relocate(Path::new(captured_path), &capture.source_root, &root)?;
                let path = if mapped.path.is_absolute() {
                    mapped.path
                } else {
                    base.join(mapped.path)
                };
                absolute_normal(&path)?;
                if path != expected_path {
                    return Err(Error::Invalid("metadata map provider path"));
                }
                let digest = ContentHash::from_hex(&object.sha256)?;
                if mapped
                    .sha256
                    .as_deref()
                    .map(ContentHash::from_hex)
                    .transpose()?
                    != Some(digest)
                {
                    return Err(Error::Invalid("metadata map provider digest"));
                }
                let (kind, label) =
                    bound_kind(&mapped.kind, mapped.files, mapped.bytes, object, &path)?;
                cp_hash.update([kind_tag(kind)]);
                cp_hash.update(digest.0);
                cp_hash.update(object.files.unwrap_or(u64::MAX).to_le_bytes());
                cp_hash.update(object.bytes.to_le_bytes());
                let entry = ClasspathEntry {
                    path: path.clone(),
                    sha256: digest,
                    kind,
                };
                let index = if let Some(&index) = unique.get(&entry) {
                    index
                } else {
                    if entries.len() == limits.max_unique_entries {
                        return Err(Error::Limit("metadata unique providers"));
                    }
                    let index = entries.len();
                    unique.insert(entry.clone(), index);
                    locations.push(ProviderLocation {
                        captured_path: captured_path.to_owned(),
                        physical_path: path,
                        sha256: digest.to_string(),
                        kind: label,
                    });
                    entries.push(entry);
                    index
                };
                at.push(index);
            }
            let identity = ContentHash(cp_hash.finalize().into());
            if pending.insert(context.id, (identity, at)).is_some() {
                return Err(Error::Invalid("duplicate metadata map context"));
            }
        }
        let mut admitted = Vec::with_capacity(entries.len());
        let mut retained = 0usize;
        for entry in &entries {
            let mut binary_limits = limits.binary;
            let (reservation, _) =
                AdmittedEntry::reservation_bytes(entry, binary_limits).map_err(binary_error)?;
            if reservation > limits.max_retained_input_bytes.saturating_sub(retained) {
                return Err(Error::Limit("metadata shared provider bytes"));
            }
            binary_limits.max_retained_bytes = reservation;
            let owner = AdmittedEntry::admit(entry.clone(), binary_limits, java_feature)
                .map_err(binary_error)?;
            if !matches!(entry.kind, EntryKind::Unavailable) {
                if let Some(error) = owner.error() {
                    return Err(binary_error(error));
                }
            }
            retained = retained
                .checked_add(owner.retained_bytes())
                .ok_or(Error::Limit("metadata shared provider bytes"))?;
            admitted.push(owner);
        }
        let mut authority_hash = Sha256::new();
        authority_hash.update(b"selector-metadata-authority/v1\0");
        authority_hash.update((pending.len() as u64).to_le_bytes());
        let mut context_states = HashMap::new();
        for (name, (identity, indices)) in pending {
            hash_string(&mut authority_hash, &name);
            authority_hash.update(identity.0);
            let snapshots: Vec<_> = indices.iter().map(|&index| &admitted[index]).collect();
            let ordered = indices
                .iter()
                .map(|&index| entries[index].clone())
                .collect();
            let loader =
                CapturedClasspath::from_admitted(ordered, &snapshots, limits.binary, java_feature)
                    .map_err(binary_error)?;
            context_states.insert(
                name,
                Context {
                    identity,
                    state: Mutex::new(ContextState {
                        loader,
                        memo: HashMap::new(),
                    }),
                },
            );
        }
        let identity = ContentHash(authority_hash.finalize().into());
        Ok(Self {
            identity,
            contexts_identity,
            contexts: context_states,
            _admitted: admitted,
            payloads: Mutex::new(HashMap::new()),
            cache_budget: Budget {
                used: AtomicUsize::new(0),
                limit: limits.max_cached_bytes,
            },
            lookup_budget: Budget {
                used: AtomicUsize::new(0),
                limit: limits.max_cached_lookups,
            },
            limits: limits.clone(),
            receipt: AuthorityReceipt {
                schema: "captured-metadata-authority/v1",
                contexts_path: contexts.to_path_buf(),
                contexts_sha256: contexts_identity.to_string(),
                binary_map_path: binary_map.to_path_buf(),
                binary_map_sha256: hash(&map_bytes).to_string(),
                authority_sha256: identity.to_string(),
                relocated_root: root,
                retained_input_bytes: retained,
                entries: locations,
            },
        })
    }
    pub fn receipt(&self) -> &AuthorityReceipt {
        &self.receipt
    }
}
impl MetadataProviderAuthority for CapturedMetadataAuthority {
    fn identity(&self) -> ContentHash {
        self.identity
    }
    fn contexts_identity(&self) -> ContentHash {
        self.contexts_identity
    }
    fn resolve(
        &self,
        context: &str,
        outer_class: &str,
    ) -> Result<Option<ProviderResolution>, Error> {
        valid_context(context, &self.limits)?;
        valid_class(outer_class, &self.limits)?;
        let context = self
            .contexts
            .get(context)
            .ok_or(Error::Invalid("metadata requested context absent"))?;
        let mut state = context
            .state
            .lock()
            .map_err(|_| Error::Invalid("metadata context lock"))?;
        if let Some(memo) = state.memo.get(outer_class) {
            return Ok(memo.resolution(context.identity));
        }
        let count = self.lookup_budget.reserve(1)?;
        // Covers Vec->Arc copying and memo/hash-table overhead before any lookup.
        let scratch = self
            .limits
            .binary
            .max_class_bytes
            .checked_mul(2)
            .and_then(|bytes| {
                bytes.checked_add(
                    state
                        .loader
                        .entries
                        .len()
                        .checked_mul(2 * std::mem::size_of::<EntryProof>())?,
                )
            })
            .and_then(|bytes| bytes.checked_add(outer_class.len() + 1024))
            .ok_or(Error::Limit("metadata class cache reservation"))?;
        let reservation = self.cache_budget.reserve(scratch)?;
        state
            .memo
            .try_reserve(1)
            .map_err(|_| Error::Limit("metadata lookup memo"))?;
        let mut retained = outer_class.len() + 256;
        let memo = match state.loader.lookup(outer_class).map_err(binary_error)? {
            ClassLookup::Absent(_) => Memo::Absent,
            ClassLookup::Found(found) => {
                let selected = found
                    .proof
                    .selected_entry
                    .ok_or(Error::Invalid("metadata selected provider absent"))?;
                let digest = found
                    .proof
                    .class_hash
                    .ok_or(Error::Invalid("metadata selected class digest absent"))?;
                let provider = state
                    .loader
                    .entries
                    .get(selected)
                    .ok_or(Error::Invalid("metadata selected provider bounds"))?;
                let provider_sha256 = provider.sha256;
                // The cold preceding-entry proof is deliberately not retained.
                drop(found.proof);
                let mut payloads = self
                    .payloads
                    .lock()
                    .map_err(|_| Error::Invalid("metadata payload lock"))?;
                let bytes = if let Some(bytes) = payloads.get(&digest) {
                    bytes.clone()
                } else {
                    payloads
                        .try_reserve(1)
                        .map_err(|_| Error::Limit("metadata shared class payloads"))?;
                    retained += found.bytes.len() + 256;
                    let bytes: Arc<[u8]> = found.bytes.into();
                    payloads.insert(digest, bytes.clone());
                    bytes
                };
                Memo::Found {
                    index: u32::try_from(selected)
                        .map_err(|_| Error::Limit("metadata provider index"))?,
                    sha256: provider_sha256,
                    bytes,
                }
            }
        };
        let result = memo.resolution(context.identity);
        state.memo.insert(outer_class.to_owned(), memo);
        reservation.retain(retained);
        count.retain(1);
        Ok(result)
    }
}

fn validate_limits(limits: &AuthorityLimits) -> Result<(), Error> {
    if limits.max_manifest_bytes == 0
        || limits.max_manifest_bytes > 64 * 1024 * 1024
        || limits.max_contexts == 0
        || limits.max_contexts > 1024
        || limits.max_entries_per_context > 65_535
        || limits.max_total_entries == 0
        || limits.max_unique_entries == 0
        || limits.max_name_bytes == 0
        || limits.max_retained_input_bytes == 0
        || limits.max_cached_bytes == 0
        || limits.max_cached_lookups == 0
        || limits.binary.max_class_bytes == 0
    {
        return Err(Error::Invalid("metadata authority limits"));
    }
    Ok(())
}
fn valid_context(context: &str, limits: &AuthorityLimits) -> Result<(), Error> {
    if context.is_empty() || context.contains('\0') || context.len() > limits.max_name_bytes {
        return Err(Error::Invalid("metadata exact compiler context"));
    }
    Ok(())
}
fn valid_class(name: &str, limits: &AuthorityLimits) -> Result<(), Error> {
    if name.len() > limits.max_name_bytes
        || name.is_empty()
        || name
            .split('/')
            .any(|part| part.is_empty() || part == "." || part == "..")
        || name
            .bytes()
            .any(|byte| matches!(byte, 0 | b'\\' | b'.' | b';' | b'['))
    {
        return Err(Error::Invalid("metadata class name"));
    }
    Ok(())
}
fn absolute_normal(path: &Path) -> Result<(), Error> {
    if !path.is_absolute()
        || path.as_os_str().as_encoded_bytes().contains(&0)
        || path
            .components()
            .any(|part| !matches!(part, Component::RootDir | Component::Normal(_)))
    {
        return Err(Error::Invalid("metadata absolute provider path"));
    }
    Ok(())
}
fn relocate(path: &Path, original: &Path, relocated: &Path) -> Result<PathBuf, Error> {
    absolute_normal(path)?;
    Ok(if let Ok(relative) = path.strip_prefix(original) {
        relocated.join(relative)
    } else {
        path.to_path_buf()
    })
}
fn bound_kind(
    mapped: &str,
    files: Option<u64>,
    bytes: Option<u64>,
    original: &CapturedObject,
    path: &Path,
) -> Result<(EntryKind, &'static str), Error> {
    match mapped {
        "unavailable" if files.is_none() && bytes.is_none() => {
            Ok((EntryKind::Unavailable, "unavailable"))
        }
        "jar"
            if original.kind == "file"
                && path.extension().is_some_and(|extension| extension == "jar")
                && files.is_none()
                && bytes.is_none() =>
        {
            if std::fs::metadata(path)?.len() != original.bytes {
                return Err(Error::Invalid("metadata captured archive size"));
            }
            Ok((EntryKind::Jar, "jar"))
        }
        "directory"
            if original.kind == "directory"
                && files == original.files
                && bytes == Some(original.bytes) =>
        {
            Ok((
                EntryKind::Directory {
                    files: files.ok_or(Error::Invalid("metadata captured directory count"))?,
                    bytes: original.bytes,
                },
                "directory",
            ))
        }
        "absent_empty_output"
            if original.kind == "absent_empty_project_output"
                && files.is_none()
                && bytes.is_none() =>
        {
            Ok((EntryKind::AbsentEmptyOutput, "absent_empty_output"))
        }
        _ => Err(Error::Invalid("metadata map/capture provider kind")),
    }
}
fn kind_tag(kind: EntryKind) -> u8 {
    match kind {
        EntryKind::Jar => 1,
        EntryKind::Directory { .. } => 2,
        EntryKind::AbsentEmptyOutput => 3,
        EntryKind::Unavailable => 4,
    }
}
fn java_feature(version: &str) -> Result<u16, Error> {
    let version = version.strip_prefix("1.").unwrap_or(version);
    version
        .split(['.', '-', '+'])
        .next()
        .and_then(|part| part.parse::<u16>().ok())
        .filter(|&version| version > 0 && version <= 255)
        .ok_or(Error::Invalid("metadata Java feature version"))
}
fn read_regular(path: &Path, limit: usize) -> Result<Vec<u8>, Error> {
    let before = std::fs::symlink_metadata(path)?;
    if !before.is_file() || before.file_type().is_symlink() {
        return Err(Error::Invalid("metadata regular manifest file"));
    }
    if before.len() > limit as u64 {
        return Err(Error::Limit("metadata manifest bytes"));
    }
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)?;
    if !same_file(&before, &file.metadata()?) {
        return Err(Error::Invalid("metadata manifest changed before read"));
    }
    let bytes = read_bounded(&mut file, limit)?;
    let after = file.metadata()?;
    if before.len() != bytes.len() as u64
        || !same_file(&before, &after)
        || !same_file(&before, &std::fs::symlink_metadata(path)?)
    {
        return Err(Error::Invalid("metadata manifest changed during read"));
    }
    Ok(bytes)
}
fn same_file(before: &Metadata, after: &Metadata) -> bool {
    after.is_file()
        && !after.file_type().is_symlink()
        && before.dev() == after.dev()
        && before.ino() == after.ino()
        && before.len() == after.len()
        && before.mtime() == after.mtime()
        && before.mtime_nsec() == after.mtime_nsec()
        && before.ctime() == after.ctime()
        && before.ctime_nsec() == after.ctime_nsec()
}
fn read_bounded(reader: impl Read, limit: usize) -> Result<Vec<u8>, Error> {
    let mut bytes = Vec::new();
    reader.take(limit as u64 + 1).read_to_end(&mut bytes)?;
    if bytes.len() > limit {
        return Err(Error::Limit("metadata manifest bytes"));
    }
    Ok(bytes)
}
fn hash(bytes: &[u8]) -> ContentHash {
    ContentHash(Sha256::digest(bytes).into())
}
fn hash_string(hash: &mut Sha256, string: &str) {
    hash.update((string.len() as u64).to_le_bytes());
    hash.update(string.as_bytes());
}
fn json_error(error: serde_json::Error) -> Error {
    Error::Message(format!("metadata authority JSON: {error}"))
}
fn binary_error(error: selector_models::binary::BinaryError) -> Error {
    Error::Message(error.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{Value, json};

    struct Fixture {
        _directory: tempfile::TempDir,
        root: PathBuf,
        contexts: PathBuf,
        map: PathBuf,
        capture: Value,
        manifest: Value,
    }
    impl Fixture {
        fn new() -> Self {
            let directory = tempfile::tempdir().unwrap();
            let root = std::fs::canonicalize(directory.path()).unwrap();
            std::fs::create_dir(root.join("lib")).unwrap();
            let library = include_bytes!("../../../fixtures/selected-external-apply/library.jar");
            std::fs::write(root.join("lib/library.jar"), library).unwrap();
            let digest = hash(library).to_string();
            let capture = json!({"schema_version":"sbt-compiler-context/v1","revision":"r",
                "source_root":"/captured/source","errors":[],"java_runtime":{"java_version":"17.0.1"},
                "contexts":[{"context_id":"a","source_revision":"r","compiler_environment_fingerprint":hash(b"environment").to_string(),
                    "full_classpath":[{"index":0,"path":"/captured/source/lib/library.jar","sha256":digest}]}],
                "input_objects":[{"path":"/captured/source/lib/library.jar","kind":"file","sha256":digest,"bytes":library.len()}]});
            let manifest = json!({"version":1,"revision":"r","facts_identity":hash(b"facts").to_string(),"java_feature":17,
                "contexts":[{"id":"a","entries":[{"path":root.join("lib/library.jar"),"sha256":digest,"kind":"jar"}]}],"types":[],"methods":[]});
            let contexts = root.join("contexts.json");
            let map = root.join("binary-map.json");
            let fixture = Self {
                _directory: directory,
                root,
                contexts,
                map,
                capture,
                manifest,
            };
            fixture.save();
            fixture
        }
        fn save(&self) {
            std::fs::write(&self.contexts, serde_json::to_vec(&self.capture).unwrap()).unwrap();
            std::fs::write(&self.map, serde_json::to_vec(&self.manifest).unwrap()).unwrap();
        }
        fn pin(&self) -> ContentHash {
            hash(&std::fs::read(&self.contexts).unwrap())
        }
        fn open(&self) -> Result<CapturedMetadataAuthority, Error> {
            CapturedMetadataAuthority::open(
                &self.map,
                &self.contexts,
                self.pin(),
                &self.root,
                &AuthorityLimits::default(),
            )
        }
        fn add_context(&mut self, name: &str) {
            let mut captured = self.capture["contexts"][0].clone();
            captured["context_id"] = json!(name);
            self.capture["contexts"]
                .as_array_mut()
                .unwrap()
                .push(captured);
            let mut mapped = self.manifest["contexts"][0].clone();
            mapped["id"] = json!(name);
            self.manifest["contexts"]
                .as_array_mut()
                .unwrap()
                .push(mapped);
        }
        fn prepend_unavailable(&mut self) {
            let sha = hash(b"not captured").to_string();
            self.capture["input_objects"].as_array_mut().unwrap().push(json!({"path":"/captured/source/opaque","kind":"unavailable","sha256":sha,"bytes":0}));
            let entries = self.capture["contexts"][0]["full_classpath"]
                .as_array_mut()
                .unwrap();
            entries[0]["index"] = json!(1);
            entries.insert(
                0,
                json!({"index":0,"path":"/captured/source/opaque","sha256":sha}),
            );
            self.manifest["contexts"][0]["entries"]
                .as_array_mut()
                .unwrap()
                .insert(
                    0,
                    json!({"path":self.root.join("opaque"),"sha256":sha,"kind":"unavailable"}),
                );
        }
    }
    const CLASS: &str = "selectedexternal/Library";

    #[test]
    fn admitted_provider_is_owned_memoized_and_shared_across_exact_contexts() {
        let mut fixture = Fixture::new();
        fixture.add_context("b");
        fixture.save();
        let authority = fixture.open().unwrap();
        assert_eq!(authority._admitted.len(), 1);
        let first = authority.resolve("a", CLASS).unwrap().unwrap();
        assert_eq!(first.provider_index, 0);
        assert_eq!(
            first.provider_sha256,
            hash(include_bytes!(
                "../../../fixtures/selected-external-apply/library.jar"
            ))
        );
        assert_eq!(first.classpath_identity, authority.contexts["b"].identity);
        let charged = authority.cache_budget.used.load(Ordering::Relaxed);
        std::fs::write(
            fixture.root.join("lib/library.jar"),
            b"replaced after immutable admission",
        )
        .unwrap();
        for _ in 0..32 {
            let repeated = authority.resolve("a", CLASS).unwrap().unwrap();
            assert!(Arc::ptr_eq(&first.class_bytes, &repeated.class_bytes));
        }
        assert_eq!(charged, authority.cache_budget.used.load(Ordering::Relaxed));
        let other = authority.resolve("b", CLASS).unwrap().unwrap();
        assert!(Arc::ptr_eq(&first.class_bytes, &other.class_bytes));
        assert!(
            selector_models::binary::parse_class(&other.class_bytes, Limits::default()).is_ok()
        );
        assert_eq!(authority.lookup_budget.used.load(Ordering::Relaxed), 2);
        assert!(fixture.open().is_err());
    }

    #[test]
    fn earlier_unknown_never_permits_a_later_provider() {
        let mut fixture = Fixture::new();
        fixture.prepend_unavailable();
        fixture.save();
        let authority = fixture.open().unwrap();
        let error = authority.resolve("a", CLASS).err().unwrap().to_string();
        assert!(error.contains("UnavailableInput"), "{error}");
        assert_eq!(authority.lookup_budget.used.load(Ordering::Relaxed), 0);
        assert_eq!(authority.cache_budget.used.load(Ordering::Relaxed), 0);
        assert!(authority.payloads.lock().unwrap().is_empty());
    }

    #[test]
    fn known_earlier_absence_selects_exact_original_index_and_order_is_bound() {
        let mut fixture = Fixture::new();
        let digest = hash(b"{\"kind\":\"absent_empty_project_output\"}").to_string();
        fixture.capture["input_objects"].as_array_mut().unwrap().push(json!({"path":"/captured/source/not-yet-built","kind":"absent_empty_project_output","sha256":digest,"bytes":0}));
        let entries = fixture.capture["contexts"][0]["full_classpath"]
            .as_array_mut()
            .unwrap();
        entries[0]["index"] = json!(1);
        entries.insert(
            0,
            json!({"index":0,"path":"/captured/source/not-yet-built","sha256":digest}),
        );
        fixture.manifest["contexts"][0]["entries"].as_array_mut().unwrap().insert(0,json!({"path":fixture.root.join("not-yet-built"),"sha256":digest,"kind":"absent_empty_output"}));
        fixture.save();
        let original = fixture.open().unwrap();
        assert_eq!(
            original
                .resolve("a", CLASS)
                .unwrap()
                .unwrap()
                .provider_index,
            1
        );
        fixture.manifest["contexts"][0]["entries"]
            .as_array_mut()
            .unwrap()
            .reverse();
        fixture.save();
        assert!(fixture.open().is_err());
        let captured = fixture.capture["contexts"][0]["full_classpath"]
            .as_array_mut()
            .unwrap();
        captured.reverse();
        for (index, entry) in captured.iter_mut().enumerate() {
            entry["index"] = json!(index);
        }
        fixture.save();
        let reordered = fixture.open().unwrap();
        assert_ne!(original.identity(), reordered.identity());
        assert_eq!(
            reordered
                .resolve("a", CLASS)
                .unwrap()
                .unwrap()
                .provider_index,
            0
        );
    }

    #[test]
    fn an_unknown_after_the_selected_provider_does_not_erase_the_valid_prefix() {
        let mut fixture = Fixture::new();
        fixture.prepend_unavailable();
        fixture.manifest["contexts"][0]["entries"]
            .as_array_mut()
            .unwrap()
            .reverse();
        let captured = fixture.capture["contexts"][0]["full_classpath"]
            .as_array_mut()
            .unwrap();
        captured.reverse();
        for (index, entry) in captured.iter_mut().enumerate() {
            entry["index"] = json!(index);
        }
        fixture.save();
        let authority = fixture.open().unwrap();
        assert_eq!(
            authority
                .resolve("a", CLASS)
                .unwrap()
                .unwrap()
                .provider_index,
            0
        );
        assert!(authority.resolve("a", "absent/Type").is_err());
    }

    #[test]
    fn symlink_manifest_and_resource_exhaustion_are_rejected_before_resolution() {
        let mut fixture = Fixture::new();
        let alias = fixture.root.join("contexts-link.json");
        std::os::unix::fs::symlink(&fixture.contexts, &alias).unwrap();
        fixture.contexts = alias;
        assert!(fixture.open().is_err());
        fixture.contexts = fixture.root.join("contexts.json");
        let mut limits = AuthorityLimits::default();
        limits.max_cached_bytes = 1;
        let authority = CapturedMetadataAuthority::open(
            &fixture.map,
            &fixture.contexts,
            fixture.pin(),
            &fixture.root,
            &limits,
        )
        .unwrap();
        assert!(matches!(
            authority.resolve("a", CLASS),
            Err(Error::Limit(_))
        ));
        assert!(authority.payloads.lock().unwrap().is_empty());
        assert_eq!(authority.lookup_budget.used.load(Ordering::Relaxed), 0);
        assert_eq!(authority.cache_budget.used.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn semantic_identity_ignores_map_recipes_and_physical_relocation() {
        let first = Fixture::new();
        let original = first.open().unwrap();
        let mut moved = Fixture::new();
        moved.manifest["facts_identity"] = json!("ignored fact revision");
        moved.manifest["types"] = json!([{"unconsumed":"mapping"}]);
        moved.manifest["methods"] = json!([{"arbitrary":"recipe"}]);
        moved.capture["source_root"] = json!("/other/captured");
        moved.capture["input_objects"][0]["path"] = json!("/other/captured/lib/library.jar");
        moved.capture["contexts"][0]["full_classpath"][0]["path"] =
            json!("/other/captured/lib/library.jar");
        moved.save();
        let relocated = moved.open().unwrap();
        assert_eq!(original.identity(), relocated.identity());
        assert_ne!(original.contexts_identity(), relocated.contexts_identity());
        assert_ne!(
            original.receipt().binary_map_sha256,
            relocated.receipt().binary_map_sha256
        );
        assert_ne!(
            original.receipt().entries[0].physical_path,
            relocated.receipt().entries[0].physical_path
        );
    }

    #[test]
    fn context_publication_order_is_not_semantic_but_runtime_and_entry_order_are() {
        let mut fixture = Fixture::new();
        fixture.add_context("b");
        fixture.save();
        let original = fixture.open().unwrap().identity();
        fixture.manifest["contexts"]
            .as_array_mut()
            .unwrap()
            .reverse();
        fixture.save();
        assert_eq!(original, fixture.open().unwrap().identity());
        fixture.capture["java_runtime"]["java_version"] = json!("21.0.1");
        fixture.manifest["java_feature"] = json!(21);
        fixture.save();
        assert_ne!(original, fixture.open().unwrap().identity());
        fixture.capture["java_runtime"]["java_version"] = json!("17.0.1");
        fixture.save();
        assert!(fixture.open().is_err());
    }

    #[test]
    fn original_capture_pin_is_required_including_the_gzip_container() {
        use std::io::Write;
        let mut fixture = Fixture::new();
        let raw_pin = fixture.pin();
        let mut gzip = flate2::write::GzEncoder::new(Vec::new(), flate2::Compression::default());
        gzip.write_all(&std::fs::read(&fixture.contexts).unwrap())
            .unwrap();
        let compressed = gzip.finish().unwrap();
        fixture.contexts = fixture.root.join("contexts.json.gz");
        std::fs::write(&fixture.contexts, &compressed).unwrap();
        let authority = fixture.open().unwrap();
        assert_eq!(authority.contexts_identity(), hash(&compressed));
        assert!(
            CapturedMetadataAuthority::open(
                &fixture.map,
                &fixture.contexts,
                raw_pin,
                &fixture.root,
                &AuthorityLimits::default()
            )
            .is_err()
        );
        let mut limited = AuthorityLimits::default();
        limited.max_manifest_bytes = compressed.len();
        assert!(
            CapturedMetadataAuthority::open(
                &fixture.map,
                &fixture.contexts,
                hash(&compressed),
                &fixture.root,
                &limited
            )
            .is_err()
        );
    }

    #[test]
    fn forged_map_order_hash_kind_count_path_and_context_are_rejected() {
        for case in 0..8 {
            let mut fixture = Fixture::new();
            match case {
                0 => {
                    fixture.manifest["contexts"][0]["entries"][0]["sha256"] =
                        json!(hash(b"wrong").to_string())
                }
                1 => {
                    fixture.manifest["contexts"][0]["entries"][0]["kind"] =
                        json!("absent_empty_output")
                }
                2 => {
                    fixture.manifest["contexts"][0]["entries"][0]["path"] =
                        json!(fixture.root.join("other.jar"))
                }
                3 => fixture.manifest["contexts"][0]["entries"][0]["files"] = json!(1),
                4 => fixture.manifest["contexts"][0]["id"] = json!("forged"),
                5 => fixture.capture["contexts"][0]["full_classpath"][0]["index"] = json!(1),
                6 => {
                    fixture.capture["contexts"][0]["full_classpath"][0]["sha256"] =
                        json!(hash(b"wrong").to_string())
                }
                7 => fixture.manifest["contexts"][0]["entries"] = json!([]),
                _ => unreachable!(),
            }
            fixture.save();
            assert!(fixture.open().is_err(), "case {case}");
        }
    }

    #[test]
    fn duplicate_or_composite_contexts_and_unsupported_java_overrides_are_rejected() {
        for case in 0..5 {
            let mut fixture = Fixture::new();
            match case {
                0 => fixture.add_context("a"),
                1 => fixture.add_context("a\0b"),
                2 => {
                    fixture.capture["contexts"][0]["java_options"] =
                        json!(["-Djdk.util.jar.version=8"])
                }
                3 => fixture.capture["contexts"][0]["java_home"] = json!("/other/jdk"),
                4 => fixture.capture["contexts"][0]["source_revision"] = json!("other"),
                _ => unreachable!(),
            }
            fixture.save();
            assert!(fixture.open().is_err(), "case {case}");
        }
        let authority = Fixture::new().open().unwrap();
        assert!(authority.resolve("a\0b", CLASS).is_err());
        assert!(authority.resolve("missing", CLASS).is_err());
        assert!(authority.resolve("a", "../outside").is_err());
    }

    #[test]
    fn absent_answers_are_memoized_and_limits_never_become_absence() {
        let fixture = Fixture::new();
        let mut limits = AuthorityLimits::default();
        limits.max_cached_lookups = 1;
        let authority = CapturedMetadataAuthority::open(
            &fixture.map,
            &fixture.contexts,
            fixture.pin(),
            &fixture.root,
            &limits,
        )
        .unwrap();
        assert!(authority.resolve("a", "absent/Class").unwrap().is_none());
        let charged = authority.cache_budget.used.load(Ordering::Relaxed);
        assert!(authority.resolve("a", "absent/Class").unwrap().is_none());
        assert_eq!(charged, authority.cache_budget.used.load(Ordering::Relaxed));
        assert!(matches!(
            authority.resolve("a", CLASS),
            Err(Error::Limit(_))
        ));
        limits.max_retained_input_bytes = 1;
        assert!(matches!(
            CapturedMetadataAuthority::open(
                &fixture.map,
                &fixture.contexts,
                fixture.pin(),
                &fixture.root,
                &limits
            ),
            Err(Error::Limit(_))
        ));
        limits = AuthorityLimits::default();
        limits.max_total_entries = 0;
        assert!(
            CapturedMetadataAuthority::open(
                &fixture.map,
                &fixture.contexts,
                fixture.pin(),
                &fixture.root,
                &limits
            )
            .is_err()
        );
    }

    #[test]
    fn hash_bound_directory_class_change_is_an_error_not_a_later_fallback() {
        let mut fixture = Fixture::new();
        let bytes = include_bytes!("../../../fixtures/binary/classes/fixture/Probe.class");
        std::fs::create_dir_all(fixture.root.join("classes/fixture")).unwrap();
        let class_path = fixture.root.join("classes/fixture/Probe.class");
        std::fs::write(&class_path, bytes).unwrap();
        let inventory = serde_json::to_vec(&json!([{"bytes":bytes.len(),"path":"fixture/Probe.class","sha256":hash(bytes).to_string()}])).unwrap();
        let digest = hash(&inventory).to_string();
        fixture.capture["input_objects"][0] = json!({"path":"/captured/source/classes","kind":"directory","sha256":digest,"files":1,"bytes":bytes.len()});
        fixture.capture["contexts"][0]["full_classpath"][0] =
            json!({"index":0,"path":"/captured/source/classes","sha256":digest});
        fixture.manifest["contexts"][0]["entries"][0] = json!({"path":fixture.root.join("classes"),"kind":"directory","sha256":digest,"files":1,"bytes":bytes.len()});
        fixture.save();
        let authority = fixture.open().unwrap();
        std::fs::write(&class_path, b"changed").unwrap();
        assert!(authority.resolve("a", "fixture/Probe").is_err());
        assert_eq!(authority.lookup_budget.used.load(Ordering::Relaxed), 0);
        assert!(fixture.open().is_err());
    }

    #[test]
    fn identical_archive_owners_and_payloads_are_safe_under_parallel_context_reads() {
        let mut fixture = Fixture::new();
        fixture.add_context("b");
        fixture.save();
        let authority = Arc::new(fixture.open().unwrap());
        let threads: Vec<_> = (0..8)
            .map(|index| {
                let authority = authority.clone();
                std::thread::spawn(move || {
                    authority
                        .resolve(if index % 2 == 0 { "a" } else { "b" }, CLASS)
                        .unwrap()
                        .unwrap()
                        .class_bytes
                })
            })
            .collect();
        let payloads: Vec<_> = threads
            .into_iter()
            .map(|thread| thread.join().unwrap())
            .collect();
        assert!(
            payloads
                .iter()
                .all(|payload| Arc::ptr_eq(payload, &payloads[0]))
        );
        assert_eq!(authority.lookup_budget.used.load(Ordering::Relaxed), 2);
        assert_eq!(authority.payloads.lock().unwrap().len(), 1);
    }
}
