//! Exact ordered runtime classpath equivalence for captured test tasks.
//!
//! This layer compares compiled inputs, not execution traces. It does not
//! establish that arbitrary files, spawned programs or the real CI launcher
//! agree across revisions. Consumers must bind the declared change scope and
//! apply the independent-suite, owning-classpath and stable-input premises.
use selector_class_diff::build_stamp;
use selector_models::binary::{BinaryError, CapturedClasspath, ClasspathEntry, EntryKind, Limits};
use selector_types::ContentHash;
use serde::Deserialize;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::io::Read;
use std::path::{Component, Path, PathBuf};
use std::process::Command;

mod classpath_delta;
pub use classpath_delta::{
    ClassFileDelta, ClasspathDelta, DirectoryDelta, FileIdentity, audit_test_classpath_delta,
};

#[cfg(test)]
mod tests;

const MAX_DOCUMENT: u64 = 64 * 1024 * 1024;
const MAX_CONTEXTS: usize = 1024;
const MAX_ENTRIES: usize = 65_535;
const BUILD_STAMP_PRODUCT: &str = "apps/common/target/scala-2.13/classes";
const BUILD_STAMP_FORWARDER: &str = "org/lfdecentralizedtrust/splice/environment/BuildInfo";

#[derive(Debug)]
pub enum Error {
    Invalid(&'static str),
    Budget,
    Io(std::io::Error),
    Json(serde_json::Error),
    Provider(BinaryError),
    Facts(selector_types::Error),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "runtime equivalence {self:?}")
    }
}

impl std::error::Error for Error {}

impl From<std::io::Error> for Error {
    fn from(error: std::io::Error) -> Self {
        Self::Io(error)
    }
}

impl From<serde_json::Error> for Error {
    fn from(error: serde_json::Error) -> Self {
        Self::Json(error)
    }
}

impl From<BinaryError> for Error {
    fn from(error: BinaryError) -> Self {
        Self::Provider(error)
    }
}

impl From<selector_types::Error> for Error {
    fn from(error: selector_types::Error) -> Self {
        Self::Facts(error)
    }
}

#[derive(Deserialize)]
struct Capture {
    schema_version: String,
    revision: String,
    git_head_at_finalize: String,
    source_root: PathBuf,
    sbt_version: String,
    java_runtime: serde_json::Value,
    contexts: Vec<Context>,
    input_objects: Vec<Object>,
    errors: Vec<serde_json::Value>,
}
#[derive(Deserialize)]
struct Context {
    context_id: String,
    configuration: String,
    base_directory: PathBuf,
    java_home: Option<PathBuf>,
    java_options: Option<Vec<String>>,
    fork: Option<bool>,
    full_classpath: Vec<Entry>,
    defined_tests: Vec<Defined>,
    source_records: Vec<Source>,
    resource_files: Vec<PathBuf>,
}
#[derive(Deserialize)]
struct Source {
    path: PathBuf,
    repo_relative_path: String,
    sha256: String,
}
#[derive(Deserialize)]
struct Entry {
    index: usize,
    path: PathBuf,
    input_object: PathBuf,
    sha256: String,
}
#[derive(Deserialize)]
struct Object {
    path: PathBuf,
    kind: String,
    sha256: String,
    bytes: u64,
    files: Option<u64>,
}
#[derive(Deserialize)]
struct Defined {
    name: String,
    fingerprint: serde_json::Value,
}
#[derive(Deserialize)]
struct Catalogue {
    schema_version: String,
    revision: String,
    complete: bool,
    issues: Vec<serde_json::Value>,
    suites: Vec<Suite>,
    families: Vec<Family>,
}
#[derive(Deserialize)]
struct Suite {
    suite: String,
    owning_context_ids: Vec<String>,
    compiler_discovery: Vec<Discovery>,
}
#[derive(Deserialize)]
struct Discovery {
    context_id: String,
    configuration: String,
    fingerprint: serde_json::Value,
}
#[derive(Deserialize)]
struct Family {
    job_id: String,
    suites: Vec<String>,
    #[serde(flatten)]
    launch: BTreeMap<String, serde_json::Value>,
}

pub struct Inputs<'a> {
    pub contexts: &'a Path,
    pub catalogue: &'a Path,
    pub physical_root: &'a Path,
}

#[derive(Debug, serde::Serialize)]
pub struct InputIdentity {
    pub revision: String,
    pub contexts_sha256: String,
    pub catalogue_sha256: String,
    pub physical_root: PathBuf,
}
#[derive(Debug, serde::Serialize)]
pub struct Row {
    pub suite: String,
    pub context: Option<String>,
    pub reason: &'static str,
    pub ordered_classpath_sha256: Option<String>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, serde::Serialize)]
#[serde(rename_all = "snake_case")]
pub enum BuildStampPolicy {
    #[default]
    CompareExactly,
    AssumeUnchanged,
}

#[derive(Debug, serde::Serialize)]
#[serde(tag = "reason", rename_all = "snake_case")]
pub enum ContextBlocker {
    DifferentOrUnsupportedLaunch,
    EmptyClasspath,
    ClasspathLength {
        base: usize,
        head: usize,
    },
    ClasspathLocation {
        index: usize,
        base: PathBuf,
        head: PathBuf,
    },
    ClasspathContent {
        index: usize,
        path: PathBuf,
    },
    UnsupportedProvider {
        index: usize,
        path: PathBuf,
    },
    BuildStampDeltaOutsidePolicy {
        index: usize,
        path: PathBuf,
    },
    ManifestClosure {
        revision: String,
    },
}

#[derive(Debug, serde::Serialize)]
pub struct Comparison {
    pub base: InputIdentity,
    pub head: InputIdentity,
    pub rows: Vec<Row>,
    pub context_blockers: BTreeMap<String, ContextBlocker>,
    pub verified_provider_entries: usize,
    pub verified_provider_bytes: u64,
    pub local_java_pins: Option<BTreeMap<String, String>>,
    pub build_stamp_policy: BuildStampPolicy,
}

#[derive(Debug, serde::Serialize)]
pub struct SourceBinding {
    pub path: String,
    pub owner: String,
    pub base_sha256: Option<String>,
    pub head_sha256: Option<String>,
}

/// Separate from graph-based selection. Only the explicitly requested tracked
/// test-source delta is covered; an identical compiled classpath does not
/// certify changes to ambient inputs or an unobserved runner.
#[derive(Debug, serde::Serialize)]
pub struct TrackedTestSelection {
    pub schema: &'static str,
    pub contract: &'static [&'static str],
    pub changed_test_sources: Vec<SourceBinding>,
    pub excluded: Vec<String>,
    pub retained: Vec<String>,
    pub comparison: Comparison,
    pub whole_checkout_omission_authority: bool,
}

struct Side {
    capture: Capture,
    catalogue: Catalogue,
    identity: InputIdentity,
}
fn hash(bytes: &[u8]) -> ContentHash {
    ContentHash(Sha256::digest(bytes).into())
}
fn no_symlinks(path: &Path) -> Result<(), Error> {
    if !path.is_absolute()
        || path
            .components()
            .any(|c| !matches!(c, Component::RootDir | Component::Normal(_)))
    {
        return Err(Error::Invalid(
            "runtime equivalence requires normalized absolute paths",
        ));
    }
    let mut prefix = PathBuf::new();
    for part in path.components() {
        prefix.push(part.as_os_str());
        match std::fs::symlink_metadata(&prefix) {
            Ok(meta) if meta.file_type().is_symlink() => {
                return Err(Error::Invalid("runtime equivalence symlink input"));
            }
            Ok(_) => (),
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => break,
            Err(err) => return Err(err.into()),
        }
    }
    Ok(())
}
fn require_absent(path: &Path) -> Result<(), Error> {
    no_symlinks(path)?;
    match std::fs::symlink_metadata(path) {
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(error.into()),
        Ok(_) => Err(Error::Invalid("manifest absence changed")),
    }
}

fn read<T: serde::de::DeserializeOwned>(path: &Path) -> Result<(T, ContentHash), Error> {
    no_symlinks(path)?;
    let mut bytes = Vec::new();
    std::fs::File::open(path)?
        .take(MAX_DOCUMENT + 1)
        .read_to_end(&mut bytes)?;
    if bytes.len() as u64 > MAX_DOCUMENT {
        return Err(Error::Budget);
    }
    let digest = hash(&bytes);
    let value = if path.extension().is_some_and(|ext| ext == "gz") {
        let mut decoder =
            flate2::read::MultiGzDecoder::new(bytes.as_slice()).take(MAX_DOCUMENT + 1);
        let value = serde_json::from_reader(&mut decoder)?;
        if decoder.limit() == 0 {
            return Err(Error::Budget);
        }
        value
    } else {
        serde_json::from_slice(&bytes)?
    };
    Ok((value, digest))
}
fn unique<'a, T>(
    rows: &'a [T],
    key: impl Fn(&'a T) -> &'a str,
) -> Result<HashMap<&'a str, &'a T>, Error> {
    let mut index = HashMap::with_capacity(rows.len());
    for row in rows {
        if index.insert(key(row), row).is_some() {
            return Err(Error::Invalid("duplicate runtime equivalence input"));
        }
    }
    Ok(index)
}
impl Side {
    fn load(inputs: Inputs<'_>) -> Result<Self, Error> {
        let (capture, contexts): (Capture, _) = read(inputs.contexts)?;
        let (catalogue, catalogue_sha): (Catalogue, _) = read(inputs.catalogue)?;
        if capture.schema_version != "sbt-compiler-context/v1"
            || catalogue.schema_version != "compiler-ci-catalogue/v1"
            || capture.revision != catalogue.revision
            || capture.revision != capture.git_head_at_finalize
            || capture.revision.len() != 40
            || !capture.revision.bytes().all(|b| b.is_ascii_hexdigit())
            || !catalogue.complete
            || !catalogue.issues.is_empty()
            || !capture.errors.is_empty()
        {
            return Err(Error::Invalid(
                "runtime equivalence capture or catalogue binding",
            ));
        }
        if capture.contexts.len() > MAX_CONTEXTS
            || capture.input_objects.len() > MAX_ENTRIES
            || catalogue.suites.len() > MAX_ENTRIES
            || catalogue.families.len() > MAX_CONTEXTS
        {
            return Err(Error::Budget);
        }
        no_symlinks(inputs.physical_root)?;
        if !inputs.physical_root.is_dir() {
            return Err(Error::Invalid("runtime equivalence physical source root"));
        }
        let identity = InputIdentity {
            revision: capture.revision.clone(),
            contexts_sha256: contexts.to_string(),
            catalogue_sha256: catalogue_sha.to_string(),
            physical_root: inputs.physical_root.to_owned(),
        };
        Ok(Self {
            capture,
            catalogue,
            identity,
        })
    }
    fn logical<'a>(&self, path: &'a Path) -> (bool, &'a Path) {
        match path.strip_prefix(&self.capture.source_root) {
            Ok(tail) => (true, tail),
            Err(_) => (false, path),
        }
    }
    fn physical(&self, path: &Path) -> PathBuf {
        match self.logical(path) {
            (true, tail) => self.identity.physical_root.join(tail),
            (false, path) => path.to_owned(),
        }
    }
}

fn suite_owner<'a>(suite: &'a Suite, contexts: &HashMap<&str, &Context>) -> Option<&'a str> {
    let [owner] = suite.owning_context_ids.as_slice() else {
        return None;
    };
    let context = contexts.get(owner.as_str())?;
    let [discovery] = suite.compiler_discovery.as_slice() else {
        return None;
    };
    if context.configuration != "test"
        || discovery.context_id != *owner
        || discovery.configuration != "test"
    {
        return None;
    }
    let mut definitions = context
        .defined_tests
        .iter()
        .filter(|d| d.name == suite.suite);
    let definition = definitions.next()?;
    if definitions.next().is_some() || definition.fingerprint != discovery.fingerprint {
        return None;
    }
    Some(owner)
}

fn memberships<'a>(
    catalogue: &'a Catalogue,
) -> Result<HashMap<&'a str, BTreeMap<&'a str, &'a BTreeMap<String, serde_json::Value>>>, Error> {
    let _ = unique(&catalogue.families, |f| &f.job_id)?;
    let mut result: HashMap<_, BTreeMap<_, _>> = HashMap::new();
    for family in &catalogue.families {
        for suite in &family.suites {
            if result
                .entry(suite.as_str())
                .or_default()
                .insert(family.job_id.as_str(), &family.launch)
                .is_some()
            {
                return Err(Error::Invalid(
                    "duplicate runtime equivalence family membership",
                ));
            }
        }
    }
    Ok(result)
}

type ObjectIndex<'a> = HashMap<&'a Path, &'a Object>;
fn objects(side: &Side) -> Result<ObjectIndex<'_>, Error> {
    let mut index = HashMap::new();
    for object in &side.capture.input_objects {
        if index.insert(object.path.as_path(), object).is_some() {
            return Err(Error::Invalid("duplicate runtime equivalence object"));
        }
    }
    Ok(index)
}
fn entry(side: &Side, objects: &ObjectIndex<'_>, row: &Entry) -> Result<ClasspathEntry, Error> {
    let object = objects
        .get(row.input_object.as_path())
        .ok_or(Error::Invalid("missing runtime equivalence object"))?;
    if object.sha256 != row.sha256 {
        return Err(Error::Invalid("runtime equivalence object binding"));
    }
    let path = side.physical(&object.path);
    if object.path != row.path {
        // sbt records classpath aliases separately from canonical input pins.
        // Accept an exact sibling JAR symlink only; its manifest-relative
        // resolution is the same through the alias and the canonical path.
        let alias = side.physical(&row.path);
        let parent = alias
            .parent()
            .ok_or(Error::Invalid("runtime alias parent"))?;
        no_symlinks(parent)?;
        no_symlinks(&path)?;
        if object.kind != "file"
            || path.parent() != Some(parent)
            || !std::fs::symlink_metadata(&alias)?.file_type().is_symlink()
            || alias.canonicalize()? != path
        {
            return Err(Error::Invalid("runtime equivalence unverified input alias"));
        }
    }
    let kind = match object.kind.as_str() {
        "file" if row.path.extension().is_some_and(|ext| ext == "jar") => EntryKind::Jar,
        "directory" => EntryKind::Directory {
            files: object
                .files
                .ok_or(Error::Invalid("missing runtime directory count"))?,
            bytes: object.bytes,
        },
        "absent_empty_project_output"
            if object.bytes == 0 && object.files.is_none_or(|n| n == 0) =>
        {
            EntryKind::AbsentEmptyOutput
        }
        _ => EntryKind::Unavailable,
    };
    Ok(ClasspathEntry {
        path,
        sha256: ContentHash::from_hex(&row.sha256)?,
        kind,
    })
}

#[derive(Default)]
struct Verifier {
    admitted: HashMap<ClasspathEntry, Vec<String>>,
    stamp_deltas: HashMap<(ClasspathEntry, ClasspathEntry), bool>,
    bytes: u64,
}
impl Verifier {
    fn record(
        &mut self,
        entry: &ClasspathEntry,
        bytes: u64,
        manifest: Vec<String>,
    ) -> Result<(), Error> {
        if self.admitted.len() >= MAX_ENTRIES {
            return Err(Error::Budget);
        }
        self.bytes = self.bytes.checked_add(bytes).ok_or(Error::Budget)?;
        self.admitted.insert(entry.clone(), manifest);
        Ok(())
    }

    fn verify_stamp_delta(
        &mut self,
        before: &ClasspathEntry,
        after: &ClasspathEntry,
    ) -> Result<bool, Error> {
        let pair = (before.clone(), after.clone());
        if let Some(&verified) = self.stamp_deltas.get(&pair) {
            return Ok(verified);
        }
        let verified = only_generated_stamp_changed(before, after)?;
        if verified {
            // Verified directories have no JAR manifest to expand.
            for entry in [before, after] {
                if let EntryKind::Directory { bytes, .. } = entry.kind
                    && !self.admitted.contains_key(entry)
                {
                    self.record(entry, bytes, Vec::new())?;
                }
            }
        }
        self.stamp_deltas.insert(pair, verified);
        Ok(verified)
    }

    fn verify_scope(
        &mut self,
        entries: &[ClasspathEntry],
        java_feature: u16,
    ) -> Result<bool, Error> {
        let paths: BTreeSet<_> = entries.iter().map(|e| e.path.as_path()).collect();
        for entry in entries {
            if !self.admitted.contains_key(entry) {
                no_symlinks(&entry.path)?;
                let bytes = match entry.kind {
                    EntryKind::AbsentEmptyOutput => {
                        require_absent(&entry.path)?;
                        0
                    }
                    EntryKind::Directory { bytes, .. } => bytes,
                    EntryKind::Jar => std::fs::metadata(&entry.path)?.len(),
                    EntryKind::Unavailable => return Ok(false),
                };
                let manifest = CapturedClasspath::new(vec![entry.clone()], Limits::default())
                    .and_then(|loader| loader.with_java_feature(Some(java_feature)))
                    .and_then(|mut loader| loader.manifest_class_path(0))?;
                self.record(entry, bytes, manifest)?;
            }
            for token in &self.admitted[entry] {
                if token.is_empty()
                    || token.contains([':', '%', '#', '?', '\\'])
                    || Path::new(token)
                        .components()
                        .any(|c| !matches!(c, Component::Normal(_)))
                {
                    return Ok(false);
                }
                let target = entry
                    .path
                    .parent()
                    .ok_or(Error::Invalid("runtime manifest parent"))?
                    .join(token);
                if !paths.contains(target.as_path()) {
                    match require_absent(&target) {
                        Ok(()) => (),
                        Err(Error::Invalid(_)) => return Ok(false),
                        Err(error) => return Err(error),
                    }
                }
            }
        }
        Ok(true)
    }
}

fn only_generated_stamp_changed(
    before: &ClasspathEntry,
    after: &ClasspathEntry,
) -> Result<bool, Error> {
    no_symlinks(&before.path)?;
    no_symlinks(&after.path)?;
    let mut base = CapturedClasspath::new(vec![before.clone()], Limits::default())?;
    let mut head = CapturedClasspath::new(vec![after.clone()], Limits::default())?;
    let module_path = format!("{}.class", build_stamp::OWNER);
    let forwarder_path = format!("{BUILD_STAMP_FORWARDER}.class");
    let base_files = base.directory_files(0)?;
    let head_files = head.directory_files(0)?;
    if base_files.len() != head_files.len() {
        return Ok(false);
    }
    let mut module_changed = false;
    let mut forwarder_found = false;
    for (old, new) in base_files.zip(head_files) {
        if old.0 == forwarder_path {
            forwarder_found = true;
        }
        if old != new {
            if old.0 != module_path || new.0 != module_path {
                return Ok(false);
            }
            module_changed = true;
        }
    }
    if !module_changed || !forwarder_found {
        return Ok(false);
    }
    let old_module = base.resolve(build_stamp::OWNER)?;
    let new_module = head.resolve(build_stamp::OWNER)?;
    let old_forwarder = base.resolve(BUILD_STAMP_FORWARDER)?;
    let new_forwarder = head.resolve(BUILD_STAMP_FORWARDER)?;
    Ok(build_stamp::compare(
        &old_module.bytes,
        &new_module.bytes,
        &old_forwarder.bytes,
        &new_forwarder.bytes,
    )
    .is_ok())
}

fn comparable_launch(base: &Side, before: &Context, head: &Side, after: &Context) -> bool {
    let supported = |c: &Context| {
        c.fork == Some(false)
            && c.java_home.is_none()
            && c.java_options.as_ref().is_some_and(Vec::is_empty)
    };
    supported(before)
        && supported(after)
        && base.logical(&before.base_directory) == head.logical(&after.base_directory)
        && base.capture.sbt_version == head.capture.sbt_version
        && base.capture.java_runtime == head.capture.java_runtime
}

enum ContextMatch {
    Verified {
        identity: ContentHash,
        used_stamp_policy: bool,
    },
    Blocked(ContextBlocker),
}

fn verify_context(
    base: &Side,
    before: &Context,
    base_objects: &ObjectIndex<'_>,
    head: &Side,
    after: &Context,
    head_objects: &ObjectIndex<'_>,
    verifier: &mut Verifier,
    java_feature: u16,
    build_stamp_policy: BuildStampPolicy,
) -> Result<ContextMatch, Error> {
    use ContextBlocker::*;
    use ContextMatch::{Blocked, Verified};
    if !comparable_launch(base, before, head, after) {
        return Ok(Blocked(DifferentOrUnsupportedLaunch));
    }
    if before.full_classpath.len() != after.full_classpath.len() {
        return Ok(Blocked(ClasspathLength {
            base: before.full_classpath.len(),
            head: after.full_classpath.len(),
        }));
    }
    if before.full_classpath.is_empty() {
        return Ok(Blocked(EmptyClasspath));
    }
    let mut b = Vec::with_capacity(before.full_classpath.len());
    let mut h = Vec::with_capacity(before.full_classpath.len());
    let mut digest = Sha256::new();
    let mut stamp_delta = None;
    digest.update(b"selector-equal-ordered-test-classpath/1\0");
    for (ordinal, (x, y)) in before
        .full_classpath
        .iter()
        .zip(&after.full_classpath)
        .enumerate()
    {
        if x.index != ordinal || y.index != ordinal {
            return Err(Error::Invalid("runtime classpath ordinal"));
        }
        let logical = base.logical(&x.path);
        let head_logical = head.logical(&y.path);
        let base_object = base.logical(&x.input_object);
        let head_object = head.logical(&y.input_object);
        if let Some((before, after)) = [(logical, head_logical), (base_object, head_object)]
            .into_iter()
            .find(|(before, after)| before != after)
        {
            return Ok(Blocked(ClasspathLocation {
                index: ordinal,
                base: before.1.to_owned(),
                head: after.1.to_owned(),
            }));
        }
        let different = x.sha256 != y.sha256;
        if different
            && (build_stamp_policy != BuildStampPolicy::AssumeUnchanged
                || logical != (true, Path::new(BUILD_STAMP_PRODUCT))
                || stamp_delta.replace(ordinal).is_some())
        {
            return Ok(Blocked(ClasspathContent {
                index: ordinal,
                path: logical.1.to_owned(),
            }));
        }
        let (x, y) = (entry(base, base_objects, x)?, entry(head, head_objects, y)?);
        let compatible_kinds = if different {
            matches!(x.kind, EntryKind::Directory { .. })
                && matches!(y.kind, EntryKind::Directory { .. })
        } else {
            x.kind == y.kind && x.kind != EntryKind::Unavailable
        };
        if !compatible_kinds {
            return Ok(Blocked(UnsupportedProvider {
                index: ordinal,
                path: logical.1.to_owned(),
            }));
        }
        let path = logical.1.as_os_str().as_encoded_bytes();
        digest.update([logical.0 as u8]);
        digest.update((path.len() as u64).to_le_bytes());
        digest.update(path);
        digest.update(x.sha256.0);
        b.push(x);
        h.push(y);
    }
    let mut identity = ContentHash(digest.finalize().into());
    if let Some(index) = stamp_delta {
        if !verifier.verify_stamp_delta(&b[index], &h[index])? {
            return Ok(Blocked(BuildStampDeltaOutsidePolicy {
                index,
                path: PathBuf::from(BUILD_STAMP_PRODUCT),
            }));
        }
        let mut assumed = Sha256::new();
        assumed.update(b"selector-assume-unchanged-generated-build-stamp/1\0");
        assumed.update(identity.0);
        assumed.update((index as u64).to_le_bytes());
        assumed.update(h[index].sha256.0);
        identity = ContentHash(assumed.finalize().into());
    }
    for (side, entries) in [(base, &b), (head, &h)] {
        if !verifier.verify_scope(entries, java_feature)? {
            return Ok(Blocked(ManifestClosure {
                revision: side.identity.revision.clone(),
            }));
        }
    }
    Ok(Verified {
        identity,
        used_stamp_policy: stamp_delta.is_some(),
    })
}

pub fn compare(base: Inputs<'_>, head: Inputs<'_>) -> Result<Comparison, Error> {
    compare_with_policy(base, head, BuildStampPolicy::CompareExactly)
}

/// Compare captured classpaths without admitting any tracked-change selection scope.
pub fn compare_with_policy(
    base: Inputs<'_>,
    head: Inputs<'_>,
    build_stamp_policy: BuildStampPolicy,
) -> Result<Comparison, Error> {
    let base = Side::load(base)?;
    let head = Side::load(head)?;
    compare_sides(base, head, build_stamp_policy)
}

fn compare_sides(
    base: Side,
    head: Side,
    build_stamp_policy: BuildStampPolicy,
) -> Result<Comparison, Error> {
    let java_feature = java_feature(&base)?;
    let b_contexts = unique(&base.capture.contexts, |c| &c.context_id)?;
    let h_contexts = unique(&head.capture.contexts, |c| &c.context_id)?;
    let b_suites = unique(&base.catalogue.suites, |s| &s.suite)?;
    let h_suites = unique(&head.catalogue.suites, |s| &s.suite)?;
    let b_members = memberships(&base.catalogue)?;
    let h_members = memberships(&head.catalogue)?;
    for (suites, members) in [(&b_suites, &b_members), (&h_suites, &h_members)] {
        if suites.is_empty()
            || suites.len() != members.len()
            || members.keys().any(|name| !suites.contains_key(name))
        {
            return Err(Error::Invalid("runtime equivalence family universe"));
        }
    }
    let b_objects = objects(&base)?;
    let h_objects = objects(&head)?;
    let mut verifier = Verifier::default();
    let mut cached = HashMap::new();
    let mut rows = Vec::with_capacity(head.catalogue.suites.len());
    for suite in &head.catalogue.suites {
        let mut row = Row {
            suite: suite.suite.clone(),
            context: None,
            reason: "missing_paired_suite",
            ordered_classpath_sha256: None,
        };
        if let Some(old) = b_suites.get(suite.suite.as_str()) {
            row.reason = "different_suite_owner_or_discovery";
            if let Some(owner) = suite_owner(suite, &h_contexts)
                && suite_owner(old, &b_contexts) == Some(owner)
                && old.compiler_discovery[0].fingerprint == suite.compiler_discovery[0].fingerprint
            {
                row.context = Some(owner.to_owned());
                row.reason = "different_suite_family";
                let family = h_members.get(suite.suite.as_str());
                if family.is_some() && b_members.get(suite.suite.as_str()) == family {
                    let result = match cached.entry(owner) {
                        std::collections::hash_map::Entry::Occupied(entry) => entry.into_mut(),
                        std::collections::hash_map::Entry::Vacant(entry) => {
                            let value = verify_context(
                                &base,
                                b_contexts[owner],
                                &b_objects,
                                &head,
                                h_contexts[owner],
                                &h_objects,
                                &mut verifier,
                                java_feature,
                                build_stamp_policy,
                            )?;
                            entry.insert(value)
                        }
                    };
                    row.reason = "different_or_unsupported_classpaths";
                    if let ContextMatch::Verified {
                        identity,
                        used_stamp_policy,
                    } = result
                    {
                        row.reason = if *used_stamp_policy {
                            "equal_under_generated_build_stamp_assumption"
                        } else {
                            "equal_verified_ordered_classpaths"
                        };
                        row.ordered_classpath_sha256 = Some(identity.to_string());
                    }
                }
            }
        }
        rows.push(row);
    }
    rows.sort_unstable_by(|a, b| a.suite.cmp(&b.suite));
    let local_java_pins = if rows.iter().any(|r| r.ordered_classpath_sha256.is_some()) {
        let home = base
            .capture
            .java_runtime
            .get("java_home")
            .and_then(|v| v.as_str())
            .ok_or(Error::Invalid("missing captured Java home"))?;
        let mut pins = BTreeMap::new();
        for relative in ["bin/java", "lib/modules", "release"] {
            let path = Path::new(home).join(relative);
            no_symlinks(&path)?;
            let mut file = std::fs::File::open(path)?.take(512 * 1024 * 1024);
            let mut digest = Sha256::new();
            std::io::copy(&mut file, &mut digest)?;
            if file.limit() == 0 {
                return Err(Error::Budget);
            }
            pins.insert(
                relative.to_owned(),
                ContentHash(digest.finalize().into()).to_string(),
            );
        }
        Some(pins)
    } else {
        None
    };
    let context_blockers = cached
        .into_iter()
        .filter_map(|(owner, result)| match result {
            ContextMatch::Blocked(blocker) => Some((owner.to_owned(), blocker)),
            ContextMatch::Verified { .. } => None,
        })
        .collect();
    Ok(Comparison {
        base: base.identity,
        head: head.identity,
        rows,
        context_blockers,
        verified_provider_entries: verifier.admitted.len(),
        verified_provider_bytes: verifier.bytes,
        local_java_pins,
        build_stamp_policy,
    })
}

fn java_feature(side: &Side) -> Result<u16, Error> {
    let version = side
        .capture
        .java_runtime
        .get("java_version")
        .and_then(serde_json::Value::as_str)
        .ok_or(Error::Invalid("missing captured Java version"))?;
    version
        .split('.')
        .next()
        .and_then(|v| v.parse::<u16>().ok())
        .filter(|v| *v >= 9)
        .ok_or(Error::Invalid("unsupported captured Java feature"))
}

fn git(repo: &Path, args: &[&str]) -> Result<Vec<u8>, Error> {
    let output = Command::new("git")
        .current_dir(repo)
        .env("GIT_NO_LAZY_FETCH", "1")
        .env("GIT_NO_REPLACE_OBJECTS", "1")
        .args(args)
        .output()?;
    if !output.status.success() {
        return Err(Error::Invalid(
            "cannot verify exact tracked test delta with Git",
        ));
    }
    Ok(output.stdout)
}

fn source_hash<'a>(
    side: &'a Side,
    repo: &Path,
    path: &str,
    blob: &str,
) -> Result<(&'a str, String), Error> {
    let mut rows = side.capture.contexts.iter().flat_map(|c| {
        c.source_records
            .iter()
            .filter(move |s| s.repo_relative_path == path)
            .map(move |s| (c, s))
    });
    let (context, source) = rows
        .next()
        .ok_or(Error::Invalid("missing captured test source"))?;
    if rows.next().is_some()
        || context.configuration != "test"
        || side.logical(&source.path) != (true, Path::new(path))
        || source_is_resource(side, Path::new(path))
    {
        return Err(Error::Invalid(
            "tracked change is not one captured test compiler input",
        ));
    }
    let physical = side.physical(&source.path);
    no_symlinks(&physical)?;
    if !physical.is_file() {
        return Err(Error::Invalid("tracked test source is not a regular file"));
    }
    let git_hash = git(
        repo,
        &[
            "hash-object",
            "--no-filters",
            "--",
            physical
                .to_str()
                .ok_or(Error::Invalid("invalid tracked test source path"))?,
        ],
    )?;
    let git_hash =
        std::str::from_utf8(&git_hash).map_err(|_| Error::Invalid("malformed Git source hash"))?;
    let mut bytes = Vec::new();
    std::fs::File::open(&physical)?
        .take(MAX_DOCUMENT + 1)
        .read_to_end(&mut bytes)?;
    if bytes.len() as u64 > MAX_DOCUMENT {
        return Err(Error::Budget);
    }
    let actual = hash(&bytes).to_string();
    if git_hash.trim() != blob || source.sha256 != actual {
        return Err(Error::Invalid(
            "compiled test source differs from exact Git delta",
        ));
    }
    Ok((&context.context_id, actual))
}

fn source_is_resource(side: &Side, path: &Path) -> bool {
    let captured = side.capture.source_root.join(path);
    let physical = side.identity.physical_root.join(path);
    side.capture.contexts.iter().any(|context| {
        context
            .resource_files
            .iter()
            .any(|p| p == path || p == &captured || p == &physical)
    })
}

fn verify_source_absence(side: &Side, path: &str, owner: &str) -> Result<(), Error> {
    if !side
        .capture
        .contexts
        .iter()
        .any(|c| c.context_id == owner && c.configuration == "test")
    {
        return Err(Error::Invalid("missing paired test source owner"));
    }
    let relative = Path::new(path);
    let captured = side.capture.source_root.join(relative);
    let physical = side.identity.physical_root.join(relative);
    if source_is_resource(side, relative)
        || side.capture.contexts.iter().any(|context| {
            context.source_records.iter().any(|s| {
                s.repo_relative_path == path
                    || s.path == relative
                    || s.path == captured
                    || s.path == physical
            })
        })
    {
        return Err(Error::Invalid(
            "absent tracked test source is a captured compiler input or resource",
        ));
    }
    require_absent(&physical)
}

#[derive(Debug, serde::Serialize)]
pub struct TrackedTestChange {
    pub path: String,
    pub base_blob: Option<String>,
    pub head_blob: Option<String>,
}

/// Check whether exact Git revisions fit the tracked Scala Test fast path.
/// Selection also verifies capture ownership, physical files and classpaths.
pub fn preflight_tracked_test_delta(
    repo: &Path,
    base_revision: &str,
    head_revision: &str,
) -> Result<Vec<TrackedTestChange>, Error> {
    for revision in [base_revision, head_revision] {
        if revision.len() != 40
            || !revision.bytes().all(|b| b.is_ascii_hexdigit())
            || git(repo, &["cat-file", "-t", revision])? != b"commit\n"
        {
            return Err(Error::Invalid("expected exact Git commit identities"));
        }
    }
    let raw = git(
        repo,
        &[
            "diff-tree",
            "-r",
            "--no-commit-id",
            "--no-renames",
            "--ignore-submodules=none",
            "--no-abbrev",
            "--raw",
            "-z",
            base_revision,
            head_revision,
            "--",
        ],
    )?;
    let raw = std::str::from_utf8(&raw).map_err(|_| Error::Invalid("malformed tracked delta"))?;
    let mut parts = raw.split_terminator('\0');
    let mut changes = Vec::new();
    while let Some(row) = parts.next() {
        let mut fields = row.split_whitespace();
        let (
            Some(base_mode),
            Some(head_mode),
            Some(base_blob),
            Some(head_blob),
            Some(status),
            None,
        ) = (
            fields.next(),
            fields.next(),
            fields.next(),
            fields.next(),
            fields.next(),
            fields.next(),
        )
        else {
            return Err(Error::Invalid("malformed tracked delta row"));
        };
        const ABSENT_BLOB: &str = "0000000000000000000000000000000000000000";
        let (base_blob, head_blob) = match (status, base_mode, head_mode) {
            ("M", ":100644", "100644") => (Some(base_blob), Some(head_blob)),
            ("A", ":000000", "100644") if base_blob == ABSENT_BLOB => (None, Some(head_blob)),
            ("D", ":100644", "000000") if head_blob == ABSENT_BLOB => (Some(base_blob), None),
            _ => {
                return Err(Error::Invalid(
                    "test delta requires regular added, deleted or modified sources",
                ));
            }
        };
        let path = parts
            .next()
            .ok_or(Error::Invalid("missing tracked delta pathname"))?;
        if changes.len() >= 32
            || !path.ends_with(".scala")
            || !path.contains("/src/test/scala/")
            || Path::new(path)
                .components()
                .any(|c| !matches!(c, Component::Normal(_)))
        {
            return Err(Error::Invalid(
                "test delta requires a bounded Scala test source change set",
            ));
        }
        changes.push(TrackedTestChange {
            path: path.to_owned(),
            base_blob: base_blob.map(str::to_owned),
            head_blob: head_blob.map(str::to_owned),
        });
    }
    if changes.is_empty() {
        return Err(Error::Invalid("no tracked test delta"));
    }
    Ok(changes)
}

pub fn select_tracked_test_delta(
    base: Inputs<'_>,
    head: Inputs<'_>,
    repo: &Path,
) -> Result<TrackedTestSelection, Error> {
    select_tracked_test_delta_with_policy(base, head, repo, BuildStampPolicy::CompareExactly)
}

/// Select for modified, added or deleted tracked Scala Test inputs. Git renames
/// are verified as separate deletion and addition rows.
///
/// The BuildInfo policy applies to generated version and timestamp literals.
/// The policy does not compute which suites observe those values.
pub fn select_tracked_test_delta_with_policy(
    base: Inputs<'_>,
    head: Inputs<'_>,
    repo: &Path,
    build_stamp_policy: BuildStampPolicy,
) -> Result<TrackedTestSelection, Error> {
    let base = Side::load(base)?;
    let head = Side::load(head)?;
    let changes =
        preflight_tracked_test_delta(repo, &base.identity.revision, &head.identity.revision)?;
    let mut source_bindings = Vec::with_capacity(changes.len());
    let mut changed_owners = BTreeSet::new();
    for TrackedTestChange {
        path,
        base_blob,
        head_blob,
    } in changes
    {
        let base_source = base_blob
            .as_deref()
            .map(|blob| source_hash(&base, repo, &path, blob))
            .transpose()?;
        let head_source = head_blob
            .as_deref()
            .map(|blob| source_hash(&head, repo, &path, blob))
            .transpose()?;
        let (owner, base_sha256, head_sha256) = match (base_source, head_source) {
            (Some((base_owner, before)), Some((head_owner, after)))
                if base_owner == head_owner && before != after =>
            {
                (base_owner, Some(before), Some(after))
            }
            (Some((owner, before)), None) => {
                verify_source_absence(&head, &path, owner)?;
                (owner, Some(before), None)
            }
            (None, Some((owner, after))) => {
                verify_source_absence(&base, &path, owner)?;
                (owner, None, Some(after))
            }
            _ => {
                return Err(Error::Invalid(
                    "test source owner or physical delta mismatch",
                ));
            }
        };
        changed_owners.insert(owner.to_owned());
        source_bindings.push(SourceBinding {
            path,
            owner: owner.to_owned(),
            base_sha256,
            head_sha256,
        });
    }
    let schema = if source_bindings
        .iter()
        .any(|s| s.base_sha256.is_none() || s.head_sha256.is_none())
    {
        "selector-tracked-test-runtime-equivalence/v2"
    } else {
        "selector-tracked-test-runtime-equivalence/v1"
    };
    let comparison = compare_sides(base, head, build_stamp_policy)?;
    let (mut excluded, mut retained) = (Vec::new(), Vec::new());
    for row in &comparison.rows {
        if row.ordered_classpath_sha256.is_some()
            && row
                .context
                .as_ref()
                .is_some_and(|owner| !changed_owners.contains(owner))
        {
            excluded.push(row.suite.clone());
        } else {
            retained.push(row.suite.clone());
        }
    }
    Ok(TrackedTestSelection {
        schema,
        contract: &[
            "independent_suites",
            "owning_captured_test_full_classpath",
            "unchanged_declared_external_inputs",
            "tracked_test_sources_are_compile_inputs",
        ],
        changed_test_sources: source_bindings,
        excluded,
        retained,
        comparison,
        whole_checkout_omission_authority: false,
    })
}
