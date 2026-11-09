//! Explicit declared-runtime bytes, separate from historical compiler inputs.
//!
//! The capture producer reads java.base through the selected runtime's JRT
//! filesystem. Admission checks its exact image and complete class inventory;
//! no Java version string, host search, purity, or runtime isolation is inferred.
use flate2::read::MultiGzDecoder;
use selector_models::binary::{CapturedClasspath, ClassLookup, ClasspathEntry, EntryKind, Limits};
use selector_types::{ContentHash, Error};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::io::Read;
use std::path::{Component, Path, PathBuf};

const MAX_MANIFEST: u64 = 8 * 1024 * 1024;
const MAX_CAPTURE: u64 = 64 * 1024 * 1024;
const MAX_CLASSES: usize = 16_384;
const MAX_CLASS_BYTES: u64 = 256 * 1024 * 1024;
const VERSION: &[u8] = b"declared-runtime-java-base/1";

#[derive(Clone, Debug)]
pub struct PlatformOptions {
    pub manifest: PathBuf,
    pub contexts: PathBuf,
    pub producer: ContentHash,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct PlatformBinding {
    #[serde(with = "hash_wire")]
    pub identity: ContentHash,
    #[serde(with = "hash_wire")]
    pub capture_sha256: ContentHash,
    #[serde(with = "hash_wire")]
    pub producer_sha256: ContentHash,
}
mod hash_wire {
    use super::*;
    pub fn serialize<S: serde::Serializer>(
        hash: &ContentHash,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&hash.to_string())
    }
    pub fn deserialize<'de, D: serde::Deserializer<'de>>(
        deserializer: D,
    ) -> Result<ContentHash, D::Error> {
        let text = String::deserialize(deserializer)?;
        ContentHash::from_hex(&text).map_err(serde::de::Error::custom)
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct FileRef {
    path: PathBuf,
    sha256: String,
    bytes: u64,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Image {
    canonical_home: PathBuf,
    launcher: FileRef,
    release: FileRef,
    modules: FileRef,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Module {
    archive: FileRef,
    inventory: FileRef,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Policy {
    authority: String,
    module: String,
    complete_inventory: bool,
    historical_compiler_image_proven: bool,
    runtime_isolation_proven: bool,
    lookup: String,
    java_options: Vec<String>,
    environment: BTreeMap<String, Option<String>>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
    schema: String,
    capture_sha256: String,
    context_ids: Vec<String>,
    java_feature: u16,
    image: Image,
    java_base: Module,
    producer_sha256: String,
    policy: Policy,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ClassRow {
    owner: String,
    class_sha256: String,
    bytes: u64,
}
#[derive(Deserialize)]
struct Capture {
    schema_version: String,
    #[serde(default)]
    errors: Vec<serde_json::Value>,
    contexts: Vec<Context>,
    java_runtime: Option<Runtime>,
}
#[derive(Deserialize)]
struct Runtime {
    java_version: String,
}
#[derive(Deserialize)]
struct Context {
    context_id: String,
    java_home: Option<PathBuf>,
    #[serde(default)]
    java_options: Vec<String>,
}

pub struct AdmittedPlatform {
    pub binding: PlatformBinding,
    pub java_feature: u16,
    pub entry: ClasspathEntry,
    pub owners: Vec<String>,
    contexts: BTreeSet<String>,
    inputs: Vec<PathBuf>,
}
impl AdmittedPlatform {
    pub fn contains_context(&self, context: &str) -> bool {
        self.contexts.contains(context)
    }
    pub fn input_files(&self) -> &[PathBuf] {
        &self.inputs
    }
}

fn failure(message: impl std::fmt::Display) -> Error {
    Error::Message(format!("declared runtime platform: {message}"))
}
fn read(path: &Path, maximum: u64) -> Result<Vec<u8>, Error> {
    let mut bytes = Vec::new();
    std::fs::File::open(path)?
        .take(maximum + 1)
        .read_to_end(&mut bytes)?;
    if bytes.len() as u64 > maximum {
        return Err(Error::Limit("platform manifest bytes"));
    }
    Ok(bytes)
}
fn digest(path: &Path, maximum: u64) -> Result<(ContentHash, u64), Error> {
    let metadata = std::fs::symlink_metadata(path)?;
    if !metadata.is_file() || metadata.file_type().is_symlink() || metadata.len() > maximum {
        return Err(failure("file type/size"));
    }
    let mut file = std::fs::File::open(path)?;
    let mut hash = Sha256::new();
    let mut buffer = [0_u8; 65_536];
    let mut size = 0_u64;
    loop {
        let count = file.read(&mut buffer)?;
        if count == 0 {
            break;
        }
        size += count as u64;
        if size > maximum {
            return Err(Error::Limit("platform file bytes"));
        }
        hash.update(&buffer[..count]);
    }
    if size != metadata.len() {
        return Err(failure("file changed during admission"));
    }
    Ok((ContentHash(hash.finalize().into()), size))
}
fn verify(reference: &FileRef, path: &Path, maximum: u64) -> Result<(), Error> {
    let expected = ContentHash::from_hex(&reference.sha256)?;
    let (actual, bytes) = digest(path, maximum)?;
    if expected == ContentHash::default() || actual != expected || bytes != reference.bytes {
        return Err(failure("file hash/size mismatch"));
    }
    Ok(())
}
fn relative(root: &Path, reference: &FileRef) -> Result<PathBuf, Error> {
    if reference.path.as_os_str().is_empty()
        || !reference
            .path
            .components()
            .all(|c| matches!(c, Component::Normal(_)))
    {
        return Err(failure("module artifact path"));
    }
    Ok(root.join(&reference.path))
}
fn feature(version: &str) -> Option<u16> {
    version
        .strip_prefix("1.")
        .unwrap_or(version)
        .split(['.', '-', '+'])
        .next()?
        .parse()
        .ok()
}

pub fn admit(options: &PlatformOptions) -> Result<AdmittedPlatform, Error> {
    let bytes = read(&options.manifest, MAX_MANIFEST)?;
    let manifest: Manifest = serde_json::from_slice(&bytes).map_err(failure)?;
    let producer = ContentHash::from_hex(&manifest.producer_sha256)?;
    let capture_sha256 = ContentHash::from_hex(&manifest.capture_sha256)?;
    let hooks = ["JAVA_TOOL_OPTIONS", "JDK_JAVA_OPTIONS", "_JAVA_OPTIONS"];
    if manifest.schema != "selector-declared-runtime-platform/v1"
        || producer == ContentHash::default()
        || producer != options.producer
        || manifest.java_feature == 0
        || manifest.java_feature > 255
        || manifest.policy.authority != "new_declared_runtime"
        || manifest.policy.module != "java.base"
        || !manifest.policy.complete_inventory
        || manifest.policy.historical_compiler_image_proven
        || manifest.policy.runtime_isolation_proven
        || manifest.policy.lookup != "jrt_filesystem_no_reflective_target_loading"
        || !manifest.policy.java_options.is_empty()
        || manifest.policy.environment.len() != hooks.len()
        || hooks
            .iter()
            .any(|name| !matches!(manifest.policy.environment.get(*name), Some(None)))
        || manifest.context_ids.is_empty()
        || manifest.context_ids.len() > 4096
        || manifest
            .context_ids
            .windows(2)
            .any(|pair| pair[0] >= pair[1])
    {
        return Err(failure("unsupported authority/policy/producer"));
    }
    if digest(&options.contexts, MAX_CAPTURE)?.0 != capture_sha256 {
        return Err(failure("original context capture hash"));
    }
    let input = std::fs::File::open(&options.contexts)?;
    let mut input: Box<dyn Read> = if options.contexts.extension().is_some_and(|e| e == "gz") {
        Box::new(MultiGzDecoder::new(input))
    } else {
        Box::new(input)
    };
    let mut capture_bytes = Vec::new();
    input
        .by_ref()
        .take(MAX_CAPTURE + 1)
        .read_to_end(&mut capture_bytes)?;
    if capture_bytes.len() as u64 > MAX_CAPTURE {
        return Err(Error::Limit("platform context bytes"));
    }
    let capture: Capture = serde_json::from_slice(&capture_bytes).map_err(failure)?;
    let contexts: BTreeMap<_, _> = capture
        .contexts
        .iter()
        .map(|c| (c.context_id.as_str(), c))
        .collect();
    if capture.schema_version != "sbt-compiler-context/v1"
        || !capture.errors.is_empty()
        || contexts.len() != capture.contexts.len()
        || capture
            .java_runtime
            .as_ref()
            .and_then(|r| feature(&r.java_version))
            != Some(manifest.java_feature)
        || manifest.context_ids.iter().any(|name| {
            contexts
                .get(name.as_str())
                .is_none_or(|c| c.java_home.is_some() || !c.java_options.is_empty())
        })
    {
        return Err(failure("context scope/runtime options"));
    }
    let home = &manifest.image.canonical_home;
    if !home.is_absolute() || std::fs::canonicalize(home)? != *home {
        return Err(failure("canonical runtime home"));
    }
    for (reference, suffix, limit) in [
        (&manifest.image.launcher, "bin/java", 32 * 1024 * 1024),
        (&manifest.image.release, "release", 1024 * 1024),
        (&manifest.image.modules, "lib/modules", 512 * 1024 * 1024),
    ] {
        if reference.path != home.join(suffix) {
            return Err(failure("runtime image path"));
        }
        verify(reference, &reference.path, limit)?;
    }
    let manifest_path = std::fs::canonicalize(&options.manifest)?;
    let root = manifest_path
        .parent()
        .ok_or_else(|| failure("manifest parent"))?;
    let archive = relative(root, &manifest.java_base.archive)?;
    let inventory = relative(root, &manifest.java_base.inventory)?;
    verify(&manifest.java_base.archive, &archive, 128 * 1024 * 1024)?;
    verify(&manifest.java_base.inventory, &inventory, MAX_MANIFEST)?;
    let classes: Vec<ClassRow> =
        serde_json::from_slice(&read(&inventory, MAX_MANIFEST)?).map_err(failure)?;
    if classes.is_empty()
        || classes.len() > MAX_CLASSES
        || classes
            .windows(2)
            .any(|rows| rows[0].owner >= rows[1].owner)
        || classes
            .iter()
            .try_fold(0_u64, |sum, row| sum.checked_add(row.bytes))
            .is_none_or(|n| n > MAX_CLASS_BYTES)
    {
        return Err(failure("class inventory order/size"));
    }
    let entry = ClasspathEntry {
        path: archive.clone(),
        sha256: ContentHash::from_hex(&manifest.java_base.archive.sha256)?,
        kind: EntryKind::Jar,
    };
    let mut limits = Limits::default();
    limits.max_archive_bytes = 128 * 1024 * 1024;
    let mut loader = CapturedClasspath::new(vec![entry.clone()], limits)
        .and_then(|loader| loader.with_java_feature(Some(manifest.java_feature)))
        .map_err(failure)?;
    let owners = loader.class_names(0).map_err(failure)?;
    if !owners
        .iter()
        .map(String::as_str)
        .eq(classes.iter().map(|row| row.owner.as_str()))
    {
        return Err(failure("archive/inventory membership"));
    }
    for row in &classes {
        let ClassLookup::Found(found) = loader.lookup(&row.owner).map_err(failure)? else {
            return Err(failure("inventoried class unavailable"));
        };
        if found.bytes.len() as u64 != row.bytes
            || found.proof.class_hash != Some(ContentHash::from_hex(&row.class_sha256)?)
        {
            return Err(failure("class inventory hash/size"));
        }
    }
    let mut hash = Sha256::new();
    hash.update(VERSION);
    hash.update(&bytes);
    let binding = PlatformBinding {
        identity: ContentHash(hash.finalize().into()),
        capture_sha256,
        producer_sha256: producer,
    };
    Ok(AdmittedPlatform {
        binding,
        java_feature: manifest.java_feature,
        entry,
        owners,
        contexts: manifest.context_ids.into_iter().collect(),
        inputs: vec![
            options.manifest.clone(),
            options.contexts.clone(),
            manifest.image.launcher.path,
            manifest.image.release.path,
            manifest.image.modules.path,
            archive,
            inventory,
        ],
    })
}
