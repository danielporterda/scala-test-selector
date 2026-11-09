//! Hash-bound external runtime metadata. Owned buffers live for one graph build;
//! the model borrows their text and retains only compact graph contributions.
use selector_facts::FactSnapshot;
use selector_models::runtime::{RuntimeInputs, RuntimeSource};
use selector_types::{ContentHash, Error};
use serde::Deserialize;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::path::{Path, PathBuf};

#[path = "runtime_capture.rs"]
mod capture;
pub use capture::{RuntimeCaptureOptions, RuntimeCaptureReceipt, capture_git_runtime};

#[path = "runtime_delta.rs"]
mod delta;
pub use delta::{
    MAX_RUNTIME_CHANGE_CAUSES, RuntimeChangeCause, RuntimeChangeReason, RuntimeChangeSeeds,
    RuntimeInputChanges, RuntimeSnapshotSide, runtime_change_seeds, runtime_input_changes,
};

const MAX_MANIFEST: u64 = 8 * 1024 * 1024;
const MAX_FILE: u64 = 64 * 1024 * 1024;
const MAX_TOTAL: u64 = 512 * 1024 * 1024;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
    version: u32,
    revision: Option<String>,
    facts_identity: Option<String>,
    #[serde(default)]
    sources: Vec<Source>,
    #[serde(default)]
    generator_packages: Vec<String>,
    overlay: Option<FileRef>,
    ci_catalogue: Option<FileRef>,
    #[serde(default)]
    suite_catalogues: Vec<Source>,
    #[serde(default)]
    compiler_inventory_complete: bool,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Source {
    path: String,
    file: PathBuf,
    sha256: String,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct FileRef {
    file: PathBuf,
    sha256: String,
}

pub struct OwnedRuntimeInputs {
    sources: Vec<(String, String)>,
    packages: Vec<String>,
    overlay: Option<String>,
    pub identity: ContentHash,
    inventory_complete: bool,
    suite_catalogues: BTreeMap<String, BTreeSet<String>>,
}

#[derive(Deserialize)]
struct CiCatalogue {
    schema_version: String,
    revision: String,
    complete: bool,
    families: Vec<CiFamily>,
    suite_names: BTreeSet<String>,
    source_receipts: Vec<CiReceipt>,
}
#[derive(Deserialize)]
struct CiFamily {
    catalogue: String,
    suites: BTreeSet<String>,
}
#[derive(Deserialize)]
struct CiReceipt {
    path: PathBuf,
    sha256: String,
    bytes: u64,
}
fn root_catalogue_path(path: &str) -> bool {
    let mut components = Path::new(path).components();
    matches!(components.next(), Some(std::path::Component::Normal(_)))
        && components.next().is_none()
}

fn catalogue_names(text: &str) -> Result<BTreeSet<String>, Error> {
    let mut names = BTreeSet::new();
    for line in text.lines() {
        if line.is_empty()
            || line.trim() != line
            || !line.contains('.')
            || !line.split('.').all(|part| {
                !part.is_empty()
                    && part
                        .bytes()
                        .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'$'))
            })
            || !names.insert(line.to_owned())
        {
            return Err(Error::Invalid(
                "suite catalogue must contain unique qualified compiler suite names",
            ));
        }
    }
    Ok(names)
}
fn admit_ci_catalogue(text: &str, facts: &FactSnapshot) -> Result<CiCatalogue, Error> {
    let catalogue: CiCatalogue = serde_json::from_str(text)
        .map_err(|error| Error::Message(format!("runtime CI catalogue JSON: {error}")))?;
    let names: BTreeSet<_> = facts
        .suites
        .iter()
        .map(|suite| facts.text(suite.name).to_owned())
        .collect();
    let family_names: BTreeSet<_> = catalogue
        .families
        .iter()
        .flat_map(|family| family.suites.iter().cloned())
        .collect();
    if catalogue.schema_version != "compiler-ci-catalogue/v1"
        || !catalogue.complete
        || catalogue.revision != facts.text(facts.revision)
        || catalogue.suite_names != names
        || family_names != names
    {
        return Err(Error::Invalid(
            "runtime CI catalogue must match the complete extracted suite inventory and revision",
        ));
    }
    Ok(catalogue)
}
impl OwnedRuntimeInputs {
    pub fn borrow(&self) -> RuntimeInputs<'_> {
        RuntimeInputs {
            sources: self
                .sources
                .iter()
                .map(|(path, text)| RuntimeSource { path, text })
                .collect(),
            generator_packages: self.packages.iter().map(String::as_str).collect(),
            overlay_json: self.overlay.as_deref(),
            manifest_identity: self.identity,
            compiler_inventory_complete: self.inventory_complete,
        }
    }
}
fn read_bounded(path: &Path, max: u64, total: &mut u64) -> Result<Vec<u8>, Error> {
    use std::io::Read;
    let file = std::fs::File::open(path)?;
    let size = file.metadata()?.len();
    if size > max || total.checked_add(size).is_none_or(|n| n > MAX_TOTAL) {
        return Err(Error::Limit("runtime metadata bytes"));
    }
    let mut bytes = Vec::with_capacity(
        usize::try_from(size).map_err(|_| Error::Limit("runtime metadata file size"))?,
    );
    file.take(max + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 > max
        || total
            .checked_add(bytes.len() as u64)
            .is_none_or(|n| n > MAX_TOTAL)
    {
        return Err(Error::Limit("runtime metadata bytes"));
    }
    *total += bytes.len() as u64;
    Ok(bytes)
}
fn verified_text(
    base: &Path,
    file: &Path,
    expected: &str,
    total: &mut u64,
    hash: &mut Sha256,
) -> Result<String, Error> {
    let path = if file.is_absolute() {
        file.to_owned()
    } else {
        base.join(file)
    };
    let bytes = read_bounded(&path, MAX_FILE, total)?;
    let digest = ContentHash(Sha256::digest(&bytes).into());
    if digest != ContentHash::from_hex(expected)? {
        return Err(Error::Message(format!(
            "runtime metadata hash mismatch: {}",
            path.display()
        )));
    }
    hash.update((bytes.len() as u64).to_le_bytes());
    hash.update(&bytes);
    String::from_utf8(bytes).map_err(|_| Error::Invalid("runtime metadata UTF-8"))
}
pub fn load_runtime_manifest(
    path: &Path,
    facts: &FactSnapshot,
) -> Result<OwnedRuntimeInputs, Error> {
    let mut total = 0;
    let bytes = read_bounded(path, MAX_MANIFEST, &mut total)?;
    let manifest: Manifest = serde_json::from_slice(&bytes)
        .map_err(|e| Error::Message(format!("runtime manifest JSON: {e}")))?;
    if manifest.version != 1 {
        return Err(Error::Invalid("runtime manifest version"));
    }
    if manifest.revision.is_none() && manifest.facts_identity.is_none() {
        return Err(Error::Invalid("runtime manifest fact binding"));
    }
    if manifest
        .revision
        .as_deref()
        .is_some_and(|revision| revision.is_empty() || revision != facts.text(facts.revision))
    {
        return Err(Error::Invalid("runtime manifest revision"));
    }
    if manifest
        .facts_identity
        .as_deref()
        .map(ContentHash::from_hex)
        .transpose()?
        .is_some_and(|id| id != facts.identity)
    {
        return Err(Error::Invalid("runtime manifest facts identity"));
    }
    let mut hash = Sha256::new();
    if manifest.generator_packages.iter().any(|package| {
        package.is_empty()
            || !package.split('.').all(|part| {
                !part.is_empty()
                    && part.bytes().enumerate().all(|(i, b)| {
                        b.is_ascii_alphabetic() || b == b'_' || (i > 0 && b.is_ascii_digit())
                    })
            })
    }) {
        return Err(Error::Invalid("runtime generator package literal"));
    }
    hash.update(b"runtime-input-manifest/1");
    hash.update(&bytes);
    let base = path.parent().unwrap_or(Path::new("."));
    let catalogue = manifest
        .ci_catalogue
        .map(|file| {
            verified_text(base, &file.file, &file.sha256, &mut total, &mut hash)
                .and_then(|text| admit_ci_catalogue(&text, facts))
        })
        .transpose()?;
    let mut sources = Vec::with_capacity(manifest.sources.len());
    let mut paths = HashSet::new();
    for source in manifest.sources {
        if source.path.is_empty() || !paths.insert(source.path.clone()) {
            return Err(Error::Invalid("duplicate runtime logical source path"));
        }
        let text = verified_text(base, &source.file, &source.sha256, &mut total, &mut hash)?;
        sources.push((source.path, text));
    }
    let mut suite_catalogues = BTreeMap::new();
    for source in manifest.suite_catalogues {
        let Some(catalogue) = &catalogue else {
            return Err(Error::Invalid(
                "suite catalogue input requires captured CI catalogue",
            ));
        };
        if !root_catalogue_path(&source.path) || !paths.insert(source.path.clone()) {
            return Err(Error::Invalid("duplicate or non-root suite catalogue path"));
        }
        let text = verified_text(base, &source.file, &source.sha256, &mut total, &mut hash)?;
        let names = catalogue_names(&text)?;
        let families: Vec<_> = catalogue
            .families
            .iter()
            .filter(|family| family.catalogue == source.path)
            .collect();
        let family_names: BTreeSet<_> = families
            .iter()
            .flat_map(|family| family.suites.iter().cloned())
            .collect();
        let digest = ContentHash::from_hex(&source.sha256)?;
        if families.is_empty()
            || names != family_names
            || !catalogue.source_receipts.iter().any(|receipt| {
                receipt.path.file_name() == Some(std::ffi::OsStr::new(&source.path))
                    && receipt.bytes == text.len() as u64
                    && ContentHash::from_hex(&receipt.sha256).ok() == Some(digest)
            })
        {
            return Err(Error::Invalid(
                "suite catalogue differs from captured CI family or source receipt",
            ));
        }
        suite_catalogues.insert(source.path, names);
    }
    let overlay = manifest
        .overlay
        .map(|file| verified_text(base, &file.file, &file.sha256, &mut total, &mut hash))
        .transpose()?;
    Ok(OwnedRuntimeInputs {
        sources,
        packages: manifest.generator_packages,
        overlay,
        identity: ContentHash(hash.finalize().into()),
        inventory_complete: manifest.compiler_inventory_complete,
        suite_catalogues,
    })
}
