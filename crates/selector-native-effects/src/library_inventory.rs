//! Provider-level trust for the conditional application-impact diagnostic.
//! This issues no strict native recipe, dispatch, initialization or VM closure.
use crate::provider::{self, ResolutionState, VerifiedProvider};
use selector_facts::FactSnapshot;
use selector_models::binary::{self, EntryKind};
use selector_types::*;
use sha2::{Digest, Sha256};
use std::collections::{HashMap, HashSet};

pub const VERSION: &str = "trusted-library-file-inventory/1";

/// An explicit component policy. Trust is never inferred from a package,
/// filename, Maven spelling, method name or a matching individual class SHA.
/// A normally admitted declared java.base is included under this policy;
/// dependency archives require an exact nonzero provider digest here.
pub struct TrustPolicy {
    archives: Vec<ContentHash>,
    identity: ContentHash,
}
impl TrustPolicy {
    pub fn new(mut archives: Vec<ContentHash>) -> Result<Self, Error> {
        if archives.len() > 4096 || archives.contains(&ContentHash::default()) {
            return Err(Error::Invalid("trusted provider policy"));
        }
        archives.sort_unstable_by_key(|hash| hash.0);
        if archives.windows(2).any(|p| p[0] == p[1]) {
            return Err(Error::Invalid("duplicate trusted provider policy"));
        }
        let mut digest = Sha256::new();
        digest.update(VERSION);
        digest.update(b"explicit-archives-and-admitted-java.base\0");
        for archive in &archives {
            digest.update(archive.0);
        }
        Ok(Self {
            archives,
            identity: ContentHash(digest.finalize().into()),
        })
    }
    pub fn identity(&self) -> ContentHash {
        self.identity
    }
    pub fn archives(&self) -> &[ContentHash] {
        &self.archives
    }
    fn contains(&self, hash: ContentHash) -> bool {
        self.archives.binary_search_by_key(&hash.0, |h| h.0).is_ok()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProviderOrigin {
    DeclaredRuntime,
    DependencyArchive,
    ApplicationProduct,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProviderBinding {
    pub context: StrId,
    pub identity: ContentHash,
    pub origin: ProviderOrigin,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TrustedFile {
    pub file: FileId,
    pub provider: u32,
    pub class_sha256: ContentHash,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FileProof {
    pub file: FileId,
    pub provider_sha256: ContentHash,
    pub selected_entry: u32,
    pub prefix_sha256: ContentHash,
    pub resolution_sha256: ContentHash,
    pub declared_platform: Option<ContentHash>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Denial {
    SourceOwned,
    Conflict,
    MissingContext,
    InvalidOrigin,
    UnresolvedProvider,
    ApplicationProduct,
    OutsidePolicy,
    FileBinding,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DeniedFile {
    pub file: FileId,
    pub reason: Denial,
}
#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub files: usize,
    pub providers: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            files: 100_000,
            providers: 65_535,
        }
    }
}
#[derive(Debug)]
pub enum Error {
    Invalid(&'static str),
    Budget,
    Facts(selector_types::Error),
    Provider(provider::Error),
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "library inventory {self:?}")
    }
}
impl std::error::Error for Error {}
impl From<selector_types::Error> for Error {
    fn from(e: selector_types::Error) -> Self {
        Self::Facts(e)
    }
}
impl From<provider::Error> for Error {
    fn from(e: provider::Error) -> Self {
        Self::Provider(e)
    }
}

pub struct LibraryInventory {
    identity: ContentHash,
    facts_identity: ContentHash,
    provider_identity: ContentHash,
    policy_identity: ContentHash,
    providers: Vec<ProviderBinding>,
    files: Vec<TrustedFile>,
    proofs: Vec<FileProof>,
    denied: Vec<DeniedFile>,
}
impl LibraryInventory {
    pub fn identity(&self) -> ContentHash {
        self.identity
    }
    pub fn facts_identity(&self) -> ContentHash {
        self.facts_identity
    }
    pub fn provider_identity(&self) -> ContentHash {
        self.provider_identity
    }
    pub fn policy_identity(&self) -> ContentHash {
        self.policy_identity
    }
    pub fn providers(&self) -> &[ProviderBinding] {
        &self.providers
    }
    pub fn files(&self) -> &[TrustedFile] {
        &self.files
    }
    pub fn file_proofs(&self) -> &[FileProof] {
        &self.proofs
    }
    pub fn denials(&self) -> &[DeniedFile] {
        &self.denied
    }
}

/// Revalidate every candidate file against immutable first-provider resolution.
/// Denials remain untrusted application frontiers. Invalid physical provenance
/// is fatal, and resource refusal cannot become a successful empty inventory.
pub fn issue(
    facts: &FactSnapshot,
    provider: &mut VerifiedProvider<'_>,
    policy: &TrustPolicy,
    limits: Limits,
) -> Result<LibraryInventory, Error> {
    facts.validate()?;
    if facts.identity == ContentHash::default()
        || limits.providers == 0
        || limits.providers >= u32::MAX as usize
    {
        return Err(Error::Invalid("inventory snapshot or limits"));
    }
    let count = facts
        .files
        .iter()
        .filter(|file| file.flags & FILE_BINARY_SOURCE != 0)
        .count();
    if count > limits.files {
        return Err(Error::Budget);
    }
    let mut source_owned = vec![false; facts.files.len()];
    for symbol in &facts.symbols {
        if symbol.flags & SYMBOL_DEFINED != 0 && !symbol.file.is_none() {
            source_owned[symbol.file.index()] = true;
        }
    }
    let mut conflicts = HashSet::new();
    let mut conflicted_symbols = HashSet::new();
    let mut global_conflict = false;
    for issue in &facts.issues {
        if issue.kind != IssueKind::ContextConflict {
            continue;
        }
        if !issue.file.is_none() {
            conflicts.insert(issue.file);
        }
        if !issue.symbol.is_none() {
            conflicted_symbols.insert(issue.symbol);
            let file = facts.symbols[issue.symbol.index()].file;
            if !file.is_none() {
                conflicts.insert(file);
            }
        } else if issue.file.is_none() {
            global_conflict = true;
        }
    }
    for body in &facts.bodies {
        let symbol = facts.symbols[body.symbol.index()];
        if body.flags & BODY_BINARY_RECIPE == 0 || symbol.flags & SYMBOL_DEFINED != 0 {
            source_owned[body.file.index()] = true;
        }
        // Compiler source ambiguity remains a source-reference frontier. It
        // does not contradict unrelated physical provider/class authority.
        // Exact native method/declaring-owner conflicts still revoke its file.
        if conflicted_symbols.contains(&body.symbol) || conflicted_symbols.contains(&symbol.owner) {
            conflicts.insert(body.file);
        }
    }
    let mut out = LibraryInventory {
        identity: ContentHash::default(),
        facts_identity: facts.identity,
        provider_identity: ContentHash(provider.identity()),
        policy_identity: policy.identity(),
        providers: Vec::new(),
        files: Vec::new(),
        proofs: Vec::new(),
        denied: Vec::new(),
    };
    out.files
        .try_reserve_exact(count)
        .map_err(|_| Error::Budget)?;
    out.proofs
        .try_reserve_exact(count)
        .map_err(|_| Error::Budget)?;
    out.denied
        .try_reserve_exact(count)
        .map_err(|_| Error::Budget)?;
    let mut provider_ids = HashMap::new();
    for (index, file) in facts.files.iter().enumerate() {
        if file.flags & FILE_BINARY_SOURCE == 0 {
            continue;
        }
        let id = FileId(index as u32);
        let result = (|| {
            if file.flags != FILE_BINARY_SOURCE || source_owned[index] {
                return Ok(Err(Denial::SourceOwned));
            }
            if global_conflict || conflicts.contains(&id) {
                return Ok(Err(Denial::Conflict));
            }
            let Some(authority) = provider.authority(facts.text(file.context)) else {
                return Ok(Err(Denial::MissingContext));
            };
            let Some((_, suffix)) = facts.text(file.path).rsplit_once("!/") else {
                return Ok(Err(Denial::InvalidOrigin));
            };
            let Some(owner) = suffix.strip_suffix(".class").filter(|s| !s.is_empty()) else {
                return Ok(Err(Denial::InvalidOrigin));
            };
            let (bytes, receipt) = provider.resolve(authority, owner)?;
            if receipt.state != ResolutionState::Found {
                return Ok(Err(Denial::UnresolvedProvider));
            }
            let (entry, application, declared) = provider.inventory_entry(&receipt)?;
            if application || !matches!(entry.kind, EntryKind::Jar) {
                return Ok(Err(Denial::ApplicationProduct));
            }
            if declared.is_none() && !policy.contains(entry.sha256) {
                return Ok(Err(Denial::OutsidePolicy));
            }
            let expected_path = format!("{}!/{owner}.class", entry.path.display());
            let Some(bytes) = bytes else {
                return Err(Error::Invalid("found provider without bytes"));
            };
            let class = binary::parse_class(&bytes, binary::Limits::default())
                .map_err(|_| Error::Invalid("trusted class structure"))?;
            if class.name != owner
                || facts.text(file.path) != expected_path
                || receipt.class_sha256 != Some(file.source_hash.0)
                || file.source_hash == ContentHash::default()
                || file.revision != facts.revision
                || !facts.text(file.source).is_empty()
            {
                return Ok(Err(Denial::FileBinding));
            }
            let mut digest = Sha256::new();
            digest.update(VERSION);
            digest.update(out.provider_identity.0);
            digest.update(policy.identity().0);
            digest.update(file.context.0.to_le_bytes());
            digest.update((facts.text(file.context).len() as u64).to_le_bytes());
            digest.update(facts.text(file.context).as_bytes());
            digest.update(receipt.selected_entry.unwrap().to_le_bytes());
            digest.update(entry.sha256.0);
            digest.update(declared.unwrap_or_default());
            let identity = ContentHash(digest.finalize().into());
            let key = (file.context, identity);
            let provider_id = if let Some(&id) = provider_ids.get(&key) {
                id
            } else {
                if out.providers.len() >= limits.providers {
                    return Err(Error::Budget);
                }
                let id = out.providers.len() as u32;
                out.providers.push(ProviderBinding {
                    context: file.context,
                    identity,
                    origin: if declared.is_some() {
                        ProviderOrigin::DeclaredRuntime
                    } else {
                        ProviderOrigin::DependencyArchive
                    },
                });
                provider_ids.insert(key, id);
                id
            };
            Ok(Ok((
                TrustedFile {
                    file: id,
                    provider: provider_id,
                    class_sha256: file.source_hash,
                },
                FileProof {
                    file: id,
                    provider_sha256: entry.sha256,
                    selected_entry: receipt.selected_entry.unwrap(),
                    prefix_sha256: ContentHash(receipt.prefix_sha256),
                    resolution_sha256: ContentHash(receipt.binding_sha256),
                    declared_platform: declared.map(ContentHash),
                },
            )))
        })();
        match result? {
            Ok((file, proof)) => {
                out.files.push(file);
                out.proofs.push(proof);
            }
            Err(reason) => out.denied.push(DeniedFile { file: id, reason }),
        }
    }
    let mut digest = Sha256::new();
    digest.update(VERSION);
    digest.update(producer_sha256().0);
    digest.update(out.facts_identity.0);
    digest.update(out.provider_identity.0);
    digest.update(out.policy_identity.0);
    for row in &out.providers {
        digest.update(row.context.0.to_le_bytes());
        digest.update(row.identity.0);
        digest.update([row.origin as u8]);
    }
    for (row, proof) in out.files.iter().zip(&out.proofs) {
        digest.update(row.file.0.to_le_bytes());
        digest.update(row.provider.to_le_bytes());
        digest.update(row.class_sha256.0);
        digest.update(proof.provider_sha256.0);
        digest.update(proof.selected_entry.to_le_bytes());
        digest.update(proof.prefix_sha256.0);
        digest.update(proof.resolution_sha256.0);
        digest.update(proof.declared_platform.unwrap_or_default().0);
    }
    for row in &out.denied {
        digest.update(row.file.0.to_le_bytes());
        digest.update([row.reason as u8]);
    }
    out.identity = ContentHash(digest.finalize().into());
    Ok(out)
}

pub fn producer_sha256() -> ContentHash {
    let mut digest = Sha256::new();
    digest.update(VERSION);
    for bytes in [
        include_bytes!("library_inventory.rs").as_slice(),
        include_bytes!("provider.rs").as_slice(),
        include_bytes!("../Cargo.toml").as_slice(),
        include_bytes!("../../selector-models/src/binary.rs").as_slice(),
        include_bytes!("../../selector-models/src/binary_metadata.rs").as_slice(),
        include_bytes!("../../selector-runtime-platform/src/lib.rs").as_slice(),
        include_bytes!("../../selector-runtime-platform/Cargo.toml").as_slice(),
        include_bytes!("../../selector-facts/src/lib.rs").as_slice(),
        include_bytes!("../../selector-facts/src/validation.rs").as_slice(),
        include_bytes!("../../selector-types/src/lib.rs").as_slice(),
    ] {
        digest.update((bytes.len() as u64).to_le_bytes());
        digest.update(bytes);
    }
    ContentHash(digest.finalize().into())
}

#[cfg(test)]
#[path = "library_inventory_tests.rs"]
mod tests;
