//! Conditional absence of requested source products from owning test providers.
//! No execution or whole-checkout equivalence claim is made by this module.
use crate::provider::{self, InputPin, ProviderOptions, ResolutionState, VerifiedProvider};
use selector_facts::FactSnapshot;
use selector_models::binary::{self, ClasspathEntry, EntryKind};
use selector_runtime_platform::PlatformOptions;
use selector_types::*;
use serde::Deserialize;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::io::Read;
use std::path::{Component, Path, PathBuf};

pub const VERSION: &str = "captured-source-classpath-absence/1";
pub const REQUEST_SCHEMA: &str = "selector-classpath-absence-request/v1";
pub const REQUIRED_BITS: u32 = SelectionContract::CURRENT_BASE_BITS
    | SelectionContract::SUITE_INDEPENDENCE
    | SelectionContract::OWNING_TEST_CLASSPATH;

#[derive(Debug)]
pub enum Error {
    Invalid(&'static str),
    Budget,
    Io(std::io::Error),
    Json(serde_json::Error),
    Provider(provider::Error),
    Facts(selector_types::Error),
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "classpath absence {self:?}")
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
impl From<provider::Error> for Error {
    fn from(e: provider::Error) -> Self {
        Self::Provider(e)
    }
}
impl From<selector_types::Error> for Error {
    fn from(e: selector_types::Error) -> Self {
        Self::Facts(e)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceProduct {
    pub file: FileId,
    pub owner_context: StrId,
    pub products_identity: ContentHash,
    pub product_count: u32,
}

#[derive(Clone, Debug)]
pub struct AbsentSource {
    pub path: String,
    pub opposite_facts: ContentHash,
    pub absence_identity: ContentHash,
}
/// Exact native materialization of one positively attributed requested source.
/// Unknown SourceFile attribution is sufficient for conservative absence scans,
/// but never sufficient to authorize an additional effective input seed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProductFile {
    pub file: FileId,
    pub source_file: FileId,
    pub owner_context: StrId,
    pub class_sha256: ContentHash,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SuiteClasspath {
    pub suite: SuiteId,
    pub owner_context: StrId,
    pub classpath_identity: ContentHash,
    pub source_products_identity: ContentHash,
    pub absence_identity: ContentHash,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Denial {
    CatalogueOwner,
    UnsupportedSuite,
    ProductPresent,
    ClassPresent,
    UnknownProvider,
    UncapturedManifestTarget,
    CompileDependencyPresent,
    UnknownCompileOwner,
}
#[derive(Clone, Copy, Debug)]
pub struct DeniedSuite {
    pub suite: SuiteId,
    pub reason: Denial,
}
#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub source_files: usize,
    pub suites: usize,
    pub classes: usize,
    pub inventory_names: usize,
    pub physical_files: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            source_files: 10_000,
            suites: 100_000,
            classes: 100_000,
            inventory_names: 2_000_000,
            physical_files: 100_000,
        }
    }
}

pub struct Issued {
    identity: ContentHash,
    facts: ContentHash,
    capture: ContentHash,
    runtime: ContentHash,
    products: ContentHash,
    sources: Vec<SourceProduct>,
    absent_sources: Vec<AbsentSource>,
    product_files: Vec<ProductFile>,
    suites: Vec<SuiteClasspath>,
    denied: Vec<DeniedSuite>,
    inputs: PhysicalInputs,
}
impl Issued {
    pub fn identity(&self) -> ContentHash {
        self.identity
    }
    pub fn facts_identity(&self) -> ContentHash {
        self.facts
    }
    pub fn capture_identity(&self) -> ContentHash {
        self.capture
    }
    pub fn runtime_contract_identity(&self) -> ContentHash {
        self.runtime
    }
    pub fn source_products_identity(&self) -> ContentHash {
        self.products
    }
    pub fn sources(&self) -> &[SourceProduct] {
        &self.sources
    }
    pub fn absent_sources(&self) -> &[AbsentSource] {
        &self.absent_sources
    }
    pub fn product_files(&self) -> &[ProductFile] {
        &self.product_files
    }
    pub fn suites(&self) -> &[SuiteClasspath] {
        &self.suites
    }
    pub fn denials(&self) -> &[DeniedSuite] {
        &self.denied
    }
    pub fn inputs(&self) -> &PhysicalInputs {
        &self.inputs
    }
    pub fn revalidate(&self) -> Result<(), Error> {
        self.inputs.revalidate()
    }
}
#[derive(Default)]
pub struct PhysicalInputs {
    pub files: Vec<InputPin>,
    pub directories: Vec<ClasspathEntry>,
    pub absent: Vec<PathBuf>,
}
impl PhysicalInputs {
    pub fn paths(&self) -> Vec<PathBuf> {
        self.files
            .iter()
            .map(|p| p.path.clone())
            .chain(self.directories.iter().map(|p| p.path.clone()))
            .chain(self.absent.iter().cloned())
            .collect()
    }
    pub fn revalidate(&self) -> Result<(), Error> {
        for pin in &self.files {
            verify_pin(pin)?;
        }
        for entry in &self.directories {
            let admitted =
                binary::AdmittedEntry::admit(entry.clone(), binary::Limits::default(), None)
                    .map_err(|e| Error::Provider(provider::Error::Native(e)))?;
            if let Some(e) = admitted.error() {
                return Err(Error::Provider(provider::Error::Native(e)));
            }
        }
        for path in &self.absent {
            require_absent(path)?;
        }
        Ok(())
    }
}

#[derive(Deserialize)]
struct Capture {
    revision: String,
    source_root: PathBuf,
    source_to_contexts: HashMap<String, Vec<String>>,
    contexts: Vec<Context>,
    input_objects: Vec<Object>,
}
#[derive(Deserialize)]
struct Context {
    context_id: String,
    configuration: String,
    #[serde(default)]
    products: Vec<PathBuf>,
    #[serde(default)]
    exported_products: Vec<Product>,
    #[serde(default)]
    source_records: Vec<Source>,
    full_classpath: Vec<Cp>,
    dependency_classpath: Vec<Cp>,
    #[serde(default)]
    defined_tests: Vec<Defined>,
}
#[derive(Deserialize)]
struct Product {
    path: PathBuf,
    sha256: String,
    input_object: Option<String>,
}
#[derive(Deserialize)]
struct Source {
    path: PathBuf,
    repo_relative_path: String,
    input_object: Option<String>,
    sha256: String,
}
#[derive(Deserialize)]
struct Cp {
    index: usize,
    path: PathBuf,
    sha256: String,
    #[serde(default)]
    project_output_origins: Vec<Origin>,
}
#[derive(Deserialize)]
struct Origin {
    context_id: String,
}
#[derive(Deserialize)]
struct Defined {
    name: String,
    fingerprint: serde_json::Value,
}
#[derive(Deserialize)]
struct Object {
    path: PathBuf,
    kind: String,
    sha256: String,
    bytes: u64,
}
#[derive(Deserialize)]
struct Catalogue {
    schema_version: String,
    complete: bool,
    issues: Vec<serde_json::Value>,
    suites: Vec<CatalogueSuite>,
}
#[derive(Deserialize)]
struct CatalogueSuite {
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
struct Attribution {
    name: String,
    source: Option<String>,
    hash: ContentHash,
}

/// An origin label alone is not output ownership. Require the same captured
/// producer to export this exact path and fingerprint before narrowing names.
fn bound_project_output(row: &Cp, contexts: &HashMap<&str, &Context>) -> bool {
    !row.project_output_origins.is_empty()
        && row.project_output_origins.iter().all(|origin| {
            contexts
                .get(origin.context_id.as_str())
                .is_some_and(|producer| {
                    producer.products.contains(&row.path)
                        && producer
                            .exported_products
                            .iter()
                            .filter(|p| p.path == row.path)
                            .count()
                            == 1
                        && producer
                            .exported_products
                            .iter()
                            .any(|p| p.path == row.path && p.sha256 == row.sha256)
                })
        })
}

fn hash(bytes: &[u8]) -> ContentHash {
    ContentHash(Sha256::digest(bytes).into())
}
fn text(d: &mut Sha256, s: &str) {
    d.update((s.len() as u64).to_le_bytes());
    d.update(s.as_bytes());
}
fn normal_relative(path: &Path) -> bool {
    !path.as_os_str().is_empty() && path.components().all(|c| matches!(c, Component::Normal(_)))
}
fn no_symlinks(path: &Path) -> Result<(), Error> {
    if !path.is_absolute()
        || !path
            .components()
            .all(|c| matches!(c, Component::RootDir | Component::Normal(_)))
    {
        return Err(Error::Invalid("physical path"));
    }
    let mut current = PathBuf::new();
    for part in path.components() {
        current.push(part.as_os_str());
        match std::fs::symlink_metadata(&current) {
            Ok(m) if m.file_type().is_symlink() => {
                return Err(Error::Invalid("symlink physical input"));
            }
            Ok(_) => (),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => break,
            Err(e) => return Err(e.into()),
        }
    }
    Ok(())
}
pub(crate) fn require_absent(path: &Path) -> Result<(), Error> {
    no_symlinks(path)?;
    match std::fs::symlink_metadata(path) {
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(e) => Err(e.into()),
        Ok(_) => Err(Error::Invalid("manifest absence changed")),
    }
}
fn read_pin(pin: &InputPin, limit: u64) -> Result<Vec<u8>, Error> {
    no_symlinks(&pin.path)?;
    let file = std::fs::File::open(&pin.path)?;
    if file.metadata()?.len() != pin.bytes || pin.bytes > limit {
        return Err(Error::Invalid("physical file size"));
    }
    let mut bytes = Vec::new();
    file.take(limit.saturating_add(1)).read_to_end(&mut bytes)?;
    if bytes.len() as u64 != pin.bytes || hash(&bytes).0 != pin.sha256 {
        return Err(Error::Invalid("physical file hash"));
    }
    Ok(bytes)
}
fn verify_pin(pin: &InputPin) -> Result<(), Error> {
    no_symlinks(&pin.path)?;
    let mut file = std::fs::File::open(&pin.path)?;
    if file.metadata()?.len() != pin.bytes {
        return Err(Error::Invalid("physical file size"));
    }
    let mut hash = Sha256::new();
    let mut buffer = [0u8; 64 * 1024];
    let mut bytes = 0u64;
    loop {
        let read = file.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        bytes = bytes.checked_add(read as u64).ok_or(Error::Budget)?;
        if bytes > pin.bytes {
            return Err(Error::Invalid("physical file size"));
        }
        hash.update(&buffer[..read]);
    }
    let actual: [u8; 32] = hash.finalize().into();
    if bytes != pin.bytes || actual != pin.sha256 {
        return Err(Error::Invalid("physical file hash"));
    }
    Ok(())
}
fn entry_hash(d: &mut Sha256, entry: &ClasspathEntry) {
    text(d, &entry.path.to_string_lossy());
    d.update(entry.sha256.0);
    match entry.kind {
        EntryKind::Jar => d.update([0]),
        EntryKind::Directory { files, bytes } => {
            d.update([1]);
            d.update(files.to_le_bytes());
            d.update(bytes.to_le_bytes());
        }
        EntryKind::AbsentEmptyOutput => d.update([2]),
        EntryKind::Unavailable => d.update([3]),
    }
}
fn add_entry(inputs: &mut PhysicalInputs, entry: &ClasspathEntry) -> Result<(), Error> {
    match entry.kind {
        EntryKind::Jar => {
            let bytes = std::fs::metadata(&entry.path)?.len();
            inputs.files.push(InputPin {
                path: entry.path.clone(),
                sha256: entry.sha256.0,
                bytes,
            });
        }
        EntryKind::Directory { .. } => inputs.directories.push(entry.clone()),
        EntryKind::AbsentEmptyOutput => inputs.absent.push(entry.path.clone()),
        EntryKind::Unavailable => return Err(Error::Invalid("unavailable physical input")),
    }
    Ok(())
}

struct EntrySummary {
    selected_hit: bool,
    all_hit: bool,
    manifest: Vec<String>,
}

fn scan_entry(
    provider: &VerifiedProvider<'_>,
    entry_id: usize,
    targets: &[String],
    all_targets: &[String],
    require_all: bool,
    cache: &mut HashMap<usize, EntrySummary>,
    total_names: &mut usize,
    limit: usize,
    paths: &HashSet<PathBuf>,
    inputs: &mut PhysicalInputs,
) -> Result<Result<(), Denial>, Error> {
    let entry = &provider.classpath_entries()[entry_id];
    if !cache.contains_key(&entry_id) {
        let (names, manifest) = match provider.entry_metadata(entry_id) {
            Ok(v) => v,
            Err(provider::Error::Native(e))
                if !matches!(
                    e.kind,
                    binary::ErrorKind::HashMismatch
                        | binary::ErrorKind::DirectoryFingerprintMismatch
                        | binary::ErrorKind::Io
                        | binary::ErrorKind::BadCrc
                        | binary::ErrorKind::SymlinkInput
                        | binary::ErrorKind::ResourceLimit
                ) =>
            {
                return Ok(Err(Denial::UnknownProvider));
            }
            Err(e) => return Err(e.into()),
        };
        *total_names = total_names.checked_add(names.len()).ok_or(Error::Budget)?;
        if *total_names > limit {
            return Err(Error::Budget);
        }
        let selected_hit = names.iter().any(|n| targets.binary_search(n).is_ok());
        let all_hit = names.iter().any(|n| all_targets.binary_search(n).is_ok());
        cache.insert(
            entry_id,
            EntrySummary {
                selected_hit,
                all_hit,
                manifest,
            },
        );
        add_entry(inputs, entry)?;
    }
    let summary = &cache[&entry_id];
    if if require_all {
        summary.all_hit
    } else {
        summary.selected_hit
    } {
        return Ok(Err(Denial::ClassPresent));
    }
    for token in &summary.manifest {
        if token.contains([':', '%', '#', '?', '\\']) || !normal_relative(Path::new(token)) {
            return Ok(Err(Denial::UncapturedManifestTarget));
        }
        let target = entry
            .path
            .parent()
            .ok_or(Error::Invalid("manifest parent"))?
            .join(token);
        if !paths.contains(&target) {
            match require_absent(&target) {
                Ok(()) => inputs.absent.push(target),
                Err(Error::Invalid(_)) => return Ok(Err(Denial::UncapturedManifestTarget)),
                Err(e) => return Err(e),
            }
        }
    }
    Ok(Ok(()))
}

pub struct Side<'a, 'p> {
    pub facts: &'a FactSnapshot,
    pub provider: &'a mut VerifiedProvider<'p>,
    pub catalogue: &'a InputPin,
    pub source_files: &'a [FileId],
    pub suites: &'a [SuiteId],
}

#[derive(Default)]
struct ClassNames {
    selected: Vec<String>,
    all: Vec<String>,
    owners: BTreeMap<String, BTreeSet<String>>,
}

struct ForeignProducts {
    sources: BTreeMap<String, BTreeSet<String>>,
    names: ClassNames,
    facts: ContentHash,
    issuer: ContentHash,
    inputs: PhysicalInputs,
}

/// Issue both revisions together. For added/removed test sources, the missing
/// side also tests the other revision's verified class inventory; an absent
/// pathname cannot hide an old copy of a changed class on its classpath.
pub fn issue_paired(
    mut base: Side<'_, '_>,
    mut head: Side<'_, '_>,
    requested: &[String],
    contract: SelectionContract,
    limits: Limits,
) -> Result<(Issued, Issued), Error> {
    fn present<'a>(facts: &'a FactSnapshot, requested: &[String]) -> BTreeSet<&'a str> {
        facts
            .files
            .iter()
            .filter(|file| file.flags & FILE_BINARY_SOURCE == 0)
            .map(|file| facts.text(file.path))
            .filter(|path| requested.binary_search_by(|p| p.as_str().cmp(path)).is_ok())
            .collect()
    }
    fn export(
        present: &mut Side<'_, '_>,
        missing: &BTreeSet<&str>,
        contract: SelectionContract,
        limits: Limits,
    ) -> Result<Option<ForeignProducts>, Error> {
        if missing.is_empty() {
            return Ok(None);
        }
        let mut file_ids = Vec::new();
        for &id in present.source_files {
            let file = present
                .facts
                .files
                .get(id.index())
                .ok_or(Error::Invalid("one-sided source file"))?;
            let path = present.facts.text(file.path);
            if missing.contains(path) {
                file_ids.push(id);
            }
        }
        if file_ids.is_empty() {
            return Err(Error::Invalid("one-sided source lacks opposite product"));
        }
        let mut names = ClassNames::default();
        let issued = issue_side(
            Side {
                facts: present.facts,
                provider: present.provider,
                catalogue: present.catalogue,
                source_files: &file_ids,
                suites: &[],
            },
            contract,
            limits,
            None,
            Some(&mut names),
            Purpose::Selection,
        )?;
        let sources = std::mem::take(&mut names.owners);
        if sources.len() != missing.len() {
            return Err(Error::Invalid("one-sided source lacks opposite product"));
        }
        Ok(Some(ForeignProducts {
            sources,
            names,
            facts: present.facts.identity,
            issuer: issued.identity(),
            inputs: issued.inputs,
        }))
    }
    if requested.is_empty()
        || requested.len() > 4096
        || requested.windows(2).any(|p| p[0] >= p[1])
        || requested.iter().any(|p| !normal_relative(Path::new(p)))
    {
        return Err(Error::Invalid("one-sided requested source scope"));
    }
    let before = present(base.facts, requested);
    let after = present(head.facts, requested);
    if before.union(&after).count() != requested.len() {
        return Err(Error::Invalid("requested source absent in both revisions"));
    }
    let base_missing = after.difference(&before).copied().collect();
    let head_missing = before.difference(&after).copied().collect();
    let base_foreign = export(&mut head, &base_missing, contract, limits)?;
    let head_foreign = export(&mut base, &head_missing, contract, limits)?;
    Ok((
        issue_side(
            base,
            contract,
            limits,
            base_foreign,
            None,
            Purpose::Selection,
        )?,
        issue_side(
            head,
            contract,
            limits,
            head_foreign,
            None,
            Purpose::Selection,
        )?,
    ))
}

fn attest_missing_sources(
    capture: &Capture,
    provider: &VerifiedProvider<'_>,
    foreign: &ForeignProducts,
    out: &mut Issued,
    limits: Limits,
) -> Result<(), Error> {
    let mut check_owners = BTreeMap::<&str, BTreeSet<&str>>::new();
    for (path, owners) in &foreign.sources {
        if capture.source_to_contexts.contains_key(path)
            || capture.contexts.iter().any(|ctx| {
                ctx.source_records
                    .iter()
                    .any(|row| row.repo_relative_path == *path)
            })
        {
            return Err(Error::Invalid("one-sided source present in capture"));
        }
        let physical = provider.captured_path(&capture.source_root.join(path))?;
        require_absent(&physical)?;
        let basename = Path::new(path)
            .file_name()
            .and_then(|n| n.to_str())
            .ok_or(Error::Invalid("one-sided source basename"))?;
        for owner in owners {
            check_owners.entry(owner).or_default().insert(basename);
        }
        let mut seal = Sha256::new();
        seal.update(VERSION);
        seal.update(out.facts.0);
        seal.update(out.capture.0);
        seal.update(provider.identity());
        seal.update(foreign.facts.0);
        seal.update(foreign.issuer.0);
        text(&mut seal, path);
        text(&mut seal, &physical.to_string_lossy());
        out.absent_sources.push(AbsentSource {
            path: path.clone(),
            opposite_facts: foreign.facts,
            absence_identity: ContentHash(seal.finalize().into()),
        });
        out.inputs.absent.push(physical);
    }
    // Captured test products can outlive a source in an incremental build.
    // Independently reject stale or unattributed classes in the same owner.
    let mut class_count = 0usize;
    for (owner, basenames) in check_owners {
        let context = capture
            .contexts
            .iter()
            .find(|ctx| ctx.context_id == owner && ctx.configuration == "test")
            .ok_or(Error::Invalid("one-sided test owner absent"))?;
        let products: BTreeSet<_> = context.products.iter().collect();
        let exported: BTreeSet<_> = context.exported_products.iter().map(|p| &p.path).collect();
        let source_basenames: BTreeSet<_> = context
            .source_records
            .iter()
            .filter_map(|record| Path::new(&record.repo_relative_path).file_name()?.to_str())
            .collect();
        if products.is_empty()
            || products != exported
            || products.len() != context.products.len()
            || exported.len() != context.exported_products.len()
        {
            return Err(Error::Invalid("one-sided test output inventory"));
        }
        for product in &context.exported_products {
            let path = provider.captured_path(&product.path)?;
            let expected = ContentHash::from_hex(&product.sha256)?;
            let entry = provider
                .classpath_entries()
                .iter()
                .position(|entry| entry.path == path && entry.sha256 == expected)
                .ok_or(Error::Invalid("one-sided test output is not admitted"))?;
            let mut loader = provider.entry_snapshot(entry)?;
            let names = loader.class_names(0).map_err(provider::Error::from)?;
            class_count = class_count.checked_add(names.len()).ok_or(Error::Budget)?;
            if class_count > limits.inventory_names {
                return Err(Error::Budget);
            }
            for name in names {
                let binary::ClassLookup::Found(class) =
                    loader.lookup(&name).map_err(provider::Error::from)?
                else {
                    return Err(Error::Invalid("one-sided test output disappeared"));
                };
                let source = selector_compiled_products::class_source_file(&class.bytes)
                    .ok()
                    .flatten()
                    .ok_or(Error::Invalid(
                        "one-sided test output lacks source attribution",
                    ))?;
                if basenames.contains(source.as_str()) {
                    return Err(Error::Invalid(
                        "one-sided test output contains stale source",
                    ));
                }
                if !source_basenames.contains(source.as_str()) {
                    return Err(Error::Invalid(
                        "one-sided test output lacks captured source",
                    ));
                }
            }
            add_entry(&mut out.inputs, &provider.classpath_entries()[entry])?;
        }
    }
    Ok(())
}

/// The source set and suite IDs come from the actual query, never request JSON.
/// Every owner product is pinned completely. SourceFile attribution narrows
/// class names only for captured project outputs with certified compile closure;
/// unattributed inputs are compared with all owner-output class names.
pub fn issue(
    facts: &FactSnapshot,
    provider: &mut VerifiedProvider<'_>,
    catalogue: &InputPin,
    source_files: &[FileId],
    suites: &[SuiteId],
    contract: SelectionContract,
    limits: Limits,
) -> Result<Issued, Error> {
    issue_side(
        Side {
            facts,
            provider,
            catalogue,
            source_files,
            suites,
        },
        contract,
        limits,
        None,
        None,
        Purpose::Selection,
    )
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Purpose {
    Selection,
    RuntimeDiagnostic,
}

/// Physical class availability for replay only. This type intentionally
/// exposes no `SuiteClasspath` certificates or selection issuer data.
pub struct RuntimeScope {
    identity: ContentHash,
    sources: Vec<SourceProduct>,
    products: Vec<ProductFile>,
    suites: Vec<SuiteId>,
    denied: Vec<DeniedSuite>,
    inputs: PhysicalInputs,
}
impl RuntimeScope {
    pub fn identity(&self) -> ContentHash {
        self.identity
    }
    pub fn sources(&self) -> &[SourceProduct] {
        &self.sources
    }
    pub fn product_files(&self) -> &[ProductFile] {
        &self.products
    }
    pub fn suites(&self) -> &[SuiteId] {
        &self.suites
    }
    pub fn denials(&self) -> &[DeniedSuite] {
        &self.denied
    }
    pub fn revalidate(&self) -> Result<(), Error> {
        self.inputs.revalidate()
    }
}

/// Admit a source product mask under the captured Test/fullClasspath premise.
/// Unlike an exclusion certificate, this proves nothing about compilation
/// influence, so it requires no transitive compiler dependency closure. It
/// still scans all source-owner product class names against every physically
/// admitted runtime entry, including classpath manifest targets.
pub fn issue_runtime_scope(
    side: Side<'_, '_>,
    contract: SelectionContract,
    limits: Limits,
) -> Result<RuntimeScope, Error> {
    let issued = issue_side(
        side,
        contract,
        limits,
        None,
        None,
        Purpose::RuntimeDiagnostic,
    )?;
    Ok(RuntimeScope {
        identity: issued.identity,
        sources: issued.sources,
        products: issued.product_files,
        suites: issued.suites.into_iter().map(|row| row.suite).collect(),
        denied: issued.denied,
        inputs: issued.inputs,
    })
}

fn issue_side(
    side: Side<'_, '_>,
    contract: SelectionContract,
    limits: Limits,
    foreign: Option<ForeignProducts>,
    mut export_names: Option<&mut ClassNames>,
    purpose: Purpose,
) -> Result<Issued, Error> {
    let Side {
        facts,
        provider,
        catalogue,
        source_files,
        suites,
    } = side;
    facts.validate()?;
    if facts.identity == ContentHash::default()
        || contract.bits() & REQUIRED_BITS != REQUIRED_BITS
        || (source_files.is_empty() && foreign.is_none())
        || source_files.len() > limits.source_files
        || suites.len() > limits.suites
    {
        return Err(Error::Invalid("scope/runtime premise"));
    }
    let capture: Capture = serde_json::from_slice(&provider.capture_document()?)?;
    if capture.revision != facts.text(facts.revision) {
        return Err(Error::Invalid("capture/facts revision"));
    }
    let catalog: Catalogue = serde_json::from_slice(&read_pin(catalogue, 64 << 20)?)?;
    if catalog.schema_version != "compiler-ci-catalogue/v1"
        || !catalog.complete
        || !catalog.issues.is_empty()
    {
        return Err(Error::Invalid("catalogue completeness"));
    }
    let contexts: HashMap<_, _> = capture
        .contexts
        .iter()
        .map(|c| (c.context_id.as_str(), c))
        .collect();
    if contexts.len() != capture.contexts.len() {
        return Err(Error::Invalid("duplicate capture context"));
    }
    let objects: HashMap<_, _> = capture
        .input_objects
        .iter()
        .map(|o| (o.path.as_path(), o))
        .collect();
    if objects.len() != capture.input_objects.len() {
        return Err(Error::Invalid("duplicate captured object"));
    }
    let mut runtime = Sha256::new();
    runtime.update(VERSION);
    if purpose == Purpose::RuntimeDiagnostic {
        runtime.update(b"runtime-diagnostic-only\0");
    }
    runtime.update(SelectionContract::VERSION.as_bytes());
    runtime.update(contract.bits().to_le_bytes());
    let mut out = Issued {
        identity: ContentHash::default(),
        facts: facts.identity,
        capture: ContentHash(provider.input_files()[0].sha256),
        runtime: ContentHash(runtime.finalize().into()),
        products: ContentHash::default(),
        sources: Vec::new(),
        absent_sources: Vec::new(),
        product_files: Vec::new(),
        suites: Vec::new(),
        denied: Vec::new(),
        inputs: PhysicalInputs::default(),
    };
    out.inputs
        .files
        .extend(provider.input_files().iter().cloned());
    out.inputs.files.push(catalogue.clone());
    if let Some(foreign) = &foreign {
        attest_missing_sources(&capture, provider, foreign, &mut out, limits)?;
    }
    let mut requested = source_files.to_vec();
    requested.sort_unstable();
    if requested.windows(2).any(|p| p[0] == p[1]) {
        return Err(Error::Invalid("duplicate source scope"));
    }
    let mut products = BTreeMap::<usize, Vec<Attribution>>::new();
    let mut target_classes = Vec::<String>::new();
    let mut all_classes = Vec::<String>::new();
    let mut owner_contexts = HashSet::new();
    let mut total_names = 0usize;
    // One flat borrowed index includes duplicate FileIds without duplicating
    // path strings or allocating a separate posting Vec for every class.
    let mut binary_files: Vec<_> = facts
        .files
        .iter()
        .enumerate()
        .filter_map(|(index, f)| {
            (f.flags == FILE_BINARY_SOURCE
                && f.revision == facts.revision
                && !f.context.is_none()
                && f.source_hash != ContentHash::default()
                && facts.text(f.source).is_empty())
            .then_some((
                f.context,
                facts.text(f.path),
                f.source_hash.0,
                FileId(index as u32),
            ))
        })
        .collect();
    binary_files.sort_unstable();
    for &file_id in &requested {
        let file = facts
            .files
            .get(file_id.index())
            .ok_or(Error::Invalid("source file ID"))?;
        let path = facts.text(file.path);
        if !normal_relative(Path::new(path))
            || file.flags & (SOURCE_VERIFIED | FILE_BINARY_SOURCE) != SOURCE_VERIFIED
            || file.source_hash == ContentHash::default()
        {
            return Err(Error::Invalid("source file authority"));
        }
        let owners = capture
            .source_to_contexts
            .get(path)
            .ok_or(Error::Invalid("source ownership absent"))?;
        let mut actual_owners: Vec<_> = capture
            .contexts
            .iter()
            .filter(|c| {
                c.source_records
                    .iter()
                    .any(|s| s.repo_relative_path == path)
            })
            .map(|c| c.context_id.as_str())
            .collect();
        actual_owners.sort_unstable();
        let mut declared_owners: Vec<_> = owners.iter().map(String::as_str).collect();
        declared_owners.sort_unstable();
        if declared_owners.is_empty()
            || declared_owners.windows(2).any(|p| p[0] == p[1])
            || actual_owners != declared_owners
            || !declared_owners.contains(&facts.text(file.context))
        {
            return Err(Error::Invalid("complete source ownership"));
        }
        if let Some(export) = export_names.as_deref_mut() {
            export.owners.insert(
                path.to_owned(),
                declared_owners
                    .iter()
                    .map(|owner| (*owner).to_owned())
                    .collect(),
            );
        }
        let mut digest = Sha256::new();
        digest.update(VERSION);
        text(&mut digest, path);
        digest.update(file.source_hash.0);
        let mut product_count = 0u32;
        for owner in declared_owners {
            owner_contexts.insert(owner.to_owned());
            let context = contexts[owner];
            if export_names.is_some() && context.configuration != "test" {
                return Err(Error::Invalid("one-sided source is not a test product"));
            }
            let records: Vec<_> = context
                .source_records
                .iter()
                .filter(|s| s.repo_relative_path == path)
                .collect();
            if records.len() != 1 || ContentHash::from_hex(&records[0].sha256)? != file.source_hash
            {
                return Err(Error::Invalid("source record hash"));
            }
            let source = records[0];
            let object = objects
                .get(Path::new(
                    source.input_object.as_deref().unwrap_or(
                        source
                            .path
                            .to_str()
                            .ok_or(Error::Invalid("source path UTF8"))?,
                    ),
                ))
                .ok_or(Error::Invalid("source object"))?;
            if object.kind != "file" || object.sha256 != source.sha256 {
                return Err(Error::Invalid("source object binding"));
            }
            let pin = InputPin {
                path: provider.captured_path(&source.path)?,
                sha256: file.source_hash.0,
                bytes: object.bytes,
            };
            read_pin(&pin, 64 << 20)?;
            out.inputs.files.push(pin);
            let mut raw_products = context.products.clone();
            raw_products.sort();
            let mut exported: Vec<_> = context
                .exported_products
                .iter()
                .map(|p| p.path.clone())
                .collect();
            exported.sort();
            if raw_products.is_empty()
                || raw_products != exported
                || exported.windows(2).any(|p| p[0] == p[1])
            {
                return Err(Error::Invalid("complete exported products"));
            }
            text(&mut digest, owner);
            for product in &context.exported_products {
                let physical = provider.captured_path(&product.path)?;
                let expected = ContentHash::from_hex(&product.sha256)?;
                let object = objects
                    .get(Path::new(
                        product.input_object.as_deref().unwrap_or(
                            product
                                .path
                                .to_str()
                                .ok_or(Error::Invalid("product path UTF8"))?,
                        ),
                    ))
                    .ok_or(Error::Invalid("product object"))?;
                if object.sha256 != product.sha256
                    || !matches!(object.kind.as_str(), "directory" | "file")
                {
                    return Err(Error::Invalid("product object binding"));
                }
                let entry = provider
                    .classpath_entries()
                    .iter()
                    .position(|e| e.path == physical && e.sha256 == expected)
                    .ok_or(Error::Invalid("product lacks admitted inventory"))?;
                if !products.contains_key(&entry) {
                    let (names, _) = provider.entry_metadata(entry)?;
                    total_names = total_names.checked_add(names.len()).ok_or(Error::Budget)?;
                    if names.is_empty() || total_names > limits.inventory_names {
                        return Err(Error::Budget);
                    }
                    let mut loader = provider.entry_snapshot(entry)?;
                    let mut attribution = Vec::with_capacity(names.len());
                    for name in names {
                        let class = match loader.lookup(&name).map_err(provider::Error::from)? {
                            binary::ClassLookup::Found(class) => class,
                            _ => return Err(Error::Invalid("product class disappeared")),
                        };
                        let source = selector_compiled_products::class_source_file(&class.bytes)
                            .ok()
                            .flatten();
                        attribution.push(Attribution {
                            name,
                            source,
                            hash: class
                                .proof
                                .class_hash
                                .ok_or(Error::Invalid("product class hash"))?,
                        });
                    }
                    all_classes.extend(attribution.iter().map(|c| c.name.clone()));
                    products.insert(entry, attribution);
                    add_entry(&mut out.inputs, &provider.classpath_entries()[entry])?;
                }
                product_count = product_count.checked_add(1).ok_or(Error::Budget)?;
                entry_hash(&mut digest, &provider.classpath_entries()[entry]);
                let requested_basename = Path::new(path)
                    .file_name()
                    .and_then(|n| n.to_str())
                    .ok_or(Error::Invalid("source basename"))?;
                let unique_basename = owner == facts.text(file.context)
                    && context
                        .source_records
                        .iter()
                        .filter(|s| {
                            Path::new(&s.repo_relative_path)
                                .file_name()
                                .and_then(|n| n.to_str())
                                == Some(requested_basename)
                        })
                        .count()
                        == 1;
                for class in &products[&entry] {
                    let known_other = class.source.as_deref().is_some_and(|name| {
                        name != requested_basename
                            && normal_relative(Path::new(name))
                            && Path::new(name).components().count() == 1
                            && context.source_records.iter().any(|s| {
                                Path::new(&s.repo_relative_path)
                                    .file_name()
                                    .and_then(|n| n.to_str())
                                    == Some(name)
                            })
                    });
                    if !known_other {
                        target_classes.push(class.name.clone());
                        if target_classes.len() > limits.classes {
                            return Err(Error::Budget);
                        }
                    }
                    if unique_basename && class.source.as_deref() == Some(requested_basename) {
                        let raw = format!("{}!/{}.class", product.path.display(), class.name);
                        let relocated = format!("{}!/{}.class", physical.display(), class.name);
                        for class_path in [raw.as_str(), relocated.as_str()]
                            .into_iter()
                            .take(if raw == relocated { 1 } else { 2 })
                        {
                            let key = (file.context, class_path, class.hash.0);
                            let start = binary_files.partition_point(|r| (r.0, r.1, r.2) < key);
                            for &(context, native_path, hash, native_file) in &binary_files[start..]
                            {
                                if (context, native_path, hash) != key {
                                    break;
                                }
                                if out.product_files.len() >= limits.physical_files {
                                    return Err(Error::Budget);
                                }
                                out.product_files.push(ProductFile {
                                    file: native_file,
                                    source_file: file_id,
                                    owner_context: context,
                                    class_sha256: class.hash,
                                });
                            }
                        }
                    }
                    text(&mut digest, &class.name);
                    digest.update(class.hash.0);
                    text(&mut digest, class.source.as_deref().unwrap_or(""));
                    digest.update([u8::from(known_other)]);
                }
            }
        }
        out.sources.push(SourceProduct {
            file: file_id,
            owner_context: file.context,
            products_identity: ContentHash(digest.finalize().into()),
            product_count,
        });
    }
    if let Some(foreign) = foreign {
        total_names = total_names
            .checked_add(foreign.names.all.len())
            .ok_or(Error::Budget)?;
        if total_names > limits.inventory_names {
            return Err(Error::Budget);
        }
        target_classes.extend(foreign.names.selected);
        all_classes.extend(foreign.names.all);
        out.inputs.files.extend(foreign.inputs.files);
        out.inputs.directories.extend(foreign.inputs.directories);
        out.inputs.absent.extend(foreign.inputs.absent);
    }
    target_classes.sort_unstable();
    target_classes.dedup();
    all_classes.sort_unstable();
    all_classes.dedup();
    if target_classes.is_empty() || target_classes.len() > limits.classes {
        return Err(Error::Invalid("no source-attributed products"));
    }
    out.product_files
        .sort_unstable_by_key(|r| (r.file, r.source_file));
    out.product_files.dedup();
    if out.product_files.windows(2).any(|r| r[0].file == r[1].file) {
        return Err(Error::Invalid("ambiguous source product file"));
    }
    let mut digest = Sha256::new();
    digest.update(VERSION);
    for row in &out.sources {
        digest.update(row.file.0.to_le_bytes());
        digest.update(row.owner_context.0.to_le_bytes());
        digest.update(row.products_identity.0);
        digest.update(row.product_count.to_le_bytes());
    }
    for row in &out.product_files {
        digest.update(row.file.0.to_le_bytes());
        digest.update(row.source_file.0.to_le_bytes());
        digest.update(row.owner_context.0.to_le_bytes());
        digest.update(row.class_sha256.0);
    }
    for row in &out.absent_sources {
        text(&mut digest, &row.path);
        digest.update(row.opposite_facts.0);
        digest.update(row.absence_identity.0);
    }
    out.products = ContentHash(digest.finalize().into());
    let mut summaries = HashMap::<usize, EntrySummary>::new();
    let changed_paths: HashSet<_> = requested
        .iter()
        .map(|id| facts.text(facts.files[id.index()].path))
        .chain(out.absent_sources.iter().map(|row| row.path.as_str()))
        .collect();
    let mut compile_cache = HashMap::<String, Result<ContentHash, Denial>>::new();
    let mut roots = suites.to_vec();
    roots.sort_unstable();
    if roots.windows(2).any(|p| p[0] == p[1]) {
        return Err(Error::Invalid("duplicate suite scope"));
    }
    for suite_id in roots {
        let result = (|| -> Result<Result<SuiteClasspath, Denial>, Error> {
            let suite = facts
                .suites
                .get(suite_id.index())
                .ok_or(Error::Invalid("suite ID"))?;
            let name = facts.text(suite.name);
            let rows: Vec<_> = catalog.suites.iter().filter(|r| r.suite == name).collect();
            if rows.len() != 1 || rows[0].owning_context_ids.len() != 1 {
                return Ok(Err(Denial::CatalogueOwner));
            }
            let owner = rows[0].owning_context_ids[0].as_str();
            let Some(context) = contexts.get(owner) else {
                return Ok(Err(Denial::CatalogueOwner));
            };
            let Some(authority) = provider.authority(owner) else {
                return Ok(Err(Denial::CatalogueOwner));
            };
            if suite.symbol.is_none() || suite.file.is_none() {
                return Ok(Err(Denial::CatalogueOwner));
            }
            let symbol = facts.symbols[suite.symbol.index()];
            let context_id = symbol.context;
            if facts.text(context_id) != owner
                || facts.files[suite.file.index()].context != context_id
                || context.configuration != "test"
            {
                return Ok(Err(Denial::CatalogueOwner));
            }
            let defined: Vec<_> = context
                .defined_tests
                .iter()
                .filter(|r| r.name == name)
                .collect();
            let discovered: Vec<_> = rows[0]
                .compiler_discovery
                .iter()
                .filter(|r| r.context_id == owner && r.configuration == "test")
                .collect();
            if defined.len() != 1
                || discovered.len() != 1
                || defined[0].fingerprint != discovered[0].fingerprint
            {
                return Ok(Err(Denial::CatalogueOwner));
            }
            // Presence is a complete denial without resolving or retaining the
            // suite's root class, or visiting its transitive compiler inputs.
            for row in &context.full_classpath {
                if owner_contexts.iter().any(|o| {
                    row.project_output_origins
                        .iter()
                        .any(|r| &r.context_id == o)
                }) {
                    return Ok(Err(Denial::ProductPresent));
                }
                let sha = ContentHash::from_hex(&row.sha256)?;
                if row.index >= context.full_classpath.len() || sha == ContentHash::default() {
                    return Err(Error::Invalid("captured CP row"));
                }
                let physical = provider.captured_path(&row.path)?;
                if products.keys().any(|&p| {
                    let e = &provider.classpath_entries()[p];
                    e.path == physical || e.sha256 == sha
                }) {
                    return Ok(Err(Denial::ProductPresent));
                }
            }
            let Some(jvm_owner) =
                selector_types::symbol::jvm_owner(facts.symbol_name(suite.symbol))
            else {
                return Ok(Err(Denial::UnsupportedSuite));
            };
            let (bytes, proof) = provider.resolve(authority, &jvm_owner)?;
            if proof.state != ResolutionState::Found {
                return Ok(Err(Denial::UnknownProvider));
            }
            let class = binary::parse_class(
                bytes.as_ref().ok_or(Error::Invalid("suite class bytes"))?,
                binary::Limits::default(),
            )
            .map_err(|_| Error::Invalid("suite class structure"))?;
            if symbol.kind != 13
                || symbol.flags & SYMBOL_DEFINED == 0
                || class.name != jvm_owner
                || class.flags & 1 == 0
                || !class
                    .methods
                    .iter()
                    .any(|m| m.name == "<init>" && m.descriptor == "()V" && m.flags & 1 != 0)
            {
                return Ok(Err(Denial::UnsupportedSuite));
            }
            if purpose == Purpose::Selection && !compile_cache.contains_key(owner) {
                let compile = (|| -> Result<Result<ContentHash, Denial>, Error> {
                    let mut pending = vec![owner];
                    let mut seen = HashSet::new();
                    let mut digest = Sha256::new();
                    digest.update(VERSION);
                    digest.update(b"compile-provider-closure\0");
                    while let Some(current) = pending.pop() {
                        if !seen.insert(current) {
                            continue;
                        }
                        if seen.len() > capture.contexts.len() {
                            return Err(Error::Budget);
                        }
                        let Some(producer) = contexts.get(current) else {
                            return Ok(Err(Denial::UnknownCompileOwner));
                        };
                        text(&mut digest, current);
                        if producer
                            .source_records
                            .iter()
                            .any(|s| changed_paths.contains(s.repo_relative_path.as_str()))
                        {
                            return Ok(Err(Denial::CompileDependencyPresent));
                        }
                        let paths: HashSet<_> = producer
                            .full_classpath
                            .iter()
                            .chain(&producer.dependency_classpath)
                            .map(|row| provider.captured_path(&row.path))
                            .collect::<Result<_, _>>()?;
                        for (kind, rows) in
                            [&producer.full_classpath, &producer.dependency_classpath]
                                .into_iter()
                                .enumerate()
                        {
                            digest.update([kind as u8]);
                            for (ordinal, row) in rows.iter().enumerate() {
                                if row.index != ordinal {
                                    return Err(Error::Invalid("compile CP ordinal"));
                                }
                                let physical = provider.captured_path(&row.path)?;
                                let sha = ContentHash::from_hex(&row.sha256)?;
                                if products.keys().any(|&p| {
                                    let e = &provider.classpath_entries()[p];
                                    e.path == physical || e.sha256 == sha
                                }) {
                                    return Ok(Err(Denial::CompileDependencyPresent));
                                }
                                for origin in &row.project_output_origins {
                                    if owner_contexts.contains(&origin.context_id) {
                                        return Ok(Err(Denial::CompileDependencyPresent));
                                    }
                                    if !contexts.contains_key(origin.context_id.as_str()) {
                                        return Ok(Err(Denial::UnknownCompileOwner));
                                    }
                                    pending.push(origin.context_id.as_str());
                                }
                                let Some(entry_id) = provider
                                    .classpath_entries()
                                    .iter()
                                    .position(|e| e.path == physical && e.sha256 == sha)
                                else {
                                    return Ok(Err(Denial::UnknownCompileOwner));
                                };
                                entry_hash(&mut digest, &provider.classpath_entries()[entry_id]);
                                if let Err(reason) = scan_entry(
                                    provider,
                                    entry_id,
                                    &target_classes,
                                    &all_classes,
                                    !bound_project_output(row, &contexts),
                                    &mut summaries,
                                    &mut total_names,
                                    limits.inventory_names,
                                    &paths,
                                    &mut out.inputs,
                                )? {
                                    return Ok(Err(if reason == Denial::ClassPresent {
                                        Denial::CompileDependencyPresent
                                    } else {
                                        reason
                                    }));
                                }
                            }
                        }
                    }
                    Ok(Ok(ContentHash(digest.finalize().into())))
                })()?;
                compile_cache.insert(owner.to_owned(), compile);
            }
            let compile_identity = match purpose {
                Purpose::RuntimeDiagnostic => ContentHash::default(),
                Purpose::Selection => match compile_cache[owner] {
                    Ok(identity) => identity,
                    Err(reason) => return Ok(Err(reason)),
                },
            };
            let entries = provider
                .context_entries(authority)
                .ok_or(Error::Invalid("suite provider context"))?
                .to_vec();
            let cp_paths: HashSet<_> = entries
                .iter()
                .map(|&i| provider.classpath_entries()[i].path.clone())
                .collect();
            let mut cp = Sha256::new();
            cp.update(VERSION);
            text(&mut cp, owner);
            cp.update(compile_identity.0);
            for entry_id in entries {
                let entry = &provider.classpath_entries()[entry_id];
                let captured_project = purpose == Purpose::Selection
                    && context.full_classpath.iter().any(|row| {
                        bound_project_output(row, &contexts)
                            && provider
                                .captured_path(&row.path)
                                .is_ok_and(|p| p == entry.path)
                            && ContentHash::from_hex(&row.sha256).is_ok_and(|h| h == entry.sha256)
                    });
                entry_hash(&mut cp, entry);
                if let Err(reason) = scan_entry(
                    provider,
                    entry_id,
                    &target_classes,
                    &all_classes,
                    !captured_project,
                    &mut summaries,
                    &mut total_names,
                    limits.inventory_names,
                    &cp_paths,
                    &mut out.inputs,
                )? {
                    return Ok(Err(reason));
                }
            }
            let classpath_identity = ContentHash(cp.finalize().into());
            let mut absence = Sha256::new();
            absence.update(VERSION);
            absence.update(out.capture.0);
            absence.update(provider.identity());
            absence.update(out.runtime.0);
            absence.update(out.products.0);
            absence.update(catalogue.sha256);
            absence.update(suite_id.0.to_le_bytes());
            absence.update(classpath_identity.0);
            Ok(Ok(SuiteClasspath {
                suite: suite_id,
                owner_context: context_id,
                classpath_identity,
                source_products_identity: out.products,
                absence_identity: ContentHash(absence.finalize().into()),
            }))
        })()?;
        match result {
            Ok(row) => out.suites.push(row),
            Err(reason) => out.denied.push(DeniedSuite {
                suite: suite_id,
                reason,
            }),
        }
    }
    out.inputs
        .files
        .sort_unstable_by(|a, b| a.path.cmp(&b.path));
    out.inputs
        .files
        .dedup_by(|a, b| a.path == b.path && a.sha256 == b.sha256 && a.bytes == b.bytes);
    out.inputs
        .directories
        .sort_unstable_by(|a, b| a.path.cmp(&b.path));
    out.inputs.directories.dedup();
    out.inputs.absent.sort();
    out.inputs.absent.dedup();
    if out.inputs.files.len() + out.inputs.directories.len() + out.inputs.absent.len()
        > limits.physical_files
    {
        return Err(Error::Budget);
    }
    let mut seal = Sha256::new();
    seal.update(VERSION);
    seal.update(producer_sha256().0);
    seal.update(out.facts.0);
    seal.update(provider.identity());
    seal.update(out.capture.0);
    seal.update(out.runtime.0);
    seal.update(out.products.0);
    seal.update(catalogue.sha256);
    for row in &out.suites {
        seal.update(row.suite.0.to_le_bytes());
        seal.update(row.owner_context.0.to_le_bytes());
        seal.update(row.classpath_identity.0);
        seal.update(row.absence_identity.0);
    }
    for row in &out.denied {
        seal.update(row.suite.0.to_le_bytes());
        seal.update([row.reason as u8]);
    }
    for path in &out.inputs.absent {
        text(&mut seal, &path.to_string_lossy());
    }
    out.identity = ContentHash(seal.finalize().into());
    if let Some(export) = export_names {
        export.selected = target_classes;
        export.all = all_classes;
    }
    Ok(out)
}

pub struct Request {
    pub identity: ContentHash,
    pub base: ProviderOptions,
    pub head: ProviderOptions,
    pub base_catalogue: InputPin,
    pub head_catalogue: InputPin,
    pub inputs: Vec<PathBuf>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WirePin {
    path: PathBuf,
    sha256: String,
    bytes: u64,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WirePlatform {
    manifest: PathBuf,
    expected_producer: String,
    contexts: PathBuf,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireProvider {
    contexts: WirePin,
    binary_map: WirePin,
    relocated_root: PathBuf,
    raw_facts_identity: Option<String>,
    platform: Option<WirePlatform>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireRequest {
    schema: String,
    base: WireProvider,
    head: WireProvider,
    base_catalogue: WirePin,
    head_catalogue: WirePin,
}
pub fn read_request(path: &Path) -> Result<Request, Error> {
    let path = if path.is_absolute() {
        path.to_owned()
    } else {
        std::env::current_dir()?.join(path)
    };
    no_symlinks(&path)?;
    let bytes = std::fs::read(&path)?;
    if bytes.len() > 1024 * 1024 {
        return Err(Error::Budget);
    }
    let wire: WireRequest = serde_json::from_slice(&bytes)?;
    if wire.schema != REQUEST_SCHEMA {
        return Err(Error::Invalid("request schema"));
    }
    let parent = path.parent().ok_or(Error::Invalid("request parent"))?;
    let physical = |p: PathBuf| -> Result<PathBuf, Error> {
        let p = if p.is_absolute() { p } else { parent.join(p) };
        no_symlinks(&p)?;
        Ok(p)
    };
    let pin = |p: WirePin| -> Result<InputPin, Error> {
        Ok(InputPin {
            path: physical(p.path)?,
            sha256: ContentHash::from_hex(&p.sha256)?.0,
            bytes: p.bytes,
        })
    };
    let provider = |w: WireProvider| -> Result<ProviderOptions, Error> {
        Ok(ProviderOptions {
            contexts: pin(w.contexts)?,
            binary_map: pin(w.binary_map)?,
            relocated_root: physical(w.relocated_root)?,
            facts_identity: w
                .raw_facts_identity
                .map(|h| ContentHash::from_hex(&h).map(|h| h.0))
                .transpose()?,
            source_products_identity: None,
            platform: w
                .platform
                .map(|p| {
                    Ok::<_, Error>(PlatformOptions {
                        manifest: physical(p.manifest)?,
                        contexts: physical(p.contexts)?,
                        producer: ContentHash::from_hex(&p.expected_producer)?,
                    })
                })
                .transpose()?,
            limits: Default::default(),
        })
    };
    let base = provider(wire.base)?;
    let head = provider(wire.head)?;
    let base_catalogue = pin(wire.base_catalogue)?;
    let head_catalogue = pin(wire.head_catalogue)?;
    let mut inputs = vec![
        path,
        base.contexts.path.clone(),
        base.binary_map.path.clone(),
        head.contexts.path.clone(),
        head.binary_map.path.clone(),
        base_catalogue.path.clone(),
        head_catalogue.path.clone(),
    ];
    for p in [&base, &head] {
        if let Some(p) = &p.platform {
            inputs.extend([p.manifest.clone(), p.contexts.clone()]);
        }
    }
    Ok(Request {
        identity: hash(&bytes),
        base,
        head,
        base_catalogue,
        head_catalogue,
        inputs,
    })
}
pub fn producer_sha256() -> ContentHash {
    let mut d = Sha256::new();
    d.update(VERSION);
    d.update(crate::library_inventory::producer_sha256().0);
    d.update(include_bytes!("classpath_absence.rs"));
    d.update(include_bytes!("stable_compilation.rs"));
    d.update(include_bytes!(
        "../../selector-compiled-products/src/lib.rs"
    ));
    d.update(include_bytes!(
        "../../selector-compiled-products/src/classfile.rs"
    ));
    d.update(include_bytes!(
        "../../selector-compiled-products/Cargo.toml"
    ));
    ContentHash(d.finalize().into())
}

#[cfg(test)]
#[path = "classpath_absence_tests.rs"]
mod tests;
