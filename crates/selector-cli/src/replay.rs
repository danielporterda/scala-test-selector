//! Portable, hash-bound native replay plans. Receipts never execute a shell.
//!
//! Stage validation is independent of execution: callers may reuse completed
//! native facts/graphs and rerun only invalid descendants. Query continuations
//! use their own typed artifact and are never labeled completed outcomes here.
use selector_artifacts::ArtifactKind;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, HashSet};
use std::fs::{self, File, OpenOptions};
use std::io::{self, BufWriter, Read, Write};
use std::path::{Component, Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

pub type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
const VERSION: u32 = 3;
const ZERO: &str = "0000000000000000000000000000000000000000000000000000000000000000";
static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

/// Bind the exact recorded invocation and its relocation map. The map is
/// separate from raw argv: deleting a relative-path binding changes resolution
/// even when the mapped path happens to equal the raw argument text.
pub fn options_identity(arguments: &[String], paths: &BTreeMap<usize, String>) -> String {
    fn field(hash: &mut Sha256, value: &[u8]) {
        hash.update((value.len() as u64).to_le_bytes());
        hash.update(value);
    }
    let mut hash = Sha256::new();
    hash.update(b"selector-recorded-options/v3\0");
    hash.update((arguments.len() as u64).to_le_bytes());
    for argument in arguments {
        field(&mut hash, argument.as_bytes());
    }
    hash.update((paths.len() as u64).to_le_bytes());
    for (&index, path) in paths {
        hash.update((index as u64).to_le_bytes());
        field(&mut hash, path.as_bytes());
    }
    hex(&hash.finalize())
}

#[derive(Clone, Debug)]
pub struct ReplayLimits {
    pub receipt_bytes: u64,
    pub file_bytes: u64,
    pub total_bytes: u64,
    pub stages: usize,
    pub pins: usize,
    pub arguments: usize,
    pub verify_compiler_inputs: bool,
    pub compiler_workers: usize,
}
impl Default for ReplayLimits {
    fn default() -> Self {
        Self {
            receipt_bytes: 8 * 1024 * 1024,
            file_bytes: 16 * 1024 * 1024 * 1024,
            total_bytes: 64 * 1024 * 1024 * 1024,
            stages: 256,
            pins: 4096,
            arguments: 2048,
            verify_compiler_inputs: true,
            compiler_workers: 4,
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArtifactPin {
    pub kind: u32,
    pub identity: String,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FilePin {
    pub role: String,
    /// Forward-slash path below the explicitly declared bundle root.
    pub path: String,
    pub bytes: u64,
    pub sha256: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub artifact: Option<ArtifactPin>,
}
impl FilePin {
    pub fn capture(
        role: impl Into<String>,
        path: &Path,
        root: &Path,
        kind: Option<ArtifactKind>,
    ) -> Result<Self> {
        let root = fs::canonicalize(root)?;
        let resolved = fs::canonicalize(path)?;
        let relative = resolved
            .strip_prefix(&root)
            .map_err(|_| "replay file escapes bundle root")?;
        let path = portable(relative)?;
        let (bytes, sha256) = hash_file(&resolved, ReplayLimits::default().file_bytes)?;
        let artifact = kind
            .map(|kind| {
                selector_artifacts::verify_file(&resolved, kind, ReplayLimits::default().file_bytes)
                    .map(|verified| ArtifactPin {
                        kind: kind as u32,
                        identity: hex(&verified.identity),
                    })
            })
            .transpose()?;
        Ok(Self {
            role: role.into(),
            path,
            bytes,
            sha256,
            artifact,
        })
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StageReceipt {
    pub id: String,
    #[serde(default)]
    pub dependencies: Vec<String>,
    pub producer_key: String,
    pub producer: String,
    pub models: String,
    pub options: String,
    pub fingerprint: String,
    #[serde(default)]
    pub inputs: Vec<FilePin>,
    #[serde(default)]
    pub outputs: Vec<FilePin>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub compiler_inputs: Option<CompilerInputBinding>,
    /// Query-only inventory/negative pins admitted by the classpath issuer.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub classpath_inputs: Option<ClasspathInputs>,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DirectoryPin {
    pub path: String,
    pub sha256: String,
    pub files: u64,
    pub bytes: u64,
}
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ClasspathInputs {
    pub directories: Vec<DirectoryPin>,
    pub absent: Vec<String>,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CompilerInputBinding {
    pub contexts: FilePin,
    pub root: String,
    pub identity: String,
}
impl StageReceipt {
    pub fn new(
        id: impl Into<String>,
        producer_key: impl Into<String>,
        producer: impl Into<String>,
        models: impl Into<String>,
        options: impl Into<String>,
    ) -> Self {
        Self {
            id: id.into(),
            dependencies: Vec::new(),
            producer_key: producer_key.into(),
            producer: producer.into(),
            models: models.into(),
            options: options.into(),
            fingerprint: ZERO.into(),
            inputs: Vec::new(),
            outputs: Vec::new(),
            compiler_inputs: None,
            classpath_inputs: None,
        }
    }
    pub fn seal(&mut self) {
        self.fingerprint = stage_fingerprint(self);
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReplayReceipt {
    pub version: u32,
    /// Relative to the receipt file's parent; may ascend to the bundle root.
    pub bundle_root: String,
    /// Exact native argv, including command name but excluding executable.
    pub arguments: Vec<String>,
    /// Argument indexes whose values must relocate with the bundle root.
    #[serde(default)]
    pub path_arguments: BTreeMap<usize, String>,
    pub producers: BTreeMap<String, String>,
    pub stages: Vec<StageReceipt>,
}
impl ReplayReceipt {
    pub fn new(arguments: Vec<String>, producers: BTreeMap<String, String>) -> Self {
        Self {
            version: VERSION,
            bundle_root: ".".into(),
            arguments,
            path_arguments: BTreeMap::new(),
            producers,
            stages: Vec::new(),
        }
    }
    pub fn add_stage(&mut self, mut stage: StageReceipt) {
        stage.seal();
        self.stages.push(stage);
    }
    pub fn set_bundle_root(&mut self, receipt: &Path, root: &Path) -> Result<()> {
        let parent = fs::canonicalize(receipt.parent().unwrap_or(Path::new(".")))?;
        let root = fs::canonicalize(root)?;
        self.bundle_root = relative_root(&parent, &root)?;
        Ok(())
    }
    pub fn bind_path_argument(&mut self, index: usize, path: &Path, root: &Path) -> Result<()> {
        if index >= self.arguments.len() {
            return Err("replay path argument index".into());
        }
        let root = fs::canonicalize(root)?;
        let absolute = if path.is_absolute() {
            path.to_owned()
        } else {
            std::env::current_dir()?.join(path)
        };
        let relative = absolute
            .strip_prefix(&root)
            .map_err(|_| "replay argument escapes bundle root")?;
        self.path_arguments.insert(
            index,
            if relative.as_os_str().is_empty() {
                ".".into()
            } else {
                portable(relative)?
            },
        );
        Ok(())
    }
    /// Returns typed native argv only. The caller passes it directly to Args;
    /// shell quoting/interpolation is neither performed nor accepted as code.
    pub fn replay_arguments(&self, receipt: &Path) -> Result<Vec<String>> {
        validate_shape(self, &ReplayLimits::default())?;
        let root = resolve_root(receipt, &self.bundle_root)?;
        let mut arguments = self.arguments.clone();
        if !matches!(
            arguments.first().map(String::as_str),
            Some("run" | "query" | "extract" | "enrich" | "build" | "verify")
        ) {
            return Err("replay supports native analysis commands only".into());
        }
        for (&index, path) in &self.path_arguments {
            arguments[index] = root
                .join(path)
                .to_str()
                .ok_or("non-UTF8 replay argument")?
                .to_owned();
        }
        // Replaying a recording must not recursively overwrite its receipt.
        let mut index = 1;
        while index < arguments.len() {
            if arguments[index] == "--receipt" {
                if index + 1 >= arguments.len() {
                    return Err("replay receipt argument has no value".into());
                }
                arguments.drain(index..index + 2);
            } else if arguments[index].starts_with("--receipt=") {
                arguments.remove(index);
            } else {
                index += 1;
            }
        }
        Ok(arguments)
    }
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum InvalidationReason {
    Valid,
    DependencyInvalid,
    StageFingerprint,
    OptionsChanged,
    ProducerChanged,
    ProducerUnavailable,
    InputMissing,
    InputChanged,
    OutputMissing,
    OutputChanged,
    ArtifactInvalid,
    ResourceLimit,
    CompilerInputsChanged,
    CompilerInputsMissing,
}
#[derive(Clone, Debug, Serialize)]
pub struct StageDecision {
    pub id: String,
    pub reusable: bool,
    pub reason: InvalidationReason,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub file_role: Option<String>,
}
#[derive(Clone, Debug, Serialize)]
pub struct VerifiedOutput {
    pub stage: String,
    pub role: String,
    pub path: PathBuf,
    pub artifact: Option<ArtifactPin>,
}
#[derive(Clone, Debug, Serialize)]
pub struct ReplayValidation {
    pub version: u32,
    pub earliest_invalidation: Option<String>,
    pub stages: Vec<StageDecision>,
    pub completed_outputs: Vec<VerifiedOutput>,
    pub compiler_inputs_verified: bool,
}
impl ReplayValidation {
    pub fn output(&self, stage: &str, role: &str) -> Option<&Path> {
        self.completed_outputs
            .iter()
            .find(|row| row.stage == stage && row.role == role)
            .map(|row| row.path.as_path())
    }
    pub fn valid(&self) -> bool {
        self.earliest_invalidation.is_none()
    }
}

pub fn load_receipt(path: &Path, limits: &ReplayLimits) -> Result<ReplayReceipt> {
    let file = File::open(path)?;
    if !file.metadata()?.is_file() || file.metadata()?.len() > limits.receipt_bytes {
        return Err("replay receipt byte limit".into());
    }
    let mut bytes = Vec::new();
    file.take(limits.receipt_bytes + 1)
        .read_to_end(&mut bytes)?;
    if bytes.len() as u64 > limits.receipt_bytes {
        return Err("replay receipt byte limit".into());
    }
    let receipt = serde_json::from_slice(&bytes)?;
    validate_shape(&receipt, limits)?;
    Ok(receipt)
}
pub fn write_receipt(path: &Path, receipt: &ReplayReceipt) -> Result<()> {
    validate_shape(receipt, &ReplayLimits::default())?;
    let parent = path.parent().unwrap_or(Path::new("."));
    let temporary = parent.join(format!(
        ".replay-{}-{}.tmp",
        std::process::id(),
        NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
    ));
    struct Cleanup(PathBuf);
    impl Drop for Cleanup {
        fn drop(&mut self) {
            let _ = fs::remove_file(&self.0);
        }
    }
    let _cleanup = Cleanup(temporary.clone());
    let file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&temporary)?;
    let mut writer = BufWriter::with_capacity(64 * 1024, file);
    {
        let mut limited = LimitedWriter {
            inner: &mut writer,
            remaining: ReplayLimits::default().receipt_bytes,
        };
        serde_json::to_writer_pretty(&mut limited, receipt)?;
        limited.write_all(b"\n")?;
    }
    writer.flush()?;
    if writer.get_ref().metadata()?.len() > ReplayLimits::default().receipt_bytes {
        return Err("replay receipt byte limit".into());
    }
    writer.get_ref().sync_all()?;
    drop(writer);
    fs::rename(&temporary, path)?;
    #[cfg(unix)]
    File::open(parent)?.sync_all()?;
    Ok(())
}
pub fn validate_receipt(
    path: &Path,
    current_producers: &BTreeMap<String, String>,
    limits: &ReplayLimits,
) -> Result<ReplayValidation> {
    let receipt = load_receipt(path, limits)?;
    let root = resolve_root(path, &receipt.bundle_root)?;
    let mut validation = ReplayValidation {
        version: VERSION,
        earliest_invalidation: None,
        stages: Vec::new(),
        completed_outputs: Vec::new(),
        compiler_inputs_verified: limits.verify_compiler_inputs,
    };
    let mut valid = HashSet::new();
    let mut admitted = BTreeMap::<String, (u64, String, Option<(u32, String)>)>::new();
    let mut total = 0u64;
    let options = options_identity(&receipt.arguments, &receipt.path_arguments);
    for stage in &receipt.stages {
        let mut reason = if stage
            .dependencies
            .iter()
            .any(|dependency| !valid.contains(dependency.as_str()))
        {
            InvalidationReason::DependencyInvalid
        } else if stage.fingerprint != stage_fingerprint(stage) {
            InvalidationReason::StageFingerprint
        } else if stage.options != options {
            InvalidationReason::OptionsChanged
        } else if current_producers.get(&stage.producer_key).is_none() {
            InvalidationReason::ProducerUnavailable
        } else if current_producers.get(&stage.producer_key) != Some(&stage.producer) {
            InvalidationReason::ProducerChanged
        } else {
            InvalidationReason::Valid
        };
        let mut file_role = None;
        if reason == InvalidationReason::Valid {
            for (output, pin) in stage
                .inputs
                .iter()
                .map(|pin| (false, pin))
                .chain(stage.outputs.iter().map(|pin| (true, pin)))
            {
                let result = validate_pin(pin, &root, limits, &mut total, &mut admitted);
                reason = match result {
                    Ok(()) => continue,
                    Err(PinFailure::Missing) => {
                        if output {
                            InvalidationReason::OutputMissing
                        } else {
                            InvalidationReason::InputMissing
                        }
                    }
                    Err(PinFailure::Changed) => {
                        if output {
                            InvalidationReason::OutputChanged
                        } else {
                            InvalidationReason::InputChanged
                        }
                    }
                    Err(PinFailure::Artifact) => InvalidationReason::ArtifactInvalid,
                    Err(PinFailure::Limit) => InvalidationReason::ResourceLimit,
                };
                file_role = Some(pin.role.clone());
                break;
            }
        }
        if reason == InvalidationReason::Valid {
            if stage.producer_key == "metadata" {
                if validate_metadata_authority(&receipt, stage, &root).is_err() {
                    reason = InvalidationReason::InputChanged;
                    file_role = Some("metadata_authority".into());
                }
            }
        }
        if reason == InvalidationReason::Valid {
            if let Some(binding) = &stage.classpath_inputs {
                if validate_classpath_inputs(binding, &root).is_err() {
                    reason = InvalidationReason::InputChanged;
                    file_role = Some("classpath_inputs".into());
                }
            }
        }
        if reason == InvalidationReason::Valid {
            if let Some(binding) = &stage.compiler_inputs {
                reason =
                    match validate_pin(&binding.contexts, &root, limits, &mut total, &mut admitted)
                    {
                        Ok(()) => InvalidationReason::Valid,
                        Err(PinFailure::Missing) => InvalidationReason::CompilerInputsMissing,
                        Err(PinFailure::Limit) => InvalidationReason::ResourceLimit,
                        Err(_) => InvalidationReason::CompilerInputsChanged,
                    };
                if reason == InvalidationReason::Valid && limits.verify_compiler_inputs {
                    let physical_root = root.join(&binding.root);
                    let context_path = root.join(&binding.contexts.path);
                    if !physical_root.is_dir() {
                        reason = InvalidationReason::CompilerInputsMissing;
                    } else if !physical_root
                        .canonicalize()
                        .is_ok_and(|path| path.starts_with(&root))
                    {
                        reason = InvalidationReason::CompilerInputsChanged;
                    } else {
                        let inventory_limits = selector_extract::compiler_inputs::InventoryLimits {
                            workers: limits.compiler_workers.clamp(1, 64),
                            ..Default::default()
                        };
                        reason = match selector_extract::compiler_inputs::admit(&context_path, &physical_root, &inventory_limits) {
                            Ok(admitted) if admitted.identity.to_string() == binding.identity => InvalidationReason::Valid,
                            Ok(admitted) if admitted.receipt.products.iter().any(|product| product.status == selector_extract::compiler_inputs::InventoryStatus::Missing) => InvalidationReason::CompilerInputsMissing,
                            _ => InvalidationReason::CompilerInputsChanged,
                        };
                    }
                }
                if reason != InvalidationReason::Valid {
                    file_role = Some("compiler_inputs".into());
                }
            }
        }
        let reusable = reason == InvalidationReason::Valid;
        if reusable {
            valid.insert(stage.id.as_str());
            validation
                .completed_outputs
                .extend(stage.outputs.iter().map(|pin| VerifiedOutput {
                    stage: stage.id.clone(),
                    role: pin.role.clone(),
                    path: root.join(&pin.path),
                    artifact: pin.artifact.clone(),
                }));
        } else if validation.earliest_invalidation.is_none() {
            validation.earliest_invalidation = Some(stage.id.clone());
        }
        validation.stages.push(StageDecision {
            id: stage.id.clone(),
            reusable,
            reason,
            file_role,
        });
    }
    Ok(validation)
}

/// Regular-file pins cannot establish directory inventories or continued
/// absence of a formerly empty output. Re-admit exactly the recorded native
/// metadata bundle before a metadata-enabled extracted artifact is reusable.
fn validate_metadata_authority(
    receipt: &ReplayReceipt,
    stage: &StageReceipt,
    root: &Path,
) -> Result<()> {
    let prefix = match (
        receipt.arguments.first().map(String::as_str),
        stage.id.as_str(),
    ) {
        (Some("extract" | "run"), "head.metadata") => "",
        (Some("run"), "base.metadata") => "base-",
        _ => return Err("metadata stage has no exact recorded extraction side".into()),
    };
    let argument = |name: &str| -> Result<(usize, &str)> {
        let flag = format!("--{prefix}{name}");
        let mut found = receipt
            .arguments
            .iter()
            .enumerate()
            .filter(|(_, value)| **value == flag);
        let index = found.next().ok_or("missing recorded metadata argument")?.0;
        if found.next().is_some() {
            return Err("ambiguous recorded metadata argument".into());
        }
        Ok((
            index + 1,
            receipt
                .arguments
                .get(index + 1)
                .ok_or("missing metadata argument value")?,
        ))
    };
    let physical_argument = |name: &str| -> Result<PathBuf> {
        let (index, _) = argument(name)?;
        let relative = receipt
            .path_arguments
            .get(&index)
            .ok_or("unbound recorded metadata path")?;
        Ok(root.join(relative))
    };
    let input = |role: &str, name: &str| -> Result<PathBuf> {
        let mut found = stage.inputs.iter().filter(|pin| pin.role == role);
        let pin = found.next().ok_or("missing metadata input pin")?;
        if found.next().is_some() {
            return Err("ambiguous metadata input pin".into());
        }
        let path = root.join(&pin.path);
        if path != physical_argument(name)? {
            return Err("metadata input differs from recorded argument".into());
        }
        Ok(path)
    };
    let manifest = input("metadata_manifest", "external-metadata")?;
    let contexts = input("metadata_contexts", "contexts")?;
    let map = input("metadata_binary_map", "metadata-binary-map")?;
    let (_, producer) = argument("external-metadata-producer")?;
    let checked = crate::metadata_stage::CheckedInputs::open(
        &manifest,
        selector_types::ContentHash::from_hex(producer)?,
        &map,
        &contexts,
        &physical_argument("compiler-input-root")?,
    )?;
    if checked.identity().to_string() != stage.models {
        return Err("metadata authority bundle identity changed".into());
    }
    Ok(())
}

fn validate_shape(receipt: &ReplayReceipt, limits: &ReplayLimits) -> Result<()> {
    if receipt.version != VERSION {
        return Err("unsupported replay receipt version; expected version 3".into());
    }
    if receipt.stages.is_empty()
        || receipt.stages.len() > limits.stages
        || receipt.arguments.len() > limits.arguments
    {
        return Err("replay receipt schema/count limit".into());
    }
    if receipt.bundle_root.len() > 8192
        || Path::new(&receipt.bundle_root).is_absolute()
        || receipt.bundle_root.contains('\\')
        || receipt.bundle_root.contains('\0')
    {
        return Err("replay bundle root".into());
    }
    if receipt
        .arguments
        .iter()
        .any(|arg| arg.len() > 65_536 || arg.contains('\0'))
    {
        return Err("replay argument limit".into());
    }
    if receipt
        .arguments
        .iter()
        .any(|arg| arg == "--assume-ordinary-compilation")
        && (receipt.arguments.first().map(String::as_str) != Some("query")
            || ![
                "--assume-owning-test-classpath",
                "--assume-independent-suites",
                "--classpath-absence-request",
                "--base-facts",
                "--base-graph",
                "--head-facts",
                "--head-graph",
            ]
            .iter()
            .all(|flag| receipt.arguments.iter().any(|arg| arg == flag))
            || receipt.arguments.iter().any(|arg| arg == "--plan-only"))
    {
        return Err(
            "ordinary compilation replay requires an explicit paired owning-classpath query".into(),
        );
    }
    let mut ids = HashSet::new();
    let mut pins = 0usize;
    for stage in &receipt.stages {
        if !name(&stage.id)
            || !name(&stage.producer_key)
            || !hash(&stage.producer)
            || !hash(&stage.models)
            || !hash(&stage.options)
            || !hash(&stage.fingerprint)
            || stage
                .dependencies
                .iter()
                .any(|id| !ids.contains(id.as_str()))
            || !ids.insert(stage.id.as_str())
        {
            return Err("replay stage identity/order".into());
        }
        // Native stage IDs carry protocol roles. A historical planner-only
        // key must not validate a complete selection outcome after policy edits.
        let role = match stage.id.as_str() {
            "head.inputs" | "base.inputs" => Some("inputs"),
            "query.plan" => Some("query"),
            "query.solve" => Some("solve"),
            "query.report" => Some("report"),
            _ => None,
        };
        if let Some(role) = role {
            if stage.producer_key != role {
                return Err(format!(
                    "native replay stage {} requires producer role {role}",
                    stage.id
                )
                .into());
            }
        }
        if stage.id == "query.plan" {
            let owning = receipt
                .arguments
                .iter()
                .any(|arg| arg == "--assume-owning-test-classpath");
            if owning != stage.classpath_inputs.is_some() {
                return Err("owning classpath replay requires physical inventory bindings".into());
            }
        }
        let required_dependencies = match stage.id.as_str() {
            "query.plan" => {
                let suffix = match receipt.arguments.first().map(String::as_str) {
                    Some("query") => "inputs",
                    Some("run") => "graph",
                    _ => return Err("native query stages require a run or query invocation".into()),
                };
                let head = format!("head.{suffix}");
                let base = format!("base.{suffix}");
                let mut dependencies = vec![head];
                if ids.contains(base.as_str()) {
                    dependencies.push(base);
                }
                Some(dependencies)
            }
            "query.solve" => Some(vec!["query.plan".to_owned()]),
            "query.report" => Some(vec!["query.solve".to_owned()]),
            _ => None,
        };
        if required_dependencies
            .as_ref()
            .is_some_and(|required| *required != stage.dependencies)
        {
            return Err(
                format!("native replay stage {} has invalid dependencies", stage.id).into(),
            );
        }
        for list in [&stage.inputs, &stage.outputs] {
            let mut roles = HashSet::new();
            for pin in list {
                pins += 1;
                if !name(&pin.role)
                    || !roles.insert(pin.role.as_str())
                    || portable(Path::new(&pin.path)).ok().as_deref() != Some(pin.path.as_str())
                    || !hash(&pin.sha256)
                {
                    return Err("replay file identity/path".into());
                }
                if let Some(artifact) = &pin.artifact {
                    kind(artifact.kind)?;
                    if !hash(&artifact.identity) {
                        return Err("replay artifact identity".into());
                    }
                }
            }
        }
        if let Some(binding) = &stage.compiler_inputs {
            pins += 1;
            if !hash(&binding.identity)
                || (binding.root != "."
                    && portable(Path::new(&binding.root)).ok().as_deref()
                        != Some(binding.root.as_str()))
                || !name(&binding.contexts.role)
                || !hash(&binding.contexts.sha256)
                || binding.contexts.artifact.is_some()
                || portable(Path::new(&binding.contexts.path)).ok().as_deref()
                    != Some(binding.contexts.path.as_str())
            {
                return Err("replay compiler input binding".into());
            }
        }
        if let Some(binding) = &stage.classpath_inputs {
            if stage.id != "query.plan" {
                return Err("classpath inputs require query.plan".into());
            }
            let mut paths = HashSet::new();
            for pin in &binding.directories {
                pins += 1;
                if !hash(&pin.sha256)
                    || portable(Path::new(&pin.path)).ok().as_deref() != Some(pin.path.as_str())
                    || !paths.insert(pin.path.as_str())
                {
                    return Err("replay classpath directory binding".into());
                }
            }
            for path in &binding.absent {
                pins += 1;
                if portable(Path::new(path)).ok().as_deref() != Some(path.as_str())
                    || !paths.insert(path.as_str())
                {
                    return Err("replay classpath negative binding".into());
                }
            }
        }
    }
    if pins > limits.pins || receipt.producers.len() > limits.stages {
        return Err("replay pin/producer count limit".into());
    }
    for (key, producer) in &receipt.producers {
        if !name(key) || !hash(producer) {
            return Err("replay producer identity".into());
        }
    }
    for (&index, path) in &receipt.path_arguments {
        if index == 0
            || index >= receipt.arguments.len()
            || (path != "." && portable(Path::new(path)).ok().as_deref() != Some(path.as_str()))
        {
            return Err("replay path argument".into());
        }
    }
    Ok(())
}
fn name(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || b"_.-".contains(&byte))
}
fn hash(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}
fn portable(path: &Path) -> Result<String> {
    if path.as_os_str().is_empty()
        || path
            .components()
            .any(|part| !matches!(part, Component::Normal(_)))
    {
        return Err("nonportable replay path".into());
    }
    let value = path.to_str().ok_or("non-UTF8 replay path")?;
    if value.len() > 8192 || value.contains(['\\', '\0']) {
        return Err("nonportable replay path".into());
    }
    Ok(path
        .components()
        .map(|part| part.as_os_str().to_str().unwrap())
        .collect::<Vec<_>>()
        .join("/"))
}
fn relative_root(from: &Path, target: &Path) -> Result<String> {
    let a: Vec<_> = from.components().collect();
    let b: Vec<_> = target.components().collect();
    let common = a.iter().zip(&b).take_while(|(a, b)| a == b).count();
    if common == 0 {
        return Err("replay bundle roots use different volumes".into());
    }
    let mut pieces = vec!["..".to_owned(); a.len() - common];
    for part in &b[common..] {
        pieces.push(
            part.as_os_str()
                .to_str()
                .ok_or("non-UTF8 bundle root")?
                .to_owned(),
        );
    }
    Ok(if pieces.is_empty() {
        ".".into()
    } else {
        pieces.join("/")
    })
}
fn resolve_root(receipt: &Path, root: &str) -> Result<PathBuf> {
    Ok(fs::canonicalize(
        receipt.parent().unwrap_or(Path::new(".")).join(root),
    )?)
}
fn kind(value: u32) -> Result<ArtifactKind> {
    match value {
        1 => Ok(ArtifactKind::Facts),
        2 => Ok(ArtifactKind::Graph),
        3 => Ok(ArtifactKind::Summaries),
        4 => Ok(ArtifactKind::Continuation),
        5 => Ok(ArtifactKind::Effects),
        _ => Err("unknown replay artifact kind".into()),
    }
}
fn hex(value: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(value.len() * 2);
    for byte in value {
        out.push(DIGITS[(byte >> 4) as usize] as char);
        out.push(DIGITS[(byte & 15) as usize] as char);
    }
    out
}
fn hash_file(path: &Path, maximum: u64) -> Result<(u64, String)> {
    let mut file = File::open(path)?;
    let expected = file.metadata()?.len();
    if !file.metadata()?.is_file() || expected > maximum {
        return Err("replay input byte limit".into());
    }
    let mut total = 0u64;
    let mut hash = Sha256::new();
    let mut bytes = [0; 64 * 1024];
    loop {
        let count = file.read(&mut bytes)?;
        if count == 0 {
            break;
        }
        total = total
            .checked_add(count as u64)
            .ok_or("replay input size overflow")?;
        if total > maximum {
            return Err("replay input byte limit".into());
        }
        hash.update(&bytes[..count]);
    }
    if total != expected || file.metadata()?.len() != expected {
        return Err("replay input changed while reading".into());
    }
    Ok((total, hex(&hash.finalize())))
}
fn stage_fingerprint(stage: &StageReceipt) -> String {
    fn field(hash: &mut Sha256, value: &[u8]) {
        hash.update((value.len() as u64).to_le_bytes());
        hash.update(value);
    }
    let mut hash = Sha256::new();
    hash.update(b"selector-native-replay-stage/v3\0");
    for value in [
        &stage.id,
        &stage.producer_key,
        &stage.producer,
        &stage.models,
        &stage.options,
    ] {
        field(&mut hash, value.as_bytes());
    }
    hash.update((stage.dependencies.len() as u64).to_le_bytes());
    for dependency in &stage.dependencies {
        field(&mut hash, dependency.as_bytes());
    }
    for pins in [&stage.inputs, &stage.outputs] {
        hash.update((pins.len() as u64).to_le_bytes());
        for pin in pins {
            for value in [&pin.role, &pin.path, &pin.sha256] {
                field(&mut hash, value.as_bytes());
            }
            hash.update(pin.bytes.to_le_bytes());
            if let Some(artifact) = &pin.artifact {
                hash.update([1]);
                hash.update(artifact.kind.to_le_bytes());
                field(&mut hash, artifact.identity.as_bytes());
            } else {
                hash.update([0]);
            }
        }
    }
    if let Some(binding) = &stage.compiler_inputs {
        hash.update([1]);
        for value in [
            &binding.root,
            &binding.identity,
            &binding.contexts.role,
            &binding.contexts.path,
            &binding.contexts.sha256,
        ] {
            field(&mut hash, value.as_bytes());
        }
        hash.update(binding.contexts.bytes.to_le_bytes());
    } else {
        hash.update([0]);
    }
    if let Some(binding) = &stage.classpath_inputs {
        field(&mut hash, b"classpath_inputs/v1");
        field(
            &mut hash,
            &serde_json::to_vec(binding).expect("classpath binding JSON"),
        );
    }
    hex(&hash.finalize())
}
fn validate_classpath_inputs(binding: &ClasspathInputs, root: &Path) -> Result<()> {
    use selector_models::binary::{AdmittedEntry, ClasspathEntry, EntryKind, Limits};
    let no_symlinks = |path: &Path| -> Result<()> {
        let mut prefix = PathBuf::new();
        for component in path.components() {
            prefix.push(component);
            match fs::symlink_metadata(&prefix) {
                Ok(metadata) if metadata.file_type().is_symlink() => {
                    return Err("classpath symlink input".into());
                }
                Ok(_) => (),
                Err(error) if error.kind() == io::ErrorKind::NotFound => break,
                Err(error) => return Err(error.into()),
            }
        }
        Ok(())
    };
    for pin in &binding.directories {
        let path = root.join(&pin.path);
        no_symlinks(&path)?;
        if !path.canonicalize()?.starts_with(root) {
            return Err("classpath directory escapes receipt root".into());
        }
        let admitted = AdmittedEntry::admit(
            ClasspathEntry {
                path,
                sha256: selector_types::ContentHash::from_hex(&pin.sha256)?,
                kind: EntryKind::Directory {
                    files: pin.files,
                    bytes: pin.bytes,
                },
            },
            Limits::default(),
            None,
        )?;
        if let Some(error) = admitted.error() {
            return Err(error.into());
        }
    }
    for path in &binding.absent {
        let path = root.join(path);
        no_symlinks(&path)?;
        // Broken symlinks also invalidate an absence claim.
        match fs::symlink_metadata(path) {
            Err(error) if error.kind() == io::ErrorKind::NotFound => (),
            _ => return Err("classpath negative input appeared".into()),
        }
    }
    Ok(())
}
enum PinFailure {
    Missing,
    Changed,
    Artifact,
    Limit,
}
struct LimitedWriter<'a, W> {
    inner: &'a mut W,
    remaining: u64,
}
impl<W: Write> Write for LimitedWriter<'_, W> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        if bytes.len() as u64 > self.remaining {
            return Err(io::Error::other("replay receipt byte limit"));
        }
        let written = self.inner.write(bytes)?;
        self.remaining -= written as u64;
        Ok(written)
    }
    fn flush(&mut self) -> io::Result<()> {
        self.inner.flush()
    }
}
fn validate_pin(
    pin: &FilePin,
    root: &Path,
    limits: &ReplayLimits,
    total: &mut u64,
    admitted: &mut BTreeMap<String, (u64, String, Option<(u32, String)>)>,
) -> std::result::Result<(), PinFailure> {
    let cached = admitted.get(&pin.path);
    let expected_artifact = pin
        .artifact
        .as_ref()
        .map(|artifact| (artifact.kind, artifact.identity.clone()));
    if let Some((bytes, sha256, artifact)) = cached {
        if *bytes == pin.bytes && *sha256 == pin.sha256 && *artifact == expected_artifact {
            return Ok(());
        }
        return Err(PinFailure::Changed);
    }
    let path = fs::canonicalize(root.join(&pin.path)).map_err(|_| PinFailure::Missing)?;
    if !path.starts_with(root) {
        return Err(PinFailure::Artifact);
    }
    if pin.bytes > limits.file_bytes || total.saturating_add(pin.bytes) > limits.total_bytes {
        return Err(PinFailure::Limit);
    }
    let (bytes, sha256) = hash_file(&path, limits.file_bytes).map_err(|_| PinFailure::Changed)?;
    if bytes != pin.bytes || sha256 != pin.sha256 {
        return Err(PinFailure::Changed);
    }
    if let Some(artifact) = &pin.artifact {
        let verified = selector_artifacts::verify_file(
            &path,
            kind(artifact.kind).map_err(|_| PinFailure::Artifact)?,
            limits.file_bytes,
        )
        .map_err(|_| PinFailure::Artifact)?;
        if hex(&verified.identity) != artifact.identity {
            return Err(PinFailure::Artifact);
        }
    }
    *total += bytes;
    admitted.insert(pin.path.clone(), (bytes, sha256, expected_artifact));
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn classpath_inventory_and_negative_pins_survive_frozen_replay() {
        for mutation in ["none", "directory", "absent", "binding_removed"] {
            let directory = tempfile::tempdir().unwrap();
            let root = directory.path().canonicalize().unwrap();
            fs::create_dir(root.join("classes")).unwrap();
            fs::write(root.join("classes/item"), b"one").unwrap();
            let digest = hex(&Sha256::digest(b"one"));
            let inventory = serde_json::to_vec(&serde_json::json!([
                {"path":"item","bytes":3,"sha256":digest}
            ]))
            .unwrap();
            let producer = "11".repeat(32);
            let producers = BTreeMap::from([
                ("inputs".into(), producer.clone()),
                ("query".into(), producer.clone()),
            ]);
            let mut receipt = ReplayReceipt::new(
                vec!["query".into(), "--assume-owning-test-classpath".into()],
                producers.clone(),
            );
            let options = options_identity(&receipt.arguments, &receipt.path_arguments);
            receipt.add_stage(StageReceipt::new(
                "head.inputs",
                "inputs",
                &producer,
                ZERO,
                &options,
            ));
            let mut plan = StageReceipt::new("query.plan", "query", &producer, ZERO, &options);
            plan.dependencies.push("head.inputs".into());
            plan.classpath_inputs = Some(ClasspathInputs {
                directories: vec![DirectoryPin {
                    path: "classes".into(),
                    sha256: hex(&Sha256::digest(&inventory)),
                    files: 1,
                    bytes: 3,
                }],
                absent: vec!["optional.jar".into()],
            });
            receipt.add_stage(plan);
            let path = root.join("receipt.json");
            write_receipt(&path, &receipt).unwrap();
            match mutation {
                "directory" => fs::write(root.join("classes/item"), b"two").unwrap(),
                "absent" => fs::write(root.join("optional.jar"), b"new").unwrap(),
                "binding_removed" => {
                    receipt.stages[1].classpath_inputs = None;
                    receipt.stages[1].seal();
                    assert!(write_receipt(&path, &receipt).is_err());
                    continue;
                }
                _ => (),
            }
            let validation = validate_receipt(
                &path,
                &producers,
                &ReplayLimits {
                    verify_compiler_inputs: false,
                    ..Default::default()
                },
            )
            .unwrap();
            assert_eq!(validation.valid(), mutation == "none");
            if mutation != "none" {
                assert_eq!(
                    validation.earliest_invalidation.as_deref(),
                    Some("query.plan")
                );
                assert_eq!(
                    validation.stages[1].file_role.as_deref(),
                    Some("classpath_inputs")
                );
            }
        }
    }
    fn metadata_fixture(root: &Path, side: &str) -> ReplayReceipt {
        use selector_extract::external_metadata::MetadataProviderAuthority;
        use serde_json::json;
        let root = root.canonicalize().unwrap();
        fs::create_dir_all(root.join("classes/fixture")).unwrap();
        let class = include_bytes!("../../../fixtures/binary/classes/fixture/Probe.class");
        fs::write(root.join("classes/fixture/Probe.class"), class).unwrap();
        let digest = |bytes: &[u8]| hex(&Sha256::digest(bytes));
        let inventory = serde_json::to_vec(
            &json!([{"path":"fixture/Probe.class","bytes":class.len(),"sha256":digest(class)}]),
        )
        .unwrap();
        let directory = digest(&inventory);
        let absent = digest(b"{\"kind\":\"absent_empty_project_output\"}");
        let contexts = json!({"schema_version":"sbt-compiler-context/v1","revision":"r","source_root":"/captured","errors":[],
            "contexts":[{"context_id":"a","source_revision":"r","compiler_environment_fingerprint":"11".repeat(32),
            "full_classpath":[{"index":0,"path":"/captured/classes","sha256":directory},{"index":1,"path":"/captured/absent","sha256":absent}]}],
            "input_objects":[{"path":"/captured/classes","kind":"directory","sha256":directory,"files":1,"bytes":class.len()},
                {"path":"/captured/absent","kind":"absent_empty_project_output","sha256":absent,"bytes":0}]});
        let map = json!({"version":1,"revision":"r","contexts":[{"id":"a","entries":[
            {"path":root.join("classes"),"kind":"directory","sha256":directory,"files":1,"bytes":class.len()},
            {"path":root.join("absent"),"kind":"absent_empty_output","sha256":absent}]}],"methods":[]});
        for (name, value) in [("contexts.json", contexts), ("map.json", map)] {
            fs::write(root.join(name), serde_json::to_vec(&value).unwrap()).unwrap();
        }
        let contexts_sha = selector_types::ContentHash::from_hex(&digest(
            &fs::read(root.join("contexts.json")).unwrap(),
        ))
        .unwrap();
        let authority = crate::external_metadata::CapturedMetadataAuthority::open(
            &root.join("map.json"),
            &root.join("contexts.json"),
            contexts_sha,
            &root,
            &Default::default(),
        )
        .unwrap();
        let converter = "22".repeat(32);
        let manifest = json!({"schema":"compiler-external-metadata/v1","producer_sha256":converter,
            "contexts_sha256":contexts_sha.to_string(),"authority_sha256":authority.identity().to_string(),"payloads":[],"bindings":[]});
        fs::write(
            root.join("metadata.json"),
            serde_json::to_vec(&manifest).unwrap(),
        )
        .unwrap();
        let checked = crate::metadata_stage::CheckedInputs::open(
            &root.join("metadata.json"),
            selector_types::ContentHash::from_hex(&converter).unwrap(),
            &root.join("map.json"),
            &root.join("contexts.json"),
            &root,
        )
        .unwrap();
        let prefix = if side == "base" { "base-" } else { "" };
        let mut args = vec![if side == "base" {
            "run".into()
        } else {
            "extract".into()
        }];
        let mut paths = BTreeMap::new();
        for (name, value) in [
            ("external-metadata", "metadata.json"),
            ("external-metadata-producer", converter.as_str()),
            ("metadata-binary-map", "map.json"),
            ("contexts", "contexts.json"),
            ("compiler-input-root", "."),
        ] {
            args.push(format!("--{prefix}{name}"));
            args.push(value.to_owned());
            if name != "external-metadata-producer" {
                paths.insert(args.len() - 1, value.to_owned());
            }
        }
        let producer = env!("SELECTOR_METADATA_PRODUCER").to_owned();
        let mut receipt = ReplayReceipt::new(
            args,
            BTreeMap::from([("metadata".into(), producer.clone())]),
        );
        receipt.path_arguments = paths;
        let mut stage = StageReceipt::new(
            format!("{side}.metadata"),
            "metadata",
            producer,
            checked.identity().to_string(),
            options_identity(&receipt.arguments, &receipt.path_arguments),
        );
        for (role, path) in checked.artifact_inputs() {
            stage
                .inputs
                .push(FilePin::capture(role, path, &root, None).unwrap());
        }
        receipt.add_stage(stage);
        receipt
    }

    #[test]
    fn metadata_replay_rechecks_nonproject_directories_and_absent_outputs_even_when_frozen() {
        for frozen in [false, true] {
            for change in ["directory", "absent"] {
                let directory = tempfile::tempdir().unwrap();
                let receipt = metadata_fixture(directory.path(), "head");
                let path = directory.path().join("receipt.json");
                write_receipt(&path, &receipt).unwrap();
                let limits = ReplayLimits {
                    verify_compiler_inputs: !frozen,
                    ..Default::default()
                };
                assert!(
                    validate_receipt(&path, &receipt.producers, &limits)
                        .unwrap()
                        .valid()
                );
                if change == "directory" {
                    fs::write(
                        directory.path().join("classes/fixture/New.class"),
                        b"new provider",
                    )
                    .unwrap();
                } else {
                    fs::create_dir(directory.path().join("absent")).unwrap();
                }
                let validation = validate_receipt(&path, &receipt.producers, &limits).unwrap();
                assert_eq!(
                    validation.earliest_invalidation.as_deref(),
                    Some("head.metadata")
                );
                assert_eq!(
                    validation.stages[0].reason,
                    InvalidationReason::InputChanged
                );
                assert_eq!(
                    validation.stages[0].file_role.as_deref(),
                    Some("metadata_authority")
                );
            }
        }
    }

    #[test]
    fn metadata_replay_uses_exact_side_and_requires_unambiguous_relocated_bindings() {
        let directory = tempfile::tempdir().unwrap();
        let original = metadata_fixture(directory.path(), "base");
        assert!(
            validate_metadata_authority(
                &original,
                &original.stages[0],
                &directory.path().canonicalize().unwrap()
            )
            .is_ok()
        );
        for change in 0..5 {
            let mut receipt = original.clone();
            match change {
                0 => receipt.arguments[0] = "query".into(),
                1 => {
                    receipt.path_arguments.remove(&2);
                }
                2 => receipt
                    .arguments
                    .extend(["--base-external-metadata-producer".into(), "22".repeat(32)]),
                3 => {
                    let pin = receipt.stages[0].inputs[0].clone();
                    receipt.stages[0].inputs.push(pin);
                }
                4 => receipt.stages[0].models = "00".repeat(32),
                _ => unreachable!(),
            }
            assert!(
                validate_metadata_authority(
                    &receipt,
                    &receipt.stages[0],
                    &directory.path().canonicalize().unwrap()
                )
                .is_err(),
                "case {change}"
            );
        }
    }
    fn fixture(root: &Path) -> ReplayReceipt {
        for (path, bytes) in [("source", "source"), ("facts", "facts"), ("graph", "graph")] {
            fs::write(root.join(path), bytes).unwrap();
        }
        let producers = BTreeMap::from([
            ("extract".into(), "11".repeat(32)),
            ("graph".into(), "22".repeat(32)),
        ]);
        let mut receipt = ReplayReceipt::new(
            vec![
                "run".into(),
                "--input".into(),
                "source".into(),
                "--changed".into(),
                "src/Known.scala".into(),
                "--max-contexts".into(),
                "100".into(),
            ],
            producers.clone(),
        );
        receipt.path_arguments.insert(2, "source".into());
        let options = options_identity(&receipt.arguments, &receipt.path_arguments);
        let mut extract = StageReceipt::new(
            "head.extract",
            "extract",
            &producers["extract"],
            ZERO,
            &options,
        );
        extract
            .inputs
            .push(FilePin::capture("source", &root.join("source"), root, None).unwrap());
        extract
            .outputs
            .push(FilePin::capture("facts", &root.join("facts"), root, None).unwrap());
        receipt.add_stage(extract);
        let mut graph =
            StageReceipt::new("head.graph", "graph", &producers["graph"], ZERO, &options);
        graph.dependencies.push("head.extract".into());
        graph
            .inputs
            .push(FilePin::capture("facts", &root.join("facts"), root, None).unwrap());
        graph
            .outputs
            .push(FilePin::capture("graph", &root.join("graph"), root, None).unwrap());
        receipt.add_stage(graph);
        receipt
    }
    #[test]
    fn unchanged_warm_inputs_and_earliest_invalidation_are_explicit() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let receipt = fixture(root);
        let path = root.join("receipt.json");
        write_receipt(&path, &receipt).unwrap();
        for _ in 0..2 {
            let validation =
                validate_receipt(&path, &receipt.producers, &ReplayLimits::default()).unwrap();
            assert!(validation.valid());
            assert_eq!(
                validation.output("head.graph", "graph"),
                Some(root.canonicalize().unwrap().join("graph").as_path())
            );
        }
        fs::write(root.join("source"), "change").unwrap();
        let validation =
            validate_receipt(&path, &receipt.producers, &ReplayLimits::default()).unwrap();
        assert_eq!(
            validation.earliest_invalidation.as_deref(),
            Some("head.extract")
        );
        assert_eq!(
            validation.stages[0].reason,
            InvalidationReason::InputChanged
        );
        assert_eq!(
            validation.stages[1].reason,
            InvalidationReason::DependencyInvalid
        );
        assert!(validation.completed_outputs.is_empty());
    }
    #[test]
    fn native_query_role_protocol_requires_version_three() {
        let directory = tempfile::tempdir().unwrap();
        let mut receipt = fixture(directory.path());
        assert_eq!(receipt.version, 3);
        let path = directory.path().join("receipt.json");
        for version in [1, 2] {
            receipt.version = version;
            // Header-only upgrades cannot acquire the v3 query-role contract.
            assert!(
                write_receipt(&path, &receipt)
                    .unwrap_err()
                    .to_string()
                    .contains("expected version 3")
            );
            fs::write(&path, serde_json::to_vec(&receipt).unwrap()).unwrap();
            assert!(
                load_receipt(&path, &ReplayLimits::default())
                    .unwrap_err()
                    .to_string()
                    .contains("expected version 3")
            );
        }
    }
    #[test]
    fn changed_seed_resource_policy_raw_argv_and_path_bindings_invalidate_reuse() {
        let directory = tempfile::tempdir().unwrap();
        let receipt = fixture(directory.path());
        let path = directory.path().join("receipt.json");
        for change in 0..6 {
            let mut changed = receipt.clone();
            match change {
                0 => changed.arguments[4] = "src/UnknownChanged.scala".into(),
                1 => changed.arguments[6] = "1".into(),
                2 => changed.arguments[0] = "query".into(),
                3 => {
                    changed.path_arguments.insert(2, "facts".into());
                }
                4 => {
                    changed.path_arguments.remove(&2);
                }
                5 => changed.arguments[2] = "another-raw-input".into(),
                _ => unreachable!(),
            }
            // Simulate an edited receipt without resigning stage metadata.
            fs::write(&path, serde_json::to_vec(&changed).unwrap()).unwrap();
            let validation =
                validate_receipt(&path, &receipt.producers, &ReplayLimits::default()).unwrap();
            assert_eq!(
                validation.earliest_invalidation.as_deref(),
                Some("head.extract")
            );
            assert_eq!(
                validation.stages[0].reason,
                InvalidationReason::OptionsChanged,
                "mutation {change}"
            );
            assert_eq!(
                validation.stages[1].reason,
                InvalidationReason::DependencyInvalid
            );
            assert!(validation.completed_outputs.is_empty());
        }
    }
    #[test]
    fn stale_producer_does_not_invalidate_independent_completed_stage() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let receipt = fixture(root);
        let path = root.join("receipt.json");
        write_receipt(&path, &receipt).unwrap();
        let mut current = receipt.producers.clone();
        current.insert("graph".into(), "33".repeat(32));
        let validation = validate_receipt(&path, &current, &ReplayLimits::default()).unwrap();
        assert_eq!(
            validation.earliest_invalidation.as_deref(),
            Some("head.graph")
        );
        assert!(validation.output("head.extract", "facts").is_some());
        assert!(validation.output("head.graph", "graph").is_none());
        assert_eq!(
            validation.stages[1].reason,
            InvalidationReason::ProducerChanged
        );
    }
    #[test]
    fn artifact_checksum_and_kind_are_verified_without_loading_snapshot_tables() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let file = root.join("facts.rsel");
        selector_artifacts::write(
            &file,
            ArtifactKind::Facts,
            &[selector_artifacts::Section {
                id: 1,
                count: 1,
                bytes: b"opaque",
            }],
        )
        .unwrap();
        assert!(FilePin::capture("facts", &file, root, Some(ArtifactKind::Graph)).is_err());
        let pin = FilePin::capture("facts", &file, root, Some(ArtifactKind::Facts)).unwrap();
        let mut receipt = fixture(root);
        receipt.stages[0].outputs = vec![pin];
        receipt.stages[0].seal();
        let path = root.join("receipt.json");
        write_receipt(&path, &receipt).unwrap();
        let mut bytes = fs::read(&file).unwrap();
        *bytes.last_mut().unwrap() ^= 1;
        fs::remove_file(&file).unwrap();
        fs::write(&file, &bytes).unwrap();
        // Re-signing the ordinary file digest still cannot bypass the internal
        // artifact checksum/section admission retained in this receipt.
        receipt.stages[0].outputs[0].sha256 = hash_file(&file, u64::MAX).unwrap().1;
        receipt.stages[0].seal();
        write_receipt(&path, &receipt).unwrap();
        let validation =
            validate_receipt(&path, &receipt.producers, &ReplayLimits::default()).unwrap();
        assert_eq!(
            validation.stages[0].reason,
            InvalidationReason::ArtifactInvalid
        );
    }
    #[test]
    fn atomic_publication_failure_preserves_destination_and_cleans_temporary() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let receipt = fixture(root);
        let path = root.join("receipt.json");
        fs::create_dir(&path).unwrap();
        fs::write(path.join("keep"), b"original").unwrap();
        assert!(write_receipt(&path, &receipt).is_err());
        assert_eq!(fs::read(path.join("keep")).unwrap(), b"original");
        assert!(!fs::read_dir(root).unwrap().any(|row| {
            row.unwrap()
                .file_name()
                .to_string_lossy()
                .starts_with(".replay-")
        }));
    }
    #[test]
    fn moved_bundle_rebinds_paths_and_rejects_shell_or_escape_instructions() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let mut receipt = fixture(root);
        receipt.path_arguments.insert(2, "source".into());
        let arguments = receipt
            .replay_arguments(&root.join("receipt.json"))
            .unwrap();
        assert_eq!(
            arguments[2],
            root.canonicalize()
                .unwrap()
                .join("source")
                .to_str()
                .unwrap()
        );
        let moved = tempfile::tempdir().unwrap();
        for name in ["source", "facts", "graph"] {
            fs::copy(root.join(name), moved.path().join(name)).unwrap();
        }
        let moved_receipt = moved.path().join("receipt.json");
        write_receipt(&moved_receipt, &receipt).unwrap();
        assert!(
            validate_receipt(&moved_receipt, &receipt.producers, &ReplayLimits::default())
                .unwrap()
                .valid()
        );
        assert_eq!(
            receipt.replay_arguments(&moved_receipt).unwrap()[2],
            moved
                .path()
                .canonicalize()
                .unwrap()
                .join("source")
                .to_str()
                .unwrap()
        );
        receipt.arguments[0] = "python3".into();
        assert!(
            receipt
                .replay_arguments(&root.join("receipt.json"))
                .is_err()
        );
        receipt.arguments[0] = "run".into();
        receipt.path_arguments.insert(2, "../escape".into());
        assert!(write_receipt(&root.join("receipt.json"), &receipt).is_err());
    }
    fn query_fixture(root: &Path) -> ReplayReceipt {
        let mut receipt = fixture(root);
        receipt.arguments = vec![
            "query".into(),
            "--head-facts".into(),
            "facts".into(),
            "--head-graph".into(),
            "graph".into(),
            "--output".into(),
            "outcome".into(),
        ];
        receipt.path_arguments = BTreeMap::from([
            (2, "facts".into()),
            (4, "graph".into()),
            (6, "outcome".into()),
        ]);
        receipt.producers.extend([
            ("inputs".into(), "66".repeat(32)),
            ("query".into(), "33".repeat(32)),
            ("solve".into(), "44".repeat(32)),
            ("report".into(), "55".repeat(32)),
            ("planner".into(), "77".repeat(32)),
        ]);
        receipt.stages.clear();
        for (file, kind) in [
            ("facts", ArtifactKind::Facts),
            ("graph", ArtifactKind::Graph),
        ] {
            fs::remove_file(root.join(file)).unwrap();
            selector_artifacts::write(
                &root.join(file),
                kind,
                &[selector_artifacts::Section {
                    id: 1,
                    count: 1,
                    bytes: b"verified opaque artifact",
                }],
            )
            .unwrap();
        }
        fs::write(root.join("outcome"), b"saved selection outcome").unwrap();
        let options = options_identity(&receipt.arguments, &receipt.path_arguments);
        let mut inputs = StageReceipt::new(
            "head.inputs",
            "inputs",
            &receipt.producers["inputs"],
            ZERO,
            &options,
        );
        inputs.outputs = vec![
            FilePin::capture(
                "facts",
                &root.join("facts"),
                root,
                Some(ArtifactKind::Facts),
            )
            .unwrap(),
            FilePin::capture(
                "graph",
                &root.join("graph"),
                root,
                Some(ArtifactKind::Graph),
            )
            .unwrap(),
        ];
        receipt.add_stage(inputs);
        let mut plan = StageReceipt::new(
            "query.plan",
            "query",
            &receipt.producers["query"],
            ZERO,
            &options,
        );
        plan.dependencies.push("head.inputs".into());
        receipt.add_stage(plan);
        let mut solve = StageReceipt::new(
            "query.solve",
            "solve",
            &receipt.producers["solve"],
            ZERO,
            &options,
        );
        solve.dependencies.push("query.plan".into());
        solve
            .outputs
            .push(FilePin::capture("outcome", &root.join("outcome"), root, None).unwrap());
        receipt.add_stage(solve);
        let mut report = StageReceipt::new(
            "query.report",
            "report",
            &receipt.producers["report"],
            ZERO,
            &options,
        );
        report.dependencies.push("query.solve".into());
        report.inputs = receipt.stages[2].outputs.clone();
        report.outputs = report.inputs.clone();
        receipt.add_stage(report);
        receipt
    }
    #[test]
    fn header_only_v3_upgrade_cannot_retain_planner_only_role_or_reseal_wrong_native_roles() {
        let dir = tempfile::tempdir().unwrap();
        let original = query_fixture(dir.path());
        let path = dir.path().join("receipt.json");
        for (index, role) in [(0, "query"), (1, "planner"), (2, "query"), (3, "query")] {
            let mut receipt = original.clone();
            receipt.stages[index].producer_key = role.into();
            receipt.stages[index].producer = receipt.producers[role].clone();
            receipt.stages[index].seal();
            fs::write(&path, serde_json::to_vec(&receipt).unwrap()).unwrap();
            assert!(
                load_receipt(&path, &ReplayLimits::default())
                    .unwrap_err()
                    .to_string()
                    .contains("requires producer role")
            );
            assert!(write_receipt(&path, &receipt).is_err());
        }
    }
    #[test]
    fn known_query_stages_cannot_omit_dependency_bindings_after_resealing() {
        let dir = tempfile::tempdir().unwrap();
        let original = query_fixture(dir.path());
        for index in 1..4 {
            let mut receipt = original.clone();
            receipt.stages[index].dependencies.clear();
            receipt.stages[index].seal();
            assert!(
                write_receipt(&dir.path().join("receipt.json"), &receipt)
                    .unwrap_err()
                    .to_string()
                    .contains("invalid dependencies")
            );
        }
    }
    #[test]
    fn selection_policy_only_change_invalidates_saved_selection_but_keeps_completed_graphs() {
        let dir = tempfile::tempdir().unwrap();
        let receipt = query_fixture(dir.path());
        let path = dir.path().join("receipt.json");
        write_receipt(&path, &receipt).unwrap();
        assert!(
            validate_receipt(&path, &receipt.producers, &ReplayLimits::default())
                .unwrap()
                .valid()
        );
        let mut selection_edit = receipt.producers.clone();
        selection_edit.insert("query".into(), "99".repeat(32));
        assert_eq!(
            selection_edit["solve"], receipt.producers["solve"],
            "fixed-point families retain their independent producer"
        );
        let result = validate_receipt(&path, &selection_edit, &ReplayLimits::default()).unwrap();
        assert_eq!(result.earliest_invalidation.as_deref(), Some("query.plan"));
        assert_eq!(result.stages[1].reason, InvalidationReason::ProducerChanged);
        assert_eq!(
            result.stages[2].reason,
            InvalidationReason::DependencyInvalid
        );
        assert_eq!(
            result.stages[3].reason,
            InvalidationReason::DependencyInvalid
        );
        assert!(result.output("head.inputs", "facts").is_some());
        assert!(result.output("head.inputs", "graph").is_some());
        assert!(result.output("query.solve", "outcome").is_none());
    }
    #[test]
    fn report_only_change_preserves_saved_outcome_for_cheap_rerender() {
        let dir = tempfile::tempdir().unwrap();
        let receipt = query_fixture(dir.path());
        let path = dir.path().join("receipt.json");
        write_receipt(&path, &receipt).unwrap();
        let mut report_edit = receipt.producers.clone();
        report_edit.insert("report".into(), "aa".repeat(32));
        let result = validate_receipt(&path, &report_edit, &ReplayLimits::default()).unwrap();
        assert_eq!(
            result.earliest_invalidation.as_deref(),
            Some("query.report")
        );
        assert_eq!(result.stages[3].reason, InvalidationReason::ProducerChanged);
        assert!(result.output("query.solve", "outcome").is_some());
        assert!(
            result
                .stages
                .iter()
                .all(|stage| stage.reusable || stage.id == "query.report")
        );
    }
}
