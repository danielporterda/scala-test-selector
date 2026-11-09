//! Small coordinator for concurrent native-stage receipt recording.
use crate::replay::{
    self, CompilerInputBinding, FilePin, ReplayReceipt, ReplayValidation, StageReceipt,
};
use selector_artifacts::ArtifactKind;
use selector_types::ContentHash;
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::SystemTime;

#[derive(Clone, Copy, Debug)]
pub struct StageFile<'a> {
    pub role: &'a str,
    pub path: &'a Path,
    pub kind: Option<ArtifactKind>,
}
#[derive(Debug)]
pub struct Recording {
    path: PathBuf,
    root: PathBuf,
    receipt: ReplayReceipt,
    stages: BTreeMap<String, StageReceipt>,
    compiler_inputs: BTreeMap<String, CompilerInputBinding>,
    options: String,
    pins: BTreeMap<(PathBuf, u32), (u64, Option<SystemTime>, FilePin)>,
}
impl Recording {
    pub fn new(
        raw: Vec<String>,
        receipt_path: PathBuf,
        path_arguments: Vec<(usize, PathBuf)>,
        producers: BTreeMap<String, String>,
    ) -> replay::Result<Self> {
        let path = absolute_lexical(&receipt_path)?;
        let mut paths: Vec<_> = path_arguments
            .iter()
            .map(|(_, path)| absolute_lexical(path))
            .collect::<replay::Result<_>>()?;
        paths.push(path.clone());
        let mut root = std::env::current_dir()?.canonicalize()?;
        for path in &paths {
            while !path.starts_with(&root) {
                root = root
                    .parent()
                    .ok_or("replay paths do not share a filesystem root")?
                    .to_owned();
            }
        }
        fs::create_dir_all(path.parent().ok_or("receipt parent")?)?;
        let mut receipt = ReplayReceipt::new(raw, producers);
        receipt.set_bundle_root(&path, &root)?;
        for (index, path) in path_arguments {
            receipt.bind_path_argument(index, &absolute_lexical(&path)?, &root)?;
        }
        let options = replay::options_identity(&receipt.arguments, &receipt.path_arguments);
        Ok(Self {
            path,
            root,
            receipt,
            stages: BTreeMap::new(),
            compiler_inputs: BTreeMap::new(),
            options,
            pins: BTreeMap::new(),
        })
    }
    /// Include physically admitted transitive inputs, such as metadata provider
    /// archives outside the invocation's initial path ancestor. This changes
    /// only the coordinate system: every prior pin and binding is rebased and
    /// every affected stage is resealed. Ordinary pin capture remains confined
    /// to the declared root. Callers must admit these inputs before including
    /// them; this method grants no input or semantic authority.
    pub fn include_transitive_inputs<'a>(
        &mut self,
        inputs: impl IntoIterator<Item = &'a Path>,
    ) -> replay::Result<()> {
        let mut root = self.root.clone();
        for input in inputs {
            let input = fs::canonicalize(input)?;
            while !input.starts_with(&root) {
                root = root
                    .parent()
                    .ok_or("transitive input has no shared root")?
                    .to_owned();
            }
        }
        if root == self.root {
            return Ok(());
        }
        if !self.receipt.stages.is_empty() {
            return Err("cannot rebase an already published recording".into());
        }
        let prefix = self.root.strip_prefix(&root)?.to_owned();
        let rebase = |path: &str| -> replay::Result<String> {
            let path = if path == "." {
                prefix.clone()
            } else {
                prefix.join(path)
            };
            Ok(path
                .to_str()
                .ok_or("transitive input root is not UTF-8")?
                .replace('\\', "/"))
        };
        let rebase_binding = |binding: &mut CompilerInputBinding| -> replay::Result<()> {
            binding.contexts.path = rebase(&binding.contexts.path)?;
            binding.root = rebase(&binding.root)?;
            Ok(())
        };
        // Prepare the complete new state before replacing any live state.
        let mut receipt = self.receipt.clone();
        receipt.set_bundle_root(&self.path, &root)?;
        for path in receipt.path_arguments.values_mut() {
            *path = rebase(path)?;
        }
        let options = replay::options_identity(&receipt.arguments, &receipt.path_arguments);
        let mut stages = self.stages.clone();
        for stage in stages.values_mut() {
            for pin in stage.inputs.iter_mut().chain(&mut stage.outputs) {
                pin.path = rebase(&pin.path)?;
            }
            if let Some(binding) = &mut stage.compiler_inputs {
                rebase_binding(binding)?;
            }
            if let Some(binding) = &mut stage.classpath_inputs {
                for pin in &mut binding.directories {
                    pin.path = rebase(&pin.path)?;
                }
                for path in &mut binding.absent {
                    *path = rebase(path)?;
                }
            }
            stage.options = options.clone();
            stage.seal();
        }
        let mut compiler_inputs = self.compiler_inputs.clone();
        for binding in compiler_inputs.values_mut() {
            rebase_binding(binding)?;
        }
        let mut pins = self.pins.clone();
        for (_, _, pin) in pins.values_mut() {
            pin.path = rebase(&pin.path)?;
        }
        self.root = root;
        self.receipt = receipt;
        self.options = options;
        self.stages = stages;
        self.compiler_inputs = compiler_inputs;
        self.pins = pins;
        Ok(())
    }
    pub fn record_stage(
        &mut self,
        id: &str,
        dependencies: &[&str],
        producer_key: &str,
        models: ContentHash,
        inputs: &[StageFile<'_>],
        outputs: &[StageFile<'_>],
    ) -> replay::Result<()> {
        let producer = self
            .receipt
            .producers
            .get(producer_key)
            .ok_or("stage producer is not registered")?
            .clone();
        let mut stage = StageReceipt::new(
            id,
            producer_key,
            producer,
            models.to_string(),
            self.options.clone(),
        );
        stage.dependencies = dependencies
            .iter()
            .map(|value| (*value).to_owned())
            .collect();
        stage.compiler_inputs = self.compiler_inputs.get(id).cloned();
        for input in inputs {
            stage.inputs.push(self.pin(input)?);
        }
        for output in outputs {
            stage.outputs.push(self.pin(output)?);
        }
        stage.seal();
        if let Some(previous) = self.stages.get(id) {
            if previous.fingerprint != stage.fingerprint {
                return Err("conflicting replay stage recordings".into());
            }
        } else {
            self.stages.insert(id.into(), stage);
        }
        Ok(())
    }
    /// Preserve admitted directory inventories and negative provider targets in
    /// the query stage. These bindings are rechecked even for frozen replay.
    pub fn record_classpath_inputs(
        &mut self,
        inputs: &[&selector_native_effects::classpath_absence::PhysicalInputs],
    ) -> replay::Result<()> {
        let relative = |path: &Path| -> replay::Result<String> {
            let path = absolute_lexical(path)?;
            let path = path.strip_prefix(&self.root)?;
            Ok(path
                .to_str()
                .ok_or("classpath path UTF-8")?
                .replace('\\', "/"))
        };
        let mut binding = replay::ClasspathInputs::default();
        for inputs in inputs {
            for entry in &inputs.directories {
                let selector_models::binary::EntryKind::Directory { files, bytes } = entry.kind
                else {
                    return Err("classpath directory binding kind".into());
                };
                binding.directories.push(replay::DirectoryPin {
                    path: relative(&entry.path)?,
                    sha256: entry.sha256.to_string(),
                    files,
                    bytes,
                });
            }
            for path in &inputs.absent {
                binding.absent.push(relative(path)?);
            }
        }
        binding.directories.sort_by(|a, b| a.path.cmp(&b.path));
        binding.directories.dedup();
        binding.absent.sort();
        binding.absent.dedup();
        let stage = self
            .stages
            .get_mut("query.plan")
            .ok_or("classpath query stage missing")?;
        if stage
            .classpath_inputs
            .as_ref()
            .is_some_and(|old| old != &binding)
        {
            return Err("conflicting classpath bindings".into());
        }
        stage.classpath_inputs = Some(binding);
        stage.seal();
        Ok(())
    }
    /// Bind extraction to the physically admitted compiler products. This may
    /// be called before or after the corresponding extract stage is recorded.
    pub fn record_compiler_inputs(
        &mut self,
        side: &str,
        contexts: &Path,
        root: &Path,
        identity: ContentHash,
    ) -> replay::Result<()> {
        let contexts = self.pin(&StageFile {
            role: "compiler_contexts",
            path: contexts,
            kind: None,
        })?;
        let root = fs::canonicalize(root)?;
        let relative = root
            .strip_prefix(&self.root)
            .map_err(|_| "compiler input root is outside the receipt bundle")?;
        let root = if relative.as_os_str().is_empty() {
            ".".to_owned()
        } else {
            relative
                .to_str()
                .ok_or("compiler root is not UTF-8")?
                .replace('\\', "/")
        };
        let binding = CompilerInputBinding {
            contexts,
            root,
            identity: identity.to_string(),
        };
        let id = format!("{side}.extract");
        if self
            .compiler_inputs
            .get(&id)
            .is_some_and(|previous| previous != &binding)
        {
            return Err("conflicting compiler input recordings".into());
        }
        self.compiler_inputs.insert(id.clone(), binding.clone());
        if let Some(stage) = self.stages.get_mut(&id) {
            stage.compiler_inputs = Some(binding);
            stage.seal();
        }
        Ok(())
    }
    fn pin(&mut self, file: &StageFile<'_>) -> replay::Result<FilePin> {
        let path = fs::canonicalize(file.path)?;
        let metadata = fs::metadata(&path)?;
        let modified = metadata.modified().ok();
        let key = (path.clone(), file.kind.map_or(0, |kind| kind as u32));
        if let Some((bytes, time, pin)) = self.pins.get(&key) {
            if *bytes == metadata.len() && modified.is_some() && *time == modified {
                let mut pin = pin.clone();
                pin.role = file.role.into();
                return Ok(pin);
            }
        }
        let pin = FilePin::capture(file.role, &path, &self.root, file.kind)?;
        self.pins
            .insert(key, (metadata.len(), modified, pin.clone()));
        Ok(pin)
    }
    pub fn finish(&mut self) -> replay::Result<()> {
        if self
            .compiler_inputs
            .keys()
            .any(|id| !self.stages.contains_key(id))
        {
            return Err("compiler input binding has no extraction stage".into());
        }
        let mut remaining = self.stages.clone();
        self.receipt.stages.clear();
        while !remaining.is_empty() {
            let id = remaining
                .iter()
                .find(|(_, stage)| {
                    stage.dependencies.iter().all(|dependency| {
                        self.receipt
                            .stages
                            .iter()
                            .any(|prior| &prior.id == dependency)
                    })
                })
                .map(|(id, _)| id.clone())
                .ok_or("replay stage dependency missing or cyclic")?;
            self.receipt.add_stage(remaining.remove(&id).unwrap());
        }
        replay::write_receipt(&self.path, &self.receipt)
    }
    /// A failed command can publish completed preparation stages, but no
    /// evidence for an extraction which never reached its publication point.
    /// With no completed stage, preserve any existing receipt unchanged.
    pub fn finish_failed(&mut self) -> replay::Result<()> {
        if self.stages.is_empty() {
            return Ok(());
        }
        self.compiler_inputs
            .retain(|id, _| self.stages.contains_key(id));
        self.finish()
    }
}

/// A valid saved graph pair bypasses extraction/enrichment/build preparation.
/// Policy and changed-input arguments remain exactly recorded, and all paths
/// are relocated by the receipt before returning native query argv.
pub fn prepared_query_arguments(
    path: &Path,
    receipt: &ReplayReceipt,
    validation: &ReplayValidation,
) -> replay::Result<Option<Vec<String>>> {
    let find = |side: &str, kind: ArtifactKind| {
        validation.completed_outputs.iter().rev().find(|output| {
            output.stage.starts_with(&format!("{side}."))
                && output
                    .artifact
                    .as_ref()
                    .is_some_and(|artifact| artifact.kind == kind as u32)
        })
    };
    let (Some(head_facts), Some(head_graph)) = (
        find("head", ArtifactKind::Facts),
        find("head", ArtifactKind::Graph),
    ) else {
        return Ok(None);
    };
    let mut arguments = receipt.replay_arguments(path)?;
    if !matches!(arguments.first().map(String::as_str), Some("run" | "query")) {
        return Ok(None);
    }
    arguments[0] = "query".into();
    let preparation = [
        "--input",
        "--base-input",
        "--syntax",
        "--base-syntax",
        "--contexts",
        "--base-contexts",
        "--compiler-input-root",
        "--base-compiler-input-root",
        "--external-metadata",
        "--external-metadata-producer",
        "--metadata-binary-map",
        "--base-external-metadata",
        "--base-external-metadata-producer",
        "--base-metadata-binary-map",
        "--binary-map",
        "--base-binary-map",
        "--platform-input",
        "--platform-producer",
        "--base-platform-input",
        "--base-platform-producer",
        "--head-facts",
        "--head-graph",
        "--base-facts",
        "--base-graph",
    ];
    let mut output = Vec::with_capacity(arguments.len() + 8);
    let mut index = 0;
    while index < arguments.len() {
        let flag = arguments[index].split('=').next().unwrap();
        if preparation.contains(&flag) {
            index += if arguments[index].contains('=') { 1 } else { 2 };
            if index > arguments.len() {
                return Err("recorded preparation argument has no value".into());
            }
        } else {
            output.push(arguments[index].clone());
            index += 1;
        }
    }
    output.extend([
        "--head-facts".into(),
        head_facts.path.to_string_lossy().into_owned(),
        "--head-graph".into(),
        head_graph.path.to_string_lossy().into_owned(),
    ]);
    match (
        find("base", ArtifactKind::Facts),
        find("base", ArtifactKind::Graph),
    ) {
        (Some(facts), Some(graph)) => output.extend([
            "--base-facts".into(),
            facts.path.to_string_lossy().into_owned(),
            "--base-graph".into(),
            graph.path.to_string_lossy().into_owned(),
        ]),
        (None, None)
            if !receipt
                .stages
                .iter()
                .any(|stage| stage.id.starts_with("base.")) => {}
        _ => return Ok(None),
    }
    Ok(Some(output))
}

fn absolute_lexical(path: &Path) -> replay::Result<PathBuf> {
    let path = if path.is_absolute() {
        path.to_owned()
    } else {
        std::env::current_dir()?.join(path)
    };
    // Follow existing ancestors once, including nonexisting output file names.
    // Resolve existing symlinks before reducing `..`; lexical reduction first
    // would bind `/a/link/../file` to a different file from the operating system.
    let mut ancestor = path.as_path();
    let mut tail = Vec::new();
    while !ancestor.exists() {
        tail.push(
            ancestor
                .components()
                .next_back()
                .ok_or("replay output path ancestor")?
                .as_os_str()
                .to_owned(),
        );
        ancestor = ancestor.parent().ok_or("replay output path parent")?;
    }
    let mut result = ancestor.canonicalize()?;
    for part in tail.into_iter().rev() {
        if part == ".." {
            if !result.pop() {
                return Err("replay path escapes filesystem root".into());
            }
        } else if part != "." {
            result.push(part);
        }
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use sha2::{Digest, Sha256};
    fn artifact(path: &Path, kind: ArtifactKind, bytes: &[u8]) {
        selector_artifacts::write(
            path,
            kind,
            &[selector_artifacts::Section {
                id: 1,
                count: 1,
                bytes,
            }],
        )
        .unwrap();
    }
    #[test]
    fn admitted_transitive_inputs_rebase_prior_and_pending_records_without_changing_files() {
        let local = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
        let external = tempfile::tempdir().unwrap();
        let input = local.path().join("documents");
        let contexts = local.path().join("contexts");
        let facts = local.path().join("facts.bin");
        let provider = external.path().join("provider.jar");
        let path = local.path().join("receipt.json");
        fs::write(&input, b"documents").unwrap();
        fs::write(&contexts, b"contexts").unwrap();
        fs::write(&provider, b"admitted external provider").unwrap();
        artifact(&facts, ArtifactKind::Facts, b"unchanged facts");
        let producers = BTreeMap::from([("extract".into(), "11".repeat(32))]);
        let raw = vec![
            "extract".into(),
            "--input".into(),
            input.to_str().unwrap().into(),
        ];
        let mut recording = Recording::new(
            raw.clone(),
            path.clone(),
            vec![(2, input.clone())],
            producers.clone(),
        )
        .unwrap();
        let old_root = recording.root.clone();
        assert!(!provider.canonicalize().unwrap().starts_with(&old_root));
        for side in ["head", "base"] {
            recording
                .record_compiler_inputs(side, &contexts, local.path(), ContentHash([7; 32]))
                .unwrap();
        }
        let source = StageFile {
            role: "documents",
            path: &input,
            kind: None,
        };
        let output = StageFile {
            role: "facts",
            path: &facts,
            kind: Some(ArtifactKind::Facts),
        };
        recording
            .record_stage(
                "head.extract",
                &[],
                "extract",
                ContentHash([3; 32]),
                &[source],
                &[output],
            )
            .unwrap();
        let old_fingerprint = recording.stages["head.extract"].fingerprint.clone();
        let old_options = recording.options.clone();
        recording
            .include_transitive_inputs([provider.as_path()])
            .unwrap();
        assert_ne!(recording.root, old_root);
        assert_ne!(recording.options, old_options);
        assert_ne!(
            recording.stages["head.extract"].fingerprint,
            old_fingerprint
        );
        assert_eq!(
            recording.stages["head.extract"].models,
            ContentHash([3; 32]).to_string()
        );
        recording
            .record_stage(
                "base.extract",
                &[],
                "extract",
                ContentHash([3; 32]),
                &[source],
                &[output],
            )
            .unwrap();
        recording
            .record_stage(
                "providers",
                &[],
                "extract",
                ContentHash([4; 32]),
                &[StageFile {
                    role: "provider",
                    path: &provider,
                    kind: None,
                }],
                &[],
            )
            .unwrap();
        recording.finish().unwrap();
        let saved = replay::load_receipt(&path, &replay::ReplayLimits::default()).unwrap();
        assert_eq!(saved.replay_arguments(&path).unwrap(), raw);
        let limits = replay::ReplayLimits {
            verify_compiler_inputs: false,
            ..Default::default()
        };
        assert!(
            replay::validate_receipt(&path, &producers, &limits)
                .unwrap()
                .valid()
        );
        for stage in saved
            .stages
            .iter()
            .filter(|stage| stage.id.ends_with(".extract"))
        {
            let binding = stage.compiler_inputs.as_ref().unwrap();
            assert_eq!(binding.identity, ContentHash([7; 32]).to_string());
            assert_eq!(
                recording.root.join(&binding.root),
                local.path().canonicalize().unwrap()
            );
            assert_eq!(
                recording.root.join(&binding.contexts.path),
                contexts.canonicalize().unwrap()
            );
            assert_eq!(
                recording.root.join(&stage.inputs[0].path),
                input.canonicalize().unwrap()
            );
        }
        fs::write(&provider, b"changed provider").unwrap();
        assert!(
            !replay::validate_receipt(&path, &producers, &limits)
                .unwrap()
                .valid()
        );
        assert_eq!(fs::read(&input).unwrap(), b"documents");
    }
    #[test]
    fn ordinary_pins_stay_confined_and_failed_transitive_admission_is_atomic() {
        let local = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
        let external = tempfile::NamedTempFile::new().unwrap();
        let mut recording = Recording::new(
            vec!["extract".into()],
            local.path().join("receipt.json"),
            vec![],
            BTreeMap::new(),
        )
        .unwrap();
        let root = recording.root.clone();
        let options = recording.options.clone();
        assert!(
            recording
                .pin(&StageFile {
                    role: "unadmitted",
                    path: external.path(),
                    kind: None
                })
                .is_err()
        );
        let absent = external.path().with_extension("absent");
        assert!(
            recording
                .include_transitive_inputs([external.path(), absent.as_path()])
                .is_err()
        );
        assert_eq!(recording.root, root);
        assert_eq!(recording.options, options);
        assert!(recording.pins.is_empty());
    }
    #[test]
    fn records_parallel_stage_order_and_replays_from_completed_artifacts() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let input = root.join("source");
        let facts = root.join("facts.bin");
        let graph = root.join("graph.bin");
        let report = root.join("future-report.json");
        let receipt = root.join("receipt.json");
        fs::write(&input, b"input").unwrap();
        artifact(&facts, ArtifactKind::Facts, b"facts");
        artifact(&graph, ArtifactKind::Graph, b"graph");
        let producers = BTreeMap::from([
            ("extract".into(), "11".repeat(32)),
            ("graph".into(), "22".repeat(32)),
        ]);
        let mut recording = Recording::new(
            vec![
                "run".into(),
                "--input".into(),
                input.to_str().unwrap().into(),
                "--output".into(),
                report.to_str().unwrap().into(),
                "--external-metadata".into(),
                "unused-head-manifest".into(),
                "--external-metadata-producer".into(),
                "33".repeat(32),
                "--metadata-binary-map".into(),
                "unused-head-map".into(),
                "--base-external-metadata".into(),
                "unused-base-manifest".into(),
                "--base-external-metadata-producer".into(),
                "44".repeat(32),
                "--base-metadata-binary-map".into(),
                "unused-base-map".into(),
                "--platform-input".into(),
                "unused-platform".into(),
                "--platform-producer".into(),
                "55".repeat(32),
                "--base-platform-input".into(),
                "unused-base-platform".into(),
                "--base-platform-producer".into(),
                "66".repeat(32),
            ],
            receipt.clone(),
            vec![(2, input.clone()), (4, report)],
            producers.clone(),
        )
        .unwrap();
        let facts_file = StageFile {
            role: "facts",
            path: &facts,
            kind: Some(ArtifactKind::Facts),
        };
        recording
            .record_stage(
                "head.graph",
                &["head.extract"],
                "graph",
                ContentHash([0; 32]),
                &[facts_file],
                &[StageFile {
                    role: "graph",
                    path: &graph,
                    kind: Some(ArtifactKind::Graph),
                }],
            )
            .unwrap();
        recording
            .record_stage(
                "head.extract",
                &[],
                "extract",
                ContentHash([0; 32]),
                &[StageFile {
                    role: "input",
                    path: &input,
                    kind: None,
                }],
                &[facts_file],
            )
            .unwrap();
        recording.finish().unwrap();
        let saved = replay::load_receipt(&receipt, &replay::ReplayLimits::default()).unwrap();
        assert_eq!(saved.stages[0].id, "head.extract");
        let validation =
            replay::validate_receipt(&receipt, &producers, &replay::ReplayLimits::default())
                .unwrap();
        assert!(validation.valid());
        let arguments = prepared_query_arguments(&receipt, &saved, &validation)
            .unwrap()
            .unwrap();
        assert_eq!(arguments[0], "query");
        assert!(!arguments.iter().any(|value| value == "--input"));
        assert!(!arguments.iter().any(|value| value.contains("metadata")));
        assert!(!arguments.iter().any(|value| value.contains("platform")));
        assert!(!arguments.iter().any(|value| value.starts_with("unused-")));
        assert!(arguments.windows(2).any(|pair| pair[0] == "--head-facts"
            && Path::new(&pair[1]) == facts.canonicalize().unwrap()));
        assert!(arguments.windows(2).any(|pair| pair[0] == "--head-graph"
            && Path::new(&pair[1]) == graph.canonicalize().unwrap()));
    }
    #[test]
    fn missing_dependency_or_conflicting_parallel_stage_is_not_published() {
        let directory = tempfile::tempdir().unwrap();
        let input = directory.path().join("source");
        fs::write(&input, b"input").unwrap();
        let path = directory.path().join("receipt.json");
        let mut recording = Recording::new(
            vec!["run".into()],
            path.clone(),
            vec![],
            BTreeMap::from([("graph".into(), "22".repeat(32))]),
        )
        .unwrap();
        recording
            .record_stage(
                "head.graph",
                &["missing"],
                "graph",
                ContentHash([0; 32]),
                &[StageFile {
                    role: "input",
                    path: &input,
                    kind: None,
                }],
                &[],
            )
            .unwrap();
        assert!(recording.finish().is_err());
        assert!(!path.exists());
        fs::write(&input, b"different input length").unwrap();
        assert!(
            recording
                .record_stage(
                    "head.graph",
                    &["missing"],
                    "graph",
                    ContentHash([0; 32]),
                    &[StageFile {
                        role: "input",
                        path: &input,
                        kind: None
                    }],
                    &[]
                )
                .is_err()
        );
    }
    #[test]
    fn failed_command_without_completed_stages_preserves_existing_receipt() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("receipt.json");
        let contexts = directory.path().join("contexts.json");
        fs::write(&contexts, b"captured contexts").unwrap();
        fs::write(&path, b"original receipt").unwrap();
        let mut recording = Recording::new(
            vec!["run".into()],
            path.clone(),
            vec![],
            BTreeMap::from([("extract".into(), "11".repeat(32))]),
        )
        .unwrap();
        recording
            .record_compiler_inputs("head", &contexts, directory.path(), ContentHash([0; 32]))
            .unwrap();
        assert!(
            recording.finish().is_err(),
            "successful publication must require its extraction stage"
        );
        recording.finish_failed().unwrap();
        assert_eq!(fs::read(&path).unwrap(), b"original receipt");
        fs::remove_file(&path).unwrap();
        recording.finish_failed().unwrap();
        assert!(!path.exists(), "no misleading empty replay receipt");
    }
    #[test]
    fn failed_partial_pipeline_records_only_completed_stages_for_native_recovery() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("receipt.json");
        let contexts = directory.path().join("contexts.json");
        let facts = directory.path().join("base-facts.bin");
        fs::write(&contexts, b"captured contexts").unwrap();
        artifact(&facts, ArtifactKind::Facts, b"completed base facts");
        let producers = BTreeMap::from([("extract".into(), "11".repeat(32))]);
        let mut recording =
            Recording::new(vec!["run".into()], path.clone(), vec![], producers.clone()).unwrap();
        recording
            .record_compiler_inputs("head", &contexts, directory.path(), ContentHash([0; 32]))
            .unwrap();
        recording
            .record_stage(
                "base.extract",
                &[],
                "extract",
                ContentHash([0; 32]),
                &[],
                &[StageFile {
                    role: "facts",
                    path: &facts,
                    kind: Some(ArtifactKind::Facts),
                }],
            )
            .unwrap();
        recording.finish_failed().unwrap();
        let saved = replay::load_receipt(&path, &replay::ReplayLimits::default()).unwrap();
        assert_eq!(saved.stages.len(), 1);
        assert_eq!(saved.stages[0].id, "base.extract");
        assert!(saved.stages[0].compiler_inputs.is_none());
        let validation =
            replay::validate_receipt(&path, &producers, &replay::ReplayLimits::default()).unwrap();
        assert!(validation.output("base.extract", "facts").is_some());
        assert!(validation.output("query.solve", "outcome").is_none());
        assert!(
            prepared_query_arguments(&path, &saved, &validation)
                .unwrap()
                .is_none()
        );
        assert_eq!(saved.replay_arguments(&path).unwrap(), vec!["run"]);
    }
    #[test]
    fn compiler_products_are_verified_unless_explicitly_frozen() {
        use replay::{InvalidationReason, ReplayLimits};
        use selector_extract::compiler_inputs::{InventoryLimits, admit};
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let source = root.join("source");
        let product = source.join("target/classes");
        fs::create_dir_all(&product).unwrap();
        let contexts = root.join("contexts.json");
        let hash = format!("{:x}", Sha256::digest(b"[]"));
        let manifest = serde_json::json!({
            "schema_version":"sbt-compiler-context/v1", "revision":"r",
            "source_root":"/captured", "errors":[],
            "contexts":[{"full_classpath":[{
                "path":"/captured/target/classes", "sha256":hash,
                "project_output_origins":[{"context_id":"a"}]
            }]}],
            "input_objects":[{"path":"/captured/target/classes", "kind":"directory",
                "sha256":hash, "files":0, "bytes":0}]
        });
        fs::write(&contexts, serde_json::to_vec(&manifest).unwrap()).unwrap();
        let admitted = admit(&contexts, &source, &InventoryLimits::default()).unwrap();
        assert_eq!(
            admitted.receipt.products[0].status,
            selector_extract::compiler_inputs::InventoryStatus::Verified
        );
        let path = root.join("receipt.json");
        let producers = BTreeMap::from([("extract".into(), "11".repeat(32))]);
        let mut recording = Recording::new(
            vec![
                "run".into(),
                "--compiler-input-root".into(),
                source.to_str().unwrap().into(),
            ],
            path.clone(),
            vec![(2, source.clone())],
            producers.clone(),
        )
        .unwrap();
        recording
            .record_stage(
                "head.extract",
                &[],
                "extract",
                ContentHash([0; 32]),
                &[],
                &[],
            )
            .unwrap();
        recording
            .record_compiler_inputs("head", &contexts, &source, admitted.identity)
            .unwrap();
        recording.finish().unwrap();
        let limits = ReplayLimits::default();
        assert!(
            replay::validate_receipt(&path, &producers, &limits)
                .unwrap()
                .valid()
        );
        fs::write(product.join("Changed.class"), b"new compiler product").unwrap();
        let changed = replay::validate_receipt(&path, &producers, &limits).unwrap();
        assert_eq!(
            changed.stages[0].reason,
            InvalidationReason::CompilerInputsChanged
        );
        let frozen = ReplayLimits {
            verify_compiler_inputs: false,
            ..Default::default()
        };
        let valid = replay::validate_receipt(&path, &producers, &frozen).unwrap();
        assert!(valid.valid());
        assert!(!valid.compiler_inputs_verified);
        fs::remove_dir_all(&product).unwrap();
        assert_eq!(
            replay::validate_receipt(&path, &producers, &limits)
                .unwrap()
                .stages[0]
                .reason,
            InvalidationReason::CompilerInputsMissing
        );
        fs::write(&contexts, b"changed captured contexts").unwrap();
        assert_eq!(
            replay::validate_receipt(&path, &producers, &frozen)
                .unwrap()
                .stages[0]
                .reason,
            InvalidationReason::CompilerInputsChanged
        );
    }
    #[cfg(unix)]
    #[test]
    fn existing_symlink_parent_is_resolved_before_dotdot() {
        use std::os::unix::fs::symlink;
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        fs::create_dir_all(root.join("a")).unwrap();
        fs::create_dir_all(root.join("b/child")).unwrap();
        symlink(root.join("b/child"), root.join("a/link")).unwrap();
        let output = root.join("a/link/../future");
        assert_eq!(
            absolute_lexical(&output).unwrap(),
            root.canonicalize().unwrap().join("b/future")
        );
    }
}
