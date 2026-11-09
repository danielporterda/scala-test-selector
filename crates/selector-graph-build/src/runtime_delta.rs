//! Query-only runtime input comparison and compiler-bound change seeds.
//! Manifest admission and graph construction stay in the parent module; this
//! source participates only in the QUERY producer's implementation identity.
use super::OwnedRuntimeInputs;
use selector_facts::FactSnapshot;
use selector_models::runtime::RuntimeSource;
use selector_types::Error;
use std::collections::{BTreeSet, HashSet};

/// Semantic input differences for a whole-diff query. Manifest identity also
/// binds revision and physical storage, so it is deliberately not a change test.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct RuntimeInputChanges {
    pub changed_paths: Vec<String>,
    /// Overlay text, package settings and inventory assertions have no logical
    /// source path. Their change requires a separate conservative query guard.
    pub authority_changed: bool,
}

/// Compare all admitted logical inputs without inventing changes for identical
/// unsupported metadata. An absent manifest supplies an empty input universe.
/// Source bytes are compared exactly; suite catalogues are admitted name sets.
pub fn runtime_input_changes(
    base: Option<&OwnedRuntimeInputs>,
    head: Option<&OwnedRuntimeInputs>,
) -> RuntimeInputChanges {
    #[derive(PartialEq, Eq)]
    enum Content<'a> {
        Source(&'a str),
        Catalogue(&'a BTreeSet<String>),
    }
    fn logical(inputs: Option<&OwnedRuntimeInputs>) -> Vec<(&str, Content<'_>)> {
        let Some(inputs) = inputs else {
            return Vec::new();
        };
        let mut rows = Vec::with_capacity(inputs.sources.len() + inputs.suite_catalogues.len());
        rows.extend(
            inputs
                .sources
                .iter()
                .map(|(path, text)| (path.as_str(), Content::Source(text))),
        );
        rows.extend(
            inputs
                .suite_catalogues
                .iter()
                .map(|(path, names)| (path.as_str(), Content::Catalogue(names))),
        );
        rows.sort_unstable_by_key(|(path, _)| *path);
        rows
    }
    fn packages(inputs: Option<&OwnedRuntimeInputs>) -> Vec<&str> {
        let mut values: Vec<_> = inputs
            .into_iter()
            .flat_map(|inputs| inputs.packages.iter().map(String::as_str))
            .collect();
        values.sort_unstable();
        values.dedup();
        values
    }
    let before = logical(base);
    let after = logical(head);
    let mut result = RuntimeInputChanges {
        authority_changed: base.and_then(|inputs| inputs.overlay.as_deref())
            != head.and_then(|inputs| inputs.overlay.as_deref())
            || packages(base) != packages(head)
            || base.is_some_and(|inputs| inputs.inventory_complete)
                != head.is_some_and(|inputs| inputs.inventory_complete),
        ..RuntimeInputChanges::default()
    };
    let (mut left, mut right) = (0, 0);
    while left < before.len() || right < after.len() {
        match (before.get(left), after.get(right)) {
            (Some((path, old)), Some((other, new))) if path == other => {
                if old != new {
                    result.changed_paths.push((*path).to_owned());
                }
                left += 1;
                right += 1;
            }
            (Some((path, _)), Some((other, _))) if path < other => {
                result.changed_paths.push((*path).to_owned());
                left += 1;
            }
            (Some(_), Some((path, _))) => {
                result.changed_paths.push((*path).to_owned());
                right += 1;
            }
            (Some((path, _)), None) => {
                result.changed_paths.push((*path).to_owned());
                left += 1;
            }
            (None, Some((path, _))) => {
                result.changed_paths.push((*path).to_owned());
                right += 1;
            }
            (None, None) => break,
        }
    }
    result.changed_paths.dedup();
    result
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum RuntimeSnapshotSide {
    Base,
    Head,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum RuntimeChangeReason {
    MissingCatalogue,
    UnboundSuite,
    MissingSuite,
    UnsupportedMetadata,
    InvalidSchema,
    MissingOperationBinding,
    IncompleteOperationBinding,
}
impl RuntimeChangeReason {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::MissingCatalogue => "missing_catalogue",
            Self::UnboundSuite => "unbound_suite",
            Self::MissingSuite => "missing_suite",
            Self::UnsupportedMetadata => "unsupported_metadata",
            Self::InvalidSchema => "invalid_schema",
            Self::MissingOperationBinding => "missing_operation_binding",
            Self::IncompleteOperationBinding => "incomplete_operation_binding",
        }
    }
}

/// One conservative runtime delta, retaining the requested changed path and
/// the compiler binding which could not be proven. Schema diffs can propagate
/// through references, so `operation_path` is separate from the changed path.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct RuntimeChangeCause {
    pub path: String,
    pub side: Option<RuntimeSnapshotSide>,
    pub reason: RuntimeChangeReason,
    pub detail: String,
    pub suite_name: Option<String>,
    pub schema_path: Option<String>,
    pub operation_path: Option<String>,
    pub verb: Option<String>,
}
impl RuntimeChangeCause {
    fn new(
        path: &str,
        side: Option<RuntimeSnapshotSide>,
        reason: RuntimeChangeReason,
        detail: impl Into<String>,
    ) -> Self {
        Self {
            path: path.to_owned(),
            side,
            reason,
            detail: detail.into(),
            suite_name: None,
            schema_path: None,
            operation_path: None,
            verb: None,
        }
    }
}

/// Runtime metadata deltas resolved through the same compiler-bound operation
/// certificates as graph construction. Files contain shared router/configuration
/// consumers which cannot be reduced to a single operation method.
#[derive(Debug, Default)]
pub struct RuntimeChangeSeeds {
    pub covered_paths: Vec<String>,
    pub base_symbols: Vec<selector_types::SymbolId>,
    pub head_symbols: Vec<selector_types::SymbolId>,
    pub base_guard_files: Vec<selector_types::FileId>,
    pub head_guard_files: Vec<selector_types::FileId>,
    pub unscoped: bool,
    pub unscoped_causes: Vec<RuntimeChangeCause>,
    /// Raw diagnostic rows omitted after the retained-row budget. Omission
    /// never removes the conservative guard, even after duplicate folding.
    pub unscoped_causes_omitted: u64,
}
pub const MAX_RUNTIME_CHANGE_CAUSES: usize = 1024;

struct CauseSink<'a> {
    rows: &'a mut Vec<RuntimeChangeCause>,
    omitted: &'a mut u64,
}
impl CauseSink<'_> {
    fn push(&mut self, make: impl FnOnce() -> RuntimeChangeCause) {
        if self.rows.len() < MAX_RUNTIME_CHANGE_CAUSES {
            self.rows.push(make());
        } else {
            *self.omitted = self.omitted.saturating_add(1);
        }
    }
    fn for_paths(&mut self, paths: &[&str], make: impl Fn(&str) -> RuntimeChangeCause) {
        let kept = paths
            .len()
            .min(MAX_RUNTIME_CHANGE_CAUSES.saturating_sub(self.rows.len()));
        self.rows
            .extend(paths[..kept].iter().map(|path| make(path)));
        *self.omitted = self.omitted.saturating_add((paths.len() - kept) as u64);
    }
}
impl RuntimeChangeSeeds {
    fn normalize(&mut self) {
        self.base_symbols.sort_unstable();
        self.base_symbols.dedup();
        self.head_symbols.sort_unstable();
        self.head_symbols.dedup();
        self.base_guard_files.sort_unstable();
        self.base_guard_files.dedup();
        self.head_guard_files.sort_unstable();
        self.head_guard_files.dedup();
        self.unscoped_causes.sort_unstable();
        self.unscoped_causes.dedup();
        self.unscoped = !self.unscoped_causes.is_empty() || self.unscoped_causes_omitted != 0;
    }
}

pub fn runtime_change_seeds(
    base_facts: &FactSnapshot,
    base_graph: &selector_graph::ProgramGraph,
    base: &OwnedRuntimeInputs,
    head_facts: &FactSnapshot,
    head_graph: &selector_graph::ProgramGraph,
    head: &OwnedRuntimeInputs,
    changed_paths: &[&str],
) -> Result<RuntimeChangeSeeds, Error> {
    use selector_models::runtime_schema::SchemaTree;
    let mut result = RuntimeChangeSeeds::default();
    let contains = |inputs: &OwnedRuntimeInputs, path: &str| {
        inputs.sources.iter().any(|(source, _)| source == path)
            || inputs.suite_catalogues.contains_key(path)
    };
    for &path in changed_paths {
        if contains(base, path) || contains(head, path) {
            result.covered_paths.push(path.to_owned());
        }
    }
    result.covered_paths.sort_unstable();
    result.covered_paths.dedup();
    if result.covered_paths.is_empty() {
        return Ok(result);
    }
    // Bound diagnostic ownership before constructing any per-cause strings.
    // Paths are already sorted; subsequent compiler/schema iteration is stable.
    let mut causes = CauseSink {
        rows: &mut result.unscoped_causes,
        omitted: &mut result.unscoped_causes_omitted,
    };
    let mut catalogue_paths = HashSet::new();
    for path in &result.covered_paths {
        if !base.suite_catalogues.contains_key(path) && !head.suite_catalogues.contains_key(path) {
            continue;
        }
        catalogue_paths.insert(path.as_str());
        let (Some(before), Some(after)) = (
            base.suite_catalogues.get(path),
            head.suite_catalogues.get(path),
        ) else {
            causes.push(|| RuntimeChangeCause::new(
                path,
                Some(if base.suite_catalogues.contains_key(path) {
                    RuntimeSnapshotSide::Head
                } else {
                    RuntimeSnapshotSide::Base
                }),
                RuntimeChangeReason::MissingCatalogue,
                "changed suite catalogue is absent from this snapshot's admitted runtime inputs",
            ));
            continue;
        };
        for (side, facts, names, symbols) in [
            (
                RuntimeSnapshotSide::Base,
                base_facts,
                before.difference(after).collect::<Vec<_>>(),
                &mut result.base_symbols,
            ),
            (
                RuntimeSnapshotSide::Head,
                head_facts,
                after.difference(before).collect::<Vec<_>>(),
                &mut result.head_symbols,
            ),
        ] {
            for name in names {
                let mut found = false;
                for suite in facts
                    .suites
                    .iter()
                    .filter(|suite| facts.text(suite.name) == name)
                {
                    found = true;
                    if suite.symbol.is_none()
                        || suite.file.is_none()
                        || suite.flags & selector_types::EDGE_UNKNOWN != 0
                    {
                        causes.push(|| {
                            let mut cause = RuntimeChangeCause::new(
                                path,
                                Some(side),
                                RuntimeChangeReason::UnboundSuite,
                                "changed suite lacks a verified compiler identity",
                            );
                            cause.suite_name = Some(name.clone());
                            cause
                        });
                    } else {
                        symbols.push(suite.symbol);
                    }
                }
                if !found {
                    causes.push(|| {
                        let mut cause = RuntimeChangeCause::new(
                            path,
                            Some(side),
                            RuntimeChangeReason::MissingSuite,
                            "changed catalogue suite is absent from the extracted suite inventory",
                        );
                        cause.suite_name = Some(name.clone());
                        cause
                    });
                }
            }
        }
    }
    fn yaml(inputs: &OwnedRuntimeInputs) -> Vec<RuntimeSource<'_>> {
        inputs
            .sources
            .iter()
            .filter(|(path, _)| path.ends_with(".yaml") || path.ends_with(".yml"))
            .map(|(path, text)| RuntimeSource {
                path: path.as_str(),
                text: text.as_str(),
            })
            .collect::<Vec<_>>()
    }
    let before_sources = yaml(base);
    let after_sources = yaml(head);
    let changed_yaml: Vec<_> = result
        .covered_paths
        .iter()
        .filter(|path| path.ends_with(".yaml") || path.ends_with(".yml"))
        .map(String::as_str)
        .collect();
    // Generator settings, frontend and non-schema runtime metadata can change
    // arbitrary bindings; no method-scope claim is made for those changes.
    for path in &result.covered_paths {
        if !catalogue_paths.contains(path.as_str())
            && !path.ends_with(".yaml")
            && !path.ends_with(".yml")
        {
            causes.push(|| {
                RuntimeChangeCause::new(
                    path,
                    None,
                    RuntimeChangeReason::UnsupportedMetadata,
                    "changed runtime metadata has no operation-scoped delta model",
                )
            });
        }
    }
    if changed_yaml.is_empty() {
        result.normalize();
        return Ok(result);
    }
    let diff = SchemaTree::new(&before_sources).and_then(|before| {
        let keys: HashSet<_> = before
            .operations()?
            .into_iter()
            .map(|operation| (operation.schema_path, operation.path, operation.verb))
            .collect();
        SchemaTree::new(&after_sources)
            .and_then(|after| before.diff(&after, &changed_yaml).map(|diff| (diff, keys)))
    });
    let (diff, before_keys) = match diff {
        Ok(diff) => diff,
        Err(error) => {
            causes.for_paths(&changed_yaml, |path| {
                RuntimeChangeCause::new(
                    path,
                    None,
                    RuntimeChangeReason::InvalidSchema,
                    format!("runtime schema delta could not be validated: {error}"),
                )
            });
            result.normalize();
            return Ok(result);
        }
    };
    let before = selector_models::runtime::operation_bindings(
        base_facts,
        &base_graph.symbol_nodes,
        &base.borrow(),
    );
    let after = selector_models::runtime::operation_bindings(
        head_facts,
        &head_graph.symbol_nodes,
        &head.borrow(),
    );
    for operation in diff.changed {
        for (side, bindings, symbols, files) in [
            (
                RuntimeSnapshotSide::Base,
                &before,
                &mut result.base_symbols,
                &mut result.base_guard_files,
            ),
            (
                RuntimeSnapshotSide::Head,
                &after,
                &mut result.head_symbols,
                &mut result.head_guard_files,
            ),
        ] {
            // An operation added inside an existing admitted schema has no
            // previous consumer. Its absence is proven by the parsed base tree.
            if side == RuntimeSnapshotSide::Base
                && !before_keys.contains(&(
                    operation.schema_path.clone(),
                    operation.path.clone(),
                    operation.verb.clone(),
                ))
            {
                continue;
            }
            let binding = bindings.iter().find(|binding| {
                binding.schema_path == operation.schema_path
                    && binding.path == operation.path
                    && binding.verb == operation.verb
            });
            let reason = if let Some(binding) = binding {
                symbols.extend_from_slice(&binding.symbols);
                files.extend_from_slice(&binding.guard_files);
                if !binding.scope_complete {
                    Some(RuntimeChangeReason::IncompleteOperationBinding)
                } else {
                    None
                }
            } else {
                Some(RuntimeChangeReason::MissingOperationBinding)
            };
            if let Some(reason) = reason {
                causes.for_paths(&changed_yaml, |path| {
                    let mut cause = RuntimeChangeCause::new(
                        path,
                        Some(side),
                        reason,
                        match reason {
                            RuntimeChangeReason::IncompleteOperationBinding => {
                                "affected schema operation lacks a complete compiler-bound consumer scope"
                            }
                            _ => "affected schema operation has no compiler-bound consumer",
                        },
                    );
                    cause.schema_path = Some(operation.schema_path.clone());
                    cause.operation_path = Some(operation.path.clone());
                    cause.verb = Some(operation.verb.clone());
                    cause
                });
            }
        }
    }
    result.normalize();
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::runtime_inputs::{catalogue_names, load_runtime_manifest};
    use selector_facts::FactBuilder;
    use selector_types::ContentHash;
    use sha2::{Digest, Sha256};
    use std::{
        collections::BTreeMap,
        path::{Path, PathBuf},
    };
    fn suite_facts(revision: &str, names: &[&str]) -> FactSnapshot {
        use selector_facts::{FileRecord, SuiteRecord};
        use selector_types::*;
        let mut builder = FactBuilder::new();
        builder.facts.revision = builder.intern(revision).unwrap();
        for name in names {
            let file = FileId(builder.facts.files.len() as u32);
            let path = builder.intern(&format!("src/{name}.scala")).unwrap();
            let source = builder.intern("class CapturedSuite").unwrap();
            builder.facts.files.push(FileRecord {
                path,
                source,
                revision: StrId::NONE,
                context: StrId::NONE,
                source_hash: ContentHash(Sha256::digest(b"class CapturedSuite").into()),
                flags: SOURCE_VERIFIED,
            });
            let symbol = builder
                .ensure_symbol(&format!("{}#", name.replace('.', "/")), file)
                .unwrap();
            builder.facts.symbols[symbol.index()].kind = 13;
            builder.facts.symbols[symbol.index()].flags = SYMBOL_DEFINED;
            let name = builder.intern(name).unwrap();
            builder.facts.suites.push(SuiteRecord {
                name,
                symbol,
                file,
                flags: 0,
            });
        }
        builder.finish().unwrap()
    }
    fn catalogue_manifest(directory: &Path, facts: &FactSnapshot, names: &[&str]) -> PathBuf {
        let log = names
            .iter()
            .map(|name| format!("{name}\n"))
            .collect::<String>();
        let sha = ContentHash(Sha256::digest(log.as_bytes()).into()).to_string();
        std::fs::write(directory.join("catalogue.log"), &log).unwrap();
        let all: BTreeSet<_> = facts
            .suites
            .iter()
            .map(|suite| facts.text(suite.name))
            .collect();
        let catalogue = serde_json::json!({"schema_version":"compiler-ci-catalogue/v1","complete":true,
            "revision":facts.text(facts.revision),"suite_names":all,"families":[{"catalogue":"test-full-class-names.log","suites":names}],
            "source_receipts":[{"path":"/captured/catalog/test-full-class-names.log","bytes":log.len(),"sha256":sha}]});
        let bytes = serde_json::to_vec(&catalogue).unwrap();
        std::fs::write(directory.join("ci-catalogue.json"), &bytes).unwrap();
        let manifest = serde_json::json!({"version":1,"revision":facts.text(facts.revision),"ci_catalogue":{"file":"ci-catalogue.json","sha256":ContentHash(Sha256::digest(&bytes).into()).to_string()},
            "suite_catalogues":[{"path":"test-full-class-names.log","file":"catalogue.log","sha256":sha}]});
        let path = directory.join("runtime.json");
        std::fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
        path
    }
    #[test]
    fn catalogue_membership_delta_seeds_actual_contextual_suites_without_global_fallback() {
        let base = suite_facts("base", &["example.Existing"]);
        let head = suite_facts("head", &["example.Existing", "example.Added"]);
        let before_dir = tempfile::tempdir().unwrap();
        let after_dir = tempfile::tempdir().unwrap();
        let before = load_runtime_manifest(
            &catalogue_manifest(before_dir.path(), &base, &["example.Existing"]),
            &base,
        )
        .unwrap();
        let after = load_runtime_manifest(
            &catalogue_manifest(
                after_dir.path(),
                &head,
                &["example.Existing", "example.Added"],
            ),
            &head,
        )
        .unwrap();
        let bg = crate::build(&base, &crate::BuildOptions::default()).unwrap();
        let hg = crate::build(&head, &crate::BuildOptions::default()).unwrap();
        let seeds = runtime_change_seeds(
            &base,
            &bg,
            &before,
            &head,
            &hg,
            &after,
            &["test-full-class-names.log"],
        )
        .unwrap();
        assert_eq!(seeds.covered_paths, ["test-full-class-names.log"]);
        assert!(!seeds.unscoped);
        assert!(seeds.unscoped_causes.is_empty());
        assert!(seeds.base_symbols.is_empty());
        assert_eq!(seeds.head_symbols, [head.suites[1].symbol]);
        let reverse = runtime_change_seeds(
            &head,
            &hg,
            &after,
            &base,
            &bg,
            &before,
            &["test-full-class-names.log"],
        )
        .unwrap();
        assert_eq!(reverse.base_symbols, [head.suites[1].symbol]);
        assert!(reverse.head_symbols.is_empty());
        assert!(!reverse.unscoped);
    }
    #[test]
    fn catalogue_proof_rejects_unbound_inputs_missing_receipts_and_different_extracted_names() {
        let directory = tempfile::tempdir().unwrap();
        let facts = suite_facts("revision", &["example.Existing"]);
        let path = catalogue_manifest(directory.path(), &facts, &["example.Existing"]);
        let original: serde_json::Value =
            serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
        let mut manifest = original.clone();
        manifest.as_object_mut().unwrap().remove("ci_catalogue");
        std::fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
        assert!(load_runtime_manifest(&path, &facts).is_err());
        std::fs::write(&path, serde_json::to_vec(&original).unwrap()).unwrap();
        let other = suite_facts("revision", &["example.Other"]);
        assert!(load_runtime_manifest(&path, &other).is_err());
        let mut catalogue: serde_json::Value = serde_json::from_slice(
            &std::fs::read(directory.path().join("ci-catalogue.json")).unwrap(),
        )
        .unwrap();
        catalogue["source_receipts"] = serde_json::json!([]);
        let bytes = serde_json::to_vec(&catalogue).unwrap();
        std::fs::write(directory.path().join("ci-catalogue.json"), &bytes).unwrap();
        let mut manifest = original;
        manifest["ci_catalogue"]["sha256"] =
            serde_json::json!(ContentHash(Sha256::digest(&bytes).into()).to_string());
        std::fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
        assert!(load_runtime_manifest(&path, &facts).is_err());
        assert!(catalogue_names("example.Existing\nexample.Existing\n").is_err());
    }
    #[test]
    fn new_catalogue_suite_without_compiler_identity_remains_explicitly_unscoped() {
        let base = suite_facts("base", &["example.Existing"]);
        let mut head = suite_facts("head", &["example.Existing", "example.Unknown"]);
        head.suites[1].symbol = selector_types::SymbolId::NONE;
        head.suites[1].file = selector_types::FileId::NONE;
        head.suites[1].flags = selector_types::EDGE_UNKNOWN;
        let before_dir = tempfile::tempdir().unwrap();
        let after_dir = tempfile::tempdir().unwrap();
        let before = load_runtime_manifest(
            &catalogue_manifest(before_dir.path(), &base, &["example.Existing"]),
            &base,
        )
        .unwrap();
        let after = load_runtime_manifest(
            &catalogue_manifest(
                after_dir.path(),
                &head,
                &["example.Existing", "example.Unknown"],
            ),
            &head,
        )
        .unwrap();
        let bg = crate::build(&base, &crate::BuildOptions::default()).unwrap();
        let hg = crate::build(&head, &crate::BuildOptions::default()).unwrap();
        let seeds = runtime_change_seeds(
            &base,
            &bg,
            &before,
            &head,
            &hg,
            &after,
            &["test-full-class-names.log"],
        )
        .unwrap();
        assert_eq!(seeds.covered_paths, ["test-full-class-names.log"]);
        assert!(seeds.unscoped);
        assert!(seeds.head_symbols.is_empty());
        assert_eq!(seeds.unscoped_causes.len(), 1);
        let cause = &seeds.unscoped_causes[0];
        assert_eq!(cause.path, "test-full-class-names.log");
        assert_eq!(cause.side, Some(RuntimeSnapshotSide::Head));
        assert_eq!(cause.reason, RuntimeChangeReason::UnboundSuite);
        assert_eq!(cause.suite_name.as_deref(), Some("example.Unknown"));
    }
    #[test]
    fn manifest_requires_bound_revision_and_hashes_every_input() {
        let directory = tempfile::tempdir().unwrap();
        let source = directory.path().join("api.yaml");
        std::fs::write(&source, b"openapi: 3.0.0\n").unwrap();
        let mut builder = FactBuilder::new();
        builder.facts.revision = builder.intern("revision-a").unwrap();
        let facts = builder.finish().unwrap();
        let sha = ContentHash(Sha256::digest(b"openapi: 3.0.0\n").into());
        let manifest = serde_json::json!({"version":1,"revision":"revision-a","sources":[{"path":"api.yaml","file":"api.yaml","sha256":sha.to_string()}],"generator_packages":["example.http.v0"]});
        let path = directory.path().join("runtime.json");
        std::fs::write(&path, manifest.to_string()).unwrap();
        let owned = load_runtime_manifest(&path, &facts).unwrap();
        let borrowed = owned.borrow();
        assert_eq!(borrowed.sources[0].text, "openapi: 3.0.0\n");
        std::fs::write(&source, b"changed").unwrap();
        assert!(load_runtime_manifest(&path, &facts).is_err());
        let mut manifest = manifest;
        manifest["revision"] = serde_json::json!("different");
        std::fs::write(&path, manifest.to_string()).unwrap();
        assert!(load_runtime_manifest(&path, &facts).is_err());
    }
    #[test]
    fn unbound_and_duplicate_logical_paths_are_rejected() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("runtime.json");
        let facts = FactSnapshot::default();
        std::fs::write(&path, r#"{"version":1}"#).unwrap();
        assert!(load_runtime_manifest(&path, &facts).is_err());
        let manifest = serde_json::json!({"version":1,"facts_identity":facts.identity.to_string(),"generator_packages":["bad; package"]});
        std::fs::write(&path, manifest.to_string()).unwrap();
        assert!(load_runtime_manifest(&path, &facts).is_err());
    }
    #[test]
    fn metadata_delta_covers_only_captured_inputs_and_missing_operation_scope_is_explicit() {
        let facts = FactSnapshot::default();
        let graph = crate::build(&facts, &crate::BuildOptions::default()).unwrap();
        let schema = "openapi: 3.0.0\npaths:\n  /value:\n    get:\n      operationId: read\n      responses:\n        '200':\n          $ref: 'model.yaml#/Response'\n";
        let inputs = |description: &str| OwnedRuntimeInputs {
            sources: vec![
                ("api.yaml".into(), schema.into()),
                (
                    "model.yaml".into(),
                    format!("Response:\n  description: {description}\n"),
                ),
            ],
            packages: Vec::new(),
            overlay: None,
            identity: ContentHash::default(),
            inventory_complete: false,
            suite_catalogues: BTreeMap::new(),
        };
        let base = inputs("before");
        let head = inputs("after");
        let delta = runtime_change_seeds(
            &facts,
            &graph,
            &base,
            &facts,
            &graph,
            &head,
            &["model.yaml", "unrelated.scala"],
        )
        .unwrap();
        assert_eq!(delta.covered_paths, vec!["model.yaml"]);
        assert!(
            delta.unscoped,
            "a referenced model delta with no compiler route certificate cannot become empty complete selection"
        );
        assert_eq!(delta.unscoped_causes.len(), 2);
        for cause in &delta.unscoped_causes {
            assert_eq!(cause.path, "model.yaml");
            assert_eq!(
                cause.reason,
                RuntimeChangeReason::IncompleteOperationBinding
            );
            assert_eq!(cause.schema_path.as_deref(), Some("api.yaml"));
            assert_eq!(cause.operation_path.as_deref(), Some("/value"));
            assert_eq!(cause.verb.as_deref(), Some("get"));
        }
        assert_eq!(
            delta
                .unscoped_causes
                .iter()
                .map(|cause| cause.side)
                .collect::<Vec<_>>(),
            [
                Some(RuntimeSnapshotSide::Base),
                Some(RuntimeSnapshotSide::Head)
            ]
        );
        let unrelated = runtime_change_seeds(
            &facts,
            &graph,
            &base,
            &facts,
            &graph,
            &head,
            &["unrelated.scala"],
        )
        .unwrap();
        assert!(unrelated.covered_paths.is_empty());
        assert!(!unrelated.unscoped);
        let unchanged =
            runtime_change_seeds(&facts, &graph, &base, &facts, &graph, &base, &["api.yaml"])
                .unwrap();
        assert!(
            unchanged.unscoped,
            "formatting-only or unbound schema changes stay conservative"
        );
    }
    #[test]
    fn runtime_delta_reports_missing_catalogue_and_unsupported_metadata_separately() {
        let facts = FactSnapshot::default();
        let graph = crate::build(&facts, &crate::BuildOptions::default()).unwrap();
        let inputs = |catalogue: bool| OwnedRuntimeInputs {
            sources: vec![("generator.conf".into(), "settings".into())],
            packages: Vec::new(),
            overlay: None,
            identity: ContentHash::default(),
            inventory_complete: false,
            suite_catalogues: if catalogue {
                [("test.log".into(), BTreeSet::new())].into()
            } else {
                BTreeMap::new()
            },
        };
        let seeds = runtime_change_seeds(
            &facts,
            &graph,
            &inputs(true),
            &facts,
            &graph,
            &inputs(false),
            &["test.log", "generator.conf", "unknown.conf"],
        )
        .unwrap();
        assert!(seeds.unscoped);
        assert_eq!(seeds.covered_paths, ["generator.conf", "test.log"]);
        assert_eq!(seeds.unscoped_causes.len(), 2);
        assert_eq!(seeds.unscoped_causes[0].path, "generator.conf");
        assert_eq!(
            seeds.unscoped_causes[0].reason,
            RuntimeChangeReason::UnsupportedMetadata
        );
        assert_eq!(seeds.unscoped_causes[1].path, "test.log");
        assert_eq!(
            seeds.unscoped_causes[1].reason,
            RuntimeChangeReason::MissingCatalogue
        );
        assert_eq!(
            seeds.unscoped_causes[1].side,
            Some(RuntimeSnapshotSide::Head)
        );
    }
    #[test]
    fn invalid_schema_delta_retains_changed_path_and_parser_diagnostic() {
        let facts = FactSnapshot::default();
        let graph = crate::build(&facts, &crate::BuildOptions::default()).unwrap();
        let inputs = |text: &str| OwnedRuntimeInputs {
            sources: vec![("api.yaml".into(), text.into())],
            packages: Vec::new(),
            overlay: None,
            identity: ContentHash::default(),
            inventory_complete: false,
            suite_catalogues: BTreeMap::new(),
        };
        let seeds = runtime_change_seeds(
            &facts,
            &graph,
            &inputs("openapi: 3.0.0\npaths: {}\n"),
            &facts,
            &graph,
            &inputs("paths: [invalid\n"),
            &["api.yaml"],
        )
        .unwrap();
        assert!(seeds.unscoped);
        assert_eq!(seeds.unscoped_causes.len(), 1);
        let cause = &seeds.unscoped_causes[0];
        assert_eq!(cause.path, "api.yaml");
        assert_eq!(cause.reason, RuntimeChangeReason::InvalidSchema);
        assert!(
            cause
                .detail
                .contains("schema delta could not be validated:")
        );
    }
    #[test]
    fn runtime_cause_budget_preserves_global_guard_and_deterministic_first_rows() {
        let facts = FactSnapshot::default();
        let graph = crate::build(&facts, &crate::BuildOptions::default()).unwrap();
        let inputs = OwnedRuntimeInputs {
            sources: (0..MAX_RUNTIME_CHANGE_CAUSES + 37)
                .map(|index| (format!("settings/{index:04}.conf"), "setting".into()))
                .collect(),
            packages: Vec::new(),
            overlay: None,
            identity: ContentHash::default(),
            inventory_complete: false,
            suite_catalogues: BTreeMap::new(),
        };
        let mut paths: Vec<_> = inputs
            .sources
            .iter()
            .map(|(path, _)| path.as_str())
            .collect();
        let first =
            runtime_change_seeds(&facts, &graph, &inputs, &facts, &graph, &inputs, &paths).unwrap();
        paths.reverse();
        let reversed =
            runtime_change_seeds(&facts, &graph, &inputs, &facts, &graph, &inputs, &paths).unwrap();
        assert!(first.unscoped && reversed.unscoped);
        assert_eq!(first.unscoped_causes.len(), MAX_RUNTIME_CHANGE_CAUSES);
        assert!(first.unscoped_causes.capacity() <= MAX_RUNTIME_CHANGE_CAUSES);
        assert_eq!(first.unscoped_causes_omitted, 37);
        assert_eq!(first.unscoped_causes, reversed.unscoped_causes);
        assert_eq!(
            first.unscoped_causes_omitted,
            reversed.unscoped_causes_omitted
        );
        assert_eq!(first.unscoped_causes[0].path, "settings/0000.conf");
        assert_eq!(
            first.unscoped_causes[MAX_RUNTIME_CHANGE_CAUSES - 1].path,
            "settings/1023.conf"
        );
    }
    #[test]
    fn discarded_runtime_causes_never_construct_diagnostic_strings() {
        let mut rows = Vec::new();
        let mut omitted = 0;
        let mut constructed = 0;
        let mut sink = CauseSink {
            rows: &mut rows,
            omitted: &mut omitted,
        };
        for _ in 0..MAX_RUNTIME_CHANGE_CAUSES + 7 {
            sink.push(|| {
                constructed += 1;
                RuntimeChangeCause::new(
                    "settings.conf",
                    None,
                    RuntimeChangeReason::UnsupportedMetadata,
                    "unmodeled",
                )
            });
        }
        let paths = vec!["model.yaml"; MAX_RUNTIME_CHANGE_CAUSES * 3];
        sink.for_paths(&paths, |_| {
            panic!("discarded bulk diagnostic must stay lazy")
        });
        assert_eq!(constructed, MAX_RUNTIME_CHANGE_CAUSES);
        assert_eq!(rows.len(), MAX_RUNTIME_CHANGE_CAUSES);
        assert_eq!(omitted, 7 + (MAX_RUNTIME_CHANGE_CAUSES * 3) as u64);
    }

    fn diff_inputs(sources: &[(&str, &str)], catalogues: &[(&str, &[&str])]) -> OwnedRuntimeInputs {
        OwnedRuntimeInputs {
            sources: sources
                .iter()
                .map(|&(path, text)| (path.to_owned(), text.to_owned()))
                .collect(),
            packages: Vec::new(),
            overlay: None,
            identity: ContentHash::default(),
            inventory_complete: false,
            suite_catalogues: catalogues
                .iter()
                .map(|&(path, names)| {
                    (
                        path.to_owned(),
                        names.iter().map(|&name| name.to_owned()).collect(),
                    )
                })
                .collect(),
        }
    }

    #[test]
    fn whole_diff_unchanged_unsupported_inputs_do_not_become_changed_paths_or_guards() {
        let base = diff_inputs(
            &[
                ("ui/settings.js", "unsupported syntax"),
                ("native/settings.json", "{opaque:true}"),
                ("api.yaml", "not an admitted schema shape"),
            ],
            &[],
        );
        let mut head = diff_inputs(
            &[
                ("api.yaml", "not an admitted schema shape"),
                ("native/settings.json", "{opaque:true}"),
                ("ui/settings.js", "unsupported syntax"),
            ],
            &[],
        );
        head.identity = ContentHash([7; 32]);
        let changed = runtime_input_changes(Some(&base), Some(&head));
        assert_eq!(changed, RuntimeInputChanges::default());
        let facts = FactSnapshot::default();
        let graph = selector_graph::ProgramGraph::default();
        let seeds =
            runtime_change_seeds(&facts, &graph, &base, &facts, &graph, &head, &[]).unwrap();
        assert!(!seeds.unscoped);
        assert!(seeds.covered_paths.is_empty());
    }

    #[test]
    fn whole_diff_reports_modified_yaml_catalogues_and_native_generation_metadata() {
        let base = diff_inputs(
            &[
                ("api.yaml", "openapi: 3.0.0\npaths: {}\n"),
                ("native/generation.json", "{\"package\":\"before\"}"),
                ("same.conf", "unchanged"),
            ],
            &[("test-full-class-names.log", &["p.Before"])],
        );
        let head = diff_inputs(
            &[
                ("api.yaml", "openapi: 3.1.0\npaths: {}\n"),
                ("native/generation.json", "{\"package\":\"after\"}"),
                ("same.conf", "unchanged"),
            ],
            &[("test-full-class-names.log", &["p.After"])],
        );
        let changed = runtime_input_changes(Some(&base), Some(&head));
        assert_eq!(
            changed.changed_paths,
            [
                "api.yaml",
                "native/generation.json",
                "test-full-class-names.log"
            ]
        );
        assert!(!changed.authority_changed);
    }

    #[test]
    fn whole_diff_includes_added_removed_and_changed_input_kinds_in_sorted_order() {
        let base = diff_inputs(
            &[("z-removed.conf", "old"), ("same-name.log", "p.Suite\n")],
            &[],
        );
        let head = diff_inputs(
            &[("a-added.yaml", "new")],
            &[("same-name.log", &["p.Suite"])],
        );
        assert_eq!(
            runtime_input_changes(Some(&base), Some(&head)).changed_paths,
            ["a-added.yaml", "same-name.log", "z-removed.conf"]
        );
        assert_eq!(
            runtime_input_changes(Some(&base), None).changed_paths,
            ["same-name.log", "z-removed.conf"]
        );
        assert_eq!(
            runtime_input_changes(None, Some(&head)).changed_paths,
            ["a-added.yaml", "same-name.log"]
        );
        assert_eq!(
            runtime_input_changes(None, None),
            RuntimeInputChanges::default()
        );
    }

    #[test]
    fn whole_diff_compares_admitted_catalogue_and_package_sets_not_publication_order() {
        let mut base = diff_inputs(&[], &[("test-full-class-names.log", &["p.A", "p.B"])]);
        let mut head = diff_inputs(&[], &[("test-full-class-names.log", &["p.B", "p.A"])]);
        base.packages = vec!["p.a".into(), "p.b".into()];
        head.packages = vec!["p.b".into(), "p.a".into(), "p.a".into()];
        head.identity = ContentHash([8; 32]);
        assert_eq!(
            runtime_input_changes(Some(&base), Some(&head)),
            RuntimeInputChanges::default()
        );
    }

    #[test]
    fn whole_diff_changed_overlay_or_manifest_authority_needs_a_guard_without_fake_paths() {
        for case in 0..4 {
            let base = diff_inputs(&[], &[]);
            let mut head = diff_inputs(&[], &[]);
            match case {
                0 => head.overlay = Some("{\"edges\":[]}".into()),
                1 => head.packages.push("changed.package".into()),
                2 => head.inventory_complete = true,
                _ => {
                    head.overlay = Some("one".into());
                    let mut base = base;
                    base.overlay = Some("other".into());
                    let changed = runtime_input_changes(Some(&base), Some(&head));
                    assert!(changed.authority_changed);
                    assert!(changed.changed_paths.is_empty());
                    continue;
                }
            }
            let changed = runtime_input_changes(Some(&base), Some(&head));
            assert!(changed.authority_changed, "case {case}");
            assert!(changed.changed_paths.is_empty());
            assert!(runtime_input_changes(Some(&head), None).authority_changed);
        }
        let mut base = diff_inputs(&[], &[]);
        let mut head = diff_inputs(&[], &[]);
        base.overlay = Some("same admitted overlay".into());
        head.overlay = base.overlay.clone();
        head.identity = ContentHash([9; 32]);
        assert_eq!(
            runtime_input_changes(Some(&base), Some(&head)),
            RuntimeInputChanges::default()
        );
    }
}
