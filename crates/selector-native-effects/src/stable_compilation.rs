//! Paired functional compilation under an explicit recorded-toolchain premise.
//! Only the target owner's own outputs may differ. Every dependency output is
//! an exact byte boundary; this does not reconstruct upstream generator inputs
//! or claim historical JDK image provenance from its recorded labels.
use crate::classpath_absence::{Error, PhysicalInputs};
use crate::provider::{InputPin, VerifiedProvider};
use selector_facts::FactSnapshot;
use selector_models::binary::{self, ClasspathEntry, EntryKind};
use selector_types::*;
use serde::Deserialize;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::io::Read;
use std::path::{Path, PathBuf};

pub const VERSION: &str = "paired-ordinary-compilation/2";
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StableCompilation {
    pub file: FileId,
    pub owner_context: StrId,
    pub source_sha256: ContentHash,
    pub inputs_identity: ContentHash,
    pub paired_identity: ContentHash,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Denial {
    MissingMetadata,
    SourceAuthority,
    SourceChanged,
    AmbiguousSource,
    RequestedDependency,
    InputBinding,
    InputUnavailable,
    UnsupportedOptions,
    InputsChanged,
}
#[derive(Debug)]
pub struct Denied {
    pub path: String,
    pub owner: String,
    pub reason: Denial,
}
pub struct Side<'a, 'p> {
    pub facts: &'a FactSnapshot,
    pub provider: &'a VerifiedProvider<'p>,
    pub candidates: &'a [FileId],
}
#[derive(Default)]
pub struct Issued {
    base: Vec<StableCompilation>,
    head: Vec<StableCompilation>,
    denied: Vec<Denied>,
    inputs: PhysicalInputs,
    identity: ContentHash,
}
impl Issued {
    pub fn base(&self) -> &[StableCompilation] {
        &self.base
    }
    pub fn head(&self) -> &[StableCompilation] {
        &self.head
    }
    pub fn denials(&self) -> &[Denied] {
        &self.denied
    }
    pub fn inputs(&self) -> &PhysicalInputs {
        &self.inputs
    }
    pub fn identity(&self) -> ContentHash {
        self.identity
    }
    pub fn revalidate(&self) -> Result<(), Error> {
        self.inputs.revalidate()
    }
}

#[derive(Deserialize)]
struct Capture {
    schema_version: String,
    source_root: PathBuf,
    sbt_version: Option<String>,
    java_runtime: Option<Runtime>,
    source_to_contexts: HashMap<String, Vec<String>>,
    contexts: Vec<Context>,
    input_objects: Vec<Object>,
}
#[derive(Deserialize)]
struct Runtime {
    #[serde(default)]
    java_home: String,
    #[serde(default)]
    java_version: String,
    #[serde(default)]
    java_vendor: String,
    #[serde(default)]
    os_arch: String,
}
#[derive(Deserialize)]
struct Context {
    context_id: String,
    configuration: String,
    base_directory: Option<PathBuf>,
    class_directory: Option<PathBuf>,
    products: Vec<PathBuf>,
    exported_products: Vec<Product>,
    source_records: Vec<Source>,
    source_files: Option<Vec<PathBuf>>,
    resource_files: Option<Vec<PathBuf>>,
    scala_version: Option<String>,
    scala_organization: Option<String>,
    scala_instance_version: Option<String>,
    scala_instance_jars: Option<Vec<PathBuf>>,
    scala_instance_inputs: Option<Vec<PathBuf>>,
    scalac_plugin_inputs: Option<Vec<PathBuf>>,
    scalac_options: Option<Vec<String>>,
    javac_options: Option<Vec<String>>,
    java_home: Option<PathBuf>,
    java_options: Option<Vec<String>>,
    fork: Option<bool>,
    full_classpath: Vec<Cp>,
    dependency_classpath: Vec<Cp>,
}
#[derive(Deserialize)]
struct Product {
    path: PathBuf,
    sha256: String,
}
#[derive(Deserialize)]
struct Source {
    path: PathBuf,
    repo_relative_path: String,
    input_object: Option<PathBuf>,
    sha256: String,
}
#[derive(Deserialize)]
struct Cp {
    index: usize,
    path: PathBuf,
    input_object: Option<PathBuf>,
    sha256: String,
    #[serde(default)]
    project_output_origins: Vec<Origin>,
}
#[derive(Deserialize)]
struct Origin {
    context_id: String,
}
#[derive(Deserialize)]
struct Object {
    path: PathBuf,
    kind: String,
    sha256: String,
    bytes: Option<u64>,
    files: Option<u64>,
}
fn norm(c: &Capture, path: &Path) -> String {
    path.strip_prefix(&c.source_root).map_or_else(
        |_| path.to_string_lossy().into_owned(),
        |tail| format!("$SOURCE_ROOT/{}", tail.display()),
    )
}
fn text(d: &mut Sha256, s: &str) {
    d.update((s.len() as u64).to_le_bytes());
    d.update(s.as_bytes());
}
fn sha(s: &str) -> Result<ContentHash, Denial> {
    ContentHash::from_hex(s).map_err(|_| Denial::InputBinding)
}
fn physical_pin(
    provider: &VerifiedProvider<'_>,
    o: &Object,
    inputs: &mut PhysicalInputs,
) -> Result<(), Denial> {
    if o.kind != "file" {
        return Err(Denial::InputBinding);
    }
    let path = provider
        .captured_path(&o.path)
        .map_err(|_| Denial::InputBinding)?;
    let mut prefix = PathBuf::new();
    for component in path.components() {
        prefix.push(component.as_os_str());
        if std::fs::symlink_metadata(&prefix)
            .map_err(|_| Denial::InputUnavailable)?
            .file_type()
            .is_symlink()
        {
            return Err(Denial::InputBinding);
        }
    }
    let pin = InputPin {
        path,
        bytes: o.bytes.ok_or(Denial::MissingMetadata)?,
        sha256: sha(&o.sha256)?.0,
    };
    let mut f = std::fs::File::open(&pin.path).map_err(|_| Denial::InputUnavailable)?;
    let meta = f.metadata().map_err(|_| Denial::InputUnavailable)?;
    if !meta.is_file() || meta.len() != pin.bytes {
        return Err(Denial::InputBinding);
    }
    let mut d = Sha256::new();
    let mut buf = [0u8; 65536];
    let mut count = 0u64;
    loop {
        let n = f.read(&mut buf).map_err(|_| Denial::InputUnavailable)?;
        if n == 0 {
            break;
        }
        count = count.checked_add(n as u64).ok_or(Denial::InputBinding)?;
        if count > pin.bytes {
            return Err(Denial::InputBinding);
        }
        d.update(&buf[..n]);
    }
    let got: [u8; 32] = d.finalize().into();
    if count != pin.bytes || got != pin.sha256 {
        return Err(Denial::InputBinding);
    }
    inputs.files.push(pin);
    Ok(())
}
fn entry(
    c: &Capture,
    provider: &VerifiedProvider<'_>,
    o: &Object,
    inputs: &mut PhysicalInputs,
) -> Result<(), Denial> {
    match o.kind.as_str() {
        "file" => physical_pin(provider, o, inputs),
        "directory" => {
            let e = ClasspathEntry {
                path: provider
                    .captured_path(&o.path)
                    .map_err(|_| Denial::InputBinding)?,
                sha256: sha(&o.sha256)?,
                kind: EntryKind::Directory {
                    files: o.files.ok_or(Denial::MissingMetadata)?,
                    bytes: o.bytes.ok_or(Denial::MissingMetadata)?,
                },
            };
            let admitted = binary::AdmittedEntry::admit(e.clone(), binary::Limits::default(), None)
                .map_err(|_| Denial::InputUnavailable)?;
            if admitted.error().is_some() {
                return Err(Denial::InputBinding);
            }
            inputs.directories.push(e);
            Ok(())
        }
        "absent_empty_project_output" => {
            let path = provider
                .captured_path(&o.path)
                .map_err(|_| Denial::InputBinding)?;
            if path.exists() || std::fs::symlink_metadata(&path).is_ok() {
                return Err(Denial::InputBinding);
            }
            let _ = c;
            inputs.absent.push(path);
            Ok(())
        }
        _ => Err(Denial::InputUnavailable),
    }
}
// Every manifest edge is part of the compiler-input identity. An unrecorded
// existing target is never interpreted as empty; a missing sibling is pinned.
fn manifest_targets(
    path: &Path,
    digest: ContentHash,
    feature: Option<u16>,
) -> Result<Vec<PathBuf>, Denial> {
    let denied = |error: binary::BinaryError| {
        eprintln!(
            "{}",
            serde_json::json!({
                "stage":"stable_compilation_input_denied", "phase":"manifest_archive",
                "path":path, "kind":format!("{:?}", error.kind), "java_feature":feature,
            })
        );
        Denial::InputBinding
    };
    let mut loader = binary::CapturedClasspath::new(
        vec![ClasspathEntry {
            path: path.to_owned(),
            sha256: digest,
            kind: EntryKind::Jar,
        }],
        binary::Limits::default(),
    )
    .map_err(&denied)?
    .with_java_feature(feature)
    .map_err(&denied)?;
    loader
        .manifest_class_path(0)
        .map_err(denied)?
        .into_iter()
        .map(|token| {
            let relative = Path::new(&token);
            if token.contains([':', '%', '#', '?', '\\'])
                || token.is_empty()
                || !relative
                    .components()
                    .all(|c| matches!(c, std::path::Component::Normal(_)))
            {
                return Err(Denial::InputBinding);
            }
            Ok(path.parent().ok_or(Denial::InputBinding)?.join(relative))
        })
        .collect()
}
fn verify_input<'a>(
    capture: &Capture,
    provider: &VerifiedProvider<'_>,
    first: &'a Object,
    objects: &HashMap<&'a Path, &'a Object>,
    requested_outputs: &[(&Path, &str)],
    verified: &mut HashSet<&'a Path>,
    inputs: &mut PhysicalInputs,
    digest: &mut Sha256,
) -> Result<(), Denial> {
    let mut pending = vec![first];
    let mut edges = 0usize;
    while let Some(o) = pending.pop() {
        if !verified.insert(o.path.as_path()) {
            continue;
        }
        if verified.len() > 65_535 {
            return Err(Denial::MissingMetadata);
        }
        entry(capture, provider, o, inputs)?;
        if o.kind != "file" {
            continue;
        }
        let physical = provider
            .captured_path(&o.path)
            .map_err(|_| Denial::InputBinding)?;
        for target in manifest_targets(&physical, sha(&o.sha256)?, provider.java_feature())? {
            edges += 1;
            if edges > 65_535 {
                return Err(Denial::MissingMetadata);
            }
            // Convert the verified physical sibling back to the original
            // captured path; relocation preserves this exact relative edge.
            let tail = target
                .strip_prefix(physical.parent().ok_or(Denial::InputBinding)?)
                .map_err(|_| Denial::InputBinding)?;
            let raw = o.path.parent().ok_or(Denial::InputBinding)?.join(tail);
            text(digest, "manifest-class-path");
            text(digest, &norm(capture, &raw));
            if let Some(child) = objects.get(raw.as_path()).copied() {
                if requested_outputs
                    .iter()
                    .any(|(p, h)| *p == child.path || *h == child.sha256)
                {
                    return Err(Denial::RequestedDependency);
                }
                digest.update([1]);
                digest.update(sha(&child.sha256)?.0);
                pending.push(child);
            } else {
                crate::classpath_absence::require_absent(&target)
                    .map_err(|_| Denial::InputBinding)?;
                digest.update([0]);
                inputs.absent.push(target);
            }
        }
    }
    Ok(())
}
fn unsupported_option(option: &str) -> bool {
    option.starts_with('@')
        || option.starts_with("-J@")
        || [
            "-classpath",
            "--class-path",
            "-cp",
            "-bootclasspath",
            "-Xbootclasspath",
            "-sourcepath",
            "--source-path",
            "-processorpath",
            "--processor-path",
            "-processor",
            "--processor-module-path",
            "--system",
            "--module-path",
            "--upgrade-module-path",
            "--module-source-path",
            "--patch-module",
            "-usejavacp",
            "-Ymacro-classpath",
            "-Xpluginsdir",
            "-Ybackend-plugin",
            "-extdirs",
            "-endorseddirs",
            "-P:wartremover:cp:",
        ]
        .iter()
        .any(|p| {
            option == *p
                || option
                    .strip_prefix(p)
                    .is_some_and(|tail| p.ends_with(':') || tail.starts_with([':', '=']))
        })
        || option == "-Xplugin"
}
fn own(c: &Context, row: &Cp) -> bool {
    c.products.contains(&row.path)
        && c.exported_products
            .iter()
            .filter(|p| p.path == row.path && p.sha256 == row.sha256)
            .count()
            == 1
        && !row.project_output_origins.is_empty()
        && row
            .project_output_origins
            .iter()
            .all(|o| o.context_id == c.context_id)
}
struct Checked {
    digest: ContentHash,
    sources: usize,
    dependencies: usize,
}

fn requested_owner_union<'a>(
    captures: &[(&'a Capture, &VerifiedProvider<'_>)],
    requested: &[String],
    inputs: &mut PhysicalInputs,
) -> Result<HashSet<&'a str>, Denial> {
    let wanted: HashSet<_> = requested.iter().map(String::as_str).collect();
    let mut owners = HashSet::new();
    let mut found = HashSet::new();
    for (capture, provider) in captures {
        let mut actual = HashMap::<&str, HashSet<&str>>::new();
        for context in &capture.contexts {
            for source in &context.source_records {
                let path = source.repo_relative_path.as_str();
                if wanted.contains(path) {
                    actual.entry(path).or_default().insert(&context.context_id);
                }
            }
        }
        for path in &wanted {
            match capture.source_to_contexts.get(*path) {
                Some(declared) => {
                    let unique: HashSet<_> = declared.iter().map(String::as_str).collect();
                    if unique.is_empty()
                        || unique.len() != declared.len()
                        || actual.get(path) != Some(&unique)
                    {
                        return Err(Denial::SourceAuthority);
                    }
                    found.insert(*path);
                    owners.extend(unique);
                }
                None => {
                    let relative = Path::new(path);
                    if actual.contains_key(path)
                        || relative.as_os_str().is_empty()
                        || !relative
                            .components()
                            .all(|part| matches!(part, std::path::Component::Normal(_)))
                    {
                        return Err(Denial::SourceAuthority);
                    }
                    let physical = provider
                        .captured_path(&capture.source_root.join(relative))
                        .map_err(|_| Denial::InputBinding)?;
                    crate::classpath_absence::require_absent(&physical)
                        .map_err(|_| Denial::SourceAuthority)?;
                    inputs.absent.push(physical);
                }
            }
        }
    }
    if found != wanted {
        return Err(Denial::MissingMetadata);
    }
    Ok(owners)
}

fn check(
    capture: &Capture,
    provider: &VerifiedProvider<'_>,
    root: &str,
    requested: &[String],
    requested_owners: &HashSet<&str>,
    inputs: &mut PhysicalInputs,
) -> Result<Checked, Denial> {
    let contexts: HashMap<_, _> = capture
        .contexts
        .iter()
        .map(|c| (c.context_id.as_str(), c))
        .collect();
    let objects: HashMap<_, _> = capture
        .input_objects
        .iter()
        .map(|o| (o.path.as_path(), o))
        .collect();
    if contexts.len() != capture.contexts.len() || objects.len() != capture.input_objects.len() {
        return Err(Denial::InputBinding);
    }
    let root = contexts.get(root).copied().ok_or(Denial::MissingMetadata)?;
    if requested_owners.contains(root.context_id.as_str()) {
        return Err(Denial::RequestedDependency);
    }
    let mut requested_outputs = Vec::new();
    for owner in requested_owners {
        let c = contexts.get(owner).ok_or(Denial::MissingMetadata)?;
        for p in &c.exported_products {
            requested_outputs.push((p.path.as_path(), p.sha256.as_str()));
        }
    }
    let source_files = root.source_files.as_ref().ok_or(Denial::MissingMetadata)?;
    let resources = root
        .resource_files
        .as_ref()
        .ok_or(Denial::MissingMetadata)?;
    let scala = root
        .scala_instance_inputs
        .as_ref()
        .ok_or(Denial::MissingMetadata)?;
    let jars = root
        .scala_instance_jars
        .as_ref()
        .ok_or(Denial::MissingMetadata)?;
    let plugins = root
        .scalac_plugin_inputs
        .as_ref()
        .ok_or(Denial::MissingMetadata)?;
    let scalac = root
        .scalac_options
        .as_ref()
        .ok_or(Denial::MissingMetadata)?;
    let javac = root.javac_options.as_ref().ok_or(Denial::MissingMetadata)?;
    if scala.is_empty()
        || scala != jars
        || root.java_home.is_some()
        || root.java_options.as_ref().is_none_or(|o| !o.is_empty())
        || root.fork != Some(false)
    {
        return Err(Denial::MissingMetadata);
    }
    let runtime = capture
        .java_runtime
        .as_ref()
        .ok_or(Denial::MissingMetadata)?;
    let mut d = Sha256::new();
    text(&mut d, VERSION);
    text(
        &mut d,
        capture
            .sbt_version
            .as_deref()
            .ok_or(Denial::MissingMetadata)?,
    );
    for s in [
        &runtime.java_home,
        &runtime.java_version,
        &runtime.java_vendor,
        &runtime.os_arch,
    ] {
        if s.is_empty() {
            return Err(Denial::MissingMetadata);
        }
        text(&mut d, s);
    }
    for s in [
        &root.scala_version,
        &root.scala_organization,
        &root.scala_instance_version,
    ] {
        text(
            &mut d,
            s.as_deref()
                .filter(|s| !s.is_empty())
                .ok_or(Denial::MissingMetadata)?,
        );
    }
    d.update([root.fork.ok_or(Denial::MissingMetadata)? as u8]);
    text(&mut d, &root.configuration);
    text(
        &mut d,
        &norm(
            capture,
            root.base_directory
                .as_deref()
                .ok_or(Denial::MissingMetadata)?,
        ),
    );
    text(
        &mut d,
        &norm(
            capture,
            root.class_directory
                .as_deref()
                .ok_or(Denial::MissingMetadata)?,
        ),
    );
    let mut roster: Vec<_> = source_files.iter().map(PathBuf::as_path).collect();
    roster.sort_unstable();
    let mut records: Vec<_> = root
        .source_records
        .iter()
        .map(|s| s.path.as_path())
        .collect();
    records.sort_unstable();
    if roster.is_empty() || roster != records || roster.windows(2).any(|p| p[0] == p[1]) {
        return Err(Denial::MissingMetadata);
    }
    for p in source_files {
        let s = root
            .source_records
            .iter()
            .find(|s| s.path == *p)
            .ok_or(Denial::MissingMetadata)?;
        if requested.contains(&s.repo_relative_path) {
            return Err(Denial::RequestedDependency);
        }
        let o = objects
            .get(s.input_object.as_deref().unwrap_or(p))
            .copied()
            .ok_or(Denial::MissingMetadata)?;
        if o.path != *p || o.sha256 != s.sha256 {
            return Err(Denial::InputBinding);
        }
        physical_pin(provider, o, inputs)?;
        text(&mut d, &s.repo_relative_path);
        d.update(sha(&s.sha256)?.0);
    }
    let mut verified = HashSet::new();
    for (kind, paths) in [
        ("resources", resources),
        ("scala-instance", scala),
        ("plugins", plugins),
    ] {
        text(&mut d, kind);
        d.update((paths.len() as u64).to_le_bytes());
        for p in paths {
            let o = objects
                .get(p.as_path())
                .copied()
                .ok_or(Denial::MissingMetadata)?;
            if kind == "resources" {
                physical_pin(provider, o, inputs)?;
            } else {
                // Declared compiler/plugin inputs are archives regardless of
                // their filename suffix; a renamed ZIP cannot bypass checks.
                verify_input(
                    capture,
                    provider,
                    o,
                    &objects,
                    &requested_outputs,
                    &mut verified,
                    inputs,
                    &mut d,
                )?;
            }
            text(&mut d, &norm(capture, p));
            d.update(sha(&o.sha256)?.0);
        }
    }
    let mut declared_plugins = BTreeSet::new();
    for (kind, options) in [("scalac", scalac), ("javac", javac)] {
        text(&mut d, kind);
        d.update((options.len() as u64).to_le_bytes());
        for option in options {
            if unsupported_option(option) {
                return Err(Denial::UnsupportedOptions);
            }
            if let Some(value) = option.strip_prefix("-Xplugin:") {
                for p in value.split(':') {
                    let p = PathBuf::from(p);
                    declared_plugins.insert(if p.is_absolute() {
                        p
                    } else {
                        capture.source_root.join(p)
                    });
                }
            }
            text(
                &mut d,
                &option.replace(
                    capture.source_root.to_string_lossy().as_ref(),
                    "$SOURCE_ROOT",
                ),
            );
        }
    }
    if declared_plugins != plugins.iter().cloned().collect() {
        return Err(Denial::InputBinding);
    }
    let mut expected_products = root.products.clone();
    expected_products.sort_unstable();
    let mut actual: Vec<_> = root
        .exported_products
        .iter()
        .map(|p| p.path.clone())
        .collect();
    actual.sort_unstable();
    if actual.is_empty() || expected_products != actual || actual.windows(2).any(|p| p[0] == p[1]) {
        return Err(Denial::InputBinding);
    }
    let mut pending = vec![root.context_id.as_str()];
    let mut seen = HashSet::new();
    let mut skipped = 0usize;
    while let Some(id) = pending.pop() {
        if !seen.insert(id) {
            continue;
        }
        if seen.len() > 1024 {
            return Err(Denial::MissingMetadata);
        }
        if requested_owners.contains(id) {
            return Err(Denial::RequestedDependency);
        }
        let ctx = contexts.get(id).copied().ok_or(Denial::MissingMetadata)?;
        if ctx
            .source_records
            .iter()
            .any(|s| requested.contains(&s.repo_relative_path))
        {
            return Err(Denial::RequestedDependency);
        }
        text(&mut d, id);
        for (kind, rows) in [(0, &ctx.full_classpath), (1, &ctx.dependency_classpath)] {
            d.update([kind]);
            d.update((rows.len() as u64).to_le_bytes());
            for (ordinal, row) in rows.iter().enumerate() {
                if row.index != ordinal {
                    return Err(Denial::InputBinding);
                }
                if requested_outputs
                    .iter()
                    .any(|(p, h)| *p == row.path || *h == row.sha256)
                {
                    return Err(Denial::RequestedDependency);
                }
                let o = objects
                    .get(row.input_object.as_deref().unwrap_or(&row.path))
                    .copied()
                    .ok_or(Denial::MissingMetadata)?;
                if o.path != row.path || o.sha256 != row.sha256 {
                    return Err(Denial::InputBinding);
                }
                verify_input(
                    capture,
                    provider,
                    o,
                    &objects,
                    &requested_outputs,
                    &mut verified,
                    inputs,
                    &mut d,
                )?;
                text(&mut d, &norm(capture, &row.path));
                let skip = id == root.context_id && kind == 0 && own(root, row);
                if skip {
                    skipped += 1;
                    d.update([1]);
                } else {
                    d.update([0]);
                    d.update(sha(&row.sha256)?.0);
                }
                d.update((row.project_output_origins.len() as u64).to_le_bytes());
                for origin in &row.project_output_origins {
                    let producer = contexts
                        .get(origin.context_id.as_str())
                        .copied()
                        .ok_or(Denial::MissingMetadata)?;
                    if !producer.products.contains(&row.path)
                        || producer
                            .exported_products
                            .iter()
                            .filter(|p| p.path == row.path && p.sha256 == row.sha256)
                            .count()
                            != 1
                    {
                        return Err(Denial::InputBinding);
                    }
                    text(&mut d, &origin.context_id);
                    pending.push(origin.context_id.as_str());
                }
            }
        }
    }
    if skipped != root.exported_products.len() {
        return Err(Denial::InputBinding);
    }
    Ok(Checked {
        digest: ContentHash(d.finalize().into()),
        sources: source_files.len(),
        dependencies: root.dependency_classpath.len(),
    })
}

pub fn issue(
    base: Side<'_, '_>,
    head: Side<'_, '_>,
    requested: &[String],
    contract: SelectionContract,
) -> Result<Issued, Error> {
    if contract != SelectionContract::owning_test_classpath_with_compilation() {
        return Err(Error::Invalid("ordinary compilation contract"));
    }
    let mut out = Issued::default();
    let rows = |side: &Side<'_, '_>| -> Result<BTreeMap<(String, String), FileId>, Error> {
        let mut rows = BTreeMap::new();
        for &id in side.candidates {
            let f = side
                .facts
                .files
                .get(id.index())
                .ok_or(Error::Invalid("compilation candidate file"))?;
            let path = side.facts.path(id);
            if requested.iter().any(|p| p == path) {
                continue;
            }
            let key = (path.to_owned(), side.facts.text(f.context).to_owned());
            if rows.insert(key, id).is_some() {
                return Err(Error::Invalid("duplicate compilation candidate"));
            }
        }
        Ok(rows)
    };
    let br = rows(&base)?;
    let hr = rows(&head)?;
    let mut candidates = Vec::new();
    for (key, &bf) in &br {
        let Some(&hf) = hr.get(key) else {
            out.denied.push(Denied {
                path: key.0.clone(),
                owner: key.1.clone(),
                reason: Denial::SourceChanged,
            });
            continue;
        };
        let b = base.facts.files[bf.index()];
        let h = head.facts.files[hf.index()];
        let flags = SOURCE_VERIFIED | SYNTAX_VERIFIED;
        if b.flags & (flags | FILE_BINARY_SOURCE) != flags
            || h.flags & (flags | FILE_BINARY_SOURCE) != flags
            || b.source_hash != h.source_hash
            || b.source_hash == ContentHash::default()
        {
            out.denied.push(Denied {
                path: key.0.clone(),
                owner: key.1.clone(),
                reason: Denial::SourceChanged,
            });
            continue;
        }
        candidates.push((key.clone(), bf, hf));
    }
    if candidates.is_empty() {
        return Ok(out);
    }
    let bc: Capture = serde_json::from_slice(&base.provider.capture_document()?)?;
    let hc: Capture = serde_json::from_slice(&head.provider.capture_document()?)?;
    if bc.schema_version != "sbt-compiler-context/v1" || hc.schema_version != bc.schema_version {
        return Err(Error::Invalid("compilation capture schema"));
    }
    // The absent side cannot silently lose the requested owner as a compiler
    // dependency. Compare against the union even on the missing-source side.
    let requested_owners = requested_owner_union(
        &[(&bc, base.provider), (&hc, head.provider)],
        requested,
        &mut out.inputs,
    );
    let mut cache = BTreeMap::<String, Result<ContentHash, Denial>>::new();
    for (key, bf, hf) in candidates {
        let bound = |capture: &Capture, side: &Side<'_, '_>, file: FileId| {
            let rows: Vec<_> = capture
                .contexts
                .iter()
                .filter(|c| c.context_id == key.1)
                .flat_map(|c| &c.source_records)
                .filter(|s| s.repo_relative_path == key.0)
                .collect();
            rows.len() == 1
                && sha(&rows[0].sha256).ok() == Some(side.facts.files[file.index()].source_hash)
                && capture
                    .source_to_contexts
                    .get(&key.0)
                    .is_some_and(|owners| owners.iter().any(|o| o == &key.1))
        };
        if !bound(&bc, &base, bf) || !bound(&hc, &head, hf) {
            out.denied.push(Denied {
                path: key.0,
                owner: key.1,
                reason: Denial::SourceAuthority,
            });
            continue;
        }
        if !cache.contains_key(&key.1) {
            let checked = (|| {
                let owners = requested_owners.as_ref().map_err(|reason| *reason)?;
                let b = check(
                    &bc,
                    base.provider,
                    &key.1,
                    requested,
                    owners,
                    &mut out.inputs,
                )?;
                let h = check(
                    &hc,
                    head.provider,
                    &key.1,
                    requested,
                    owners,
                    &mut out.inputs,
                )?;
                eprintln!(
                    "{}",
                    serde_json::json!({"stage":"stable_compilation_inputs","owner":key.1,"base_sources":b.sources,"head_sources":h.sources,"base_dependencies":b.dependencies,"head_dependencies":h.dependencies})
                );
                if b.digest != h.digest {
                    return Err(Denial::InputsChanged);
                }
                Ok(b.digest)
            })();
            cache.insert(key.1.clone(), checked);
        }
        match cache[&key.1] {
            Err(reason) => out.denied.push(Denied {
                path: key.0,
                owner: key.1,
                reason,
            }),
            Ok(inputs_identity) => {
                let b = base.facts.files[bf.index()];
                let h = head.facts.files[hf.index()];
                let mut d = Sha256::new();
                text(&mut d, VERSION);
                d.update(producer_sha256().0);
                d.update(contract.bits().to_le_bytes());
                d.update(base.facts.identity.0);
                d.update(head.facts.identity.0);
                d.update(base.provider.identity());
                d.update(head.provider.identity());
                d.update((requested.len() as u64).to_le_bytes());
                for path in requested {
                    text(&mut d, path);
                }
                text(&mut d, &key.0);
                text(&mut d, &key.1);
                d.update(b.source_hash.0);
                d.update(inputs_identity.0);
                for side in [&out.inputs.files] {
                    for p in side {
                        d.update(p.sha256);
                    }
                }
                let paired_identity = ContentHash(d.finalize().into());
                out.base.push(StableCompilation {
                    file: bf,
                    owner_context: b.context,
                    source_sha256: b.source_hash,
                    inputs_identity,
                    paired_identity,
                });
                out.head.push(StableCompilation {
                    file: hf,
                    owner_context: h.context,
                    source_sha256: h.source_hash,
                    inputs_identity,
                    paired_identity,
                });
            }
        }
    }
    out.base.sort_unstable_by_key(|r| r.file);
    out.head.sort_unstable_by_key(|r| r.file);
    out.inputs.files.extend(
        base.provider
            .input_files()
            .iter()
            .chain(head.provider.input_files())
            .cloned(),
    );
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
    let mut d = Sha256::new();
    text(&mut d, VERSION);
    d.update(producer_sha256().0);
    for r in &out.base {
        d.update(r.paired_identity.0);
    }
    out.identity = ContentHash(d.finalize().into());
    eprintln!(
        "{}",
        serde_json::json!({"stage":"stable_compilation","base_accepted":out.base.len(),"head_accepted":out.head.len(),"denied":out.denied.len(),"identity":out.identity.to_string(),"denials":out.denied.iter().take(16).map(|r|serde_json::json!({"path":r.path,"owner":r.owner,"reason":format!("{:?}",r.reason)})).collect::<Vec<_>>()})
    );
    Ok(out)
}
pub fn producer_sha256() -> ContentHash {
    let mut d = Sha256::new();
    d.update(VERSION);
    d.update(include_bytes!("stable_compilation.rs"));
    d.update(crate::classpath_absence::producer_sha256().0);
    ContentHash(d.finalize().into())
}

#[cfg(test)]
#[path = "stable_compilation_tests.rs"]
mod tests;
