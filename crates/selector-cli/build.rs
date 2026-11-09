use serde_json::Value;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

fn sources(path: &Path, files: &mut Vec<PathBuf>) {
    if path.is_dir() {
        let mut children: Vec<_> = std::fs::read_dir(path)
            .unwrap()
            .map(|e| e.unwrap().path())
            .collect();
        children.sort();
        for child in children {
            sources(&child, files);
        }
    } else if path.extension().is_some_and(|e| e == "rs") {
        files.push(path.to_owned());
    }
}
fn selected_source(stage: &str, package: &str, file: &Path) -> bool {
    let name = file.file_name().unwrap().to_str().unwrap();
    match (stage, package) {
        ("metadata", "selector-cli") => matches!(
            name,
            "main.rs" | "external_metadata.rs" | "metadata_stage.rs"
        ),
        ("metadata", "selector-models") => {
            name == "lib.rs"
                || name.starts_with("binary")
                || file.components().any(|part| part.as_os_str() == "binary")
        }
        ("metadata", "selector-extract") => matches!(
            name,
            "lib.rs"
                | "external_metadata.rs"
                | "semantic_wire.rs"
                | "signature.rs"
                | "callable.rs"
                | "buffer.rs"
        ),
        ("metadata", package)
            if matches!(
                package,
                "selector-artifacts"
                    | "selector-catalogue"
                    | "selector-graph"
                    | "selector-graph-build"
                    | "selector-domain"
                    | "selector-result"
                    | "selector-transfer"
                    | "selector-solve"
                    | "selector-plan"
                    | "selector-select"
                    | "selector-report"
                    | "selector-native-effects"
                    | "selector-effects"
                    | "selector-compiled-products"
            ) =>
        {
            false
        }
        // Runtime reason validation is consumed by execution and rendering;
        // fact/graph preparation and candidate/query policy do not read it.
        (_, "selector-issue") => matches!(stage, "solve" | "report"),
        // Runtime delta policy consumes prepared metadata; it cannot change
        // manifest admission, graph construction or execution summaries.
        (_, "selector-graph-build") if name == "runtime_delta.rs" => stage == "query",
        // Pinned JVM descriptors are consumed by binary admission. Other
        // stages consume the admitted fact identity, not this fallback table.
        (_, "selector-framework") if name == "native_abi.rs" => stage == "binary",
        ("query", "selector-framework") => false,
        ("query", "selector-graph-build") => name.starts_with("runtime"),
        ("query", "selector-models") => {
            name == "lib.rs"
                || name.starts_with("runtime")
                || name.starts_with("binary")
                || file.components().any(|part| part.as_os_str() == "binary")
        }
        ("binary", "selector-framework") => name == "lib.rs",
        ("extract", "selector-extract") => !matches!(name, "toolchain.rs" | "raw_capture.rs"),
        ("binary", "selector-models" | "selector-graph-build") => {
            name.starts_with("binary") || file.components().any(|part| part.as_os_str() == "binary")
        }
        _ => true,
    }
}

#[cfg(test)]
mod source_filter_tests {
    use super::*;

    #[test]
    fn classpath_issuer_binds_inventory_and_sourcefile_parsers_to_query() {
        for file in ["lib.rs", "binary.rs", "binary/classpath.rs"] {
            assert!(selected_source("query", "selector-models", Path::new(file)));
        }
        assert!(selected_source(
            "query",
            "selector-compiled-products",
            Path::new("lib.rs")
        ));
        assert!(selected_source(
            "query",
            "selector-native-effects",
            Path::new("classpath_absence.rs")
        ));
        for package in [
            "selector-native-effects",
            "selector-effects",
            "selector-compiled-products",
        ] {
            assert!(!selected_source("metadata", package, Path::new("lib.rs")));
        }
        assert!(!selected_source(
            "query",
            "selector-graph-build",
            Path::new("binary_inputs.rs")
        ));
    }

    #[test]
    fn metadata_admission_binds_binary_and_signature_parsers_without_runtime_models() {
        for name in ["binary.rs", "binary/metadata.rs", "lib.rs"] {
            assert!(selected_source(
                "metadata",
                "selector-models",
                Path::new(name)
            ));
        }
        assert!(!selected_source(
            "metadata",
            "selector-models",
            Path::new("runtime_schema.rs")
        ));
        for name in [
            "external_metadata.rs",
            "semantic_wire.rs",
            "signature.rs",
            "callable.rs",
        ] {
            assert!(selected_source(
                "metadata",
                "selector-extract",
                Path::new(name)
            ));
        }
        assert!(!selected_source(
            "metadata",
            "selector-extract",
            Path::new("syntax.rs")
        ));
    }

    #[test]
    fn runtime_delta_is_bound_only_to_query_and_parser_remains_graph_bound() {
        let delta = Path::new("crates/selector-graph-build/src/runtime_delta.rs");
        for stage in [
            "extract", "binary", "graph", "solve", "plan", "query", "report",
        ] {
            assert_eq!(
                selected_source(stage, "selector-graph-build", delta),
                stage == "query",
                "{stage}"
            );
        }
        for source in ["runtime_inputs.rs", "runtime_capture.rs"] {
            let path = Path::new(source);
            assert!(selected_source("graph", "selector-graph-build", path));
            assert!(selected_source("query", "selector-graph-build", path));
        }
        assert!(selected_source(
            "graph",
            "selector-models",
            Path::new("runtime_schema.rs")
        ));
        assert!(selected_source(
            "query",
            "selector-models",
            Path::new("runtime_schema.rs")
        ));
    }

    #[test]
    fn pinned_native_abi_is_bound_only_to_binary_admission() {
        let abi = Path::new("crates/selector-framework/src/native_abi.rs");
        for stage in [
            "extract", "binary", "graph", "solve", "plan", "query", "report",
        ] {
            assert_eq!(
                selected_source(stage, "selector-framework", abi),
                stage == "binary",
                "{stage}"
            );
        }
        for stage in ["extract", "binary", "graph"] {
            assert!(selected_source(
                stage,
                "selector-framework",
                Path::new("lib.rs")
            ));
        }
        assert!(!selected_source(
            "query",
            "selector-framework",
            Path::new("lib.rs")
        ));
    }

    #[test]
    fn runtime_issue_source_is_bound_only_to_solver_and_report() {
        for stage in [
            "extract", "binary", "graph", "solve", "plan", "query", "report",
        ] {
            assert_eq!(
                selected_source(stage, "selector-issue", Path::new("lib.rs")),
                matches!(stage, "solve" | "report"),
                "{stage}"
            );
        }
    }
}
fn dependency_closure<'a>(metadata: &'a Value, root: &str) -> BTreeSet<&'a str> {
    let packages = metadata["packages"].as_array().unwrap();
    let nodes: BTreeMap<_, _> = metadata["resolve"]["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .map(|node| (node["id"].as_str().unwrap(), node))
        .collect();
    let root = packages
        .iter()
        .find(|package| package["name"] == root)
        .unwrap()["id"]
        .as_str()
        .unwrap();
    let mut selected = BTreeSet::new();
    let mut pending = vec![root];
    while let Some(id) = pending.pop() {
        if !selected.insert(id) {
            continue;
        }
        for dependency in nodes[id]["deps"].as_array().unwrap() {
            if dependency["dep_kinds"]
                .as_array()
                .unwrap()
                .iter()
                .any(|kind| kind["kind"].is_null() || kind["kind"] == "build")
            {
                pending.push(dependency["pkg"].as_str().unwrap());
            }
        }
    }
    selected
}
fn field(hash: &mut Sha256, bytes: &[u8]) {
    hash.update((bytes.len() as u64).to_le_bytes());
    hash.update(bytes);
}
fn producer(root: &Path, stage: &str, package: &str, metadata: &Value, lock: &str, rustc: &[u8]) {
    let mut hash = Sha256::new();
    field(&mut hash, b"selector-stage-producer/v2");
    field(&mut hash, include_bytes!("build.rs"));
    field(&mut hash, stage.as_bytes());
    field(&mut hash, rustc);
    if stage == "metadata" {
        for name in ["main.rs", "external_metadata.rs", "metadata_stage.rs"] {
            let path = root.join("crates/selector-cli/src").join(name);
            println!("cargo:rerun-if-changed={}", path.display());
            field(&mut hash, format!("selector-cli/src/{name}").as_bytes());
            field(
                &mut hash,
                &std::fs::read(path).expect("read metadata admission orchestration"),
            );
        }
    }
    if stage == "query" {
        // Selection is persisted separately from execution summaries. Query
        // orchestration and runtime metadata deltas can alter its seed policy
        // without changing any solver implementation or graph snapshot.
        for name in [
            "main.rs",
            "replay.rs",
            "recording.rs",
            "classpath_absence.rs",
        ] {
            let path = root.join("crates/selector-cli/src").join(name);
            println!("cargo:rerun-if-changed={}", path.display());
            field(&mut hash, format!("selector-cli/src/{name}").as_bytes());
            field(
                &mut hash,
                &std::fs::read(path).expect("read query orchestration"),
            );
        }
    }
    if stage == "extract" {
        // Source normalization participates in the fact producer even though
        // its implementation shares compiler binding code with the graph leaf.
        // Hash its exact inputs without pulling unrelated graph/model edits
        // into compiler-fact invalidation.
        let recipe = root.join("crates/selector-graph-build/src/source_recipes.rs");
        println!("cargo:rerun-if-changed={}", recipe.display());
        field(&mut hash, b"source_recipes.rs");
        field(
            &mut hash,
            &std::fs::read(recipe).expect("read source recipes"),
        );
    }
    if stage == "binary" {
        // Binary admission supplies runtime class metadata needed to normalize
        // declared result constraints after enrichment.
        let bounds = root.join("crates/selector-extract/src/result_bounds.rs");
        println!("cargo:rerun-if-changed={}", bounds.display());
        field(&mut hash, b"result_bounds.rs");
        field(
            &mut hash,
            &std::fs::read(bounds).expect("read result bounds"),
        );
    }
    for (name, value) in std::env::vars()
        .filter(|(name, _)| name == "TARGET" || name.starts_with("CARGO_CFG_"))
        .collect::<BTreeMap<_, _>>()
    {
        field(&mut hash, name.as_bytes());
        field(&mut hash, value.as_bytes());
    }
    let mut selected = dependency_closure(metadata, package);
    if stage == "query" {
        // Include the exact locked dependency versions/features used by native
        // runtime diffing. Source filters above keep binary admission, graph
        // construction and framework contracts out of query-only invalidation.
        selected.extend(dependency_closure(metadata, "selector-graph-build"));
        // Conditional classpath proofs are query policy. Bind the verified
        // issuer and its exact dependency closure, independently of preparation.
        selected.extend(dependency_closure(metadata, "selector-native-effects"));
    }
    if stage == "metadata" {
        selected.extend(dependency_closure(metadata, "selector-extract"));
        // The adapter also uses CLI dependencies such as libc's file-open
        // flags. Bind their exact resolved versions/features; source filters
        // keep unrelated algorithms out of this admission producer.
        selected.extend(dependency_closure(metadata, "selector-cli"));
    }
    let nodes: BTreeMap<_, _> = metadata["resolve"]["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .map(|node| (node["id"].as_str().unwrap(), node))
        .collect();
    let mut packages: Vec<_> = metadata["packages"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|package| selected.contains(package["id"].as_str().unwrap()))
        .collect();
    packages.sort_unstable_by_key(|package| {
        (
            package["name"].as_str().unwrap(),
            package["version"].as_str().unwrap(),
            package["source"].as_str(),
        )
    });
    let lock_entries: Vec<_> = lock.split("[[package]]").skip(1).collect();
    for package in packages {
        // Resolve normal/build dependencies with Cargo, then qualify only their
        // locked blocks (including checksums), never the unrelated whole lockfile.
        let name = package["name"].as_str().unwrap();
        let name_line = format!("name = {}", serde_json::to_string(name).unwrap());
        let version_line = format!(
            "version = {}",
            serde_json::to_string(&package["version"]).unwrap()
        );
        let source_line = package["source"]
            .as_str()
            .map(|source| format!("source = {}", serde_json::to_string(source).unwrap()));
        let entries: Vec<_> = lock_entries
            .iter()
            .filter(|entry| {
                let lines: Vec<_> = entry.lines().collect();
                lines.contains(&name_line.as_str())
                    && lines.contains(&version_line.as_str())
                    && match &source_line {
                        Some(source) => lines.contains(&source.as_str()),
                        None => !lines.iter().any(|line| line.starts_with("source = ")),
                    }
            })
            .collect();
        assert_eq!(entries.len(), 1, "exact locked producer dependency {name}");
        field(&mut hash, name.as_bytes());
        field(&mut hash, package["version"].as_str().unwrap().as_bytes());
        field(
            &mut hash,
            package["source"].as_str().unwrap_or("").as_bytes(),
        );
        field(
            &mut hash,
            entries[0]
                .lines()
                .find(|line| line.starts_with("checksum = "))
                .unwrap_or("")
                .as_bytes(),
        );
        // Dependency spelling in Cargo.lock acquires version suffixes when an
        // unrelated package adds another version. Qualify resolved edges instead.
        let mut dependencies = Vec::new();
        for dependency in nodes[package["id"].as_str().unwrap()]["deps"]
            .as_array()
            .unwrap()
        {
            let kinds: Vec<_> = dependency["dep_kinds"]
                .as_array()
                .unwrap()
                .iter()
                .filter(|kind| kind["kind"].is_null() || kind["kind"] == "build")
                .collect();
            if kinds.is_empty() {
                continue;
            }
            let target = metadata["packages"]
                .as_array()
                .unwrap()
                .iter()
                .find(|candidate| candidate["id"] == dependency["pkg"])
                .unwrap();
            dependencies.push(
                serde_json::to_string(&(
                    &dependency["name"],
                    &target["name"],
                    &target["version"],
                    &target["source"],
                    kinds,
                ))
                .unwrap(),
            );
        }
        dependencies.sort_unstable();
        for dependency in dependencies {
            field(&mut hash, dependency.as_bytes());
        }
        for key in ["edition", "rust_version"] {
            field(
                &mut hash,
                serde_json::to_string(&package[key]).unwrap().as_bytes(),
            );
        }
        field(
            &mut hash,
            serde_json::to_string(&nodes[package["id"].as_str().unwrap()]["features"])
                .unwrap()
                .as_bytes(),
        );
        if package["source"].is_null() {
            let manifest = Path::new(package["manifest_path"].as_str().unwrap());
            let directory = manifest.parent().unwrap();
            let mut files = Vec::new();
            sources(&directory.join("src"), &mut files);
            files.retain(|file| selected_source(stage, name, file));
            files.push(manifest.to_owned());
            println!("cargo:rerun-if-changed={}", directory.join("src").display());
            for file in files {
                println!("cargo:rerun-if-changed={}", file.display());
                field(
                    &mut hash,
                    file.strip_prefix(root)
                        .unwrap()
                        .to_string_lossy()
                        .as_bytes(),
                );
                field(
                    &mut hash,
                    &std::fs::read(&file).expect("read producer source"),
                );
            }
        }
    }
    println!(
        "cargo:rustc-env=SELECTOR_{}_PRODUCER={:x}",
        stage.to_uppercase(),
        hash.finalize()
    );
}
fn main() {
    let output = PathBuf::from(std::env::var_os("OUT_DIR").unwrap());
    let profile = output
        .ancestors()
        .nth(3)
        .and_then(Path::file_name)
        .unwrap()
        .to_string_lossy();
    println!("cargo:rustc-env=SELECTOR_BUILD_PROFILE={profile}");
    println!(
        "cargo:rustc-env=SELECTOR_BUILD_OPT_LEVEL={}",
        std::env::var("OPT_LEVEL").unwrap()
    );
    let root = PathBuf::from(std::env::var_os("CARGO_MANIFEST_DIR").unwrap())
        .join("../..")
        .canonicalize()
        .unwrap();
    let metadata = std::process::Command::new(std::env::var_os("CARGO").unwrap())
        .args(["metadata", "--format-version", "1", "--locked", "--offline"])
        .current_dir(&root)
        .output()
        .expect("read locked Cargo metadata");
    assert!(
        metadata.status.success(),
        "{}",
        String::from_utf8_lossy(&metadata.stderr)
    );
    let metadata: Value = serde_json::from_slice(&metadata.stdout).unwrap();
    let lock = std::fs::read_to_string(root.join("Cargo.lock")).unwrap();
    let rustc =
        std::process::Command::new(std::env::var_os("RUSTC").unwrap_or_else(|| "rustc".into()))
            .arg("--version")
            .output()
            .unwrap();
    assert!(rustc.status.success());
    println!(
        "cargo:rustc-env=SELECTOR_BUILD_RUSTC={}",
        String::from_utf8_lossy(&rustc.stdout).trim()
    );
    for (stage, package) in [
        ("extract", "selector-extract"),
        ("metadata", "selector-models"),
        ("binary", "selector-graph-build"),
        ("graph", "selector-graph-build"),
        ("plan", "selector-plan"),
        ("query", "selector-select"),
        ("report", "selector-report"),
        ("solve", "selector-solve"),
    ] {
        producer(&root, stage, package, &metadata, &lock, &rustc.stdout);
    }
    println!(
        "cargo:rerun-if-changed={}",
        root.join("Cargo.toml").display()
    );
    println!(
        "cargo:rerun-if-changed={}",
        root.join("Cargo.lock").display()
    );
    println!("cargo:rerun-if-changed=build.rs");
}
