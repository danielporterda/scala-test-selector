//! Inspect Cargo's resolved package declarations, never implementation text.
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::process::Command;

fn metadata() -> Value {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap();
    let output = Command::new(env!("CARGO"))
        .args([
            "metadata",
            "--no-deps",
            "--format-version",
            "1",
            "--offline",
        ])
        .current_dir(root)
        .output()
        .expect("run cargo metadata");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).expect("Cargo metadata JSON")
}

fn dependencies() -> BTreeMap<String, BTreeSet<String>> {
    let metadata = metadata();
    metadata["packages"]
        .as_array()
        .unwrap()
        .iter()
        .map(|package| {
            let name = package["name"].as_str().unwrap().to_owned();
            let deps = package["dependencies"]
                .as_array()
                .unwrap()
                .iter()
                .filter(|dependency| dependency["kind"].is_null() || dependency["kind"] == "build")
                .filter_map(|dependency| dependency["name"].as_str())
                .filter(|name| name.starts_with("selector-"))
                .map(str::to_owned)
                .collect();
            (name, deps)
        })
        .collect()
}

#[test]
fn runtime_record_leaves_have_no_algorithm_or_external_dependency() {
    let metadata = metadata();
    for (name, expected) in [
        ("selector-issue", vec!["selector-types"]),
        ("selector-effects", vec![]),
    ] {
        let leaf = metadata["packages"]
            .as_array()
            .unwrap()
            .iter()
            .find(|package| package["name"] == name)
            .unwrap();
        let dependencies: Vec<_> = leaf["dependencies"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|dependency| dependency["kind"].is_null() || dependency["kind"] == "build")
            .map(|dependency| dependency["name"].as_str().unwrap())
            .collect();
        assert_eq!(
            dependencies, expected,
            "{name} stopped being a thin record leaf"
        );
    }
}

fn descendants(graph: &BTreeMap<String, BTreeSet<String>>, edited: &str) -> BTreeSet<String> {
    let mut affected = BTreeSet::from([edited.to_owned()]);
    loop {
        let old = affected.len();
        for (name, deps) in graph {
            if name != "selector-acceptance" && deps.iter().any(|dep| affected.contains(dep)) {
                affected.insert(name.clone());
            }
        }
        if affected.len() == old {
            return affected;
        }
    }
}

#[test]
fn narrow_leaf_edits_have_only_their_declared_dependents() {
    let graph = dependencies();
    for (edited, expected) in [
        ("report", vec!["report", "cli"]),
        ("select", vec!["select", "cli"]),
        ("extract", vec!["extract", "cli"]),
        ("graph-build", vec!["graph-build", "cli"]),
        ("class-diff", vec!["class-diff"]),
        (
            "models",
            vec![
                "models",
                "jvm-resolve",
                "runtime-platform",
                "native-effects",
                "graph-build",
                "class-diff",
                "cli",
            ],
        ),
        ("solve", vec!["solve", "cli"]),
        ("transfer", vec!["transfer", "solve", "cli"]),
        (
            "issue",
            vec![
                "issue", "result", "transfer", "solve", "select", "report", "cli",
            ],
        ),
        ("catalogue", vec!["catalogue", "cli"]),
        ("plan", vec!["plan", "select", "cli"]),
        (
            "jvm-resolve",
            vec!["jvm-resolve", "graph-build", "native-effects", "cli"],
        ),
        (
            "runtime-platform",
            vec!["runtime-platform", "graph-build", "native-effects", "cli"],
        ),
        (
            "compiled-products",
            vec!["compiled-products", "effect-world", "native-effects", "cli"],
        ),
        (
            "effects",
            vec![
                "effects",
                "effects-codec",
                "effect-plan",
                "source-effects",
                "native-effects",
                "cli",
            ],
        ),
        ("effects-codec", vec!["effects-codec"]),
        ("effect-plan", vec!["effect-plan"]),
        ("effect-world", vec!["effect-world"]),
        ("source-effects", vec!["source-effects"]),
        // The opt-in classpath issuer is reached by the CLI. It does not put
        // native producers behind the strict planner, selector or solver.
        ("native-effects", vec!["native-effects", "cli"]),
        (
            "framework",
            vec![
                "framework",
                "extract",
                "models",
                "jvm-resolve",
                "runtime-platform",
                "native-effects",
                "graph-build",
                "class-diff",
                "cli",
            ],
        ),
    ] {
        let expected = expected
            .into_iter()
            .map(|name| format!("selector-{name}"))
            .collect::<BTreeSet<_>>();
        assert_eq!(
            descendants(&graph, &format!("selector-{edited}")),
            expected,
            "{edited} crossed an intended compile-time boundary"
        );
    }
}

#[test]
fn schemas_and_readers_cannot_depend_on_algorithms_or_acceptance() {
    let graph = dependencies();
    for (name, allowed) in [
        ("types", vec![]),
        ("effects", vec![]),
        ("compiled-products", vec![]),
        ("effects-codec", vec!["artifacts", "effects"]),
        ("jvm-resolve", vec!["types", "models"]),
        ("runtime-platform", vec!["types", "models"]),
        ("issue", vec!["types"]),
        ("framework", vec!["types"]),
        ("artifacts", vec!["types"]),
        ("catalogue", vec!["types", "artifacts"]),
        ("facts", vec!["types", "artifacts"]),
        ("graph", vec!["types", "artifacts"]),
        ("domain", vec!["types"]),
        ("result", vec!["types", "issue"]),
        ("plan", vec!["types", "facts", "graph"]),
        ("class-diff", vec!["types", "models"]),
    ] {
        let allowed = allowed
            .into_iter()
            .map(|name| format!("selector-{name}"))
            .collect::<BTreeSet<_>>();
        let name = format!("selector-{name}");
        assert!(
            graph[&name].is_subset(&allowed),
            "{name} gained dependencies {:?}",
            graph[&name]
        );
    }
    for (name, deps) in &graph {
        assert!(
            !deps.contains("selector-acceptance"),
            "production dependency {name} -> acceptance"
        );
        assert!(!deps.contains(name), "self dependency in {name}");
    }
    // Cargo itself rejects graph cycles. These assertions protect the narrower DAG
    // promised for concurrent compilation, rather than repeating Cargo's cycle check.
}

#[test]
fn capsule_producers_do_not_link_selection_or_execution_kernels() {
    let graph = dependencies();
    for (name, allowed) in [
        ("effect-plan", vec!["effects"]),
        (
            "effect-world",
            vec!["compiled-products", "facts", "graph", "types"],
        ),
        ("source-effects", vec!["effects", "facts", "graph", "types"]),
        (
            "native-effects",
            vec![
                "compiled-products",
                "effects",
                "facts",
                "jvm-resolve",
                "models",
                "runtime-platform",
                "types",
            ],
        ),
    ] {
        let allowed = allowed
            .into_iter()
            .map(|name| format!("selector-{name}"))
            .collect::<BTreeSet<_>>();
        let name = format!("selector-{name}");
        assert!(
            graph[&name].is_subset(&allowed),
            "{name} crossed a producer/kernel boundary: {:?}",
            graph[&name]
        );
    }
}
