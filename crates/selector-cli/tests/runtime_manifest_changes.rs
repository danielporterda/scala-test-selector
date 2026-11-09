//! CLI wiring tests, using tiny admitted fact snapshots. Unknown runtime joins
//! are intentionally conservative; these are not HTTP model precision oracles.
use selector_facts::{BodyRecord, FactBuilder, FactSnapshot, FileRecord, SuiteRecord};
use selector_types::*;
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn digest(bytes: &[u8]) -> ContentHash {
    ContentHash(Sha256::digest(bytes).into())
}

struct Snapshot {
    facts: PathBuf,
    graph: PathBuf,
    manifest: PathBuf,
    identity: ContentHash,
}

fn facts(directory: &Path, revision: &str, extra_external: bool) -> (FactSnapshot, PathBuf) {
    let mut b = FactBuilder::new();
    b.facts.revision = b.intern(revision).unwrap();
    let source = "class Alpha\nclass Beta\n";
    let path = b.intern("Suites.scala").unwrap();
    let text = b.intern(source).unwrap();
    let context = b.intern("fixture/test").unwrap();
    b.facts.files.push(FileRecord {
        path,
        source: text,
        revision: b.facts.revision,
        context,
        source_hash: digest(source.as_bytes()),
        flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
    });
    for (name, display, span) in [
        ("fixture/Alpha#", "Alpha", Span { start: 0, end: 12 }),
        ("fixture/Beta#", "Beta", Span { start: 12, end: 23 }),
    ] {
        let symbol = b.ensure_symbol(name, FileId(0)).unwrap();
        let record = &mut b.facts.symbols[symbol.index()];
        record.file = FileId(0);
        record.flags = SYMBOL_DEFINED;
        record.span = span;
        b.facts.bodies.push(BodyRecord {
            symbol,
            file: FileId(0),
            span,
            name_span: span,
            operations: IdRange::default(),
            parameters: IdRange::default(),
            body_hash: digest(&source.as_bytes()[span.start as usize..span.end as usize]),
            flags: BODY_INITIALIZER,
        });
        let name = b.intern(display).unwrap();
        b.facts.suites.push(SuiteRecord {
            name,
            symbol,
            file: FileId(0),
            flags: 0,
        });
    }
    // Models/binary enrichment can add external compiler declarations without
    // changing the captured source revision. The final artifact ID must bind it.
    if extra_external {
        b.ensure_symbol("dependency/Enriched#", FileId::NONE)
            .unwrap();
    }
    let mut facts = b.finish().unwrap();
    let path = directory.join("facts.bin");
    facts.identity = selector_facts::codec::write(&path, &facts).unwrap();
    (facts, path)
}
fn manifest(
    directory: &Path,
    facts: &FactSnapshot,
    label: &str,
    description: &str,
    binding: ContentHash,
) -> PathBuf {
    let schema = format!(
        "openapi: 3.0.0\ninfo:\n  title: Fixture\n  version: '1'\npaths:\n  /value:\n    get:\n      operationId: read\n      responses:\n        '200':\n          description: {description}\n"
    );
    let source = directory.join(format!("{label}.yaml"));
    std::fs::write(&source, &schema).unwrap();
    let path = directory.join(format!("{label}.json"));
    let value = serde_json::json!({"version":1,"revision":facts.text(facts.revision),"facts_identity":binding.to_string(),
        "sources":[{"path":"api.yaml","file":source.file_name().unwrap().to_str().unwrap(),"sha256":digest(schema.as_bytes()).to_string()}],
        "generator_packages":["fixture.http"],"compiler_inventory_complete":false});
    std::fs::write(&path, serde_json::to_vec(&value).unwrap()).unwrap();
    path
}
fn snapshot(root: &Path, revision: &str, description: &str, extra: bool) -> Snapshot {
    let directory = root.join(revision);
    std::fs::create_dir_all(&directory).unwrap();
    let (facts, file) = facts(&directory, revision, extra);
    let manifest = manifest(&directory, &facts, "runtime", description, facts.identity);
    let input =
        selector_graph_build::runtime_inputs::load_runtime_manifest(&manifest, &facts).unwrap();
    let mut graph = selector_graph_build::build_with_runtime(
        &facts,
        &selector_graph_build::BuildOptions {
            workers: 1,
            include_models: true,
        },
        &input.borrow(),
    )
    .unwrap();
    assert_eq!(graph.runtime_identity, input.identity);
    let path = directory.join("graph.bin");
    graph.identity = selector_graph::codec::write(&path, &graph).unwrap();
    Snapshot {
        facts: file,
        graph: path,
        manifest,
        identity: facts.identity,
    }
}
fn query(
    base: &Snapshot,
    head: &Snapshot,
    base_manifest: Option<&Path>,
    head_manifest: Option<&Path>,
) -> Output {
    query_scope(
        base,
        head,
        base_manifest,
        head_manifest,
        &["--changed", "api.yaml"],
    )
}
fn query_scope(
    base: &Snapshot,
    head: &Snapshot,
    base_manifest: Option<&Path>,
    head_manifest: Option<&Path>,
    scope: &[&str],
) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_selector"));
    command
        .arg("query")
        .arg("--base-facts")
        .arg(&base.facts)
        .arg("--base-graph")
        .arg(&base.graph)
        .arg("--head-facts")
        .arg(&head.facts)
        .arg("--head-graph")
        .arg(&head.graph)
        .args(scope)
        .args(["--workers", "2", "--full-report"]);
    if let Some(path) = base_manifest {
        command.arg("--base-runtime-input").arg(path);
    }
    if let Some(path) = head_manifest {
        command.arg("--runtime-input").arg(path);
    }
    command.output().unwrap()
}

#[test]
fn runtime_only_schema_change_stays_conservative_and_missing_manifests_never_omit_suites() {
    let root = tempfile::tempdir().unwrap();
    let base = snapshot(root.path(), "base", "before", false);
    let head = snapshot(root.path(), "head", "after", false);
    let output = query(&base, &head, Some(&base.manifest), Some(&head.manifest));
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let json: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(json["change_scope"]["mode"], "requested_paths");
    assert_eq!(
        json["change_scope"]["effective_requested_source_paths"],
        serde_json::json!([])
    );
    assert_eq!(json["completion"], "conservative");
    assert_eq!(json["suites"].as_array().unwrap().len(), 2);
    assert!(
        json["suites"]
            .as_array()
            .unwrap()
            .iter()
            .all(|suite| suite["guarded"] == true)
    );
    assert!(
        json["head"]["obligations"]
            .as_array()
            .unwrap()
            .iter()
            .any(|o| o["kind"] == "unsupported_model")
    );
    let output = query(&base, &head, None, None);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let json: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(json["suites"].as_array().unwrap().len(), 2);
    assert_eq!(json["completion"], "conservative");
}

#[test]
fn whole_diff_includes_runtime_changes_and_guards_unavailable_runtime_inputs() {
    let root = tempfile::tempdir().unwrap();
    let base = snapshot(root.path(), "base", "before", false);
    let head = snapshot(root.path(), "head", "after", false);
    for (before, after) in [
        (Some(base.manifest.as_path()), Some(head.manifest.as_path())),
        (None, None),
        (Some(base.manifest.as_path()), None),
    ] {
        let output = query_scope(&base, &head, before, after, &["--whole-diff"]);
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let json: Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(json["change_scope"]["mode"], "snapshot_delta");
        assert_eq!(json["completion"], "conservative");
        assert_eq!(json["suites"].as_array().unwrap().len(), 2);
        assert!(
            json["suites"]
                .as_array()
                .unwrap()
                .iter()
                .all(|suite| suite["guarded"] == true)
        );
    }
}

#[test]
fn query_rejects_runtime_manifest_from_another_graph_or_the_other_revision() {
    let root = tempfile::tempdir().unwrap();
    let base = snapshot(root.path(), "base", "before", false);
    let head = snapshot(root.path(), "head", "after", false);
    let hf = selector_facts::codec::read(&head.facts).unwrap();
    let other = manifest(
        head.manifest.parent().unwrap(),
        &hf,
        "other",
        "different schema",
        head.identity,
    );
    let output = query(&base, &head, Some(&base.manifest), Some(&other));
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("does not match graph runtime identity")
    );
    let output = query(&base, &head, Some(&head.manifest), Some(&head.manifest));
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("runtime manifest revision"));
}

#[test]
fn runtime_manifest_must_bind_the_final_enriched_fact_identity() {
    let root = tempfile::tempdir().unwrap();
    let base = snapshot(root.path(), "base", "before", false);
    let head = snapshot(root.path(), "head", "after", true);
    let raw_dir = root.path().join("pre-enrichment");
    std::fs::create_dir(&raw_dir).unwrap();
    let (raw, _) = facts(&raw_dir, "head", false);
    assert_ne!(raw.identity, head.identity);
    let hf = selector_facts::codec::read(&head.facts).unwrap();
    let stale = manifest(
        head.manifest.parent().unwrap(),
        &hf,
        "pre-enrichment-runtime",
        "after",
        raw.identity,
    );
    let output = query(&base, &head, Some(&base.manifest), Some(&stale));
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("runtime manifest facts identity"));
    let valid = query(&base, &head, Some(&base.manifest), Some(&head.manifest));
    assert!(
        valid.status.success(),
        "{}",
        String::from_utf8_lossy(&valid.stderr)
    );
}
