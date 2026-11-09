//! Process-level opt-in policy controls over a normalized capture protocol.
//! The class/provider bytes are genuine frozen fixtures; source/compiler rows
//! are explicitly normalized and do not claim an original CI discovery capture.
#[allow(dead_code)]
#[path = "../../selector-native-effects/src/classpath_absence_fixture.rs"]
mod fixture;
use fixture::{Fixture, Mode};
use selector_facts::{BodyRecord, OperationRecord};
use selector_types::*;
use serde_json::Value;
use std::{
    path::{Path, PathBuf},
    process::{Command, Output},
};

fn prepare(root: &Path, mode: Mode, required: bool) -> (Fixture, PathBuf, PathBuf) {
    use sha2::{Digest, Sha256};
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures");
    std::fs::create_dir_all(root.join("base")).unwrap();
    std::fs::create_dir_all(root.join("head")).unwrap();
    let mut base = fixture::make(&root.join("base"), &fixtures, mode);
    let mut head = fixture::make(&root.join("head"), &fixtures, mode);
    // Explicit normalized paired source mutation: update actual bytes, captured
    // source/input-object pins, and the normalized body identity together. The
    // frozen JVM product bytes remain genuine; this is not a compiler claim.
    let source_path = head.root.join("changed/Fixture.java");
    let mut source = std::fs::read(&source_path).unwrap();
    source.extend(b"// normalized head source revision\n");
    std::fs::write(&source_path, &source).unwrap();
    let source_hash = ContentHash(Sha256::digest(&source).into());
    let text = StrId(head.facts.strings.entries.len() as u32);
    head.facts.strings.entries.push(selector_facts::TextRange {
        start: head.facts.strings.bytes.len() as u64,
        len: source.len() as u32,
    });
    head.facts.strings.bytes.extend(&source);
    head.facts.files[head.changed.index()].source = text;
    head.facts.files[head.changed.index()].source_hash = source_hash;
    let mut contexts: Value =
        serde_json::from_slice(&std::fs::read(&head.contexts).unwrap()).unwrap();
    contexts["contexts"][0]["source_records"][0]["sha256"] =
        serde_json::json!(source_hash.to_string());
    for object in contexts["input_objects"].as_array_mut().unwrap() {
        if object["path"].as_str() == source_path.to_str() {
            object["sha256"] = serde_json::json!(source_hash.to_string());
            object["bytes"] = serde_json::json!(source.len());
        }
    }
    std::fs::write(&head.contexts, serde_json::to_vec(&contexts).unwrap()).unwrap();
    let mut request: Value =
        serde_json::from_slice(&std::fs::read(&head.request).unwrap()).unwrap();
    let base_request: Value =
        serde_json::from_slice(&std::fs::read(&base.request).unwrap()).unwrap();
    request["base"] = base_request["base"].clone();
    request["base_catalogue"] = base_request["base_catalogue"].clone();
    request["head"]["contexts"] = fixture::pin(&head.contexts);
    std::fs::write(&head.request, serde_json::to_vec(&request).unwrap()).unwrap();
    let prepare_side = |f: &mut Fixture, facts: &Path, graph_path: &Path| {
        for file in &mut f.facts.files {
            file.flags |= SYNTAX_VERIFIED;
        }
        let suite = f.facts.suites[f.suite.index()].symbol;
        let changed = f
            .facts
            .symbols
            .iter()
            .position(|s| s.file == f.changed && s.flags & SYMBOL_DEFINED != 0)
            .map(|i| SymbolId(i as u32))
            .unwrap();
        for symbol in [changed, suite] {
            let file = f.facts.symbols[symbol.index()].file;
            let body = BodyId(f.facts.bodies.len() as u32);
            let start = f.facts.operations.len() as u32;
            if symbol == suite {
                if required {
                    f.facts.operations.push(OperationRecord {
                        body,
                        opcode: Opcode::Initialize,
                        target: changed,
                        dest: ValueId::NONE,
                        a: ValueId::NONE,
                        b: ValueId::NONE,
                        arguments: IdRange::default(),
                        span: Span::default(),
                        flags: 0,
                    });
                }
                // The ordinary kernel is deliberately open. Provider denial
                // must not be confused with a separate complete-unaffected proof.
                f.facts.operations.push(OperationRecord {
                    body,
                    opcode: Opcode::Unknown,
                    target: SymbolId::NONE,
                    dest: ValueId::NONE,
                    a: ValueId::NONE,
                    b: ValueId::NONE,
                    arguments: IdRange::default(),
                    span: Span::default(),
                    flags: 0,
                });
            }
            f.facts.bodies.push(BodyRecord {
                symbol,
                file,
                span: Span::default(),
                name_span: Span::default(),
                operations: IdRange {
                    start,
                    len: f.facts.operations.len() as u32 - start,
                },
                parameters: IdRange::default(),
                body_hash: if symbol == suite {
                    ContentHash([42; 32])
                } else {
                    f.facts.files[file.index()].source_hash
                },
                flags: BODY_INITIALIZER,
            });
        }
        f.facts.identity = selector_facts::codec::write(facts, &f.facts).unwrap();
        let graph = selector_graph_build::build(
            &f.facts,
            &selector_graph_build::BuildOptions {
                workers: 1,
                include_models: false,
            },
        )
        .unwrap();
        selector_graph::codec::write(graph_path, &graph).unwrap();
    };
    let base_facts = head.root.join("base-query-facts.bin");
    let base_graph = head.root.join("base-query-graph.bin");
    let facts = head.root.join("query-facts.bin");
    let graph = head.root.join("query-graph.bin");
    prepare_side(&mut base, &base_facts, &base_graph);
    prepare_side(&mut head, &facts, &graph);
    (head, facts, graph)
}

fn query(f: &Fixture, facts: &Path, graph: &Path, name: &str, extra: &[&str]) -> (Output, Value) {
    let report = f.root.join(format!("{name}.json"));
    let paired_base = |head: &Path| {
        let mut name = std::ffi::OsString::from("base-");
        name.push(head.file_name().unwrap());
        head.with_file_name(name)
    };
    let mut command = Command::new(env!("CARGO_BIN_EXE_selector"));
    command
        .args(["query", "--base-facts"])
        .arg(paired_base(facts))
        .arg("--head-facts")
        .arg(facts)
        .arg("--base-graph")
        .arg(paired_base(graph))
        .arg("--head-graph")
        .arg(graph)
        .args([
            "--changed",
            "changed/Fixture.java",
            "--workers",
            "1",
            "--assume-independent-suites",
        ])
        .arg("--output")
        .arg(&report)
        .args(extra);
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let json = serde_json::from_slice(&std::fs::read(report).unwrap()).unwrap();
    (output, json)
}
fn opted(f: &Fixture, facts: &Path, graph: &Path, name: &str, extra: &[&str]) -> (Output, Value) {
    let mut flags = vec![
        "--assume-owning-test-classpath",
        "--classpath-absence-request",
        f.request.to_str().unwrap(),
    ];
    flags.extend(extra);
    query(f, facts, graph, name, &flags)
}
#[test]
fn verified_absence_is_explicit_and_retention_and_required_win() {
    let directory = tempfile::tempdir().unwrap();
    let (f, facts, graph) = prepare(directory.path(), Mode::Absent, false);
    let (_, strict) = query(&f, &facts, &graph, "strict", &[]);
    assert_eq!(strict["selection_contract"]["bits"], 496);
    let (output, conditional) = opted(&f, &facts, &graph, "conditional", &[]);
    assert_eq!(conditional["selection_contract"]["bits"], 1008);
    assert_eq!(conditional["decisions"][0]["status"], "excluded");
    assert_eq!(conditional["decisions"][0]["guarded"], false);
    assert!(
        conditional["decisions"][0]["reasons"]
            .as_array()
            .unwrap()
            .contains(&serde_json::json!("classpath_absence"))
    );
    assert!(String::from_utf8_lossy(&output.stderr).contains("\"effective_all_roots\":true"));
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .lines()
            .filter_map(|line| serde_json::from_str::<Value>(line).ok())
            .any(|row| row["stage"] == "query_prepare"
                && row["base_execution_seeds"].as_u64().unwrap_or(0) > 0
                && row["head_execution_seeds"].as_u64().unwrap_or(0) > 0)
    );
    let (_, retained) = opted(
        &f,
        &facts,
        &graph,
        "retained",
        &["--retain-suite", "admissioncase.Fixture"],
    );
    assert_ne!(retained["decisions"][0]["status"], "excluded");
    assert_eq!(retained["selection_contract"]["bits"], 1008);
    // A request names physical inputs. Supplying purported proof rows is not an
    // alternate admission path, even when all ordinary request pins are valid.
    let mut forged: Value = serde_json::from_slice(&std::fs::read(&f.request).unwrap()).unwrap();
    forged["evidence"] = serde_json::json!({"absence_identity":"11".repeat(32)});
    let forged_path = f.root.join("forged-request.json");
    std::fs::write(&forged_path, serde_json::to_vec(&forged).unwrap()).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_selector"))
        .args(["query", "--base-facts"])
        .arg(f.root.join("base-query-facts.bin"))
        .arg("--head-facts")
        .arg(&facts)
        .arg("--base-graph")
        .arg(f.root.join("base-query-graph.bin"))
        .arg("--head-graph")
        .arg(&graph)
        .args([
            "--changed",
            "changed/Fixture.java",
            "--assume-independent-suites",
            "--assume-owning-test-classpath",
            "--classpath-absence-request",
        ])
        .arg(forged_path)
        .arg("--output")
        .arg(f.root.join("forged.json"))
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(!f.root.join("forged.json").exists());
    let directory = tempfile::tempdir().unwrap();
    let (f, facts, graph) = prepare(directory.path(), Mode::Absent, true);
    let (_, required) = opted(&f, &facts, &graph, "required", &[]);
    assert_eq!(required["decisions"][0]["status"], "required");
    let (output, pruned) = opted(
        &f,
        &facts,
        &graph,
        "pruned",
        &["--prune-certified-classpath-roots"],
    );
    assert_eq!(pruned["decisions"][0]["status"], "excluded");
    assert_eq!(pruned["decisions"][0]["proofs"], serde_json::json!([]));
    assert_eq!(pruned["execution_seeds"], required["execution_seeds"]);
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("\"paired_classpath_pruned_roots\":1")
    );
    let (_, retained) = opted(
        &f,
        &facts,
        &graph,
        "pruned-retained",
        &[
            "--prune-certified-classpath-roots",
            "--retain-suite",
            "admissioncase.Fixture",
        ],
    );
    assert_eq!(retained["decisions"][0]["status"], "required");
}
#[test]
fn present_products_deny_and_frozen_replay_rechecks_directory_and_absence() {
    let directory = tempfile::tempdir().unwrap();
    let (f, facts, graph) = prepare(directory.path(), Mode::Present, false);
    let (output, present) = opted(
        &f,
        &facts,
        &graph,
        "present",
        &["--prune-certified-classpath-roots"],
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("\"paired_classpath_pruned_roots\":0")
    );
    assert_ne!(present["decisions"][0]["status"], "excluded");
    assert!(
        !present["decisions"][0]["reasons"]
            .as_array()
            .unwrap()
            .contains(&serde_json::json!("classpath_absence"))
    );
    assert_eq!(present["selection_contract"]["bits"], 1008);
    for mutation in ["directory", "absent"] {
        let directory = tempfile::tempdir().unwrap();
        let (f, facts, graph) = prepare(directory.path(), Mode::ManifestGap, false);
        let receipt = f.root.join("receipt.json");
        let (_, result) = opted(
            &f,
            &facts,
            &graph,
            "before",
            &["--receipt", receipt.to_str().unwrap()],
        );
        assert_eq!(result["decisions"][0]["status"], "excluded");
        let before = std::fs::read(&receipt).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_selector"))
            .args(["replay", "--receipt"])
            .arg(&receipt)
            .args(["--validate-only", "--frozen-inputs"])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let valid: Value = serde_json::from_slice(&output.stdout).unwrap();
        assert!(valid["earliest_invalidation"].is_null());
        if mutation == "directory" {
            std::fs::write(f.root.join("suite-classes/new-resource"), b"new").unwrap();
        } else {
            std::fs::write(f.root.join("optional.jar"), b"new").unwrap();
        }
        let output = Command::new(env!("CARGO_BIN_EXE_selector"))
            .args(["replay", "--receipt"])
            .arg(&receipt)
            .args(["--validate-only", "--frozen-inputs"])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let invalid: Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(invalid["earliest_invalidation"], "query.plan");
        assert_eq!(std::fs::read(receipt).unwrap(), before);
    }
}

#[test]
fn output_overlap_rejects_before_opening_progress_or_receipt() {
    let directory = tempfile::tempdir().unwrap();
    let (f, facts, graph) = prepare(directory.path(), Mode::Absent, false);
    let class = f.root.join("suite-classes/admissioncase/Fixture.class");
    let progress = f.root.join("changed-classes/new-progress.jsonl");
    let receipt = f.root.join("suite-classes/new-receipt.json");
    let original = std::fs::read(&class).unwrap();
    let contexts = std::fs::read(&f.contexts).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_selector"))
        .args(["query", "--base-facts"])
        .arg(f.root.join("base-query-facts.bin"))
        .arg("--base-graph")
        .arg(f.root.join("base-query-graph.bin"))
        .arg("--head-facts")
        .arg(facts)
        .arg("--head-graph")
        .arg(graph)
        .args([
            "--changed",
            "changed/Fixture.java",
            "--assume-independent-suites",
            "--assume-owning-test-classpath",
            "--classpath-absence-request",
        ])
        .arg(&f.request)
        .arg("--output")
        .arg(&class)
        .arg("--progress-jsonl")
        .arg(&progress)
        .arg("--receipt")
        .arg(&receipt)
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("output overlaps"));
    assert_eq!(std::fs::read(class).unwrap(), original);
    assert_eq!(std::fs::read(&f.contexts).unwrap(), contexts);
    assert!(!progress.exists());
    assert!(!receipt.exists());
}

#[test]
fn ordinary_compilation_is_a_distinct_explicit_contract_and_replay_option() {
    let directory = tempfile::tempdir().unwrap();
    let (f, facts, graph) = prepare(directory.path(), Mode::Absent, false);
    let (_, owning) = opted(&f, &facts, &graph, "owning-only", &[]);
    assert_eq!(owning["selection_contract"]["bits"], 1008);
    let receipt = f.root.join("compilation-receipt.json");
    let (_, ordinary) = opted(
        &f,
        &facts,
        &graph,
        "ordinary-compilation",
        &[
            "--assume-ordinary-compilation",
            "--receipt",
            receipt.to_str().unwrap(),
        ],
    );
    assert_eq!(ordinary["selection_contract"]["bits"], 2032);
    assert_eq!(ordinary["decisions"][0]["status"], "excluded");
    let original = std::fs::read(&receipt).unwrap();
    let mut recorded: Value = serde_json::from_slice(&original).unwrap();
    assert!(
        recorded["arguments"]
            .as_array()
            .unwrap()
            .contains(&serde_json::json!("--assume-ordinary-compilation"))
    );
    assert!(
        recorded["stages"]
            .as_array()
            .unwrap()
            .iter()
            .any(|stage| stage["id"] == "query.plan" && stage["classpath_inputs"].is_object())
    );
    let replay = |path: &Path| {
        let output = Command::new(env!("CARGO_BIN_EXE_selector"))
            .args(["replay", "--receipt"])
            .arg(path)
            .args(["--validate-only", "--frozen-inputs"])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        serde_json::from_slice::<Value>(&output.stdout).unwrap()
    };
    assert!(replay(&receipt)["earliest_invalidation"].is_null());
    let removed = recorded["arguments"]
        .as_array()
        .unwrap()
        .iter()
        .position(|arg| arg == "--assume-ordinary-compilation")
        .unwrap();
    recorded["arguments"]
        .as_array_mut()
        .unwrap()
        .remove(removed);
    let bindings = std::mem::take(recorded["path_arguments"].as_object_mut().unwrap());
    for (index, path) in bindings {
        let index = index.parse::<usize>().unwrap();
        recorded["path_arguments"][if index > removed { index - 1 } else { index }.to_string()] =
            path;
    }
    let changed = f.root.join("without-compilation-receipt.json");
    std::fs::write(&changed, serde_json::to_vec(&recorded).unwrap()).unwrap();
    let invalid = replay(&changed);
    assert!(!invalid["earliest_invalidation"].is_null());
    assert!(
        invalid["stages"]
            .as_array()
            .unwrap()
            .iter()
            .any(|stage| stage["reason"] == "options_changed")
    );
    assert_eq!(std::fs::read(receipt).unwrap(), original);
}

// This capture protocol deliberately uses a genuine tiny JAR as a normalized
// tool input. It tests identity admission, without claiming a compiler launch.
fn configure_compilation_pair(f: &Fixture) {
    let mut request: Value = serde_json::from_slice(&std::fs::read(&f.request).unwrap()).unwrap();
    let tool = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../fixtures/binary/fixture-stored.jar")
        .canonicalize()
        .unwrap();
    for side in ["base", "head"] {
        let path = PathBuf::from(request[side]["contexts"]["path"].as_str().unwrap());
        let mut capture: Value = serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
        capture["sbt_version"] = serde_json::json!("normalized");
        capture["java_runtime"] = serde_json::json!({"java_home":"/declared/jdk","java_version":"21","java_vendor":"normalized","os_arch":"normalized"});
        let root = capture["source_root"].clone();
        let context = &mut capture["contexts"][1];
        context["base_directory"] = root;
        context["source_files"] = serde_json::json!([context["source_records"][0]["path"]]);
        context["resource_files"] = serde_json::json!([]);
        context["scala_version"] = serde_json::json!("2.13.18");
        context["scala_organization"] = serde_json::json!("org.scala-lang");
        context["scala_instance_version"] = serde_json::json!("2.13.18");
        context["scala_instance_jars"] = serde_json::json!([tool]);
        context["scala_instance_inputs"] = serde_json::json!([tool]);
        context["scalac_plugin_inputs"] = serde_json::json!([]);
        context["scalac_options"] = serde_json::json!([]);
        context["javac_options"] = serde_json::json!([]);
        context["java_home"] = Value::Null;
        context["java_options"] = serde_json::json!([]);
        context["fork"] = serde_json::json!(false);
        let mut object = fixture::pin(&tool);
        object["kind"] = serde_json::json!("file");
        capture["input_objects"]
            .as_array_mut()
            .unwrap()
            .push(object);
        std::fs::write(&path, serde_json::to_vec(&capture).unwrap()).unwrap();
        request[side]["contexts"] = fixture::pin(&path);
    }
    std::fs::write(&f.request, serde_json::to_vec(&request).unwrap()).unwrap();
}
fn add_signature_only_seed(f: &Fixture) -> (PathBuf, PathBuf) {
    let head_facts = f.root.join("metadata-query-facts.bin");
    let head_graph = f.root.join("metadata-query-graph.bin");
    for (side, original_facts, facts_path, graph_path) in [
        (
            false,
            f.root.join("base-query-facts.bin"),
            f.root.join("base-metadata-query-facts.bin"),
            f.root.join("base-metadata-query-graph.bin"),
        ),
        (
            true,
            f.root.join("query-facts.bin"),
            head_facts.clone(),
            head_graph.clone(),
        ),
    ] {
        let mut facts = selector_facts::codec::read(&original_facts).unwrap();
        let mut intern = |text: &str| {
            let id = StrId(facts.strings.entries.len() as u32);
            facts.strings.entries.push(selector_facts::TextRange {
                start: facts.strings.bytes.len() as u64,
                len: text.len() as u32,
            });
            facts.strings.bytes.extend(text.as_bytes());
            id
        };
        let name = intern("local114");
        let signature = intern(if side {
            "{\"type_ref\":{\"symbol\":\"scala/Long#\"}}"
        } else {
            "{\"type_ref\":{\"symbol\":\"scala/Int#\"}}"
        });
        facts.symbols.push(selector_facts::SymbolRecord {
            name,
            display: name,
            owner: SymbolId::NONE,
            file: FileId(1),
            context: facts.files[1].context,
            kind: 19,
            properties: 1024,
            signature,
            span: Span::default(),
            flags: SYMBOL_DEFINED,
        });
        facts.identity = selector_facts::codec::write(&facts_path, &facts).unwrap();
        let graph = selector_graph_build::build(
            &facts,
            &selector_graph_build::BuildOptions {
                workers: 1,
                include_models: false,
            },
        )
        .unwrap();
        selector_graph::codec::write(&graph_path, &graph).unwrap();
    }
    (head_facts, head_graph)
}
#[test]
fn ordinary_compilation_accounts_for_stable_source_metadata_but_not_changed_settings() {
    let directory = tempfile::tempdir().unwrap();
    let (f, _, _) = prepare(directory.path(), Mode::Absent, false);
    configure_compilation_pair(&f);
    let (facts, graph) = add_signature_only_seed(&f);
    let (_, owning) = opted(&f, &facts, &graph, "metadata-owning-only", &[]);
    assert_eq!(owning["selection_contract"]["bits"], 1008);
    assert_ne!(owning["decisions"][0]["status"], "excluded");
    let (metadata_output, ordinary) = opted(
        &f,
        &facts,
        &graph,
        "metadata-compilation",
        &["--assume-ordinary-compilation"],
    );
    assert_eq!(ordinary["selection_contract"]["bits"], 2032);
    assert_eq!(ordinary["decisions"][0]["status"], "excluded");
    assert!(
        String::from_utf8_lossy(&metadata_output.stderr)
            .lines()
            .filter_map(|line| serde_json::from_str::<Value>(line).ok())
            .any(|row| row["stage"] == "stable_compilation_inputs"
                && row["owner"] == "project:suite/configuration:test"
                && row["base_sources"] == 1
                && row["head_sources"] == 1)
    );
    let mut request: Value = serde_json::from_slice(&std::fs::read(&f.request).unwrap()).unwrap();
    let mut capture: Value = serde_json::from_slice(&std::fs::read(&f.contexts).unwrap()).unwrap();
    capture["contexts"][1]["scalac_options"] = serde_json::json!(["-normalized-settings-change"]);
    std::fs::write(&f.contexts, serde_json::to_vec(&capture).unwrap()).unwrap();
    request["head"]["contexts"] = fixture::pin(&f.contexts);
    std::fs::write(&f.request, serde_json::to_vec(&request).unwrap()).unwrap();
    let (_, changed) = opted(
        &f,
        &facts,
        &graph,
        "metadata-settings-changed",
        &["--assume-ordinary-compilation"],
    );
    assert_eq!(changed["selection_contract"]["bits"], 2032);
    assert_ne!(changed["decisions"][0]["status"], "excluded");
    let directory = tempfile::tempdir().unwrap();
    let (f, facts, graph) = prepare(directory.path(), Mode::Absent, true);
    let (_, required) = opted(
        &f,
        &facts,
        &graph,
        "compilation-required",
        &["--assume-ordinary-compilation"],
    );
    assert_eq!(required["decisions"][0]["status"], "required");
}
