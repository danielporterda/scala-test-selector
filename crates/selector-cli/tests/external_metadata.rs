//! Native CLI admission uses actual ordered compiler providers, not fixture-only
//! authority hashes. No JVM or full-corpus analysis is invoked by these tests.
use selector_facts::{BodyRecord, FactSnapshot, OperationRecord};
use selector_types::*;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const CONTEXT: &str = "project:external-metadata/configuration:test";
const CLASS: &str = "selectedexternal/Configuration";
const APPLY: &str = "selectedexternal/Configuration#PatienceConfig.apply(+1).";
fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../fixtures/external-metadata")
        .canonicalize()
        .unwrap()
}
fn read(path: &Path) -> Value {
    serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap()
}
fn save(path: &Path, value: &Value) {
    std::fs::write(path, serde_json::to_vec(value).unwrap()).unwrap();
}
fn cli(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_selector"))
        .args(args)
        .output()
        .unwrap()
}
fn good(args: &[&str]) -> Output {
    let output = cli(args);
    assert!(
        output.status.success(),
        "{:?}\n{}",
        args,
        String::from_utf8_lossy(&output.stderr)
    );
    output
}
fn s(path: &Path) -> &str {
    path.to_str().unwrap()
}
struct Inputs {
    temp: tempfile::TempDir,
    fixture: PathBuf,
    contexts: PathBuf,
    map: PathBuf,
    admission: PathBuf,
    producer: String,
}
impl Inputs {
    fn new() -> Self {
        let temp = tempfile::tempdir().unwrap();
        let fixture = fixture();
        let contexts = temp.path().join("contexts.json");
        let original_contexts = std::fs::read(fixture.join("compiler-contexts.json")).unwrap();
        let mut capture: Value = serde_json::from_slice(&original_contexts).unwrap();
        // This is a NEW native context input derived from the recorded actual
        // compiler invocation. The frozen fixture's smaller binder wire did not
        // claim source_root/input_objects or a captured Java runtime.
        assert!(capture.get("source_root").is_none());
        assert!(capture.get("input_objects").is_none());
        assert!(capture.get("java_runtime").is_none());
        let source_root = capture["provenance"]["compiler_command"]
            .as_array()
            .unwrap()
            .iter()
            .filter_map(Value::as_str)
            .find_map(|arg| arg.strip_prefix("-P:semanticdb:sourceroot:"))
            .unwrap()
            .to_owned();
        assert_eq!(Path::new(&source_root), fixture);
        let objects: Vec<_> = capture["contexts"][0]["full_classpath"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| {
                let path = Path::new(row["path"].as_str().unwrap());
                let bytes = std::fs::read(path).unwrap();
                let digest = ContentHash(Sha256::digest(&bytes).into()).to_string();
                assert_eq!(row["sha256"], digest);
                json!({"path":row["path"],"kind":"file","sha256":digest,"bytes":bytes.len()})
            })
            .collect();
        capture["source_root"] = json!(source_root);
        capture["input_objects"] = json!(objects);
        capture["native_projection_of_sha256"] =
            json!(ContentHash(Sha256::digest(&original_contexts).into()).to_string());
        save(&contexts, &capture);
        assert_eq!(
            std::fs::read(fixture.join("compiler-contexts.json")).unwrap(),
            original_contexts
        );
        let entries: Vec<_> = capture["contexts"][0]["full_classpath"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| json!({"path":row["path"],"sha256":row["sha256"],"kind":"jar"}))
            .collect();
        let map = temp.path().join("binary-map.json");
        save(
            &map,
            &json!({"version":1,"revision":capture["revision"],"java_feature":null,"types":[],"methods":[],"contexts":[{"id":CONTEXT,"entries":entries}]}),
        );
        let requests = temp.path().join("provider-requests.json");
        save(
            &requests,
            &json!({"schema":"external-metadata-provider-requests/v1","classes":[{"context":CONTEXT,"outer_class":CLASS},{"context":CONTEXT,"outer_class":"absent/Missing"}]}),
        );
        let preview = temp.path().join("authority.json");
        good(&[
            "metadata-authority",
            "--contexts",
            s(&contexts),
            "--metadata-binary-map",
            s(&map),
            "--compiler-input-root",
            s(&fixture),
            "--input",
            s(&requests),
            "--output",
            s(&preview),
        ]);
        let authority = read(&preview);
        assert_eq!(
            authority["schema"],
            "external-metadata-provider-authority/v1"
        );
        let rows = authority["classes"].as_array().unwrap();
        let missing = rows
            .iter()
            .find(|r| r["outer_class"] == "absent/Missing")
            .unwrap();
        assert_eq!(missing["available"], false);
        assert_eq!(missing["class_sha256"], Value::Null);
        let provider = rows.iter().find(|r| r["outer_class"] == CLASS).unwrap();
        assert_eq!(provider["available"], true);
        let mut admitted = read(&fixture.join("admission.json"));
        admitted["authority_sha256"] = authority["authority_sha256"].clone();
        admitted["contexts_sha256"] = authority["contexts_sha256"].clone();
        let projection = &mut admitted["bindings"][0]["projections"][0];
        for (left, right) in [
            ("provider_index", "provider_index"),
            ("provider_sha256", "provider_sha256"),
            ("outer_class_sha256", "class_sha256"),
        ] {
            assert_eq!(projection[left], provider[right]);
        }
        projection["classpath_sha256"] = provider["classpath_sha256"].clone();
        std::fs::copy(
            fixture.join("external-signatures.semanticdb"),
            temp.path().join("external-signatures.semanticdb"),
        )
        .unwrap();
        let producer = admitted["producer_sha256"].as_str().unwrap().to_owned();
        let admission = temp.path().join("admission.json");
        save(&admission, &admitted);
        Self {
            temp,
            fixture,
            contexts,
            map,
            admission,
            producer,
        }
    }
    fn extract(&self, output: &Path, workers: &str, metadata: bool) -> Output {
        self.extract_recorded(output, workers, metadata, None)
    }
    fn extract_recorded(
        &self,
        output: &Path,
        workers: &str,
        metadata: bool,
        receipt: Option<&Path>,
    ) -> Output {
        let documents = self.fixture.join("documents.jsonl");
        let syntax = self.fixture.join("syntax.jsonl");
        let mut args = vec![
            "extract",
            "--input",
            s(&documents),
            "--syntax",
            s(&syntax),
            "--contexts",
            s(&self.contexts),
            "--compiler-input-root",
            s(&self.fixture),
            "--workers",
            workers,
            "--output",
            s(output),
        ];
        if metadata {
            args.extend([
                "--external-metadata",
                s(&self.admission),
                "--external-metadata-producer",
                &self.producer,
                "--metadata-binary-map",
                s(&self.map),
            ]);
        }
        if let Some(receipt) = receipt {
            args.extend(["--receipt", s(receipt)]);
        }
        cli(&args)
    }
    fn run(&self, name: &str) -> Output {
        let catalogue = self.temp.path().join("suites.json");
        save(
            &catalogue,
            &json!({"complete":true,"suite_names":["selectedexternal.DiagnosticSuite"]}),
        );
        let documents = self.fixture.join("documents.jsonl");
        let syntax = self.fixture.join("syntax.jsonl");
        let artifacts = self.temp.path().join("artifacts");
        let output = self.temp.path().join(format!("{name}.json"));
        let receipt = self.temp.path().join(format!("{name}-receipt.json"));
        cli(&[
            "run",
            "--head",
            s(&documents),
            "--head-syntax",
            s(&syntax),
            "--contexts",
            s(&self.contexts),
            "--compiler-input-root",
            s(&self.fixture),
            "--workers",
            "1",
            "--catalogue-input",
            s(&catalogue),
            "--changed",
            "src/selectedexternal/Calls.scala",
            "--artifacts",
            s(&artifacts),
            "--output",
            s(&output),
            "--receipt",
            s(&receipt),
            "--external-metadata",
            s(&self.admission),
            "--external-metadata-producer",
            &self.producer,
            "--metadata-binary-map",
            s(&self.map),
        ])
    }
}
fn body<'a>(facts: &'a FactSnapshot, name: &str) -> &'a BodyRecord {
    let symbol = facts
        .find_symbol(&format!("selectedexternal/Calls#{name}()."))
        .unwrap();
    facts.bodies.iter().find(|b| b.symbol == symbol).unwrap()
}
fn calls<'a>(
    facts: &'a FactSnapshot,
    body: &BodyRecord,
    target: &str,
) -> Vec<(usize, &'a OperationRecord)> {
    facts.operations[body.operations.range()]
        .iter()
        .enumerate()
        .filter(|(_, op)| {
            matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
                && facts.symbol_name(op.target) == target
        })
        .collect()
}
fn guarded(facts: &FactSnapshot, name: &str) -> bool {
    let symbol = body(facts, name).symbol;
    facts.issues.iter().any(|issue| {
        issue.symbol == symbol
            && issue.kind == IssueKind::UnknownExecution
            && facts.text(issue.detail).contains("argument signature")
    })
}

#[test]
fn native_provider_admission_repairs_source_formals_and_is_worker_deterministic() {
    let i = Inputs::new();
    let baseline = i.temp.path().join("none.bin");
    let one = i.temp.path().join("one.bin");
    let four = i.temp.path().join("four.bin");
    for (path, workers, meta) in [
        (&baseline, "1", false),
        (&one, "1", true),
        (&four, "4", true),
    ] {
        let result = i.extract(path, workers, meta);
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
    }
    assert_eq!(std::fs::read(&one).unwrap(), std::fs::read(&four).unwrap());
    let no = selector_facts::codec::read(&baseline).unwrap();
    let facts = selector_facts::codec::read(&one).unwrap();
    assert!(guarded(&no, "inherited"));
    assert!(!guarded(&facts, "inherited"));
    let owner = body(&facts, "inherited");
    let interval = calls(&facts, owner, "selectedexternal/Calls#interval().");
    let timeout = calls(&facts, owner, "selectedexternal/Calls#timeout().");
    let apply = calls(&facts, owner, APPLY);
    assert_eq!((interval.len(), timeout.len(), apply.len()), (1, 1, 1));
    assert!(interval[0].0 < timeout[0].0 && timeout[0].0 < apply[0].0);
    assert_eq!(
        &facts.operands[apply[0].1.arguments.range()],
        &[timeout[0].1.dest, interval[0].1.dest]
    );
    let method = facts.find_symbol(APPLY).unwrap();
    assert_eq!(facts.symbols[method.index()].flags & SYMBOL_DEFINED, 0);
    assert!(!facts.bodies.iter().any(|b| b.symbol == method));
    let parents = |f: &FactSnapshot| {
        let mut rows: Vec<_> = f
            .relations
            .iter()
            .filter(|r| r.kind == RelationKind::Parent)
            .map(|r| (f.symbol_name(r.source), f.symbol_name(r.target)))
            .collect();
        rows.sort();
        rows.into_iter()
            .map(|(a, b)| (a.to_owned(), b.to_owned()))
            .collect::<Vec<_>>()
    };
    assert_eq!(parents(&facts), parents(&no));
    let returned = body(&facts, "appliedReturned");
    assert_eq!(
        calls(
            &facts,
            returned,
            "selectedexternal/Configuration#PatienceConfig.returning()."
        )
        .len(),
        1
    );
    assert_eq!(
        facts.operations[returned.operations.range()]
            .iter()
            .filter(|op| op.opcode == Opcode::InvokeCallback)
            .count(),
        1
    );
}

#[test]
fn warmed_run_checks_metadata_bundle_without_compiler_normalization_and_records_inputs() {
    let i = Inputs::new();
    let first = i.run("cold");
    assert!(
        first.status.success(),
        "{}",
        String::from_utf8_lossy(&first.stderr)
    );
    let warm = i.run("warm");
    assert!(
        warm.status.success(),
        "{}",
        String::from_utf8_lossy(&warm.stderr)
    );
    let events: Vec<Value> = String::from_utf8_lossy(&warm.stderr)
        .lines()
        .filter_map(|l| serde_json::from_str(l).ok())
        .collect();
    assert!(events.iter().any(|e| e["stage"] == "metadata_inputs"
        && e["input_bundle_checked"] == true
        && e["full_signature_admission"] == false));
    assert!(
        events
            .iter()
            .any(|e| e["stage"] == "extract" && e["cache_hit"] == true)
    );
    assert!(!events.iter().any(|e| e["stage"] == "metadata_admission"));
    let receipt = read(&i.temp.path().join("warm-receipt.json"));
    let stage = receipt["stages"]
        .as_array()
        .unwrap()
        .iter()
        .find(|s| s["id"] == "head.metadata")
        .unwrap();
    assert_eq!(stage["producer_key"], "metadata");
    let roles: Vec<_> = stage["inputs"]
        .as_array()
        .unwrap()
        .iter()
        .map(|r| r["role"].as_str().unwrap())
        .collect();
    for role in [
        "metadata_manifest",
        "metadata_contexts",
        "metadata_binary_map",
        "metadata_payload_0",
        "metadata_provider_0",
    ] {
        assert!(roles.contains(&role), "{roles:?}");
    }
    let extract = receipt["stages"]
        .as_array()
        .unwrap()
        .iter()
        .find(|s| s["id"] == "head.extract")
        .unwrap();
    assert_eq!(extract["dependencies"], json!(["head.metadata"]));
    let payload = i.temp.path().join("external-signatures.semanticdb");
    let original = std::fs::read(&payload).unwrap();
    let mut changed = original.clone();
    changed[0] ^= 1;
    std::fs::write(&payload, changed).unwrap();
    assert!(!i.run("mutated-payload").status.success());
    std::fs::write(payload, original).unwrap();
    let original = read(&i.admission);
    let mut changed = original.clone();
    changed["bindings"][0]["projections"][0]["provider_index"] = json!(1);
    save(&i.admission, &changed);
    assert!(!i.run("mutated-provider").status.success());
    save(&i.admission, &original);
    let mut changed = read(&i.contexts);
    changed["contexts"][0]["compiler_environment_fingerprint"] = json!("00".repeat(32));
    save(&i.contexts, &changed);
    assert!(!i.run("mutated-context").status.success());
}

#[test]
fn standalone_extract_receipt_records_metadata_and_revalidates_transitive_inputs() {
    let i = Inputs::new();
    for metadata in [false, true] {
        let output = i.temp.path().join(format!("extract-{metadata}.bin"));
        let receipt = i
            .temp
            .path()
            .join(format!("extract-{metadata}.receipt.json"));
        let run = i.extract_recorded(&output, "1", metadata, Some(&receipt));
        assert!(
            run.status.success(),
            "{}",
            String::from_utf8_lossy(&run.stderr)
        );
        let saved = read(&receipt);
        assert_eq!(saved["arguments"][0], "extract");
        let stages = saved["stages"].as_array().unwrap();
        let extract = stages
            .iter()
            .find(|row| row["id"] == "head.extract")
            .unwrap();
        assert!(extract["compiler_inputs"].is_object());
        assert_eq!(extract["outputs"][0]["role"], "facts");
        assert_eq!(
            extract["dependencies"],
            if metadata {
                json!(["head.metadata"])
            } else {
                json!([])
            }
        );
        assert_eq!(
            stages.iter().any(|row| row["id"] == "head.metadata"),
            metadata
        );
        let validation = i
            .temp
            .path()
            .join(format!("extract-{metadata}.validation.json"));
        good(&[
            "replay",
            "--receipt",
            s(&receipt),
            "--validate-only",
            "--output",
            s(&validation),
        ]);
        assert!(read(&validation)["earliest_invalidation"].is_null());
        if metadata {
            let payload = i.temp.path().join("external-signatures.semanticdb");
            let mut bytes = std::fs::read(&payload).unwrap();
            bytes[0] ^= 1;
            std::fs::write(&payload, bytes).unwrap();
            good(&[
                "replay",
                "--receipt",
                s(&receipt),
                "--validate-only",
                "--output",
                s(&validation),
            ]);
            assert_eq!(read(&validation)["earliest_invalidation"], "head.metadata");
        }
    }
}

#[test]
fn request_plan_is_bounded_normalization_only_and_partial_metadata_keeps_guards() {
    let i = Inputs::new();
    let documents = i.fixture.join("documents.jsonl");
    let syntax = i.fixture.join("syntax.jsonl");
    let output = i.temp.path().join("requests.json");
    let run = good(&[
        "metadata-requests",
        "--input",
        s(&documents),
        "--syntax",
        s(&syntax),
        "--contexts",
        s(&i.contexts),
        "--workers",
        "1",
        "--output",
        s(&output),
    ]);
    let plan = read(&output);
    assert_eq!(plan["schema"], "compiler-external-metadata-requests/v1");
    assert_eq!(
        plan["requests_total"].as_u64().unwrap() as usize,
        plan["requests"].as_array().unwrap().len()
    );
    assert!(
        plan["requests"]
            .as_array()
            .unwrap()
            .iter()
            .any(|r| r["symbol"] == APPLY && r["context"] == CONTEXT)
    );
    assert!(!String::from_utf8_lossy(&run.stderr).contains("source_recipes"));
    let mut partial = read(&i.admission);
    partial["bindings"] = json!([]);
    partial["payloads"] = json!([]);
    save(&i.admission, &partial);
    let out = i.temp.path().join("partial.bin");
    let result = i.extract(&out, "1", true);
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert!(guarded(
        &selector_facts::codec::read(&out).unwrap(),
        "inherited"
    ));
}

#[test]
fn precheck_does_not_replace_full_request_membership_admission() {
    let i = Inputs::new();
    let mut admitted = read(&i.admission);
    admitted["bindings"][0]["roots"]
        .as_array_mut()
        .unwrap()
        .push(json!(
            "selectedexternal/Configuration#PatienceConfig.notRequested()."
        ));
    save(&i.admission, &admitted);
    let result = i.extract(&i.temp.path().join("bad.bin"), "1", true);
    assert!(!result.status.success());
    assert!(String::from_utf8_lossy(&result.stderr).contains("not uniquely requested"));
}

#[test]
fn metadata_options_fail_early_as_complete_command_specific_sets() {
    for args in [
        vec!["extract", "--external-metadata", "missing.json"],
        vec!["extract", "--external-metadata-producer", "invalid"],
        vec!["query", "--metadata-binary-map", "missing.json"],
        vec!["run", "--base-external-metadata", "missing.json"],
        vec!["metadata-requests", "--input", "missing.json"],
        vec![
            "metadata-authority",
            "--contexts",
            "missing.json",
            "--metadata-binary-map",
            "missing.json",
        ],
    ] {
        let output = cli(&args);
        assert!(!output.status.success(), "{args:?}");
    }
}

#[test]
fn run_maps_base_metadata_without_leaking_it_into_head() {
    let i = Inputs::new();
    let documents = i.fixture.join("documents.jsonl");
    let syntax = i.fixture.join("syntax.jsonl");
    let catalogue = i.temp.path().join("suites.json");
    save(
        &catalogue,
        &json!({"complete":true,"suite_names":["selectedexternal.DiagnosticSuite"]}),
    );
    let artifacts = i.temp.path().join("artifacts");
    let output = i.temp.path().join("pair.json");
    let receipt = i.temp.path().join("pair-receipt.json");
    good(&[
        "run",
        "--head",
        s(&documents),
        "--head-syntax",
        s(&syntax),
        "--base",
        s(&documents),
        "--base-syntax",
        s(&syntax),
        "--contexts",
        s(&i.contexts),
        "--compiler-input-root",
        s(&i.fixture),
        "--base-contexts",
        s(&i.contexts),
        "--base-compiler-input-root",
        s(&i.fixture),
        "--base-external-metadata",
        s(&i.admission),
        "--base-external-metadata-producer",
        &i.producer,
        "--base-metadata-binary-map",
        s(&i.map),
        "--workers",
        "4",
        "--catalogue-input",
        s(&catalogue),
        "--changed",
        "src/selectedexternal/Calls.scala",
        "--artifacts",
        s(&artifacts),
        "--output",
        s(&output),
        "--receipt",
        s(&receipt),
    ]);
    let receipt = read(&receipt);
    let stages = receipt["stages"].as_array().unwrap();
    assert!(stages.iter().any(|stage| stage["id"] == "base.metadata"));
    assert!(!stages.iter().any(|stage| stage["id"] == "head.metadata"));
    assert_eq!(
        stages
            .iter()
            .find(|stage| stage["id"] == "base.extract")
            .unwrap()["dependencies"],
        json!(["base.metadata"])
    );
    assert_eq!(
        stages
            .iter()
            .find(|stage| stage["id"] == "head.extract")
            .unwrap()["dependencies"],
        json!([])
    );
}
