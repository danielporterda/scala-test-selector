//! Real caller compile against the recorded physical JAR classpath, followed by
//! signature-only metadata admission. Byte perturbations below are negatives.
use selector_extract::external_metadata::{
    ExternalMetadataLimits, MetadataProviderAuthority, MetadataRequestLimits, ProviderResolution,
    admit,
};
use selector_extract::{ExtractOptions, finish_capture, prepare_capture};
use selector_facts::{BodyRecord, FactSnapshot, OperationRecord};
use selector_models::binary::{CapturedClasspath, ClassLookup, ClasspathEntry, EntryKind, Limits};
use selector_types::*;
use serde_json::{Value, json};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

const CONTEXT: &str = "project:external-metadata/configuration:test";
const APPLY: &str = "selectedexternal/Configuration#PatienceConfig.apply(+1).";
fn directory() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/external-metadata")
}
fn read_json(path: &Path) -> Value {
    serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap()
}
fn manifest() -> Value {
    read_json(&directory().join("manifest.json"))
}
fn hash(value: &Value) -> ContentHash {
    ContentHash::from_hex(value.as_str().unwrap()).unwrap()
}
fn options() -> ExtractOptions {
    ExtractOptions {
        workers: 2,
        compiler_contexts: Some(directory().join("compiler-contexts.json")),
        ..Default::default()
    }
}
fn prepared() -> selector_extract::PreparedCapture {
    prepare_capture(
        &directory().join("documents.jsonl"),
        Some(&directory().join("syntax.jsonl")),
        &options(),
    )
    .unwrap()
}
struct Authority {
    identity: ContentHash,
    contexts: ContentHash,
    classpath_identity: ContentHash,
    classpath: Mutex<CapturedClasspath>,
}
impl Authority {
    fn new() -> Self {
        let manifest = manifest();
        let entries = manifest["ordered_actual_compiler_classpath"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| ClasspathEntry {
                path: PathBuf::from(row["path"].as_str().unwrap()),
                sha256: hash(&row["sha256"]),
                kind: EntryKind::Jar,
            })
            .collect();
        Self {
            identity: hash(&manifest["authority_sha256"]),
            contexts: hash(&manifest["context_manifest_sha256"]),
            classpath_identity: hash(&manifest["classpath_sha256"]),
            classpath: Mutex::new(
                CapturedClasspath::new(entries, Limits::default())
                    .unwrap()
                    .with_java_feature(Some(21))
                    .unwrap(),
            ),
        }
    }
}
impl MetadataProviderAuthority for Authority {
    fn identity(&self) -> ContentHash {
        self.identity
    }
    fn contexts_identity(&self) -> ContentHash {
        self.contexts
    }
    fn resolve(
        &self,
        context: &str,
        outer_class: &str,
    ) -> Result<Option<ProviderResolution>, Error> {
        if context != CONTEXT {
            return Ok(None);
        }
        let mut classpath = self.classpath.lock().unwrap();
        let found = match classpath
            .lookup(outer_class)
            .map_err(|error| Error::Message(error.to_string()))?
        {
            ClassLookup::Found(found) => found,
            ClassLookup::Absent(_) => return Ok(None),
        };
        let provider_index = found.proof.selected_entry.unwrap();
        Ok(Some(ProviderResolution {
            classpath_identity: self.classpath_identity,
            provider_index: provider_index as u32,
            provider_sha256: classpath.entries[provider_index].sha256,
            class_bytes: Arc::from(found.bytes),
        }))
    }
}
fn metadata(
    prepared: &selector_extract::PreparedCapture,
) -> Arc<selector_extract::external_metadata::AdmittedExternalMetadata> {
    let requests = prepared
        .metadata_requests(&MetadataRequestLimits::default())
        .unwrap();
    assert_eq!(
        requests.contexts_identity(),
        Some(hash(&manifest()["context_manifest_sha256"]))
    );
    for root in read_json(&directory().join("admission.json"))["bindings"][0]["roots"]
        .as_array()
        .unwrap()
    {
        assert!(
            requests
                .iter()
                .any(|request| request.context == CONTEXT
                    && request.symbol == root.as_str().unwrap())
        );
    }
    Arc::new(
        admit(
            &directory().join("admission.json"),
            &requests,
            &Authority::new(),
            hash(&manifest()["producer_sha256"]),
            &ExternalMetadataLimits::default(),
        )
        .unwrap(),
    )
}
fn enhanced() -> FactSnapshot {
    let owner = prepared();
    let admitted = metadata(&owner);
    finish_capture(owner, Some(admitted)).unwrap()
}
fn body<'a>(facts: &'a FactSnapshot, name: &str) -> &'a BodyRecord {
    let symbol = facts
        .find_symbol(&format!("selectedexternal/Calls#{name}()."))
        .unwrap();
    facts
        .bodies
        .iter()
        .find(|body| body.symbol == symbol)
        .unwrap()
}
fn ops<'a>(facts: &'a FactSnapshot, body: &BodyRecord) -> &'a [OperationRecord] {
    &facts.operations[body.operations.range()]
}
fn calls<'a>(
    facts: &'a FactSnapshot,
    body: &BodyRecord,
    symbol: &str,
) -> Vec<(usize, &'a OperationRecord)> {
    ops(facts, body)
        .iter()
        .enumerate()
        .filter(|(_, op)| {
            matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
                && facts.symbol_name(op.target) == symbol
        })
        .collect()
}
fn argument_guard(facts: &FactSnapshot, name: &str) -> bool {
    let owner = body(facts, name);
    facts.issues.iter().any(|issue| {
        issue.symbol == owner.symbol
            && issue.kind == IssueKind::UnknownExecution
            && facts.text(issue.detail).contains("argument signature")
    })
}

#[test]
fn actual_compiler_context_is_pinned_and_tiny_jvm_order_is_independent() {
    let fixture = directory();
    let receipt = manifest();
    let contexts = read_json(&fixture.join("compiler-contexts.json"));
    assert_eq!(
        contexts["capture_kind"],
        "direct_scalac_fixture_actual_physical_classpath"
    );
    assert_eq!(
        contexts["provenance"]["original_directory_relabelled_as_jar"],
        false
    );
    let command = contexts["provenance"]["compiler_command"]
        .as_array()
        .unwrap();
    let classpath = command
        .windows(2)
        .find(|pair| pair[0] == "-classpath")
        .unwrap()[1]
        .as_str()
        .unwrap();
    assert_eq!(
        classpath,
        contexts["provenance"]["target_classpath_argument"]
            .as_str()
            .unwrap()
    );
    let actual: Vec<_> = classpath.split(':').collect();
    for (index, row) in receipt["ordered_actual_compiler_classpath"]
        .as_array()
        .unwrap()
        .iter()
        .enumerate()
    {
        assert_eq!(actual[index], row["path"].as_str().unwrap());
    }
    assert_eq!(
        std::fs::read_to_string(fixture.join("jvm-inherited.stdout")).unwrap(),
        "inherited:interval,timeout:1:2\n"
    );
    assert_eq!(
        std::fs::read_to_string(fixture.join("jvm-eta.stdout")).unwrap(),
        "eta-created:qualifier\neta-invoked:qualifier,timeout,interval\n"
    );
    assert_eq!(
        std::fs::read_to_string(fixture.join("jvm-applied-returned.stdout")).unwrap(),
        "applied-returned:qualifier,timeout,factory,interval,returned-body\n"
    );
}

#[test]
fn admitted_scala_signature_repairs_formal_binding_without_changing_provider_evaluation() {
    let baseline = finish_capture(prepared(), None).unwrap();
    assert!(argument_guard(&baseline, "inherited"));
    let facts = enhanced();
    let owner = body(&facts, "inherited");
    let interval = calls(&facts, owner, "selectedexternal/Calls#interval().");
    let timeout = calls(&facts, owner, "selectedexternal/Calls#timeout().");
    let apply = calls(&facts, owner, APPLY);
    assert_eq!((interval.len(), timeout.len(), apply.len()), (1, 1, 1));
    assert!(interval[0].0 < timeout[0].0 && timeout[0].0 < apply[0].0);
    assert_eq!(
        &facts.operands[apply[0].1.arguments.range()],
        &[timeout[0].1.dest, interval[0].1.dest],
        "formal order is timeout,interval; provider evaluation stays interval,timeout"
    );
    assert!(!argument_guard(&facts, "inherited"));
    assert_ne!(
        facts.identity, baseline.identity,
        "admitted metadata is part of the snapshot identity"
    );
    assert_eq!(
        facts.files.len(),
        baseline.files.len(),
        "signature metadata adds no source file"
    );
    let parents = |facts: &FactSnapshot| {
        let mut rows: Vec<_> = facts
            .relations
            .iter()
            .filter(|r| r.kind == RelationKind::Parent)
            .map(|r| {
                (
                    facts.symbol_name(r.source).to_owned(),
                    facts.symbol_name(r.target).to_owned(),
                )
            })
            .collect();
        rows.sort();
        rows
    };
    assert_eq!(
        parents(&facts),
        parents(&baseline),
        "formal metadata grants no hierarchy authority"
    );
    let method = facts.find_symbol(APPLY).unwrap();
    assert_eq!(facts.symbols[method.index()].flags & SYMBOL_DEFINED, 0);
    assert!(!facts.symbols[method.index()].signature.is_none());
    assert!(
        !facts.bodies.iter().any(|b| b.symbol == method),
        "metadata does not supply an executable body"
    );
    let graph = selector_graph_build::build(&facts, &Default::default()).unwrap();
    assert!(
        graph
            .issues
            .iter()
            .any(|i| i.symbol == method && i.kind == IssueKind::UnknownExecution),
        "callee execution remains unproved after signature-only admission"
    );
}

#[test]
fn returned_function_still_executes_only_beyond_the_declared_factory_clause() {
    let facts = enhanced();
    let owner = body(&facts, "appliedReturned");
    let factory = calls(
        &facts,
        owner,
        "selectedexternal/Configuration#PatienceConfig.returning().",
    );
    assert_eq!(factory.len(), 1);
    assert_eq!(factory[0].1.arguments.len, 1);
    let invocation: Vec<_> = ops(&facts, owner)
        .iter()
        .filter(|op| op.opcode == Opcode::InvokeCallback)
        .collect();
    assert_eq!(invocation.len(), 1);
    assert_eq!(invocation[0].arguments.len, 1);
    assert_eq!(invocation[0].a, factory[0].1.dest);
    let qualified = body(&facts, "qualified");
    assert!(
        calls(&facts, qualified, APPLY).is_empty(),
        "metadata supplies no missing compiler selection witness"
    );
    assert!(
        facts
            .issues
            .iter()
            .any(|i| i.symbol == qualified.symbol && i.kind == IssueKind::UnknownExecution)
    );
}

fn reject_manifest(mut edit: impl FnMut(&mut Value), expected_producer: ContentHash) {
    let owner = prepared();
    let requests = owner
        .metadata_requests(&MetadataRequestLimits::default())
        .unwrap();
    let mut value = read_json(&directory().join("admission.json"));
    value["payloads"][0]["path"] = json!(directory().join("external-signatures.semanticdb"));
    edit(&mut value);
    let temporary = tempfile::tempdir().unwrap();
    let path = temporary.path().join("admission.json");
    std::fs::write(&path, serde_json::to_vec(&value).unwrap()).unwrap();
    assert!(
        admit(
            &path,
            &requests,
            &Authority::new(),
            expected_producer,
            &ExternalMetadataLimits::default()
        )
        .is_err()
    );
}
#[test]
fn forged_context_provider_index_digest_and_outer_class_are_rejected() {
    let producer = hash(&manifest()["producer_sha256"]);
    reject_manifest(
        |v| v["bindings"][0]["context"] = json!("foreign-context"),
        producer,
    );
    reject_manifest(
        |v| v["bindings"][0]["projections"][0]["provider_index"] = json!(1),
        producer,
    );
    reject_manifest(
        |v| v["bindings"][0]["projections"][0]["provider_sha256"] = json!("11".repeat(32)),
        producer,
    );
    reject_manifest(
        |v| v["bindings"][0]["projections"][0]["outer_class_sha256"] = json!("11".repeat(32)),
        producer,
    );
    reject_manifest(
        |v| v["bindings"][0]["projections"][0]["outer_class"] = json!("selectedexternal/Calls"),
        producer,
    );
    reject_manifest(
        |v| v["bindings"][0]["projections"][0]["classpath_sha256"] = json!("11".repeat(32)),
        producer,
    );
    reject_manifest(|v| v["contexts_sha256"] = json!("11".repeat(32)), producer);
    reject_manifest(|_| {}, ContentHash([11; 32]));
}
#[test]
fn java_fallback_missing_formal_and_source_documents_are_not_signature_payloads() {
    let receipt = manifest();
    let producer = hash(&receipt["producer_sha256"]);
    for name in [
        "negative-java-language.semanticdb",
        "negative-missing-formal.semanticdb",
        "raw/META-INF/semanticdb/src/selectedexternal/Calls.scala.semanticdb",
    ] {
        let row = receipt["files"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["path"] == name)
            .unwrap();
        reject_manifest(
            |v| {
                v["payloads"][0]["path"] = json!(directory().join(name));
                v["payloads"][0]["sha256"] = row["sha256"].clone();
            },
            producer,
        );
    }
}
#[test]
fn admitted_rows_cannot_be_reused_for_another_capture_owner_or_context_file() {
    let original = prepared();
    let admitted = metadata(&original);
    let temporary = tempfile::tempdir().unwrap();
    let documents = temporary.path().join("documents.jsonl");
    let source = read_json(&directory().join("documents.jsonl"));
    // Keep one physical JSONL row while changing only insignificant whitespace.
    std::fs::write(
        &documents,
        format!("{} \n", serde_json::to_string(&source).unwrap()),
    )
    .unwrap();
    let other = prepare_capture(
        &documents,
        Some(&directory().join("syntax.jsonl")),
        &options(),
    )
    .unwrap();
    assert!(finish_capture(other, Some(admitted)).is_err());
    let contexts = temporary.path().join("compiler-contexts.json");
    let mut bytes = std::fs::read(directory().join("compiler-contexts.json")).unwrap();
    bytes.push(b' ');
    std::fs::write(&contexts, bytes).unwrap();
    let alternate = prepare_capture(
        &directory().join("documents.jsonl"),
        Some(&directory().join("syntax.jsonl")),
        &ExtractOptions {
            compiler_contexts: Some(contexts),
            ..options()
        },
    )
    .unwrap();
    let requests = alternate.metadata_requests(&Default::default()).unwrap();
    assert!(
        admit(
            &directory().join("admission.json"),
            &requests,
            &Authority::new(),
            hash(&manifest()["producer_sha256"]),
            &Default::default()
        )
        .is_err()
    );
}

#[test]
fn actual_ordered_resolver_never_skips_an_unavailable_earlier_provider() {
    let owner = prepared();
    let requests = owner.metadata_requests(&Default::default()).unwrap();
    let mut authority = Authority::new();
    let mut entries = authority.classpath.lock().unwrap().entries.clone();
    // Explicit negative authority perturbation: no available class in the
    // later real library can justify looking past this unavailable prefix.
    entries.insert(
        0,
        ClasspathEntry {
            path: directory().join("intentionally-unavailable-provider"),
            sha256: ContentHash([0; 32]),
            kind: EntryKind::Unavailable,
        },
    );
    authority.classpath = Mutex::new(
        CapturedClasspath::new(entries, Limits::default())
            .unwrap()
            .with_java_feature(Some(21))
            .unwrap(),
    );
    assert!(
        authority
            .resolve(CONTEXT, "selectedexternal/Configuration")
            .is_err()
    );
    assert!(
        admit(
            &directory().join("admission.json"),
            &requests,
            &authority,
            hash(&manifest()["producer_sha256"]),
            &Default::default()
        )
        .is_err()
    );
}
