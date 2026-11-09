//! Labeled normalized protocol controls over genuine pinned class bytes.
use super::provider::*;
use super::*;
use selector_types::ContentHash;
use serde_json::{Value as Json, json};
use std::path::{Path, PathBuf};

struct Fixture {
    _dir: tempfile::TempDir,
    root: PathBuf,
    contexts: PathBuf,
    map: PathBuf,
}
fn pin(path: &Path) -> InputPin {
    let bytes = std::fs::read(path).unwrap();
    InputPin {
        path: path.to_owned(),
        sha256: Sha256::digest(&bytes).into(),
        bytes: bytes.len() as u64,
    }
}
fn wire_hash(path: &Path) -> String {
    ContentHash(pin(path).sha256).to_string()
}
impl Fixture {
    fn new(opaque: bool) -> Self {
        let dir = tempfile::tempdir().unwrap();
        let root = std::fs::canonicalize(dir.path()).unwrap();
        let fixtures =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/native-admission-chain");
        let library = root.join("library.jar");
        let shadow = root.join("shadow.jar");
        let gap = root.join("opaque.bin");
        std::fs::copy(fixtures.join("bytecode.jar"), &library).unwrap();
        std::fs::copy(fixtures.join("shadow.jar"), &shadow).unwrap();
        std::fs::write(&gap, b"opaque provider").unwrap();
        let first = if opaque { &gap } else { &shadow };
        let cp = |path: &Path, index: usize| json!({"index":index,"path":path,"input_object":path,"sha256":wire_hash(path)});
        let captured = json!({"schema_version":"sbt-compiler-context/v1","revision":"normalized-provider-control","source_root":root,"errors":[],"java_runtime":{"java_version":"21.0.12.1"},"contexts":[
            {"context_id":"a","full_classpath":[cp(&library,0)],"java_options":[],"java_home":null},
            {"context_id":"b","full_classpath":[cp(first,0),cp(&library,1)],"java_options":[],"java_home":null}
        ],"input_objects":([&library,&shadow,&gap].map(|path|json!({"path":path,"kind":"file","sha256":wire_hash(path),"bytes":std::fs::metadata(path).unwrap().len()})))});
        let entry =
            |path: &Path, kind: &str| json!({"path":path,"sha256":wire_hash(path),"kind":kind});
        let native = json!({"version":1,"revision":"normalized-provider-control","java_feature":21,"contexts":[
            {"id":"a","entries":[entry(&library,"jar")]},
            {"id":"b","entries":[entry(first,if opaque{"unavailable"}else{"jar"}),entry(&library,"jar")]}
        ],"types":[],"methods":[]});
        let contexts = root.join("contexts.json");
        let map = root.join("binary-map.json");
        std::fs::write(&contexts, serde_json::to_vec(&captured).unwrap()).unwrap();
        std::fs::write(&map, serde_json::to_vec(&native).unwrap()).unwrap();
        Self {
            _dir: dir,
            root,
            contexts,
            map,
        }
    }
    fn options(&self) -> ProviderOptions {
        ProviderOptions {
            contexts: pin(&self.contexts),
            binary_map: pin(&self.map),
            relocated_root: self.root.clone(),
            facts_identity: None,
            source_products_identity: None,
            platform: None,
            limits: Default::default(),
        }
    }
    fn mutate_map(&self, change: impl FnOnce(&mut Json)) {
        let mut map: Json = serde_json::from_slice(&std::fs::read(&self.map).unwrap()).unwrap();
        change(&mut map);
        std::fs::write(&self.map, serde_json::to_vec(&map).unwrap()).unwrap();
    }
}

#[test]
fn provider_selects_exact_contextual_first_bytes_and_publishes_bound_prefix_receipts() {
    let f = Fixture::new(false);
    let mut provider = VerifiedProvider::admit(&f.options(), None).unwrap();
    assert_eq!(provider.authority("a"), Some(0));
    assert_eq!(provider.authority("b"), Some(1));
    let (a, pa) = provider.resolve(0, "admissioncase/Getter").unwrap();
    let (b, pb) = provider.resolve(1, "admissioncase/Getter").unwrap();
    assert_ne!(
        pa.class_sha256, pb.class_sha256,
        "genuine shadow bytecode differs"
    );
    assert_eq!(pa.selected_entry, Some(0));
    assert_eq!(pb.selected_entry, Some(0));
    assert_eq!(pa.state, ResolutionState::Found);
    assert_eq!(pb.state, ResolutionState::Found);
    assert_ne!(pa.binding_sha256, pb.binding_sha256);
    assert_ne!(pa.provider, pb.provider);
    assert_eq!(
        binary::parse_class(a.as_ref().unwrap(), Default::default())
            .unwrap()
            .name,
        "admissioncase/Getter"
    );
    assert_eq!(
        binary::parse_class(b.as_ref().unwrap(), Default::default())
            .unwrap()
            .name,
        "admissioncase/Getter"
    );
    let (again, proof) = provider.resolve(0, "admissioncase/Getter").unwrap();
    assert!(Arc::ptr_eq(a.as_ref().unwrap(), again.as_ref().unwrap()));
    assert!(Arc::ptr_eq(&pa, &proof));
    assert!(provider.resolve(9, "admissioncase/Getter").is_err());
}

#[test]
fn opaque_prefix_never_borrows_a_later_class_and_verified_miss_is_not_empty_code() {
    let f = Fixture::new(true);
    let mut provider = VerifiedProvider::admit(&f.options(), None).unwrap();
    let (bytes, proof) = provider.resolve(1, "admissioncase/Getter").unwrap();
    assert!(bytes.is_none());
    assert_eq!(proof.state, ResolutionState::OpaquePrefix);
    assert_eq!(proof.selected_entry, None);
    let (bytes, proof) = provider.resolve(0, "not/present/Owner").unwrap();
    assert!(bytes.is_none());
    assert_eq!(proof.state, ResolutionState::VerifiedClasspathMiss);
    assert_eq!(proof.examined_prefix, 1);
    let roots = [ClassDemand {
        authority: 1,
        owner: "admissioncase/Getter",
    }];
    let output = produce(&roots, &mut provider, Default::default()).unwrap();
    assert_eq!(output.phases.len(), 1);
    assert_eq!(output.data.methods[0].top, effects::TopMask::ALL);
}

#[test]
fn resealed_map_reordering_foreign_context_hash_and_override_mismatches_fail_closed() {
    for case in 0..5 {
        let f = Fixture::new(false);
        match case {
            0 => f.mutate_map(|map| {
                map["contexts"][1]["entries"]
                    .as_array_mut()
                    .unwrap()
                    .reverse()
            }),
            1 => f.mutate_map(|map| map["contexts"][0]["id"] = json!("foreign")),
            2 => f.mutate_map(|map| {
                map["contexts"][0]["entries"][0]["sha256"] = json!(ContentHash([3; 32]).to_string())
            }),
            3 => f.mutate_map(|map| map["java_feature"] = json!(17)),
            4 => {
                let mut capture: Json =
                    serde_json::from_slice(&std::fs::read(&f.contexts).unwrap()).unwrap();
                capture["contexts"][0]["java_options"] =
                    json!(["--patch-module=java.base=elsewhere"]);
                std::fs::write(&f.contexts, serde_json::to_vec(&capture).unwrap()).unwrap();
            }
            _ => unreachable!(),
        }
        assert!(
            VerifiedProvider::admit(&f.options(), None).is_err(),
            "case{case}"
        );
    }
}

#[test]
fn captured_input_pin_and_physical_classpath_hash_are_separate_required_authorities() {
    let f = Fixture::new(false);
    let mut options = f.options();
    options.contexts.sha256 = [0; 32];
    assert!(matches!(
        VerifiedProvider::admit(&options, None),
        Err(provider::Error::Invalid("input pin hash"))
    ));
    let f = Fixture::new(false);
    let options = f.options();
    std::fs::write(f.root.join("library.jar"), b"changed").unwrap();
    assert!(matches!(
        VerifiedProvider::admit(&options, None),
        Err(provider::Error::Native(_))
    ));
    let f = Fixture::new(false);
    let mut options = f.options();
    options.source_products_identity = Some([1; 32]);
    assert!(matches!(
        VerifiedProvider::admit(&options, None),
        Err(provider::Error::Invalid("source-product capture binding"))
    ));
}

#[test]
fn native_producer_uses_verified_provider_without_turning_provider_proof_into_vm_closure() {
    let f = Fixture::new(false);
    let mut provider = VerifiedProvider::admit(&f.options(), None).unwrap();
    let roots = [ClassDemand {
        authority: 0,
        owner: "admissioncase/Getter",
    }];
    let output = produce(&roots, &mut provider, Default::default()).unwrap();
    assert!(!output.data.calls.is_empty());
    assert!(
        output
            .data
            .methods
            .iter()
            .all(|m| m.top == effects::TopMask::ALL)
    );
    assert!(output.blobs.iter().all(|b| b.binding_sha256 != [0; 32]));
    let proof = provider.receipt(0, "admissioncase/Getter").unwrap();
    assert_eq!(Some(output.blobs[0].class_sha256), proof.class_sha256);
    assert_eq!(output.blobs[0].binding_sha256, proof.binding_sha256);
}

#[test]
fn provider_cache_budgets_do_not_relabel_refusal_as_missing_class() {
    let f = Fixture::new(false);
    let mut options = f.options();
    options.limits.retained_archives = 1;
    assert!(matches!(
        VerifiedProvider::admit(&options, None),
        Err(provider::Error::Budget)
    ));
    let f = Fixture::new(false);
    let mut options = f.options();
    options.limits.cached_classes = 1;
    let mut provider = VerifiedProvider::admit(&options, None).unwrap();
    provider.resolve(0, "admissioncase/Getter").unwrap();
    assert!(matches!(
        provider.resolve(0, "admissioncase/Box"),
        Err(provider::Error::Budget)
    ));
    assert!(provider.receipt(0, "admissioncase/Box").is_none());
}

#[test]
fn inventory_provider_drops_union_payloads_but_preserves_order_hashes_and_caps() {
    let f = Fixture::new(false);
    let mut options = f.options();
    let mut ordinary = VerifiedProvider::admit(&options, None).unwrap();
    let resident = ordinary.retained_archive_bytes();
    let mut peak = 0usize;
    for entry in ordinary.classpath_entries() {
        peak = peak.max(
            binary::AdmittedEntry::admit(entry.clone(), options.limits.binary, Some(21))
                .unwrap()
                .retained_bytes(),
        );
    }
    assert!(
        resident > peak,
        "two genuine archives exceed one archive's residency"
    );
    options.limits.retained_archives = peak;
    assert!(matches!(
        VerifiedProvider::admit(&options, None),
        Err(provider::Error::Budget)
    ));
    let mut streaming = VerifiedProvider::admit_inventory(&options).unwrap();
    assert_eq!(streaming.retained_archive_bytes(), 0);
    assert_eq!(streaming.identity(), ordinary.identity());
    for (authority, owner) in [
        (0, "admissioncase/Getter"),
        (1, "admissioncase/Getter"),
        (0, "missing/Absent"),
    ] {
        let (expected, proof) = ordinary.resolve(authority, owner).unwrap();
        let (actual, streamed) = streaming.resolve(authority, owner).unwrap();
        assert_eq!(actual, expected);
        assert_eq!(streamed.state, proof.state);
        assert_eq!(streamed.selected_entry, proof.selected_entry);
        assert_eq!(streamed.examined_prefix, proof.examined_prefix);
        assert_eq!(streamed.prefix_sha256, proof.prefix_sha256);
        assert_eq!(streamed.binding_sha256, proof.binding_sha256);
    }
    assert_eq!(streaming.retained_archive_bytes(), 0);
    std::fs::write(
        f.root.join("library.jar"),
        b"changed after metadata admission",
    )
    .unwrap();
    assert!(matches!(
        streaming.resolve(0, "admissioncase/Box"),
        Err(provider::Error::Native(_))
    ));
    let f = Fixture::new(true);
    let mut streaming = VerifiedProvider::admit_inventory(&f.options()).unwrap();
    let (_, opaque) = streaming.resolve(1, "admissioncase/Getter").unwrap();
    assert_eq!(opaque.state, ResolutionState::OpaquePrefix);
    assert_eq!(opaque.selected_entry, None);
    let mut options = f.options();
    options.limits.retained_archives = 1;
    let mut streaming = VerifiedProvider::admit_inventory(&options).unwrap();
    assert!(matches!(
        streaming.resolve(0, "admissioncase/Getter"),
        Err(provider::Error::Budget)
    ));
    assert!(streaming.receipt(0, "admissioncase/Getter").is_none());
}

#[test]
fn exact_member_resolution_reuses_contextual_headers_and_never_guesses_foreign_field_owners() {
    let f = Fixture::new(false);
    let mut p = VerifiedProvider::admit(&f.options(), None).unwrap();
    let metadata = p.metadata(0, "admissioncase/Getter").unwrap().unwrap();
    let again = p.metadata(0, "admissioncase/Getter").unwrap().unwrap();
    assert!(Arc::ptr_eq(&metadata, &again));
    let field = metadata
        .fields()
        .next()
        .expect("genuine getter has backing field");
    let member = MemberRef {
        owner: metadata.name(),
        name: field.name,
        descriptor: field.descriptor,
    };
    let result = p
        .resolve_member(0, member, MemberInvocation::InstanceField, None)
        .unwrap();
    assert!(
        matches!(&result.resolution,selector_jvm_resolve::Resolution::Found(row) if row.declared_owner=="admissioncase/Getter")
    );
    let first = result as *const _;
    assert_eq!(
        first,
        p.resolve_member(0, member, MemberInvocation::InstanceField, None)
            .unwrap() as *const _
    );
    let wrong = p
        .resolve_member(0, member, MemberInvocation::StaticField, None)
        .unwrap();
    assert!(matches!(
        wrong.resolution,
        selector_jvm_resolve::Resolution::Unknown(
            selector_jvm_resolve::UnknownReason::InvocationMismatch
        )
    ));
    assert!(
        p.resolve_member(4, member, MemberInvocation::InstanceField, None)
            .is_err()
    );
}

#[test]
fn declaring_field_aliases_require_exact_contextual_resolution_and_keep_runtime_regions_separate() {
    let f = Fixture::new(false);
    let mut provider = VerifiedProvider::admit(&f.options(), None).unwrap();
    let roots = [ClassDemand {
        authority: 0,
        owner: "admissioncase/Getter",
    }];
    let output = produce(&roots, &mut provider, Default::default()).unwrap();
    let fields = resolve_declaring_fields(&output, &mut provider).unwrap();
    assert!(fields.iter().any(|row|matches!(row,FieldAuthority::Declared(row) if row.owner.as_ref()=="admissioncase/Getter" && row.authority==0 && row.class.class_sha256.is_some())));
    let mut opaque = Fixture::new(true);
    let _ = &mut opaque;
    let mut foreign = VerifiedProvider::admit(&opaque.options(), None).unwrap();
    // Consumer authority0 remains exactly library; authority1's opaque prefix
    // cannot canonicalize that symbolic storage by borrowing later bytes.
    let mut normalized = output;
    for class in &mut normalized.classes {
        class.authority = 1;
    }
    let pending = resolve_declaring_fields(&normalized, &mut foreign).unwrap();
    assert!(
        !pending
            .iter()
            .any(|row| matches!(row, FieldAuthority::Declared(_)))
    );
}
