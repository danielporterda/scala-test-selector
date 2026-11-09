//! Normalized authority-protocol controls over genuine frozen JVM class bytes.
//! These rows do not claim original compiler discovery or runtime execution.
use super::*;
#[allow(dead_code)]
#[path = "classpath_absence_fixture.rs"]
mod fixture;
use fixture::{Fixture, Mode};
use serde_json::{Value, json};

fn make(mode: Mode) -> (tempfile::TempDir, Fixture) {
    let dir = tempfile::tempdir().unwrap();
    let f = fixture::make(
        dir.path(),
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures"),
        mode,
    );
    (dir, f)
}
fn run(f: &Fixture) -> Result<Issued, Error> {
    let r = read_request(&f.request)?;
    let mut provider = VerifiedProvider::admit_inventory(&r.base)?;
    issue(
        &f.facts,
        &mut provider,
        &r.base_catalogue,
        &[f.changed],
        &[f.suite],
        SelectionContract::owning_test_classpath(),
        Limits::default(),
    )
}
fn json(path: &Path) -> Value {
    serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap()
}
fn write(path: &Path, value: &Value) {
    std::fs::write(path, serde_json::to_vec(value).unwrap()).unwrap();
}
fn reseal(f: &Fixture) {
    let mut r = json(&f.request);
    for side in ["base", "head"] {
        r[side]["contexts"] = fixture::pin(&f.contexts);
        r[side]["binary_map"] = fixture::pin(&f.map);
    }
    r["base_catalogue"] = fixture::pin(&f.catalogue);
    r["head_catalogue"] = fixture::pin(&f.catalogue);
    write(&f.request, &r);
}

fn make_test_product(f: &mut Fixture, source_present: bool, stale: bool) {
    let before = "project:changed/configuration:compile";
    let after = "project:changed/configuration:test";
    for p in [&f.contexts, &f.map] {
        let raw = std::fs::read_to_string(p).unwrap().replace(before, after);
        std::fs::write(p, raw).unwrap();
    }
    let mut capture = json(&f.contexts);
    capture["contexts"][0]["configuration"] = json!("test");
    let ctx = f.facts.files[f.changed.index()].context;
    let start = f.facts.strings.bytes.len() as u64;
    f.facts.strings.bytes.extend_from_slice(after.as_bytes());
    f.facts.strings.entries[ctx.index()] = selector_facts::TextRange {
        start,
        len: after.len() as u32,
    };
    if !source_present {
        let old_source = f.root.join("changed/Fixture.java");
        let other_source = f.root.join("changed/Another.java");
        std::fs::rename(&old_source, &other_source).unwrap();
        let raw = "changed/Another.java";
        let path = f.facts.files[f.changed.index()].path;
        let start = f.facts.strings.bytes.len() as u64;
        f.facts.strings.bytes.extend_from_slice(raw.as_bytes());
        f.facts.strings.entries[path.index()] = selector_facts::TextRange {
            start,
            len: raw.len() as u32,
        };
        capture["source_to_contexts"]
            .as_object_mut()
            .unwrap()
            .remove("changed/Fixture.java");
        capture["source_to_contexts"][raw] = json!([after]);
        let record = &mut capture["contexts"][0]["source_records"][0];
        record["repo_relative_path"] = json!(raw);
        record["path"] = json!(other_source);
        record["input_object"] = json!(other_source);
        capture["input_objects"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|o| o["path"] == json!(old_source))
            .unwrap()["path"] = json!(other_source);
        if !stale {
            let product = f.root.join("changed-classes");
            let class = product.join("admissioncase/Getter.class");
            let bytes = std::fs::read(&class).unwrap();
            let mut bytes = bytes.to_vec();
            let at = bytes
                .windows(12)
                .position(|w| w == b"Fixture.java")
                .unwrap();
            bytes[at..at + 12].copy_from_slice(b"Another.java");
            std::fs::write(&class, &bytes).unwrap();
            let row = json!([{"path":"admissioncase/Getter.class","bytes":bytes.len(),"sha256":hash(&bytes).to_string()}]);
            let directory_hash = hash(&serde_json::to_vec(&row).unwrap()).to_string();
            let old_hash = capture["contexts"][0]["exported_products"][0]["sha256"]
                .as_str()
                .unwrap()
                .to_owned();
            capture =
                serde_json::from_str(&capture.to_string().replace(&old_hash, &directory_hash))
                    .unwrap();
            let map = std::fs::read_to_string(&f.map)
                .unwrap()
                .replace(&old_hash, &directory_hash);
            std::fs::write(&f.map, map).unwrap();
        }
    }
    write(&f.contexts, &capture);
    reseal(f);
}

fn issue_added_test(base: &Fixture, head: &Fixture) -> Result<(Issued, Issued), Error> {
    let br = read_request(&base.request)?;
    let hr = read_request(&head.request)?;
    let mut bp = VerifiedProvider::admit_inventory(&br.base)?;
    let mut hp = VerifiedProvider::admit_inventory(&hr.head)?;
    issue_paired(
        Side {
            facts: &base.facts,
            provider: &mut bp,
            catalogue: &br.base_catalogue,
            source_files: &[],
            suites: &[base.suite],
        },
        Side {
            facts: &head.facts,
            provider: &mut hp,
            catalogue: &hr.head_catalogue,
            source_files: &[head.changed],
            suites: &[head.suite],
        },
        &["changed/Fixture.java".into()],
        SelectionContract::owning_test_classpath(),
        Limits::default(),
    )
}

#[test]
fn one_sided_source_requires_physical_absence_and_a_clean_owner_output() {
    let (_base_dir, mut base) = make(Mode::Absent);
    let (_head_dir, mut head) = make(Mode::Absent);
    make_test_product(&mut base, false, false);
    make_test_product(&mut head, true, false);
    let (b, h) = issue_added_test(&base, &head).unwrap();
    assert_eq!(b.absent_sources()[0].path, "changed/Fixture.java");
    assert_eq!(b.absent_sources()[0].opposite_facts, h.facts_identity());
    assert_eq!(b.suites().len(), 1);
    assert_eq!(h.suites().len(), 1);
    b.revalidate().unwrap();
    std::fs::write(base.root.join("changed/Fixture.java"), b"reappeared").unwrap();
    assert!(b.revalidate().is_err());
    assert!(issue_added_test(&base, &head).is_err());

    let (_stale_dir, mut stale) = make(Mode::Absent);
    make_test_product(&mut stale, false, true);
    assert!(matches!(
        issue_added_test(&stale, &head),
        Err(Error::Invalid(
            "one-sided test output contains stale source"
        ))
    ));

    let (_repack_dir, mut repack) = make(Mode::Alternate);
    make_test_product(&mut repack, false, false);
    let (b, h) = issue_added_test(&repack, &head).unwrap();
    assert_eq!(b.denials()[0].reason, Denial::CompileDependencyPresent);
    assert!(b.suites().is_empty());
    assert_eq!(h.suites().len(), 1);
}

#[test]
fn exact_absence_and_known_other_source_products_are_bound_and_revalidated() {
    for mode in [Mode::Absent, Mode::KnownOtherSource] {
        let (_dir, f) = make(mode);
        let issued = run(&f).unwrap();
        assert_eq!(issued.sources().len(), 1);
        assert_eq!(issued.sources()[0].file, f.changed);
        assert_eq!(issued.sources()[0].product_count, 1);
        assert_eq!(issued.suites().len(), 1);
        assert!(issued.denials().is_empty());
        assert_ne!(issued.identity(), ContentHash::default());
        assert_eq!(issued.facts_identity(), f.facts.identity);
        assert_eq!(
            issued.suites()[0].source_products_identity,
            issued.source_products_identity()
        );
        issued.revalidate().unwrap();
        assert_eq!(run(&f).unwrap().identity(), issued.identity());
        std::fs::write(f.root.join("changed-classes/new-resource"), b"changed").unwrap();
        assert!(issued.revalidate().is_err());
    }
}

#[test]
fn direct_alternate_compile_only_and_unattributed_products_never_issue_absence() {
    for mode in [
        Mode::Present,
        Mode::Alternate,
        Mode::CompileOnly,
        Mode::MissingSource,
    ] {
        let (_dir, f) = make(mode);
        let issued = run(&f).unwrap();
        assert!(issued.suites().is_empty());
        assert_eq!(issued.denials().len(), 1);
        assert!(matches!(
            issued.denials()[0].reason,
            Denial::CompileDependencyPresent | Denial::ClassPresent | Denial::ProductPresent
        ));
    }
}

/// Stored ZIP with one genuine class. This avoids compiler/JVM/tool execution.
fn one_class_jar(path: &Path, name: &[u8], body: &[u8]) {
    let mut crc = !0u32;
    for &b in body {
        crc ^= b as u32;
        for _ in 0..8 {
            crc = (crc >> 1) ^ if crc & 1 != 0 { 0xedb88320 } else { 0 };
        }
    }
    crc = !crc;
    let mut out = Vec::new();
    let u16le = |o: &mut Vec<u8>, v: u16| o.extend(v.to_le_bytes());
    let u32le = |o: &mut Vec<u8>, v: u32| o.extend(v.to_le_bytes());
    u32le(&mut out, 0x04034b50);
    for n in [20, 0, 0, 0, 0] {
        u16le(&mut out, n);
    }
    u32le(&mut out, crc);
    u32le(&mut out, body.len() as u32);
    u32le(&mut out, body.len() as u32);
    u16le(&mut out, name.len() as u16);
    u16le(&mut out, 0);
    out.extend(name);
    out.extend(body);
    let offset = out.len() as u32;
    u32le(&mut out, 0x02014b50);
    for n in [20, 20, 0, 0, 0, 0] {
        u16le(&mut out, n);
    }
    u32le(&mut out, crc);
    u32le(&mut out, body.len() as u32);
    u32le(&mut out, body.len() as u32);
    for n in [name.len() as u16, 0, 0, 0, 0] {
        u16le(&mut out, n);
    }
    u32le(&mut out, 0);
    u32le(&mut out, 0);
    out.extend(name);
    let size = out.len() as u32 - offset;
    u32le(&mut out, 0x06054b50);
    for n in [0, 0, 1, 1] {
        u16le(&mut out, n);
    }
    u32le(&mut out, size);
    u32le(&mut out, offset);
    u16le(&mut out, 0);
    std::fs::write(path, out).unwrap();
}

#[test]
fn nonproject_archives_use_all_owner_names_even_for_another_source_file() {
    for (compile_only, false_origin) in [(false, false), (true, false), (false, true)] {
        let (_dir, f) = make(Mode::KnownOtherSource);
        assert_eq!(run(&f).unwrap().suites().len(), 1);
        let jar = f.root.join("repackaged.jar");
        let class =
            std::fs::read(f.root.join("suite-classes/admissioncase/Fixture.class")).unwrap();
        one_class_jar(&jar, b"admissioncase/Fixture.class", &class);
        let p = fixture::pin(&jar);
        let mut capture = json(&f.contexts);
        let mut object = p.clone();
        object["kind"] = json!("file");
        capture["input_objects"]
            .as_array_mut()
            .unwrap()
            .push(object);
        let cp = |n| json!({"index":n,"path":jar,"sha256":p["sha256"],"project_output_origins":if false_origin {json!([{"context_id":"project:suite/configuration:test"}])}else{json!([])}});
        // Make the compile-only archive independently admitted by the native
        // provider without making it a runtime member of this test context.
        capture["contexts"][0]["full_classpath"]
            .as_array_mut()
            .unwrap()
            .push(cp(1));
        if !compile_only {
            capture["contexts"][1]["full_classpath"]
                .as_array_mut()
                .unwrap()
                .push(cp(1));
        }
        capture["contexts"][1]["dependency_classpath"]
            .as_array_mut()
            .unwrap()
            .push(cp(1));
        write(&f.contexts, &capture);
        let mut map = json(&f.map);
        let entry = json!({"path":jar,"sha256":p["sha256"],"kind":"jar"});
        map["contexts"][0]["entries"]
            .as_array_mut()
            .unwrap()
            .push(entry.clone());
        if !compile_only {
            map["contexts"][1]["entries"]
                .as_array_mut()
                .unwrap()
                .push(entry);
        }
        write(&f.map, &map);
        reseal(&f);
        let issued = run(&f).unwrap();
        assert!(issued.suites().is_empty());
        assert_eq!(issued.denials()[0].reason, Denial::CompileDependencyPresent);
    }
}

#[test]
fn contract_ownership_and_catalogue_are_required_not_caller_claims() {
    let (_dir, f) = make(Mode::Absent);
    let r = read_request(&f.request).unwrap();
    let mut provider = VerifiedProvider::admit(&r.base, None).unwrap();
    assert!(
        issue(
            &f.facts,
            &mut provider,
            &r.base_catalogue,
            &[f.changed],
            &[f.suite],
            SelectionContract::current(SuiteSemantics::Independent),
            Limits::default()
        )
        .is_err()
    );
    let mut capture = json(&f.contexts);
    capture["source_to_contexts"]["changed/Fixture.java"] = json!(["unknown-context"]);
    write(&f.contexts, &capture);
    reseal(&f);
    assert!(run(&f).is_err());
    let (_dir, f) = make(Mode::Absent);
    let mut catalogue = json(&f.catalogue);
    catalogue["suites"][0]["owning_context_ids"] = json!(["project:changed/configuration:compile"]);
    write(&f.catalogue, &catalogue);
    reseal(&f);
    let issued = run(&f).unwrap();
    assert!(issued.suites().is_empty());
    assert_eq!(issued.denials()[0].reason, Denial::CatalogueOwner);
}

#[test]
fn runtime_scope_is_distinct_from_the_compilation_absence_certificate() {
    fn replay(f: &Fixture) -> RuntimeScope {
        let r = read_request(&f.request).unwrap();
        let mut provider = VerifiedProvider::admit_inventory(&r.base).unwrap();
        issue_runtime_scope(
            Side {
                facts: &f.facts,
                provider: &mut provider,
                catalogue: &r.base_catalogue,
                source_files: &[f.changed],
                suites: &[f.suite],
            },
            SelectionContract::owning_test_classpath(),
            Limits::default(),
        )
        .unwrap()
    }
    let (_dir, f) = make(Mode::Absent);
    let mut capture = json(&f.contexts);
    capture["contexts"][1]["dependency_classpath"][0]["project_output_origins"] =
        json!([{"context_id":"unknown-producer"}]);
    write(&f.contexts, &capture);
    reseal(&f);
    let strict = run(&f).unwrap();
    assert_eq!(strict.denials()[0].reason, Denial::UnknownCompileOwner);
    assert!(strict.suites().is_empty());
    let scope = replay(&f);
    assert_ne!(scope.identity(), strict.identity());
    assert_eq!(scope.suites(), &[f.suite]);
    assert_eq!(scope.sources()[0].file, f.changed);
    scope.revalidate().unwrap();
    let (_present_dir, present) = make(Mode::Present);
    let scope = replay(&present);
    assert!(scope.suites().is_empty());
    assert_eq!(scope.denials()[0].reason, Denial::ProductPresent);
}

#[test]
fn compile_producer_source_and_unknown_origin_fail_closed() {
    for unknown in [false, true] {
        let (_dir, f) = make(Mode::Absent);
        let mut capture = json(&f.contexts);
        if unknown {
            capture["contexts"][1]["dependency_classpath"][0]["project_output_origins"] =
                json!([{"context_id":"unknown-producer"}]);
        } else {
            let source = capture["contexts"][0]["source_records"][0].clone();
            capture["contexts"][1]["source_records"]
                .as_array_mut()
                .unwrap()
                .push(source);
        }
        write(&f.contexts, &capture);
        reseal(&f);
        if unknown {
            let issued = run(&f).unwrap();
            assert!(issued.suites().is_empty());
            assert_eq!(issued.denials()[0].reason, Denial::UnknownCompileOwner);
        } else {
            // The complete source_to_contexts inventory no longer agrees with
            // the new source record, before any absence row can be issued.
            assert!(run(&f).is_err());
        }
    }
}

#[test]
fn manifest_negative_inputs_are_pinned_and_existing_unadmitted_targets_deny() {
    let (_dir, f) = make(Mode::ManifestGap);
    let issued = run(&f).unwrap();
    assert_eq!(issued.suites().len(), 1);
    let missing = f.root.join("optional.jar");
    assert!(issued.inputs().absent.contains(&missing));
    issued.revalidate().unwrap();
    std::fs::write(&missing, b"new provider").unwrap();
    assert!(issued.revalidate().is_err());
    let after = run(&f).unwrap();
    assert!(after.suites().is_empty());
    assert_eq!(after.denials()[0].reason, Denial::UncapturedManifestTarget);
}

#[test]
fn bounded_inventory_and_unsealed_physical_inputs_cannot_issue() {
    let (_dir, f) = make(Mode::Absent);
    let r = read_request(&f.request).unwrap();
    let mut provider = VerifiedProvider::admit(&r.base, None).unwrap();
    assert!(matches!(
        issue(
            &f.facts,
            &mut provider,
            &r.base_catalogue,
            &[f.changed],
            &[f.suite],
            SelectionContract::owning_test_classpath(),
            Limits {
                inventory_names: 0,
                ..Limits::default()
            }
        ),
        Err(Error::Budget)
    ));
    std::fs::write(f.root.join("suite-classes/late"), b"late").unwrap();
    assert!(run(&f).is_err());
}

#[test]
fn present_products_are_denied_before_root_class_cache_or_compile_scans() {
    let (_dir, f) = make(Mode::Present);
    let mut request = read_request(&f.request).unwrap();
    request.base.limits.cached_class_bytes = 0;
    request.base.limits.cached_classes = 0;
    let mut provider = VerifiedProvider::admit_inventory(&request.base).unwrap();
    let issued = issue(
        &f.facts,
        &mut provider,
        &request.base_catalogue,
        &[f.changed],
        &[f.suite],
        SelectionContract::owning_test_classpath(),
        Limits::default(),
    )
    .unwrap();
    assert!(issued.suites().is_empty());
    assert_eq!(issued.denials()[0].reason, Denial::ProductPresent);
    assert!(provider.receipt(1, "admissioncase/Fixture").is_none());
}

#[test]
fn requests_reject_unknown_evidence_and_changed_exact_pin() {
    let (_dir, f) = make(Mode::Absent);
    let mut request = json(&f.request);
    request["verified"] = json!(true);
    write(&f.request, &request);
    assert!(read_request(&f.request).is_err());
    request.as_object_mut().unwrap().remove("verified");
    request["base"]["contexts"]["sha256"] = json!("11".repeat(32));
    write(&f.request, &request);
    let r = read_request(&f.request).unwrap();
    assert!(VerifiedProvider::admit(&r.base, None).is_err());
}

fn add_text(facts: &mut FactSnapshot, value: &str) -> StrId {
    let id = StrId(facts.strings.entries.len() as u32);
    let start = facts.strings.bytes.len() as u64;
    facts.strings.bytes.extend_from_slice(value.as_bytes());
    facts.strings.entries.push(selector_facts::TextRange {
        start,
        len: value.len() as u32,
    });
    id
}
fn native_file(f: &mut Fixture, path: &str, context: StrId, class_hash: ContentHash) -> FileId {
    let path = add_text(&mut f.facts, path);
    let id = FileId(f.facts.files.len() as u32);
    f.facts.files.push(selector_facts::FileRecord {
        path,
        source: StrId::NONE,
        context,
        revision: f.facts.revision,
        source_hash: class_hash,
        flags: FILE_BINARY_SOURCE,
    });
    id
}

#[test]
fn exact_product_files_include_duplicates_and_both_captured_and_relocated_paths_only() {
    let (_dir, mut f) = make(Mode::KnownOtherSource);
    // Relocate the original captured root by metadata only. The provider must
    // still verify the genuine bytes under the declared physical relocation.
    let raw_root = "/normalized-original-source";
    fn relocate(v: &mut Value, from: &str, to: &str) {
        match v {
            Value::String(s) => {
                if let Some(tail) = s.strip_prefix(from) {
                    *s = format!("{to}{tail}");
                }
            }
            Value::Array(a) => {
                for v in a {
                    relocate(v, from, to);
                }
            }
            Value::Object(o) => {
                for v in o.values_mut() {
                    relocate(v, from, to);
                }
            }
            _ => (),
        }
    }
    let mut capture = json(&f.contexts);
    relocate(&mut capture, f.root.to_str().unwrap(), raw_root);
    write(&f.contexts, &capture);
    reseal(&f);
    let context = f.facts.files[f.changed.index()].context;
    let foreign = f.facts.files[1].context;
    let class_hash =
        hash(&std::fs::read(f.root.join("changed-classes/admissioncase/Getter.class")).unwrap());
    let physical = format!(
        "{}/changed-classes!/admissioncase/Getter.class",
        f.root.display()
    );
    let a = native_file(&mut f, &physical, context, class_hash);
    let b = native_file(&mut f, &physical, context, class_hash);
    let c = native_file(
        &mut f,
        &format!("{raw_root}/changed-classes!/admissioncase/Getter.class"),
        context,
        class_hash,
    );
    native_file(&mut f, &physical, foreign, class_hash);
    native_file(&mut f, &physical, context, ContentHash([19; 32]));
    native_file(
        &mut f,
        "/unowned/output!/admissioncase/Getter.class",
        context,
        class_hash,
    );
    let other_hash =
        hash(&std::fs::read(f.root.join("changed-classes/admissioncase/Fixture.class")).unwrap());
    let other_path = format!(
        "{}/changed-classes!/admissioncase/Fixture.class",
        f.root.display()
    );
    native_file(&mut f, &other_path, context, other_hash);
    f.facts.identity =
        selector_facts::codec::write(&f.root.join("product-file-facts.bin"), &f.facts).unwrap();
    let issued = run(&f).unwrap();
    assert_eq!(
        issued
            .product_files()
            .iter()
            .map(|r| r.file)
            .collect::<Vec<_>>(),
        [a, b, c]
    );
    assert!(
        issued
            .product_files()
            .iter()
            .all(|r| r.source_file == f.changed
                && r.owner_context == context
                && r.class_sha256 == class_hash)
    );
    assert_eq!(issued.suites().len(), 1);
    issued.revalidate().unwrap();
}

#[test]
fn sourcefile_absence_overapprox_never_authorizes_ambiguous_or_unknown_native_seeds() {
    for ambiguous in [false, true] {
        let (_dir, mut f) = make(if ambiguous {
            Mode::Absent
        } else {
            Mode::MissingSource
        });
        let context = f.facts.files[f.changed.index()].context;
        let class_name = if ambiguous { "Getter" } else { "Fixture" };
        let class_hash = hash(
            &std::fs::read(
                f.root
                    .join(format!("changed-classes/admissioncase/{class_name}.class")),
            )
            .unwrap(),
        );
        let class_path = format!(
            "{}/changed-classes!/admissioncase/{class_name}.class",
            f.root.display()
        );
        native_file(&mut f, &class_path, context, class_hash);
        if ambiguous {
            let other = f.root.join("other/Fixture.java");
            std::fs::create_dir_all(other.parent().unwrap()).unwrap();
            std::fs::write(&other, b"// distinct source with the same basename\n").unwrap();
            let mut capture = json(&f.contexts);
            let p = fixture::pin(&other);
            let mut object = p.clone();
            object["kind"] = json!("file");
            capture["input_objects"]
                .as_array_mut()
                .unwrap()
                .push(object);
            capture["contexts"][0]["source_records"].as_array_mut().unwrap().push(json!({"path":other,"input_object":other,"repo_relative_path":"other/Fixture.java","sha256":p["sha256"]}));
            capture["source_to_contexts"]["other/Fixture.java"] =
                json!(["project:changed/configuration:compile"]);
            write(&f.contexts, &capture);
            reseal(&f);
        }
        f.facts.identity =
            selector_facts::codec::write(&f.root.join("native-seed-facts.bin"), &f.facts).unwrap();
        let issued = run(&f).unwrap();
        assert!(issued.product_files().is_empty());
    }
}
