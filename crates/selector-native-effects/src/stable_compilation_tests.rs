//! Normalized capture-protocol controls over genuine frozen JVM bytes.
//! These are admission tests, not compiler execution/provenance assertions.
use super::*;
use crate::classpath_absence::read_request;
#[allow(dead_code)]
#[path = "classpath_absence_fixture.rs"]
mod fixture;
use fixture::{Fixture, Mode};
use serde_json::{Value, json};
const OWNER: &str = "project:suite/configuration:test";
fn make(mode: Mode) -> (tempfile::TempDir, Fixture) {
    let dir = tempfile::tempdir().unwrap();
    let f = fixture::make(
        dir.path(),
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures"),
        mode,
    );
    let mut c = load(&f.contexts);
    let tool = if matches!(mode, Mode::ManifestGap) {
        f.root.join("manifest.jar")
    } else {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../fixtures/binary/fixture-stored.jar")
            .canonicalize()
            .unwrap()
    };
    c["sbt_version"] = json!("normalized");
    c["java_runtime"] = json!({"java_home":"/declared/jdk","java_version":"21","java_vendor":"normalized","os_arch":"normalized"});
    let ctx = &mut c["contexts"][1];
    ctx["base_directory"] = json!(f.root);
    ctx["source_files"] = json!([ctx["source_records"][0]["path"]]);
    ctx["resource_files"] = json!([]);
    ctx["scala_version"] = json!("2.13.18");
    ctx["scala_organization"] = json!("org.scala-lang");
    ctx["scala_instance_version"] = json!("2.13.18");
    ctx["scala_instance_jars"] = json!([tool]);
    ctx["scala_instance_inputs"] = json!([tool]);
    ctx["scalac_plugin_inputs"] = json!([]);
    ctx["scalac_options"] = json!([]);
    ctx["javac_options"] = json!([]);
    ctx["java_home"] = Value::Null;
    ctx["java_options"] = json!([]);
    ctx["fork"] = json!(false);
    let objects = c["input_objects"].as_array_mut().unwrap();
    if !objects.iter().any(|o| o["path"] == json!(tool)) {
        let mut pin = fixture::pin(&tool);
        pin["kind"] = json!("file");
        objects.push(pin);
    }
    save(&f, &c);
    (dir, f)
}
fn load(p: &Path) -> Value {
    serde_json::from_slice(&std::fs::read(p).unwrap()).unwrap()
}
fn save(f: &Fixture, c: &Value) {
    std::fs::write(&f.contexts, serde_json::to_vec(c).unwrap()).unwrap();
    let mut r = load(&f.request);
    for side in ["base", "head"] {
        r[side]["contexts"] = fixture::pin(&f.contexts);
    }
    std::fs::write(&f.request, serde_json::to_vec(&r).unwrap()).unwrap();
}
fn run(f: &Fixture) -> Result<(Checked, PhysicalInputs), Denial> {
    let r = read_request(&f.request).unwrap();
    let p = VerifiedProvider::admit_inventory(&r.base).unwrap();
    let capture: Capture = serde_json::from_value(load(&f.contexts)).unwrap();
    let mut inputs = PhysicalInputs::default();
    let requested = ["changed/Fixture.java".into()];
    let owners = requested_owner_union(&[(&capture, &p)], &requested, &mut inputs)?;
    let checked = check(&capture, &p, OWNER, &requested, &owners, &mut inputs)?;
    Ok((checked, inputs))
}

#[test]
fn one_sided_source_keeps_its_opposite_owner_in_the_compilation_boundary() {
    let (_bd, b) = make(Mode::CompileOnly);
    let (_hd, h) = make(Mode::Absent);
    let mut capture = load(&b.contexts);
    capture["source_to_contexts"]
        .as_object_mut()
        .unwrap()
        .remove("changed/Fixture.java");
    capture["contexts"][0]["source_records"] = json!([]);
    save(&b, &capture);
    let path = b.root.join("changed/Fixture.java");
    std::fs::remove_file(&path).unwrap();
    let br = read_request(&b.request).unwrap();
    let hr = read_request(&h.request).unwrap();
    let bp = VerifiedProvider::admit_inventory(&br.base).unwrap();
    let hp = VerifiedProvider::admit_inventory(&hr.head).unwrap();
    let before: Capture = serde_json::from_value(load(&b.contexts)).unwrap();
    let after: Capture = serde_json::from_value(load(&h.contexts)).unwrap();
    let requested = ["changed/Fixture.java".into()];
    let mut pins = PhysicalInputs::default();
    let sides = [(&before, &bp), (&after, &hp)];
    let owners = requested_owner_union(&sides, &requested, &mut pins).unwrap();
    assert!(owners.contains("project:changed/configuration:compile"));
    assert!(pins.absent.contains(&path));
    assert!(matches!(
        check(&before, &bp, OWNER, &requested, &owners, &mut pins),
        Err(Denial::RequestedDependency)
    ));
    check(&after, &hp, OWNER, &requested, &owners, &mut pins).unwrap();
    std::fs::write(path, b"appeared").unwrap();
    assert!(pins.revalidate().is_err());
    assert!(matches!(
        requested_owner_union(&sides, &requested, &mut pins),
        Err(Denial::SourceAuthority)
    ));
}
#[test]
fn exact_declared_inputs_are_relocation_stable_and_settings_are_not_ignored() {
    let (_bd, b) = make(Mode::Absent);
    let (_hd, h) = make(Mode::Absent);
    let (bc, pins) = run(&b).unwrap();
    let (hc, _) = run(&h).unwrap();
    assert_eq!(bc.digest, hc.digest);
    assert_eq!(bc.sources, 1);
    pins.revalidate().unwrap();
    let mut c = load(&h.contexts);
    c["contexts"][1]["scalac_options"] = json!(["-deprecation"]);
    save(&h, &c);
    assert_ne!(bc.digest, run(&h).unwrap().0.digest);
    c["contexts"][1]["fork"] = Value::Null;
    save(&h, &c);
    assert!(matches!(run(&h), Err(Denial::MissingMetadata)));
}
#[test]
fn unbound_compiler_loader_inputs_and_argument_files_decline() {
    for option in [
        "@options.txt",
        "-J@vm.txt",
        "-Xpluginsdir:/unbound",
        "-Xpluginsdir=/unbound",
        "-Ymacro-classpath:/unbound",
        "--processor-module-path=/unbound",
        "-Ybackend-plugin:/unbound",
    ] {
        assert!(unsupported_option(option), "{option}");
    }
    let (_dir, f) = make(Mode::Absent);
    for option in ["@options.txt", "-Xpluginsdir:/unbound"] {
        let mut c = load(&f.contexts);
        c["contexts"][1]["scalac_options"] = json!([option]);
        save(&f, &c);
        assert!(matches!(run(&f), Err(Denial::UnsupportedOptions)));
    }
    assert!(!unsupported_option("-Xplugin:/exact/pinned.jar"));
    assert!(!unsupported_option("-deprecation"));
}
#[test]
fn manifest_absence_is_pinned_and_an_existing_unrecorded_sibling_declines() {
    let (_dir, f) = make(Mode::ManifestGap);
    let (_, inputs) = run(&f).unwrap();
    let absent = f.root.join("optional.jar");
    assert!(inputs.absent.contains(&absent));
    inputs.revalidate().unwrap();
    std::fs::write(&absent, b"appeared").unwrap();
    assert!(inputs.revalidate().is_err());
    assert!(matches!(run(&f), Err(Denial::InputBinding)));
}
#[test]
fn complete_rosters_requested_dependencies_and_exact_source_binding_are_required() {
    let (_dir, mut f) = make(Mode::Absent);
    let original = load(&f.contexts);
    let mut c = original.clone();
    c["contexts"][1]["source_files"] = json!([]);
    save(&f, &c);
    assert!(matches!(run(&f), Err(Denial::MissingMetadata)));
    let mut c = original.clone();
    let mut requested = c["contexts"][0]["full_classpath"][0].clone();
    requested["index"] = json!(0);
    c["contexts"][1]["dependency_classpath"] = json!([requested]);
    save(&f, &c);
    assert!(matches!(run(&f), Err(Denial::RequestedDependency)));
    save(&f, &original);
    let r = read_request(&f.request).unwrap();
    let bp = VerifiedProvider::admit_inventory(&r.base).unwrap();
    let hp = VerifiedProvider::admit_inventory(&r.head).unwrap();
    f.facts.files[1].source_hash = ContentHash([42; 32]);
    let out = issue(
        Side {
            facts: &f.facts,
            provider: &bp,
            candidates: &[FileId(1)],
        },
        Side {
            facts: &f.facts,
            provider: &hp,
            candidates: &[FileId(1)],
        },
        &["changed/Fixture.java".into()],
        SelectionContract::owning_test_classpath_with_compilation(),
    )
    .unwrap();
    assert!(out.base().is_empty());
    assert_eq!(out.denials()[0].reason, Denial::SourceAuthority);
}
#[test]
fn requested_sources_are_never_issued_compilation_stability_rows() {
    let (_dir, f) = make(Mode::Absent);
    let r = read_request(&f.request).unwrap();
    let bp = VerifiedProvider::admit_inventory(&r.base).unwrap();
    let hp = VerifiedProvider::admit_inventory(&r.head).unwrap();
    let out = issue(
        Side {
            facts: &f.facts,
            provider: &bp,
            candidates: &[FileId(0), FileId(1)],
        },
        Side {
            facts: &f.facts,
            provider: &hp,
            candidates: &[FileId(0), FileId(1)],
        },
        &["changed/Fixture.java".into()],
        SelectionContract::owning_test_classpath_with_compilation(),
    )
    .unwrap();
    assert_eq!(out.base().len(), 1);
    assert_eq!(out.base()[0].file, FileId(1));
    assert_eq!(out.head()[0].paired_identity, out.base()[0].paired_identity);
    out.revalidate().unwrap();
}

#[test]
fn renamed_compiler_archives_still_bind_manifest_dependencies() {
    let (_md, manifest) = make(Mode::ManifestGap);
    let (_dir, f) = make(Mode::Absent);
    let tool = f.root.join("compiler.data");
    std::fs::copy(manifest.root.join("manifest.jar"), &tool).unwrap();
    let mut c = load(&f.contexts);
    c["contexts"][1]["scala_instance_jars"] = json!([tool]);
    c["contexts"][1]["scala_instance_inputs"] = json!([tool]);
    let mut object = fixture::pin(&tool);
    object["kind"] = json!("file");
    c["input_objects"].as_array_mut().unwrap().push(object);
    save(&f, &c);
    let (_, pins) = run(&f).unwrap();
    let sibling = f.root.join("optional.jar");
    assert!(pins.absent.contains(&sibling));
    std::fs::write(&sibling, b"unrecorded compiler dependency").unwrap();
    assert!(pins.revalidate().is_err());
    assert!(matches!(run(&f), Err(Denial::InputBinding)));
}

#[test]
fn multi_release_compiler_archives_use_only_the_admitted_provider_feature() {
    let (_dir, f) = make(Mode::Absent);
    let tool = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../fixtures/multi-release/multi-release.jar")
        .canonicalize()
        .unwrap();
    let pin = fixture::pin(&tool);
    let digest = ContentHash::from_hex(pin["sha256"].as_str().unwrap()).unwrap();
    assert!(manifest_targets(&tool, digest, None).is_err());
    assert!(
        manifest_targets(&tool, digest, Some(21))
            .unwrap()
            .is_empty()
    );
    let mut c = load(&f.contexts);
    c["contexts"][1]["scala_instance_jars"] = json!([tool]);
    c["contexts"][1]["scala_instance_inputs"] = json!([tool]);
    let mut object = pin;
    object["kind"] = json!("file");
    c["input_objects"].as_array_mut().unwrap().push(object);
    save(&f, &c);
    // The fixture map admits feature21. The issuer forwards that authority;
    // neither the current host JVM nor a hardcoded fallback supplies it.
    run(&f).unwrap().1.revalidate().unwrap();
}
