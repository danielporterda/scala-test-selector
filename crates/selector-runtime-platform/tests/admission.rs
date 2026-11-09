//! Physical-admission controls. These fixture image files are deliberately not
//! executable Java images; no test infers VM semantics from admission alone.
use selector_models::binary::{CapturedClasspath, ClassLookup, Limits};
use selector_runtime_platform::{PlatformOptions, admit};
use selector_types::ContentHash;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::fs;
use std::path::Path;

struct Fixture {
    _directory: tempfile::TempDir,
    options: PlatformOptions,
    manifest: Value,
    capture: Value,
    inventory: Value,
}

fn file(path: &Path) -> Value {
    let bytes = fs::read(path).unwrap();
    json!({"path":path,"bytes":bytes.len(),"sha256":format!("{:x}",Sha256::digest(&bytes))})
}

impl Fixture {
    fn new() -> Self {
        let directory = tempfile::tempdir().unwrap();
        let root = fs::canonicalize(directory.path()).unwrap();
        let home = root.join("fixture-home");
        fs::create_dir_all(home.join("bin")).unwrap();
        fs::create_dir_all(home.join("lib")).unwrap();
        for (suffix, bytes) in [
            ("bin/java", b"physical fixture launcher".as_slice()),
            ("release", b"physical fixture release".as_slice()),
            ("lib/modules", b"physical fixture modules".as_slice()),
        ] {
            fs::write(home.join(suffix), bytes).unwrap();
        }
        let archive = root.join("classes.jar");
        fs::write(
            &archive,
            include_bytes!("../../../fixtures/native-finite-effects/bytecode.jar"),
        )
        .unwrap();
        let reference = file(&archive);
        let entry = selector_models::binary::ClasspathEntry {
            path: archive,
            sha256: ContentHash::from_hex(reference["sha256"].as_str().unwrap()).unwrap(),
            kind: selector_models::binary::EntryKind::Jar,
        };
        let mut loader = CapturedClasspath::new(vec![entry], Limits::default())
            .unwrap()
            .with_java_feature(Some(21))
            .unwrap();
        let inventory = Value::Array(
            loader
                .class_names(0)
                .unwrap()
                .into_iter()
                .map(|owner| {
                    let ClassLookup::Found(found) = loader.lookup(&owner).unwrap() else {
                        panic!("fixture class unavailable")
                    };
                    json!({"owner":owner,"bytes":found.bytes.len(),
                        "class_sha256":format!("{:x}",Sha256::digest(&found.bytes))})
                })
                .collect(),
        );
        let capture = json!({
            "schema_version":"sbt-compiler-context/v1", "errors":[],
            "java_runtime":{"java_version":"21"},
            "contexts":[{"context_id":"fixture:test","java_home":null,"java_options":[]}]
        });
        let manifest = json!({
            "schema":"selector-declared-runtime-platform/v1",
            "capture_sha256":"", "context_ids":["fixture:test"], "java_feature":21,
            "image":{"canonical_home":home,"launcher":file(&home.join("bin/java")),
                "release":file(&home.join("release")),"modules":file(&home.join("lib/modules"))},
            "java_base":{"archive":{"path":"classes.jar","bytes":reference["bytes"],
                "sha256":reference["sha256"]},"inventory":{}},
            "producer_sha256":ContentHash([7;32]).to_string(),
            "policy":{"authority":"new_declared_runtime","module":"java.base",
                "complete_inventory":true,"historical_compiler_image_proven":false,
                "runtime_isolation_proven":false,
                "lookup":"jrt_filesystem_no_reflective_target_loading","java_options":[],
                "environment":{"JAVA_TOOL_OPTIONS":null,"JDK_JAVA_OPTIONS":null,"_JAVA_OPTIONS":null}}
        });
        let mut result = Self {
            _directory: directory,
            options: PlatformOptions {
                manifest: root.join("manifest.json"),
                contexts: root.join("contexts.json"),
                producer: ContentHash([7; 32]),
            },
            manifest,
            capture,
            inventory,
        };
        result.publish();
        result
    }

    fn publish(&mut self) {
        fs::write(
            &self.options.contexts,
            serde_json::to_vec(&self.capture).unwrap(),
        )
        .unwrap();
        self.manifest["capture_sha256"] = file(&self.options.contexts)["sha256"].clone();
        let inventory = self.options.manifest.with_file_name("inventory.json");
        fs::write(&inventory, serde_json::to_vec(&self.inventory).unwrap()).unwrap();
        let mut inventory_ref = file(&inventory);
        inventory_ref["path"] = json!("inventory.json");
        self.manifest["java_base"]["inventory"] = inventory_ref;
        fs::write(
            &self.options.manifest,
            serde_json::to_vec(&self.manifest).unwrap(),
        )
        .unwrap();
    }
}

#[test]
fn physical_membership_and_context_binding_survive_the_crate_split() {
    let fixture = Fixture::new();
    let admitted = admit(&fixture.options).unwrap();
    assert!(admitted.contains_context("fixture:test"));
    assert!(!admitted.contains_context("other:test"));
    assert_eq!(
        admitted.owners.len(),
        fixture.inventory.as_array().unwrap().len()
    );
    assert_eq!(admitted.input_files().len(), 7);
    let mut wrong_producer = fixture.options.clone();
    wrong_producer.producer = ContentHash([8; 32]);
    assert!(admit(&wrong_producer).is_err());
}

#[test]
fn repinned_inventories_cannot_hide_missing_classes_or_forge_class_bytes() {
    for mutation in 0..3 {
        let mut fixture = Fixture::new();
        match mutation {
            0 => {
                fixture.inventory.as_array_mut().unwrap().pop();
            }
            1 => {
                fixture.inventory[0]["class_sha256"] = json!(ContentHash([9; 32]).to_string());
            }
            2 => {
                fixture.inventory[0]["bytes"] = json!(1);
            }
            _ => unreachable!(),
        }
        fixture.publish(); // Deliberately renew every enclosing content hash.
        assert!(
            admit(&fixture.options).is_err(),
            "inventory mutation {mutation}"
        );
    }
}

#[test]
fn repinned_contexts_and_policy_cannot_upgrade_runtime_authority() {
    for mutation in 0..5 {
        let mut fixture = Fixture::new();
        match mutation {
            0 => {
                fixture.capture["contexts"][0]["java_home"] = json!("/unproven/compiler/home");
            }
            1 => {
                fixture.capture["contexts"][0]["java_options"] = json!(["-javaagent:unknown.jar"]);
            }
            2 => {
                let duplicate = fixture.capture["contexts"][0].clone();
                fixture.capture["contexts"]
                    .as_array_mut()
                    .unwrap()
                    .push(duplicate);
            }
            3 => {
                fixture.manifest["policy"]["runtime_isolation_proven"] = json!(true);
            }
            4 => {
                fixture.manifest["policy"]["historical_compiler_image_proven"] = json!(true);
            }
            _ => unreachable!(),
        }
        fixture.publish();
        assert!(
            admit(&fixture.options).is_err(),
            "authority mutation {mutation}"
        );
    }
}
