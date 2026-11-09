use super::*;
use serde_json::json;

const CHANGED: &str = "scan/src/test/scala/ScanSuite.scala";
const ROOTS: [(&str, &str); 2] = [("app", "AppSuite"), ("scan", "ScanSuite")];
const BASE_STAMP: &[u8] = include_bytes!("../../../fixtures/native-build-stamp/base-module.class");
const HEAD_STAMP: &[u8] = include_bytes!("../../../fixtures/native-build-stamp/head-module.class");
const STAMP_FORWARDER: &[u8] =
    include_bytes!("../../../fixtures/native-build-stamp/forwarder.class");

fn write(path: &Path, bytes: &[u8]) {
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, bytes).unwrap();
}
fn snapshot(root: &Path, java: &Path, revision: &str, source: &[u8]) {
    write(&root.join(CHANGED), source);
    let mut contexts = Vec::new();
    let mut objects = Vec::new();
    let mut suites = Vec::new();
    for (owner, suite) in ROOTS {
        let context = format!("project:{owner}/configuration:test");
        let product = root.join(owner).join("test-classes");
        let member = format!("{suite}.class");
        let bytes = if owner == "scan" {
            source
        } else {
            b"same app output"
        };
        write(&product.join(&member), bytes);
        let inventory = serde_json::to_vec(&json!([{
            "bytes":bytes.len(), "path":member, "sha256":hash(bytes).to_string()
        }]))
        .unwrap();
        let digest = hash(&inventory).to_string();
        let fingerprint = json!({"type":"subclass","superclass":"org.scalatest.Suite",
                                "is_module":false,"require_no_arg_constructor":true});
        objects.push(json!({"path":product,"sha256":digest,"kind":"directory",
                            "files":1,"bytes":bytes.len()}));
        contexts.push(json!({
            "context_id":context,"configuration":"test","base_directory":root.join(owner),
            "java_home":null,"java_options":[],"fork":false,"resource_files":[],
            "full_classpath":[{"index":0,"path":product,"input_object":product,"sha256":digest}],
            "defined_tests":[{"name":suite,"fingerprint":fingerprint}],
            "source_records":if owner == "scan" {json!([{"path":root.join(CHANGED),
                "repo_relative_path":CHANGED,"sha256":hash(source).to_string()}])} else {json!([])}
        }));
        suites.push(
            json!({"suite":suite,"owning_context_ids":[context],"compiler_discovery":[
                {"context_id":context,"configuration":"test","fingerprint":fingerprint}
            ]}),
        );
    }
    let contexts = json!({"schema_version":"sbt-compiler-context/v1","revision":revision,
        "git_head_at_finalize":revision,"source_root":root,"sbt_version":"1.12.14","errors":[],
        "java_runtime":{"java_home":java,"java_version":"21.0.12"},"contexts":contexts,
        "input_objects":objects});
    let catalogue = json!({"schema_version":"compiler-ci-catalogue/v1","revision":revision,
        "complete":true,"issues":[],"suites":suites,
        "families":[{"job_id":"test","suites":["AppSuite","ScanSuite"],"test_name":"all"}]});
    write(
        &root.join("contexts.json"),
        &serde_json::to_vec(&contexts).unwrap(),
    );
    write(
        &root.join("catalogue.json"),
        &serde_json::to_vec(&catalogue).unwrap(),
    );
}
fn compare_test(base: &Path, head: &Path, repo: &Path) -> Result<TrackedTestSelection, Error> {
    compare_test_with_policy(base, head, repo, BuildStampPolicy::CompareExactly)
}

fn audit_test(base: &Path, head: &Path) -> Result<ClasspathDelta, Error> {
    audit_test_classpath_delta(
        Inputs {
            contexts: &base.join("contexts.json"),
            catalogue: &base.join("catalogue.json"),
            physical_root: base,
        },
        Inputs {
            contexts: &head.join("contexts.json"),
            catalogue: &head.join("catalogue.json"),
            physical_root: head,
        },
        "project:scan/configuration:test",
    )
}

fn compare_test_with_policy(
    base: &Path,
    head: &Path,
    repo: &Path,
    policy: BuildStampPolicy,
) -> Result<TrackedTestSelection, Error> {
    select_tracked_test_delta_with_policy(
        Inputs {
            contexts: &base.join("contexts.json"),
            catalogue: &base.join("catalogue.json"),
            physical_root: base,
        },
        Inputs {
            contexts: &head.join("contexts.json"),
            catalogue: &head.join("catalogue.json"),
            physical_root: head,
        },
        repo,
        policy,
    )
}

fn add_common_product(root: &Path, stamp: &[u8], resource: &[u8]) {
    let product = root.join(BUILD_STAMP_PRODUCT);
    let files = [
        (format!("{}.class", build_stamp::OWNER), stamp),
        (format!("{BUILD_STAMP_FORWARDER}.class"), STAMP_FORWARDER),
        ("reference.conf".to_owned(), resource),
    ];
    let mut inventory = Vec::new();
    let mut total_bytes = 0;
    for (path, bytes) in files {
        write(&product.join(&path), bytes);
        inventory
            .push(json!({"bytes": bytes.len(), "path": path, "sha256": hash(bytes).to_string()}));
        total_bytes += bytes.len();
    }
    let digest = hash(&serde_json::to_vec(&inventory).unwrap()).to_string();
    let capture_path = root.join("contexts.json");
    let mut capture: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&capture_path).unwrap()).unwrap();
    capture["input_objects"]
        .as_array_mut()
        .unwrap()
        .push(json!({
            "path": product, "sha256": digest, "kind": "directory", "files": 3, "bytes": total_bytes
        }));
    for context in capture["contexts"].as_array_mut().unwrap() {
        context["full_classpath"]
            .as_array_mut()
            .unwrap()
            .push(json!({
                "index": 1, "path": product, "input_object": product, "sha256": digest
            }));
    }
    write(&capture_path, &serde_json::to_vec(&capture).unwrap());
}
fn commit(repo: &Path, name: &str) -> String {
    git(repo, &["add", "."]).unwrap();
    git(
        repo,
        &[
            "-c",
            "user.name=Fixture",
            "-c",
            "user.email=fixture@example.test",
            "-c",
            "commit.gpgsign=false",
            "commit",
            "-m",
            name,
        ],
    )
    .unwrap();
    String::from_utf8(git(repo, &["rev-parse", "HEAD"]).unwrap())
        .unwrap()
        .trim()
        .to_owned()
}

#[test]
fn paired_classpath_audit_reports_both_class_directories_and_fails_on_resource_changes() {
    let temp = tempfile::tempdir().unwrap();
    let root = temp.path().canonicalize().unwrap();
    let (base, head, java) = (root.join("base"), root.join("head"), root.join("java"));
    snapshot(&base, &java, &"a".repeat(40), b"before");
    snapshot(&head, &java, &"b".repeat(40), b"after");
    add_common_product(&base, BASE_STAMP, b"resource");
    add_common_product(&head, HEAD_STAMP, b"resource");

    let audit = audit_test(&base, &head).unwrap();
    assert_eq!(audit.ordered_providers, 2);
    assert_eq!(audit.verified_provider_entries, 4);
    assert!(!audit.omission_authority);
    let [test, stamp] = audit.changed_directories.as_slice() else {
        panic!("both directories must be verified");
    };
    assert_eq!(test.path, Path::new("scan/test-classes"));
    let [class] = test.classes.as_slice() else {
        panic!("only ScanSuite.class changed");
    };
    assert_eq!(class.path, "ScanSuite.class");
    assert_eq!(
        class.base.as_ref().unwrap().sha256,
        hash(b"before").to_string()
    );
    assert_eq!(
        class.head.as_ref().unwrap().sha256,
        hash(b"after").to_string()
    );
    assert_eq!(stamp.path, Path::new(BUILD_STAMP_PRODUCT));
    assert_eq!(
        stamp.classes[0].path,
        format!("{}.class", build_stamp::OWNER)
    );
    write(&head.join("scan/test-classes/ScanSuite.class"), b"tamper");
    assert!(matches!(audit_test(&base, &head), Err(Error::Provider(_))));

    snapshot(&head, &java, &"b".repeat(40), b"after");
    add_common_product(&head, HEAD_STAMP, b"new resource");
    assert!(matches!(
        audit_test(&base, &head),
        Err(Error::Invalid("classpath delta includes a non-class file"))
    ));
}

#[test]
fn exact_test_only_git_delta_and_equal_compiled_inputs_certify_other_project() {
    let temp = tempfile::tempdir().unwrap();
    let temp = temp.path().canonicalize().unwrap();
    let repo = temp.join("repo");
    let base = temp.join("base");
    let head = temp.join("head");
    let java = temp.join("java");
    std::fs::create_dir(&repo).unwrap();
    git(&repo, &["init", "-q"]).unwrap();
    for f in ["bin/java", "lib/modules", "release"] {
        write(&java.join(f), f.as_bytes());
    }
    write(&repo.join(CHANGED), b"before");
    let before = commit(&repo, "base");
    write(&repo.join(CHANGED), b"after");
    let after = commit(&repo, "head");
    let changes = preflight_tracked_test_delta(&repo, &before, &after).unwrap();
    assert_eq!(changes.len(), 1);
    assert_eq!(changes[0].path, CHANGED);
    assert_ne!(changes[0].base_blob, changes[0].head_blob);
    assert!(preflight_tracked_test_delta(&repo, &before, "HEAD").is_err());
    snapshot(&base, &java, &before, b"before");
    snapshot(&head, &java, &after, b"after");
    let result = compare_test(&base, &head, &repo).unwrap();
    assert_eq!(result.excluded, ["AppSuite"]);
    assert_eq!(result.retained, ["ScanSuite"]);
    assert_eq!(result.changed_test_sources[0].path, CHANGED);
    assert!(!result.whole_checkout_omission_authority);
    assert_eq!(result.comparison.verified_provider_entries, 2);
    assert_eq!(result.comparison.local_java_pins.unwrap().len(), 3);
    assert!(matches!(
        &result.comparison.context_blockers["project:scan/configuration:test"],
        ContextBlocker::ClasspathContent { index: 0, path } if path == Path::new("scan/test-classes")
    ));

    add_common_product(&base, BASE_STAMP, b"same resource");
    add_common_product(&head, HEAD_STAMP, b"same resource");
    let exact = compare_test(&base, &head, &repo).unwrap();
    assert!(exact.excluded.is_empty());
    assert!(matches!(
        &exact.comparison.context_blockers["project:app/configuration:test"],
        ContextBlocker::ClasspathContent { index: 1, path } if path == Path::new(BUILD_STAMP_PRODUCT)
    ));
    let policy = BuildStampPolicy::AssumeUnchanged;
    let selected = compare_test_with_policy(&base, &head, &repo, policy).unwrap();
    assert_eq!(selected.excluded, ["AppSuite"]);
    assert_eq!(selected.retained, ["ScanSuite"]);
    assert_eq!(selected.comparison.verified_provider_entries, 4);
    assert_eq!(
        selected.comparison.rows[0].reason,
        "equal_under_generated_build_stamp_assumption"
    );
    assert_eq!(selected.comparison.build_stamp_policy, policy);
    write(
        &head.join(BUILD_STAMP_PRODUCT).join("reference.conf"),
        b"tampered",
    );
    assert!(compare_test_with_policy(&base, &head, &repo, policy).is_err());

    let mut compatible = HEAD_STAMP.to_vec();
    let start = compatible
        .windows(5)
        .position(|bytes| bytes == b"0.9.1")
        .unwrap();
    compatible[start + 4] = b'2';
    for (stamp, resource) in [
        (compatible.as_slice(), b"same resource".as_slice()),
        (HEAD_STAMP, b"changed resource".as_slice()),
    ] {
        snapshot(&head, &java, &after, b"after");
        add_common_product(&head, stamp, resource);
        let result = compare_test_with_policy(&base, &head, &repo, policy).unwrap();
        assert!(result.excluded.is_empty());
        assert!(matches!(
            &result.comparison.context_blockers["project:app/configuration:test"],
            ContextBlocker::BuildStampDeltaOutsidePolicy { index: 1, .. }
        ));
    }

    snapshot(&base, &java, &before, b"before");
    snapshot(&head, &java, &after, b"after");

    write(&head.join("app/test-classes/AppSuite.class"), b"tampered");
    assert!(compare_test(&base, &head, &repo).is_err());
    write(
        &head.join("app/test-classes/AppSuite.class"),
        b"same app output",
    );
    write(&head.join(CHANGED), b"wrong source");
    assert!(compare_test(&base, &head, &repo).is_err());

    write(&repo.join("build.sbt"), b"changed runtime configuration");
    let unrelated = commit(&repo, "head with build input");
    assert!(preflight_tracked_test_delta(&repo, &before, &unrelated).is_err());
    snapshot(&head, &java, &unrelated, b"after");
    assert!(compare_test(&base, &head, &repo).is_err());
    assert!(compare_test_with_policy(&base, &head, &repo, policy).is_err());
}

mod tracked_file_delta {
    use super::*;

    const OLD: &str = "scan/src/test/scala/OldHelper.scala";
    const NEW: &str = "scan/src/test/scala/NewHelper.scala";
    const SOURCE: &[u8] = b"object Helper";

    struct Fixture {
        _temp: tempfile::TempDir,
        repo: PathBuf,
        base: PathBuf,
        head: PathBuf,
    }

    impl Fixture {
        fn new(before: Option<&str>, after: Option<&str>) -> Self {
            let temp = tempfile::tempdir().unwrap();
            let root = temp.path().canonicalize().unwrap();
            let repo = root.join("repo");
            let base = root.join("base");
            let head = root.join("head");
            let java = root.join("java");
            std::fs::create_dir(&repo).unwrap();
            git(&repo, &["init", "-q"]).unwrap();
            write(&repo.join("README.md"), b"fixture");
            for file in ["bin/java", "lib/modules", "release"] {
                write(&java.join(file), file.as_bytes());
            }
            if let Some(path) = before {
                write(&repo.join(path), SOURCE);
            }
            let base_rev = commit(&repo, "base");
            if let Some(path) = before {
                std::fs::remove_file(repo.join(path)).unwrap();
            }
            // An unchanged body also exercises Git's rename normalization.
            let head_source: &[u8] = if before == after {
                b"object Helper { val n = 1 }"
            } else {
                SOURCE
            };
            if let Some(path) = after {
                write(&repo.join(path), head_source);
            }
            let head_rev = commit(&repo, "head");
            for (root, revision, path, source) in [
                (&base, base_rev, before, SOURCE),
                (&head, head_rev, after, head_source),
            ] {
                snapshot(root, &java, &revision, b"same compiled scan output");
                std::fs::remove_file(root.join(CHANGED)).unwrap();
                edit_capture(root, |capture| {
                    capture["contexts"][1]["source_records"] = match path {
                        Some(path) => {
                            write(&root.join(path), source);
                            json!([{
                                "path": root.join(path),
                                "repo_relative_path": path,
                                "sha256": hash(source).to_string()
                            }])
                        }
                        None => json!([]),
                    };
                });
            }
            Self {
                _temp: temp,
                repo,
                base,
                head,
            }
        }

        fn select(&self) -> Result<TrackedTestSelection, Error> {
            compare_test(&self.base, &self.head, &self.repo)
        }
    }

    fn edit_capture(root: &Path, edit: impl FnOnce(&mut serde_json::Value)) {
        let path = root.join("contexts.json");
        let mut capture = serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
        edit(&mut capture);
        write(&path, &serde_json::to_vec(&capture).unwrap());
    }

    #[test]
    fn accepts_test_add_delete_and_rename_while_retaining_the_changed_owner() {
        for (before, after) in [
            (None, Some(NEW)),
            (Some(OLD), None),
            (Some(OLD), Some(NEW)),
            (Some(OLD), Some(OLD)),
        ] {
            let fixture = Fixture::new(before, after);
            let selection = fixture.select().unwrap();
            let source_only_modified = before == after;
            assert_eq!(
                selection.schema,
                if source_only_modified {
                    "selector-tracked-test-runtime-equivalence/v1"
                } else {
                    "selector-tracked-test-runtime-equivalence/v2"
                }
            );
            assert_eq!(selection.excluded, ["AppSuite"]);
            assert_eq!(selection.retained, ["ScanSuite"]);
            assert!(
                selection.comparison.rows[1]
                    .ordered_classpath_sha256
                    .is_some()
            );
            let json = serde_json::to_value(&selection).unwrap();
            let changes = json["changed_test_sources"].as_array().unwrap();
            for path in [before, after].into_iter().flatten() {
                let change = changes
                    .iter()
                    .find(|change| change["path"] == path)
                    .unwrap();
                assert_eq!(change["owner"], "project:scan/configuration:test");
                assert_eq!(change["base_sha256"].is_string(), before == Some(path));
                assert_eq!(change["head_sha256"].is_string(), after == Some(path));
                assert_eq!(change["base_sha256"].is_null(), before != Some(path));
                assert_eq!(change["head_sha256"].is_null(), after != Some(path));
            }
            assert_eq!(
                changes.len(),
                if before.is_some() && after.is_some() && before != after {
                    2
                } else {
                    1
                }
            );
        }
    }

    #[test]
    fn rejects_existing_path_on_the_git_absent_side() {
        let fixture = Fixture::new(Some(OLD), None);
        let unexpected = fixture.head.join(OLD);
        write(&unexpected, SOURCE);
        assert!(matches!(
            fixture.select(),
            Err(Error::Invalid("manifest absence changed"))
        ));
        #[cfg(unix)]
        {
            std::fs::remove_file(&unexpected).unwrap();
            std::os::unix::fs::symlink("missing-target", unexpected).unwrap();
            assert!(matches!(
                fixture.select(),
                Err(Error::Invalid("runtime equivalence symlink input"))
            ));
        }
    }

    #[test]
    fn rejects_captured_source_or_resource_on_the_git_absent_side() {
        let fixture = Fixture::new(None, Some(NEW));
        edit_capture(&fixture.base, |capture| {
            capture["contexts"][0]["source_records"] = json!([{
                "path": fixture.base.join(NEW),
                "repo_relative_path": "unexpected-path",
                "sha256": hash(SOURCE).to_string()
            }]);
        });
        assert!(matches!(
            fixture.select(),
            Err(Error::Invalid(
                "absent tracked test source is a captured compiler input or resource"
            ))
        ));
        edit_capture(&fixture.base, |capture| {
            capture["contexts"][0]["source_records"] = json!([]);
            capture["contexts"][0]["resource_files"] = json!([fixture.base.join(NEW)]);
        });
        assert!(matches!(
            fixture.select(),
            Err(Error::Invalid(
                "absent tracked test source is a captured compiler input or resource"
            ))
        ));
    }

    #[test]
    fn rejects_one_sided_change_without_a_paired_test_owner() {
        let fixture = Fixture::new(None, Some(NEW));
        edit_capture(&fixture.base, |capture| {
            capture["contexts"][1]["configuration"] = json!("compile");
        });
        assert!(matches!(
            fixture.select(),
            Err(Error::Invalid("missing paired test source owner"))
        ));
    }
}
