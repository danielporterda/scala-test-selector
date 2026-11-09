use super::*;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{
    fs,
    path::{Path, PathBuf},
};
fn sha(b: &[u8]) -> Hash {
    Sha256::digest(b).into()
}
fn pin(path: &Path) -> Pin {
    let b = fs::read(path).unwrap();
    Pin {
        path: path.into(),
        sha256: hash_hex(sha(&b)),
        bytes: b.len() as u64,
    }
}
fn put(path: &Path, b: impl AsRef<[u8]>) {
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, b).unwrap();
}
fn jsonfile(path: &Path, v: &Value) {
    put(path, serde_json::to_vec(v).unwrap())
}
fn hash(b: &[u8]) -> String {
    hash_hex(sha(b))
}
fn u2(b: &mut Vec<u8>, n: u16) {
    b.extend(n.to_be_bytes())
}
fn u4(b: &mut Vec<u8>, n: u32) {
    b.extend(n.to_be_bytes())
}
fn class(owner: &str, source: &str, module: bool) -> Vec<u8> {
    // Synthetic ABI fixture, deliberately not compiler provenance/effect evidence.
    let words = [
        owner,
        "java/lang/Object",
        "<init>",
        "()V",
        "Code",
        "SourceFile",
        source,
        "MODULE$",
        "",
        "<clinit>",
        "effect",
        "(I)V",
    ];
    let mut cp = Vec::new();
    for (i, s) in words.iter().enumerate() {
        cp.push(1);
        let text = if i == 8 {
            format!("L{owner};")
        } else {
            s.to_string()
        };
        u2(&mut cp, text.len() as u16);
        cp.extend(text.as_bytes());
    }
    cp.push(7);
    u2(&mut cp, 1);
    cp.push(7);
    u2(&mut cp, 2);
    let mut b = 0xcafebabeu32.to_be_bytes().to_vec();
    u2(&mut b, 0);
    u2(&mut b, 61);
    u2(&mut b, 15);
    b.extend(cp);
    u2(&mut b, 1);
    u2(&mut b, 13);
    u2(&mut b, 14);
    u2(&mut b, 0);
    u2(&mut b, module as u16);
    if module {
        u2(&mut b, 9);
        u2(&mut b, 8);
        u2(&mut b, 9);
        u2(&mut b, 0)
    }
    u2(&mut b, if module { 3 } else { 2 });
    for (name, desc, flags) in if module {
        vec![(3, 4, 1), (10, 4, 8), (11, 12, 1)]
    } else {
        vec![(3, 4, 1), (11, 12, 1)]
    } {
        u2(&mut b, flags);
        u2(&mut b, name);
        u2(&mut b, desc);
        u2(&mut b, 1);
        u2(&mut b, 5);
        u4(&mut b, 13);
        u2(&mut b, 1);
        u2(&mut b, 2);
        u4(&mut b, 1);
        b.push(0xb1);
        u2(&mut b, 0);
        u2(&mut b, 0)
    }
    u2(&mut b, 1);
    u2(&mut b, 6);
    u4(&mut b, 2);
    u2(&mut b, 7);
    b
}
fn stamp() -> Value {
    json!({"class":"sbt.internal.inc.FarmHash","written":"farm(abc)","hash":"abc","modified":null})
}
struct Fixture {
    _tmp: tempfile::TempDir,
    root: PathBuf,
    manifest: Manifest,
    path: PathBuf,
    expect: Expectations,
}
impl Fixture {
    fn new() -> Self {
        let tmp = tempfile::tempdir().unwrap();
        let dir = tmp.path();
        let root = dir.join("source");
        let source = root.join("src/Suite.scala");
        put(&source, "package p\nclass Suite\nobject Module\n");
        let src = fs::read(&source).unwrap();
        let products = root.join("classes");
        let a = products.join("p/Suite.class");
        let z = products.join("p/Module$.class");
        put(&a, class("p/Suite", "Suite.scala", false));
        put(&z, class("p/Module$", "Suite.scala", true));
        let records = json!([{"bytes":fs::metadata(&z).unwrap().len(),"path":"p/Module$.class","sha256":pin(&z).sha256},{"bytes":fs::metadata(&a).unwrap().len(),"path":"p/Suite.class","sha256":pin(&a).sha256}]);
        let object_hash = hash(&serde_json::to_vec(&records).unwrap());
        let context = "project:fixture/configuration:test";
        let context_path = dir.join("contexts.json");
        jsonfile(
            &context_path,
            &json!({"source_root":root,"contexts":[{"context_id":context,"class_directory":products,"source_records":[{"path":source,"repo_relative_path":"src/Suite.scala","sha256":hash(&src)}],"full_classpath":[{"index":0,"path":products,"input_object":products,"sha256":object_hash}]}],"input_objects":[{"path":products,"kind":"directory","sha256":object_hash,"files":2,"bytes":fs::metadata(&a).unwrap().len()+fs::metadata(&z).unwrap().len()}]}),
        );
        let doc = dir.join("documents.jsonl");
        let v = json!({"path":"src/Suite.scala","source_sha256":hash(&src),"source_contexts":[context],"source_text":String::from_utf8(src.clone()).unwrap(),"document":{"symbols":[{"symbol":"p/Suite#","kind":13},{"symbol":"p/Module.","kind":10}],"occurrences":[{"symbol":"p/Suite#","role":2},{"symbol":"p/Module.","role":2}]}});
        put(&doc, format!("{}\n", v));
        let analysis = dir.join("analysis.zip");
        put(&analysis, b"synthetic test analysis");
        let output = dir.join("reader.jsonl");
        let rows = json!({"source":"${BASE}/src/Suite.scala","source_stamp":stamp(),"source_bytes":src.len(),"source_sha256":hash(&src),"recomputed_source_farmhash":stamp(),"products":[{"path":"${BASE}/classes/p/Suite.class","stamp":stamp(),"bytes":pin(&a).bytes,"sha256":pin(&a).sha256,"recomputed_content_hash":stamp()},{"path":"${BASE}/classes/p/Module$.class","stamp":stamp(),"bytes":pin(&z).bytes,"sha256":pin(&z).sha256,"recomputed_content_hash":stamp()}]});
        put(&output, format!("{}\n", rows));
        let producer = dir.join("producer");
        put(&producer, b"synthetic test-only reader");
        let p = pin(&producer);
        let mut h = Sha256::new();
        h.update(b"retained-zinc-source-products-producer/v1\0");
        let text = p.path.to_str().unwrap();
        h.update((text.len() as u64).to_le_bytes());
        h.update(text.as_bytes());
        h.update(parse_hash(&p.sha256).unwrap());
        h.update(p.bytes.to_le_bytes());
        let producer_hash: Hash = h.finalize().into();
        let receipt = dir.join("reader-receipt.json");
        jsonfile(
            &receipt,
            &json!({"all_inputs_unchanged":true,"inputs":[pin(&analysis),p],"commands":[{"case":"read","command":["ReadZinc",analysis,root],"exit_code":0,"stdout":output,"stdout_bytes":pin(&output).bytes}]}),
        );
        let compile = dir.join("compile.json");
        jsonfile(
            &compile,
            &json!({"exit_code":0,"command":["synthetic-test-only"]}),
        );
        let manifest = Manifest {
            schema: "retained-zinc-source-products/v1".into(),
            qualification: "new_retained_analysis_correspondence".into(),
            producer_sha256: hash_hex(producer_hash),
            producer_inputs: vec![pin(&producer)],
            contexts: pin(&context_path),
            documents: pin(&doc),
            compile_receipt: pin(&compile),
            inputs: vec![ContextInput {
                context: context.into(),
                analysis: pin(&analysis),
                reader_output: pin(&output),
                reader_receipt: pin(&receipt),
            }],
        };
        let path = dir.join("manifest.json");
        put(&path, serde_json::to_vec(&manifest).unwrap());
        let expect = Expectations {
            manifest: sha(&fs::read(&path).unwrap()),
            producer: producer_hash,
            contexts: parse_hash(&manifest.contexts.sha256).unwrap(),
            documents: parse_hash(&manifest.documents.sha256).unwrap(),
            compile_receipt: parse_hash(&manifest.compile_receipt.sha256).unwrap(),
        };
        Self {
            _tmp: tmp,
            root,
            manifest,
            path,
            expect,
        }
    }
    fn republish(&mut self) {
        put(&self.path, serde_json::to_vec(&self.manifest).unwrap());
        self.expect.manifest = sha(&fs::read(&self.path).unwrap());
    }
    fn edit_rows(&mut self, f: impl FnOnce(&mut Value)) {
        let p = &self.manifest.inputs[0].reader_output.path;
        let mut v: Value = serde_json::from_slice(&fs::read(p).unwrap()).unwrap();
        f(&mut v);
        put(p, format!("{}\n", v));
        self.manifest.inputs[0].reader_output = pin(p);
        let rp = &self.manifest.inputs[0].reader_receipt.path;
        let mut r: Value = serde_json::from_slice(&fs::read(rp).unwrap()).unwrap();
        r["commands"][0]["stdout_bytes"] = json!(self.manifest.inputs[0].reader_output.bytes);
        jsonfile(rp, &r);
        self.manifest.inputs[0].reader_receipt = pin(rp);
        self.republish();
    }
    fn open(&self) -> Result<VerifiedBinding, Error> {
        admit(&self.path, &self.expect, &Limits::default())
    }
}
#[test]
fn complete_products_expose_all_method_keys_and_exact_root_phases() {
    let f = Fixture::new();
    let b = f.open().unwrap();
    assert_eq!(
        (b.source_count(), b.class_count(), b.method_count()),
        (1, 2, 5)
    );
    let s = b
        .find_source("project:fixture/configuration:test", "src/Suite.scala")
        .unwrap();
    assert_eq!(b.changed_methods(s).unwrap().count(), 5);
    let r = b
        .root_entry(
            "project:fixture/configuration:test",
            "src/Suite.scala",
            "p/Suite",
            RootKind::Class,
        )
        .unwrap();
    assert_eq!(b.method(r.entry).unwrap().name, "<init>");
    let r = b
        .root_entry(
            "project:fixture/configuration:test",
            "src/Suite.scala",
            "p/Module$",
            RootKind::Module,
        )
        .unwrap();
    assert_eq!(b.method(r.entry).unwrap().name, "<clinit>");
    assert!(matches!(
        b.root_entry(
            "project:fixture/configuration:test",
            "src/Suite.scala",
            "p/Other",
            RootKind::Class
        ),
        Err(Pending::NoExactSourceDefinition)
    ));
}
#[test]
fn stale_source_product_inventory_and_external_pins_fail_closed() {
    for which in 0..5 {
        let mut f = Fixture::new();
        match which {
            0 => put(&f.root.join("src/Suite.scala"), "changed"),
            1 => put(&f.root.join("classes/p/Suite.class"), b"changed"),
            2 => put(
                &f.root.join("classes/p/Extra.class"),
                class("p/Extra", "Suite.scala", false),
            ),
            3 => {
                fs::remove_file(f.root.join("classes/p/Suite.class")).unwrap();
            }
            4 => {
                f.expect.documents = [1; 32];
                f.republish()
            }
            _ => unreachable!(),
        }
        assert!(f.open().is_err(), "mutation {which}");
    }
}
#[test]
fn duplicate_missing_foreign_and_noncontent_relations_reject() {
    for which in 0..7 {
        let mut f = Fixture::new();
        f.edit_rows(|r| match which {
            0 => {
                r["products"].as_array_mut().unwrap().pop();
            }
            1 => {
                let p = r["products"][0].clone();
                r["products"].as_array_mut().unwrap().push(p)
            }
            2 => r["products"][0]["path"] = json!("${BASE}/../escape.class"),
            3 => r["source_stamp"]["class"] = json!("sbt.internal.inc.LastModified"),
            4 => r["products"][0]["stamp"]["hash"] = json!("def"),
            5 => r["source"] = json!("${OTHER}/src/Suite.scala"),
            6 => r["recomputed_source_farmhash"]["written"] = json!("farm(def)"),
            _ => unreachable!(),
        });
        assert!(f.open().is_err(), "relation mutation {which}");
    }
}
#[test]
fn source_without_semanticdb_is_pending_not_empty() {
    let mut f = Fixture::new();
    put(&f.manifest.documents.path, "\n");
    f.manifest.documents = pin(&f.manifest.documents.path);
    f.expect.documents = parse_hash(&f.manifest.documents.sha256).unwrap();
    f.republish();
    assert!(f.open().is_err()); // malformed row is never accepted as empty
    let mut f = Fixture::new();
    put(&f.manifest.documents.path, "");
    f.manifest.documents = pin(&f.manifest.documents.path);
    f.expect.documents = parse_hash(&f.manifest.documents.sha256).unwrap();
    f.republish();
    let b = f.open().unwrap();
    assert_eq!(b.method_count(), 5);
    assert!(matches!(
        b.changed_methods(SourceId(0)),
        Err(Pending::SourceNotInSemanticDb)
    ));
    assert!(matches!(
        b.root_entry(
            "project:fixture/configuration:test",
            "src/Suite.scala",
            "p/Suite",
            RootKind::Class
        ),
        Err(Pending::SourceNotInSemanticDb)
    ));
}
#[test]
fn context_provider_and_budgets_are_real_admission_constraints() {
    let mut f = Fixture::new();
    let mut c: Value =
        serde_json::from_slice(&fs::read(&f.manifest.contexts.path).unwrap()).unwrap();
    c["contexts"][0]["full_classpath"][0]["index"] = json!(1);
    jsonfile(&f.manifest.contexts.path, &c);
    f.manifest.contexts = pin(&f.manifest.contexts.path);
    f.expect.contexts = parse_hash(&f.manifest.contexts.sha256).unwrap();
    f.republish();
    assert!(f.open().is_err());
    let f = Fixture::new();
    let mut limits = Limits::default();
    limits.max_owned_bytes = 1;
    assert!(matches!(
        admit(&f.path, &f.expect, &limits),
        Err(Error::Limit(_))
    ));
}
#[test]
fn malformed_class_and_sourcefile_mismatch_reject() {
    let b = class("p/Suite", "Suite.scala", false);
    assert!(crate::classfile::parse(&b).is_ok());
    for i in [0, 9, b.len() - 1] {
        let mut c = b.clone();
        c[i] ^= 0xff;
        assert!(crate::classfile::parse(&c).is_err(), "class mutation {i}");
    }
    assert!(crate::classfile::descriptor("(Ljava/lang/String;I)V").is_ok());
    for bad in ["(V)V", "()", "([V)V", "(I)Vx"] {
        assert!(crate::classfile::descriptor(bad).is_err());
    }
}

#[test]
fn independently_repinned_wrong_sourcefile_and_class_owner_are_rejected() {
    // Re-pin every physical wrapper so rejection tests actual class/source
    // correspondence, not merely an earlier stale SHA check.
    for (owner, source) in [("p/Suite", "Wrong.scala"), ("p/Other", "Suite.scala")] {
        let mut f = Fixture::new();
        let p = f.root.join("classes/p/Suite.class");
        put(&p, class(owner, source, false));
        let new_pin = pin(&p);
        f.edit_rows(|row| {
            let p = &mut row["products"][0];
            p["bytes"] = json!(new_pin.bytes);
            p["sha256"] = json!(new_pin.sha256);
        });
        let a = pin(&f.root.join("classes/p/Suite.class"));
        let b = pin(&f.root.join("classes/p/Module$.class"));
        let inventory = json!([
            {"bytes":b.bytes,"path":"p/Module$.class","sha256":b.sha256},
            {"bytes":a.bytes,"path":"p/Suite.class","sha256":a.sha256}
        ]);
        let inventory_hash = hash(&serde_json::to_vec(&inventory).unwrap());
        let mut contexts: Value =
            serde_json::from_slice(&fs::read(&f.manifest.contexts.path).unwrap()).unwrap();
        contexts["input_objects"][0]["sha256"] = json!(inventory_hash);
        contexts["input_objects"][0]["bytes"] = json!(a.bytes + b.bytes);
        contexts["contexts"][0]["full_classpath"][0]["sha256"] = json!(inventory_hash);
        jsonfile(&f.manifest.contexts.path, &contexts);
        f.manifest.contexts = pin(&f.manifest.contexts.path);
        f.expect.contexts = parse_hash(&f.manifest.contexts.sha256).unwrap();
        f.republish();
        let reason = f.open().err().unwrap().to_string();
        assert!(
            reason == "class SourceFile/source owner mismatch"
                || reason == "class owner/path mismatch",
            "{reason}"
        );
    }
}

#[test]
fn borrowed_class_arc_is_shared_and_root_requests_cannot_cross_contexts() {
    let f = Fixture::new();
    let b = f.open().unwrap();
    let a = b.class_bytes_arc(ClassId(0)).unwrap();
    let z = b.class_bytes_arc(ClassId(0)).unwrap();
    assert!(std::sync::Arc::ptr_eq(&a, &z));
    assert_eq!(
        b.class(ClassId(0)).unwrap().context,
        "project:fixture/configuration:test"
    );
    assert!(matches!(
        b.root_entry(
            "project:other/configuration:test",
            "src/Suite.scala",
            "p/Suite",
            RootKind::Class
        ),
        Err(Pending::SourceNotInSemanticDb)
    ));
    assert!(b.method(MethodId(u32::MAX)).is_none());
    assert!(b.class_bytes_arc(ClassId(u32::MAX)).is_none());
}
