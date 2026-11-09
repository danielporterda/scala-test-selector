//! Shared normalized authority-protocol fixture over genuine frozen JVM bytes.
//! This is not an original compiler/CI discovery capture or execution claim.
use selector_facts::{FactBuilder, FileRecord, SuiteRecord};
use selector_types::*;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::path::{Path, PathBuf};

#[derive(Clone, Copy)]
pub enum Mode {
    Absent,
    Present,
    Alternate,
    CompileOnly,
    KnownOtherSource,
    MissingSource,
    ManifestGap,
}
pub struct Fixture {
    pub root: PathBuf,
    pub contexts: PathBuf,
    pub map: PathBuf,
    pub catalogue: PathBuf,
    pub request: PathBuf,
    pub facts: selector_facts::FactSnapshot,
    pub changed: FileId,
    pub suite: SuiteId,
}
fn hash(bytes: &[u8]) -> String {
    ContentHash(Sha256::digest(bytes).into()).to_string()
}
pub fn pin(path: &Path) -> Value {
    let bytes = std::fs::read(path).unwrap();
    json!({"path":path,"sha256":hash(&bytes),"bytes":bytes.len()})
}
fn directory(path: &Path) -> Value {
    fn scan(root: &Path, path: &Path, rows: &mut Vec<Value>) {
        for e in std::fs::read_dir(path).unwrap() {
            let e = e.unwrap();
            if e.file_type().unwrap().is_dir() {
                scan(root, &e.path(), rows)
            } else {
                let bytes = std::fs::read(e.path()).unwrap();
                rows.push(json!({"path":e.path().strip_prefix(root).unwrap().to_str().unwrap(),"bytes":bytes.len(),"sha256":hash(&bytes)}));
            }
        }
    }
    let mut rows = Vec::new();
    scan(path, path, &mut rows);
    rows.sort_by(|a, b| a["path"].as_str().cmp(&b["path"].as_str()));
    json!({"path":path,"kind":"directory","sha256":hash(&serde_json::to_vec(&rows).unwrap()),"files":rows.len(),"bytes":rows.iter().map(|v|v["bytes"].as_u64().unwrap()).sum::<u64>()})
}
fn write_class(root: &Path, name: &str, bytes: &[u8]) {
    let path = root.join(format!("{name}.class"));
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, bytes).unwrap();
}
fn metadata_rename(bytes: &[u8], old: &[u8], new: &[u8]) -> Vec<u8> {
    assert_eq!(old.len(), new.len());
    let mut b = bytes.to_vec();
    let at = b.windows(old.len()).position(|x| x == old).unwrap();
    b[at..at + old.len()].copy_from_slice(new);
    b
}
/// Minimal stored ZIP writer for manifest-only protocol inputs, no JVM/tools.
fn manifest_jar(path: &Path) {
    let name = b"META-INF/MANIFEST.MF";
    let body = b"Manifest-Version: 1.0\r\nClass-Path: optional.jar\r\n\r\n";
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
pub fn make(root: &Path, fixtures: &Path, mode: Mode) -> Fixture {
    let root = root.canonicalize().unwrap();
    let changed_dir = root.join("changed-classes");
    let suite_dir = root.join("suite-classes");
    std::fs::create_dir_all(&changed_dir).unwrap();
    std::fs::create_dir_all(&suite_dir).unwrap();
    let original = fixtures.join("native-admission-chain/classes/admissioncase");
    let getter = std::fs::read(original.join("Getter.class")).unwrap();
    let entry = std::fs::read(original.join("Fixture.class")).unwrap();
    write_class(&changed_dir, "admissioncase/Getter", &getter);
    write_class(&suite_dir, "admissioncase/Fixture", &entry);
    if matches!(mode, Mode::Alternate) {
        write_class(&suite_dir, "admissioncase/Getter", &getter);
    }
    if matches!(mode, Mode::KnownOtherSource | Mode::MissingSource) {
        let bytes = if matches!(mode, Mode::KnownOtherSource) {
            metadata_rename(&entry, b"Fixture.java", b"Another.java")
        } else {
            metadata_rename(&entry, b"SourceFile", b"SourceFild")
        };
        write_class(&changed_dir, "admissioncase/Fixture", &bytes);
    }
    let changed_source = root.join("changed/Fixture.java");
    let suite_source = root.join("suite/Fixture.java");
    std::fs::create_dir_all(changed_source.parent().unwrap()).unwrap();
    std::fs::create_dir_all(suite_source.parent().unwrap()).unwrap();
    std::fs::write(
        &changed_source,
        b"// normalized source owner for genuine Getter.class\n",
    )
    .unwrap();
    std::fs::write(
        &suite_source,
        b"// normalized catalogue owner for genuine Fixture.class\n",
    )
    .unwrap();
    let changed_obj = directory(&changed_dir);
    let suite_obj = directory(&suite_dir);
    let mut objects = vec![
        changed_obj.clone(),
        suite_obj.clone(),
        {
            let mut p = pin(&changed_source);
            p["kind"] = json!("file");
            p
        },
        {
            let mut p = pin(&suite_source);
            p["kind"] = json!("file");
            p
        },
    ];
    let cp = |obj: &Value, index: usize, owner: &str| json!({"index":index,"path":obj["path"],"input_object":obj["path"],"sha256":obj["sha256"],"project_output_origins":if owner.is_empty(){json!([])}else{json!([{"context_id":owner}])}});
    let changed_owner = "project:changed/configuration:compile";
    let suite_owner = "project:suite/configuration:test";
    let mut runtime = vec![cp(&suite_obj, 0, suite_owner)];
    if matches!(mode, Mode::Present) {
        runtime.push(cp(&changed_obj, runtime.len(), changed_owner));
    }
    if matches!(mode, Mode::ManifestGap) {
        let jar = root.join("manifest.jar");
        manifest_jar(&jar);
        let mut obj = pin(&jar);
        obj["kind"] = json!("file");
        runtime.push(cp(&obj, runtime.len(), ""));
        objects.push(obj);
    }
    let mut dependency = runtime.clone();
    if matches!(mode, Mode::CompileOnly) {
        dependency.push(cp(&changed_obj, dependency.len(), changed_owner));
    }
    let source = |path: &Path, logical: &str| json!({"path":path,"repo_relative_path":logical,"input_object":path,"sha256":pin(path)["sha256"]});
    let product =
        |obj: &Value| json!({"path":obj["path"],"input_object":obj["path"],"sha256":obj["sha256"]});
    let mut changed_records = vec![source(&changed_source, "changed/Fixture.java")];
    let mut owners =
        json!({"changed/Fixture.java":[changed_owner],"suite/Fixture.java":[suite_owner]});
    if matches!(mode, Mode::KnownOtherSource) {
        let other = root.join("changed/Another.java");
        std::fs::write(&other, b"// normalized other captured source\n").unwrap();
        changed_records.push(source(&other, "changed/Another.java"));
        let mut obj = pin(&other);
        obj["kind"] = json!("file");
        objects.push(obj);
        owners["changed/Another.java"] = json!([changed_owner]);
    }
    let fingerprint = json!({"is_module":false,"require_no_arg_constructor":true,"type":"normalized_callable_root"});
    let contexts = root.join("contexts.json");
    let capture = json!({"schema_version":"sbt-compiler-context/v1","revision":"normalized-cp-absence","source_root":root,"errors":[],"java_runtime":{"java_version":"21.0.12.1"},"source_to_contexts":owners,
        "contexts":[{"context_id":changed_owner,"configuration":"compile","class_directory":changed_dir,"products":[changed_dir],"exported_products":[product(&changed_obj)],"source_records":changed_records,"full_classpath":[cp(&changed_obj,0,changed_owner)],"dependency_classpath":[]},
        {"context_id":suite_owner,"configuration":"test","class_directory":suite_dir,"products":[suite_dir],"exported_products":[product(&suite_obj)],"source_records":[source(&suite_source,"suite/Fixture.java")],"defined_tests":[{"name":"admissioncase.Fixture","fingerprint":fingerprint}],"full_classpath":runtime,"dependency_classpath":dependency}],"input_objects":objects});
    std::fs::write(&contexts, serde_json::to_vec(&capture).unwrap()).unwrap();
    let native_entry = |row: &Value| {
        let object = objects.iter().find(|o| o["path"] == row["path"]).unwrap();
        let mut entry = json!({"path":object["path"],"sha256":object["sha256"],"kind":if object["kind"]=="directory"{"directory"}else{"jar"}});
        if object["kind"] == "directory" {
            entry["files"] = object["files"].clone();
            entry["bytes"] = object["bytes"].clone();
        }
        entry
    };
    let map = root.join("map.json");
    std::fs::write(&map,json!({"version":1,"revision":"normalized-cp-absence","java_feature":21,"types":[],"methods":[],"contexts":[{"id":changed_owner,"entries":[native_entry(&cp(&changed_obj,0,changed_owner))]},{"id":suite_owner,"entries":runtime.iter().map(native_entry).collect::<Vec<_>>()}]}).to_string()).unwrap();
    let catalogue = root.join("catalogue.json");
    std::fs::write(&catalogue,json!({"schema_version":"compiler-ci-catalogue/v1","complete":true,"issues":[],"suites":[{"suite":"admissioncase.Fixture","owning_context_ids":[suite_owner],"compiler_discovery":[{"context_id":suite_owner,"configuration":"test","fingerprint":fingerprint}]}]}).to_string()).unwrap();
    let mut b = FactBuilder::new();
    b.facts.revision = b.intern("normalized-cp-absence").unwrap();
    for (logical, path, context) in [
        ("changed/Fixture.java", &changed_source, changed_owner),
        ("suite/Fixture.java", &suite_source, suite_owner),
    ] {
        let path_id = b.intern(logical).unwrap();
        let text = String::from_utf8(std::fs::read(path).unwrap()).unwrap();
        let source = b.intern(&text).unwrap();
        let context = b.intern(context).unwrap();
        b.facts.files.push(FileRecord {
            path: path_id,
            source,
            context,
            revision: b.facts.revision,
            source_hash: ContentHash::from_hex(pin(path)["sha256"].as_str().unwrap()).unwrap(),
            flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
        });
    }
    let changed_symbol = b.ensure_symbol("admissioncase/Getter#", FileId(0)).unwrap();
    b.facts.symbols[changed_symbol.index()].file = FileId(0);
    b.facts.symbols[changed_symbol.index()].flags = SYMBOL_DEFINED;
    b.facts.symbols[changed_symbol.index()].kind = 13;
    let symbol = b
        .ensure_symbol("admissioncase/Fixture#", FileId(1))
        .unwrap();
    b.facts.symbols[symbol.index()].file = FileId(1);
    b.facts.symbols[symbol.index()].flags = SYMBOL_DEFINED;
    b.facts.symbols[symbol.index()].kind = 13;
    let name = b.intern("admissioncase.Fixture").unwrap();
    b.facts.suites.push(SuiteRecord {
        name,
        symbol,
        file: FileId(1),
        flags: 0,
    });
    let mut facts = b.finish().unwrap();
    facts.identity = selector_facts::codec::write(&root.join("facts.bin"), &facts).unwrap();
    let provider = json!({"contexts":pin(&contexts),"binary_map":pin(&map),"relocated_root":root,"raw_facts_identity":null,"platform":null});
    let request = root.join("request.json");
    std::fs::write(&request,json!({"schema":"selector-classpath-absence-request/v1","base":provider,"head":provider,"base_catalogue":pin(&catalogue),"head_catalogue":pin(&catalogue)}).to_string()).unwrap();
    Fixture {
        root,
        contexts,
        map,
        catalogue,
        request,
        facts,
        changed: FileId(0),
        suite: SuiteId(0),
    }
}
