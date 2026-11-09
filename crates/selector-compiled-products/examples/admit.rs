use selector_compiled_products::*;
use serde_json::{Value, json};
use std::{env, fs, path::Path};
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let a: Vec<_> = env::args().collect();
    if a.len() != 3 {
        return Err("manifest expectations".into());
    }
    let x: Value = serde_json::from_slice(&fs::read(&a[2])?)?;
    let h = |key: &str| parse_hash(x[key].as_str().ok_or(Error::Invalid("expected pin"))?);
    let expected = Expectations {
        manifest: h("manifest")?,
        producer: h("producer")?,
        contexts: h("contexts")?,
        documents: h("documents")?,
        compile_receipt: h("compile_receipt")?,
    };
    let b = admit(Path::new(&a[1]), &expected, &Limits::default())?;
    let mut sources = Vec::new();
    let mut verified = 0;
    for i in 0..b.source_count() {
        let s = b.source(SourceId(i as u32)).unwrap();
        verified += s.semantic_db_verified as usize;
        if s.path.ends_with("ThresholdsTest.scala")
            || s.path.ends_with("UrlValidatorTest.scala")
            || s.path.ends_with("AcsSnapshotStore.scala")
            || s.path.ends_with("BaseTest.scala")
        {
            let methods:Vec<_>=b.changed_methods(s.id)?.map(|id|{let m=b.method(id).unwrap();json!({"owner":m.owner,"name":m.name,"descriptor":m.descriptor,"class_sha256":hash_hex(m.class_sha256),"flags":m.flags,"code":m.has_code})}).collect();
            let root = if s.path.ends_with("ThresholdsTest.scala") {
                Some("org/lfdecentralizedtrust/splice/config/ThresholdsTest")
            } else if s.path.ends_with("UrlValidatorTest.scala") {
                Some("org/lfdecentralizedtrust/splice/http/UrlValidatorTest")
            } else {
                None
            };
            let entry=root.map(|r|b.root_entry(s.context,s.path,r,RootKind::Class).map(|r|{let m=b.method(r.entry).unwrap();json!({"owner":m.owner,"name":m.name,"descriptor":m.descriptor,"class_sha256":hash_hex(m.class_sha256)})}));
            sources.push(json!({"context":s.context,"path":s.path,"source_sha256":hash_hex(s.source_sha256),"classes":s.classes,"methods":s.methods,"root_entry":entry.transpose().map_err(|_|Error::Invalid("pending root"))?,"method_keys":methods}));
        }
    }
    println!(
        "{}",
        serde_json::to_string_pretty(
            &json!({"schema":"compiled-source-correspondence-control/v1","scope":"NEW retained-analysis correspondence; no effect closure, source Unknown waiver, or exclusion authority","manifest_sha256":hash_hex(b.identity()),"contexts_sha256":hash_hex(b.contexts_identity()),"documents_sha256":hash_hex(b.documents_identity()),"sources":b.source_count(),"semanticdb_verified_sources":verified,"captured_only_pending_sources":b.source_count()-verified,"classes":b.class_count(),"methods":b.method_count(),"owned_bytes_charged":b.owned_bytes(),"selected_sources":sources})
        )?
    );
    Ok(())
}
