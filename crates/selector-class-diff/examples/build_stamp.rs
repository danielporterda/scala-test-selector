//! Usage: cargo run -p selector-class-diff --example build_stamp --
//! BASE_MODULE HEAD_MODULE BASE_FORWARDER HEAD_FORWARDER [BASE_SOURCE HEAD_SOURCE]
use selector_class_diff::build_stamp::{DESCRIPTOR, OWNER, compare};
use serde_json::json;
use std::{fs::File, io::Read, path::Path};

fn bounded(path: &Path) -> Result<Vec<u8>, std::io::Error> {
    let mut bytes = Vec::new();
    File::open(path)?
        .take(16 * 1024 + 1)
        .read_to_end(&mut bytes)?;
    Ok(bytes)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let paths: Vec<_> = std::env::args_os().skip(1).collect();
    let (base, head, base_forwarder, head_forwarder, sources) = match paths.as_slice() {
        [base, head, base_forwarder, head_forwarder] => {
            (base, head, base_forwarder, head_forwarder, None)
        }
        [base, head, base_forwarder, head_forwarder, before, after] => {
            (base, head, base_forwarder, head_forwarder, Some((before, after)))
        }
        _ => return Err("expected BASE_MODULE HEAD_MODULE BASE_FORWARDER HEAD_FORWARDER [BASE_SOURCE HEAD_SOURCE]".into()),
    };
    let base_bytes = bounded(base.as_ref())?;
    let head_bytes = bounded(head.as_ref())?;
    let delta = compare(
        &base_bytes,
        &head_bytes,
        &bounded(base_forwarder.as_ref())?,
        &bounded(head_forwarder.as_ref())?,
    )
    .map_err(|reason| format!("unsupported BuildInfo class layout: {reason:?}"))?;
    let mut report = json!({
        "schema": "selector-build-stamp-audit/v1",
        "scope": "Exact generated class wire and named getter surfaces; no suite omission authority.",
        "class_owner": OWNER,
        "getter_descriptor": DESCRIPTOR,
        "base_module_sha256": delta.before_module.to_string(),
        "head_module_sha256": delta.after_module.to_string(),
        "forwarder_sha256": delta.forwarder.to_string(),
        "base_stamp": {"compiledVersion": delta.before.compiled_version, "commitUnixTimestamp": delta.before.commit_unix_timestamp},
        "head_stamp": {"compiledVersion": delta.after.compiled_version, "commitUnixTimestamp": delta.after.commit_unix_timestamp},
        "reader_surfaces": delta.reader_surfaces().map(|s| s.member()).collect::<Vec<_>>(),
        "omission_authority": false,
    });
    if let Some((before, after)) = sources {
        let [base_source, head_source] = delta
            .verify_sources(&bounded(before.as_ref())?, &bounded(after.as_ref())?)
            .map_err(|reason| format!("unsupported generated BuildInfo source: {reason:?}"))?;
        report["base_source_sha256"] = json!(base_source.to_string());
        report["head_source_sha256"] = json!(head_source.to_string());
    }
    println!("{}", serde_json::to_string_pretty(&report)?);
    Ok(())
}
