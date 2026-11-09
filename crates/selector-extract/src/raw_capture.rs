//! Native SemanticDB v4 capture normalization, using the pinned 4.15.2 schema.
//!
//! Raw messages and strings stay borrowed from one bounded input buffer. The
//! serializer scans declared fields without allocating a JSON object per symbol,
//! type, occurrence, or synthetic tree. Unknown fields/wire types fail clearly;
//! opaque documentation bytes never become inferred symbol references.
//! Original protobuf bytes remain the input artifact and are identified by SHA256.

use crate::semantic_wire::{Message, Wire, text_field};
use md5::{Digest as Md5Digest, Md5};
use rayon::prelude::*;
use selector_types::{ContentHash, Error};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::fs::{self, File};
use std::io::{self, BufWriter, Read, Write};
use std::path::{Component, Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);
#[derive(Debug, Clone)]
pub struct RawInput {
    pub path: PathBuf,
    pub expected_sha256: Option<ContentHash>,
    pub semanticdb_input: String,
    pub input_target_contexts: Vec<String>,
}
#[derive(Debug, Clone)]
pub struct SourceBinding {
    /// Exact compiler URI normalized to a repository relative path.
    pub path: String,
    pub file: PathBuf,
    pub expected_sha256: Option<ContentHash>,
    pub source_contexts: Vec<String>,
}
#[derive(Debug, Clone)]
pub struct RawCaptureOptions {
    pub revision: String,
    pub source_root: PathBuf,
    pub sources: Vec<SourceBinding>,
    pub workers: usize,
    pub max_raw_bytes: usize,
    pub max_source_bytes: usize,
    pub max_in_flight_bytes: u64,
    pub max_total_raw_bytes: u64,
    pub max_output_bytes: u64,
    pub max_fields: u64,
    pub max_depth: usize,
}
impl Default for RawCaptureOptions {
    fn default() -> Self {
        Self {
            revision: String::new(),
            source_root: PathBuf::from("."),
            sources: Vec::new(),
            workers: 1,
            max_raw_bytes: 64 * 1024 * 1024,
            max_source_bytes: 64 * 1024 * 1024,
            max_in_flight_bytes: 256 * 1024 * 1024,
            max_total_raw_bytes: 2 * 1024 * 1024 * 1024,
            max_output_bytes: 8 * 1024 * 1024 * 1024,
            max_fields: 4_000_000,
            max_depth: 200,
        }
    }
}
#[derive(Debug, Clone, Copy)]
pub struct RawCaptureRun {
    pub raw_inputs: usize,
    pub documents: usize,
    pub validated_sources: usize,
    pub raw_bytes: u64,
    pub output_bytes: u64,
    pub effective_workers: usize,
    pub producer: ContentHash,
}

pub fn producer() -> ContentHash {
    let mut digest = Sha256::new();
    digest.update(include_bytes!("raw_capture.rs"));
    digest.update(include_bytes!("semantic_wire.rs"));
    ContentHash(digest.finalize().into())
}

/// Produce the same document-wrapper contract consumed by `import_capture`,
/// directly from compiler protobufs. A failed call can leave partial output;
/// callers publish only after success. Each temporary worker output is dropped
/// after its bounded group is merged, and worker count obeys the owned-byte budget.
pub fn capture_raw(
    inputs: &[RawInput],
    output: &mut impl Write,
    options: &RawCaptureOptions,
) -> Result<RawCaptureRun, Error> {
    if options.revision.is_empty()
        || options.workers == 0
        || options.max_raw_bytes == 0
        || options.max_source_bytes == 0
        || options.max_depth == 0
    {
        return Err(Error::Invalid("raw capture options"));
    }
    let worker_bytes = (options.max_raw_bytes as u64)
        .checked_add(options.max_source_bytes as u64)
        .ok_or(Error::Limit("raw capture worker bytes"))?;
    let allowed = usize::try_from(options.max_in_flight_bytes / worker_bytes).unwrap_or(usize::MAX);
    let workers = options.workers.min(allowed).min(64);
    if workers == 0 {
        return Err(Error::Limit("raw capture in-flight bytes"));
    }
    let mut total_bytes = 0u64;
    for input in inputs {
        let metadata = fs::metadata(&input.path)?;
        if !metadata.is_file() || metadata.len() > options.max_raw_bytes as u64 {
            return Err(Error::Limit("raw SemanticDB bytes"));
        }
        total_bytes = total_bytes
            .checked_add(metadata.len())
            .ok_or(Error::Limit("raw capture total bytes"))?;
        if total_bytes > options.max_total_raw_bytes {
            return Err(Error::Limit("raw capture total bytes"));
        }
    }
    let mut bindings = HashMap::with_capacity(options.sources.len());
    for binding in &options.sources {
        if bindings.insert(binding.path.as_str(), binding).is_some() {
            return Err(Error::Invalid("duplicate raw capture source binding"));
        }
    }
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(workers)
        .build()
        .map_err(|e| Error::Message(e.to_string()))?;
    let mut writer = Output {
        inner: output,
        bytes: 0,
        maximum: options.max_output_bytes,
    };
    let mut run = RawCaptureRun {
        raw_inputs: inputs.len(),
        documents: 0,
        validated_sources: 0,
        raw_bytes: 0,
        output_bytes: 0,
        effective_workers: workers,
        producer: producer(),
    };
    for batch in inputs.chunks(workers) {
        let completed: Vec<_> = pool.install(|| {
            batch
                .par_iter()
                .map(|input| capture_one(input, &bindings, options, run.producer))
                .collect()
        });
        for completed in completed {
            let (temporary, documents, validated, raw_bytes) = completed?;
            io::copy(&mut File::open(&temporary.0)?, &mut writer)?;
            run.documents += documents;
            run.validated_sources += validated;
            run.raw_bytes += raw_bytes;
            if run.raw_bytes > options.max_total_raw_bytes {
                return Err(Error::Limit("raw capture total bytes"));
            }
        }
    }
    writer.flush()?;
    run.output_bytes = writer.bytes;
    Ok(run)
}

/// Explicit, hash-bound capture manifest. Paths resolve relative to the manifest
/// location, except `source_root` and source URI paths are never guessed by name.
pub fn capture_manifest(
    path: &Path,
    output: &mut impl Write,
    limits: &RawCaptureOptions,
) -> Result<RawCaptureRun, Error> {
    #[derive(Deserialize)]
    struct Input {
        path: PathBuf,
        #[serde(default)]
        sha256: Option<String>,
        semanticdb_input: String,
        #[serde(default)]
        input_target_contexts: Vec<String>,
    }
    #[derive(Deserialize)]
    struct Source {
        path: String,
        file: PathBuf,
        #[serde(default)]
        sha256: Option<String>,
        #[serde(default)]
        source_contexts: Vec<String>,
    }
    #[derive(Deserialize)]
    struct Manifest {
        version: u32,
        revision: String,
        source_root: PathBuf,
        inputs: Vec<Input>,
        #[serde(default)]
        sources: Vec<Source>,
    }
    let maximum = 16 * 1024 * 1024;
    if fs::metadata(path)?.len() > maximum {
        return Err(Error::Limit("raw capture manifest bytes"));
    }
    let manifest: Manifest =
        serde_json::from_reader(File::open(path)?.take(maximum + 1)).map_err(json_error)?;
    if manifest.version != 1 {
        return Err(Error::Invalid("raw capture manifest version"));
    }
    let parent = path.parent().unwrap_or(Path::new("."));
    let resolve = |path: PathBuf| {
        if path.is_absolute() {
            path
        } else {
            parent.join(path)
        }
    };
    let mut options = limits.clone();
    options.revision = manifest.revision;
    options.source_root = resolve(manifest.source_root);
    options.sources = manifest
        .sources
        .into_iter()
        .map(|source| {
            Ok(SourceBinding {
                path: source.path,
                file: resolve(source.file),
                expected_sha256: source
                    .sha256
                    .map(|hash| ContentHash::from_hex(&hash))
                    .transpose()?,
                source_contexts: source.source_contexts,
            })
        })
        .collect::<Result<_, Error>>()?;
    let inputs = manifest
        .inputs
        .into_iter()
        .map(|input| {
            Ok(RawInput {
                path: resolve(input.path),
                expected_sha256: input
                    .sha256
                    .map(|hash| ContentHash::from_hex(&hash))
                    .transpose()?,
                semanticdb_input: input.semanticdb_input,
                input_target_contexts: input.input_target_contexts,
            })
        })
        .collect::<Result<Vec<_>, Error>>()?;
    capture_raw(&inputs, output, &options)
}
fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut result = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        result.push(DIGITS[(byte >> 4) as usize] as char);
        result.push(DIGITS[(byte & 15) as usize] as char);
    }
    result
}
fn json_error(error: serde_json::Error) -> Error {
    Error::Message(error.to_string())
}
fn read_bounded(path: &Path, maximum: usize) -> Result<Vec<u8>, Error> {
    let mut file = File::open(path)?;
    let metadata = file.metadata()?;
    if !metadata.is_file() || metadata.len() > maximum as u64 {
        return Err(Error::Limit("raw capture file bytes"));
    }
    let length =
        usize::try_from(metadata.len()).map_err(|_| Error::Limit("raw capture file bytes"))?;
    let mut bytes = Vec::new();
    bytes
        .try_reserve_exact(length)
        .map_err(|_| Error::Limit("raw capture file allocation"))?;
    bytes.resize(length, 0);
    file.read_exact(&mut bytes)?;
    let mut extra = [0];
    if file.read(&mut extra)? != 0 {
        return Err(Error::Invalid("raw capture file grew while reading"));
    }
    Ok(bytes)
}
fn capture_one(
    input: &RawInput,
    bindings: &HashMap<&str, &SourceBinding>,
    options: &RawCaptureOptions,
    producer: ContentHash,
) -> Result<(Temporary, usize, usize, u64), Error> {
    let raw = read_bounded(&input.path, options.max_raw_bytes)?;
    let raw_hash = ContentHash(Sha256::digest(&raw).into());
    if input
        .expected_sha256
        .is_some_and(|expected| expected != raw_hash)
    {
        return Err(Error::Invalid("raw SemanticDB SHA256 mismatch"));
    }
    let mut fields = 0;
    validate("TextDocuments", &raw, options, 0, &mut fields)?;
    let (temporary, file) = temporary()?;
    let mut writer = Output {
        inner: BufWriter::with_capacity(128 * 1024, file),
        bytes: 0,
        maximum: options.max_output_bytes,
    };
    let raw_hash = raw_hash.to_string();
    let producer = producer.to_string();
    let mut documents = 0;
    let mut validated = 0;
    for field in Wire::new(&raw) {
        let field = field?;
        if field.number != 1 {
            return Err(Error::Invalid("TextDocuments field"));
        }
        let bytes = field.bytes()?;
        let uri = text_field(bytes, 2)?.ok_or(Error::Invalid("SemanticDB URI missing"))?;
        let path = source_path(uri, &options.source_root)?;
        let binding = bindings.get(path.as_str()).copied();
        let file = binding
            .map(|binding| binding.file.clone())
            .or_else(|| safe_source_file(&options.source_root, &path));
        let source = match file {
            Some(file) if file.is_file() => Some(read_bounded(&file, options.max_source_bytes)?),
            _ => None,
        };
        let embedded = text_field(bytes, 3)?;
        let source_text = source
            .as_deref()
            .map(std::str::from_utf8)
            .transpose()
            .map_err(|_| Error::Invalid("UTF-8 source text"))?
            .or(embedded);
        let source_sha =
            source_text.map(|source| ContentHash(Sha256::digest(source.as_bytes()).into()));
        if binding
            .and_then(|binding| binding.expected_sha256)
            .is_some_and(|expected| source_sha != Some(expected))
        {
            return Err(Error::Invalid("raw capture source SHA256 mismatch"));
        }
        let source_md5 = source_text.map(|source| hex(&Md5::digest(source.as_bytes())));
        let expected_md5 = text_field(bytes, 11)?;
        let matches = source_md5
            .as_deref()
            .zip(expected_md5)
            .is_some_and(|(source, expected)| source.eq_ignore_ascii_case(expected));
        #[derive(Serialize)]
        struct Row<'a> {
            path: &'a str,
            revision: &'a str,
            semanticdb_input: &'a str,
            semanticdb_input_sha256: &'a str,
            capture_producer_sha256: &'a str,
            source_sha256: Option<String>,
            source_md5: Option<&'a str>,
            source_md5_matches: bool,
            source_contexts: &'a [String],
            input_target_contexts: &'a [String],
            source_text: Option<&'a str>,
            enclosing_member_attribution: &'static str,
            document: Message<'a>,
        }
        let row = Row {
            path: &path,
            revision: &options.revision,
            semanticdb_input: &input.semanticdb_input,
            semanticdb_input_sha256: &raw_hash,
            capture_producer_sha256: &producer,
            source_sha256: source_sha.map(|hash| hash.to_string()),
            source_md5: source_md5.as_deref(),
            source_md5_matches: matches,
            source_contexts: binding.map_or(&[], |binding| binding.source_contexts.as_slice()),
            input_target_contexts: &input.input_target_contexts,
            source_text,
            enclosing_member_attribution: "Definition ranges cover name tokens; join validated source AST spans separately.",
            document: Message {
                name: "TextDocument",
                bytes,
            },
        };
        serde_json::to_writer(&mut writer, &row).map_err(json_error)?;
        writer.write_all(b"\n")?;
        documents += 1;
        validated += usize::from(matches);
    }
    writer.flush()?;
    Ok((temporary, documents, validated, raw.len() as u64))
}
fn source_path(uri: &str, source_root: &Path) -> Result<String, Error> {
    let path = uri
        .strip_prefix("file://localhost/")
        .map(|path| format!("/{path}"))
        .or_else(|| uri.strip_prefix("file://").map(str::to_owned))
        .unwrap_or_else(|| uri.to_owned());
    let mut bytes = Vec::with_capacity(path.len());
    let raw = path.as_bytes();
    let mut index = 0;
    while index < raw.len() {
        if raw[index] == b'%' {
            let pair = raw
                .get(index + 1..index + 3)
                .ok_or(Error::Invalid("URI percent escape"))?;
            let value = |byte: u8| match byte {
                b'0'..=b'9' => Some(byte - b'0'),
                b'a'..=b'f' => Some(byte - b'a' + 10),
                b'A'..=b'F' => Some(byte - b'A' + 10),
                _ => None,
            };
            bytes.push(
                value(pair[0])
                    .zip(value(pair[1]))
                    .map(|(a, b)| a * 16 + b)
                    .ok_or(Error::Invalid("URI percent escape"))?,
            );
            index += 3;
        } else {
            bytes.push(raw[index]);
            index += 1;
        }
    }
    let decoded = String::from_utf8(bytes).map_err(|_| Error::Invalid("UTF-8 SemanticDB URI"))?;
    if Path::new(&decoded).is_absolute() {
        if let (Ok(root), Ok(source)) = (fs::canonicalize(source_root), fs::canonicalize(&decoded))
        {
            if let Ok(relative) = source.strip_prefix(root) {
                if !relative.as_os_str().is_empty() {
                    return relative
                        .to_str()
                        .map(str::to_owned)
                        .ok_or(Error::Invalid("UTF-8 source path"));
                }
            }
        }
    }
    Ok(decoded)
}
fn safe_source_file(root: &Path, path: &str) -> Option<PathBuf> {
    let relative = Path::new(path);
    if relative.is_absolute()
        || relative
            .components()
            .any(|component| !matches!(component, Component::Normal(_)))
        || path.contains("://")
    {
        return None;
    }
    let root = fs::canonicalize(root).ok()?;
    let source = fs::canonicalize(root.join(relative)).ok()?;
    source.starts_with(&root).then_some(source)
}
struct Temporary(PathBuf);
impl Drop for Temporary {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}
fn temporary() -> Result<(Temporary, File), Error> {
    loop {
        let path = std::env::temp_dir().join(format!(
            ".selector-raw-{}-{}.jsonl",
            std::process::id(),
            NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
        ));
        match File::options().write(true).create_new(true).open(&path) {
            Ok(file) => return Ok((Temporary(path), file)),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(error.into()),
        }
    }
}
struct Output<W> {
    inner: W,
    bytes: u64,
    maximum: u64,
}
impl<W: Write> Write for Output<W> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        if self
            .bytes
            .checked_add(bytes.len() as u64)
            .is_none_or(|next| next > self.maximum)
        {
            return Err(io::Error::other("raw capture output byte limit"));
        }
        let count = self.inner.write(bytes)?;
        self.bytes += count as u64;
        Ok(count)
    }
    fn flush(&mut self) -> io::Result<()> {
        self.inner.flush()
    }
}

fn validate(
    name: &str,
    bytes: &[u8],
    options: &RawCaptureOptions,
    depth: usize,
    total: &mut u64,
) -> Result<(), Error> {
    crate::semantic_wire::validate(
        name,
        bytes,
        &crate::semantic_wire::Limits {
            max_depth: options.max_depth,
            max_fields: options.max_fields,
        },
        depth,
        total,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{Value as Json, json};
    fn checked(name: &'static str, bytes: &[u8]) -> Result<Json, Error> {
        validate(name, bytes, &RawCaptureOptions::default(), 0, &mut 0)?;
        serde_json::to_value(Message { name, bytes }).map_err(json_error)
    }
    fn put_varint(mut value: u64, bytes: &mut Vec<u8>) {
        loop {
            let next = (value & 127) as u8;
            value >>= 7;
            bytes.push(next | if value == 0 { 0 } else { 128 });
            if value == 0 {
                break;
            }
        }
    }
    #[test]
    fn strict_wire_validation_preserves_negative_ranges_and_default_presence() {
        assert_eq!(
            checked("Range", &[]).unwrap(),
            json!({"start_line":0,"start_character":0,"end_line":0,"end_character":0})
        );
        for raw in [u32::MAX as u64, u64::MAX] {
            let mut bytes = vec![8];
            put_varint(raw, &mut bytes);
            assert_eq!(checked("Range", &bytes).unwrap()["start_line"], -1);
        }
        let mut overflow = vec![8];
        put_varint((1u64 << 32) + 5, &mut overflow);
        assert!(checked("Range", &overflow).is_err());
        for malformed in [
            &[0u8][..],
            &[0x0a, 8][..],
            &[8, 0x80][..],
            &[0x0b][..],
            &[0x08, 1, 0x08, 2][..],
        ] {
            assert!(checked("Range", malformed).is_err());
        }
        assert!(checked("SymbolOccurrence", &[0x0a, 0, 0x0a, 0]).is_err());
        assert!(checked("TextDocuments", &[0x12, 0]).is_err());
        assert!(checked("TextDocument", &[0x12, 1, 0xff]).is_err());
    }
    #[test]
    fn constants_are_typed_presence_aware_and_float_bits_are_preserved() {
        assert_eq!(checked("Constant", &[]).unwrap(), json!({}));
        assert_eq!(
            checked("Constant", &[0x12, 0]).unwrap(),
            json!({"boolean_constant":{"value":false}})
        );
        assert_eq!(
            checked("Constant", &[0x0a, 0]).unwrap(),
            json!({"unit_constant":{}})
        );
        assert_eq!(
            checked("Constant", &[0x52, 0]).unwrap(),
            json!({"string_constant":{"value":""}})
        );
        assert!(checked("Constant", &[0x12, 0, 0x0a, 0]).is_err());
        let mut floating = vec![0x42, 5, 0x0d];
        floating.extend_from_slice(&f32::NAN.to_le_bytes());
        let decoded = checked("Constant", &floating).unwrap();
        assert!(decoded["float_constant"].get("value").is_none());
        assert_eq!(
            decoded["float_constant"]["ieee754_bits_le"],
            hex(&f32::NAN.to_le_bytes())
        );
    }
    #[test]
    fn depth_field_and_owned_byte_limits_fail_before_unbounded_growth() {
        let options = RawCaptureOptions {
            max_fields: 1,
            ..RawCaptureOptions::default()
        };
        assert!(validate("Range", &[8, 0, 16, 0], &options, 0, &mut 0).is_err());
        let options = RawCaptureOptions {
            max_depth: 1,
            ..RawCaptureOptions::default()
        };
        assert!(validate("TextDocuments", &[0x0a, 2, 0x2a, 0], &options, 0, &mut 0).is_err());
        let mut output = Vec::new();
        let options = RawCaptureOptions {
            revision: "r".into(),
            max_in_flight_bytes: 1,
            ..RawCaptureOptions::default()
        };
        assert!(capture_raw(&[], &mut output, &options).is_err());
    }
    fn normalize_legacy(value: &mut Json) {
        match value {
            Json::Object(fields) => {
                for (name, value) in fields.iter_mut() {
                    if name.ends_with("_constant") {
                        *value = Json::Null;
                        continue;
                    }
                    if name == "range" {
                        if let Some(fields) = value.as_object_mut() {
                            for key in
                                ["start_line", "start_character", "end_line", "end_character"]
                            {
                                fields.entry(key).or_insert(json!(0));
                            }
                        }
                    }
                    normalize_legacy(value);
                }
            }
            Json::Array(values) => {
                for value in values {
                    normalize_legacy(value);
                }
            }
            _ => {}
        }
    }
    #[test]
    fn genuine_raw_clock_and_spliceapp_replay_matches_captured_document_semantics() {
        let fixture = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/compiler-smoke");
        let original = fs::read_to_string(fixture.join("documents.jsonl")).unwrap();
        let rows: Vec<Json> = original
            .lines()
            .map(|line| serde_json::from_str(line).unwrap())
            .collect();
        let mut inputs = Vec::new();
        let mut sources = Vec::new();
        for row in &rows {
            let hash = row["semanticdb_input_sha256"].as_str().unwrap();
            let path = row["path"].as_str().unwrap();
            inputs.push(RawInput {
                path: fixture.join("raw").join(format!("{hash}.semanticdb")),
                expected_sha256: Some(ContentHash::from_hex(hash).unwrap()),
                semanticdb_input: row["semanticdb_input"].as_str().unwrap().into(),
                input_target_contexts: serde_json::from_value(row["input_target_contexts"].clone())
                    .unwrap(),
            });
            sources.push(SourceBinding {
                path: path.into(),
                file: fixture.join(if path.ends_with("/Clock.scala") {
                    "clock.scala"
                } else {
                    "splice-app.scala"
                }),
                expected_sha256: Some(
                    ContentHash::from_hex(row["source_sha256"].as_str().unwrap()).unwrap(),
                ),
                source_contexts: serde_json::from_value(row["source_contexts"].clone()).unwrap(),
            });
        }
        let options = RawCaptureOptions {
            revision: rows[0]["revision"].as_str().unwrap().into(),
            source_root: fixture.clone(),
            sources,
            workers: 8,
            ..RawCaptureOptions::default()
        };
        let mut output = Vec::new();
        let run = capture_raw(&inputs, &mut output, &options).unwrap();
        assert_eq!(run.documents, 2);
        assert_eq!(run.validated_sources, 2);
        assert_eq!(run.effective_workers, 2);
        let decoded: Vec<Json> = std::str::from_utf8(&output)
            .unwrap()
            .lines()
            .map(|line| serde_json::from_str(line).unwrap())
            .collect();
        for (actual, expected) in decoded.iter().zip(&rows) {
            for field in [
                "path",
                "revision",
                "semanticdb_input",
                "semanticdb_input_sha256",
                "source_sha256",
                "source_md5",
                "source_md5_matches",
                "source_contexts",
                "input_target_contexts",
                "source_text",
            ] {
                assert_eq!(actual[field], expected[field], "wrapper field {field}");
            }
            let mut actual = actual["document"].clone();
            let mut expected = expected["document"].clone();
            normalize_legacy(&mut actual);
            normalize_legacy(&mut expected);
            assert_eq!(actual, expected, "raw compiler document projection");
        }
        let temporary = tempfile::tempdir().unwrap();
        let normalized = temporary.path().join("native.jsonl");
        fs::write(&normalized, &output).unwrap();
        let options = crate::ExtractOptions {
            workers: 2,
            ..crate::ExtractOptions::default()
        };
        let native = crate::import_capture(&normalized, None, &options).unwrap();
        let legacy =
            crate::import_capture(&fixture.join("documents.jsonl"), None, &options).unwrap();
        assert_eq!(native.files.len(), legacy.files.len());
        assert_eq!(native.symbols.len(), legacy.symbols.len());
        assert_eq!(native.occurrences.len(), legacy.occurrences.len());
        assert_eq!(native.relations.len(), legacy.relations.len());
        for (a, b) in native.files.iter().zip(&legacy.files) {
            assert_eq!(
                (
                    native.text(a.path),
                    native.text(a.source),
                    native.text(a.context),
                    a.source_hash,
                    a.flags
                ),
                (
                    legacy.text(b.path),
                    legacy.text(b.source),
                    legacy.text(b.context),
                    b.source_hash,
                    b.flags
                )
            );
        }
        for (a, b) in native.symbols.iter().zip(&legacy.symbols) {
            assert_eq!(
                (
                    native.text(a.name),
                    native.text(a.display),
                    native.symbol_name(a.owner),
                    a.kind,
                    a.properties,
                    a.span,
                    a.flags
                ),
                (
                    legacy.text(b.name),
                    legacy.text(b.display),
                    legacy.symbol_name(b.owner),
                    b.kind,
                    b.properties,
                    b.span,
                    b.flags
                )
            );
        }
        for (a, b) in native.occurrences.iter().zip(&legacy.occurrences) {
            assert_eq!(
                (
                    a.file,
                    native.symbol_name(a.symbol),
                    a.span,
                    a.role,
                    a.ordinal
                ),
                (
                    b.file,
                    legacy.symbol_name(b.symbol),
                    b.span,
                    b.role,
                    b.ordinal
                )
            );
        }
        for (a, b) in native.relations.iter().zip(&legacy.relations) {
            assert_eq!(
                (
                    native.symbol_name(a.source),
                    native.symbol_name(a.target),
                    a.kind,
                    a.file
                ),
                (
                    legacy.symbol_name(b.source),
                    legacy.symbol_name(b.target),
                    b.kind,
                    b.file
                )
            );
        }
    }
}
