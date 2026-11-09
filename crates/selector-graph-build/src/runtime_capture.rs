//! Native bounded producer for model inputs from an exact immutable Git tree.
use super::*;
use std::io::{Read, Write};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

pub struct RuntimeCaptureOptions<'a> {
    pub repository: &'a Path,
    pub revision: &'a str,
    pub ci_catalogue: &'a Path,
    /// Optional immutable historical auxiliary export. Exact Git blob hashes
    /// are recomputed before these bytes can replace a missing local object.
    pub auxiliary_sources: Option<&'a Path>,
    pub output: &'a Path,
    /// Explicit exporter assertion; callers should leave this false without a
    /// complete compiler/source-coverage receipt for the captured revision.
    pub compiler_inventory_complete: bool,
}
pub struct RuntimeCaptureReceipt {
    pub revision: String,
    pub manifest: PathBuf,
    pub manifest_sha256: ContentHash,
    pub sources: usize,
    pub suite_catalogues: usize,
    pub source_bytes: u64,
    pub captured_source_fallbacks: usize,
}
fn git(repository: &Path, args: &[&str], maximum: u64) -> Result<Vec<u8>, Error> {
    let mut child = Command::new("git")
        .arg("--no-pager")
        .args(["-c", "remote.origin.promisor=false"])
        .env("GIT_NO_LAZY_FETCH", "1")
        .arg("-C")
        .arg(repository)
        .args(args)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    let stderr = child
        .stderr
        .take()
        .ok_or(Error::Invalid("Git stderr pipe"))?;
    // Drain errors concurrently so a failing subprocess cannot block on its
    // stderr pipe. Retain only a bounded diagnostic prefix.
    let errors = std::thread::spawn(move || -> Result<Vec<u8>, std::io::Error> {
        let mut stream = stderr;
        let mut buffer = [0u8; 8192];
        let mut result = Vec::new();
        loop {
            let size = stream.read(&mut buffer)?;
            if size == 0 {
                break;
            }
            let keep = size.min((16 * 1024usize).saturating_sub(result.len()));
            result.extend_from_slice(&buffer[..keep]);
        }
        Ok(result)
    });
    let mut bytes = Vec::new();
    let read = child
        .stdout
        .take()
        .ok_or(Error::Invalid("Git stdout pipe"))?
        .take(maximum + 1)
        .read_to_end(&mut bytes);
    if read.is_err() || bytes.len() as u64 > maximum {
        let _ = child.kill();
        let _ = child.wait();
        let _ = errors.join();
        read?;
        return Err(Error::Limit("Git runtime capture bytes"));
    }
    let status = child.wait()?;
    let errors = errors
        .join()
        .map_err(|_| Error::Invalid("Git stderr reader"))??;
    if !status.success() {
        return Err(Error::Message(format!(
            "Git runtime capture failed: {}",
            String::from_utf8_lossy(&errors).trim()
        )));
    }
    Ok(bytes)
}
static NEXT: AtomicU64 = AtomicU64::new(0);
struct Temporary(PathBuf);
impl Drop for Temporary {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}
fn stage(parent: &Path, bytes: &[u8]) -> Result<Temporary, Error> {
    let path = parent.join(format!(
        ".runtime-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    let temporary = Temporary(path);
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&temporary.0)?;
    file.write_all(bytes)?;
    file.sync_all()?;
    Ok(temporary)
}
fn blob(parent: &Path, bytes: &[u8]) -> Result<(String, String), Error> {
    let sha = ContentHash(Sha256::digest(bytes).into()).to_string();
    let relative = format!("runtime-inputs/{sha}");
    let path = parent.join(&relative);
    if !path.exists() {
        let temporary = stage(&parent.join("runtime-inputs"), bytes)?;
        let mut permissions = std::fs::metadata(&temporary.0)?.permissions();
        permissions.set_readonly(true);
        std::fs::set_permissions(&temporary.0, permissions)?;
        if let Err(error) = std::fs::hard_link(&temporary.0, &path) {
            if error.kind() != std::io::ErrorKind::AlreadyExists {
                return Err(error.into());
            }
        }
    }
    let mut existing = std::fs::File::open(&path)?;
    if existing.metadata()?.len() != bytes.len() as u64 {
        return Err(Error::Invalid("runtime content-addressed blob length"));
    }
    let mut hash = Sha256::new();
    let mut buffer = [0u8; 16 * 1024];
    let mut observed = 0u64;
    loop {
        let size = existing.read(&mut buffer)?;
        if size == 0 {
            break;
        }
        observed += size as u64;
        if observed > bytes.len() as u64 {
            return Err(Error::Invalid("runtime content-addressed blob changed"));
        }
        hash.update(&buffer[..size]);
    }
    if observed != bytes.len() as u64 || ContentHash(hash.finalize().into()).to_string() != sha {
        return Err(Error::Invalid(
            "runtime content-addressed blob collision or corruption",
        ));
    }
    Ok((relative, sha))
}
fn model_source(path: &str) -> bool {
    path == "build.sbt"
        || path.starts_with("apps/")
            && path.contains("/src/main/openapi/")
            && (path.ends_with(".yaml") || path.ends_with(".yml"))
}
#[derive(serde::Deserialize)]
struct CapturedSource {
    path: String,
    text: String,
    sha256: String,
    git_blob_sha: String,
    bytes: usize,
}
#[derive(serde::Deserialize)]
struct AuxiliaryCapture {
    schema_version: String,
    #[serde(deserialize_with = "model_capture_rows")]
    sources: BTreeMap<String, CapturedSource>,
}
fn model_capture_rows<'de, D: serde::Deserializer<'de>>(
    deserializer: D,
) -> Result<BTreeMap<String, CapturedSource>, D::Error> {
    struct Rows;
    impl<'de> serde::de::Visitor<'de> for Rows {
        type Value = BTreeMap<String, CapturedSource>;
        fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
            formatter.write_str("bounded auxiliary source rows")
        }
        fn visit_seq<A: serde::de::SeqAccess<'de>>(
            self,
            mut sequence: A,
        ) -> Result<Self::Value, A::Error> {
            let mut result = BTreeMap::new();
            let mut count = 0;
            while let Some(row) = sequence.next_element::<CapturedSource>()? {
                count += 1;
                if count > 100_000 {
                    return Err(serde::de::Error::custom("auxiliary source count limit"));
                }
                if model_source(&row.path) {
                    if row.text.len() != row.bytes
                        || row.text.len() as u64 > MAX_FILE
                        || ContentHash::from_hex(&row.sha256).ok()
                            != Some(ContentHash(Sha256::digest(row.text.as_bytes()).into()))
                        || !git_blob_matches(row.text.as_bytes(), &row.git_blob_sha)
                    {
                        return Err(serde::de::Error::custom(
                            "auxiliary source SHA256 or Git blob hash mismatch",
                        ));
                    }
                    if result.insert(row.path.clone(), row).is_some() {
                        return Err(serde::de::Error::custom("duplicate auxiliary source path"));
                    }
                }
            }
            Ok(result)
        }
    }
    deserializer.deserialize_seq(Rows)
}
fn git_blob_matches(bytes: &[u8], expected: &str) -> bool {
    let mut hash = sha1::Sha1::new();
    hash.update(format!("blob {}\0", bytes.len()));
    hash.update(bytes);
    let hash = hash.finalize();
    let mut text = [0u8; 40];
    let digits = b"0123456789abcdef";
    for (index, byte) in hash.iter().copied().enumerate() {
        text[index * 2] = digits[(byte >> 4) as usize];
        text[index * 2 + 1] = digits[(byte & 15) as usize];
    }
    expected.as_bytes() == text
}
fn auxiliary_capture(path: &Path) -> Result<BTreeMap<String, CapturedSource>, Error> {
    let mut total = 0;
    let bytes = read_bounded(path, MAX_FILE, &mut total)?;
    let source: Box<dyn Read> = if bytes.starts_with(&[0x1f, 0x8b]) {
        Box::new(flate2::read::GzDecoder::new(std::io::Cursor::new(bytes)))
    } else {
        Box::new(std::io::Cursor::new(bytes))
    };
    let mut source = source.take(MAX_FILE + 1);
    let capture: AuxiliaryCapture = serde_json::from_reader(&mut source)
        .map_err(|error| Error::Message(format!("runtime auxiliary capture JSON: {error}")))?;
    if source.limit() == 0 {
        return Err(Error::Limit("runtime auxiliary decoded bytes"));
    }
    if capture.schema_version != "compiler-selector-auxiliary-sources/v1" {
        return Err(Error::Invalid("runtime auxiliary capture schema"));
    }
    Ok(capture.sources)
}

/// Capture compiler-independent OpenAPI/build metadata and exact CI suite lists.
/// Unrelated Daml/frontend/config files are not declared covered by this model
/// producer. A delta to any such uncaptured path remains an explicit unknown.
pub fn capture_git_runtime(
    options: RuntimeCaptureOptions<'_>,
) -> Result<RuntimeCaptureReceipt, Error> {
    if options.revision.is_empty()
        || options.revision.starts_with('-')
        || options.revision.contains(['\0', '\n', '\r'])
    {
        return Err(Error::Invalid("runtime Git revision"));
    }
    let revision = git(
        options.repository,
        &[
            "rev-parse",
            "--verify",
            &format!("{}^{{commit}}", options.revision),
        ],
        1024,
    )?;
    let revision = std::str::from_utf8(&revision)
        .map_err(|_| Error::Invalid("Git revision UTF-8"))?
        .trim()
        .to_owned();
    if revision.len() != 40 || !revision.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err(Error::Invalid("runtime Git commit SHA"));
    }
    let mut total = 0;
    let ci_bytes = read_bounded(options.ci_catalogue, MAX_FILE, &mut total)?;
    let catalogue: CiCatalogue = serde_json::from_slice(&ci_bytes)
        .map_err(|error| Error::Message(format!("runtime CI catalogue JSON: {error}")))?;
    let names: BTreeSet<_> = catalogue
        .families
        .iter()
        .flat_map(|family| family.suites.iter().cloned())
        .collect();
    if catalogue.schema_version != "compiler-ci-catalogue/v1"
        || !catalogue.complete
        || catalogue.revision != revision
        || names != catalogue.suite_names
    {
        return Err(Error::Invalid(
            "runtime capture requires a complete matching CI catalogue",
        ));
    }
    let tree = git(
        options.repository,
        &["ls-tree", "-r", "-z", "--full-tree", &revision],
        32 * 1024 * 1024,
    )?;
    let catalogue_paths: BTreeSet<_> = catalogue
        .families
        .iter()
        .map(|family| family.catalogue.as_str())
        .collect();
    let captured = options
        .auxiliary_sources
        .map(auxiliary_capture)
        .transpose()?
        .unwrap_or_default();
    let mut captured_source_fallbacks = 0;
    if catalogue_paths
        .iter()
        .any(|path| !root_catalogue_path(path))
    {
        return Err(Error::Invalid("runtime capture CI catalogue path"));
    }
    let parent = options
        .output
        .parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    std::fs::create_dir_all(parent.join("runtime-inputs"))?;
    let (ci_file, ci_sha) = blob(parent, &ci_bytes)?;
    let mut sources = Vec::new();
    let mut suite_catalogues = Vec::new();
    let mut observed = BTreeSet::new();
    for row in tree.split(|byte| *byte == 0).filter(|row| !row.is_empty()) {
        let row = std::str::from_utf8(row).map_err(|_| Error::Invalid("Git tree path UTF-8"))?;
        let (metadata, path) = row
            .split_once('\t')
            .ok_or(Error::Invalid("Git tree entry"))?;
        if !model_source(path) && !catalogue_paths.contains(path) {
            continue;
        }
        if !metadata.starts_with("100644 blob ") && !metadata.starts_with("100755 blob ") {
            return Err(Error::Invalid(
                "runtime input is not a regular tracked Git blob",
            ));
        }
        let bytes = if let Some(source) = captured
            .get(path)
            .filter(|source| metadata.rsplit(' ').next() == Some(source.git_blob_sha.as_str()))
        {
            captured_source_fallbacks += 1;
            std::borrow::Cow::Borrowed(source.text.as_bytes())
        } else {
            std::borrow::Cow::Owned(git(
                options.repository,
                &["show", &format!("{revision}:{path}")],
                MAX_FILE,
            )?)
        };
        if total
            .checked_add(bytes.len() as u64)
            .is_none_or(|value| value > MAX_TOTAL)
        {
            return Err(Error::Limit("runtime capture total bytes"));
        }
        total += bytes.len() as u64;
        std::str::from_utf8(&bytes).map_err(|_| Error::Invalid("runtime Git source UTF-8"))?;
        let (file, sha) = blob(parent, &bytes)?;
        let entry = serde_json::json!({"path":path,"file":file,"sha256":sha});
        if catalogue_paths.contains(path) {
            let text = std::str::from_utf8(&bytes)
                .map_err(|_| Error::Invalid("runtime catalogue UTF-8"))?;
            let expected: BTreeSet<_> = catalogue
                .families
                .iter()
                .filter(|family| family.catalogue == path)
                .flat_map(|family| family.suites.iter().cloned())
                .collect();
            if catalogue_names(text)? != expected
                || !catalogue.source_receipts.iter().any(|receipt| {
                    receipt.path.file_name() == Some(std::ffi::OsStr::new(path))
                        && receipt.bytes == bytes.len() as u64
                        && receipt.sha256 == sha
                })
            {
                return Err(Error::Invalid(
                    "tracked suite list differs from captured CI catalogue receipt",
                ));
            }
            observed.insert(path);
            suite_catalogues.push(entry);
        } else {
            sources.push(entry);
        }
    }
    if observed != catalogue_paths {
        return Err(Error::Invalid(
            "captured CI suite catalogue is absent from Git revision",
        ));
    }
    let source_count = sources.len();
    let catalogue_count = suite_catalogues.len();
    let manifest = serde_json::json!({"version":1,"revision":revision,"sources":sources,"suite_catalogues":suite_catalogues,
        "ci_catalogue":{"file":ci_file,"sha256":ci_sha},"compiler_inventory_complete":options.compiler_inventory_complete});
    let bytes =
        serde_json::to_vec_pretty(&manifest).map_err(|error| Error::Message(error.to_string()))?;
    if bytes.len() as u64 > MAX_MANIFEST {
        return Err(Error::Limit("runtime capture manifest bytes"));
    }
    let temporary = stage(parent, &bytes)?;
    std::fs::rename(&temporary.0, options.output)?;
    Ok(RuntimeCaptureReceipt {
        revision,
        manifest: options.output.to_owned(),
        manifest_sha256: ContentHash(Sha256::digest(bytes).into()),
        sources: source_count,
        suite_catalogues: catalogue_count,
        source_bytes: total,
        captured_source_fallbacks,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn producer_reads_exact_git_blobs_and_rejects_unmatched_catalogue_receipts() {
        let directory = tempfile::tempdir().unwrap();
        let repo = directory.path().join("repo");
        std::fs::create_dir_all(&repo).unwrap();
        git(&repo, &["init", "-q"], 1024).unwrap();
        std::fs::write(repo.join("build.sbt"), "val example = 1\n").unwrap();
        let schema = repo.join("apps/example/src/main/openapi/api.yaml");
        std::fs::create_dir_all(schema.parent().unwrap()).unwrap();
        std::fs::write(&schema, "openapi: 3.0.3\npaths: {}\n").unwrap();
        let log = b"example.Suite\n";
        std::fs::write(repo.join("test-full-class-names.log"), log).unwrap();
        git(&repo, &["add", "."], 1024).unwrap();
        git(
            &repo,
            &[
                "-c",
                "user.name=Selector Test",
                "-c",
                "user.email=selector@example.invalid",
                "commit",
                "-q",
                "-m",
                "fixture",
            ],
            1024,
        )
        .unwrap();
        let revision = String::from_utf8(git(&repo, &["rev-parse", "HEAD"], 1024).unwrap())
            .unwrap()
            .trim()
            .to_owned();
        let catalogue = serde_json::json!({"schema_version":"compiler-ci-catalogue/v1","revision":revision,"complete":true,
            "suite_names":["example.Suite"],"families":[{"catalogue":"test-full-class-names.log","suites":["example.Suite"]}],
            "source_receipts":[{"path":"/capture/catalog/test-full-class-names.log","bytes":log.len(),"sha256":ContentHash(Sha256::digest(log).into()).to_string()}]});
        let input = directory.path().join("ci.json");
        std::fs::write(&input, serde_json::to_vec(&catalogue).unwrap()).unwrap();
        let output = directory.path().join("out/runtime.json");
        let capture = || {
            capture_git_runtime(RuntimeCaptureOptions {
                repository: &repo,
                revision: &revision,
                ci_catalogue: &input,
                auxiliary_sources: None,
                output: &output,
                compiler_inventory_complete: false,
            })
        };
        let result = capture().unwrap();
        assert_eq!(result.sources, 2);
        assert_eq!(result.suite_catalogues, 1);
        let before = std::fs::read(&output).unwrap();
        std::fs::write(&schema, "worktree has changed\n").unwrap();
        capture().unwrap();
        assert_eq!(before, std::fs::read(&output).unwrap());
        let git_hash = String::from_utf8(
            git(
                &repo,
                &["rev-parse", &format!("{revision}:build.sbt")],
                1024,
            )
            .unwrap(),
        )
        .unwrap()
        .trim()
        .to_owned();
        let auxiliary = directory.path().join("auxiliary.json.gz");
        let text = "val example = 1\n";
        let capture_json = serde_json::json!({"schema_version":"compiler-selector-auxiliary-sources/v1","sources":[
            {"path":"build.sbt","text":text,"bytes":text.len(),"sha256":ContentHash(Sha256::digest(text.as_bytes()).into()).to_string(),"git_blob_sha":git_hash}]});
        let mut compressed = flate2::write::GzEncoder::new(Vec::new(), flate2::Compression::fast());
        compressed
            .write_all(&serde_json::to_vec(&capture_json).unwrap())
            .unwrap();
        std::fs::write(&auxiliary, compressed.finish().unwrap()).unwrap();
        let result = capture_git_runtime(RuntimeCaptureOptions {
            repository: &repo,
            revision: &revision,
            ci_catalogue: &input,
            auxiliary_sources: Some(&auxiliary),
            output: &output,
            compiler_inventory_complete: false,
        })
        .unwrap();
        assert_eq!(result.captured_source_fallbacks, 1);
        assert_eq!(before, std::fs::read(&output).unwrap());
        let mut tampered = capture_json;
        tampered["sources"][0]["text"] = serde_json::json!("unbound");
        std::fs::write(&auxiliary, serde_json::to_vec(&tampered).unwrap()).unwrap();
        assert!(auxiliary_capture(&auxiliary).is_err());
        let mut catalogue = catalogue;
        catalogue["source_receipts"] = serde_json::json!([]);
        std::fs::write(&input, serde_json::to_vec(&catalogue).unwrap()).unwrap();
        assert!(capture().is_err());
    }
}
