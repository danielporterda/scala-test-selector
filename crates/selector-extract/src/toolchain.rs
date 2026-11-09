//! Native orchestration of the existing, genuine Scalameta structural exporter.
//!
//! Compile prerequisite: cached Scala 2.13.18, Scalameta 4.15.2 and ujson 4.0.2
//! jars listed below, plus a Java runtime. No downloader or Python process is
//! involved. Compiler identities still come from SemanticDB, never syntax names.
//! JSON input batches and returned source rows have independent byte limits.
//! A failed run can leave partial caller output: publish the output only on success.

use selector_types::{ContentHash, Error};
use serde::de::{DeserializeSeed, MapAccess, SeqAccess, Visitor};
use serde::{Deserialize, Serialize};
use serde_json::value::RawValue;
use sha2::{Digest, Sha256};
use std::borrow::Cow;
use std::cell::Cell;
use std::collections::HashMap;
use std::fmt;
use std::fs::{self, File, OpenOptions};
use std::io::{self, BufReader, BufWriter, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::rc::Rc;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::time::{Duration, Instant};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, Clone)]
pub struct SyntaxLimits {
    pub java_heap_bytes: u64,
    pub parallel_java_heap_bytes: u64,
    pub batch_source_bytes: usize,
    pub max_source_bytes: usize,
    pub max_total_source_bytes: u64,
    pub max_sources: usize,
    pub max_input_bytes: u64,
    pub max_output_bytes: u64,
    pub max_output_row_bytes: usize,
    pub max_diagnostic_bytes: usize,
    pub max_tool_file_bytes: u64,
    pub max_tool_total_bytes: u64,
    pub compile_timeout: Duration,
    pub parse_timeout: Duration,
}
impl Default for SyntaxLimits {
    fn default() -> Self {
        Self {
            java_heap_bytes: 1024 * 1024 * 1024,
            parallel_java_heap_bytes: 4 * 1024 * 1024 * 1024,
            // Scalameta trees and the structural JSON expand source bytes many
            // times. The real corpus exceeds a 1 GiB JVM with 16 MiB batches.
            batch_source_bytes: 2 * 1024 * 1024,
            max_source_bytes: 64 * 1024 * 1024,
            max_total_source_bytes: 2 * 1024 * 1024 * 1024,
            max_sources: 65_536,
            max_input_bytes: 512 * 1024 * 1024,
            max_output_bytes: 512 * 1024 * 1024,
            max_output_row_bytes: 64 * 1024 * 1024,
            max_diagnostic_bytes: 64 * 1024,
            max_tool_file_bytes: 256 * 1024 * 1024,
            max_tool_total_bytes: 1024 * 1024 * 1024,
            compile_timeout: Duration::from_secs(120),
            parse_timeout: Duration::from_secs(240),
        }
    }
}
#[derive(Debug, Clone, Copy)]
pub struct SyntaxSource<'a> {
    pub path: &'a str,
    pub text: &'a str,
    /// The compiler/source capture's expected digest, not an inferred identity.
    pub source_sha256: ContentHash,
}
#[derive(Debug, Clone, Copy)]
pub struct SyntaxRun {
    pub effective_workers: usize,
    pub sources: usize,
    pub batches: usize,
    pub source_bytes: u64,
    pub output_bytes: u64,
    pub producer: ContentHash,
    pub cache_hits: usize,
}
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
struct Pin {
    path: PathBuf,
    sha256: String,
}
#[derive(Debug, Serialize, Deserialize)]
struct Manifest {
    version: u32,
    java_heap_bytes: u64,
    java: PathBuf,
    classpath: String,
    main_class: String,
    exporter: Option<PathBuf>,
    producer_sha256: String,
    files: Vec<Pin>,
}

/// Public command fields remain inspectable. Mutating them invalidates the pin
/// and causes `run_sources` to fail before invoking an unexpected configuration.
#[derive(Debug, Clone)]
pub struct SyntaxTool {
    pub java: PathBuf,
    pub classpath: String,
    pub main_class: String,
    pub producer: ContentHash,
    java_heap_bytes: u64,
    exporter: Option<PathBuf>,
    pins: Vec<Pin>,
}
struct OwnedSyntaxSource {
    path: String,
    text: String,
    source_sha256: ContentHash,
}

impl SyntaxTool {
    /// Pin a precompiled exporter and all classpath files. For trusted workflows,
    /// save its manifest and require that manifest on later executions.
    pub fn pin(
        java: &Path,
        classpath: &[PathBuf],
        main_class: &str,
        exporter: Option<&Path>,
        limits: &SyntaxLimits,
    ) -> Result<Self, Error> {
        validate_limits(limits)?;
        if main_class.is_empty() {
            return Err(Error::Invalid("syntax main class"));
        }
        let java = fs::canonicalize(java)?;
        let entries = classpath
            .iter()
            .map(fs::canonicalize)
            .collect::<Result<Vec<_>, _>>()?;
        if entries.is_empty() {
            return Err(Error::Invalid("syntax classpath"));
        }
        let classpath = std::env::join_paths(entries)
            .map_err(|e| Error::Message(e.to_string()))?
            .into_string()
            .map_err(|_| Error::Invalid("UTF-8 syntax classpath"))?;
        let exporter = exporter.map(fs::canonicalize).transpose()?;
        let mut tool = Self {
            java,
            classpath,
            main_class: main_class.to_owned(),
            producer: ContentHash::default(),
            java_heap_bytes: limits.java_heap_bytes,
            exporter,
            pins: Vec::new(),
        };
        tool.pins = tool.capture_pins(limits)?;
        tool.producer = tool.fingerprint(&tool.pins);
        Ok(tool)
    }
    pub fn write_manifest(&self, path: &Path) -> Result<(), Error> {
        let manifest = Manifest {
            version: 1,
            java_heap_bytes: self.java_heap_bytes,
            java: self.java.clone(),
            classpath: self.classpath.clone(),
            main_class: self.main_class.clone(),
            exporter: self.exporter.clone(),
            producer_sha256: self.producer.to_string(),
            files: self.pins.clone(),
        };
        let mut file = OpenOptions::new().write(true).create_new(true).open(path)?;
        serde_json::to_writer_pretty(&mut file, &manifest).map_err(json_error)?;
        file.write_all(b"\n")?;
        file.sync_all()?;
        Ok(())
    }
    pub fn from_manifest(path: &Path, limits: &SyntaxLimits) -> Result<Self, Error> {
        validate_limits(limits)?;
        if fs::metadata(path)?.len() > limits.max_input_bytes.min(4 * 1024 * 1024) {
            return Err(Error::Limit("syntax tool manifest bytes"));
        }
        let manifest: Manifest = serde_json::from_reader(
            File::open(path)?.take(limits.max_input_bytes.min(4 * 1024 * 1024) + 1),
        )
        .map_err(json_error)?;
        if manifest.version != 1 {
            return Err(Error::Invalid("syntax tool manifest version"));
        }
        let tool = Self {
            java: manifest.java,
            classpath: manifest.classpath,
            main_class: manifest.main_class,
            producer: ContentHash::from_hex(&manifest.producer_sha256)?,
            java_heap_bytes: manifest.java_heap_bytes,
            exporter: manifest.exporter,
            pins: manifest.files,
        };
        tool.verify(limits)?;
        Ok(tool)
    }
    /// Compile the checked-in ScalaSpans.scala using only the adapter's exact
    /// cached coordinates. Published compiler outputs are reused through a pinned
    /// manifest. Changes to source, Java, ordered jars or generated classes reject
    /// stale outputs instead of silently changing producer identity.
    pub fn compile_cached(
        exporter: &Path,
        cache: &Path,
        limits: &SyntaxLimits,
    ) -> Result<Self, Error> {
        validate_limits(limits)?;
        let java = find_java()?;
        let jars = cached_jars()?;
        let source = fs::canonicalize(exporter)?;
        let compiler = Self::pin(&java, &jars, "scala.tools.nsc.Main", Some(&source), limits)?;
        fs::create_dir_all(cache)?;
        let cache = fs::canonicalize(cache)?;
        let destination = cache.join(compiler.producer.to_string());
        let manifest = destination.join("tool.json");
        if destination.exists() {
            return Self::from_manifest(&manifest, limits);
        }
        let mut work = Workspace::new(&cache)?;
        let classes = work.path.join("classes");
        fs::create_dir(&classes)?;
        let mut command = Command::new(&compiler.java);
        command
            .arg(compiler.heap_flag())
            .args([
                "-cp",
                &compiler.classpath,
                "scala.tools.nsc.Main",
                "-classpath",
                &compiler.classpath,
                "-d",
            ])
            .arg(&classes)
            .arg(&source);
        run_child(command, None, limits.compile_timeout, limits)?;
        compiler.verify(limits)?;
        let mut paths = vec![classes];
        paths.extend(jars);
        let mut tool = Self::pin(&compiler.java, &paths, "ScalaSpans", Some(&source), limits)?;
        // The compiled tree is published by one directory rename. Rewrite paths
        // before writing the marker so every committed manifest uses final names.
        let old = work.path.clone();
        let remap = |path: &Path| {
            path.strip_prefix(&old).map_or_else(
                |_| path.to_path_buf(),
                |relative| destination.join(relative),
            )
        };
        tool.classpath =
            std::env::join_paths(std::env::split_paths(&tool.classpath).map(|path| remap(&path)))
                .map_err(|e| Error::Message(e.to_string()))?
                .into_string()
                .map_err(|_| Error::Invalid("UTF-8 classpath"))?;
        for pin in &mut tool.pins {
            pin.path = remap(&pin.path);
        }
        tool.producer = tool.fingerprint(&tool.pins);
        tool.write_manifest(&work.path.join("tool.json"))?;
        match fs::rename(&work.path, &destination) {
            Ok(()) => {
                work.keep = true;
            }
            Err(_) if destination.exists() => return Self::from_manifest(&manifest, limits),
            Err(error) => return Err(error.into()),
        }
        Self::from_manifest(&manifest, limits)
    }
    pub fn verify(&self, limits: &SyntaxLimits) -> Result<(), Error> {
        if self.java_heap_bytes != limits.java_heap_bytes {
            return Err(Error::Invalid(
                "syntax Java heap configuration differs from pinned producer",
            ));
        }
        if self.main_class.is_empty() {
            return Err(Error::Invalid("syntax main class"));
        }
        let actual = self.capture_pins(limits)?;
        if actual != self.pins || self.fingerprint(&actual) != self.producer {
            return Err(Error::Invalid(
                "changed syntax producer artifacts/configuration",
            ));
        }
        Ok(())
    }
    fn capture_pins(&self, limits: &SyntaxLimits) -> Result<Vec<Pin>, Error> {
        let mut paths = vec![self.java.clone()];
        if let Some(source) = &self.exporter {
            paths.push(source.clone());
        }
        let entries: Vec<_> = std::env::split_paths(&self.classpath).collect();
        if entries.is_empty() {
            return Err(Error::Invalid("syntax classpath"));
        }
        for entry in entries {
            if !entry.is_absolute() {
                return Err(Error::Invalid("relative syntax classpath entry"));
            }
            if entry.is_dir() {
                collect_files(&entry, &mut paths, 0, limits.max_sources)?;
            } else {
                paths.push(entry);
            }
        }
        let mut total = 0u64;
        paths
            .into_iter()
            .map(|path| {
                let (hash, size) = hash_file(&path, limits.max_tool_file_bytes)?;
                total = total
                    .checked_add(size)
                    .ok_or(Error::Limit("syntax tool bytes"))?;
                if total > limits.max_tool_total_bytes {
                    return Err(Error::Limit("syntax tool bytes"));
                }
                Ok(Pin {
                    path,
                    sha256: hash.to_string(),
                })
            })
            .collect()
    }
    fn heap_flag(&self) -> String {
        format!("-Xmx{}", self.java_heap_bytes)
    }
    fn fingerprint(&self, pins: &[Pin]) -> ContentHash {
        let mut hash = Sha256::new();
        hash.update(b"selector-syntax-tool/v1\0");
        let heap = self.heap_flag();
        for field in [
            self.java.to_string_lossy().as_ref(),
            &self.classpath,
            &self.main_class,
            &heap,
        ] {
            hash.update((field.len() as u64).to_le_bytes());
            hash.update(field.as_bytes());
        }
        for pin in pins {
            let path = pin.path.to_string_lossy();
            hash.update((path.len() as u64).to_le_bytes());
            hash.update(path.as_bytes());
            hash.update(pin.sha256.as_bytes());
        }
        ContentHash(hash.finalize().into())
    }

    /// Run sorted, bounded batches and stream bound source rows to JSONL. Input
    /// text remains borrowed; parser JSON is retained for only one bounded row.
    /// Output coordinates remain JVM UTF-16 for the native importer's conversion.
    pub fn run_sources(
        &self,
        sources: &[SyntaxSource<'_>],
        output: &mut impl Write,
        limits: &SyntaxLimits,
    ) -> Result<SyntaxRun, Error> {
        validate_limits(limits)?;
        self.verify(limits)?;
        let result = self.run_sources_unverified(sources, output, limits)?;
        self.verify(limits)?;
        Ok(result)
    }
    fn run_sources_unverified(
        &self,
        sources: &[SyntaxSource<'_>],
        output: &mut impl Write,
        limits: &SyntaxLimits,
    ) -> Result<SyntaxRun, Error> {
        if sources.len() > limits.max_sources {
            return Err(Error::Limit("syntax source count"));
        }
        let mut ordered: Vec<_> = (0..sources.len()).collect();
        ordered.sort_unstable_by_key(|&index| sources[index].path);
        let mut source_bytes = 0u64;
        let mut previous = None;
        for &index in &ordered {
            let source = sources[index];
            if source.path.is_empty() || previous == Some(source.path) {
                return Err(Error::Invalid("empty/duplicate syntax source path"));
            }
            if source.text.len() > limits.max_source_bytes {
                return Err(Error::Limit("syntax source bytes"));
            }
            source_bytes = source_bytes
                .checked_add(source.text.len() as u64)
                .ok_or(Error::Limit("syntax total source bytes"))?;
            if source_bytes > limits.max_total_source_bytes {
                return Err(Error::Limit("syntax total source bytes"));
            }
            if ContentHash(Sha256::digest(source.text.as_bytes()).into()) != source.source_sha256 {
                return Err(Error::Invalid("changed syntax source SHA256"));
            }
            previous = Some(source.path);
        }
        let producer = self.producer.to_string();
        let mut writer = LimitedWriter {
            inner: output,
            bytes: 0,
            maximum: limits.max_output_bytes,
        };
        let mut batches = 0;
        let mut start = 0;
        while start < ordered.len() {
            let mut end = start;
            let mut bytes = 0usize;
            while end < ordered.len() {
                let length = sources[ordered[end]].text.len();
                if end > start && bytes.saturating_add(length) > limits.batch_source_bytes {
                    break;
                }
                bytes = bytes.saturating_add(length);
                end += 1;
            }
            let work = Workspace::new(&std::env::temp_dir())?;
            let input_path = work.path.join("input.json");
            let output_path = work.path.join("output.json");
            let file = File::create(&input_path)?;
            let mut input = LimitedWriter {
                inner: BufWriter::with_capacity(128 * 1024, file),
                bytes: 0,
                maximum: limits.max_input_bytes,
            };
            input.write_all(b"{")?;
            let mut expected = HashMap::with_capacity(end - start);
            for (ordinal, &index) in ordered[start..end].iter().enumerate() {
                let source = sources[index];
                if ordinal > 0 {
                    input.write_all(b",")?;
                }
                serde_json::to_writer(&mut input, source.path).map_err(json_error)?;
                input.write_all(b":")?;
                serde_json::to_writer(&mut input, source.text).map_err(json_error)?;
                expected.insert(source.path, (source.source_sha256, ordinal));
            }
            input.write_all(b"}")?;
            input.flush()?;
            drop(input);
            let mut command = Command::new(&self.java);
            command
                .arg(self.heap_flag())
                .args(["-cp", &self.classpath, &self.main_class])
                .arg(&input_path)
                .arg(&output_path);
            run_child(command, Some(&output_path), limits.parse_timeout, limits)?;
            decode_output(&output_path, &expected, &producer, &mut writer, limits)?;
            batches += 1;
            start = end;
        }
        writer.flush()?;
        Ok(SyntaxRun {
            effective_workers: 1,
            sources: sources.len(),
            batches,
            source_bytes,
            output_bytes: writer.bytes,
            producer: self.producer,
            cache_hits: 0,
        })
    }
}

fn validate_limits(limits: &SyntaxLimits) -> Result<(), Error> {
    if limits.java_heap_bytes == 0
        || limits.parallel_java_heap_bytes < limits.java_heap_bytes
        || limits.batch_source_bytes == 0
        || limits.max_source_bytes == 0
        || limits.max_sources == 0
        || limits.max_output_row_bytes == 0
        || limits.max_diagnostic_bytes == 0
        || limits.parse_timeout.is_zero()
        || limits.compile_timeout.is_zero()
    {
        return Err(Error::Invalid("syntax limits"));
    }
    Ok(())
}
fn json_error(error: serde_json::Error) -> Error {
    Error::Message(error.to_string())
}
fn hash_file(path: &Path, maximum: u64) -> Result<(ContentHash, u64), Error> {
    let metadata = fs::metadata(path)?;
    if !metadata.is_file() {
        return Err(Error::Invalid("syntax tool input is not a regular file"));
    }
    let mut file = File::open(path)?;
    let size = file.metadata()?.len();
    if size > maximum {
        return Err(Error::Limit("syntax tool file bytes"));
    }
    let mut hash = Sha256::new();
    let mut buffer = [0; 64 * 1024];
    let mut total = 0u64;
    loop {
        let count = file.read(&mut buffer)?;
        if count == 0 {
            break;
        }
        total = total
            .checked_add(count as u64)
            .ok_or(Error::Limit("syntax tool file bytes"))?;
        if total > maximum {
            return Err(Error::Limit("syntax tool file bytes"));
        }
        hash.update(&buffer[..count]);
    }
    if size != total {
        return Err(Error::Invalid("syntax tool file changed during hashing"));
    }
    Ok((ContentHash(hash.finalize().into()), total))
}
fn collect_files(
    directory: &Path,
    output: &mut Vec<PathBuf>,
    depth: usize,
    maximum: usize,
) -> Result<(), Error> {
    if depth > 32 {
        return Err(Error::Limit("syntax classpath directory depth"));
    }
    let mut entries: Vec<_> = fs::read_dir(directory)?
        .take(maximum.saturating_add(1))
        .collect::<Result<_, _>>()?;
    if entries.len() > maximum || output.len().saturating_add(entries.len()) > maximum {
        return Err(Error::Limit("syntax classpath file count"));
    }
    entries.sort_unstable_by_key(|entry| entry.file_name());
    for entry in entries {
        let kind = entry.file_type()?;
        if kind.is_symlink() {
            return Err(Error::Invalid("symlink inside syntax classpath directory"));
        }
        if kind.is_dir() {
            collect_files(&entry.path(), output, depth + 1, maximum)?;
        } else if kind.is_file() {
            output.push(entry.path());
        } else {
            return Err(Error::Invalid("syntax classpath file type"));
        }
    }
    Ok(())
}
fn find_java() -> Result<PathBuf, Error> {
    if let Some(path) = std::env::var_os("SCALA_AST_JAVA") {
        return Ok(fs::canonicalize(path)?);
    }
    for path in [
        "/opt/homebrew/opt/openjdk@21/libexec/openjdk.jdk/Contents/Home/bin/java",
        "/opt/homebrew/opt/openjdk/libexec/openjdk.jdk/Contents/Home/bin/java",
    ] {
        if Path::new(path).is_file() {
            return Ok(fs::canonicalize(path)?);
        }
    }
    for directory in std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default()) {
        let path = directory.join(if cfg!(windows) { "java.exe" } else { "java" });
        if path.is_file() {
            return Ok(fs::canonicalize(path)?);
        }
    }
    Err(Error::Message(
        "Java unavailable; set SCALA_AST_JAVA".to_owned(),
    ))
}
fn cached_jars() -> Result<Vec<PathBuf>, Error> {
    let cache = if let Some(cache) = std::env::var_os("COURSIER_CACHE") {
        PathBuf::from(cache)
    } else {
        PathBuf::from(std::env::var_os("HOME").ok_or(Error::Invalid("HOME for cached Scala jars"))?)
            .join("Library/Caches/Coursier/v1")
    };
    let maven = cache.join("https/repo1.maven.org/maven2");
    let coordinates = [
        ("org/scala-lang", "scala-library", "2.13.18"),
        ("org/scala-lang", "scala-compiler", "2.13.18"),
        ("org/scala-lang", "scala-reflect", "2.13.18"),
        ("org/scalameta", "scalameta_2.13", "4.15.2"),
        ("org/scalameta", "parsers_2.13", "4.15.2"),
        ("org/scalameta", "trees_2.13", "4.15.2"),
        ("org/scalameta", "common_2.13", "4.15.2"),
        ("org/scalameta", "io_2.13", "4.15.2"),
        ("com/lihaoyi", "fastparse_2.13", "3.1.1"),
        ("com/lihaoyi", "sourcecode_2.13", "0.4.4"),
        ("com/lihaoyi", "geny_2.13", "1.1.1"),
        ("com/lihaoyi", "ujson_2.13", "4.0.2"),
        ("com/lihaoyi", "upickle-core_2.13", "4.0.2"),
    ];
    coordinates
        .into_iter()
        .map(|(group, artifact, version)| {
            let path = maven
                .join(group)
                .join(artifact)
                .join(version)
                .join(format!("{artifact}-{version}.jar"));
            fs::canonicalize(&path).map_err(|error| {
                Error::Message(format!(
                    "cached Scala/Scalameta prerequisite missing: {}: {error}",
                    path.display()
                ))
            })
        })
        .collect()
}

struct Workspace {
    path: PathBuf,
    keep: bool,
}
impl Workspace {
    fn new(parent: &Path) -> Result<Self, Error> {
        loop {
            let path = parent.join(format!(
                ".selector-syntax-{}-{}",
                std::process::id(),
                NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed)
            ));
            match fs::create_dir(&path) {
                Ok(()) => return Ok(Self { path, keep: false }),
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(error) => return Err(error.into()),
            }
        }
    }
}
impl Drop for Workspace {
    fn drop(&mut self) {
        if !self.keep {
            let _ = fs::remove_dir_all(&self.path);
        }
    }
}
struct LimitedWriter<W> {
    inner: W,
    bytes: u64,
    maximum: u64,
}
impl<W: Write> Write for LimitedWriter<W> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        let next = self
            .bytes
            .checked_add(bytes.len() as u64)
            .ok_or_else(|| io::Error::other("syntax output byte overflow"))?;
        if next > self.maximum {
            return Err(io::Error::other("syntax input/output byte limit"));
        }
        let count = self.inner.write(bytes)?;
        self.bytes += count as u64;
        Ok(count)
    }
    fn flush(&mut self) -> io::Result<()> {
        self.inner.flush()
    }
}

struct ChildOwner(Option<Child>);
impl Drop for ChildOwner {
    fn drop(&mut self) {
        if let Some(child) = &mut self.0 {
            let _ = child.kill();
            let _ = child.wait();
        }
    }
}
fn run_child(
    mut command: Command,
    output: Option<&Path>,
    timeout: Duration,
    limits: &SyntaxLimits,
) -> Result<(), Error> {
    command
        .env_remove("JAVA_TOOL_OPTIONS")
        .env_remove("JDK_JAVA_OPTIONS")
        .env_remove("_JAVA_OPTIONS")
        .env_remove("CLASSPATH")
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut owner = ChildOwner(Some(command.spawn()?));
    let child = owner.0.as_mut().unwrap();
    let overflow = Arc::new(AtomicBool::new(false));
    let drain = |mut reader: Box<dyn Read + Send>, exceeded: Arc<AtomicBool>| {
        let maximum = limits.max_diagnostic_bytes;
        std::thread::Builder::new()
            .name("syntax-diagnostic-drain".into())
            .spawn(move || {
                let mut retained = Vec::new();
                let mut scratch = [0; 8192];
                let mut total = 0usize;
                loop {
                    let count = reader.read(&mut scratch)?;
                    if count == 0 {
                        break;
                    }
                    total = total.saturating_add(count);
                    let keep = count.min(maximum.saturating_sub(retained.len()));
                    retained.extend_from_slice(&scratch[..keep]);
                    if total > maximum {
                        exceeded.store(true, Ordering::Release);
                    }
                }
                Ok::<_, io::Error>(retained)
            })
    };
    let stdout = drain(Box::new(child.stdout.take().unwrap()), overflow.clone())?;
    let stderr = drain(Box::new(child.stderr.take().unwrap()), overflow.clone())?;
    let started = Instant::now();
    let outcome = loop {
        if overflow.load(Ordering::Acquire) {
            break Err(Error::Limit("syntax child diagnostics"));
        }
        if output.is_some_and(|path| {
            fs::metadata(path).is_ok_and(|meta| meta.len() > limits.max_output_bytes)
        }) {
            break Err(Error::Limit("syntax child output bytes"));
        }
        if started.elapsed() > timeout {
            break Err(Error::Limit("syntax child wall time"));
        }
        match child.try_wait()? {
            Some(status) if status.success() => break Ok(()),
            Some(status) => {
                break Err(Error::Message(format!(
                    "syntax JVM process failed: {status}"
                )));
            }
            None => std::thread::sleep(Duration::from_millis(10)),
        }
    };
    // Kill/reap before joining pipe readers on failure; never wait on a child
    // blocked by full stdout/stderr pipes or retain unlimited diagnostic strings.
    if outcome.is_err() {
        let _ = child.kill();
    }
    child.wait()?;
    let stdout = stdout
        .join()
        .map_err(|_| Error::Invalid("syntax stdout reader panic"))??;
    let stderr = stderr
        .join()
        .map_err(|_| Error::Invalid("syntax stderr reader panic"))??;
    owner.0 = None;
    if let Err(error) = outcome {
        return Err(Error::Message(format!(
            "{error}\nstdout: {}\nstderr: {}",
            String::from_utf8_lossy(&stdout),
            String::from_utf8_lossy(&stderr)
        )));
    }
    if overflow.load(Ordering::Acquire) {
        return Err(Error::Limit("syntax child diagnostics"));
    }
    if let Some(path) = output {
        if fs::metadata(path)?.len() > limits.max_output_bytes {
            return Err(Error::Limit("syntax child output bytes"));
        }
    }
    Ok(())
}

struct RowLimitedReader<R> {
    inner: R,
    row: Rc<Cell<Option<usize>>>,
}
impl<R: Read> Read for RowLimitedReader<R> {
    fn read(&mut self, buffer: &mut [u8]) -> io::Result<usize> {
        let take = match self.row.get() {
            Some(0) if !buffer.is_empty() => {
                return Err(io::Error::other("syntax output row byte limit"));
            }
            Some(left) => left.min(buffer.len()),
            None => buffer.len(),
        };
        let count = self.inner.read(&mut buffer[..take])?;
        if let Some(left) = self.row.get() {
            self.row.set(Some(left - count));
        }
        Ok(count)
    }
}
#[derive(Deserialize)]
struct SourceHeader<'a> {
    #[serde(borrow)]
    path: Cow<'a, str>,
    #[serde(borrow)]
    sha256: Cow<'a, str>,
}
#[derive(Serialize)]
struct BoundRow<'a> {
    path: &'a str,
    source_sha256: &'a str,
    producer_sha256: &'a str,
    ast: &'a RawValue,
}
struct OutputSeed<'a, W> {
    expected: &'a HashMap<&'a str, (ContentHash, usize)>,
    producer: &'a str,
    output: &'a mut W,
    budget: Rc<Cell<Option<usize>>>,
    row_limit: usize,
}
impl<'de, W: Write> DeserializeSeed<'de> for OutputSeed<'_, W> {
    type Value = ();
    fn deserialize<D: serde::Deserializer<'de>>(self, deserializer: D) -> Result<(), D::Error> {
        deserializer.deserialize_map(self)
    }
}
impl<'de, W: Write> Visitor<'de> for OutputSeed<'_, W> {
    type Value = ();
    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("ScalaSpans output object")
    }
    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<(), A::Error> {
        let mut schema = None;
        let mut parser = None;
        let mut sources = false;
        while let Some(key) = map.next_key::<String>()? {
            match key.as_str() {
                "schema_version" if schema.is_none() => schema = Some(map.next_value::<u32>()?),
                "parser" if parser.is_none() => parser = Some(map.next_value::<String>()?),
                "sources" if !sources => {
                    sources = true;
                    map.next_value_seed(SourcesSeed {
                        expected: self.expected,
                        producer: self.producer,
                        output: self.output,
                        budget: self.budget.clone(),
                        row_limit: self.row_limit,
                    })?;
                }
                _ => {
                    return Err(serde::de::Error::custom(
                        "unexpected/duplicate ScalaSpans output field",
                    ));
                }
            }
        }
        if schema != Some(1) || parser.as_deref() != Some("scalameta-4.15.2") || !sources {
            return Err(serde::de::Error::custom(
                "unsupported/missing ScalaSpans output schema",
            ));
        }
        Ok(())
    }
}
struct SourcesSeed<'a, W> {
    expected: &'a HashMap<&'a str, (ContentHash, usize)>,
    producer: &'a str,
    output: &'a mut W,
    budget: Rc<Cell<Option<usize>>>,
    row_limit: usize,
}
impl<'de, W: Write> DeserializeSeed<'de> for SourcesSeed<'_, W> {
    type Value = ();
    fn deserialize<D: serde::Deserializer<'de>>(self, deserializer: D) -> Result<(), D::Error> {
        deserializer.deserialize_seq(self)
    }
}
impl<'de, W: Write> Visitor<'de> for SourcesSeed<'_, W> {
    type Value = ();
    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("bounded ScalaSpans source array")
    }
    fn visit_seq<A: SeqAccess<'de>>(self, mut sequence: A) -> Result<(), A::Error> {
        let mut seen = vec![false; self.expected.len()];
        loop {
            self.budget.set(Some(self.row_limit));
            let next = sequence.next_element::<Box<RawValue>>();
            self.budget.set(Some(self.row_limit));
            let Some(raw) = next? else {
                break;
            };
            if raw.get().len() > self.row_limit {
                return Err(serde::de::Error::custom("syntax output row byte limit"));
            }
            let header: SourceHeader<'_> =
                serde_json::from_str(raw.get()).map_err(serde::de::Error::custom)?;
            let Some(&(expected, ordinal)) = self.expected.get(header.path.as_ref()) else {
                return Err(serde::de::Error::custom(
                    "unexpected ScalaSpans source path",
                ));
            };
            if seen[ordinal]
                || ContentHash::from_hex(&header.sha256).map_err(serde::de::Error::custom)?
                    != expected
            {
                return Err(serde::de::Error::custom(
                    "duplicate/stale ScalaSpans source",
                ));
            }
            seen[ordinal] = true;
            let row = BoundRow {
                path: &header.path,
                source_sha256: &header.sha256,
                producer_sha256: self.producer,
                ast: &raw,
            };
            serde_json::to_writer(&mut *self.output, &row).map_err(serde::de::Error::custom)?;
            self.output
                .write_all(b"\n")
                .map_err(serde::de::Error::custom)?;
        }
        if seen.iter().any(|seen| !seen) {
            return Err(serde::de::Error::custom(
                "ScalaSpans output inventory mismatch",
            ));
        }
        Ok(())
    }
}
fn decode_output(
    path: &Path,
    expected: &HashMap<&str, (ContentHash, usize)>,
    producer: &str,
    output: &mut impl Write,
    limits: &SyntaxLimits,
) -> Result<(), Error> {
    if fs::metadata(path)?.len() > limits.max_output_bytes {
        return Err(Error::Limit("syntax output bytes"));
    }
    let budget = Rc::new(Cell::new(Some(limits.max_output_row_bytes)));
    let reader = RowLimitedReader {
        inner: BufReader::with_capacity(128 * 1024, File::open(path)?),
        row: budget.clone(),
    };
    let mut deserializer = serde_json::Deserializer::from_reader(reader);
    OutputSeed {
        expected,
        producer,
        output,
        budget,
        row_limit: limits.max_output_row_bytes,
    }
    .deserialize(&mut deserializer)
    .map_err(json_error)?;
    deserializer.end().map_err(json_error)
}

const ROW_CACHE_MAGIC: &[u8] = b"selector-syntax-row/v1\0";

#[derive(Deserialize)]
struct CachedBoundRow<'a> {
    #[serde(borrow)]
    path: Cow<'a, str>,
    #[serde(borrow)]
    source_sha256: Cow<'a, str>,
    #[serde(borrow)]
    producer_sha256: Cow<'a, str>,
    #[serde(borrow)]
    ast: &'a RawValue,
}

fn source_cache_key(producer: ContentHash, path: &str, source: ContentHash) -> ContentHash {
    let mut hash = Sha256::new();
    hash.update(b"selector-syntax-source/v1\0");
    hash.update(producer.0);
    hash.update((path.len() as u64).to_le_bytes());
    hash.update(path.as_bytes());
    hash.update(source.0);
    ContentHash(hash.finalize().into())
}

fn validate_bound_row<'a>(
    row: &'a [u8],
    producer: ContentHash,
    limits: &SyntaxLimits,
) -> Result<(CachedBoundRow<'a>, ContentHash), Error> {
    if row.len() > limits.max_output_row_bytes {
        return Err(Error::Limit("syntax cache row bytes"));
    }
    let bound: CachedBoundRow<'a> = serde_json::from_slice(row).map_err(json_error)?;
    let source = ContentHash::from_hex(&bound.source_sha256)?;
    if bound.path.is_empty() || ContentHash::from_hex(&bound.producer_sha256)? != producer {
        return Err(Error::Invalid("syntax cache producer/path"));
    }
    let ast: SourceHeader<'_> = serde_json::from_str(bound.ast.get()).map_err(json_error)?;
    if ast.path != bound.path || ContentHash::from_hex(&ast.sha256)? != source {
        return Err(Error::Invalid("syntax cache source binding"));
    }
    let key = source_cache_key(producer, &bound.path, source);
    Ok((bound, key))
}

/// Staged rows are not shared until the command's final producer-pin check.
/// Cache admission reads one bounded row into caller-owned reusable scratch.
struct SourceCache {
    root: PathBuf,
    stage: Workspace,
    producer: ContentHash,
}
impl SourceCache {
    fn new(root: &Path, producer: ContentHash) -> Result<Self, Error> {
        fs::create_dir_all(root)?;
        let root = fs::canonicalize(root)?;
        let stage = Workspace::new(&root)?;
        Ok(Self {
            root: root.join(producer.to_string()),
            stage,
            producer,
        })
    }
    fn path(&self, key: ContentHash) -> PathBuf {
        let name = key.to_string();
        self.root
            .join(&name[..2])
            .join(format!("{}.syntax", &name[2..]))
    }
    fn staged(&self, key: ContentHash) -> PathBuf {
        self.stage.path.join(format!("{key}.syntax"))
    }
    fn probe(&self, key: ContentHash, limits: &SyntaxLimits) -> Result<bool, Error> {
        match fs::metadata(self.path(key)) {
            Ok(meta) => {
                if !meta.is_file()
                    || meta.len()
                        > limits.max_output_row_bytes as u64 + ROW_CACHE_MAGIC.len() as u64 + 72
                {
                    return Err(Error::Invalid("syntax cache entry size/type"));
                }
                Ok(true)
            }
            Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(false),
            Err(e) => Err(e.into()),
        }
    }
    fn stage_row(&self, row: &[u8], limits: &SyntaxLimits) -> Result<(), Error> {
        let (_, key) = validate_bound_row(row, self.producer, limits)?;
        let path = self.staged(key);
        let mut file = match OpenOptions::new().write(true).create_new(true).open(&path) {
            Ok(file) => file,
            Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {
                let mut existing = Vec::new();
                self.read_entry(&path, key, &mut existing, limits)?;
                if existing != row {
                    return Err(Error::Invalid("non-deterministic syntax cache row"));
                }
                return Ok(());
            }
            Err(e) => return Err(e.into()),
        };
        let hash: ContentHash = ContentHash(Sha256::digest(row).into());
        file.write_all(ROW_CACHE_MAGIC)?;
        file.write_all(&key.0)?;
        file.write_all(&hash.0)?;
        file.write_all(&(row.len() as u64).to_le_bytes())?;
        file.write_all(row)?;
        file.sync_data()?;
        Ok(())
    }
    fn read_entry(
        &self,
        path: &Path,
        key: ContentHash,
        scratch: &mut Vec<u8>,
        limits: &SyntaxLimits,
    ) -> Result<(), Error> {
        let mut file = File::open(path)?;
        let size = file.metadata()?.len();
        let overhead = ROW_CACHE_MAGIC.len() as u64 + 72;
        if size < overhead || size > limits.max_output_row_bytes as u64 + overhead {
            return Err(Error::Invalid("syntax cache entry size"));
        }
        let mut magic = [0; ROW_CACHE_MAGIC.len()];
        file.read_exact(&mut magic)?;
        let mut stored_key = [0; 32];
        let mut expected = [0; 32];
        let mut length = [0; 8];
        file.read_exact(&mut stored_key)?;
        file.read_exact(&mut expected)?;
        file.read_exact(&mut length)?;
        let len = usize::try_from(u64::from_le_bytes(length))
            .map_err(|_| Error::Limit("syntax cache row bytes"))?;
        if magic != ROW_CACHE_MAGIC
            || stored_key != key.0
            || len > limits.max_output_row_bytes
            || len as u64 + overhead != size
        {
            return Err(Error::Invalid("syntax cache entry header"));
        }
        scratch.clear();
        scratch
            .try_reserve(len)
            .map_err(|_| Error::Limit("syntax cache row allocation"))?;
        scratch.resize(len, 0);
        file.read_exact(scratch)?;
        let mut extra = [0];
        if file.read(&mut extra)? != 0 || Sha256::digest(&*scratch).as_slice() != expected {
            return Err(Error::Invalid("syntax cache row checksum"));
        }
        let (_, actual) = validate_bound_row(scratch, self.producer, limits)?;
        if actual != key {
            return Err(Error::Invalid("syntax cache input identity"));
        }
        Ok(())
    }
    fn load(
        &self,
        key: ContentHash,
        scratch: &mut Vec<u8>,
        limits: &SyntaxLimits,
    ) -> Result<(), Error> {
        let path = self.path(key);
        let path = if path.exists() {
            path
        } else {
            self.staged(key)
        };
        self.read_entry(&path, key, scratch, limits)
    }
    fn publish(&self, limits: &SyntaxLimits) -> Result<(), Error> {
        let mut scratch = Vec::new();
        for entry in fs::read_dir(&self.stage.path)? {
            let entry = entry?;
            let name = entry.file_name();
            let name = name
                .to_str()
                .ok_or(Error::Invalid("syntax cache filename"))?;
            let key = ContentHash::from_hex(
                name.strip_suffix(".syntax")
                    .ok_or(Error::Invalid("syntax cache filename"))?,
            )?;
            self.read_entry(&entry.path(), key, &mut scratch, limits)?;
            let checksum: ContentHash = ContentHash(Sha256::digest(&scratch).into());
            let destination = self.path(key);
            let parent = destination
                .parent()
                .ok_or(Error::Invalid("syntax cache parent"))?;
            fs::create_dir_all(parent)?;
            match fs::hard_link(entry.path(), &destination) {
                Ok(()) => {}
                Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {
                    self.read_entry(&destination, key, &mut scratch, limits)?;
                    if ContentHash(Sha256::digest(&scratch).into()) != checksum {
                        return Err(Error::Invalid("non-deterministic published syntax row"));
                    }
                }
                Err(e) => return Err(e.into()),
            }
        }
        Ok(())
    }
}

impl SyntaxTool {
    /// Reuse rows only for this exact pinned producer, compiler path and source.
    /// Publication follows the final pin check; failed commands expose no new rows.
    pub fn run_capture_cached(
        &self,
        capture: &Path,
        output: &mut impl Write,
        workers: usize,
        limits: &SyntaxLimits,
        cache: &Path,
    ) -> Result<SyntaxRun, Error> {
        let cache = SourceCache::new(cache, self.producer)?;
        let result = self.run_capture_impl(capture, output, workers, limits, Some(&cache))?;
        cache.publish(limits)?;
        Ok(result)
    }

    /// Admit existing native bound JSONL (optionally gzip) without rerunning JVMs.
    /// Every row must carry this producer and match its embedded path/source SHA.
    pub fn import_syntax_cache(
        &self,
        syntax: &Path,
        cache: &Path,
        limits: &SyntaxLimits,
    ) -> Result<usize, Error> {
        validate_limits(limits)?;
        self.verify(limits)?;
        let cache = SourceCache::new(cache, self.producer)?;
        let options = crate::ExtractOptions {
            max_input_bytes: limits.max_output_bytes,
            max_document_bytes: limits.max_output_row_bytes.saturating_add(1),
            ..Default::default()
        };
        let mut input = crate::Input::open(syntax, &options, 0)?;
        let mut rows = 0;
        while let Some(mut row) = input.line()? {
            while row.last().is_some_and(u8::is_ascii_whitespace) {
                row.pop();
            }
            if row.is_empty() {
                continue;
            }
            if rows >= limits.max_sources {
                return Err(Error::Limit("syntax cache source count"));
            }
            cache.stage_row(&row, limits)?;
            rows += 1;
        }
        self.verify(limits)?;
        cache.publish(limits)?;
        Ok(rows)
    }

    /// Stream captured SemanticDB JSONL (optionally gzip), borrowing each decoder
    /// batch once. Independent JVM batches run in a bounded pool and write local
    /// temporary JSONL; ordered merge never retains whole-program source or ASTs.
    /// Tool contents are verified once before and once after this entire command.
    pub fn run_capture(
        &self,
        capture: &Path,
        output: &mut impl Write,
        workers: usize,
        limits: &SyntaxLimits,
    ) -> Result<SyntaxRun, Error> {
        self.run_capture_impl(capture, output, workers, limits, None)
    }
    fn run_capture_impl(
        &self,
        capture: &Path,
        output: &mut impl Write,
        workers: usize,
        limits: &SyntaxLimits,
        cache: Option<&SourceCache>,
    ) -> Result<SyntaxRun, Error> {
        validate_limits(limits)?;
        if workers == 0 || workers > 64 {
            return Err(Error::Invalid("syntax workers (1..=64)"));
        }
        self.verify(limits)?;
        let effective_workers = workers.min(
            usize::try_from(limits.parallel_java_heap_bytes / limits.java_heap_bytes)
                .unwrap_or(usize::MAX),
        );
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(effective_workers)
            .build()
            .map_err(|e| Error::Message(e.to_string()))?;
        let options = crate::ExtractOptions {
            max_input_bytes: limits.max_total_source_bytes,
            max_document_bytes: usize::try_from(limits.max_input_bytes)
                .unwrap_or(usize::MAX)
                .min(limits.max_source_bytes.saturating_mul(8)),
            batch_bytes: limits.batch_source_bytes,
            workers,
            ..crate::ExtractOptions::default()
        };
        let mut input = crate::Input::open(capture, &options, 0)?;
        let mut seen: HashMap<String, ContentHash> = HashMap::new();
        let mut writer = LimitedWriter {
            inner: output,
            bytes: 0,
            maximum: limits.max_output_bytes,
        };
        let mut total = SyntaxRun {
            effective_workers,
            sources: 0,
            batches: 0,
            source_bytes: 0,
            output_bytes: 0,
            producer: self.producer,
            cache_hits: 0,
        };
        // Charge work groups by actual source text, not SemanticDB wire size.
        // Only minimal owned source rows survive each bounded decoder batch.
        let target = limits
            .batch_source_bytes
            .checked_mul(effective_workers)
            .ok_or(Error::Limit("syntax source group bytes"))?;
        let mut group = Vec::new();
        let mut group_bytes = 0usize;
        loop {
            let lines = input.batch(options.batch_bytes)?;
            if lines.is_empty() {
                break;
            }
            #[derive(Deserialize)]
            struct CaptureRow<'a> {
                #[serde(borrow)]
                path: Cow<'a, str>,
                #[serde(default, borrow)]
                source_text: Option<Cow<'a, str>>,
                #[serde(default, borrow)]
                source_sha256: Option<Cow<'a, str>>,
            }
            for line in &lines {
                let row: CaptureRow<'_> = serde_json::from_slice(line).map_err(json_error)?;
                let text = row
                    .source_text
                    .ok_or(Error::Invalid("syntax capture source_text missing"))?;
                if row.path.is_empty() || text.len() > limits.max_source_bytes {
                    return Err(Error::Limit("syntax source path/bytes"));
                }
                let expected = ContentHash::from_hex(
                    row.source_sha256
                        .as_deref()
                        .ok_or(Error::Invalid("syntax capture source_sha256 missing"))?,
                )?;
                if ContentHash(Sha256::digest(text.as_bytes()).into()) != expected {
                    return Err(Error::Invalid("changed syntax capture source SHA256"));
                }
                if let Some(previous) = seen.get(row.path.as_ref()) {
                    if *previous != expected {
                        return Err(Error::Invalid(
                            "conflicting source versions in syntax capture",
                        ));
                    }
                    continue;
                }
                if seen.len() >= limits.max_sources {
                    return Err(Error::Limit("syntax capture source count"));
                }
                seen.insert(row.path.to_string(), expected);
                total.sources += 1;
                total.source_bytes = total
                    .source_bytes
                    .checked_add(text.len() as u64)
                    .ok_or(Error::Limit("syntax total source bytes"))?;
                if total.source_bytes > limits.max_total_source_bytes {
                    return Err(Error::Limit("syntax total source bytes"));
                }
                group_bytes = group_bytes
                    .checked_add(text.len())
                    .ok_or(Error::Limit("syntax source group bytes"))?;
                group.push(OwnedSyntaxSource {
                    path: row.path.into_owned(),
                    text: text.into_owned(),
                    source_sha256: expected,
                });
                if group_bytes >= target {
                    let (batches, hits) =
                        self.run_group_unverified(&group, &mut writer, &pool, limits, cache)?;
                    total.batches += batches;
                    total.cache_hits += hits;
                    group.clear();
                    group_bytes = 0;
                }
            }
            // `lines` and all compiler occurrences disappear here. Parsed source
            // rows have moved into the bounded group, never a whole-corpus DOM.
        }
        if !group.is_empty() {
            let (batches, hits) =
                self.run_group_unverified(&group, &mut writer, &pool, limits, cache)?;
            total.batches += batches;
            total.cache_hits += hits;
        }
        self.verify(limits)?;
        writer.flush()?;
        total.output_bytes = writer.bytes;
        Ok(total)
    }
    fn run_group_unverified(
        &self,
        owned: &[OwnedSyntaxSource],
        output: &mut impl Write,
        pool: &rayon::ThreadPool,
        limits: &SyntaxLimits,
        cache: Option<&SourceCache>,
    ) -> Result<(usize, usize), Error> {
        use rayon::prelude::*;
        let mut sources: Vec<_> = owned
            .iter()
            .map(|s| SyntaxSource {
                path: s.path.as_str(),
                text: s.text.as_str(),
                source_sha256: s.source_sha256,
            })
            .collect();
        sources.sort_unstable_by_key(|s| s.path);
        let mut chunks = Vec::new();
        let mut start = 0;
        while start < sources.len() {
            let mut end = start;
            let mut bytes = 0usize;
            while end < sources.len() {
                let len = sources[end].text.len();
                if end > start && bytes.saturating_add(len) > limits.batch_source_bytes {
                    break;
                }
                bytes = bytes.saturating_add(len);
                end += 1;
            }
            chunks.push(&sources[start..end]);
            start = end;
        }
        let completed: Vec<Result<(Workspace, SyntaxRun), Error>> = pool.install(|| {
            chunks
                .par_iter()
                .map(|sources| {
                    let work = Workspace::new(&std::env::temp_dir())?;
                    let mut out = BufWriter::with_capacity(
                        128 * 1024,
                        File::create(work.path.join("bound.jsonl"))?,
                    );
                    let result = if let Some(cache) = cache {
                        self.run_cached_sources_unverified(sources, &mut out, limits, cache)?
                    } else {
                        self.run_sources_unverified(sources, &mut out, limits)?
                    };
                    out.flush()?;
                    Ok((work, result))
                })
                .collect()
        });
        let (mut batches, mut hits) = (0, 0);
        for completed in completed {
            let (work, result) = completed?;
            io::copy(&mut File::open(work.path.join("bound.jsonl"))?, output)?;
            batches += result.batches;
            hits += result.cache_hits;
        }
        Ok((batches, hits))
    }
    fn run_cached_sources_unverified(
        &self,
        sources: &[SyntaxSource<'_>],
        output: &mut impl Write,
        limits: &SyntaxLimits,
        cache: &SourceCache,
    ) -> Result<SyntaxRun, Error> {
        let mut missing = Vec::new();
        let mut ordered: Vec<_> = (0..sources.len()).collect();
        ordered.sort_unstable_by_key(|i| sources[*i].path);
        for &i in &ordered {
            let s = sources[i];
            let key = source_cache_key(self.producer, s.path, s.source_sha256);
            if !cache.probe(key, limits)? {
                missing.push(s);
            }
        }
        let mut batches = 0;
        if !missing.is_empty() {
            let work = Workspace::new(&std::env::temp_dir())?;
            let path = work.path.join("fresh.jsonl");
            let mut file = BufWriter::with_capacity(128 * 1024, File::create(&path)?);
            batches = self
                .run_sources_unverified(&missing, &mut file, limits)?
                .batches;
            file.flush()?;
            drop(file);
            let options = crate::ExtractOptions {
                max_input_bytes: limits.max_output_bytes,
                max_document_bytes: limits.max_output_row_bytes.saturating_add(1),
                ..Default::default()
            };
            let mut input = crate::Input::open(&path, &options, 0)?;
            while let Some(mut row) = input.line()? {
                while row.last().is_some_and(u8::is_ascii_whitespace) {
                    row.pop();
                }
                if !row.is_empty() {
                    cache.stage_row(&row, limits)?;
                }
            }
        }
        let mut writer = LimitedWriter {
            inner: output,
            bytes: 0,
            maximum: limits.max_output_bytes,
        };
        let mut scratch = Vec::new();
        for &i in &ordered {
            let source = sources[i];
            let key = source_cache_key(self.producer, source.path, source.source_sha256);
            cache.load(key, &mut scratch, limits)?;
            writer.write_all(&scratch)?;
            writer.write_all(b"\n")?;
        }
        writer.flush()?;
        Ok(SyntaxRun {
            effective_workers: 1,
            sources: sources.len(),
            batches,
            source_bytes: sources.iter().map(|s| s.text.len() as u64).sum(),
            output_bytes: writer.bytes,
            producer: self.producer,
            cache_hits: sources.len() - missing.len(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn digest(source: &str) -> ContentHash {
        ContentHash(Sha256::digest(source.as_bytes()).into())
    }
    fn output_json(path: &str, source: &str) -> String {
        json!({"schema_version":1,"parser":"scalameta-4.15.2","sources":[{"path":path,"sha256":digest(source).to_string(),"members":[],"owners":[],"diagnostics":[]}]}).to_string()
    }
    #[test]
    fn parser_output_is_bound_and_inventory_stale_duplicate_and_size_fail() {
        let temporary = tempfile::tempdir().unwrap();
        let path = temporary.path().join("output.json");
        let expected = HashMap::from([("A.scala", (digest("object A"), 0))]);
        fs::write(&path, output_json("A.scala", "object A")).unwrap();
        let mut output = Vec::new();
        decode_output(
            &path,
            &expected,
            &"a".repeat(64),
            &mut output,
            &SyntaxLimits::default(),
        )
        .unwrap();
        let row: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(row["source_sha256"], digest("object A").to_string());
        assert_eq!(row["producer_sha256"], "a".repeat(64));
        fs::write(&path, output_json("A.scala", "object B")).unwrap();
        assert!(
            decode_output(
                &path,
                &expected,
                "producer",
                &mut Vec::new(),
                &SyntaxLimits::default()
            )
            .is_err()
        );
        fs::write(&path, output_json("B.scala", "object A")).unwrap();
        assert!(
            decode_output(
                &path,
                &expected,
                "producer",
                &mut Vec::new(),
                &SyntaxLimits::default()
            )
            .is_err()
        );
        fs::write(&path, output_json("A.scala", "object A")).unwrap();
        let limits = SyntaxLimits {
            max_output_row_bytes: 32,
            ..SyntaxLimits::default()
        };
        assert!(decode_output(&path, &expected, "producer", &mut Vec::new(), &limits).is_err());
        let limits = SyntaxLimits {
            max_output_bytes: 32,
            ..SyntaxLimits::default()
        };
        assert!(decode_output(&path, &expected, "producer", &mut Vec::new(), &limits).is_err());
    }
    #[cfg(unix)]
    fn fake_tool(directory: &Path, body: &str) -> SyntaxTool {
        use std::os::unix::fs::PermissionsExt;
        let java = directory.join("fake-java");
        fs::write(&java, format!("#!/bin/sh\n{body}\n")).unwrap();
        fs::set_permissions(&java, fs::Permissions::from_mode(0o755)).unwrap();
        let classes = directory.join("classes");
        fs::create_dir(&classes).unwrap();
        fs::write(classes.join("ScalaSpans.class"), b"fixture class").unwrap();
        SyntaxTool::pin(
            &java,
            &[classes],
            "ScalaSpans",
            None,
            &SyntaxLimits::default(),
        )
        .unwrap()
    }
    #[cfg(unix)]
    #[test]
    fn process_failure_timeout_source_change_and_tool_tamper_are_rejected() {
        let temporary = tempfile::tempdir().unwrap();
        let source = SyntaxSource {
            path: "A.scala",
            text: "object A",
            source_sha256: digest("object A"),
        };
        let tool = fake_tool(temporary.path(), "printf 'parser diagnostic' >&2\nexit 7");
        let error = tool
            .run_sources(&[source], &mut Vec::new(), &SyntaxLimits::default())
            .unwrap_err()
            .to_string();
        assert!(error.contains("parser diagnostic"));
        assert!(error.contains("failed"));
        let bad = SyntaxSource {
            source_sha256: digest("changed"),
            ..source
        };
        assert!(
            tool.run_sources(&[bad], &mut Vec::new(), &SyntaxLimits::default())
                .is_err()
        );
        fs::write(&tool.java, b"changed tool").unwrap();
        assert!(tool.verify(&SyntaxLimits::default()).is_err());
        let timeout_dir = tempfile::tempdir().unwrap();
        let tool = fake_tool(timeout_dir.path(), "while :; do :; done");
        let limits = SyntaxLimits {
            parse_timeout: Duration::from_millis(30),
            ..SyntaxLimits::default()
        };
        let start = Instant::now();
        assert!(
            tool.run_sources(&[source], &mut Vec::new(), &limits)
                .unwrap_err()
                .to_string()
                .contains("wall time")
        );
        assert!(start.elapsed() < Duration::from_secs(2));
    }
    #[cfg(unix)]
    #[test]
    fn pinned_manifest_roundtrip_and_capture_streaming_work_without_python() {
        let temporary = tempfile::tempdir().unwrap();
        let json = output_json("A.scala", "object A");
        let tool = fake_tool(temporary.path(), &format!("printf '%s' '{json}' > \"$6\""));
        let manifest = temporary.path().join("tool.json");
        tool.write_manifest(&manifest).unwrap();
        let tool = SyntaxTool::from_manifest(&manifest, &SyntaxLimits::default()).unwrap();
        let capture = temporary.path().join("capture.jsonl");
        fs::write(&capture, format!("{}\n", json!({"path":"A.scala","source_text":"object A","source_sha256":digest("object A").to_string()}))).unwrap();
        let mut output = Vec::new();
        let result = tool
            .run_capture(&capture, &mut output, 2, &SyntaxLimits::default())
            .unwrap();
        assert_eq!(result.sources, 1);
        assert_eq!(result.batches, 1);
        let row: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(row["producer_sha256"], tool.producer.to_string());
        assert!(row.get("ast").is_some());
    }
    fn capture_file(path: &Path, sources: &[(&str, &str)], padding: usize) {
        let mut out = BufWriter::new(File::create(path).unwrap());
        for (path, text) in sources {
            serde_json::to_writer(&mut out,&json!({"path":path,"source_text":text,
            "source_sha256":digest(text).to_string(),"unused_compiler_payload":"x".repeat(padding)})).unwrap();
            out.write_all(b"\n").unwrap();
        }
        out.flush().unwrap();
    }
    fn bound_row(path: &str, source: &str, producer: ContentHash) -> Vec<u8> {
        let ast=json!({"path":path,"sha256":digest(source).to_string(),"members":[],"owners":[],"diagnostics":[]}).to_string();
        let ast = RawValue::from_string(ast).unwrap();
        let source = digest(source).to_string();
        let producer = producer.to_string();
        let row = BoundRow {
            path,
            source_sha256: &source,
            producer_sha256: &producer,
            ast: ast.as_ref(),
        };
        serde_json::to_vec(&row).unwrap()
    }
    #[cfg(unix)]
    #[test]
    fn source_cache_cold_and_warm_output_match_without_relaunching_the_jvm() {
        let temporary = tempfile::tempdir().unwrap();
        let marker = temporary.path().join("calls");
        let json = output_json("A.scala", "object A");
        let tool = fake_tool(
            temporary.path(),
            &format!(
                "printf x >> '{}'\nprintf '%s' '{json}' > \"$6\"",
                marker.display()
            ),
        );
        let capture = temporary.path().join("capture.jsonl");
        capture_file(&capture, &[("A.scala", "object A")], 0);
        let cache = temporary.path().join("cache");
        let limits = SyntaxLimits::default();
        let mut cold = Vec::new();
        let first = tool
            .run_capture_cached(&capture, &mut cold, 8, &limits, &cache)
            .unwrap();
        let mut warm = Vec::new();
        let next = tool
            .run_capture_cached(&capture, &mut warm, 8, &limits, &cache)
            .unwrap();
        assert_eq!(cold, warm);
        assert_eq!(first.batches, 1);
        assert_eq!(first.cache_hits, 0);
        assert_eq!(next.batches, 0);
        assert_eq!(next.cache_hits, 1);
        assert_eq!(fs::read(marker).unwrap(), b"x");
    }
    #[cfg(unix)]
    #[test]
    fn wire_heavy_documents_are_grouped_by_actual_source_bytes() {
        let temporary = tempfile::tempdir().unwrap();
        let mut parsed: serde_json::Value =
            serde_json::from_str(&output_json("A.scala", "object A")).unwrap();
        parsed["sources"].as_array_mut().unwrap().push(
            serde_json::from_str::<serde_json::Value>(&output_json("B.scala", "object B")).unwrap()
                ["sources"][0]
                .clone(),
        );
        let tool = fake_tool(
            temporary.path(),
            &format!("printf '%s' '{}' > \"$6\"", parsed),
        );
        let capture = temporary.path().join("capture.jsonl");
        capture_file(
            &capture,
            &[("A.scala", "object A"), ("B.scala", "object B")],
            4096,
        );
        let limits = SyntaxLimits {
            batch_source_bytes: 128,
            ..Default::default()
        };
        let result = tool
            .run_capture(&capture, &mut Vec::new(), 4, &limits)
            .unwrap();
        assert_eq!(result.sources, 2);
        assert_eq!(result.batches, 1);
    }
    #[cfg(unix)]
    #[test]
    fn imported_rows_reuse_unchanged_sources_and_parse_only_the_missing_source() {
        let temporary = tempfile::tempdir().unwrap();
        let json = output_json("B.scala", "object B");
        let tool = fake_tool(temporary.path(), &format!("printf '%s' '{json}' > \"$6\""));
        let cache = temporary.path().join("cache");
        let existing = temporary.path().join("existing.jsonl");
        let mut first = bound_row("A.scala", "object A", tool.producer);
        first.push(b'\n');
        fs::write(&existing, &first).unwrap();
        let limits = SyntaxLimits::default();
        assert_eq!(
            tool.import_syntax_cache(&existing, &cache, &limits)
                .unwrap(),
            1
        );
        let capture = temporary.path().join("capture.jsonl");
        capture_file(
            &capture,
            &[("A.scala", "object A"), ("B.scala", "object B")],
            0,
        );
        let mut out = Vec::new();
        let result = tool
            .run_capture_cached(&capture, &mut out, 4, &limits, &cache)
            .unwrap();
        assert_eq!(result.cache_hits, 1);
        assert_eq!(result.batches, 1);
        let mut expected = first;
        expected.extend(bound_row("B.scala", "object B", tool.producer));
        expected.push(b'\n');
        assert_eq!(out, expected);
        let mut again = Vec::new();
        let warm = tool
            .run_capture_cached(&capture, &mut again, 4, &limits, &cache)
            .unwrap();
        assert_eq!(warm.cache_hits, 2);
        assert_eq!(warm.batches, 0);
        assert_eq!(again, out);
    }
    #[cfg(unix)]
    #[test]
    fn source_cache_keys_bind_path_source_and_producer_and_reject_corrupt_rows() {
        let temporary = tempfile::tempdir().unwrap();
        let producer = digest("tool");
        let cache = SourceCache::new(temporary.path(), producer).unwrap();
        let row = bound_row("A.scala", "object A", producer);
        let limits = SyntaxLimits::default();
        cache.stage_row(&row, &limits).unwrap();
        cache.publish(&limits).unwrap();
        let key = source_cache_key(producer, "A.scala", digest("object A"));
        assert!(cache.probe(key, &limits).unwrap());
        assert!(
            !cache
                .probe(
                    source_cache_key(producer, "A.scala", digest("object changed")),
                    &limits
                )
                .unwrap()
        );
        assert!(
            !cache
                .probe(
                    source_cache_key(producer, "B.scala", digest("object A")),
                    &limits
                )
                .unwrap()
        );
        let other = SourceCache::new(temporary.path(), digest("new tool")).unwrap();
        assert!(!other.probe(key, &limits).unwrap());
        let file = cache.path(key);
        let mut bytes = fs::read(&file).unwrap();
        *bytes.last_mut().unwrap() ^= 1;
        fs::write(&file, bytes).unwrap();
        assert!(cache.load(key, &mut Vec::new(), &limits).is_err());
        assert!(
            cache
                .stage_row(
                    &bound_row("A.scala", "object A", digest("foreign")),
                    &limits
                )
                .is_err()
        );
    }
    #[cfg(unix)]
    #[test]
    fn changed_tool_after_parsing_cannot_publish_cache_rows() {
        let temporary = tempfile::tempdir().unwrap();
        let json = output_json("A.scala", "object A");
        let tool = fake_tool(
            temporary.path(),
            &format!(
                "printf changed > '{}/classes/ScalaSpans.class'\nprintf '%s' '{json}' > \"$6\"",
                temporary.path().display()
            ),
        );
        let capture = temporary.path().join("capture.jsonl");
        capture_file(&capture, &[("A.scala", "object A")], 0);
        let dir = temporary.path().join("cache");
        let limits = SyntaxLimits::default();
        assert!(
            tool.run_capture_cached(&capture, &mut Vec::new(), 1, &limits, &dir)
                .is_err()
        );
        let cache = SourceCache::new(&dir, tool.producer).unwrap();
        assert!(
            !cache
                .probe(
                    source_cache_key(tool.producer, "A.scala", digest("object A")),
                    &limits
                )
                .unwrap()
        );
    }
    #[test]
    #[ignore = "requires the explicitly cached Scala/Scalameta jars and Java runtime"]
    fn native_cached_toolchain_compiles_and_parses_real_scala() {
        let temporary = tempfile::tempdir().unwrap();
        let exporter = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../../compiler-selector/engine/spans/ScalaSpans.scala");
        let limits = SyntaxLimits::default();
        let tool = SyntaxTool::compile_cached(&exporter, temporary.path(), &limits).unwrap();
        let source = "object Real { def f(x: Int): Int = x + 1 }";
        let mut output = Vec::new();
        tool.run_sources(
            &[SyntaxSource {
                path: "Real.scala",
                text: source,
                source_sha256: digest(source),
            }],
            &mut output,
            &limits,
        )
        .unwrap();
        let row: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(row["source_sha256"], digest(source).to_string());
        assert!(
            row["ast"]["members"]
                .as_array()
                .unwrap()
                .iter()
                .any(|member| member["name"] == "f")
        );
        let again = SyntaxTool::compile_cached(&exporter, temporary.path(), &limits).unwrap();
        assert_eq!(again.producer, tool.producer);
        let capture = temporary.path().join("capture.jsonl");
        capture_file(&capture, &[("Real.scala", source)], 0);
        let cache = temporary.path().join("source-cache");
        let mut cold = Vec::new();
        let mut warm = Vec::new();
        let first = tool
            .run_capture_cached(&capture, &mut cold, 2, &limits, &cache)
            .unwrap();
        let second = tool
            .run_capture_cached(&capture, &mut warm, 2, &limits, &cache)
            .unwrap();
        assert_eq!(first.batches, 1);
        assert_eq!(second.batches, 0);
        assert_eq!(second.cache_hits, 1);
        assert_eq!(output, cold);
        assert_eq!(cold, warm);
    }
}
