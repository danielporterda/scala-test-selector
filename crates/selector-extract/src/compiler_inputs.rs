//! Admission of relocated compiler product inventories. Complete class absence
//! is proved by every captured file's bytes, never by the Scala source list.
use crate::{json_error, sha};
use flate2::read::MultiGzDecoder;
use rayon::prelude::*;
use selector_types::{ContentHash, Error};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{HashMap, HashSet};
use std::io::{Read, Write};
use std::path::{Component, Path, PathBuf};

#[derive(Clone, Debug)]
pub struct InventoryLimits {
    pub workers: usize,
    pub max_manifest_bytes: u64,
    pub max_directory_files: usize,
    pub max_directory_bytes: u64,
}
impl Default for InventoryLimits {
    fn default() -> Self {
        Self {
            workers: 4,
            max_manifest_bytes: 64 * 1024 * 1024,
            max_directory_files: 250_000,
            max_directory_bytes: 8 * 1024 * 1024 * 1024,
        }
    }
}
#[derive(Clone, Copy, Debug, Serialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum InventoryStatus {
    Verified,
    Missing,
    FingerprintMismatch,
    Unsupported,
    ResourceLimited,
}
#[derive(Debug, Serialize)]
pub struct ProductReceipt {
    pub captured_path: String,
    pub physical_path: PathBuf,
    pub expected_sha256: String,
    pub observed_sha256: Option<String>,
    pub status: InventoryStatus,
    pub observed_files: u64,
    pub observed_bytes: u64,
    pub classes: usize,
}
#[derive(Debug, Serialize)]
pub struct InventoryReceipt {
    pub schema: &'static str,
    pub revision: String,
    pub manifest_sha256: String,
    pub identity: String,
    pub relocated_root: PathBuf,
    pub products: Vec<ProductReceipt>,
}
#[derive(Debug)]
pub struct CompilerInputs {
    pub identity: ContentHash,
    pub receipt: InventoryReceipt,
    manifest: ContentHash,
    products: HashMap<String, ProductInventory>,
}
#[derive(Debug)]
pub struct ProductInventory {
    pub path: PathBuf,
    pub expected: ContentHash,
    pub status: InventoryStatus,
    classes: Vec<String>,
}
impl ProductInventory {
    /// None preserves uncertainty; an empty verified slice proves no classes.
    pub fn classes(&self) -> Option<&[String]> {
        (self.status == InventoryStatus::Verified).then_some(&self.classes)
    }
    pub fn contains(&self, owner: &str) -> Option<bool> {
        self.classes()
            .map(|classes| classes.binary_search_by(|s| s.as_str().cmp(owner)).is_ok())
    }
}
impl CompilerInputs {
    pub fn matches_manifest(&self, bytes: &[u8]) -> bool {
        self.manifest == sha(bytes)
    }
    pub fn product(&self, captured_path: &str, expected: ContentHash) -> Option<&ProductInventory> {
        self.products
            .get(captured_path)
            .filter(|p| p.expected == expected)
    }
}
#[derive(Deserialize)]
struct Manifest {
    schema_version: String,
    revision: String,
    source_root: PathBuf,
    #[serde(default)]
    errors: Vec<serde_json::Value>,
    contexts: Vec<Context>,
    input_objects: Vec<Object>,
}
#[derive(Deserialize)]
struct Context {
    full_classpath: Vec<Entry>,
}
#[derive(Deserialize)]
struct Entry {
    path: String,
    input_object: Option<String>,
    sha256: Option<String>,
    #[serde(default)]
    project_output_origins: Vec<serde_json::Value>,
}
#[derive(Deserialize)]
struct Object {
    path: String,
    kind: String,
    sha256: String,
    files: Option<u64>,
    bytes: u64,
}
struct Row {
    path: String,
    bytes: u64,
    sha: ContentHash,
}
struct Observation {
    status: InventoryStatus,
    hash: Option<ContentHash>,
    files: u64,
    bytes: u64,
    classes: Vec<String>,
}

/// Rehash each unique captured product once. This must run before a persistent
/// extraction cache lookup; include the returned identity in that stage key.
/// The Arc passed to extraction retains only immutable class-name inventories.
pub fn admit(
    capture_manifest: &Path,
    relocated_root: &Path,
    limits: &InventoryLimits,
) -> Result<CompilerInputs, Error> {
    if limits.workers == 0 || limits.max_directory_files == 0 || limits.max_manifest_bytes == 0 {
        return Err(Error::Invalid("compiler inventory limits"));
    }
    let file = std::fs::File::open(capture_manifest)?;
    let reader: Box<dyn Read> = if capture_manifest.extension().is_some_and(|s| s == "gz") {
        Box::new(MultiGzDecoder::new(file))
    } else {
        Box::new(file)
    };
    let mut bytes = Vec::new();
    reader
        .take(limits.max_manifest_bytes + 1)
        .read_to_end(&mut bytes)?;
    if bytes.len() as u64 > limits.max_manifest_bytes {
        return Err(Error::Limit("compiler inventory manifest bytes"));
    }
    let manifest_hash = sha(&bytes);
    let manifest: Manifest = serde_json::from_slice(&bytes).map_err(json_error)?;
    if manifest.schema_version != "sbt-compiler-context/v1"
        || !manifest.errors.is_empty()
        || !manifest.source_root.is_absolute()
        || manifest.revision.is_empty()
    {
        return Err(Error::Invalid("compiler inventory manifest"));
    }
    let relocated_root = std::fs::canonicalize(relocated_root)?;
    if !relocated_root.is_dir() {
        return Err(Error::Invalid("compiler inventory relocation root"));
    }
    let mut objects = HashMap::new();
    for object in &manifest.input_objects {
        ContentHash::from_hex(&object.sha256)?;
        if objects.insert(object.path.as_str(), object).is_some() {
            return Err(Error::Invalid("duplicate compiler inventory object"));
        }
    }
    let mut required = HashSet::new();
    for context in &manifest.contexts {
        for entry in &context.full_classpath {
            if !entry.project_output_origins.is_empty() {
                let object_path = entry.input_object.as_deref().unwrap_or(&entry.path);
                let object = objects
                    .get(object_path)
                    .ok_or(Error::Invalid("compiler product object absent"))?;
                if entry.sha256.as_deref() != Some(&object.sha256) {
                    return Err(Error::Invalid("compiler product object hash binding"));
                }
                required.insert(object_path);
            }
        }
    }
    let mut required: Vec<_> = required.into_iter().collect();
    required.sort_unstable();
    let mut jobs = Vec::with_capacity(required.len());
    for path in required {
        let object = objects[path];
        let relative = Path::new(path)
            .strip_prefix(&manifest.source_root)
            .map_err(|_| Error::Invalid("compiler product outside captured root"))?;
        if relative
            .components()
            .any(|c| !matches!(c, Component::Normal(_)))
        {
            return Err(Error::Invalid("compiler product relative path"));
        }
        jobs.push((object, relocated_root.join(relative)));
    }
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(limits.workers)
        .build()
        .map_err(|e| Error::Message(e.to_string()))?;
    let observations: Vec<_> = pool.install(|| {
        jobs.par_iter()
            .map(|(object, path)| observe(object, path, limits))
            .collect()
    });
    let mut identity = Sha256::new();
    identity.update(b"verified-compiler-products/v1");
    identity.update(manifest_hash.0);
    let mut products = HashMap::with_capacity(jobs.len());
    let mut receipt = Vec::with_capacity(jobs.len());
    for ((object, path), observed) in jobs.into_iter().zip(observations) {
        let expected = ContentHash::from_hex(&object.sha256)?;
        identity.update((object.path.len() as u64).to_le_bytes());
        identity.update(object.path.as_bytes());
        let physical = path.to_string_lossy();
        identity.update((physical.len() as u64).to_le_bytes());
        identity.update(physical.as_bytes());
        identity.update([observed.status as u8]);
        identity.update(observed.hash.unwrap_or_default().0);
        identity.update(observed.files.to_le_bytes());
        identity.update(observed.bytes.to_le_bytes());
        receipt.push(ProductReceipt {
            captured_path: object.path.clone(),
            physical_path: path.clone(),
            expected_sha256: object.sha256.clone(),
            observed_sha256: observed.hash.map(|h| h.to_string()),
            status: observed.status,
            observed_files: observed.files,
            observed_bytes: observed.bytes,
            classes: observed.classes.len(),
        });
        products.insert(
            object.path.clone(),
            ProductInventory {
                path,
                expected,
                status: observed.status,
                classes: observed.classes,
            },
        );
    }
    let identity = ContentHash(identity.finalize().into());
    Ok(CompilerInputs {
        identity,
        manifest: manifest_hash,
        products,
        receipt: InventoryReceipt {
            schema: "verified-compiler-products/v1",
            revision: manifest.revision,
            manifest_sha256: manifest_hash.to_string(),
            identity: identity.to_string(),
            relocated_root,
            products: receipt,
        },
    })
}
fn observe(object: &Object, root: &Path, limits: &InventoryLimits) -> Observation {
    let failed = |status| Observation {
        status,
        hash: None,
        files: 0,
        bytes: 0,
        classes: Vec::new(),
    };
    if object.kind == "absent_empty_project_output" {
        return match std::fs::symlink_metadata(root) {
            Err(e)
                if e.kind() == std::io::ErrorKind::NotFound
                    && object.sha256
                        == sha(b"{\"kind\":\"absent_empty_project_output\"}").to_string()
                    && object.bytes == 0 =>
            {
                Observation {
                    status: InventoryStatus::Verified,
                    hash: Some(sha(b"{\"kind\":\"absent_empty_project_output\"}")),
                    files: 0,
                    bytes: 0,
                    classes: Vec::new(),
                }
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => failed(InventoryStatus::Missing),
            _ => failed(InventoryStatus::FingerprintMismatch),
        };
    }
    if object.kind != "directory" || object.files.is_none() {
        return failed(InventoryStatus::Unsupported);
    }
    if object.files.unwrap() > limits.max_directory_files as u64
        || object.bytes > limits.max_directory_bytes
    {
        return failed(InventoryStatus::ResourceLimited);
    }
    let Ok(meta) = std::fs::symlink_metadata(root) else {
        return failed(InventoryStatus::Missing);
    };
    if !meta.is_dir() || meta.file_type().is_symlink() {
        return failed(InventoryStatus::Unsupported);
    }
    let (rows, total) = match scan(root, limits) {
        Ok(scanned) => scanned,
        Err(Error::Limit(_)) => return failed(InventoryStatus::ResourceLimited),
        Err(_) => return failed(InventoryStatus::Unsupported),
    };
    let hash = inventory_hash(&rows);
    let matches = rows.len() as u64 == object.files.unwrap()
        && total == object.bytes
        && hash.to_string() == object.sha256;
    let mut classes: Vec<_> = if matches {
        rows.iter()
            .filter_map(|r| r.path.strip_suffix(".class").map(str::to_owned))
            .collect()
    } else {
        Vec::new()
    };
    // Removing '.class' changes prefix ordering (C$Inner.class sorts before
    // C.class, while C sorts before C$Inner). Absence lookups require this order.
    classes.sort_unstable();
    Observation {
        status: if matches {
            InventoryStatus::Verified
        } else {
            InventoryStatus::FingerprintMismatch
        },
        hash: Some(hash),
        files: rows.len() as u64,
        bytes: total,
        classes,
    }
}
fn scan(root: &Path, limits: &InventoryLimits) -> Result<(Vec<Row>, u64), Error> {
    let mut pending = vec![root.to_path_buf()];
    let mut rows = Vec::new();
    let mut total = 0u64;
    let mut directories = 0usize;
    while let Some(directory) = pending.pop() {
        directories += 1;
        if directories > limits.max_directory_files {
            return Err(Error::Limit("compiler product directories"));
        }
        for entry in std::fs::read_dir(directory)? {
            let entry = entry?;
            let kind = entry.file_type()?;
            if kind.is_symlink() {
                return Err(Error::Invalid("compiler product symlink"));
            }
            if kind.is_dir() {
                pending.push(entry.path());
                continue;
            }
            if !kind.is_file() {
                return Err(Error::Invalid("compiler product file type"));
            }
            if rows.len() >= limits.max_directory_files {
                return Err(Error::Limit("compiler product files"));
            }
            let path = entry.path();
            let relative = path
                .strip_prefix(root)
                .unwrap()
                .to_str()
                .ok_or(Error::Invalid("compiler product UTF8 path"))?
                .replace(std::path::MAIN_SEPARATOR, "/");
            let mut file = std::fs::File::open(&path)?;
            let mut hash = Sha256::new();
            let mut size = 0u64;
            let mut block = [0u8; 64 * 1024];
            loop {
                let n = file.read(&mut block)?;
                if n == 0 {
                    break;
                }
                size += n as u64;
                total = total
                    .checked_add(n as u64)
                    .ok_or(Error::Limit("compiler product bytes"))?;
                if total > limits.max_directory_bytes {
                    return Err(Error::Limit("compiler product bytes"));
                }
                hash.update(&block[..n]);
            }
            rows.push(Row {
                path: relative,
                bytes: size,
                sha: ContentHash(hash.finalize().into()),
            });
        }
    }
    rows.sort_unstable_by(|a, b| a.path.cmp(&b.path));
    Ok((rows, total))
}
struct HashWriter(Sha256);
impl Write for HashWriter {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        self.0.update(bytes);
        Ok(bytes.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}
fn inventory_hash(rows: &[Row]) -> ContentHash {
    let mut out = HashWriter(Sha256::new());
    out.write_all(b"[").unwrap();
    for (i, row) in rows.iter().enumerate() {
        if i > 0 {
            out.write_all(b",").unwrap();
        }
        write!(out, "{{\"bytes\":{},\"path\":", row.bytes).unwrap();
        json_string(&mut out, &row.path);
        write!(out, ",\"sha256\":\"{}\"}}", row.sha).unwrap();
    }
    out.write_all(b"]").unwrap();
    ContentHash(out.0.finalize().into())
}
fn json_string(out: &mut HashWriter, text: &str) {
    out.write_all(b"\"").unwrap();
    for c in text.chars() {
        match c {
            '"' => out.write_all(b"\\\"").unwrap(),
            '\\' => out.write_all(b"\\\\").unwrap(),
            '\n' => out.write_all(b"\\n").unwrap(),
            '\r' => out.write_all(b"\\r").unwrap(),
            '\t' => out.write_all(b"\\t").unwrap(),
            '\u{8}' => out.write_all(b"\\b").unwrap(),
            '\u{c}' => out.write_all(b"\\f").unwrap(),
            c if !(' '..='~').contains(&c) => {
                for unit in c.encode_utf16(&mut [0u16; 2]) {
                    write!(out, "\\u{unit:04x}").unwrap();
                }
            }
            c => out.write_all(&[c as u8]).unwrap(),
        }
    }
    out.write_all(b"\"").unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    #[test]
    fn relocated_full_inventory_rejects_changed_missing_and_added_classes() {
        let directory = tempfile::tempdir().unwrap();
        let classes = directory.path().join("target/classes");
        std::fs::create_dir_all(classes.join("p")).unwrap();
        std::fs::write(classes.join("p/C.class"), b"captured").unwrap();
        std::fs::write(classes.join("p/C$Inner.class"), b"nested").unwrap();
        let (rows, total) = scan(&classes, &InventoryLimits::default()).unwrap();
        let hash = inventory_hash(&rows);
        let manifest = json!({"schema_version":"sbt-compiler-context/v1","revision":"r","source_root":"/old/root",
            "errors":[],"contexts":[{"full_classpath":[{"path":"/old/root/target/classes","sha256":hash.to_string(),
                "project_output_origins":[{"context_id":"a"}]}]}],
            "input_objects":[{"path":"/old/root/target/classes","kind":"directory","sha256":hash.to_string(),"files":rows.len(),"bytes":total}]});
        let path = directory.path().join("contexts.json");
        std::fs::write(&path, manifest.to_string()).unwrap();
        let admitted = admit(&path, directory.path(), &InventoryLimits::default()).unwrap();
        let product = admitted.product("/old/root/target/classes", hash).unwrap();
        assert_eq!(product.contains("p/C"), Some(true));
        assert_eq!(product.contains("p/C$Inner"), Some(true));
        assert_eq!(product.contains("p/JavaShadow"), Some(false));
        std::fs::write(classes.join("p/JavaShadow.class"), b"new").unwrap();
        let changed = admit(&path, directory.path(), &InventoryLimits::default()).unwrap();
        assert_ne!(admitted.identity, changed.identity);
        assert_eq!(
            changed
                .product("/old/root/target/classes", hash)
                .unwrap()
                .contains("p/JavaShadow"),
            None
        );
        assert_eq!(
            product.contains("p/JavaShadow"),
            Some(false),
            "admitted owner remains immutable"
        );
        std::fs::remove_dir_all(&classes).unwrap();
        let missing = admit(&path, directory.path(), &InventoryLimits::default()).unwrap();
        assert_eq!(missing.receipt.products[0].status, InventoryStatus::Missing);
    }
    #[test]
    fn canonical_inventory_encoding_matches_capture_unicode_and_key_order() {
        let row = Row {
            path: "p/é😀\\\".class".into(),
            bytes: 3,
            sha: sha(b"abc"),
        };
        let json = format!(
            "[{{\"bytes\":3,\"path\":\"p/\\u00e9\\ud83d\\ude00\\\\\\\".class\",\"sha256\":\"{}\"}}]",
            sha(b"abc")
        );
        assert_eq!(inventory_hash(&[row]), sha(json.as_bytes()));
    }
}
