//! New retained-analysis source/product correspondence. This is neither an effect
//! summary nor permission to discard a source Unknown. Only `admit` constructs a
//! `VerifiedBinding`; callers must separately admit compiled effect coverage.
use crate::classfile;
use flate2::read::MultiGzDecoder;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fmt,
    fs::{self, File},
    io::{BufRead, BufReader, Read},
    ops::Range,
    path::{Component, Path, PathBuf},
    sync::Arc,
};

pub type Hash = [u8; 32];
#[derive(Debug)]
pub enum Error {
    Io(std::io::Error),
    Json(serde_json::Error),
    Invalid(&'static str),
    Limit(&'static str),
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(e) => e.fmt(f),
            Self::Json(e) => e.fmt(f),
            Self::Invalid(s) | Self::Limit(s) => f.write_str(s),
        }
    }
}
impl std::error::Error for Error {}
impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}
impl From<serde_json::Error> for Error {
    fn from(e: serde_json::Error) -> Self {
        Self::Json(e)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MethodAbi {
    pub name: String,
    pub descriptor: String,
    pub flags: u16,
    pub has_code: bool,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Pin {
    pub path: PathBuf,
    pub sha256: String,
    pub bytes: u64,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ContextInput {
    pub context: String,
    pub analysis: Pin,
    pub reader_output: Pin,
    pub reader_receipt: Pin,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Manifest {
    pub schema: String,
    pub qualification: String,
    pub producer_sha256: String,
    pub producer_inputs: Vec<Pin>,
    pub contexts: Pin,
    pub documents: Pin,
    pub compile_receipt: Pin,
    pub inputs: Vec<ContextInput>,
}
/// All expected pins come from the supervising invocation, outside the manifest.
#[derive(Clone, Debug)]
pub struct Expectations {
    pub manifest: Hash,
    pub producer: Hash,
    pub contexts: Hash,
    pub documents: Hash,
    pub compile_receipt: Hash,
}
#[derive(Clone, Debug)]
pub struct Limits {
    pub max_manifest_bytes: u64,
    pub max_json_bytes: u64,
    pub max_document_bytes: u64,
    pub max_line_bytes: usize,
    pub max_class_bytes: u64,
    pub max_inventory_bytes: u64,
    pub max_owned_bytes: u64,
    pub max_sources: usize,
    pub max_classes: usize,
    pub max_methods: usize,
    pub max_files: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            max_manifest_bytes: 2 << 20,
            max_json_bytes: 512 << 20,
            max_document_bytes: 2 << 30,
            max_line_bytes: 32 << 20,
            max_class_bytes: 32 << 20,
            max_inventory_bytes: 512 << 20,
            max_owned_bytes: 256 << 20,
            max_sources: 100_000,
            max_classes: 100_000,
            max_methods: 2_000_000,
            max_files: 200_000,
        }
    }
}
struct Budget {
    used: u64,
    max: u64,
}
impl Budget {
    fn charge(&mut self, n: u64) -> Result<(), Error> {
        self.used = self
            .used
            .checked_add(n)
            .ok_or(Error::Limit("owned-byte overflow"))?;
        if self.used > self.max {
            return Err(Error::Limit("owned-byte budget"));
        }
        Ok(())
    }
}
#[derive(Default)]
struct Texts {
    values: Vec<Arc<str>>,
    ids: HashMap<Arc<str>, u32>,
}
impl Texts {
    fn intern(&mut self, s: &str, b: &mut Budget) -> Result<u32, Error> {
        if let Some(id) = self.ids.get(s) {
            return Ok(*id);
        }
        b.charge(s.len() as u64 + 96)?;
        let id = u32::try_from(self.values.len()).map_err(|_| Error::Limit("text index"))?;
        let text: Arc<str> = s.into();
        self.values.push(text.clone());
        self.ids.insert(text, id);
        Ok(id)
    }
    fn get(&self, id: u32) -> &str {
        &self.values[id as usize]
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct MethodId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ClassId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SourceId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pending {
    SourceNotInSemanticDb,
    NoExactSourceDefinition,
    NoExactCompiledClass,
    NoPublicZeroArgumentConstructor,
    NoModuleInitializationPhase,
    AmbiguousRoot,
}
impl fmt::Display for Pending {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for Pending {}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RootKind {
    Class,
    Module,
}
#[derive(Clone, Copy, Debug)]
pub struct RootEntry {
    pub source: SourceId,
    pub class: ClassId,
    pub entry: MethodId,
    pub kind: RootKind,
}
struct SourceRow {
    context: u32,
    path: u32,
    hash: Hash,
    semantic: bool,
    classes: Range<usize>,
    methods: Range<usize>,
    definitions: Vec<(u32, u32)>,
}
struct ClassRow {
    source: SourceId,
    owner: u32,
    hash: Hash,
    flags: u16,
    module_field: bool,
    methods: Range<usize>,
    bytes: Arc<[u8]>,
}
struct MethodRow {
    class: ClassId,
    name: u32,
    descriptor: u32,
    flags: u16,
    has_code: bool,
}
/// Opaque validated correspondence. Absence of a method is not an empty recipe.
pub struct VerifiedBinding {
    identity: Hash,
    contexts: Hash,
    documents: Hash,
    texts: Texts,
    sources: Vec<SourceRow>,
    classes: Vec<ClassRow>,
    methods: Vec<MethodRow>,
    owned_bytes: u64,
}
#[derive(Clone, Copy)]
pub struct MethodView<'a> {
    pub id: MethodId,
    pub class: ClassId,
    pub context: &'a str,
    pub owner: &'a str,
    pub name: &'a str,
    pub descriptor: &'a str,
    pub class_sha256: Hash,
    pub flags: u16,
    pub has_code: bool,
}
#[derive(Clone, Copy)]
pub struct ClassView<'a> {
    pub id: ClassId,
    pub source: SourceId,
    pub context: &'a str,
    pub owner: &'a str,
    pub class_sha256: Hash,
    pub flags: u16,
    pub methods: usize,
}
#[derive(Clone, Copy)]
pub struct SourceView<'a> {
    pub id: SourceId,
    pub context: &'a str,
    pub path: &'a str,
    pub source_sha256: Hash,
    pub semantic_db_verified: bool,
    pub classes: usize,
    pub methods: usize,
}
impl VerifiedBinding {
    pub fn identity(&self) -> Hash {
        self.identity
    }
    pub fn contexts_identity(&self) -> Hash {
        self.contexts
    }
    pub fn documents_identity(&self) -> Hash {
        self.documents
    }
    pub fn owned_bytes(&self) -> u64 {
        self.owned_bytes
    }
    pub fn source_count(&self) -> usize {
        self.sources.len()
    }
    pub fn class_count(&self) -> usize {
        self.classes.len()
    }
    pub fn method_count(&self) -> usize {
        self.methods.len()
    }
    pub fn source(&self, id: SourceId) -> Option<SourceView<'_>> {
        let r = self.sources.get(id.0 as usize)?;
        Some(SourceView {
            id,
            context: self.texts.get(r.context),
            path: self.texts.get(r.path),
            source_sha256: r.hash,
            semantic_db_verified: r.semantic,
            classes: r.classes.len(),
            methods: r.methods.len(),
        })
    }
    pub fn find_source(&self, context: &str, path: &str) -> Option<SourceId> {
        self.sources
            .iter()
            .position(|r| self.texts.get(r.context) == context && self.texts.get(r.path) == path)
            .map(|i| SourceId(i as u32))
    }
    pub fn method(&self, id: MethodId) -> Option<MethodView<'_>> {
        let r = self.methods.get(id.0 as usize)?;
        let c = &self.classes[r.class.0 as usize];
        let s = &self.sources[c.source.0 as usize];
        Some(MethodView {
            id,
            class: r.class,
            context: self.texts.get(s.context),
            owner: self.texts.get(c.owner),
            name: self.texts.get(r.name),
            descriptor: self.texts.get(r.descriptor),
            class_sha256: c.hash,
            flags: r.flags,
            has_code: r.has_code,
        })
    }
    pub fn class(&self, id: ClassId) -> Option<ClassView<'_>> {
        let c = self.classes.get(id.0 as usize)?;
        let s = &self.sources[c.source.0 as usize];
        Some(ClassView {
            id,
            source: c.source,
            context: self.texts.get(s.context),
            owner: self.texts.get(c.owner),
            class_sha256: c.hash,
            flags: c.flags,
            methods: c.methods.len(),
        })
    }
    pub fn class_bytes_arc(&self, id: ClassId) -> Option<Arc<[u8]>> {
        self.classes.get(id.0 as usize).map(|c| c.bytes.clone())
    }
    pub fn class_bytes(&self, id: ClassId) -> Option<&[u8]> {
        self.classes.get(id.0 as usize).map(|c| c.bytes.as_ref())
    }
    /// Coarse changed-file seed universe: every method, including generated ones.
    pub fn changed_methods(
        &self,
        id: SourceId,
    ) -> Result<impl Iterator<Item = MethodId> + '_, Pending> {
        let r = self
            .sources
            .get(id.0 as usize)
            .ok_or(Pending::SourceNotInSemanticDb)?;
        if !r.semantic {
            return Err(Pending::SourceNotInSemanticDb);
        }
        Ok(r.methods.clone().map(|i| MethodId(i as u32)))
    }
    /// Only top-level exact compiler class/object definitions are supported here.
    /// Nested/encoded name mappings remain pending, never guessed from spelling.
    pub fn root_entry(
        &self,
        context: &str,
        path: &str,
        jvm_class: &str,
        kind: RootKind,
    ) -> Result<RootEntry, Pending> {
        let source = self
            .find_source(context, path)
            .ok_or(Pending::SourceNotInSemanticDb)?;
        let s = &self.sources[source.0 as usize];
        if !s.semantic {
            return Err(Pending::SourceNotInSemanticDb);
        }
        let semantic = match kind {
            RootKind::Class => format!("{jvm_class}#"),
            RootKind::Module => {
                let owner = jvm_class
                    .strip_suffix('$')
                    .ok_or(Pending::NoExactSourceDefinition)?;
                format!("{owner}.")
            }
        };
        let k = match kind {
            RootKind::Class => 13,
            RootKind::Module => 10,
        };
        if !s
            .definitions
            .iter()
            .any(|(name, kind)| *kind == k && self.texts.get(*name) == semantic)
        {
            return Err(Pending::NoExactSourceDefinition);
        }
        let mut cs = s
            .classes
            .clone()
            .filter(|i| self.texts.get(self.classes[*i].owner) == jvm_class);
        let c = cs.next().ok_or(Pending::NoExactCompiledClass)?;
        if cs.next().is_some() {
            return Err(Pending::AmbiguousRoot);
        }
        let class = &self.classes[c];
        let (name, required, absent) = match kind {
            RootKind::Class => {
                if class.flags & (0x200 | 0x400) != 0 || class.flags & 1 == 0 {
                    return Err(Pending::NoPublicZeroArgumentConstructor);
                }
                ("<init>", 1, Pending::NoPublicZeroArgumentConstructor)
            }
            RootKind::Module => {
                if !class.module_field {
                    return Err(Pending::NoModuleInitializationPhase);
                }
                ("<clinit>", 8, Pending::NoModuleInitializationPhase)
            }
        };
        let mut ms = class.methods.clone().filter(|i| {
            let m = &self.methods[*i];
            self.texts.get(m.name) == name
                && self.texts.get(m.descriptor) == "()V"
                && m.flags & required == required
                && !(kind == RootKind::Class && m.flags & 8 != 0)
                && m.has_code
        });
        let entry = ms.next().ok_or(absent)?;
        if ms.next().is_some() {
            return Err(Pending::AmbiguousRoot);
        }
        Ok(RootEntry {
            source,
            class: ClassId(c as u32),
            entry: MethodId(entry as u32),
            kind,
        })
    }
}
#[derive(Deserialize)]
struct Contexts {
    source_root: PathBuf,
    contexts: Vec<CapturedContext>,
    input_objects: Vec<Object>,
}
#[derive(Deserialize)]
struct CapturedContext {
    context_id: String,
    class_directory: PathBuf,
    source_records: Vec<CapturedSource>,
    full_classpath: Vec<ClasspathEntry>,
}
#[derive(Deserialize)]
struct CapturedSource {
    path: PathBuf,
    repo_relative_path: String,
    sha256: String,
}
#[derive(Deserialize)]
struct ClasspathEntry {
    index: u32,
    path: PathBuf,
    input_object: PathBuf,
    sha256: String,
}
#[derive(Deserialize)]
struct Object {
    path: PathBuf,
    kind: String,
    sha256: Option<String>,
    files: Option<u64>,
    bytes: Option<u64>,
}
#[derive(Clone, Deserialize)]
struct Stamp {
    class: String,
    written: String,
    hash: Option<String>,
    modified: Option<u64>,
}
#[derive(Deserialize)]
struct Product {
    path: String,
    stamp: Stamp,
    bytes: u64,
    sha256: String,
    recomputed_content_hash: Stamp,
}
#[derive(Deserialize)]
struct ZincRow {
    source: String,
    source_stamp: Stamp,
    source_bytes: u64,
    source_sha256: String,
    recomputed_source_farmhash: Stamp,
    products: Vec<Product>,
}
#[derive(Deserialize)]
struct Receipt {
    inputs: Vec<Pin>,
    commands: Vec<Command>,
    all_inputs_unchanged: bool,
}
#[derive(Deserialize)]
struct Command {
    case: String,
    command: Vec<String>,
    exit_code: i32,
    stdout: PathBuf,
    stdout_bytes: u64,
}
#[derive(Deserialize)]
struct Doc<'a> {
    #[serde(borrow)]
    path: &'a str,
    #[serde(borrow)]
    source_sha256: &'a str,
    #[serde(borrow)]
    source_contexts: Vec<&'a str>,
    #[serde(borrow)]
    source_text: Option<&'a serde_json::value::RawValue>,
    #[serde(borrow)]
    document: &'a serde_json::value::RawValue,
}
#[derive(Deserialize)]
struct Definitions<'a> {
    #[serde(borrow)]
    symbols: Vec<Symbol<'a>>,
    #[serde(borrow)]
    occurrences: Vec<Occurrence<'a>>,
}
#[derive(Deserialize)]
struct Symbol<'a> {
    #[serde(borrow)]
    symbol: &'a str,
    kind: u32,
}
#[derive(Deserialize)]
struct Occurrence<'a> {
    #[serde(borrow)]
    symbol: &'a str,
    role: u32,
}
#[derive(Serialize)]
struct Inventory<'a> {
    bytes: u64,
    path: &'a str,
    sha256: &'a str,
}
struct FileEntry {
    relative: String,
    path: PathBuf,
    hash: String,
    bytes: u64,
}

pub fn hash_hex(h: Hash) -> String {
    h.iter().map(|b| format!("{b:02x}")).collect()
}
pub fn parse_hash(s: &str) -> Result<Hash, Error> {
    if s.len() != 64
        || !s
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err(Error::Invalid("noncanonical SHA256"));
    }
    let mut h = [0; 32];
    for i in 0..32 {
        h[i] = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).unwrap()
    }
    Ok(h)
}
fn digest(bytes: &[u8]) -> Hash {
    Sha256::digest(bytes).into()
}
fn no_symlink(path: &Path) -> Result<(), Error> {
    // Physical tool locations can have platform symlink ancestors (/var or
    // Homebrew opt). The named file/root itself and every inventory descendant
    // must be regular; SHA256, not path spelling, binds the opened bytes.
    if fs::symlink_metadata(path)?.file_type().is_symlink() {
        return Err(Error::Invalid("symlink authority path"));
    }
    Ok(())
}

fn read_file(path: &Path, max: u64) -> Result<Vec<u8>, Error> {
    no_symlink(path)?;
    let f = File::open(path)?;
    let m = f.metadata()?;
    if !m.is_file() || m.len() > max {
        return Err(Error::Limit("input file bound"));
    }
    let mut bytes = Vec::with_capacity(m.len() as usize);
    f.take(max + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 != m.len() || bytes.len() as u64 > max {
        return Err(Error::Invalid("input changed while reading"));
    }
    Ok(bytes)
}
fn pin_bytes(pin: &Pin, max: u64) -> Result<Vec<u8>, Error> {
    let bytes = read_file(&pin.path, max)?;
    if bytes.len() as u64 != pin.bytes || digest(&bytes) != parse_hash(&pin.sha256)? {
        return Err(Error::Invalid("physical pin mismatch"));
    }
    Ok(bytes)
}
fn verify_pin(pin: &Pin) -> Result<(), Error> {
    no_symlink(&pin.path)?;
    let mut f = File::open(&pin.path)?;
    if f.metadata()?.len() != pin.bytes {
        return Err(Error::Invalid("pin size"));
    }
    let mut hash = Sha256::new();
    let mut buffer = [0; 65536];
    let mut count = 0u64;
    loop {
        let n = f.read(&mut buffer)?;
        if n == 0 {
            break;
        }
        count = count
            .checked_add(n as u64)
            .ok_or(Error::Limit("pin overflow"))?;
        if count > pin.bytes {
            return Err(Error::Invalid("pin grew"));
        }
        hash.update(&buffer[..n]);
    }
    if count != pin.bytes || Hash::from(hash.finalize()) != parse_hash(&pin.sha256)? {
        return Err(Error::Invalid("physical pin mismatch"));
    }
    Ok(())
}
fn decompressed(bytes: Vec<u8>, gz: bool, max: u64) -> Result<Vec<u8>, Error> {
    if !gz {
        return Ok(bytes);
    }
    let mut out = Vec::new();
    MultiGzDecoder::new(bytes.as_slice())
        .take(max + 1)
        .read_to_end(&mut out)?;
    if out.len() as u64 > max {
        return Err(Error::Limit("decompressed bound"));
    }
    Ok(out)
}
fn relative(s: &str) -> Result<&str, Error> {
    if s.is_empty()
        || s.contains('\\')
        || !s.is_ascii()
        || Path::new(s)
            .components()
            .any(|c| !matches!(c, Component::Normal(_)))
    {
        return Err(Error::Invalid("noncanonical relative path"));
    }
    Ok(s)
}
fn virtual_path(base: &Path, s: &str) -> Result<PathBuf, Error> {
    let rel = s
        .strip_prefix("${BASE}/")
        .ok_or(Error::Invalid("unbound virtual path"))?;
    Ok(base.join(relative(rel)?))
}
fn path_source_name(path: &str) -> Option<&str> {
    Path::new(path).file_name()?.to_str()
}
fn stamp(a: &Stamp, b: &Stamp) -> Result<(), Error> {
    let h = a
        .hash
        .as_deref()
        .ok_or(Error::Invalid("noncontent stamp"))?;
    if a.class != "sbt.internal.inc.FarmHash"
        || b.class != a.class
        || a.modified.is_some()
        || b.modified.is_some()
        || h.is_empty()
        || h.len() > 16
        || !h
            .bytes()
            .all(|c| c.is_ascii_hexdigit() && !c.is_ascii_uppercase())
        || a.written != format!("farm({h})")
        || b.hash != a.hash
        || b.written != a.written
    {
        return Err(Error::Invalid("content stamp mismatch"));
    }
    Ok(())
}
fn inventory(root: &Path, limits: &Limits) -> Result<Vec<FileEntry>, Error> {
    no_symlink(root)?;
    let mut pending = vec![root.to_owned()];
    let mut result = Vec::new();
    let mut total_bytes = 0u64;
    while let Some(dir) = pending.pop() {
        for e in fs::read_dir(dir)? {
            let e = e?;
            let meta = e.file_type()?;
            if meta.is_symlink() {
                return Err(Error::Invalid("symlink product"));
            }
            let p = e.path();
            if meta.is_dir() {
                pending.push(p)
            } else if meta.is_file() {
                if result.len() >= limits.max_files {
                    return Err(Error::Limit("directory files"));
                }
                let rel = p
                    .strip_prefix(root)
                    .map_err(|_| Error::Invalid("product outside directory"))?
                    .to_str()
                    .ok_or(Error::Invalid("product path UTF8"))?
                    .to_owned();
                relative(&rel)?;
                let size = e.metadata()?.len();
                total_bytes = total_bytes
                    .checked_add(size)
                    .ok_or(Error::Limit("inventory byte overflow"))?;
                if total_bytes > limits.max_inventory_bytes {
                    return Err(Error::Limit("directory byte budget"));
                }
                let mut sha = Sha256::new();
                let mut f = File::open(&p)?;
                let n = std::io::copy(&mut f, &mut HashWriter(&mut sha))?;
                if n != size {
                    return Err(Error::Invalid("product changed while hashing"));
                }
                result.push(FileEntry {
                    relative: rel,
                    path: p,
                    hash: hash_hex(sha.finalize().into()),
                    bytes: size,
                });
            } else {
                return Err(Error::Invalid("nonregular product"));
            }
        }
    }
    result.sort_by(|a, b| a.relative.cmp(&b.relative));
    Ok(result)
}
struct HashWriter<'a>(&'a mut Sha256);
impl std::io::Write for HashWriter<'_> {
    fn write(&mut self, b: &[u8]) -> std::io::Result<usize> {
        self.0.update(b);
        Ok(b.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}
fn inventory_hash(files: &[FileEntry]) -> Result<Hash, Error> {
    let records: Vec<_> = files
        .iter()
        .map(|f| Inventory {
            bytes: f.bytes,
            path: &f.relative,
            sha256: &f.hash,
        })
        .collect();
    Ok(digest(&serde_json::to_vec(&records)?))
}
fn lines<R: BufRead>(
    mut reader: R,
    max: usize,
    mut f: impl FnMut(&str) -> Result<(), Error>,
) -> Result<(), Error> {
    let mut line = String::new();
    loop {
        line.clear();
        let n = reader.by_ref().take(max as u64 + 1).read_line(&mut line)?;
        if n == 0 {
            break;
        }
        if n > max {
            return Err(Error::Limit("JSONL line"));
        }
        if !line.ends_with('\n') {
            return Err(Error::Invalid("unterminated JSONL"));
        }
        f(&line)?;
    }
    Ok(())
}
fn reader_proof(
    input: &ContextInput,
    base: &Path,
    limits: &Limits,
    verified: &mut HashMap<PathBuf, (String, u64)>,
) -> Result<(), Error> {
    let bytes = pin_bytes(&input.reader_receipt, limits.max_manifest_bytes)?;
    let receipt: Receipt = serde_json::from_slice(&bytes)?;
    if !receipt.all_inputs_unchanged {
        return Err(Error::Invalid("reader input mutation"));
    }
    let analysis = receipt.inputs.iter().any(|p| {
        p.path == input.analysis.path
            && p.sha256 == input.analysis.sha256
            && p.bytes == input.analysis.bytes
    });
    if !analysis {
        return Err(Error::Invalid("reader omitted analysis pin"));
    }
    for p in &receipt.inputs {
        verify_once(p, verified)?
    }
    let mut matches = 0;
    for c in receipt.commands {
        if c.case.starts_with("read")
            && c.exit_code == 0
            && c.stdout == input.reader_output.path
            && c.stdout_bytes == input.reader_output.bytes
            && c.command.len() >= 3
            && c.command[c.command.len() - 3] == "ReadZinc"
            && fs::canonicalize(&c.command[c.command.len() - 2])?
                == fs::canonicalize(&input.analysis.path)?
            && fs::canonicalize(&c.command[c.command.len() - 1])? == fs::canonicalize(base)?
        {
            matches += 1
        }
    }
    if matches != 1 {
        return Err(Error::Invalid("reader command provenance"));
    }
    Ok(())
}
fn compile_success(bytes: &[u8]) -> Result<(), Error> {
    let v: serde_json::Value = serde_json::from_slice(bytes)?;
    if v.get("exit_code").and_then(|v| v.as_i64()) == Some(0) {
        return Ok(());
    }
    if v.get("commands")
        .and_then(|v| v.as_array())
        .is_some_and(|a| {
            a.iter().any(|r| {
                r.get("exit_code").and_then(|v| v.as_i64()) == Some(0) && r.get("command").is_some()
            })
        })
    {
        return Ok(());
    }
    Err(Error::Invalid("compile receipt is not successful"))
}

fn verify_once(p: &Pin, verified: &mut HashMap<PathBuf, (String, u64)>) -> Result<(), Error> {
    let key = fs::canonicalize(&p.path)?;
    if let Some((hash, size)) = verified.get(&key) {
        if hash != &p.sha256 || *size != p.bytes {
            return Err(Error::Invalid("one path conflicting pins"));
        }
        return Ok(());
    }
    verify_pin(p)?;
    verified.insert(key, (p.sha256.clone(), p.bytes));
    Ok(())
}

pub fn admit(
    manifest_path: &Path,
    expected: &Expectations,
    limits: &Limits,
) -> Result<VerifiedBinding, Error> {
    let bytes = read_file(manifest_path, limits.max_manifest_bytes)?;
    if digest(&bytes) != expected.manifest {
        return Err(Error::Invalid("manifest pin mismatch"));
    }
    let m: Manifest = serde_json::from_slice(&bytes)?;
    if m.schema != "retained-zinc-source-products/v1"
        || m.qualification != "new_retained_analysis_correspondence"
        || parse_hash(&m.producer_sha256)? != expected.producer
    {
        return Err(Error::Invalid("producer or schema authority"));
    }
    if parse_hash(&m.contexts.sha256)? != expected.contexts
        || parse_hash(&m.documents.sha256)? != expected.documents
        || parse_hash(&m.compile_receipt.sha256)? != expected.compile_receipt
    {
        return Err(Error::Invalid("external authority pin mismatch"));
    }
    let mut verified = HashMap::new();
    let mut producer = Sha256::new();
    producer.update(b"retained-zinc-source-products-producer/v1\0");
    if m.producer_inputs.is_empty() {
        return Err(Error::Invalid("empty producer authority"));
    }
    for p in &m.producer_inputs {
        verify_once(p, &mut verified)?;
        let path = p.path.to_str().ok_or(Error::Invalid("producer path"))?;
        producer.update((path.len() as u64).to_le_bytes());
        producer.update(path.as_bytes());
        producer.update(parse_hash(&p.sha256)?);
        producer.update(p.bytes.to_le_bytes());
    }
    if Hash::from(producer.finalize()) != expected.producer {
        return Err(Error::Invalid("producer inputs identity"));
    }
    compile_success(&pin_bytes(&m.compile_receipt, limits.max_manifest_bytes)?)?;
    let context_bytes = pin_bytes(&m.contexts, limits.max_json_bytes)?;
    let context_bytes = decompressed(
        context_bytes,
        m.contexts.path.extension().is_some_and(|s| s == "gz"),
        limits.max_json_bytes,
    )?;
    let contexts: Contexts = serde_json::from_slice(&context_bytes)?;
    no_symlink(&contexts.source_root)?;
    let mut budget = Budget {
        used: 0,
        max: limits.max_owned_bytes,
    };
    let mut out = VerifiedBinding {
        identity: expected.manifest,
        contexts: expected.contexts,
        documents: expected.documents,
        texts: Texts::default(),
        sources: Vec::new(),
        classes: Vec::new(),
        methods: Vec::new(),
        owned_bytes: 0,
    };
    let mut contexts_seen = HashSet::new();
    let mut byte_owners: HashMap<Hash, Arc<[u8]>> = HashMap::new();
    let mut selected: HashMap<String, HashMap<String, usize>> = HashMap::new();
    for input in &m.inputs {
        if !contexts_seen.insert(input.context.as_str()) {
            return Err(Error::Invalid("duplicate context request"));
        }
        let mut candidates = contexts
            .contexts
            .iter()
            .filter(|c| c.context_id == input.context);
        let c = candidates
            .next()
            .ok_or(Error::Invalid("uncaptured context"))?;
        if candidates.next().is_some() {
            return Err(Error::Invalid("ambiguous captured context"));
        }
        let mut objects = contexts
            .input_objects
            .iter()
            .filter(|o| o.path == c.class_directory);
        let object = objects
            .next()
            .filter(|o| o.kind == "directory")
            .ok_or(Error::Invalid("missing captured product directory"))?;
        if objects.next().is_some() {
            return Err(Error::Invalid("ambiguous captured product object"));
        }
        if object.bytes.is_none_or(|n| n > limits.max_inventory_bytes) {
            return Err(Error::Limit("captured directory byte budget"));
        }
        let first = c
            .full_classpath
            .first()
            .ok_or(Error::Invalid("empty classpath"))?;
        if first.index != 0
            || first.path != c.class_directory
            || first.input_object != object.path
            || Some(first.sha256.as_str()) != object.sha256.as_deref()
        {
            return Err(Error::Invalid("own product is not first provider"));
        }
        verify_pin(&input.analysis)?;
        verify_pin(&input.reader_output)?;
        reader_proof(input, &contexts.source_root, limits, &mut verified)?;
        let files = inventory(&c.class_directory, limits)?;
        if Some(files.len() as u64) != object.files
            || Some(files.iter().map(|f| f.bytes).sum::<u64>()) != object.bytes
            || inventory_hash(&files)?
                != parse_hash(
                    object
                        .sha256
                        .as_deref()
                        .ok_or(Error::Invalid("captured directory hash missing"))?,
                )?
        {
            return Err(Error::Invalid("captured directory inventory mismatch"));
        }
        let mut products: HashMap<PathBuf, &FileEntry> = files
            .iter()
            .filter(|f| f.relative.ends_with(".class"))
            .map(|f| (f.path.clone(), f))
            .collect();
        selected.insert(input.context.clone(), HashMap::new());
        let mut captured = BTreeMap::new();
        for s in &c.source_records {
            relative(&s.repo_relative_path)?;
            if s.path != contexts.source_root.join(&s.repo_relative_path)
                || captured.insert(s.path.clone(), s).is_some()
            {
                return Err(Error::Invalid("captured source identity"));
            }
        }
        let mut rows = BTreeMap::new();
        lines(
            BufReader::new(File::open(&input.reader_output.path)?),
            limits.max_line_bytes,
            |line| {
                let row: ZincRow = serde_json::from_str(line)?;
                let path = virtual_path(&contexts.source_root, &row.source)?;
                if rows.insert(path, row).is_some() {
                    return Err(Error::Invalid("duplicate Zinc source"));
                }
                Ok(())
            },
        )?;
        if rows.len() != captured.len() || rows.keys().ne(captured.keys()) {
            return Err(Error::Invalid("incomplete source product relation"));
        }
        for (path, row) in rows {
            if out.sources.len() >= limits.max_sources {
                return Err(Error::Limit("source count"));
            }
            let src = captured[&path];
            let source_bytes = read_file(&path, limits.max_line_bytes as u64)?;
            if source_bytes.len() as u64 != row.source_bytes
                || digest(&source_bytes) != parse_hash(&src.sha256)?
                || row.source_sha256 != src.sha256
            {
                return Err(Error::Invalid("stale source bytes"));
            }
            stamp(&row.source_stamp, &row.recomputed_source_farmhash)?;
            budget.charge(160)?;
            let source = SourceId(out.sources.len() as u32);
            let class_start = out.classes.len();
            let method_start = out.methods.len();
            let context = out.texts.intern(&input.context, &mut budget)?;
            let source_path = out.texts.intern(&src.repo_relative_path, &mut budget)?;
            let mut ps = row.products;
            ps.sort_by(|a, b| a.path.cmp(&b.path));
            for p in ps {
                if out.classes.len() >= limits.max_classes {
                    return Err(Error::Limit("class count"));
                }
                let path = virtual_path(&contexts.source_root, &p.path)?;
                let f = products.remove(&path).ok_or(Error::Invalid(
                    "unowned duplicate or uncaptured class product",
                ))?;
                if p.bytes != f.bytes || p.sha256 != f.hash {
                    return Err(Error::Invalid("stale product bytes"));
                }
                stamp(&p.stamp, &p.recomputed_content_hash)?;
                let hash = parse_hash(&p.sha256)?;
                let owned = if let Some(bytes) = byte_owners.get(&hash) {
                    bytes.clone()
                } else {
                    budget.charge(p.bytes + 64)?;
                    let bytes: Arc<[u8]> = pin_bytes(
                        &Pin {
                            path: path.clone(),
                            sha256: p.sha256,
                            bytes: p.bytes,
                        },
                        limits.max_class_bytes,
                    )?
                    .into();
                    byte_owners.insert(hash, bytes.clone());
                    bytes
                };
                let header = classfile::parse(&owned)?;
                if header
                    .source_file
                    .as_deref()
                    .is_some_and(|name| path_source_name(&src.repo_relative_path) != Some(name))
                {
                    return Err(Error::Invalid("class SourceFile/source owner mismatch"));
                }
                if format!("{}.class", header.owner) != f.relative {
                    return Err(Error::Invalid("class owner/path mismatch"));
                }
                let id = ClassId(out.classes.len() as u32);
                let start = out.methods.len();
                let owner = out.texts.intern(&header.owner, &mut budget)?;
                budget.charge(128)?;
                for method in header.methods {
                    if out.methods.len() >= limits.max_methods {
                        return Err(Error::Limit("method count"));
                    }
                    budget.charge(32)?;
                    out.methods.push(MethodRow {
                        class: id,
                        name: out.texts.intern(&method.name, &mut budget)?,
                        descriptor: out.texts.intern(&method.descriptor, &mut budget)?,
                        flags: method.flags,
                        has_code: method.has_code,
                    });
                }
                out.classes.push(ClassRow {
                    source,
                    owner,
                    hash,
                    flags: header.flags,
                    module_field: header.module_field,
                    methods: start..out.methods.len(),
                    bytes: owned,
                });
            }
            selected
                .get_mut(&input.context)
                .expect("selected context initialized")
                .insert(src.repo_relative_path.clone(), source.0 as usize);
            out.sources.push(SourceRow {
                context,
                path: source_path,
                hash: parse_hash(&src.sha256)?,
                semantic: false,
                classes: class_start..out.classes.len(),
                methods: method_start..out.methods.len(),
                definitions: Vec::new(),
            });
        }
        if !products.is_empty() {
            return Err(Error::Invalid("class file without unique Zinc source"));
        }
    }
    drop(contexts);
    drop(context_bytes);
    // Stream the original capture once; no JSON tree or full source copies survive a row.
    verify_pin(&m.documents)?;
    let file = File::open(&m.documents.path)?;
    let read: Box<dyn Read> = if m.documents.path.extension().is_some_and(|e| e == "gz") {
        Box::new(MultiGzDecoder::new(file))
    } else {
        Box::new(file)
    };
    let mut docs_seen = HashSet::new();
    let mut read = read.take(limits.max_document_bytes + 1);
    lines(BufReader::new(&mut read), limits.max_line_bytes, |line| {
        let doc: Doc<'_> = serde_json::from_str(line)?;
        for context in &doc.source_contexts {
            let Some(&index) = selected.get(*context).and_then(|paths| paths.get(doc.path)) else {
                continue;
            };
            let s = &out.sources[index];
            if parse_hash(doc.source_sha256)? != s.hash {
                return Err(Error::Invalid("SemanticDB source hash mismatch"));
            }
            let text: String = serde_json::from_str(
                doc.source_text
                    .ok_or(Error::Invalid("missing SemanticDB source text"))?
                    .get(),
            )?;
            if digest(text.as_bytes()) != s.hash {
                return Err(Error::Invalid("SemanticDB embedded source mismatch"));
            }
            let definitions: Definitions<'_> = serde_json::from_str(doc.document.get())?;
            let roles: HashSet<&str> = definitions
                .occurrences
                .iter()
                .filter(|o| o.role == 2)
                .map(|o| o.symbol)
                .collect();
            let mut names = Vec::new();
            for d in definitions.symbols {
                if matches!(d.kind, 10 | 13) && roles.contains(d.symbol) {
                    budget.charge(16)?;
                    names.push((out.texts.intern(d.symbol, &mut budget)?, d.kind));
                }
            }
            names.sort_unstable();
            names.dedup();
            if !docs_seen.insert(index) {
                return Err(Error::Invalid("duplicate SemanticDB source/context"));
            }
            out.sources[index].semantic = true;
            out.sources[index].definitions = names;
        }
        Ok(())
    })?;
    if read.limit() == 0 {
        return Err(Error::Limit("SemanticDB document byte bound"));
    }
    // Recheck mutable physical authority after the read. Retained bytes own class identity.
    verify_pin(&m.contexts)?;
    verify_pin(&m.documents)?;
    for input in &m.inputs {
        verify_pin(&input.analysis)?;
        verify_pin(&input.reader_output)?;
        verify_pin(&input.reader_receipt)?;
    }
    out.owned_bytes = budget.used;
    Ok(out)
}
