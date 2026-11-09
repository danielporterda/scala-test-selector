//! Native, bounded import of captured compiler identities and validated syntax.
//!
//! Decoder objects borrow a bounded batch of JSON lines. Only pooled strings and
//! flat records survive admission. No source spelling is used to resolve targets.
mod buffer;
mod callable;
mod compiler_contexts;
pub mod compiler_inputs;
mod coordinates;
pub mod external_metadata;
mod normalize;
mod prepared_capture;
pub mod raw_capture;
mod result_bounds;
mod semantic;
mod semantic_wire;
mod signature;
mod source_forms;
mod syntax;
mod syntax_tree;
mod synthetics;
pub mod toolchain;

use flate2::read::MultiGzDecoder;
use selector_facts::*;
use selector_types::*;
use serde::Deserialize;
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::fs::File;
use std::io::{BufRead, BufReader, Read};
use std::path::{Path, PathBuf};

pub use coordinates::SourceCoordinates;
pub use prepared_capture::{PreparedCapture, finish_capture, prepare_capture};
pub use result_bounds::project_result_bounds;

/// Producer domain for callers constructing in-memory snapshots. Persisted
/// artifact content digests are authoritative; change this domain when compiler
/// normalization or execution-recipe semantics change incompatibly.
pub const EXTRACTOR_VERSION: &str = "selector-extract/24:curried-compiler-type-prefix-completion";

#[derive(Clone, Debug)]
pub struct ExtractOptions {
    /// Maximum uncompressed compiler + syntax input size.
    pub max_input_bytes: u64,
    /// Maximum one-row size; read limits apply before allocating a complete row.
    pub max_document_bytes: usize,
    /// Bounded decoder batch. A single admitted row may exceed this up to max_document_bytes.
    pub batch_bytes: usize,
    pub workers: usize,
    pub expected_revision: Option<String>,
    pub expected_syntax_producer: Option<ContentHash>,
    pub catalogue: Option<PathBuf>,
    /// Finalized ordered classpath/source-origin manifest; otherwise discover a sibling capture manifest.
    pub compiler_contexts: Option<PathBuf>,
    /// Pre-admitted immutable product inventories; include their identity in cache keys.
    pub compiler_inputs: Option<std::sync::Arc<compiler_inputs::CompilerInputs>>,
}
impl Default for ExtractOptions {
    fn default() -> Self {
        Self {
            max_input_bytes: 2 * 1024 * 1024 * 1024,
            max_document_bytes: 64 * 1024 * 1024,
            batch_bytes: 16 * 1024 * 1024,
            workers: std::thread::available_parallelism().map_or(1, usize::from),
            expected_revision: None,
            expected_syntax_producer: None,
            catalogue: None,
            compiler_contexts: None,
            compiler_inputs: None,
        }
    }
}

pub(crate) fn json_error(error: serde_json::Error) -> Error {
    Error::Message(error.to_string())
}
/// SemanticDB types can exceed serde_json's default 128 levels. Admit a bounded
/// larger depth before disabling that default, so malformed input cannot exhaust
/// a worker stack through unbounded recursive deserialization.
pub(crate) fn from_json<'de, T: Deserialize<'de>>(input: &'de str) -> Result<T, Error> {
    let mut depth = 0usize;
    let mut quoted = false;
    let mut escaped = false;
    for byte in input.bytes() {
        if quoted {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                quoted = false;
            }
        } else {
            match byte {
                b'"' => quoted = true,
                b'{' | b'[' => {
                    depth += 1;
                    if depth > 512 {
                        return Err(Error::Limit("JSON nesting depth"));
                    }
                }
                b'}' | b']' => depth = depth.saturating_sub(1),
                _ => (),
            }
        }
    }
    let mut decoder = serde_json::Deserializer::from_str(input);
    decoder.disable_recursion_limit();
    let value = T::deserialize(&mut decoder).map_err(json_error)?;
    decoder.end().map_err(json_error)?;
    Ok(value)
}
pub(crate) fn sha(bytes: &[u8]) -> ContentHash {
    ContentHash(Sha256::digest(bytes).into())
}

pub(crate) struct Input {
    reader: Box<dyn BufRead>,
    total: u64,
    max_total: u64,
    max_row: usize,
}
impl Input {
    fn open(path: &Path, options: &ExtractOptions, consumed: u64) -> Result<Self, Error> {
        let file = File::open(path)?;
        let reader: Box<dyn Read> = if path.extension().is_some_and(|s| s == "gz") {
            Box::new(MultiGzDecoder::new(file))
        } else {
            Box::new(file)
        };
        Ok(Self {
            reader: Box::new(BufReader::with_capacity(256 * 1024, reader)),
            total: consumed,
            max_total: options.max_input_bytes,
            max_row: options.max_document_bytes,
        })
    }
    /// Bounds memory even for a malformed JSON line without a terminating newline.
    fn line(&mut self) -> Result<Option<Vec<u8>>, Error> {
        let mut out = Vec::new();
        loop {
            let part = self.reader.fill_buf()?;
            if part.is_empty() {
                return Ok((!out.is_empty()).then_some(out));
            }
            let n = part
                .iter()
                .position(|&b| b == b'\n')
                .map_or(part.len(), |n| n + 1);
            if out.len().checked_add(n).is_none_or(|n| n > self.max_row) {
                return Err(Error::Limit("document bytes"));
            }
            self.total = self
                .total
                .checked_add(n as u64)
                .ok_or(Error::Limit("input bytes"))?;
            if self.total > self.max_total {
                return Err(Error::Limit("input bytes"));
            }
            let done = part[n - 1] == b'\n';
            out.extend_from_slice(&part[..n]);
            self.reader.consume(n);
            if done {
                return Ok(Some(out));
            }
        }
    }
    fn batch(&mut self, bytes: usize) -> Result<Vec<Vec<u8>>, Error> {
        let mut rows = Vec::new();
        let mut used = 0;
        while used < bytes.max(1) || rows.is_empty() {
            let Some(row) = self.line()? else { break };
            used += row.len();
            if row.iter().any(|b| !b.is_ascii_whitespace()) {
                rows.push(row);
            }
        }
        Ok(rows)
    }
}

/// Imports the actual `export_documents.py` capture format, optionally joining
/// Scalameta JSONL `{path,source_sha256,producer_sha256,ast}` rows.
///
/// Mixed revisions and invalid JSON are rejected. Missing/stale source or syntax
/// remains explicit conservative evidence, never a name-based substitute graph.
pub fn import_capture(
    path: &Path,
    syntax: Option<&Path>,
    options: &ExtractOptions,
) -> Result<FactSnapshot, Error> {
    finish_capture(prepare_capture(path, syntax, options)?, None)
}

/// Attach captured CI names through exact compiler discovery bindings. A class
/// and its companion module are different runnable identities, even when their
/// display class names coincide.
pub fn attach_catalogue(builder: &mut FactBuilder, path: &Path) -> Result<(), Error> {
    let catalogue = read_catalogue(path)?;
    if !catalogue.complete {
        builder.issue(
            IssueKind::InvalidInput,
            FileId::NONE,
            SymbolId::NONE,
            "suite catalogue is incomplete",
        )?;
    }
    let bindings = catalogue_bindings(&builder.facts, &catalogue)?;
    for binding in bindings {
        let pooled = builder.intern(&binding.name)?;
        if let Some((kind, reason)) = binding.unknown {
            builder.facts.suites.push(SuiteRecord {
                name: pooled,
                symbol: SymbolId::NONE,
                file: FileId::NONE,
                flags: EDGE_UNKNOWN,
            });
            let detail = format!("catalogue suite {}: {reason}", binding.name);
            if binding.candidates.is_empty() {
                builder.issue(kind, FileId::NONE, SymbolId::NONE, &detail)?;
            } else {
                // The name's exact admitted declarations scope ambiguity; none
                // becomes a runnable root without discovery authority.
                for symbol in binding.candidates {
                    let file = builder.facts.symbols[symbol.index()].file;
                    builder.issue(kind, file, symbol, &detail)?;
                }
            }
        } else {
            for symbol in binding.selected {
                let file = builder.facts.symbols[symbol.index()].file;
                builder.facts.suites.push(SuiteRecord {
                    name: pooled,
                    symbol,
                    file,
                    flags: 0,
                });
            }
        }
    }
    Ok(())
}

#[derive(Deserialize)]
struct CatalogueFamily {
    #[serde(default)]
    suites: Vec<String>,
}
#[derive(Deserialize)]
struct SuiteCatalogue {
    #[serde(default)]
    complete: bool,
    #[serde(default)]
    families: Vec<CatalogueFamily>,
    #[serde(default)]
    suite_names: Vec<String>,
    // Raw records keep unsupported discovery payloads local to their known name
    // instead of either allocating a JSON DOM or dropping the catalogue entry.
    #[serde(default)]
    suites: Vec<Box<serde_json::value::RawValue>>,
}
#[derive(Deserialize)]
struct CapturedSuite<'a> {
    suite: String,
    #[serde(default, borrow)]
    compiler_discovery: Option<&'a serde_json::value::RawValue>,
    #[serde(default, borrow)]
    owning_context_ids: Option<&'a serde_json::value::RawValue>,
}
#[derive(Deserialize)]
struct CapturedDiscovery {
    #[serde(default)]
    context_id: Option<String>,
    #[serde(default)]
    fingerprint: Option<DiscoveryFingerprint>,
}
#[derive(Deserialize)]
struct DiscoveryFingerprint {
    #[serde(default, rename = "type")]
    kind: Option<String>,
    #[serde(default)]
    superclass: Option<String>,
    #[serde(default)]
    is_module: Option<bool>,
    #[serde(default)]
    require_no_arg_constructor: Option<bool>,
}
#[derive(PartialEq, Eq, PartialOrd, Ord)]
struct DiscoveryBinding {
    context: String,
    is_module: bool,
    require_no_arg_constructor: bool,
}
struct CatalogueEntry {
    name: String,
    rich: bool,
    discovery: Vec<DiscoveryBinding>,
    unknown: Option<(IssueKind, &'static str)>,
}
struct CatalogueBinding {
    name: String,
    selected: Vec<SymbolId>,
    candidates: Vec<SymbolId>,
    unknown: Option<(IssueKind, &'static str)>,
}

fn read_catalogue(path: &Path) -> Result<SuiteCatalogue, Error> {
    let file = File::open(path)?;
    const MAX: u64 = 64 * 1024 * 1024;
    if file.metadata()?.len() > MAX {
        return Err(Error::Limit("catalogue bytes"));
    }
    let mut input = String::new();
    file.take(MAX + 1).read_to_string(&mut input)?;
    if input.len() as u64 > MAX {
        return Err(Error::Limit("catalogue bytes"));
    }
    from_json(&input)
}

fn discovery_bindings(
    record: &CapturedSuite<'_>,
) -> Result<Vec<DiscoveryBinding>, (IssueKind, &'static str)> {
    let invalid = (
        IssueKind::InvalidInput,
        "compiler discovery metadata is missing or malformed",
    );
    let raw = record.compiler_discovery.ok_or(invalid)?;
    let discoveries: Vec<CapturedDiscovery> = from_json(raw.get()).map_err(|_| invalid)?;
    if discoveries.is_empty() {
        return Err(invalid);
    }
    let mut bindings = Vec::with_capacity(discoveries.len());
    for discovery in discoveries {
        let context = discovery
            .context_id
            .filter(|context| !context.is_empty())
            .ok_or(invalid)?;
        let fingerprint = discovery.fingerprint.ok_or(invalid)?;
        let is_module = fingerprint.is_module.ok_or(invalid)?;
        let require_no_arg_constructor = fingerprint.require_no_arg_constructor.ok_or(invalid)?;
        if fingerprint.kind.as_deref() != Some("subclass")
            || fingerprint.superclass.as_deref() != Some("org.scalatest.Suite")
        {
            return Err((
                IssueKind::UnsupportedSchema,
                "unsupported compiler discovery fingerprint",
            ));
        }
        bindings.push(DiscoveryBinding {
            context,
            is_module,
            require_no_arg_constructor,
        });
    }
    bindings.sort_unstable();
    bindings.dedup();
    if let Some(raw) = record.owning_context_ids {
        let mut owners: Vec<String> = from_json(raw.get()).map_err(|_| invalid)?;
        owners.sort_unstable();
        owners.dedup();
        let mut discovered: Vec<_> = bindings
            .iter()
            .map(|binding| binding.context.as_str())
            .collect();
        discovered.dedup();
        if owners.iter().map(String::as_str).ne(discovered) {
            return Err((
                IssueKind::ContextConflict,
                "owning contexts contradict compiler discovery contexts",
            ));
        }
    }
    Ok(bindings)
}

fn catalogue_bindings(
    facts: &FactSnapshot,
    catalogue: &SuiteCatalogue,
) -> Result<Vec<CatalogueBinding>, Error> {
    let mut entries = Vec::<CatalogueEntry>::new();
    let mut names = HashMap::<String, usize>::new();
    fn entry<'a>(
        name: &str,
        entries: &'a mut Vec<CatalogueEntry>,
        names: &mut HashMap<String, usize>,
    ) -> &'a mut CatalogueEntry {
        let index = *names.entry(name.to_owned()).or_insert_with(|| {
            let index = entries.len();
            entries.push(CatalogueEntry {
                name: name.to_owned(),
                rich: false,
                discovery: Vec::new(),
                unknown: None,
            });
            index
        });
        &mut entries[index]
    }
    for name in catalogue
        .families
        .iter()
        .flat_map(|family| &family.suites)
        .chain(&catalogue.suite_names)
    {
        entry(name, &mut entries, &mut names);
    }
    let mut rich_catalogue = false;
    for raw in &catalogue.suites {
        if raw.get().trim_start().starts_with('"') {
            let name: String = from_json(raw.get())?;
            entry(&name, &mut entries, &mut names);
            continue;
        }
        rich_catalogue = true;
        let record: CapturedSuite<'_> = from_json(raw.get())?;
        let target = entry(&record.suite, &mut entries, &mut names);
        target.rich = true;
        match discovery_bindings(&record) {
            Ok(bindings) => target.discovery.extend(bindings),
            Err(unknown) => target.unknown = Some(unknown),
        }
    }
    let mut candidates = vec![Vec::<SymbolId>::new(); entries.len()];
    let mut class_name = String::new();
    for (index, symbol) in facts.symbols.iter().enumerate() {
        if symbol.flags & SYMBOL_DEFINED == 0 || !matches!(symbol.kind, 10 | 13 | 14) {
            continue;
        }
        compiler_class_name(facts.text(symbol.name), &mut class_name);
        if let Some(index_in_catalogue) = names.get(&class_name) {
            candidates[*index_in_catalogue].push(SymbolId(index as u32));
        }
    }
    let mut result = Vec::with_capacity(entries.len());
    for (mut entry, candidates) in entries.into_iter().zip(candidates) {
        let mut selected = Vec::new();
        if rich_catalogue && !entry.rich {
            entry.unknown = Some((
                IssueKind::InvalidInput,
                "rich catalogue entry has no compiler discovery record",
            ));
        }
        if entry.unknown.is_none() && entry.rich {
            entry.discovery.sort_unstable();
            entry.discovery.dedup();
            for binding in entry.discovery {
                let mut matches = candidates.iter().copied().filter(|id| {
                    let symbol = &facts.symbols[id.index()];
                    !symbol.context.is_none()
                        && facts.text(symbol.context) == binding.context
                        && if binding.is_module {
                            symbol.kind == 10
                        } else {
                            matches!(symbol.kind, 13 | 14)
                        }
                });
                match (matches.next(), matches.next()) {
                    (Some(symbol), None) => selected.push(symbol),
                    (None, _) => {
                        entry.unknown = Some((
                            IssueKind::UnresolvedSymbol,
                            "compiler discovery has no exact admitted context and class/module identity",
                        ));
                        break;
                    }
                    _ => {
                        entry.unknown = Some((
                            IssueKind::ContextConflict,
                            "compiler discovery matches ambiguous compiler identities",
                        ));
                        break;
                    }
                }
            }
        } else if entry.unknown.is_none() {
            match candidates.as_slice() {
                [symbol] => selected.push(*symbol),
                [] => {
                    entry.unknown =
                        Some((IssueKind::UnresolvedSymbol, "no admitted compiler identity"))
                }
                _ => {
                    entry.unknown = Some((
                        IssueKind::ContextConflict,
                        "legacy catalogue name matches ambiguous class/module or compiler contexts",
                    ))
                }
            }
        }
        selected.sort_unstable();
        selected.dedup();
        if entry.unknown.is_some() {
            selected.clear();
        }
        result.push(CatalogueBinding {
            name: entry.name,
            selected,
            candidates,
            unknown: entry.unknown,
        });
    }
    Ok(result)
}

/// Reuse one projection buffer for the compiler type inventory. The captured
/// discovery context and class/module fingerprint resolve display-name collisions.
fn compiler_class_name(symbol: &str, out: &mut String) {
    out.clear();
    for character in symbol.trim_end_matches(['#', '.']).chars() {
        match character {
            '/' | '#' => out.push('.'),
            '`' => (),
            character => out.push(character),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use md5::{Digest as Md5Digest, Md5};
    use serde_json::{Value, json};
    fn input(source: &str, path: &str, context: &str) -> Value {
        let digest = Md5::digest(source.as_bytes());
        let md5 = digest
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>();
        json!({"path":path,"revision":"r1","source_text":source,"source_sha256":sha(source.as_bytes()).to_string(),
            "source_contexts":[context],"input_target_contexts":[context],
            "document":{"schema":4,"language":1,"uri":path,"md5":md5,"symbols":[],"occurrences":[]}})
    }
    fn run(
        rows: &[Value],
        syntax: Option<Value>,
        options: &ExtractOptions,
    ) -> Result<FactSnapshot, Error> {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("documents.jsonl");
        std::fs::write(
            &path,
            rows.iter().map(|r| format!("{r}\n")).collect::<String>(),
        )
        .unwrap();
        let syntax_path = syntax.map(|s| {
            let path = dir.path().join("syntax.jsonl");
            std::fs::write(&path, format!("{s}\n")).unwrap();
            path
        });
        import_capture(&path, syntax_path.as_deref(), options)
    }
    fn catalogue_builder(declarations: &[(&str, &str, u32)]) -> FactBuilder {
        let mut builder = FactBuilder::new();
        let mut files = HashMap::new();
        for &(name, context, kind) in declarations {
            let file = if let Some(file) = files.get(context) {
                *file
            } else {
                let path = builder.intern(&format!("{context}.scala")).unwrap();
                let context_id = builder.intern(context).unwrap();
                let source = builder.intern("").unwrap();
                let file = FileId(builder.facts.files.len() as u32);
                builder.facts.files.push(FileRecord {
                    path,
                    source,
                    context: context_id,
                    revision: StrId::NONE,
                    source_hash: sha(b""),
                    flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
                });
                files.insert(context, file);
                file
            };
            let symbol = builder.ensure_symbol(name, file).unwrap();
            let record = &mut builder.facts.symbols[symbol.index()];
            record.kind = kind;
            record.file = file;
            record.flags = SYMBOL_DEFINED;
        }
        builder
    }
    fn discovery(context: &str, is_module: bool) -> Value {
        json!({"context_id":context,"fingerprint":{"type":"subclass","superclass":"org.scalatest.Suite",
            "is_module":is_module,"require_no_arg_constructor":true}})
    }
    fn attach(builder: &mut FactBuilder, catalogue: &Value) {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("catalogue.json");
        std::fs::write(&path, serde_json::to_vec(catalogue).unwrap()).unwrap();
        attach_catalogue(builder, &path).unwrap();
        builder.facts.validate().unwrap();
    }
    #[test]
    fn captured_subclass_fingerprint_does_not_promote_non_suite_companion() {
        // Exact discovery payload from PR7743 CI catalogue sha256
        // d553857a83cb9cfb4417a4b0eed910a3ee8dded329161059c40fce4ab685c510.
        // The genuine companion extends MockitoSugar, not ScalaTest Suite.
        let name = "org.lfdecentralizedtrust.splice.auth.AuthTokenManagerTest";
        let class = "org/lfdecentralizedtrust/splice/auth/AuthTokenManagerTest#";
        let module = "org/lfdecentralizedtrust/splice/auth/AuthTokenManagerTest.";
        let context = "project:apps-common/configuration:test";
        let mut builder = catalogue_builder(&[(class, context, 13), (module, context, 10)]);
        attach(
            &mut builder,
            &json!({"complete":true,"families":[{"suites":[name]}],"suites":[{
            "suite":name,"compiler_discovery":[{"configuration":"test","context_id":context,
                "fingerprint":{"is_module":false,"require_no_arg_constructor":true,
                    "superclass":"org.scalatest.Suite","type":"subclass"},"project_id":"apps-common"}],
            "owning_context_ids":[context]}]}),
        );
        assert_eq!(builder.facts.suites.len(), 1);
        assert_eq!(
            builder.facts.symbol_name(builder.facts.suites[0].symbol),
            class
        );
        assert_eq!(builder.facts.suites[0].flags, 0);
        assert!(builder.facts.issues.is_empty());
    }
    #[test]
    fn module_and_context_fingerprints_preserve_only_recorded_compiler_identities() {
        let mut builder = catalogue_builder(&[
            ("p/Suite#", "a:test", 13),
            ("p/Suite.", "a:test", 10),
            ("p/Suite#", "b:test", 13),
            ("p/Suite.", "b:test", 10),
        ]);
        attach(
            &mut builder,
            &json!({"complete":true,"suites":[{"suite":"p.Suite",
            "compiler_discovery":[discovery("b:test",true)],"owning_context_ids":["b:test"]}]}),
        );
        assert_eq!(builder.facts.suites.len(), 1);
        let symbol = &builder.facts.symbols[builder.facts.suites[0].symbol.index()];
        assert_eq!(symbol.kind, 10);
        assert_eq!(builder.facts.text(symbol.context), "b:test");
        assert!(builder.facts.issues.is_empty());
        let mut multiple = catalogue_builder(&[
            ("p/Suite#", "a:test", 13),
            ("p/Suite.", "a:test", 10),
            ("p/Suite#", "b:test", 13),
            ("p/Suite.", "b:test", 10),
        ]);
        attach(
            &mut multiple,
            &json!({"complete":true,"suites":[{"suite":"p.Suite",
            "compiler_discovery":[discovery("a:test",false),discovery("b:test",true),discovery("a:test",false)],
            "owning_context_ids":["a:test","b:test"]}]}),
        );
        assert_eq!(
            multiple.facts.suites.len(),
            2,
            "every recorded context/module key, without duplicate roots"
        );
        assert_eq!(
            multiple
                .facts
                .suites
                .iter()
                .map(|suite| suite.symbol)
                .collect::<Vec<_>>(),
            vec![SymbolId(0), SymbolId(3)]
        );
    }
    #[test]
    fn incomplete_conflicting_and_unsupported_discovery_stays_one_scoped_unknown() {
        let valid = discovery("a:test", false);
        let controls = vec![
            json!({"suite":"p.Suite"}),
            json!({"suite":"p.Suite","compiler_discovery":[]}),
            json!({"suite":"p.Suite","compiler_discovery":[{"fingerprint":valid["fingerprint"]}]}),
            json!({"suite":"p.Suite","compiler_discovery":[{"context_id":"a:test"}]}),
            json!({"suite":"p.Suite","compiler_discovery":[{"context_id":"a:test","fingerprint":{
                "type":"subclass","superclass":"org.scalatest.Suite","is_module":"false","require_no_arg_constructor":true}}]}),
            json!({"suite":"p.Suite","compiler_discovery":[{"context_id":"a:test","fingerprint":{
                "type":"subclass","superclass":"org.scalatest.Suite","is_module":false}}]}),
            json!({"suite":"p.Suite","compiler_discovery":[{"context_id":"a:test","fingerprint":{
                "type":"annotated","superclass":"org.scalatest.Suite","is_module":false,"require_no_arg_constructor":true}}]}),
            json!({"suite":"p.Suite","compiler_discovery":[{"context_id":"a:test","fingerprint":{
                "type":"subclass","superclass":"p.OtherSuite","is_module":false,"require_no_arg_constructor":true}}]}),
            json!({"suite":"p.Suite","compiler_discovery":[valid],"owning_context_ids":["other:test"]}),
            json!({"suite":"p.Suite","compiler_discovery":[discovery("missing:test",false)]}),
            json!({"suite":"p.Suite","compiler_discovery":[valid,discovery("missing:test",false)]}),
        ];
        for record in controls {
            let mut builder =
                catalogue_builder(&[("p/Suite#", "a:test", 13), ("p/Suite.", "a:test", 10)]);
            attach(
                &mut builder,
                &json!({"complete":true,"families":[{"suites":["p.Suite"]}],"suites":[record]}),
            );
            assert_eq!(builder.facts.suites.len(), 1, "{record}");
            assert!(builder.facts.suites[0].symbol.is_none(), "{record}");
            assert_eq!(builder.facts.text(builder.facts.suites[0].name), "p.Suite");
            assert_eq!(builder.facts.suites[0].flags, EDGE_UNKNOWN);
            assert!(!builder.facts.issues.is_empty());
            assert!(
                builder
                    .facts
                    .issues
                    .iter()
                    .all(|issue| !issue.symbol.is_none() && !issue.file.is_none()),
                "{record}"
            );
        }
        let mut duplicate = catalogue_builder(&[("p/Suite#", "a:test", 13)]);
        attach(
            &mut duplicate,
            &json!({"complete":true,"suites":[{"suite":"p.Suite","compiler_discovery":[discovery("a:test",false)]},
            {"suite":"p.Suite","compiler_discovery":[]}]}),
        );
        assert_eq!(duplicate.facts.suites.len(), 1);
        assert!(
            duplicate.facts.suites[0].symbol.is_none(),
            "a valid duplicate must not hide contradictory incomplete discovery"
        );
    }
    #[test]
    fn legacy_unique_names_remain_supported_and_ambiguity_cannot_forge_two_roots() {
        let mut unique = catalogue_builder(&[("p/Suite#", "a:test", 13)]);
        attach(
            &mut unique,
            &json!({"complete":true,"families":[{"suites":["p.Suite"]}],"suites":["p.Suite"]}),
        );
        assert_eq!(unique.facts.suites.len(), 1);
        assert_eq!(unique.facts.suites[0].symbol, SymbolId(0));
        let mut ambiguous =
            catalogue_builder(&[("p/Suite#", "a:test", 13), ("p/Suite.", "a:test", 10)]);
        attach(
            &mut ambiguous,
            &json!({"complete":true,"families":[{"suites":["p.Suite"]}]}),
        );
        assert_eq!(ambiguous.facts.suites.len(), 1);
        assert!(ambiguous.facts.suites[0].symbol.is_none());
        assert!(
            ambiguous
                .facts
                .issues
                .iter()
                .all(|issue| issue.kind == IssueKind::ContextConflict)
        );
        let mut missing = catalogue_builder(&[("p/Suite#", "a:test", 13)]);
        attach(
            &mut missing,
            &json!({"complete":true,"families":[{"suites":["p.Suite","p.Other"]}],"suites":[{
            "suite":"p.Other","compiler_discovery":[discovery("a:test",false)]}]}),
        );
        assert_eq!(missing.facts.suites.len(), 2);
        assert!(
            missing
                .facts
                .suites
                .iter()
                .all(|suite| suite.symbol.is_none()),
            "a missing rich record cannot downgrade to legacy inference"
        );
    }
    #[test]
    #[ignore = "read-only actual compiler facts/catalogue census; set SELECTOR_DISCOVERY_FACTS and SELECTOR_DISCOVERY_CATALOGUE"]
    fn actual_catalogue_discovery_census() {
        let facts_path = std::env::var("SELECTOR_DISCOVERY_FACTS").unwrap();
        let catalogue_path = std::env::var("SELECTOR_DISCOVERY_CATALOGUE").unwrap();
        let facts = selector_facts::codec::read(Path::new(&facts_path)).unwrap();
        let catalogue = read_catalogue(Path::new(&catalogue_path)).unwrap();
        let bindings = catalogue_bindings(&facts, &catalogue).unwrap();
        let selected = bindings
            .iter()
            .filter(|entry| entry.unknown.is_none())
            .map(|entry| entry.selected.len())
            .sum::<usize>();
        let unknown = bindings
            .iter()
            .filter(|entry| entry.unknown.is_some())
            .count();
        let removed=bindings.iter().flat_map(|entry|entry.candidates.iter().filter(|candidate|!entry.selected.contains(candidate)))
            .map(|symbol|json!({"symbol":facts.symbol_name(*symbol),"context":facts.text(facts.symbols[symbol.index()].context),
                "kind":facts.symbols[symbol.index()].kind})).collect::<Vec<_>>();
        println!(
            "{}",
            json!({"facts":facts_path,"facts_identity":facts.identity.to_string(),"catalogue":catalogue_path,
            "catalogue_sha256":sha(&std::fs::read(&catalogue_path).unwrap()).to_string(),"names":bindings.len(),
            "previous_name_candidates":bindings.iter().map(|entry|entry.candidates.len()).sum::<usize>(),
            "selected_roots":selected,"unknown_names":unknown,"removed_candidates":removed})
        );
        if let Ok(expected) = std::env::var("SELECTOR_DISCOVERY_EXPECTED_ROOTS") {
            assert_eq!(selected, expected.parse::<usize>().unwrap());
            assert_eq!(unknown, 0);
        }
    }
    #[test]
    fn stale_missing_and_unsupported_documents_are_not_admitted() {
        let mut stale = input("object A", "A.scala", "p:compile");
        stale["document"]["md5"] = json!("00000000000000000000000000000000");
        let mut missing = input("object B", "B.scala", "p:compile");
        missing["source_text"] = Value::Null;
        let mut unsupported = input("object C", "C.scala", "p:compile");
        unsupported["document"]["schema"] = json!(5);
        let facts = run(
            &[stale, missing, unsupported],
            None,
            &ExtractOptions::default(),
        )
        .unwrap();
        assert_eq!(facts.files.len(), 3);
        assert!(facts.symbols.is_empty());
        for kind in [
            IssueKind::StaleSource,
            IssueKind::MissingSource,
            IssueKind::UnsupportedSchema,
        ] {
            assert!(facts.issues.iter().any(|i| i.kind == kind));
        }
    }
    #[test]
    fn compiler_locals_and_contexts_keep_separate_identities() {
        let mut a = input("x", "A.scala", "a:compile");
        a["document"]["symbols"] =
            json!([{"symbol":"local0","kind":19},{"symbol":"p/C#f(+2).","kind":3}]);
        let mut b = a.clone();
        b["path"] = json!("B.scala");
        b["document"]["uri"] = json!("B.scala");
        let mut c = a.clone();
        c["source_contexts"] = json!(["b:test"]);
        c["input_target_contexts"] = json!(["b:test"]);
        let facts = run(&[a, b, c], None, &ExtractOptions::default()).unwrap();
        assert_eq!(
            facts
                .symbols
                .iter()
                .filter(|s| facts.text(s.name) == "local0")
                .count(),
            3
        );
        assert_eq!(
            facts
                .symbols
                .iter()
                .filter(|s| facts.text(s.name) == "p/C#f(+2).")
                .count(),
            2
        );
    }
    #[test]
    fn utf16_occurrences_and_parent_types_are_exact() {
        let mut row = input("😀x", "A.scala", "a");
        row["document"]["symbols"] = json!([{"symbol":"p/C#","kind":13,"signature":{"class_signature":{"parents":[{"type_ref":{"symbol":"p/Base#","type_arguments":[{"type_ref":{"symbol":"p/Arg#"}}]}}]}}}]);
        row["document"]["occurrences"] = json!([
            {"symbol":"p/C#","role":2,"range":{"start_character":2,"end_character":3}},
            {"symbol":"local0","role":1,"range":{"start_character":1,"end_character":2}}]);
        let facts = run(&[row], None, &ExtractOptions::default()).unwrap();
        assert_eq!(facts.occurrences.len(), 1);
        assert_eq!(facts.occurrences[0].span, Span { start: 4, end: 5 });
        let parents: Vec<_> = facts
            .relations
            .iter()
            .filter(|r| r.kind == RelationKind::Parent)
            .map(|r| facts.symbol_name(r.target))
            .collect();
        assert_eq!(parents, ["p/Base#"]);
        assert!(
            facts
                .relations
                .iter()
                .any(|r| r.kind == RelationKind::Signature
                    && facts.symbol_name(r.target) == "p/Arg#")
        );
    }
    #[test]
    fn ordered_scala_parent_provenance_excludes_missing_java_and_conflicting_signatures() {
        let mut row = input("x", "A.scala", "a");
        row["document"]["symbols"] = json!([
            {"symbol":"p/C#","kind":13,"signature":{"class_signature":{"parents":[
                {"type_ref":{"symbol":"p/First#"}}, {"type_ref":{"symbol":"p/Second#"}}]}}},
            {"symbol":"p/Empty#","kind":14,"signature":{"class_signature":{}}},
            {"symbol":"p/Missing#","kind":13},
            {"symbol":"p/Java#","kind":13,"language":2,"signature":{"class_signature":{}}},
            {"symbol":"p/Unknown#","kind":13,"signature":{"class_signature":{"parents":[{"unknown_type":{}}]}}}
        ]);
        let facts = run(&[row.clone()], None, &ExtractOptions::default()).unwrap();
        for name in ["p/C#", "p/Empty#"] {
            assert_ne!(
                facts.symbols[facts.find_symbol(name).unwrap().index()].flags
                    & SYMBOL_SCALA_PARENTS_COMPLETE,
                0
            );
        }
        for name in ["p/Missing#", "p/Java#", "p/Unknown#"] {
            assert_eq!(
                facts.symbols[facts.find_symbol(name).unwrap().index()].flags
                    & SYMBOL_SCALA_PARENTS_COMPLETE,
                0
            );
        }
        let class = facts.find_symbol("p/C#").unwrap();
        assert_eq!(
            facts
                .relations
                .iter()
                .filter(|r| r.source == class && r.kind == RelationKind::Parent)
                .map(|r| facts.symbol_name(r.target))
                .collect::<Vec<_>>(),
            ["p/First#", "p/Second#"]
        );
        let mut other = input("x", "B.scala", "a");
        other["document"]["symbols"] = json!([
            {"symbol":"p/C#","kind":13,"signature":{"class_signature":{"parents":[]}}}
        ]);
        let facts = run(&[row.clone(), other], None, &ExtractOptions::default()).unwrap();
        let class = facts.find_symbol("p/C#").unwrap();
        assert_eq!(
            facts.symbols[class.index()].flags & SYMBOL_SCALA_PARENTS_COMPLETE,
            0
        );
        assert!(
            facts
                .issues
                .iter()
                .any(|i| i.kind == IssueKind::ContextConflict && i.symbol == class)
        );
        row["document"]["language"] = json!(2);
        let facts = run(&[row], None, &ExtractOptions::default()).unwrap();
        assert!(
            facts
                .symbols
                .iter()
                .all(|s| s.flags & SYMBOL_SCALA_PARENTS_COMPLETE == 0)
        );
    }
    #[test]
    fn same_instance_super_keeps_compiler_target_and_qualified_dispatch_flags() {
        for (receiver, bound, flags) in [
            ("super", true, OP_SUPER),
            ("super[T]", true, OP_SUPER | OP_QUALIFIED_SUPER),
            ("super[T]", false, 0),
            ("Outer.super", true, 0),
        ] {
            let source = format!("def f = {receiver}.g()");
            let name = 8 + receiver.len() + 1;
            let mut row = input(&source, "A.scala", "a");
            row["document"]["symbols"] = json!([
                {"symbol":"p/Layer#f().","kind":3},
                {"symbol":"p/CompilerChosen#g(+2).","kind":3},
                {"symbol":"p/CompilerQualifier#","kind":14}
            ]);
            let mut occurrences = vec![
                json!({"symbol":"p/Layer#f().","role":2,"range":{"start_character":4,"end_character":5}}),
                json!({"symbol":"p/CompilerChosen#g(+2).","role":1,"range":{"start_character":name,"end_character":name+1}}),
            ];
            if receiver == "super[T]" && bound {
                occurrences.push(json!({"symbol":"p/CompilerQualifier#","role":1,"range":{"start_character":14,"end_character":15}}));
            }
            row["document"]["occurrences"] = json!(occurrences);
            let syntax = json!({"path":"A.scala","source_sha256":sha(source.as_bytes()).to_string(),
                "producer_sha256":ContentHash([1;32]).to_string(),"ast":{
                    "members":[{"executable":true,"kind":"def","start":0,"end":source.len(),
                        "name_start":4,"name_end":5,"body_start":8,"body_end":source.len()}],
                    "call_sites":[{"start":8,"end":source.len(),"name_start":name,"name_end":name+1,
                        "receiver_start":8,"receiver_end":8+receiver.len(),"kind":"apply","arguments":[]}]}});
            let facts = run(&[row], Some(syntax), &ExtractOptions::default()).unwrap();
            let call = facts
                .operations
                .iter()
                .find(|o| matches!(o.opcode, Opcode::Call | Opcode::VirtualCall))
                .unwrap();
            assert_eq!(facts.symbol_name(call.target), "p/CompilerChosen#g(+2).");
            assert_eq!(call.flags, flags, "{receiver}, binding={bound}");
            if flags != 0 {
                assert_eq!(call.a, ValueId(0));
                assert!(!facts.operations.iter().any(|o| o.opcode == Opcode::Unknown));
            } else {
                assert!(facts.operations.iter().any(|o| o.opcode == Opcode::Unknown));
                assert!(
                    facts
                        .issues
                        .iter()
                        .any(|i| i.kind == IssueKind::UnknownExecution)
                );
            }
        }
    }
    #[test]
    fn package_qualifiers_are_compile_only_but_object_receivers_execute() {
        let source = "def f = pkg.Obj.run()";
        let mut row = input(source, "A.scala", "a");
        row["document"]["symbols"] = json!([
            {"symbol":"p/A#f().","kind":3},
            {"symbol":"pkg/","kind":11},
            {"symbol":"pkg/Obj.","kind":10},
            {"symbol":"pkg/Obj.run().","kind":3}]);
        row["document"]["occurrences"] = json!([
            {"symbol":"p/A#f().","role":2,"range":{"start_character":4,"end_character":5}},
            {"symbol":"pkg/","role":1,"range":{"start_character":8,"end_character":11}},
            {"symbol":"pkg/Obj.","role":1,"range":{"start_character":12,"end_character":15}},
            {"symbol":"pkg/Obj.run().","role":1,"range":{"start_character":16,"end_character":19}}]);
        let syntax = json!({"path":"A.scala","source_sha256":sha(source.as_bytes()).to_string(),
        "producer_sha256":ContentHash([1;32]).to_string(),"ast":{
            "members":[{"executable":true,"kind":"def","start":0,"end":21,
                "name_start":4,"name_end":5,"body_start":8,"body_end":21}],
            "call_sites":[
                {"start":8,"end":11,"name_start":8,"name_end":11,"kind":"select","arguments":[]},
                {"start":8,"end":15,"name_start":12,"name_end":15,"receiver_start":8,"receiver_end":11,"kind":"select","arguments":[]},
                {"start":8,"end":21,"name_start":16,"name_end":19,"receiver_start":8,"receiver_end":15,"kind":"apply","arguments":[]}
            ]}});
        let facts = run(&[row], Some(syntax), &ExtractOptions::default()).unwrap();
        assert!(
            facts
                .occurrences
                .iter()
                .any(|o| facts.symbol_name(o.symbol) == "pkg/")
        );
        assert!(
            !facts
                .operations
                .iter()
                .any(|o| facts.symbol_name(o.target) == "pkg/")
        );
        assert!(
            facts
                .operations
                .iter()
                .any(|o| facts.symbol_name(o.target) == "pkg/Obj.")
        );
        assert!(
            facts
                .operations
                .iter()
                .any(|o| facts.symbol_name(o.target) == "pkg/Obj.run().")
        );
    }
    #[test]
    fn revision_and_memory_limits_fail_before_partial_publication() {
        let row = input("x", "A.scala", "a");
        let wrong = ExtractOptions {
            expected_revision: Some("other".into()),
            ..Default::default()
        };
        assert!(run(&[row.clone()], None, &wrong).is_err());
        let limited = ExtractOptions {
            max_document_bytes: 8,
            ..Default::default()
        };
        assert!(matches!(run(&[row], None, &limited), Err(Error::Limit(_))));
    }
    #[test]
    fn deferred_calls_belong_to_closure_and_not_eager_parent() {
        let source = "def f = () => g()";
        let mut row = input(source, "A.scala", "a");
        row["document"]["symbols"] =
            json!([{"symbol":"p/A#f().","kind":3},{"symbol":"p/A#g().","kind":3}]);
        row["document"]["occurrences"] = json!([
            {"symbol":"p/A#f().","role":2,"range":{"start_character":4,"end_character":5}},
            {"symbol":"p/A#g().","role":1,"range":{"start_character":14,"end_character":15}}]);
        let syntax = json!({"path":"A.scala","source_sha256":sha(source.as_bytes()).to_string(),"producer_sha256":ContentHash([1;32]).to_string(),
            "ast":{"members":[{"executable":true,"kind":"def","start":0,"end":17,"name_start":4,"name_end":5,"body_start":8,"body_end":17}],
            "deferred_ranges":[{"start":8,"end":17,"body_start":14,"body_end":17}],
            "call_sites":[{"start":14,"end":17,"name_start":14,"name_end":15,"kind":"apply","arguments":[]}]}});
        let facts = run(&[row], Some(syntax), &ExtractOptions::default()).unwrap();
        let parent = facts
            .bodies
            .iter()
            .find(|b| facts.symbol_name(b.symbol) == "p/A#f().")
            .unwrap();
        let parent_ops = &facts.operations[parent.operations.range()];
        assert!(parent_ops.iter().any(|o| o.opcode == Opcode::BindCallback));
        assert!(
            !parent_ops
                .iter()
                .any(|o| matches!(o.opcode, Opcode::Call | Opcode::VirtualCall))
        );
        let deferred = facts
            .bodies
            .iter()
            .find(|b| b.flags & BODY_DEFERRED != 0)
            .unwrap();
        assert!(
            facts.operations[deferred.operations.range()]
                .iter()
                .any(|o| o.opcode == Opcode::Call && facts.symbol_name(o.target) == "p/A#g().")
        );
    }
    fn simple_synthetic(tree: Value) -> FactSnapshot {
        let source = "def f = 1";
        let mut row = input(source, "A.scala", "a");
        row["document"]["symbols"] = json!([{"symbol":"p/A#f().","kind":3}]);
        row["document"]["occurrences"] =
            json!([{"symbol":"p/A#f().","role":2,"range":{"start_character":4,"end_character":5}}]);
        row["document"]["synthetics"] =
            json!([{"range":{"start_character":8,"end_character":9},"tree":tree}]);
        let syntax = json!({"path":"A.scala","source_sha256":sha(source.as_bytes()).to_string(),"producer_sha256":ContentHash([1;32]).to_string(),
            "ast":{"members":[{"executable":true,"kind":"def","start":0,"end":9,"name_start":4,"name_end":5,"body_start":8,"body_end":9}],
            "value_expressions":[{"start":8,"end":9,"kind":"literal"}]}});
        run(&[row], Some(syntax), &ExtractOptions::default()).unwrap()
    }
    #[test]
    fn compiler_inserted_callee_is_executable_but_type_argument_is_not() {
        let facts = simple_synthetic(json!({"apply_tree":{"function":{"type_apply_tree":{
            "function":{"id_tree":{"symbol":"p/Convert.apply()."}},
            "type_arguments":[{"type_ref":{"symbol":"p/StaticType#"}}]}},
            "arguments":[{"original_tree":{"range":{"start_character":8,"end_character":9}}}]}}));
        assert!(facts.operations.iter().any(
            |o| o.opcode == Opcode::Call && facts.symbol_name(o.target) == "p/Convert.apply()."
        ));
        assert!(
            !facts
                .operations
                .iter()
                .any(|o| facts.symbol_name(o.target) == "p/StaticType#")
        );
        assert!(
            facts
                .occurrences
                .iter()
                .any(|o| o.role == 3 && facts.symbol_name(o.symbol) == "p/StaticType#")
        );
    }
    #[test]
    fn exact_original_argument_certificate_requires_the_complete_compiler_tree_shape() {
        let original = json!({"original_tree":{"range":{"start_line":0,"start_character":8,"end_line":0,"end_character":9}}});
        for (function, arguments, expected) in [
            (
                json!({"id_tree":{"symbol":"p/Convert.apply()."}}),
                vec![original.clone()],
                true,
            ),
            (
                json!({"type_apply_tree":{"function":{"id_tree":{"symbol":"p/Convert.apply()."}},"type_arguments":[]}}),
                vec![original.clone()],
                false,
            ),
            (
                json!({"id_tree":{"symbol":"p/Convert.apply()."}}),
                vec![original.clone(), original.clone()],
                false,
            ),
            (
                json!({"id_tree":{"symbol":"p/Convert.apply()."}}),
                vec![json!({"original_tree":{}})],
                false,
            ),
            (
                json!({"id_tree":{"symbol":"p/Convert.apply()."}}),
                vec![
                    json!({"original_tree":{"range":{"start_line":0,"start_character":8,"end_line":0,"end_character":8}}}),
                ],
                false,
            ),
        ] {
            let facts =
                simple_synthetic(json!({"apply_tree":{"function":function,"arguments":arguments}}));
            let op = facts
                .operations
                .iter()
                .find(|o| {
                    o.opcode == Opcode::Call && facts.symbol_name(o.target) == "p/Convert.apply()."
                })
                .unwrap();
            assert_eq!(
                op.flags & OP_SYNTHETIC_EXACT_ORIGINAL_ARGUMENT != 0,
                expected
            );
        }
    }
    #[test]
    fn synthetic_function_is_deferred_and_macro_expansion_is_unknown() {
        let facts = simple_synthetic(
            json!({"function_tree":{"parameters":[{"symbol":"local0"}],"body":{
            "apply_tree":{"function":{"id_tree":{"symbol":"p/Callback.run()."}},"arguments":[{"id_tree":{"symbol":"local0"}}]}}}}),
        );
        let parent = facts
            .bodies
            .iter()
            .find(|b| facts.symbol_name(b.symbol) == "p/A#f().")
            .unwrap();
        assert!(
            facts.operations[parent.operations.range()]
                .iter()
                .any(|o| o.opcode == Opcode::BindCallback)
        );
        assert!(
            !facts.operations[parent.operations.range()]
                .iter()
                .any(|o| facts.symbol_name(o.target) == "p/Callback.run().")
        );
        assert!(
            facts
                .bodies
                .iter()
                .filter(|b| b.flags & BODY_DEFERRED != 0)
                .any(|b| facts.operations[b.operations.range()]
                    .iter()
                    .any(|o| facts.symbol_name(o.target) == "p/Callback.run()."))
        );
        let macro_facts = simple_synthetic(
            json!({"macro_expansion_tree":{"before_expansion":{"id_tree":{"symbol":"p/Macro.expand()."}},"tpe":{"type_ref":{"symbol":"p/Output#"}}}}),
        );
        assert!(
            macro_facts
                .issues
                .iter()
                .any(|i| i.kind == IssueKind::UnknownExecution)
        );
        assert!(
            !macro_facts
                .operations
                .iter()
                .any(|o| macro_facts.symbol_name(o.target) == "p/Macro.expand()."
                    && matches!(
                        o.opcode,
                        Opcode::Call | Opcode::VirtualCall | Opcode::Allocate
                    ))
        );
    }
    #[test]
    fn macro_identity_and_result_are_opaque_metadata_with_a_strict_direct_tree_certificate() {
        let tree = json!({"macro_expansion_tree":{"before_expansion":{"id_tree":{"symbol":"p/Macro.expand()."}},"tpe":{"type_ref":{"symbol":"p/Output#"}}}});
        for control in 0..4 {
            let mut tree = tree.clone();
            match control {
                1 => {
                    tree["macro_expansion_tree"]["before_expansion"]["id_tree"]["extra"] =
                        json!(true)
                }
                2 => tree["macro_expansion_tree"]["tpe"]["type_ref"]["type_arguments"] = json!([]),
                3 => tree["extra"] = json!(true),
                _ => (),
            }
            let facts = simple_synthetic(tree);
            let op = facts
                .operations
                .iter()
                .find(|op| op.flags & OP_MACRO_EXPANSION != 0)
                .unwrap();
            assert_eq!(op.opcode, Opcode::Unknown);
            assert_eq!(facts.symbol_name(op.target), "p/Macro.expand().");
            assert_eq!(op.flags & OP_MACRO_DIRECT_TREE != 0, control == 0);
            let metadata = facts
                .operations
                .iter()
                .find(|other| other.dest == op.a)
                .unwrap();
            assert_eq!(metadata.opcode, Opcode::Constant);
            assert_eq!(metadata.flags, OP_MACRO_RESULT_TYPE);
            assert_eq!(facts.symbol_name(metadata.target), "p/Output#");
            assert_eq!(metadata.span.start, metadata.span.end);
            assert!(
                !facts
                    .operations
                    .iter()
                    .any(|op| matches!(op.opcode, Opcode::Call | Opcode::Allocate))
            );
        }
    }
    #[test]
    fn unsigned_negative_range_sentinel_is_reported_without_rejecting_document() {
        let mut row = input("x", "A.scala", "a");
        row["document"]["occurrences"] = json!([{"symbol":"local0","role":1,"range":{"start_character":u64::MAX,"end_character":u64::MAX}}]);
        let facts = run(&[row], None, &ExtractOptions::default()).unwrap();
        assert_eq!(facts.files[0].flags & SOURCE_VERIFIED, SOURCE_VERIFIED);
        assert!(facts.occurrences.is_empty());
        assert!(
            facts
                .issues
                .iter()
                .any(|i| i.kind == IssueKind::InvalidInput)
        );
    }

    #[test]
    fn by_name_actual_is_deferred_without_a_written_lambda() {
        let source = "def f = g(h())";
        let mut row = input(source, "A.scala", "a");
        row["document"]["symbols"] = json!([
            {"symbol":"p/A#f().","kind":3},
            {"symbol":"p/A#g().","kind":3,"signature":{"method_signature":{"parameter_lists":[{"symlinks":["p/A#g().(x)"]}]}}},
            {"symbol":"p/A#g().(x)","kind":8,"signature":{"value_signature":{"tpe":{"by_name_type":{"tpe":{"type_ref":{"symbol":"scala/Int#"}}}}}}},
            {"symbol":"p/A#h().","kind":3}]);
        row["document"]["occurrences"] = json!([
            {"symbol":"p/A#f().","role":2,"range":{"start_character":4,"end_character":5}},
            {"symbol":"p/A#g().","role":1,"range":{"start_character":8,"end_character":9}},
            {"symbol":"p/A#h().","role":1,"range":{"start_character":10,"end_character":11}}]);
        let syntax = json!({"path":"A.scala","source_sha256":sha(source.as_bytes()).to_string(),"producer_sha256":ContentHash([1;32]).to_string(),
            "ast":{"members":[{"executable":true,"kind":"def","start":0,"end":14,"name_start":4,"name_end":5,"body_start":8,"body_end":14}],
            "call_sites":[{"start":8,"end":14,"name_start":8,"name_end":9,"kind":"apply","arguments":[{"start":10,"end":13,"expression_start":10,"expression_end":13}]},
            {"start":10,"end":13,"name_start":10,"name_end":11,"kind":"apply","arguments":[]}]}});
        let facts = run(&[row], Some(syntax), &ExtractOptions::default()).unwrap();
        let parent = facts
            .bodies
            .iter()
            .find(|b| facts.symbol_name(b.symbol) == "p/A#f().")
            .unwrap();
        let ops = &facts.operations[parent.operations.range()];
        assert!(ops.iter().any(|o| o.opcode == Opcode::BindCallback));
        assert!(
            ops.iter()
                .any(|o| o.opcode == Opcode::Call && facts.symbol_name(o.target) == "p/A#g().")
        );
        assert!(
            !ops.iter()
                .any(|o| facts.symbol_name(o.target) == "p/A#h().")
        );
        assert!(
            facts
                .bodies
                .iter()
                .filter(|b| b.flags & BODY_DEFERRED != 0)
                .any(|b| facts.operations[b.operations.range()]
                    .iter()
                    .any(|o| facts.symbol_name(o.target) == "p/A#h()."))
        );
    }
    #[test]
    fn named_arguments_keep_source_evaluation_but_bind_compiler_parameter_order() {
        let source = "def f = g(b=2,a=1)";
        let mut row = input(source, "A.scala", "a");
        row["document"]["symbols"] = json!([
            {"symbol":"p/A#f().","kind":3},
            {"symbol":"p/A#g().","kind":3,"signature":{"method_signature":{"parameter_lists":[{"symlinks":["p/A#g().(a)","p/A#g().(b)"]}]}}},
            {"symbol":"p/A#g().(a)","kind":8},{"symbol":"p/A#g().(b)","kind":8}]);
        row["document"]["occurrences"] = json!([
            {"symbol":"p/A#f().","role":2,"range":{"start_character":4,"end_character":5}},
            {"symbol":"p/A#g().","role":1,"range":{"start_character":8,"end_character":9}},
            {"symbol":"p/A#g().(b)","role":1,"range":{"start_character":10,"end_character":11}},
            {"symbol":"p/A#g().(a)","role":1,"range":{"start_character":14,"end_character":15}}]);
        let syntax = json!({"path":"A.scala","source_sha256":sha(source.as_bytes()).to_string(),"producer_sha256":ContentHash([1;32]).to_string(),
            "ast":{"members":[{"executable":true,"kind":"def","start":0,"end":18,"name_start":4,"name_end":5,"body_start":8,"body_end":18}],
            "call_sites":[{"start":8,"end":18,"name_start":8,"name_end":9,"kind":"apply","arguments":[
                {"start":10,"end":13,"expression_start":12,"expression_end":13,"label_range":{"start":10,"end":11}},
                {"start":14,"end":17,"expression_start":16,"expression_end":17,"label_range":{"start":14,"end":15}}]}],
            "value_expressions":[{"start":12,"end":13,"kind":"literal"},{"start":16,"end":17,"kind":"literal"}]}});
        let facts = run(&[row], Some(syntax), &ExtractOptions::default()).unwrap();
        let constants: Vec<_> = facts
            .operations
            .iter()
            .filter(|o| o.opcode == Opcode::Constant)
            .collect();
        assert_eq!(constants[0].span.start, 12);
        assert_eq!(constants[1].span.start, 16);
        let call = facts
            .operations
            .iter()
            .find(|o| o.opcode == Opcode::Call)
            .unwrap();
        assert_eq!(
            &facts.operands[call.arguments.range()],
            &[constants[1].dest, constants[0].dest]
        );
    }
    #[test]
    fn default_expression_binds_declared_getter_and_stays_deferred() {
        let source = "def f(a: Int = h()) = a";
        let mut row = input(source, "A.scala", "a");
        row["document"]["symbols"] = json!([
            {"symbol":"p/A#f().","kind":3,"signature":{"method_signature":{"parameter_lists":[{"symlinks":["p/A#f().(a)"]}]}}},
            {"symbol":"p/A#f().(a)","kind":8,"properties":32768},
            {"symbol":"p/A#f$default$1().","display_name":"f$default$1","kind":3},
            {"symbol":"p/A#h().","kind":3}]);
        row["document"]["occurrences"] = json!([
            {"symbol":"p/A#f().","role":2,"range":{"start_character":4,"end_character":5}},
            {"symbol":"p/A#f().(a)","role":2,"range":{"start_character":6,"end_character":7}},
            {"symbol":"p/A#h().","role":1,"range":{"start_character":15,"end_character":16}},
            {"symbol":"p/A#f().(a)","role":1,"range":{"start_character":22,"end_character":23}}]);
        let syntax = json!({"path":"A.scala","source_sha256":sha(source.as_bytes()).to_string(),"producer_sha256":ContentHash([1;32]).to_string(),
            "ast":{"members":[{"executable":true,"kind":"def","start":0,"end":23,"name_start":4,"name_end":5,"body_start":22,"body_end":23,
                "parameters":[{"start":6,"end":18,"name_start":6,"name_end":7,"default":{"start":15,"end":18}}]}],
            "call_sites":[{"start":15,"end":18,"name_start":15,"name_end":16,"kind":"apply","arguments":[]}],
            "value_expressions":[{"start":22,"end":23,"kind":"reference"}]}});
        let facts = run(&[row], Some(syntax), &ExtractOptions::default()).unwrap();
        let method = facts
            .bodies
            .iter()
            .find(|body| facts.symbol_name(body.symbol) == "p/A#f().")
            .unwrap();
        assert!(
            !facts.operations[method.operations.range()]
                .iter()
                .any(|op| facts.symbol_name(op.target) == "p/A#h().")
        );
        let getter = facts
            .bodies
            .iter()
            .find(|body| facts.symbol_name(body.symbol) == "p/A#f$default$1().")
            .unwrap();
        assert_ne!(getter.flags & BODY_DEFERRED, 0);
        assert!(
            facts.operations[getter.operations.range()]
                .iter()
                .any(|op| op.opcode == Opcode::Call && facts.symbol_name(op.target) == "p/A#h().")
        );
    }
    #[test]
    fn deferred_body_edits_and_comments_do_not_change_factory_owned_recipe() {
        fn fixture(prefix: &str, callee: &str) -> FactSnapshot {
            let source = format!("{prefix}def f = () => {callee}()");
            let start = prefix.len();
            let call = source.rfind(callee).unwrap();
            let end = source.len();
            let mut row = input(&source, "A.scala", "a");
            let target = format!("p/A#{callee}().");
            row["document"]["symbols"] =
                json!([{"symbol":"p/A#f().","kind":3},{"symbol":target,"kind":3}]);
            row["document"]["occurrences"] = json!([
                {"symbol":"p/A#f().","role":2,"range":{"start_character":start+4,"end_character":start+5}},
                {"symbol":target,"role":1,"range":{"start_character":call,"end_character":call+1}}]);
            let syntax = json!({"path":"A.scala","source_sha256":sha(source.as_bytes()).to_string(),"producer_sha256":ContentHash([1;32]).to_string(),
                "ast":{"members":[{"executable":true,"kind":"def","start":start,"end":end,"name_start":start+4,"name_end":start+5,"body_start":start+8,"body_end":end}],
                "deferred_ranges":[{"start":start+8,"end":end,"body_start":call,"body_end":end}],
                "call_sites":[{"start":call,"end":end,"name_start":call,"name_end":call+1,"kind":"apply","arguments":[]}]}});
            run(&[row], Some(syntax), &ExtractOptions::default()).unwrap()
        }
        let original = fixture("", "g");
        let comment = fixture("/* comment */ ", "g");
        let edited = fixture("", "h");
        let factory_hash = |facts: &FactSnapshot| {
            facts
                .bodies
                .iter()
                .find(|b| facts.symbol_name(b.symbol) == "p/A#f().")
                .unwrap()
                .body_hash
        };
        assert_eq!(factory_hash(&original), factory_hash(&comment));
        assert_eq!(factory_hash(&original), factory_hash(&edited));
        let closure = |facts: &FactSnapshot| {
            facts
                .bodies
                .iter()
                .find(|b| b.flags & BODY_DEFERRED != 0)
                .unwrap()
                .body_hash
        };
        assert_eq!(closure(&original), closure(&comment));
        assert_ne!(closure(&original), closure(&edited));
        let closure_name = |facts: &FactSnapshot| {
            facts
                .symbol_name(
                    facts
                        .bodies
                        .iter()
                        .find(|b| b.flags & BODY_DEFERRED != 0)
                        .unwrap()
                        .symbol,
                )
                .to_owned()
        };
        assert_eq!(closure_name(&original), closure_name(&comment));
    }
    #[test]
    fn document_normalization_is_identical_across_worker_and_batch_partitions() {
        let mut a = input("x", "A.scala", "a");
        a["document"]["symbols"] = json!([{"symbol":"p/A#","kind":13,"signature":{"class_signature":{"parents":[{"type_ref":{"symbol":"p/B#"}}]}}}]);
        a["document"]["occurrences"] =
            json!([{"symbol":"p/A#","role":2,"range":{"start_character":0,"end_character":1}}]);
        let mut b = input("x", "B.scala", "a");
        b["document"]["symbols"] = json!([{"symbol":"p/B#","kind":13}]);
        b["document"]["occurrences"] =
            json!([{"symbol":"p/B#","role":2,"range":{"start_character":0,"end_character":1}}]);
        let rows = [a, b];
        let serial = run(
            &rows,
            None,
            &ExtractOptions {
                workers: 1,
                batch_bytes: 1,
                ..Default::default()
            },
        )
        .unwrap();
        let parallel = run(
            &rows,
            None,
            &ExtractOptions {
                workers: 4,
                ..Default::default()
            },
        )
        .unwrap();
        assert_eq!(serial.identity, parallel.identity);
        assert_eq!(serial.strings.bytes, parallel.strings.bytes);
        assert_eq!(serial.symbols.len(), parallel.symbols.len());
        assert_eq!(serial.relations.len(), parallel.relations.len());
        for (a, b) in serial.symbols.iter().zip(&parallel.symbols) {
            assert_eq!(
                (
                    a.name,
                    a.owner,
                    a.file,
                    a.context,
                    a.kind,
                    a.properties,
                    a.signature,
                    a.span,
                    a.flags
                ),
                (
                    b.name,
                    b.owner,
                    b.file,
                    b.context,
                    b.kind,
                    b.properties,
                    b.signature,
                    b.span,
                    b.flags
                )
            );
        }
        let b = parallel.find_symbol("p/B#").unwrap();
        assert_eq!(parallel.path(parallel.symbols[b.index()].file), "B.scala");
    }
    #[test]
    fn local_owned_closures_keep_source_identity_across_files_and_publication_orders() {
        let source = "def f = () => g()";
        let mut rows = Vec::new();
        let mut syntax_rows = Vec::new();
        for path in ["A.scala", "B.scala"] {
            let target = format!("p/{}#g().", path.trim_end_matches(".scala"));
            let mut row = input(source, path, "same:compile");
            row["document"]["symbols"] = json!([
                {"symbol":"local4","kind":3}, {"symbol":target,"kind":3}]);
            row["document"]["occurrences"] = json!([
                {"symbol":"local4","role":2,"range":{"start_character":4,"end_character":5}},
                {"symbol":target,"role":1,"range":{"start_character":14,"end_character":15}}]);
            rows.push(row);
            syntax_rows.push(json!({"path":path,"source_sha256":sha(source.as_bytes()).to_string(),
                "producer_sha256":ContentHash([1;32]).to_string(),"ast":{
                    "members":[{"executable":true,"kind":"def","start":0,"end":17,
                        "name_start":4,"name_end":5,"body_start":8,"body_end":17}],
                    "deferred_ranges":[{"start":8,"end":17,"body_start":14,"body_end":17}],
                    "call_sites":[{"start":14,"end":17,"name_start":14,"name_end":15,"kind":"apply","arguments":[]}]}}));
        }
        let directory = tempfile::tempdir().unwrap();
        let capture = directory.path().join("documents.jsonl");
        let syntax = directory.path().join("syntax.jsonl");
        std::fs::write(
            &syntax,
            syntax_rows
                .iter()
                .map(|r| format!("{r}\n"))
                .collect::<String>(),
        )
        .unwrap();
        let mut baseline = None;
        for workers in [1, 4] {
            std::fs::write(
                &capture,
                rows.iter().map(|r| format!("{r}\n")).collect::<String>(),
            )
            .unwrap();
            let facts = import_capture(
                &capture,
                Some(&syntax),
                &ExtractOptions {
                    workers,
                    ..Default::default()
                },
            )
            .unwrap();
            let deferred: Vec<_> = facts
                .bodies
                .iter()
                .filter(|b| b.flags & BODY_DEFERRED != 0)
                .collect();
            assert_eq!(deferred.len(), 2);
            assert_ne!(deferred[0].symbol, deferred[1].symbol);
            let mut identities = Vec::new();
            for body in deferred {
                let symbol = &facts.symbols[body.symbol.index()];
                assert_eq!(
                    symbol.file, body.file,
                    "synthetic declaration/body source must agree"
                );
                assert_eq!(facts.symbol_name(symbol.owner), "local4");
                assert_eq!(facts.symbols[symbol.owner.index()].file, body.file);
                let path = facts.path(body.file);
                let target = format!("p/{}#g().", path.trim_end_matches(".scala"));
                assert!(
                    facts.operations[body.operations.range()]
                        .iter()
                        .any(|op| op.opcode == Opcode::Call
                            && facts.symbol_name(op.target) == target)
                );
                identities.push((path.to_owned(), facts.symbol_name(body.symbol).to_owned()));
            }
            identities.sort_unstable();
            if let Some(previous) = &baseline {
                assert_eq!(&identities, previous);
            } else {
                baseline = Some(identities);
            }
            rows.reverse();
        }
    }
}
