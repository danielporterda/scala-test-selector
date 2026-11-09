//! Compiler normalization owns one program until external metadata admission
//! completes. Finishing consumes that owner and lowers syntax exactly once.
use crate::{
    EXTRACTOR_VERSION, ExtractOptions, Input, attach_catalogue, compiler_contexts,
    external_metadata::{self, AdmittedExternalMetadata, MetadataRequestLimits, MetadataRequests},
    normalize, result_bounds, syntax, synthetics,
};
use rayon::prelude::*;
use selector_facts::*;
use selector_types::*;
use sha2::{Digest, Sha256};
use std::collections::HashSet;
use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::sync::{Arc, OnceLock};

/// The normalized compiler tables have one owner. No source body has been
/// lowered and external metadata cannot claim a source definition.
#[must_use]
pub struct PreparedCapture {
    builder: FactBuilder,
    synthetics: Option<synthetics::Synthetics>,
    identity: Sha256,
    consumed: u64,
    pool: rayon::ThreadPool,
    contexts_path: Option<PathBuf>,
    contexts_identity: OnceLock<ContentHash>,
    capture_identity: ContentHash,
    syntax_path: Option<PathBuf>,
    options: ExtractOptions,
}
impl PreparedCapture {
    pub fn metadata_requests(
        &self,
        limits: &MetadataRequestLimits,
    ) -> Result<MetadataRequests<'_>, Error> {
        let contexts_identity = match self.contexts_path.as_deref() {
            None => None,
            Some(path) => {
                if let Some(pin) = self.contexts_identity.get() {
                    Some(*pin)
                } else {
                    let pin = context_pin(path)?;
                    if self.contexts_identity.set(pin).is_err()
                        && self.contexts_identity.get() != Some(&pin)
                    {
                        return Err(Error::Invalid(
                            "compiler contexts changed while collecting metadata requests",
                        ));
                    }
                    Some(pin)
                }
            }
        };
        external_metadata::requests(
            &self.builder,
            self.synthetics.as_ref(),
            limits,
            self.capture_identity,
            contexts_identity,
        )
    }
    pub fn revision(&self) -> &str {
        self.builder.facts.text(self.builder.facts.revision)
    }
}

/// Normalize compiler documents once; the returned owner can wait while a
/// driver admits batched external metadata using its exact requested identities.
pub fn prepare_capture(
    path: &Path,
    syntax: Option<&Path>,
    options: &ExtractOptions,
) -> Result<PreparedCapture, Error> {
    if options.workers == 0 || options.max_document_bytes == 0 || options.batch_bytes == 0 {
        return Err(Error::Invalid("extraction limits"));
    }
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(options.workers)
        .build()
        .map_err(|e| Error::Message(e.to_string()))?;
    let mut builder = FactBuilder::new();
    let mut input = Input::open(path, options, 0)?;
    let mut identity = Sha256::new();
    identity.update(EXTRACTOR_VERSION.as_bytes());
    identity.update([0]);
    identity.update(selector_framework::VERSION.as_bytes());
    identity.update([0]);
    let mut seen = HashSet::new();
    let mut synthetics = syntax.map(|_| synthetics::Synthetics::default());
    loop {
        let lines = input.batch(options.batch_bytes)?;
        if lines.is_empty() {
            break;
        }
        for row in &lines {
            identity.update(row);
        }
        // Borrowed wire strings and signatures live exactly as long as this batch.
        let decoded: Vec<_> = pool.install(|| {
            lines
                .par_iter()
                .map(|line| normalize::prepare(line, options, syntax.is_some()))
                .collect()
        });
        for partition in decoded {
            normalize::publish(&mut builder, synthetics.as_mut(), partition?, &mut seen)?;
        }
    }
    let contexts_path = options.compiler_contexts.clone().or_else(|| {
        path.parent()
            .map(|parent| parent.join("compiler-contexts.json.gz"))
            .filter(|path| path.is_file())
    });
    let contexts_identity = OnceLock::new();
    let capture_identity = ContentHash(identity.clone().finalize().into());
    Ok(PreparedCapture {
        builder,
        synthetics,
        identity,
        consumed: input.total,
        pool,
        contexts_path,
        contexts_identity,
        capture_identity,
        syntax_path: syntax.map(Path::to_owned),
        options: options.clone(),
    })
}

/// Consume the normalized compiler owner, publish optional metadata, and lower
/// source syntax once. With no metadata this preserves import_capture semantics.
pub fn finish_capture(
    prepared: PreparedCapture,
    metadata: Option<Arc<AdmittedExternalMetadata>>,
) -> Result<FactSnapshot, Error> {
    let PreparedCapture {
        mut builder,
        mut synthetics,
        mut identity,
        consumed,
        pool,
        contexts_path,
        contexts_identity,
        capture_identity,
        syntax_path,
        options,
    } = prepared;
    let contexts_identity = contexts_identity.into_inner();
    let syntax = syntax_path.as_deref();
    let options = &options;
    if let Some(metadata) = metadata {
        metadata.validate_scope(capture_identity, contexts_identity)?;
        if contexts_path.as_deref().map(context_pin).transpose()? != contexts_identity {
            return Err(Error::Invalid(
                "compiler contexts changed after metadata admission",
            ));
        }
        metadata.publish(&mut builder)?;
        identity.update(b"\0external-compiler-metadata/v1\0");
        identity.update(metadata.identity().0);
    }
    // Repeated metadata cannot turn conflicting compiler signatures into an
    // asserted complete parent order, regardless of publication order.
    for issue in &builder.facts.issues {
        if issue.kind == IssueKind::ContextConflict && !issue.symbol.is_none() {
            builder.facts.symbols[issue.symbol.index()].flags &= !SYMBOL_SCALA_PARENTS_COMPLETE;
        }
    }
    let qualified_bindings = compiler_contexts::bind(
        &mut builder,
        synthetics.as_mut(),
        contexts_path.as_deref(),
        options,
        &mut identity,
    )?;
    if let Some(path) = syntax {
        syntax::import(
            &mut builder,
            path,
            options,
            consumed,
            &pool,
            &mut identity,
            synthetics.as_ref().expect("syntax pending IR"),
        )?;
    }
    qualified_bindings.attach(&mut builder)?;
    let missing: Vec<_> = builder
        .facts
        .files
        .iter()
        .enumerate()
        .filter(|(_, f)| f.flags & SOURCE_VERIFIED != 0 && f.flags & SYNTAX_VERIFIED == 0)
        .map(|(i, _)| FileId(i as u32))
        .collect();
    for file in missing {
        builder.issue(IssueKind::MissingSyntax, file, SymbolId::NONE,
            "validated executable spans absent; compiler name-token occurrences are compilation facts only")?;
    }
    if let Some(path) = &options.catalogue {
        let mut catalogue = File::open(path)?;
        if catalogue.metadata()?.len() > 64 * 1024 * 1024 {
            return Err(Error::Limit("catalogue bytes"));
        }
        let mut buffer = [0u8; 65536];
        identity.update(b"\0catalogue/v2\0");
        loop {
            let n = catalogue.read(&mut buffer)?;
            if n == 0 {
                break;
            }
            identity.update(&buffer[..n]);
        }
        attach_catalogue(&mut builder, path)?;
    }
    result_bounds::project(&mut builder)?;
    identity.update(b"\0compiler-result-bounds/v1\0");
    for bound in &builder.facts.result_bounds {
        identity.update(bound.symbol.0.to_le_bytes());
        identity.update(bound.operation.0.to_le_bytes());
        identity.update(bound.classes.len.to_le_bytes());
        for class in &builder.facts.bound_classes[bound.classes.range()] {
            identity.update(class.0.to_le_bytes());
        }
    }
    identity.update(b"\0owned-recipes/v1\0");
    for body in &builder.facts.bodies {
        identity.update(builder.facts.symbol_name(body.symbol).as_bytes());
        identity.update([0]);
        if !body.symbol.is_none() {
            identity.update(
                builder
                    .facts
                    .text(builder.facts.symbols[body.symbol.index()].context)
                    .as_bytes(),
            );
        }
        identity.update([0]);
        identity.update(body.body_hash.0);
        identity.update(body.flags.to_le_bytes());
    }
    builder.facts.identity = ContentHash(identity.finalize().into());
    builder.finish()
}

fn context_pin(path: &Path) -> Result<ContentHash, Error> {
    let mut file = File::open(path)?;
    if file.metadata()?.len() > 64 * 1024 * 1024 {
        return Err(Error::Limit("compiler context input bytes"));
    }
    let mut hash = Sha256::new();
    let mut buffer = [0u8; 65536];
    let mut total = 0u64;
    loop {
        let count = file.read(&mut buffer)?;
        if count == 0 {
            break;
        }
        total += count as u64;
        if total > 64 * 1024 * 1024 {
            return Err(Error::Limit("compiler context input bytes"));
        }
        hash.update(&buffer[..count]);
    }
    Ok(ContentHash(hash.finalize().into()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::external_metadata::*;
    use std::sync::atomic::{AtomicU64, Ordering};
    static NEXT: AtomicU64 = AtomicU64::new(0);
    struct Temporary(PathBuf);
    impl Temporary {
        fn new() -> Self {
            let path = std::env::temp_dir().join(format!(
                "selector-prepared-capture-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            std::fs::create_dir(&path).unwrap();
            Self(path)
        }
    }
    impl Drop for Temporary {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    fn fixture() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/compiler-smoke")
    }
    #[test]
    fn compiler_tables_move_into_finish_without_reopening_source_and_none_bytes_match() {
        let temporary = Temporary::new();
        let input = temporary.0.join("documents.jsonl");
        std::fs::copy(fixture().join("documents.jsonl"), &input).unwrap();
        let syntax = fixture().join("syntax.jsonl");
        let options = ExtractOptions {
            workers: 1,
            ..ExtractOptions::default()
        };
        let prepared = prepare_capture(&input, Some(&syntax), &options).unwrap();
        assert!(prepared.builder.facts.bodies.is_empty());
        assert!(prepared.builder.facts.operations.is_empty());
        assert!(!prepared.synthetics.as_ref().unwrap().nodes.is_empty());
        // Finishing must use the owned normalized compiler tables, not parse the source again.
        std::fs::write(&input, b"invalid replacement compiler capture").unwrap();
        let finished = finish_capture(prepared, None).unwrap();
        let wrapper =
            crate::import_capture(&fixture().join("documents.jsonl"), Some(&syntax), &options)
                .unwrap();
        assert_eq!(finished.identity, wrapper.identity);
        let first = temporary.0.join("split.bin");
        let second = temporary.0.join("wrapper.bin");
        assert_eq!(
            selector_facts::codec::write(&first, &finished).unwrap(),
            selector_facts::codec::write(&second, &wrapper).unwrap()
        );
        assert_eq!(
            std::fs::read(first).unwrap(),
            std::fs::read(second).unwrap()
        );
    }
    #[test]
    fn metadata_none_preserves_native_golden_except_exact_constructor_binding() {
        // This is the actual independently produced historical artifact, not a
        // new expected digest generated through the prepare/finish wrapper.
        let fixture =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/selected-external-apply");
        let golden = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../fixtures/metadata-none-native-regression/pre-refactor.bin");
        let input = fixture.join("documents.jsonl");
        let syntax = fixture.join("syntax.jsonl");
        assert_eq!(
            crate::sha(&std::fs::read(&input).unwrap()).to_string(),
            "04c5e35c82857d4fcc822c0ffb981cfc24404f31d3db196d99923768af4a092d"
        );
        assert_eq!(
            crate::sha(&std::fs::read(&syntax).unwrap()).to_string(),
            "84f5fa5d62235c5b732479bb0991f492fcc3f7e0c4e511598068a458dfbdd3eb"
        );
        let historical_bytes = std::fs::read(&golden).unwrap();
        assert_eq!(
            crate::sha(&historical_bytes).to_string(),
            "610285e2ffdbf1f805270159dd2d38b52058ea378be0d9a706fe316e00ed22dc"
        );
        let historical = selector_facts::codec::read(&golden).unwrap();
        assert_eq!(
            historical.identity.to_string(),
            "368b21f194341e60c3999d6d11b73bf488ae0a9ccde1297a9aaabe849025c1cd"
        );
        let mut facts = finish_capture(
            prepare_capture(
                &input,
                Some(&syntax),
                &ExtractOptions {
                    workers: 1,
                    ..ExtractOptions::default()
                },
            )
            .unwrap(),
            None,
        )
        .unwrap();
        let class = facts.find_symbol("selectedexternal/Span#").unwrap();
        let constructor = facts
            .find_symbol("selectedexternal/Span#`<init>`().")
            .unwrap();
        let owners = [
            "selectedexternal/Calls#interval().",
            "selectedexternal/Calls#timeout().",
        ]
        .map(|name| facts.find_symbol(name).unwrap());
        let mut targets = 0;
        let mut hashes = 0;
        for (current, old) in facts.operations.iter_mut().zip(&historical.operations) {
            if current.target == constructor && old.target == class {
                assert_eq!(current.opcode, Opcode::Allocate);
                assert!(owners.contains(&facts.bodies[current.body.index()].symbol));
                current.target = old.target;
                targets += 1;
            }
        }
        assert_eq!(targets, 2);
        for (current, old) in facts.bodies.iter_mut().zip(&historical.bodies) {
            if owners.contains(&current.symbol) {
                assert_ne!(current.body_hash, old.body_hash);
                current.body_hash = old.body_hash;
                hashes += 1;
            }
        }
        assert_eq!(hashes, 2);
        const OLD_GUARD: &str = "constructor overload has no exact compiler occurrence";
        const NEW_GUARD: &str =
            "compiler-selected constructor has no authoritative source argument signature";
        let mut guards = 0;
        for (index, current) in facts.issues.iter().enumerate() {
            if owners.contains(&current.symbol) {
                assert_eq!(current.kind, IssueKind::UnknownExecution);
                assert_eq!(facts.text(current.detail), NEW_GUARD);
                let old = &historical.issues[index];
                assert_eq!(old.symbol, current.symbol);
                assert_eq!(old.kind, IssueKind::UnresolvedSymbol);
                assert_eq!(historical.text(old.detail), OLD_GUARD);
                guards += 1;
            }
        }
        assert_eq!(guards, 2);
        for current in &mut facts.issues {
            if owners.contains(&current.symbol) {
                current.kind = IssueKind::UnresolvedSymbol;
            }
        }
        // No string identifiers may be remapped. Only the shared guard text
        // changes; byte offsets after that text naturally move in the pool.
        assert_eq!(facts.strings.len(), historical.strings.len());
        let mut guard_strings = 0;
        for index in 0..facts.strings.len() {
            let id = StrId(index as u32);
            if historical.text(id) == OLD_GUARD {
                assert_eq!(facts.text(id), NEW_GUARD);
                guard_strings += 1;
            } else {
                assert_eq!(facts.text(id), historical.text(id));
            }
        }
        assert_eq!(guard_strings, 1);
        facts.strings = historical.strings;
        let temporary = Temporary::new();
        let output = temporary.0.join("normalized.bin");
        assert_eq!(
            selector_facts::codec::write(&output, &facts)
                .unwrap()
                .to_string(),
            "368b21f194341e60c3999d6d11b73bf488ae0a9ccde1297a9aaabe849025c1cd"
        );
        assert_eq!(std::fs::read(output).unwrap(), historical_bytes);
    }
    struct Authority(ContentHash);
    impl MetadataProviderAuthority for Authority {
        fn identity(&self) -> ContentHash {
            crate::sha(b"test-authority")
        }
        fn contexts_identity(&self) -> ContentHash {
            self.0
        }
        fn resolve(&self, _: &str, _: &str) -> Result<Option<ProviderResolution>, Error> {
            panic!("empty metadata has no provider lookup")
        }
    }
    fn empty_metadata(prepared: &PreparedCapture, directory: &Path) -> AdmittedExternalMetadata {
        let requests = prepared
            .metadata_requests(&MetadataRequestLimits::default())
            .unwrap();
        let context = requests.contexts_identity().unwrap();
        let authority = Authority(context);
        let manifest = ExternalMetadataManifest {
            module_headers: Vec::new(),
            schema: MANIFEST_SCHEMA.to_owned(),
            producer_sha256: crate::sha(b"test-converter").to_string(),
            authority_sha256: authority.identity().to_string(),
            contexts_sha256: context.to_string(),
            payloads: vec![],
            bindings: vec![],
        };
        let path = directory.join("external.json");
        std::fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
        admit(
            &path,
            &requests,
            &authority,
            crate::sha(b"test-converter"),
            &ExternalMetadataLimits::default(),
        )
        .unwrap()
    }
    #[test]
    fn raw_context_pin_and_capture_owner_are_checked_before_metadata_publication() {
        let temporary = Temporary::new();
        let contexts = temporary.0.join("compiler-contexts.json.gz");
        let physical = b"physical gzip-container control; not decompressed bytes";
        std::fs::write(&contexts, physical).unwrap();
        let options = ExtractOptions {
            workers: 1,
            compiler_contexts: Some(contexts.clone()),
            ..ExtractOptions::default()
        };
        let prepared = prepare_capture(&fixture().join("documents.jsonl"), None, &options).unwrap();
        let requests = prepared
            .metadata_requests(&MetadataRequestLimits::default())
            .unwrap();
        assert_eq!(requests.contexts_identity(), Some(crate::sha(physical)));
        let metadata = empty_metadata(&prepared, &temporary.0);
        std::fs::write(&contexts, b"changed physical context input").unwrap();
        assert!(matches!(
            finish_capture(prepared, Some(Arc::new(metadata))),
            Err(Error::Invalid(
                "compiler contexts changed after metadata admission"
            ))
        ));
        std::fs::write(&contexts, physical).unwrap();
        let prepared = prepare_capture(&fixture().join("documents.jsonl"), None, &options).unwrap();
        let metadata = empty_metadata(&prepared, &temporary.0);
        let original = std::fs::read_to_string(fixture().join("documents.jsonl")).unwrap();
        let changed: String = original
            .lines()
            .map(|line| {
                format!(
                    "{},\"scope_control\":true}}\n",
                    line.trim_end().strip_suffix('}').unwrap()
                )
            })
            .collect();
        let input = temporary.0.join("different-capture.jsonl");
        std::fs::write(&input, changed).unwrap();
        let other = prepare_capture(&input, None, &options).unwrap();
        other
            .metadata_requests(&MetadataRequestLimits::default())
            .unwrap();
        assert!(matches!(
            finish_capture(other, Some(Arc::new(metadata))),
            Err(Error::Invalid(
                "external metadata belongs to another compiler capture"
            ))
        ));
    }
}
