//! Normalized capture/snapshot controls over the genuine admission-chain JARs.
//! The explicit test archive policy is not a standard-library semantic claim.
use super::*;
use crate::provider::{InputPin, ProviderOptions};
use selector_facts::{FactBuilder, FileRecord, IssueRecord};
use serde_json::{Value, json};
use std::path::{Path, PathBuf};

struct Fixture {
    _dir: tempfile::TempDir,
    root: PathBuf,
    contexts: PathBuf,
    map: PathBuf,
    library: PathBuf,
}
fn pin(path: &Path) -> InputPin {
    let bytes = std::fs::read(path).unwrap();
    InputPin {
        path: path.to_owned(),
        sha256: Sha256::digest(&bytes).into(),
        bytes: bytes.len() as u64,
    }
}
impl Fixture {
    fn new(opaque: bool, application: bool) -> Self {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path().canonicalize().unwrap();
        let fixtures =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/native-admission-chain");
        let library = root.join("library.jar");
        let shadow = root.join("shadow.jar");
        let gap = root.join("opaque.jar");
        std::fs::copy(fixtures.join("bytecode.jar"), &library).unwrap();
        std::fs::copy(fixtures.join("shadow.jar"), &shadow).unwrap();
        std::fs::write(&gap, b"opaque").unwrap();
        let first = if opaque { &gap } else { &shadow };
        let cp = |path: &Path, index| json!({"index":index,"path":path,"input_object":path,"sha256":ContentHash(pin(path).sha256).to_string()});
        let mut capture = json!({"schema_version":"sbt-compiler-context/v1","revision":"normalized-library-issuer", "source_root":root,"errors":[],"java_runtime":{"java_version":"21.0.12.1"},
            "contexts":[{"context_id":"a","full_classpath":[cp(&library,0)]},
                {"context_id":"b","full_classpath":[cp(first,0),cp(&library,1)]},
                {"context_id":"c","full_classpath":[cp(&library,0)]}],
            "input_objects":([&library,&shadow,&gap].map(|p|json!({"path":p,"kind":"file","sha256":ContentHash(pin(p).sha256).to_string(),"bytes":pin(p).bytes})))});
        if application {
            capture["contexts"][0]["full_classpath"][0]["project_output_origins"] =
                json!([{"context_id":"own-source"}]);
        }
        let entry = |path: &Path, kind| json!({"path":path,"kind":kind,"sha256":ContentHash(pin(path).sha256).to_string()});
        let native = json!({"version":1,"revision":"normalized-library-issuer","java_feature":21,
            "contexts":[{"id":"a","entries":[entry(&library,"jar")]},
                {"id":"b","entries":[entry(first,if opaque{"unavailable"}else{"jar"}),entry(&library,"jar")]},
                {"id":"c","entries":[entry(&library,"jar")]}],"types":[],"methods":[]});
        let contexts = root.join("contexts.json");
        let map = root.join("map.json");
        std::fs::write(&contexts, serde_json::to_vec(&capture).unwrap()).unwrap();
        std::fs::write(&map, serde_json::to_vec(&native).unwrap()).unwrap();
        Self {
            _dir: dir,
            root,
            contexts,
            map,
            library,
        }
    }
    fn provider(&self) -> VerifiedProvider<'static> {
        VerifiedProvider::admit(
            &ProviderOptions {
                contexts: pin(&self.contexts),
                binary_map: pin(&self.map),
                relocated_root: self.root.clone(),
                facts_identity: None,
                source_products_identity: None,
                platform: None,
                limits: Default::default(),
            },
            None,
        )
        .unwrap()
    }
    fn policy(&self) -> TrustPolicy {
        TrustPolicy::new(vec![ContentHash(pin(&self.library).sha256)]).unwrap()
    }
    fn facts(&self, contexts: &[&str]) -> FactSnapshot {
        let mut provider = self.provider();
        let (_, receipt) = provider.resolve(0, "admissioncase/Getter").unwrap();
        let class_hash = ContentHash(receipt.class_sha256.unwrap());
        let mut builder = FactBuilder::new();
        builder.facts.revision = builder.intern("normalized-library-issuer").unwrap();
        let empty = builder.intern("").unwrap();
        let path = builder
            .intern(&format!(
                "{}!/admissioncase/Getter.class",
                self.library.display()
            ))
            .unwrap();
        for &context in contexts {
            let context = builder.intern(context).unwrap();
            builder.facts.files.push(FileRecord {
                path,
                source: empty,
                revision: builder.facts.revision,
                context,
                source_hash: class_hash,
                flags: FILE_BINARY_SOURCE,
            });
        }
        let mut facts = builder.finish().unwrap();
        facts.identity =
            selector_facts::codec::write(&self.root.join("facts.bin"), &facts).unwrap();
        facts
    }
    fn mutate_capture(&self, change: impl FnOnce(&mut Value)) {
        let mut capture = serde_json::from_slice(&std::fs::read(&self.contexts).unwrap()).unwrap();
        change(&mut capture);
        std::fs::write(&self.contexts, serde_json::to_vec(&capture).unwrap()).unwrap();
    }
}

#[test]
fn exact_policy_issues_contextual_file_and_first_provider_receipts_deterministically() {
    let f = Fixture::new(false, false);
    let facts = f.facts(&["a", "c"]);
    let mut first = f.provider();
    let mut second = f.provider();
    let a = issue(&facts, &mut first, &f.policy(), Limits::default()).unwrap();
    let b = issue(&facts, &mut second, &f.policy(), Limits::default()).unwrap();
    assert_eq!(a.identity(), b.identity());
    assert_eq!(a.files(), b.files());
    assert_eq!(a.files().len(), 2);
    assert_eq!(a.providers().len(), 2);
    assert!(a.denials().is_empty());
    assert_ne!(a.providers()[0].identity, a.providers()[1].identity);
    assert_ne!(
        a.file_proofs()[0].resolution_sha256,
        a.file_proofs()[1].resolution_sha256
    );
    assert_eq!(
        a.file_proofs()[0].provider_sha256,
        a.file_proofs()[1].provider_sha256
    );
    assert_eq!(a.facts_identity(), facts.identity);
    assert_eq!(a.provider_identity(), ContentHash(first.identity()));
    assert_eq!(a.policy_identity(), f.policy().identity());
    assert!(
        a.providers()
            .iter()
            .all(|p| p.origin == ProviderOrigin::DependencyArchive)
    );
}

#[test]
fn matching_class_or_path_does_not_authorize_a_shadow_or_opaque_provider() {
    for opaque in [false, true] {
        let f = Fixture::new(opaque, false);
        let facts = f.facts(&["b"]);
        let result = issue(&facts, &mut f.provider(), &f.policy(), Limits::default()).unwrap();
        assert!(result.files().is_empty());
        assert_eq!(
            result.denials()[0].reason,
            if opaque {
                Denial::UnresolvedProvider
            } else {
                Denial::OutsidePolicy
            }
        );
    }
    let f = Fixture::new(false, false);
    let facts = f.facts(&["a"]);
    let result = issue(
        &facts,
        &mut f.provider(),
        &TrustPolicy::new(Vec::new()).unwrap(),
        Limits::default(),
    )
    .unwrap();
    assert!(result.files().is_empty());
    assert_eq!(result.denials()[0].reason, Denial::OutsidePolicy);
}

#[test]
fn file_hash_context_revision_and_origin_are_independent_required_bindings() {
    for mutation in 0..4 {
        let f = Fixture::new(false, false);
        let mut facts = f.facts(&["a"]);
        match mutation {
            0 => facts.files[0].source_hash = ContentHash([4; 32]),
            1 => facts.files[0].context = StrId::NONE,
            2 => facts.files[0].revision = StrId::NONE,
            _ => facts.files[0].path = facts.files[0].context,
        }
        let result = issue(&facts, &mut f.provider(), &f.policy(), Limits::default()).unwrap();
        assert!(result.files().is_empty(), "mutation {mutation}");
        assert_eq!(result.denials().len(), 1);
    }
}

#[test]
fn source_ownership_and_captured_application_products_cannot_be_allowlisted() {
    let f = Fixture::new(false, false);
    let mut facts = f.facts(&["a"]);
    facts.symbols.push(selector_facts::SymbolRecord {
        name: facts.files[0].path,
        display: StrId::NONE,
        owner: SymbolId::NONE,
        file: FileId(0),
        context: facts.files[0].context,
        kind: 13,
        properties: 0,
        signature: StrId::NONE,
        span: Span::default(),
        flags: SYMBOL_DEFINED,
    });
    let result = issue(&facts, &mut f.provider(), &f.policy(), Limits::default()).unwrap();
    assert_eq!(result.denials()[0].reason, Denial::SourceOwned);
    for ownership in 0..3 {
        let f = Fixture::new(false, ownership == 0);
        if ownership == 1 {
            f.mutate_capture(|c| c["contexts"][0]["class_directory"] = json!(f.library));
        }
        if ownership == 2 {
            f.mutate_capture(|c| {
                c["contexts"][0]["exported_products"] = json!([{"path":f.library}])
            });
        }
        let facts = f.facts(&["a"]);
        let result = issue(&facts, &mut f.provider(), &f.policy(), Limits::default()).unwrap();
        assert!(result.files().is_empty());
        assert_eq!(
            result.denials()[0].reason,
            Denial::ApplicationProduct,
            "ownership {ownership}"
        );
    }
}

#[test]
fn exact_file_and_global_conflicts_revoke_authority_without_cross_context_trust() {
    for global in [false, true] {
        let f = Fixture::new(false, false);
        let mut facts = f.facts(&["a", "c"]);
        facts.issues.push(IssueRecord {
            kind: IssueKind::ContextConflict,
            file: if global { FileId::NONE } else { FileId(0) },
            symbol: SymbolId::NONE,
            detail: StrId::NONE,
        });
        let result = issue(&facts, &mut f.provider(), &f.policy(), Limits::default()).unwrap();
        assert_eq!(result.files().len(), usize::from(!global));
        assert_eq!(result.denials()[0].reason, Denial::Conflict);
        if !global {
            assert_eq!(result.files()[0].file, FileId(1));
        }
    }
}

#[test]
fn source_conflict_stays_a_source_frontier_without_revoking_independent_binary_files() {
    let f = Fixture::new(false, false);
    let mut facts = f.facts(&["a", "c"]);
    let source = FileId(facts.files.len() as u32);
    facts.files.push(FileRecord {
        flags: SOURCE_VERIFIED,
        ..facts.files[0]
    });
    let symbol = SymbolId(facts.symbols.len() as u32);
    facts.symbols.push(selector_facts::SymbolRecord {
        name: facts.files[0].path,
        display: StrId::NONE,
        owner: SymbolId::NONE,
        file: source,
        context: facts.files[0].context,
        kind: 3,
        properties: 0,
        signature: StrId::NONE,
        span: Span::default(),
        flags: SYMBOL_DEFINED,
    });
    facts.issues.push(IssueRecord {
        kind: IssueKind::ContextConflict,
        file: source,
        symbol,
        detail: StrId::NONE,
    });
    let result = issue(&facts, &mut f.provider(), &f.policy(), Limits::default()).unwrap();
    assert_eq!(result.files().len(), 2);
    assert!(result.denials().is_empty());
    assert_eq!(
        facts.issues[0].symbol, symbol,
        "source obligation remains intact"
    );
}

#[test]
fn exact_native_method_or_declaring_owner_conflict_revokes_only_its_body_file() {
    for owner_conflict in [false, true] {
        let f = Fixture::new(false, false);
        let mut facts = f.facts(&["a", "c"]);
        for (index, kind) in [(0, 13), (1, 3)] {
            facts.symbols.push(selector_facts::SymbolRecord {
                name: facts.files[0].path,
                display: StrId::NONE,
                owner: if index == 1 {
                    SymbolId(0)
                } else {
                    SymbolId::NONE
                },
                file: FileId::NONE,
                context: facts.files[0].context,
                kind,
                properties: 0,
                signature: StrId::NONE,
                span: Span::default(),
                flags: SYMBOL_NATIVE_BINARY,
            });
        }
        facts.bodies.push(selector_facts::BodyRecord {
            symbol: SymbolId(1),
            file: FileId(0),
            span: Span::default(),
            name_span: Span::default(),
            operations: IdRange::default(),
            parameters: IdRange::default(),
            body_hash: ContentHash([8; 32]),
            flags: BODY_BINARY_RECIPE,
        });
        facts.issues.push(IssueRecord {
            kind: IssueKind::ContextConflict,
            file: FileId::NONE,
            symbol: SymbolId(u32::from(!owner_conflict)),
            detail: StrId::NONE,
        });
        let result = issue(&facts, &mut f.provider(), &f.policy(), Limits::default()).unwrap();
        assert_eq!(result.files().len(), 1);
        assert_eq!(result.files()[0].file, FileId(1));
        assert_eq!(
            result.denials()[0],
            DeniedFile {
                file: FileId(0),
                reason: Denial::Conflict
            }
        );
    }
}

#[test]
fn policy_and_work_budgets_fail_closed_instead_of_issuing_empty_success() {
    assert!(TrustPolicy::new(vec![ContentHash::default()]).is_err());
    assert!(TrustPolicy::new(vec![ContentHash([1; 32]); 2]).is_err());
    let f = Fixture::new(false, false);
    let facts = f.facts(&["a", "c"]);
    assert!(matches!(
        issue(
            &facts,
            &mut f.provider(),
            &f.policy(),
            Limits {
                files: 1,
                ..Default::default()
            }
        ),
        Err(Error::Budget)
    ));
    assert!(matches!(
        issue(
            &facts,
            &mut f.provider(),
            &f.policy(),
            Limits {
                providers: 1,
                ..Default::default()
            }
        ),
        Err(Error::Budget)
    ));
    let options = ProviderOptions {
        contexts: pin(&f.contexts),
        binary_map: pin(&f.map),
        relocated_root: f.root.clone(),
        facts_identity: None,
        source_products_identity: None,
        platform: None,
        limits: Default::default(),
    };
    std::fs::write(&f.library, b"changed physical provider").unwrap();
    assert!(VerifiedProvider::admit(&options, None).is_err());
}
