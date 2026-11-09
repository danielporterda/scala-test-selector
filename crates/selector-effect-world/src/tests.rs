use super::*;
use selector_facts::FactSnapshot;
use selector_graph::ProgramGraph;
use selector_types::*;

fn empty() -> (FactSnapshot, ProgramGraph, SnapshotPins) {
    let facts = FactSnapshot {
        identity: ContentHash([1; 32]),
        ..Default::default()
    };
    let mut graph = ProgramGraph {
        identity: ContentHash([2; 32]),
        facts_identity: facts.identity,
        ..Default::default()
    };
    graph.index().unwrap();
    let pins = SnapshotPins {
        facts: facts.identity,
        graph: graph.identity,
        runtime: None,
    };
    (facts, graph, pins)
}
#[test]
fn snapshot_identity_runtime_and_graph_links_are_exact() {
    let (facts, mut graph, pins) = empty();
    assert!(ValidatedSnapshot::new(&facts, &graph, pins).is_ok());
    for field in 0..4 {
        let mut p = pins;
        match field {
            0 => p.facts = ContentHash::default(),
            1 => p.graph = ContentHash([3; 32]),
            2 => p.runtime = Some(ContentHash::default()),
            3 => p.runtime = Some(ContentHash([4; 32])),
            _ => unreachable!(),
        }
        assert!(ValidatedSnapshot::new(&facts, &graph, p).is_err());
    }
    graph.facts_identity = ContentHash([5; 32]);
    assert!(ValidatedSnapshot::new(&facts, &graph, pins).is_err());
}
#[test]
fn root_identity_has_unambiguous_length_prefixes() {
    let a = RootKey {
        name: "ab",
        context: "c",
        compiler_class: "p/Suite#",
    };
    let b = RootKey {
        name: "a",
        context: "bc",
        compiler_class: "p/Suite#",
    };
    assert_ne!(a.digest(), b.digest());
    assert_ne!(
        a.digest(),
        RootKey {
            compiler_class: "p/Suite.",
            ..a
        }
        .digest()
    );
    assert_eq!(a.digest(), a.digest());
}

mod admitted_fixture {
    //! Real frozen compiler class/SDB bytes, with an explicitly synthetic unit
    //! transport envelope. This tests admission/binding APIs, not Zinc lineage.
    //! The independent retained-analysis example supplies the genuine lineage.
    use super::*;
    use selector_compiled_products as p;
    use selector_facts::{FactBuilder, FileRecord, SuiteRecord};
    use selector_graph::NodeRecord;
    use serde_json::{Value, json};
    use sha2::{Digest, Sha256};
    use std::{
        fs,
        path::{Path, PathBuf},
    };
    pub const CONTEXT: &str = "project:anonymous-construction/configuration:test";
    pub const SOURCE: &str = "src/anonymouscase/Allocations.scala";
    fn hash(b: &[u8]) -> String {
        p::hash_hex(Sha256::digest(b).into())
    }
    fn pin(path: &Path) -> p::Pin {
        let b = fs::read(path).unwrap();
        p::Pin {
            path: path.into(),
            sha256: hash(&b),
            bytes: b.len() as u64,
        }
    }
    fn put(path: &Path, bytes: impl AsRef<[u8]>) {
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, bytes).unwrap();
    }
    fn jsonfile(path: &Path, value: Value) {
        put(path, serde_json::to_vec(&value).unwrap())
    }
    fn stamp() -> Value {
        json!({"class":"sbt.internal.inc.FarmHash","written":"farm(abc)","hash":"abc","modified":null})
    }
    pub struct Fixture {
        pub _tmp: tempfile::TempDir,
        pub products: p::VerifiedBinding,
        pub product_pins: ProductPins,
        pub facts: FactSnapshot,
        pub graph: ProgramGraph,
        pub pins: SnapshotPins,
    }
    impl Fixture {
        pub fn new() -> Self {
            let base = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../../fixtures/anonymous-construction");
            let frozen: Value =
                serde_json::from_slice(&fs::read(base.join("manifest.json")).unwrap()).unwrap();
            let tmp = tempfile::tempdir().unwrap();
            let dir = tmp.path();
            let source_root = dir.join("source");
            let mut products = Vec::new();
            let mut inventory = Vec::new();
            for record in frozen["files"].as_array().unwrap() {
                let name = record["path"].as_str().unwrap();
                if !(name.starts_with("classes/") && name.ends_with(".class"))
                    && name != SOURCE
                    && name != "documents.jsonl"
                {
                    continue;
                }
                let b = fs::read(base.join(name)).unwrap();
                assert_eq!(hash(&b), record["sha256"].as_str().unwrap());
                assert_eq!(b.len() as u64, record["bytes"].as_u64().unwrap());
                if let Some(rel) = name.strip_prefix("classes/") {
                    put(&source_root.join(name), &b);
                    products.push(json!({"path":format!("${{BASE}}/{name}"),"stamp":stamp(),"bytes":b.len(),"sha256":hash(&b),"recomputed_content_hash":stamp()}));
                    inventory.push(json!({"bytes":b.len(),"path":rel,"sha256":hash(&b)}));
                } else if name == SOURCE {
                    put(&source_root.join(name), b);
                }
            }
            inventory.sort_by(|a, b| a["path"].as_str().cmp(&b["path"].as_str()));
            let inventory_hash = hash(&serde_json::to_vec(&inventory).unwrap());
            let total: u64 = inventory.iter().map(|f| f["bytes"].as_u64().unwrap()).sum();
            let source = fs::read(source_root.join(SOURCE)).unwrap();
            let sha = hash(&source);
            let classdir = source_root.join("classes");
            let contexts = dir.join("contexts.json");
            jsonfile(
                &contexts,
                json!({"source_root":source_root,"contexts":[{"context_id":CONTEXT,"class_directory":classdir,"source_records":[{"path":source_root.join(SOURCE),"repo_relative_path":SOURCE,"sha256":sha}],"full_classpath":[{"index":0,"path":classdir,"input_object":classdir,"sha256":inventory_hash}]}],"input_objects":[{"path":classdir,"kind":"directory","sha256":inventory_hash,"files":inventory.len(),"bytes":total}]}),
            );
            let analysis = dir.join("unit-transport-analysis");
            put(
                &analysis,
                b"synthetic unit transport; NOT a real Zinc analysis",
            );
            let output = dir.join("reader.jsonl");
            put(
                &output,
                format!(
                    "{}\n",
                    json!({"source":format!("${{BASE}}/{SOURCE}"),"source_stamp":stamp(),"source_bytes":source.len(),"source_sha256":sha,"recomputed_source_farmhash":stamp(),"products":products})
                ),
            );
            let producer = dir.join("unit-producer");
            put(
                &producer,
                b"synthetic unit transport over genuine frozen compiler products; no lineage claim",
            );
            let pi = pin(&producer);
            let mut h = Sha256::new();
            h.update(b"retained-zinc-source-products-producer/v1\0");
            let text = pi.path.to_str().unwrap();
            h.update((text.len() as u64).to_le_bytes());
            h.update(text.as_bytes());
            h.update(p::parse_hash(&pi.sha256).unwrap());
            h.update(pi.bytes.to_le_bytes());
            let producer_hash: p::Hash = h.finalize().into();
            let receipt = dir.join("reader-receipt.json");
            jsonfile(
                &receipt,
                json!({"all_inputs_unchanged":true,"inputs":[pin(&analysis),pi],"commands":[{"case":"read-unit","command":["ReadZinc",analysis,source_root],"exit_code":0,"stdout":output,"stdout_bytes":pin(&output).bytes}]}),
            );
            let compile = dir.join("compile.json");
            jsonfile(
                &compile,
                json!({"exit_code":0,"qualification":"synthetic unit transport; original genuine compiler provenance in pinned fixture manifest"}),
            );
            let manifest = p::Manifest {
                schema: "retained-zinc-source-products/v1".into(),
                qualification: "new_retained_analysis_correspondence".into(),
                producer_sha256: p::hash_hex(producer_hash),
                producer_inputs: vec![pin(&producer)],
                contexts: pin(&contexts),
                documents: pin(&base.join("documents.jsonl")),
                compile_receipt: pin(&compile),
                inputs: vec![p::ContextInput {
                    context: CONTEXT.into(),
                    analysis: pin(&analysis),
                    reader_output: pin(&output),
                    reader_receipt: pin(&receipt),
                }],
            };
            let mp = dir.join("manifest.json");
            put(&mp, serde_json::to_vec(&manifest).unwrap());
            let expected = p::Expectations {
                manifest: p::parse_hash(&pin(&mp).sha256).unwrap(),
                producer: producer_hash,
                contexts: p::parse_hash(&manifest.contexts.sha256).unwrap(),
                documents: p::parse_hash(&manifest.documents.sha256).unwrap(),
                compile_receipt: p::parse_hash(&manifest.compile_receipt.sha256).unwrap(),
            };
            let binding = p::admit(&mp, &expected, &p::Limits::default()).unwrap();
            let mut b = FactBuilder::new();
            b.facts.identity = ContentHash([1; 32]);
            let path = b.intern(SOURCE).unwrap();
            let text = b.intern(std::str::from_utf8(&source).unwrap()).unwrap();
            let context = b.intern(CONTEXT).unwrap();
            b.facts.files.push(FileRecord {
                path,
                source: text,
                revision: StrId::NONE,
                context,
                source_hash: ContentHash(p::parse_hash(&sha).unwrap()),
                flags: SOURCE_VERIFIED,
            });
            let file = FileId(0);
            for (name, raw, kind) in [
                ("anonymouscase.Active", "anonymouscase/Active#", 13),
                ("anonymouscase.Dormant", "anonymouscase/Dormant#", 13),
                ("anonymouscase.Effects", "anonymouscase/Effects.", 10),
            ] {
                let symbol = b.ensure_symbol(raw, file).unwrap();
                let row = &mut b.facts.symbols[symbol.index()];
                row.file = file;
                row.kind = kind;
                row.context = context;
                row.flags = SYMBOL_DEFINED;
                let name = b.intern(name).unwrap();
                b.facts.suites.push(SuiteRecord {
                    name,
                    symbol,
                    file,
                    flags: 0,
                });
            }
            let unresolved = b.intern("uncaptured.PendingSuite").unwrap();
            b.facts.suites.push(SuiteRecord {
                name: unresolved,
                symbol: SymbolId::NONE,
                file: FileId::NONE,
                flags: EDGE_UNKNOWN,
            });
            let facts = b.finish().unwrap();
            let mut graph = ProgramGraph {
                identity: ContentHash([2; 32]),
                facts_identity: facts.identity,
                ..Default::default()
            };
            for (i, s) in facts.symbols.iter().enumerate() {
                graph.nodes.push(NodeRecord {
                    symbol: SymbolId(i as u32),
                    file: s.file,
                    body: BodyId::NONE,
                    flags: 0,
                });
                graph.symbol_nodes.push(NodeId(i as u32));
            }
            graph.index().unwrap();
            let pins = SnapshotPins {
                facts: facts.identity,
                graph: graph.identity,
                runtime: None,
            };
            Self {
                _tmp: tmp,
                products: binding,
                product_pins: ProductPins {
                    manifest: expected.manifest,
                    contexts: expected.contexts,
                    documents: expected.documents,
                },
                facts,
                graph,
                pins,
            }
        }
        pub fn snapshot(&self) -> ValidatedSnapshot<'_> {
            ValidatedSnapshot::new(&self.facts, &self.graph, self.pins).unwrap()
        }
    }
}

#[test]
fn genuine_compiler_products_bind_class_module_and_keep_unresolved_roots() {
    let f = admitted_fixture::Fixture::new();
    let s = f.snapshot();
    let c =
        CompiledCatalogue::bind(&s, &f.products, f.product_pins, BindingLimits::default()).unwrap();
    assert_eq!(c.roots().len(), 4);
    for i in 0..3 {
        let RootBinding::Bound(root) = c.roots()[i].binding else {
            panic!("root{i} not bound")
        };
        let m = c.entry_method(i as u32).unwrap();
        assert_eq!(m.descriptor, "()V");
        assert_eq!(root.class, root.initialize_class);
        assert_eq!(m.name, if i == 2 { "<clinit>" } else { "<init>" });
    }
    assert!(matches!(
        c.roots()[3].binding,
        RootBinding::Pending(PendingBinding::CatalogueUnresolved)
    ));
    let methods = c
        .bind_requested(
            &[RequestedSource {
                context: admitted_fixture::CONTEXT,
                path: admitted_fixture::SOURCE,
            }],
            BindingLimits::default(),
        )
        .unwrap();
    assert!(methods.all_requested_bound());
    assert_eq!(methods.methods().len(), f.products.method_count());
}
#[test]
fn seed_subsets_deduplicate_methods_and_report_each_pending_request() {
    let f = admitted_fixture::Fixture::new();
    let s = f.snapshot();
    let c =
        CompiledCatalogue::bind(&s, &f.products, f.product_pins, BindingLimits::default()).unwrap();
    let yes = RequestedSource {
        context: admitted_fixture::CONTEXT,
        path: admitted_fixture::SOURCE,
    };
    let rows = c
        .bind_requested(
            &[
                yes,
                yes,
                RequestedSource {
                    context: "missing",
                    path: admitted_fixture::SOURCE,
                },
                RequestedSource {
                    context: admitted_fixture::CONTEXT,
                    path: "missing.scala",
                },
            ],
            BindingLimits::default(),
        )
        .unwrap();
    assert_eq!(rows.rows().len(), 4);
    assert_eq!(rows.methods().len(), f.products.method_count());
    assert!(!rows.all_requested_bound());
    assert!(matches!(rows.rows()[2].binding, SeedBinding::Pending(_)));
    let mut limits = BindingLimits::default();
    limits.max_seed_methods = 1;
    assert!(c.bind_requested(&[yes], limits).is_err());
}
#[test]
fn stale_source_pins_and_duplicate_root_keys_never_select_a_candidate() {
    let mut f = admitted_fixture::Fixture::new();
    let snapshot = f.snapshot();
    let mut pins = f.product_pins;
    pins.documents = [3; 32];
    assert!(
        CompiledCatalogue::bind(&snapshot, &f.products, pins, BindingLimits::default()).is_err()
    );
    f.facts.files[0].source_hash = ContentHash([4; 32]);
    let snapshot = f.snapshot();
    let c = CompiledCatalogue::bind(
        &snapshot,
        &f.products,
        f.product_pins,
        BindingLimits::default(),
    )
    .unwrap();
    assert!(matches!(
        c.roots()[0].binding,
        RootBinding::Pending(PendingBinding::SourceHashMismatch)
    ));
    drop(c);
    f.facts.suites.push(f.facts.suites[0]);
    let snapshot = f.snapshot();
    assert!(
        CompiledCatalogue::bind(
            &snapshot,
            &f.products,
            f.product_pins,
            BindingLimits::default()
        )
        .is_err()
    );
}

#[test]
fn unrequested_added_source_is_reported_by_separate_captured_delta_coverage() {
    use selector_facts::{FactBuilder, FileRecord};
    let base = admitted_fixture::Fixture::new();
    let mut head = admitted_fixture::Fixture::new();
    let mut builder = FactBuilder::new();
    builder.facts = std::mem::take(&mut head.facts);
    let path = builder.intern("generated/OtherSource.scala").unwrap();
    let text = builder.intern("object OtherSource").unwrap();
    let context = builder.intern(admitted_fixture::CONTEXT).unwrap();
    builder.facts.files.push(FileRecord {
        path,
        source: text,
        revision: StrId::NONE,
        context,
        source_hash: ContentHash([7; 32]),
        flags: SOURCE_VERIFIED,
    });
    head.facts = builder.finish().unwrap();
    let a = base.snapshot();
    let b = head.snapshot();
    let a = CompiledCatalogue::bind(
        &a,
        &base.products,
        base.product_pins,
        BindingLimits::default(),
    )
    .unwrap();
    let b = CompiledCatalogue::bind(
        &b,
        &head.products,
        head.product_pins,
        BindingLimits::default(),
    )
    .unwrap();
    let selected = b
        .bind_requested(
            &[RequestedSource {
                context: admitted_fixture::CONTEXT,
                path: admitted_fixture::SOURCE,
            }],
            BindingLimits::default(),
        )
        .unwrap();
    assert!(selected.all_requested_bound());
    let whole = compare_captured_sources(&a, &b, BindingLimits::default()).unwrap();
    assert_eq!(whole.rows().len(), 1);
    assert!(!whole.all_changed_sources_bound());
    assert!(whole.rows()[0].base_file.is_none());
    assert_eq!(
        whole.rows()[0].head_pending,
        Some(PendingBinding::MissingProductSource)
    );
}
#[test]
fn changed_compiler_context_and_unverified_input_remain_pending() {
    use selector_facts::FactBuilder;
    let base = admitted_fixture::Fixture::new();
    let mut head = admitted_fixture::Fixture::new();
    let mut b = FactBuilder::new();
    b.facts = std::mem::take(&mut head.facts);
    let other = b.intern("project:other/configuration:test").unwrap();
    b.facts.files[0].context = other;
    for symbol in &mut b.facts.symbols {
        symbol.context = other;
    }
    head.facts = b.finish().unwrap();
    let a = base.snapshot();
    let b = head.snapshot();
    let a = CompiledCatalogue::bind(
        &a,
        &base.products,
        base.product_pins,
        BindingLimits::default(),
    )
    .unwrap();
    let b = CompiledCatalogue::bind(
        &b,
        &head.products,
        head.product_pins,
        BindingLimits::default(),
    )
    .unwrap();
    let delta = compare_captured_sources(&a, &b, BindingLimits::default()).unwrap();
    assert_eq!(delta.rows().len(), 2);
    assert!(!delta.all_changed_sources_bound());
    assert!(
        b.roots()
            .iter()
            .all(|r| matches!(r.binding, RootBinding::Pending(_)))
    );
    let mut limits = BindingLimits::default();
    limits.max_roots = 1;
    assert!(
        CompiledCatalogue::bind(&base.snapshot(), &base.products, base.product_pins, limits)
            .is_err()
    );
}
