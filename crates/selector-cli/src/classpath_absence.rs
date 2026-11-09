//! Query-only bridge from checked physical provider evidence to paired policy.
//! Request JSON identifies inputs; it never carries trusted proof rows.
use selector_facts::FactSnapshot;
use selector_graph::ProgramGraph;
use selector_native_effects::stable_compilation;
use selector_native_effects::{classpath_absence as issuer, provider::VerifiedProvider};
use selector_plan::{PlanSeeds, classpath_absence as policy};
use selector_select::ChangeSeeds;
use selector_types::*;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::sync::Arc;

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

pub struct ExecutionFrontiers {
    pub base: Arc<[selector_solve::ExecutionRoot]>,
    pub head: Arc<[selector_solve::ExecutionRoot]>,
    pub pruned: usize,
}

/// Schedule an omission only when the same contextual suite has an exact
/// certificate in both revisions. All other roots still get a normal query.
/// The selection stage revalidates the proof and the issuer rechecks its
/// physical inputs before any omitted root can become an exclusion.
pub fn execution_frontiers(
    plan: &policy::Plan,
    base_facts: &FactSnapshot,
    base_graph: &ProgramGraph,
    head_facts: &FactSnapshot,
    head_graph: &ProgramGraph,
) -> Result<ExecutionFrontiers> {
    fn key(facts: &FactSnapshot, root: selector_select::SuiteRoot) -> (&str, &str, &str, &str) {
        let suite = &facts.suites[root.suite.index()];
        let symbol = &facts.symbols[root.receiver.index()];
        let name = facts.text(symbol.name);
        let local_scope = if selector_types::symbol::is_local(name) || name.starts_with("@local:") {
            facts.path(symbol.file)
        } else {
            ""
        };
        (
            facts.text(suite.name),
            name,
            facts.text(symbol.context),
            local_scope,
        )
    }
    let base_roots = selector_select::suite_roots(base_facts, base_graph)?;
    let head_roots = selector_select::suite_roots(head_facts, head_graph)?;
    let base_certified: BTreeMap<_, _> = base_roots
        .iter()
        .copied()
        .filter(|r| plan.certificate(false, r.suite, r.node).is_some())
        .map(|r| (key(base_facts, r), r.suite))
        .collect();
    let mut omit_base = BTreeSet::new();
    let mut omit_head = BTreeSet::new();
    for r in &head_roots {
        if plan.certificate(true, r.suite, r.node).is_some()
            && let Some(base) = base_certified.get(&key(head_facts, *r))
        {
            omit_base.insert(*base);
            omit_head.insert(r.suite);
        }
    }
    let scheduled = |roots: Vec<selector_select::SuiteRoot>, omitted: &BTreeSet<SuiteId>| {
        roots
            .into_iter()
            .filter(|r| !omitted.contains(&r.suite))
            .map(|r| selector_solve::ExecutionRoot {
                node: r.node,
                receiver: r.receiver,
            })
            .collect::<Vec<_>>()
            .into()
    };
    Ok(ExecutionFrontiers {
        base: scheduled(base_roots, &omit_base),
        head: scheduled(head_roots, &omit_head),
        pruned: omit_head.len(),
    })
}

/// Inventory a superset of the requested products, never a subset of effective
/// changes. A native node may retain its compiler source on SymbolRecord.file.
fn source_inventory(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    requested: &[String],
    execution: &[NodeId],
    declarations: &[NodeId],
) -> Result<Vec<FileId>> {
    let mut paths: BTreeSet<&str> = requested.iter().map(String::as_str).collect();
    for &node in execution.iter().chain(declarations) {
        let node = graph.nodes.get(node.index()).ok_or("classpath seed node")?;
        let symbol_file = if node.symbol.is_none() {
            FileId::NONE
        } else {
            facts
                .symbols
                .get(node.symbol.index())
                .ok_or("classpath seed symbol")?
                .file
        };
        for id in [node.file, symbol_file] {
            if id.is_none() {
                continue;
            }
            let file = facts.files.get(id.index()).ok_or("classpath seed file")?;
            if file.flags & (SOURCE_VERIFIED | SYNTAX_VERIFIED | FILE_BINARY_SOURCE)
                == SOURCE_VERIFIED | SYNTAX_VERIFIED
            {
                paths.insert(facts.text(file.path));
            }
        }
    }
    // Once a path is admitted into the proof universe, include every source
    // context, including unverified siblings so ordinary admission fails closed.
    Ok(facts
        .files
        .iter()
        .enumerate()
        .filter_map(|(index, file)| {
            (file.flags & FILE_BINARY_SOURCE == 0 && paths.contains(facts.text(file.path)))
                .then_some(FileId(index as u32))
        })
        .collect())
}
fn check_outputs(
    protected: impl IntoIterator<Item = PathBuf>,
    outputs: &[PathBuf],
    resolve: fn(&Path) -> Result<PathBuf>,
) -> Result<()> {
    let outputs = outputs
        .iter()
        .map(|p| resolve(p))
        .collect::<Result<Vec<_>>>()?;
    for input in protected {
        let input = resolve(&input)?;
        if outputs
            .iter()
            .any(|output| output.starts_with(&input) || input.starts_with(output))
        {
            return Err("classpath query output overlaps an admitted physical input".into());
        }
    }
    Ok(())
}
#[derive(serde::Deserialize)]
struct PathOnly {
    path: PathBuf,
}
#[derive(serde::Deserialize)]
struct CapturePaths {
    source_root: PathBuf,
    input_objects: Vec<PathOnly>,
    source_to_contexts: BTreeMap<PathBuf, serde::de::IgnoredAny>,
}
#[derive(serde::Deserialize)]
struct MapPaths {
    contexts: Vec<MapContextPaths>,
}
#[derive(serde::Deserialize)]
struct MapContextPaths {
    entries: Vec<PathOnly>,
}
#[derive(serde::Deserialize)]
struct PlatformPaths {
    image: ImagePaths,
    java_base: BasePaths,
}
#[derive(serde::Deserialize)]
struct ImagePaths {
    launcher: PathOnly,
    release: PathOnly,
    modules: PathOnly,
}
#[derive(serde::Deserialize)]
struct BasePaths {
    archive: PathOnly,
    inventory: PathOnly,
}
fn read_paths<T: serde::de::DeserializeOwned>(path: &Path, limit: u64) -> Result<T> {
    use std::io::Read;
    let input = std::fs::File::open(path)?;
    let reader: Box<dyn Read> = if path.extension().is_some_and(|x| x == "gz") {
        Box::new(std::io::BufReader::new(flate2::read::GzDecoder::new(input)))
    } else {
        Box::new(std::io::BufReader::new(input))
    };
    let mut reader = reader.take(
        limit
            .checked_add(1)
            .ok_or("classpath preflight byte limit")?,
    );
    let value = serde_json::from_reader(&mut reader)?;
    if reader.limit() == 0 {
        return Err("classpath preflight byte limit".into());
    }
    Ok(value)
}
/// Run before opening progress/receipt outputs. Narrow path-only decoding skips
/// unrelated capture records without retaining the document or rehashing CP
/// providers. These paths only reject overlap; they never grant proof authority.
pub fn preflight_outputs(
    path: &Path,
    outputs: &[PathBuf],
    resolve: fn(&Path) -> Result<PathBuf>,
) -> Result<()> {
    let request = issuer::read_request(path)?;
    let mut protected = request.inputs;
    let relative = |path: PathBuf, document: &Path| {
        if path.is_absolute() {
            path
        } else {
            document.parent().unwrap_or(Path::new(".")).join(path)
        }
    };
    let sides = [&request.base, &request.head];
    let mut source_paths = [BTreeSet::new(), BTreeSet::new()];
    for (index, options) in sides.into_iter().enumerate() {
        let capture: CapturePaths =
            read_paths(&options.contexts.path, options.limits.manifest_bytes)?;
        source_paths[index] = capture.source_to_contexts.into_keys().collect();
        protected.extend(capture.input_objects.into_iter().map(|object| {
            object
                .path
                .strip_prefix(&capture.source_root)
                .map_or_else(|_| object.path.clone(), |p| options.relocated_root.join(p))
        }));
        let map: MapPaths = read_paths(&options.binary_map.path, options.limits.manifest_bytes)?;
        protected.extend(
            map.contexts
                .into_iter()
                .flat_map(|context| context.entries)
                .map(|entry| relative(entry.path, &options.binary_map.path)),
        );
        if let Some(platform) = &options.platform {
            let pins: PlatformPaths =
                read_paths(&platform.manifest, options.limits.manifest_bytes)?;
            protected.extend(
                [
                    pins.image.launcher.path,
                    pins.image.release.path,
                    pins.image.modules.path,
                    pins.java_base.archive.path,
                    pins.java_base.inventory.path,
                ]
                .into_iter()
                .map(|p| relative(p, &platform.manifest)),
            );
        }
    }
    // The missing side of a newly added/removed source is an input as well.
    // Protect it before opening progress logs or other query output paths.
    for (index, options) in sides.into_iter().enumerate() {
        protected.extend(
            source_paths[1 - index]
                .difference(&source_paths[index])
                .filter(|path| {
                    path.components()
                        .all(|part| matches!(part, std::path::Component::Normal(_)))
                })
                .map(|path| options.relocated_root.join(path)),
        );
    }
    check_outputs(protected, outputs, resolve)
}

fn evidence<'a>(
    issued: &issuer::Issued,
    sources: &'a [policy::SourceProduct],
    product_files: &'a [policy::ProductFile],
    stable_compilation: &'a [policy::StableCompilation],
    suites: &'a [policy::SuiteClasspath],
) -> policy::Evidence<'a> {
    policy::Evidence {
        identity: issued.identity(),
        facts_identity: issued.facts_identity(),
        capture_identity: issued.capture_identity(),
        runtime_contract_identity: issued.runtime_contract_identity(),
        source_products_identity: issued.source_products_identity(),
        sources,
        product_files,
        stable_compilation,
        suites,
    }
}
pub struct Prepared {
    pub plan: policy::Plan,
    base: issuer::Issued,
    head: issuer::Issued,
    stable: stable_compilation::Issued,
    request: PathBuf,
    request_identity: ContentHash,
    files: Vec<PathBuf>,
}
impl Prepared {
    pub fn prepare(
        path: &Path,
        base_facts: &FactSnapshot,
        base_graph: &ProgramGraph,
        head_facts: &FactSnapshot,
        head_graph: &ProgramGraph,
        seeds: &ChangeSeeds,
        retained: &[&str],
        ordinary_compilation: bool,
    ) -> Result<Self> {
        let request = issuer::read_request(path)?;
        let scope = selector_select::classpath_absence_scope(
            base_facts, base_graph, head_facts, head_graph, seeds,
        )?;
        let contract = if ordinary_compilation {
            SelectionContract::owning_test_classpath_with_compilation()
        } else {
            SelectionContract::owning_test_classpath()
        };
        let base_sources = source_inventory(
            base_facts,
            base_graph,
            &scope.requested_paths,
            &seeds.base,
            &seeds.base_compile,
        )?;
        let head_sources = source_inventory(
            head_facts,
            head_graph,
            &scope.requested_paths,
            &seeds.head,
            &seeds.head_compile,
        )?;
        let mut base_provider = VerifiedProvider::admit_inventory(&request.base)?;
        let mut head_provider = VerifiedProvider::admit_inventory(&request.head)?;
        let stable = if ordinary_compilation {
            stable_compilation::issue(
                stable_compilation::Side {
                    facts: base_facts,
                    provider: &base_provider,
                    candidates: &base_sources,
                },
                stable_compilation::Side {
                    facts: head_facts,
                    provider: &head_provider,
                    candidates: &head_sources,
                },
                &scope.requested_paths,
                contract,
            )?
        } else {
            stable_compilation::Issued::default()
        };
        let inventory = |facts: &FactSnapshot,
                         source_union: &[FileId],
                         stable_rows: &[stable_compilation::StableCompilation],
                         execution: &[NodeId],
                         declarations: &[NodeId]| {
            let sources: Vec<_> = source_union
                .iter()
                .copied()
                .filter(|id| stable_rows.binary_search_by_key(id, |r| r.file).is_err())
                .collect();
            let paths: BTreeSet<_> = source_union.iter().map(|id| facts.path(*id)).collect();
            eprintln!(
                "{}",
                serde_json::json!({"stage":"classpath_absence_source_inventory",
                "revision":facts.text(facts.revision),"source_files":source_union.len(),"runtime_absence_sources":sources.len(),"stable_compilation_sources":stable_rows.len(),
                "execution_seeds":execution.len(),"declaration_seeds":declarations.len(),
                "paths":paths.iter().take(16).collect::<Vec<_>>(),"paths_truncated":paths.len()>16})
            );
            sources
        };
        let base_files = inventory(
            base_facts,
            &base_sources,
            stable.base(),
            &seeds.base,
            &seeds.base_compile,
        );
        let head_files = inventory(
            head_facts,
            &head_sources,
            stable.head(),
            &seeds.head,
            &seeds.head_compile,
        );
        let suites = |facts: &FactSnapshot| {
            (0..facts.suites.len())
                .map(|i| SuiteId(i as u32))
                .collect::<Vec<_>>()
        };
        let (base, head) = issuer::issue_paired(
            issuer::Side {
                facts: base_facts,
                provider: &mut base_provider,
                catalogue: &request.base_catalogue,
                source_files: &base_files,
                suites: &suites(base_facts),
            },
            issuer::Side {
                facts: head_facts,
                provider: &mut head_provider,
                catalogue: &request.head_catalogue,
                source_files: &head_files,
                suites: &suites(head_facts),
            },
            &scope.requested_paths,
            contract,
            issuer::Limits::default(),
        )?;
        let source_rows = |issued: &issuer::Issued| -> Vec<policy::SourceProduct> {
            issued
                .sources()
                .iter()
                .map(|s| policy::SourceProduct {
                    file: s.file,
                    owner_context: s.owner_context,
                    products_identity: s.products_identity,
                    product_count: s.product_count,
                })
                .collect()
        };
        let suite_rows =
            |issued: &issuer::Issued, facts: &FactSnapshot| -> Vec<policy::SuiteClasspath> {
                issued
                    .suites()
                    .iter()
                    .filter(|s| !retained.contains(&facts.text(facts.suites[s.suite.index()].name)))
                    .map(|s| policy::SuiteClasspath {
                        suite: s.suite,
                        owner_context: s.owner_context,
                        classpath_identity: s.classpath_identity,
                        source_products_identity: s.source_products_identity,
                        absence_identity: s.absence_identity,
                    })
                    .collect()
            };
        let bs = source_rows(&base);
        let hs = source_rows(&head);
        let product_files = |issued: &issuer::Issued| -> Vec<policy::ProductFile> {
            issued
                .product_files()
                .iter()
                .map(|row| policy::ProductFile {
                    file: row.file,
                    source_file: row.source_file,
                    owner_context: row.owner_context,
                    class_sha256: row.class_sha256,
                })
                .collect()
        };
        let bp = product_files(&base);
        let hp = product_files(&head);
        let stable_rows =
            |rows: &[stable_compilation::StableCompilation]| -> Vec<policy::StableCompilation> {
                rows.iter()
                    .map(|r| policy::StableCompilation {
                        file: r.file,
                        owner_context: r.owner_context,
                        source_sha256: r.source_sha256,
                        inputs_identity: r.inputs_identity,
                        paired_identity: r.paired_identity,
                    })
                    .collect()
            };
        let bc = stable_rows(stable.base());
        let hc = stable_rows(stable.head());
        let bt = suite_rows(&base, base_facts);
        let ht = suite_rows(&head, head_facts);
        let absent = |issued: &issuer::Issued| {
            issued
                .absent_sources()
                .iter()
                .map(|row| policy::AbsentSource {
                    path: row.path.clone(),
                    opposite_facts: row.opposite_facts,
                    absence_identity: row.absence_identity,
                })
                .collect::<Vec<_>>()
        };
        let plan = policy::Plan::new_with_source_absence(
            policy::Side {
                facts: base_facts,
                graph: base_graph,
                seeds: PlanSeeds {
                    execution: &seeds.base,
                    declarations: &seeds.base_compile,
                    unscoped: seeds.conservative,
                },
                evidence: evidence(&base, &bs, &bp, &bc, &bt),
            },
            policy::Side {
                facts: head_facts,
                graph: head_graph,
                seeds: PlanSeeds {
                    execution: &seeds.head,
                    declarations: &seeds.head_compile,
                    unscoped: seeds.conservative,
                },
                evidence: evidence(&head, &hs, &hp, &hc, &ht),
            },
            scope,
            contract,
            &absent(&base),
            &absent(&head),
        )?;
        let mut files = request.inputs;
        files.extend(
            base.inputs()
                .files
                .iter()
                .chain(&head.inputs().files)
                .chain(&stable.inputs().files)
                .map(|p| p.path.clone()),
        );
        files.sort();
        files.dedup();
        eprintln!(
            "{}",
            serde_json::json!({"stage":"classpath_absence","identity":plan.identity().to_string(),
            "base_source_products":bs.len(),"head_source_products":hs.len(),"base_absent_sources":base.absent_sources().len(),"head_absent_sources":head.absent_sources().len(),"base_certified_suites":bt.len(),"head_certified_suites":ht.len(),
            "base_product_files":bp.len(),"head_product_files":hp.len(),
            "base_stable_compilation":bc.len(),"head_stable_compilation":hc.len(),
            "base_denied_suites":base.denials().len(),"head_denied_suites":head.denials().len(),"contract_bits":contract.bits()})
        );
        Ok(Self {
            plan,
            base,
            head,
            stable,
            request: path.to_owned(),
            request_identity: request.identity,
            files,
        })
    }
    pub fn files(&self) -> &[PathBuf] {
        &self.files
    }
    pub fn physical_inputs(&self) -> [&issuer::PhysicalInputs; 3] {
        [self.base.inputs(), self.head.inputs(), self.stable.inputs()]
    }
    pub fn validate_outputs(
        &self,
        outputs: &[PathBuf],
        resolve: fn(&Path) -> Result<PathBuf>,
    ) -> Result<()> {
        let paths = self.files.iter().cloned().chain(
            self.physical_inputs()
                .into_iter()
                .flat_map(|input| input.paths()),
        );
        check_outputs(paths, outputs, resolve)
    }
    pub fn existing_roots(&self) -> Result<Vec<PathBuf>> {
        let mut paths = self.files.clone();
        for input in self.physical_inputs() {
            paths.extend(input.directories.iter().map(|p| p.path.clone()));
            for path in &input.absent {
                let mut existing = path.as_path();
                while !existing.exists() {
                    existing = existing.parent().ok_or("absent provider ancestor")?;
                }
                paths.push(existing.to_owned());
            }
        }
        Ok(paths)
    }
    pub fn revalidate(&self) -> Result<()> {
        if issuer::read_request(&self.request)?.identity != self.request_identity {
            return Err("classpath request changed during query".into());
        }
        self.base.revalidate()?;
        self.head.revalidate()?;
        self.stable.revalidate()?;
        Ok(())
    }
}

#[cfg(test)]
mod source_inventory_tests {
    use super::*;
    use selector_facts::{FactBuilder, FileRecord};
    use selector_graph::NodeRecord;

    #[test]
    fn all_effective_seed_sources_and_contexts_expand_inventory_without_changing_request() {
        let mut b = FactBuilder::new();
        let empty = b.intern("").unwrap();
        for (path, context, flags) in [
            (
                "Requested.scala",
                "requested",
                SOURCE_VERIFIED | SYNTAX_VERIFIED,
            ),
            ("Ledger.scala", "owner", SOURCE_VERIFIED | SYNTAX_VERIFIED),
            (
                "Ledger.scala",
                "consumer",
                SOURCE_VERIFIED | SYNTAX_VERIFIED,
            ),
            (
                "Unrelated.scala",
                "owner",
                SOURCE_VERIFIED | SYNTAX_VERIFIED,
            ),
            ("native.class", "owner", FILE_BINARY_SOURCE),
            ("Ledger.scala", "unknown", SOURCE_VERIFIED),
        ] {
            let path = b.intern(path).unwrap();
            let context = b.intern(context).unwrap();
            b.facts.files.push(FileRecord {
                path,
                context,
                source: empty,
                source_hash: ContentHash([7; 32]),
                revision: StrId::NONE,
                flags,
            });
        }
        let symbol = b.ensure_symbol("p/Ledger#changed().", FileId(1)).unwrap();
        b.facts.symbols[symbol.index()].file = FileId(1);
        let facts = b.finish().unwrap();
        let mut graph = ProgramGraph::default();
        graph.nodes.push(NodeRecord {
            symbol,
            file: FileId(4),
            body: BodyId::NONE,
            flags: 0,
        });
        graph.nodes.push(NodeRecord {
            symbol: SymbolId::NONE,
            file: FileId(3),
            body: BodyId::NONE,
            flags: 0,
        });
        let requested = vec!["Requested.scala".to_owned()];
        assert_eq!(
            source_inventory(&facts, &graph, &requested, &[], &[NodeId(0)]).unwrap(),
            [FileId(0), FileId(1), FileId(2), FileId(5)]
        );
        assert_eq!(
            source_inventory(&facts, &graph, &requested, &[NodeId(1)], &[]).unwrap(),
            [FileId(0), FileId(3)]
        );
        assert_eq!(requested, ["Requested.scala"]);
        assert!(source_inventory(&facts, &graph, &requested, &[NodeId(99)], &[]).is_err());
    }
}
