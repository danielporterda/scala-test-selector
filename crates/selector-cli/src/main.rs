//! Native extraction, build, query and report command orchestration.
mod classpath_absence;
mod diagnostics;
mod explain;
mod external_metadata;
mod inspect;
mod metadata_stage;
mod probe;
mod recording;
mod replay;
mod retention_precheck;
use selector_catalogue::{ArtifactRecord, CacheKey, Catalogue, RunStatus};
use selector_facts::FactSnapshot;
use selector_graph::ProgramGraph;
use selector_report::ReportSnapshots;
use selector_result::SelectionResult;
use selector_select::ChangeSeeds;
use selector_types::*;
use sha2::{Digest, Sha256};
use std::{
    collections::BTreeMap,
    fs,
    io::{self, BufRead, BufReader, BufWriter, Read, Write},
    path::{Path, PathBuf},
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
    time::Instant,
};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
static OUTPUT_SEQUENCE: AtomicU64 = AtomicU64::new(0);
const HELP: &str = "selector: Rust compiler-backed analysis\n\
  capture --input raw-capture-manifest.json --output documents.jsonl\n\
  runtime --repository DIR --revision COMMIT --catalogue-input suites.json --output runtime-manifest.json\n\
  compiler-inputs --contexts compiler-contexts.json.gz --compiler-input-root DIR --output inventory.json\n\
  syntax --input documents.jsonl[.gz] [--toolchain tool.json | --exporter ScalaSpans.scala --tool-cache DIR] --output syntax.jsonl\n\
  extract --input documents.jsonl[.gz] [--syntax syntax.jsonl] [--catalogue-input suites.json] --output facts.bin\n\
  metadata-authority --contexts compiler-contexts.json[.gz] --metadata-binary-map map.json --compiler-input-root DIR --input provider-requests.json --output authority.json\n\
  metadata-requests --input documents.jsonl[.gz] --contexts compiler-contexts.json[.gz] [--syntax syntax.jsonl] --output requests.json\n\
  enrich --facts facts.bin --binary-map binary-manifest.json --output enriched-facts.bin\n\
  binary-map --facts facts.bin --contexts compiler-contexts.json.gz --compiler-input-root DIR --output binary-manifest.json\n\
  build --facts facts.bin [--runtime-input runtime-manifest.json] --output graph.bin\n\
  query --head-facts facts.bin --head-graph graph.bin [--base-facts base.bin --base-graph base-graph.bin] --changed path --output result.json\n\
  retention-precheck --facts facts.bin --graph graph.bin --output guards.json (diagnostic; no solver or omissions)\n\
  run --head documents.jsonl[.gz] [--head-syntax syntax.jsonl] [--base base.jsonl.gz --base-syntax syntax.jsonl] --catalogue-input suites.json --changed path --artifacts DIR --output result.json\n\
  verify --facts facts.bin [--graph graph.bin]\n\
  explain --report result.json --suite fully.qualified.Suite\n\
  audit-changes --head-facts facts.bin --head-graph graph.bin --base-facts base.bin --base-graph base-graph.bin --changed path\n\
  producers prints stage producer identities without loading program inputs.\n\
  replay --receipt receipt.json [--validate-only] [--frozen-inputs] [--output result.json]\n\
  rerender --report result.json [--text] --output result.txt\n\
  inspect-checkpoint --facts facts.bin --graph graph.bin --checkpoint query.bin --output inventory.json\n\
  probe-root --facts facts.bin --graph graph.bin --root-node N [--receiver-symbol compiler/Symbol#] --output probe.json\n\
  Probe roots also accept --root-symbol compiler/Symbol# [--root-context CONTEXT] instead of --root-node.\n\
  transfer-replay --bundle DIR [--compare | --minimized-output DIR] --output replay.json\n\
  --changed may repeat; --changed-list reads newline-separated paths.\n\
  Query also accepts --seed exact/compiler/Symbol#method(). for head-only impact.\n\
  Shared: --workers N, --memory-budget BYTES, --max-contexts N, --max-steps N, --text.\n\
  Query: --plan-only, --all-roots, --max-context-variants N, --progress-jsonl PATH.\n\
  --assume-independent-suites explicitly assumes suites do not share hidden state; default is shared state.\n\
  --retain-suite EXACTNAME may repeat and keeps named timing/performance-sensitive suites runnable.\n\
  Paired query opt-in: --assume-owning-test-classpath --classpath-absence-request request.json requires independent suites.\n\
  --assume-ordinary-compilation additionally assumes unchanged source and declared compile inputs produce unchanged program behavior.\n\
  --prune-certified-classpath-roots schedules only roots without an exact paired absence proof.\n\
  Context variants: N exact argument frames per callee, exact receiver and callback code shape; then one joined frame.\n\
  --changed/--seed scope impact to the requested inputs; --whole-diff compares all captured source changes.\n\
  Resume: --checkpoint-dir DIR, --stop-after-round N, --resume-dir DIR.\n\
  Reports: compact decisions by default; --full-report or --full-evidence PATH retains context proofs.\n\
  Transfer export: --replay-bundle DIR --replay-node N [--replay-context N] [--replay-revision base|head].\n\
  Family export: add --replay-family [--replay-family-contexts N, maximum 64]; context selects an exact receiver family.\n\
  Inspection accepts transfer export flags and --inventory-rows N; it cannot resume or publish analysis.\n\
  Probe executes one root only; defaults: 1 worker, 64 MiB query state, 10k contexts, 1m operations. No exclusion authority.\n\
  Binary admission: --binary-memory-budget BYTES per revision (default 768 MiB).\n\
  Declared runtime: --platform-input manifest.json --platform-producer SHA require --contexts; optional for binary-map/enrich/run.\n\
  This supplies new pinned java.base bytes, not historical compiler-image or runtime-isolation proof; run base flags are independent.\n\
  --catalogue DB records immutable stage entries and request outcomes.\n\
  Metadata: --external-metadata manifest.json --external-metadata-producer SHA --metadata-binary-map map.json require --contexts and --compiler-input-root.\n\
  run accepts base equivalents of metadata flags, --binary-map/--base-binary-map and --runtime-input/--base-runtime-input.\n\
  Incomplete analysis is explicit and conservatively retains runnable suites.\n";

#[derive(Default, Clone)]
struct Args {
    command: String,
    values: BTreeMap<String, Vec<String>>,
    raw: Vec<String>,
    side: &'static str,
    recording: Option<Arc<std::sync::Mutex<recording::Recording>>>,
    events: Option<diagnostics::EventSink>,
}
impl Args {
    fn parse(input: impl IntoIterator<Item = String>) -> Result<Self> {
        let raw: Vec<String> = input.into_iter().collect();
        let mut it = raw.iter().cloned();
        let command = it.next().unwrap_or_else(|| "help".into());
        let mut values: BTreeMap<String, Vec<String>> = BTreeMap::new();
        while let Some(key) = it.next() {
            if !key.starts_with("--") {
                return Err(format!("unexpected positional argument {key:?}").into());
            }
            let name = &key[2..];
            if ![
                "input",
                "repository",
                "auxiliary-sources",
                "compiler-inventory-complete",
                "compiler-input-root",
                "base-compiler-input-root",
                "external-metadata",
                "external-metadata-producer",
                "metadata-binary-map",
                "base-external-metadata",
                "base-external-metadata-producer",
                "base-metadata-binary-map",
                "syntax",
                "toolchain",
                "exporter",
                "tool-cache",
                "syntax-cache",
                "reuse-syntax",
                "java-heap-bytes",
                "parallel-java-heap-bytes",
                "max-input-bytes",
                "max-output-bytes",
                "max-document-bytes",
                "batch-bytes",
                "catalogue-input",
                "base-catalogue-input",
                "contexts",
                "base-contexts",
                "runtime-input",
                "base-runtime-input",
                "summary-cache",
                "progress-jsonl",
                "stop-after-round",
                "checkpoint-dir",
                "resume-dir",
                "census-capacity",
                "census-stride",
                "current-local-audit",
                "audit-max-contexts",
                "audit-max-steps",
                "audit-memory-budget",
                "all-roots",
                "plan-only",
                "assume-independent-suites",
                "assume-owning-test-classpath",
                "assume-ordinary-compilation",
                "prune-certified-classpath-roots",
                "classpath-absence-request",
                "retain-suite",
                "whole-diff",
                "full-report",
                "full-evidence",
                "receipt",
                "validate-only",
                "frozen-inputs",
                "checkpoint",
                "inventory-rows",
                "root-node",
                "root-symbol",
                "root-context",
                "receiver-symbol",
                "max-checkpoint-bytes",
                "replay-family",
                "replay-family-contexts",
                "compare",
                "bundle",
                "minimized-output",
                "replay-bundle",
                "replay-node",
                "replay-context",
                "replay-revision",
                "min-calls",
                "min-reads",
                "target-node",
                "max-minimize-evaluations",
                "binary-map",
                "base-binary-map",
                "platform-input",
                "platform-producer",
                "base-platform-input",
                "base-platform-producer",
                "output",
                "facts",
                "graph",
                "head-facts",
                "head-graph",
                "base-facts",
                "base-graph",
                "head",
                "head-syntax",
                "base",
                "base-syntax",
                "changed",
                "changed-list",
                "seed",
                "artifacts",
                "workers",
                "memory-budget",
                "binary-memory-budget",
                "max-contexts",
                "max-context-variants",
                "max-steps",
                "catalogue",
                "revision",
                "base-revision",
                "report",
                "suite",
                "text",
                "help",
                "no-models",
            ]
            .contains(&name)
            {
                return Err(format!("unknown option {key}").into());
            }
            let value = if [
                "text",
                "help",
                "no-models",
                "compiler-inventory-complete",
                "all-roots",
                "plan-only",
                "assume-independent-suites",
                "assume-owning-test-classpath",
                "assume-ordinary-compilation",
                "prune-certified-classpath-roots",
                "whole-diff",
                "full-report",
                "validate-only",
                "frozen-inputs",
                "replay-family",
                "compare",
                "current-local-audit",
            ]
            .contains(&name)
            {
                String::new()
            } else {
                it.next()
                    .filter(|x| !x.starts_with("--"))
                    .ok_or_else(|| format!("{key} requires a value"))?
            };
            if !["changed", "seed", "retain-suite"].contains(&name) && values.contains_key(name) {
                return Err(format!("duplicate option {key}").into());
            }
            values.entry(name.to_owned()).or_default().push(value);
        }
        Ok(Self {
            command,
            values,
            raw,
            side: "head",
            recording: None,
            events: None,
        })
    }
    fn value(&self, name: &str) -> Option<&str> {
        self.values
            .get(name)
            .and_then(|x| x.first())
            .map(String::as_str)
    }
    fn path(&self, name: &str) -> Option<PathBuf> {
        self.value(name).map(PathBuf::from)
    }
    fn required(&self, name: &str) -> Result<PathBuf> {
        self.path(name)
            .ok_or_else(|| format!("--{name} is required").into())
    }
    fn flag(&self, name: &str) -> bool {
        self.values.contains_key(name)
    }
    fn suite_semantics(&self) -> SuiteSemantics {
        if self.flag("assume-independent-suites") {
            SuiteSemantics::Independent
        } else {
            SuiteSemantics::SharedState
        }
    }
    fn retained_suites(&self) -> Vec<&str> {
        let mut names: Vec<_> = self
            .values
            .get("retain-suite")
            .into_iter()
            .flatten()
            .map(String::as_str)
            .collect();
        names.sort_unstable();
        names.dedup();
        names
    }
    fn number(&self, name: &str, default: usize) -> Result<usize> {
        match self.value(name) {
            None => Ok(default),
            Some(v) => {
                let n = v.parse::<usize>()?;
                if n == 0 {
                    return Err(format!("--{name} must be positive").into());
                }
                Ok(n)
            }
        }
    }
    fn changed(&self) -> Result<Vec<String>> {
        let mut paths = self.values.get("changed").cloned().unwrap_or_default();
        if let Some(p) = self.path("changed-list") {
            for line in BufReader::new(fs::File::open(p)?).lines() {
                let line = line?;
                if !line.trim().is_empty() {
                    paths.push(line);
                }
            }
        }
        paths.sort();
        paths.dedup();
        Ok(paths)
    }
    fn solve_options(&self) -> Result<selector_solve::SolveOptions> {
        let mut options = selector_solve::SolveOptions::default();
        options.workers = self.workers()?;
        options.memory_budget_bytes = self.number("memory-budget", options.memory_budget_bytes)?;
        options.max_contexts = self.number("max-contexts", options.max_contexts)?;
        options.retain_context_evidence =
            self.flag("full-report") || self.path("full-evidence").is_some();
        if self.value("max-context-variants").is_some() {
            let variants = self.number("max-context-variants", 0)?;
            if variants == 0 {
                return Err("--max-context-variants must be positive".into());
            }
            options.context_policy = selector_solve::ContextPolicy::BoundedArguments {
                max_variants_per_receiver: variants,
            };
        }
        options.census.capacity = self
            .value("census-capacity")
            .map(str::parse::<usize>)
            .transpose()?
            .unwrap_or(options.census.capacity);
        if options.census.capacity > 65_536 {
            return Err("--census-capacity must be at most 65536".into());
        }
        options.census.evaluation_stride =
            self.number("census-stride", options.census.evaluation_stride as usize)? as u64;
        if options.census.evaluation_stride == 0 {
            return Err("--census-stride must be positive".into());
        }
        if let Some(value) = self.value("max-steps") {
            options.max_steps = value.parse()?;
            if options.max_steps == 0 {
                return Err("--max-steps must be positive".into());
            }
        }
        Ok(options)
    }
    fn workers(&self) -> Result<usize> {
        self.number(
            "workers",
            std::thread::available_parallelism().map_or(1, usize::from),
        )
    }
    fn validate(&self) -> Result<()> {
        if self.flag("prune-certified-classpath-roots")
            && (!self.flag("assume-owning-test-classpath") || self.flag("all-roots"))
        {
            return Err("--prune-certified-classpath-roots requires --assume-owning-test-classpath and conflicts with --all-roots".into());
        }
        if self.flag("assume-ordinary-compilation") && !self.flag("assume-owning-test-classpath") {
            return Err(
                "--assume-ordinary-compilation requires --assume-owning-test-classpath".into(),
            );
        }
        if self.flag("assume-owning-test-classpath")
            || self.path("classpath-absence-request").is_some()
        {
            if self.command != "query" {
                return Err("owning test classpath policy currently requires paired query".into());
            }
            if !self.flag("assume-owning-test-classpath") {
                return Err(
                    "--classpath-absence-request requires --assume-owning-test-classpath".into(),
                );
            }
            if self.suite_semantics() != SuiteSemantics::Independent {
                return Err(
                    "--assume-owning-test-classpath requires --assume-independent-suites".into(),
                );
            }
            self.required("classpath-absence-request")?;
            self.required("base-facts")?;
            self.required("base-graph")?;
            self.required("head-facts")?;
            self.required("head-graph")?;
            if self.flag("plan-only") {
                return Err("owning test classpath policy requires a paired query result; --plan-only is unsupported".into());
            }
            if self.values.contains_key("seed") {
                return Err("owning test classpath policy requires requested source changes; --seed is unsupported".into());
            }
        }
        if self.values.contains_key("retain-suite") {
            if !matches!(self.command.as_str(), "query" | "run") {
                return Err("--retain-suite requires query or run".into());
            }
            if self
                .retained_suites()
                .iter()
                .any(|name| name.is_empty() || name.chars().any(char::is_control))
            {
                return Err("--retain-suite requires an exact nonempty catalogue name".into());
            }
        }
        if self.flag("assume-independent-suites")
            && !matches!(self.command.as_str(), "query" | "run")
        {
            return Err("--assume-independent-suites requires query or run".into());
        }
        for prefix in ["", "base-"] {
            let input = format!("{prefix}platform-input");
            let producer = format!("{prefix}platform-producer");
            if self.values.contains_key(&input) || self.values.contains_key(&producer) {
                if !matches!(self.command.as_str(), "binary-map" | "enrich" | "run")
                    || (!prefix.is_empty()
                        && (self.command != "run" || self.path("base").is_none()))
                {
                    return Err("platform inputs require binary-map, enrich or the corresponding run revision".into());
                }
                self.required(&input)?;
                self.required(&format!("{prefix}contexts"))?;
                let expected = self
                    .value(&producer)
                    .ok_or("platform input requires its producer")?;
                if ContentHash::from_hex(expected)? == ContentHash::default() {
                    return Err("platform producer must be nonzero".into());
                }
                if self.command == "run" {
                    self.required(&format!("{prefix}binary-map"))?;
                }
            }
        }
        for prefix in ["", "base-"] {
            let flags = [
                format!("{prefix}external-metadata"),
                format!("{prefix}external-metadata-producer"),
                format!("{prefix}metadata-binary-map"),
            ];
            if flags.iter().any(|name| self.values.contains_key(name))
                && !(prefix.is_empty()
                    && self.command == "metadata-authority"
                    && self.values.contains_key("metadata-binary-map")
                    && !self.values.contains_key("external-metadata")
                    && !self.values.contains_key("external-metadata-producer"))
            {
                if !matches!(self.command.as_str(), "extract" | "run")
                    || (!prefix.is_empty()
                        && (self.command != "run" || self.path("base").is_none()))
                {
                    return Err(
                        "external metadata flags require extract or the corresponding run revision"
                            .into(),
                    );
                }
                for name in &flags {
                    self.required(name)?;
                }
                self.required(&format!("{prefix}contexts"))?;
                self.required(&format!("{prefix}compiler-input-root"))?;
                if ContentHash::from_hex(self.value(&flags[1]).unwrap())? == ContentHash::default()
                {
                    return Err("external metadata producer must be nonzero".into());
                }
            }
        }
        if self.command == "metadata-authority" {
            self.required("contexts")?;
            self.required("metadata-binary-map")?;
            self.required("compiler-input-root")?;
        }
        if self.command == "metadata-requests" {
            self.required("contexts")?;
        }

        if self.command == "probe-root" {
            probe::validate(self)?;
        }
        if self.command == "retention-precheck" {
            retention_precheck::validate(self)?;
        }
        if matches!(self.command.as_str(), "query" | "run") {
            self.solve_options()?;
        }
        if self.flag("whole-diff") {
            if !matches!(self.command.as_str(), "query" | "run" | "audit-changes") {
                return Err("--whole-diff requires query, run or audit-changes".into());
            }
            if ["changed", "changed-list", "seed"]
                .iter()
                .any(|name| self.values.contains_key(*name))
            {
                return Err(
                    "--whole-diff cannot be combined with --changed, --changed-list or --seed"
                        .into(),
                );
            }
            let paired = if self.command == "run" {
                self.path("base").is_some()
            } else {
                self.path("base-facts").is_some() && self.path("base-graph").is_some()
            };
            if !paired {
                return Err("--whole-diff requires paired base/head inputs".into());
            }
        }
        if self.path("replay-bundle").is_some() && self.value("replay-node").is_none() {
            return Err("--replay-node is required with --replay-bundle".into());
        }
        if self.flag("replay-family") && self.path("replay-bundle").is_none() {
            return Err("--replay-family requires --replay-bundle".into());
        }
        if let Some(side) = self.value("replay-revision") {
            if !matches!(side, "base" | "head") {
                return Err("--replay-revision must be base or head".into());
            }
        }
        if let Some(max) = self.value("replay-family-contexts") {
            let max = max.parse::<usize>()?;
            if !(1..=64).contains(&max) {
                return Err("--replay-family-contexts must be between 1 and 64".into());
            }
        }
        Ok(())
    }
}

fn hash_file(path: &Path) -> Result<ContentHash> {
    let mut h = Sha256::new();
    let mut input = fs::File::open(path)?;
    let mut buffer = [0; 128 * 1024];
    loop {
        let n = input.read(&mut buffer)?;
        if n == 0 {
            break;
        }
        h.update(&buffer[..n]);
    }
    Ok(ContentHash(h.finalize().into()))
}
fn stage_inputs(paths: &[Option<&Path>], extra: &[u8]) -> Result<ContentHash> {
    let mut h = Sha256::new();
    h.update(b"selector-stage-input/v1\0");
    for p in paths {
        match p {
            Some(p) => {
                h.update([1]);
                h.update(hash_file(p)?.0);
            }
            None => h.update([0]),
        }
    }
    h.update(extra);
    Ok(ContentHash(h.finalize().into()))
}
fn extract_producer() -> ContentHash {
    ContentHash::from_hex(env!("SELECTOR_EXTRACT_PRODUCER")).expect("build-time digest")
}
fn graph_producer() -> ContentHash {
    ContentHash::from_hex(env!("SELECTOR_GRAPH_PRODUCER")).expect("build-time digest")
}
fn binary_producer() -> ContentHash {
    ContentHash::from_hex(env!("SELECTOR_BINARY_PRODUCER")).expect("build-time digest")
}

fn producers() -> BTreeMap<String, String> {
    [
        ("extract", env!("SELECTOR_EXTRACT_PRODUCER")),
        ("metadata", env!("SELECTOR_METADATA_PRODUCER")),
        ("binary", env!("SELECTOR_BINARY_PRODUCER")),
        ("graph", env!("SELECTOR_GRAPH_PRODUCER")),
        ("planner", env!("SELECTOR_PLAN_PRODUCER")),
        ("query", env!("SELECTOR_QUERY_PRODUCER")),
        ("solve", env!("SELECTOR_SOLVE_PRODUCER")),
        ("report", env!("SELECTOR_REPORT_PRODUCER")),
    ]
    .into_iter()
    .map(|(name, hash)| (name.into(), hash.into()))
    .chain(std::iter::once((
        "inputs".into(),
        ContentHash(Sha256::digest(b"selector-pinned-native-inputs/facts-v2/graph-v1").into())
            .to_string(),
    )))
    .collect()
}

fn record_stage(
    args: &Args,
    id: &str,
    deps: &[&str],
    producer: &str,
    models: ContentHash,
    inputs: &[recording::StageFile<'_>],
    outputs: &[recording::StageFile<'_>],
) -> Result<()> {
    if let Some(recording) = &args.recording {
        recording
            .lock()
            .map_err(|_| "receipt writer lock poisoned")?
            .record_stage(id, deps, producer, models, inputs, outputs)?;
    }
    Ok(())
}

fn record_prepared(
    args: &Args,
    stage: &str,
    inputs: &[(&str, Option<&Path>)],
    output: &Path,
) -> Result<()> {
    if args.recording.is_none() {
        return Ok(());
    }
    let id = format!("{}.{}", args.side, stage);
    let prior = match stage {
        "enrich" => Some("extract"),
        "graph" => Some(if args.path("binary-map").is_some() {
            "enrich"
        } else {
            "extract"
        }),
        _ => None,
    };
    let dependency = prior
        .map(|prior| format!("{}.{}", args.side, prior))
        .or_else(|| {
            (stage == "extract" && args.path("external-metadata").is_some())
                .then(|| format!("{}.metadata", args.side))
        });
    let deps: Vec<_> = dependency.iter().map(String::as_str).collect();
    let inputs: Vec<_> = inputs
        .iter()
        .filter_map(|(role, path)| {
            path.map(|path| recording::StageFile {
                role,
                path,
                kind: None,
            })
        })
        .collect();
    record_stage(
        args,
        &id,
        &deps,
        match stage {
            "enrich" => "binary",
            "graph" => "graph",
            _ => "extract",
        },
        ContentHash::default(),
        &inputs,
        &[recording::StageFile {
            role: if stage == "graph" { "graph" } else { "facts" },
            path: output,
            kind: Some(if stage == "graph" {
                selector_artifacts::ArtifactKind::Graph
            } else {
                selector_artifacts::ArtifactKind::Facts
            }),
        }],
    )
}

fn record_query_inputs(args: &Args, has_base: bool) -> Result<()> {
    if args.recording.is_none() {
        return Ok(());
    }
    for side in if has_base {
        &["base", "head"][..]
    } else {
        &["head"][..]
    } {
        let facts = args.required(&format!("{side}-facts"))?;
        let graph = args.required(&format!("{side}-graph"))?;
        record_stage(
            args,
            &format!("{side}.inputs"),
            &[],
            "inputs",
            ContentHash::default(),
            &[],
            &[
                recording::StageFile {
                    role: "facts",
                    path: &facts,
                    kind: Some(selector_artifacts::ArtifactKind::Facts),
                },
                recording::StageFile {
                    role: "graph",
                    path: &graph,
                    kind: Some(selector_artifacts::ArtifactKind::Graph),
                },
            ],
        )?;
    }
    Ok(())
}

fn record_query_plan(
    args: &Args,
    has_base: bool,
    identity: ContentHash,
    absence: Option<&classpath_absence::Prepared>,
) -> Result<()> {
    if args.recording.is_none() {
        return Ok(());
    }
    let suffix = if args.command == "run" {
        "graph"
    } else {
        "inputs"
    };
    let head = format!("head.{suffix}");
    let base = format!("base.{suffix}");
    let mut dependencies = vec![head.as_str()];
    if has_base {
        dependencies.push(&base);
    }
    let paths = [
        ("changes", args.path("changed-list")),
        ("head_runtime", args.path("runtime-input")),
        ("base_runtime", args.path("base-runtime-input")),
    ];
    let mut inputs: Vec<_> = paths
        .iter()
        .filter_map(|(role, path)| {
            path.as_ref().map(|path| recording::StageFile {
                role,
                path,
                kind: None,
            })
        })
        .collect();
    let roles: Vec<_> = absence
        .into_iter()
        .flat_map(|a| a.files())
        .enumerate()
        .map(|(i, _)| format!("classpath_{i}"))
        .collect();
    if let Some(absence) = absence {
        let roots = absence.existing_roots()?;
        args.recording
            .as_ref()
            .expect("recording checked")
            .lock()
            .map_err(|_| "receipt writer lock poisoned")?
            .include_transitive_inputs(roots.iter().map(PathBuf::as_path))?;
        inputs.extend(absence.files().iter().zip(&roles).map(|(path, role)| {
            recording::StageFile {
                role,
                path,
                kind: None,
            }
        }));
    }
    record_stage(
        args,
        "query.plan",
        &dependencies,
        "query",
        identity,
        &inputs,
        &[],
    )?;
    if let Some(absence) = absence {
        args.recording
            .as_ref()
            .expect("recording checked")
            .lock()
            .map_err(|_| "receipt writer lock poisoned")?
            .record_classpath_inputs(&absence.physical_inputs())?;
    }
    Ok(())
}

fn record_query_outcome(args: &Args) -> Result<()> {
    if args.recording.is_none() {
        return Ok(());
    }
    let path = args.required("output")?;
    let outputs = [recording::StageFile {
        role: "outcome",
        path: &path,
        kind: None,
    }];
    record_stage(
        args,
        "query.solve",
        &["query.plan"],
        "solve",
        ContentHash::default(),
        &[],
        &outputs,
    )?;
    record_stage(
        args,
        "query.report",
        &["query.solve"],
        "report",
        ContentHash::default(),
        &outputs,
        &outputs,
    )
}

/// Compare outputs through existing ancestors so a relocated relative path or
/// symlink spelling does not accidentally count as a new destination.
fn replay_path_identity(path: &Path) -> Result<PathBuf> {
    let path = if path.is_absolute() {
        path.to_owned()
    } else {
        std::env::current_dir()?.join(path)
    };
    let mut ancestor = path.as_path();
    let mut tail = Vec::new();
    while !ancestor.exists() {
        tail.push(
            ancestor
                .components()
                .next_back()
                .ok_or("replay output ancestor")?
                .as_os_str()
                .to_owned(),
        );
        ancestor = ancestor.parent().ok_or("replay output ancestor")?;
    }
    let mut resolved = ancestor.canonicalize()?;
    for component in tail.into_iter().rev() {
        if component == ".." {
            resolved.pop();
        } else if component != "." {
            resolved.push(component);
        }
    }
    Ok(resolved)
}
/// A new report destination carries its recorded diagnostic outputs with it.
/// Inputs and shared caches keep their recorded bindings; explicit caller
/// destinations always take precedence.
fn relocate_replay_diagnostics(recorded: &mut Args, requested: &Args) -> Result<()> {
    let Some(output) = requested.path("output") else {
        return Ok(());
    };
    if let Some(old) = recorded.path("output") {
        if replay_path_identity(&old)? == replay_path_identity(&output)? {
            return Ok(());
        }
    }
    let suffixes = [
        ("progress-jsonl", ".progress.jsonl"),
        ("full-evidence", ".full-evidence.json"),
        ("checkpoint-dir", ".checkpoints"),
        ("replay-bundle", ".replay"),
    ];
    let protected = std::iter::once("output")
        .chain(suffixes.iter().map(|(name, _)| *name))
        .filter_map(|name| recorded.path(name))
        .map(|path| replay_path_identity(&path))
        .collect::<Result<Vec<_>>>()?;
    for (flag, suffix) in suffixes {
        if !recorded.flag(flag) || requested.flag(flag) {
            continue;
        }
        let base = output.file_name().ok_or("replay output has no filename")?;
        let mut sequence = 0usize;
        let destination = loop {
            let mut name = base.to_os_string();
            name.push(suffix);
            if sequence != 0 {
                name.push(format!(".{sequence}"));
            }
            let destination = output.with_file_name(name);
            if !protected.contains(&replay_path_identity(&destination)?) {
                break destination;
            }
            sequence = sequence
                .checked_add(1)
                .ok_or("replay diagnostic path sequence")?;
        };
        recorded.values.insert(
            flag.into(),
            vec![destination.to_string_lossy().into_owned()],
        );
    }
    Ok(())
}

fn execute_recorded(mut args: Args) -> Result<Option<Completion>> {
    args.validate()?;
    if let Some(request) = args.path("classpath-absence-request") {
        classpath_absence::preflight_outputs(
            &request,
            &classpath_output_paths(&args),
            replay_path_identity,
        )?;
    }
    args.events = Some(diagnostics::EventSink::new(
        args.path("progress-jsonl").as_deref(),
    )?);
    let _progress = stage_progress(&args, args.command.as_str(), "request");
    if let Some(path) = args
        .path("receipt")
        .filter(|_| matches!(args.command.as_str(), "run" | "query" | "extract"))
    {
        args.required("output")?;
        let path_flags = [
            "input",
            "head",
            "base",
            "syntax",
            "head-syntax",
            "base-syntax",
            "catalogue-input",
            "base-catalogue-input",
            "contexts",
            "base-contexts",
            "compiler-input-root",
            "base-compiler-input-root",
            "external-metadata",
            "metadata-binary-map",
            "base-external-metadata",
            "base-metadata-binary-map",
            "runtime-input",
            "base-runtime-input",
            "binary-map",
            "base-binary-map",
            "platform-input",
            "base-platform-input",
            "head-facts",
            "head-graph",
            "base-facts",
            "base-graph",
            "changed-list",
            "classpath-absence-request",
            "output",
            "artifacts",
            "catalogue",
            "summary-cache",
            "progress-jsonl",
            "checkpoint-dir",
            "resume-dir",
            "full-evidence",
            "receipt",
        ];
        let paths = args
            .raw
            .iter()
            .enumerate()
            .filter_map(|(index, value)| {
                value
                    .strip_prefix("--")
                    .filter(|name| path_flags.contains(name))
                    .and_then(|_| {
                        args.raw
                            .get(index + 1)
                            .map(|path| (index + 1, PathBuf::from(path)))
                    })
            })
            .collect();
        args.recording = Some(Arc::new(std::sync::Mutex::new(recording::Recording::new(
            args.raw.clone(),
            path,
            paths,
            producers(),
        )?)));
    }
    let result = execute(&args);
    if let Some(recording) = &args.recording {
        let mut writer = recording
            .lock()
            .map_err(|_| "receipt writer lock poisoned")?;
        let finish = if result.is_ok() {
            writer.finish()
        } else {
            writer.finish_failed()
        };
        if let Err(error) = finish {
            if result.is_ok() {
                return Err(error);
            }
            eprintln!("recording completed native stages failed: {error}");
        }
    }
    result
}
fn classpath_output_paths(args: &Args) -> Vec<PathBuf> {
    [
        "output",
        "receipt",
        "progress-jsonl",
        "summary-cache",
        "checkpoint-dir",
        "full-evidence",
        "replay-bundle",
        "artifacts",
    ]
    .into_iter()
    .filter_map(|name| args.path(name))
    .collect()
}

fn stage_progress(args: &Args, phase: &str, side: &str) -> diagnostics::StageProgress {
    diagnostics::StageProgress::start(args.events.clone().unwrap_or_default(), phase, side)
}

fn contexts_input(args: &Args, input: &Path) -> Option<PathBuf> {
    args.path("contexts").or_else(|| {
        input
            .parent()
            .map(|p| p.join("compiler-contexts.json.gz"))
            .filter(|p| p.is_file())
    })
}

fn extraction_options(
    args: &Args,
    input: &Path,
    catalogue_input: Option<&Path>,
    compiler_inputs: Option<Arc<selector_extract::compiler_inputs::CompilerInputs>>,
) -> Result<selector_extract::ExtractOptions> {
    let mut options = selector_extract::ExtractOptions {
        workers: args.workers()?,
        expected_revision: args.value("revision").map(str::to_owned),
        catalogue: catalogue_input.map(Path::to_owned),
        compiler_contexts: contexts_input(args, input),
        compiler_inputs,
        ..Default::default()
    };
    options.max_input_bytes =
        args.number("max-input-bytes", usize::try_from(options.max_input_bytes)?)? as u64;
    options.max_document_bytes = args.number("max-document-bytes", options.max_document_bytes)?;
    options.batch_bytes = args.number("batch-bytes", options.batch_bytes)?;
    Ok(options)
}

fn checked_metadata(args: &Args) -> Result<Option<metadata_stage::CheckedInputs>> {
    args.path("external-metadata")
        .map(|manifest| {
            metadata_stage::CheckedInputs::open(
                &manifest,
                ContentHash::from_hex(
                    args.value("external-metadata-producer")
                        .ok_or("--external-metadata-producer is required")?,
                )?,
                &args.required("metadata-binary-map")?,
                &args.required("contexts")?,
                &args.required("compiler-input-root")?,
            )
            .map_err(Into::into)
        })
        .transpose()
}

fn record_metadata_inputs(
    args: &Args,
    metadata: Option<&metadata_stage::CheckedInputs>,
) -> Result<()> {
    let Some(metadata) = metadata else {
        return Ok(());
    };
    let inputs: Vec<_> = metadata
        .artifact_inputs()
        .map(|(role, path)| recording::StageFile {
            role,
            path,
            kind: None,
        })
        .collect();
    if let Some(recording) = &args.recording {
        recording
            .lock()
            .map_err(|_| "receipt writer lock poisoned")?
            .include_transitive_inputs(inputs.iter().map(|input| input.path))?;
    }
    record_stage(
        args,
        &format!("{}.metadata", args.side),
        &[],
        "metadata",
        metadata.identity(),
        &inputs,
        &[],
    )
}

fn extract_file(
    args: &Args,
    input: &Path,
    syntax: Option<&Path>,
    catalogue_input: Option<&Path>,
    output: &Path,
    compiler_inputs: Option<Arc<selector_extract::compiler_inputs::CompilerInputs>>,
    metadata: Option<&metadata_stage::CheckedInputs>,
) -> Result<FactSnapshot> {
    let _progress = stage_progress(args, "extract", args.side);
    let options = extraction_options(args, input, catalogue_input, compiler_inputs)?;
    let mut facts = if let Some(metadata) = metadata {
        let prepared = selector_extract::prepare_capture(input, syntax, &options)?;
        let requests = prepared.metadata_requests(&Default::default())?;
        let admitted = metadata.admit(&requests)?;
        eprintln!(
            "{}",
            serde_json::json!({"stage":"metadata_admission","cache_hit":false,"requests":requests.len(),"methods":admitted.methods(),"identity":admitted.identity().to_string(),"compiler_normalizations":1})
        );
        selector_extract::finish_capture(prepared, Some(admitted))?
    } else {
        selector_extract::import_capture(input, syntax, &options)?
    };

    let recipes = selector_graph_build::source_recipes::augment_source_recipes(&mut facts)?;
    eprintln!(
        "{}",
        serde_json::json!({
            "stage": "source_recipes", "normalized_parents": recipes.normalized_parents,
        "normalized_initializers": recipes.normalized_initializers,
            "unsupported_alias_parents": recipes.unsupported_alias_parents,
            "parameter_accessors": recipes.parameter_accessors,
        })
    );
    facts.identity = selector_facts::codec::write(output, &facts)?;
    eprintln!(
        "{}",
        serde_json::json!({"stage":"extract","cache_hit":false,"files":facts.files.len(),"symbols":facts.symbols.len(),"occurrences":facts.occurrences.len(),"bodies":facts.bodies.len(),"issues":facts.issues.len(),"owned_bytes":facts.owned_bytes()})
    );
    Ok(facts)
}

fn admit_compiler_inputs(
    args: &Args,
    input: &Path,
) -> Result<Option<Arc<selector_extract::compiler_inputs::CompilerInputs>>> {
    let Some(root) = args.path("compiler-input-root") else {
        return Ok(None);
    };
    let _progress = stage_progress(args, "compiler_inputs", args.side);
    let contexts = contexts_input(args, input)
        .ok_or("--compiler-input-root requires a captured compiler context manifest")?;
    let mut limits = selector_extract::compiler_inputs::InventoryLimits::default();
    limits.workers = args.workers()?;
    let inputs = selector_extract::compiler_inputs::admit(&contexts, &root, &limits)?;
    eprintln!(
        "{}",
        serde_json::json!({
            "stage": "compiler_inputs", "identity": inputs.identity.to_string(),
            "products": inputs.receipt.products.len(),
            "verified": inputs.receipt.products.iter().filter(|p| p.status == selector_extract::compiler_inputs::InventoryStatus::Verified).count(),
        })
    );
    Ok(Some(Arc::new(inputs)))
}
fn build_graph(args: &Args, facts: &FactSnapshot, output: &Path) -> Result<ProgramGraph> {
    let runtime = args
        .path("runtime-input")
        .map(|path| selector_graph_build::runtime_inputs::load_runtime_manifest(&path, facts))
        .transpose()?;
    build_graph_with_runtime(args, facts, output, runtime.as_ref())
}
fn build_graph_with_runtime(
    args: &Args,
    facts: &FactSnapshot,
    output: &Path,
    runtime: Option<&selector_graph_build::runtime_inputs::OwnedRuntimeInputs>,
) -> Result<ProgramGraph> {
    let _progress = stage_progress(args, "build", args.side);
    let options = selector_graph_build::BuildOptions {
        workers: args.workers()?,
        include_models: !args.flag("no-models"),
    };
    if runtime.is_some() && !options.include_models {
        return Err("--runtime-input requires enabled runtime models".into());
    }
    let mut graph = match runtime {
        Some(runtime) => {
            selector_graph_build::build_with_runtime(facts, &options, &runtime.borrow())?
        }
        None => selector_graph_build::build(facts, &options)?,
    };
    verify_binding(facts, &graph)?;
    graph.identity = selector_graph::codec::write(output, &graph)?;
    eprintln!(
        "{}",
        serde_json::json!({"stage":"build","cache_hit":false,"nodes":graph.nodes.len(),"edges":graph.edges.len(),"issues":graph.issues.len(),"owned_bytes":graph.owned_bytes()})
    );
    Ok(graph)
}

fn verify_binding(facts: &FactSnapshot, graph: &ProgramGraph) -> Result<()> {
    facts.validate()?;
    graph.validate()?;
    if graph.facts_identity != facts.identity {
        return Err("graph belongs to a different fact snapshot".into());
    }
    if graph.symbol_nodes.len() != facts.symbols.len() {
        return Err("graph symbol inventory differs from facts".into());
    }
    let sym = |s: SymbolId| s.is_none() || s.index() < facts.symbols.len();
    let file = |f: FileId| f.is_none() || f.index() < facts.files.len();
    for n in &graph.nodes {
        if n.symbol.is_none()
            || !sym(n.symbol)
            || !file(n.file)
            || (!n.body.is_none() && n.body.index() >= facts.bodies.len())
        {
            return Err("graph node has invalid fact references".into());
        }
        if !n.body.is_none() {
            let body = &facts.bodies[n.body.index()];
            if body.symbol != n.symbol || body.file != n.file {
                return Err("graph body belongs to another symbol or file".into());
            }
        } else if facts.symbols[n.symbol.index()].file != n.file {
            return Err("graph node belongs to another symbol's file".into());
        }
    }
    for e in &graph.edges {
        if !sym(e.receiver)
            || (!e.occurrence.is_none() && e.occurrence.index() >= facts.occurrences.len())
            || (!e.operation.is_none() && e.operation.index() >= facts.operations.len())
        {
            return Err("graph edge has invalid fact references".into());
        }
        let source = &graph.nodes[e.source.index()];
        if !e.operation.is_none() && facts.operations[e.operation.index()].body != source.body {
            return Err("graph edge operation belongs to another source body".into());
        }
        if !e.occurrence.is_none() && facts.occurrences[e.occurrence.index()].file != source.file {
            let occurrence = &facts.occurrences[e.occurrence.index()];
            return Err(format!(
                "graph edge occurrence belongs to another source file: source node {} symbol {} body {} file {:?}; occurrence {} symbol {} file {:?}; edge {:?}",
                e.source.0,
                facts.symbol_name(source.symbol),
                source.body.0,
                facts.path(source.file),
                e.occurrence.0,
                facts.symbol_name(occurrence.symbol),
                facts.path(occurrence.file),
                e,
            ).into());
        }
    }
    for i in &graph.issues {
        if !sym(i.symbol)
            || !file(i.file)
            || (!i.detail.is_none() && i.detail.index() >= facts.strings.len())
        {
            return Err("graph issue has invalid fact references".into());
        }
    }
    for diagnostic in &graph.diagnostics {
        if !sym(diagnostic.symbol) || !file(diagnostic.file) {
            return Err("graph diagnostic has invalid fact references".into());
        }
    }
    Ok(())
}

/// Catalogue entries name immutable files, but files may have been removed or
/// damaged outside the catalogue. Preserve rejected bytes and rebuild from the
/// same hash-bound inputs. Registration still enforces the immutable stage key.
fn admit_cached<T>(
    record: &ArtifactRecord,
    stage: &str,
    read: impl FnOnce() -> Result<T>,
) -> Result<Option<T>> {
    match read() {
        Ok(value) => Ok(Some(value)),
        Err(error) => {
            if matches!(error.downcast_ref::<Error>(), Some(Error::Limit(_))) {
                return Err(error);
            }
            let mut rejected = None;
            if record.path.try_exists()? {
                for _ in 0..64 {
                    let mut name = record
                        .path
                        .file_name()
                        .ok_or("cached artifact filename")?
                        .to_os_string();
                    name.push(format!(
                        ".rejected-{}-{}",
                        std::process::id(),
                        OUTPUT_SEQUENCE.fetch_add(1, Ordering::Relaxed)
                    ));
                    let path = record.path.with_file_name(name);
                    if path.try_exists()? {
                        continue;
                    }
                    match fs::rename(&record.path, &path) {
                        Ok(()) => {
                            rejected = Some(path);
                            break;
                        }
                        Err(error) if error.kind() == io::ErrorKind::NotFound => break,
                        Err(error) => return Err(error.into()),
                    }
                }
                if record.path.try_exists()? {
                    return Err("cannot preserve rejected cached artifact".into());
                }
            }
            eprintln!(
                "{}",
                serde_json::json!({"stage":stage,"cache_hit":false,
                "cache_reason":if rejected.is_some(){"artifact_rejected"}else{"artifact_missing"},
                "artifact":record.path,"preserved_at":rejected,"detail":error.to_string()})
            );
            Ok(None)
        }
    }
}

fn cached_extract(
    args: &Args,
    catalogue: &mut Catalogue,
    dir: &Path,
    input: &Path,
    syntax: Option<&Path>,
    catalogue_input: Option<&Path>,
) -> Result<FactSnapshot> {
    let _progress = stage_progress(args, "fact_preparation", args.side);
    let contexts = contexts_input(args, input);
    let metadata = checked_metadata(args)?;
    record_metadata_inputs(args, metadata.as_ref())?;
    let compiler_inputs = admit_compiler_inputs(args, input)?;
    if let (Some(recording), Some(inputs), Some(root), Some(contexts)) = (
        &args.recording,
        compiler_inputs.as_ref(),
        args.path("compiler-input-root"),
        contexts.as_deref(),
    ) {
        recording
            .lock()
            .map_err(|_| "receipt writer lock poisoned")?
            .record_compiler_inputs(args.side, contexts, &root, inputs.identity)?;
    }
    let mut extra = Sha256::new();
    extra.update(args.value("revision").unwrap_or("").as_bytes());
    extra.update([u8::from(compiler_inputs.is_some())]);
    if let Some(inputs) = &compiler_inputs {
        extra.update(inputs.identity.0);
    }
    if let Some(metadata) = &metadata {
        extra.update(b"\0external-metadata-inputs/v1\0");
        extra.update(metadata.identity().0);
    }
    let inputs = stage_inputs(
        &[Some(input), syntax, catalogue_input, contexts.as_deref()],
        &extra.finalize(),
    )?;
    let producer = extract_producer();
    let key = CacheKey {
        stage: "extract/v2",
        inputs: inputs.0,
        producer: producer.0,
    };
    if let Some(record) = catalogue.lookup(key)? {
        if let Some(facts) = admit_cached(&record, "extract", || {
            let facts = selector_facts::codec::read(&record.path)?;
            if facts.identity.0 != record.identity {
                return Err("catalogue fact identity mismatch".into());
            }
            Ok(facts)
        })? {
            record_prepared(
                args,
                "extract",
                &[
                    ("documents", Some(input)),
                    ("syntax", syntax),
                    ("catalogue", catalogue_input),
                    ("contexts", contexts.as_deref()),
                ],
                &record.path,
            )?;
            eprintln!(
                "{}",
                serde_json::json!({"stage":"extract","cache_hit":true,"files":facts.files.len(),"symbols":facts.symbols.len(),"occurrences":facts.occurrences.len(),"bodies":facts.bodies.len(),"issues":facts.issues.len(),"owned_bytes":facts.owned_bytes()})
            );
            return Ok(facts);
        }
    }
    let output = dir.join(format!("facts-{inputs}-{producer}.bin"));
    let facts = extract_file(
        args,
        input,
        syntax,
        catalogue_input,
        &output,
        compiler_inputs,
        metadata.as_ref(),
    )?;
    catalogue.register(
        key,
        ArtifactRecord {
            identity: facts.identity.0,
            kind: 1,
            path: fs::canonicalize(&output)?,
            bytes: fs::metadata(&output)?.len(),
        },
    )?;
    record_prepared(
        args,
        "extract",
        &[
            ("documents", Some(input)),
            ("syntax", syntax),
            ("catalogue", catalogue_input),
            ("contexts", contexts.as_deref()),
        ],
        &output,
    )?;
    Ok(facts)
}
fn cached_graph(
    args: &Args,
    catalogue: &mut Catalogue,
    dir: &Path,
    facts: &FactSnapshot,
) -> Result<ProgramGraph> {
    let _progress = stage_progress(args, "graph_preparation", args.side);
    let runtime = args
        .path("runtime-input")
        .map(|path| selector_graph_build::runtime_inputs::load_runtime_manifest(&path, facts))
        .transpose()?;
    let mut hash = Sha256::new();
    hash.update(facts.identity.0);
    hash.update([u8::from(!args.flag("no-models"))]);
    hash.update(
        runtime
            .as_ref()
            .map_or(ContentHash::default(), |input| input.identity)
            .0,
    );
    let inputs = ContentHash(hash.finalize().into());
    let producer = graph_producer();
    let key = CacheKey {
        stage: "graph/v1",
        inputs: inputs.0,
        producer: producer.0,
    };
    if let Some(record) = catalogue.lookup(key)? {
        if let Some(graph) = admit_cached(&record, "build", || {
            let graph = selector_graph::codec::read_bound(&record.path, facts.identity)?;
            if graph.identity.0 != record.identity {
                return Err("catalogue graph identity mismatch".into());
            }
            if graph.runtime_identity
                != runtime
                    .as_ref()
                    .map_or(ContentHash::default(), |input| input.identity)
            {
                return Err("catalogue graph runtime identity mismatch".into());
            }
            verify_binding(facts, &graph)?;
            Ok(graph)
        })? {
            record_prepared(
                args,
                "graph",
                &[("runtime", args.path("runtime-input").as_deref())],
                &record.path,
            )?;
            eprintln!(
                "{}",
                serde_json::json!({"stage":"build","cache_hit":true,"nodes":graph.nodes.len(),"edges":graph.edges.len(),"issues":graph.issues.len(),"owned_bytes":graph.owned_bytes()})
            );
            return Ok(graph);
        }
    }
    let output = dir.join(format!("graph-{inputs}-{producer}.bin"));
    let graph = build_graph_with_runtime(args, facts, &output, runtime.as_ref())?;
    catalogue.register(
        key,
        ArtifactRecord {
            identity: graph.identity.0,
            kind: 2,
            path: fs::canonicalize(&output)?,
            bytes: fs::metadata(&output)?.len(),
        },
    )?;
    record_prepared(
        args,
        "graph",
        &[("runtime", args.path("runtime-input").as_deref())],
        &output,
    )?;
    Ok(graph)
}

fn cached_snapshot(
    args: &Args,
    catalogue: &mut Catalogue,
    dir: &Path,
    input: &Path,
    syntax: Option<&Path>,
    suites: Option<&Path>,
) -> Result<(FactSnapshot, ProgramGraph)> {
    let facts = cached_extract(args, catalogue, dir, input, syntax, suites)?;
    let facts = cached_enrich(args, catalogue, dir, facts)?;
    let graph = cached_graph(args, catalogue, dir, &facts)?;
    Ok((facts, graph))
}

fn native_class_metrics<'a>(
    contexts: impl Iterator<Item = selector_graph_build::binary_inputs::BinaryContextMetrics<'a>>,
) -> serde_json::Value {
    let mut rows = Vec::new();
    let (mut count, mut found, mut unknown, mut bytes, mut requests) =
        (0usize, 0usize, 0usize, 0usize, 0u64);
    let (mut deferred, mut derived) = (0u64, 0usize);
    let (mut released, mut received, mut retried, mut method_guards, mut scoped_dispatch) =
        (0usize, 0usize, 0usize, 0usize, 0usize);
    let (mut trusted_models, mut trusted_fallbacks, mut receiver_dispatch) =
        (0usize, 0usize, 0usize);
    for context in contexts {
        count += 1;
        found = found.saturating_add(context.found);
        unknown = unknown.saturating_add(context.unknown);
        bytes = bytes.saturating_add(context.retained_bytes);
        requests = requests.saturating_add(context.requests);
        deferred = deferred.saturating_add(context.deferred_admissions);
        derived = derived.saturating_add(context.derived_methods);
        released = released.saturating_add(context.method_slots_released);
        received = received.saturating_add(context.method_slots_received);
        retried = retried.saturating_add(context.retried_callers);
        method_guards = method_guards.saturating_add(context.method_guard_rows);
        scoped_dispatch = scoped_dispatch.saturating_add(context.scoped_dispatch_rows);
        receiver_dispatch = receiver_dispatch.saturating_add(context.receiver_dispatch_rows);
        trusted_models = trusted_models.saturating_add(context.trusted_runtime_models);
        trusted_fallbacks =
            trusted_fallbacks.saturating_add(context.trusted_runtime_model_fallbacks);
        if rows.len() < 64 {
            let end = context
                .context
                .char_indices()
                .nth(256)
                .map_or(context.context.len(), |(at, _)| at);
            rows.push(serde_json::json!({
                "context": &context.context[..end], "context_truncated": end != context.context.len(),
                "found":context.found, "unknown":context.unknown,
                "retained_class_bytes":context.retained_bytes, "requests":context.requests,
                "phase":context.phase, "active_method":context.active_method.0,
                "pending_methods":context.pending_methods,
                "deferred_admissions":context.deferred_admissions,
                "derived_methods":context.derived_methods,
                "method_slots_released":context.method_slots_released,
                "method_slots_received":context.method_slots_received,
                "retried_callers":context.retried_callers,
                "method_guard_rows":context.method_guard_rows,
                "scoped_dispatch_rows":context.scoped_dispatch_rows,
                "receiver_dispatch_rows":context.receiver_dispatch_rows,
                "trusted_runtime_models":context.trusted_runtime_models,
                "trusted_runtime_model_fallbacks":context.trusted_runtime_model_fallbacks,
            }));
        }
    }
    serde_json::json!({
        "contexts":count, "found":found, "unknown":unknown,
        "retained_class_bytes":bytes, "requests":requests,
        "deferred_admissions":deferred, "derived_methods":derived,
        "method_slots_released":released, "method_slots_received":received,
        "retried_callers":retried, "method_guard_rows":method_guards,
        "scoped_dispatch_rows":scoped_dispatch,
        "receiver_dispatch_rows":receiver_dispatch,
        "receiver_dispatch_rows_definition":"published receiver-only wildcard frontier rows; uncertainty is retained at matching dispatch, not an unconditional class guard",
        "trusted_runtime_models":trusted_models, "trusted_runtime_model_fallbacks":trusted_fallbacks,
        "trusted_runtime_models_definition":"final published trusted runtime recipes; retry attempts are not counted",
        "trusted_runtime_model_fallbacks_definition":"recognized exact trusted runtime API contracts whose model was declined; ordinary effects and guards remain",
        "method_guard_rows_definition":"published typed method-budget guard rows after per-node dedup; not all blocked calls or current runtime guards",
        "scoped_dispatch_rows_definition":"published receiver/contract deferred-dispatch rows; missing coverage retained at matching calls, not removed uncertainty",
        "deferred_admissions_definition":"historical admission refusal attempts, including retries; not a remaining frontier count",
        "retained_class_bytes_definition":"sum of context-local class lengths; shared storage may be counted more than once",
        "sample_complete":rows.len() == count, "sample":rows,
    })
}

fn enrich_facts(
    mut facts: FactSnapshot,
    mut inputs: selector_graph_build::binary_inputs::OwnedBinaryInputs,
    output: &Path,
) -> Result<FactSnapshot> {
    let input_bytes = inputs.retained_input_bytes();
    let counts = |facts: &FactSnapshot| {
        facts
            .operations
            .iter()
            .fold((0usize, 0usize), |(macros, clauses), operation| {
                (
                    macros + usize::from(operation.flags & OP_MACRO_EXPANSION != 0),
                    clauses + usize::from(operation.flags & OP_SYNTHETIC_PARAMETER_APPLY != 0),
                )
            })
    };
    let (macro_count, parameter_apply_count) = counts(&facts);
    if let Err(error) =
        selector_graph_build::binary_inputs::augment_binary_facts(&mut facts, &mut inputs)
    {
        let envelopes = inputs.envelope_metrics();
        eprintln!(
            "{}",
            serde_json::json!({
                "stage":"enrich_failed", "error":error.to_string(), "snapshot_published":false,
                "admitted_input_bytes":input_bytes,
                "partial_symbols":facts.symbols.len(), "partial_bodies":facts.bodies.len(),
                "partial_operations":facts.operations.len(), "partial_issues":facts.issues.len(),
                "native_class_cache":native_class_metrics(inputs.context_metrics()),
                "native_effect_envelopes":{
                    "decoded_methods":envelopes.decoded_methods,
                    "decoded_instructions":envelopes.decoded_instructions,
                    "decode_cache_hits":envelopes.decode_cache_hits,
                    "fallback_methods":envelopes.fallback_methods,
                    "complete_local_envelopes":envelopes.complete_local_envelopes,
                    "open_envelopes":envelopes.open_envelopes,
                    "malformed_rejects":envelopes.malformed_rejects,
                    "budget_rejects":envelopes.budget_rejects,
                    "retained_decode_bytes":envelopes.retained_decode_bytes,
                }
            })
        );
        return Err(error.into());
    }
    let (unresolved_macros, retained_parameter_applies) = counts(&facts);
    let envelopes = inputs.envelope_metrics();
    let classes = native_class_metrics(inputs.context_metrics());
    // Classpath archives belong to admission/enrichment, not snapshot encoding.
    drop(inputs);
    selector_extract::project_result_bounds(&mut facts)?;
    facts.identity = selector_facts::codec::write(output, &facts)?;
    eprintln!(
        "{}",
        serde_json::json!({"stage":"enrich","cache_hit":false,"files":facts.files.len(),"symbols":facts.symbols.len(),"bodies":facts.bodies.len(),"issues":facts.issues.len(),"owned_bytes":facts.owned_bytes(),"admitted_input_bytes":input_bytes,
        "modeled_macros":macro_count.saturating_sub(unresolved_macros),"unresolved_macros":unresolved_macros,
        "folded_parameter_apply_stages":parameter_apply_count.saturating_sub(retained_parameter_applies),
        "retained_parameter_apply_stages":retained_parameter_applies,
        "native_class_cache":classes,
        "native_effect_envelopes":{
            "decoded_methods":envelopes.decoded_methods,
            "decoded_instructions":envelopes.decoded_instructions,
            "decode_cache_hits":envelopes.decode_cache_hits,
            "fallback_methods":envelopes.fallback_methods,
            "complete_local_envelopes":envelopes.complete_local_envelopes,
            "open_envelopes":envelopes.open_envelopes,
            "malformed_rejects":envelopes.malformed_rejects,
            "budget_rejects":envelopes.budget_rejects,
            "retained_decode_bytes":envelopes.retained_decode_bytes
        }})
    );
    Ok(facts)
}

fn binary_options(args: &Args) -> Result<selector_graph_build::binary_inputs::BinaryInputOptions> {
    let mut options = selector_graph_build::binary_inputs::BinaryInputOptions::default();
    options.workers = args.workers()?;
    options.max_retained_bytes = args.number("binary-memory-budget", options.max_retained_bytes)?;
    Ok(options)
}

fn platform_options(
    args: &Args,
) -> Result<Option<selector_graph_build::binary_platform::PlatformOptions>> {
    args.path("platform-input")
        .map(|manifest| {
            Ok(selector_graph_build::binary_platform::PlatformOptions {
                manifest,
                contexts: args.required("contexts")?,
                producer: ContentHash::from_hex(
                    args.value("platform-producer")
                        .ok_or("platform producer is required")?,
                )?,
            })
        })
        .transpose()
}

fn record_binary_prepared(
    args: &Args,
    binary_map: &Path,
    platform: &[PathBuf],
    output: &Path,
) -> Result<()> {
    let roles = [
        "platform_manifest",
        "platform_contexts",
        "platform_launcher",
        "platform_release",
        "platform_modules",
        "platform_archive",
        "platform_inventory",
    ];
    if platform.len() != 0 && platform.len() != roles.len() {
        return Err("platform receipt inputs".into());
    }
    if let Some(recording) = &args.recording {
        recording
            .lock()
            .map_err(|_| "receipt writer lock poisoned")?
            .include_transitive_inputs(platform.iter().map(PathBuf::as_path))?;
    }
    let mut files = vec![("binary-map", Some(binary_map))];
    files.extend(
        roles
            .iter()
            .zip(platform)
            .map(|(&role, path)| (role, Some(path.as_path()))),
    );
    record_prepared(args, "enrich", &files, output)
}

fn cached_enrich(
    args: &Args,
    catalogue: &mut Catalogue,
    dir: &Path,
    facts: FactSnapshot,
) -> Result<FactSnapshot> {
    let _progress = stage_progress(args, "binary_preparation", args.side);
    let Some(path) = args.path("binary-map") else {
        return Ok(facts);
    };
    // Admission checks the actual ordered classpath even on a derived-stage hit.
    let binary = selector_graph_build::binary_inputs::load_binary_manifest_with_platform(
        &path,
        &facts,
        &binary_options(args)?,
        platform_options(args)?.as_ref(),
    )?;
    let mut hash = Sha256::new();
    hash.update(b"selector-binary-facts/v2\0");
    hash.update(facts.identity.0);
    hash.update(binary.identity.0);
    let inputs = ContentHash(hash.finalize().into());
    let producer = binary_producer();
    let key = CacheKey {
        stage: "binary-facts/v2",
        inputs: inputs.0,
        producer: producer.0,
    };
    if let Some(record) = catalogue.lookup(key)? {
        if let Some(loaded) = admit_cached(&record, "enrich", || {
            let loaded = selector_facts::codec::read(&record.path)?;
            if loaded.identity.0 != record.identity {
                return Err("catalogue binary fact identity mismatch".into());
            }
            Ok(loaded)
        })? {
            record_binary_prepared(args, &path, binary.platform_input_files(), &record.path)?;
            eprintln!(
                "{}",
                serde_json::json!({"stage":"enrich","cache_hit":true,"files":loaded.files.len(),"symbols":loaded.symbols.len(),"bodies":loaded.bodies.len(),"issues":loaded.issues.len(),"owned_bytes":loaded.owned_bytes()})
            );
            return Ok(loaded);
        }
    }
    let output = dir.join(format!("binary-facts-{inputs}-{producer}.bin"));
    let platform_files = binary.platform_input_files().to_vec();
    let facts = enrich_facts(facts, binary, &output)?;
    catalogue.register(
        key,
        ArtifactRecord {
            identity: facts.identity.0,
            kind: 1,
            path: fs::canonicalize(&output)?,
            bytes: fs::metadata(&output)?.len(),
        },
    )?;
    record_binary_prepared(args, &path, &platform_files, &output)?;
    Ok(facts)
}

/// Base and head have independent producers. Partition the requested CPU budget
/// between them; catalogue transactions remain short stage publications.
fn prepare_snapshots(
    args: &Args,
    catalogue: &mut Catalogue,
    catalogue_file: &Path,
    dir: &Path,
    head: &Path,
    base: Option<&Path>,
) -> Result<(
    (FactSnapshot, ProgramGraph),
    Option<(FactSnapshot, ProgramGraph)>,
)> {
    let suites = args.path("catalogue-input");
    let base_suites = args.path("base-catalogue-input");
    let head_syntax = args.path("head-syntax");
    let base_syntax = args.path("base-syntax");
    let mut base_args = args.clone();
    base_args.side = "base";
    base_args.values.remove("contexts");
    base_args.values.remove("runtime-input");
    base_args.values.remove("binary-map");
    base_args.values.remove("compiler-input-root");
    if let Some(root) = args.value("base-compiler-input-root") {
        base_args
            .values
            .insert("compiler-input-root".into(), vec![root.to_owned()]);
    }
    if let Some(path) = args.value("base-binary-map") {
        base_args
            .values
            .insert("binary-map".into(), vec![path.to_owned()]);
    }
    if let Some(path) = args.value("base-runtime-input") {
        base_args
            .values
            .insert("runtime-input".into(), vec![path.to_owned()]);
    }
    for name in [
        "external-metadata",
        "external-metadata-producer",
        "metadata-binary-map",
        "platform-input",
        "platform-producer",
    ] {
        base_args.values.remove(name);
        if let Some(value) = args.value(&format!("base-{name}")) {
            base_args.values.insert(name.into(), vec![value.to_owned()]);
        }
    }
    base_args.values.remove("revision");
    if let Some(revision) = args.value("base-revision") {
        base_args
            .values
            .insert("revision".into(), vec![revision.to_owned()]);
    }
    if let Some(contexts) = args.value("base-contexts") {
        base_args
            .values
            .insert("contexts".into(), vec![contexts.to_owned()]);
    }
    let workers = args.workers()?;
    if let Some(base) = base.filter(|_| workers > 1) {
        let mut head_args = args.clone();
        head_args
            .values
            .insert("workers".into(), vec![(workers - workers / 2).to_string()]);
        base_args
            .values
            .insert("workers".into(), vec![(workers / 2).to_string()]);
        std::thread::scope(|scope| {
            let job = scope.spawn(|| -> std::result::Result<_, String> {
                (|| {
                    let mut own_catalogue = Catalogue::open(catalogue_file)?;
                    cached_snapshot(
                        &base_args,
                        &mut own_catalogue,
                        dir,
                        base,
                        base_syntax.as_deref(),
                        base_suites.as_deref().or(suites.as_deref()),
                    )
                })()
                .map_err(|e: Box<dyn std::error::Error>| e.to_string())
            });
            let head_result = cached_snapshot(
                &head_args,
                catalogue,
                dir,
                head,
                head_syntax.as_deref(),
                suites.as_deref(),
            );
            let base_result = job.join().map_err(|_| "base snapshot worker panicked")?;
            Ok((head_result?, Some(base_result?)))
        })
    } else {
        let head = cached_snapshot(
            args,
            catalogue,
            dir,
            head,
            head_syntax.as_deref(),
            suites.as_deref(),
        )?;
        let base = base
            .map(|path| {
                cached_snapshot(
                    &base_args,
                    catalogue,
                    dir,
                    path,
                    base_syntax.as_deref(),
                    base_suites.as_deref().or(suites.as_deref()),
                )
            })
            .transpose()?;
        Ok((head, base))
    }
}

fn bound_runtime_input(
    path: Option<PathBuf>,
    facts: &FactSnapshot,
    graph: &ProgramGraph,
) -> Result<Option<selector_graph_build::runtime_inputs::OwnedRuntimeInputs>> {
    path.map(|path| {
        let inputs = selector_graph_build::runtime_inputs::load_runtime_manifest(&path, facts)?;
        if inputs.identity != graph.runtime_identity {
            return Err(format!(
                "runtime manifest {} does not match graph runtime identity {} (manifest {})",
                path.display(),
                graph.runtime_identity,
                inputs.identity
            )
            .into());
        }
        Ok(inputs)
    })
    .transpose()
}

struct PreparedQuery {
    seeds: ChangeSeeds,
    base_guards: Vec<NodeId>,
    head_guards: Vec<NodeId>,
    source_paths: Vec<String>,
    source_conservative: bool,
    auxiliary_conservative: bool,
    elapsed_ns: u128,
}

fn prepare_query(
    args: &Args,
    base_facts: &FactSnapshot,
    base_graph: &ProgramGraph,
    head_facts: &FactSnapshot,
    head_graph: &ProgramGraph,
    has_base: bool,
) -> Result<PreparedQuery> {
    let _progress = stage_progress(args, "query_prepare", "request");
    let prepare_start = Instant::now();
    verify_binding(base_facts, base_graph)?;
    verify_binding(head_facts, head_graph)?;
    if head_facts.suites.is_empty() {
        return Err(
            "no captured runnable suites: supply --catalogue-input during extraction".into(),
        );
    }
    let changed = args.changed()?;
    let paths: Vec<_> = changed.iter().map(String::as_str).collect();
    let base_runtime = if has_base {
        bound_runtime_input(args.path("base-runtime-input"), base_facts, base_graph)?
    } else {
        None
    };
    let head_runtime = bound_runtime_input(args.path("runtime-input"), head_facts, head_graph)?;
    let whole_runtime = args.flag("whole-diff").then(|| {
        selector_graph_build::runtime_inputs::runtime_input_changes(
            base_runtime.as_ref(),
            head_runtime.as_ref(),
        )
    });
    let runtime_paths: Vec<_> = whole_runtime.as_ref().map_or_else(
        || paths.clone(),
        |delta| delta.changed_paths.iter().map(String::as_str).collect(),
    );
    let runtime_authority_changed = whole_runtime.as_ref().is_some_and(|delta| {
        delta.authority_changed
            || (!delta.changed_paths.is_empty()
                && (base_runtime.is_none() || head_runtime.is_none()))
            || (base_graph.runtime_identity != ContentHash::default() && base_runtime.is_none())
            || (head_graph.runtime_identity != ContentHash::default() && head_runtime.is_none())
    });
    let auxiliary = match (&base_runtime, &head_runtime) {
        (Some(base), Some(head)) => {
            Some(selector_graph_build::runtime_inputs::runtime_change_seeds(
                base_facts,
                base_graph,
                base,
                head_facts,
                head_graph,
                head,
                &runtime_paths,
            )?)
        }
        _ => None,
    };
    let source_paths: Vec<_> = paths
        .iter()
        .copied()
        .filter(|path| {
            auxiliary
                .as_ref()
                .is_none_or(|aux| !aux.covered_paths.iter().any(|covered| covered == path))
        })
        .collect();
    let mut seeds = if has_base {
        selector_select::changed_seeds_with_mode(
            base_facts,
            base_graph,
            head_facts,
            head_graph,
            &source_paths,
            if args.flag("whole-diff") {
                selector_result::SourceChangeMode::SnapshotDelta
            } else {
                selector_result::SourceChangeMode::RequestedPaths
            },
        )?
    } else {
        ChangeSeeds::default()
    };
    let mut base_guards = Vec::new();
    let mut head_guards = Vec::new();
    let source_conservative = seeds.conservative;
    let auxiliary_conservative =
        runtime_authority_changed || auxiliary.as_ref().is_some_and(|a| a.unscoped);
    if runtime_authority_changed {
        seeds.record_unscoped(selector_result::ChangeGuardCause {
            side: selector_result::SnapshotSide::Head,
            reason: selector_result::ChangeGuardReason::ExternalInput,
            kind: IssueKind::UnsupportedModel,
            file: FileId::NONE, symbol: SymbolId::NONE, detail: StrId::NONE, path: None,
            external: Some(Box::new(selector_result::ExternalGuardDetail {
                reason: "runtime_input_authority_changed".into(),
                message: "whole-diff runtime inputs are missing or their overlay, generator packages or inventory authority changed".into(),
                suite_name: None, schema_path: None, operation_path: None, verb: None,
            })),
        });
        seeds.head_obligations.push(selector_result::Obligation {
            kind: IssueKind::UnsupportedModel,
            file: FileId::NONE,
            symbol: SymbolId::NONE,
            detail: StrId::NONE,
        });
    }
    if let Some(auxiliary) = auxiliary {
        for symbol in auxiliary.base_symbols {
            if let Some(node) = base_graph.node_for_symbol(symbol) {
                seeds.base.push(node);
            }
        }
        for symbol in auxiliary.head_symbols {
            if let Some(node) = head_graph.node_for_symbol(symbol) {
                seeds.head.push(node);
            }
        }
        let base_files: std::collections::BTreeSet<_> =
            auxiliary.base_guard_files.into_iter().collect();
        let head_files: std::collections::BTreeSet<_> =
            auxiliary.head_guard_files.into_iter().collect();
        base_guards.extend(
            base_graph
                .nodes
                .iter()
                .enumerate()
                .filter(|(_, node)| base_files.contains(&node.file))
                .map(|(i, _)| NodeId(i as u32)),
        );
        head_guards.extend(
            head_graph
                .nodes
                .iter()
                .enumerate()
                .filter(|(_, node)| head_files.contains(&node.file))
                .map(|(i, _)| NodeId(i as u32)),
        );
        if auxiliary.unscoped {
            if auxiliary.unscoped_causes_omitted > 0 {
                seeds.record_unscoped(selector_result::ChangeGuardCause {
                    side: selector_result::SnapshotSide::Head,
                    reason: selector_result::ChangeGuardReason::ExternalInput,
                    kind: IssueKind::UnsupportedModel,
                    file: FileId::NONE,
                    symbol: SymbolId::NONE,
                    detail: StrId::NONE,
                    path: None,
                    external: Some(Box::new(selector_result::ExternalGuardDetail {
                        reason: "runtime_causes_truncated".into(),
                        message: format!(
                            "{} additional runtime causes omitted by the diagnostic limit",
                            auxiliary.unscoped_causes_omitted
                        ),
                        suite_name: None,
                        schema_path: None,
                        operation_path: None,
                        verb: None,
                    })),
                });
            }
            for cause in auxiliary.unscoped_causes {
                let sides: &[selector_result::SnapshotSide] = match cause.side {
                    Some(selector_graph_build::runtime_inputs::RuntimeSnapshotSide::Base) => {
                        &[selector_result::SnapshotSide::Base]
                    }
                    Some(selector_graph_build::runtime_inputs::RuntimeSnapshotSide::Head) => {
                        &[selector_result::SnapshotSide::Head]
                    }
                    None => &[
                        selector_result::SnapshotSide::Base,
                        selector_result::SnapshotSide::Head,
                    ],
                };
                for &side in sides {
                    seeds.record_unscoped(selector_result::ChangeGuardCause {
                        side,
                        reason: selector_result::ChangeGuardReason::ExternalInput,
                        kind: IssueKind::UnsupportedModel,
                        file: FileId::NONE,
                        symbol: SymbolId::NONE,
                        detail: StrId::NONE,
                        path: Some(cause.path.clone()),
                        external: Some(Box::new(selector_result::ExternalGuardDetail {
                            reason: cause.reason.as_str().into(),
                            message: cause.detail.clone(),
                            suite_name: cause.suite_name.clone(),
                            schema_path: cause.schema_path.clone(),
                            operation_path: cause.operation_path.clone(),
                            verb: cause.verb.clone(),
                        })),
                    });
                }
            }
            seeds.head_obligations.push(selector_result::Obligation {
                kind: IssueKind::UnsupportedModel,
                file: FileId::NONE,
                symbol: SymbolId::NONE,
                detail: StrId::NONE,
            });
        }
    }
    if !has_base && !changed.is_empty() {
        // A head-only change request cannot observe removed relationships.
        // Retain suites conservatively rather than pretending it is a full diff.
        for path in &changed {
            seeds.record_unscoped(selector_result::ChangeGuardCause {
                side: selector_result::SnapshotSide::Head,
                reason: selector_result::ChangeGuardReason::ExternalInput,
                kind: IssueKind::InvalidInput,
                file: FileId::NONE,
                symbol: SymbolId::NONE,
                detail: StrId::NONE,
                path: Some(path.clone()),
                external: Some(Box::new(selector_result::ExternalGuardDetail {
                    reason: "base_revision_missing".into(),
                    message: "a head-only request cannot observe removed relationships".into(),
                    suite_name: None,
                    schema_path: None,
                    operation_path: None,
                    verb: None,
                })),
            });
        }
        seeds.head_obligations.push(selector_result::Obligation {
            kind: IssueKind::InvalidInput,
            file: FileId::NONE,
            symbol: SymbolId::NONE,
            detail: StrId::NONE,
        });
        for (i, n) in head_graph.nodes.iter().enumerate() {
            if changed.iter().any(|p| p == head_facts.path(n.file)) {
                seeds.head.push(NodeId::checked(i)?);
            }
        }
    }
    if let Some(symbols) = args.values.get("seed") {
        for name in symbols {
            let mut found = false;
            for (i, s) in head_facts.symbols.iter().enumerate() {
                if head_facts.text(s.name) == name {
                    if let Some(n) = head_graph.node_for_symbol(SymbolId::checked(i)?) {
                        seeds.head.push(n);
                        found = true;
                    }
                }
            }
            if !found {
                return Err(format!("compiler seed symbol not found: {name}").into());
            }
        }
    }
    if changed.is_empty() && !args.values.contains_key("seed") && !args.flag("whole-diff") {
        return Err("supply --changed/--changed-list, --seed or --whole-diff".into());
    }
    seeds.head.sort_unstable();
    seeds.head.dedup();
    seeds.base.sort_unstable();
    seeds.base.dedup();
    for name in args.retained_suites() {
        if !head_facts
            .suites
            .iter()
            .any(|suite| head_facts.text(suite.name) == name)
        {
            return Err(
                format!("--retain-suite has no exact current catalogue match: {name}").into(),
            );
        }
        for (facts, graph, guards, side) in [
            (
                head_facts,
                head_graph,
                &mut head_guards,
                selector_result::SnapshotSide::Head,
            ),
            (
                base_facts,
                base_graph,
                &mut base_guards,
                selector_result::SnapshotSide::Base,
            ),
        ] {
            if matches!(side, selector_result::SnapshotSide::Base) && !has_base {
                continue;
            }
            for suite in facts
                .suites
                .iter()
                .filter(|suite| facts.text(suite.name) == name)
            {
                if let Some(node) = graph.node_for_symbol(suite.symbol) {
                    guards.push(node);
                }
                seeds.guard_causes.push(selector_result::ChangeGuardCause {
                    side, reason: selector_result::ChangeGuardReason::ExternalInput,
                    kind: IssueKind::UnsupportedModel, file: suite.file, symbol: suite.symbol,
                    detail: StrId::NONE, path: None,
                    external: Some(Box::new(selector_result::ExternalGuardDetail {
                        reason: "explicit_suite_retention".into(),
                        message: "suite retained by exact --retain-suite policy outside functional selection".into(),
                        suite_name: Some(name.to_owned()), schema_path: None, operation_path: None, verb: None,
                    })),
                });
            }
        }
    }
    for guards in [&mut base_guards, &mut head_guards] {
        guards.sort_unstable();
        guards.dedup();
    }
    Ok(PreparedQuery {
        seeds,
        base_guards,
        head_guards,
        source_paths: source_paths.into_iter().map(str::to_owned).collect(),
        source_conservative,
        auxiliary_conservative,
        elapsed_ns: prepare_start.elapsed().as_nanos(),
    })
}

fn solve(
    args: &Args,
    base_facts: &FactSnapshot,
    base_graph: &ProgramGraph,
    head_facts: &FactSnapshot,
    head_graph: &ProgramGraph,
    has_base: bool,
) -> Result<SelectionResult> {
    let PreparedQuery {
        seeds,
        base_guards,
        head_guards,
        elapsed_ns,
        ..
    } = prepare_query(
        args, base_facts, base_graph, head_facts, head_graph, has_base,
    )?;
    let mut options = args.solve_options()?;
    let absence = args
        .path("classpath-absence-request")
        .map(|path| {
            classpath_absence::Prepared::prepare(
                &path,
                base_facts,
                base_graph,
                head_facts,
                head_graph,
                &seeds,
                &args.retained_suites(),
                args.flag("assume-ordinary-compilation"),
            )
        })
        .transpose()?;
    let all_roots = args.flag("all-roots") || absence.is_some();
    let classpath_frontiers = if args.flag("prune-certified-classpath-roots") {
        let proof = absence.as_ref().ok_or("missing paired classpath proof")?;
        Some(classpath_absence::execution_frontiers(
            &proof.plan,
            base_facts,
            base_graph,
            head_facts,
            head_graph,
        )?)
    } else {
        None
    };
    if let Some(absence) = &absence {
        absence.validate_outputs(&classpath_output_paths(args), replay_path_identity)?;
    }
    let plan_progress = stage_progress(args, "query_plan", "request");
    let plan_start = Instant::now();
    let plan_revision = |facts: &FactSnapshot,
                         graph: &ProgramGraph,
                         execution: &[NodeId],
                         declarations: &[NodeId],
                         guards: &[NodeId]| {
        selector_plan::plan_guarded_with_semantics(
            facts,
            graph,
            selector_plan::PlanSeeds {
                execution,
                declarations,
                unscoped: seeds.conservative,
            },
            guards,
            args.suite_semantics(),
        )
    };
    let (base_plan, head_plan) = if has_base && options.workers > 1 {
        std::thread::scope(|scope| {
            let base = scope.spawn(|| {
                plan_revision(
                    base_facts,
                    base_graph,
                    &seeds.base,
                    &seeds.base_compile,
                    &base_guards,
                )
            });
            let head = plan_revision(
                head_facts,
                head_graph,
                &seeds.head,
                &seeds.head_compile,
                &head_guards,
            );
            let base = base
                .join()
                .map_err(|_| Error::Invalid("base candidate planner panic"))?;
            Ok::<_, Error>((Some(base?), head?))
        })?
    } else {
        let base = if has_base {
            Some(plan_revision(
                base_facts,
                base_graph,
                &seeds.base,
                &seeds.base_compile,
                &base_guards,
            )?)
        } else {
            None
        };
        (
            base,
            plan_revision(
                head_facts,
                head_graph,
                &seeds.head,
                &seeds.head_compile,
                &head_guards,
            )?,
        )
    };
    eprintln!(
        "{}",
        serde_json::json!({"stage":"query_plan","elapsed_ns":plan_start.elapsed().as_nanos(),
        "all_roots_control":args.flag("all-roots"),
        "effective_all_roots":all_roots && classpath_frontiers.is_none(),
        "paired_classpath_pruned_roots":classpath_frontiers.as_ref().map_or(0, |f| f.pruned),
        "base_candidates":base_plan.as_ref().map(|plan|plan.roots.len()),
        "head_candidates":head_plan.roots.len(),"head_catalogue":head_facts.suites.len()})
    );
    record_query_plan(
        args,
        has_base,
        absence
            .as_ref()
            .map_or_else(|| head_plan.identity(), |a| a.plan.identity()),
        absence.as_ref(),
    )?;
    drop(plan_progress);
    let cache = args
        .path("summary-cache")
        .or_else(|| args.path("artifacts").map(|path| path.join("summaries")));
    let runtime = match cache {
        Some(path) => selector_solve::SolverRuntime::with_cache_directory(
            &options,
            &path,
            ContentHash::from_hex(env!("SELECTOR_SOLVE_PRODUCER"))?,
        )?,
        None => selector_solve::SolverRuntime::new(&options)?,
    };
    let events = args.events.clone().unwrap_or_default();
    let control = Arc::new(selector_solve::SolveControl::default());
    let _signals = diagnostics::SignalGuard::install()?;
    options.control = Some(control.clone());
    let stop_after_round = args
        .value("stop-after-round")
        .map(str::parse::<u64>)
        .transpose()?;
    if let Some(round) = stop_after_round {
        control.checkpoint_after_round(round);
    }
    eprintln!(
        "{}",
        serde_json::json!({
            "stage": "query_prepare", "elapsed_ns": elapsed_ns,
            "base_execution_seeds": seeds.base.len(), "head_execution_seeds": seeds.head.len(),
            "unscoped_change": seeds.conservative,
        })
    );
    let analysis_start = Instant::now();
    let base_analysis = |options: &selector_solve::SolveOptions| {
        let mut options = options.clone();
        if let Some(frontiers) = &classpath_frontiers {
            options.execution_roots = Some(frontiers.base.clone());
        } else if !all_roots {
            options.execution_roots = Some(
                base_plan
                    .as_ref()
                    .expect("base revision plan")
                    .roots
                    .iter()
                    .map(|root| selector_solve::ExecutionRoot {
                        node: root.node,
                        receiver: root.receiver,
                    })
                    .collect::<Vec<_>>()
                    .into(),
            );
        }
        options.observer = Some(Arc::new(diagnostics::Observer::new(
            "base",
            events.clone(),
            control.clone(),
            &options,
        )));
        analyze_revision(
            args,
            "base",
            base_facts,
            base_graph,
            selector_solve::AnalysisSeeds {
                execution: &seeds.base,
                declarations: &seeds.base_compile,
            },
            &base_guards,
            &options,
            &runtime,
        )
    };
    let head_analysis = |options: &selector_solve::SolveOptions| {
        let mut options = options.clone();
        if let Some(frontiers) = &classpath_frontiers {
            options.execution_roots = Some(frontiers.head.clone());
        } else if !all_roots {
            options.execution_roots = Some(
                head_plan
                    .roots
                    .iter()
                    .map(|root| selector_solve::ExecutionRoot {
                        node: root.node,
                        receiver: root.receiver,
                    })
                    .collect::<Vec<_>>()
                    .into(),
            );
        }
        options.observer = Some(Arc::new(diagnostics::Observer::new(
            "head",
            events.clone(),
            control.clone(),
            &options,
        )));
        analyze_revision(
            args,
            "head",
            head_facts,
            head_graph,
            selector_solve::AnalysisSeeds {
                execution: &seeds.head,
                declarations: &seeds.head_compile,
            },
            &head_guards,
            &options,
            &runtime,
        )
    };
    let (base, head) = if has_base && runtime.workers() > 1 {
        // Revision owners are independent. Share the bounded CPU pool while
        // partitioning query storage and scratch; no snapshot is cloned into a
        // worker. A single-worker request retains sequential peak memory.
        let (base_options, head_options) = revision_options(&options, runtime.workers());
        std::thread::scope(|scope| {
            let base = scope.spawn(|| base_analysis(&base_options));
            let head = head_analysis(&head_options);
            let base = base
                .join()
                .map_err(|_| Error::Invalid("base analysis worker panic"))?;
            Ok::<_, Error>((Some(base?), head?))
        })?
    } else {
        let base = if has_base {
            Some(base_analysis(&options)?)
        } else {
            None
        };
        (base, head_analysis(&options)?)
    };
    eprintln!(
        "{}",
        serde_json::json!({
            "stage": "query_analysis", "elapsed_ns": analysis_start.elapsed().as_nanos(),
            "workers": runtime.workers(), "revisions_parallel": has_base && runtime.workers() > 1,
        })
    );
    // The evidence was admitted before execution and must still describe the
    // actual physical provider world at publication time.
    if let Some(absence) = &absence {
        absence.revalidate()?;
    }
    let result = if let Some(absence) = &absence {
        selector_select::select_with_classpath_absence(
            base_facts,
            base_graph,
            head_facts,
            head_graph,
            seeds,
            base,
            head,
            &absence.plan,
        )?
    } else if all_roots {
        selector_select::select_with_semantics(
            base_facts,
            base_graph,
            head_facts,
            head_graph,
            seeds,
            base,
            head,
            args.suite_semantics(),
        )?
    } else {
        selector_select::select_with_plan(
            base_facts,
            base_graph,
            head_facts,
            head_graph,
            seeds,
            base,
            head,
            base_plan.as_ref(),
            &head_plan,
        )?
    };
    let retained = args.retained_suites();
    if result.decisions.iter().any(|decision| {
        decision.status == selector_result::SuiteDecisionStatus::Excluded
            && retained
                .binary_search(&head_facts.text(head_facts.suites[decision.suite.index()].name))
                .is_ok()
    }) {
        return Err("explicitly retained suite was excluded; refusing to publish selection".into());
    }
    Ok(result)
}

fn analyze_revision(
    args: &Args,
    side: &str,
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    seeds: selector_solve::AnalysisSeeds<'_>,
    guards: &[NodeId],
    options: &selector_solve::SolveOptions,
    runtime: &selector_solve::SolverRuntime,
) -> std::result::Result<selector_result::AnalysisResult, Error> {
    analyze_revision_with_inspection(
        args,
        side,
        facts,
        graph,
        seeds,
        guards,
        options,
        runtime,
        |_, _| Ok(()),
    )
    .map(|(result, ())| result)
}

fn analyze_revision_with_inspection<T>(
    args: &Args,
    side: &str,
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    seeds: selector_solve::AnalysisSeeds<'_>,
    guards: &[NodeId],
    options: &selector_solve::SolveOptions,
    runtime: &selector_solve::SolverRuntime,
    inspect: impl FnOnce(
        &selector_solve::QuerySession<'_>,
        &selector_result::AnalysisResult,
    ) -> std::result::Result<T, Error>,
) -> std::result::Result<(selector_result::AnalysisResult, T), Error> {
    let producer = ContentHash::from_hex(env!("SELECTOR_SOLVE_PRODUCER"))?;
    let session_progress = stage_progress(args, "query_session_admission", side);
    let mut session = if let Some(dir) = args.path("resume-dir") {
        let path = dir.join(format!("{side}.bin"));
        let mut session = selector_solve::QuerySession::from_checkpoint(
            facts, graph, options, runtime, &path, producer,
        )?;
        eprintln!(
            "{}",
            serde_json::json!({"stage":"query_resume","revision":side,"path":path,"states":session.metrics().states,"operations":session.metrics().edge_visits})
        );
        session.resume()?;
        session
    } else {
        selector_solve::QuerySession::with_runtime(facts, graph, options, runtime)?
    };
    drop(session_progress);
    let result = session.analyze_typed_guarded(seeds, guards)?;
    let finalization = session.finalization_census(&result)?;
    args.events
        .clone()
        .unwrap_or_default()
        .emit(&serde_json::json!({
            "stage": "query_finalization_census",
            "revision": side,
            "census": finalization,
        }));
    if let Some(dir) = args.path("checkpoint-dir") {
        fs::create_dir_all(&dir)?;
        let path = dir.join(format!("{side}.bin"));
        let start = Instant::now();
        let identity = session.save_checkpoint(&path, producer)?;
        eprintln!(
            "{}",
            serde_json::json!({"stage":"query_checkpoint","revision":side,"path":path,
            "identity":identity.to_string(),"elapsed_ns":start.elapsed().as_nanos(),"bytes":fs::metadata(path)?.len()})
        );
    }
    session.persist_completed()?;
    if let Some(directory) = args
        .path("replay-bundle")
        .filter(|_| args.value("replay-revision").unwrap_or("head") == side)
    {
        let node = NodeId(
            args.value("replay-node")
                .ok_or(Error::Invalid(
                    "--replay-node is required with --replay-bundle",
                ))?
                .parse()
                .map_err(|_| Error::Invalid("--replay-node integer"))?,
        );
        let context = args
            .value("replay-context")
            .map(|value| value.parse::<u32>().map(ContextId))
            .transpose()
            .map_err(|_| Error::Invalid("--replay-context integer"))?;
        if args.flag("replay-family") {
            let report = session.export_replay_family(
                node,
                context,
                &directory,
                &selector_solve::replay::ReplayLimits::default(),
                args.number("replay-family-contexts", 64)
                    .map_err(|_| Error::Invalid("--replay-family-contexts integer"))?,
            )?;
            eprintln!(
                "{}",
                serde_json::json!({"stage":"transfer_replay_family_export","revision":side,"directory":directory,"bundle":report})
            );
        } else {
            let report = session.export_replay(
                node,
                context,
                &directory,
                &selector_solve::replay::ReplayLimits::default(),
            )?;
            eprintln!(
                "{}",
                serde_json::json!({"stage":"transfer_replay_export","revision":side,"directory":directory,"bundle":report})
            );
        }
    }
    let inspection = inspect(&session, &result)?;
    Ok((result, inspection))
}

fn revision_options(
    options: &selector_solve::SolveOptions,
    workers: usize,
) -> (selector_solve::SolveOptions, selector_solve::SolveOptions) {
    debug_assert!(workers > 1);
    let mut base = options.clone();
    let mut head = options.clone();
    base.workers = workers / 2;
    head.workers = workers - base.workers;
    base.shard_count = base.workers;
    head.shard_count = head.workers;
    base.memory_budget_bytes = options.memory_budget_bytes / 2;
    head.memory_budget_bytes = options.memory_budget_bytes - base.memory_budget_bytes;
    (base, head)
}

fn read_revision(
    args: &Args,
    side: &str,
    facts: &Path,
    graph: &Path,
) -> std::result::Result<(FactSnapshot, ProgramGraph), Error> {
    let _progress = stage_progress(args, "query_admission", side);
    let facts = selector_facts::codec::read(facts)?;
    let graph = selector_graph::codec::read_bound(graph, facts.identity)?;
    Ok((facts, graph))
}

fn plan_json(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    plan: &selector_plan::CandidatePlan,
) -> serde_json::Value {
    let node_json = |node: NodeId| {
        if node.is_none() {
            return serde_json::json!({"node":null,"symbol":null,"path":null,"unscoped":true});
        }
        let record = graph.nodes[node.index()];
        serde_json::json!({"node":node.0,"symbol":(!record.symbol.is_none()).then(||facts.text(facts.symbols[record.symbol.index()].name)),
            "path":(!record.file.is_none()).then(||facts.path(record.file))})
    };
    let metrics = plan.metrics();
    let contract = SelectionContract::current(plan.suite_semantics());
    serde_json::json!({"snapshot":plan.snapshot().to_string(),"identity":plan.identity().to_string(),
        "assumptions":plan.assumptions(),"unscoped":plan.unscoped(),
        "suite_semantics":plan.suite_semantics().as_str(),
        "suite_semantics_assumption_bit":plan.suite_semantics().assumption_bit(),
        "assume_independent_suites":plan.suite_semantics()==SuiteSemantics::Independent,
        "selection_contract":{"version":SelectionContract::VERSION,"bits":contract.bits(),
            "assumptions":contract.assumptions().collect::<Vec<_>>()},
        "metrics":{"roots":metrics.roots,"candidates":metrics.candidates,"excluded":metrics.excluded,
            "potential_edges":metrics.potential_edges,"unknown_frontiers":metrics.unknown_frontiers,
            "unknown_roots":metrics.unknown_roots,"heap_roots":metrics.heap_roots,"owned_bytes":metrics.owned_bytes},
        "candidate_roots":plan.roots.iter().map(|root|node_json(root.node)).collect::<Vec<_>>(),
        "excluded_roots":plan.excluded_roots().iter().map(|root|serde_json::json!({"root":node_json(*root),
            "certificate":plan.cert_identity(*root).map(|id|id.to_string())})).collect::<Vec<_>>(),
        "frontiers":plan.frontiers().iter().take(64).map(|frontier|serde_json::json!({"root":node_json(frontier.node),"reasons":frontier.reasons})).collect::<Vec<_>>(),
        "frontiers_truncated":plan.frontiers().len()>64})
}

fn publish_output(args: &Args, write: impl FnOnce(&mut dyn Write) -> Result<()>) -> Result<()> {
    if let Some(path) = args.path("output") {
        if let Some(parent) = path.parent().filter(|x| !x.as_os_str().is_empty()) {
            fs::create_dir_all(parent)?;
        }
        let mut temporary = None;
        for _ in 0..64 {
            let mut name = path
                .file_name()
                .ok_or("output has no filename")?
                .to_os_string();
            name.push(format!(
                ".selector-{}-{}.tmp",
                std::process::id(),
                OUTPUT_SEQUENCE.fetch_add(1, Ordering::Relaxed)
            ));
            let temp = path.with_file_name(name);
            match fs::OpenOptions::new()
                .create_new(true)
                .write(true)
                .open(&temp)
            {
                Ok(file) => {
                    temporary = Some((temp, file));
                    break;
                }
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(error) => return Err(error.into()),
            }
        }
        let (temp, file) = temporary.ok_or("cannot allocate unique output temporary")?;
        let operation = (|| {
            let mut out = BufWriter::new(file);
            write(&mut out)?;
            out.flush()?;
            out.get_ref().sync_all()?;
            drop(out);
            fs::rename(&temp, &path)?;
            #[cfg(unix)]
            fs::File::open(
                path.parent()
                    .filter(|p| !p.as_os_str().is_empty())
                    .unwrap_or(Path::new(".")),
            )?
            .sync_all()?;
            Ok(())
        })();
        if operation.is_err() {
            let _ = fs::remove_file(&temp);
        }
        operation
    } else {
        let stdout = io::stdout();
        let mut out = BufWriter::new(stdout.lock());
        write(&mut out)?;
        out.flush()?;
        Ok(())
    }
}
fn report(args: &Args, snapshots: &ReportSnapshots<'_>, result: &SelectionResult) -> Result<()> {
    let evidence = if let Some(path) = args.path("full-evidence") {
        if args.path("output").as_ref() == Some(&path) {
            return Err("--full-evidence must differ from --output".into());
        }
        let mut evidence_args = args.clone();
        evidence_args
            .values
            .insert("output".into(), vec![path.to_string_lossy().into_owned()]);
        publish_output(&evidence_args, |out| {
            selector_report::write_json(out, snapshots, result)?;
            Ok(())
        })?;
        Some((
            fs::canonicalize(&path)?.to_string_lossy().into_owned(),
            hash_file(&path)?,
            fs::metadata(path)?.len(),
        ))
    } else {
        None
    };
    let evidence_ref =
        evidence
            .as_ref()
            .map(|(path, sha256, bytes)| selector_report::ReportEvidenceRef {
                path,
                sha256: *sha256,
                bytes: *bytes,
            });
    publish_output(args, |out| {
        if args.flag("text") {
            if args.flag("full-report") {
                selector_report::write_text(out, snapshots, result)?;
            } else {
                selector_report::write_compact_text(out, snapshots, result)?;
            }
        } else if args.flag("full-report") {
            selector_report::write_json(out, snapshots, result)?;
        } else {
            selector_report::write_compact_json_with_evidence(
                out,
                snapshots,
                result,
                evidence_ref.as_ref(),
            )?;
        }
        Ok(())
    })
}

fn execute(args: &Args) -> Result<Option<Completion>> {
    let start = Instant::now();
    match args.command.as_str() {
        "help" | "--help" | "-h" => {
            print!("{HELP}");
            return Ok(None);
        }
        "producers" => {
            publish_output(args, |out| {
                serde_json::to_writer(
                    out,
                    &serde_json::json!({
                        "schema_version": 1,
                        "producers": producers(),
                        "build": {"version": env!("CARGO_PKG_VERSION"), "profile": env!("SELECTOR_BUILD_PROFILE"),
                            "opt_level":env!("SELECTOR_BUILD_OPT_LEVEL"),"debug_assertions":cfg!(debug_assertions),"rustc":env!("SELECTOR_BUILD_RUSTC")},
                    }),
                )?;
                Ok(())
            })?;
        }
        "rerender" => {
            publish_output(args, |out| {
                explain::render_saved(&args.required("report")?, out, args.flag("text"))
            })?;
        }
        "inspect-checkpoint" => inspect::execute(args)?,
        "retention-precheck" => retention_precheck::execute(args)?,
        "replay" => {
            let path = args.required("receipt")?;
            let limits = replay::ReplayLimits {
                verify_compiler_inputs: !args.flag("frozen-inputs"),
                compiler_workers: args.workers()?,
                ..Default::default()
            };
            let validation = replay::validate_receipt(&path, &producers(), &limits)?;
            if args.flag("validate-only") {
                publish_output(args, |out| {
                    serde_json::to_writer_pretty(out, &validation)?;
                    Ok(())
                })?;
            } else {
                let receipt = replay::load_receipt(&path, &limits)?;
                let overrides = args.values.keys().any(|name| {
                    !matches!(
                        name.as_str(),
                        "receipt" | "output" | "text" | "frozen-inputs"
                    )
                });
                let only_report_stale = validation.valid()
                    || validation
                        .stages
                        .iter()
                        .all(|stage| stage.reusable || stage.id == "query.report");
                if !overrides
                    && only_report_stale
                    && let Some(outcome) = validation.output("query.solve", "outcome")
                {
                    publish_output(args, |out| {
                        explain::render_saved(outcome, out, args.flag("text"))
                    })?;
                } else {
                    eprintln!(
                        "{}",
                        serde_json::json!({"stage":"native_replay","earliest_invalidation":validation.earliest_invalidation,
                        "reusable_stages":validation.stages.iter().filter(|stage|stage.reusable).count()})
                    );
                    let raw = recording::prepared_query_arguments(&path, &receipt, &validation)?
                        .unwrap_or(receipt.replay_arguments(&path)?);
                    let mut replay_args = Args::parse(raw)?;
                    relocate_replay_diagnostics(&mut replay_args, args)?;
                    for (name, values) in &args.values {
                        if !matches!(name.as_str(), "receipt" | "validate-only") {
                            replay_args.values.insert(name.clone(), values.clone());
                        }
                    }
                    if args.path("resume-dir").is_some() && args.value("stop-after-round").is_none()
                    {
                        replay_args.values.remove("stop-after-round");
                    }
                    return execute_recorded(replay_args);
                }
            }
        }
        "probe-root" => return Ok(Some(probe::execute(args)?)),
        "transfer-replay" if args.required("bundle")?.join("family.json").is_file() => {
            inspect::replay_family(args)?
        }
        "transfer-replay" => {
            let bundle = selector_solve::replay::ReplayBundle::read(
                &args.required("bundle")?,
                &selector_solve::replay::ReplayLimits::default(),
            )?;
            if let Some(directory) = args.path("minimized-output") {
                let explicit_predicate = args.value("min-calls").is_some()
                    || args.value("min-reads").is_some()
                    || args.value("target-node").is_some();
                let predicate = selector_solve::replay::ReplayPredicate {
                    min_calls: args
                        .value("min-calls")
                        .map(str::parse)
                        .transpose()?
                        .unwrap_or(0),
                    min_reads: args
                        .value("min-reads")
                        .map(str::parse)
                        .transpose()?
                        .unwrap_or(0),
                    target: args
                        .value("target-node")
                        .map(|value| value.parse::<u32>().map(NodeId))
                        .transpose()?,
                    preserve_exact_output: !explicit_predicate,
                    ..Default::default()
                };
                let options = selector_solve::replay::MinimizeOptions {
                    max_evaluations: args.number("max-minimize-evaluations", 256)?,
                    ..Default::default()
                };
                let minimized = bundle.minimize(&options, &predicate)?;
                bundle.write_minimized(&directory, &minimized)?;
                publish_output(args, |out| {
                    serde_json::to_writer_pretty(out, &minimized)?;
                    Ok(())
                })?;
            } else if args.flag("compare") {
                let comparison =
                    bundle.compare(&selector_solve::replay::ReplayOptions::default())?;
                publish_output(args, |out| {
                    serde_json::to_writer_pretty(out, &comparison)?;
                    Ok(())
                })?;
            } else {
                let outcome = bundle.replay(&selector_solve::replay::ReplayOptions::default())?;
                publish_output(args, |out| {
                    serde_json::to_writer_pretty(out, &outcome)?;
                    Ok(())
                })?;
            }
        }
        "capture" => {
            use selector_extract::raw_capture::{RawCaptureOptions, capture_manifest};
            let mut limits = RawCaptureOptions::default();
            limits.workers = args.workers()?;
            limits.max_raw_bytes = args.number("max-document-bytes", limits.max_raw_bytes)?;
            limits.max_total_raw_bytes = args.number(
                "max-input-bytes",
                usize::try_from(limits.max_total_raw_bytes)?,
            )? as u64;
            limits.max_output_bytes = args.number(
                "max-output-bytes",
                usize::try_from(limits.max_output_bytes)?,
            )? as u64;
            limits.max_in_flight_bytes = args.number(
                "memory-budget",
                usize::try_from(limits.max_in_flight_bytes)?,
            )? as u64;
            publish_output(args, |mut out| {
                let run = capture_manifest(&args.required("input")?, &mut out, &limits)?;
                eprintln!(
                    "{}",
                    serde_json::json!({"stage":"capture","raw_inputs":run.raw_inputs,"documents":run.documents,"validated_sources":run.validated_sources,"raw_bytes":run.raw_bytes,"output_bytes":run.output_bytes,"effective_workers":run.effective_workers,"producer":run.producer.to_string()})
                );
                Ok(())
            })?;
        }
        "runtime" => {
            use selector_graph_build::runtime_inputs::{
                RuntimeCaptureOptions, capture_git_runtime,
            };
            let repository = args.required("repository")?;
            let catalogue = args.required("catalogue-input")?;
            let output = args.required("output")?;
            let receipt = capture_git_runtime(RuntimeCaptureOptions {
                repository: &repository,
                revision: args.value("revision").ok_or("--revision is required")?,
                ci_catalogue: &catalogue,
                output: &output,
                compiler_inventory_complete: args.flag("compiler-inventory-complete"),
                auxiliary_sources: args.path("auxiliary-sources").as_deref(),
            })?;
            eprintln!(
                "{}",
                serde_json::json!({
                    "stage": "runtime_capture", "revision": receipt.revision,
                    "manifest": receipt.manifest, "identity": receipt.manifest_sha256.to_string(),
                    "sources": receipt.sources, "suite_catalogues": receipt.suite_catalogues,
                    "source_bytes": receipt.source_bytes,
                })
            );
        }
        "compiler-inputs" => {
            let contexts = args.required("contexts")?;
            let root = args.required("compiler-input-root")?;
            let mut limits = selector_extract::compiler_inputs::InventoryLimits::default();
            limits.workers = args.workers()?;
            let inputs = selector_extract::compiler_inputs::admit(&contexts, &root, &limits)?;
            publish_output(args, |out| {
                serde_json::to_writer_pretty(out, &inputs.receipt)?;
                Ok(())
            })?;
        }
        "syntax" => {
            use selector_extract::toolchain::{SyntaxLimits, SyntaxTool};
            let mut limits = SyntaxLimits::default();
            limits.max_input_bytes =
                args.number("max-input-bytes", usize::try_from(limits.max_input_bytes)?)? as u64;
            limits.max_output_bytes = args.number(
                "max-output-bytes",
                usize::try_from(limits.max_output_bytes)?,
            )? as u64;
            limits.max_source_bytes = args.number("max-document-bytes", limits.max_source_bytes)?;
            limits.batch_source_bytes = args.number("batch-bytes", limits.batch_source_bytes)?;
            limits.java_heap_bytes =
                args.number("java-heap-bytes", usize::try_from(limits.java_heap_bytes)?)? as u64;
            limits.parallel_java_heap_bytes = args.number(
                "parallel-java-heap-bytes",
                usize::try_from(limits.parallel_java_heap_bytes)?,
            )? as u64;
            let tool = if let Some(path) = args.path("toolchain") {
                SyntaxTool::from_manifest(&path, &limits)?
            } else {
                SyntaxTool::compile_cached(
                    &args.required("exporter")?,
                    &args.required("tool-cache")?,
                    &limits,
                )?
            };
            let input = args.required("input")?;
            let cache = args.path("syntax-cache");
            if let Some(previous) = args.path("reuse-syntax") {
                let cache = cache
                    .as_deref()
                    .ok_or("--reuse-syntax requires --syntax-cache")?;
                let count = tool.import_syntax_cache(&previous, cache, &limits)?;
                eprintln!(
                    "{}",
                    serde_json::json!({"stage":"syntax-cache-import","sources":count})
                );
            }
            publish_output(args, |mut out| {
                let run = match cache.as_deref() {
                    Some(cache) => {
                        tool.run_capture_cached(&input, &mut out, args.workers()?, &limits, cache)?
                    }
                    None => tool.run_capture(&input, &mut out, args.workers()?, &limits)?,
                };
                eprintln!(
                    "{}",
                    serde_json::json!({"stage":"syntax","sources":run.sources,"batches":run.batches,"cache_hits":run.cache_hits,"effective_workers":run.effective_workers,"source_bytes":run.source_bytes,"output_bytes":run.output_bytes,"producer":run.producer.to_string()})
                );
                Ok(())
            })?;
        }
        "extract" => {
            let input = args.required("input")?;
            let metadata = checked_metadata(args)?;
            record_metadata_inputs(args, metadata.as_ref())?;
            let compiler_inputs = admit_compiler_inputs(args, &input)?;
            let contexts = contexts_input(args, &input);
            if let (Some(recording), Some(inputs), Some(root), Some(contexts)) = (
                &args.recording,
                compiler_inputs.as_ref(),
                args.path("compiler-input-root"),
                contexts.as_deref(),
            ) {
                recording
                    .lock()
                    .map_err(|_| "receipt writer lock poisoned")?
                    .record_compiler_inputs(args.side, contexts, &root, inputs.identity)?;
            }
            let syntax = args.path("syntax");
            let catalogue = args.path("catalogue-input");
            let output = args.required("output")?;
            let facts = extract_file(
                args,
                &input,
                syntax.as_deref(),
                catalogue.as_deref(),
                &output,
                compiler_inputs,
                metadata.as_ref(),
            )?;
            record_prepared(
                args,
                "extract",
                &[
                    ("documents", Some(&input)),
                    ("syntax", syntax.as_deref()),
                    ("catalogue", catalogue.as_deref()),
                    ("contexts", contexts.as_deref()),
                ],
                &output,
            )?;
            eprintln!("facts identity: {}", facts.identity);
        }
        "metadata-authority" => {
            publish_output(args, |mut out| {
                metadata_stage::write_authority_preview(
                    &args.required("input")?,
                    &args.required("metadata-binary-map")?,
                    &args.required("contexts")?,
                    &args.required("compiler-input-root")?,
                    &mut out,
                )
            })?;
        }
        "metadata-requests" => {
            use serde::Serialize;
            #[derive(Serialize)]
            struct Request<'a> {
                context: &'a str,
                symbol: &'a str,
            }
            let input = args.required("input")?;
            let options = extraction_options(
                args,
                &input,
                args.path("catalogue-input").as_deref(),
                admit_compiler_inputs(args, &input)?,
            )?;
            let prepared = selector_extract::prepare_capture(
                &input,
                args.path("syntax").as_deref(),
                &options,
            )?;
            let requests = prepared.metadata_requests(&Default::default())?;
            publish_output(args, |mut out| {
                out.write_all(
                    b"{\"schema\":\"compiler-external-metadata-requests/v1\",\"request_identity\":",
                )?;
                serde_json::to_writer(&mut out, &requests.identity().to_string())?;
                out.write_all(b",\"contexts_sha256\":")?;
                serde_json::to_writer(
                    &mut out,
                    &requests.contexts_identity().map(|hash| hash.to_string()),
                )?;
                out.write_all(b",\"revision\":")?;
                serde_json::to_writer(&mut out, prepared.revision())?;
                write!(
                    &mut out,
                    ",\"requests_total\":{},\"requests\":[",
                    requests.len()
                )?;
                for (index, row) in requests.iter().enumerate() {
                    if index != 0 {
                        out.write_all(b",")?;
                    }
                    serde_json::to_writer(
                        &mut out,
                        &Request {
                            context: row.context,
                            symbol: row.symbol,
                        },
                    )?;
                }
                out.write_all(b"]}\n")?;
                Ok(())
            })?;
            eprintln!(
                "{}",
                serde_json::json!({"stage":"metadata_requests","requests":requests.len(),"body_lowering":false,"jvm_invoked":false})
            );
        }
        "binary-map" => {
            let facts = selector_facts::codec::read(&args.required("facts")?)?;
            let contexts = args.required("contexts")?;
            let root = args.required("compiler-input-root")?;
            let mut options = selector_graph_build::binary_capture::CaptureOptions::default();
            options.workers = args.workers()?;
            options.platform = platform_options(args)?;
            let generated =
                selector_graph_build::binary_capture::generate(&facts, &contexts, &root, &options)?;
            publish_output(args, |out| {
                serde_json::to_writer_pretty(out, &generated.manifest)?;
                Ok(())
            })?;
            eprintln!(
                "{}",
                serde_json::json!({"stage":"binary_capture","receipt":generated.receipt})
            );
        }
        "enrich" => {
            let facts = selector_facts::codec::read(&args.required("facts")?)?;
            let inputs = selector_graph_build::binary_inputs::load_binary_manifest_with_platform(
                &args.required("binary-map")?,
                &facts,
                &binary_options(args)?,
                platform_options(args)?.as_ref(),
            )?;
            let facts = enrich_facts(facts, inputs, &args.required("output")?)?;
            eprintln!("enriched facts identity: {}", facts.identity);
        }
        "build" => {
            let facts = selector_facts::codec::read(&args.required("facts")?)?;
            let graph = build_graph(args, &facts, &args.required("output")?)?;
            eprintln!("graph identity: {}", graph.identity);
        }
        "verify" => {
            let facts = selector_facts::codec::read(&args.required("facts")?)?;
            if let Some(path) = args.path("graph") {
                let graph = selector_graph::codec::read_bound(&path, facts.identity)?;
                verify_binding(&facts, &graph)?;
            }
            eprintln!("verified facts {}", facts.identity);
        }
        "query" | "audit-changes" => {
            let head_facts = args.required("head-facts")?;
            let head_graph = args.required("head-graph")?;
            let base_paths = match (args.path("base-facts"), args.path("base-graph")) {
                (Some(f), Some(g)) => Some((f, g)),
                (None, None) => None,
                _ => return Err("--base-facts and --base-graph must be supplied together".into()),
            };
            let admission_start = Instant::now();
            let ((hf, hg), base) = match base_paths {
                Some((f, g)) if args.workers()? > 1 => std::thread::scope(|scope| {
                    let base = scope.spawn(|| read_revision(args, "base", &f, &g));
                    let head = read_revision(args, "head", &head_facts, &head_graph);
                    let base = base
                        .join()
                        .map_err(|_| Error::Invalid("base admission worker panic"))?;
                    Ok::<_, Error>((head?, Some(base?)))
                })?,
                Some((f, g)) => (
                    read_revision(args, "head", &head_facts, &head_graph)?,
                    Some(read_revision(args, "base", &f, &g)?),
                ),
                None => (read_revision(args, "head", &head_facts, &head_graph)?, None),
            };
            eprintln!(
                "{}",
                serde_json::json!({
                    "stage": "query_admission", "elapsed_ns": admission_start.elapsed().as_nanos(),
                    "revisions_parallel": base.is_some() && args.workers()? > 1,
                })
            );
            let (bf, bg) = base.as_ref().map_or((&hf, &hg), |(f, g)| (f, g));
            {
                let _progress = stage_progress(args, "query_input_receipt", "request");
                record_query_inputs(args, base.is_some())?;
            }
            if args.command == "audit-changes" {
                let prepared = prepare_query(args, bf, bg, &hf, &hg, base.is_some())?;
                let mut scope = Vec::new();
                selector_report::write_source_change_scope(
                    &mut scope,
                    &ReportSnapshots {
                        base_facts: bf,
                        base_graph: bg,
                        head_facts: &hf,
                        head_graph: &hg,
                    },
                    prepared.seeds.change_scope.as_ref(),
                )?;
                let scope: serde_json::Value = serde_json::from_slice(&scope)?;
                let obligations = |facts: &FactSnapshot, rows: &[selector_result::Obligation]| {
                    rows.iter().map(|row| serde_json::json!({
                        "kind": format!("{:?}", row.kind),
                        "file": (!row.file.is_none()).then(|| facts.path(row.file)),
                        "symbol": (!row.symbol.is_none()).then(|| facts.text(facts.symbols[row.symbol.index()].name)),
                        "detail": (!row.detail.is_none()).then(|| facts.text(row.detail)),
                    })).collect::<Vec<_>>()
                };
                publish_output(args, |out| {
                    serde_json::to_writer_pretty(
                        out,
                        &serde_json::json!({
                            "schema_version": 1, "stage": "change_audit",
                            "elapsed_ns": prepared.elapsed_ns,
                            "source_paths": prepared.source_paths,
                            "change_scope": scope,
                            "source_conservative": prepared.source_conservative,
                            "auxiliary_conservative": prepared.auxiliary_conservative,
                            "unscoped_change": prepared.seeds.conservative,
                            "base_execution_seeds": prepared.seeds.base.len(),
                            "head_execution_seeds": prepared.seeds.head.len(),
                            "base_compilation_seeds": prepared.seeds.base_compile.len(),
                            "head_compilation_seeds": prepared.seeds.head_compile.len(),
                            "base_guard_nodes": prepared.base_guards.len(),
                            "head_guard_nodes": prepared.head_guards.len(),
                        "guard_causes": prepared.seeds.guard_causes.iter().map(|cause| {
                            let facts = match cause.side {selector_result::SnapshotSide::Base => bf, selector_result::SnapshotSide::Head => &hf};
                            serde_json::json!({"snapshot":format!("{:?}",cause.side),"reason":format!("{:?}",cause.reason),
                                "kind":format!("{:?}",cause.kind),
                                "path":cause.path.as_deref().or_else(||(!cause.file.is_none()).then(||facts.path(cause.file))),
                                "symbol":(!cause.symbol.is_none()).then(||facts.text(facts.symbols[cause.symbol.index()].name)),
                                "detail":(!cause.detail.is_none()).then(||facts.text(cause.detail)),
                                "external":cause.external.as_ref().map(|external|serde_json::json!({"reason":external.reason,
                                    "message":external.message,"suite_name":external.suite_name,"schema_path":external.schema_path,
                                    "operation_path":external.operation_path,"verb":external.verb}))})
                        }).collect::<Vec<_>>(),
                            "base_obligations": obligations(bf, &prepared.seeds.base_obligations),
                            "head_obligations": obligations(&hf, &prepared.seeds.head_obligations),
                        }),
                    )?;
                    Ok(())
                })?;
                return Ok(None);
            }
            if args.flag("plan-only") {
                let prepared = prepare_query(args, bf, bg, &hf, &hg, base.is_some())?;
                let head_plan = selector_plan::plan_guarded_with_semantics(
                    &hf,
                    &hg,
                    selector_plan::PlanSeeds {
                        execution: &prepared.seeds.head,
                        declarations: &prepared.seeds.head_compile,
                        unscoped: prepared.seeds.conservative,
                    },
                    &prepared.head_guards,
                    args.suite_semantics(),
                )?;
                let base_plan = if base.is_some() {
                    Some(selector_plan::plan_guarded_with_semantics(
                        bf,
                        bg,
                        selector_plan::PlanSeeds {
                            execution: &prepared.seeds.base,
                            declarations: &prepared.seeds.base_compile,
                            unscoped: prepared.seeds.conservative,
                        },
                        &prepared.base_guards,
                        args.suite_semantics(),
                    )?)
                } else {
                    None
                };
                let contract = SelectionContract::current(args.suite_semantics());
                publish_output(args, |out| {
                    serde_json::to_writer_pretty(
                        out,
                        &serde_json::json!({"schema_version":1,"stage":"candidate_plan",
                    "suite_semantics":args.suite_semantics().as_str(),
                    "suite_semantics_assumption_bit":args.suite_semantics().assumption_bit(),
                    "assume_independent_suites":args.suite_semantics()==SuiteSemantics::Independent,
                    "selection_contract":{"version":SelectionContract::VERSION,"bits":contract.bits(),
                        "assumptions":contract.assumptions().collect::<Vec<_>>()},
                    "retained_suites":args.retained_suites(),
                    "head":plan_json(&hf,&hg,&head_plan),"base":base_plan.as_ref().map(|plan|plan_json(bf,bg,plan))}),
                    )?;
                    Ok(())
                })?;
                return Ok(None);
            }
            let result = solve(args, bf, bg, &hf, &hg, base.is_some())?;
            report(
                args,
                &ReportSnapshots {
                    base_facts: bf,
                    base_graph: bg,
                    head_facts: &hf,
                    head_graph: &hg,
                },
                &result,
            )?;
            record_query_outcome(args)?;
            eprintln!(
                "query: {} selected suites, {:?}, {:.3}s",
                result.suites.len(),
                result.completion,
                start.elapsed().as_secs_f64()
            );
            return Ok(Some(result.completion));
        }
        "run" => {
            let dir = args.required("artifacts")?;
            fs::create_dir_all(&dir)?;
            let catalogue_file = args
                .path("catalogue")
                .unwrap_or_else(|| dir.join("catalogue.sqlite"));
            let mut catalogue = Catalogue::open(&catalogue_file)?;
            let head = args.required("head")?;
            let base_path = args.path("base");
            let head_syntax = args.path("head-syntax");
            let base_syntax = args.path("base-syntax");
            let catalogue_path = args.path("catalogue-input");
            let base_catalogue_path = args.path("base-catalogue-input");
            let configuration = serde_json::to_vec(&args.values)?;
            let head_contexts = contexts_input(args, &head);
            let base_contexts = base_path.as_ref().and_then(|base| {
                args.path("base-contexts").or_else(|| {
                    base.parent()
                        .map(|p| p.join("compiler-contexts.json.gz"))
                        .filter(|p| p.is_file())
                })
            });
            let runtime_input = args.path("runtime-input");
            let base_runtime_input = args.path("base-runtime-input");
            let binary_map = args.path("binary-map");
            let base_binary_map = args.path("base-binary-map");
            let input_identity = stage_inputs(
                &[
                    Some(&head),
                    base_path.as_deref(),
                    head_syntax.as_deref(),
                    base_syntax.as_deref(),
                    catalogue_path.as_deref(),
                    base_catalogue_path.as_deref(),
                    head_contexts.as_deref(),
                    base_contexts.as_deref(),
                    runtime_input.as_deref(),
                    base_runtime_input.as_deref(),
                    binary_map.as_deref(),
                    base_binary_map.as_deref(),
                ],
                &configuration,
            )?;
            let run = catalogue.begin_run("run", input_identity.0)?;
            let outcome = (|| -> Result<SelectionResult> {
                let cat = args.path("catalogue-input");
                if cat.is_none() {
                    return Err("run requires --catalogue-input for captured test discovery".into());
                }
                let ((hf, hg), base) = prepare_snapshots(
                    args,
                    &mut catalogue,
                    &catalogue_file,
                    &dir,
                    &head,
                    base_path.as_deref(),
                )?;
                let (bf, bg) = base.as_ref().map_or((&hf, &hg), |(f, g)| (f, g));
                let result = solve(args, bf, bg, &hf, &hg, base.is_some())?;
                report(
                    args,
                    &ReportSnapshots {
                        base_facts: bf,
                        base_graph: bg,
                        head_facts: &hf,
                        head_graph: &hg,
                    },
                    &result,
                )?;
                record_query_outcome(args)?;
                Ok(result)
            })();
            match outcome {
                Ok(result) => {
                    let status = if result.completion == Completion::Complete {
                        RunStatus::Complete
                    } else {
                        RunStatus::Incomplete
                    };
                    catalogue.finish_run(
                        run,
                        status,
                        &format!(
                            "{{\"elapsed_seconds\":{},\"selected_suites\":{}}}",
                            start.elapsed().as_secs_f64(),
                            result.suites.len()
                        ),
                    )?;
                    eprintln!(
                        "run {run}: {} selected suites, {:?}, {:.3}s",
                        result.suites.len(),
                        result.completion,
                        start.elapsed().as_secs_f64()
                    );
                    return Ok(Some(result.completion));
                }
                Err(error) => {
                    if let Err(record_error) = catalogue.finish_run(run, RunStatus::Failed, "{}") {
                        eprintln!("recording failed run: {record_error}");
                    }
                    return Err(error);
                }
            }
        }
        "explain" => {
            let wanted = args.value("suite").ok_or("--suite is required")?;
            publish_output(args, |out| {
                explain::explain_report(&args.required("report")?, wanted, out)
            })?;
        }
        _ => return Err(format!("unknown command {:?}; use --help", args.command).into()),
    }
    eprintln!("elapsed: {:.3}s", start.elapsed().as_secs_f64());
    Ok(None)
}

fn main() {
    let result = Args::parse(std::env::args().skip(1)).and_then(|args| {
        if args.flag("help") {
            print!("{HELP}");
            Ok(None)
        } else {
            execute_recorded(args)
        }
    });
    match result {
        Ok(_) => {}
        Err(error) => {
            eprintln!("selector: {error}");
            std::process::exit(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn args(v: &[&str]) -> Result<Args> {
        Args::parse(v.iter().map(|s| s.to_string()))
    }
    #[test]
    fn independent_suite_assumption_is_explicit_query_policy_and_replay_bound() {
        for command in ["query", "run"] {
            let shared = args(&[command]).unwrap();
            shared.validate().unwrap();
            assert_eq!(shared.suite_semantics(), SuiteSemantics::SharedState);
            let independent = args(&[
                command,
                "--assume-independent-suites",
                "--retain-suite",
                "pkg.PerformanceTest",
                "--retain-suite",
                "pkg.TimingTest",
            ])
            .unwrap();
            independent.validate().unwrap();
            assert_eq!(independent.suite_semantics(), SuiteSemantics::Independent);
            assert_ne!(
                replay::options_identity(&shared.raw, &BTreeMap::new()),
                replay::options_identity(&independent.raw, &BTreeMap::new())
            );
            let directory = tempfile::tempdir().unwrap();
            let mut receipt = replay::ReplayReceipt::new(independent.raw.clone(), producers());
            let (stage, producer) = if command == "query" {
                ("head.inputs", "inputs")
            } else {
                ("head.graph", "graph")
            };
            receipt.add_stage(replay::StageReceipt::new(
                stage,
                producer,
                &receipt.producers[producer],
                ContentHash::default().to_string(),
                replay::options_identity(&receipt.arguments, &receipt.path_arguments),
            ));
            let restored = receipt
                .replay_arguments(&directory.path().join("receipt.json"))
                .unwrap();
            assert_eq!(restored, independent.raw);
            assert_eq!(
                Args::parse(restored.clone()).unwrap().retained_suites(),
                ["pkg.PerformanceTest", "pkg.TimingTest"]
            );
            assert_eq!(
                Args::parse(restored).unwrap().suite_semantics(),
                SuiteSemantics::Independent
            );
        }
        args(&["query", "--plan-only", "--assume-independent-suites"])
            .unwrap()
            .validate()
            .unwrap();
        for command in ["extract", "build", "binary-map", "probe-root", "replay"] {
            assert!(
                args(&[command, "--assume-independent-suites"])
                    .unwrap()
                    .validate()
                    .unwrap_err()
                    .to_string()
                    .contains("requires query or run")
            );
        }
        assert!(args(&["query", "--assume-independent-suites", "false"]).is_err());
        assert!(
            args(&[
                "query",
                "--assume-independent-suites",
                "--assume-independent-suites"
            ])
            .is_err()
        );
    }

    #[test]
    fn owning_test_classpath_is_explicit_paired_policy_and_raw_replay_bound() {
        let invocation = [
            "query",
            "--assume-independent-suites",
            "--assume-owning-test-classpath",
            "--classpath-absence-request",
            "request.json",
            "--base-facts",
            "base.bin",
            "--base-graph",
            "base-graph.bin",
            "--head-facts",
            "head.bin",
            "--head-graph",
            "head-graph.bin",
        ];
        let accepted = args(&invocation).unwrap();
        accepted.validate().unwrap();
        let directory = tempfile::tempdir().unwrap();
        let mut receipt = replay::ReplayReceipt::new(accepted.raw.clone(), producers());
        receipt.add_stage(replay::StageReceipt::new(
            "head.inputs",
            "inputs",
            &receipt.producers["inputs"],
            ContentHash::default().to_string(),
            replay::options_identity(&receipt.arguments, &receipt.path_arguments),
        ));
        assert_eq!(
            receipt
                .replay_arguments(&directory.path().join("receipt.json"))
                .unwrap(),
            accepted.raw
        );
        let mut strict = accepted.raw.clone();
        strict.retain(|value| value != "--assume-owning-test-classpath");
        assert_ne!(
            replay::options_identity(&accepted.raw, &BTreeMap::new()),
            replay::options_identity(&strict, &BTreeMap::new())
        );
        for missing in [
            "--assume-independent-suites",
            "--assume-owning-test-classpath",
        ] {
            let rejected: Vec<_> = invocation
                .iter()
                .copied()
                .filter(|value| *value != missing)
                .collect();
            assert!(args(&rejected).unwrap().validate().is_err());
        }
        for command in ["run", "extract", "build", "probe-root", "replay"] {
            let mut rejected = invocation;
            rejected[0] = command;
            assert!(args(&rejected).unwrap().validate().is_err());
        }
        for extra in ["--plan-only", "--seed"] {
            let mut rejected = invocation.to_vec();
            rejected.push(extra);
            if extra == "--seed" {
                rejected.push("pkg/Changed#apply().");
            }
            assert!(args(&rejected).unwrap().validate().is_err());
        }
        for incomplete in [
            vec![
                "query",
                "--assume-independent-suites",
                "--assume-owning-test-classpath",
            ],
            vec![
                "query",
                "--assume-independent-suites",
                "--assume-owning-test-classpath",
                "--classpath-absence-request",
                "request.json",
            ],
        ] {
            assert!(args(&incomplete).unwrap().validate().is_err());
        }
        assert!(args(&["query", "--assume-owning-test-classpath", "false"]).is_err());
        assert!(
            args(&[
                "query",
                "--assume-owning-test-classpath",
                "--assume-owning-test-classpath"
            ])
            .is_err()
        );
    }

    #[test]
    fn ordinary_compilation_requires_explicit_paired_owning_policy_and_replay_binding() {
        let invocation = [
            "query",
            "--assume-independent-suites",
            "--assume-owning-test-classpath",
            "--assume-ordinary-compilation",
            "--classpath-absence-request",
            "request.json",
            "--base-facts",
            "base.bin",
            "--base-graph",
            "base-graph.bin",
            "--head-facts",
            "head.bin",
            "--head-graph",
            "head-graph.bin",
        ];
        let accepted = args(&invocation).unwrap();
        accepted.validate().unwrap();
        assert!(accepted.flag("assume-ordinary-compilation"));
        let mut receipt = replay::ReplayReceipt::new(accepted.raw.clone(), producers());
        receipt.add_stage(replay::StageReceipt::new(
            "head.inputs",
            "inputs",
            &receipt.producers["inputs"],
            ContentHash::default().to_string(),
            replay::options_identity(&receipt.arguments, &receipt.path_arguments),
        ));
        let directory = tempfile::tempdir().unwrap();
        assert_eq!(
            receipt
                .replay_arguments(&directory.path().join("receipt.json"))
                .unwrap(),
            accepted.raw
        );
        let owning: Vec<_> = accepted
            .raw
            .iter()
            .filter(|arg| arg.as_str() != "--assume-ordinary-compilation")
            .cloned()
            .collect();
        assert_ne!(
            replay::options_identity(&owning, &BTreeMap::new()),
            replay::options_identity(&accepted.raw, &BTreeMap::new())
        );
        for missing in [
            "--assume-owning-test-classpath",
            "--assume-independent-suites",
        ] {
            let raw: Vec<_> = invocation
                .iter()
                .copied()
                .filter(|arg| *arg != missing)
                .collect();
            assert!(args(&raw).unwrap().validate().is_err());
            let mut malformed = receipt.clone();
            malformed.arguments.retain(|arg| arg != missing);
            assert!(
                malformed
                    .replay_arguments(&directory.path().join("receipt.json"))
                    .is_err()
            );
        }
        for command in ["run", "extract", "build", "probe-root", "replay"] {
            let mut raw = invocation;
            raw[0] = command;
            assert!(args(&raw).unwrap().validate().is_err());
        }
        let mut plan = invocation.to_vec();
        plan.push("--plan-only");
        assert!(args(&plan).unwrap().validate().is_err());
        assert!(
            args(&["query", "--assume-ordinary-compilation"])
                .unwrap()
                .validate()
                .is_err()
        );
        assert!(args(&["query", "--assume-ordinary-compilation", "false"]).is_err());
        assert!(
            args(&[
                "query",
                "--assume-ordinary-compilation",
                "--assume-ordinary-compilation"
            ])
            .is_err()
        );
    }

    #[test]
    fn suite_retention_requires_exact_nonempty_names_and_query_policy() {
        let retained = args(&[
            "query",
            "--retain-suite",
            "pkg.Test",
            "--retain-suite",
            "pkg.Test",
            "--retain-suite",
            "pkg.Other",
        ])
        .unwrap();
        retained.validate().unwrap();
        assert_eq!(retained.retained_suites(), ["pkg.Other", "pkg.Test"]);
        for name in ["", "pkg.Test\n", "pkg.\u{0085}Test"] {
            assert!(
                args(&["query", "--retain-suite", name])
                    .unwrap()
                    .validate()
                    .is_err()
            );
        }
        for command in ["extract", "build", "replay", "probe-root"] {
            assert!(
                args(&[command, "--retain-suite", "pkg.Test"])
                    .unwrap()
                    .validate()
                    .is_err()
            );
        }
    }

    #[test]
    fn plan_json_exposes_and_binds_suite_semantics_for_identical_inputs() {
        let root =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/execution-smoke/head");
        let facts = selector_extract::import_capture(
            &root.join("documents.jsonl"),
            Some(&root.join("syntax.jsonl")),
            &selector_extract::ExtractOptions {
                workers: 1,
                catalogue: Some(root.join("catalogue.json")),
                ..Default::default()
            },
        )
        .unwrap();
        let graph = selector_graph_build::build(
            &facts,
            &selector_graph_build::BuildOptions {
                workers: 1,
                include_models: false,
            },
        )
        .unwrap();
        let plan = |semantics, unscoped| {
            selector_plan::plan_guarded_with_semantics(
                &facts,
                &graph,
                selector_plan::PlanSeeds {
                    execution: &[],
                    declarations: &[],
                    unscoped,
                },
                &[],
                semantics,
            )
            .unwrap()
        };
        let shared = plan(SuiteSemantics::SharedState, false);
        let independent = plan(SuiteSemantics::Independent, false);
        assert_ne!(shared.identity(), independent.identity());
        assert_eq!(shared.assumptions() ^ independent.assumptions(), 16);
        for (plan, semantics, assumption) in [
            (&shared, "shared_state", false),
            (&independent, "independent_suites", true),
        ] {
            let json = plan_json(&facts, &graph, plan);
            assert_eq!(json["suite_semantics"], semantics);
            assert_eq!(
                json["selection_contract"]["version"],
                SelectionContract::VERSION
            );
            assert_eq!(
                json["selection_contract"]["bits"],
                if assumption { 496 } else { 480 }
            );
            assert_eq!(
                json["selection_contract"]["assumptions"],
                serde_json::json!(
                    SelectionContract::current(plan.suite_semantics())
                        .assumptions()
                        .collect::<Vec<_>>()
                )
            );
            assert_eq!(json["assume_independent_suites"], assumption);
            assert_eq!(
                json["suite_semantics_assumption_bit"],
                if assumption { 16 } else { 0 }
            );
        }
        let global = plan(SuiteSemantics::SharedState, true);
        let json = plan_json(&facts, &graph, &global);
        assert!(
            json["frontiers"]
                .as_array()
                .unwrap()
                .iter()
                .any(|frontier| {
                    frontier["root"]["node"].is_null() && frontier["root"]["unscoped"] == true
                })
        );
    }
    #[test]
    fn declared_platform_flags_require_explicit_independent_revision_authority() {
        let producer = "11".repeat(32);
        let valid = args(&[
            "enrich",
            "--platform-input",
            "platform.json",
            "--platform-producer",
            &producer,
            "--contexts",
            "contexts.json",
        ])
        .unwrap();
        valid.validate().unwrap();
        let options = platform_options(&valid).unwrap().unwrap();
        assert_eq!(options.contexts, PathBuf::from("contexts.json"));
        assert_eq!(options.producer.to_string(), producer);
        assert!(
            platform_options(&args(&["enrich"]).unwrap())
                .unwrap()
                .is_none()
        );
        for flags in [
            vec![
                "enrich",
                "--platform-input",
                "platform.json",
                "--contexts",
                "contexts.json",
            ],
            vec![
                "enrich",
                "--platform-input",
                "platform.json",
                "--platform-producer",
                &producer,
            ],
            vec![
                "query",
                "--platform-input",
                "platform.json",
                "--platform-producer",
                &producer,
                "--contexts",
                "contexts.json",
            ],
            vec![
                "run",
                "--platform-input",
                "platform.json",
                "--platform-producer",
                &producer,
                "--contexts",
                "contexts.json",
            ],
            vec![
                "run",
                "--base-platform-input",
                "base.json",
                "--base-platform-producer",
                &producer,
                "--contexts",
                "head-contexts.json",
            ],
        ] {
            assert!(args(&flags).unwrap().validate().is_err(), "{flags:?}");
        }
        args(&[
            "run",
            "--head",
            "head",
            "--base",
            "base",
            "--base-platform-input",
            "base-platform.json",
            "--base-platform-producer",
            &producer,
            "--base-contexts",
            "base-contexts.json",
            "--base-binary-map",
            "base-map.json",
        ])
        .unwrap()
        .validate()
        .unwrap();
    }
    #[test]
    fn native_stage_receipt_pins_platform_image_and_rejects_changed_reuse() {
        let directory = tempfile::tempdir().unwrap();
        let receipt = directory.path().join("receipt.json");
        let output = directory.path().join("facts.bin");
        selector_facts::codec::write(&output, &FactSnapshot::default()).unwrap();
        let binary = directory.path().join("binary.json");
        fs::write(&binary, b"native map").unwrap();
        let platform: Vec<_> = (0..7)
            .map(|index| {
                let path = directory.path().join(format!("platform-input-{index}"));
                fs::write(&path, format!("input{index}")).unwrap();
                path
            })
            .collect();
        let producers = BTreeMap::from([
            ("extract".into(), "11".repeat(32)),
            ("binary".into(), "22".repeat(32)),
        ]);
        let recording = recording::Recording::new(
            vec!["run".into()],
            receipt.clone(),
            Vec::new(),
            producers.clone(),
        )
        .unwrap();
        let mut invocation = args(&["run"]).unwrap();
        invocation.side = "head";
        invocation.recording = Some(Arc::new(std::sync::Mutex::new(recording)));
        record_stage(
            &invocation,
            "head.extract",
            &[],
            "extract",
            ContentHash::default(),
            &[],
            &[recording::StageFile {
                role: "facts",
                path: &output,
                kind: Some(selector_artifacts::ArtifactKind::Facts),
            }],
        )
        .unwrap();
        record_binary_prepared(&invocation, &binary, &platform, &output).unwrap();
        invocation
            .recording
            .as_ref()
            .unwrap()
            .lock()
            .unwrap()
            .finish()
            .unwrap();
        let limits = replay::ReplayLimits::default();
        let saved = replay::load_receipt(&receipt, &limits).unwrap();
        let stage = saved.stages.iter().find(|s| s.id == "head.enrich").unwrap();
        assert_eq!(stage.inputs.len(), 8);
        assert!(
            stage
                .inputs
                .iter()
                .any(|file| file.role == "platform_modules")
        );
        assert!(
            replay::validate_receipt(&receipt, &producers, &limits)
                .unwrap()
                .valid()
        );
        fs::write(&platform[4], b"changed runtime image").unwrap();
        let changed = replay::validate_receipt(&receipt, &producers, &limits).unwrap();
        assert!(!changed.valid());
        assert_eq!(
            changed.earliest_invalidation.as_deref(),
            Some("head.enrich")
        );
    }
    #[test]
    fn native_census_totals_include_unsampled_contexts_with_bounded_utf8_labels() {
        let name = "é".repeat(300);
        let census = native_class_metrics((0..65).map(|_| {
            selector_graph_build::binary_inputs::BinaryContextMetrics {
                context: &name,
                found: 2,
                unknown: 3,
                retained_bytes: 100,
                requests: 10,
                phase: "native-body",
                active_method: SymbolId(7),
                pending_methods: 4,
                deferred_admissions: 5,
                derived_methods: 6,
                method_slots_released: 7,
                method_slots_received: 11,
                retried_callers: 3,
                method_guard_rows: 6,
                scoped_dispatch_rows: 7,
                receiver_dispatch_rows: 10,
                trusted_runtime_models: 8,
                trusted_runtime_model_fallbacks: 9,
            }
        }));
        assert_eq!(census["contexts"], 65);
        assert_eq!(census["found"], 130);
        assert_eq!(census["unknown"], 195);
        assert_eq!(census["retained_class_bytes"], 6500);
        assert_eq!(census["requests"], 650);
        assert_eq!(census["deferred_admissions"], 325);
        assert_eq!(census["derived_methods"], 390);
        assert_eq!(census["method_slots_released"], 455);
        assert_eq!(census["method_slots_received"], 715);
        assert_eq!(census["retried_callers"], 195);
        assert_eq!(census["method_guard_rows"], 390);
        assert_eq!(census["scoped_dispatch_rows"], 455);
        assert_eq!(census["receiver_dispatch_rows"], 650);
        assert_eq!(census["trusted_runtime_models"], 520);
        assert_eq!(census["trusted_runtime_model_fallbacks"], 585);
        assert_eq!(census["sample_complete"], false);
        let sample = census["sample"].as_array().unwrap();
        assert_eq!(sample.len(), 64);
        assert_eq!(sample[0]["context"].as_str().unwrap().chars().count(), 256);
        assert_eq!(sample[0]["context_truncated"], true);
        assert_eq!(sample[0]["active_method"], 7);
        assert_eq!(sample[0]["pending_methods"], 4);
        assert_eq!(sample[0]["method_slots_released"], 7);
        assert_eq!(sample[0]["method_slots_received"], 11);
        assert_eq!(sample[0]["retried_callers"], 3);
        assert_eq!(sample[0]["method_guard_rows"], 6);
        assert_eq!(sample[0]["scoped_dispatch_rows"], 7);
        assert_eq!(sample[0]["receiver_dispatch_rows"], 10);
        assert_eq!(sample[0]["trusted_runtime_models"], 8);
        assert_eq!(sample[0]["trusted_runtime_model_fallbacks"], 9);
    }
    #[test]
    fn explicit_replay_output_moves_only_recorded_auxiliaries_and_honors_explicit_paths() {
        let dir = tempfile::tempdir().unwrap();
        let old = dir.path().join("old.json");
        let new = dir.path().join("new.json");
        let mut recorded = Args::parse([
            "query".to_owned(),
            "--output".into(),
            old.to_string_lossy().into_owned(),
            "--progress-jsonl".into(),
            dir.path().join("old.log").to_string_lossy().into_owned(),
            "--checkpoint-dir".into(),
            dir.path()
                .join("old-checkpoints")
                .to_string_lossy()
                .into_owned(),
            "--summary-cache".into(),
            dir.path()
                .join("shared-cache")
                .to_string_lossy()
                .into_owned(),
            "--resume-dir".into(),
            dir.path()
                .join("input-checkpoints")
                .to_string_lossy()
                .into_owned(),
        ])
        .unwrap();
        let requested = Args::parse([
            "replay".to_owned(),
            "--output".into(),
            new.to_string_lossy().into_owned(),
        ])
        .unwrap();
        relocate_replay_diagnostics(&mut recorded, &requested).unwrap();
        assert_eq!(
            recorded.path("progress-jsonl"),
            Some(dir.path().join("new.json.progress.jsonl"))
        );
        assert_eq!(
            recorded.path("checkpoint-dir"),
            Some(dir.path().join("new.json.checkpoints"))
        );
        assert_eq!(
            recorded.path("summary-cache"),
            Some(dir.path().join("shared-cache"))
        );
        assert_eq!(
            recorded.path("resume-dir"),
            Some(dir.path().join("input-checkpoints"))
        );
        assert!(recorded.path("full-evidence").is_none());
        assert!(recorded.path("replay-bundle").is_none());
        let mut no_progress = args(&["query", "--output", "original"]).unwrap();
        relocate_replay_diagnostics(&mut no_progress, &requested).unwrap();
        assert!(no_progress.path("progress-jsonl").is_none());
        let explicit = args(&[
            "replay",
            "--output",
            new.to_str().unwrap(),
            "--progress-jsonl",
            "explicit.log",
        ])
        .unwrap();
        let previous = recorded.path("progress-jsonl");
        relocate_replay_diagnostics(&mut recorded, &explicit).unwrap();
        assert_eq!(
            recorded.path("progress-jsonl"),
            previous,
            "the caller merge supplies its explicit path"
        );
    }
    #[test]
    fn rejects_typos_duplicates_and_zero_workers() {
        assert!(args(&["query", "--worker", "2"]).is_err());
        assert!(args(&["query", "--workers", "2", "--workers", "4"]).is_err());
        assert!(
            args(&["query", "--workers", "0"])
                .unwrap()
                .workers()
                .is_err()
        );
    }
    #[test]
    fn binary_admission_honors_workers_and_its_explicit_memory_limit() {
        let a = args(&[
            "enrich",
            "--workers",
            "3",
            "--binary-memory-budget",
            "12345",
        ])
        .unwrap();
        let options = binary_options(&a).unwrap();
        assert_eq!(options.workers, 3);
        assert_eq!(options.max_retained_bytes, 12345);
        assert!(
            binary_options(&args(&["enrich", "--binary-memory-budget", "0"]).unwrap()).is_err()
        );
    }
    #[test]
    fn repeated_changes_are_canonical() {
        let a = args(&[
            "query",
            "--changed",
            "b.scala",
            "--changed",
            "a.scala",
            "--changed",
            "a.scala",
        ])
        .unwrap();
        assert_eq!(a.changed().unwrap(), ["a.scala", "b.scala"]);
    }
    #[test]
    fn whole_diff_requires_paired_inputs_and_excludes_requested_scopes() {
        for command in ["query", "audit-changes"] {
            let paired = [
                command,
                "--base-facts",
                "base",
                "--base-graph",
                "graph",
                "--whole-diff",
            ];
            args(&paired).unwrap().validate().unwrap();
            for option in ["--changed", "--changed-list", "--seed"] {
                let mut mixed = paired.to_vec();
                mixed.extend([option, "requested"]);
                assert!(
                    args(&mixed)
                        .unwrap()
                        .validate()
                        .unwrap_err()
                        .to_string()
                        .contains("cannot be combined")
                );
            }
            assert!(
                args(&[command, "--whole-diff"])
                    .unwrap()
                    .validate()
                    .unwrap_err()
                    .to_string()
                    .contains("paired")
            );
            assert!(
                args(&[command, "--base-facts", "base", "--whole-diff"])
                    .unwrap()
                    .validate()
                    .is_err()
            );
        }
        args(&["run", "--base", "base", "--whole-diff"])
            .unwrap()
            .validate()
            .unwrap();
        assert!(args(&["run", "--whole-diff"]).unwrap().validate().is_err());
        assert!(
            args(&["build", "--whole-diff"])
                .unwrap()
                .validate()
                .is_err()
        );
    }
    #[test]
    fn explicit_seed_keeps_empty_requested_source_scope_while_whole_diff_seeds_changes() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/execution-smoke");
        let load = |side: &str| {
            let dir = root.join(side);
            let facts = selector_extract::import_capture(
                &dir.join("documents.jsonl"),
                Some(&dir.join("syntax.jsonl")),
                &selector_extract::ExtractOptions {
                    workers: 1,
                    catalogue: Some(dir.join("catalogue.json")),
                    ..Default::default()
                },
            )
            .unwrap();
            let graph = selector_graph_build::build(
                &facts,
                &selector_graph_build::BuildOptions {
                    workers: 1,
                    include_models: true,
                },
            )
            .unwrap();
            (facts, graph)
        };
        let (base, bg) = load("base");
        let (head, hg) = load("head");
        let requested = prepare_query(
            &args(&["query", "--seed", "executioncase/Unchanged.value()."]).unwrap(),
            &base,
            &bg,
            &head,
            &hg,
            true,
        )
        .unwrap();
        let scope = requested.seeds.change_scope.as_ref().unwrap();
        assert_eq!(
            scope.mode,
            selector_result::SourceChangeMode::RequestedPaths
        );
        assert!(scope.requested_paths.is_empty());
        assert!(scope.outside_count > 0);
        assert!(requested.seeds.base.is_empty());
        assert_eq!(requested.seeds.head.len(), 1);
        assert_eq!(
            head.text(head.symbols[hg.nodes[requested.seeds.head[0].index()].symbol.index()].name),
            "executioncase/Unchanged.value()."
        );
        let whole = prepare_query(
            &args(&["query", "--whole-diff"]).unwrap(),
            &base,
            &bg,
            &head,
            &hg,
            true,
        )
        .unwrap();
        assert_eq!(
            whole.seeds.change_scope.as_ref().unwrap().mode,
            selector_result::SourceChangeMode::SnapshotDelta
        );
        assert!(!whole.seeds.base.is_empty());
        assert!(!whole.seeds.head.is_empty());
    }
    #[test]
    fn query_options_bound_diagnostics_without_disabling_core_progress() {
        let options = args(&[
            "query",
            "--census-capacity",
            "0",
            "--census-stride",
            "1",
            "--max-context-variants",
            "3",
            "--workers",
            "2",
            "--max-steps",
            "1",
        ])
        .unwrap()
        .solve_options()
        .unwrap();
        assert_eq!(options.census.capacity, 0);
        assert_eq!(options.census.evaluation_stride, 1);
        assert_eq!(options.workers, 2);
        assert_eq!(options.max_steps, 1);
        assert_eq!(
            options.context_policy,
            selector_solve::ContextPolicy::BoundedArguments {
                max_variants_per_receiver: 3
            }
        );
        assert!(!options.retain_context_evidence);
        assert!(
            args(&["query", "--census-capacity", "65537"])
                .unwrap()
                .solve_options()
                .is_err()
        );
        assert!(
            args(&["query", "--census-stride", "0"])
                .unwrap()
                .solve_options()
                .is_err()
        );
        assert!(
            args(&["query", "--full-report"])
                .unwrap()
                .solve_options()
                .unwrap()
                .retain_context_evidence
        );
    }
    #[test]
    fn invalid_query_and_replay_controls_fail_before_program_admission() {
        let invalid = args(&[
            "query",
            "--head-facts",
            "does-not-exist",
            "--head-graph",
            "absent",
            "--max-steps",
            "0",
        ])
        .unwrap();
        assert!(
            execute_recorded(invalid)
                .unwrap_err()
                .to_string()
                .contains("--max-steps")
        );
        for options in [
            vec!["query", "--replay-family"],
            vec!["query", "--replay-bundle", "out"],
            vec!["query", "--replay-revision", "other"],
            vec!["query", "--replay-family-contexts", "65"],
        ] {
            assert!(args(&options).unwrap().validate().is_err());
        }
    }
    #[test]
    fn revision_workers_and_memory_share_one_request_budget() {
        for workers in [2, 3, 4, 8, 16] {
            let options = selector_solve::SolveOptions {
                workers,
                memory_budget_bytes: 1025,
                ..Default::default()
            };
            let (base, head) = revision_options(&options, workers);
            assert_eq!(base.workers + head.workers, workers);
            assert!(base.workers > 0 && head.workers > 0);
            assert_eq!(base.shard_count + head.shard_count, workers);
            assert_eq!(base.memory_budget_bytes + head.memory_budget_bytes, 1025);
            assert_eq!(base.max_contexts, options.max_contexts);
            assert_eq!(head.max_steps, options.max_steps);
        }
    }
    #[test]
    fn failed_output_does_not_replace_existing_result() {
        let d = tempfile::tempdir().unwrap();
        let p = d.path().join("result.json");
        fs::write(&p, "original").unwrap();
        let a = args(&["query", "--output", p.to_str().unwrap()]).unwrap();
        assert!(
            publish_output(&a, |out| {
                out.write_all(b"partial")?;
                Err("failed report".into())
            })
            .is_err()
        );
        assert_eq!(fs::read_to_string(p).unwrap(), "original");
    }
    #[test]
    fn graph_admission_rejects_cross_body_operation_provenance() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/compiler-smoke");
        let facts = selector_extract::import_capture(
            &root.join("documents.jsonl"),
            Some(&root.join("syntax.jsonl")),
            &selector_extract::ExtractOptions {
                workers: 1,
                ..Default::default()
            },
        )
        .unwrap();
        let mut graph = selector_graph_build::build(
            &facts,
            &selector_graph_build::BuildOptions {
                workers: 1,
                include_models: true,
            },
        )
        .unwrap();
        verify_binding(&facts, &graph).unwrap();
        let edge = graph
            .edges
            .iter()
            .position(|e| !e.operation.is_none())
            .unwrap();
        let source_body = graph.nodes[graph.edges[edge].source.index()].body;
        graph.edges[edge].operation = OperationId(
            facts
                .operations
                .iter()
                .position(|op| op.body != source_body)
                .unwrap() as u32,
        );
        assert!(
            verify_binding(&facts, &graph)
                .unwrap_err()
                .to_string()
                .contains("another source body")
        );
    }
    #[test]
    fn change_audit_preserves_exact_uncaptured_path_without_running_solver() {
        let root =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/execution-smoke/head");
        let facts = selector_extract::import_capture(
            &root.join("documents.jsonl"),
            Some(&root.join("syntax.jsonl")),
            &selector_extract::ExtractOptions {
                workers: 1,
                catalogue: Some(root.join("catalogue.json")),
                ..Default::default()
            },
        )
        .unwrap();
        let graph = selector_graph_build::build(
            &facts,
            &selector_graph_build::BuildOptions {
                workers: 1,
                include_models: true,
            },
        )
        .unwrap();
        let args = args(&["audit-changes", "--changed", "absent/File.scala"]).unwrap();
        let prepared = prepare_query(&args, &facts, &graph, &facts, &graph, true).unwrap();
        assert!(prepared.source_conservative);
        assert!(!prepared.auxiliary_conservative);
        assert_eq!(prepared.source_paths, ["absent/File.scala"]);
        assert!(prepared.seeds.guard_causes.iter().any(|cause| cause.reason
            == selector_result::ChangeGuardReason::UncapturedChangedPath
            && cause.path.as_deref() == Some("absent/File.scala")));
        assert!(prepared.seeds.head.is_empty());
        assert!(prepared.seeds.base.is_empty());
    }
    #[test]
    fn cached_graph_recovers_missing_and_corrupt_artifacts_with_identical_identity() {
        let fixture = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/compiler-smoke");
        let facts = selector_extract::import_capture(
            &fixture.join("documents.jsonl"),
            Some(&fixture.join("syntax.jsonl")),
            &selector_extract::ExtractOptions {
                workers: 1,
                ..Default::default()
            },
        )
        .unwrap();
        let dir = tempfile::tempdir().unwrap();
        let mut catalogue = Catalogue::open(&dir.path().join("catalogue.sqlite")).unwrap();
        let args = args(&["run", "--workers", "1"]).unwrap();
        let original = cached_graph(&args, &mut catalogue, dir.path(), &facts).unwrap();
        let artifact = fs::read_dir(dir.path())
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .find(|path| path.extension().is_some_and(|extension| extension == "bin"))
            .unwrap();
        fs::remove_file(&artifact).unwrap();
        let rebuilt = cached_graph(&args, &mut catalogue, dir.path(), &facts).unwrap();
        assert_eq!(rebuilt.identity, original.identity);
        fs::remove_file(&artifact).unwrap();
        fs::write(&artifact, b"damaged artifact").unwrap();
        let rebuilt = cached_graph(&args, &mut catalogue, dir.path(), &facts).unwrap();
        assert_eq!(rebuilt.identity, original.identity);
        let preserved = fs::read_dir(dir.path())
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .find(|path| {
                path.file_name()
                    .unwrap()
                    .to_string_lossy()
                    .contains(".rejected-")
            })
            .unwrap();
        assert_eq!(fs::read(preserved).unwrap(), b"damaged artifact");
        verify_binding(&facts, &rebuilt).unwrap();
    }
}
