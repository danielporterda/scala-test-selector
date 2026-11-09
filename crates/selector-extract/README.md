# Compiler capture normalization

`import_capture(input, syntax, &ExtractOptions)` admits the native captured
SemanticDB JSONL (plain or gzip), optionally joins the source-bound Scalameta
sidecar, and returns the flat `selector-facts` snapshot. `EXTRACTOR_VERSION` names
the in-memory producer contract. Saved artifact content hashes are authoritative.

The compiler rows require captured source text and matching compiler MD5, validate
optional source SHA256, and reject mixed/incorrect revisions. Missing, stale,
unsupported and unresolved evidence remains explicit. Compiler UTF-16 positions
become validated UTF-8 byte spans; offsets splitting a surrogate pair are invalid.
Compiler global overload descriptors remain intact and local IDs remain scoped to
their source document.

Workers normalize independent documents into bounded local fact partitions.
Publication deterministically remaps pooled strings/IDs and appends flat columns.
Workers never clone the program. The decoded batch, local interning indexes,
source-coordinate maps and temporary compiler-expression IR have explicit drop
boundaries. Borrowing signature projection and small stack argument/child buffers
avoid allocating a JSON object graph or argument vector for ordinary records.

A supplied `compiler_contexts` manifest, or an automatically discovered sibling
`compiler-contexts.json.gz`, binds consumer references through the actual ordered
classpath's project output origins. Source hashes, revision and product hashes
must match. Provider definitions stay separate; an opaque earlier binary, absent
origin, or ambiguous origin preserves an unknown reference. A later overload may
not bypass an earlier class provider. When a positive source candidate follows
another project output, that binding stays a possible target and carries a
consumer-scoped `ContextConflict`: source records do not prove the absence of
Java/generated classes in an earlier output. `compiler_inputs::admit` can verify
relocated product directories against the captured full file inventory hash and
retain complete class names in one immutable snapshot. Passing that snapshot in
`ExtractOptions.compiler_inputs` proves earlier class absence where the entire
product matches; a matching earlier Java/generated class blocks a later source
binding. Changed, missing or incomplete products preserve qualified candidates
and `ContextConflict`. Include the admission identity before an extraction cache
lookup. With syntax, the narrowest owning body receives the obligation;
declaration dependencies retain declaration scope.

The syntax sidecar is JSONL `{path,source_sha256,producer_sha256,ast}` from the
pinned `ScalaSpans` producer. Compiler occurrences establish every source target;
syntax establishes executable ownership, arguments and deferred boundaries.
Typed function parameters, returned function applications, by-name actuals,
compiler-inserted function trees, eager/lazy initialization and compiler default
getters have distinct recipes. Macro expansion runtime effects, unavailable
binary bodies, unsupported result/pattern forms and incomplete parameter/default
bindings remain conservative obligations.

Owned execution recipe hashes exclude deferred child bodies. Synthetic recipe
identities use structural ordinals within their compiler owner, while source
positions remain separate evidence. Consequently, changing a dormant callback
body does not change the eager factory recipe, and comments do not rename
closures.

`toolchain` invokes and validates the pinned external Scala/Scalameta producer;
`raw_capture` decodes raw SemanticDB protobufs natively. Neither path needs a
Python runtime. The original raw inputs and external producer identities are
preserved for independent evaluation.

Useful checks:

```sh
cargo test -p selector-extract --offline
cargo test -p selector-acceptance --test compiler_capture --offline
cargo run -p selector-extract --example import --profile perf-dev --offline -- CAPTURE.jsonl.gz SYNTAX.jsonl 4
cargo run -p selector-extract --example signature_allocations --profile perf-dev --offline -- CAPTURE.jsonl.gz
```

Pass `-` for the syntax argument in the importer example to measure compiler
normalization independently. Allocation assays are instrumented and should not be
used as wall-clock throughput measurements.
