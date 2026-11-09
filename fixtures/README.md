# Real compiler fixtures

`compiler-smoke/documents.jsonl` contains two complete original capture rows from
the sealed PR7646 head `c759ad48a1dffcbc4cc0abc6527a0252ced85f6b`. JSONL row bytes
and source/compiler record ordering are retained exactly. The raw protobuf files
are copied by matching their SHA256 from the sealed raw layers. Their names are
their content hashes. Sources are also supplied as ordinary UTF-8 files.

`syntax.jsonl` contains newly generated native ScalaSpans output from an actual
JVM invocation over both exact captured source texts. It contains members,
owners, call sites and value expressions, and is consumed directly by the Rust
extractor. `native-tooling.json` records the exporter digest and ordered Scala /
Scalameta jar hashes. The wrapper producer ID is the exporter source digest;
the broader ordered toolchain identities are retained separately. This syntax
output is newly generated, not a historical PR7646 syntax capture.

`helper-syntax.jsonl` separately retains the independently captured helper-shadow
Scalameta lowering for `Clock.scala`. Its source bytes and SHA256 match exactly. Its original compiler
document has identical symbol/occurrence/synthetic multisets, but occurrence
ordering and raw input hashes differ from the selected PR7646 capture. The
fixture does not substitute that older document for the PR7646 row or relabel
its different schema as ScalaSpans. The independently reviewed Clock method-body
ranges agree across both syntax producers.

`manifest.json` records upstream revisions, producer identities, byte counts,
hashes, source/build contexts and the fixture's coverage boundary. No source
parsing, compiler invocation or Python execution is required to use these files
in Rust tests. No `build.rs` invokes fixture preparation.

`expected.json` is an evaluator-only assertion file. The two direct calls have
been checked against exact source text, compiler references and separate syntax
body ranges. The declaration assertions check concrete kind/override identities.
These are independent of previous selector outputs. They do not constitute a
whole-program soundness oracle or a complete suite catalogue. Never install these
expected calls as production graph input.

Development-only reproduction from the repository root:

```sh
python3 ci-cost-study/rust-selector/fixtures/prepare.py
python3 ci-cost-study/rust-selector/fixtures/prepare.py --verify
```

The first command uses the original local large capture inputs, validates their
hashes, and rewrites the generated fixture files while retaining the checked-in
native syntax output. Installing a newly produced native output requires
`--native-syntax /path/to/syntax.jsonl --native-tooling /path/to/tooling.json`;
this validates source, exporter and ordered jar hashes. The second needs only the
checked-in fixture outputs and verifies their integrity and source-reviewed
assertions. `expected.json` is maintained separately and is never generated from
an analyzer result. Rust acceptance tests must additionally exercise importer
integrity and graph construction directly.

Synthetic mutation controls should be created in test memory by modifying one
of these admitted fixture records, and named as such: stale source hash, false
compiler-MD5 match, conflicting source contexts, negative or out-of-bounds ranges,
and truncated/malformed raw bytes. Such mutations must not acquire genuine
capture provenance.
