# Independently compiled execution fixture

This fixture compiles real Scala 2.13.18 source with the SemanticDB 4.15.2 compiler
plugin and ScalaTest 3.2.19, then generates genuine Scalameta syntax through the
native Rust `syntax` command. Original protobufs, source bytes and generated JVM
classfiles are retained. Native Rust `capture` produces `documents.jsonl`;
`reference-documents.jsonl` is a separate historical-decoder comparison artifact.
No expected selection, legacy graph, or hand-authored edge enters extraction.

Three real ScalaTest `Suite` subclasses exercise **suite construction**. There are
zero registered test cases: this deliberately avoids claiming coverage of the
external registration engine. ScalaTest Runner successfully constructs/runs all
three suites. A separate JVM checker then establishes the observed values:

| Suite | Base | Head | Source-reviewed change impact |
| --- | ---: | ---: | --- |
| `AffectedSuite` | 41 | 42 | Included: invokes a returned callback to `Changed.value`. |
| `UnaffectedSuite` | 7 | 7 | Excluded: same callback factory with an independent callback. |
| `DormantSuite` | 7 | 7 | Excluded: its factory referencing `Changed` is never invoked. |

`expected.json` freezes these independent evaluator assertions. It is never a
selector input. A complete precise result must have real execution contexts,
select exactly `AffectedSuite`, retain full callback/capture evidence, and guard
no suite. External constructor uncertainty must be discharged by an exact proven
model or captured bytecode; an entire ScalaTest API cannot be assumed pure.

`base/` and `head/` have identical sources except the constant return value in
`src/executioncase/Changed.scala`. Revision identifiers are explicitly source-tree
hash prefixes, not claims that these fixtures came from Git revisions. Their
captured catalogue contains the actual JVM names observed by the independent
checker. `capture.json` has portable relative raw/source bindings and hashes.
`manifest.json` pins compiler/plugin/framework inputs, commands and output files.
The exact JVM classpath starts with the captured own classes and a small
`framework-prefix.jar` containing unmodified original framework classes. Independent
JVM execution uses that same prefix. For portable Rust tests the original suffix
jars are explicitly marked unavailable; lookups stop there and cannot treat the
suffix as empty. Required bound classes must resolve in the captured prefix.
Third-party attribution and the original license are included. This proves a
particular reachable initialization scope, not complete ScalaTest implementation
coverage.

Regenerate offline after building the native executable:

```sh
cargo build -p selector-cli --profile perf-dev --offline
python3 tools/prepare_execution_smoke.py
python3 tools/prepare_execution_smoke.py --verify
```

The generator reads cached compiler/plugin/framework jars and launches Java/Rust.
Its Python reference-decoder use is fixture validation only, never a production
runtime requirement. Compiler classes and SemanticDB bytes are generated from the
checked-in source, not synthesized by the evaluator.
