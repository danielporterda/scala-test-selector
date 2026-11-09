This is an actual Scala 2.13.18 / SemanticDB 4.15.2 capture. A separately compiled
library supplies a curried implicit method returning `Int` and a method returning
`Function0`. Caller capture intentionally omits the library declarations, so the
external signature is absent until exact classfile admission.

`WordSuite` extends ScalaTest 3.2.19 `AnyWordSpec` with `Matchers`. Its compiler
synthetic for `convertToStringShouldWrapper` is exactly
`Apply(Apply(Id(method), [OriginalTree]), [Position.here, Prettifier.default])`.
It reproduces the external multi-clause/non-function ambiguity without inventing
semantic records. The source-known two-clause method and genuine returned/stored
callbacks are controls. The stored callback executes twice; it cannot be erased
as a redundant parameter clause.

The independent JVM receipt reports:

```text
external:1:1
source:2:2
returned:4:4
reused:16:32:32
registered:1:0
executed:8
```

WordSuite registers one test without executing its effect, then the JVM executes
that test once. A separate real ScalaTest runner confirms one test passed.
Original compiler protobufs, native normalized documents, source-bound Scalameta
AST, original classfiles, javap output, exact dependency hashes and commands are
retained. `binary.json` uses the actual ordered compile/runtime classpath.

Verify without compiling or invoking the JVM:

```sh
python3 tools/prepare_curried_synthetics.py --verify
cargo test --locked --offline -p selector-acceptance --test curried_synthetics
```

Regeneration is an explicit offline developer action requiring the pinned cached
JDK/Scala/ScalaTest tooling:

```sh
python3 tools/prepare_curried_synthetics.py --selector artifacts/phase2-producer/selector-semantic-fixed
```
