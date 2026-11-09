This fixture freezes actual Scala 2.13.18 / SemanticDB 4.15.2 desugaring of nested
Future comprehensions. `Pipeline.execute` contains an outer comprehension and a
curried by-name `clueF` scope whose inner comprehension has a value enumerator,
then two further generators. The JVM exercises inherited source code through
`ActiveSuite`. `DormantSuite` stores the other comprehension in a closure.

Independent JVM observations are:

```text
dormant-before:0
active:first,clue:guard,load:3,check:3,save:3,after:3,finish
dormant-invoked:clue:dormant,load:99,check:99,save:99,after:99
```

The parasitic execution context makes the observed order deterministic. The
validation program awaits completion before inspecting the log. These are suite
construction/invocation controls with zero registered testcases, not a measured
test-reduction result. A separate actual ScalaTest runner completes both suites.

Original compiler protobuf, native normalized documents, source-bound Scalameta
AST, compiled classfiles and javap output are retained with exact source/tool/JAR
hashes. Synthetics are enabled explicitly. Expected events are evaluator evidence
and are never imported as graph facts.

Verify the frozen inputs without a JVM:

```sh
python3 tools/prepare_for_comprehension.py --verify
```

Regeneration uses the pinned cached toolchain and a native selector capture/syntax
producer, with no repository/SBT compilation:

```sh
python3 tools/prepare_for_comprehension.py --selector artifacts/phase2-producer/selector-scoped-fixed
```
