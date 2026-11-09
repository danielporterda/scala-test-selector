# Direct-call parity companion

The captured source differs from `execution-smoke` by making the two executed
field initializers call `Changed.value()` and `Unchanged.value()` directly.
`Factory.make` and dormant methods remain in the compiler input, but no executed
path uses the returned-callback factory. Both analyzers must exclude the dormant
suite and the unaffected suite. Independent JVM values and real ScalaTest Runner
logs are preserved; no test bodies are registered.

`tools/prepare_parity_direct.py` reuses the pinned actual compiler/JVM producer
without changing either analyzer. Raw protobufs, exact classfiles, native syntax,
source hashes and JVM observations are frozen. Original third-party notices are
included alongside the unmodified framework prefix.

`expected.json` is evaluator-only. It records the exact three unresolved legacy
superclass-constructor identities as a visible diagnostic difference; Rust binds
the corresponding actual initializer bytecode. See `tools/PARITY.md` for the
prospective comparison and timing criteria and its deliberately limited scope.
