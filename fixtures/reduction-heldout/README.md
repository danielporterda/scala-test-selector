This held-out compiler/JVM mutation changes `Unchanged.value` from 7 to 9, sharing
the original exact `execution-smoke/base` capture. The original acceptance change
instead changed `Changed.value` from 41 to 42. Independent JVM construction now
observes `[41,9,9]`; the opposite callback family and direct initializer change,
while `AffectedSuite` remains unrelated. The actual ScalaTest runner completes
all three suites. This covers construction lifecycle and zero registered tests.

The head source, raw SemanticDB protobufs, native syntax, classfiles, commands,
toolchain hashes and observations are frozen. The verified original framework
prefix is shared, not replaced with assumed-pure framework behavior. Expectations
are evaluator-only and never supplied to graph construction.

Offline regeneration: `python3 tools/prepare_reduction_heldout.py`. Hash check:
`python3 tools/prepare_reduction_heldout.py --verify`. Neither command runs in the
fast developer smoke/replay loop.
