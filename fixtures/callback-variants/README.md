# Callback code and captured-data fixture

Real Scala 2.13.18/SemanticDB 4.15.2 compiler output and JVM construction observations
cover six different lexical callbacks through `Shared.run`. Only the sixth callback
calls the changed method. A separate six-suite cohort passes callbacks from the
same lexical factory site with different captured data; bounded joining within
that code family must preserve the changed alternative. `Opaque.callback` executes
as 99 in the JVM, while its separately compiled body is deliberately unadmitted in
the analysis input. It remains an unknown callback, never a purity contract.

The public planner/query/selection regression declares each cohort's runnable
universe explicitly and reseals its suite inventory. All admitted compiler bodies
remain present. This isolates callback precision from the sound shared-heap guard
that an opaque runnable component can impose on other heap-reading components.
The three cohorts are separate queries, not a claim that their joint opaque query
can safely exclude the same suites.

These are actual ScalaTest Suite constructor lifecycles with zero registered test
bodies, independently constructed and run by ScalaTest Runner. No CI reduction or
wall-time claim follows from the suite counts. Frozen base/head JVM values differ
only at the sixth lexical and sixth captured callback, 41 to 42.

`python3 tools/prepare_callback_variants.py --selector <frozen selector>` prepares
the fixture using cached jars. `--verify` checks pinned fixture files without a JVM.
