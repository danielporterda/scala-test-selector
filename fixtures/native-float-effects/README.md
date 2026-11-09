# Native floating-point effect controls

`Probe.java` is compiled with the pinned local JDK and executed independently
of the selector. The retained classes, archive, `javap` output, JVM observations
and generator are hashed in `manifest.json`. Regenerate with
`python3 tools/prepare_native_float_effects.py`; verify retained bytes with
`python3 tools/prepare_native_float_effects.py --verify`.

The normal Rust test loop reads these retained bytes and does not launch Java.
The public acceptance target `native_float_effects` checks all eight division
and remainder opcodes, native admission, ordinary lowering, graph construction
and solving. Floating results stay unknown data. Integer/long zero-divisor
frontiers, callbacks (including handler-only calls), writes, native calls,
reflection, monitors, array access and unsupported dynamic calls stay visible.

The [JVM instruction specification](https://docs.oracle.com/javase/specs/jvms/se21/html/jvms-6.html#jvms-6.5.ddiv)
defines floating division and remainder as non-throwing, including zero divisors.
The explicit-throw observation is a separate diagnostic; this repair changes
only opcodes 110, 111, 114 and 115. These callable controls establish no real CI
suite exclusion, runtime catalogue completeness or performance improvement.
