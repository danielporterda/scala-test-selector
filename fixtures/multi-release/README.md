# Genuine multi-release JAR controls

Java21 `javac` compiles three actual `mr.Probe.value()` implementations with
`--release 8`, `--release 17` and `--release 21`. Deterministic JARs contain the
base entry and, except for `plain.jar`, the version17/21 entries. Only
`multi-release.jar` declares `Multi-Release: true`; the false, missing-attribute
and missing-manifest variants must keep the base implementation.

Independent Java21 class-loader runs set `jdk.util.jar.version=8,17,21`. A separate
`JarFile` program explicitly selects each `Runtime.Version` and reports the
physical entry name. The manifest freezes all commands, producer identity,
class/JAR/source hashes and results. No expected output enters analyzer modeling.

Generate with `python3 tools/prepare_multi_release.py`; verify frozen files with
`python3 tools/prepare_multi_release.py --verify`. JVM compilation/execution uses
at most 256 MiB heap and two visible CPUs per small command.
