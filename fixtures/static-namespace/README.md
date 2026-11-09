# Java static namespace compiler fixture

Actual Scala callers distinguish Java static class receivers, Scala module values,
Java instances and class literals. The pinned JVM observations prove static class
initialization occurs on a real call, not on `classOf` or dormant closure creation;
module and instance initialization have independent counters. The JVM also rejects
an earlier same-owner instance-method shadow with IncompatibleClassChangeError.

Analysis admits verified classfiles from `bytecode.jar`. Only the exact static
method receiver can become an unused EMPTY constant; its native method body and
class-initialization effects remain. Scala modules, instance methods, unavailable
prefixes and the real wrong-staticness shadow are conservative controls. A class
literal is type data, not a runtime static-namespace proof or an initialization.

Frozen SemanticDB synthetics, native AST, source, classes, javap output and independent
JVM observations are retained. This is a bounded mechanism fixture with no CI
catalogue or registered tests. Generate using `python3 tools/prepare_static_namespace.py
--selector <frozen selector>`; `--verify` validates pinned files without a JVM.
