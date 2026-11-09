# Anonymous construction compiler fixture

Genuine Scala 2.13.18/SemanticDB 4.15.2 output, with synthetics enabled and native
Scalameta ASTs, records local anonymous classes rather than inventing owners from
source names. The pinned JVM execution distinguishes trait initialization,
constructor argument effects, nonempty anonymous body effects, deferred creation,
and overridden methods that execute only when called.

The empty `new Parent {}` case admits only a complete compiler-owned anonymous
class recipe. Parameterized class constructors, nonempty anonymous initialization
and anonymous method declarations are conservative controls for that narrow rule;
their runtime observations do not authorize empty-effect contracts. Dormant
closure creation must not execute the anonymous initializer.

Normal tests use the frozen compiler/source/class bytes without invoking a JVM.
Regenerate with `python3 tools/prepare_anonymous_construction.py`; `--verify`
checks pinned files and toolchain jars without compiling or executing anything.
This fixture has no CI catalogue or registered test cases.
