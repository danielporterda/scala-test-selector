# Compiler default and constructor forms

These inputs were compiled with Scala 2.13.18 and SemanticDB 4.15.2. Each side
contains five source files, thirteen independently constructed ScalaTest suites,
the original SemanticDB, hash-bound native syntax, and the genuine classfiles.
The source change replaces `Effects.changed()`'s result, 41, with 42.

The JVM observations and ScalaTest discovery are retained in `execution.log` and
`scalatest.log`. They establish seven affected suites and six exclusions across
omitted and explicit ordinary defaults, case-class apply/new/copy defaults,
primary and secondary constructors, by-name defaults that are read or ignored,
and a default getter that receives an earlier parameter clause. The selector's
expected results are compared with these observations for one and four workers.

Source lowering must use the exact compiler constructor occurrence, including
zero-width delegation anchors. A constructor overload declaration is never an
eager class initializer. Default binding requires both the compiler formal's
DEFAULT property and the exact compiler-owned getter. Missing evidence remains
an explicit uncertainty. Generated case-class methods are supplied by the
retained classfiles; the ordinary default getter also has a source-only test.

Regenerate with `python3 tools/prepare_constructor_forms.py --selector PATH`.
Check the complete frozen receipt with
`python3 tools/prepare_constructor_forms.py --verify`. Preparation compiles and
runs Scala; Rust analysis reads only the retained inputs.
