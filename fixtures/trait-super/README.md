# Genuine trait and super dispatch

Scala 2.13.18 and SemanticDB 4.15.2 compile the checked-in source. A separate JVM
execution asserts `Uses.plain == 2` through the rightmost `Layer` mixin, and
`Uses.qualified == 1` through explicit `super[Root]`. Raw compiler protobuf bytes,
native decoded documents and genuine Scalameta syntax are retained with hashes.
The source-reviewed expectations are evaluator-only. This fixture checks ordered
parents and exact super receiver/qualifier identities; it has no suite catalogue
and does not claim complete test selection or external-library execution coverage.

Regenerate with `python3 tools/prepare_trait_super.py`; verify frozen inputs with
`python3 tools/prepare_trait_super.py --verify`. Generation uses the existing pinned
offline compiler toolchain and native Rust capture/syntax executable.
