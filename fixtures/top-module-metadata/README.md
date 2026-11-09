# Pinned top-level module metadata

This signature-only capture reads the existing Scala `Effects.note` method from `../selected-external-apply/library.jar`. The caller SemanticDB, native AST, class bytes and independent JVM observations remain in `../external-metadata`; no source or test JVM was rerun.

`manifest.json` and the raw SemanticDB payload are unchanged producer output. `native-contexts.json` is the previously approved explicit native projection of the original direct-scalac command: its source root and two physical JAR objects come from that command. It preserves the absent Java-runtime feature. `native-inputs-receipt.json` retains this distinction from the smaller original context capture.

`fixture.json` pins the copied raw receipts and unchanged dependencies. `tooling/` preserves the exact historical producer source inputs as reference snapshots; those pins do not depend on future edits to the live producer. The general producer uses Scala 2.13.18/SemanticDB 4.15.2, strict signatures, no JDK or ambient classpath, and verified class-only JAR views without manifest expansion. Its one JVM batch took 0.304 s and peaked at 100,204,544 bytes on the shared host; this is a metadata-read diagnostic, not a selector or CI speed result. The redundant module class lacks its own ScalaSig and was rejected; the exact requested method was recovered from its ScalaSig-bearing companion class.

Reproduction uses `tools/produce_external_metadata.py` with the pinned `requests.json`, `native-contexts.json`, `native-binary-map.json`, `--compiler-input-root ../external-metadata`, `--symbol 'selectedexternal/Effects.note().'`, `--max-requests 1`, `--heap-mib 512`, a compatible native selector, and a fresh output directory. All original execution paths in raw receipts are preserved.

The acceptance test proves the compiler-witnessed module read uses an explicit adapter retaining ordinary class initialization, the real static `MODULE$` read, and native body/field effects. Missing metadata or an unavailable earlier provider must leave the source read unresolved. It makes no purity or test-exclusion claim.
