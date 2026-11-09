These are genuine classfiles extracted, without recompilation, from ScalaTest
3.2.19 `scalatest-wordspec_2.13` and `scalatest-core_2.13`. The manifest pins the
complete original provider JAR hashes and exact ZIP entry/class hashes. The
subset contains 29 classes (396,815 class bytes).

The complete, unmodified `scalatest-wordspec_2.13-3.2.19.jar` is vendored here
for portable native-admission tests. It is 134,854 bytes with SHA-256
`08050f3d05c72575cac29a1483185b443d5f9f34c1fcf80c683083330385ef93`.
`manifest.json` records its fixture-relative path in the WordSpec provider's
`local_path`; the original cache path is provenance only. Tests should use this
local archive and its exact hash instead of a Coursier cache path. The original
Maven POM, Apache 2.0 license and attribution are retained under `provenance/`,
`LICENSE-APACHE` and `THIRD-PARTY-NOTICE.txt`. The original archive contains no
LICENSE, NOTICE or COPYING entry; its bytes have not been repackaged.

`methods.json` binds 256 selected exact method ABIs and Code hashes to those
class hashes. `protocol.json` retains the independently decoded calls, fields,
allocations, dynamic bootstrap references and limited local transport for the
initial WordSpec protocol review. Neither inventory asserts complete effects.
The original extraction tool is retained as a provenance snapshot, alongside
the original diagnostic location/hash. It is not a portable fixture generator.

Run `python3 fixtures/scalatest-execution/verify.py --self-test` from the Rust
workspace. Verification is offline and launches no JVM or compiler. It checks
the complete local archive pin and all 10 extracted WordSpec classes against
their original ZIP members, without opening any external cache path. Six
in-memory adverse controls reject a forged Code hash, wrong descriptor, an
abstract method relabeled as an empty body, a truncated classfile, a forged
archive pin and an extracted-class/archive mismatch.

The synchronous nonfixture protocol must retain application setter/getter and
lifecycle overrides, stored test callbacks, strict name/tag/position inputs,
custom TestData/Args/Reporter/Stopper/Filter/config paths, exception callbacks,
class initialization and synchronization. Default tag collection genuinely
uses annotation reflection. Async/fixture styles, afterWord/shared behaviors,
nested suites, unsupported carriers, unresolved overrides and metadata escapes
require their own verified recipe or an explicit guard. Provider/class hashes
alone do not make these paths empty, nor establish a complete suite execution.
