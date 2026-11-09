# Native JVM summary fixtures

The seven classfiles and three JARs are real `javac` outputs from `Probe.java`.
`manifest.json` records the source/compiler hashes, exact compiler version and
arguments, byte counts and output hashes. The alternate JAR changes only the
factory's return from a fresh allocation to null; captured classpath order must
choose the first class, never union both definitions. Stored and raw-deflated
JARs exercise both supported ZIP codecs. Rust tests consume checked-in bytes,
with no Java, `javap`, Python or network at test/runtime.

The classfile parser borrows its input. Its bounded straight-line interpreter
owns flat value, argument, call, write and bytecode-offset tables. It preserves
receiver/parameter identity, category-2 local slots, allocations and their exact
constructor arguments, fields and invocation descriptors. Virtual/interface
calls remain receiver-dependent relations. Declared return types do not become
allocations. A bridge method is resolved by its actual JVM descriptor and is
never replaced by a parent implementation. Unknown control flow retains known
prefix calls and an explicit unknown return alternative after IR lowering.

Unsupported branches, arithmetic, monitors, exceptions, `invokedynamic`, dynamic
constants, missing/native/abstract bodies and unsupported encodings remain typed
unknowns. Static field reads and writes lower to explicit global slots and
initialization of their exact admitted owner. Missing field/owner identity keeps
an unknown effect. Forwarded call results retain the exact dynamic dependency;
an unresolved callee remains unknown in the graph and query phases.

Classpath admission validates an earlier JAR's full SHA256 even when the desired
class is absent, preventing fallback to a different later class after an input
change. Admitted archive bytes are owned and immutable for the snapshot lifetime.
ZIP member names, compression bounds, CRCs and internal class identity are
checked. Duplicate entries, ZIP64/encryption and multi-release class overlays
remain unsupported rather than choosing potentially wrong runtime bytes.

Source output directories use the capture producer's exact canonical full file
inventory fingerprint. A verified inventory can establish absence; a source
class that shadows a later binary remains explicit uncertainty. Pruned,
unreadable, symlinked and mismatched directories cannot prove absence. Memory,
code, stack, local, value and directory-work budgets are explicit. No mapped
external mutable files or query-global caches are used.

Development-only regeneration (the JDK path is recorded in the script):

```sh
python3 ci-cost-study/rust-selector/fixtures/binary/prepare.py
cargo test --manifest-path ci-cost-study/rust-selector/Cargo.toml -p selector-models binary --offline
cargo test --manifest-path ci-cost-study/rust-selector/Cargo.toml -p selector-graph-build binary_lower --offline
```
