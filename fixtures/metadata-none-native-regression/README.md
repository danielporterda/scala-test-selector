# Historical metadata-None native facts

`pre-refactor.bin` is the original native result from the immutable CLI pinned
in `provenance.json`, retained byte for byte from the independent pre-refactor
run. The selected-external-apply compiler documents and syntax remain unchanged.

The current extractor intentionally improves two allocations in this capture:
`Calls.interval` and `Calls.timeout` select the exact compiler-occurrence
`Span.<init>` identity, instead of using the `Span` class as the call target.
Their missing-constructor-signature guards replace unresolved-overload guards;
the guards remain present. The two body hashes therefore change. No constructor
metadata, implementation, purity, or provider authority is inferred.

The regression test checks these exact differences, then restores only the two
operation targets, two issue kinds/details, two body hashes and corresponding
string value. Canonical serialization must reproduce the complete original
artifact and its independently pinned digest. All other fields remain covered.
The separate prepare/finish-versus-import test checks current metadata-None byte
equivalence directly. The genuine external-constructor-prefix fixture verifies
constructor selection independently against compiler and JVM observations.

The extractor version is not serialized by the facts codec and cannot explain
a canonical byte change.
