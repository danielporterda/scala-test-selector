This initial layer binds compiled source ownership to captured suite and changed
source identities. It is **not** a fully admitted effect world, an effect summary,
a source-guard waiver, or test-exclusion authority.

`ValidatedSnapshot` immutably borrows facts/graph after one validation, exact
nonzero expected identities, graph-to-facts identity, explicit runtime identity,
and cross-artifact reference checks. The supervisor still has to admit the actual
artifact bytes and producers. The borrowed token prevents mutation while used.

`CompiledCatalogue` additionally requires exact retained-analysis manifest,
original compiler-context, and original SemanticDB input pins. It keeps one row
per captured suite, including unresolved, unsupported and pending roots. Stable
root keys hash length-prefixed name, compiler context and exact class descriptor;
local IDs and class content hashes do not determine cross-revision identity.
Duplicate keys fail. Only exact top-level compiler class/module names are mapped;
nested/encoded names and composite contexts stay pending. A bound constructor
also carries a mandatory class-initialization demand; parent/default-interface
and runtime effects require separate admission. Constructor lookup is not full
startup proof.

Requested sources bind to every owned compiled method, including generated
methods. Flat method IDs are sorted/deduplicated; each request retains its own
bound/pending row. No method-level SemanticDB/JVM spelling heuristic is used.
Requested binding completeness applies only to those requests. A separate merge
compares all captured nonbinary source/context deltas and reports any pending
side, including unrequested generated sources. Neither scope certifies native,
runtime, catalogue or whole-checkout completeness.

Unit tests use genuine frozen compiler classes and SemanticDB from
anonymous-construction, with an explicitly synthetic unit transport envelope.
They exercise the real opaque product admission API rather than constructing a
success token. Actual retained Zinc lineage remains separately pinned in the
three-context source-products control; synthetic unit stamps are not presented
as production provenance.
