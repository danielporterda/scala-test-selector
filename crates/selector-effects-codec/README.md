# Effect-capsule persistence

This crate stores typed local effect capsules. It supplies checked transport,
not an exclusion certificate or a trusted producer. Query execution does not
consume these artifacts until an admitted world builder and planner validate
all semantic authority and input bindings.

Schema 3 uses `ArtifactKind::Effects` and `SEFXP003` metadata. Its thirty-three sections
contain fixed little-endian scalars; Rust layouts are never disk layouts. The
reader rejects schemas 1 and 2, completed summary-cache artifacts, unknown flags, bad
checksums, extra/missing sections and mismatched expected world identities. An
absent optional artifact means ALL TOP; a named invalid artifact fails admission.

The binding pins producer, facts, graph, runtime, input inventory, full root
universe, reviewed contracts and member authority, plus exact fact namespaces.
Runtime ZERO is explicitly expected absence, never an unspecified wildcard.
The artifact digest includes metadata and keys. Consumers also bind their
canonical DTO digest; those digests intentionally represent different bytes.

Foreign keys retain compiler context, ordered provider identity, class hash,
owner, method name, descriptor and flags. Source fields/classes use bound fact
symbol IDs without invented JVM descriptors or class hashes. A foreign node hint
cannot replace an open source capsule. Source/native aliases require independent
link and coverage authority; duplicate/conflicting logical subjects are rejected.
A stored `canonical`, `resolved`, authority number or hash alone establishes no
semantic proof.

Callable code identity is separate from heap origins. The callable schema retains symbolic
calls, exact callable creations, capture cells, local copies, returns, stores and
loads. SAM keys bind provider/class/interface ABI and authority; adapter keys bind
exact enclosing/BSM/implementation references, ordered bootstrap argument digest,
instantiated descriptor and full adaptation-proof digest. Finite adapter rows
must match the admitted normalized arity/capture shape. Unsupported adapters keep
ALL TOP. A creation with no admitted SAM remains representable without invoking
its code; activation without admitted SAM authority opens Calls. Body parameter
count does not invent a SAM descriptor or prove a bootstrap adaptation.

Creation-specific default bridges retain the actual foreign default-method body,
requested SAM and private native proof digest. The proof key binds the creator's
complete generated-method set, default Code, transport policy, creator adapter and
both SAM identities. Unknown proof evidence requires an ALL TOP target; a dormant
creation does not execute the default body. Adapter normalization remains a
separate proof from default-method transport, and neither establishes purity.

Class initialization, loading/verification and unavailable-class boundaries use
explicit runtime-phase keys bound to a class and producer authority. These are
ALL TOP, zero-argument subjects, not fabricated JVM member names. Known code,
initialization and zero-actual direct-call lower bounds are preserved without
claiming that those phases are complete.

Each effect channel has its independent TOP flag. Noncanonical storage and
unresolved class/exception/external evidence require relevant channels to stay
TOP. Method-owned sites and flat effect/origin/callable ranges are checked for
bounds, overlap and orphan rows. An exception type key proves neither a fresh
exception object nor finite implicit JVM/native effects.

`canonicalize_origins` normalizes producer layouts where a closure's captures
were appended before later call arguments. It moves origins and callable values
together, updates every owning range and returns a checked row/range map for
producer sidecars. It preserves code, value coordinates and row IDs. Already
canonical data needs no allocation; repacking uses three flat scratch columns,
charged with the retained DTO before copying. Overlap, orphan rows and failures
leave all source tables and headers unchanged. Reader validation stays strict.
Source projections can retain stable creation IDs in their sidecars and depend
only on the core DTO. The artifact-writing caller explicitly normalizes the
projection before `write`; the writer never silently moves producer data.

`write` validates borrowed producer tables and streams records through the
artifact writer. `open` owns one bounded verified wire buffer and exposes copied
scalar rows and borrowed UTF-8 without per-record allocations. `admit` retains an
already verified immutable artifact owner, including a mapping whose backing-file
lifetime contract remains the caller's duty.

`materialize` optionally decodes seventeen flat DTO columns once. It preflights the
combined wire, conservative fixed directory metadata and decoded column bytes,
then checks actual vector capacities before filling. `Materialized` retains both
wire provenance and DTO; keys and text remain borrowed from the wire. Consumers
charge `transport_bytes()` alongside DTO capacities. The directory allowance is
bound to the current artifact implementation; an artifact-owned ledger can
replace that conservative allowance later.

Defaults admit at most 256 MiB total wire, 64 MiB text and two million aggregate
key/effect rows; the core DTO applies its own row/byte caps. Failed validation
publishes no new artifact, and immutable publication rejects different content at
an existing path. Focused controls cover roundtrip, zero-allocation borrowed
lookup, materialization budgets/capacities/teardown, malformed or transplanted
records, callable scope, adapter identity and strict legacy rejection.

The earlier standalone schema-1 experiment and its twelve-test receipt are
historical under `benchmark-output/typed-effects-prototype-v1/codec`; its exact
sources are archived there. They are not schema-3 test evidence or suite-exclusion
authority.
