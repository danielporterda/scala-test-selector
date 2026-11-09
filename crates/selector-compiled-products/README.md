This leaf admits a **new retained-analysis correspondence** between captured
source files and their exact compiled class products. It does not supply effect
summaries, remove source unknowns, or grant test exclusion authority.

`admit` takes an externally pinned manifest and expected producer, original
compiler-context, original SemanticDB capture, and successful compile-receipt
hashes. It verifies the retained Zinc analysis and reader provenance, original
captured directory hash (all files), current source/class SHA256 hashes, FarmHash
content-stamp correspondence, and unique complete class-product ownership. The
reader is a pinned offline Zinc API program; its raw output and invocation
receipt are explicit inputs. This is not a recovered historical Zinc capture.
The trusted supervising invocation must bind the manifest and reader producer;
a self-declared manifest hash is not independent authority.

The output owns validated class bytes once through `Arc<[u8]>` and interns
method identity strings once. It enumerates every method ABI of every owned
class. Source files absent from SemanticDB stay explicitly pending. Verified
source changes map to **all** their compiled methods, including generated
methods; no SemanticDB-method/JVM-descriptor spelling heuristic is used.

Root lookup requires an exact source definition and owned class. Class roots
require a public concrete class with an actual public `()V` constructor. Module
roots require the exact source object, self-typed static `MODULE$`, and actual
static `()V` class initializer. Nested/encoded class-name mappings not proved by
this interface remain pending. Own products must be captured classpath ordinal
zero; a preceding provider needs additional authority rather than a shortcut.

The classfile reader validates bounded structural ABI and Code-attribute shape.
It is not an instruction verifier or all-path effect producer. A consumer must
separately verify compiled effect coverage, providers, dispatch, callback
adapters, lifecycle, and VM/native effects before choosing compiled authority.

Limits distinguish retained output bytes (`max_owned_bytes`) from bounded
admission scratch: the context JSON cap, one JSONL-line cap, one classfile cap,
source/method/file counts, and a streaming document byte cap. Refusal is an error,
never truncation or an empty recipe. The current directory hashing and typed
context decode are sequential; no per-method classpath or Zinc parse occurs.
