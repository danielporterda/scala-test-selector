# Typed effect summaries

Flat numeric effect tables and checked callable-value graphs. This crate validates structure and bounded namespaces. It does not attest producer semantics, exact provider identity, complete runnable catalogues, or suite exclusion authority; those belong to verified producers and the planner.

Each effect channel has an independent TOP bit. Finite entries in an open channel are diagnostic lower bounds. Missing methods are explicit ALL-TOP rows. Callable creation records code and capture references without invoking it. Heap identity and callable code identity are separate: losing a private allocation origin does not erase a known implementation, and losing capture precision does not fabricate a different implementation.

`Constant` means proven non-callable, never an opaque return. Unproduced local cells remain unknown. Invoking unknown, non-callable, missing, incompatible-SAM, or budget-widened values stays open. Native lambda implementations require an admitted adapter including receiver/capture/SAM argument mapping and any boxing, casts, or bridges; raw method arity alone is insufficient.

All table indices and method-local coordinates are checked. Immutable views borrow one owner. Reusable callable cells use flat bounded vectors and caller-reserved capacity; exhausted code sets become unknown rather than truncated finite sets. Recursive captures are numeric graph edges, without recursive owned payloads or runtime context identities.

Default-SAM compatibility is creation-specific. A checked bridge row routes activation through the actual default method, including its field reads, initialization, and other effects. That method receives the original callable payload as its receiver value; it does not receive the creator implementation's lexical receiver or captures. A missing compatibility proof stays unknown, even when arities agree. Artifact admission must bind the exact generated-method set, default provider/code, and no-override proof.

Runtime phases use a separate subject namespace from real JVM methods such as `<clinit>`. Current phase capsules remain ALL-TOP with no formal parameters or local values. Known initialization calls and code observations are retained as lower bounds and cannot certify a closed phase.
