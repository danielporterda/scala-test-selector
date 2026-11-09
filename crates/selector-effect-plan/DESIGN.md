# Callable composition and influence coverage

Callable identity and memory identity are independent. A finite creation has a
static implementation/SAM template and captured-value bindings. Its instantiated
payload records the defining analysis frame. Heap escape can widen its receiver
or captured memory regions to Any while preserving known code. Loading a payload
in another root must retain its original capture coordinates. A creation does
not execute its implementation.

The finite frame key is `(catalogue entry, method)`. Repeated calls to the same
method join actuals; recursive calls join the same cells. This deliberately
overapproximates invocation distinctions without storing recursive histories.
It is an analysis coordinate, not an address space or runtime isolation claim.
Shared canonical field/element cells join values across the full catalogue.
Missing aliases, unknown targets, unsupported SAM adaptation and exhausted sets
open Calls. Unknown memory origins do not erase known callable alternatives.

The current conservative change rule marks every effect of an enclosing root
when a reachable method, code observation or matching shared read is influenced.
That rule can overretain stable framework bookkeeping when only a later test
callback changes. Callable identity alone does not justify narrowing it.

The minimum additional producer contract for finer influence is a complete
dependency list for each local effect and call:

- An effect reference identifies its channel and method-local ordinal. Method
  locality is retained through composition; raw ordinals are never flattened.
- Scalar dependencies need a distinct source enum: unknown, proven stable
  literal, receiver, argument, capture, local, call result, heap read, method or
  class code, and call effect. `ValueRef::Constant` proves only that a value is
  noncallable; it is not a stable literal proof. A dependency can be data,
  receiver/address, callable target/capture, or control. These roles must not be
  conflated.
- Every effect and invocation has an explicit completeness claim, even for an
  empty dependency list. A missing row is unknown, not independent. The claim
  must be bound to the exact source/native recipe and reviewed contract.
- A changed method conservatively influences its result, selected targets,
  control and effects unless a separate paired transfer proves otherwise.
  Unchanged methods can propagate influence through call results, actuals,
  captures and alias-compatible reads. Code observation remains separate.

Control dependency is necessary. In `if (changed()) field = 7`, the stored value
is constant but the write is influenced. Conversely, a registration write whose
inputs and control are unchanged must not become influenced solely because a
stored callback is invoked later and returns a changed value. Discarding a call
result never discards its possible execution effects.

Known noncallable constants are not generic opaque returns. An unknown concrete
value may still be stable under the same-input contract, but only after complete
read/call/code-observation dependencies establish that relation. A class-resource
observer also needs exact changed-method-to-class coverage. Reflection, JNI,
unresolved calls and missing source forms cannot inherit a finite influence set
from unchanged ordinary arguments alone.

Required adverse controls include a changed return controlling a constant write,
two sibling callees with local ordinal zero, a returned callable with captured
callback, dormant creation, a capture that widens to Any without losing code,
cross-root heap store/load preserving the creator payload, two callers sharing a
factory site, recursive payload cycles, wrong SAM/provider adaptation, missing
definitions, and budget exhaustion. Paired proof consumption requires both
snapshots, complete root/ambient coverage and current admitted bindings.
