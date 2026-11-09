# Native may-effect envelope fixture

The pinned JDK 21 compiler emits real Java 17 classes. Calls to `changed()` occur
behind conditional branches, dense/sparse switches and an exception handler.
Independent JVM observations distinguish taken and untaken branches. A disjoint
scalar method uses branching/arithmetic without calling `changed()`. No-argument
`branchEntry` and `disjointEntry` provide explicit callable-root surrogates for a
public planner gate. The no-field nested `Scalar` component isolates arithmetic
from Probe’s static counter initialization, which remains a heap frontier. This inventory is not a CI catalogue or suite-discovery claim.

Static callback escape does not run the callback until `invokeEscaped`; its
static field and later callback invocation remain effects. Reflection, arrays
and monitors are explicit conservative boundaries unless their effects have a
separately admitted contract. Runtime observations do not certify absence of
other effects or whole-program test exclusions.

`shadow.jar` is separately compiled same-owner bytecode whose `branch` returns
zero without calling `changed`. It supplies an ordered-classpath authority
control, never a fallback for missing original classes. Malformed/truncated
bytecode controls must reject before producing a closed effect envelope.

Regenerate with `python3 tools/prepare_native_envelope.py`; `--verify` validates
all hashes and frozen JVM observations without invoking a JVM.
