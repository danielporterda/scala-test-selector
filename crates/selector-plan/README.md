# Potential dependency planning

The planner excludes a suite only through potential execution and declaration
dependencies. Observed solver reachability can refute a certificate but cannot
establish absence. Known field reads depend on all potential matching writers,
including dormant stores and unresolved source/native aliases.

`plan` and `plan_guarded` use `SuiteSemantics::SharedState`. A runnable opaque
boundary can mutate hidden shared state, so every potential heap reader remains
a candidate. An unidentified field write also creates this exposure without
requiring an additional call or callback frontier. Closed scalar components can
still be certified independently.

`plan_guarded_with_semantics` accepts an explicit `SuiteSemantics::Independent`
assumption. It removes only that blanket exposure to hidden effects of other
suites. Known writer/read, changed-code, declaration and initialization
dependencies remain. Unknown callbacks, dispatch, reflection, heap targets and
input guards reached within the suite remain candidates. Unscoped uncertainty
still prevents exclusion.

Suite independence is an analysis assumption, not evidence of separate JVMs,
processes or classloaders. Suites that intentionally communicate through hidden
shared state require shared-state analysis or explicit dependency coverage.
The chosen semantics is private in each plan and participates in both its seal
and root certificates through the assumption bits. Consumers must use the same
semantics on both sides of a paired query.

Certificates also declare the current functional-selection contract: functional
test behavior, a closed captured application classpath, trusted runtime semantic
contracts, and unchanged external inputs except the tracked inputs. These are
model premises, not verified properties of a running JVM. Timing-sensitive tests
and executions outside those premises require a different contract. All four
bits and the contract version participate in the plan identity, including when
the plan has no exclusions. Declaring these premises does not by itself close
an unresolved callback, initializer, exception or native recipe.

Sparse `DeferredReceiverDispatch` relations describe omitted native method
discovery for a receiver, not an opaque class initializer. The planner checks
eligible instance invocation sites using reusable local value provenance and a
flat ancestry index. An exact allocation can avoid an unrelated receiver's
frontier only with complete ancestry. A `KnownReceiverDispatch` relation covers
only its exact receiver and requested contract; it does not cover descendants,
unknown values, or the selected body's effects. Lexical `this` and values from
unresolved calls, fields and parameters remain conservative. Literal callbacks,
empty scalar receivers, constructors and explicitly selected super calls do not
acquire this additional receiver-discovery frontier. Their ordinary callback,
body, initialization and input boundaries still apply.

An `OP_JVM_NONVIRTUAL` certificate also avoids this additional frontier only on
`Call` in a `BODY_BINARY_RECIPE` owned by a `FILE_BINARY_SOURCE` file. The native
producer emits it for exact static/special bytecode invocations. Source flags,
virtual operations and missing binary ownership cannot claim this exemption.
It does not close missing targets, selected body effects or initialization.
