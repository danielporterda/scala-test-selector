# Structured compiler-synthetic lowering

`captured-patterns.json` contains nine exact SemanticDB synthetic trees, their
source excerpts, ordinals and source/compiler provenance. They are taken from
the sealed full PR7646 head corpus. The companion `expected.json` supplies
evaluator-only classification assertions; it is never graph input.

The full corpus has 278,656 synthetics: 49,961 root `select_tree`, 118,402 root
`apply_tree`, and 110,293 root `type_apply_tree`. Nested trees include 18,184
`function_tree` and 12,829 `macro_expansion_tree`. Treating all role-3 references
as unknown loses known inserted callees, argument computations, callback
invocations and static type substitutions. Flattening every nested `symbol`
into an execution edge also loses semantics: type arguments are not calls,
functions are deferred, and compile-time macros are not runtime bodies.

The old `compiler-selector/engine/graph.py::_synthetics` does perform that broad
recursive symbol walk. Its direct-call regressions are valuable; its flattening
is not a precise transfer representation to copy into the new engine.

Minimal structured lowering, suitable for compact tagged records:

1. `SelectTree` carries a selected compiler target plus qualifier value or
   `OriginalTree` reference. `IdTree` carries the exact compiler symbol; its
   declaration kind decides value/parameter/accessor interpretation.
2. `ApplyTree` evaluates/binds the function and arguments in order. An
   `OriginalTree` function augments an existing exact source call rather than
   inventing a new target. An `OriginalTree` argument refers to already extracted
   source work and should not cause source reparsing or duplicate lowering.
3. `TypeApplyTree` follows its function for execution, retaining type-argument
   references and substitutions separately. Verify exact signature parameter
   identities and arity before applying narrowing.
4. `FunctionTree` creates a deferred callback recipe and file-scoped parameters;
   body evaluation occurs through the callback consumer's contract, never by
   recursively visiting the argument tree eagerly.
5. `MacroExpansionTree` preserves macro/static type evidence separately. If the
   expanded executable body is unavailable, emit an explicit scoped unknown
   rather than a call to the compile-time macro or an empty effect.
6. Validate all `OriginalTree` ranges in the same source UTF-16 coordinate
   system. Bind an outer result only at the exact function/application range;
   nested argument conversions must not become the outer call's result.

Important focused regressions already in the reference engine:

- `test_regressions.py::CompilerRuntimeRegressions`:
  `test_select_tree_callee_is_executable_without_a_written_callee_occurrence`,
  `test_literal_rhs_synthetic_conversion_is_runtime_while_signature_type_is_declaration`,
  and `test_synthetic_local_ids_from_two_documents_do_not_cross_contaminate`.
- `test_expression_types.py`: selected `Factory.apply` return type, nested
  conversion exclusion, and `OriginalTree`-only implicit wrappers introduce no
  callee.
- `test_compiler_value_bounds.py`: exact `TypeApplyTree` type substitution,
  unresolved type-argument arity, and type arguments are not runtime alternatives.
- `test_callback_aliases.py`: argument-owned conversion prohibits transparent
  alias reuse; an enclosing invocation's separate implicit clause does not.
- `test_forwarding.py::EnclosingImplicitClauseTest`: exact source/allocation
  range and inserted actual/formal identity/order are necessary. Unknown wrapper
  shapes, missing metadata, by-name/repeated/mutable/lazy actuals and multiple
  conflicting enclosing synthetics remain rejected.

New Rust tests should combine the real examples with small named mutation
controls: remove the inserted target's written occurrence; put the same tree in
a type/signature range; change a parameter from local0 in one file to local0 in
another; move an OriginalTree range into a nested argument; wrap only with type
application; insert an unknown tree tag; or place a method target inside a
deferred function. Assert operation kinds, argument identities and remaining
uncertainty as well as graph reachability.

Development-only regeneration:

```sh
python3 ci-cost-study/rust-selector/fixtures/synthetics/prepare.py
```

This validates the sealed source gzip hash and scans the corpus once. The
resulting files are consumed directly by Rust; no Python runs in production.
