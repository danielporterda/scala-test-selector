# Compiler static result constraints

These base/head inputs were compiled with Scala 2.13.18 and SemanticDB 4.15.2.
Raw protobuf, unchanged source files, Java library source/classfiles, native
ScalaSpans output, hashes, exact compiler arguments and independent JVM values
are retained. Rust acceptance needs none of the preparation toolchain.

`Opaque` is genuinely compiled and used by the JVM witness, but its body is
deliberately unadmitted to the Rust graph. Its results therefore remain unknown
and guarded. The verified source result type constrains the possible unknown
classes; it cannot establish an allocation or complete the opaque effects.

The independently known subtype matrix is:

| Implementation | Base | Narrow | Marker | Effect |
|---|---|---|---|---|
| final Allowed | yes | yes | yes | affected |
| final NoMarker | yes | yes | no | unmarked |
| final Sibling | yes | no | no | outsider |

All calls use the inherited compiler target `Base#work().`. The following
expectations distinguish result constraints from that shared dispatch target:

| Case | Feasible effects | Required uncertainty |
|---|---|---|
| exact Allowed allocation, or known factory declared Base | affected | no unknown result introduced by widening |
| unknown factory declared Narrow | affected, unmarked | opaque effects remain guarded |
| alias of Narrow, or type parameter bounded by Narrow | affected, unmarked | opaque effects remain guarded |
| Narrow with Marker | affected | both bounds apply to the same unknown alternative |
| exact Allowed joined with a separate unknown Base result | affected, unmarked, outsider | known allocation identity and broad unknown both survive |
| branch between exact Allowed and exact Sibling | affected, outsider | NoMarker remains excluded |

The compiler encodes the intersection inside
`structural_type.tpe.with_type.types`. The alias has equal lower/upper type
bounds. The generic result references its exact method type parameter, whose
compiler `type_signature.upper_bound` names Narrow.

Synthetic negative controls remove the verified Narrow class declaration or
replace it with an unverified type parameter. These alterations are explicitly
separate from original compiler data: neither can license excluding the final
Sibling implementation. Its candidate and guard must both remain.

At the initial TDD reproduction, four of five Rust tests passed. The static
unknown constraint gate found that a global TOP lost these bounds: all four
bounded cases entered Sibling, and the intersection also entered NoMarker.
The extractor now projects complete compiler constraints into flat result-bound
columns. Distinct bounded unknown clauses remain alternatives, and each clause
contains conjunctive class bounds. All five gates pass with guards intact and
without fabricated allocation evidence.

```sh
python3 tools/prepare_value_bounds.py --verify
cargo test -p selector-acceptance --test value_bounds --offline
python3 tools/value_bounds_parity.py --output tools/parity/value-bounds.json
```

The parity tool also executes the eighteen retained legacy bound tests and runs
their normalizer against these actual captured compiler signatures. Use
`--allow-known-gaps` only to write a receipt while retaining the failing Rust
gate; it records the failure and does not change the acceptance expectations.
