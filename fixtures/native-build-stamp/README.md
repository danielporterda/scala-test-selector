# Retained BuildInfo bytecode

These files are the physical generated Splice class outputs from PR7743's
verified `apps-common / Compile` products. They are unmodified. The base is
`f20116bc144298a8952b9a89ec057694734dc989`; the head is
`8d6193f4c449e04e7d96840d13f031cf966fe146`.

| Fixture | Original class | SHA-256 |
|---|---|---|
| `base-module.class` | `org/lfdecentralizedtrust/splice/environment/BuildInfo$.class` | `d7e5db1f53ec20cf78666a197772cde6888284c054bee81d69c95bac01c25080` |
| `head-module.class` | same | `d1969acceef2ec74722e33bb5dd2da7142e04b186fd005cd231eeb71760ff770` |
| `forwarder.class` | `org/lfdecentralizedtrust/splice/environment/BuildInfo.class` (identical in both revisions) | `405102b569db87b93918cc577aab8e69b08ec7c0da53aeb24e04ce0aa69a46a5` |

Run `cargo test --offline -p selector-class-diff` from the selector workspace.
The tests check the observed field/accessor wire, a one-field delta of a different
length, and refusals for a changed compatible version, unsupported literal,
modified initializer, forwarder mismatch, truncation and input budget.

To inspect any physical pair that uses the same exact reviewed template:

```sh
cargo run --offline -p selector-class-diff --example build_stamp -- \
  BASE_MODULE HEAD_MODULE BASE_FORWARDER HEAD_FORWARDER
```

The [PR7743 audit](../../tools/rust-final/pr7743/build-stamp-reader-audit.json)
rehashes both product inventories and records direct JVM member references in
nonempty `apps/` products. `ValidatorFaucetCapZeroTimeBasedIntegrationTest`
and `ValidatorLicenseMetadataTimeBasedIntegrationTest` directly read a changed
stamp. `AppUpgradeIntegrationTest` directly reads the unchanged compatibility
field, which does not prove its other behavior unaffected. A suite can still
observe the stamps via its fixtures, a status or version endpoint, compatibility
checks, or validator license updates.

A matching class template establishes exact byte and reader facts only.
It does not prove provider completeness, fixture inactivity, absence of other
consumers, or whole-checkout omission authority.
