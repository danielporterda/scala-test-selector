# Declared runtime platform acceptance

The complete `java.base` archive stays in an explicitly retained local artifact;
this fixture does not vendor a runtime image or discover the host JDK in tests.
The capture reads class bytes through the declared runtime's JRT filesystem,
without reflectively loading target classes. Its manifest binds the original
compiler-context capture, selected contexts, producer, image files, archive,
inventory and each class digest.

`declared_runtime_platform.rs` runs three small default controls without a JDK.
Its malformed protocol inputs contain a normalized image placeholder and the
existing genuine Object class solely to test specific rejection boundaries;
they are never presented as a real image. The missing-platform control checks
that the public query still guards an unavailable System method.

The explicit ignored test requires `SELECTOR_PLATFORM_MANIFEST`,
`SELECTOR_PLATFORM_CONTEXTS` and `SELECTOR_PLATFORM_PRODUCER`. Run it with:

```sh
CARGO_BUILD_JOBS=2 cargo test --locked --offline -p selector-acceptance \
  --test declared_runtime_platform \
  genuine_complete_java_base_normal_admission_keeps_native_system_opaque \
  -- --ignored --exact
```

It reads the complete genuine inventory through normal platform admission,
binds the native map to that declaration, verifies Object/Serializable class
authority and Object constructor lowering, and retains the actual native
System execution guard. The callable native endpoints are engine controls,
not discovered CI suites. The small native admission budget is explicit.
A normalized opaque `java/lang/Object#` reference also verifies that explicit
platform admission uses the real constructor recipe rather than the legacy
compiler-reference shortcut. Its placeholder gains no invented executable body.
The real String `length` method demands the actual Serializable parent header.

This is new declared-runtime authority. It does not prove the historical
compiler image, runtime isolation, complete project execution, safe suite
omission, or resolution of every Span uncertainty. The compact validation
receipt records the actual retained capture and measurements separately.
