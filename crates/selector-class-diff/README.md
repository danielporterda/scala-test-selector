# Native class-file diagnostics

This independent leaf compares two borrowed class files and reports `Identical`,
`LineNumberTablesOnly`, `OtherChange`, or typed `Unavailable`. The native CLI,
planner and selector do not depend on this crate. Its tests verify the normal/build
dependency closures used by all eight native producer identities exclude it.

`compare_line_number_tables` removes only whole nested `Code.LineNumberTable`
attributes from comparison, including their enclosing derived lengths/counts.
Constant-pool layout, code, exception tables, declarations and every other
attribute remain exact. Both inputs undergo bounded structural checks first.
Malformed, unsupported or over-budget input produces `Unavailable`; it never
certifies a validated prefix. Structural checks are not JVM stack/type verification.

Raw SHA-256 identities are retained. Every result is diagnostic only and grants
**no omission authority**. In particular, changed line tables remain observable
through stack traces and raw class resources. The genuine javac/JVM fixture at
`fixtures/native-lnt` observes both: an unchanged throwing callee captures its
changed ancestor frame, and a resource reader hashes the changed bytes before
loading the target class. Other fixtures change constants, opcodes, initialization,
annotations and parameter metadata. Synthetic wire controls cover opaque attrs,
constant-pool layout, table insertion/removal, malformed code and budgets.

Run `cargo test -p selector-class-diff --locked --offline` and
`python3 tools/prepare_native_lnt.py --verify` from the workspace root.
The latter verifies frozen evidence without invoking a JVM; omit `--verify`
only to deliberately regenerate the tiny compiler/JVM fixture.
