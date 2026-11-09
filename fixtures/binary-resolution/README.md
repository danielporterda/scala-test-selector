# JVM inherited member resolution

These are genuine `javac --release 17` classfiles and a deterministic JAR from
`Resolution.java`. `manifest.json` records source, compiler, JVM, JDK module,
source archive and every output hash. The producer also executes the real JVM
reflection/call witness in `Resolution.main`: inherited methods and static
fields declare `ResolveBase`, the maximal interface default declares
`DefaultOne`, the super call executes `ResolveMid`, interface fields precede
superclass fields, and a class's own field takes precedence.

The JAR includes the unmodified `java.lang.Object` class from the recorded JDK
module, so proving its missing members does not rely on a fabricated bootstrap
class. Its corresponding source and JDK license notices are retained under
`jdk-source/`, `LICENSE`, `ADDITIONAL_LICENSE_INFO` and `ASSEMBLY_EXCEPTION`.
Java tests run only during fixture production. Rust tests require no Java,
Python or network and load the exact ordered, SHA-verified JAR.

The two files in `controls/` are explicitly synthetic negative controls, each
derived by one equal-width constant-pool UTF8 name replacement described in the
manifest. One creates competing concrete defaults, the other a cyclic interface.
Tests also explicitly withhold required metadata and request noninherited
constructors, wrong descriptors and wrong static invocation kinds. Those cases
remain scoped unknowns; interface candidates are never chosen arbitrarily.

The resolver follows [JVMS field and method resolution](https://docs.oracle.com/javase/specs/jvms/se21/html/jvms-5.html#jvms-5.4.3.2)
and [invokespecial selection](https://docs.oracle.com/javase/specs/jvms/se21/html/jvms-6.html#jvms-6.5.invokespecial).
It returns exact declaring JVM identities. Access control, receiver dispatch and
static-versus-instance lifecycle phases remain separate graph responsibilities.

```sh
python3 fixtures/binary-resolution/prepare.py
cargo test -p selector-graph-build binary_resolve --offline
cargo test -p selector-graph-build binary_lower --offline
cargo test -p selector-graph-build --test binary_inheritance --offline
```
