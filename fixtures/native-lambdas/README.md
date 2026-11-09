# Native lambda authority fixture

This fixture is actual Java 17 bytecode produced by the pinned JDK 21 compiler.
`LambdaMetafactory.metafactory` creates three deferred `Runnable` values:
a static implementation capturing an integer, an instance implementation capturing
both its receiver and an integer, and a bound instance method reference.
The independent JVM runner observes zero effects when these values are created,
then the exact static/receiver/bound effects when each is invoked. A separate
`DeferredTarget::touch` factory proves that merely creating a static method
reference does not initialize its target class: its real static initializer runs
only when the reference is invoked. A genuine unbound `Consumer<Probe>` method
reference is also executed independently; it deliberately remains an unsupported
analysis boundary until its SAM/receiver adaptation has an admitted contract.

`unsupportedThenStore` uses `StringConcatFactory.makeConcatWithConstants`, an
unsupported bootstrap with a known String result descriptor, before a real
instance field store. Analysis must retain that later store and explicit unknown
bootstrap effects. No unsupported bootstrap is declared pure.

`manifest.json` pins sources, original classfiles, deterministic JAR, full
`javap -v -p -c` output, command lines and the independent JVM output. Regenerate
with `python3 tools/prepare_native_lambdas.py`; verification alone needs no JVM:
`python3 tools/prepare_native_lambdas.py --verify`.
