# ScalaTest registration ABI styles

These are genuine Scala 2.13.18 + SemanticDB 4.15.2 compiler captures using
ScalaTest 3.2.19. The manifest records source identities, raw protobufs, native
ScalaSpans output, original classfiles, compiler arguments, tool hashes and the
independent JVM execution witness. No compiler or Python runtime is needed to
run the Rust acceptance tests.

Nine concrete suites each register and successfully run one test: async
WordSpec; fixture WordSpec and fixture async WordSpec with Function1 or explicit
Function0 arguments; tagged fixture and tagged async registration; FlatSpec
`it should ... in`; and nested WordSpec `when` registration.

The fixture-function factory changes `made` to 7 while constructing its suite.
Its returned function leaves `observed` at zero until the registered test runs,
when it changes to 41. The Rust assertions retain the eager factory call, pass
its returned callback to `RegisterTest`, and keep the returned function body in
a distinct deferred recipe. This guards against treating a function-valued
argument as a by-name argument and deferring its factory effects.

The exact versioned ABI contracts distinguish argument evaluation from callback
execution. Declared compiler parameter modes remain authoritative. Framework
bodies are deliberately unadmitted here, so external lifecycle uncertainty is
preserved; these are source candidate and value-flow gates, not an all-clear
framework coverage claim.

```sh
python3 tools/prepare_registration_smoke.py --verify --fixture fixtures/registration-styles
cargo test -p selector-acceptance --test registration_styles --offline
python3 tools/registration_parity.py --output tools/parity/registration-behaviors.json
```

To regenerate, pass `--fixture fixtures/registration-styles` without `--verify`.
The producer uses the locally pinned compiler, framework JARs and JVM and runs
the Scala validator before writing the receipt.
