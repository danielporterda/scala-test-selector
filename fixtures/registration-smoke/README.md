# Registered ScalaTest and lifecycle witness

These inputs are genuine Scala 2.13.18 + SemanticDB 4.15.2 compiler output from
the retained source files, with ScalaTest 3.2.19. Native Rust capture replay and
the hash-bound JVM ScalaSpans producer emitted the checked-in JSONL. The manifest
records original raw protobuf, source, compiler, framework and generated hashes.

The independent JVM validator constructs and executes eleven concrete suites,
each with one actual registered test. It checks observed fields are zero before
execution, then checks all eleven results after `Suite.run`. The cases cover
curried FunSuite registration, WordSpec registration and nested scopes, dormant
versus invoked stored callbacks, concrete dispatch in inherited registered work,
an overridden `beforeAll` sibling and `withFixture`.

`OpaqueSink` is a separately compiled library whose callback invocation depends
on a JVM property. The source behavior fixture does not admit its body or the
framework's binaries; external uncertainty remains explicit. Candidate precision
assertions are independent of those guards. This is not evidence that the whole
fixture has complete framework coverage or that every legacy output is equal.

The versioned exact external ABI fallback proves argument deferral only. Source
and imported compiler parameter modes take precedence. Synthetic metadata
controls in the Rust test verify strict and by-name declarations separately;
malformed descriptors and unsupported overloads cannot acquire fallback proof.

```sh
python3 tools/prepare_registration_smoke.py --verify
cargo test -p selector-acceptance --test registration_capture --offline
python3 tools/registration_parity.py --output tools/parity/registration-behaviors.json
```

Regeneration uses the locally pinned compiler/framework JARs and Java executable
recorded in `tools/prepare_registration_smoke.py`; it runs an actual compiler and
JVM validator. Rust regression execution needs no Python, Java or network.
