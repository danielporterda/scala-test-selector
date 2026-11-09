# Primitive JVM instruction fixture

These are byte-identical copies of the genuine inputs and independent
observations originally produced in `benchmark-output/jvms-finite-effects-v1`.
`migration.json` pins every copied byte. Original manifests/logs retain their
historical paths and producer qualification; this move does not claim a new
compiler run, runtime capture, verifier or isolation contract.

`Probe.class` has SHA-256
`e0019927542b275cb17ab2b6d2a2d3e3133050eaa59268306e096ec2c2f01aca`.
Its inventory covers 48 methods, primitive loads/allocation/length, reference
array and store negatives, callbacks/field writes in handlers, monitor/native/
reflection/dynamic boundaries, and malformed structural controls. Warm-loop
exception identity observations are diagnostic; no freshness or optimizer
behavior is assumed by native effect admission.
