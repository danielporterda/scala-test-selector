# Incomplete native hierarchy and executable initialization

The frozen Java 17-target classfiles were produced by the pinned JDK 21 compiler.
Each observation starts a fresh JVM with every genuine class present. `retained.jar`
is an analysis-only capture that omits Marker, DefaultParent, SuperParent and
Missing; `bytecode.jar` preserves all original classes. No class bytes are edited.

The independent observations distinguish three initialization rules:

- `Child.ping()` initializes Child, invokes the changed member both from Child's
  initializer and from ping, and never initializes its Marker superinterface.
  Missing Marker metadata prevents a closed hierarchy proof, but does not create
  an additional executable initializer obligation for this static interface call.
- Initializing DefaultChild initializes the real default-method interface first.
  Omitting that interface from the analysis leaves this executable phase unknown.
- SuperChild initializes its actual superclass; construction invokes that actual
  superclass constructor. Omitting it leaves both executable channels guarded.

`Child.opaque()` calls an omitted actual callee, so that call remains guarded even
when the unrelated hierarchy diagnostic is metadata-only. An unavailable earlier
classpath provider also retains its authority boundary. The public enrichment and
solver controls classify these separately; no missing class is declared pure.

`javap.log` retains the actual initialization bytecode and hierarchy declarations.
The manifest pins source, classes, deterministic archives, commands and JVM output.
Exact java/lang/Object bytes are reused from the independently pinned
`native-hierarchy/bootstrap.jar`, whose JDK source and licenses are retained there.
These are native callable-root surrogates, not a CI suite catalogue. Normal Rust
acceptance consumes frozen bytes and does not invoke javac or a JVM.
