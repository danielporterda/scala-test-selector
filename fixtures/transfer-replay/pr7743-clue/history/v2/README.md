# PR7743 clue transfer replay

`bundle/` is a version 2 replay re-executed by the pinned current kernel against the original paused PR7743 head publication snapshot. The version 1 checkpoint is opened read-only: the solver is never resumed. Complete source-node candidates and immutable World responses are retained. Source bytes are stripped; file paths, revisions, contexts, and source hashes remain.

The current kernel records the actual first runtime issue at operation 1909541 (`UnknownOperation`). `reduction.json` records 29 source operations reduced to 12 active operations while retaining nine calls, the captured callback, at least ten dependency reads, and an uncertainty guard. The reduced evaluation's first issue is `ExecutionGuard` at the same operation; the original opcode remains part of the immutable bundle. Candidates, type metadata, and callback recipe authority remain available during reduction.

`history/` preserves the original version 1 metadata, provenance, and reduction. The original binary artifacts are pinned by their hashes and Git commit in `provenance.json`. Historical v1 output belongs to its original producer and is not admitted as v2. The new first issue was observed by transfer re-execution; it was not inferred from the old checkpoint.

Rust tests load this bundle without Python, compiler jars, original sources, full facts, or a solver run. This is one transfer snapshot; it does not establish a fixed point or whole-query coverage. See `provenance.json` for exact source, checkpoint, operator, and artifact identities.
