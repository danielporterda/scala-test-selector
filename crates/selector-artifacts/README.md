# Immutable analysis artifacts

`write` and `write_streaming` publish complete files atomically without replacing
existing inodes. `publish` chooses a SHA-256 content name. Publication syncs the
file and, on Unix, its parent directory. Catalogue registration happens afterward.
An identical publication is idempotent; different content at the same path fails.

All integers are little endian. Version 1 consists of an 80-byte header, a sorted
64-byte entry per section, zero alignment padding, and section data:

| Header offset | Width | Meaning |
| --- | --- | --- |
| 0 | 8 | `RSELART\0` |
| 8 | 4 | Version (`1`) |
| 12 | 4 | Kind (`1` facts, `2` graph, `3` query summaries, `4` continuation, `5` potential effects) |
| 16 | 4 | Section count |
| 20 | 4 | Section-directory entry width (`64`) |
| 24 | 8 | Header/directory byte length |
| 32 | 8 | Complete file length |
| 40 | 32 | SHA-256 of entire file with these bytes zeroed |
| 72 | 8 | Reserved zero bytes |

Each entry contains a section ID (u32), reserved zero flags (u32), record count
(u64), byte offset (u64), byte length (u64), and SHA-256 of section bytes. IDs are
strictly increasing, sections begin at 8-byte boundaries, ranges do not overlap,
and every gap is zero padding. Counts describe records; the owning fact/graph
codec validates count-to-record-width relationships. Admission validates every
section and the whole-file checksum once. Potential effects use an independent
kind because they describe possible execution and require their own provider,
runtime and coverage admission. They cannot be read as query summaries or query
continuations even when their payload bytes match. Reads then return borrowed slices with
no allocations and no per-read checksum work.

`open_bounded` allocates one bounded owned byte buffer plus the small section
index. It is safe even when external producers can mutate input files. Keeping
the buffer as a Vec avoids a potential capacity-shrinking copy during admission.
`write_streaming` invokes an encoder twice and checks exact length and identical
output; it retains only O(section-count) metadata, a 128 KiB output buffer, and a 16 KiB stack batching buffer. Scalar
and small record encoder writes are hashed/output in batches; large chunks bypass
the batching copy.

Unix `open_mapped_immutable` is explicitly unsafe. Its caller must guarantee that
no process/file descriptor changes the backing inode for the owner's lifetime.
Read-only permissions, checksums, and cooperative locks are insufficient to prove
this. The mapped owner retains its file descriptor; slices borrow the owner, and
workers can share it through Arc. Unlinking an immutable inode on Unix is safe;
truncating or overwriting it is not. Arbitrary external paths use the owned reader.
