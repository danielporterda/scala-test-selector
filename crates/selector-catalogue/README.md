# Selector catalogue

A sibling leaf crate using one rusqlite dependency and one SQLite connection per
command/thread. WAL permits concurrent readers; short IMMEDIATE transactions
serialize metadata writers without a stale-read-to-writer upgrade race. FULL
synchronous mode commits durable references after artifact publication.

The catalogue stores immutable artifact locations/lengths/kinds, stage entries
keyed by (stage, input identity, producer identity), ordered multi-file manifests,
and run metadata. It performs no graph traversal or per-edge analysis operations.
Register only admitted immutable artifacts. Existence and length are checked here;
content/schema checksums are the artifact reader's responsibility. Paths must
continue referring to the published immutable content after registration.

Batch registration and manifest publication are transactional. A key or identity
conflict rolls back the entire batch. Missing manifest members prevent any
manifest publication. Repeating identical writes is idempotent. Completed,
incomplete, and failed runs are terminal; rewriting their status or metrics fails.

The schema has an explicit application ID and version. Unknown versions or other
application IDs are rejected. No automatic migration or garbage collector is
provided yet; deleting an artifact requires a separate lease-aware policy.
