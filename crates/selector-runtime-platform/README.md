# Declared runtime platform admission

This crate verifies the explicitly supplied Java runtime image, class inventory
and captured compiler-context bindings. It owns no graph construction or query
policy, so native effect extraction and graph construction can compile in
parallel after their shared parsers.

Admission rechecks image and class content hashes, provider membership, producer
identity and context options. An admitted image supplies exact bytes. It does not
establish historical compiler-image identity, class-loader behavior, effect
purity, or isolation between test suites.

The graph builder retains its existing `binary_platform` import path as a
compatibility re-export of this crate. Both users therefore share the same
admission implementation and proof types.
