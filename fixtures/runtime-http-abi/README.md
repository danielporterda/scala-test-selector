# Frozen compiler HTTP ABI projection

`original.json.gz` is an exact copy of the original compiler-backed HTTP ABI
fixture identified and hashed in `manifest.json`. The Rust acceptance test imports
only its captured compiler documents and source texts. It independently rebuilds
55 runtime bridge joins and retains two unresolved endpoints; legacy output edges
are never graph inputs. The fixture deliberately projects declarations and
definition occurrences, so this tests ABI joins, not full execution soundness or
complete reference/synthetic coverage. Tests need no legacy executable or exporter.
