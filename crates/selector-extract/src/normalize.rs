//! Independent document normalization and deterministic flat-table publication.
//! Workers own one bounded document partition; no worker clones the program.
//! The ordered merge interns only final strings and translates compact IDs.
use crate::{ExtractOptions, semantic, synthetics::Synthetics};
use selector_facts::*;
use selector_types::*;
use std::collections::HashSet;

pub(crate) struct Partition {
    identity: ContentHash,
    facts: FactSnapshot,
    synthetics: Option<Synthetics>,
}
pub(crate) fn prepare(
    line: &[u8],
    options: &ExtractOptions,
    include_synthetics: bool,
) -> Result<Partition, Error> {
    let decoded = semantic::decode(line)?;
    let identity = decoded.identity;
    let mut builder = FactBuilder::new();
    let mut synthetics = include_synthetics.then(Synthetics::default);
    semantic::admit(
        &mut builder,
        decoded,
        options,
        &mut HashSet::new(),
        synthetics.as_mut(),
    )?;
    Ok(Partition {
        identity,
        facts: builder.finish()?,
        synthetics,
    })
}
fn string(map: &[StrId], value: StrId) -> StrId {
    if value.is_none() {
        value
    } else {
        map[value.index()]
    }
}
fn symbol(map: &[SymbolId], value: SymbolId) -> SymbolId {
    if value.is_none() {
        value
    } else {
        map[value.index()]
    }
}

pub(crate) fn publish(
    builder: &mut FactBuilder,
    pending: Option<&mut Synthetics>,
    partition: Partition,
    seen: &mut HashSet<ContentHash>,
) -> Result<(), Error> {
    let Partition {
        identity,
        facts,
        synthetics,
    } = partition;
    if !facts.revision.is_none() {
        let revision = facts.text(facts.revision);
        if !builder.facts.revision.is_none()
            && builder.facts.text(builder.facts.revision) != revision
        {
            return Err(Error::Invalid("mixed capture revisions"));
        }
        builder.facts.revision = builder.intern(revision)?;
    }
    if !seen.insert(identity) {
        return Ok(());
    }
    if facts.files.len() != 1 || !facts.bodies.is_empty() || !facts.operations.is_empty() {
        return Err(Error::Invalid("semantic document partition shape"));
    }
    let mut strings = Vec::with_capacity(facts.strings.len());
    for index in 0..facts.strings.len() {
        strings.push(builder.intern(facts.text(StrId(index as u32)))?);
    }
    let file = FileId::checked(builder.facts.files.len())?;
    let source = facts.files[0];
    builder.facts.files.push(FileRecord {
        path: string(&strings, source.path),
        source: string(&strings, source.source),
        revision: string(&strings, source.revision),
        context: string(&strings, source.context),
        source_hash: source.source_hash,
        flags: source.flags,
    });
    let mut symbols = Vec::with_capacity(facts.symbols.len());
    for record in &facts.symbols {
        symbols.push(builder.ensure_pooled_symbol(string(&strings, record.name), file)?);
    }
    for (index, local) in facts.symbols.iter().enumerate() {
        let id = symbols[index];
        let previous = builder.facts.symbols[id.index()];
        let signature = string(&strings, local.signature);
        if local.flags & SYMBOL_DEFINED != 0 && local.kind != 0 {
            if previous.flags & SYMBOL_DEFINED != 0
                && !previous.signature.is_none()
                && (previous.signature != signature || previous.kind != local.kind)
            {
                builder.issue(
                    IssueKind::ContextConflict,
                    file,
                    id,
                    "compiler identity has conflicting information in one context",
                )?;
            }
            let record = &mut builder.facts.symbols[id.index()];
            record.display = string(&strings, local.display);
            record.signature = signature;
            record.kind = local.kind;
            record.properties = local.properties;
        }
        let record = &mut builder.facts.symbols[id.index()];
        record.flags |= local.flags;
        if local.span.start < local.span.end {
            record.file = file;
            record.span = local.span;
        } else if record.span.start == record.span.end && !local.file.is_none() {
            record.file = file;
        }
        if !local.owner.is_none() && (record.owner.is_none() || local.flags & SYMBOL_DEFINED != 0) {
            record.owner = symbol(&symbols, local.owner);
        }
    }
    builder.facts.occurrences.reserve(facts.occurrences.len());
    for o in facts.occurrences {
        builder.facts.occurrences.push(OccurrenceRecord {
            file,
            symbol: symbol(&symbols, o.symbol),
            ..o
        });
    }
    builder.facts.relations.reserve(facts.relations.len());
    for r in facts.relations {
        builder.facts.relations.push(RelationRecord {
            file,
            source: symbol(&symbols, r.source),
            target: symbol(&symbols, r.target),
            ..r
        });
    }
    for issue in facts.issues {
        builder.facts.issues.push(IssueRecord {
            file: if issue.file.is_none() {
                FileId::NONE
            } else {
                file
            },
            symbol: symbol(&symbols, issue.symbol),
            detail: string(&strings, issue.detail),
            kind: issue.kind,
        });
    }
    if let (Some(target), Some(local)) = (pending, synthetics) {
        let node_offset =
            u32::try_from(target.nodes.len()).map_err(|_| Error::Limit("synthetic nodes"))?;
        let link_offset =
            u32::try_from(target.links.len()).map_err(|_| Error::Limit("synthetic links"))?;
        let parameter_offset = u32::try_from(target.parameters.len())
            .map_err(|_| Error::Limit("synthetic parameters"))?;
        target.nodes.reserve(local.nodes.len());
        for mut node in local.nodes {
            node.target = symbol(&symbols, node.target);
            node.children.start = node
                .children
                .start
                .checked_add(link_offset)
                .ok_or(Error::Limit("synthetic links"))?;
            node.parameters.start = node
                .parameters
                .start
                .checked_add(parameter_offset)
                .ok_or(Error::Limit("synthetic parameters"))?;
            target.nodes.push(node);
        }
        target.links.reserve(local.links.len());
        for link in local.links {
            target.links.push(
                link.checked_add(node_offset)
                    .ok_or(Error::Limit("synthetic nodes"))?,
            );
        }
        for parameter in local.parameters {
            target.parameters.push(symbol(&symbols, parameter));
        }
        for mut root in local.roots {
            root.file = file;
            root.node = root
                .node
                .checked_add(node_offset)
                .ok_or(Error::Limit("synthetic nodes"))?;
            target.roots.push(root);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    fn row(path: &str, revision: &str) -> Vec<u8> {
        serde_json::to_vec(&json!({"path":path,"revision":revision,"source_text":"x",
            "source_sha256":crate::sha(b"x").to_string(),"input_target_contexts":["a"],
            "document":{"schema":4,"uri":path,"md5":"9dd4e461268c8034f5c8564e155c67a6",
                "symbols":[],"occurrences":[{"symbol":"local0","role":1,"range":{"start_character":0,"end_character":1}}]}})).unwrap()
    }
    #[test]
    fn undefined_locals_keep_document_file_identity_through_publication() {
        let mut builder = FactBuilder::new();
        let mut seen = HashSet::new();
        for path in ["A.scala", "B.scala"] {
            publish(
                &mut builder,
                None,
                prepare(&row(path, "r"), &ExtractOptions::default(), false).unwrap(),
                &mut seen,
            )
            .unwrap();
        }
        let facts = builder.finish().unwrap();
        let a = facts.occurrences[0].symbol;
        let b = facts.occurrences[1].symbol;
        assert_ne!(a, b);
        assert_ne!(facts.symbols[a.index()].file, facts.symbols[b.index()].file);
        assert_eq!(facts.symbols[a.index()].flags & SYMBOL_DEFINED, 0);
    }
    #[test]
    fn duplicate_partition_cannot_hide_mixed_revision() {
        let mut builder = FactBuilder::new();
        let mut seen = HashSet::new();
        publish(
            &mut builder,
            None,
            prepare(&row("A.scala", "r1"), &ExtractOptions::default(), false).unwrap(),
            &mut seen,
        )
        .unwrap();
        assert!(
            publish(
                &mut builder,
                None,
                prepare(&row("A.scala", "r2"), &ExtractOptions::default(), false).unwrap(),
                &mut seen
            )
            .is_err()
        );
    }
}
