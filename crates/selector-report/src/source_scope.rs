//! Source request scope is separate from execution completeness and omission
//! authority. Validation borrows paths and uses two compact file-ID sort runs.
use super::*;
use selector_result::{
    MAX_OUTSIDE_SOURCE_DELTAS, SourceChangeMode, SourceChangeScope, SourceFileDelta,
};

pub(crate) const OUTSIDE_NOTICE: &str = "Other captured source changes need a separate selection. This result does not authorize omissions for the whole checkout.";
pub(crate) const REQUESTED_NOTICE: &str = "This result records the effective requested source paths. Source scope alone does not authorize omissions for the whole checkout.";
pub(crate) const SNAPSHOT_NOTICE: &str = "This result covers the captured source delta. Source scope alone does not authorize omissions for the whole checkout.";
pub(crate) const UNKNOWN_NOTICE: &str =
    "Source change scope was not recorded; whole-checkout omission authority is unknown.";

fn key(facts: &FactSnapshot, file: FileId) -> (&str, &str) {
    (
        facts.path(file),
        facts.text(facts.files[file.index()].context),
    )
}
fn physical(facts: &FactSnapshot, file: FileId) -> bool {
    let file = &facts.files[file.index()];
    file.flags & SOURCE_VERIFIED != 0
        && file.flags & FILE_BINARY_SOURCE == 0
        && !file.source.is_none()
}
fn inventory(facts: &FactSnapshot) -> Result<Vec<FileId>, Error> {
    let mut ids: Vec<_> = (0..facts.files.len())
        .map(FileId::checked)
        .collect::<Result<_, _>>()?;
    ids.sort_unstable_by(|a, b| key(facts, *a).cmp(&key(facts, *b)));
    if ids.windows(2).any(|w| key(facts, w[0]) == key(facts, w[1])) {
        return Err(Error::Invalid("source scope duplicate contextual file"));
    }
    Ok(ids)
}
fn has_path(facts: &FactSnapshot, inventory: &[FileId], path: &str) -> bool {
    // The contextual inventory is already ordered by path first. A different
    // compiler context cannot prove that a physical source path disappeared.
    inventory
        .binary_search_by(|id| facts.path(*id).cmp(path))
        .is_ok()
}

pub(crate) fn validate(
    s: &ReportSnapshots<'_>,
    scope: Option<&SourceChangeScope>,
) -> Result<(), Error> {
    let Some(scope) = scope else { return Ok(()) };
    if scope.requested_paths.windows(2).any(|w| w[0] >= w[1])
        || scope.requested_paths.iter().any(String::is_empty)
        || scope.outside.len() > MAX_OUTSIDE_SOURCE_DELTAS
        || scope
            .outside
            .iter()
            .any(|row| row.base_file.is_none() && row.head_file.is_none())
    {
        return Err(Error::Invalid("source change scope shape"));
    }
    if scope.mode == SourceChangeMode::SnapshotDelta {
        if !scope.requested_paths.is_empty()
            || scope.outside_count != 0
            || !scope.outside.is_empty()
        {
            return Err(Error::Invalid("snapshot source scope"));
        }
        return Ok(());
    }
    let base = inventory(s.base_facts)?;
    let head = inventory(s.head_facts)?;
    let (mut b, mut h, mut count, mut sample) = (0, 0, 0u64, 0usize);
    while b < base.len() || h < head.len() {
        let (before, after) = match (base.get(b), head.get(h)) {
            (Some(before), Some(after)) => {
                match key(s.base_facts, *before).cmp(&key(s.head_facts, *after)) {
                    std::cmp::Ordering::Equal => {
                        b += 1;
                        h += 1;
                        (Some(*before), Some(*after))
                    }
                    std::cmp::Ordering::Less => {
                        b += 1;
                        (Some(*before), None)
                    }
                    std::cmp::Ordering::Greater => {
                        h += 1;
                        (None, Some(*after))
                    }
                }
            }
            (Some(before), None) => {
                b += 1;
                (Some(*before), None)
            }
            (None, Some(after)) => {
                h += 1;
                (None, Some(*after))
            }
            (None, None) => break,
        };
        let changed = match (before, after) {
            (Some(before), Some(after)) => {
                physical(s.base_facts, before)
                    && physical(s.head_facts, after)
                    && s.base_facts.files[before.index()].source_hash
                        != s.head_facts.files[after.index()].source_hash
            }
            (Some(before), None) => {
                physical(s.base_facts, before)
                    && !has_path(s.head_facts, &head, s.base_facts.path(before))
            }
            (None, Some(after)) => {
                physical(s.head_facts, after)
                    && !has_path(s.base_facts, &base, s.head_facts.path(after))
            }
            (None, None) => false,
        };
        if !changed {
            continue;
        }
        let path = after.map_or_else(
            || s.base_facts.path(before.unwrap()),
            |file| s.head_facts.path(file),
        );
        if scope
            .requested_paths
            .binary_search_by(|requested| requested.as_str().cmp(path))
            .is_ok()
        {
            continue;
        }
        count += 1;
        if sample < MAX_OUTSIDE_SOURCE_DELTAS {
            let expected = SourceFileDelta {
                base_file: before.unwrap_or(FileId::NONE),
                head_file: after.unwrap_or(FileId::NONE),
            };
            if scope.outside.get(sample) != Some(&expected) {
                return Err(Error::Invalid("source scope outside file provenance"));
            }
            sample += 1;
        }
    }
    if scope.outside_count != count || scope.outside.len() != sample {
        return Err(Error::Invalid("source scope outside count"));
    }
    Ok(())
}

fn notice(scope: &SourceChangeScope) -> &'static str {
    if scope.outside_count != 0 {
        OUTSIDE_NOTICE
    } else if scope.mode == SourceChangeMode::RequestedPaths {
        REQUESTED_NOTICE
    } else {
        SNAPSHOT_NOTICE
    }
}

pub(crate) fn write_json<W: Write>(
    out: &mut W,
    s: &ReportSnapshots<'_>,
    scope: Option<&SourceChangeScope>,
) -> Result<(), Error> {
    let Some(scope) = scope else {
        out.write_all(b"null")?;
        return Ok(());
    };
    out.write_all(b"{\"mode\":")?;
    json_string(
        out,
        match scope.mode {
            SourceChangeMode::RequestedPaths => "requested_paths",
            SourceChangeMode::SnapshotDelta => "snapshot_delta",
        },
    )?;
    out.write_all(b",\"effective_requested_source_paths\":[")?;
    for (i, path) in scope.requested_paths.iter().enumerate() {
        if i != 0 {
            out.write_all(b",")?;
        }
        json_string(out, path)?;
    }
    write!(
        out,
        "],\"outside_count\":{},\"outside_sample_complete\":{},\"covers_captured_source_delta\":{},\"whole_checkout_omission_authority\":false,\"notice\":",
        scope.outside_count,
        scope.outside_count == scope.outside.len() as u64,
        scope.outside_count == 0
    )?;
    json_string(out, notice(scope))?;
    out.write_all(b",\"outside\":[")?;
    for (i, row) in scope.outside.iter().enumerate() {
        if i != 0 {
            out.write_all(b",")?;
        }
        out.write_all(b"{\"base_file_id\":")?;
        json_id(out, row.base_file.0)?;
        out.write_all(b",\"head_file_id\":")?;
        json_id(out, row.head_file.0)?;
        let (facts, file) = if row.head_file.is_none() {
            (s.base_facts, row.base_file)
        } else {
            (s.head_facts, row.head_file)
        };
        let (path, context) = key(facts, file);
        out.write_all(b",\"path\":")?;
        json_string(out, path)?;
        out.write_all(b",\"context\":")?;
        json_string(out, context)?;
        for (name, facts, file) in [
            ("base_source_sha256", s.base_facts, row.base_file),
            ("head_source_sha256", s.head_facts, row.head_file),
        ] {
            write!(out, ",\"{name}\":")?;
            if file.is_none() {
                out.write_all(b"null")?;
            } else {
                write!(out, "\"{}\"", facts.files[file.index()].source_hash)?;
            }
        }
        out.write_all(b"}")?;
    }
    out.write_all(b"]}")?;
    Ok(())
}

pub(crate) fn write_text<W: Write>(
    out: &mut W,
    s: &ReportSnapshots<'_>,
    scope: Option<&SourceChangeScope>,
) -> Result<(), Error> {
    let Some(scope) = scope else {
        writeln!(out, "{UNKNOWN_NOTICE}")?;
        return Ok(());
    };
    writeln!(
        out,
        "Source scope: {}; {} effective requested source paths; {} captured source changes outside the request.",
        match scope.mode {
            SourceChangeMode::RequestedPaths => "requested paths",
            SourceChangeMode::SnapshotDelta => "snapshot delta",
        },
        scope.requested_paths.len(),
        scope.outside_count
    )?;
    writeln!(out, "{}", notice(scope))?;
    for path in &scope.requested_paths {
        writeln!(out, "  requested source: {path}")?;
    }
    for row in &scope.outside {
        let (facts, file) = if row.head_file.is_none() {
            (s.base_facts, row.base_file)
        } else {
            (s.head_facts, row.head_file)
        };
        let (path, context) = key(facts, file);
        writeln!(out, "  outside source: {path} [{context}]")?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn source_files(hash: u8) -> FactSnapshot {
        let mut b = selector_facts::FactBuilder::new();
        for i in 0..66 {
            let path = b.intern(&format!("src/Generated{i:02}.scala")).unwrap();
            let source = b
                .intern(if hash == 1 {
                    "object Before"
                } else {
                    "object After"
                })
                .unwrap();
            b.facts.files.push(selector_facts::FileRecord {
                path,
                source,
                revision: StrId::NONE,
                context: StrId::NONE,
                source_hash: ContentHash([hash; 32]),
                flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
            });
        }
        b.finish().unwrap()
    }
    #[test]
    fn outside_sample_is_bounded_and_count_is_checked_against_both_inventories() {
        let base = source_files(1);
        let head = source_files(2);
        let graph = ProgramGraph::default();
        let snapshots = ReportSnapshots {
            base_facts: &base,
            base_graph: &graph,
            head_facts: &head,
            head_graph: &graph,
        };
        let mut scope = SourceChangeScope {
            mode: SourceChangeMode::RequestedPaths,
            requested_paths: vec!["src/Generated65.scala".into()],
            outside_count: 65,
            outside: (0..64)
                .map(|id| SourceFileDelta {
                    base_file: FileId(id),
                    head_file: FileId(id),
                })
                .collect(),
        };
        validate(&snapshots, Some(&scope)).unwrap();
        let mut bytes = Vec::new();
        write_json(&mut bytes, &snapshots, Some(&scope)).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(json["outside"].as_array().unwrap().len(), 64);
        assert_eq!(json["outside_sample_complete"], false);
        assert_eq!(json["outside_count"], 65);
        scope.requested_paths.clear();
        scope.outside_count = 66;
        validate(&snapshots, Some(&scope)).unwrap();
        scope.requested_paths.push("src/Generated65.scala".into());
        scope.outside_count = 64;
        assert!(validate(&snapshots, Some(&scope)).is_err());
        scope.outside_count = 65;
        scope.outside[0].head_file = FileId(1);
        assert!(validate(&snapshots, Some(&scope)).is_err());
        scope.mode = SourceChangeMode::SnapshotDelta;
        assert!(validate(&snapshots, Some(&scope)).is_err());
    }
    #[test]
    fn compiler_context_moves_and_extra_contexts_are_not_physical_source_deltas() {
        fn files(rows: &[(&str, &str, u8)]) -> FactSnapshot {
            let mut builder = selector_facts::FactBuilder::new();
            for (path, context, hash) in rows {
                let path = builder.intern(path).unwrap();
                let context = builder.intern(context).unwrap();
                let source = builder.intern("object Example").unwrap();
                builder.facts.files.push(selector_facts::FileRecord {
                    path,
                    context,
                    source,
                    revision: StrId::NONE,
                    source_hash: ContentHash([*hash; 32]),
                    flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
                });
            }
            builder.finish().unwrap()
        }
        let graph = ProgramGraph::default();
        let empty = SourceChangeScope {
            mode: SourceChangeMode::RequestedPaths,
            requested_paths: Vec::new(),
            outside_count: 0,
            outside: Vec::new(),
        };
        let base = files(&[("src/Example.scala", "project:old", 1)]);
        for rows in [
            vec![("src/Example.scala", "project:new", 1)],
            vec![("src/Example.scala", "project:new", 2)],
            vec![
                ("src/Example.scala", "project:old", 1),
                ("src/Example.scala", "project:new", 1),
            ],
        ] {
            let head = files(&rows);
            let snapshots = ReportSnapshots {
                base_facts: &base,
                base_graph: &graph,
                head_facts: &head,
                head_graph: &graph,
            };
            validate(&snapshots, Some(&empty)).unwrap();
            let reversed = ReportSnapshots {
                base_facts: &head,
                base_graph: &graph,
                head_facts: &base,
                head_graph: &graph,
            };
            validate(&reversed, Some(&empty)).unwrap();
        }
        let changed = files(&[("src/Example.scala", "project:old", 2)]);
        let snapshots = ReportSnapshots {
            base_facts: &base,
            base_graph: &graph,
            head_facts: &changed,
            head_graph: &graph,
        };
        assert!(validate(&snapshots, Some(&empty)).is_err());
        let physical = SourceChangeScope {
            outside_count: 1,
            outside: vec![SourceFileDelta {
                base_file: FileId(0),
                head_file: FileId(0),
            }],
            ..empty
        };
        validate(&snapshots, Some(&physical)).unwrap();
        let new_path = files(&[("src/New.scala", "project:new", 1)]);
        let snapshots = ReportSnapshots {
            base_facts: &base,
            base_graph: &graph,
            head_facts: &new_path,
            head_graph: &graph,
        };
        let physical = SourceChangeScope {
            mode: SourceChangeMode::RequestedPaths,
            requested_paths: Vec::new(),
            outside_count: 2,
            outside: vec![
                SourceFileDelta {
                    base_file: FileId(0),
                    head_file: FileId::NONE,
                },
                SourceFileDelta {
                    base_file: FileId::NONE,
                    head_file: FileId(0),
                },
            ],
        };
        validate(&snapshots, Some(&physical)).unwrap();
    }
    #[test]
    fn full_delta_and_legacy_scope_never_grant_whole_checkout_omission_authority() {
        let scope = SourceChangeScope {
            mode: SourceChangeMode::SnapshotDelta,
            requested_paths: Vec::new(),
            outside_count: 0,
            outside: Vec::new(),
        };
        let base = source_files(1);
        let head = source_files(2);
        let graph = ProgramGraph::default();
        let snapshots = ReportSnapshots {
            base_facts: &base,
            base_graph: &graph,
            head_facts: &head,
            head_graph: &graph,
        };
        validate(&snapshots, Some(&scope)).unwrap();
        let mut bytes = Vec::new();
        write_json(&mut bytes, &snapshots, Some(&scope)).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(json["covers_captured_source_delta"], true);
        assert_eq!(json["whole_checkout_omission_authority"], false);
        bytes.clear();
        write_text(&mut bytes, &snapshots, None).unwrap();
        assert!(
            String::from_utf8(bytes)
                .unwrap()
                .contains("scope was not recorded")
        );
    }
}
