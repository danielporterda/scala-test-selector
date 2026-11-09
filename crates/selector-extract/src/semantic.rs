use crate::{ExtractOptions, SourceCoordinates, from_json, json_error, sha};
use md5::{Digest as Md5Digest, Md5};
use selector_facts::*;
use selector_types::*;
use serde::Deserialize;
use serde_json::{Value, value::RawValue};
use sha2::{Digest, Sha256};
use std::borrow::Cow;
use std::collections::HashSet;

#[derive(Deserialize)]
pub(crate) struct Row<'a> {
    #[serde(default, borrow)]
    path: Cow<'a, str>,
    #[serde(default, borrow)]
    revision: Cow<'a, str>,
    #[serde(default, borrow)]
    source_text: Option<Cow<'a, str>>,
    #[serde(default, borrow)]
    source_sha256: Option<Cow<'a, str>>,
    #[serde(default, borrow)]
    source_md5: Option<Cow<'a, str>>,
    #[serde(default, borrow)]
    source_contexts: Vec<Cow<'a, str>>,
    #[serde(default, borrow)]
    input_target_contexts: Vec<Cow<'a, str>>,
    #[serde(borrow)]
    document: &'a RawValue,
}
#[derive(Deserialize)]
pub(crate) struct Document<'a> {
    #[serde(default)]
    schema: u32,
    #[serde(default)]
    language: u32,
    #[serde(default, borrow)]
    uri: Cow<'a, str>,
    #[serde(default, borrow)]
    text: Option<Cow<'a, str>>,
    #[serde(default, borrow)]
    md5: Cow<'a, str>,
    #[serde(default, borrow)]
    symbols: Vec<Information<'a>>,
    #[serde(default, borrow)]
    occurrences: Vec<Occurrence<'a>>,
    #[serde(default, borrow)]
    synthetics: Vec<Synthetic<'a>>,
}
#[derive(Deserialize)]
struct Information<'a> {
    #[serde(default, borrow)]
    symbol: Cow<'a, str>,
    #[serde(default, borrow)]
    display_name: Cow<'a, str>,
    #[serde(default)]
    kind: u32,
    #[serde(default)]
    language: u32,
    #[serde(default)]
    properties: u64,
    #[serde(default, borrow)]
    signature: Option<&'a RawValue>,
    #[serde(default, borrow)]
    annotations: Vec<&'a RawValue>,
    #[serde(default, borrow)]
    access: Option<&'a RawValue>,
    #[serde(default, borrow)]
    overridden_symbols: Vec<Cow<'a, str>>,
}
#[derive(Clone, Copy, Deserialize)]
struct Range {
    #[serde(default, deserialize_with = "coordinate")]
    start_line: i64,
    #[serde(default, deserialize_with = "coordinate")]
    start_character: i64,
    #[serde(default, deserialize_with = "coordinate")]
    end_line: i64,
    #[serde(default, deserialize_with = "coordinate")]
    end_character: i64,
}
// Some historical decoded captures retain the protobuf negative int32 sentinel
// as its unsigned 64-bit wire spelling. Preserve invalidity, never truncate it
// into an apparently valid column, and report the individual malformed range.
fn coordinate<'de, D: serde::Deserializer<'de>>(decoder: D) -> Result<i64, D::Error> {
    struct Position;
    impl<'de> serde::de::Visitor<'de> for Position {
        type Value = i64;
        fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str("integer source position")
        }
        fn visit_i64<E: serde::de::Error>(self, value: i64) -> Result<i64, E> {
            Ok(value)
        }
        fn visit_u64<E: serde::de::Error>(self, value: u64) -> Result<i64, E> {
            Ok(i64::try_from(value).unwrap_or(-1))
        }
    }
    decoder.deserialize_any(Position)
}
impl Range {
    fn coords(self) -> [i64; 4] {
        [
            self.start_line,
            self.start_character,
            self.end_line,
            self.end_character,
        ]
    }
}
#[derive(Deserialize)]
struct Occurrence<'a> {
    #[serde(borrow)]
    symbol: Cow<'a, str>,
    #[serde(default)]
    role: u32,
    #[serde(default)]
    range: Option<Range>,
}
#[derive(Deserialize)]
struct Synthetic<'a> {
    #[serde(default)]
    range: Option<Range>,
    #[serde(default, borrow)]
    tree: Option<&'a RawValue>,
}

pub(crate) struct Decoded<'a> {
    row: Row<'a>,
    document: Document<'a>,
    source_hash: ContentHash,
    coordinates: Option<SourceCoordinates>,
    invalid: Option<(IssueKind, &'static str)>,
    context: String,
    pub(crate) identity: ContentHash,
}

pub(crate) fn decode(line: &[u8]) -> Result<Decoded<'_>, Error> {
    let mut row: Row<'_> = serde_json::from_slice(line).map_err(json_error)?;
    let document: Document<'_> = from_json(row.document.get())?;
    let source = row.source_text.as_deref().or(document.text.as_deref());
    let mut invalid = None;
    let mut coordinates = None;
    let mut source_hash = ContentHash::default();
    if document.schema != 4 {
        invalid = Some((IssueKind::UnsupportedSchema, "SemanticDB schema must be 4"));
    }
    if let Some(source) = source {
        source_hash = sha(source.as_bytes());
        let digest = Md5::digest(source.as_bytes());
        let mut hex = [0u8; 32];
        for (i, byte) in digest.iter().enumerate() {
            const DIGITS: &[u8; 16] = b"0123456789abcdef";
            hex[i * 2] = DIGITS[(byte >> 4) as usize];
            hex[i * 2 + 1] = DIGITS[(byte & 15) as usize];
        }
        let digest = std::str::from_utf8(&hex).expect("hex digits");
        if document.md5.is_empty()
            || !document.md5.eq_ignore_ascii_case(digest)
            || row
                .source_md5
                .as_deref()
                .is_some_and(|s| !s.eq_ignore_ascii_case(digest))
            || row
                .source_sha256
                .as_deref()
                .is_some_and(|s| ContentHash::from_hex(s).ok() != Some(source_hash))
            || (row.source_text.is_some() && document.text.as_deref().is_some_and(|s| s != source))
        {
            invalid = Some((
                IssueKind::StaleSource,
                "source MD5/SHA256 does not match compiler capture",
            ));
        }
        coordinates = Some(SourceCoordinates::new(source)?);
    } else {
        invalid = Some((
            IssueKind::MissingSource,
            "compiler document has no captured source text",
        ));
    }
    if row.path.is_empty() {
        row.path = document.uri.clone();
    }
    if row.path.is_empty() {
        return Err(Error::Invalid("capture path"));
    }
    let contexts = if row.input_target_contexts.is_empty() {
        &mut row.source_contexts
    } else {
        &mut row.input_target_contexts
    };
    contexts.sort_unstable();
    contexts.dedup();
    let context = contexts
        .iter()
        .map(|c| c.as_ref())
        .collect::<Vec<_>>()
        .join("\0");
    let mut identity = Sha256::new();
    identity.update(row.path.as_bytes());
    identity.update([0]);
    identity.update(context.as_bytes());
    identity.update([0]);
    identity.update(row.document.get().as_bytes());
    Ok(Decoded {
        row,
        document,
        source_hash,
        coordinates,
        invalid,
        context,
        identity: ContentHash(identity.finalize().into()),
    })
}

pub(crate) fn admit(
    builder: &mut FactBuilder,
    decoded: Decoded<'_>,
    options: &ExtractOptions,
    seen: &mut HashSet<ContentHash>,
    mut synthetics: Option<&mut crate::synthetics::Synthetics>,
) -> Result<(), Error> {
    let Decoded {
        row,
        document,
        source_hash,
        coordinates,
        invalid,
        context,
        identity,
    } = decoded;
    if let Some(expected) = &options.expected_revision {
        if row.revision != expected.as_str() {
            return Err(Error::Invalid(
                "capture revision does not match expected revision",
            ));
        }
    }
    if !row.revision.is_empty() {
        if !builder.facts.revision.is_none()
            && builder.facts.text(builder.facts.revision) != row.revision
        {
            return Err(Error::Invalid("mixed capture revisions"));
        }
        builder.facts.revision = builder.intern(&row.revision)?;
    }
    if !seen.insert(identity) {
        return Ok(());
    }
    let file = FileId::checked(builder.facts.files.len())?;
    let path = builder.intern(&row.path)?;
    let source = row
        .source_text
        .as_deref()
        .or(document.text.as_deref())
        .map(|s| builder.intern(s))
        .transpose()?
        .unwrap_or(StrId::NONE);
    let revision = builder.intern(&row.revision)?;
    let context = builder.intern(&context)?;
    builder.facts.files.push(FileRecord {
        path,
        source,
        revision,
        context,
        source_hash,
        flags: if invalid.is_none() {
            SOURCE_VERIFIED
        } else {
            0
        },
    });
    if let Some((kind, detail)) = invalid {
        builder.issue(kind, file, SymbolId::NONE, detail)?;
        return Ok(());
    }
    let coordinates = coordinates.ok_or(Error::Invalid("source coordinates"))?;
    let first_symbol = builder.facts.symbols.len();
    for information in &document.symbols {
        information_fact(builder, file, information, document.language == 1)?;
    }
    for (ordinal, raw) in document.occurrences.iter().enumerate() {
        let symbol = builder.ensure_symbol(&raw.symbol, file)?;
        let span = raw
            .range
            .ok_or(Error::Invalid("occurrence without range"))
            .and_then(|r| coordinates.semantic_span(r.coords()));
        let span = match span {
            Ok(span) => span,
            Err(_) => {
                builder.issue(
                    IssueKind::InvalidInput,
                    file,
                    symbol,
                    "invalid or absent compiler occurrence range",
                )?;
                continue;
            }
        };
        builder.facts.occurrences.push(OccurrenceRecord {
            file,
            symbol,
            span,
            role: raw.role,
            ordinal: u32::try_from(ordinal).map_err(|_| Error::Limit("occurrence ordinal"))?,
        });
        if raw.role == 2 {
            let record = &mut builder.facts.symbols[symbol.index()];
            record.file = file;
            record.span = span;
            record.flags |= SYMBOL_DEFINED;
        }
    }
    // Synthetic tree references have a distinct role. They remain compilation
    // dependencies until validated syntax establishes executable ownership.
    for (ordinal, synthetic) in document.synthetics.iter().enumerate() {
        let span = synthetic
            .range
            .ok_or(Error::Invalid("synthetic range"))
            .and_then(|r| coordinates.semantic_span(r.coords()));
        let span = match span {
            Ok(span) => span,
            Err(_) => {
                builder.issue(
                    IssueKind::InvalidInput,
                    file,
                    SymbolId::NONE,
                    "invalid synthetic range",
                )?;
                continue;
            }
        };
        if let Some(tree) = synthetic.tree {
            let value: Value = from_json(tree.get())?;
            if let Some(pending) = synthetics.as_deref_mut() {
                let node = pending.parse(builder, file, &value, span, &coordinates)?;
                pending.bind_root(file, span, node);
            }
            let mut symbols = Vec::new();
            declared_symbols(&value, &mut symbols);
            symbols.sort_unstable();
            symbols.dedup();
            for name in symbols {
                let symbol = builder.ensure_symbol(name, file)?;
                builder.facts.occurrences.push(OccurrenceRecord {
                    file,
                    symbol,
                    span,
                    role: 3,
                    ordinal: u32::try_from(ordinal)
                        .map_err(|_| Error::Limit("synthetic ordinal"))?,
                });
            }
        }
    }
    // Scopes are authoritative. The descriptor grammar only supplies missing
    // owners; it preserves overload and parameter suffixes verbatim.
    let mut i = first_symbol;
    while i < builder.facts.symbols.len() {
        let s = builder.facts.symbols[i];
        if s.context == context && s.owner.is_none() {
            let name = builder.facts.text(s.name);
            if let Some(owner) = global_owner(name) {
                let owner = owner.to_owned();
                let parent = builder.ensure_symbol(&owner, file)?;
                builder.facts.symbols[i].owner = parent;
            }
        }
        i += 1;
    }
    Ok(())
}

fn information_fact(
    builder: &mut FactBuilder,
    file: FileId,
    information: &Information<'_>,
    scala: bool,
) -> Result<SymbolId, Error> {
    if information.symbol.is_empty() {
        return Ok(SymbolId::NONE);
    }
    let symbol = builder.ensure_symbol(&information.symbol, file)?;
    let display = builder.intern(&information.display_name)?;
    let signature = information
        .signature
        .map(|s| builder.intern(s.get()))
        .transpose()?
        .unwrap_or(StrId::NONE);
    let existing = builder.facts.symbols[symbol.index()];
    let exact_private = scala
        && information.language != 2
        && information.kind == 3
        && !signature.is_none()
        && builder.facts.files[file.index()].flags & SOURCE_VERIFIED != 0
        && information.access.is_some_and(|access| {
            matches!(
                access.get(),
                r#"{"private_access":null}"#
                    | r#"{"private_access":{}}"#
                    | r#"{"private_this_access":null}"#
                    | r#"{"private_this_access":{}}"#
            )
        })
        && (existing.flags & SYMBOL_DEFINED == 0
            || (existing.flags & SYMBOL_SCALA_PRIVATE_METHOD != 0
                && existing.signature == signature
                && existing.kind == information.kind));
    if existing.flags & SYMBOL_DEFINED != 0
        && !existing.signature.is_none()
        && (existing.signature != signature || existing.kind != information.kind)
    {
        builder.issue(
            IssueKind::ContextConflict,
            file,
            symbol,
            "compiler identity has conflicting information in one context",
        )?;
    }
    let record = &mut builder.facts.symbols[symbol.index()];
    record.display = display;
    record.kind = information.kind;
    record.properties = information.properties;
    record.signature = signature;
    // Metadata may repeat in another document's hardlink/signature. A verified
    // definition occurrence owns its source span; later metadata cannot move
    // that span into a different file.
    if record.file.is_none() || record.span.start == record.span.end {
        record.file = file;
    }
    record.flags |= SYMBOL_DEFINED;
    if exact_private {
        record.flags |= SYMBOL_SCALA_PRIVATE_METHOD;
    } else {
        // Inconsistent repeated metadata stays unproved even if a later row
        // repeats private access. It cannot restore the cleared authority.
        record.flags &= !SYMBOL_SCALA_PRIVATE_METHOD;
    }
    for overridden in &information.overridden_symbols {
        relation(builder, symbol, overridden, RelationKind::Override, file)?;
    }
    if let Some(signature) = information.signature {
        let mut projected = crate::signature::project(signature.get())?;
        if scala
            && information.language != 2
            && matches!(information.kind, 10 | 13 | 14)
            && projected.complete_scala_parents
            && builder.facts.files[file.index()].flags & SOURCE_VERIFIED != 0
        {
            builder.facts.symbols[symbol.index()].flags |= SYMBOL_SCALA_PARENTS_COMPLETE;
        }
        projected.references.sort_unstable();
        let mut previous = None;
        for target in projected.references.iter() {
            if previous == Some(target.0.as_ref()) {
                continue;
            }
            relation(builder, symbol, &target.0, RelationKind::Signature, file)?;
            previous = Some(target.0.as_ref());
        }
        for target in projected.parents.iter() {
            relation(builder, symbol, &target.0, RelationKind::Parent, file)?;
        }
        for target in projected.scoped_links.iter() {
            let target = builder.ensure_symbol(&target.0, file)?;
            builder.facts.symbols[target.index()].owner = symbol;
            builder.facts.relations.push(RelationRecord {
                source: symbol,
                target,
                kind: RelationKind::Member,
                file,
            });
        }
        for raw in projected.hardlinks {
            let info: Information<'_> = from_json(raw.get())?;
            let target = information_fact(builder, file, &info, scala)?;
            if !target.is_none() {
                builder.facts.symbols[target.index()].owner = symbol;
                builder.facts.relations.push(RelationRecord {
                    source: symbol,
                    target,
                    kind: RelationKind::Member,
                    file,
                });
            }
        }
    }
    for annotation in &information.annotations {
        let value: Value = from_json(annotation.get())?;
        let mut refs = Vec::new();
        declared_symbols(&value, &mut refs);
        for target in refs {
            relation(builder, symbol, target, RelationKind::Annotation, file)?;
        }
    }
    if let Some(access) = information.access {
        let value: Value = from_json(access.get())?;
        let mut refs = Vec::new();
        declared_symbols(&value, &mut refs);
        for target in refs {
            relation(builder, symbol, target, RelationKind::Signature, file)?;
        }
    }
    Ok(symbol)
}

fn relation(
    builder: &mut FactBuilder,
    source: SymbolId,
    target: &str,
    kind: RelationKind,
    file: FileId,
) -> Result<(), Error> {
    if target.is_empty() {
        return Ok(());
    }
    let target = builder.ensure_symbol(target, file)?;
    builder.facts.relations.push(RelationRecord {
        source,
        target,
        kind,
        file,
    });
    Ok(())
}

/// Only schema-declared symbol fields; literal/documentation payloads are opaque.
fn declared_symbols<'a>(value: &'a Value, out: &mut Vec<&'a str>) {
    match value {
        Value::Object(map) => {
            for (key, child) in map {
                match key.as_str() {
                    "symbol" => {
                        if let Some(s) = child.as_str() {
                            out.push(s);
                        }
                    }
                    "symlinks" | "overridden_symbols" => {
                        if let Some(xs) = child.as_array() {
                            out.extend(xs.iter().filter_map(Value::as_str));
                        }
                    }
                    "documentation" | "constant" | "literal_tree" | "constant_type" => (),
                    _ => declared_symbols(child, out),
                }
            }
        }
        Value::Array(xs) => {
            for child in xs {
                declared_symbols(child, out);
            }
        }
        _ => (),
    }
}
pub(crate) use selector_types::symbol::global_owner;

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn compiler_private_access_requires_verified_scala_and_consistent_metadata() {
        let mut b = FactBuilder::new();
        let path = b.intern("Private.scala").unwrap();
        let source = b.intern("").unwrap();
        b.facts.files.push(FileRecord {
            path,
            source,
            revision: StrId::NONE,
            context: StrId::NONE,
            source_hash: ContentHash([1; 32]),
            flags: SOURCE_VERIFIED,
        });
        let mut read = |name, access, scala| {
            let info = format!(
                r#"{{"symbol":"p/PrettyUtil#{name}().","kind":3,"language":1,"signature":{{"method_signature":{{"type_parameters":{{}}}}}},"access":{access}}}"#
            );
            let info: Information<'_> = from_json(&info).unwrap();
            let id = information_fact(&mut b, FileId(0), &info, scala).unwrap();
            b.facts.symbols[id.index()].flags & SYMBOL_SCALA_PRIVATE_METHOD != 0
        };
        let private = r#"{"private_access":null}"#;
        let private_this = r#"{"private_this_access":{}}"#;
        let private_package = r#"{"private_within_access":{"symbol":"p/"}}"#;
        let public = r#"{"public_access":null}"#;
        assert!(read("m", private, true));
        assert!(read("m", private, true));
        assert!(!read("m", public, true));
        assert!(!read("m", private, true));
        assert!(read("n", private_this, true));
        assert!(!read("o", private_package, true));
        assert!(!read("p", private, false));
    }
    #[test]
    fn owner_keeps_overloads() {
        assert_eq!(global_owner("a/B#f(+2).(x)"), Some("a/B#f(+2)."));
        assert_eq!(global_owner("a/B#f(+2)."), Some("a/B#"));
        assert_eq!(global_owner("a/`B.C`#f()."), Some("a/`B.C`#"));
        assert_eq!(global_owner("local2"), None);
    }
}
