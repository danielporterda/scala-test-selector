//! Admit the paired runtime inputs for class- and method-level analysis.
use super::{
    CapturedClasspath, ClasspathEntry, ContentHash, EntryKind, Error, InputIdentity, Inputs,
    Limits, MAX_ENTRIES, Side, Verifier, comparable_launch, entry, java_feature, no_symlinks,
    objects, unique,
};
use std::cmp::Ordering;
use std::path::PathBuf;

const MAX_CHANGED_CLASSES: usize = 4096;

#[derive(Debug, serde::Serialize)]
pub struct ClasspathDelta {
    pub schema: &'static str,
    pub base: InputIdentity,
    pub head: InputIdentity,
    pub context_id: String,
    pub java_feature: u16,
    pub ordered_providers: usize,
    pub verified_provider_entries: usize,
    pub verified_provider_bytes: u64,
    pub changed_directories: Vec<DirectoryDelta>,
    pub omission_authority: bool,
}

#[derive(Debug, serde::Serialize)]
pub struct DirectoryDelta {
    pub ordered_index: usize,
    pub path: PathBuf,
    pub repo_relative: bool,
    pub base_sha256: String,
    pub head_sha256: String,
    pub classes: Vec<ClassFileDelta>,
}

#[derive(Debug, serde::Serialize)]
pub struct ClassFileDelta {
    pub path: String,
    pub base: Option<FileIdentity>,
    pub head: Option<FileIdentity>,
}

#[derive(Debug, serde::Serialize)]
pub struct FileIdentity {
    pub bytes: u64,
    pub sha256: String,
}

/// Verify both ordered classpaths and report all exact directory class changes.
/// Changed JARs, changed non-class files, and open JAR manifest dependencies
/// fail admission. Generated classes are compared with their ordinary bytes.
pub fn audit_test_classpath_delta(
    base: Inputs<'_>,
    head: Inputs<'_>,
    context_id: &str,
) -> Result<ClasspathDelta, Error> {
    let (base, head) = (Side::load(base)?, Side::load(head)?);
    let base_contexts = unique(&base.capture.contexts, |c| &c.context_id)?;
    let head_contexts = unique(&head.capture.contexts, |c| &c.context_id)?;
    let missing = "missing paired test context for classpath delta";
    let before = base_contexts
        .get(context_id)
        .ok_or(Error::Invalid(missing))?;
    let after = head_contexts
        .get(context_id)
        .ok_or(Error::Invalid(missing))?;
    if before.configuration != "test"
        || after.configuration != "test"
        || !comparable_launch(&base, before, &head, after)
    {
        return Err(Error::Invalid("incomparable paired test launch"));
    }
    let count = before.full_classpath.len();
    if count == 0 || count != after.full_classpath.len() {
        return Err(Error::Invalid("incomparable paired test classpath length"));
    }
    if count > MAX_ENTRIES {
        return Err(Error::Budget);
    }
    let java_feature = java_feature(&base)?;
    let base_objects = objects(&base)?;
    let head_objects = objects(&head)?;
    let mut base_entries = Vec::with_capacity(count);
    let mut head_entries = Vec::with_capacity(count);
    let mut changed_directories = Vec::new();
    let mut remaining = MAX_CHANGED_CLASSES;
    let mut verifier = Verifier::default();
    for (index, (old, new)) in before
        .full_classpath
        .iter()
        .zip(&after.full_classpath)
        .enumerate()
    {
        let logical = base.logical(&old.path);
        if old.index != index
            || new.index != index
            || logical != head.logical(&new.path)
            || base.logical(&old.input_object) != head.logical(&new.input_object)
        {
            return Err(Error::Invalid(
                "incomparable paired test classpath location",
            ));
        }
        let b = entry(&base, &base_objects, old)?;
        let h = entry(&head, &head_objects, new)?;
        if b.sha256 != h.sha256 {
            let classes = changed_classes(&b, &h, &mut remaining, &mut verifier)?;
            changed_directories.push(DirectoryDelta {
                ordered_index: index,
                path: logical.1.to_owned(),
                repo_relative: logical.0,
                base_sha256: b.sha256.to_string(),
                head_sha256: h.sha256.to_string(),
                classes,
            });
        } else if b.kind != h.kind || b.kind == EntryKind::Unavailable {
            return Err(Error::Invalid(
                "incompatible paired test classpath provider",
            ));
        }
        base_entries.push(b);
        head_entries.push(h);
    }
    if !verifier.verify_scope(&base_entries, java_feature)?
        || !verifier.verify_scope(&head_entries, java_feature)?
    {
        return Err(Error::Invalid(
            "open paired test classpath manifest dependencies",
        ));
    }
    Ok(ClasspathDelta {
        schema: "selector-test-classpath-delta/v1",
        base: base.identity,
        head: head.identity,
        context_id: context_id.to_owned(),
        java_feature,
        ordered_providers: count,
        verified_provider_entries: verifier.admitted.len(),
        verified_provider_bytes: verifier.bytes,
        changed_directories,
        omission_authority: false,
    })
}

fn changed_classes(
    base: &ClasspathEntry,
    head: &ClasspathEntry,
    remaining: &mut usize,
    verifier: &mut Verifier,
) -> Result<Vec<ClassFileDelta>, Error> {
    let (
        EntryKind::Directory {
            bytes: base_bytes, ..
        },
        EntryKind::Directory {
            bytes: head_bytes, ..
        },
    ) = (&base.kind, &head.kind)
    else {
        return Err(Error::Invalid("classpath delta outside paired directories"));
    };
    no_symlinks(&base.path)?;
    no_symlinks(&head.path)?;
    let mut b = CapturedClasspath::new(vec![base.clone()], Limits::default())?;
    let mut h = CapturedClasspath::new(vec![head.clone()], Limits::default())?;
    let mut old = b.directory_files(0)?.peekable();
    let mut new = h.directory_files(0)?.peekable();
    let mut classes = Vec::new();
    while old.peek().is_some() || new.peek().is_some() {
        let order = match (old.peek(), new.peek()) {
            (Some(b), Some(h)) => b.0.cmp(h.0),
            (Some(_), None) => Ordering::Less,
            (None, Some(_)) => Ordering::Greater,
            (None, None) => break,
        };
        let (b, h) = match order {
            Ordering::Less => (old.next(), None),
            Ordering::Equal => (old.next(), new.next()),
            Ordering::Greater => (None, new.next()),
        };
        if b == h {
            continue;
        }
        let path = b.or(h).expect("at least one observed file").0;
        if !path.ends_with(".class") {
            return Err(Error::Invalid("classpath delta includes a non-class file"));
        }
        *remaining = remaining.checked_sub(1).ok_or(Error::Budget)?;
        let file = |(_, bytes, sha): (&str, u64, ContentHash)| FileIdentity {
            bytes,
            sha256: sha.to_string(),
        };
        classes.push(ClassFileDelta {
            path: path.to_owned(),
            base: b.map(file),
            head: h.map(file),
        });
    }
    for (provider, bytes) in [(base, *base_bytes), (head, *head_bytes)] {
        if !verifier.admitted.contains_key(provider) {
            verifier.record(provider, bytes, Vec::new())?;
        }
    }
    Ok(classes)
}
