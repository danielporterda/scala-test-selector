//! Borrowed ownership queries for SemanticDB symbol descriptors.
//!
//! Compiler scopes are authoritative when supplied. This fallback only removes
//! the last descriptor; it never resolves a source name, strips an overload
//! disambiguator, or turns a declared type into a runtime receiver.

/// Whether `symbol` has the exact SemanticDB local-symbol spelling `local[0-9]+`.
///
/// A global package named `local` and a backticked name containing `local` remain
/// global identities. Document-scoped canonical locals (`@local:...`) are handled
/// separately by [`global_owner`].
pub fn is_local(symbol: &str) -> bool {
    symbol
        .strip_prefix("local")
        .is_some_and(|suffix| !suffix.is_empty() && suffix.bytes().all(|b| b.is_ascii_digit()))
}

/// Structural Scala 2 / Java class ABI for a global compiler type/module owner.
/// This does not resolve a symbol or erase type aliases. Unsupported spellings
/// return None, so class absence is never inferred from a guessed binary name.
pub fn jvm_owner(symbol: &str) -> Option<String> {
    if symbol.starts_with('@') || symbol.starts_with("_root_/") || symbol.starts_with("_empty_/") {
        return None;
    }
    let bytes = symbol.as_bytes();
    let mut out = String::with_capacity(symbol.len());
    let mut at = 0;
    let mut classes = false;
    while at < bytes.len() {
        let start = at;
        let name = if bytes[at] == b'`' {
            at += 1;
            let quoted = at;
            while at < bytes.len() && bytes[at] != b'`' {
                at += 1;
            }
            if at == bytes.len() {
                return None;
            }
            let name = &symbol[quoted..at];
            at += 1;
            name
        } else {
            while at < bytes.len() && !matches!(bytes[at], b'/' | b'.' | b'#' | b'(' | b'[' | b'`')
            {
                at += 1;
            }
            &symbol[start..at]
        };
        if name.is_empty() || at >= bytes.len() {
            return None;
        }
        let descriptor = bytes[at];
        at += 1;
        match descriptor {
            b'/' if !classes => {
                out.push_str(&jvm_name(name)?);
                out.push('/');
            }
            b'#' | b'.' => {
                if classes {
                    out.push('$');
                }
                out.push_str(&jvm_name(name)?);
                classes = true;
                if at == bytes.len() && descriptor == b'.' {
                    out.push('$');
                }
            }
            _ => return None,
        }
    }
    classes.then_some(out)
}

/// Exact supported ASCII subset of Scala NameTransformer encoding. This is a
/// compiler-identity projection, never a source-spelling callee resolver.
pub fn jvm_name(name: &str) -> Option<String> {
    let mut out = String::with_capacity(name.len());
    for c in name.chars() {
        let encoded = match c {
            '~' => "$tilde",
            '=' => "$eq",
            '<' => "$less",
            '>' => "$greater",
            '!' => "$bang",
            '#' => "$hash",
            '%' => "$percent",
            '^' => "$up",
            '&' => "$amp",
            '|' => "$bar",
            '*' => "$times",
            '/' => "$div",
            '+' => "$plus",
            '-' => "$minus",
            ':' => "$colon",
            '\\' => "$bslash",
            '?' => "$qmark",
            '@' => "$at",
            c if c.is_ascii_alphanumeric() || c == '_' || c == '$' => {
                out.push(c);
                continue;
            }
            _ => return None,
        };
        out.push_str(encoded);
    }
    (!out.is_empty()).then_some(out)
}

/// Return the compiler descriptor enclosing `symbol`, borrowing its exact bytes.
///
/// This is the allocation-free counterpart of the reference engine's
/// `semantic_index.global_owner`. Method overloads, quoted names, value
/// parameters and type parameters retain their compiler identity. Two offsets
/// suffice: only the final boundary and its predecessor can be returned.
///
/// Empty, local and scoped-local symbols have no global owner. Unterminated
/// quotes or delimiters, nested unquoted delimiters, mismatched closing
/// delimiters and incomplete final descriptors are rejected. The reference
/// engine's single depth counter accepts some malformed inputs; rejecting those
/// does not turn malformed bytes into an authoritative ownership relation.
/// This helper does not replace full symbol validation at input admission.
pub fn global_owner(symbol: &str) -> Option<&str> {
    if symbol.is_empty() || is_local(symbol) || symbol.starts_with("@local:") {
        return None;
    }
    let mut previous_boundary = None;
    let mut last_boundary = None;
    let mut quoted = false;
    let mut closing = None;
    let bytes = symbol.as_bytes();

    for (index, &byte) in bytes.iter().enumerate() {
        if byte == b'`' {
            quoted = !quoted;
            continue;
        }
        if quoted {
            continue;
        }
        let mut boundary = None;
        match byte {
            b'(' | b'[' => {
                if closing.is_some() {
                    return None;
                }
                if index > 0 && matches!(bytes[index - 1], b'.' | b'#' | b'/') {
                    boundary = Some(index);
                }
                closing = Some(if byte == b'(' { b')' } else { b']' });
            }
            b')' | b']' => {
                if closing != Some(byte) {
                    return None;
                }
                closing = None;
            }
            b'.' | b'#' | b'/' if closing.is_none() => boundary = Some(index + 1),
            _ => {}
        }
        if let Some(boundary) = boundary {
            previous_boundary = last_boundary;
            last_boundary = Some(boundary);
        }
    }
    if quoted
        || closing.is_some()
        || !matches!(bytes.last(), Some(b'.' | b'#' | b'/' | b')' | b']'))
    {
        return None;
    }
    let end = match last_boundary {
        Some(end) if end == bytes.len() => previous_boundary?,
        Some(end) => end,
        None => return None,
    };
    Some(&symbol[..end])
}

/// Borrow the final descriptor's name for an already namespace-checked model.
///
/// This is a name projection, never a target resolver: the full original symbol
/// (including overload disambiguation) remains the operation's identity. Quoted
/// names are unwrapped without allocation and punctuation inside them is kept.
/// Descriptor parameters and type parameters return their enclosed names.
pub fn member_name(symbol: &str) -> Option<&str> {
    if symbol.is_empty() || is_local(symbol) || symbol.starts_with("@local:") {
        return None;
    }
    let owner_len = global_owner(symbol)?.len();
    let descriptor = &symbol[owner_len..];
    let name = if descriptor.starts_with('(') && descriptor.ends_with(')')
        || descriptor.starts_with('[') && descriptor.ends_with(']')
    {
        &descriptor[1..descriptor.len() - 1]
    } else {
        let mut quoted = false;
        let mut end = None;
        for (index, byte) in descriptor.bytes().enumerate() {
            if byte == b'`' {
                quoted = !quoted;
            } else if !quoted && matches!(byte, b'(' | b'.' | b'#' | b'/') {
                end = Some(index);
                break;
            }
        }
        &descriptor[..end?]
    };
    let name = if name.starts_with('`') && name.ends_with('`') && name.len() >= 2 {
        &name[1..name.len() - 1]
    } else {
        name
    };
    if name.is_empty() { None } else { Some(name) }
}

#[cfg(test)]
mod tests {
    use super::{global_owner, is_local, jvm_owner, member_name};

    #[test]
    fn jvm_owner_preserves_structural_nested_module_and_operator_abi() {
        for (symbol, expected) in [
            ("p/C#", "p/C"),
            ("p/C.", "p/C$"),
            ("p/C#Nested#", "p/C$Nested"),
            ("p/C.Nested#", "p/C$Nested"),
            ("p/`++`#", "p/$plus$plus"),
            ("p/C#Inner.", "p/C$Inner$"),
        ] {
            assert_eq!(jvm_owner(symbol).as_deref(), Some(expected));
        }
        for symbol in [
            "local4",
            "@closure:x:0",
            "p/C#f().",
            "p/C#[T]",
            "p/",
            "p/名字#",
            "p/`a.b`#",
        ] {
            assert_eq!(jvm_owner(symbol), None, "{symbol}");
        }
    }

    #[test]
    fn locals_are_exact_ascii_document_scoped_identifiers() {
        for symbol in [
            "local0",
            "local12",
            "local00042",
            "local999999999999999999999999",
        ] {
            assert!(is_local(symbol), "{symbol}");
            assert_eq!(global_owner(symbol), None);
        }
        for symbol in [
            "",
            "local",
            "Local1",
            "local-1",
            "local1x",
            "local١",
            "local１２",
            "local/package/C#",
            "`local12`#",
            "@local:doc:local0",
        ] {
            assert!(!is_local(symbol), "{symbol}");
        }
        assert_eq!(global_owner("@local:doc:local0"), None);
        assert_eq!(
            global_owner("local/package/C#f()."),
            Some("local/package/C#")
        );
    }

    #[test]
    fn compiler_descriptor_kinds_keep_exact_owner_prefixes() {
        for (symbol, owner) in [
            ("p/", None),
            ("_root_/", None),
            ("p/q/", Some("p/")),
            ("p/C#", Some("p/")),
            ("p/Object.", Some("p/")),
            ("p/C#member.", Some("p/C#")),
            ("p/C#f().", Some("p/C#")),
            ("p/C#f(+1).", Some("p/C#")),
            ("p/C#f(+37).(x)", Some("p/C#f(+37).")),
            ("p/C#f(+37).[T]", Some("p/C#f(+37).")),
            ("p/C#[T]", Some("p/C#")),
            ("p/C#`<init>`().(callback)", Some("p/C#`<init>`().")),
            ("p/C#Nested#f().", Some("p/C#Nested#")),
            ("p/C#f().localMethod().", Some("p/C#f().")),
        ] {
            assert_eq!(global_owner(symbol), owner, "{symbol}");
        }
    }

    #[test]
    fn backticks_hide_descriptor_punctuation_without_normalizing_names() {
        for (symbol, owner) in [
            ("p/C#`odd.name`().", "p/C#"),
            ("p/C#`x#y`().", "p/C#"),
            ("p/`path/part`#member.", "p/`path/part`#"),
            ("p/C#`[]()/#.`(+2).(`x.y`)", "p/C#`[]()/#.`(+2)."),
            ("p/C#[`[T]`]", "p/C#"),
            ("名字/型#`取得.値`().(引数)", "名字/型#`取得.値`()."),
        ] {
            assert_eq!(global_owner(symbol), Some(owner), "{symbol}");
            let actual = global_owner(symbol).unwrap();
            assert_eq!(
                actual.as_ptr(),
                symbol.as_ptr(),
                "owner must borrow input bytes"
            );
        }
    }

    #[test]
    fn real_compiler_identities_keep_overrides_parameters_and_synthetic_names() {
        for (symbol, owner) in [
            (
                "org/lfdecentralizedtrust/splice/SpliceApp.loadConfig().(defaultPorts)",
                "org/lfdecentralizedtrust/splice/SpliceApp.loadConfig().",
            ),
            (
                "com/digitalasset/canton/time/Clock#internalMonotonicTime().(minSpacingMicros)",
                "com/digitalasset/canton/time/Clock#internalMonotonicTime().",
            ),
            (
                "com/digitalasset/canton/time/Clock#scheduleAfterCancellable().[A]",
                "com/digitalasset/canton/time/Clock#scheduleAfterCancellable().",
            ),
            ("p/Case#copy$default$1().", "p/Case#"),
            ("p/Case.`<init>$default$1`().", "p/Case."),
        ] {
            assert_eq!(global_owner(symbol), Some(owner), "{symbol}");
        }
    }

    #[test]
    fn model_name_projection_handles_object_owners_and_quoted_names() {
        for (symbol, name) in [
            ("scala/Predef.assert().", "assert"),
            ("scala/concurrent/Future.apply().", "apply"),
            ("scala/collection/IterableOps#map(+2).", "map"),
            ("p/C#f(+2).(callback)", "callback"),
            ("p/C#f(+2).[T]", "T"),
            ("p/C#`odd.name/#`().", "odd.name/#"),
            ("p/C#`<init>`().", "<init>"),
        ] {
            assert_eq!(member_name(symbol), Some(name), "{symbol}");
        }
        for symbol in ["", "local2", "@local:doc:local2", "p/C#f("] {
            assert_eq!(member_name(symbol), None, "{symbol}");
        }
    }

    #[test]
    fn malformed_symbols_cannot_supply_an_owner() {
        for symbol in [
            "",
            "unterminated`",
            "p/C#`unfinished",
            "p/C#f(",
            "p/C#[T",
            "p/C#f()).",
            "p/C#f(].",
            "p/C#[T)",
            "p/C#f((x)).",
            "p/C#f().(x]",
            "p/C#unfinished",
        ] {
            assert_eq!(global_owner(symbol), None, "{symbol}");
        }
    }

    #[test]
    fn long_compiler_names_use_constant_auxiliary_storage() {
        // Stack input demonstrates that no name-length-dependent container is
        // needed. Repeated reads must always borrow the original prefix.
        let mut storage = [b'x'; 16_384];
        storage[..4].copy_from_slice(b"p/C#");
        let end = storage.len();
        storage[end - 3..].copy_from_slice(b"().");
        let symbol = std::str::from_utf8(&storage).unwrap();
        for _ in 0..32 {
            assert_eq!(global_owner(symbol), Some("p/C#"));
        }
    }

    #[test]
    fn captured_symbols_match_reference_descriptor_owners() {
        for row in include_str!("../../../fixtures/symbols/captured-owners.tsv").lines() {
            let (symbol, expected) = row.split_once('\t').unwrap();
            let expected = if expected == "-" {
                None
            } else {
                Some(expected)
            };
            assert_eq!(global_owner(symbol), expected, "{symbol}");
        }
    }
}
