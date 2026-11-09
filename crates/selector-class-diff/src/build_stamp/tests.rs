use super::*;
use selector_models::binary::{Limits, parse_class};

const BASE: &[u8] = include_bytes!("../../../../fixtures/native-build-stamp/base-module.class");
const HEAD: &[u8] = include_bytes!("../../../../fixtures/native-build-stamp/head-module.class");
const FORWARDER_BYTES: &[u8] =
    include_bytes!("../../../../fixtures/native-build-stamp/forwarder.class");

fn observed<'a>(before: &'a [u8], after: &'a [u8]) -> Result<BuildStampDelta<'a>, Unsupported> {
    compare(before, after, FORWARDER_BYTES, FORWARDER_BYTES)
}

fn replace_literal(bytes: &[u8], original: &str, value: &[u8]) -> Vec<u8> {
    let start = bytes
        .windows(original.len())
        .position(|s| s == original.as_bytes())
        .unwrap();
    let mut result = bytes[..start - 2].to_vec();
    result.extend_from_slice(&(value.len() as u16).to_be_bytes());
    result.extend_from_slice(value);
    result.extend_from_slice(&bytes[start + original.len()..]);
    result
}

#[test]
fn admitted_template_is_the_compiled_pair_with_exact_field_reads_and_writes() {
    let delta = observed(BASE, HEAD).unwrap();
    assert_eq!(
        delta.before.compiled_version,
        "0.10.0-snapshot.20261012.1.0.vf20116bc"
    );
    assert_eq!(delta.after.commit_unix_timestamp, "1791883137");
    assert_ne!(delta.before_module, delta.after_module);
    assert_eq!(
        delta.reader_surfaces().collect::<Vec<_>>(),
        [
            ReaderSurface::CompiledVersion,
            ReaderSurface::CommitUnixTimestamp,
            ReaderSurface::FormattedSummary,
        ]
    );
    for bytes in [BASE, HEAD] {
        let class = parse_class(bytes, Limits::default()).unwrap();
        assert_eq!(class.name, OWNER);
        assert_eq!(class.flags & 0x10, 0x10, "the module class is final");
        let init = class.method("<clinit>", Some("()V")).unwrap().code.unwrap();
        assert_eq!(
            &init[16..31],
            &[
                0x12, 29, 0xb3, 0, 31, 0x12, 33, 0xb3, 0, 35, 0x12, 37, 0xb3, 0, 39
            ]
        );
        assert_eq!(
            &init[51..76],
            &[
                0xb2, 0, 23, 0xb6, 0, 63, 0x53, 0x59, 0x04, 0xb2, 0, 23, 0xb6, 0, 65, 0x53, 0x59,
                0x05, 0xb2, 0, 23, 0xb6, 0, 67, 0x53
            ]
        );
        assert_eq!(&init[79..], &[0xb6, 0, 75, 0xb3, 0, 77, 0xb1]);
        for (name, field_ref) in [
            ("compiledVersion", 31),
            ("commitUnixTimestamp", 35),
            ("compatibleVersion", 39),
            ("toString", 77),
        ] {
            let f = class.fields.iter().find(|f| f.name == name).unwrap();
            assert_eq!(f.flags, 0x1a, "{name} is private static final");
            assert_eq!(f.descriptor, "Ljava/lang/String;");
            let getter = class.method(name, Some(DESCRIPTOR)).unwrap();
            assert_eq!(getter.flags, 1, "getter is public and non-static");
            assert_eq!(getter.code.unwrap(), &[0xb2, 0, field_ref, 0xb0]);
        }
    }
    let class = parse_class(FORWARDER_BYTES, Limits::default()).unwrap();
    for (name, method_ref) in [
        ("compiledVersion", 53),
        ("commitUnixTimestamp", 50),
        ("compatibleVersion", 47),
        ("toString", 44),
    ] {
        let method = class.method(name, Some(DESCRIPTOR)).unwrap();
        assert_eq!(method.flags, 9, "forwarder is public static");
        assert_eq!(
            method.code.unwrap(),
            &[0xb2, 0, 16, 0xb6, 0, method_ref, 0xb0]
        );
    }
}

#[test]
fn one_changed_literal_affects_only_its_getter_and_formatted_summary() {
    let version_only = replace_literal(BASE, "0.10.0-snapshot.20261012.1.0.vf20116bc", b"10.0.0");
    assert_eq!(
        observed(BASE, &version_only)
            .unwrap()
            .reader_surfaces()
            .collect::<Vec<_>>(),
        [
            ReaderSurface::CompiledVersion,
            ReaderSurface::FormattedSummary
        ]
    );
    let timestamp_only = replace_literal(BASE, "1791804334", b"1");
    assert_eq!(
        observed(BASE, &timestamp_only)
            .unwrap()
            .reader_surfaces()
            .collect::<Vec<_>>(),
        [
            ReaderSurface::CommitUnixTimestamp,
            ReaderSurface::FormattedSummary
        ]
    );
    assert_eq!(observed(BASE, BASE).unwrap().reader_surfaces().count(), 0);
}

#[test]
fn different_forwarder_compatible_value_or_wire_never_inherits_the_model() {
    let mut bad_forwarder = FORWARDER_BYTES.to_vec();
    bad_forwarder.push(0);
    assert_eq!(
        compare(BASE, HEAD, FORWARDER_BYTES, &bad_forwarder),
        Err(Unsupported::ForwarderTemplate)
    );
    let compatible = replace_literal(BASE, "0.9.1", b"0.9.2");
    let mut altered_body = HEAD.to_vec();
    let at = altered_body
        .windows(5)
        .position(|s| s == [0x12, 29, 0xb3, 0, 31])
        .unwrap();
    altered_body[at + 4] = 35;
    for invalid in [&compatible, &altered_body, &HEAD[..HEAD.len() - 1]] {
        assert_eq!(observed(BASE, invalid), Err(Unsupported::ModuleTemplate));
    }
    let malformed = replace_literal(BASE, "1791804334", b"9223372036854775808");
    assert_eq!(observed(BASE, &malformed), Err(Unsupported::StampLiteral));
    assert_eq!(
        observed(BASE, &[0; MAX_CLASS_BYTES + 1]),
        Err(Unsupported::ClassSize)
    );
}

#[test]
fn generated_source_requires_the_exact_compiled_literals_and_template() {
    let before = br#"// $COVERAGE-OFF$
package org.lfdecentralizedtrust.splice.environment

/** This object was generated by sbt-buildinfo. */
case object BuildInfo {
  /** The value is "0.10.0-snapshot.20261012.1.0.vf20116bc". */
  val compiledVersion: String = "0.10.0-snapshot.20261012.1.0.vf20116bc"
  /** The value is "1791804334". */
  val commitUnixTimestamp: String = "1791804334"
  /** The value is "0.9.1". */
  val compatibleVersion: String = "0.9.1"
  override val toString: String = {
    "compiledVersion: %s, commitUnixTimestamp: %s, compatibleVersion: %s".format(
      compiledVersion, commitUnixTimestamp, compatibleVersion
    )
  }
}
// $COVERAGE-ON$
"#;
    let delta = observed(BASE, HEAD).unwrap();
    let after = std::str::from_utf8(before)
        .unwrap()
        .replace(delta.before.compiled_version, delta.after.compiled_version)
        .replace(
            delta.before.commit_unix_timestamp,
            delta.after.commit_unix_timestamp,
        );
    let hashes = delta.verify_sources(before, after.as_bytes()).unwrap();
    assert_eq!(
        hashes.map(|h| h.to_string()),
        [
            "9cda9ea9925fb93ae37d69233ef36fe6b3e055184e608ca69e31f81a7a930b5b",
            "92be90d3b76a9476a3449d5a181750dea97f9e5c74d674973236d6f7b3da46de",
        ]
    );
    let altered = after.replace("0.9.1", "0.9.2");
    for bad in [before.as_slice(), altered.as_bytes()] {
        assert_eq!(
            delta.verify_sources(before, bad),
            Err(Unsupported::SourceTemplate)
        );
    }
}
