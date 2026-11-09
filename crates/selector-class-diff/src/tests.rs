use super::*;

const BASE: &[u8] =
    include_bytes!("../../../fixtures/native-lnt/variants/base/classes/lntcase/Probe.class");
const SHIFTED: &[u8] =
    include_bytes!("../../../fixtures/native-lnt/variants/shifted/classes/lntcase/Probe.class");
fn compare(a: &[u8], b: &[u8]) -> LntComparison {
    compare_line_number_tables(a, b, LntLimits::default())
}

#[test]
fn genuine_shifted_lines_remain_observable_without_omission_authority() {
    let result = compare(BASE, SHIFTED);
    assert_eq!(result.change, LntChange::LineNumberTablesOnly, "{result:?}");
    let (before, after) = result.raw_hashes.unwrap();
    assert_ne!(before, after);
    assert!(result.diagnostic_only());
    assert!(!result.omission_authority());
    assert!(result.metrics.instructions_validated > 0);
    assert!(result.metrics.line_tables_validated > 0);
    assert_eq!(compare(BASE, BASE).change, LntChange::Identical);
    let fixture: serde_json::Value =
        serde_json::from_str(include_str!("../../../fixtures/native-lnt/manifest.json")).unwrap();
    let left = &fixture["observations"]["base"];
    let right = &fixture["observations"]["shifted"];
    assert_eq!(
        left["stack_line"].as_u64().unwrap() + 7,
        right["stack_line"].as_u64().unwrap()
    );
    assert_eq!(left["stack_origin"], "lntcase.Thrower");
    assert_eq!(right["stack_origin"], "lntcase.Thrower");
    for (observed, actual) in [(left, before), (right, after)] {
        assert_eq!(observed["target_loaded_during_resource_read"], false);
        assert_eq!(observed["resource_sha256"], actual.to_string());
    }
}

#[test]
fn genuine_constants_opcodes_initializers_annotations_and_parameter_metadata_are_other_changes() {
    for bytes in [
        &include_bytes!(
            "../../../fixtures/native-lnt/variants/constant/classes/lntcase/Probe.class"
        )[..],
        &include_bytes!("../../../fixtures/native-lnt/variants/opcode/classes/lntcase/Probe.class")
            [..],
        &include_bytes!(
            "../../../fixtures/native-lnt/variants/initializer/classes/lntcase/Probe.class"
        )[..],
        &include_bytes!(
            "../../../fixtures/native-lnt/variants/annotation/classes/lntcase/Probe.class"
        )[..],
        &include_bytes!(
            "../../../fixtures/native-lnt/variants/method-parameters/classes/lntcase/Probe.class"
        )[..],
    ] {
        let mut left = Reader::new(BASE);
        skip_pool(&mut left).unwrap();
        let mut right = Reader::new(bytes);
        skip_pool(&mut right).unwrap();
        assert_eq!(
            &BASE[..left.at],
            &bytes[..right.at],
            "the genuine negative isolates non-CP bytes"
        );
        assert_eq!(compare(BASE, bytes).change, LntChange::OtherChange);
    }
}

fn class_attributes(bytes: &[u8]) -> usize {
    let mut r = Reader::new(bytes);
    skip_pool(&mut r).unwrap();
    r.take(6).unwrap();
    let interfaces = r.u2().unwrap() as usize;
    r.take(interfaces * 2).unwrap();
    for _ in 0..2 {
        for _ in 0..r.u2().unwrap() {
            r.take(6).unwrap();
            for _ in 0..r.u2().unwrap() {
                attribute(&mut r).unwrap();
            }
        }
    }
    r.at
}
fn opaque_attribute(bytes: &[u8], value: u8) -> Vec<u8> {
    let class = parse_class(bytes, Limits::default()).unwrap();
    let name = (1..u16::from_be_bytes(bytes[8..10].try_into().unwrap()))
        .find(|index| utf8(&class, *index).ok() == Some("value"))
        .unwrap();
    let at = class_attributes(bytes);
    let mut out = bytes.to_vec();
    let count = u16::from_be_bytes(out[at..at + 2].try_into().unwrap());
    out[at..at + 2].copy_from_slice(&(count + 1).to_be_bytes());
    out.extend_from_slice(&name.to_be_bytes());
    out.extend_from_slice(&1u32.to_be_bytes());
    out.push(value);
    out
}
#[test]
fn opaque_attributes_are_preserved_exactly_and_unrelated_constant_pool_growth_refuses_equivalence()
{
    let left = opaque_attribute(BASE, 7);
    let right = opaque_attribute(SHIFTED, 7);
    assert_eq!(
        compare(&left, &right).change,
        LntChange::LineNumberTablesOnly
    );
    assert_eq!(
        compare(&left, &opaque_attribute(SHIFTED, 8)).change,
        LntChange::OtherChange
    );
    let mut r = Reader::new(SHIFTED);
    skip_pool(&mut r).unwrap();
    let mut extra = SHIFTED[..r.at].to_vec();
    let count = u16::from_be_bytes(extra[8..10].try_into().unwrap());
    extra[8..10].copy_from_slice(&(count + 1).to_be_bytes());
    extra.extend_from_slice(&[1, 0, 6]);
    extra.extend_from_slice(b"unused");
    extra.extend_from_slice(&SHIFTED[r.at..]);
    assert_eq!(compare(BASE, &extra).change, LntChange::OtherChange);
}

#[test]
fn malformed_inputs_are_unavailable_even_when_other_bytes_also_differ() {
    for length in [0, 3, 9, 31, BASE.len() - 1] {
        assert!(matches!(
            compare(&BASE[..length], SHIFTED).change,
            LntChange::Unavailable(_)
        ));
    }
    let mut trailing = SHIFTED.to_vec();
    trailing.push(0);
    assert!(matches!(
        compare(BASE, &trailing).change,
        LntChange::Unavailable(_)
    ));
    let mut bad_magic = BASE.to_vec();
    bad_magic[0] = 0;
    assert!(matches!(
        compare(&bad_magic, SHIFTED).change,
        LntChange::Unavailable(_)
    ));
    let mut bad_attribute = opaque_attribute(SHIFTED, 1);
    let length = bad_attribute.len();
    bad_attribute[length - 5..length - 1].copy_from_slice(&2u32.to_be_bytes());
    assert!(matches!(
        compare(BASE, &bad_attribute).change,
        LntChange::Unavailable(_)
    ));
}

#[test]
fn every_budget_stop_is_unavailable_and_never_a_prefix_certificate() {
    for limits in [
        LntLimits {
            max_input_bytes: 0,
            ..Default::default()
        },
        LntLimits {
            max_scratch_bytes: 0,
            ..Default::default()
        },
        LntLimits {
            max_attributes: 0,
            ..Default::default()
        },
        LntLimits {
            max_line_entries: 0,
            ..Default::default()
        },
        LntLimits {
            max_instructions: 0,
            ..Default::default()
        },
    ] {
        let compared = compare_line_number_tables(BASE, SHIFTED, limits);
        assert!(
            matches!(
                compared.change,
                LntChange::Unavailable(LntUnavailable {
                    error: BinaryError {
                        kind: ErrorKind::ResourceLimit,
                        ..
                    },
                    ..
                })
            ),
            "{compared:?}"
        );
        assert!(!compared.omission_authority());
    }
}

fn first_line_table(bytes: &[u8]) -> (usize, usize, usize, usize) {
    let class = parse_class(bytes, Limits::default()).unwrap();
    let mut r = Reader::new(bytes);
    skip_pool(&mut r).unwrap();
    r.take(6).unwrap();
    let n = r.u2().unwrap() as usize;
    r.take(n * 2).unwrap();
    for _ in 0..r.u2().unwrap() {
        r.take(6).unwrap();
        for _ in 0..r.u2().unwrap() {
            attribute(&mut r).unwrap();
        }
    }
    for _ in 0..r.u2().unwrap() {
        r.take(6).unwrap();
        for _ in 0..r.u2().unwrap() {
            let outer = r.at;
            let attr = attribute(&mut r).unwrap();
            if utf8(&class, attr.name).unwrap() != "Code" {
                continue;
            }
            let base = attr.bytes.as_ptr() as usize - bytes.as_ptr() as usize;
            let mut code = Reader::new(attr.bytes);
            code.take(4).unwrap();
            let n = code.u4().unwrap() as usize;
            code.take(n).unwrap();
            let n = code.u2().unwrap() as usize;
            code.take(n * 8).unwrap();
            let count = base + code.at;
            for _ in 0..code.u2().unwrap() {
                let begin = base + code.at;
                let attr = attribute(&mut code).unwrap();
                if utf8(&class, attr.name).unwrap() == "LineNumberTable" {
                    return (outer, count, begin, base + code.at);
                }
            }
        }
    }
    panic!("genuine fixture has line tables")
}
#[test]
fn table_addition_removal_and_malformed_pc_or_count_have_distinct_results() {
    let (outer, count, start, end) = first_line_table(SHIFTED);
    let outer_length = u32::from_be_bytes(SHIFTED[outer + 2..outer + 6].try_into().unwrap());
    let attributes = u16::from_be_bytes(SHIFTED[count..count + 2].try_into().unwrap());
    let mut removed = SHIFTED.to_vec();
    removed[outer + 2..outer + 6]
        .copy_from_slice(&(outer_length - (end - start) as u32).to_be_bytes());
    removed[count..count + 2].copy_from_slice(&(attributes - 1).to_be_bytes());
    removed.drain(start..end);
    assert_eq!(
        compare(BASE, &removed).change,
        LntChange::LineNumberTablesOnly
    );
    let mut doubled = SHIFTED.to_vec();
    doubled[outer + 2..outer + 6]
        .copy_from_slice(&(outer_length + (end - start) as u32).to_be_bytes());
    doubled[count..count + 2].copy_from_slice(&(attributes + 1).to_be_bytes());
    doubled.splice(end..end, SHIFTED[start..end].iter().copied());
    assert_eq!(
        compare(BASE, &doubled).change,
        LntChange::LineNumberTablesOnly
    );
    let mut bad_pc = SHIFTED.to_vec();
    bad_pc[start + 8..start + 10].copy_from_slice(&2u16.to_be_bytes()); // inside invokespecial's operand
    assert!(matches!(
        compare(BASE, &bad_pc).change,
        LntChange::Unavailable(LntUnavailable {
            stage: LntStage::LineTable,
            ..
        })
    ));
    let mut bad_count = SHIFTED.to_vec();
    bad_count[start + 6..start + 8].copy_from_slice(&65535u16.to_be_bytes());
    assert!(matches!(
        compare(BASE, &bad_count).change,
        LntChange::Unavailable(_)
    ));
}

#[test]
fn malformed_instructions_and_declaration_flags_cannot_hide_behind_a_metadata_delta() {
    let class = parse_class(SHIFTED, Limits::default()).unwrap();
    let method = &class.methods[0];
    let at = method.code.unwrap().as_ptr() as usize - SHIFTED.as_ptr() as usize;
    let mut bad_code = SHIFTED.to_vec();
    bad_code[at] = 0xfe;
    assert!(matches!(
        compare(BASE, &bad_code).change,
        LntChange::Unavailable(LntUnavailable {
            stage: LntStage::Code,
            ..
        })
    ));
    let mut r = Reader::new(SHIFTED);
    skip_pool(&mut r).unwrap();
    let mut bad_flags = SHIFTED.to_vec();
    bad_flags[r.at] |= 0x04; // class abstract + final
    assert!(matches!(
        compare(BASE, &bad_flags).change,
        LntChange::Unavailable(_)
    ));
    let envelope =
        include_bytes!("../../../fixtures/native-envelope/classes/envelopecase/Probe.class");
    assert_eq!(
        compare(envelope, envelope).change,
        LntChange::Identical,
        "structural validity is independent of reflection/monitor/native effects, never omission authority"
    );
}

#[test]
fn diagnostic_leaf_is_outside_all_native_producer_dependency_closures() {
    use std::collections::{BTreeMap, BTreeSet};
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let output = std::process::Command::new(env!("CARGO"))
        .args(["metadata", "--format-version", "1", "--locked", "--offline"])
        .current_dir(root)
        .output()
        .expect("locked offline Cargo graph");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let metadata: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    let packages = metadata["packages"].as_array().unwrap();
    let id = |name: &str| {
        packages.iter().find(|p| p["name"] == name).unwrap()["id"]
            .as_str()
            .unwrap()
    };
    let leaf = id("selector-class-diff");
    let nodes: BTreeMap<_, _> = metadata["resolve"]["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .map(|node| (node["id"].as_str().unwrap(), node))
        .collect();
    // These roots include every explicit extension in selector-cli/build.rs:
    // metadata also imports CLI/extract; query also imports graph-build.
    for package in [
        "selector-extract",
        "selector-models",
        "selector-graph-build",
        "selector-plan",
        "selector-select",
        "selector-report",
        "selector-solve",
        "selector-cli",
    ] {
        let mut pending = vec![id(package)];
        let mut closure = BTreeSet::new();
        while let Some(current) = pending.pop() {
            if !closure.insert(current) {
                continue;
            }
            for dependency in nodes[current]["deps"].as_array().unwrap() {
                if dependency["dep_kinds"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|kind| kind["kind"].is_null() || kind["kind"] == "build")
                {
                    pending.push(dependency["pkg"].as_str().unwrap());
                }
            }
        }
        assert!(
            !closure.contains(leaf),
            "diagnostic checker entered {package} producer closure"
        );
    }
}
