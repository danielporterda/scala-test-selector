//! Exact Java21 primitive-data contracts, after normal declared-platform admission.
//!
//! These methods cannot call application code through primitive array elements.
//! Primitive-array and numeric-formatting results are TOP: no EMPTY result or
//! invented allocation. Bounds helpers retain their normal scalar/void returns.
//! These are trusted functional contracts, not assertions of exception-free code.
//! Consumers MUST emit each `primitive_read_arguments` entry as a trusted
//! ReadElements dependency and retain the listed class-initialization phases.
//! Caller exception-handler recipes remain executable. These contracts do not
//! admit caller-array writers, reference arrays, reflection or arbitrary natives.
use crate::binary::{BinaryValueId, ClassFile, Limits, MethodInfo, MethodSummary, Value};
use selector_types::ContentHash;
use sha2::{Digest, Sha256};

pub const VERSION: &str =
    "declared-java21-primitive-data/v2:static-formatting-bounds:input-heap-reads:top-reference-result:explicit-init:no-caller-writes";
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Kind {
    Utf16Length,
    Utf16Char,
    Utf16Compress,
    ByteRangeCopy,
    IntegerDecimal,
    IntegerRadix,
    LongDecimal,
    LongRadix,
    BoundsBeginEnd,
    BoundsOffCount,
}
pub struct Model<'a> {
    pub kind: Kind,
    pub summary: MethodSummary<'a>,
    /// Owner initialization is already preserved by ordinary native entry.
    pub additional_initialization_owners: &'static [&'static str],
    /// Required heap-input dependencies, even though values remain unknown.
    pub primitive_read_arguments: &'static [u16],
    /// Allocation identity and byte contents are deliberately not fabricated.
    pub fresh_primitive_array_result: bool,
}
#[derive(Clone, Copy)]
enum Return {
    UnknownData,
    Argument(u16),
    Void,
}
struct Spec {
    owner: &'static str,
    name: &'static str,
    descriptor: &'static str,
    class_hash: ContentHash,
    code_hash: ContentHash,
    code_len: usize,
    flags: u16,
    kind: Kind,
    initializers: &'static [&'static str],
    primitive_reads: &'static [u16],
    returned: Return,
}
const SPECS: &[Spec] = &[
    Spec {
        owner: "java/lang/StringUTF16",
        name: "getChar",
        descriptor: "([BI)C",
        class_hash: ContentHash([
            0xe0, 0x3e, 0x9a, 0x01, 0x2b, 0x6c, 0x29, 0xde, 0x21, 0x30, 0xef, 0x49, 0xba, 0xda,
            0xb7, 0x7d, 0x42, 0x1f, 0x52, 0x72, 0xe1, 0xc7, 0x22, 0x24, 0x83, 0x85, 0x45, 0xe1,
            0x09, 0x14, 0x88, 0xb5,
        ]),
        code_hash: ContentHash([
            0x54, 0x8e, 0x34, 0x01, 0x88, 0x78, 0x52, 0x93, 0xe5, 0x7a, 0xde, 0x0b, 0x59, 0xd0,
            0x13, 0x66, 0x09, 0x7d, 0xdb, 0x10, 0x71, 0x6b, 0x9e, 0xc5, 0xb0, 0x46, 0x19, 0x7c,
            0x91, 0x1c, 0x21, 0x14,
        ]),
        code_len: 60,
        flags: 8,
        kind: Kind::Utf16Char,
        initializers: &["java/lang/AssertionError"],
        primitive_reads: &[0],
        returned: Return::UnknownData,
    },
    Spec {
        owner: "java/lang/StringUTF16",
        name: "length",
        descriptor: "([B)I",
        class_hash: ContentHash([
            0xe0, 0x3e, 0x9a, 0x01, 0x2b, 0x6c, 0x29, 0xde, 0x21, 0x30, 0xef, 0x49, 0xba, 0xda,
            0xb7, 0x7d, 0x42, 0x1f, 0x52, 0x72, 0xe1, 0xc7, 0x22, 0x24, 0x83, 0x85, 0x45, 0xe1,
            0x09, 0x14, 0x88, 0xb5,
        ]),
        code_hash: ContentHash([
            0x49, 0x1b, 0xf1, 0x22, 0x6c, 0xdd, 0x83, 0x29, 0x85, 0xf0, 0x87, 0x73, 0x46, 0x61,
            0xdc, 0x59, 0x5d, 0x23, 0x25, 0x7f, 0x68, 0xd0, 0xa7, 0x42, 0xa2, 0xad, 0xbe, 0x4b,
            0x6c, 0x88, 0x69, 0x1e,
        ]),
        code_len: 5,
        flags: 9,
        kind: Kind::Utf16Length,
        initializers: &[],
        primitive_reads: &[0],
        returned: Return::UnknownData,
    },
    Spec {
        owner: "java/lang/StringUTF16",
        name: "compress",
        descriptor: "([BII)[B",
        class_hash: ContentHash([
            0xe0, 0x3e, 0x9a, 0x01, 0x2b, 0x6c, 0x29, 0xde, 0x21, 0x30, 0xef, 0x49, 0xba, 0xda,
            0xb7, 0x7d, 0x42, 0x1f, 0x52, 0x72, 0xe1, 0xc7, 0x22, 0x24, 0x83, 0x85, 0x45, 0xe1,
            0x09, 0x14, 0x88, 0xb5,
        ]),
        code_hash: ContentHash([
            0x39, 0xa9, 0x8a, 0x1f, 0xeb, 0x00, 0x1a, 0xf3, 0x67, 0xc4, 0xc1, 0x5e, 0xb7, 0xd2,
            0xf6, 0xb7, 0x4b, 0x75, 0x9c, 0x89, 0x01, 0x15, 0xbb, 0x61, 0xf7, 0xc7, 0x79, 0x78,
            0xf5, 0x2a, 0x90, 0xef,
        ]),
        code_len: 66,
        flags: 9,
        kind: Kind::Utf16Compress,
        initializers: &["java/util/Arrays"],
        primitive_reads: &[0],
        returned: Return::UnknownData,
    },
    Spec {
        owner: "java/util/Arrays",
        name: "copyOfRange",
        descriptor: "([BII)[B",
        class_hash: ContentHash([
            0x4a, 0x41, 0xd8, 0x9c, 0xb7, 0x92, 0x84, 0x29, 0x8b, 0x95, 0x30, 0x3a, 0x66, 0xb3,
            0x73, 0x89, 0x55, 0xd2, 0x26, 0x94, 0xf9, 0xb3, 0x40, 0x16, 0xd8, 0x72, 0x41, 0xd9,
            0xae, 0x81, 0x93, 0xab,
        ]),
        code_hash: ContentHash([
            0xfc, 0x4b, 0x90, 0xf5, 0x6d, 0xf6, 0x87, 0xc5, 0x34, 0xa2, 0x2d, 0x83, 0x53, 0x7b,
            0x00, 0x97, 0x02, 0xea, 0x52, 0x4b, 0x1f, 0xf4, 0xc0, 0x24, 0x01, 0x21, 0x23, 0x45,
            0x76, 0x46, 0xa3, 0x22,
        ]),
        code_len: 25,
        flags: 9,
        kind: Kind::ByteRangeCopy,
        initializers: &[],
        primitive_reads: &[0],
        returned: Return::UnknownData,
    },
    Spec {
        owner: "java/lang/Integer",
        name: "toString",
        descriptor: "(I)Ljava/lang/String;",
        class_hash: ContentHash([
            0x44, 0xbc, 0x6d, 0x0e, 0x77, 0xa7, 0xf4, 0x96, 0x5c, 0x2f, 0xa6, 0xbc, 0xec, 0xc9,
            0xaf, 0x63, 0xb8, 0x41, 0xef, 0x94, 0xea, 0xce, 0x39, 0x8f, 0xcb, 0xc1, 0xf9, 0x54,
            0xc3, 0x83, 0x51, 0x79,
        ]),
        code_hash: ContentHash([
            0x52, 0x11, 0x28, 0x05, 0xc5, 0xd6, 0xa1, 0xa0, 0xef, 0x34, 0x91, 0x00, 0xc8, 0x78,
            0xb4, 0xcb, 0x31, 0xf3, 0xb4, 0x40, 0x76, 0x21, 0x87, 0xb2, 0x13, 0x33, 0xbe, 0xf8,
            0x8f, 0x7f, 0x7d, 0x3e,
        ]),
        code_len: 55,
        flags: 9,
        kind: Kind::IntegerDecimal,
        initializers: &["java/lang/String", "java/lang/StringUTF16"],
        primitive_reads: &[],
        returned: Return::UnknownData,
    },
    Spec {
        owner: "java/lang/Integer",
        name: "toString",
        descriptor: "(II)Ljava/lang/String;",
        class_hash: ContentHash([
            0x44, 0xbc, 0x6d, 0x0e, 0x77, 0xa7, 0xf4, 0x96, 0x5c, 0x2f, 0xa6, 0xbc, 0xec, 0xc9,
            0xaf, 0x63, 0xb8, 0x41, 0xef, 0x94, 0xea, 0xce, 0x39, 0x8f, 0xcb, 0xc1, 0xf9, 0x54,
            0xc3, 0x83, 0x51, 0x79,
        ]),
        code_hash: ContentHash([
            0x6f, 0x56, 0xdd, 0xc2, 0x12, 0xef, 0x1d, 0x1a, 0xc6, 0x77, 0x86, 0x80, 0x62, 0xfb,
            0xc7, 0xb5, 0xb5, 0xe1, 0x89, 0x6b, 0x12, 0x0e, 0x8d, 0xea, 0x74, 0x5a, 0x65, 0x31,
            0xdd, 0xbc, 0xe9, 0x9a,
        ]),
        code_len: 128,
        flags: 9,
        kind: Kind::IntegerRadix,
        initializers: &[
            "java/lang/String",
            "java/lang/StringLatin1",
            "java/lang/StringUTF16",
        ],
        primitive_reads: &[],
        returned: Return::UnknownData,
    },
    Spec {
        owner: "java/lang/Long",
        name: "toString",
        descriptor: "(J)Ljava/lang/String;",
        class_hash: ContentHash([
            0xcc, 0x18, 0xd5, 0x1e, 0xf0, 0xf7, 0x49, 0x06, 0xc2, 0xc8, 0x71, 0x48, 0x49, 0xff,
            0x77, 0x8f, 0x7e, 0x01, 0xa4, 0xa2, 0x95, 0x39, 0xba, 0x88, 0x17, 0xfa, 0xed, 0xb9,
            0x89, 0xa5, 0x0f, 0x29,
        ]),
        code_hash: ContentHash([
            0x44, 0x7f, 0x3f, 0xc9, 0xeb, 0xd7, 0x17, 0x69, 0xbd, 0x63, 0xcf, 0xf8, 0xee, 0x9a,
            0x30, 0x92, 0xd3, 0xc9, 0x6f, 0x56, 0x58, 0xe8, 0xc5, 0x08, 0xc4, 0xf0, 0xac, 0x20,
            0x62, 0x3b, 0xd8, 0x86,
        ]),
        code_len: 55,
        flags: 9,
        kind: Kind::LongDecimal,
        initializers: &["java/lang/String", "java/lang/StringUTF16"],
        primitive_reads: &[],
        returned: Return::UnknownData,
    },
    Spec {
        owner: "java/lang/Long",
        name: "toString",
        descriptor: "(JI)Ljava/lang/String;",
        class_hash: ContentHash([
            0xcc, 0x18, 0xd5, 0x1e, 0xf0, 0xf7, 0x49, 0x06, 0xc2, 0xc8, 0x71, 0x48, 0x49, 0xff,
            0x77, 0x8f, 0x7e, 0x01, 0xa4, 0xa2, 0x95, 0x39, 0xba, 0x88, 0x17, 0xfa, 0xed, 0xb9,
            0x89, 0xa5, 0x0f, 0x29,
        ]),
        code_hash: ContentHash([
            0x66, 0x62, 0x85, 0x91, 0x38, 0x7e, 0xa5, 0x0c, 0x0a, 0x2f, 0xb5, 0x35, 0x5e, 0x49,
            0x9a, 0x3b, 0xb4, 0x77, 0xed, 0x3a, 0x84, 0x82, 0x1f, 0x68, 0x3c, 0x2f, 0x50, 0x73,
            0x5d, 0xde, 0x40, 0xdb,
        ]),
        code_len: 139,
        flags: 9,
        kind: Kind::LongRadix,
        initializers: &[
            "java/lang/Integer",
            "java/lang/String",
            "java/lang/StringLatin1",
            "java/lang/StringUTF16",
        ],
        primitive_reads: &[],
        returned: Return::UnknownData,
    },
    Spec {
        owner: "java/lang/String",
        name: "checkBoundsOffCount",
        descriptor: "(III)I",
        class_hash: ContentHash([
            0x83, 0x1a, 0x11, 0xd5, 0xc7, 0x6c, 0x84, 0xb8, 0x77, 0x7a, 0x78, 0x13, 0x44, 0x0b,
            0x45, 0x70, 0xd4, 0x99, 0x34, 0xde, 0xe0, 0x5c, 0x28, 0x5c, 0x90, 0x68, 0xa0, 0xec,
            0x43, 0x15, 0x84, 0x12,
        ]),
        code_hash: ContentHash([
            0x7c, 0x62, 0xa2, 0x50, 0xbb, 0xcf, 0x8b, 0x1e, 0x9b, 0x19, 0x6e, 0xb6, 0xa3, 0x09,
            0x53, 0x15, 0x4d, 0x60, 0xfa, 0xbe, 0x8b, 0x0a, 0x00, 0xa8, 0x44, 0xcd, 0x12, 0x80,
            0x07, 0x96, 0x38, 0x99,
        ]),
        code_len: 10,
        flags: 8,
        kind: Kind::BoundsOffCount,
        initializers: &[
            "jdk/internal/util/Preconditions",
            "java/lang/StringIndexOutOfBoundsException",
        ],
        primitive_reads: &[],
        returned: Return::Argument(0),
    },
    Spec {
        owner: "java/lang/String",
        name: "checkBoundsBeginEnd",
        descriptor: "(III)V",
        class_hash: ContentHash([
            0x83, 0x1a, 0x11, 0xd5, 0xc7, 0x6c, 0x84, 0xb8, 0x77, 0x7a, 0x78, 0x13, 0x44, 0x0b,
            0x45, 0x70, 0xd4, 0x99, 0x34, 0xde, 0xe0, 0x5c, 0x28, 0x5c, 0x90, 0x68, 0xa0, 0xec,
            0x43, 0x15, 0x84, 0x12,
        ]),
        code_hash: ContentHash([
            0xb9, 0x40, 0x45, 0x87, 0x6c, 0xfe, 0x59, 0x25, 0x36, 0x89, 0x17, 0x01, 0xed, 0x24,
            0x19, 0x1b, 0x38, 0xa5, 0x37, 0xf2, 0x1a, 0xd7, 0xc9, 0xd4, 0x67, 0x7a, 0xae, 0x91,
            0xba, 0x41, 0xae, 0xf6,
        ]),
        code_len: 11,
        flags: 8,
        kind: Kind::BoundsBeginEnd,
        initializers: &[
            "jdk/internal/util/Preconditions",
            "java/lang/StringIndexOutOfBoundsException",
        ],
        primitive_reads: &[],
        returned: Return::Void,
    },
];

/// Census only: matching an API family never supplies model authority.
pub fn candidate(owner: &str, name: &str, descriptor: &str) -> bool {
    SPECS
        .iter()
        .any(|spec| spec.owner == owner && spec.name == name && spec.descriptor == descriptor)
}

/// `class_hash` must come from the existing hash-verified, context-qualified
/// first provider in declared java.base, not an arbitrary classpath or caller
/// assertion. This function adds exact owner/ABI/class/Code guards; it does not
/// replace provider admission. Unsupported shapes and budgets use the ordinary
/// native summary, retaining its open boundaries.
pub fn model<'a>(
    class: &ClassFile<'a>,
    method: &MethodInfo<'a>,
    class_hash: ContentHash,
    limits: Limits,
) -> Option<Model<'a>> {
    let spec = SPECS.iter().find(|spec| {
        class.name == spec.owner
            && method.name == spec.name
            && method.descriptor == spec.descriptor
            && class_hash == spec.class_hash
    })?;
    let code = method.code?;
    if class.major != 65
        || method.flags != spec.flags
        || method.exception_handlers != 0
        || !method.exception_table.is_empty()
        || code.len() != spec.code_len
        || ContentHash(Sha256::digest(code).into()) != spec.code_hash
        || code.len() > limits.max_code_bytes
        || limits.max_steps < code.len()
        || method.max_stack as usize > limits.max_stack
        || method.max_locals as usize > limits.max_locals
    {
        return None;
    }
    let descriptor = crate::binary::method_descriptor(method.descriptor).ok()?;
    let count = descriptor.parameter_count;
    let extra = usize::from(!matches!(spec.returned, Return::Argument(_)));
    let value_count = count.checked_add(extra)?;
    if value_count > limits.max_values {
        return None;
    }
    let mut values = Vec::with_capacity(value_count);
    let mut value_offsets = Vec::with_capacity(value_count);
    for index in 0..count {
        values.push(Value::Argument(u16::try_from(index).ok()?));
        value_offsets.push(0);
    }
    let result = match spec.returned {
        Return::Argument(index) => {
            if usize::from(index) >= count {
                return None;
            }
            BinaryValueId(u32::from(index))
        }
        returned => {
            let result = BinaryValueId(u32::try_from(values.len()).ok()?);
            values.push(match returned {
                Return::UnknownData => Value::UnknownData,
                Return::Void => Value::Void,
                Return::Argument(_) => unreachable!(),
            });
            value_offsets.push(u32::try_from(code.len()).ok()?);
            result
        }
    };
    Some(Model {
        kind: spec.kind,
        summary: MethodSummary {
            descriptor: method.descriptor,
            values,
            value_offsets,
            calls: Vec::new(),
            arguments: Vec::new(),
            field_writes: Vec::new(),
            lambdas: Vec::new(),
            unknown_offsets: Vec::new(),
            returned: Some(result),
            unknown: None,
            envelope: None,
        },
        additional_initialization_owners: spec.initializers,
        primitive_read_arguments: spec.primitive_reads,
        fresh_primitive_array_result: matches!(
            spec.kind,
            Kind::Utf16Compress | Kind::ByteRangeCopy
        ),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    const UTF16: &[u8] =
        include_bytes!("../../../fixtures/jdk-primitive-models/java/lang/StringUTF16.class");
    const ARRAYS: &[u8] =
        include_bytes!("../../../fixtures/jdk-primitive-models/java/util/Arrays.class");
    const INTEGER: &[u8] =
        include_bytes!("../../../fixtures/jdk-primitive-models/java/lang/Integer.class");
    const LONG: &[u8] =
        include_bytes!("../../../fixtures/jdk-primitive-models/java/lang/Long.class");
    const STRING: &[u8] =
        include_bytes!("../../../fixtures/jdk-primitive-models/java/lang/String.class");
    fn hash(bytes: &[u8]) -> ContentHash {
        ContentHash(Sha256::digest(bytes).into())
    }
    #[test]
    fn genuine_exact_java21_leaves_keep_primitive_heap_inputs_and_unknown_results() {
        for bytes in [UTF16, ARRAYS] {
            let class = crate::binary::parse_class(bytes, Limits::default()).unwrap();
            for spec in SPECS.iter().filter(|spec| spec.owner == class.name) {
                let method = class.method(spec.name, Some(spec.descriptor)).unwrap();
                let modeled = model(&class, method, hash(bytes), Limits::default()).unwrap();
                assert_eq!(modeled.kind, spec.kind);
                assert_eq!(modeled.primitive_read_arguments, &[0]);
                assert!(modeled.summary.complete());
                assert_eq!(
                    modeled.summary.values[modeled.summary.returned.unwrap().0 as usize],
                    Value::UnknownData
                );
                assert!(!modeled.summary.values.iter().any(|value| matches!(
                    value,
                    Value::Constant { .. }
                        | Value::Void
                        | Value::Allocation { .. }
                        | Value::MayAllocation { .. }
                )));
                assert!(
                    modeled.summary.field_writes.is_empty() && modeled.summary.lambdas.is_empty()
                );
                assert_eq!(
                    modeled.fresh_primitive_array_result,
                    matches!(spec.kind, Kind::Utf16Compress | Kind::ByteRangeCopy)
                );
            }
        }
    }
    #[test]
    fn genuine_static_numeric_formatters_keep_top_reference_results_and_initialization() {
        for bytes in [INTEGER, LONG] {
            let class = crate::binary::parse_class(bytes, Limits::default()).unwrap();
            let specs: Vec<_> = SPECS
                .iter()
                .filter(|spec| spec.owner == class.name)
                .collect();
            assert_eq!(specs.len(), 2);
            for spec in specs {
                let method = class.method(spec.name, Some(spec.descriptor)).unwrap();
                let modeled = model(&class, method, hash(bytes), Limits::default()).unwrap();
                let summary = &modeled.summary;
                assert!(summary.complete());
                assert_eq!(
                    summary.values[summary.returned.unwrap().0 as usize],
                    Value::UnknownData
                );
                assert!(modeled.primitive_read_arguments.is_empty());
                assert!(!modeled.fresh_primitive_array_result);
                assert!(summary.calls.is_empty() && summary.field_writes.is_empty());
                assert!(!summary.values.iter().any(|value| matches!(
                    value,
                    Value::Void
                        | Value::Null
                        | Value::Receiver
                        | Value::Allocation { .. }
                        | Value::MayAllocation { .. }
                        | Value::Lambda(_)
                )));
                assert!(modeled
                    .additional_initialization_owners
                    .contains(&"java/lang/String"));
                assert!(modeled
                    .additional_initialization_owners
                    .contains(&"java/lang/StringUTF16"));
                if matches!(modeled.kind, Kind::IntegerRadix | Kind::LongRadix) {
                    assert!(modeled
                        .additional_initialization_owners
                        .contains(&"java/lang/StringLatin1"));
                }
                if modeled.kind == Kind::LongRadix {
                    assert!(modeled
                        .additional_initialization_owners
                        .contains(&"java/lang/Integer"));
                }
            }
        }
    }

    #[test]
    fn genuine_bounds_contracts_keep_normal_return_alias_and_exception_initializers() {
        let class = crate::binary::parse_class(STRING, Limits::default()).unwrap();
        for (name, desc, result, count) in [
            ("checkBoundsOffCount", "(III)I", Value::Argument(0), 3),
            ("checkBoundsBeginEnd", "(III)V", Value::Void, 4),
        ] {
            let method = class.method(name, Some(desc)).unwrap();
            let limits = Limits {
                max_values: count,
                ..Default::default()
            };
            let modeled = model(&class, method, hash(STRING), limits).unwrap();
            assert_eq!(modeled.summary.values.len(), count);
            assert_eq!(
                modeled.summary.values[modeled.summary.returned.unwrap().0 as usize],
                result
            );
            assert!(modeled.summary.complete());
            assert!(modeled.primitive_read_arguments.is_empty());
            assert_eq!(
                modeled.additional_initialization_owners,
                &[
                    "jdk/internal/util/Preconditions",
                    "java/lang/StringIndexOutOfBoundsException"
                ]
            );
            assert!(model(
                &class,
                method,
                hash(STRING),
                Limits {
                    max_values: count - 1,
                    ..Default::default()
                }
            )
            .is_none());
        }
    }

    #[test]
    fn static_contracts_do_not_admit_receiver_writers_reference_callbacks_or_changed_code() {
        for bytes in [INTEGER, LONG, STRING] {
            let class = crate::binary::parse_class(bytes, Limits::default()).unwrap();
            for spec in SPECS.iter().filter(|spec| spec.owner == class.name) {
                let method = *class.method(spec.name, Some(spec.descriptor)).unwrap();
                let mut changed_code = method.code.unwrap().to_vec();
                changed_code[0] ^= 1; // synthetic mutation, never labeled compiler output
                for changed in [
                    MethodInfo {
                        code: Some(&changed_code),
                        ..method
                    },
                    MethodInfo {
                        flags: method.flags & !8,
                        ..method
                    },
                    MethodInfo {
                        exception_handlers: 1,
                        ..method
                    },
                    MethodInfo {
                        descriptor: "()Ljava/lang/String;",
                        ..method
                    },
                ] {
                    assert!(model(&class, &changed, hash(bytes), Limits::default()).is_none());
                }
                assert!(
                    model(&class, &method, ContentHash::default(), Limits::default()).is_none()
                );
                for limits in [
                    Limits {
                        max_values: 0,
                        ..Default::default()
                    },
                    Limits {
                        max_steps: 0,
                        ..Default::default()
                    },
                    Limits {
                        max_code_bytes: 0,
                        ..Default::default()
                    },
                ] {
                    assert!(model(&class, &method, hash(bytes), limits).is_none());
                }
            }
            if class.name != "java/lang/String" {
                let instance = class
                    .method("toString", Some("()Ljava/lang/String;"))
                    .unwrap();
                assert!(model(&class, instance, hash(bytes), Limits::default()).is_none());
            }
        }
        let string = crate::binary::parse_class(STRING, Limits::default()).unwrap();
        for (name, desc) in [
            ("valueOf", "(Ljava/lang/Object;)Ljava/lang/String;"),
            ("hashCode", "()I"),
            ("length", "()I"),
            ("getChars", "(II[CI)V"),
        ] {
            let method = string.method(name, Some(desc)).unwrap();
            assert!(!candidate(string.name, name, desc));
            assert!(model(&string, method, hash(STRING), Limits::default()).is_none());
        }
        assert!(!candidate(
            "java/lang/AbstractStringBuilder",
            "append",
            "(I)Ljava/lang/AbstractStringBuilder;"
        ));
        assert!(!candidate("java/lang/StringUTF16", "getChars", "(III[B)I"));
    }

    #[test]
    fn direct_implementation_initializers_remain_explicit_model_dependencies() {
        let class = crate::binary::parse_class(UTF16, Limits::default()).unwrap();
        for (name, desc, initializers) in [
            ("compress", "([BII)[B", &["java/util/Arrays"][..]),
            ("getChar", "([BI)C", &["java/lang/AssertionError"][..]),
            ("length", "([B)I", &[][..]),
        ] {
            let modeled = model(
                &class,
                class.method(name, Some(desc)).unwrap(),
                hash(UTF16),
                Limits::default(),
            )
            .unwrap();
            assert_eq!(modeled.additional_initialization_owners, initializers);
        }
    }
    #[test]
    fn mutating_and_reference_array_overloads_and_unknown_providers_stay_unsupported() {
        let class = crate::binary::parse_class(UTF16, Limits::default()).unwrap();
        let method = class.method("compress", Some("([BI[BII)I")).unwrap();
        assert!(model(&class, method, hash(UTF16), Limits::default()).is_none());
        let arrays = crate::binary::parse_class(ARRAYS, Limits::default()).unwrap();
        let method = arrays
            .method(
                "copyOfRange",
                Some("([Ljava/lang/Object;II)[Ljava/lang/Object;"),
            )
            .unwrap();
        assert!(model(&arrays, method, hash(ARRAYS), Limits::default()).is_none());
        let method = class.method("length", Some("([B)I")).unwrap();
        assert!(model(&class, method, ContentHash::default(), Limits::default()).is_none());
        let mut wrong = hash(UTF16);
        wrong.0[0] ^= 1;
        assert!(model(&class, method, wrong, Limits::default()).is_none());
    }
    #[test]
    fn synthetic_code_flags_handlers_and_budget_mutations_cannot_inherit_trusted_authority() {
        let class = crate::binary::parse_class(UTF16, Limits::default()).unwrap();
        let original = *class.method("length", Some("([B)I")).unwrap();
        let code = [3, 172]; // synthetic constant result, not a compiler artifact
        for changed in [
            MethodInfo {
                code: Some(&code),
                ..original
            },
            MethodInfo {
                flags: original.flags | 0x100,
                ..original
            },
            MethodInfo {
                exception_handlers: 1,
                ..original
            },
            MethodInfo {
                descriptor: "()I",
                ..original
            },
        ] {
            assert!(model(&class, &changed, hash(UTF16), Limits::default()).is_none());
        }
        for limits in [
            Limits {
                max_values: 0,
                ..Default::default()
            },
            Limits {
                max_code_bytes: 0,
                ..Default::default()
            },
            Limits {
                max_steps: 0,
                ..Default::default()
            },
        ] {
            assert!(model(&class, &original, hash(UTF16), limits).is_none());
        }
    }
}
