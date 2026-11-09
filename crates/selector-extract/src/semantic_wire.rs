//! Pure bounded SemanticDB 4.15.2 wire validation and borrowing serialization.
//! Shared by source capture and selected external metadata admission.
use selector_types::Error;
use serde::ser::{SerializeMap, SerializeSeq};
use serde::{Serialize, Serializer};

#[derive(Clone, Copy)]
pub(crate) struct Limits {
    pub(crate) max_depth: usize,
    pub(crate) max_fields: u64,
}

#[derive(Clone, Copy)]
enum FieldKind {
    Integer,
    Text,
    Opaque,
    Message(&'static str),
}
#[derive(Clone, Copy)]
struct Field {
    number: u32,
    name: &'static str,
    kind: FieldKind,
    repeated: bool,
}
#[derive(Clone, Copy)]
pub(crate) enum Value<'a> {
    Integer(u64),
    Bytes(&'a [u8]),
    Fixed(&'a [u8]),
}
#[derive(Clone, Copy)]
pub(crate) struct WireField<'a> {
    pub(crate) number: u32,
    pub(crate) value: Value<'a>,
}
impl<'a> WireField<'a> {
    pub(crate) fn bytes(self) -> Result<&'a [u8], Error> {
        match self.value {
            Value::Bytes(bytes) => Ok(bytes),
            _ => Err(Error::Invalid("length-delimited protobuf wire type")),
        }
    }
}
pub(crate) struct Wire<'a> {
    bytes: &'a [u8],
    offset: usize,
    failed: bool,
}
impl<'a> Wire<'a> {
    pub(crate) fn new(bytes: &'a [u8]) -> Self {
        Self {
            bytes,
            offset: 0,
            failed: false,
        }
    }
}
fn varint(bytes: &[u8], offset: &mut usize) -> Result<u64, Error> {
    let mut result = 0;
    for shift in (0..70).step_by(7) {
        let byte = *bytes
            .get(*offset)
            .ok_or(Error::Invalid("truncated protobuf varint"))?;
        *offset += 1;
        if shift == 63 && byte > 1 {
            return Err(Error::Invalid("overflowing protobuf varint"));
        }
        result |= u64::from(byte & 127) << shift;
        if byte < 128 {
            return Ok(result);
        }
    }
    Err(Error::Invalid("overflowing protobuf varint"))
}
impl<'a> Iterator for Wire<'a> {
    type Item = Result<WireField<'a>, Error>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.offset == self.bytes.len() || self.failed {
            return None;
        }
        let value = (|| {
            let tag = varint(self.bytes, &mut self.offset)?;
            let number = tag >> 3;
            if number == 0 || number >= (1 << 29) {
                return Err(Error::Invalid("protobuf field number"));
            }
            let wire = tag & 7;
            let value = match wire {
                0 => Value::Integer(varint(self.bytes, &mut self.offset)?),
                1 | 2 | 5 => {
                    let length = if wire == 1 {
                        8
                    } else if wire == 5 {
                        4
                    } else {
                        usize::try_from(varint(self.bytes, &mut self.offset)?)
                            .map_err(|_| Error::Limit("protobuf byte length"))?
                    };
                    let end = self
                        .offset
                        .checked_add(length)
                        .ok_or(Error::Invalid("protobuf length overflow"))?;
                    let bytes = self
                        .bytes
                        .get(self.offset..end)
                        .ok_or(Error::Invalid("truncated protobuf bytes"))?;
                    self.offset = end;
                    if wire == 2 {
                        Value::Bytes(bytes)
                    } else {
                        Value::Fixed(bytes)
                    }
                }
                _ => return Err(Error::Invalid("unsupported protobuf wire type")),
            };
            Ok(WireField {
                number: number as u32,
                value,
            })
        })();
        if value.is_err() {
            self.failed = true;
        }
        Some(value)
    }
}
fn int32(value: u64) -> Result<i32, Error> {
    if value <= u32::MAX as u64 {
        Ok(value as u32 as i32)
    } else if value >= u64::MAX - i32::MAX as u64 {
        Ok(value as i64 as i32)
    } else {
        Err(Error::Invalid("lossy protobuf int32 coordinate"))
    }
}
pub(crate) fn text_field(bytes: &[u8], number: u32) -> Result<Option<&str>, Error> {
    let mut result = None;
    for field in Wire::new(bytes) {
        let field = field?;
        if field.number == number {
            result = Some(
                std::str::from_utf8(field.bytes()?)
                    .map_err(|_| Error::Invalid("protobuf UTF-8"))?,
            );
        }
    }
    Ok(result)
}
pub(crate) fn validate(
    name: &str,
    bytes: &[u8],
    options: &Limits,
    depth: usize,
    total: &mut u64,
) -> Result<(), Error> {
    if depth > options.max_depth {
        return Err(Error::Limit("SemanticDB message depth"));
    }
    if name == "Constant" {
        return validate_constant(bytes);
    }
    let fields = schema(name).ok_or(Error::Invalid("SemanticDB message schema"))?;
    let mut range_seen = 0u8;
    let mut singular_ranges = 0u32;
    for wire in Wire::new(bytes) {
        let wire = wire?;
        *total = total
            .checked_add(1)
            .ok_or(Error::Limit("SemanticDB field count"))?;
        if *total > options.max_fields {
            return Err(Error::Limit("SemanticDB field count"));
        }
        let field = fields
            .iter()
            .find(|field| field.number == wire.number)
            .ok_or_else(|| {
                Error::Message(format!(
                    "unsupported SemanticDB field {name}.{}",
                    wire.number
                ))
            })?;
        match field.kind {
            FieldKind::Integer => {
                let Value::Integer(value) = wire.value else {
                    return Err(Error::Invalid("protobuf integer wire type"));
                };
                if name == "Range" {
                    int32(value)?;
                    let bit = 1u8 << wire.number;
                    if range_seen & bit != 0 {
                        return Err(Error::Invalid("repeated protobuf Range coordinate"));
                    }
                    range_seen |= bit;
                }
            }
            FieldKind::Text => {
                std::str::from_utf8(wire.bytes()?).map_err(|_| Error::Invalid("protobuf UTF-8"))?;
            }
            FieldKind::Opaque => {
                wire.bytes()?;
            }
            FieldKind::Message(child) => {
                if child == "Range" && !field.repeated {
                    let bit = 1u32 << field.number;
                    if singular_ranges & bit != 0 {
                        return Err(Error::Invalid("repeated singular protobuf Range"));
                    }
                    singular_ranges |= bit;
                }
                validate(child, wire.bytes()?, options, depth + 1, total)?;
            }
        }
    }
    Ok(())
}
pub(crate) struct Message<'a> {
    pub(crate) name: &'static str,
    pub(crate) bytes: &'a [u8],
}
struct Scalar<'a> {
    kind: FieldKind,
    value: Value<'a>,
    coordinate: bool,
}
struct Repeated<'a> {
    field: Field,
    bytes: &'a [u8],
}
impl Serialize for Message<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        if self.name == "Constant" {
            return Constant(self.bytes).serialize(serializer);
        }
        let fields = schema(self.name)
            .ok_or_else(|| serde::ser::Error::custom("unknown SemanticDB message"))?;
        let mut map = serializer.serialize_map(None)?;
        for field in fields {
            let mut last = None;
            for wire in Wire::new(self.bytes) {
                let wire = wire.map_err(serde::ser::Error::custom)?;
                if wire.number == field.number {
                    last = Some(wire);
                }
            }
            if field.repeated {
                if last.is_some() {
                    map.serialize_entry(
                        field.name,
                        &Repeated {
                            field: *field,
                            bytes: self.bytes,
                        },
                    )?;
                }
            } else if let Some(wire) = last {
                map.serialize_entry(
                    field.name,
                    &Scalar {
                        kind: field.kind,
                        value: wire.value,
                        coordinate: self.name == "Range",
                    },
                )?;
            } else if self.name == "Range" {
                map.serialize_entry(field.name, &0)?;
            }
        }
        map.end()
    }
}
impl Serialize for Repeated<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut seq = serializer.serialize_seq(None)?;
        for wire in Wire::new(self.bytes) {
            let wire = wire.map_err(serde::ser::Error::custom)?;
            if wire.number == self.field.number {
                seq.serialize_element(&Scalar {
                    kind: self.field.kind,
                    value: wire.value,
                    coordinate: false,
                })?;
            }
        }
        seq.end()
    }
}
impl Serialize for Scalar<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match (self.kind, self.value) {
            (FieldKind::Integer, Value::Integer(value)) if self.coordinate => {
                serializer.serialize_i32(int32(value).map_err(serde::ser::Error::custom)?)
            }
            (FieldKind::Integer, Value::Integer(value)) => serializer.serialize_u64(value),
            (FieldKind::Text, Value::Bytes(bytes)) => serializer
                .serialize_str(std::str::from_utf8(bytes).map_err(serde::ser::Error::custom)?),
            (FieldKind::Opaque, Value::Bytes(_)) => serializer.serialize_none(),
            (FieldKind::Message(name), Value::Bytes(bytes)) => {
                Message { name, bytes }.serialize(serializer)
            }
            _ => Err(serde::ser::Error::custom("SemanticDB wire type mismatch")),
        }
    }
}

fn constant_arm(bytes: &[u8]) -> Result<Option<WireField<'_>>, Error> {
    let mut fields = Wire::new(bytes);
    let first = fields.next().transpose()?;
    if fields.next().is_some() {
        return Err(Error::Invalid("ambiguous SemanticDB constant arm"));
    }
    Ok(first)
}
fn validate_constant(bytes: &[u8]) -> Result<(), Error> {
    let Some(arm) = constant_arm(bytes)? else {
        return Ok(());
    };
    let payload = arm.bytes()?;
    let inner = constant_arm(payload)?;
    match arm.number {
        1 | 11 if inner.is_none() => Ok(()),
        2..=7 => {
            if let Some(field) = inner {
                if field.number != 1 {
                    return Err(Error::Invalid("SemanticDB constant scalar field"));
                }
                let Value::Integer(value) = field.value else {
                    return Err(Error::Invalid("SemanticDB constant scalar wire"));
                };
                if (3..=6).contains(&arm.number) {
                    int32(value)?;
                }
            }
            Ok(())
        }
        8 | 9 => {
            if let Some(field) = inner {
                if field.number != 1 {
                    return Err(Error::Invalid("SemanticDB constant floating field"));
                }
                let Value::Fixed(bytes) = field.value else {
                    return Err(Error::Invalid("SemanticDB constant floating wire"));
                };
                if bytes.len() != if arm.number == 8 { 4 } else { 8 } {
                    return Err(Error::Invalid("SemanticDB constant float width"));
                }
            }
            Ok(())
        }
        10 => {
            if let Some(field) = inner {
                if field.number != 1 {
                    return Err(Error::Invalid("SemanticDB constant string field"));
                }
                std::str::from_utf8(field.bytes()?)
                    .map_err(|_| Error::Invalid("SemanticDB constant UTF-8"))?;
            }
            Ok(())
        }
        _ => Err(Error::Invalid("unsupported SemanticDB constant")),
    }
}
struct Constant<'a>(&'a [u8]);
impl Serialize for Constant<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut map = serializer.serialize_map(None)?;
        if let Some(arm) = constant_arm(self.0).map_err(serde::ser::Error::custom)? {
            let names = [
                "",
                "unit_constant",
                "boolean_constant",
                "byte_constant",
                "short_constant",
                "char_constant",
                "int_constant",
                "long_constant",
                "float_constant",
                "double_constant",
                "string_constant",
                "null_constant",
            ];
            map.serialize_entry(
                names[arm.number as usize],
                &ConstantPayload {
                    arm: arm.number,
                    bytes: arm.bytes().map_err(serde::ser::Error::custom)?,
                },
            )?;
        }
        map.end()
    }
}
struct ConstantPayload<'a> {
    arm: u32,
    bytes: &'a [u8],
}
impl Serialize for ConstantPayload<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut map = serializer.serialize_map(None)?;
        let inner = constant_arm(self.bytes).map_err(serde::ser::Error::custom)?;
        match self.arm {
            1 | 11 => {}
            2 => {
                let value = match inner.map(|field| field.value) {
                    Some(Value::Integer(value)) => value != 0,
                    _ => false,
                };
                map.serialize_entry("value", &value)?;
            }
            3..=7 => {
                let value = match inner.map(|field| field.value) {
                    Some(Value::Integer(value)) => value,
                    _ => 0,
                };
                if self.arm == 7 {
                    map.serialize_entry("value", &(value as i64))?;
                } else {
                    map.serialize_entry(
                        "value",
                        &int32(value).map_err(serde::ser::Error::custom)?,
                    )?;
                }
            }
            8 | 9 => {
                let empty = [0; 8];
                let bytes = match inner.map(|field| field.value) {
                    Some(Value::Fixed(bytes)) => bytes,
                    _ => &empty[..if self.arm == 8 { 4 } else { 8 }],
                };
                let mut hex = [0u8; 16];
                const HEX: &[u8; 16] = b"0123456789abcdef";
                for (index, byte) in bytes.iter().enumerate() {
                    hex[index * 2] = HEX[(byte >> 4) as usize];
                    hex[index * 2 + 1] = HEX[(byte & 15) as usize];
                }
                map.serialize_entry(
                    "ieee754_bits_le",
                    std::str::from_utf8(&hex[..bytes.len() * 2])
                        .map_err(serde::ser::Error::custom)?,
                )?;
                let value = if self.arm == 8 {
                    f32::from_le_bytes(bytes.try_into().unwrap()) as f64
                } else {
                    f64::from_le_bytes(bytes.try_into().unwrap())
                };
                if value.is_finite() {
                    map.serialize_entry("value", &value)?;
                }
            }
            10 => {
                let bytes = match inner.map(|field| field.value) {
                    Some(Value::Bytes(bytes)) => bytes,
                    _ => &[],
                };
                map.serialize_entry(
                    "value",
                    std::str::from_utf8(bytes).map_err(serde::ser::Error::custom)?,
                )?;
            }
            _ => return Err(serde::ser::Error::custom("unsupported SemanticDB constant")),
        }
        map.end()
    }
}
fn schema(name: &str) -> Option<&'static [Field]> {
    Some(match name {
        "TextDocuments" => &[Field {
            number: 1,
            name: "documents",
            kind: FieldKind::Message("TextDocument"),
            repeated: true,
        }],
        "TextDocument" => &[
            Field {
                number: 1,
                name: "schema",
                kind: FieldKind::Integer,
                repeated: false,
            },
            Field {
                number: 2,
                name: "uri",
                kind: FieldKind::Text,
                repeated: false,
            },
            Field {
                number: 3,
                name: "text",
                kind: FieldKind::Text,
                repeated: false,
            },
            Field {
                number: 5,
                name: "symbols",
                kind: FieldKind::Message("SymbolInformation"),
                repeated: true,
            },
            Field {
                number: 6,
                name: "occurrences",
                kind: FieldKind::Message("SymbolOccurrence"),
                repeated: true,
            },
            Field {
                number: 7,
                name: "diagnostics",
                kind: FieldKind::Message("Diagnostic"),
                repeated: true,
            },
            Field {
                number: 10,
                name: "language",
                kind: FieldKind::Integer,
                repeated: false,
            },
            Field {
                number: 11,
                name: "md5",
                kind: FieldKind::Text,
                repeated: false,
            },
            Field {
                number: 12,
                name: "synthetics",
                kind: FieldKind::Message("Synthetic"),
                repeated: true,
            },
        ],
        "Range" => &[
            Field {
                number: 1,
                name: "start_line",
                kind: FieldKind::Integer,
                repeated: false,
            },
            Field {
                number: 2,
                name: "start_character",
                kind: FieldKind::Integer,
                repeated: false,
            },
            Field {
                number: 3,
                name: "end_line",
                kind: FieldKind::Integer,
                repeated: false,
            },
            Field {
                number: 4,
                name: "end_character",
                kind: FieldKind::Integer,
                repeated: false,
            },
        ],
        "Scope" => &[
            Field {
                number: 1,
                name: "symlinks",
                kind: FieldKind::Text,
                repeated: true,
            },
            Field {
                number: 2,
                name: "hardlinks",
                kind: FieldKind::Message("SymbolInformation"),
                repeated: true,
            },
        ],
        "Type" => &[
            Field {
                number: 2,
                name: "type_ref",
                kind: FieldKind::Message("TypeRef"),
                repeated: false,
            },
            Field {
                number: 20,
                name: "single_type",
                kind: FieldKind::Message("SingleType"),
                repeated: false,
            },
            Field {
                number: 21,
                name: "this_type",
                kind: FieldKind::Message("ThisType"),
                repeated: false,
            },
            Field {
                number: 22,
                name: "super_type",
                kind: FieldKind::Message("SuperType"),
                repeated: false,
            },
            Field {
                number: 23,
                name: "constant_type",
                kind: FieldKind::Message("ConstantType"),
                repeated: false,
            },
            Field {
                number: 17,
                name: "intersection_type",
                kind: FieldKind::Message("Types"),
                repeated: false,
            },
            Field {
                number: 18,
                name: "union_type",
                kind: FieldKind::Message("Types"),
                repeated: false,
            },
            Field {
                number: 19,
                name: "with_type",
                kind: FieldKind::Message("Types"),
                repeated: false,
            },
            Field {
                number: 7,
                name: "structural_type",
                kind: FieldKind::Message("StructuralType"),
                repeated: false,
            },
            Field {
                number: 8,
                name: "annotated_type",
                kind: FieldKind::Message("AnnotatedType"),
                repeated: false,
            },
            Field {
                number: 9,
                name: "existential_type",
                kind: FieldKind::Message("ExistentialType"),
                repeated: false,
            },
            Field {
                number: 10,
                name: "universal_type",
                kind: FieldKind::Message("UniversalType"),
                repeated: false,
            },
            Field {
                number: 13,
                name: "by_name_type",
                kind: FieldKind::Message("UnaryType"),
                repeated: false,
            },
            Field {
                number: 14,
                name: "repeated_type",
                kind: FieldKind::Message("UnaryType"),
                repeated: false,
            },
            Field {
                number: 25,
                name: "match_type",
                kind: FieldKind::Message("MatchType"),
                repeated: false,
            },
            Field {
                number: 26,
                name: "lambda_type",
                kind: FieldKind::Message("LambdaType"),
                repeated: false,
            },
        ],
        "TypeRef" => &[
            Field {
                number: 1,
                name: "prefix",
                kind: FieldKind::Message("Type"),
                repeated: false,
            },
            Field {
                number: 2,
                name: "symbol",
                kind: FieldKind::Text,
                repeated: false,
            },
            Field {
                number: 3,
                name: "type_arguments",
                kind: FieldKind::Message("Type"),
                repeated: true,
            },
        ],
        "SingleType" => &[
            Field {
                number: 1,
                name: "prefix",
                kind: FieldKind::Message("Type"),
                repeated: false,
            },
            Field {
                number: 2,
                name: "symbol",
                kind: FieldKind::Text,
                repeated: false,
            },
        ],
        "ThisType" => &[Field {
            number: 1,
            name: "symbol",
            kind: FieldKind::Text,
            repeated: false,
        }],
        "SuperType" => &[
            Field {
                number: 1,
                name: "prefix",
                kind: FieldKind::Message("Type"),
                repeated: false,
            },
            Field {
                number: 2,
                name: "symbol",
                kind: FieldKind::Text,
                repeated: false,
            },
        ],
        "ConstantType" => &[Field {
            number: 1,
            name: "constant",
            kind: FieldKind::Message("Constant"),
            repeated: false,
        }],
        "Types" => &[Field {
            number: 1,
            name: "types",
            kind: FieldKind::Message("Type"),
            repeated: true,
        }],
        "StructuralType" => &[
            Field {
                number: 4,
                name: "tpe",
                kind: FieldKind::Message("Type"),
                repeated: false,
            },
            Field {
                number: 5,
                name: "declarations",
                kind: FieldKind::Message("Scope"),
                repeated: false,
            },
        ],
        "AnnotatedType" => &[
            Field {
                number: 1,
                name: "tpe",
                kind: FieldKind::Message("Type"),
                repeated: false,
            },
            Field {
                number: 3,
                name: "annotations",
                kind: FieldKind::Message("AnnotationTree"),
                repeated: true,
            },
        ],
        "ExistentialType" => &[
            Field {
                number: 1,
                name: "tpe",
                kind: FieldKind::Message("Type"),
                repeated: false,
            },
            Field {
                number: 3,
                name: "declarations",
                kind: FieldKind::Message("Scope"),
                repeated: false,
            },
        ],
        "UniversalType" => &[
            Field {
                number: 2,
                name: "tpe",
                kind: FieldKind::Message("Type"),
                repeated: false,
            },
            Field {
                number: 3,
                name: "type_parameters",
                kind: FieldKind::Message("Scope"),
                repeated: false,
            },
        ],
        "UnaryType" => &[Field {
            number: 1,
            name: "tpe",
            kind: FieldKind::Message("Type"),
            repeated: false,
        }],
        "LambdaType" => &[
            Field {
                number: 1,
                name: "parameters",
                kind: FieldKind::Message("Scope"),
                repeated: false,
            },
            Field {
                number: 2,
                name: "return_type",
                kind: FieldKind::Message("Type"),
                repeated: false,
            },
        ],
        "MatchType" => &[
            Field {
                number: 1,
                name: "scrutinee",
                kind: FieldKind::Message("Type"),
                repeated: false,
            },
            Field {
                number: 2,
                name: "cases",
                kind: FieldKind::Message("CaseType"),
                repeated: true,
            },
        ],
        "CaseType" => &[
            Field {
                number: 1,
                name: "key",
                kind: FieldKind::Message("Type"),
                repeated: false,
            },
            Field {
                number: 2,
                name: "body",
                kind: FieldKind::Message("Type"),
                repeated: false,
            },
        ],
        "Constant" => &[
            Field {
                number: 1,
                name: "unit_constant",
                kind: FieldKind::Opaque,
                repeated: false,
            },
            Field {
                number: 2,
                name: "boolean_constant",
                kind: FieldKind::Opaque,
                repeated: false,
            },
            Field {
                number: 3,
                name: "byte_constant",
                kind: FieldKind::Opaque,
                repeated: false,
            },
            Field {
                number: 4,
                name: "short_constant",
                kind: FieldKind::Opaque,
                repeated: false,
            },
            Field {
                number: 5,
                name: "char_constant",
                kind: FieldKind::Opaque,
                repeated: false,
            },
            Field {
                number: 6,
                name: "int_constant",
                kind: FieldKind::Opaque,
                repeated: false,
            },
            Field {
                number: 7,
                name: "long_constant",
                kind: FieldKind::Opaque,
                repeated: false,
            },
            Field {
                number: 8,
                name: "float_constant",
                kind: FieldKind::Opaque,
                repeated: false,
            },
            Field {
                number: 9,
                name: "double_constant",
                kind: FieldKind::Opaque,
                repeated: false,
            },
            Field {
                number: 10,
                name: "string_constant",
                kind: FieldKind::Opaque,
                repeated: false,
            },
            Field {
                number: 11,
                name: "null_constant",
                kind: FieldKind::Opaque,
                repeated: false,
            },
        ],
        "Signature" => &[
            Field {
                number: 1,
                name: "class_signature",
                kind: FieldKind::Message("ClassSignature"),
                repeated: false,
            },
            Field {
                number: 2,
                name: "method_signature",
                kind: FieldKind::Message("MethodSignature"),
                repeated: false,
            },
            Field {
                number: 3,
                name: "type_signature",
                kind: FieldKind::Message("TypeSignature"),
                repeated: false,
            },
            Field {
                number: 4,
                name: "value_signature",
                kind: FieldKind::Message("ValueSignature"),
                repeated: false,
            },
        ],
        "ClassSignature" => &[
            Field {
                number: 1,
                name: "type_parameters",
                kind: FieldKind::Message("Scope"),
                repeated: false,
            },
            Field {
                number: 2,
                name: "parents",
                kind: FieldKind::Message("Type"),
                repeated: true,
            },
            Field {
                number: 3,
                name: "self",
                kind: FieldKind::Message("Type"),
                repeated: false,
            },
            Field {
                number: 4,
                name: "declarations",
                kind: FieldKind::Message("Scope"),
                repeated: false,
            },
        ],
        "MethodSignature" => &[
            Field {
                number: 1,
                name: "type_parameters",
                kind: FieldKind::Message("Scope"),
                repeated: false,
            },
            Field {
                number: 2,
                name: "parameter_lists",
                kind: FieldKind::Message("Scope"),
                repeated: true,
            },
            Field {
                number: 3,
                name: "return_type",
                kind: FieldKind::Message("Type"),
                repeated: false,
            },
            Field {
                number: 4,
                name: "throws",
                kind: FieldKind::Message("Type"),
                repeated: true,
            },
        ],
        "TypeSignature" => &[
            Field {
                number: 1,
                name: "type_parameters",
                kind: FieldKind::Message("Scope"),
                repeated: false,
            },
            Field {
                number: 2,
                name: "lower_bound",
                kind: FieldKind::Message("Type"),
                repeated: false,
            },
            Field {
                number: 3,
                name: "upper_bound",
                kind: FieldKind::Message("Type"),
                repeated: false,
            },
        ],
        "ValueSignature" => &[Field {
            number: 1,
            name: "tpe",
            kind: FieldKind::Message("Type"),
            repeated: false,
        }],
        "SymbolInformation" => &[
            Field {
                number: 1,
                name: "symbol",
                kind: FieldKind::Text,
                repeated: false,
            },
            Field {
                number: 3,
                name: "kind",
                kind: FieldKind::Integer,
                repeated: false,
            },
            Field {
                number: 4,
                name: "properties",
                kind: FieldKind::Integer,
                repeated: false,
            },
            Field {
                number: 5,
                name: "display_name",
                kind: FieldKind::Text,
                repeated: false,
            },
            Field {
                number: 13,
                name: "annotations",
                kind: FieldKind::Message("AnnotationTree"),
                repeated: true,
            },
            Field {
                number: 16,
                name: "language",
                kind: FieldKind::Integer,
                repeated: false,
            },
            Field {
                number: 17,
                name: "signature",
                kind: FieldKind::Message("Signature"),
                repeated: false,
            },
            Field {
                number: 18,
                name: "access",
                kind: FieldKind::Message("Access"),
                repeated: false,
            },
            Field {
                number: 19,
                name: "overridden_symbols",
                kind: FieldKind::Text,
                repeated: true,
            },
            Field {
                number: 20,
                name: "documentation",
                kind: FieldKind::Opaque,
                repeated: false,
            },
        ],
        "AnnotationTree" => &[
            Field {
                number: 1,
                name: "tpe",
                kind: FieldKind::Message("Type"),
                repeated: false,
            },
            Field {
                number: 2,
                name: "arguments",
                kind: FieldKind::Message("Tree"),
                repeated: true,
            },
        ],
        "Access" => &[
            Field {
                number: 1,
                name: "private_access",
                kind: FieldKind::Opaque,
                repeated: false,
            },
            Field {
                number: 2,
                name: "private_this_access",
                kind: FieldKind::Opaque,
                repeated: false,
            },
            Field {
                number: 3,
                name: "private_within_access",
                kind: FieldKind::Message("WithinAccess"),
                repeated: false,
            },
            Field {
                number: 4,
                name: "protected_access",
                kind: FieldKind::Opaque,
                repeated: false,
            },
            Field {
                number: 5,
                name: "protected_this_access",
                kind: FieldKind::Opaque,
                repeated: false,
            },
            Field {
                number: 6,
                name: "protected_within_access",
                kind: FieldKind::Message("WithinAccess"),
                repeated: false,
            },
            Field {
                number: 7,
                name: "public_access",
                kind: FieldKind::Opaque,
                repeated: false,
            },
        ],
        "WithinAccess" => &[Field {
            number: 1,
            name: "symbol",
            kind: FieldKind::Text,
            repeated: false,
        }],
        "SymbolOccurrence" => &[
            Field {
                number: 1,
                name: "range",
                kind: FieldKind::Message("Range"),
                repeated: false,
            },
            Field {
                number: 2,
                name: "symbol",
                kind: FieldKind::Text,
                repeated: false,
            },
            Field {
                number: 3,
                name: "role",
                kind: FieldKind::Integer,
                repeated: false,
            },
        ],
        "Diagnostic" => &[
            Field {
                number: 1,
                name: "range",
                kind: FieldKind::Message("Range"),
                repeated: false,
            },
            Field {
                number: 2,
                name: "severity",
                kind: FieldKind::Integer,
                repeated: false,
            },
            Field {
                number: 3,
                name: "message",
                kind: FieldKind::Text,
                repeated: false,
            },
        ],
        "Synthetic" => &[
            Field {
                number: 1,
                name: "range",
                kind: FieldKind::Message("Range"),
                repeated: false,
            },
            Field {
                number: 2,
                name: "tree",
                kind: FieldKind::Message("Tree"),
                repeated: false,
            },
        ],
        "Tree" => &[
            Field {
                number: 1,
                name: "apply_tree",
                kind: FieldKind::Message("ApplyTree"),
                repeated: false,
            },
            Field {
                number: 2,
                name: "function_tree",
                kind: FieldKind::Message("FunctionTree"),
                repeated: false,
            },
            Field {
                number: 3,
                name: "id_tree",
                kind: FieldKind::Message("IdTree"),
                repeated: false,
            },
            Field {
                number: 4,
                name: "literal_tree",
                kind: FieldKind::Message("LiteralTree"),
                repeated: false,
            },
            Field {
                number: 5,
                name: "macro_expansion_tree",
                kind: FieldKind::Message("MacroExpansionTree"),
                repeated: false,
            },
            Field {
                number: 6,
                name: "original_tree",
                kind: FieldKind::Message("OriginalTree"),
                repeated: false,
            },
            Field {
                number: 7,
                name: "select_tree",
                kind: FieldKind::Message("SelectTree"),
                repeated: false,
            },
            Field {
                number: 8,
                name: "type_apply_tree",
                kind: FieldKind::Message("TypeApplyTree"),
                repeated: false,
            },
            Field {
                number: 9,
                name: "assign_tree",
                kind: FieldKind::Message("AssignTree"),
                repeated: false,
            },
            Field {
                number: 10,
                name: "annotation_tree",
                kind: FieldKind::Message("AnnotationTree"),
                repeated: false,
            },
        ],
        "ApplyTree" => &[
            Field {
                number: 1,
                name: "function",
                kind: FieldKind::Message("Tree"),
                repeated: false,
            },
            Field {
                number: 2,
                name: "arguments",
                kind: FieldKind::Message("Tree"),
                repeated: true,
            },
            Field {
                number: 3,
                name: "properties",
                kind: FieldKind::Integer,
                repeated: false,
            },
        ],
        "FunctionTree" => &[
            Field {
                number: 1,
                name: "parameters",
                kind: FieldKind::Message("IdTree"),
                repeated: true,
            },
            Field {
                number: 2,
                name: "body",
                kind: FieldKind::Message("Tree"),
                repeated: false,
            },
        ],
        "IdTree" => &[Field {
            number: 1,
            name: "symbol",
            kind: FieldKind::Text,
            repeated: false,
        }],
        "LiteralTree" => &[Field {
            number: 1,
            name: "constant",
            kind: FieldKind::Message("Constant"),
            repeated: false,
        }],
        "MacroExpansionTree" => &[
            Field {
                number: 1,
                name: "before_expansion",
                kind: FieldKind::Message("Tree"),
                repeated: false,
            },
            Field {
                number: 2,
                name: "tpe",
                kind: FieldKind::Message("Type"),
                repeated: false,
            },
        ],
        "OriginalTree" => &[Field {
            number: 1,
            name: "range",
            kind: FieldKind::Message("Range"),
            repeated: false,
        }],
        "SelectTree" => &[
            Field {
                number: 1,
                name: "qualifier",
                kind: FieldKind::Message("Tree"),
                repeated: false,
            },
            Field {
                number: 2,
                name: "id",
                kind: FieldKind::Message("IdTree"),
                repeated: false,
            },
        ],
        "TypeApplyTree" => &[
            Field {
                number: 1,
                name: "function",
                kind: FieldKind::Message("Tree"),
                repeated: false,
            },
            Field {
                number: 2,
                name: "type_arguments",
                kind: FieldKind::Message("Type"),
                repeated: true,
            },
        ],
        "AssignTree" => &[
            Field {
                number: 1,
                name: "lhs",
                kind: FieldKind::Message("Tree"),
                repeated: false,
            },
            Field {
                number: 2,
                name: "rhs",
                kind: FieldKind::Message("Tree"),
                repeated: false,
            },
        ],
        _ => return None,
    })
}
