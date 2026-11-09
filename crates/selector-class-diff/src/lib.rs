//! Diagnostic comparison only. Exact raw hashes remain admission identities.
//!
//! Only Code.LineNumberTable attributes and their derived enclosing lengths/
//! counts are omitted from comparison. Constant-pool bytes, attribute order and
//! every other byte must match. This is not JVM type verification, a provider
//! confinement proof, an execution summary, or permission to omit a suite.
pub mod build_stamp;

use selector_models::binary::diagnostic::{CodeValidator, utf8, validate_constant_pool};
use selector_models::binary::{
    BinaryError, ClassFile, ErrorKind, Limits, MethodInfo, method_descriptor, parse_class,
};
use selector_types::ContentHash;
use sha2::{Digest, Sha256};
type Result<T> = std::result::Result<T, BinaryError>;
fn error(kind: ErrorKind, offset: usize) -> BinaryError {
    BinaryError { kind, offset }
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}
impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, at: 0 }
    }
    fn take(&mut self, count: usize) -> Result<&'a [u8]> {
        let end = self
            .at
            .checked_add(count)
            .ok_or(error(ErrorKind::Truncated, self.at))?;
        let bytes = self
            .bytes
            .get(self.at..end)
            .ok_or(error(ErrorKind::Truncated, self.at))?;
        self.at = end;
        Ok(bytes)
    }
    fn u1(&mut self) -> Result<u8> {
        Ok(self.take(1)?[0])
    }
    fn u2(&mut self) -> Result<u16> {
        Ok(u16::from_be_bytes(self.take(2)?.try_into().unwrap()))
    }
    fn u4(&mut self) -> Result<u32> {
        Ok(u32::from_be_bytes(self.take(4)?.try_into().unwrap()))
    }
    fn end(&self) -> Result<()> {
        if self.at == self.bytes.len() {
            Ok(())
        } else {
            Err(error(ErrorKind::TrailingBytes, self.at))
        }
    }
}
fn valid_dynamic_name(name: &str) -> Result<()> {
    if name.is_empty()
        || name
            .bytes()
            .any(|b| matches!(b, b'.' | b';' | b'[' | b'/' | b'<' | b'>' | b'\0'))
    {
        return Err(error(ErrorKind::BadConstant, 0));
    }
    Ok(())
}

#[derive(Clone, Copy, Debug)]
pub struct LntLimits {
    pub binary: Limits,
    pub max_input_bytes: usize,
    pub max_scratch_bytes: usize,
    pub max_attributes: usize,
    pub max_line_entries: usize,
    pub max_instructions: usize,
}
impl Default for LntLimits {
    fn default() -> Self {
        Self {
            binary: Limits::default(),
            max_input_bytes: 16 * 1024 * 1024,
            max_scratch_bytes: 16 * 1024 * 1024,
            max_attributes: 262_144,
            max_line_entries: 1_048_576,
            max_instructions: 2_097_152,
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LntSide {
    Before,
    After,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LntStage {
    Input,
    Scratch,
    ClassWire,
    Code,
    LineTable,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LntUnavailable {
    pub side: Option<LntSide>,
    pub stage: LntStage,
    /// Follows BinaryError offsets: Code uses method-relative PCs; class errors
    /// can identify wire positions or constant-pool indices.
    pub error: BinaryError,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LntChange {
    Identical,
    LineNumberTablesOnly,
    OtherChange,
    Unavailable(LntUnavailable),
}
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LntMetrics {
    pub input_bytes: usize,
    /// Conservative preflight charge, not an allocator/RSS measurement.
    pub scratch_upper_bound_bytes: usize,
    pub methods_validated: usize,
    pub instructions_validated: usize,
    pub attributes_validated: usize,
    pub line_tables_validated: usize,
    pub line_entries_validated: usize,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LntComparison {
    pub change: LntChange,
    /// Absent when input/scratch budgets reject before hashing. Never normalized.
    pub raw_hashes: Option<(ContentHash, ContentHash)>,
    pub metrics: LntMetrics,
}
impl LntComparison {
    pub const fn diagnostic_only(&self) -> bool {
        true
    }
    pub const fn omission_authority(&self) -> bool {
        false
    }
}
fn bad(offset: usize) -> BinaryError {
    error(ErrorKind::BadConstant, offset)
}
fn limit(offset: usize) -> BinaryError {
    error(ErrorKind::ResourceLimit, offset)
}

/// Both inputs are structurally checked before returning OtherChange as well.
/// Unknown attribute payloads remain opaque and exact; their internal semantics
/// and JVM stack-map/type verification are outside this diagnostic's authority.
pub fn compare_line_number_tables(before: &[u8], after: &[u8], limits: LntLimits) -> LntComparison {
    let mut result = LntComparison {
        change: LntChange::OtherChange,
        raw_hashes: None,
        metrics: LntMetrics::default(),
    };
    let unavailable = |stage| {
        LntChange::Unavailable(LntUnavailable {
            side: None,
            stage,
            error: limit(0),
        })
    };
    let Some(total) = before.len().checked_add(after.len()) else {
        result.change = unavailable(LntStage::Input);
        return result;
    };
    result.metrics.input_bytes = total;
    if total > limits.max_input_bytes
        || before.len() > limits.binary.max_class_bytes
        || after.len() > limits.binary.max_class_bytes
    {
        result.change = unavailable(LntStage::Input);
        return result;
    }
    // parse_class borrows byte payloads. Its CP/member/interface vectors have
    // at most 32 bytes of capacity per input byte, including geometric growth.
    // The reusable decoder's instruction/target/boundary capacities are bounded
    // by 32 bytes per possible Code byte. Reject before those allocations.
    let upper = total
        .checked_mul(32)
        .and_then(|n| {
            limits
                .binary
                .max_code_bytes
                .checked_add(1)
                .and_then(|code| code.checked_mul(32))
                .and_then(|code| n.checked_add(code))
        })
        .and_then(|n| n.checked_add(4096));
    let Some(upper) = upper else {
        result.change = unavailable(LntStage::Scratch);
        return result;
    };
    result.metrics.scratch_upper_bound_bytes = upper;
    if upper > limits.max_scratch_bytes {
        result.change = unavailable(LntStage::Scratch);
        return result;
    }
    result.raw_hashes = Some((
        ContentHash(Sha256::digest(before).into()),
        ContentHash(Sha256::digest(after).into()),
    ));
    let mut validator = CodeValidator::default();
    let mut member_order = Vec::new();
    let mut run = || -> std::result::Result<bool, LntUnavailable> {
        let left = parse_class(before, limits.binary).map_err(|error| LntUnavailable {
            side: Some(LntSide::Before),
            stage: LntStage::ClassWire,
            error,
        })?;
        let right = parse_class(after, limits.binary).map_err(|error| LntUnavailable {
            side: Some(LntSide::After),
            stage: LntStage::ClassWire,
            error,
        })?;
        for (side, bytes, class) in [
            (LntSide::Before, before, &left),
            (LntSide::After, after, &right),
        ] {
            validate_constant_pool(class).map_err(|error| LntUnavailable {
                side: Some(side),
                stage: LntStage::ClassWire,
                error,
            })?;
            validate_declarations(class, &mut member_order).map_err(|error| LntUnavailable {
                side: Some(side),
                stage: LntStage::ClassWire,
                error,
            })?;
            validate_wire(bytes, class, limits, &mut validator, &mut result.metrics).map_err(
                |(stage, error)| LntUnavailable {
                    side: Some(side),
                    stage,
                    error,
                },
            )?;
        }
        equivalent(before, after, &left, &right).map_err(|error| LntUnavailable {
            side: None,
            stage: LntStage::ClassWire,
            error,
        })
    };
    result.change = match run() {
        Err(error) => LntChange::Unavailable(error),
        Ok(_) if before == after => LntChange::Identical,
        Ok(true) => LntChange::LineNumberTablesOnly,
        Ok(false) => LntChange::OtherChange,
    };
    result
}

fn validate_declarations(class: &ClassFile<'_>, order: &mut Vec<usize>) -> Result<()> {
    if class.flags & !0xf631 != 0
        || class.flags & (0x10 | 0x400) == 0x410
        || (class.flags & 0x200 != 0 && class.flags & 0x400 == 0)
        || (class.parent.is_none() && class.name != "java/lang/Object" && class.flags & 0x8000 == 0)
    {
        return Err(bad(0));
    }
    let access = |flags: u16| (flags & 7).count_ones() <= 1;
    for field in &class.fields {
        valid_dynamic_name(field.name)?;
        if !access(field.flags) || field.flags & !0x50df != 0 || field.flags & 0x50 == 0x50 {
            return Err(bad(0));
        }
    }
    for method in &class.methods {
        if !access(method.flags)
            || method.flags & !0x1dff != 0
            || (method.flags & 0x400 != 0 && method.flags & (2 | 8 | 16 | 32 | 0x100 | 0x800) != 0)
        {
            return Err(bad(0));
        }
        match method.name {
            "<init>"
                if method.flags & !(7 | 0x80 | 0x800 | 0x1000) != 0
                    || method_descriptor(method.descriptor)?.return_type != "V" =>
            {
                return Err(bad(0));
            }
            "<clinit>"
                if method.descriptor != "()V" || (class.major >= 51 && method.flags & 8 == 0) =>
            {
                return Err(bad(0));
            }
            "<init>" | "<clinit>" => {}
            name => valid_dynamic_name(name)?,
        }
    }
    for methods in [false, true] {
        order.clear();
        let count = if methods {
            class.methods.len()
        } else {
            class.fields.len()
        };
        order.try_reserve_exact(count).map_err(|_| limit(0))?;
        order.extend(0..count);
        let key = |i: usize| {
            if methods {
                let m = class.methods[i];
                (m.name, m.descriptor)
            } else {
                let f = class.fields[i];
                (f.name, f.descriptor)
            }
        };
        order.sort_unstable_by_key(|i| key(*i));
        if order.windows(2).any(|pair| key(pair[0]) == key(pair[1])) {
            return Err(bad(0));
        }
    }
    Ok(())
}
fn skip_pool(reader: &mut Reader<'_>) -> Result<()> {
    reader.take(8)?;
    let count = reader.u2()? as usize;
    let mut i = 1;
    while i < count {
        let tag = reader.u1()?;
        match tag {
            1 => {
                let n = reader.u2()? as usize;
                reader.take(n)?;
            }
            3 | 4 | 9..=12 | 17 | 18 => {
                reader.take(4)?;
            }
            5 | 6 => {
                reader.take(8)?;
                i += 1;
            }
            7 | 8 | 16 | 19 | 20 => {
                reader.take(2)?;
            }
            15 => {
                reader.take(3)?;
            }
            _ => {
                return Err(error(ErrorKind::UnsupportedConstant, reader.at - 1));
            }
        }
        i += 1;
    }
    Ok(())
}
#[derive(Clone, Copy)]
struct Attribute<'a> {
    name: u16,
    bytes: &'a [u8],
}
fn attribute<'a>(reader: &mut Reader<'a>) -> Result<Attribute<'a>> {
    let name = reader.u2()?;
    let length = reader.u4()? as usize;
    Ok(Attribute {
        name,
        bytes: reader.take(length)?,
    })
}
fn charge(value: &mut usize, add: usize, maximum: usize, offset: usize) -> Result<()> {
    *value = value.checked_add(add).ok_or(limit(offset))?;
    if *value > maximum {
        Err(limit(offset))
    } else {
        Ok(())
    }
}
type Checked<T> = std::result::Result<T, (LntStage, BinaryError)>;
fn wire<T>(result: Result<T>) -> Checked<T> {
    result.map_err(|error| (LntStage::ClassWire, error))
}

fn validate_wire(
    bytes: &[u8],
    class: &ClassFile<'_>,
    limits: LntLimits,
    validator: &mut CodeValidator,
    metrics: &mut LntMetrics,
) -> Checked<()> {
    let mut reader = Reader::new(bytes);
    wire(skip_pool(&mut reader))?;
    wire(reader.take(6))?;
    let interfaces = wire(reader.u2())? as usize;
    wire(reader.take(interfaces * 2))?;
    for methods in [false, true] {
        let count = wire(reader.u2())? as usize;
        if count
            != if methods {
                class.methods.len()
            } else {
                class.fields.len()
            }
        {
            return Err((LntStage::ClassWire, bad(reader.at)));
        }
        for index in 0..count {
            wire(reader.take(6))?;
            let attributes = wire(reader.u2())? as usize;
            wire(charge(
                &mut metrics.attributes_validated,
                attributes,
                limits.max_attributes,
                reader.at,
            ))?;
            let mut code = false;
            if methods {
                metrics.methods_validated += 1;
            }
            for _ in 0..attributes {
                let attr = wire(attribute(&mut reader))?;
                match wire(utf8(class, attr.name))? {
                    "LineNumberTable" => return Err((LntStage::ClassWire, bad(reader.at))),
                    "Code" if !methods || code => {
                        return Err((LntStage::ClassWire, bad(reader.at)));
                    }
                    "Code" => {
                        code = true;
                        validate_code(
                            attr.bytes,
                            class,
                            &class.methods[index],
                            limits,
                            validator,
                            metrics,
                        )?;
                    }
                    _ => {}
                }
            }
            if methods {
                let flags = class.methods[index].flags;
                if code == (flags & (0x100 | 0x400) != 0) || flags & (0x100 | 0x400) == 0x500 {
                    return Err((
                        LntStage::ClassWire,
                        error(ErrorKind::InvalidCode, reader.at),
                    ));
                }
            }
        }
    }
    let attrs = wire(reader.u2())? as usize;
    wire(charge(
        &mut metrics.attributes_validated,
        attrs,
        limits.max_attributes,
        reader.at,
    ))?;
    for _ in 0..attrs {
        let attr = wire(attribute(&mut reader))?;
        if matches!(wire(utf8(class, attr.name))?, "LineNumberTable" | "Code") {
            return Err((LntStage::ClassWire, bad(reader.at)));
        }
    }
    wire(reader.end())
}
fn validate_code(
    bytes: &[u8],
    class: &ClassFile<'_>,
    method: &MethodInfo<'_>,
    limits: LntLimits,
    validator: &mut CodeValidator,
    metrics: &mut LntMetrics,
) -> Checked<()> {
    let mut binary_limits = limits.binary;
    binary_limits.max_steps = binary_limits.max_steps.min(
        limits
            .max_instructions
            .saturating_sub(metrics.instructions_validated),
    );
    validator
        .validate(class, method, binary_limits)
        .map_err(|error| (LntStage::Code, error))?;
    metrics.instructions_validated += validator.instruction_count();
    let mut reader = Reader::new(bytes);
    wire(reader.take(4))?;
    let code_len = wire(reader.u4())? as usize;
    wire(reader.take(code_len))?;
    let handlers = wire(reader.u2())? as usize;
    wire(reader.take(handlers * 8))?;
    let attrs = wire(reader.u2())? as usize;
    wire(charge(
        &mut metrics.attributes_validated,
        attrs,
        limits.max_attributes,
        reader.at,
    ))?;
    for _ in 0..attrs {
        let attr = wire(attribute(&mut reader))?;
        let name = wire(utf8(class, attr.name))?;
        if name == "Code" {
            return Err((LntStage::ClassWire, bad(reader.at)));
        }
        if name != "LineNumberTable" {
            continue;
        }
        metrics.line_tables_validated += 1;
        let check = || -> Result<usize> {
            let mut lines = Reader::new(attr.bytes);
            let count = lines.u2()? as usize;
            if attr.bytes.len() != 2 + count * 4 {
                return Err(bad(reader.at));
            }
            if count
                > limits
                    .max_line_entries
                    .saturating_sub(metrics.line_entries_validated)
            {
                return Err(limit(reader.at));
            }
            for _ in 0..count {
                let pc = lines.u2()? as usize;
                lines.u2()?;
                if pc >= code_len || !validator.instruction_start(pc) {
                    return Err(error(ErrorKind::InvalidCode, pc));
                }
            }
            lines.end()?;
            Ok(count)
        };
        metrics.line_entries_validated += check().map_err(|error| (LntStage::LineTable, error))?;
    }
    wire(reader.end())
}

fn equal_attributes(
    a: &mut Reader<'_>,
    b: &mut Reader<'_>,
    ca: &ClassFile<'_>,
    cb: &ClassFile<'_>,
    code: bool,
) -> Result<bool> {
    let n = a.u2()?;
    if n != b.u2()? {
        return Ok(false);
    }
    for _ in 0..n {
        let (left, right) = (attribute(a)?, attribute(b)?);
        if left.name != right.name {
            return Ok(false);
        }
        if code && utf8(ca, left.name)? == "Code" && utf8(cb, right.name)? == "Code" {
            if !equal_code(left.bytes, right.bytes, ca, cb)? {
                return Ok(false);
            }
        } else if left.bytes != right.bytes {
            return Ok(false);
        }
    }
    Ok(true)
}
fn next_non_line<'a>(
    reader: &mut Reader<'a>,
    remaining: &mut u16,
    class: &ClassFile<'_>,
) -> Result<Option<Attribute<'a>>> {
    while *remaining != 0 {
        *remaining -= 1;
        let attr = attribute(reader)?;
        if utf8(class, attr.name)? != "LineNumberTable" {
            return Ok(Some(attr));
        }
    }
    Ok(None)
}
fn equal_code(a: &[u8], b: &[u8], ca: &ClassFile<'_>, cb: &ClassFile<'_>) -> Result<bool> {
    let (mut a, mut b) = (Reader::new(a), Reader::new(b));
    if a.take(4)? != b.take(4)? {
        return Ok(false);
    }
    let (al, bl) = (a.u4()? as usize, b.u4()? as usize);
    if al != bl || a.take(al)? != b.take(bl)? {
        return Ok(false);
    }
    let (al, bl) = (a.u2()? as usize, b.u2()? as usize);
    if al != bl || a.take(al * 8)? != b.take(bl * 8)? {
        return Ok(false);
    }
    let (mut al, mut bl) = (a.u2()?, b.u2()?);
    loop {
        match (
            next_non_line(&mut a, &mut al, ca)?,
            next_non_line(&mut b, &mut bl, cb)?,
        ) {
            (None, None) => return Ok(true),
            (Some(a), Some(b)) if a.name == b.name && a.bytes == b.bytes => {}
            _ => return Ok(false),
        }
    }
}
fn equivalent(a: &[u8], b: &[u8], ca: &ClassFile<'_>, cb: &ClassFile<'_>) -> Result<bool> {
    let (mut a_reader, mut b_reader) = (Reader::new(a), Reader::new(b));
    skip_pool(&mut a_reader)?;
    skip_pool(&mut b_reader)?;
    if a[..a_reader.at] != b[..b_reader.at] {
        return Ok(false);
    }
    if a_reader.take(6)? != b_reader.take(6)? {
        return Ok(false);
    }
    let (ai, bi) = (a_reader.u2()? as usize, b_reader.u2()? as usize);
    if ai != bi || a_reader.take(ai * 2)? != b_reader.take(bi * 2)? {
        return Ok(false);
    }
    for methods in [false, true] {
        let (an, bn) = (a_reader.u2()?, b_reader.u2()?);
        if an != bn {
            return Ok(false);
        }
        for _ in 0..an {
            if a_reader.take(6)? != b_reader.take(6)?
                || !equal_attributes(&mut a_reader, &mut b_reader, ca, cb, methods)?
            {
                return Ok(false);
            }
        }
    }
    equal_attributes(&mut a_reader, &mut b_reader, ca, cb, false)
}

#[cfg(test)]
#[path = "tests.rs"]
mod tests;
