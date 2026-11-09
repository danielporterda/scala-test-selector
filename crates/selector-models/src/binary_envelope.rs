//! Complete structural native may-effect coverage, independent of precise data.
//!
//! Every instruction (including catch handlers and unselected branches) is
//! decoded before fallback can be closed. Imprecise operands are TOP; aliases,
//! callbacks and external effects still use ordinary guarded consumers.
//! This checks structural bytecode coverage, not JVM stack/type verification.
//! A complete local envelope still depends on admitted callees, class phases,
//! callback/receiver resolution and heap consumers in the ordinary graph.
use super::*;
use std::collections::HashMap;

#[path = "binary_envelope_aliases.rs"]
mod aliases;

#[derive(Clone, Copy, Debug, Default)]
pub struct EnvelopeCoverage {
    pub instructions: u32,
    pub fallback: bool,
    /// Every encoded instruction and exception target was structurally checked.
    /// This alone is not a closed-execution or precise-value certificate.
    pub structurally_complete: bool,
    pub open_channels: u32,
}
#[derive(Clone, Copy, Debug, Default)]
pub struct EnvelopeMetrics {
    pub decoded_methods: u64,
    pub decoded_instructions: u64,
    pub decode_cache_hits: u64,
    pub fallback_methods: u64,
    pub complete_local_envelopes: u64,
    pub open_envelopes: u64,
    pub malformed_rejects: u64,
    pub budget_rejects: u64,
    /// Instruction capacities plus a conservative per-entry index/Arc charge.
    /// This is the bounded retained-cache charge, not allocator instrumentation.
    pub retained_decode_bytes: usize,
}
#[derive(Clone, Copy)]
struct Instruction {
    pc: u32,
    operand: u16,
    opcode: u8,
    auxiliary: u8,
}
struct Scan {
    instructions: Vec<Instruction>,
}
/// Diagnostic consumers reuse the same checked instruction-boundary decoder.
/// The existing admission path still receives exactly the same Scan records.
#[derive(Default)]
pub(super) struct StructuralCodeValidator {
    instructions: Vec<Instruction>,
    starts: Vec<bool>,
    targets: Vec<usize>,
}
impl StructuralCodeValidator {
    pub(super) fn validate(
        &mut self,
        class: &ClassFile<'_>,
        method: &MethodInfo<'_>,
        limits: Limits,
    ) -> Result<()> {
        decode_reusing(class, method, limits, self)
    }
    pub(super) fn instruction_count(&self) -> usize {
        self.instructions.len()
    }
    pub(super) fn instruction_start(&self, pc: usize) -> bool {
        self.starts.get(pc).copied().unwrap_or(false)
    }
}
/// A bounded instruction cache owns no class bytes or fact/graph borrow. Keys
/// include the admitted whole-class hash, method identity and structural limits;
/// provider resolution remains a separate, context-qualified operation.
pub struct EnvelopeCache {
    scans: HashMap<ContentHash, Arc<Scan>>,
    max_bytes: usize,
    metrics: EnvelopeMetrics,
}
impl EnvelopeCache {
    pub fn new(max_bytes: usize) -> Self {
        Self {
            scans: HashMap::new(),
            max_bytes,
            metrics: EnvelopeMetrics::default(),
        }
    }
    pub fn metrics(&self) -> EnvelopeMetrics {
        self.metrics
    }
    pub fn summarize<'a>(
        &mut self,
        class: &ClassFile<'a>,
        method: &MethodInfo<'a>,
        class_hash: ContentHash,
        limits: Limits,
    ) -> MethodSummary<'a> {
        let mut precise = summarize(class, method, limits);
        let mut hash = Sha256::new();
        hash.update(b"native-effect-instructions/1\0");
        hash.update(class_hash.0);
        for text in [method.name, method.descriptor] {
            hash.update((text.len() as u64).to_le_bytes());
            hash.update(text.as_bytes());
        }
        hash.update(method.flags.to_le_bytes());
        hash.update(method.max_stack.to_le_bytes());
        hash.update(method.max_locals.to_le_bytes());
        if let Some(code) = method.code {
            hash.update((code.len() as u64).to_le_bytes());
            hash.update(code);
        } else {
            hash.update(0u64.to_le_bytes());
        }
        hash.update(method.exception_handlers.to_le_bytes());
        hash.update((method.exception_table.len() as u64).to_le_bytes());
        hash.update(method.exception_table);
        for bound in [
            limits.max_code_bytes,
            limits.max_locals,
            limits.max_stack,
            limits.max_steps,
        ] {
            hash.update((bound as u64).to_le_bytes());
        }
        let key = ContentHash(hash.finalize().into());
        let scan = if class_hash != ContentHash::default() {
            self.scans.get(&key).cloned()
        } else {
            None
        };
        let scan = if let Some(scan) = scan {
            self.metrics.decode_cache_hits += 1;
            scan
        } else {
            match decode(class, method, limits) {
                Ok(scan) => {
                    self.metrics.decoded_methods += 1;
                    self.metrics.decoded_instructions += scan.instructions.len() as u64;
                    let bytes = std::mem::size_of::<Scan>()
                        + scan.instructions.capacity() * std::mem::size_of::<Instruction>()
                        + 256;
                    let scan = Arc::new(scan);
                    if class_hash != ContentHash::default()
                        && self
                            .metrics
                            .retained_decode_bytes
                            .checked_add(bytes)
                            .is_some_and(|n| n <= self.max_bytes)
                    {
                        self.scans.insert(key, scan.clone());
                        self.metrics.retained_decode_bytes += bytes;
                    }
                    scan
                }
                Err(error) => {
                    if error.kind == ErrorKind::ResourceLimit {
                        self.metrics.budget_rejects += 1;
                    } else if error.kind != ErrorKind::MissingCode {
                        self.metrics.malformed_rejects += 1;
                    }
                    self.metrics.open_envelopes += 1;
                    precise.unknown = Some(error);
                    precise.envelope = Some(EnvelopeCoverage {
                        fallback: true,
                        ..Default::default()
                    });
                    return precise;
                }
            }
        };
        let count = scan.instructions.len() as u32;
        // Structural API calls are frontiers even when their operands happen to
        // fit the straight-line interpreter. A known descriptor is not a model
        // for reflection, dynamic loading or native/global execution.
        let has_open = method.flags & 0x20 != 0
            || scan
                .instructions
                .iter()
                .any(|instruction| is_open(class, *instruction));
        if precise.complete() && !has_open {
            precise.envelope = Some(EnvelopeCoverage {
                instructions: count,
                structurally_complete: true,
                ..Default::default()
            });
            return precise;
        }
        self.metrics.fallback_methods += 1;
        match project(class, method, &scan, limits) {
            Ok(mut out) => {
                let open = out.unknown_offsets.len() as u32;
                out.envelope = Some(EnvelopeCoverage {
                    instructions: count,
                    fallback: true,
                    structurally_complete: true,
                    open_channels: open,
                });
                if out.complete() {
                    self.metrics.complete_local_envelopes += 1;
                } else {
                    self.metrics.open_envelopes += 1;
                }
                out
            }
            Err(error) => {
                if error.kind == ErrorKind::ResourceLimit {
                    self.metrics.budget_rejects += 1;
                } else {
                    self.metrics.malformed_rejects += 1;
                }
                self.metrics.open_envelopes += 1;
                precise.unknown = Some(error);
                precise.envelope = Some(EnvelopeCoverage {
                    instructions: count,
                    fallback: true,
                    structurally_complete: true,
                    open_channels: 1,
                });
                precise
            }
        }
    }
}
pub fn summarize_with_envelope<'a>(
    class: &ClassFile<'a>,
    method: &MethodInfo<'a>,
    limits: Limits,
) -> MethodSummary<'a> {
    EnvelopeCache::new(0).summarize(class, method, ContentHash::default(), limits)
}
fn invalid(pc: usize) -> BinaryError {
    BinaryError::at(ErrorKind::InvalidCode, pc)
}
fn target(targets: &mut Vec<usize>, pc: usize, delta: i32, length: usize) -> Result<()> {
    let target = (pc as i64).checked_add(delta as i64).ok_or(invalid(pc))?;
    if target < 0 || target as usize >= length {
        return Err(invalid(pc));
    }
    targets.push(target as usize);
    Ok(())
}
fn local(method: &MethodInfo<'_>, index: u16, width: usize, pc: usize) -> Result<()> {
    if (index as usize)
        .checked_add(width)
        .is_none_or(|end| end > method.max_locals as usize)
    {
        return Err(invalid(pc));
    }
    Ok(())
}
fn member<'a>(class: &ClassFile<'a>, index: u16, opcode: u8, pc: usize) -> Result<MemberRef<'a>> {
    let value = class.member(index, opcode <= 181)?;
    let Constant::Member { tag, .. } = class.pool[index as usize] else {
        return Err(invalid(pc));
    };
    let valid = match opcode {
        178..=181 => tag == 9,
        182 => tag == 10,
        185 => tag == 11,
        _ => tag == 10 || (class.major >= 52 && tag == 11),
    };
    if !valid {
        return Err(invalid(pc));
    }
    valid_class_name(value.owner)?;
    if opcode <= 181 || value.name != "<init>" {
        valid_dynamic_name(value.name)?;
    }
    if opcode <= 181 {
        field_descriptor(value.descriptor)?;
    } else {
        let descriptor = method_descriptor(value.descriptor)?;
        if value.name == "<clinit>"
            || (value.name == "<init>"
                && (opcode != 183 || tag != 10 || descriptor.return_type != "V"))
        {
            return Err(invalid(pc));
        }
    }
    Ok(value)
}
fn constant(class: &ClassFile<'_>, index: u16, wide: bool, pc: usize) -> Result<()> {
    let value = class.pool.get(index as usize).ok_or(invalid(pc))?;
    let category = match value {
        Constant::Integer(_) | Constant::Number(3 | 4) => false,
        Constant::String(text) => {
            class.utf(*text)?;
            false
        }
        Constant::Class(_) => {
            let name = class.class(index)?;
            if name.starts_with('[') {
                field_descriptor(name)?;
            } else {
                valid_class_name(name)?;
            }
            false
        }
        Constant::MethodType(_) => {
            class.method_type(index)?;
            false
        }
        Constant::MethodHandle { .. } => {
            class.method_handle(index)?;
            false
        }
        Constant::WideNumber(5 | 6) => true,
        Constant::Dynamic { pair, .. } => {
            class.bootstrap_argument(index)?;
            width(field_descriptor(class.name_type(*pair)?.1)?) == 2
        }
        _ => return Err(invalid(pc)),
    };
    if category != wide {
        return Err(invalid(pc));
    }
    Ok(())
}
fn decode(class: &ClassFile<'_>, method: &MethodInfo<'_>, limits: Limits) -> Result<Scan> {
    let mut scratch = StructuralCodeValidator::default();
    scratch.validate(class, method, limits)?;
    Ok(Scan {
        instructions: scratch.instructions,
    })
}
fn decode_reusing(
    class: &ClassFile<'_>,
    method: &MethodInfo<'_>,
    limits: Limits,
    scratch: &mut StructuralCodeValidator,
) -> Result<()> {
    let code = method
        .code
        .ok_or(BinaryError::at(ErrorKind::MissingCode, 0))?;
    if code.is_empty() {
        return Err(invalid(0));
    }
    if code.len() > limits.max_code_bytes
        || method.max_locals as usize > limits.max_locals
        || method.max_stack as usize > limits.max_stack
    {
        return Err(BinaryError::at(ErrorKind::ResourceLimit, 0));
    }
    if method.flags & (0x100 | 0x400) != 0 {
        return Err(invalid(0));
    }
    let descriptor = method_descriptor(method.descriptor)?;
    if descriptor.parameter_slots + usize::from(method.flags & 8 == 0) > method.max_locals as usize
    {
        return Err(invalid(0));
    }
    if method.exception_table.len() != method.exception_handlers as usize * 8 {
        return Err(invalid(0));
    }
    let starts = &mut scratch.starts;
    starts.clear();
    starts
        .try_reserve_exact(code.len() + 1)
        .map_err(|_| BinaryError::at(ErrorKind::ResourceLimit, 0))?;
    starts.resize(code.len() + 1, false);
    let targets = &mut scratch.targets;
    targets.clear();
    let instructions = &mut scratch.instructions;
    instructions.clear();
    instructions
        .try_reserve_exact(code.len().min(256))
        .map_err(|_| BinaryError::at(ErrorKind::ResourceLimit, 0))?;
    let mut reader = Reader::new(code);
    while reader.at < code.len() {
        let pc = reader.at;
        if instructions.len() >= limits.max_steps {
            return Err(BinaryError::at(ErrorKind::ResourceLimit, pc));
        }
        starts[pc] = true;
        let opcode = reader.u1()?;
        let mut operand = 0;
        let mut auxiliary = 0;
        match opcode {
            0..=15 | 26..=53 | 59..=131 | 133..=152 | 172..=177 | 190..=191 | 194..=195 => {}
            16 => {
                reader.u1()?;
            }
            17 => {
                reader.u2()?;
            }
            18 => {
                operand = reader.u1()? as u16;
                constant(class, operand, false, pc)?;
            }
            19..=20 => {
                operand = reader.u2()?;
                constant(class, operand, opcode == 20, pc)?;
            }
            21..=25 | 54..=58 | 169 => {
                operand = reader.u1()? as u16;
                local(
                    method,
                    operand,
                    if matches!(opcode, 22 | 24 | 55 | 57) {
                        2
                    } else {
                        1
                    },
                    pc,
                )?;
            }
            132 => {
                operand = reader.u1()? as u16;
                reader.u1()?;
                local(method, operand, 1, pc)?;
            }
            153..=168 | 198..=199 => {
                let delta = reader.u2()? as i16 as i32;
                target(targets, pc, delta, code.len())?;
            }
            170..=171 => {
                while reader.at % 4 != 0 {
                    if reader.u1()? != 0 {
                        return Err(invalid(pc));
                    }
                }
                target(targets, pc, reader.u4()? as i32, code.len())?;
                if opcode == 170 {
                    let low = reader.u4()? as i32;
                    let high = reader.u4()? as i32;
                    let count = high as i64 - low as i64 + 1;
                    if count <= 0 || count as usize > (code.len() - reader.at) / 4 {
                        return Err(invalid(pc));
                    }
                    for _ in 0..count {
                        target(targets, pc, reader.u4()? as i32, code.len())?;
                    }
                } else {
                    let count = reader.u4()? as i32;
                    if count < 0 || count as usize > (code.len() - reader.at) / 8 {
                        return Err(invalid(pc));
                    }
                    let mut previous = None;
                    for _ in 0..count {
                        let key = reader.u4()? as i32;
                        if previous.is_some_and(|old| old >= key) {
                            return Err(invalid(pc));
                        }
                        previous = Some(key);
                        target(targets, pc, reader.u4()? as i32, code.len())?;
                    }
                }
            }
            178..=185 => {
                operand = reader.u2()?;
                let reference = member(class, operand, opcode, pc)?;
                if opcode == 185 {
                    if reader.u1()? as usize
                        != method_descriptor(reference.descriptor)?.parameter_slots + 1
                        || reader.u1()? != 0
                    {
                        return Err(invalid(pc));
                    }
                }
            }
            186 => {
                operand = reader.u2()?;
                class.invoke_dynamic(operand)?;
                if reader.u2()? != 0 {
                    return Err(invalid(pc));
                }
            }
            187 | 189 | 192..=193 => {
                operand = reader.u2()?;
                let name = class.class(operand)?;
                if opcode == 187 {
                    valid_class_name(name)?;
                } else if name.starts_with('[') {
                    field_descriptor(name)?;
                } else {
                    valid_class_name(name)?;
                }
            }
            188 => {
                auxiliary = reader.u1()?;
                if !(4..=11).contains(&auxiliary) {
                    return Err(invalid(pc));
                }
            }
            196 => {
                auxiliary = reader.u1()?;
                operand = reader.u2()?;
                if !matches!(auxiliary,21..=25|54..=58|132|169) {
                    return Err(invalid(pc));
                }
                if auxiliary == 132 {
                    reader.u2()?;
                }
                local(
                    method,
                    operand,
                    if matches!(auxiliary, 22 | 24 | 55 | 57) {
                        2
                    } else {
                        1
                    },
                    pc,
                )?;
            }
            197 => {
                operand = reader.u2()?;
                auxiliary = reader.u1()?;
                let name = class.class(operand)?;
                field_descriptor(name)?;
                if auxiliary == 0
                    || auxiliary as usize > name.bytes().take_while(|byte| *byte == b'[').count()
                {
                    return Err(invalid(pc));
                }
            }
            200..=201 => {
                target(targets, pc, reader.u4()? as i32, code.len())?;
            }
            _ => return Err(invalid(pc)),
        }
        if matches!(opcode, 26..=45) {
            let family = (opcode - 26) / 4;
            local(
                method,
                ((opcode - 26) % 4) as u16,
                if matches!(family, 1 | 3) { 2 } else { 1 },
                pc,
            )?;
        }
        if matches!(opcode, 59..=78) {
            let family = (opcode - 59) / 4;
            local(
                method,
                ((opcode - 59) % 4) as u16,
                if matches!(family, 1 | 3) { 2 } else { 1 },
                pc,
            )?;
        }
        if (172..=177).contains(&opcode) {
            let valid = match opcode {
                172 => matches!(descriptor.return_type, "Z" | "B" | "C" | "S" | "I"),
                173 => descriptor.return_type == "J",
                174 => descriptor.return_type == "F",
                175 => descriptor.return_type == "D",
                176 => reference_type(descriptor.return_type),
                _ => descriptor.return_type == "V",
            };
            if !valid {
                return Err(invalid(pc));
            }
        }
        if reader.at == code.len()
            && !matches!(opcode,167|169..=177|191|200..=201)
            && !(opcode == 196 && auxiliary == 169)
        {
            return Err(invalid(pc));
        }
        instructions.push(Instruction {
            pc: pc as u32,
            operand,
            opcode,
            auxiliary,
        });
    }
    starts[code.len()] = true;
    if targets.iter().any(|target| !starts[*target]) {
        return Err(invalid(0));
    }
    let mut handlers = Reader::new(method.exception_table);
    for _ in 0..method.exception_handlers {
        let start = handlers.u2()? as usize;
        let end = handlers.u2()? as usize;
        let handler = handlers.u2()? as usize;
        let catch = handlers.u2()?;
        if start >= end
            || end > code.len()
            || handler >= code.len()
            || !starts[start]
            || !starts[end]
            || !starts[handler]
        {
            return Err(invalid(handler));
        }
        if catch != 0 {
            valid_class_name(class.class(catch)?)?;
        }
    }
    Ok(())
}
fn reflective(member: MemberRef<'_>) -> bool {
    member.owner.starts_with("java/lang/reflect/")
        || member.owner.starts_with("java/lang/invoke/")
        || member.owner == "java/util/ServiceLoader"
        || (member.owner == "java/lang/Class" && matches!(member.name, "forName" | "newInstance"))
        || ((member.owner == "java/lang/ClassLoader"
            || member.owner == "java/lang/System"
            || member.owner.ends_with("/Unsafe"))
            && matches!(
                member.name,
                "load"
                    | "loadLibrary"
                    | "loadClass"
                    | "findClass"
                    | "defineClass"
                    | "defineAnonymousClass"
                    | "allocateInstance"
            ))
}
fn is_open(class: &ClassFile<'_>, instruction: Instruction) -> bool {
    match instruction.opcode {
        // Only integer/long division and remainder can throw here. Floating
        // div/rem are IEEE 754 scalar operations, including a zero divisor:
        // https://docs.oracle.com/javase/specs/jvms/se21/html/jvms-6.html#jvms-6.5.ddiv
        46..=53
        | 79..=86
        | 108
        | 109
        | 112
        | 113
        | 168..=169
        | 188..=190
        | 194..=195
        | 197
        | 201 => true,
        196 => instruction.auxiliary == 169,
        18..=20 => matches!(
            class.pool[instruction.operand as usize],
            Constant::Dynamic { .. }
        ),
        182..=185 => class
            .member(instruction.operand, false)
            .is_ok_and(reflective),
        186 => class
            .invoke_dynamic(instruction.operand)
            .and_then(|dynamic| {
                class.lambda(
                    dynamic,
                    ValueRange {
                        start: 0,
                        len: dynamic.descriptor.parameter_count as u32,
                    },
                    instruction.pc,
                )
            })
            .is_err(),
        _ => false,
    }
}
fn project<'a>(
    class: &ClassFile<'a>,
    method: &MethodInfo<'a>,
    scan: &Scan,
    limits: Limits,
) -> Result<MethodSummary<'a>> {
    let mut out = project_coarse(class, method, scan, limits)?;
    aliases::refine(class, method, scan, limits, &mut out);
    Ok(out)
}
fn project_coarse<'a>(
    class: &ClassFile<'a>,
    method: &MethodInfo<'a>,
    scan: &Scan,
    limits: Limits,
) -> Result<MethodSummary<'a>> {
    let mut out = MethodSummary {
        descriptor: method.descriptor,
        values: Vec::new(),
        value_offsets: Vec::new(),
        calls: Vec::new(),
        arguments: Vec::new(),
        field_writes: Vec::new(),
        lambdas: Vec::new(),
        unknown_offsets: Vec::new(),
        returned: None,
        unknown: None,
        envelope: None,
    };
    let top = out.value(Value::UnknownData, limits, 0)?;
    if method.flags & 0x20 != 0 {
        out.unknown = Some(BinaryError::at(ErrorKind::UnsupportedOpcode(194), 0));
        out.unknown_offsets.push(0);
    }
    // Fallback operands deliberately remain unknown. It does not fabricate an
    // exact object/callback from a declared type or select one branch's alias.
    for instruction in &scan.instructions {
        let Instruction {
            pc,
            operand,
            opcode,
            ..
        } = *instruction;
        if is_open(class, *instruction) {
            out.unknown.get_or_insert(BinaryError::at(
                ErrorKind::UnsupportedOpcode(opcode),
                pc as usize,
            ));
            out.unknown_offsets.push(pc);
        }
        match opcode {
            178..=181 => {
                let member = class.member(operand, true)?;
                match opcode {
                    178 => {
                        out.value(Value::StaticField(member), limits, pc)?;
                    }
                    180 => {
                        out.value(
                            Value::Field {
                                member,
                                receiver: top,
                            },
                            limits,
                            pc,
                        )?;
                    }
                    _ => out.field_writes.push(FieldWrite {
                        member,
                        receiver: (opcode == 181).then_some(top),
                        value: top,
                        offset: pc,
                    }),
                }
            }
            182..=185 => {
                let member = class.member(operand, false)?;
                let descriptor = method_descriptor(member.descriptor)?;
                let first = out.arguments.len();
                if first
                    .checked_add(descriptor.parameter_count)
                    .is_none_or(|n| n > limits.max_values)
                {
                    return Err(BinaryError::at(ErrorKind::ResourceLimit, pc as usize));
                }
                out.arguments
                    .resize(first + descriptor.parameter_count, top);
                let index = out.calls.len();
                out.calls.push(Call {
                    member,
                    kind: match opcode {
                        182 => InvokeKind::Virtual,
                        183 => InvokeKind::Special,
                        184 => InvokeKind::Static,
                        _ => InvokeKind::Interface,
                    },
                    receiver: (opcode != 184).then_some(top),
                    arguments: ValueRange {
                        start: first as u32,
                        len: descriptor.parameter_count as u32,
                    },
                    offset: pc,
                });
                if descriptor.return_type != "V" {
                    out.value(Value::CallResult(index as u32), limits, pc)?;
                }
            }
            186 => {
                let dynamic = class.invoke_dynamic(operand)?;
                let first = out.arguments.len();
                let count = dynamic.descriptor.parameter_count;
                if first
                    .checked_add(count)
                    .is_none_or(|n| n > limits.max_values)
                {
                    return Err(BinaryError::at(ErrorKind::ResourceLimit, pc as usize));
                }
                out.arguments.resize(first + count, top);
                if let Ok(lambda) = class.lambda(
                    dynamic,
                    ValueRange {
                        start: first as u32,
                        len: count as u32,
                    },
                    pc,
                ) {
                    let index = out.lambdas.len();
                    out.lambdas.push(lambda);
                    out.value(Value::Lambda(index as u32), limits, pc)?;
                }
            }
            187 => {
                out.value(
                    Value::MayAllocation {
                        class: class.class(operand)?,
                        offset: pc,
                    },
                    limits,
                    pc,
                )?;
            }
            _ => {}
        }
        if out.calls.len() > limits.max_values
            || out.field_writes.len() > limits.max_values
            || out.lambdas.len() > limits.max_values
        {
            return Err(BinaryError::at(ErrorKind::ResourceLimit, pc as usize));
        }
    }
    out.returned = Some(
        if method_descriptor(method.descriptor)?.return_type == "V" {
            out.value(Value::Void, limits, method.code.unwrap().len() as u32)?
        } else {
            top
        },
    );
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    const PROBE: &[u8] =
        include_bytes!("../../../fixtures/native-envelope/classes/envelopecase/Probe.class");
    fn class() -> ClassFile<'static> {
        parse_class(PROBE, Limits::default()).unwrap()
    }
    #[test]
    fn floating_div_rem_zero_divisors_are_unknown_data_not_execution_frontiers() {
        let class = class();
        let original = *class.method("disjointScalar", None).unwrap();
        for (opcode, constant, returned, descriptor, stack) in [
            (110, 11, 174, "()F", 2), // fconst_0, fdiv, freturn
            (114, 11, 174, "()F", 2), // fconst_0, frem, freturn
            (111, 14, 175, "()D", 4), // dconst_0, ddiv, dreturn
            (115, 14, 175, "()D", 4), // dconst_0, drem, dreturn
        ] {
            let code = [constant, constant, opcode, returned];
            let method = MethodInfo {
                descriptor,
                code: Some(&code),
                max_stack: stack,
                max_locals: 0,
                ..original
            };
            let summary = summarize_with_envelope(&class, &method, Limits::default());
            let envelope = summary.envelope.unwrap();
            assert!(envelope.structurally_complete);
            assert!(summary.complete(), "opcode {opcode}: {:?}", summary.unknown);
            assert_eq!(envelope.open_channels, 0);
            assert!(summary.unknown_offsets.is_empty());
            assert!(summary.calls.is_empty() && summary.field_writes.is_empty());
            assert_eq!(
                summary.values[summary.returned.unwrap().0 as usize],
                Value::UnknownData
            );
        }
        for (opcode, constant, returned, descriptor, stack) in [
            (108, 3, 172, "()I", 2), // iconst_0, idiv, ireturn
            (112, 3, 172, "()I", 2), // iconst_0, irem, ireturn
            (109, 9, 173, "()J", 4), // lconst_0, ldiv, lreturn
            (113, 9, 173, "()J", 4), // lconst_0, lrem, lreturn
        ] {
            let code = [constant, constant, opcode, returned];
            let method = MethodInfo {
                descriptor,
                code: Some(&code),
                max_stack: stack,
                max_locals: 0,
                ..original
            };
            let summary = summarize_with_envelope(&class, &method, Limits::default());
            assert!(summary.envelope.unwrap().structurally_complete);
            assert!(!summary.complete(), "integer opcode {opcode} stays open");
            assert_eq!(summary.unknown_offsets, [2]);
            assert_eq!(summary.envelope.unwrap().open_channels, 1);
        }
    }
    #[test]
    fn floating_prefix_preserves_calls_writes_handlers_and_other_open_channels() {
        let class = class();
        for name in [
            "reset",
            "branch",
            "sparseSwitch",
            "denseSwitch",
            "caught",
            "monitor",
            "array",
            "reflection",
            "invokesMissing",
        ] {
            let original = *class.method(name, None).unwrap();
            let baseline = summarize_with_envelope(&class, &original, Limits::default());
            // Four bytes preserve switch alignment and all relative branch
            // offsets. No original instruction, effect, or handler is removed.
            let mut code = vec![11, 11, 110, 87]; // 0f / 0f; pop
            code.extend_from_slice(original.code.unwrap());
            let mut handlers = original.exception_table.to_vec();
            for handler in handlers.chunks_exact_mut(8) {
                for field in handler[..6].chunks_exact_mut(2) {
                    let offset = u16::from_be_bytes([field[0], field[1]]) + 4;
                    field.copy_from_slice(&offset.to_be_bytes());
                }
            }
            let method = MethodInfo {
                code: Some(&code),
                exception_table: &handlers,
                max_stack: original.max_stack.max(2),
                ..original
            };
            let summary = summarize_with_envelope(&class, &method, Limits::default());
            assert!(summary.envelope.unwrap().structurally_complete, "{name}");
            assert_eq!(summary.complete(), baseline.complete(), "{name}");
            assert_eq!(summary.calls.len(), baseline.calls.len(), "{name}");
            for (actual, expected) in summary.calls.iter().zip(&baseline.calls) {
                assert_eq!(actual.member, expected.member, "{name}");
                assert_eq!(actual.kind, expected.kind, "{name}");
                assert_eq!(actual.offset, expected.offset + 4, "{name}");
            }
            assert_eq!(
                summary.field_writes.len(),
                baseline.field_writes.len(),
                "{name}"
            );
            for (actual, expected) in summary.field_writes.iter().zip(&baseline.field_writes) {
                assert_eq!(actual.member, expected.member, "{name}");
                assert_eq!(
                    actual.receiver.is_some(),
                    expected.receiver.is_some(),
                    "{name}"
                );
                assert_eq!(actual.offset, expected.offset + 4, "{name}");
            }
            assert_eq!(
                summary.unknown_offsets,
                baseline
                    .unknown_offsets
                    .iter()
                    .map(|pc| pc + 4)
                    .collect::<Vec<_>>(),
                "{name}"
            );
        }
    }
    #[test]
    fn genuine_branch_switch_and_handler_envelopes_include_hidden_static_calls() {
        let class = class();
        for name in ["branch", "sparseSwitch", "denseSwitch", "caught"] {
            let method = class.method(name, None).unwrap();
            let summary = summarize_with_envelope(&class, method, Limits::default());
            assert!(
                summary.envelope.unwrap().structurally_complete,
                "{name}: {:?}",
                summary.unknown
            );
            assert!(
                summary
                    .calls
                    .iter()
                    .any(|call| call.member.owner == "envelopecase/Probe"
                        && call.member.name == "changed"),
                "hidden call in {name}"
            );
            assert!(summary.complete(), "{name}: {:?}", summary.unknown);
            assert!(summary.values.contains(&Value::UnknownData));
            if name == "caught" {
                assert!(method.exception_handlers > 0);
                assert!(summary.values.iter().any(|value| matches!(
                    value,
                    Value::MayAllocation {
                        class: "java/lang/IllegalArgumentException",
                        ..
                    }
                )));
            }
        }
    }
    #[test]
    fn genuine_scalar_data_can_be_unknown_while_external_channels_stay_open() {
        let class = class();
        let scalar = summarize_with_envelope(
            &class,
            class.method("disjointScalar", None).unwrap(),
            Limits::default(),
        );
        assert!(scalar.complete());
        assert!(scalar.calls.is_empty() && scalar.field_writes.is_empty());
        assert_eq!(
            scalar.values[scalar.returned.unwrap().0 as usize],
            Value::UnknownData
        );
        for name in ["reflection", "array", "monitor", "missing"] {
            let summary = summarize_with_envelope(
                &class,
                class.method(name, None).unwrap(),
                Limits::default(),
            );
            assert!(!summary.complete(), "{name} cannot be closed");
            if name == "monitor" {
                assert!(
                    summary
                        .calls
                        .iter()
                        .any(|call| call.member.name == "changed"),
                    "an open channel cannot truncate later effects"
                );
            }
        }
        let escaped = summarize_with_envelope(
            &class,
            class.method("invokeEscaped", None).unwrap(),
            Limits::default(),
        );
        assert!(
            escaped
                .calls
                .iter()
                .any(|call| call.member.owner == "java/lang/Runnable" && call.member.name == "run")
        );
        assert!(
            escaped
                .values
                .iter()
                .any(|value| matches!(value, Value::StaticField(_)))
        );
    }
    #[test]
    fn boundary_constant_pool_handler_and_budget_corruption_never_close_a_prefix() {
        let class = class();
        let original = *class.method("branch", None).unwrap();
        for case in 0..4 {
            let mut code = original.code.unwrap().to_vec();
            match case {
                0 => {
                    code[2] = 0;
                    code[3] = 1;
                }
                1 => {
                    code[5] = 0xff;
                    code[6] = 0xff;
                }
                2 => {
                    code.pop();
                }
                _ => {
                    code[1] = 0xcb;
                }
            }
            let method = MethodInfo {
                code: Some(&code),
                ..original
            };
            let summary = summarize_with_envelope(&class, &method, Limits::default());
            assert!(!summary.complete(), "corrupt case {case}");
            assert!(!summary.envelope.unwrap().structurally_complete);
        }
        let original = *class.method("caught", None).unwrap();
        let mut table = original.exception_table.to_vec();
        table[4] = 0;
        table[5] = 2; // inside the first conditional's operand, not an instruction
        let method = MethodInfo {
            exception_table: &table,
            ..original
        };
        assert!(!summarize_with_envelope(&class, &method, Limits::default()).complete());
        let limited = Limits {
            max_steps: 1,
            ..Limits::default()
        };
        let summary =
            summarize_with_envelope(&class, class.method("branch", None).unwrap(), limited);
        assert_eq!(summary.unknown.unwrap().kind, ErrorKind::ResourceLimit);
        assert!(!summary.envelope.unwrap().structurally_complete);
        let sync = MethodInfo {
            flags: original.flags | 0x20,
            ..original
        };
        assert!(!summarize_with_envelope(&class, &sync, Limits::default()).complete());
    }
    #[test]
    fn shared_decode_cache_is_class_method_and_budget_bound_without_class_borrows() {
        let class = class();
        let hash = ContentHash(Sha256::digest(PROBE).into());
        let mut cache = EnvelopeCache::new(1024 * 1024);
        for _ in 0..3 {
            assert!(
                cache
                    .summarize(
                        &class,
                        class.method("branch", None).unwrap(),
                        hash,
                        Limits::default()
                    )
                    .complete()
            );
        }
        let metrics = cache.metrics();
        assert_eq!(metrics.decoded_methods, 1);
        assert_eq!(metrics.decode_cache_hits, 2);
        assert!(metrics.retained_decode_bytes <= 1024 * 1024);
        let shadow = include_bytes!(
            "../../../fixtures/native-envelope/shadow-classes/envelopecase/Probe.class"
        );
        let shadow_class = parse_class(shadow, Limits::default()).unwrap();
        let summary = cache.summarize(
            &shadow_class,
            shadow_class.method("branch", None).unwrap(),
            ContentHash(Sha256::digest(shadow).into()),
            Limits::default(),
        );
        assert!(
            !summary
                .calls
                .iter()
                .any(|call| call.member.name == "changed")
        );
        assert_eq!(cache.metrics().decode_cache_hits, 2);
        let mut no_cache = EnvelopeCache::new(1);
        no_cache.summarize(
            &class,
            class.method("branch", None).unwrap(),
            hash,
            Limits::default(),
        );
        assert_eq!(no_cache.metrics().retained_decode_bytes, 0);
    }
    #[test]
    fn malformed_switch_payloads_and_indirect_constants_remain_open() {
        let class = class();
        for name in ["sparseSwitch", "denseSwitch"] {
            let original = *class.method(name, None).unwrap();
            // Both genuine javac switches begin at PC 1, then two padding bytes
            // and a signed default displacement. Targets into padding are bad.
            assert!(matches!(original.code.unwrap()[1], 170 | 171));
            for padding in [true, false] {
                let mut code = original.code.unwrap().to_vec();
                if padding {
                    code[2] = 1;
                } else {
                    code[4..8].copy_from_slice(&2i32.to_be_bytes());
                }
                let method = MethodInfo {
                    code: Some(&code),
                    ..original
                };
                let summary = summarize_with_envelope(&class, &method, Limits::default());
                assert!(!summary.complete());
                assert!(!summary.envelope.unwrap().structurally_complete);
            }
        }
        let mut malformed_class = self::class();
        let entry = malformed_class
            .pool
            .iter_mut()
            .find(|entry| matches!(entry, Constant::String(_)))
            .unwrap();
        *entry = Constant::String(u16::MAX);
        let method = malformed_class.method("caught", None).unwrap();
        assert!(!summarize_with_envelope(&malformed_class, method, Limits::default()).complete());
    }
}
