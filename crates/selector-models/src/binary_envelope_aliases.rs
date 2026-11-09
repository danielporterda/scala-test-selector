//! Bounded forward-control-flow value refinement of a complete may envelope.
//! Effects remain the original structural scan's rows, including unreachable
//! branches. Any unsupported control/data shape discards the entire refinement.
use super::*;

const MAX_INSTRUCTIONS: usize = 512;
const MAX_SLOTS: usize = 256;
const MAX_PATHS: usize = 128;
const MAX_ALTERNATIVES: usize = 64;
const MAX_STEPS: usize = 8192;
const MAX_OPERANDS: usize = 4096;
const MAX_MERGED_OPERANDS: usize = 16_384;
#[derive(Clone, Copy)]
struct Slot {
    id: BinaryValueId,
    width: u8,
}
#[derive(Clone)]
struct State {
    at: usize,
    stack: Vec<Slot>,
    locals: Vec<Option<Slot>>,
}
impl State {
    fn pop(&mut self, width: u8) -> Option<Slot> {
        let value = self.stack.pop()?;
        (value.width == width).then_some(value)
    }
    fn push(&mut self, value: Slot, maximum: usize) -> Option<()> {
        if self.stack.iter().map(|v| v.width as usize).sum::<usize>() + value.width as usize
            > maximum
        {
            return None;
        }
        self.stack.push(value);
        Some(())
    }
}
fn add(rows: &mut Vec<BinaryValueId>, id: BinaryValueId, top: BinaryValueId) {
    if rows == &[top] {
        return;
    }
    if let Err(index) = rows.binary_search_by_key(&id.0, |v| v.0) {
        if rows.len() == MAX_ALTERNATIVES {
            rows.clear();
            rows.push(top);
        } else {
            rows.insert(index, id);
        }
    }
}
fn merged<'a>(
    out: &mut MethodSummary<'a>,
    rows: &[BinaryValueId],
    pc: u32,
    limits: Limits,
) -> Option<BinaryValueId> {
    match rows {
        [] => None,
        [one] => Some(*one),
        _ => {
            let start = out.arguments.len();
            if start.checked_add(rows.len())? > limits.max_values.min(MAX_MERGED_OPERANDS) {
                return None;
            }
            out.arguments.extend_from_slice(rows);
            out.value(
                Value::Alternatives(ValueRange {
                    start: start as u32,
                    len: rows.len() as u32,
                }),
                limits,
                pc,
            )
            .ok()
        }
    }
}
/// The caps bound retained path slots to at most128*(256+256) and origins to
/// at most64 per operand. There is one shared instruction/producer index; path
/// states contain only numeric slots. Loops and handlers retain the old TOP.
pub(super) fn refine<'a>(
    class: &ClassFile<'a>,
    method: &MethodInfo<'a>,
    scan: &Scan,
    limits: Limits,
    out: &mut MethodSummary<'a>,
) {
    if scan.instructions.len() > MAX_INSTRUCTIONS
        || method.max_locals as usize > MAX_SLOTS
        || method.max_stack as usize > MAX_SLOTS
        || method.exception_handlers != 0
        || out.arguments.len() > MAX_OPERANDS
        || scan.instructions.iter().any(|i| {
            !matches!(i.opcode, 0..=45 | 54..=78 | 87..=89 | 95..=167 | 170..=187 | 191..=193 | 198..=200)
                && !(i.opcode == 196 && matches!(i.auxiliary, 21..=25 | 54..=58 | 132))
        })
    {
        return;
    }
    let mut candidate = out.clone();
    if analyze(class, method, scan, limits, &mut candidate).is_some() {
        *out = candidate;
    }
}
fn analyze<'a>(
    class: &ClassFile<'a>,
    method: &MethodInfo<'a>,
    scan: &Scan,
    limits: Limits,
    out: &mut MethodSummary<'a>,
) -> Option<()> {
    let code = method.code?;
    let descriptor = method_descriptor(method.descriptor).ok()?;
    let top = out
        .values
        .iter()
        .position(|v| matches!(v, Value::UnknownData))
        .map(|i| BinaryValueId(i as u32))?;
    let original_values = out.values.len();
    let mut producers = vec![None; scan.instructions.len()];
    let mut calls = vec![None; scan.instructions.len()];
    let mut writes = vec![None; scan.instructions.len()];
    // Envelope rows are in bytecode order. Share three linear numeric indexes
    // rather than rescanning every producer/call/write for every path step.
    let mut cursor = 0;
    for (id, (value, pc)) in out.values.iter().zip(&out.value_offsets).enumerate() {
        if !matches!(
            value,
            Value::StaticField(_)
                | Value::Field { .. }
                | Value::CallResult(_)
                | Value::MayAllocation { .. }
                | Value::Lambda(_)
        ) {
            continue;
        }
        while scan.instructions.get(cursor)?.pc < *pc {
            cursor += 1;
        }
        if scan.instructions.get(cursor)?.pc != *pc {
            return None;
        }
        producers[cursor] = Some(BinaryValueId(id as u32));
    }
    cursor = 0;
    for (id, call) in out.calls.iter().enumerate() {
        while scan.instructions.get(cursor)?.pc < call.offset {
            cursor += 1;
        }
        if scan.instructions.get(cursor)?.pc != call.offset {
            return None;
        }
        calls[cursor] = Some(id);
    }
    cursor = 0;
    for (id, write) in out.field_writes.iter().enumerate() {
        while scan.instructions.get(cursor)?.pc < write.offset {
            cursor += 1;
        }
        if scan.instructions.get(cursor)?.pc != write.offset {
            return None;
        }
        writes[cursor] = Some(id);
    }
    let mut state = State {
        at: 0,
        stack: Vec::new(),
        locals: vec![None; method.max_locals as usize],
    };
    let mut local = 0;
    if method.flags & 8 == 0 {
        let id = out.value(Value::Receiver, limits, 0).ok()?;
        *state.locals.get_mut(0)? = Some(Slot { id, width: 1 });
        local = 1;
    }
    for (i, parameter) in descriptor.parameters().enumerate() {
        let width = width(parameter);
        let id = out.value(Value::Argument(i as u16), limits, 0).ok()?;
        *state.locals.get_mut(local)? = Some(Slot { id, width });
        local += width as usize;
    }
    let mut field_receivers = vec![Vec::new(); original_values];
    let mut call_receivers = vec![Vec::new(); out.calls.len()];
    let mut arguments = vec![Vec::new(); out.arguments.len()];
    let mut write_receivers = vec![Vec::new(); out.field_writes.len()];
    let mut write_values = vec![Vec::new(); out.field_writes.len()];
    let mut returned = Vec::new();
    let mut pending = Vec::new();
    let mut paths = 1usize;
    let mut steps = 0usize;
    loop {
        let at = state.at;
        let instruction = *scan.instructions.get(at)?;
        let pc = instruction.pc;
        steps += 1;
        if steps > limits.max_steps.min(MAX_STEPS) {
            return None;
        }
        let mut targets = Vec::new();
        let mut terminal = false;
        let op = if instruction.opcode == 196 {
            instruction.auxiliary
        } else {
            instruction.opcode
        };
        let push = |state: &mut State, id, width| {
            state.push(Slot { id, width }, method.max_stack as usize)
        };
        match op {
            0 => (),
            1..=20 => {
                let width = if matches!(op, 9 | 10 | 14 | 15 | 20) {
                    2
                } else {
                    1
                };
                let id = if let Some(id) = producers[at] {
                    id
                } else {
                    let id = if matches!(op, 18..=20)
                        && !matches!(
                            class.pool.get(instruction.operand as usize)?,
                            Constant::Integer(_) | Constant::Number(_) | Constant::WideNumber(_)
                        ) {
                        // Reference ldc values have no exact object model. EMPTY
                        // would silently erase receivers/returns; retain TOP.
                        top
                    } else {
                        let value = if op == 1 {
                            Value::Null
                        } else {
                            Value::Constant {
                                pool_index: instruction.operand,
                                wide: width == 2,
                            }
                        };
                        out.value(value, limits, pc).ok()?
                    };
                    producers[at] = Some(id);
                    id
                };
                push(&mut state, id, width)?;
            }
            21..=45 => {
                let (index, width) = if op <= 25 {
                    (
                        instruction.operand as usize,
                        if matches!(op, 22 | 24) { 2 } else { 1 },
                    )
                } else {
                    (
                        ((op - 26) % 4) as usize,
                        if matches!((op - 26) / 4, 1 | 3) { 2 } else { 1 },
                    )
                };
                let slot = (*state.locals.get(index)?)?;
                if slot.width != width {
                    return None;
                }
                state.push(slot, method.max_stack as usize)?;
            }
            54..=78 => {
                let (index, width) = if op <= 58 {
                    (
                        instruction.operand as usize,
                        if matches!(op, 55 | 57) { 2 } else { 1 },
                    )
                } else {
                    (
                        ((op - 59) % 4) as usize,
                        if matches!((op - 59) / 4, 1 | 3) { 2 } else { 1 },
                    )
                };
                let value = state.pop(width)?;
                *state.locals.get_mut(index)? = Some(value);
                if width == 2 {
                    *state.locals.get_mut(index + 1)? = None;
                }
                // Overwriting the second half invalidates a former wide local.
                if index > 0 && state.locals[index - 1].is_some_and(|v| v.width == 2) {
                    state.locals[index - 1] = None;
                }
            }
            87 => {
                state.pop(1)?;
            }
            88 => {
                let a = state.stack.pop()?;
                if a.width == 1 {
                    state.pop(1)?;
                }
            }
            89 => {
                let a = state.pop(1)?;
                state.push(a, method.max_stack as usize)?;
                state.push(a, method.max_stack as usize)?;
            }
            95 => {
                let a = state.pop(1)?;
                let b = state.pop(1)?;
                state.push(a, method.max_stack as usize)?;
                state.push(b, method.max_stack as usize)?;
            }
            96..=115 => {
                let w = if matches!((op - 96) % 4, 1 | 3) { 2 } else { 1 };
                state.pop(w)?;
                state.pop(w)?;
                push(&mut state, top, w)?;
            }
            116..=119 => {
                let w = if matches!(op - 116, 1 | 3) { 2 } else { 1 };
                state.pop(w)?;
                push(&mut state, top, w)?;
            }
            120..=125 => {
                let w = if (op - 120) % 2 == 1 { 2 } else { 1 };
                state.pop(1)?;
                state.pop(w)?;
                push(&mut state, top, w)?;
            }
            126..=131 => {
                let w = if (op - 126) % 2 == 1 { 2 } else { 1 };
                state.pop(w)?;
                state.pop(w)?;
                push(&mut state, top, w)?;
            }
            132 => {
                let index = instruction.operand as usize;
                if state.locals.get(index)?.is_none_or(|slot| slot.width != 1) {
                    return None;
                }
                *state.locals.get_mut(index)? = Some(Slot { id: top, width: 1 });
                if index > 0 && state.locals[index - 1].is_some_and(|slot| slot.width == 2) {
                    return None;
                }
            }
            133..=147 => {
                let (from, to) = [
                    (1, 2),
                    (1, 1),
                    (1, 2),
                    (2, 1),
                    (2, 1),
                    (2, 2),
                    (1, 1),
                    (1, 2),
                    (1, 2),
                    (2, 1),
                    (2, 2),
                    (2, 1),
                    (1, 1),
                    (1, 1),
                    (1, 1),
                ][(op - 133) as usize];
                state.pop(from)?;
                push(&mut state, top, to)?;
            }
            148..=152 => {
                let w = if matches!(op, 149 | 150) { 1 } else { 2 };
                state.pop(w)?;
                state.pop(w)?;
                push(&mut state, top, 1)?;
            }
            153..=167 | 198..=200 => {
                if matches!(op, 153..=158 | 198 | 199) {
                    state.pop(1)?;
                } else if matches!(op, 159..=166) {
                    state.pop(1)?;
                    state.pop(1)?;
                }
                let delta = if op == 200 {
                    i32::from_be_bytes(
                        code.get(pc as usize + 1..pc as usize + 5)?
                            .try_into()
                            .ok()?,
                    ) as i64
                } else {
                    i16::from_be_bytes(
                        code.get(pc as usize + 1..pc as usize + 3)?
                            .try_into()
                            .ok()?,
                    ) as i64
                };
                let target = (pc as i64).checked_add(delta)?;
                if target <= pc as i64 {
                    return None;
                }
                targets.push(
                    scan.instructions
                        .binary_search_by_key(&(target as u32), |i| i.pc)
                        .ok()?,
                );
                if matches!(op, 167 | 200) {
                    terminal = true;
                }
            }
            170 | 171 => {
                state.pop(1)?;
                let mut reader = Reader::new(code);
                reader.at = (pc as usize + 4) & !3;
                let default = reader.u4().ok()? as i32;
                let mut deltas = vec![default];
                if op == 170 {
                    let low = reader.u4().ok()? as i32;
                    let high = reader.u4().ok()? as i32;
                    let count = (high as i64).checked_sub(low as i64)?.checked_add(1)?;
                    if count < 1 || count as usize >= MAX_PATHS {
                        return None;
                    }
                    for _ in low..=high {
                        deltas.push(reader.u4().ok()? as i32);
                    }
                } else {
                    let count = reader.u4().ok()? as usize;
                    if count >= MAX_PATHS {
                        return None;
                    }
                    for _ in 0..count {
                        reader.u4().ok()?;
                        deltas.push(reader.u4().ok()? as i32);
                    }
                }
                for delta in deltas {
                    let target = (pc as i64).checked_add(delta as i64)?;
                    if target <= pc as i64 {
                        return None;
                    }
                    let index = scan
                        .instructions
                        .binary_search_by_key(&(target as u32), |i| i.pc)
                        .ok()?;
                    if !targets.contains(&index) {
                        targets.push(index);
                    }
                }
                terminal = true;
            }
            172..=177 => {
                let valid = match op {
                    172 => matches!(descriptor.return_type, "B" | "C" | "I" | "S" | "Z"),
                    173 => descriptor.return_type == "J",
                    174 => descriptor.return_type == "F",
                    175 => descriptor.return_type == "D",
                    176 => {
                        descriptor.return_type.starts_with('L')
                            || descriptor.return_type.starts_with('[')
                    }
                    _ => descriptor.return_type == "V",
                };
                if !valid {
                    return None;
                }
                let id = if op == 177 {
                    out.returned?
                } else {
                    state.pop(width(descriptor.return_type))?.id
                };
                if !state.stack.is_empty() {
                    return None;
                }
                add(&mut returned, id, top);
                terminal = true;
            }
            178..=181 => {
                let member = class.member(instruction.operand, true).ok()?;
                let w = width(field_descriptor(member.descriptor).ok()?);
                match op {
                    178 => {
                        push(&mut state, producers[at]?, w)?;
                    }
                    180 => {
                        let receiver = state.pop(1)?.id;
                        let id = producers[at]?;
                        add(&mut field_receivers[id.0 as usize], receiver, top);
                        push(&mut state, id, w)?;
                    }
                    _ => {
                        let value = state.pop(w)?.id;
                        let index = writes[at]?;
                        add(&mut write_values[index], value, top);
                        if op == 181 {
                            let receiver = state.pop(1)?.id;
                            add(&mut write_receivers[index], receiver, top);
                        }
                    }
                }
            }
            182..=186 => {
                let (desc, range) = if op == 186 {
                    let desc = class.invoke_dynamic(instruction.operand).ok()?.descriptor;
                    let range = producers[at].and_then(|id| match out.values[id.0 as usize] {
                        Value::Lambda(i) => Some(out.lambdas[i as usize].captures),
                        _ => None,
                    });
                    (desc, range)
                } else {
                    let index = calls[at]?;
                    (
                        method_descriptor(out.calls[index].member.descriptor).ok()?,
                        Some(out.calls[index].arguments),
                    )
                };
                let mut actuals = Vec::with_capacity(desc.parameter_count);
                let widths: Vec<_> = desc.parameters().map(width).collect();
                for w in widths.into_iter().rev() {
                    actuals.push(state.pop(w)?.id);
                }
                actuals.reverse();
                if let Some(range) = range {
                    for (i, id) in range.range().zip(actuals) {
                        add(&mut arguments[i], id, top);
                    }
                }
                if op != 184 && op != 186 {
                    let receiver = state.pop(1)?.id;
                    add(&mut call_receivers[calls[at]?], receiver, top);
                }
                if desc.return_type != "V" {
                    push(
                        &mut state,
                        producers[at].unwrap_or(top),
                        width(desc.return_type),
                    )?;
                }
            }
            187 => {
                push(&mut state, producers[at]?, 1)?;
            }
            191 => {
                state.pop(1)?;
                terminal = true;
            }
            192 => {
                let value = state.pop(1)?;
                state.push(value, method.max_stack as usize)?;
            }
            193 => {
                state.pop(1)?;
                push(&mut state, top, 1)?;
            }
            _ => return None,
        }
        if !terminal {
            targets.push(state.at.checked_add(1)?);
        }
        if targets.is_empty() {
            if let Some(next) = pending.pop() {
                state = next;
                continue;
            }
            break;
        }
        state.at = targets.pop()?;
        for at in targets {
            paths += 1;
            if paths > MAX_PATHS {
                return None;
            }
            let mut other = state.clone();
            other.at = at;
            pending.push(other);
        }
    }
    if returned.is_empty() {
        return None;
    }
    // All reachable paths are complete. Only now refine existing operand rows;
    // unreachable structural effects keep their original unknown operands.
    for (i, rows) in field_receivers.iter().enumerate() {
        if !rows.is_empty() {
            let receiver = merged(out, rows, out.value_offsets[i], limits)?;
            if let Value::Field { receiver: old, .. } = &mut out.values[i] {
                *old = receiver;
            }
        }
    }
    for (i, rows) in call_receivers.iter().enumerate() {
        if !rows.is_empty() {
            out.calls[i].receiver = Some(merged(out, rows, out.calls[i].offset, limits)?);
        }
    }
    for (i, rows) in arguments.iter().enumerate() {
        if !rows.is_empty() {
            let pc = out
                .calls
                .iter()
                .find(|c| c.arguments.range().contains(&i))
                .map(|c| c.offset)
                .or_else(|| {
                    out.lambdas
                        .iter()
                        .find(|l| l.captures.range().contains(&i))
                        .map(|l| l.offset)
                })?;
            out.arguments[i] = merged(out, rows, pc, limits)?;
        }
    }
    for i in 0..out.field_writes.len() {
        let pc = out.field_writes[i].offset;
        if !write_values[i].is_empty() {
            out.field_writes[i].value = merged(out, &write_values[i], pc, limits)?;
        }
        if !write_receivers[i].is_empty() {
            out.field_writes[i].receiver = Some(merged(out, &write_receivers[i], pc, limits)?);
        }
    }
    out.returned = Some(merged(out, &returned, code.len() as u32, limits)?);
    Some(())
}

#[cfg(test)]
#[path = "binary_aliases_review_tests.rs"]
mod review_tests;

#[cfg(test)]
#[path = "binary_aliases_tests.rs"]
mod tests;
