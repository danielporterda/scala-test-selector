//! Producer-side layout normalization. Value coordinates stay in their owning
//! method; only flat origin/value rows and the ranges addressing them move.
use crate::*;
use std::mem::size_of;

/// A scalar row mapping, not semantic authority. Identity layouts need no heap.
pub struct OriginRemap {
    rows: u32,
    map: Option<Vec<u32>>,
}
impl OriginRemap {
    pub fn row(&self, old: u32) -> Option<u32> {
        if old >= self.rows {
            return None;
        }
        Some(self.map.as_ref().map_or(old, |m| m[old as usize]))
    }
    pub fn range(&self, old: Range) -> Result<Range, Error> {
        let indices = old
            .checked(self.rows as usize)
            .map_err(|_| Error::Invalid("origin remap range"))?;
        if old.len == 0 {
            return Ok(Range::EMPTY);
        }
        let start = self
            .row(old.start)
            .ok_or(Error::Invalid("origin remap start"))?;
        for (offset, index) in indices.enumerate() {
            if self.row(index as u32) != start.checked_add(offset as u32) {
                return Err(Error::Invalid("origin remap not contiguous"));
            }
        }
        Ok(Range {
            start,
            len: old.len,
        })
    }
    pub fn owned_bytes(&self) -> usize {
        self.map
            .as_ref()
            .map_or(0, |m| m.capacity() * size_of::<u32>())
    }
    pub fn is_identity(&self) -> bool {
        self.map.is_none()
    }
}

fn own_rows(range: Range, next: &mut u32, count: usize) -> Result<(), Error> {
    range
        .checked(count)
        .map_err(|_| Error::Invalid("producer row range"))?;
    if range.len != 0 {
        if range.start != *next {
            return Err(Error::Invalid("producer row partition"));
        }
        *next = next
            .checked_add(range.len)
            .ok_or(Error::Limit("producer row count"))?;
    }
    Ok(())
}
fn layout(data: &CapsuleData) -> Result<bool, Error> {
    let n = data.origins.len();
    if n >= NONE as usize || n != data.callable_values.len() {
        return Err(Error::Invalid("parallel origin/value geometry"));
    }
    let mut call_next = 0;
    let mut creation_next = 0;
    let mut total = 0u32;
    let mut canonical = true;
    for method in &data.methods {
        own_rows(method.calls, &mut call_next, data.calls.len())?;
        own_rows(method.creations, &mut creation_next, data.creations.len())?;
        for range in method
            .calls
            .checked(data.calls.len())
            .map_err(|_| Error::Invalid("producer call range"))?
            .flat_map(|i| [data.calls[i].arguments, data.calls[i].captures])
            .chain(
                method
                    .creations
                    .checked(data.creations.len())
                    .map_err(|_| Error::Invalid("producer creation range"))?
                    .map(|i| data.creations[i].captures),
            )
        {
            range
                .checked(n)
                .map_err(|_| Error::Invalid("producer origin range"))?;
            if range.len != 0 {
                canonical &= range.start == total;
                total = total
                    .checked_add(range.len)
                    .ok_or(Error::Limit("producer origin count"))?;
            }
        }
    }
    if call_next as usize != data.calls.len()
        || creation_next as usize != data.creations.len()
        || total as usize != n
    {
        return Err(Error::Invalid("unowned producer rows"));
    }
    Ok(canonical)
}

/// Repack both parallel columns into method/call/creation order, without changing
/// any value coordinate or method/call/creation ID. Every input row must have one
/// owner: overlap, orphan rows and external padding fail closed. Failures leave
/// the DTO, headers and ranges untouched. Charge retained DTO + all three scratch
/// capacities before copying; the returned mapping remains part of the charge.
pub fn canonicalize_origins(
    data: &mut CapsuleData,
    max_owned_bytes: usize,
) -> Result<OriginRemap, Error> {
    let canonical = layout(data)?;
    let existing = data
        .owned_bytes()
        .map_err(|_| Error::Limit("producer DTO bytes"))?;
    if existing > max_owned_bytes {
        return Err(Error::Limit("producer DTO budget"));
    }
    let n = data.origins.len();
    if canonical {
        return Ok(OriginRemap {
            rows: n as u32,
            map: None,
        });
    }
    let scratch = n
        .checked_mul(size_of::<Origin>() + size_of::<ValueRef>() + size_of::<u32>())
        .and_then(|n| existing.checked_add(n))
        .ok_or(Error::Limit("origin repack bytes"))?;
    if scratch > max_owned_bytes {
        return Err(Error::Limit("origin repack preflight"));
    }
    let mut origins = Vec::<Origin>::new();
    let mut values = Vec::<ValueRef>::new();
    let mut map = Vec::<u32>::new();
    origins
        .try_reserve_exact(n)
        .map_err(|_| Error::Limit("origin repack capacity"))?;
    values
        .try_reserve_exact(n)
        .map_err(|_| Error::Limit("value repack capacity"))?;
    map.try_reserve_exact(n)
        .map_err(|_| Error::Limit("origin map capacity"))?;
    let scratch = origins
        .capacity()
        .checked_mul(size_of::<Origin>())
        .and_then(|b| {
            values
                .capacity()
                .checked_mul(size_of::<ValueRef>())
                .and_then(|v| b.checked_add(v))
        })
        .and_then(|b| {
            map.capacity()
                .checked_mul(size_of::<u32>())
                .and_then(|m| b.checked_add(m))
        })
        .and_then(|b| existing.checked_add(b))
        .ok_or(Error::Limit("origin repack capacity bytes"))?;
    if scratch > max_owned_bytes {
        return Err(Error::Limit("origin repack capacity budget"));
    }
    map.resize(n, NONE);
    for method in &data.methods {
        for range in method
            .calls
            .checked(data.calls.len())
            .expect("validated calls")
            .flat_map(|i| [data.calls[i].arguments, data.calls[i].captures])
            .chain(
                method
                    .creations
                    .checked(data.creations.len())
                    .expect("validated creations")
                    .map(|i| data.creations[i].captures),
            )
        {
            for index in range.checked(n).expect("validated origins") {
                if map[index] != NONE {
                    return Err(Error::Invalid("overlapping producer origins"));
                }
                map[index] = origins.len() as u32;
                origins.push(data.origins[index]);
                values.push(data.callable_values[index]);
            }
        }
    }
    if map.contains(&NONE) {
        return Err(Error::Invalid("orphan producer origins"));
    }
    let remap = OriginRemap {
        rows: n as u32,
        map: Some(map),
    };
    // All fallible remaps finish before the first mutation.
    for call in &data.calls {
        remap.range(call.arguments)?;
        remap.range(call.captures)?;
    }
    for creation in &data.creations {
        remap.range(creation.captures)?;
    }
    for call in &mut data.calls {
        call.arguments = remap
            .range(call.arguments)
            .expect("validated argument remap");
        call.captures = remap
            .range(call.captures)
            .expect("validated call capture remap");
    }
    for creation in &mut data.creations {
        creation.captures = remap
            .range(creation.captures)
            .expect("validated creation capture remap");
    }
    data.origins = origins;
    data.callable_values = values;
    Ok(remap)
}
