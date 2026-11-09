use crate::{Error, MethodAbi};
use std::collections::HashSet;
#[derive(Clone)]
pub(crate) struct Header {
    pub owner: String,
    pub flags: u16,
    pub methods: Vec<MethodAbi>,
    pub module_field: bool,
    pub source_file: Option<String>,
}
struct Reader<'a> {
    b: &'a [u8],
    p: usize,
}
impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8], Error> {
        let end = self
            .p
            .checked_add(n)
            .ok_or(Error::Invalid("classfile overflow"))?;
        let x = self
            .b
            .get(self.p..end)
            .ok_or(Error::Invalid("truncated classfile"))?;
        self.p = end;
        Ok(x)
    }
    fn u1(&mut self) -> Result<u8, Error> {
        Ok(self.take(1)?[0])
    }
    fn u2(&mut self) -> Result<u16, Error> {
        Ok(u16::from_be_bytes(self.take(2)?.try_into().unwrap()))
    }
    fn u4(&mut self) -> Result<u32, Error> {
        Ok(u32::from_be_bytes(self.take(4)?.try_into().unwrap()))
    }
    fn done(&self) -> Result<(), Error> {
        if self.p == self.b.len() {
            Ok(())
        } else {
            Err(Error::Invalid("classfile trailing bytes"))
        }
    }
}
#[derive(Clone)]
enum Cp {
    Empty,
    Utf(String),
    Class(u16),
    Other,
}
fn utf(cp: &[Cp], i: u16) -> Result<&str, Error> {
    match cp.get(i as usize) {
        Some(Cp::Utf(s)) => Ok(s),
        _ => Err(Error::Invalid("classfile UTF reference")),
    }
}
fn class(cp: &[Cp], i: u16) -> Result<&str, Error> {
    match cp.get(i as usize) {
        Some(Cp::Class(n)) => utf(cp, *n),
        _ => Err(Error::Invalid("classfile class reference")),
    }
}
fn mutf(b: &[u8]) -> Result<String, Error> {
    let mut units = Vec::new();
    let mut p = 0;
    while p < b.len() {
        let a = b[p];
        p += 1;
        let u = if a > 0 && a < 128 {
            a as u16
        } else if a & 0xe0 == 0xc0 {
            let c = *b.get(p).ok_or(Error::Invalid("truncated modified UTF8"))?;
            p += 1;
            if c & 0xc0 != 0x80 {
                return Err(Error::Invalid("modified UTF8 continuation"));
            }
            let u = (((a & 31) as u16) << 6) | (c & 63) as u16;
            if u < 128 && u != 0 {
                return Err(Error::Invalid("overlong modified UTF8"));
            }
            u
        } else if a & 0xf0 == 0xe0 {
            let c = *b.get(p).ok_or(Error::Invalid("truncated modified UTF8"))?;
            let d = *b
                .get(p + 1)
                .ok_or(Error::Invalid("truncated modified UTF8"))?;
            p += 2;
            if c & 0xc0 != 0x80 || d & 0xc0 != 0x80 {
                return Err(Error::Invalid("modified UTF8 continuation"));
            }
            let u = (((a & 15) as u16) << 12) | (((c & 63) as u16) << 6) | (d & 63) as u16;
            if u < 2048 {
                return Err(Error::Invalid("overlong modified UTF8"));
            }
            u
        } else {
            return Err(Error::Invalid("modified UTF8 lead"));
        };
        units.push(u);
    }
    String::from_utf16(&units).map_err(|_| Error::Invalid("unpaired classfile UTF16"))
}
fn attrs(r: &mut Reader<'_>, cp: &[Cp], mut code: Option<&mut bool>) -> Result<(), Error> {
    let n = r.u2()?;
    for _ in 0..n {
        let name = utf(cp, r.u2()?)?;
        let len = r.u4()? as usize;
        let bytes = r.take(len)?;
        if name == "Code" {
            let Some(ref mut seen) = code else { continue };
            if **seen {
                return Err(Error::Invalid("duplicate Code"));
            }
            **seen = true;
            let mut q = Reader { b: bytes, p: 0 };
            q.take(4)?;
            let size = q.u4()? as usize;
            if size == 0 || size > 65535 {
                return Err(Error::Invalid("Code bound"));
            }
            q.take(size)?;
            let n = q.u2()?;
            for _ in 0..n {
                let start = q.u2()? as usize;
                let end = q.u2()? as usize;
                let handler = q.u2()? as usize;
                let catch = q.u2()?;
                if start >= end || end > size || handler >= size {
                    return Err(Error::Invalid("Code handler range"));
                }
                if catch != 0 {
                    class(cp, catch)?;
                }
            }
            attrs(&mut q, cp, None)?;
            q.done()?;
        }
    }
    Ok(())
}
fn field_type(b: &[u8], p: &mut usize, void: bool) -> Result<(), Error> {
    let c = *b.get(*p).ok_or(Error::Invalid("descriptor truncated"))?;
    *p += 1;
    match c {
        b'V' if void => Ok(()),
        b'B' | b'C' | b'D' | b'F' | b'I' | b'J' | b'S' | b'Z' => Ok(()),
        b'L' => {
            let start = *p;
            while b.get(*p).is_some_and(|c| *c != b';') {
                if matches!(b[*p], b'.' | b'[' | b'(' | b')' | 0) {
                    return Err(Error::Invalid("descriptor class"));
                }
                *p += 1;
            }
            if *p == start || b.get(*p) != Some(&b';') {
                return Err(Error::Invalid("descriptor class"));
            }
            *p += 1;
            Ok(())
        }
        b'[' => {
            let mut rank = 1;
            while b.get(*p) == Some(&b'[') {
                rank += 1;
                *p += 1;
            }
            if rank > 255 {
                return Err(Error::Invalid("array rank"));
            }
            field_type(b, p, false)
        }
        _ => Err(Error::Invalid("descriptor type")),
    }
}
pub(crate) fn descriptor(s: &str) -> Result<(), Error> {
    let b = s.as_bytes();
    if b.first() != Some(&b'(') {
        return Err(Error::Invalid("method descriptor"));
    }
    let mut p = 1;
    while b.get(p) != Some(&b')') {
        field_type(b, &mut p, false)?;
    }
    p += 1;
    field_type(b, &mut p, true)?;
    if p != b.len() {
        return Err(Error::Invalid("descriptor suffix"));
    }
    Ok(())
}
pub(crate) fn parse(bytes: &[u8]) -> Result<Header, Error> {
    let mut r = Reader { b: bytes, p: 0 };
    if r.u4()? != 0xcafebabe {
        return Err(Error::Invalid("classfile magic"));
    }
    r.take(4)?;
    let n = r.u2()? as usize;
    if n == 0 {
        return Err(Error::Invalid("constant pool"));
    }
    let mut cp = vec![Cp::Empty; n];
    let mut i = 1;
    while i < n {
        let tag = r.u1()?;
        cp[i] = match tag {
            1 => {
                let n = r.u2()? as usize;
                Cp::Utf(mutf(r.take(n)?)?)
            }
            7 => Cp::Class(r.u2()?),
            3 | 4 => {
                r.take(4)?;
                Cp::Other
            }
            5 | 6 => {
                r.take(8)?;
                i += 1;
                if i >= n {
                    return Err(Error::Invalid("wide pool index"));
                }
                Cp::Other
            }
            8 | 16 | 19 | 20 => {
                r.take(2)?;
                Cp::Other
            }
            9..=12 | 17 | 18 => {
                r.take(4)?;
                Cp::Other
            }
            15 => {
                r.take(3)?;
                Cp::Other
            }
            _ => return Err(Error::Invalid("constant pool tag")),
        };
        i += 1;
    }
    let flags = r.u2()?;
    let owner = class(&cp, r.u2()?)?.to_owned();
    let parent = r.u2()?;
    if parent != 0 {
        class(&cp, parent)?;
    }
    for _ in 0..r.u2()? {
        class(&cp, r.u2()?)?;
    }
    let mut module_field = false;
    for _ in 0..r.u2()? {
        let f = r.u2()?;
        let name = utf(&cp, r.u2()?)?;
        let desc = utf(&cp, r.u2()?)?;
        if name == "MODULE$" && f & 8 != 0 && desc == format!("L{owner};") {
            module_field = true;
        }
        let mut p = 0;
        field_type(desc.as_bytes(), &mut p, false)?;
        if p != desc.len() {
            return Err(Error::Invalid("field descriptor"));
        }
        attrs(&mut r, &cp, None)?;
    }
    let mut methods = Vec::new();
    let mut keys = HashSet::new();
    for _ in 0..r.u2()? {
        let flags = r.u2()?;
        let name = utf(&cp, r.u2()?)?;
        let desc = utf(&cp, r.u2()?)?;
        descriptor(desc)?;
        if !keys.insert((name, desc)) {
            return Err(Error::Invalid("duplicate method ABI"));
        }
        let mut code = false;
        attrs(&mut r, &cp, Some(&mut code))?;
        if code && flags & (0x100 | 0x400) != 0 {
            return Err(Error::Invalid("native abstract Code"));
        }
        if !code && flags & (0x100 | 0x400) == 0 {
            return Err(Error::Invalid("missing Code"));
        }
        methods.push(MethodAbi {
            name: name.to_owned(),
            descriptor: desc.to_owned(),
            flags,
            has_code: code,
        });
    }
    let mut source_file = None;
    for _ in 0..r.u2()? {
        let attr = utf(&cp, r.u2()?)?;
        let n = r.u4()? as usize;
        let bytes = r.take(n)?;
        if attr == "SourceFile" {
            if source_file.is_some() || n != 2 {
                return Err(Error::Invalid("SourceFile attribute"));
            }
            source_file = Some(utf(&cp, u16::from_be_bytes(bytes.try_into().unwrap()))?.to_owned());
        }
    }
    r.done()?;
    Ok(Header {
        owner,
        flags,
        methods,
        module_field,
        source_file,
    })
}
