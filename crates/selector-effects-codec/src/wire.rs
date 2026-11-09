use crate::Error;
use selector_artifacts::Artifact;
use std::io::{self, Write};

pub(crate) struct Cursor<'a> {
    bytes: &'a [u8],
    at: usize,
}
impl<'a> Cursor<'a> {
    pub fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, at: 0 }
    }
    pub fn u32(&mut self) -> u32 {
        let end = self.at + 4;
        let value = u32::from_le_bytes(self.bytes[self.at..end].try_into().expect("admitted row"));
        self.at = end;
        value
    }
    pub fn hash(&mut self) -> [u8; 32] {
        let end = self.at + 32;
        let value = self.bytes[self.at..end].try_into().expect("admitted row");
        self.at = end;
        value
    }
    pub fn boolean(&mut self) -> Result<bool, Error> {
        match self.u32() {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(Error::Invalid("capsule boolean")),
        }
    }
}

pub(crate) struct Row<const N: usize> {
    bytes: [u8; N],
    at: usize,
}
impl<const N: usize> Row<N> {
    pub fn u32(&mut self, value: u32) {
        self.bytes[self.at..self.at + 4].copy_from_slice(&value.to_le_bytes());
        self.at += 4;
    }
    pub fn hash(&mut self, value: &[u8; 32]) {
        self.bytes[self.at..self.at + 32].copy_from_slice(value);
        self.at += 32;
    }
    pub fn bytes(&mut self, value: &[u8]) {
        self.bytes[self.at..self.at + value.len()].copy_from_slice(value);
        self.at += value.len();
    }
}
pub(crate) fn row<const N: usize>(
    out: &mut dyn Write,
    fill: impl FnOnce(&mut Row<N>),
) -> io::Result<()> {
    let mut value = Row {
        bytes: [0; N],
        at: 0,
    };
    fill(&mut value);
    assert_eq!(value.at, N, "codec row geometry");
    out.write_all(&value.bytes)
}

pub(crate) fn table(
    artifact: &Artifact,
    id: u32,
    width: usize,
    maximum: u32,
) -> Result<usize, Error> {
    let count = artifact.count(id)?;
    if count >= u64::from(u32::MAX) || count > u64::from(maximum) {
        return Err(Error::Limit("capsule row count"));
    }
    let count = usize::try_from(count).map_err(|_| Error::Limit("capsule table address space"))?;
    if count.checked_mul(width) != Some(artifact.section(id)?.len()) {
        return Err(Error::Invalid("capsule table geometry"));
    }
    Ok(count)
}

pub(crate) fn at(
    artifact: &Artifact,
    section: u32,
    index: u32,
    width: usize,
) -> Result<Cursor<'_>, Error> {
    let start = (index as usize)
        .checked_mul(width)
        .ok_or(Error::Limit("capsule row offset"))?;
    let end = start
        .checked_add(width)
        .ok_or(Error::Limit("capsule row end"))?;
    let bytes = artifact
        .section(section)?
        .get(start..end)
        .ok_or(Error::Invalid("capsule row reference"))?;
    Ok(Cursor::new(bytes))
}
