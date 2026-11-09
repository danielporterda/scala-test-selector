use selector_types::{Error, Span};

/// Sparse UTF-16 -> UTF-8 mapping: ASCII sources allocate only a line index.
/// Non-ASCII characters retain one checkpoint each, rather than one offset per
/// source byte or UTF-16 code unit. Surrogate-pair splits are rejected.
pub struct SourceCoordinates {
    lines: Vec<(u32, u32)>, // absolute UTF-16 start and content length
    non_ascii: Vec<Checkpoint>,
    units: u32,
    bytes: u32,
}
struct Checkpoint {
    units: u32,
    bytes: u32,
    width: u32,
    byte_width: u32,
}
impl SourceCoordinates {
    pub fn new(source: &str) -> Result<Self, Error> {
        let bytes = u32::try_from(source.len()).map_err(|_| Error::Limit("source bytes"))?;
        let mut non_ascii = Vec::new();
        let mut units = 0u32;
        for (offset, ch) in source.char_indices() {
            if !ch.is_ascii() {
                non_ascii.push(Checkpoint {
                    units,
                    bytes: offset as u32,
                    width: ch.len_utf16() as u32,
                    byte_width: ch.len_utf8() as u32,
                });
            }
            units = units
                .checked_add(ch.len_utf16() as u32)
                .ok_or(Error::Limit("source UTF-16 units"))?;
        }
        let mut lines = Vec::new();
        let mut start = 0u32;
        for line in source.split_inclusive('\n') {
            let content = line.trim_end_matches(['\r', '\n']);
            lines.push((start, content.encode_utf16().count() as u32));
            start += line.encode_utf16().count() as u32;
        }
        if source.is_empty() || source.ends_with('\n') {
            lines.push((start, 0));
        }
        Ok(Self {
            lines,
            non_ascii,
            units,
            bytes,
        })
    }
    pub fn absolute(&self, offset: i64) -> Result<u32, Error> {
        let offset =
            u32::try_from(offset).map_err(|_| Error::Invalid("negative UTF-16 position"))?;
        if offset > self.units {
            return Err(Error::Invalid("UTF-16 position outside source"));
        }
        let end = self.non_ascii.partition_point(|c| c.units <= offset);
        if end == 0 {
            return Ok(offset);
        }
        let last = &self.non_ascii[end - 1];
        if offset > last.units && offset < last.units + last.width {
            return Err(Error::Invalid("UTF-16 position splits surrogate pair"));
        }
        if offset == last.units {
            return Ok(last.bytes);
        }
        Ok(last.bytes + last.byte_width + offset - last.units - last.width)
    }
    pub fn position(&self, line: i64, column: i64) -> Result<u32, Error> {
        let line = usize::try_from(line).map_err(|_| Error::Invalid("negative source line"))?;
        let column = u32::try_from(column).map_err(|_| Error::Invalid("negative source column"))?;
        let &(start, len) = self.lines.get(line).ok_or(Error::Invalid("source line"))?;
        if column > len {
            return Err(Error::Invalid("source column outside line"));
        }
        self.absolute((start + column) as i64)
    }
    pub fn span(&self, start: i64, end: i64) -> Result<Span, Error> {
        Span::new(self.absolute(start)? as usize, self.absolute(end)? as usize)
    }
    pub fn semantic_span(&self, r: [i64; 4]) -> Result<Span, Error> {
        Span::new(
            self.position(r[0], r[1])? as usize,
            self.position(r[2], r[3])? as usize,
        )
    }
    pub fn bytes(&self) -> u32 {
        self.bytes
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn sparse_unicode_positions() {
        let c = SourceCoordinates::new("a😀é\r\nxyz\n").unwrap();
        assert_eq!(c.position(0, 1).unwrap(), 1);
        assert!(c.position(0, 2).is_err());
        assert_eq!(c.position(0, 3).unwrap(), 5);
        assert_eq!(c.position(0, 4).unwrap(), 7);
        assert_eq!(c.position(1, 0).unwrap(), 9);
        assert_eq!(c.position(2, 0).unwrap(), 13);
        assert!(c.position(0, 5).is_err());
        assert!(c.span(4, 1).is_err());
    }
    #[test]
    fn empty_and_ascii() {
        let c = SourceCoordinates::new("").unwrap();
        assert_eq!(c.position(0, 0).unwrap(), 0);
        assert!(c.position(1, 0).is_err());
        assert_eq!(
            SourceCoordinates::new("ab\ncd")
                .unwrap()
                .position(1, 2)
                .unwrap(),
            5
        );
    }
}
