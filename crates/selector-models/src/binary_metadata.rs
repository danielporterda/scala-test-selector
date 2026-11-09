//! Owned native headers without self references. All text, code and exception
//! views are reconstructed from checked ranges into immutable class bytes.
use super::*;

#[derive(Clone, Copy, Debug, Default)]
struct Bytes {
    start: u32,
    len: u32,
}
impl Bytes {
    fn capture(owner: &[u8], value: &[u8]) -> Result<Self> {
        if value.is_empty() {
            return Ok(Self::default());
        }
        let start = (value.as_ptr() as usize)
            .checked_sub(owner.as_ptr() as usize)
            .ok_or(BinaryError::at(ErrorKind::BadConstant, 0))?;
        if start
            .checked_add(value.len())
            .is_none_or(|end| end > owner.len())
        {
            return Err(BinaryError::at(ErrorKind::BadConstant, start));
        }
        Ok(Self {
            start: u32::try_from(start)
                .map_err(|_| BinaryError::at(ErrorKind::ResourceLimit, 0))?,
            len: u32::try_from(value.len())
                .map_err(|_| BinaryError::at(ErrorKind::ResourceLimit, 0))?,
        })
    }
    fn get(self, owner: &[u8]) -> &[u8] {
        &owner[self.start as usize..self.start as usize + self.len as usize]
    }
    fn text(self, owner: &[u8]) -> &str {
        std::str::from_utf8(self.get(owner)).expect("checked immutable native metadata")
    }
}
#[derive(Clone, Copy, Debug)]
struct MethodRow {
    name: Bytes,
    descriptor: Bytes,
    code: Bytes,
    exceptions: Bytes,
    flags: u16,
    max_stack: u16,
    max_locals: u16,
    exception_handlers: u16,
}
#[derive(Clone, Copy, Debug)]
struct FieldRow {
    name: Bytes,
    descriptor: Bytes,
    flags: u16,
}
#[derive(Clone, Copy, Debug)]
pub struct ClassHeader<'a> {
    pub name: &'a str,
    pub parent: Option<&'a str>,
    pub flags: u16,
    pub major: u16,
    pub minor: u16,
}
/// One parse owns compact metadata; lookups allocate and parse nothing. This
/// content identity does not replace context-qualified provider admission.
#[derive(Debug)]
pub struct ClassMetadata {
    bytes: Arc<[u8]>,
    hash: ContentHash,
    name: Bytes,
    parent: Option<Bytes>,
    interfaces: Vec<Bytes>,
    methods: Vec<MethodRow>,
    fields: Vec<FieldRow>,
    method_order: Vec<u32>,
    field_order: Vec<u32>,
    flags: u16,
    major: u16,
    minor: u16,
}
impl ClassMetadata {
    pub fn new(bytes: Arc<[u8]>, limits: Limits) -> Result<Self> {
        let class = parse_class(&bytes, limits)?;
        let metadata_bytes = class
            .interfaces
            .len()
            .checked_mul(std::mem::size_of::<Bytes>())
            .and_then(|n| {
                n.checked_add(
                    class
                        .methods
                        .len()
                        .checked_mul(std::mem::size_of::<MethodRow>() + 4)?,
                )
            })
            .and_then(|n| {
                n.checked_add(
                    class
                        .fields
                        .len()
                        .checked_mul(std::mem::size_of::<FieldRow>() + 4)?,
                )
            })
            .and_then(|n| n.checked_add(bytes.len()))
            .and_then(|n| n.checked_add(std::mem::size_of::<Self>()))
            .ok_or(BinaryError::at(ErrorKind::ResourceLimit, 0))?;
        if metadata_bytes > limits.max_retained_bytes {
            return Err(BinaryError::at(ErrorKind::ResourceLimit, 0));
        }
        let mut interfaces = Vec::new();
        let mut methods = Vec::new();
        let mut fields = Vec::new();
        let mut method_order = Vec::new();
        let mut field_order = Vec::new();
        interfaces
            .try_reserve_exact(class.interfaces.len())
            .map_err(|_| BinaryError::at(ErrorKind::ResourceLimit, 0))?;
        methods
            .try_reserve_exact(class.methods.len())
            .map_err(|_| BinaryError::at(ErrorKind::ResourceLimit, 0))?;
        fields
            .try_reserve_exact(class.fields.len())
            .map_err(|_| BinaryError::at(ErrorKind::ResourceLimit, 0))?;
        method_order
            .try_reserve_exact(class.methods.len())
            .map_err(|_| BinaryError::at(ErrorKind::ResourceLimit, 0))?;
        field_order
            .try_reserve_exact(class.fields.len())
            .map_err(|_| BinaryError::at(ErrorKind::ResourceLimit, 0))?;
        for interface in &class.interfaces {
            interfaces.push(Bytes::capture(&bytes, interface.as_bytes())?);
        }
        for (index, method) in class.methods.iter().enumerate() {
            methods.push(MethodRow {
                name: Bytes::capture(&bytes, method.name.as_bytes())?,
                descriptor: Bytes::capture(&bytes, method.descriptor.as_bytes())?,
                code: Bytes::capture(&bytes, method.code.unwrap_or(&[]))?,
                exceptions: Bytes::capture(&bytes, method.exception_table)?,
                flags: method.flags,
                max_stack: method.max_stack,
                max_locals: method.max_locals,
                exception_handlers: method.exception_handlers,
            });
            method_order.push(index as u32);
        }
        for (index, field) in class.fields.iter().enumerate() {
            fields.push(FieldRow {
                name: Bytes::capture(&bytes, field.name.as_bytes())?,
                descriptor: Bytes::capture(&bytes, field.descriptor.as_bytes())?,
                flags: field.flags,
            });
            field_order.push(index as u32);
        }
        method_order.sort_unstable_by(|a, b| {
            let (a, b) = (methods[*a as usize], methods[*b as usize]);
            (a.name.get(&bytes), a.descriptor.get(&bytes))
                .cmp(&(b.name.get(&bytes), b.descriptor.get(&bytes)))
        });
        field_order.sort_unstable_by(|a, b| {
            let (a, b) = (fields[*a as usize], fields[*b as usize]);
            (a.name.get(&bytes), a.descriptor.get(&bytes))
                .cmp(&(b.name.get(&bytes), b.descriptor.get(&bytes)))
        });
        let name = Bytes::capture(&bytes, class.name.as_bytes())?;
        let parent = class
            .parent
            .map(|parent| Bytes::capture(&bytes, parent.as_bytes()))
            .transpose()?;
        let (flags, major, minor) = (class.flags, class.major, class.minor);
        let hash = ContentHash(Sha256::digest(&bytes).into());
        drop(class);
        Ok(Self {
            bytes,
            hash,
            name,
            parent,
            interfaces,
            methods,
            fields,
            method_order,
            field_order,
            flags,
            major,
            minor,
        })
    }
    pub fn hash(&self) -> ContentHash {
        self.hash
    }
    pub fn bytes(&self) -> &Arc<[u8]> {
        &self.bytes
    }
    pub fn name(&self) -> &str {
        self.name.text(&self.bytes)
    }
    pub fn parent(&self) -> Option<&str> {
        self.parent.map(|range| range.text(&self.bytes))
    }
    pub fn flags(&self) -> u16 {
        self.flags
    }
    pub fn header(&self) -> ClassHeader<'_> {
        ClassHeader {
            name: self.name(),
            parent: self.parent(),
            flags: self.flags,
            major: self.major,
            minor: self.minor,
        }
    }
    pub fn interfaces(&self) -> impl ExactSizeIterator<Item = &str> + DoubleEndedIterator {
        self.interfaces.iter().map(|range| range.text(&self.bytes))
    }
    fn method_view(&self, row: MethodRow) -> MethodInfo<'_> {
        MethodInfo {
            flags: row.flags,
            name: row.name.text(&self.bytes),
            descriptor: row.descriptor.text(&self.bytes),
            max_stack: row.max_stack,
            max_locals: row.max_locals,
            code: (row.code.len != 0).then(|| row.code.get(&self.bytes)),
            exception_handlers: row.exception_handlers,
            exception_table: row.exceptions.get(&self.bytes),
        }
    }
    fn field_view(&self, row: FieldRow) -> FieldInfo<'_> {
        FieldInfo {
            flags: row.flags,
            name: row.name.text(&self.bytes),
            descriptor: row.descriptor.text(&self.bytes),
        }
    }
    pub fn methods(&self) -> impl ExactSizeIterator<Item = MethodInfo<'_>> + DoubleEndedIterator {
        self.methods.iter().map(|row| self.method_view(*row))
    }
    pub fn fields(&self) -> impl ExactSizeIterator<Item = FieldInfo<'_>> + DoubleEndedIterator {
        self.fields.iter().map(|row| self.field_view(*row))
    }
    /// Stable classfile ordinal, useful for hash-bound method cache keys.
    pub fn method_index(&self, name: &str, descriptor: Option<&str>) -> Result<usize> {
        let compare = |id: &u32| {
            let row = self.methods[*id as usize];
            let by_name = row.name.get(&self.bytes).cmp(name.as_bytes());
            if by_name.is_eq() {
                descriptor.map_or(by_name, |descriptor| {
                    row.descriptor.get(&self.bytes).cmp(descriptor.as_bytes())
                })
            } else {
                by_name
            }
        };
        let start = self.method_order.partition_point(|id| compare(id).is_lt());
        let end = self.method_order.partition_point(|id| !compare(id).is_gt());
        if start == end {
            return Err(BinaryError::at(ErrorKind::MissingMethod, 0));
        }
        if end != start + 1 {
            return Err(BinaryError::at(ErrorKind::AmbiguousMethod, 0));
        }
        Ok(self.method_order[start] as usize)
    }
    pub fn method(&self, name: &str, descriptor: Option<&str>) -> Result<MethodInfo<'_>> {
        Ok(self.method_view(self.methods[self.method_index(name, descriptor)?]))
    }
    /// Exact field identity; duplicates are invalid class metadata, never a pick.
    pub fn field(&self, name: &str, descriptor: &str) -> Result<Option<FieldInfo<'_>>> {
        let compare = |id: &u32| {
            let row = self.fields[*id as usize];
            (row.name.get(&self.bytes), row.descriptor.get(&self.bytes))
                .cmp(&(name.as_bytes(), descriptor.as_bytes()))
        };
        let start = self.field_order.partition_point(|id| compare(id).is_lt());
        let end = self.field_order.partition_point(|id| !compare(id).is_gt());
        if start == end {
            return Ok(None);
        }
        if end != start + 1 {
            return Err(BinaryError::at(ErrorKind::BadConstant, 0));
        }
        Ok(Some(
            self.field_view(self.fields[self.field_order[start] as usize]),
        ))
    }
    /// Charges metadata separately when the caller already owns shared bytes.
    pub fn metadata_bytes(&self) -> usize {
        std::mem::size_of::<Self>()
            + self.interfaces.capacity() * std::mem::size_of::<Bytes>()
            + self.methods.capacity() * std::mem::size_of::<MethodRow>()
            + self.fields.capacity() * std::mem::size_of::<FieldRow>()
            + (self.method_order.capacity() + self.field_order.capacity()) * 4
    }
    pub fn owned_bytes(&self) -> usize {
        self.bytes.len() + self.metadata_bytes()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const PROBE: &[u8] = include_bytes!("../../../fixtures/binary/classes/fixture/Probe.class");
    #[test]
    fn owned_headers_and_exact_indexes_match_all_borrowed_metadata() {
        let bytes: Arc<[u8]> = Arc::from(PROBE);
        let class = parse_class(&bytes, Limits::default()).unwrap();
        let metadata = ClassMetadata::new(bytes.clone(), Limits::default()).unwrap();
        assert!(Arc::ptr_eq(metadata.bytes(), &bytes));
        assert_eq!(metadata.name(), class.name);
        assert_eq!(metadata.parent(), class.parent);
        assert_eq!(metadata.interfaces().collect::<Vec<_>>(), class.interfaces);
        assert_eq!(metadata.header().flags, class.flags);
        assert_eq!(metadata.hash(), ContentHash(Sha256::digest(PROBE).into()));
        for (index, original) in class.methods.iter().enumerate() {
            let method = metadata
                .method(original.name, Some(original.descriptor))
                .unwrap();
            assert_eq!(
                metadata
                    .method_index(original.name, Some(original.descriptor))
                    .unwrap(),
                index
            );
            assert_eq!(
                (
                    method.flags,
                    method.name,
                    method.descriptor,
                    method.max_stack,
                    method.max_locals,
                    method.code,
                    method.exception_table,
                    method.exception_handlers
                ),
                (
                    original.flags,
                    original.name,
                    original.descriptor,
                    original.max_stack,
                    original.max_locals,
                    original.code,
                    original.exception_table,
                    original.exception_handlers
                )
            );
        }
        for original in &class.fields {
            let field = metadata
                .field(original.name, original.descriptor)
                .unwrap()
                .unwrap();
            assert_eq!(
                (field.name, field.descriptor, field.flags),
                (original.name, original.descriptor, original.flags)
            );
        }
        assert_eq!(
            metadata.method("over", None).unwrap_err().kind,
            ErrorKind::AmbiguousMethod
        );
        assert_eq!(
            metadata.method("missing", None).unwrap_err().kind,
            ErrorKind::MissingMethod
        );
        assert!(metadata.field("missing", "I").unwrap().is_none());
    }
    #[test]
    fn warmed_headers_and_method_hits_do_not_reparse_constant_pool() {
        let before = class_parse_calls();
        let metadata = ClassMetadata::new(Arc::from(PROBE), Limits::default()).unwrap();
        assert_eq!(class_parse_calls(), before + 1);
        for _ in 0..10_000 {
            let method = std::hint::black_box(
                metadata
                    .method("make", Some("(Ljava/lang/Runnable;)Lfixture/Made;"))
                    .unwrap(),
            );
            assert!(method.code.is_some());
            std::hint::black_box(metadata.field("callback", "Ljava/lang/Runnable;").unwrap());
            assert!(metadata.method("notThere", None).is_err());
        }
        assert_eq!(
            class_parse_calls(),
            before + 1,
            "lookup must not parse class metadata again"
        );
    }
    #[test]
    fn metadata_lifetime_budget_and_malformed_inputs_are_explicit() {
        let metadata = {
            let temporary: Arc<[u8]> = Arc::from(PROBE);
            ClassMetadata::new(temporary, Limits::default()).unwrap()
        };
        assert_eq!(metadata.name(), "fixture/Probe");
        assert!(metadata.owned_bytes() > PROBE.len());
        assert!(
            ClassMetadata::new(
                Arc::from(PROBE),
                Limits {
                    max_retained_bytes: PROBE.len(),
                    ..Limits::default()
                }
            )
            .is_err()
        );
        assert!(
            ClassMetadata::new(Arc::from(&PROBE[..PROBE.len() - 1]), Limits::default()).is_err()
        );
        assert!(std::mem::size_of::<MethodRow>() <= 48);
    }
}
