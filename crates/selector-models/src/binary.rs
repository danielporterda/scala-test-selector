//! Bounded, hash-bound JVM classpath snapshots and straight-line value summaries.
//!
//! Class bytes, descriptors and code are borrowed during parsing/interpretation.
//! Values live in one flat arena; aliases (including `dup` before `<init>`) share
//! IDs. Unsupported bytecode keeps its known prefix and an explicit unknown.
//! Virtual calls describe receiver flow, never a proof of concrete dispatch.

#[path = "binary_envelope.rs"]
mod envelope;
pub use envelope::{EnvelopeCache, EnvelopeCoverage, EnvelopeMetrics, summarize_with_envelope};
#[path = "binary_metadata.rs"]
mod metadata;
pub use metadata::{ClassHeader, ClassMetadata};
/// Structural checks for independent diagnostic tools, without effect or admission authority.
#[path = "binary_diagnostic.rs"]
pub mod diagnostic;

use selector_types::ContentHash;
use sha2::{Digest, Sha256};
use std::fmt;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::sync::Arc;

#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub max_class_bytes: usize,
    pub max_archive_bytes: usize,
    pub max_retained_bytes: usize,
    pub max_directory_files: usize,
    pub max_directory_bytes: u64,
    pub max_code_bytes: usize,
    pub max_locals: usize,
    pub max_stack: usize,
    pub max_values: usize,
    pub max_steps: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            max_class_bytes: 16 * 1024 * 1024,
            max_archive_bytes: 128 * 1024 * 1024,
            max_retained_bytes: 256 * 1024 * 1024,
            max_directory_files: 250_000,
            max_directory_bytes: 8 * 1024 * 1024 * 1024,
            max_code_bytes: 65_535,
            max_locals: 4096,
            max_stack: 4096,
            max_values: 65_536,
            max_steps: 65_536,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    Truncated,
    BadMagic,
    BadConstant,
    UnsupportedConstant,
    InvalidUtf8,
    InvalidDescriptor,
    InvalidCode,
    DuplicateCode,
    DuplicateBootstrapMethods,
    UnsupportedBootstrap,
    TrailingBytes,
    ResourceLimit,
    MissingCode,
    ExceptionHandlers,
    StackUnderflow,
    InvalidStackCategory,
    InvalidLocal,
    InvalidReturn,
    UnsupportedOpcode(u8),
    DynamicConstant,
    UnknownReturn,
    NoReturn,
    MissingMethod,
    AmbiguousMethod,
    InvalidClassName,
    Io,
    HashMismatch,
    InvalidZip,
    UnsupportedZip,
    DuplicateZipMember,
    UnsupportedCompression,
    BadCrc,
    MultiReleaseArchive,
    UnsupportedClassVersion,
    ClassNotFound,
    ClassIdentityMismatch,
    DirectoryFingerprintMismatch,
    SourceOutputShadows,
    UnavailableInput,
    SymlinkInput,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BinaryError {
    pub kind: ErrorKind,
    pub offset: usize,
}
impl BinaryError {
    fn at(kind: ErrorKind, offset: usize) -> Self {
        Self { kind, offset }
    }
}
impl fmt::Display for BinaryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "binary input {:?} at byte {}", self.kind, self.offset)
    }
}
impl std::error::Error for BinaryError {}
type Result<T> = std::result::Result<T, BinaryError>;

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}
impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, at: 0 }
    }
    fn take(&mut self, n: usize) -> Result<&'a [u8]> {
        let end = self
            .at
            .checked_add(n)
            .ok_or(BinaryError::at(ErrorKind::Truncated, self.at))?;
        let value = self
            .bytes
            .get(self.at..end)
            .ok_or(BinaryError::at(ErrorKind::Truncated, self.at))?;
        self.at = end;
        Ok(value)
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
            Err(BinaryError::at(ErrorKind::TrailingBytes, self.at))
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum Constant<'a> {
    Empty,
    Utf8(&'a [u8]),
    Integer(i32),
    Number(u8),
    WideNumber(u8),
    Class(u16),
    String(u16),
    Member { tag: u8, class: u16, pair: u16 },
    Pair { name: u16, descriptor: u16 },
    MethodHandle { kind: u8, reference: u16 },
    MethodType(u16),
    Dynamic { bootstrap: u16, pair: u16 },
    InvokeDynamic { bootstrap: u16, pair: u16 },
    Other,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MemberRef<'a> {
    pub owner: &'a str,
    pub name: &'a str,
    pub descriptor: &'a str,
}
/// JVMS 4.4.8 reference kinds. Field and constructor handles are represented
/// faithfully even when the execution adapter cannot summarize them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum ReferenceKind {
    GetField = 1,
    GetStatic = 2,
    PutField = 3,
    PutStatic = 4,
    InvokeVirtual = 5,
    InvokeStatic = 6,
    InvokeSpecial = 7,
    NewInvokeSpecial = 8,
    InvokeInterface = 9,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MethodHandle<'a> {
    pub kind: ReferenceKind,
    pub member: MemberRef<'a>,
}
/// Borrowed big-endian constant-pool indexes; no per-bootstrap argument owner.
#[derive(Clone, Copy, Debug)]
pub struct BootstrapArguments<'a>(&'a [u8]);
impl<'a> BootstrapArguments<'a> {
    pub fn len(self) -> usize {
        self.0.len() / 2
    }
    pub fn is_empty(self) -> bool {
        self.0.is_empty()
    }
    pub fn get(self, index: usize) -> Option<u16> {
        let at = index.checked_mul(2)?;
        Some(u16::from_be_bytes(
            self.0.get(at..at.checked_add(2)?)?.try_into().ok()?,
        ))
    }
    pub fn iter(self) -> impl ExactSizeIterator<Item = u16> + 'a {
        self.0
            .chunks_exact(2)
            .map(|b| u16::from_be_bytes([b[0], b[1]]))
    }
}
#[derive(Clone, Copy, Debug)]
struct BootstrapRow<'a> {
    handle: u16,
    arguments: BootstrapArguments<'a>,
}
#[derive(Clone, Copy, Debug)]
pub struct BootstrapMethod<'a> {
    pub method: MethodHandle<'a>,
    pub arguments: BootstrapArguments<'a>,
}
#[derive(Clone, Copy, Debug)]
pub struct InvokeDynamic<'a> {
    pub name: &'a str,
    pub descriptor: MethodDescriptor<'a>,
    pub bootstrap: BootstrapMethod<'a>,
}
#[derive(Clone, Copy, Debug)]
pub enum BootstrapArgument<'a> {
    Integer(i32),
    Float,
    Long,
    Double,
    String,
    Class(&'a str),
    MethodHandle(MethodHandle<'a>),
    MethodType(MethodDescriptor<'a>),
    Dynamic {
        name: &'a str,
        descriptor: &'a str,
        bootstrap: u16,
    },
}
#[derive(Clone, Copy, Debug)]
pub struct FieldInfo<'a> {
    pub flags: u16,
    pub name: &'a str,
    pub descriptor: &'a str,
}
#[derive(Clone, Copy, Debug)]
pub struct MethodInfo<'a> {
    pub flags: u16,
    pub name: &'a str,
    pub descriptor: &'a str,
    pub max_stack: u16,
    pub max_locals: u16,
    pub code: Option<&'a [u8]>,
    pub exception_handlers: u16,
    /// Raw verified 8-byte Code exception records, borrowed from the class.
    pub exception_table: &'a [u8],
}
#[derive(Debug)]
pub struct ClassFile<'a> {
    pub name: &'a str,
    pub parent: Option<&'a str>,
    pub interfaces: Vec<&'a str>,
    pub flags: u16,
    pub major: u16,
    pub minor: u16,
    pub fields: Vec<FieldInfo<'a>>,
    pub methods: Vec<MethodInfo<'a>>,
    pool: Vec<Constant<'a>>,
    bootstrap_methods: Vec<BootstrapRow<'a>>,
}
impl<'a> ClassFile<'a> {
    fn utf(&self, index: u16) -> Result<&'a str> {
        utf(&self.pool, index)
    }
    fn class(&self, index: u16) -> Result<&'a str> {
        class_name(&self.pool, index)
    }
    fn member(&self, index: u16, field: bool) -> Result<MemberRef<'a>> {
        let Some(Constant::Member { tag, class, pair }) = self.pool.get(index as usize) else {
            return Err(BinaryError::at(ErrorKind::BadConstant, index as usize));
        };
        if (field && *tag != 9) || (!field && !matches!(*tag, 10 | 11)) {
            return Err(BinaryError::at(ErrorKind::BadConstant, index as usize));
        }
        let Some(Constant::Pair { name, descriptor }) = self.pool.get(*pair as usize) else {
            return Err(BinaryError::at(ErrorKind::BadConstant, *pair as usize));
        };
        Ok(MemberRef {
            owner: self.class(*class)?,
            name: self.utf(*name)?,
            descriptor: self.utf(*descriptor)?,
        })
    }
    fn name_type(&self, index: u16) -> Result<(&'a str, &'a str)> {
        let Some(Constant::Pair { name, descriptor }) = self.pool.get(index as usize) else {
            return Err(BinaryError::at(ErrorKind::BadConstant, index as usize));
        };
        Ok((self.utf(*name)?, self.utf(*descriptor)?))
    }
    pub fn method_type(&self, index: u16) -> Result<MethodDescriptor<'a>> {
        let Some(Constant::MethodType(descriptor)) = self.pool.get(index as usize) else {
            return Err(BinaryError::at(ErrorKind::BadConstant, index as usize));
        };
        method_descriptor(self.utf(*descriptor)?)
    }
    pub fn method_handle(&self, index: u16) -> Result<MethodHandle<'a>> {
        let Some(Constant::MethodHandle { kind, reference }) = self.pool.get(index as usize) else {
            return Err(BinaryError::at(ErrorKind::BadConstant, index as usize));
        };
        let kind = match kind {
            1 => ReferenceKind::GetField,
            2 => ReferenceKind::GetStatic,
            3 => ReferenceKind::PutField,
            4 => ReferenceKind::PutStatic,
            5 => ReferenceKind::InvokeVirtual,
            6 => ReferenceKind::InvokeStatic,
            7 => ReferenceKind::InvokeSpecial,
            8 => ReferenceKind::NewInvokeSpecial,
            9 => ReferenceKind::InvokeInterface,
            _ => return Err(BinaryError::at(ErrorKind::BadConstant, index as usize)),
        };
        let field = matches!(
            kind,
            ReferenceKind::GetField
                | ReferenceKind::GetStatic
                | ReferenceKind::PutField
                | ReferenceKind::PutStatic
        );
        let Some(Constant::Member { tag, .. }) = self.pool.get(*reference as usize) else {
            return Err(BinaryError::at(ErrorKind::BadConstant, *reference as usize));
        };
        let correct_tag = match kind {
            ReferenceKind::GetField
            | ReferenceKind::GetStatic
            | ReferenceKind::PutField
            | ReferenceKind::PutStatic => *tag == 9,
            ReferenceKind::InvokeVirtual | ReferenceKind::NewInvokeSpecial => *tag == 10,
            ReferenceKind::InvokeInterface => *tag == 11,
            _ => *tag == 10 || (self.major >= 52 && *tag == 11),
        };
        if !correct_tag {
            return Err(BinaryError::at(ErrorKind::BadConstant, *reference as usize));
        }
        let member = self.member(*reference, field)?;
        valid_class_name(member.owner)?;
        if kind != ReferenceKind::NewInvokeSpecial {
            valid_dynamic_name(member.name)?;
        }
        if field {
            field_descriptor(member.descriptor)?;
        } else {
            let descriptor = method_descriptor(member.descriptor)?;
            if (kind == ReferenceKind::NewInvokeSpecial
                && (member.name != "<init>" || descriptor.return_type != "V"))
                || (kind != ReferenceKind::NewInvokeSpecial
                    && matches!(member.name, "<init>" | "<clinit>"))
            {
                return Err(BinaryError::at(ErrorKind::BadConstant, *reference as usize));
            }
        }
        Ok(MethodHandle { kind, member })
    }
    pub fn bootstrap_count(&self) -> usize {
        self.bootstrap_methods.len()
    }
    pub fn bootstrap_method(&self, index: u16) -> Result<BootstrapMethod<'a>> {
        let row = self
            .bootstrap_methods
            .get(index as usize)
            .ok_or(BinaryError::at(ErrorKind::BadConstant, index as usize))?;
        Ok(BootstrapMethod {
            method: self.method_handle(row.handle)?,
            arguments: row.arguments,
        })
    }
    pub fn invoke_dynamic(&self, index: u16) -> Result<InvokeDynamic<'a>> {
        let Some(Constant::InvokeDynamic { bootstrap, pair }) = self.pool.get(index as usize)
        else {
            return Err(BinaryError::at(ErrorKind::BadConstant, index as usize));
        };
        let (name, descriptor) = self.name_type(*pair)?;
        valid_dynamic_name(name)?;
        Ok(InvokeDynamic {
            name,
            descriptor: method_descriptor(descriptor)?,
            bootstrap: self.bootstrap_method(*bootstrap)?,
        })
    }
    pub fn bootstrap_argument(&self, index: u16) -> Result<BootstrapArgument<'a>> {
        Ok(match self.pool.get(index as usize) {
            Some(Constant::Integer(value)) => BootstrapArgument::Integer(*value),
            Some(Constant::Number(4)) => BootstrapArgument::Float,
            Some(Constant::WideNumber(5)) => BootstrapArgument::Long,
            Some(Constant::WideNumber(6)) => BootstrapArgument::Double,
            Some(Constant::String(string)) => {
                if !matches!(self.pool.get(*string as usize), Some(Constant::Utf8(_))) {
                    return Err(BinaryError::at(ErrorKind::BadConstant, *string as usize));
                }
                BootstrapArgument::String
            }
            Some(Constant::Class(_)) => BootstrapArgument::Class(self.class(index)?),
            Some(Constant::MethodHandle { .. }) => {
                BootstrapArgument::MethodHandle(self.method_handle(index)?)
            }
            Some(Constant::MethodType(_)) => {
                BootstrapArgument::MethodType(self.method_type(index)?)
            }
            Some(Constant::Dynamic { bootstrap, pair }) => {
                let (name, descriptor) = self.name_type(*pair)?;
                valid_dynamic_name(name)?;
                field_descriptor(descriptor)?;
                if *bootstrap as usize >= self.bootstrap_methods.len() {
                    return Err(BinaryError::at(ErrorKind::BadConstant, index as usize));
                }
                BootstrapArgument::Dynamic {
                    name,
                    descriptor,
                    bootstrap: *bootstrap,
                }
            }
            _ => return Err(BinaryError::at(ErrorKind::BadConstant, index as usize)),
        })
    }
    fn lambda(
        &self,
        dynamic: InvokeDynamic<'a>,
        captures: ValueRange,
        offset: u32,
    ) -> Result<Lambda<'a>> {
        const META_DESCRIPTOR: &str = "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodHandle;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;";
        const ALT_DESCRIPTOR: &str = "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;[Ljava/lang/Object;)Ljava/lang/invoke/CallSite;";
        let b = dynamic.bootstrap;
        let unsupported = || BinaryError::at(ErrorKind::UnsupportedBootstrap, offset as usize);
        if b.method.kind != ReferenceKind::InvokeStatic
            || b.method.member.owner != "java/lang/invoke/LambdaMetafactory"
            || !((b.method.member.name == "metafactory"
                && b.method.member.descriptor == META_DESCRIPTOR
                && b.arguments.len() == 3)
                || (b.method.member.name == "altMetafactory"
                    && b.method.member.descriptor == ALT_DESCRIPTOR
                    && b.arguments.len() >= 4))
        {
            return Err(unsupported());
        }
        let sam = self.method_type(b.arguments.get(0).ok_or_else(unsupported)?)?;
        let implementation = self.method_handle(b.arguments.get(1).ok_or_else(unsupported)?)?;
        let instantiated = self.method_type(b.arguments.get(2).ok_or_else(unsupported)?)?;
        let mut serializable = false;
        if b.method.member.name == "altMetafactory" {
            let integer = |index| -> Result<i32> {
                match self.bootstrap_argument(b.arguments.get(index).ok_or_else(unsupported)?)? {
                    BootstrapArgument::Integer(value) => Ok(value),
                    _ => Err(unsupported()),
                }
            };
            let flags = integer(3)?;
            if flags & !7 != 0 {
                return Err(unsupported());
            }
            serializable = flags & 1 != 0;
            let mut next = 4;
            if flags & 2 != 0 {
                if integer(next)? != 0 {
                    return Err(unsupported());
                }
                next += 1;
            }
            if flags & 4 != 0 {
                let count = usize::try_from(integer(next)?).map_err(|_| unsupported())?;
                next += 1;
                if count > b.arguments.len().saturating_sub(next) {
                    return Err(unsupported());
                }
                for index in next..next + count {
                    let bridge =
                        self.method_type(b.arguments.get(index).ok_or_else(unsupported)?)?;
                    if bridge.text != sam.text && bridge.text != instantiated.text {
                        return Err(unsupported());
                    }
                }
                next += count;
            }
            if next != b.arguments.len() {
                return Err(unsupported());
            }
        }
        let kind = match implementation.kind {
            ReferenceKind::InvokeStatic => InvokeKind::Static,
            ReferenceKind::InvokeVirtual => InvokeKind::Virtual,
            ReferenceKind::InvokeInterface => InvokeKind::Interface,
            _ => return Err(unsupported()),
        };
        let interface = dynamic
            .descriptor
            .return_type
            .strip_prefix('L')
            .and_then(|s| s.strip_suffix(';'))
            .ok_or_else(unsupported)?;
        valid_class_name(interface)?;
        let target = method_descriptor(implementation.member.descriptor)?;
        let receiver = usize::from(kind != InvokeKind::Static);
        if sam.parameter_count != instantiated.parameter_count
            || dynamic.descriptor.parameter_count + sam.parameter_count
                != target.parameter_count + receiver
            || captures.len as usize != dynamic.descriptor.parameter_count
        {
            return Err(unsupported());
        }
        // The supported adapter only forwards reference identities or scalar
        // values. Boxing/unboxing and constructor/special adaptation remain an
        // explicit dynamic boundary; no allocation or effects are invented.
        for (erased, specialized) in sam.parameters().zip(instantiated.parameters()) {
            if !same_or_references(specialized, erased) {
                return Err(unsupported());
            }
        }
        if !same_or_references(instantiated.return_type, sam.return_type) {
            return Err(unsupported());
        }
        let mut target_parameters = target.parameters();
        for (i, capture) in dynamic.descriptor.parameters().enumerate() {
            if i == 0 && receiver != 0 {
                if capture.strip_prefix('L').and_then(|s| s.strip_suffix(';'))
                    != Some(implementation.member.owner)
                {
                    return Err(unsupported());
                }
            } else if target_parameters.next() != Some(capture) {
                return Err(unsupported());
            }
        }
        for (i, actual) in instantiated.parameters().enumerate() {
            if i == 0 && receiver != 0 && dynamic.descriptor.parameter_count == 0 {
                if actual.strip_prefix('L').and_then(|s| s.strip_suffix(';'))
                    != Some(implementation.member.owner)
                {
                    return Err(unsupported());
                }
            } else if !adaptable(actual, target_parameters.next().ok_or_else(unsupported)?) {
                return Err(unsupported());
            }
        }
        if target_parameters.next().is_some()
            || (instantiated.return_type != "V"
                && (target.return_type == "V"
                    || !adaptable(target.return_type, instantiated.return_type)))
        {
            return Err(unsupported());
        }
        Ok(Lambda {
            offset,
            interface,
            sam_name: dynamic.name,
            sam_descriptor: sam.text,
            instantiated_descriptor: instantiated.text,
            implementation: implementation.member,
            kind,
            captures,
            serializable,
        })
    }
    /// Exact descriptors select overloads; compiler `(+N)` is never JVM order.
    pub fn method(&self, name: &str, descriptor: Option<&str>) -> Result<&MethodInfo<'a>> {
        let mut matches = self
            .methods
            .iter()
            .filter(|m| m.name == name && descriptor.is_none_or(|d| m.descriptor == d));
        let found = matches
            .next()
            .ok_or(BinaryError::at(ErrorKind::MissingMethod, 0))?;
        if matches.next().is_some() {
            return Err(BinaryError::at(ErrorKind::AmbiguousMethod, 0));
        }
        Ok(found)
    }
}
fn utf<'a>(pool: &[Constant<'a>], index: u16) -> Result<&'a str> {
    let Some(Constant::Utf8(bytes)) = pool.get(index as usize) else {
        return Err(BinaryError::at(ErrorKind::BadConstant, index as usize));
    };
    // Modified UTF-8 in arbitrary string constants is preserved opaque. A name
    // requiring unsupported surrogate/NUL decoding is rejected, never repaired.
    std::str::from_utf8(bytes).map_err(|_| BinaryError::at(ErrorKind::InvalidUtf8, index as usize))
}
fn class_name<'a>(pool: &[Constant<'a>], index: u16) -> Result<&'a str> {
    let Some(Constant::Class(name)) = pool.get(index as usize) else {
        return Err(BinaryError::at(ErrorKind::BadConstant, index as usize));
    };
    utf(pool, *name)
}
fn skip_attributes(r: &mut Reader<'_>, pool: &[Constant<'_>]) -> Result<()> {
    for _ in 0..r.u2()? {
        utf(pool, r.u2()?)?;
        let n = r.u4()? as usize;
        r.take(n)?;
    }
    Ok(())
}
fn valid_dynamic_name(name: &str) -> Result<()> {
    if name.is_empty()
        || name
            .bytes()
            .any(|b| matches!(b, b'.' | b';' | b'[' | b'/' | b'<' | b'>' | b'\0'))
    {
        return Err(BinaryError::at(ErrorKind::BadConstant, 0));
    }
    Ok(())
}

#[cfg(test)]
thread_local! { static CLASS_PARSE_CALLS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) }; }
#[cfg(test)]
fn class_parse_calls() -> usize {
    CLASS_PARSE_CALLS.with(std::cell::Cell::get)
}
pub fn parse_class(bytes: &[u8], limits: Limits) -> Result<ClassFile<'_>> {
    #[cfg(test)]
    CLASS_PARSE_CALLS.with(|count| count.set(count.get() + 1));
    if bytes.len() > limits.max_class_bytes {
        return Err(BinaryError::at(ErrorKind::ResourceLimit, 0));
    }
    let mut r = Reader::new(bytes);
    if r.u4()? != 0xcafebabe {
        return Err(BinaryError::at(ErrorKind::BadMagic, 0));
    }
    let minor = r.u2()?;
    let major = r.u2()?;
    if major < 45 {
        return Err(BinaryError::at(ErrorKind::BadMagic, 6));
    }
    let count = r.u2()? as usize;
    if count == 0 {
        return Err(BinaryError::at(ErrorKind::BadConstant, r.at));
    }
    let mut pool = vec![Constant::Empty; count];
    let mut index = 1;
    while index < count {
        let tag = r.u1()?;
        pool[index] = match tag {
            1 => {
                let n = r.u2()? as usize;
                Constant::Utf8(r.take(n)?)
            }
            3 => Constant::Integer(r.u4()? as i32),
            4 => {
                r.take(4)?;
                Constant::Number(tag)
            }
            5 | 6 => {
                r.take(8)?;
                if index + 1 >= count {
                    return Err(BinaryError::at(ErrorKind::BadConstant, r.at));
                }
                Constant::WideNumber(tag)
            }
            7 => Constant::Class(r.u2()?),
            8 => Constant::String(r.u2()?),
            9..=11 => Constant::Member {
                tag,
                class: r.u2()?,
                pair: r.u2()?,
            },
            12 => Constant::Pair {
                name: r.u2()?,
                descriptor: r.u2()?,
            },
            15 => Constant::MethodHandle {
                kind: r.u1()?,
                reference: r.u2()?,
            },
            16 => Constant::MethodType(r.u2()?),
            19 | 20 => {
                r.take(2)?;
                Constant::Other
            }
            17 => Constant::Dynamic {
                bootstrap: r.u2()?,
                pair: r.u2()?,
            },
            18 => Constant::InvokeDynamic {
                bootstrap: r.u2()?,
                pair: r.u2()?,
            },
            _ => return Err(BinaryError::at(ErrorKind::UnsupportedConstant, r.at - 1)),
        };
        // Long/double occupy the first of two slots, with an unusable second.
        index += if matches!(tag, 5 | 6) { 2 } else { 1 };
    }
    let flags = r.u2()?;
    let name = class_name(&pool, r.u2()?)?;
    valid_class_name(name)?;
    let parent_index = r.u2()?;
    let parent = if parent_index == 0 {
        None
    } else {
        Some(class_name(&pool, parent_index)?)
    };
    let mut interfaces = Vec::new();
    for _ in 0..r.u2()? {
        interfaces.push(class_name(&pool, r.u2()?)?);
    }
    let mut fields = Vec::new();
    for _ in 0..r.u2()? {
        let field = FieldInfo {
            flags: r.u2()?,
            name: utf(&pool, r.u2()?)?,
            descriptor: utf(&pool, r.u2()?)?,
        };
        field_descriptor(field.descriptor)?;
        skip_attributes(&mut r, &pool)?;
        fields.push(field);
    }
    let mut methods = Vec::new();
    for _ in 0..r.u2()? {
        let mut m = MethodInfo {
            flags: r.u2()?,
            name: utf(&pool, r.u2()?)?,
            descriptor: utf(&pool, r.u2()?)?,
            max_stack: 0,
            max_locals: 0,
            code: None,
            exception_handlers: 0,
            exception_table: &[],
        };
        method_descriptor(m.descriptor)?;
        for _ in 0..r.u2()? {
            let attr = utf(&pool, r.u2()?)?;
            let n = r.u4()? as usize;
            let payload = r.take(n)?;
            if attr == "Code" {
                if m.code.is_some() {
                    return Err(BinaryError::at(ErrorKind::DuplicateCode, r.at));
                }
                let mut c = Reader::new(payload);
                m.max_stack = c.u2()?;
                m.max_locals = c.u2()?;
                let n = c.u4()? as usize;
                if n == 0
                    || n > 65_535
                    || n > limits.max_code_bytes
                    || m.max_stack as usize > limits.max_stack
                    || m.max_locals as usize > limits.max_locals
                {
                    return Err(BinaryError::at(ErrorKind::ResourceLimit, r.at));
                }
                m.code = Some(c.take(n)?);
                m.exception_handlers = c.u2()?;
                let handlers_at = c.at;
                for _ in 0..m.exception_handlers {
                    let start = c.u2()? as usize;
                    let end = c.u2()? as usize;
                    let handler = c.u2()? as usize;
                    let catch = c.u2()?;
                    if start >= end || end > n || handler >= n {
                        return Err(BinaryError::at(ErrorKind::InvalidCode, c.at));
                    }
                    if catch != 0 {
                        class_name(&pool, catch)?;
                    }
                }
                m.exception_table = &c.bytes[handlers_at..c.at];
                skip_attributes(&mut c, &pool)?;
                c.end()?;
            }
        }
        methods.push(m);
    }
    let mut bootstrap_methods = Vec::new();
    let mut saw_bootstrap = false;
    for _ in 0..r.u2()? {
        let attribute = utf(&pool, r.u2()?)?;
        let length = r.u4()? as usize;
        let payload = r.take(length)?;
        if attribute == "BootstrapMethods" {
            if saw_bootstrap {
                return Err(BinaryError::at(ErrorKind::DuplicateBootstrapMethods, r.at));
            }
            saw_bootstrap = true;
            let mut b = Reader::new(payload);
            let count = b.u2()? as usize;
            if count > payload.len().saturating_sub(2) / 4 {
                return Err(BinaryError::at(ErrorKind::Truncated, r.at));
            }
            bootstrap_methods
                .try_reserve_exact(count)
                .map_err(|_| BinaryError::at(ErrorKind::ResourceLimit, r.at))?;
            for _ in 0..count {
                let handle = b.u2()?;
                let arguments = b.u2()? as usize;
                bootstrap_methods.push(BootstrapRow {
                    handle,
                    arguments: BootstrapArguments(b.take(arguments * 2)?),
                });
            }
            b.end()?;
        }
    }
    r.end()?;
    let class = ClassFile {
        name,
        parent,
        interfaces,
        flags,
        major,
        minor,
        fields,
        methods,
        pool,
        bootstrap_methods,
    };
    // New constant forms are validated once, including unused entries. Bootstrap
    // argument cycles through CONSTANT_Dynamic are legal format; no recursion.
    for (index, entry) in class.pool.iter().enumerate() {
        match entry {
            Constant::MethodHandle { .. } => {
                if major < 51 {
                    return Err(BinaryError::at(ErrorKind::BadConstant, index));
                }
                class.method_handle(index as u16)?;
            }
            Constant::MethodType(_) => {
                if major < 51 {
                    return Err(BinaryError::at(ErrorKind::BadConstant, index));
                }
                class.method_type(index as u16)?;
            }
            Constant::InvokeDynamic { .. } => {
                if major < 51 {
                    return Err(BinaryError::at(ErrorKind::BadConstant, index));
                }
                class.invoke_dynamic(index as u16)?;
            }
            Constant::Dynamic { .. } => {
                if major < 55 {
                    return Err(BinaryError::at(ErrorKind::BadConstant, index));
                }
                class.bootstrap_argument(index as u16)?;
            }
            _ => (),
        }
    }
    for index in 0..class.bootstrap_count() {
        let bootstrap = class.bootstrap_method(index as u16)?;
        // A bootstrap is invoked; a field handle can never be an invocation.
        if !matches!(
            bootstrap.method.kind,
            ReferenceKind::InvokeStatic | ReferenceKind::NewInvokeSpecial
        ) {
            return Err(BinaryError::at(ErrorKind::BadConstant, index));
        }
        for argument in bootstrap.arguments.iter() {
            class.bootstrap_argument(argument)?;
        }
    }
    Ok(class)
}

#[derive(Clone, Copy, Debug)]
pub struct MethodDescriptor<'a> {
    pub text: &'a str,
    pub return_type: &'a str,
    pub parameter_count: usize,
    pub parameter_slots: usize,
    end: usize,
}
impl<'a> MethodDescriptor<'a> {
    pub fn parameters(self) -> Parameters<'a> {
        Parameters {
            descriptor: self.text,
            at: 1,
            end: self.end,
        }
    }
}
pub struct Parameters<'a> {
    descriptor: &'a str,
    at: usize,
    end: usize,
}
impl<'a> Iterator for Parameters<'a> {
    type Item = &'a str;
    fn next(&mut self) -> Option<Self::Item> {
        if self.at >= self.end {
            return None;
        }
        let start = self.at;
        self.at = one_type(self.descriptor, start, false).ok()?;
        Some(&self.descriptor[start..self.at])
    }
}
fn one_type(s: &str, start: usize, void: bool) -> Result<usize> {
    let b = s.as_bytes();
    let mut at = start;
    let mut dimensions = 0;
    while b.get(at) == Some(&b'[') {
        at += 1;
        dimensions += 1;
        if dimensions > 255 {
            return Err(BinaryError::at(ErrorKind::InvalidDescriptor, at));
        }
    }
    match b.get(at).copied() {
        Some(b'B' | b'C' | b'D' | b'F' | b'I' | b'J' | b'S' | b'Z') => Ok(at + 1),
        Some(b'V') if void && dimensions == 0 => Ok(at + 1),
        Some(b'L') => {
            let begin = at + 1;
            at = begin;
            while b.get(at).is_some_and(|c| *c != b';') {
                if matches!(b[at], b'.' | b'[' | b'\0' | b'(' | b')') {
                    return Err(BinaryError::at(ErrorKind::InvalidDescriptor, at));
                }
                at += 1;
            }
            if at == begin || b.get(at) != Some(&b';') {
                Err(BinaryError::at(ErrorKind::InvalidDescriptor, at))
            } else {
                Ok(at + 1)
            }
        }
        _ => Err(BinaryError::at(ErrorKind::InvalidDescriptor, at)),
    }
}
pub fn field_descriptor(s: &str) -> Result<&str> {
    if one_type(s, 0, false)? != s.len() {
        return Err(BinaryError::at(ErrorKind::InvalidDescriptor, 0));
    }
    Ok(s)
}
pub fn method_descriptor(s: &str) -> Result<MethodDescriptor<'_>> {
    if !s.starts_with('(') {
        return Err(BinaryError::at(ErrorKind::InvalidDescriptor, 0));
    }
    let mut at = 1;
    let mut count = 0;
    let mut slots = 0;
    while s.as_bytes().get(at) != Some(&b')') {
        let end = one_type(s, at, false)?;
        slots += width(&s[at..end]) as usize;
        count += 1;
        at = end;
        if slots > 255 {
            return Err(BinaryError::at(ErrorKind::InvalidDescriptor, at));
        }
    }
    let end = one_type(s, at + 1, true)?;
    if end != s.len() {
        return Err(BinaryError::at(ErrorKind::InvalidDescriptor, end));
    }
    Ok(MethodDescriptor {
        text: s,
        return_type: &s[at + 1..end],
        parameter_count: count,
        parameter_slots: slots,
        end: at,
    })
}
fn width(descriptor: &str) -> u8 {
    if matches!(descriptor, "J" | "D") {
        2
    } else {
        1
    }
}
fn reference_type(descriptor: &str) -> bool {
    descriptor.starts_with('L') || descriptor.starts_with('[')
}
fn same_or_references(from: &str, to: &str) -> bool {
    from == to || (reference_type(from) && reference_type(to))
}
fn adaptable(from: &str, to: &str) -> bool {
    same_or_references(from, to)
        || matches!(
            (from, to),
            ("B", "S" | "I" | "J" | "F" | "D")
                | ("S" | "C", "I" | "J" | "F" | "D")
                | ("I", "J" | "F" | "D")
                | ("J", "F" | "D")
                | ("F", "D")
        )
}
fn valid_class_name(name: &str) -> Result<()> {
    if name.is_empty()
        || name.starts_with('/')
        || name.ends_with('/')
        || name
            .split('/')
            .any(|p| p.is_empty() || p == "." || p == "..")
        || name
            .bytes()
            .any(|b| matches!(b, b'\0' | b'\\' | b'.' | b';' | b'['))
    {
        return Err(BinaryError::at(ErrorKind::InvalidClassName, 0));
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BinaryValueId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ValueRange {
    pub start: u32,
    pub len: u32,
}
impl ValueRange {
    pub fn range(self) -> std::ops::Range<usize> {
        self.start as usize..self.start as usize + self.len as usize
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Value<'a> {
    Receiver,
    Argument(u16),
    Null,
    Constant {
        pool_index: u16,
        wide: bool,
    },
    Allocation {
        class: &'a str,
        offset: u32,
        constructor: Option<u32>,
    },
    StaticField(MemberRef<'a>),
    Field {
        member: MemberRef<'a>,
        receiver: BinaryValueId,
    },
    CallResult(u32),
    /// Index into MethodSummary::lambdas; creation never executes its target.
    Lambda(u32),
    /// Descriptor-known dynamic operation whose semantics are unsupported.
    UnknownDynamic,
    /// Structurally covered computation with imprecise data, not open effects.
    UnknownData,
    /// Finite may-alias alternatives from a bounded all-path native analysis.
    /// The range indexes MethodSummary::arguments, not JVM arguments.
    Alternatives(ValueRange),
    /// May-allocation from a complete instruction scan; constructor calls are
    /// represented separately and receiver aliasing remains conservative.
    MayAllocation {
        class: &'a str,
        offset: u32,
    },
    UnknownLocal(u16),
    Void,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InvokeKind {
    Virtual,
    Special,
    Static,
    Interface,
}
impl InvokeKind {
    pub fn requires_receiver_dispatch(self) -> bool {
        matches!(self, Self::Virtual | Self::Interface)
    }
}
#[derive(Clone, Copy, Debug)]
pub struct Call<'a> {
    pub member: MemberRef<'a>,
    pub kind: InvokeKind,
    pub receiver: Option<BinaryValueId>,
    pub arguments: ValueRange,
    pub offset: u32,
}
#[derive(Clone, Copy, Debug)]
pub struct FieldWrite<'a> {
    pub member: MemberRef<'a>,
    pub receiver: Option<BinaryValueId>,
    pub value: BinaryValueId,
    pub offset: u32,
}
#[derive(Clone, Copy, Debug)]
pub struct Lambda<'a> {
    pub offset: u32,
    pub interface: &'a str,
    pub sam_name: &'a str,
    pub sam_descriptor: &'a str,
    pub instantiated_descriptor: &'a str,
    pub implementation: MemberRef<'a>,
    pub kind: InvokeKind,
    pub captures: ValueRange,
    /// Serializable factory property; creation never invokes serialization.
    pub serializable: bool,
}
#[derive(Clone, Debug)]
pub struct MethodSummary<'a> {
    pub descriptor: &'a str,
    pub values: Vec<Value<'a>>,
    /// Bytecode PCs, parallel to values; source spans are deliberately separate.
    pub value_offsets: Vec<u32>,
    pub calls: Vec<Call<'a>>,
    pub arguments: Vec<BinaryValueId>,
    pub field_writes: Vec<FieldWrite<'a>>,
    pub lambdas: Vec<Lambda<'a>>,
    /// Recoverable dynamic boundaries, in bytecode order. Interpretation can
    /// continue because the exact call-site descriptor supplies stack effects.
    pub unknown_offsets: Vec<u32>,
    pub returned: Option<BinaryValueId>,
    pub unknown: Option<BinaryError>,
    pub envelope: Option<EnvelopeCoverage>,
}
impl<'a> MethodSummary<'a> {
    pub fn complete(&self) -> bool {
        self.unknown.is_none()
    }
    pub fn effects_complete(&self) -> bool {
        self.complete()
            && self.calls.is_empty()
            && self.lambdas.is_empty()
            && !self
                .values
                .iter()
                .any(|v| matches!(v, Value::StaticField(_)))
            && !self.field_writes.iter().any(|w| w.receiver.is_none())
    }
    fn value(&mut self, value: Value<'a>, limits: Limits, offset: u32) -> Result<BinaryValueId> {
        if self.values.len() >= limits.max_values || self.values.len() >= u32::MAX as usize {
            return Err(BinaryError::at(ErrorKind::ResourceLimit, 0));
        }
        let id = BinaryValueId(self.values.len() as u32);
        self.values.push(value);
        self.value_offsets.push(offset);
        Ok(id)
    }
}

#[derive(Clone, Copy)]
struct StackValue {
    id: BinaryValueId,
    width: u8,
}
struct Interpreter<'c, 'a> {
    class: &'c ClassFile<'a>,
    out: MethodSummary<'a>,
    stack: Vec<StackValue>,
    locals: Vec<Option<StackValue>>,
    slots: usize,
    max_stack: usize,
    limits: Limits,
    pc: u32,
}
impl<'a> Interpreter<'_, 'a> {
    fn new_value(&mut self, v: Value<'a>, width: u8) -> Result<StackValue> {
        Ok(StackValue {
            id: self.out.value(v, self.limits, self.pc)?,
            width,
        })
    }
    fn push(&mut self, v: StackValue) -> Result<()> {
        if self.slots + v.width as usize > self.max_stack {
            return Err(BinaryError::at(ErrorKind::InvalidStackCategory, 0));
        }
        self.slots += v.width as usize;
        self.stack.push(v);
        Ok(())
    }
    fn push_new(&mut self, v: Value<'a>, width: u8) -> Result<()> {
        let v = self.new_value(v, width)?;
        self.push(v)
    }
    fn pop(&mut self) -> Result<StackValue> {
        let v = self
            .stack
            .pop()
            .ok_or(BinaryError::at(ErrorKind::StackUnderflow, 0))?;
        self.slots -= v.width as usize;
        Ok(v)
    }
    fn pop_width(&mut self, width: u8) -> Result<StackValue> {
        let v = self.pop()?;
        if v.width != width {
            Err(BinaryError::at(ErrorKind::InvalidStackCategory, 0))
        } else {
            Ok(v)
        }
    }
    fn load(&mut self, index: usize, width: u8) -> Result<()> {
        let value = *self
            .locals
            .get(index)
            .ok_or(BinaryError::at(ErrorKind::InvalidLocal, index))?;
        let v = match value {
            Some(v) if v.width == width => v,
            Some(_) => return Err(BinaryError::at(ErrorKind::InvalidLocal, index)),
            None => self.new_value(Value::UnknownLocal(index as u16), width)?,
        };
        self.push(v)
    }
    fn store(&mut self, index: usize, width: u8) -> Result<()> {
        if index + width as usize > self.locals.len() {
            return Err(BinaryError::at(ErrorKind::InvalidLocal, index));
        }
        let v = self.pop_width(width)?;
        if index > 0 && self.locals[index - 1].is_some_and(|v| v.width == 2) {
            self.locals[index - 1] = None;
        }
        self.locals[index] = Some(v);
        if width == 2 {
            self.locals[index + 1] = None;
        }
        Ok(())
    }
    fn run(&mut self, method: &MethodInfo<'a>) -> Result<()> {
        let code = method
            .code
            .ok_or(BinaryError::at(ErrorKind::MissingCode, 0))?;
        if method.exception_handlers != 0 {
            return Err(BinaryError::at(ErrorKind::ExceptionHandlers, 0));
        }
        let descriptor = method_descriptor(method.descriptor)?;
        if method.flags & 8 == 0 && descriptor.parameter_slots >= 255 {
            return Err(BinaryError::at(ErrorKind::InvalidDescriptor, 0));
        }
        let mut slot = 0;
        if method.flags & 8 == 0 {
            if self.locals.is_empty() {
                return Err(BinaryError::at(ErrorKind::InvalidLocal, 0));
            }
            let v = self.new_value(Value::Receiver, 1)?;
            self.locals[0] = Some(v);
            slot = 1;
        }
        for (index, p) in descriptor.parameters().enumerate() {
            let width = width(p);
            if slot + width as usize > self.locals.len() {
                return Err(BinaryError::at(ErrorKind::InvalidLocal, slot));
            }
            let v = self.new_value(Value::Argument(index as u16), width)?;
            self.locals[slot] = Some(v);
            slot += width as usize;
        }
        let mut r = Reader::new(code);
        let mut steps = 0;
        while r.at < code.len() {
            let at = r.at;
            self.pc = at as u32;
            let opcode = r.u1()?;
            steps += 1;
            if steps > self.limits.max_steps {
                return Err(BinaryError::at(ErrorKind::ResourceLimit, at));
            }
            let operation = (|| -> Result<()> {
                match opcode {
                    0 => (),
                    1 => self.push_new(Value::Null, 1)?,
                    2..=15 => self.push_new(
                        Value::Constant {
                            pool_index: 0,
                            wide: matches!(opcode, 9 | 10 | 14 | 15),
                        },
                        if matches!(opcode, 9 | 10 | 14 | 15) {
                            2
                        } else {
                            1
                        },
                    )?,
                    16 => {
                        r.take(1)?;
                        self.push_new(
                            Value::Constant {
                                pool_index: 0,
                                wide: false,
                            },
                            1,
                        )?;
                    }
                    17 => {
                        r.take(2)?;
                        self.push_new(
                            Value::Constant {
                                pool_index: 0,
                                wide: false,
                            },
                            1,
                        )?;
                    }
                    18..=20 => {
                        let index = if opcode == 18 {
                            r.u1()? as u16
                        } else {
                            r.u2()?
                        };
                        let constant = self
                            .class
                            .pool
                            .get(index as usize)
                            .ok_or(BinaryError::at(ErrorKind::BadConstant, at))?;
                        let wide = match constant {
                            Constant::Dynamic { .. } => {
                                return Err(BinaryError::at(ErrorKind::DynamicConstant, at));
                            }
                            Constant::Number(tag) => {
                                if !matches!(*tag, 3 | 4) {
                                    return Err(BinaryError::at(ErrorKind::BadConstant, at));
                                }
                                false
                            }
                            Constant::Integer(_) => false,
                            Constant::WideNumber(tag) => {
                                if !matches!(*tag, 5 | 6) {
                                    return Err(BinaryError::at(ErrorKind::BadConstant, at));
                                }
                                true
                            }
                            Constant::String(_)
                            | Constant::Class(_)
                            | Constant::MethodHandle { .. }
                            | Constant::MethodType(_) => false,
                            _ => return Err(BinaryError::at(ErrorKind::BadConstant, at)),
                        };
                        if wide != (opcode == 20) {
                            return Err(BinaryError::at(ErrorKind::InvalidStackCategory, at));
                        }
                        self.push_new(
                            Value::Constant {
                                pool_index: index,
                                wide,
                            },
                            if wide { 2 } else { 1 },
                        )?;
                    }
                    21..=25 => {
                        let index = r.u1()? as usize;
                        self.load(index, if matches!(opcode, 22 | 24) { 2 } else { 1 })?;
                    }
                    26..=45 => {
                        let index = (opcode - 26) % 4;
                        let family = (opcode - 26) / 4;
                        self.load(index as usize, if matches!(family, 1 | 3) { 2 } else { 1 })?;
                    }
                    54..=58 => {
                        let index = r.u1()? as usize;
                        self.store(index, if matches!(opcode, 55 | 57) { 2 } else { 1 })?;
                    }
                    59..=78 => {
                        let index = (opcode - 59) % 4;
                        let family = (opcode - 59) / 4;
                        self.store(index as usize, if matches!(family, 1 | 3) { 2 } else { 1 })?;
                    }
                    87 => {
                        self.pop_width(1)?;
                    }
                    89 => {
                        let v = *self
                            .stack
                            .last()
                            .ok_or(BinaryError::at(ErrorKind::StackUnderflow, at))?;
                        if v.width != 1 {
                            return Err(BinaryError::at(ErrorKind::InvalidStackCategory, at));
                        }
                        self.push(v)?;
                    }
                    95 => {
                        let a = self.pop_width(1)?;
                        let b = self.pop_width(1)?;
                        self.push(a)?;
                        self.push(b)?;
                    }
                    187 => {
                        let name = self.class.class(r.u2()?)?;
                        valid_class_name(name)?;
                        self.push_new(
                            Value::Allocation {
                                class: name,
                                offset: at as u32,
                                constructor: None,
                            },
                            1,
                        )?;
                    }
                    192 => {
                        self.class.class(r.u2()?)?;
                        if self.stack.last().is_none_or(|v| v.width != 1) {
                            return Err(BinaryError::at(ErrorKind::InvalidStackCategory, at));
                        }
                    }
                    178..=181 => {
                        let member = self.class.member(r.u2()?, true)?;
                        let width = width(field_descriptor(member.descriptor)?);
                        match opcode {
                            178 => self.push_new(Value::StaticField(member), width)?,
                            180 => {
                                let receiver = self.pop_width(1)?.id;
                                self.push_new(Value::Field { member, receiver }, width)?;
                            }
                            179 => {
                                let value = self.pop_width(width)?.id;
                                self.out.field_writes.push(FieldWrite {
                                    member,
                                    receiver: None,
                                    value,
                                    offset: at as u32,
                                });
                            }
                            _ => {
                                let value = self.pop_width(width)?.id;
                                let receiver = self.pop_width(1)?.id;
                                self.out.field_writes.push(FieldWrite {
                                    member,
                                    receiver: Some(receiver),
                                    value,
                                    offset: at as u32,
                                });
                            }
                        }
                    }
                    182..=185 => {
                        let member = self.class.member(r.u2()?, false)?;
                        let desc = method_descriptor(member.descriptor)?;
                        if opcode == 185 {
                            if r.u1()? as usize != desc.parameter_slots + 1 || r.u1()? != 0 {
                                return Err(BinaryError::at(ErrorKind::InvalidCode, at));
                            }
                        }
                        let mut widths = [0u8; 255];
                        for (i, p) in desc.parameters().enumerate() {
                            widths[i] = width(p);
                        }
                        let first = self.out.arguments.len();
                        let end = first
                            .checked_add(desc.parameter_count)
                            .ok_or(BinaryError::at(ErrorKind::ResourceLimit, at))?;
                        if end > self.limits.max_values || end > u32::MAX as usize {
                            return Err(BinaryError::at(ErrorKind::ResourceLimit, at));
                        }
                        self.out.arguments.resize(end, BinaryValueId(u32::MAX));
                        for i in (0..desc.parameter_count).rev() {
                            self.out.arguments[first + i] = self.pop_width(widths[i])?.id;
                        }
                        let receiver = if opcode == 184 {
                            None
                        } else {
                            Some(self.pop_width(1)?.id)
                        };
                        let kind = match opcode {
                            182 => InvokeKind::Virtual,
                            183 => InvokeKind::Special,
                            184 => InvokeKind::Static,
                            _ => InvokeKind::Interface,
                        };
                        let call_index = u32::try_from(self.out.calls.len())
                            .map_err(|_| BinaryError::at(ErrorKind::ResourceLimit, at))?;
                        self.out.calls.push(Call {
                            member,
                            kind,
                            receiver,
                            arguments: ValueRange {
                                start: first as u32,
                                len: desc.parameter_count as u32,
                            },
                            offset: at as u32,
                        });
                        if member.name == "<init>" {
                            if kind != InvokeKind::Special || desc.return_type != "V" {
                                return Err(BinaryError::at(ErrorKind::InvalidCode, at));
                            }
                            if let Some(receiver) = receiver {
                                if let Value::Allocation {
                                    class, constructor, ..
                                } = &mut self.out.values[receiver.0 as usize]
                                {
                                    if *class != member.owner || constructor.is_some() {
                                        return Err(BinaryError::at(ErrorKind::InvalidCode, at));
                                    }
                                    *constructor = Some(call_index);
                                }
                            }
                        } else if desc.return_type != "V" {
                            self.push_new(Value::CallResult(call_index), width(desc.return_type))?;
                        }
                    }
                    186 => {
                        let dynamic = self.class.invoke_dynamic(r.u2()?)?;
                        if r.u2()? != 0 {
                            return Err(BinaryError::at(ErrorKind::InvalidCode, at));
                        }
                        let descriptor = dynamic.descriptor;
                        let mut widths = [0u8; 255];
                        for (i, parameter) in descriptor.parameters().enumerate() {
                            widths[i] = width(parameter);
                        }
                        let first = self.out.arguments.len();
                        let end = first
                            .checked_add(descriptor.parameter_count)
                            .ok_or(BinaryError::at(ErrorKind::ResourceLimit, at))?;
                        if end > self.limits.max_values || end > u32::MAX as usize {
                            return Err(BinaryError::at(ErrorKind::ResourceLimit, at));
                        }
                        self.out.arguments.resize(end, BinaryValueId(u32::MAX));
                        for i in (0..descriptor.parameter_count).rev() {
                            self.out.arguments[first + i] = self.pop_width(widths[i])?.id;
                        }
                        let captures = ValueRange {
                            start: first as u32,
                            len: descriptor.parameter_count as u32,
                        };
                        match self.class.lambda(dynamic, captures, at as u32) {
                            Ok(lambda) => {
                                let index = u32::try_from(self.out.lambdas.len())
                                    .map_err(|_| BinaryError::at(ErrorKind::ResourceLimit, at))?;
                                if self.out.lambdas.len() >= self.limits.max_values {
                                    return Err(BinaryError::at(ErrorKind::ResourceLimit, at));
                                }
                                self.out.lambdas.push(lambda);
                                self.push_new(Value::Lambda(index), 1)?;
                            }
                            Err(error) => {
                                self.out
                                    .unknown
                                    .get_or_insert(BinaryError::at(error.kind, at));
                                self.out.unknown_offsets.push(at as u32);
                                if descriptor.return_type != "V" {
                                    self.push_new(
                                        Value::UnknownDynamic,
                                        width(descriptor.return_type),
                                    )?;
                                }
                            }
                        }
                    }
                    172..=177 => {
                        let expected = descriptor.return_type;
                        let valid = match opcode {
                            172 => matches!(expected, "B" | "C" | "I" | "S" | "Z"),
                            173 => expected == "J",
                            174 => expected == "F",
                            175 => expected == "D",
                            176 => expected.starts_with('L') || expected.starts_with('['),
                            _ => expected == "V",
                        };
                        if !valid {
                            return Err(BinaryError::at(ErrorKind::InvalidReturn, at));
                        }
                        let id = if opcode == 177 {
                            self.out.value(Value::Void, self.limits, self.pc)?
                        } else {
                            self.pop_width(width(expected))?.id
                        };
                        self.out.returned = Some(id);
                        if r.at != code.len() || !self.stack.is_empty() {
                            return Err(BinaryError::at(ErrorKind::InvalidReturn, at));
                        }
                        // The normalized operation graph preserves exact call
                        // identities and propagates their return dependencies.
                        // A forwarded call result is a supported recipe; only
                        // its subsequently resolved callee may be opaque.
                        if matches!(self.out.values[id.0 as usize], Value::UnknownLocal(_)) {
                            return Err(BinaryError::at(ErrorKind::UnknownReturn, at));
                        }
                        if matches!(
                            self.out.values[id.0 as usize],
                            Value::Allocation {
                                constructor: None,
                                ..
                            }
                        ) {
                            return Err(BinaryError::at(ErrorKind::InvalidReturn, at));
                        }
                    }
                    _ => return Err(BinaryError::at(ErrorKind::UnsupportedOpcode(opcode), at)),
                }
                Ok(())
            })();
            if let Err(mut error) = operation {
                if error.offset == 0 {
                    error.offset = at;
                }
                return Err(error);
            }
        }
        if self.out.returned.is_none() {
            return Err(BinaryError::at(ErrorKind::NoReturn, code.len()));
        }
        Ok(())
    }
}

pub fn summarize<'a>(
    class: &ClassFile<'a>,
    method: &MethodInfo<'a>,
    limits: Limits,
) -> MethodSummary<'a> {
    let out = MethodSummary {
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
    if method.max_locals as usize > limits.max_locals
        || method.max_stack as usize > limits.max_stack
        || method.code.is_some_and(|c| c.len() > limits.max_code_bytes)
    {
        return MethodSummary {
            unknown: Some(BinaryError::at(ErrorKind::ResourceLimit, 0)),
            ..out
        };
    }
    let mut vm = Interpreter {
        class,
        out,
        stack: Vec::with_capacity((method.max_stack as usize).min(64)),
        locals: vec![None; method.max_locals as usize],
        slots: 0,
        max_stack: method.max_stack as usize,
        limits,
        pc: 0,
    };
    if let Err(error) = vm.run(method) {
        vm.out.unknown = Some(error);
    }
    vm.out
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum EntryKind {
    Jar,
    /// Matches the capture producer's full sorted file inventory. Callers must
    /// prefer existing source recipes when admitting a missing binary body.
    Directory {
        files: u64,
        bytes: u64,
    },
    AbsentEmptyOutput,
    Unavailable,
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ClasspathEntry {
    pub path: PathBuf,
    pub sha256: ContentHash,
    pub kind: EntryKind,
}
#[derive(Clone, Copy, Debug)]
pub struct EntryProof {
    pub entry_index: usize,
    pub sha256: ContentHash,
    pub absent: bool,
}
#[derive(Debug)]
pub struct ResolutionProof {
    pub selected_entry: Option<usize>,
    pub class_hash: Option<ContentHash>,
    pub examined: Vec<EntryProof>,
}
#[derive(Debug)]
pub struct ResolvedClass {
    pub bytes: Vec<u8>,
    pub proof: ResolutionProof,
}
#[derive(Debug)]
pub enum ClassLookup {
    Found(ResolvedClass),
    Absent(ResolutionProof),
}
struct Jar {
    bytes: Vec<u8>,
    members: Vec<ZipMember>,
}
struct ZipMember {
    name: std::ops::Range<usize>,
    logical: std::ops::Range<usize>,
    version: u16,
    local: usize,
    compressed: usize,
    size: usize,
    crc: u32,
    method: u16,
    flags: u16,
}
struct Directory {
    files: Vec<DirectoryFile>,
}
enum Loaded {
    Jar(Jar),
    Directory(Directory),
    Empty,
    Failed(BinaryError),
}
/// One immutable input owner, reusable across ordered compiler contexts. A
/// failed/opaque input is retained too: sharing must never erase an earlier
/// unknown and permit a later classpath candidate to win.
#[derive(Clone)]
pub struct AdmittedEntry {
    entry: Arc<ClasspathEntry>,
    loaded: Arc<Loaded>,
    java_feature: Option<u16>,
    retained: usize,
}
impl AdmittedEntry {
    pub fn reservation_bytes(entry: &ClasspathEntry, limits: Limits) -> Result<(usize, usize)> {
        match entry.kind {
            EntryKind::Jar => {
                let size = std::fs::metadata(&entry.path)
                    .map_err(|_| BinaryError::at(ErrorKind::Io, 0))?
                    .len();
                if size > limits.max_archive_bytes as u64 {
                    return Err(BinaryError::at(ErrorKind::ResourceLimit, 0));
                }
                Ok((
                    size as usize
                        + 1
                        + 65535 * std::mem::size_of::<ZipMember>()
                        + limits.max_class_bytes,
                    size as usize,
                ))
            }
            EntryKind::Directory { .. } => Ok((
                limits.max_retained_bytes.min(64 * 1024 * 1024),
                limits.max_archive_bytes,
            )),
            _ => Ok((0, limits.max_archive_bytes)),
        }
    }
    pub fn admit(entry: ClasspathEntry, limits: Limits, java_feature: Option<u16>) -> Result<Self> {
        let mut loader =
            CapturedClasspath::new(vec![entry.clone()], limits)?.with_java_feature(java_feature)?;
        let _ = loader.admit(0);
        Ok(Self {
            entry: Arc::new(entry),
            loaded: loader.loaded[0].take().unwrap(),
            java_feature,
            retained: loader.retained,
        })
    }
    pub fn retained_bytes(&self) -> usize {
        self.retained
    }
    pub fn error(&self) -> Option<BinaryError> {
        match self.loaded.as_ref() {
            Loaded::Failed(error) => Some(*error),
            _ => None,
        }
    }
}

/// Query workers share an admitted classpath owner; jars are verified into
/// bounded owned buffers once, so external mutation cannot alter their reads.
/// Directory outputs retain the complete captured file/hash inventory. Selected
/// class bytes are read into owned buffers and checked against that inventory.
pub struct CapturedClasspath {
    pub entries: Vec<ClasspathEntry>,
    loaded: Vec<Option<Arc<Loaded>>>,
    limits: Limits,
    retained: usize,
    java_feature: Option<u16>,
}
impl CapturedClasspath {
    pub fn new(entries: Vec<ClasspathEntry>, limits: Limits) -> Result<Self> {
        if entries.len() > 65_535 {
            return Err(BinaryError::at(ErrorKind::ResourceLimit, 0));
        }
        let loaded = (0..entries.len()).map(|_| None).collect();
        Ok(Self {
            entries,
            loaded,
            limits,
            retained: 0,
            java_feature: None,
        })
    }
    /// Exact captured JVM feature version. Missing authority keeps manifest-
    /// enabled multi-release class selection unknown rather than choosing base.
    pub fn with_java_feature(mut self, feature: Option<u16>) -> Result<Self> {
        if feature.is_some_and(|version| version == 0 || version > 255) {
            return Err(BinaryError::at(ErrorKind::UnsupportedClassVersion, 0));
        }
        self.java_feature = feature;
        Ok(self)
    }
    /// Reuse only exact path/digest/kind/runtime snapshots. Shared owned bytes
    /// are charged by the admission owner once; these context handles own no
    /// additional archive buffers and preserve their supplied classpath order.
    pub fn from_admitted(
        entries: Vec<ClasspathEntry>,
        snapshots: &[&AdmittedEntry],
        limits: Limits,
        java_feature: Option<u16>,
    ) -> Result<Self> {
        if entries.len() != snapshots.len() {
            return Err(BinaryError::at(ErrorKind::InvalidCode, 0));
        }
        let mut loader = Self::new(entries, limits)?.with_java_feature(java_feature)?;
        for (i, (entry, snapshot)) in loader.entries.iter().zip(snapshots).enumerate() {
            if entry != snapshot.entry.as_ref() || java_feature != snapshot.java_feature {
                return Err(BinaryError::at(ErrorKind::HashMismatch, i));
            }
            loader.loaded[i] = Some(snapshot.loaded.clone());
        }
        Ok(loader)
    }
    pub fn retained_bytes(&self) -> usize {
        self.retained
    }
    /// Complete, hash-admitted class names in one ordered entry. Callers may
    /// retain this compact inventory while dropping archive buffers; this is
    /// useful when the same entry occurs in many compiler contexts.
    pub fn class_names(&mut self, index: usize) -> Result<Vec<String>> {
        if index >= self.entries.len() {
            return Err(BinaryError::at(ErrorKind::InvalidClassName, index));
        }
        self.admit(index)?;
        let mut names: Vec<String> = match self.loaded[index].as_ref().unwrap().as_ref() {
            Loaded::Jar(jar) => {
                let mut names = Vec::new();
                for member in &jar.members {
                    let name = std::str::from_utf8(&jar.bytes[member.logical.clone()])
                        .map_err(|_| BinaryError::at(ErrorKind::InvalidUtf8, index))?;
                    if let Some(owner) = name.strip_suffix(".class") {
                        names.push(owner.to_owned());
                    }
                }
                names
            }
            Loaded::Directory(directory) => directory
                .files
                .iter()
                .filter_map(|file| file.path.strip_suffix(".class").map(str::to_owned))
                .collect(),
            Loaded::Empty => Vec::new(),
            Loaded::Failed(error) => return Err(*error),
        };
        names.sort_unstable();
        names.dedup();
        Ok(names)
    }
    /// Read the main JAR manifest's Class-Path from already admitted bytes.
    /// This exposes metadata only; normal class lookup never expands it.
    pub fn manifest_class_path(&mut self, index: usize) -> Result<Vec<String>> {
        if index >= self.entries.len() {
            return Err(BinaryError::at(ErrorKind::InvalidClassName, index));
        }
        self.admit(index)?;
        match self.loaded[index].as_ref().unwrap().as_ref() {
            Loaded::Jar(jar) => {
                let Some(member) = jar
                    .members
                    .iter()
                    .find(|m| &jar.bytes[m.logical.clone()] == b"META-INF/MANIFEST.MF")
                else {
                    return Ok(Vec::new());
                };
                if member.size > 1024 * 1024 {
                    return Err(BinaryError::at(ErrorKind::ResourceLimit, index));
                }
                manifest_class_path(&zip_read(jar, member, self.limits)?)
            }
            Loaded::Failed(error) => Err(*error),
            _ => Ok(Vec::new()),
        }
    }
    /// Borrow the sorted path, size and digest inventory of a verified directory.
    pub fn directory_files(
        &mut self,
        index: usize,
    ) -> Result<impl ExactSizeIterator<Item = (&str, u64, ContentHash)>> {
        if index >= self.entries.len() {
            return Err(BinaryError::at(ErrorKind::InvalidClassName, index));
        }
        self.admit(index)?;
        let Loaded::Directory(directory) = self.loaded[index].as_ref().unwrap().as_ref() else {
            return Err(BinaryError::at(
                ErrorKind::DirectoryFingerprintMismatch,
                index,
            ));
        };
        Ok(directory
            .files
            .iter()
            .map(|file| (file.path.as_str(), file.size, file.sha)))
    }

    /// Validate every ordered input before reusing a derived summary manifest.
    /// This is admission work, outside per-edge/query execution.
    pub fn verify_all(&mut self) -> Result<()> {
        for index in 0..self.entries.len() {
            self.admit(index)?;
        }
        Ok(())
    }
    fn admit(&mut self, index: usize) -> Result<()> {
        if let Some(previous) = &self.loaded[index] {
            return match previous.as_ref() {
                Loaded::Failed(e) => Err(*e),
                _ => Ok(()),
            };
        }
        let entry = &self.entries[index];
        let observed = (|| -> Result<(Loaded, usize)> {
            match entry.kind {
                EntryKind::Jar => {
                    let bytes = read_bounded(
                        &entry.path,
                        self.limits
                            .max_archive_bytes
                            .min(self.limits.max_retained_bytes.saturating_sub(self.retained)),
                    )?;
                    if hash(&bytes) != entry.sha256 {
                        return Err(BinaryError::at(ErrorKind::HashMismatch, index));
                    }
                    let mut jar = Jar {
                        members: zip_members(&bytes)?,
                        bytes,
                    };
                    select_java_members(&mut jar, self.java_feature, self.limits)?;
                    let retained = jar
                        .bytes
                        .capacity()
                        .checked_add(jar.members.capacity() * std::mem::size_of::<ZipMember>())
                        .ok_or(BinaryError::at(ErrorKind::ResourceLimit, index))?;
                    Ok((Loaded::Jar(jar), retained))
                }
                EntryKind::Directory { files, bytes } => {
                    let directory =
                        directory_snapshot(&entry.path, entry.sha256, files, bytes, self.limits)?;
                    let retained = directory.files.capacity()
                        * std::mem::size_of::<DirectoryFile>()
                        + directory
                            .files
                            .iter()
                            .map(|file| file.path.capacity())
                            .sum::<usize>();
                    Ok((Loaded::Directory(directory), retained))
                }
                EntryKind::AbsentEmptyOutput => {
                    match std::fs::symlink_metadata(&entry.path) {
                        Err(e) if e.kind() == std::io::ErrorKind::NotFound => (),
                        Err(_) => return Err(BinaryError::at(ErrorKind::Io, index)),
                        Ok(_) => {
                            return Err(BinaryError::at(
                                ErrorKind::DirectoryFingerprintMismatch,
                                index,
                            ));
                        }
                    }
                    if entry.sha256 != hash(b"{\"kind\":\"absent_empty_project_output\"}") {
                        return Err(BinaryError::at(
                            ErrorKind::DirectoryFingerprintMismatch,
                            index,
                        ));
                    }
                    Ok((Loaded::Empty, 0))
                }
                EntryKind::Unavailable => Err(BinaryError::at(ErrorKind::UnavailableInput, index)),
            }
        })();
        match observed {
            Ok((loaded, bytes))
                if self
                    .retained
                    .checked_add(bytes)
                    .is_some_and(|b| b <= self.limits.max_retained_bytes) =>
            {
                self.retained += bytes;
                self.loaded[index] = Some(Arc::new(loaded));
                Ok(())
            }
            Ok(_) => {
                let e = BinaryError::at(ErrorKind::ResourceLimit, index);
                self.loaded[index] = Some(Arc::new(Loaded::Failed(e)));
                Err(e)
            }
            Err(e) => {
                self.loaded[index] = Some(Arc::new(Loaded::Failed(e)));
                Err(e)
            }
        }
    }
    /// Captured order is authoritative. Every preceding absence is hash-bound;
    /// a corrupt/unavailable earlier entry never permits choosing a later class.
    pub fn lookup(&mut self, owner: &str) -> Result<ClassLookup> {
        valid_class_name(owner)?;
        let requested = format!("{owner}.class");
        let mut examined = Vec::new();
        for index in 0..self.entries.len() {
            self.admit(index)?;
            let bytes = match self.loaded[index].as_ref().unwrap().as_ref() {
                Loaded::Jar(jar) => {
                    match jar.members.binary_search_by(|m| {
                        jar.bytes[m.logical.clone()].cmp(requested.as_bytes())
                    }) {
                        Ok(member) => Some(zip_read(jar, &jar.members[member], self.limits)?),
                        Err(_) => None,
                    }
                }
                Loaded::Directory(directory) => {
                    match directory
                        .files
                        .binary_search_by(|file| file.path.as_str().cmp(&requested))
                    {
                        Ok(file) => {
                            let expected = &directory.files[file];
                            let mut path = self.entries[index].path.clone();
                            if std::fs::symlink_metadata(&path)
                                .map_err(|_| BinaryError::at(ErrorKind::Io, index))?
                                .file_type()
                                .is_symlink()
                            {
                                return Err(BinaryError::at(ErrorKind::SymlinkInput, index));
                            }
                            for component in Path::new(&expected.path).components() {
                                path.push(component);
                                let metadata = std::fs::symlink_metadata(&path)
                                    .map_err(|_| BinaryError::at(ErrorKind::Io, index))?;
                                if metadata.file_type().is_symlink() {
                                    return Err(BinaryError::at(ErrorKind::SymlinkInput, index));
                                }
                            }
                            let bytes = read_bounded(&path, self.limits.max_class_bytes)?;
                            if bytes.len() as u64 != expected.size || hash(&bytes) != expected.sha {
                                return Err(BinaryError::at(ErrorKind::HashMismatch, index));
                            }
                            Some(bytes)
                        }
                        Err(_) => None,
                    }
                }
                Loaded::Empty => None,
                Loaded::Failed(e) => return Err(*e),
            };
            examined.push(EntryProof {
                entry_index: index,
                sha256: self.entries[index].sha256,
                absent: bytes.is_none(),
            });
            if let Some(bytes) = bytes {
                let class = parse_class(&bytes, self.limits)?;
                if class.name != owner {
                    return Err(BinaryError::at(ErrorKind::ClassIdentityMismatch, index));
                }
                if self
                    .java_feature
                    .is_some_and(|feature| class.major > feature + 44 || class.minor == u16::MAX)
                {
                    return Err(BinaryError::at(ErrorKind::UnsupportedClassVersion, index));
                }
                drop(class);
                let class_hash = hash(&bytes);
                return Ok(ClassLookup::Found(ResolvedClass {
                    bytes,
                    proof: ResolutionProof {
                        selected_entry: Some(index),
                        class_hash: Some(class_hash),
                        examined,
                    },
                }));
            }
        }
        Ok(ClassLookup::Absent(ResolutionProof {
            selected_entry: None,
            class_hash: None,
            examined,
        }))
    }
    pub fn resolve(&mut self, owner: &str) -> Result<ResolvedClass> {
        match self.lookup(owner)? {
            ClassLookup::Found(found) => Ok(found),
            ClassLookup::Absent(_) => Err(BinaryError::at(ErrorKind::ClassNotFound, 0)),
        }
    }
}
fn hash(bytes: &[u8]) -> ContentHash {
    ContentHash(Sha256::digest(bytes).into())
}
fn read_bounded(path: &Path, maximum: usize) -> Result<Vec<u8>> {
    let mut file = std::fs::File::open(path).map_err(|_| BinaryError::at(ErrorKind::Io, 0))?;
    let size = file
        .metadata()
        .map_err(|_| BinaryError::at(ErrorKind::Io, 0))?
        .len();
    if size > maximum as u64 {
        return Err(BinaryError::at(ErrorKind::ResourceLimit, 0));
    }
    let mut bytes = Vec::new();
    bytes
        .try_reserve_exact(size as usize + 1)
        .map_err(|_| BinaryError::at(ErrorKind::ResourceLimit, 0))?;
    (&mut file)
        .take(size.saturating_add(1))
        .read_to_end(&mut bytes)
        .map_err(|_| BinaryError::at(ErrorKind::Io, 0))?;
    if bytes.len() > maximum || bytes.len() as u64 != size {
        return Err(BinaryError::at(ErrorKind::ResourceLimit, 0));
    }
    Ok(bytes)
}
fn le16(bytes: &[u8], at: usize) -> Result<u16> {
    let end = at
        .checked_add(2)
        .ok_or(BinaryError::at(ErrorKind::InvalidZip, at))?;
    Ok(u16::from_le_bytes(
        bytes
            .get(at..end)
            .ok_or(BinaryError::at(ErrorKind::InvalidZip, at))?
            .try_into()
            .unwrap(),
    ))
}
fn le32(bytes: &[u8], at: usize) -> Result<u32> {
    let end = at
        .checked_add(4)
        .ok_or(BinaryError::at(ErrorKind::InvalidZip, at))?;
    Ok(u32::from_le_bytes(
        bytes
            .get(at..end)
            .ok_or(BinaryError::at(ErrorKind::InvalidZip, at))?
            .try_into()
            .unwrap(),
    ))
}
fn zip_members(bytes: &[u8]) -> Result<Vec<ZipMember>> {
    if bytes.len() < 22 {
        return Err(BinaryError::at(ErrorKind::InvalidZip, 0));
    }
    let begin = bytes.len().saturating_sub(22 + 65_535);
    let end = (begin..=bytes.len() - 22)
        .rev()
        .find(|&at| {
            bytes[at..at + 4] == [0x50, 0x4b, 0x05, 0x06]
                && le16(bytes, at + 20).is_ok_and(|n| at + 22 + n as usize == bytes.len())
        })
        .ok_or(BinaryError::at(ErrorKind::InvalidZip, 0))?;
    let count = le16(bytes, end + 10)? as usize;
    if le16(bytes, end + 4)? != 0
        || le16(bytes, end + 6)? != 0
        || le16(bytes, end + 8)? as usize != count
        || count == 65_535
    {
        return Err(BinaryError::at(ErrorKind::UnsupportedZip, end));
    }
    let size = le32(bytes, end + 12)? as usize;
    let mut at = le32(bytes, end + 16)? as usize;
    let central_end = at
        .checked_add(size)
        .ok_or(BinaryError::at(ErrorKind::InvalidZip, at))?;
    if central_end != end {
        return Err(BinaryError::at(ErrorKind::InvalidZip, at));
    }
    let mut members = Vec::with_capacity(count);
    for _ in 0..count {
        if at > bytes.len().saturating_sub(46) {
            return Err(BinaryError::at(ErrorKind::InvalidZip, at));
        }
        if le32(bytes, at)? != 0x02014b50 {
            return Err(BinaryError::at(ErrorKind::InvalidZip, at));
        }
        let flags = le16(bytes, at + 8)?;
        let method = le16(bytes, at + 10)?;
        if flags & 0x41 != 0 || le16(bytes, at + 34)? != 0 {
            return Err(BinaryError::at(ErrorKind::UnsupportedZip, at));
        }
        let compressed = le32(bytes, at + 20)? as usize;
        let size = le32(bytes, at + 24)? as usize;
        let local = le32(bytes, at + 42)? as usize;
        if local > bytes.len().saturating_sub(30) {
            return Err(BinaryError::at(ErrorKind::InvalidZip, at));
        }
        if [compressed, size, local].contains(&(u32::MAX as usize)) {
            return Err(BinaryError::at(ErrorKind::UnsupportedZip, at));
        }
        let n = le16(bytes, at + 28)? as usize;
        let extra = le16(bytes, at + 30)? as usize;
        let comment = le16(bytes, at + 32)? as usize;
        let start = at
            .checked_add(46)
            .ok_or(BinaryError::at(ErrorKind::InvalidZip, at))?;
        let name = start
            ..start
                .checked_add(n)
                .ok_or(BinaryError::at(ErrorKind::InvalidZip, at))?;
        let raw = bytes
            .get(name.clone())
            .ok_or(BinaryError::at(ErrorKind::InvalidZip, at))?;
        if std::str::from_utf8(raw).is_err() {
            return Err(BinaryError::at(ErrorKind::InvalidUtf8, at));
        }
        members.push(ZipMember {
            name: name.clone(),
            logical: name.clone(),
            version: 0,
            local,
            compressed,
            size,
            crc: le32(bytes, at + 16)?,
            method,
            flags,
        });
        at = name
            .end
            .checked_add(extra)
            .and_then(|n| n.checked_add(comment))
            .ok_or(BinaryError::at(ErrorKind::InvalidZip, at))?;
        if at > central_end {
            return Err(BinaryError::at(ErrorKind::InvalidZip, at));
        }
    }
    if at != central_end {
        return Err(BinaryError::at(ErrorKind::InvalidZip, at));
    }
    members.sort_unstable_by(|a, b| bytes[a.name.clone()].cmp(&bytes[b.name.clone()]));
    if members
        .windows(2)
        .any(|w| bytes[w[0].name.clone()] == bytes[w[1].name.clone()])
    {
        return Err(BinaryError::at(ErrorKind::DuplicateZipMember, 0));
    }
    Ok(members)
}
/// JAR File Specification / JarFile.getEntry: the manifest opts in, then the
/// highest version <= the captured feature shadows base (versions start at 9).
fn select_java_members(jar: &mut Jar, feature: Option<u16>, limits: Limits) -> Result<()> {
    let mut manifest = None;
    for (i, member) in jar.members.iter().enumerate() {
        if jar.bytes[member.name.clone()].eq_ignore_ascii_case(b"META-INF/MANIFEST.MF") {
            if manifest.replace(i).is_some() {
                return Err(BinaryError::at(ErrorKind::InvalidZip, i));
            }
        }
    }
    let enabled = if let Some(index) = manifest {
        let bytes = zip_read(jar, &jar.members[index], limits)?;
        manifest_multi_release(&bytes)?
    } else {
        false
    };
    let prefix = b"META-INF/versions/";
    let versioned = jar
        .members
        .iter()
        .any(|member| jar.bytes[member.name.clone()].starts_with(prefix));
    if enabled && versioned && feature.is_none() {
        return Err(BinaryError::at(ErrorKind::MultiReleaseArchive, 0));
    }
    let max = feature.unwrap_or(8);
    jar.members.retain_mut(|member| {
        let name = &jar.bytes[member.name.clone()];
        let Some(tail) = name.strip_prefix(prefix) else {
            return true;
        };
        if !enabled || max < 9 {
            return false;
        }
        let Some(slash) = tail.iter().position(|b| *b == b'/') else {
            return false;
        };
        let version = &tail[..slash];
        if version.first() == Some(&b'0')
            || version.is_empty()
            || !version.iter().all(u8::is_ascii_digit)
        {
            return false;
        }
        let Some(version) = version.iter().try_fold(0u16, |n, d| {
            n.checked_mul(10)?.checked_add((d - b'0') as u16)
        }) else {
            return false;
        };
        if version < 9 || version > max || tail[slash + 1..].starts_with(b"META-INF/") {
            return false;
        }
        member.logical.start = member.name.start + prefix.len() + slash + 1;
        member.version = version;
        true
    });
    jar.members.sort_unstable_by(|a, b| {
        jar.bytes[a.logical.clone()]
            .cmp(&jar.bytes[b.logical.clone()])
            .then_with(|| b.version.cmp(&a.version))
    });
    jar.members
        .dedup_by(|a, b| jar.bytes[a.logical.clone()] == jar.bytes[b.logical.clone()]);
    Ok(())
}
fn manifest_multi_release(bytes: &[u8]) -> Result<bool> {
    let text =
        std::str::from_utf8(bytes).map_err(|_| BinaryError::at(ErrorKind::InvalidUtf8, 0))?;
    let mut key: Option<&str> = None;
    let mut value = String::new();
    let mut result = None;
    let finish = |key: Option<&str>, value: &str, result: &mut Option<bool>| -> Result<()> {
        if key.is_some_and(|key| key.eq_ignore_ascii_case("Multi-Release")) {
            if result.is_some() {
                return Err(BinaryError::at(ErrorKind::InvalidZip, 0));
            }
            *result = Some(value.eq_ignore_ascii_case("true"));
        }
        Ok(())
    };
    // Main section only. Folded values follow the manifest continuation rule.
    for line in text.lines() {
        if line.is_empty() {
            break;
        }
        if let Some(continuation) = line.strip_prefix(' ') {
            if key.is_none() {
                return Err(BinaryError::at(ErrorKind::InvalidZip, 0));
            }
            if key.is_some_and(|key| key.eq_ignore_ascii_case("Multi-Release")) {
                if value != "!" && value.len() + continuation.len() <= 4 {
                    value.push_str(continuation);
                } else {
                    value.clear();
                    value.push('!');
                }
            }
            continue;
        }
        finish(key, &value, &mut result)?;
        let Some((next, next_value)) = line.split_once(": ") else {
            return Err(BinaryError::at(ErrorKind::InvalidZip, 0));
        };
        if next.is_empty()
            || !next
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'-' | b'_'))
        {
            return Err(BinaryError::at(ErrorKind::InvalidZip, 0));
        }
        key = Some(next);
        value.clear();
        if next.eq_ignore_ascii_case("Multi-Release") {
            if next_value.len() <= 4 {
                value.push_str(next_value);
            } else {
                value.push('!');
            }
        }
    }
    finish(key, &value, &mut result)?;
    Ok(result.unwrap_or(false))
}
fn manifest_class_path(bytes: &[u8]) -> Result<Vec<String>> {
    if bytes.len() > 1024 * 1024 {
        return Err(BinaryError::at(ErrorKind::ResourceLimit, 0));
    }
    let text =
        std::str::from_utf8(bytes).map_err(|_| BinaryError::at(ErrorKind::InvalidUtf8, 0))?;
    let mut key: Option<&str> = None;
    let mut value = String::new();
    let mut result = None;
    let finish = |key: Option<&str>, value: &str, result: &mut Option<Vec<String>>| -> Result<()> {
        if key.is_some_and(|key| key.eq_ignore_ascii_case("Class-Path")) {
            if result.is_some() {
                return Err(BinaryError::at(ErrorKind::InvalidZip, 0));
            }
            let mut entries = Vec::new();
            for token in value.split_ascii_whitespace() {
                if entries.len() >= 4096 {
                    return Err(BinaryError::at(ErrorKind::ResourceLimit, 0));
                }
                entries.push(token.to_owned());
            }
            *result = Some(entries);
        }
        Ok(())
    };
    for line in text.lines() {
        if line.is_empty() {
            break;
        }
        if let Some(continuation) = line.strip_prefix(' ') {
            if key.is_none() {
                return Err(BinaryError::at(ErrorKind::InvalidZip, 0));
            }
            if key.is_some_and(|key| key.eq_ignore_ascii_case("Class-Path")) {
                value.push_str(continuation);
            }
            continue;
        }
        finish(key, &value, &mut result)?;
        let Some((next, next_value)) = line.split_once(": ") else {
            return Err(BinaryError::at(ErrorKind::InvalidZip, 0));
        };
        if next.is_empty()
            || !next
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'-' | b'_'))
        {
            return Err(BinaryError::at(ErrorKind::InvalidZip, 0));
        }
        key = Some(next);
        value.clear();
        if next.eq_ignore_ascii_case("Class-Path") {
            value.push_str(next_value);
        }
    }
    finish(key, &value, &mut result)?;
    Ok(result.unwrap_or_default())
}
fn zip_read(jar: &Jar, member: &ZipMember, limits: Limits) -> Result<Vec<u8>> {
    let bytes = &jar.bytes;
    let at = member.local;
    if member.size > limits.max_class_bytes {
        return Err(BinaryError::at(ErrorKind::ResourceLimit, at));
    }
    if le32(bytes, at)? != 0x04034b50
        || le16(bytes, at + 6)? != member.flags
        || le16(bytes, at + 8)? != member.method
    {
        return Err(BinaryError::at(ErrorKind::InvalidZip, at));
    }
    let n = le16(bytes, at + 26)? as usize;
    let extra = le16(bytes, at + 28)? as usize;
    let name = at
        .checked_add(30)
        .ok_or(BinaryError::at(ErrorKind::InvalidZip, at))?;
    if bytes.get(name..name + n) != Some(&bytes[member.name.clone()]) {
        return Err(BinaryError::at(ErrorKind::InvalidZip, at));
    }
    let start = name
        .checked_add(n)
        .and_then(|n| n.checked_add(extra))
        .ok_or(BinaryError::at(ErrorKind::InvalidZip, at))?;
    let compressed = bytes
        .get(
            start
                ..start
                    .checked_add(member.compressed)
                    .ok_or(BinaryError::at(ErrorKind::InvalidZip, at))?,
        )
        .ok_or(BinaryError::at(ErrorKind::InvalidZip, at))?;
    let output = match member.method {
        0 => {
            if member.compressed != member.size {
                return Err(BinaryError::at(ErrorKind::InvalidZip, at));
            }
            compressed.to_vec()
        }
        8 => {
            let mut out = Vec::new();
            out.try_reserve_exact(member.size)
                .map_err(|_| BinaryError::at(ErrorKind::ResourceLimit, at))?;
            let mut decoder = flate2::read::DeflateDecoder::new(compressed);
            (&mut decoder)
                .take(member.size as u64 + 1)
                .read_to_end(&mut out)
                .map_err(|_| BinaryError::at(ErrorKind::InvalidZip, at))?;
            if out.len() != member.size || decoder.total_in() != compressed.len() as u64 {
                return Err(BinaryError::at(ErrorKind::InvalidZip, at));
            }
            out
        }
        _ => return Err(BinaryError::at(ErrorKind::UnsupportedCompression, at)),
    };
    if crc32(&output) != member.crc {
        return Err(BinaryError::at(ErrorKind::BadCrc, at));
    }
    Ok(output)
}
const fn crc_table() -> [u32; 256] {
    let mut out = [0; 256];
    let mut i = 0;
    while i < 256 {
        let mut n = i as u32;
        let mut b = 0;
        while b < 8 {
            n = if n & 1 == 1 {
                0xedb88320 ^ (n >> 1)
            } else {
                n >> 1
            };
            b += 1;
        }
        out[i] = n;
        i += 1;
    }
    out
}
fn crc32(bytes: &[u8]) -> u32 {
    const TABLE: [u32; 256] = crc_table();
    let mut crc = 0xffff_ffff;
    for &b in bytes {
        crc = TABLE[((crc as u8) ^ b) as usize] ^ (crc >> 8);
    }
    !crc
}

struct DirectoryFile {
    path: String,
    size: u64,
    sha: ContentHash,
}
fn directory_snapshot(
    root: &Path,
    expected: ContentHash,
    expected_files: u64,
    expected_bytes: u64,
    limits: Limits,
) -> Result<Directory> {
    if expected_files > limits.max_directory_files as u64
        || expected_bytes > limits.max_directory_bytes
    {
        return Err(BinaryError::at(ErrorKind::ResourceLimit, 0));
    }
    let meta = std::fs::symlink_metadata(root).map_err(|_| BinaryError::at(ErrorKind::Io, 0))?;
    if meta.file_type().is_symlink() {
        return Err(BinaryError::at(ErrorKind::SymlinkInput, 0));
    }
    if !meta.is_dir() {
        return Err(BinaryError::at(ErrorKind::DirectoryFingerprintMismatch, 0));
    }
    let mut pending = vec![root.to_path_buf()];
    let mut inventory = Vec::new();
    let mut path_bytes = root.as_os_str().len();
    let mut total = 0u64;
    let mut directories = 0usize;
    while let Some(directory) = pending.pop() {
        path_bytes = path_bytes.saturating_sub(directory.as_os_str().len());
        directories += 1;
        if directories > limits.max_directory_files.max(1) {
            return Err(BinaryError::at(ErrorKind::ResourceLimit, 0));
        }
        for entry in std::fs::read_dir(directory).map_err(|_| BinaryError::at(ErrorKind::Io, 0))? {
            let entry = entry.map_err(|_| BinaryError::at(ErrorKind::Io, 0))?;
            let filetype = entry
                .file_type()
                .map_err(|_| BinaryError::at(ErrorKind::Io, 0))?;
            if filetype.is_symlink() {
                return Err(BinaryError::at(ErrorKind::SymlinkInput, 0));
            }
            if filetype.is_dir() {
                if pending.len() + directories >= limits.max_directory_files.max(1) {
                    return Err(BinaryError::at(ErrorKind::ResourceLimit, 0));
                }
                let path = entry.path();
                path_bytes = path_bytes.saturating_add(path.as_os_str().len());
                if path_bytes
                    + pending.capacity().max(4).max(2 * (pending.len() + 1))
                        * std::mem::size_of::<PathBuf>()
                    + inventory.capacity() * std::mem::size_of::<DirectoryFile>()
                    > limits.max_retained_bytes
                {
                    return Err(BinaryError::at(ErrorKind::ResourceLimit, 0));
                }
                pending.push(path);
                continue;
            }
            if !filetype.is_file() {
                return Err(BinaryError::at(ErrorKind::DirectoryFingerprintMismatch, 0));
            }
            if inventory.len() >= limits.max_directory_files {
                return Err(BinaryError::at(ErrorKind::ResourceLimit, 0));
            }
            let path = entry.path();
            let relative = path
                .strip_prefix(root)
                .map_err(|_| BinaryError::at(ErrorKind::Io, 0))?
                .to_str()
                .ok_or(BinaryError::at(ErrorKind::InvalidUtf8, 0))?
                .replace(std::path::MAIN_SEPARATOR, "/");
            path_bytes = path_bytes.saturating_add(relative.capacity());
            if path_bytes
                + pending.capacity() * std::mem::size_of::<PathBuf>()
                + inventory.capacity().max(4).max(2 * (inventory.len() + 1))
                    * std::mem::size_of::<DirectoryFile>()
                > limits.max_retained_bytes
            {
                return Err(BinaryError::at(ErrorKind::ResourceLimit, 0));
            }
            let mut file =
                std::fs::File::open(&path).map_err(|_| BinaryError::at(ErrorKind::Io, 0))?;
            let mut digest = Sha256::new();
            let mut size = 0u64;
            let mut block = [0; 64 * 1024];
            loop {
                let n = file
                    .read(&mut block)
                    .map_err(|_| BinaryError::at(ErrorKind::Io, 0))?;
                if n == 0 {
                    break;
                }
                size = size
                    .checked_add(n as u64)
                    .ok_or(BinaryError::at(ErrorKind::ResourceLimit, 0))?;
                total = total
                    .checked_add(n as u64)
                    .ok_or(BinaryError::at(ErrorKind::ResourceLimit, 0))?;
                if total > limits.max_directory_bytes {
                    return Err(BinaryError::at(ErrorKind::ResourceLimit, 0));
                }
                digest.update(&block[..n]);
            }
            inventory.push(DirectoryFile {
                path: relative,
                size,
                sha: ContentHash(digest.finalize().into()),
            });
        }
    }
    inventory.sort_unstable_by(|a, b| a.path.cmp(&b.path));
    if inventory.len() as u64 != expected_files || total != expected_bytes {
        return Err(BinaryError::at(ErrorKind::DirectoryFingerprintMismatch, 0));
    }
    let mut sink = DigestWriter {
        hash: Sha256::new(),
        bytes: [0; 4096],
        used: 0,
    };
    use std::io::Write;
    sink.write_all(b"[")
        .map_err(|_| BinaryError::at(ErrorKind::Io, 0))?;
    for (i, file) in inventory.iter().enumerate() {
        if i > 0 {
            sink.write_all(b",").unwrap();
        }
        write!(sink, "{{\"bytes\":{},\"path\":", file.size).unwrap();
        json_string(&mut sink, &file.path);
        write!(sink, ",\"sha256\":\"{}\"}}", file.sha).unwrap();
    }
    sink.write_all(b"]").unwrap();
    sink.flush().unwrap();
    if ContentHash(sink.hash.finalize().into()) != expected {
        return Err(BinaryError::at(ErrorKind::DirectoryFingerprintMismatch, 0));
    }
    Ok(Directory { files: inventory })
}
struct DigestWriter {
    hash: Sha256,
    bytes: [u8; 4096],
    used: usize,
}
impl std::io::Write for DigestWriter {
    fn write(&mut self, mut input: &[u8]) -> std::io::Result<usize> {
        let n = input.len();
        while !input.is_empty() {
            let take = input.len().min(self.bytes.len() - self.used);
            self.bytes[self.used..self.used + take].copy_from_slice(&input[..take]);
            self.used += take;
            input = &input[take..];
            if self.used == self.bytes.len() {
                self.flush()?;
            }
        }
        Ok(n)
    }
    fn flush(&mut self) -> std::io::Result<()> {
        self.hash.update(&self.bytes[..self.used]);
        self.used = 0;
        Ok(())
    }
}
fn json_string(out: &mut DigestWriter, s: &str) {
    use std::io::Write;
    out.write_all(b"\"").unwrap();
    for c in s.chars() {
        match c {
            '"' => out.write_all(b"\\\"").unwrap(),
            '\\' => out.write_all(b"\\\\").unwrap(),
            '\n' => out.write_all(b"\\n").unwrap(),
            '\r' => out.write_all(b"\\r").unwrap(),
            '\t' => out.write_all(b"\\t").unwrap(),
            '\u{8}' => out.write_all(b"\\b").unwrap(),
            '\u{c}' => out.write_all(b"\\f").unwrap(),
            c if !(' '..='~').contains(&c) => {
                let mut units = [0; 2];
                for unit in c.encode_utf16(&mut units) {
                    write!(out, "\\u{unit:04x}").unwrap();
                }
            }
            c => out.write_all(&[c as u8]).unwrap(),
        }
    }
    out.write_all(b"\"").unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;
    const PROBE: &[u8] = include_bytes!("../../../fixtures/binary/classes/fixture/Probe.class");
    const MADE: &[u8] = include_bytes!("../../../fixtures/binary/classes/fixture/Made.class");
    const CHILD: &[u8] = include_bytes!("../../../fixtures/binary/classes/fixture/Child.class");
    fn fixture(name: &str) -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../fixtures/binary")
            .join(name)
    }
    fn jar(name: &str) -> ClasspathEntry {
        let path = fixture(name);
        let manifest: serde_json::Value =
            serde_json::from_str(include_str!("../../../fixtures/binary/manifest.json")).unwrap();
        let expected = manifest["outputs"]
            .as_array()
            .unwrap()
            .iter()
            .find(|r| r["path"] == name)
            .unwrap()["sha256"]
            .as_str()
            .unwrap();
        ClasspathEntry {
            path,
            sha256: ContentHash::from_hex(expected).unwrap(),
            kind: EntryKind::Jar,
        }
    }
    fn result<'a>(class: &ClassFile<'a>, name: &str) -> MethodSummary<'a> {
        summarize(class, class.method(name, None).unwrap(), Limits::default())
    }
    fn returned<'s, 'a>(summary: &'s MethodSummary<'a>) -> &'s Value<'a> {
        &summary.values[summary.returned.unwrap().0 as usize]
    }
    #[test]
    fn descriptors_validate_categories_arrays_and_exact_arity() {
        let d = method_descriptor("(JLjava/lang/Object;D[[I)Ljava/lang/Object;").unwrap();
        assert_eq!(d.parameter_count, 4);
        assert_eq!(d.parameter_slots, 6);
        assert_eq!(
            d.parameters().collect::<Vec<_>>(),
            ["J", "Ljava/lang/Object;", "D", "[[I"]
        );
        for invalid in [
            "",
            "I",
            "(V)V",
            "([V)V",
            "(Ljava/lang/Object)V",
            "(I)Vx",
            "(I)",
            "()L;",
            "()[",
            "(I)V\0",
        ] {
            assert!(method_descriptor(invalid).is_err(), "{invalid}");
        }
    }
    #[test]
    fn real_class_headers_and_exact_overload_lookup() {
        let class = parse_class(PROBE, Limits::default()).unwrap();
        assert_eq!(class.name, "fixture/Probe");
        assert_eq!(class.parent, Some("java/lang/Object"));
        assert_eq!(class.interfaces, ["fixture/Runner"]);
        assert_eq!(
            class.method("over", None).unwrap_err().kind,
            ErrorKind::AmbiguousMethod
        );
        assert!(class.method("over", Some("(I)Ljava/lang/Object;")).is_ok());
        assert!(
            class
                .method("over", Some("(Ljava/lang/String;)Ljava/lang/Object;"))
                .is_ok()
        );
        assert_eq!(
            class.method("missing", None).unwrap_err().kind,
            ErrorKind::MissingMethod
        );
    }
    #[test]
    fn allocation_alias_records_original_constructor_argument() {
        let class = parse_class(PROBE, Limits::default()).unwrap();
        let s = result(&class, "make");
        assert!(s.complete(), "{:?}", s.unknown);
        let Value::Allocation {
            class: allocated,
            constructor: Some(call),
            ..
        } = returned(&s)
        else {
            panic!("missing allocation")
        };
        assert_eq!(*allocated, "fixture/Made");
        let call = &s.calls[*call as usize];
        assert_eq!(call.member.name, "<init>");
        assert_eq!(call.kind, InvokeKind::Special);
        assert_eq!(call.member.descriptor, "(Ljava/lang/Runnable;)V");
        assert_eq!(
            s.values[s.arguments[call.arguments.start as usize].0 as usize],
            Value::Argument(0)
        );
        assert!(!s.effects_complete());
    }
    #[test]
    fn receiver_argument_field_and_wide_slot_identities_stay_distinct() {
        let class = parse_class(PROBE, Limits::default()).unwrap();
        assert_eq!(*returned(&result(&class, "forward")), Value::Argument(0));
        assert_eq!(*returned(&result(&class, "self")), Value::Receiver);
        assert_eq!(*returned(&result(&class, "wide")), Value::Argument(1));
        assert!(matches!(
            returned(&result(&class, "wideConstant")),
            Value::Constant { wide: true, .. }
        ));
        let s = result(&class, "getter");
        assert!(s.complete());
        let Value::Field { member, receiver } = returned(&s) else {
            panic!("missing getter")
        };
        assert_eq!(member.name, "callback");
        assert_eq!(member.owner, "fixture/Probe");
        assert_eq!(s.values[receiver.0 as usize], Value::Receiver);
    }
    #[test]
    fn virtual_calls_are_forwarding_relations_not_concrete_dispatch_proofs() {
        let class = parse_class(PROBE, Limits::default()).unwrap();
        let s = result(&class, "invoke");
        assert!(s.complete());
        let call = &s.calls[0];
        assert_eq!(call.kind, InvokeKind::Interface);
        assert_eq!(call.member.owner, "java/lang/Runnable");
        assert_eq!(call.member.name, "run");
        assert_eq!(
            s.values[call.receiver.unwrap().0 as usize],
            Value::Argument(0)
        );
        assert!(call.kind.requires_receiver_dispatch());
        let s = result(&class, "submit");
        let call = &s.calls[0];
        assert_eq!(s.values[call.receiver.unwrap().0 as usize], Value::Receiver);
        assert_eq!(
            s.values[s.arguments[call.arguments.start as usize].0 as usize],
            Value::Argument(0)
        );
        assert!(!s.effects_complete());
    }
    #[test]
    fn constructor_store_and_callback_invocation_are_separate() {
        let class = parse_class(MADE, Limits::default()).unwrap();
        let s = result(&class, "<init>");
        assert!(s.complete());
        assert_eq!(s.field_writes.len(), 1);
        let write = &s.field_writes[0];
        assert_eq!(write.member.name, "callback");
        assert_eq!(s.values[write.value.0 as usize], Value::Argument(0));
        assert!(!s.calls.iter().any(|c| c.member.name == "run"));
        let class = parse_class(PROBE, Limits::default()).unwrap();
        let s = result(&class, "callAfterStore");
        assert!(s.complete());
        assert!(
            s.calls
                .iter()
                .any(|c| c.member.name == "run" && c.kind == InvokeKind::Interface)
        );
    }
    #[test]
    fn unsupported_flow_keeps_known_prefix_and_does_not_invent_allocations() {
        let class = parse_class(PROBE, Limits::default()).unwrap();
        for name in ["branch", "declaredOnly"] {
            let s = result(&class, name);
            assert!(!s.complete(), "{name}");
            assert!(s.returned.is_none(), "{name}");
        }
        let lambda = result(&class, "indy");
        assert!(lambda.complete());
        assert!(matches!(returned(&lambda), Value::Lambda(0)));
        assert_eq!(lambda.lambdas.len(), 1);
        assert!(
            lambda.calls.is_empty(),
            "creation must not execute lambda body"
        );
        let s = result(&class, "partial");
        assert!(!s.complete());
        assert_eq!(s.calls[0].member.name, "run");
    }
    fn dynamic_index(class: &ClassFile<'_>) -> u16 {
        class
            .pool
            .iter()
            .position(|entry| matches!(entry, Constant::InvokeDynamic { .. }))
            .unwrap() as u16
    }
    #[test]
    fn typed_bootstrap_projection_is_borrowed_and_creation_stays_deferred() {
        let class = parse_class(PROBE, Limits::default()).unwrap();
        let dynamic = class.invoke_dynamic(dynamic_index(&class)).unwrap();
        assert_eq!(dynamic.name, "run");
        assert_eq!(dynamic.descriptor.text, "()Ljava/lang/Runnable;");
        assert_eq!(dynamic.bootstrap.method.kind, ReferenceKind::InvokeStatic);
        assert_eq!(
            dynamic.bootstrap.method.member.owner,
            "java/lang/invoke/LambdaMetafactory"
        );
        let arguments = dynamic.bootstrap.arguments;
        assert_eq!(arguments.len(), 3);
        assert_eq!(arguments.get(3), None);
        assert_eq!(arguments.get(usize::MAX), None);
        assert_eq!(
            class.method_type(arguments.get(0).unwrap()).unwrap().text,
            "()V"
        );
        let target = class.method_handle(arguments.get(1).unwrap()).unwrap();
        assert_eq!(target.kind, ReferenceKind::InvokeStatic);
        assert_eq!(target.member.owner, "fixture/Probe");
        let summary = result(&class, "indy");
        assert!(summary.complete());
        assert!(summary.calls.is_empty());
        assert_eq!(summary.lambdas[0].captures.len, 0);
        assert!(!summary.lambdas[0].serializable);
        let begin = PROBE.as_ptr() as usize;
        let end = begin + PROBE.len();
        for borrowed in [dynamic.name, dynamic.descriptor.text, target.member.name] {
            assert!((begin..end).contains(&(borrowed.as_ptr() as usize)));
        }
    }
    fn add_utf<'a>(class: &mut ClassFile<'a>, text: &'a str) -> u16 {
        let index = class.pool.len() as u16;
        class.pool.push(Constant::Utf8(text.as_bytes()));
        index
    }
    #[test]
    fn redundant_alt_bridge_protocol_preserves_property_and_rejects_extra_adaptation() {
        // Normalized protocol control mirrors ScalaTest's genuine flags=5,
        // bridgeCount=1 shape; the actual pinned class is an acceptance gate.
        let mut class = parse_class(PROBE, Limits::default()).unwrap();
        let dynamic = class.invoke_dynamic(dynamic_index(&class)).unwrap();
        let row = class.bootstrap_methods[0];
        let method_type = row.arguments.get(0).unwrap();
        let implementation = row.arguments.get(1).unwrap();
        let alt_name = add_utf(&mut class, "altMetafactory");
        let alt_descriptor = add_utf(
            &mut class,
            "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;[Ljava/lang/Object;)Ljava/lang/invoke/CallSite;",
        );
        let Constant::MethodHandle { reference, .. } = class.pool[row.handle as usize] else {
            panic!()
        };
        let Constant::Member { pair, .. } = class.pool[reference as usize] else {
            panic!()
        };
        class.pool[pair as usize] = Constant::Pair {
            name: alt_name,
            descriptor: alt_descriptor,
        };
        let flags = class.pool.len() as u16;
        class.pool.push(Constant::Integer(5));
        let count = class.pool.len() as u16;
        class.pool.push(Constant::Integer(1));
        let bytes: Vec<u8> = [
            method_type,
            implementation,
            method_type,
            flags,
            count,
            method_type,
        ]
        .into_iter()
        .flat_map(u16::to_be_bytes)
        .collect();
        class.bootstrap_methods[0].arguments = BootstrapArguments(&bytes);
        let lambda = class
            .lambda(
                class.invoke_dynamic(dynamic_index(&class)).unwrap(),
                ValueRange { start: 0, len: 0 },
                5,
            )
            .unwrap();
        assert_eq!(lambda.interface, "java/lang/Runnable");
        assert_eq!(
            lambda.sam_descriptor,
            dynamic
                .bootstrap
                .arguments
                .get(0)
                .map(|i| class.method_type(i).unwrap().text)
                .unwrap()
        );
        assert!(lambda.serializable);
        class.pool[flags as usize] = Constant::Integer(8);
        assert!(
            result(&class, "indy").lambdas.is_empty(),
            "unknown flags must stay opaque"
        );
        class.pool[flags as usize] = Constant::Integer(7);
        assert!(
            result(&class, "indy").lambdas.is_empty(),
            "nonempty marker list must stay opaque"
        );
        class.pool[flags as usize] = Constant::Integer(5);
        class.pool[count as usize] = Constant::Integer(-1);
        assert!(result(&class, "indy").lambdas.is_empty());
        class.pool[count as usize] = Constant::Integer(2);
        assert!(
            result(&class, "indy").lambdas.is_empty(),
            "truncated bridge list must stay opaque"
        );
        class.pool[count as usize] = Constant::Integer(1);
        let descriptor = add_utf(&mut class, "(I)V");
        let bridge = class.pool.len() as u16;
        class.pool.push(Constant::MethodType(descriptor));
        let other_bridge: Vec<u8> = [
            method_type,
            implementation,
            method_type,
            flags,
            count,
            bridge,
        ]
        .into_iter()
        .flat_map(u16::to_be_bytes)
        .collect();
        class.bootstrap_methods[0].arguments = BootstrapArguments(&other_bridge);
        assert!(
            result(&class, "indy").lambdas.is_empty(),
            "nonredundant bridge adaptation stays opaque"
        );
        class.bootstrap_methods[0].arguments = BootstrapArguments(&bytes);
        let Constant::MethodHandle { reference, .. } = class.pool[implementation as usize] else {
            panic!()
        };
        class.pool[implementation as usize] = Constant::MethodHandle { kind: 7, reference };
        assert!(
            result(&class, "indy").lambdas.is_empty(),
            "special target semantics are unsupported"
        );
    }
    #[test]
    fn unsupported_dynamic_preserves_later_field_writes_and_exact_wide_stack_effect() {
        let mut class = parse_class(PROBE, Limits::default()).unwrap();
        let dynamic = dynamic_index(&class);
        let row = class.bootstrap_methods[0];
        let Constant::MethodHandle { reference, .. } = class.pool[row.handle as usize] else {
            panic!()
        };
        let Constant::Member { pair, .. } = class.pool[reference as usize] else {
            panic!()
        };
        let (name, _) = match class.pool[pair as usize] {
            Constant::Pair { name, descriptor } => (name, descriptor),
            _ => panic!(),
        };
        let unknown_descriptor = add_utf(&mut class, "()V");
        class.pool[pair as usize] = Constant::Pair {
            name,
            descriptor: unknown_descriptor,
        };
        let Constant::InvokeDynamic { pair, .. } = class.pool[dynamic as usize] else {
            panic!()
        };
        let Constant::Pair { name, .. } = class.pool[pair as usize] else {
            panic!()
        };
        let wide_descriptor = add_utf(&mut class, "(J)J");
        class.pool[pair as usize] = Constant::Pair {
            name,
            descriptor: wide_descriptor,
        };
        let field = class
            .pool
            .iter()
            .enumerate()
            .find(|(i, entry)| {
                matches!(entry, Constant::Member { tag: 9, .. })
                    && class
                        .member(*i as u16, true)
                        .is_ok_and(|m| m.name == "callback")
            })
            .unwrap()
            .0 as u16;
        let [dh, dl] = dynamic.to_be_bytes();
        let [fh, fl] = field.to_be_bytes();
        let code = [30, 186, dh, dl, 0, 0, 63, 44, 45, 181, fh, fl, 177];
        let method = MethodInfo {
            flags: 8,
            name: "normalized_unsupported_then_store",
            descriptor: "(JLfixture/Probe;Ljava/lang/Runnable;)V",
            max_stack: 2,
            max_locals: 4,
            code: Some(&code),
            exception_handlers: 0,
            exception_table: &[],
        };
        let summary = summarize(&class, &method, Limits::default());
        assert_eq!(
            summary.unknown.unwrap().kind,
            ErrorKind::UnsupportedBootstrap
        );
        assert_eq!(summary.unknown_offsets, [1]);
        assert_eq!(summary.field_writes.len(), 1);
        assert!(summary.lambdas.is_empty());
        assert!(summary.calls.is_empty());
        let write = summary.field_writes[0];
        assert_eq!(
            summary.values[write.receiver.unwrap().0 as usize],
            Value::Argument(1)
        );
        assert_eq!(summary.values[write.value.0 as usize], Value::Argument(2));
        assert!(summary.values.contains(&Value::UnknownDynamic));
        assert!(summary.returned.is_some());
    }
    fn pool_offsets(bytes: &[u8]) -> (Vec<usize>, usize) {
        let mut r = Reader::new(bytes);
        r.take(8).unwrap();
        let count = r.u2().unwrap() as usize;
        let mut rows = vec![0; count];
        let mut index = 1;
        while index < count {
            rows[index] = r.at;
            let tag = r.u1().unwrap();
            match tag {
                1 => {
                    let n = r.u2().unwrap() as usize;
                    r.take(n).unwrap();
                }
                3 | 4 | 9..=12 | 17 | 18 => {
                    r.take(4).unwrap();
                }
                5 | 6 => {
                    r.take(8).unwrap();
                    index += 1;
                }
                7 | 8 | 16 | 19 | 20 => {
                    r.take(2).unwrap();
                }
                15 => {
                    r.take(3).unwrap();
                }
                _ => panic!("fixture tag {tag}"),
            }
            index += 1;
        }
        (rows, r.at)
    }
    fn bootstrap_location(bytes: &[u8]) -> (usize, usize, usize) {
        let class = parse_class(bytes, Limits::default()).unwrap();
        let (_, end) = pool_offsets(bytes);
        let mut r = Reader::new(bytes);
        r.at = end;
        r.take(6).unwrap();
        let interfaces = r.u2().unwrap();
        r.take(interfaces as usize * 2).unwrap();
        for _ in 0..2 {
            for _ in 0..r.u2().unwrap() {
                r.take(6).unwrap();
                skip_attributes(&mut r, &class.pool).unwrap();
            }
        }
        let count_at = r.at;
        let count = r.u2().unwrap();
        for _ in 0..count {
            let header = r.at;
            let name = r.u2().unwrap();
            let length = r.u4().unwrap() as usize;
            let start = r.at;
            r.take(length).unwrap();
            if class.utf(name).unwrap() == "BootstrapMethods" {
                return (count_at, header, r.at.max(start));
            }
        }
        panic!("missing fixture bootstrap")
    }
    #[test]
    fn malformed_bootstrap_handles_types_indexes_counts_and_duplicates_reject_before_summary() {
        let class = parse_class(PROBE, Limits::default()).unwrap();
        let (offsets, _) = pool_offsets(PROBE);
        let handle = class.bootstrap_methods[0].handle;
        let method_type = class.bootstrap_methods[0].arguments.get(0).unwrap();
        let dynamic = dynamic_index(&class);
        let ordinary_name = class
            .pool
            .iter()
            .position(|entry| matches!(entry, Constant::Utf8(bytes) if *bytes == b"fixture/Probe"))
            .unwrap() as u16;
        let mut cases = Vec::new();
        for kind in [0, 10] {
            let mut bytes = PROBE.to_vec();
            bytes[offsets[handle as usize] + 1] = kind;
            cases.push(bytes);
        }
        let mut bytes = PROBE.to_vec();
        bytes[offsets[handle as usize] + 2..offsets[handle as usize] + 4]
            .copy_from_slice(&0u16.to_be_bytes());
        cases.push(bytes);
        let mut bytes = PROBE.to_vec();
        bytes[offsets[handle as usize] + 1] = 9;
        cases.push(bytes); // Interface kind cannot target Methodref.
        let mut bytes = PROBE.to_vec();
        bytes[offsets[method_type as usize] + 1..offsets[method_type as usize] + 3]
            .copy_from_slice(&ordinary_name.to_be_bytes());
        cases.push(bytes);
        let mut bytes = PROBE.to_vec();
        bytes[offsets[dynamic as usize] + 1..offsets[dynamic as usize] + 3]
            .copy_from_slice(&u16::MAX.to_be_bytes());
        cases.push(bytes);
        let (count_at, bootstrap, end) = bootstrap_location(PROBE);
        let payload = bootstrap + 6;
        let mut bytes = PROBE.to_vec();
        bytes[payload..payload + 2].copy_from_slice(&u16::MAX.to_be_bytes());
        cases.push(bytes);
        let mut bytes = PROBE.to_vec();
        bytes[payload + 2..payload + 4].copy_from_slice(&0u16.to_be_bytes());
        cases.push(bytes); // Bootstrap method is not a handle.
        let mut bytes = PROBE.to_vec();
        bytes[payload + 6..payload + 8].copy_from_slice(&0u16.to_be_bytes());
        cases.push(bytes); // Nonloadable argument.
        let mut bytes = PROBE.to_vec();
        bytes[payload + 4..payload + 6].copy_from_slice(&u16::MAX.to_be_bytes());
        cases.push(bytes);
        let mut bytes = PROBE.to_vec();
        let count = u16::from_be_bytes(bytes[count_at..count_at + 2].try_into().unwrap());
        bytes[count_at..count_at + 2].copy_from_slice(&(count + 1).to_be_bytes());
        bytes.extend_from_slice(&PROBE[bootstrap..end]);
        cases.push(bytes);
        let mut bytes = PROBE.to_vec();
        bytes[bootstrap..bootstrap + 2].copy_from_slice(&ordinary_name.to_be_bytes());
        cases.push(bytes); // Missing required attribute.
        for (index, bytes) in cases.into_iter().enumerate() {
            assert!(
                parse_class(&bytes, Limits::default()).is_err(),
                "malformed control {index}"
            );
        }
        for end in payload..end {
            assert!(parse_class(&PROBE[..end], Limits::default()).is_err());
        }
    }
    #[test]
    fn covariant_bridge_is_not_replaced_by_parent_implementation() {
        let class = parse_class(CHILD, Limits::default()).unwrap();
        let method = class.method("make", Some("()Lfixture/Made;")).unwrap();
        assert_ne!(method.flags & 0x40, 0);
        let s = summarize(&class, method, Limits::default());
        assert!(s.complete());
        assert_eq!(
            s.values[s.returned.unwrap().0 as usize],
            Value::CallResult(0)
        );
        assert_eq!(s.calls[0].member.owner, "fixture/Child");
        assert_eq!(s.calls[0].member.descriptor, "()Lfixture/Refined;");
    }
    #[test]
    fn malformed_truncated_and_resource_limited_inputs_are_rejected() {
        for end in 0..PROBE.len() {
            assert!(
                parse_class(&PROBE[..end], Limits::default()).is_err(),
                "prefix {end}"
            );
        }
        assert_eq!(
            parse_class(
                PROBE,
                Limits {
                    max_class_bytes: 8,
                    ..Limits::default()
                }
            )
            .unwrap_err()
            .kind,
            ErrorKind::ResourceLimit
        );
        let class = parse_class(PROBE, Limits::default()).unwrap();
        let s = summarize(
            &class,
            class.method("make", None).unwrap(),
            Limits {
                max_values: 1,
                ..Limits::default()
            },
        );
        assert_eq!(s.unknown.unwrap().kind, ErrorKind::ResourceLimit);
        let mut class = parse_class(PROBE, Limits::default()).unwrap();
        class.pool[1] = Constant::Dynamic {
            bootstrap: 0,
            pair: 0,
        };
        let method = MethodInfo {
            flags: 8,
            name: "synthetic_condy_control",
            descriptor: "()Ljava/lang/Object;",
            max_stack: 1,
            max_locals: 0,
            code: Some(&[18, 1, 176]),
            exception_handlers: 0,
            exception_table: &[],
        };
        assert_eq!(
            summarize(&class, &method, Limits::default())
                .unknown
                .unwrap()
                .kind,
            ErrorKind::DynamicConstant
        );
    }
    #[test]
    fn ordered_captured_jar_hashes_and_compression_select_exact_class() {
        for name in ["fixture-stored.jar", "fixture-deflated.jar"] {
            let mut cp = CapturedClasspath::new(vec![jar(name)], Limits::default()).unwrap();
            let found = cp.resolve("fixture/Probe").unwrap();
            assert_eq!(found.bytes, PROBE);
            assert_eq!(found.proof.examined.len(), 1);
            assert!(!found.proof.examined[0].absent);
        }
        let mut cp = CapturedClasspath::new(
            vec![jar("fixture-alternate.jar"), jar("fixture-stored.jar")],
            Limits::default(),
        )
        .unwrap();
        let found = cp.resolve("fixture/Probe").unwrap();
        let class = parse_class(&found.bytes, Limits::default()).unwrap();
        assert_eq!(*returned(&result(&class, "make")), Value::Null);
        let mut cp = CapturedClasspath::new(
            vec![jar("fixture-stored.jar"), jar("fixture-alternate.jar")],
            Limits::default(),
        )
        .unwrap();
        let found = cp.resolve("fixture/Probe").unwrap();
        assert_eq!(found.bytes, PROBE);
        let ClassLookup::Absent(proof) = cp.lookup("fixture/NotPresent").unwrap() else {
            panic!("unexpected class")
        };
        assert_eq!(proof.examined.len(), 2);
        assert!(proof.examined.iter().all(|e| e.absent));
    }
    static TEMP: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    struct Temporary(PathBuf);
    impl Temporary {
        fn new() -> Self {
            let n = TEMP.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let p =
                std::env::temp_dir().join(format!("selector-binary-{}-{n}", std::process::id()));
            std::fs::create_dir(&p).unwrap();
            Self(p)
        }
    }
    impl Drop for Temporary {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    #[test]
    fn preceding_hash_failure_cannot_fall_through_and_owned_snapshot_is_stable() {
        let temp = Temporary::new();
        let path = temp.0.join("earlier.jar");
        let bytes = std::fs::read(fixture("fixture-stored.jar")).unwrap();
        std::fs::write(&path, &bytes).unwrap();
        let first = ClasspathEntry {
            path: path.clone(),
            sha256: hash(&bytes),
            kind: EntryKind::Jar,
        };
        let mut cp = CapturedClasspath::new(
            vec![first.clone(), jar("fixture-alternate.jar")],
            Limits::default(),
        )
        .unwrap();
        assert_eq!(cp.resolve("fixture/Probe").unwrap().bytes, PROBE);
        std::fs::write(&path, b"changed after admission").unwrap();
        assert_eq!(cp.resolve("fixture/Probe").unwrap().bytes, PROBE);
        let mut cp =
            CapturedClasspath::new(vec![first, jar("fixture-alternate.jar")], Limits::default())
                .unwrap();
        assert_eq!(
            cp.resolve("fixture/Probe").unwrap_err().kind,
            ErrorKind::HashMismatch
        );
        assert_eq!(
            cp.resolve("fixture/Probe").unwrap_err().kind,
            ErrorKind::HashMismatch
        );
    }
    #[test]
    fn shared_input_owners_keep_mutation_order_digest_and_runtime_boundaries() {
        let temp = Temporary::new();
        let path = temp.0.join("captured.jar");
        let bytes = std::fs::read(fixture("fixture-stored.jar")).unwrap();
        std::fs::write(&path, &bytes).unwrap();
        let entry = ClasspathEntry {
            path: path.clone(),
            sha256: hash(&bytes),
            kind: EntryKind::Jar,
        };
        let original = AdmittedEntry::admit(entry.clone(), Limits::default(), Some(21)).unwrap();
        let alternate_entry = jar("fixture-alternate.jar");
        let alternate =
            AdmittedEntry::admit(alternate_entry.clone(), Limits::default(), Some(21)).unwrap();
        let mut first = CapturedClasspath::from_admitted(
            vec![entry.clone(), alternate_entry.clone()],
            &[&original, &alternate],
            Limits::default(),
            Some(21),
        )
        .unwrap();
        let mut reversed = CapturedClasspath::from_admitted(
            vec![alternate_entry, entry.clone()],
            &[&alternate, &original],
            Limits::default(),
            Some(21),
        )
        .unwrap();
        assert_eq!(first.retained_bytes(), 0);
        assert!(original.retained_bytes() >= bytes.len());
        std::fs::write(&path, b"changed external bytes").unwrap();
        assert_eq!(first.resolve("fixture/Probe").unwrap().bytes, PROBE);
        let other = reversed.resolve("fixture/Probe").unwrap();
        let class = parse_class(&other.bytes, Limits::default()).unwrap();
        assert_eq!(*returned(&result(&class, "make")), Value::Null);
        assert_eq!(
            CapturedClasspath::from_admitted(
                vec![entry.clone()],
                &[&original],
                Limits::default(),
                Some(17)
            )
            .err()
            .unwrap()
            .kind,
            ErrorKind::HashMismatch
        );
        let mut wrong = entry.clone();
        wrong.sha256 = ContentHash([7; 32]);
        assert_eq!(
            CapturedClasspath::from_admitted(
                vec![wrong],
                &[&original],
                Limits::default(),
                Some(21)
            )
            .err()
            .unwrap()
            .kind,
            ErrorKind::HashMismatch
        );
        let unavailable_entry = ClasspathEntry {
            path: temp.0.join("opaque"),
            sha256: ContentHash::default(),
            kind: EntryKind::Unavailable,
        };
        let unavailable =
            AdmittedEntry::admit(unavailable_entry.clone(), Limits::default(), Some(21)).unwrap();
        let mut blocked = CapturedClasspath::from_admitted(
            vec![unavailable_entry, entry],
            &[&unavailable, &original],
            Limits::default(),
            Some(21),
        )
        .unwrap();
        assert_eq!(
            blocked.resolve("fixture/Probe").unwrap_err().kind,
            ErrorKind::UnavailableInput
        );
    }
    #[test]
    fn directory_absence_is_full_fingerprint_bound_and_pruning_is_unknown() {
        let temp = Temporary::new();
        let path = temp.0.join("keep.txt");
        std::fs::write(&path, b"abc").unwrap();
        let canonical = format!(
            "[{{\"bytes\":3,\"path\":\"keep.txt\",\"sha256\":\"{}\"}}]",
            hash(b"abc")
        );
        let entry = ClasspathEntry {
            path: temp.0.clone(),
            sha256: hash(canonical.as_bytes()),
            kind: EntryKind::Directory { files: 1, bytes: 3 },
        };
        let mut cp = CapturedClasspath::new(
            vec![entry.clone(), jar("fixture-stored.jar")],
            Limits::default(),
        )
        .unwrap();
        let found = cp.resolve("fixture/Probe").unwrap();
        assert_eq!(found.proof.examined.len(), 2);
        assert!(found.proof.examined[0].absent);
        std::fs::remove_file(path).unwrap();
        let mut cp =
            CapturedClasspath::new(vec![entry, jar("fixture-stored.jar")], Limits::default())
                .unwrap();
        assert_eq!(
            cp.resolve("fixture/Probe").unwrap_err().kind,
            ErrorKind::DirectoryFingerprintMismatch
        );
    }
    #[test]
    fn verified_directory_class_wins_in_order_and_selected_bytes_cannot_change() {
        let temp = Temporary::new();
        std::fs::create_dir(temp.0.join("fixture")).unwrap();
        let path = temp.0.join("fixture/Probe.class");
        std::fs::write(&path, PROBE).unwrap();
        let canonical = format!(
            "[{{\"bytes\":{},\"path\":\"fixture/Probe.class\",\"sha256\":\"{}\"}}]",
            PROBE.len(),
            hash(PROBE)
        );
        let entry = ClasspathEntry {
            path: temp.0.clone(),
            sha256: hash(canonical.as_bytes()),
            kind: EntryKind::Directory {
                files: 1,
                bytes: PROBE.len() as u64,
            },
        };
        let mut cp =
            CapturedClasspath::new(vec![entry, jar("fixture-alternate.jar")], Limits::default())
                .unwrap();
        let found = cp.resolve("fixture/Probe").unwrap();
        assert_eq!(found.bytes, PROBE);
        assert_eq!(found.proof.selected_entry, Some(0));
        assert_eq!(found.proof.class_hash, Some(hash(PROBE)));
        assert_eq!(found.proof.examined.len(), 1);
        std::fs::write(&path, b"post-admission mutation").unwrap();
        assert_eq!(found.bytes, PROBE);
        assert_eq!(
            cp.resolve("fixture/Probe").unwrap_err().kind,
            ErrorKind::HashMismatch
        );
    }
    #[test]
    fn multi_release_authority_comes_only_from_a_valid_main_manifest_attribute() {
        assert!(manifest_multi_release(b"Manifest-Version: 1.0\r\nmUlTi-ReLeAsE: tr\r\n ue\r\n\r\nName: entry\r\nMulti-Release: false\r\n").unwrap());
        assert!(
            !manifest_multi_release(b"Manifest-Version: 1.0\n\nName: entry\nMulti-Release: true\n")
                .unwrap()
        );
        assert!(!manifest_multi_release(b"Multi-Release: false\n\n").unwrap());
        assert!(!manifest_multi_release(b"").unwrap());
        assert_eq!(
            manifest_multi_release(b"Multi-Release: true\nMulti-Release: false\n\n")
                .unwrap_err()
                .kind,
            ErrorKind::InvalidZip
        );
        assert_eq!(
            manifest_multi_release(b" continuation without header\n")
                .unwrap_err()
                .kind,
            ErrorKind::InvalidZip
        );
    }
    #[test]
    fn manifest_classpath_inventory_is_main_section_folded_bounded_and_not_lookup() {
        assert_eq!(manifest_class_path(b"Manifest-Version: 1.0\r\ncLaSs-PaTh: first.j\r\n ar second.jar\r\n\r\nName: later\r\nClass-Path: ignored.jar\r\n").unwrap(), ["first.jar", "second.jar"]);
        assert!(
            manifest_class_path(b"Manifest-Version: 1.0\n\nName: later\nClass-Path: ignored.jar\n")
                .unwrap()
                .is_empty()
        );
        assert!(manifest_class_path(b"Class-Path: a.jar\nClass-Path: b.jar\n\n").is_err());
        assert!(manifest_class_path(b" orphan continuation\n").is_err());
        assert!(manifest_class_path(b"Class-Path no-colon\n").is_err());
        assert!(manifest_class_path(&vec![b'x'; 1024 * 1024 + 1]).is_err());
        let many = format!("Class-Path: {}\n\n", "a.jar ".repeat(4097));
        assert_eq!(
            manifest_class_path(many.as_bytes()).unwrap_err().kind,
            ErrorKind::ResourceLimit
        );
    }
    #[test]
    fn genuine_multi_release_classes_match_independent_jvm_version_controls() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/multi-release");
        let manifest: serde_json::Value =
            serde_json::from_slice(&std::fs::read(root.join("manifest.json")).unwrap()).unwrap();
        for jar in [
            "multi-release.jar",
            "false.jar",
            "missing-attribute.jar",
            "no-manifest.jar",
            "plain.jar",
        ] {
            let receipt = manifest["jars"]
                .as_array()
                .unwrap()
                .iter()
                .find(|j| j["path"] == jar)
                .unwrap();
            let entry = ClasspathEntry {
                path: root.join(jar),
                kind: EntryKind::Jar,
                sha256: ContentHash::from_hex(receipt["sha256"].as_str().unwrap()).unwrap(),
            };
            for feature in [8, 9, 17, 20, 21] {
                let expected = if jar == "multi-release.jar" {
                    if feature >= 21 {
                        21
                    } else if feature >= 17 {
                        17
                    } else {
                        8
                    }
                } else {
                    8
                };
                let mut cp = CapturedClasspath::new(vec![entry.clone()], Limits::default())
                    .unwrap()
                    .with_java_feature(Some(feature))
                    .unwrap();
                assert_eq!(cp.class_names(0).unwrap(), ["mr/Main", "mr/Probe"]);
                let class = cp.resolve("mr/Probe").unwrap();
                let bytes =
                    std::fs::read(root.join(format!("classes/{expected}/mr/Probe.class"))).unwrap();
                assert_eq!(class.bytes, bytes, "{jar} feature{feature}");
                assert_eq!(class.proof.class_hash, Some(hash(&bytes)));
                if [8, 17, 21].contains(&feature) {
                    let control = manifest["controls"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .find(|control| {
                            control["jar"] == jar && control["requested_version"] == feature
                        })
                        .unwrap();
                    assert_eq!(control["execution"]["exit_code"], 0);
                    assert_eq!(control["execution"]["stdout"], format!("{expected}\n"));
                    let selected = if expected == 8 {
                        "mr/Probe.class".to_owned()
                    } else {
                        format!("META-INF/versions/{expected}/mr/Probe.class")
                    };
                    assert!(
                        control["selection"]["stdout"]
                            .as_str()
                            .unwrap()
                            .starts_with(&format!("{selected}\n"))
                    );
                }
            }
            let mut cp = CapturedClasspath::new(vec![entry], Limits::default()).unwrap();
            if jar == "multi-release.jar" {
                assert_eq!(
                    cp.resolve("mr/Probe").unwrap_err().kind,
                    ErrorKind::MultiReleaseArchive
                );
            } else {
                assert_eq!(
                    cp.resolve("mr/Probe").unwrap().bytes,
                    std::fs::read(root.join("classes/8/mr/Probe.class")).unwrap()
                );
            }
        }
    }
    #[test]
    fn zip_crc_and_class_identity_are_validated_before_analysis() {
        let mut bytes = std::fs::read(fixture("fixture-stored.jar")).unwrap();
        let members = zip_members(&bytes).unwrap();
        let selected = members
            .iter()
            .position(|m| &bytes[m.name.clone()] == b"fixture/Probe.class")
            .unwrap();
        let m = &members[selected];
        let start = m.local
            + 30
            + le16(&bytes, m.local + 26).unwrap() as usize
            + le16(&bytes, m.local + 28).unwrap() as usize;
        bytes[start] ^= 1;
        let jar = Jar { bytes, members };
        assert_eq!(
            zip_read(&jar, &jar.members[selected], Limits::default())
                .unwrap_err()
                .kind,
            ErrorKind::BadCrc
        );
        assert_eq!(crc32(b"123456789"), 0xcbf43926);
    }
}
