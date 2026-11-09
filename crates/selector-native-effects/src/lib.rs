//! Native structural lower bounds. This prototype grants no closed-effect authority.
use selector_effects as effects;
use selector_models::binary::{self, BinaryValueId, MemberRef, MethodInfo, Value};
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::mem::size_of;
use std::sync::Arc;

mod adapters;
pub use adapters::{CallableAdapterRef, SamRef};
mod axiom;
pub use axiom::{AxiomReceipt, RuntimeAxiom};
pub mod classpath_absence;
pub mod framework_transport;
pub mod library_inventory;
mod members;
pub mod provider;
pub mod stable_compilation;
pub use members::{DeclaringField, FieldAuthority, resolve_declaring_fields};
mod reachable;
pub use reachable::{ReachabilityLimits, RootMethodDemand, produce_reachable};

pub const NONE: u32 = u32::MAX;

#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub classes: usize,
    pub class_bytes: usize,
    pub references: usize,
    pub rows: usize,
    pub retained_bytes: usize,
    pub binary: binary::Limits,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            classes: 8192,
            class_bytes: 64 << 20,
            references: 200_000,
            rows: 2_000_000,
            retained_bytes: 256 << 20,
            binary: binary::Limits::default(),
        }
    }
}
#[derive(Debug)]
pub enum Error {
    Budget,
    Binding,
    ClassHash,
    ClassOwner,
    ConflictingProvider,
    TextRange,
    Binary(binary::BinaryError),
    Capsule(effects::Error),
    Provider(Box<provider::Error>),
}
impl From<binary::BinaryError> for Error {
    fn from(value: binary::BinaryError) -> Self {
        Self::Binary(value)
    }
}
impl From<effects::Error> for Error {
    fn from(value: effects::Error) -> Self {
        Self::Capsule(value)
    }
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "native capsule {self:?}")
    }
}
impl std::error::Error for Error {}

/// Imported artifact-local authority, not an ambient compiler ContextId.
#[derive(Clone, Copy)]
pub struct ClassDemand<'a> {
    pub authority: u32,
    pub owner: &'a str,
}
/// The caller must admit provider order/context separately. A hash is not that proof.
pub struct ProvidedClass {
    pub bytes: Arc<[u8]>,
    pub class_sha256: [u8; 32],
    pub authority: u32,
    pub provider: u32,
    pub binding_sha256: [u8; 32],
}
pub trait ClassProvider {
    fn class(&mut self, demand: ClassDemand<'_>) -> Result<Option<ProvidedClass>, Error>;
    /// Optional exact JVM member resolution. None retains the original symbolic
    /// endpoint as TOP; it never authorizes a guessed ancestor implementation.
    fn declaration(
        &mut self,
        _authority: u32,
        _member: MemberRef<'_>,
        _kind: binary::InvokeKind,
        _caller: Option<&str>,
    ) -> Result<Option<Arc<str>>, Error> {
        Ok(None)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TextSource {
    Input,
    Blob,
    Builtin,
    Owned,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TextRef {
    pub source: TextSource,
    pub index: u32,
    pub start: u32,
    pub len: u32,
}
impl TextRef {
    fn builtin(index: u32) -> Self {
        Self {
            source: TextSource::Builtin,
            index,
            start: 0,
            len: 0,
        }
    }
}
const BUILTINS: [&str; 6] = [
    "<class-initialization>",
    "()V",
    "<unavailable-class>",
    "<vm-loading-verification-boundary>",
    "<shared-throwable-fields-and-stack-metadata>",
    "Ljava/lang/Throwable;",
];
pub struct Blob {
    pub metadata: Arc<binary::ClassMetadata>,
    pub bytes: Arc<[u8]>,
    pub class_sha256: [u8; 32],
    pub authority: u32,
    pub provider: u32,
    pub binding_sha256: [u8; 32],
}
#[derive(Clone, Copy, Debug)]
pub struct ClassRef {
    pub authority: u32,
    pub owner: TextRef,
    pub blob: u32,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ForeignKind {
    Method,
    ClassInitialization,
    UnavailableClass,
    RuntimeBoundary,
}
#[derive(Clone, Copy, Debug)]
pub struct ForeignMethod {
    pub method: effects::MethodId,
    pub class: u32,
    pub kind: ForeignKind,
    pub name: TextRef,
    pub descriptor: TextRef,
}
#[derive(Clone, Copy, Debug)]
pub struct PhaseRef {
    pub method: effects::MethodId,
    pub class: u32,
    pub kind: ForeignKind,
    pub dependencies: effects::Range,
}
#[derive(Clone, Copy, Debug)]
pub struct FieldRef {
    pub class: u32,
    pub name: TextRef,
    pub descriptor: TextRef,
    /// A semantic runtime region is never an invented concrete Java field.
    pub runtime_throwable_region: bool,
}
#[derive(Clone, Copy, Debug)]
pub struct Site {
    pub method: effects::MethodId,
    pub pc: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PrimitiveType {
    Boolean,
    Byte,
    ByteOrBoolean,
    Char,
    Short,
    Int,
    Long,
    Float,
    Double,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PrimitiveKind {
    Read(PrimitiveType),
    Length,
    Allocate(PrimitiveType),
    IntegerDivisionOrRemainder,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VmException {
    NullPointer,
    ArrayIndexOutOfBounds,
    NegativeArraySize,
    OutOfMemory,
    Arithmetic,
}
#[derive(Clone, Copy, Debug)]
pub struct PrimitiveOperation {
    pub site: u32,
    pub kind: PrimitiveKind,
    pub base: effects::Origin,
    /// Explicit conditional JVMS exceptions. Their objects may be shared.
    pub exceptions: u32,
    pub scalar_top: bool,
    pub shared_throwable_metadata: bool,
    /// No verified stack/type/VM contract has been admitted by this prototype.
    pub requires_verification_and_vm_contract: bool,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OpenReason {
    MissingVerification,
    MissingClass,
    MissingCode,
    NativeMethod,
    SynchronizedMethod,
    LocalSummaryPartial,
    ReferenceArrayLoad,
    ArrayWrite,
    ReferenceArrayAllocation,
    DynamicBootstrap,
    Monitor,
    ExplicitThrow,
    LambdaCapture,
    UnsupportedInstruction,
    IncompleteEffectInventory,
    AdmissionBudget,
}
#[derive(Clone, Copy, Debug)]
pub struct OpenSite {
    pub method: effects::MethodId,
    pub pc: u32,
    pub reason: OpenReason,
}
#[derive(Default)]
struct Postings {
    classes: HashMap<[u8; 32], u32>,
    methods: HashMap<[u8; 32], u32>,
    fields: HashMap<[u8; 32], u32>,
    sams: HashMap<[u8; 32], u32>,
    sam_next: Vec<u32>,
    class_next: Vec<u32>,
    method_next: Vec<u32>,
    field_next: Vec<u32>,
}

pub struct Produced<'a> {
    pub data: effects::CapsuleData,
    pub blobs: Vec<Blob>,
    pub inputs: Vec<&'a str>,
    pub owned_text: Vec<Arc<str>>,
    pub classes: Vec<ClassRef>,
    pub methods: Vec<ForeignMethod>,
    pub sams: Vec<SamRef>,
    pub adapters: Vec<CallableAdapterRef>,
    pub phases: Vec<PhaseRef>,
    pub fields: Vec<FieldRef>,
    pub sites: Vec<Site>,
    pub primitives: Vec<PrimitiveOperation>,
    pub open: Vec<OpenSite>,
    pub roots: Vec<effects::MethodId>,
    pub axiom: Option<AxiomReceipt>,
    pub projected: Vec<bool>,
}
impl<'a> Produced<'a> {
    pub fn text(&self, text: TextRef) -> &str {
        match text.source {
            TextSource::Input => self.inputs[text.index as usize],
            TextSource::Blob => std::str::from_utf8(
                &self.blobs[text.index as usize].bytes
                    [text.start as usize..(text.start + text.len) as usize],
            )
            .expect("parser-checked UTF8 range"),
            TextSource::Builtin => BUILTINS[text.index as usize],
            TextSource::Owned => self.owned_text[text.index as usize].as_ref(),
        }
    }
    pub fn foreign(&self, method: effects::MethodId) -> Option<&ForeignMethod> {
        let row = self.data.methods.get(method.0 as usize)?;
        (row.subject.kind == effects::SubjectKind::ForeignMethod)
            .then(|| self.methods.get(row.subject.index as usize))
            .flatten()
    }
    pub fn phase(&self, method: effects::MethodId) -> Option<&PhaseRef> {
        let row = self.data.methods.get(method.0 as usize)?;
        (row.subject.kind == effects::SubjectKind::RuntimePhase)
            .then(|| self.phases.get(row.subject.index as usize))
            .flatten()
    }
    pub fn bounds(&self) -> effects::RefBounds {
        effects::RefBounds {
            fact_nodes: 0,
            sams: self.sams.len() as u32,
            adapters: self.adapters.len() as u32,
            phases: self.phases.len() as u32,
            bridge_proofs: 0,
            foreign_methods: self.methods.len() as u32,
            authorities: self
                .classes
                .iter()
                .map(|class| class.authority)
                .max()
                .map_or(0, |id| id + 1),
            members: self.fields.len() as u32,
            classes: self.classes.len() as u32,
            exceptions: 5,
            externals: 0,
            sites: self.sites.len() as u32,
        }
    }
}

struct Builder<'a, 'p> {
    out: Produced<'a>,
    postings: Postings,
    limits: Limits,
    class_bytes: usize,
    metadata_bytes: usize,
    owned_text_bytes: usize,
    queue_bytes: usize,
    validator: binary::diagnostic::CodeValidator,
    axiom: Option<&'p RuntimeAxiom>,
    throwable_region: Option<u32>,
    functions: Vec<ForeignMethod>,
    adapter_arguments: Vec<effects::ValueRef>,
    adapter_drafts: Vec<adapters::Draft>,
    adapter_cursor: usize,
}
fn digest(parts: &[&[u8]]) -> [u8; 32] {
    let mut hash = Sha256::new();
    for part in parts {
        hash.update((part.len() as u64).to_le_bytes());
        hash.update(part);
    }
    hash.finalize().into()
}
fn range(start: usize, end: usize) -> effects::Range {
    effects::Range {
        start: start as u32,
        len: (end - start) as u32,
    }
}
impl<'a, 'p> Builder<'a, 'p> {
    fn new(limits: Limits, axiom: Option<&'p RuntimeAxiom>) -> Self {
        Self {
            out: Produced {
                data: Default::default(),
                blobs: Vec::new(),
                inputs: Vec::new(),
                owned_text: Vec::new(),
                classes: Vec::new(),
                methods: Vec::new(),
                fields: Vec::new(),
                phases: Vec::new(),
                sams: Vec::new(),
                adapters: Vec::new(),
                sites: Vec::new(),
                primitives: Vec::new(),
                open: Vec::new(),
                roots: Vec::new(),
                axiom: axiom.map(RuntimeAxiom::receipt),
                projected: Vec::new(),
            },
            postings: Postings::default(),
            limits,
            class_bytes: 0,
            metadata_bytes: 0,
            owned_text_bytes: 0,
            queue_bytes: 0,
            validator: Default::default(),
            axiom,
            throwable_region: None,
            functions: Vec::new(),
            adapter_arguments: Vec::new(),
            adapter_drafts: Vec::new(),
            adapter_cursor: 0,
        }
    }
    fn check(&self) -> Result<(), Error> {
        let o = &self.out;
        let d = &o.data;
        let references = o.classes.len()
            + self.functions.len()
            + o.fields.len()
            + o.sams.len()
            + o.adapters.len();
        let rows = d.methods.len()
            + d.calls.len()
            + d.origins.len()
            + d.callable_values.len()
            + d.value_flows.len()
            + d.creations.len()
            + d.sam_arities.len()
            + d.callable_bridges.len()
            + d.code_observations.len()
            + d.reads.len()
            + d.writes.len()
            + d.escapes.len()
            + d.initializes.len()
            + d.throws.len()
            + d.synchronizes.len()
            + d.external.len()
            + d.flows.len()
            + o.sites.len()
            + o.primitives.len()
            + o.open.len();
        // Hash postings own one digest/index allocation per distinct key. Charge
        // a conservative fixed overhead as well as actual flat arena capacities.
        let bytes = d.owned_bytes()?
            + self.class_bytes
            + 160 * references
            + size_of::<ClassRef>() * o.classes.capacity()
            + size_of::<ForeignMethod>() * o.methods.capacity()
            + size_of::<ForeignMethod>() * self.functions.capacity()
            + size_of::<PhaseRef>() * o.phases.capacity()
            + size_of::<SamRef>() * o.sams.capacity()
            + size_of::<CallableAdapterRef>() * o.adapters.capacity()
            + size_of::<effects::ValueRef>() * self.adapter_arguments.capacity()
            + size_of::<adapters::Draft>() * self.adapter_drafts.capacity()
            + size_of::<FieldRef>() * o.fields.capacity()
            + size_of::<Blob>() * o.blobs.capacity()
            + size_of::<Site>() * o.sites.capacity()
            + size_of::<PrimitiveOperation>() * o.primitives.capacity()
            + size_of::<OpenSite>() * o.open.capacity()
            + size_of::<&str>() * o.inputs.capacity()
            + size_of::<effects::MethodId>() * o.roots.capacity()
            + o.projected.capacity()
            + o.owned_text.capacity() * size_of::<Arc<str>>()
            + self.owned_text_bytes
            + self.metadata_bytes
            + self.queue_bytes
            + (self.postings.class_next.capacity()
                + self.postings.method_next.capacity()
                + self.postings.field_next.capacity()
                + self.postings.sam_next.capacity())
                * 4;
        if references > self.limits.references
            || rows > self.limits.rows
            || bytes > self.limits.retained_bytes
            || o.classes.len() > self.limits.classes
            || rows >= NONE as usize
        {
            return Err(Error::Budget);
        }
        Ok(())
    }
    fn input(&mut self, text: &'a str) -> TextRef {
        let index = self.out.inputs.len() as u32;
        self.out.inputs.push(text);
        TextRef {
            source: TextSource::Input,
            index,
            start: 0,
            len: text.len() as u32,
        }
    }
    fn text(&self, text: TextRef) -> &str {
        self.out.text(text)
    }
    fn borrowed(&self, blob: u32, text: &str) -> Result<TextRef, Error> {
        let bytes = &self.out.blobs[blob as usize].bytes;
        let start = (text.as_ptr() as usize)
            .checked_sub(bytes.as_ptr() as usize)
            .ok_or(Error::TextRange)?;
        let end = start.checked_add(text.len()).ok_or(Error::TextRange)?;
        if end > bytes.len() || bytes[start..end] != *text.as_bytes() {
            return Err(Error::TextRange);
        }
        Ok(TextRef {
            source: TextSource::Blob,
            index: blob,
            start: start as u32,
            len: text.len() as u32,
        })
    }
    fn class(&mut self, authority: u32, owner: TextRef) -> Result<u32, Error> {
        let key = digest(&[&authority.to_le_bytes(), self.text(owner).as_bytes()]);
        let mut next = self.postings.classes.get(&key).copied().unwrap_or(NONE);
        while next != NONE {
            let row = self.out.classes[next as usize];
            if row.authority == authority && self.text(row.owner) == self.text(owner) {
                return Ok(next);
            }
            next = self.postings.class_next[next as usize];
        }
        let id = self.out.classes.len() as u32;
        self.out.classes.push(ClassRef {
            authority,
            owner,
            blob: NONE,
        });
        self.postings
            .class_next
            .push(self.postings.classes.insert(key, id).unwrap_or(NONE));
        self.check()?;
        Ok(id)
    }
    fn method(
        &mut self,
        class: u32,
        kind: ForeignKind,
        name: TextRef,
        descriptor: TextRef,
    ) -> Result<effects::MethodId, Error> {
        let key = digest(&[
            &class.to_le_bytes(),
            &[kind as u8],
            self.text(name).as_bytes(),
            self.text(descriptor).as_bytes(),
        ]);
        let mut next = self.postings.methods.get(&key).copied().unwrap_or(NONE);
        while next != NONE {
            let row = self.functions[next as usize];
            if row.class == class
                && row.kind == kind
                && self.text(row.name) == self.text(name)
                && self.text(row.descriptor) == self.text(descriptor)
            {
                return Ok(row.method);
            }
            next = self.postings.method_next[next as usize];
        }
        let arity = binary::method_descriptor(self.text(descriptor))?.parameter_count as u32;
        let id = self.functions.len() as u32;
        let method = effects::MethodId(self.out.data.methods.len() as u32);
        let function = ForeignMethod {
            method,
            class,
            kind,
            name,
            descriptor,
        };
        self.functions.push(function);
        let subject = if kind == ForeignKind::Method {
            let index = self.out.methods.len() as u32;
            self.out.methods.push(function);
            effects::SubjectRef {
                kind: effects::SubjectKind::ForeignMethod,
                index,
            }
        } else {
            let index = self.out.phases.len() as u32;
            self.out.phases.push(PhaseRef {
                method,
                class,
                kind,
                dependencies: effects::Range::EMPTY,
            });
            effects::SubjectRef {
                kind: effects::SubjectKind::RuntimePhase,
                index,
            }
        };
        self.out.projected.push(false);
        self.out.data.methods.push(effects::MethodRow::unknown(
            subject,
            self.out.classes[class as usize].authority,
            arity,
            0,
            0,
        ));
        self.postings
            .method_next
            .push(self.postings.methods.insert(key, id).unwrap_or(NONE));
        self.check()?;
        Ok(method)
    }
    fn function(&self, method: effects::MethodId) -> Option<ForeignMethod> {
        let row = self.out.data.methods.get(method.0 as usize)?;
        match row.subject.kind {
            effects::SubjectKind::ForeignMethod => {
                self.out.methods.get(row.subject.index as usize).copied()
            }
            effects::SubjectKind::RuntimePhase => self
                .out
                .phases
                .get(row.subject.index as usize)
                .map(|phase| ForeignMethod {
                    method,
                    class: phase.class,
                    kind: phase.kind,
                    name: TextRef::builtin(match phase.kind {
                        ForeignKind::ClassInitialization => 0,
                        ForeignKind::RuntimeBoundary => 3,
                        _ => 2,
                    }),
                    descriptor: TextRef::builtin(1),
                }),
            _ => None,
        }
    }
    fn member_method(
        &mut self,
        blob: u32,
        authority: u32,
        member: MemberRef<'_>,
    ) -> Result<effects::MethodId, Error> {
        let owner = self.borrowed(blob, member.owner)?;
        let name = self.borrowed(blob, member.name)?;
        let descriptor = self.borrowed(blob, member.descriptor)?;
        let class = self.class(authority, owner)?;
        self.method(class, ForeignKind::Method, name, descriptor)
    }
    fn field(&mut self, blob: u32, authority: u32, member: MemberRef<'_>) -> Result<u32, Error> {
        let owner = self.borrowed(blob, member.owner)?;
        let name = self.borrowed(blob, member.name)?;
        let descriptor = self.borrowed(blob, member.descriptor)?;
        let class = self.class(authority, owner)?;
        let key = digest(&[
            &class.to_le_bytes(),
            self.text(name).as_bytes(),
            self.text(descriptor).as_bytes(),
        ]);
        let mut next = self.postings.fields.get(&key).copied().unwrap_or(NONE);
        while next != NONE {
            let row = self.out.fields[next as usize];
            if row.class == class
                && self.text(row.name) == self.text(name)
                && self.text(row.descriptor) == self.text(descriptor)
            {
                return Ok(next);
            }
            next = self.postings.field_next[next as usize];
        }
        let id = self.out.fields.len() as u32;
        self.out.fields.push(FieldRef {
            class,
            name,
            descriptor,
            runtime_throwable_region: false,
        });
        self.postings
            .field_next
            .push(self.postings.fields.insert(key, id).unwrap_or(NONE));
        self.check()?;
        Ok(id)
    }
    fn initialize(&mut self, blob: u32, authority: u32, owner: &str) -> Result<(), Error> {
        let text = self.borrowed(blob, owner)?;
        let class = self.class(authority, text)?;
        let target = self.method(
            class,
            ForeignKind::ClassInitialization,
            TextRef::builtin(0),
            TextRef::builtin(1),
        )?;
        self.out.data.initializes.push(target);
        Ok(())
    }
    fn shared_throwable_region(&mut self) -> Result<u32, Error> {
        if let Some(id) = self.throwable_region {
            return Ok(id);
        }
        let id = self.out.fields.len() as u32;
        self.out.fields.push(FieldRef {
            class: NONE,
            name: TextRef::builtin(4),
            descriptor: TextRef::builtin(5),
            runtime_throwable_region: true,
        });
        self.postings.field_next.push(NONE);
        self.throwable_region = Some(id);
        self.check()?;
        Ok(id)
    }
    fn site(&mut self, method: effects::MethodId, pc: u32) -> u32 {
        let id = self.out.sites.len() as u32;
        self.out.sites.push(Site { method, pc });
        id
    }
    fn origin(values: &[effects::Origin], value: BinaryValueId) -> effects::Origin {
        values
            .get(value.0 as usize)
            .copied()
            .unwrap_or(effects::Origin::ANY)
    }
    fn callable(summary: &binary::MethodSummary<'_>, id: BinaryValueId) -> effects::ValueRef {
        match summary.values.get(id.0 as usize) {
            Some(Value::Receiver) => effects::ValueRef::RECEIVER,
            Some(Value::Argument(index)) => effects::ValueRef::argument(u32::from(*index)),
            Some(Value::Null) => effects::ValueRef::CONSTANT,
            Some(_) => effects::ValueRef::local(id.0),
            None => effects::ValueRef::UNKNOWN,
        }
    }
    fn emit_method(
        &mut self,
        blob: u32,
        class_id: u32,
        class: &binary::ClassFile<'_>,
        method: &MethodInfo<'_>,
        target: effects::MethodId,
    ) -> Result<(), Error> {
        self.out.open.push(OpenSite {
            method: target,
            pc: 0,
            reason: OpenReason::MissingVerification,
        });
        if method.code.is_none() {
            self.out.open.push(OpenSite {
                method: target,
                pc: 0,
                reason: if method.flags & 0x100 != 0 {
                    OpenReason::NativeMethod
                } else {
                    OpenReason::MissingCode
                },
            });
            return self.check();
        }
        self.validator.validate(class, method, self.limits.binary)?;
        let summary = binary::summarize_with_envelope(class, method, self.limits.binary);
        let authority = self.out.classes[class_id as usize].authority;
        let mut row = self.out.data.methods[target.0 as usize];
        row.locals = summary.values.len() as u32;
        let start = Starts::new(&self.out.data);
        let mut values = Vec::with_capacity(summary.values.len());
        let mut allocations = HashMap::<u32, u32>::new();
        for value in &summary.values {
            let origin = match *value {
                Value::Receiver => effects::Origin::RECEIVER,
                Value::Argument(i) => effects::Origin::argument(u32::from(i)),
                Value::Allocation { offset, .. } | Value::MayAllocation { offset, .. } => {
                    let next = allocations.len() as u32;
                    effects::Origin::fresh(*allocations.entry(offset).or_insert(next))
                }
                Value::Alternatives(r) => {
                    let mut aliases = summary.arguments[r.range()]
                        .iter()
                        .map(|&id| Self::origin(&values, id));
                    let first = aliases.next().unwrap_or(effects::Origin::ANY);
                    if aliases.all(|alias| alias == first) {
                        first
                    } else {
                        effects::Origin::ANY
                    }
                }
                _ => effects::Origin::ANY,
            };
            values.push(origin);
        }
        row.fresh_sites = allocations.len() as u32;
        self.out.data.code_observations.push(effects::CodeRef {
            kind: effects::CodeKind::Class,
            index: class_id,
        });
        for (call_index, call) in summary.calls.iter().enumerate() {
            let callee = self.member_method(blob, authority, call.member)?;
            let local = (self.out.data.calls.len() - start.calls) as u32;
            let first = self.out.data.origins.len();
            for &arg in &summary.arguments[call.arguments.range()] {
                self.out.data.origins.push(Self::origin(&values, arg));
                self.out
                    .data
                    .callable_values
                    .push(Self::callable(&summary, arg));
            }
            let arguments = range(first, self.out.data.origins.len());
            let receiver = call
                .receiver
                .map_or(effects::Origin::ANY, |id| Self::origin(&values, id));
            let site = self.site(target, call.offset);
            self.out.data.calls.push(effects::CallRow {
                site,
                target: effects::CallTarget::Direct(callee),
                kind: match call.kind {
                    binary::InvokeKind::Static => effects::CallKind::Static,
                    binary::InvokeKind::Special => effects::CallKind::Special,
                    binary::InvokeKind::Virtual => effects::CallKind::Virtual,
                    binary::InvokeKind::Interface => effects::CallKind::Interface,
                },
                receiver,
                receiver_value: call.receiver.map_or(effects::ValueRef::UNKNOWN, |id| Self::callable(&summary, id)),
                result: summary.values.iter().position(|value| matches!(value,Value::CallResult(index) if *index as usize==call_index)).map_or(NONE,|index|index as u32),
                arguments,
                captures: effects::Range::EMPTY,
            });
            self.out.data.code_observations.push(effects::CodeRef {
                kind: effects::CodeKind::Method,
                index: callee.0,
            });
            self.out.data.flows.push(effects::FlowRef {
                source: receiver,
                sink: effects::FlowSink::CallReceiver,
                via: local,
                index: 0,
            });
            for index in 0..arguments.len {
                self.out.data.flows.push(effects::FlowRef {
                    source: self.out.data.origins[first + index as usize],
                    sink: effects::FlowSink::CallArgument,
                    via: local,
                    index,
                });
            }
            if call.kind == binary::InvokeKind::Static {
                self.initialize(blob, authority, call.member.owner)?;
            }
            self.check()?;
        }
        for (index, value) in summary.values.iter().enumerate() {
            match *value {
                Value::StaticField(member) | Value::Field { member, .. } => {
                    let field = self.field(blob, authority, member)?;
                    let (kind, base) = match *value {
                        Value::Field { receiver, .. } => (
                            effects::StorageKind::InstanceField,
                            Self::origin(&values, receiver),
                        ),
                        _ => (effects::StorageKind::StaticField, effects::Origin::ANY),
                    };
                    self.out.data.reads.push(effects::StorageRef {
                        kind,
                        member: field,
                        base,
                    });
                    self.out.data.value_flows.push(effects::ValueFlow {
                        kind: effects::ValueFlowKind::Load,
                        value: effects::ValueRef::local(index as u32),
                        index: (self.out.data.reads.len() - start.reads - 1) as u32,
                    });
                    if kind == effects::StorageKind::StaticField {
                        self.initialize(blob, authority, member.owner)?;
                    }
                }
                Value::Allocation { class, .. } | Value::MayAllocation { class, .. } => {
                    self.initialize(blob, authority, class)?
                }
                Value::Constant { pool_index, .. } => {
                    if let Ok(binary::BootstrapArgument::Class(owner)) =
                        class.bootstrap_argument(pool_index)
                    {
                        let text = self.borrowed(blob, owner)?;
                        let observed = self.class(authority, text)?;
                        self.out.data.code_observations.push(effects::CodeRef {
                            kind: effects::CodeKind::Class,
                            index: observed,
                        });
                    }
                }
                Value::Lambda(_) => self.out.open.push(OpenSite {
                    method: target,
                    pc: summary.value_offsets[index],
                    reason: OpenReason::LambdaCapture,
                }),
                Value::Alternatives(range) => {
                    for &value in &summary.arguments[range.range()] {
                        self.out.data.value_flows.push(effects::ValueFlow {
                            kind: effects::ValueFlowKind::Copy,
                            value: Self::callable(&summary, value),
                            index: index as u32,
                        });
                    }
                }
                _ => (),
            }
            self.check()?;
        }
        for write in &summary.field_writes {
            let member = self.field(blob, authority, write.member)?;
            let base = write
                .receiver
                .map_or(effects::Origin::ANY, |id| Self::origin(&values, id));
            let local = (self.out.data.writes.len() - start.writes) as u32;
            self.out.data.writes.push(effects::StorageRef {
                kind: if write.receiver.is_some() {
                    effects::StorageKind::InstanceField
                } else {
                    effects::StorageKind::StaticField
                },
                member,
                base,
            });
            self.out.data.flows.push(effects::FlowRef {
                source: Self::origin(&values, write.value),
                sink: effects::FlowSink::HeapWrite,
                via: local,
                index: 0,
            });
            self.out.data.value_flows.push(effects::ValueFlow {
                kind: effects::ValueFlowKind::Store,
                value: Self::callable(&summary, write.value),
                index: local,
            });
            if write.receiver.is_none() {
                self.initialize(blob, authority, write.member.owner)?;
            }
            self.check()?;
        }
        for (index, lambda) in summary.lambdas.iter().enumerate() {
            let implementation = self.member_method(blob, authority, lambda.implementation)?;
            self.out.data.code_observations.push(effects::CodeRef {
                kind: effects::CodeKind::Method,
                index: implementation.0,
            });
            self.creation(
                blob, class, method, &summary, &values, target, index, lambda,
            )?;
            // Creation is not invocation; all open channels remain explicit.
        }
        if let Some(returned) = summary.returned {
            self.out.data.value_flows.push(effects::ValueFlow {
                kind: effects::ValueFlowKind::Return,
                value: Self::callable(&summary, returned),
                index: 0,
            });
            self.out.data.flows.push(effects::FlowRef {
                source: Self::origin(&values, returned),
                sink: effects::FlowSink::Return,
                via: NONE,
                index: 0,
            });
            let result = binary::method_descriptor(method.descriptor)?.return_type;
            if result.starts_with('L') || result.starts_with('[') {
                self.out.data.escapes.push(effects::EscapeRef {
                    origin: Self::origin(&values, returned),
                    sink: effects::EscapeSink::Return,
                    index: 0,
                });
            }
        }
        if summary.unknown.is_some() {
            self.out.open.push(OpenSite {
                method: target,
                pc: 0,
                reason: OpenReason::LocalSummaryPartial,
            });
        }
        self.primitive_scan(target, method)?;
        if self
            .axiom
            .is_some_and(|axiom| axiom.permits(authority, class.major))
        {
            let code = method.code.expect("validated code");
            let mut finite_local = !matches!(summary.unknown, Some(error) if error.kind == binary::ErrorKind::ResourceLimit);
            // A structurally checked decoder does not prove that a separately
            // budgeted summary retained every effect. Match every field/call/
            // allocation PC before declaring those local channels exhaustive.
            let mut observed = Vec::new();
            for call in &summary.calls {
                observed.push((
                    call.offset,
                    match call.kind {
                        binary::InvokeKind::Virtual => 182,
                        binary::InvokeKind::Special => 183,
                        binary::InvokeKind::Static => 184,
                        binary::InvokeKind::Interface => 185,
                    },
                ));
            }
            for (value, &pc) in summary.values.iter().zip(&summary.value_offsets) {
                match value {
                    Value::StaticField(_) => observed.push((pc, 178)),
                    Value::Field { .. } => observed.push((pc, 180)),
                    Value::Allocation { .. } | Value::MayAllocation { .. } => {
                        observed.push((pc, 187))
                    }
                    _ => (),
                }
            }
            for write in &summary.field_writes {
                observed.push((
                    write.offset,
                    if write.receiver.is_some() { 181 } else { 179 },
                ));
            }
            observed.sort_unstable();
            let mut expected = Vec::new();
            let mut implicit_exception = false;
            for pc in 0..code.len() {
                if !self.validator.instruction_start(pc) {
                    continue;
                }
                let opcode = code[pc];
                if matches!(opcode, 178..=185 | 187) {
                    expected.push((pc as u32, opcode));
                }
                // Every instruction is checked, including all handler ranges.
                // Unsupported stores/reference array accesses are not hidden by
                // an earlier primitive operation or an unselected branch.
                if !matches!(opcode, 0..=49 | 51..=78 | 87..=167 | 170..=185 | 187 | 188 | 190 | 192 | 193 | 196 | 198..=200)
                    || (opcode == 196 && code[pc + 1] == 169)
                {
                    finite_local = false;
                    self.out.open.push(OpenSite {
                        method: target,
                        pc: pc as u32,
                        reason: OpenReason::UnsupportedInstruction,
                    });
                }
                if matches!(opcode, 18..=20) {
                    let cp = if opcode == 18 {
                        u16::from(code[pc + 1])
                    } else {
                        u16::from_be_bytes([code[pc + 1], code[pc + 2]])
                    };
                    if matches!(
                        class.bootstrap_argument(cp),
                        Ok(binary::BootstrapArgument::Dynamic { .. })
                    ) {
                        finite_local = false;
                    }
                }
                implicit_exception |= matches!(opcode, 46..=49 | 51..=53 | 108 | 109 | 112 | 113 | 178..=185 | 187 | 188 | 190 | 192);
            }
            if observed != expected || !finite_local {
                finite_local = false;
                self.out.open.push(OpenSite {
                    method: target,
                    pc: 0,
                    reason: OpenReason::IncompleteEffectInventory,
                });
            }
            if method.flags & (0x20 | 0x100) != 0 {
                finite_local = false;
            }
            if finite_local {
                let mut bits = row.top.bits()
                    & !((1 << effects::Channel::Reads as u32)
                        | (1 << effects::Channel::Writes as u32));
                if summary
                    .calls
                    .iter()
                    .all(|call| !call.kind.requires_receiver_dispatch())
                {
                    bits &= !(1 << effects::Channel::Calls as u32);
                }
                row.top = effects::TopMask::from_bits(bits).expect("known channel mask");
                if implicit_exception {
                    let member = self.shared_throwable_region()?;
                    self.out.data.writes.push(effects::StorageRef {
                        kind: effects::StorageKind::RuntimeState,
                        member,
                        base: effects::Origin::ANY,
                    });
                }
                // The law constrains accepted instructions, not arbitrary
                // application loaders, security hooks, VerifyError creation or
                // class-resolution execution. Composition MUST retain this
                // explicit ALL-TOP boundary, even if no local call occurs.
                let boundary = self.method(
                    class_id,
                    ForeignKind::RuntimeBoundary,
                    TextRef::builtin(3),
                    TextRef::builtin(1),
                )?;
                self.out.data.initializes.push(boundary);
            }
        }
        start.finish(&mut row, &self.out.data);
        // Only an admitted instruction-local axiom may close selected channels.
        // Its VM boundary, and all remaining TOP channels, are still composed.
        self.out.data.methods[target.0 as usize] = row;
        self.out.projected[target.0 as usize] = true;
        self.finish_adapters()?;
        self.check()
    }
    fn primitive_scan(
        &mut self,
        method_id: effects::MethodId,
        method: &MethodInfo<'_>,
    ) -> Result<(), Error> {
        if method.flags & 0x20 != 0 {
            self.out.open.push(OpenSite {
                method: method_id,
                pc: 0,
                reason: OpenReason::SynchronizedMethod,
            });
        }
        let code = method.code.expect("validated code");
        for pc in 0..code.len() {
            if !self.validator.instruction_start(pc) {
                continue;
            }
            let opcode = code[pc];
            let kind = match opcode {
                46 => Some(PrimitiveKind::Read(PrimitiveType::Int)),
                47 => Some(PrimitiveKind::Read(PrimitiveType::Long)),
                48 => Some(PrimitiveKind::Read(PrimitiveType::Float)),
                49 => Some(PrimitiveKind::Read(PrimitiveType::Double)),
                51 => Some(PrimitiveKind::Read(PrimitiveType::ByteOrBoolean)),
                52 => Some(PrimitiveKind::Read(PrimitiveType::Char)),
                53 => Some(PrimitiveKind::Read(PrimitiveType::Short)),
                190 => Some(PrimitiveKind::Length),
                188 => Some(PrimitiveKind::Allocate(match code[pc + 1] {
                    4 => PrimitiveType::Boolean,
                    5 => PrimitiveType::Char,
                    6 => PrimitiveType::Float,
                    7 => PrimitiveType::Double,
                    8 => PrimitiveType::Byte,
                    9 => PrimitiveType::Short,
                    10 => PrimitiveType::Int,
                    11 => PrimitiveType::Long,
                    _ => return Err(Error::Binding),
                })),
                108 | 109 | 112 | 113 => Some(PrimitiveKind::IntegerDivisionOrRemainder),
                _ => None,
            };
            if let Some(kind) = kind {
                let site = self.site(method_id, pc as u32);
                let exceptions = match kind {
                    PrimitiveKind::Read(_) => {
                        (1 << VmException::NullPointer as u32)
                            | (1 << VmException::ArrayIndexOutOfBounds as u32)
                    }
                    PrimitiveKind::Length => 1 << VmException::NullPointer as u32,
                    PrimitiveKind::Allocate(_) => {
                        (1 << VmException::NegativeArraySize as u32)
                            | (1 << VmException::OutOfMemory as u32)
                    }
                    PrimitiveKind::IntegerDivisionOrRemainder => {
                        1 << VmException::Arithmetic as u32
                    }
                };
                self.out.primitives.push(PrimitiveOperation {
                    site,
                    kind,
                    base: effects::Origin::ANY,
                    exceptions,
                    scalar_top: true,
                    shared_throwable_metadata: true,
                    requires_verification_and_vm_contract: true,
                });
                if matches!(kind, PrimitiveKind::Read(_) | PrimitiveKind::Length) {
                    self.out.data.reads.push(effects::StorageRef {
                        kind: effects::StorageKind::ArrayElements,
                        member: NONE,
                        base: effects::Origin::ANY,
                    });
                }
                for exception in 0..5 {
                    if exceptions & (1 << exception) != 0 {
                        self.out.data.throws.push(exception);
                    }
                }
            }
            let reason = match opcode {
                50 => Some(OpenReason::ReferenceArrayLoad),
                79..=86 => Some(OpenReason::ArrayWrite),
                189 | 197 => Some(OpenReason::ReferenceArrayAllocation),
                186 => Some(OpenReason::DynamicBootstrap),
                194 | 195 => Some(OpenReason::Monitor),
                191 => Some(OpenReason::ExplicitThrow),
                _ => None,
            };
            if let Some(reason) = reason {
                self.out.open.push(OpenSite {
                    method: method_id,
                    pc: pc as u32,
                    reason,
                });
            }
            self.check()?;
        }
        Ok(())
    }
    fn append(
        &mut self,
        demand: ClassDemand<'a>,
        provided: Option<ProvidedClass>,
    ) -> Result<(), Error> {
        if demand.authority == NONE
            || demand.owner.is_empty()
            || demand.owner.len() > u16::MAX as usize
        {
            return Err(Error::Binding);
        }
        let input = self.out.inputs.len() as u32;
        self.out.inputs.push(demand.owner);
        let owner = TextRef {
            source: TextSource::Input,
            index: input,
            start: 0,
            len: demand.owner.len() as u32,
        };
        let class_id = self.class(demand.authority, owner)?;
        let Some(provided) = provided else {
            let method = self.method(
                class_id,
                ForeignKind::UnavailableClass,
                TextRef::builtin(2),
                TextRef::builtin(1),
            )?;
            self.out.open.push(OpenSite {
                method,
                pc: 0,
                reason: OpenReason::MissingClass,
            });
            self.out.roots.push(method);
            return self.check();
        };
        if provided.authority != demand.authority || provided.provider == NONE {
            return Err(Error::Binding);
        }
        if provided.bytes.len() > self.limits.binary.max_class_bytes
            || self
                .class_bytes
                .checked_add(provided.bytes.len())
                .is_none_or(|bytes| bytes > self.limits.class_bytes)
        {
            return Err(Error::Budget);
        }
        if <[u8; 32]>::from(Sha256::digest(&provided.bytes)) != provided.class_sha256 {
            return Err(Error::ClassHash);
        }
        if self.out.classes[class_id as usize].blob != NONE {
            let previous = &self.out.blobs[self.out.classes[class_id as usize].blob as usize];
            if previous.class_sha256 != provided.class_sha256
                || previous.provider != provided.provider
                || previous.binding_sha256 != provided.binding_sha256
            {
                return Err(Error::ConflictingProvider);
            }
            return Ok(());
        }
        self.class_bytes = self
            .class_bytes
            .checked_add(provided.bytes.len())
            .ok_or(Error::Budget)?;
        if self.class_bytes > self.limits.class_bytes {
            return Err(Error::Budget);
        }
        let bytes = provided.bytes.clone();
        let class = binary::parse_class(&bytes, self.limits.binary)?;
        binary::diagnostic::validate_constant_pool(&class)?;
        if class.name != demand.owner {
            return Err(Error::ClassOwner);
        }
        let blob = self.out.blobs.len() as u32;
        let metadata = Arc::new(binary::ClassMetadata::new(
            provided.bytes.clone(),
            self.limits.binary,
        )?);
        self.metadata_bytes = self
            .metadata_bytes
            .checked_add(metadata.metadata_bytes())
            .ok_or(Error::Budget)?;
        self.out.blobs.push(Blob {
            metadata,
            bytes: provided.bytes,
            class_sha256: provided.class_sha256,
            authority: provided.authority,
            provider: provided.provider,
            binding_sha256: provided.binding_sha256,
        });
        self.out.classes[class_id as usize].blob = blob;
        let mut methods = Vec::with_capacity(class.methods.len());
        for method in &class.methods {
            let name = self.borrowed(blob, method.name)?;
            let descriptor = self.borrowed(blob, method.descriptor)?;
            let target = self.method(class_id, ForeignKind::Method, name, descriptor)?;
            methods.push(target);
            self.out.roots.push(target);
        }
        // Register all headers before projecting bodies; self calls reuse the
        // same method IDs and never consume a second declaration slot.
        for (method, target) in class.methods.iter().zip(methods) {
            self.emit_method(blob, class_id, &class, method, target)?;
        }
        self.check()
    }
}
struct Starts {
    calls: usize,
    code: usize,
    reads: usize,
    writes: usize,
    escapes: usize,
    init: usize,
    throws: usize,
    sync: usize,
    external: usize,
    flows: usize,
    value_flows: usize,
    creations: usize,
}
impl Starts {
    fn new(d: &effects::CapsuleData) -> Self {
        Self {
            calls: d.calls.len(),
            code: d.code_observations.len(),
            reads: d.reads.len(),
            writes: d.writes.len(),
            escapes: d.escapes.len(),
            init: d.initializes.len(),
            throws: d.throws.len(),
            sync: d.synchronizes.len(),
            external: d.external.len(),
            flows: d.flows.len(),
            value_flows: d.value_flows.len(),
            creations: d.creations.len(),
        }
    }
    fn finish(self, row: &mut effects::MethodRow, d: &effects::CapsuleData) {
        row.calls = range(self.calls, d.calls.len());
        row.code_observations = range(self.code, d.code_observations.len());
        row.reads = range(self.reads, d.reads.len());
        row.writes = range(self.writes, d.writes.len());
        row.escapes = range(self.escapes, d.escapes.len());
        row.initializes = range(self.init, d.initializes.len());
        row.throws = range(self.throws, d.throws.len());
        row.synchronizes = range(self.sync, d.synchronizes.len());
        row.external = range(self.external, d.external.len());
        row.flows = range(self.flows, d.flows.len());
        row.value_flows = range(self.value_flows, d.value_flows.len());
        row.creations = range(self.creations, d.creations.len());
    }
}

/// Atomic bounded projection. Errors publish no partial capsule collection.
pub fn produce<'a>(
    demands: &'a [ClassDemand<'a>],
    provider: &mut impl ClassProvider,
    limits: Limits,
) -> Result<Produced<'a>, Error> {
    produce_inner(demands, provider, limits, None)
}
/// Instruction-local finite channels under an explicitly admitted contract.
/// The returned VM boundary remains ALL-TOP; this is no overall closure claim.
pub fn produce_with_axiom<'a>(
    demands: &'a [ClassDemand<'a>],
    provider: &mut impl ClassProvider,
    limits: Limits,
    axiom: &RuntimeAxiom,
) -> Result<Produced<'a>, Error> {
    produce_inner(demands, provider, limits, Some(axiom))
}
fn produce_inner<'a>(
    demands: &'a [ClassDemand<'a>],
    provider: &mut impl ClassProvider,
    limits: Limits,
    axiom: Option<&RuntimeAxiom>,
) -> Result<Produced<'a>, Error> {
    if demands.len() > limits.classes
        || limits.rows >= NONE as usize
        || limits.references >= NONE as usize
    {
        return Err(Error::Budget);
    }
    let mut builder = Builder::new(limits, axiom);
    for &demand in demands {
        let input = provider.class(demand)?;
        builder.append(demand, input)?;
    }
    builder.check()?;
    effects::validate(
        &builder.out.data,
        builder.out.bounds(),
        effects::Limits {
            max_methods: limits.references,
            max_rows: limits.rows,
            max_bytes: limits.retained_bytes,
        },
    )?;
    Ok(builder.out)
}

#[cfg(test)]
mod provider_tests;
#[cfg(test)]
mod tests;
