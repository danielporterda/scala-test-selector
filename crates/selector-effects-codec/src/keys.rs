//! Fixed-size provenance keys. These describe identity, not semantic authority.
use crate::{Error, NONE};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Hash(pub [u8; 32]);
impl Hash {
    pub fn is_zero(self) -> bool {
        self.0 == [0; 32]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Binding {
    pub producer: Hash,
    pub facts: Hash,
    pub graph: Hash,
    /// Zero is an explicitly expected absence, never an unverified wildcard.
    /// Consumers still need all runtime/environment channels proved closed.
    pub runtime: Hash,
    pub inputs: Hash,
    pub root_universe: Hash,
    pub contracts: Hash,
    pub member_authority: Hash,
    pub fact_nodes: u32,
    pub fact_symbols: u32,
    pub fact_operations: u32,
    pub roots: u32,
}
impl Binding {
    pub(crate) fn validate(self) -> Result<(), Error> {
        if self.producer.is_zero()
            || self.facts.is_zero()
            || self.graph.is_zero()
            || self.inputs.is_zero()
            || self.root_universe.is_zero()
            || self.contracts.is_zero()
            || self.member_authority.is_zero()
            || self.fact_nodes == NONE
            || self.fact_symbols == NONE
            || self.fact_operations == NONE
        {
            return Err(Error::Invalid("unbound capsule identity"));
        }
        if self.roots > self.fact_nodes {
            return Err(Error::Invalid("capsule root count"));
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TextRange {
    pub start: u32,
    pub len: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ContextKey {
    pub name: u32,
    /// Exact ordered classpath/capture authority for this compiler context.
    pub inputs: Hash,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum ProviderKind {
    Archive = 1,
    Directory = 2,
    RuntimeImage = 3,
}
impl ProviderKind {
    pub(crate) fn decode(value: u32) -> Result<Self, Error> {
        match value {
            1 => Ok(Self::Archive),
            2 => Ok(Self::Directory),
            3 => Ok(Self::RuntimeImage),
            _ => Err(Error::Invalid("capsule provider kind")),
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProviderKey {
    pub context: u32,
    pub ordinal: u32,
    pub kind: ProviderKind,
    pub path: u32,
    pub digest: Hash,
}

/// Only a resolved provider AND exact class hash permits a finite method row.
/// The absent form retains its logical ABI and must correspond to ALL TOP.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ForeignMethod {
    pub context: u32,
    pub provider: u32,
    pub class: Hash,
    pub owner: u32,
    pub name: u32,
    pub descriptor: u32,
    /// Descriptive hint only. It cannot replace a FactNode capsule or discharge
    /// source uncertainty. A linker needs independent exact method/coverage
    /// authority, and must reject conflicts before choosing one subject.
    pub node: u32,
    pub method_flags: u32,
    pub resolved: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum MemberKind {
    StaticField = 1,
    InstanceField = 2,
    ArrayElements = 3,
    RuntimeState = 4,
}
impl MemberKind {
    pub(crate) fn decode(value: u32) -> Result<Self, Error> {
        match value {
            1 => Ok(Self::StaticField),
            2 => Ok(Self::InstanceField),
            3 => Ok(Self::ArrayElements),
            4 => Ok(Self::RuntimeState),
            _ => Err(Error::Invalid("capsule member kind")),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum MemberIdentity {
    FactSymbol = 0,
    ForeignMember = 1,
    RuntimeKey = 2,
    ArrayKey = 3,
}
impl MemberIdentity {
    pub(crate) fn decode(value: u32) -> Result<Self, Error> {
        match value {
            0 => Ok(Self::FactSymbol),
            1 => Ok(Self::ForeignMember),
            2 => Ok(Self::RuntimeKey),
            3 => Ok(Self::ArrayKey),
            _ => Err(Error::Invalid("capsule member identity kind")),
        }
    }
}

/// A raw CP owner/name/descriptor is not a canonical alias proof. False keeps
/// the corresponding read/write/escape channel TOP at every use.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MemberKey {
    pub identity: MemberIdentity,
    pub fact_symbol: u32,
    pub context: u32,
    pub provider: u32,
    pub class: Hash,
    pub owner: u32,
    pub name: u32,
    pub descriptor: u32,
    pub kind: MemberKind,
    pub canonical: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum ClassIdentity {
    FactSymbol = 0,
    ForeignClass = 1,
}
impl ClassIdentity {
    pub(crate) fn decode(value: u32) -> Result<Self, Error> {
        match value {
            0 => Ok(Self::FactSymbol),
            1 => Ok(Self::ForeignClass),
            _ => Err(Error::Invalid("capsule class identity kind")),
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ClassKey {
    pub identity: ClassIdentity,
    pub fact_symbol: u32,
    pub context: u32,
    pub provider: u32,
    pub class: Hash,
    pub owner: u32,
    pub node: u32,
    pub resolved: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum AuthorityKind {
    SourceRecipe = 1,
    NativeEnvelope = 2,
    ReviewedContract = 3,
}
impl AuthorityKind {
    pub(crate) fn decode(value: u32) -> Result<Self, Error> {
        match value {
            1 => Ok(Self::SourceRecipe),
            2 => Ok(Self::NativeEnvelope),
            3 => Ok(Self::ReviewedContract),
            _ => Err(Error::Invalid("capsule authority kind")),
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AuthorityKey {
    pub producer: Hash,
    pub contract: Hash,
    pub kind: AuthorityKind,
    pub name: u32,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExceptionKey {
    pub class: u32,
    /// Exact type-key availability only. This proves neither fresh exception
    /// allocation nor bounded implicit stack/native effects. Preallocated or
    /// shared VM exceptions need explicit runtime writes/flows or channel TOP.
    pub known: bool,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExternalKey {
    pub context: u32,
    pub kind: u32,
    pub name: u32,
    pub digest: Hash,
    pub canonical: bool,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum SiteKind {
    FactOperation = 0,
    NativeBytecode = 1,
}
impl SiteKind {
    pub(crate) fn decode(value: u32) -> Result<Self, Error> {
        match value {
            0 => Ok(Self::FactOperation),
            1 => Ok(Self::NativeBytecode),
            _ => Err(Error::Invalid("capsule site kind")),
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SiteKey {
    pub method: u32,
    pub offset: u32,
    pub fact_operation: u32,
    pub kind: SiteKind,
}

/// Exact invoked SAM ABI. `resolved` is only a structural claim; a trusted
/// producer must establish the provider/interface and authority binding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SamKey {
    pub authority: u32,
    pub context: u32,
    pub provider: u32,
    pub class: Hash,
    pub owner: u32,
    pub name: u32,
    pub descriptor: u32,
    pub resolved: bool,
}

/// Exact normalized invokedynamic adapter identity. Hashes bind ordered raw BSM
/// arguments and the complete adaptation/bridge proof; names alone never link
/// a source recipe or grant finite callable behavior.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CallableAdapterKey {
    pub authority: u32,
    pub enclosing_method: u32,
    pub enclosing_foreign_method: u32,
    pub site: u32,
    pub bootstrap_foreign_method: u32,
    pub bootstrap_handle_kind: u32,
    pub bootstrap_arguments: Hash,
    pub implementation_foreign_method: u32,
    pub implementation_handle_kind: u32,
    pub sam: u32,
    pub invoked_name: u32,
    pub invoked_descriptor: u32,
    pub instantiated_descriptor: u32,
    pub adaptation: Hash,
    pub normalized_arity: u32,
    pub normalized_captures: u32,
    pub resolved: bool,
}

/// A creation-specific reviewed default-method route. This records the complete
/// native proof digest; it does not infer compatibility from a method name and
/// does not certify that the default method has no effects.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CallableBridgeProofKey {
    pub authority: u32,
    pub creation: u32,
    pub creator_adapter: u32,
    pub from_sam: u32,
    pub to_sam: u32,
    pub default_foreign_method: u32,
    pub generated_method_set: Hash,
    pub default_code: Hash,
    pub transport_policy: Hash,
    pub proof: Hash,
    pub no_override: bool,
    pub resolved: bool,
}

#[repr(u32)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PhaseKind {
    ClassInitialization = 0,
    LoadingVerification = 1,
    UnavailableClass = 2,
}
impl PhaseKind {
    pub fn decode(value: u32) -> Result<Self, crate::Error> {
        match value {
            0 => Ok(Self::ClassInitialization),
            1 => Ok(Self::LoadingVerification),
            2 => Ok(Self::UnavailableClass),
            _ => Err(crate::Error::Invalid("runtime phase kind")),
        }
    }
}
/// Runtime/class availability is not a fabricated JVM member. Phase subjects
/// remain ALL TOP until a separately admitted explicit phase contract exists.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PhaseKey {
    pub class: u32,
    pub authority: u32,
    pub kind: PhaseKind,
}
