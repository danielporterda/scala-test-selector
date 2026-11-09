//! Allocation-free identities and wire-independent semantic records.
pub mod symbol;

use std::fmt;

macro_rules! ids {
    ($($name:ident),* $(,)?) => {$ (
        #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
        #[repr(transparent)]
        pub struct $name(pub u32);
        impl $name {
            pub const NONE: Self = Self(u32::MAX);
            pub const fn index(self) -> usize { self.0 as usize }
            pub const fn is_none(self) -> bool { self.0 == u32::MAX }
            pub fn checked(index: usize) -> Result<Self, Error> {
                if index >= u32::MAX as usize { Err(Error::Limit("32-bit identifier capacity")) }
                else { Ok(Self(index as u32)) }
            }
        }
    )*};
}
ids!(
    StrId,
    FileId,
    SymbolId,
    OccurrenceId,
    BodyId,
    OperationId,
    ValueId,
    NodeId,
    EdgeId,
    ContextId,
    ProofId,
    SuiteId,
    SetId
);

/// The test-isolation contract used for selection. This describes an analysis
/// assumption, not a claim that the runner creates separate JVMs or processes.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum SuiteSemantics {
    #[default]
    SharedState,
    /// Hidden effects of another suite do not influence this suite. Known
    /// dependencies and uncertainty reached within a suite are still retained.
    Independent,
}
impl SuiteSemantics {
    /// Bit included in persisted exclusion assumptions for this contract.
    pub const fn assumption_bit(self) -> u32 {
        match self {
            Self::SharedState => 0,
            Self::Independent => 16,
        }
    }
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::SharedState => "shared_state",
            Self::Independent => "independent_suites",
        }
    }
}

/// Explicit premises of the test-selection model. These describe functional
/// test behavior, not verified properties of the JVM or external services.
/// Keeping the bits private prevents accidentally accepting unknown premises
/// when reading a saved result. Construction and iteration allocate nothing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SelectionContract(u32);
impl SelectionContract {
    pub const VERSION: &'static str = "selector-selection-contract/1";
    pub const SUITE_INDEPENDENCE: u32 = 16;
    pub const FUNCTIONAL_BEHAVIOR: u32 = 32;
    pub const CLOSED_APPLICATION_CLASSPATH: u32 = 64;
    pub const TRUSTED_RUNTIME_CONTRACTS: u32 = 128;
    pub const STABLE_EXTERNAL_INPUTS: u32 = 256;
    /// Opt-in premise that each suite uses its owning captured Test/fullClasspath.
    /// This is a runner/classloader assumption, not an observed loader trace.
    pub const OWNING_TEST_CLASSPATH: u32 = 512;
    /// Ordinary compilation preserves functional behavior for unchanged sources
    /// under an independently checked stable declared compiler/build input set.
    pub const ORDINARY_COMPILATION: u32 = 1024;
    pub const CURRENT_BASE_BITS: u32 = Self::FUNCTIONAL_BEHAVIOR
        | Self::CLOSED_APPLICATION_CLASSPATH
        | Self::TRUSTED_RUNTIME_CONTRACTS
        | Self::STABLE_EXTERNAL_INPUTS;
    pub const KNOWN_MASK: u32 = Self::CURRENT_BASE_BITS
        | Self::SUITE_INDEPENDENCE
        | Self::OWNING_TEST_CLASSPATH
        | Self::ORDINARY_COMPILATION;

    pub const fn current(suite_semantics: SuiteSemantics) -> Self {
        Self(Self::CURRENT_BASE_BITS | suite_semantics.assumption_bit())
    }
    /// Explicit conditional mode for suites using their owning captured test
    /// classpath. Current/default contracts never enable this premise.
    pub const fn owning_test_classpath() -> Self {
        Self(Self::CURRENT_BASE_BITS | Self::SUITE_INDEPENDENCE | Self::OWNING_TEST_CLASSPATH)
    }
    /// Separate opt-in extension; ordinary/default classpath certificates do not
    /// silently assume compilation stability.
    pub const fn owning_test_classpath_with_compilation() -> Self {
        Self(Self::owning_test_classpath().bits() | Self::ORDINARY_COMPILATION)
    }
    /// Saved reports may have older or fewer explicit premises. Never upgrade
    /// them to CURRENT while decoding, and never discard an unrecognized bit.
    pub const fn from_bits(bits: u32) -> Option<Self> {
        if bits & !Self::KNOWN_MASK == 0 {
            Some(Self(bits))
        } else {
            None
        }
    }
    pub const fn bits(self) -> u32 {
        self.0
    }
    pub const fn suite_semantics(self) -> SuiteSemantics {
        if self.0 & Self::SUITE_INDEPENDENCE != 0 {
            SuiteSemantics::Independent
        } else {
            SuiteSemantics::SharedState
        }
    }
    pub const fn contains(self, assumption: u32) -> bool {
        self.0 & assumption == assumption
    }
    pub fn assumptions(self) -> impl Iterator<Item = &'static str> {
        [
            (Self::SUITE_INDEPENDENCE, "suite_independence"),
            (Self::FUNCTIONAL_BEHAVIOR, "functional_behavior"),
            (
                Self::CLOSED_APPLICATION_CLASSPATH,
                "closed_application_classpath",
            ),
            (Self::TRUSTED_RUNTIME_CONTRACTS, "trusted_runtime_contracts"),
            (Self::STABLE_EXTERNAL_INPUTS, "stable_external_inputs"),
            (Self::OWNING_TEST_CLASSPATH, "owning_test_full_classpath"),
            (Self::ORDINARY_COMPILATION, "ordinary_compilation"),
        ]
        .into_iter()
        .filter_map(move |(bit, name)| self.contains(bit).then_some(name))
    }
}
impl Default for SelectionContract {
    fn default() -> Self {
        Self::current(SuiteSemantics::SharedState)
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}
impl Span {
    pub fn new(start: usize, end: usize) -> Result<Self, Error> {
        if start > end || end > u32::MAX as usize {
            return Err(Error::Invalid("source span"));
        }
        Ok(Self {
            start: start as u32,
            end: end as u32,
        })
    }
    pub fn contains(self, other: Self) -> bool {
        self.start <= other.start && other.end <= self.end
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct IdRange {
    pub start: u32,
    pub len: u32,
}
impl IdRange {
    pub fn range(self) -> std::ops::Range<usize> {
        self.start as usize..self.start as usize + self.len as usize
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct ContentHash(pub [u8; 32]);
impl ContentHash {
    pub fn from_hex(s: &str) -> Result<Self, Error> {
        if s.len() != 64 {
            return Err(Error::Invalid("SHA-256 length"));
        }
        let mut out = [0; 32];
        fn nibble(b: u8) -> Result<u8, Error> {
            match b {
                b'0'..=b'9' => Ok(b - b'0'),
                b'a'..=b'f' => Ok(b - b'a' + 10),
                b'A'..=b'F' => Ok(b - b'A' + 10),
                _ => Err(Error::Invalid("SHA-256 encoding")),
            }
        }
        for (i, b) in out.iter_mut().enumerate() {
            *b = (nibble(s.as_bytes()[i * 2])? << 4) | nibble(s.as_bytes()[i * 2 + 1])?;
        }
        Ok(Self(out))
    }
}
impl fmt::Display for ContentHash {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for b in self.0 {
            write!(f, "{b:02x}")?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub enum Error {
    Io(std::io::Error),
    Invalid(&'static str),
    Message(String),
    Limit(&'static str),
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(e) => e.fmt(f),
            Self::Invalid(s) => write!(f, "invalid {s}"),
            Self::Message(s) => f.write_str(s),
            Self::Limit(s) => write!(f, "resource limit: {s}"),
        }
    }
}
impl std::error::Error for Error {}
impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum RelationKind {
    Signature = 1,
    Parent = 2,
    Override = 3,
    Annotation = 4,
    Member = 5,
    Capture = 6,
    RuntimeBridge = 7,
    /// An optional native implementation was deferred for this receiver class
    /// (source) and exact virtual method contract (target). It is uncertainty
    /// at a matching dispatch, not an unconditional receiver initialization.
    DeferredDispatch = 8,
    /// Bounded implementation-discovery bookkeeping omitted contracts for this
    /// admitted receiver class. A contextual C -> C marker defers uncertainty
    /// until an actual instance dispatch can use C; it is not an initializer.
    DeferredReceiverDispatch = 9,
    /// Exact admitted class-chain lookup selected an executable implementation
    /// for receiver (source) and contract (target). This covers only that exact
    /// receiver/contract pair, and never certifies the implementation's effects.
    KnownReceiverDispatch = 10,
}
impl RelationKind {
    pub fn decode(n: u32) -> Result<Self, Error> {
        Ok(match n {
            1 => Self::Signature,
            2 => Self::Parent,
            3 => Self::Override,
            4 => Self::Annotation,
            5 => Self::Member,
            6 => Self::Capture,
            7 => Self::RuntimeBridge,
            8 => Self::DeferredDispatch,
            9 => Self::DeferredReceiverDispatch,
            10 => Self::KnownReceiverDispatch,
            _ => return Err(Error::Invalid("relation kind")),
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u32)]
pub enum EdgeKind {
    Compile = 1,
    Call = 2,
    VirtualCall = 3,
    Initialize = 4,
    Callback = 5,
    Fixture = 6,
    RuntimeBridge = 7,
    Guard = 8,
    Return = 9,
    Field = 10,
    Construct = 11,
    Default = 12,
}
impl EdgeKind {
    pub fn decode(n: u32) -> Result<Self, Error> {
        Ok(match n {
            1 => Self::Compile,
            2 => Self::Call,
            3 => Self::VirtualCall,
            4 => Self::Initialize,
            5 => Self::Callback,
            6 => Self::Fixture,
            7 => Self::RuntimeBridge,
            8 => Self::Guard,
            9 => Self::Return,
            10 => Self::Field,
            11 => Self::Construct,
            12 => Self::Default,
            _ => return Err(Error::Invalid("edge kind")),
        })
    }
    pub fn is_execution(self) -> bool {
        self != Self::Compile
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum Opcode {
    Call = 1,
    VirtualCall = 2,
    Allocate = 3,
    Assign = 4,
    Parameter = 5,
    Return = 6,
    BindCallback = 7,
    InvokeCallback = 8,
    LoadField = 9,
    StoreField = 10,
    Initialize = 11,
    Unknown = 12,
    Constant = 13,
    Join = 14,
    DefaultArgument = 15,
    RegisterTest = 16,
    /// Intrinsic element carrier for compiler-proven repeated actuals. Target
    /// names its synthetic element channel, never a concrete runtime class.
    PackSequence = 17,
    /// Read the may-union of a carrier's elements; this never invokes them.
    ReadElements = 18,
}
/// Reserved semantic channel for explicit sequence carriers. It is not a
/// compiler class/member and grants no dispatch or executable authority.
pub const SEQUENCE_ELEMENTS_SYMBOL: &str = "@selector:sequence-elements";
impl Opcode {
    pub const fn is_heap_site(self) -> bool {
        matches!(self, Self::Allocate | Self::PackSequence)
    }
    pub fn decode(n: u32) -> Result<Self, Error> {
        Ok(match n {
            1 => Self::Call,
            2 => Self::VirtualCall,
            3 => Self::Allocate,
            4 => Self::Assign,
            5 => Self::Parameter,
            6 => Self::Return,
            7 => Self::BindCallback,
            8 => Self::InvokeCallback,
            9 => Self::LoadField,
            10 => Self::StoreField,
            11 => Self::Initialize,
            12 => Self::Unknown,
            13 => Self::Constant,
            14 => Self::Join,
            15 => Self::DefaultArgument,
            16 => Self::RegisterTest,
            17 => Self::PackSequence,
            18 => Self::ReadElements,
            _ => return Err(Error::Invalid("opcode")),
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum IssueKind {
    MissingSource = 1,
    StaleSource = 2,
    UnsupportedSchema = 3,
    MissingSyntax = 4,
    UnresolvedSymbol = 5,
    UnknownExecution = 6,
    MissingBinary = 7,
    UnsupportedModel = 8,
    ContextConflict = 9,
    ResourceLimit = 10,
    InvalidInput = 11,
    /// An admitted child header has unavailable or deferred ancestry metadata.
    /// This is not evidence of missing effects in an admitted executable body.
    IncompleteHierarchy = 12,
}
impl IssueKind {
    pub fn decode(n: u32) -> Result<Self, Error> {
        Ok(match n {
            1 => Self::MissingSource,
            2 => Self::StaleSource,
            3 => Self::UnsupportedSchema,
            4 => Self::MissingSyntax,
            5 => Self::UnresolvedSymbol,
            6 => Self::UnknownExecution,
            7 => Self::MissingBinary,
            8 => Self::UnsupportedModel,
            9 => Self::ContextConflict,
            10 => Self::ResourceLimit,
            11 => Self::InvalidInput,
            12 => Self::IncompleteHierarchy,
            _ => return Err(Error::Invalid("issue kind")),
        })
    }
    /// Only execution uncertainty may be projected as a runtime graph issue.
    /// Hierarchy completeness is checked separately by consumers that need it.
    pub const fn is_execution_boundary(self) -> bool {
        !matches!(self, Self::IncompleteHierarchy)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Completion {
    Complete,
    Conservative,
    ResourceLimited,
}

pub const SOURCE_VERIFIED: u32 = 1;
pub const SYNTAX_VERIFIED: u32 = 2;
pub const FILE_BINARY_SOURCE: u32 = 4;
pub const SYMBOL_DEFINED: u32 = 1;
pub const SYMBOL_NATIVE_BINARY: u32 = 2;
/// Verified Scala compiler ClassSignature supplies the complete ordered parents.
pub const SYMBOL_SCALA_PARENTS_COMPLETE: u32 = 4;
/// An admitted exact JVM class/interface header verifies this external type's
/// metadata. This neither proves Scala parent order nor executable effects.
pub const SYMBOL_JVM_CLASS_HEADER_VERIFIED: u32 = 8;
/// Exact admitted JVM metadata (or the fixed Object-root ancestry law) supplies
/// all direct superclass/interface endpoints in this compiler context. This is
/// unordered local inventory, not Scala linearization, transitive closure,
/// finality or executable purity.
pub const SYMBOL_JVM_PARENTS_COMPLETE: u32 = 16;
/// Verified Scala compiler access metadata says this method is lexically
/// private, not package-qualified private. It supplies dispatch evidence only.
pub const SYMBOL_SCALA_PRIVATE_METHOD: u32 = 32;
pub const BODY_DEFERRED: u32 = 1;
pub const BODY_INITIALIZER: u32 = 2;
pub const BODY_LAZY: u32 = 4;
pub const BODY_BINARY_RECIPE: u32 = 8;
pub const BODY_STATIC_INITIALIZER: u32 = 16;
/// A source/hash-bound compiler recipe without a written expression body,
/// currently restricted to proven constructor parameter accessors.
pub const BODY_SOURCE_RECIPE: u32 = 32;
pub const OP_STATIC_FIELD: u32 = 1;
pub const EDGE_UNKNOWN: u32 = 1;
/// Same-instance Scala super invocation; a trait's plain super is stackable.
pub const OP_SUPER: u32 = 2;
/// Explicit Scala super qualifier, with the compiler-bound target retained.
pub const OP_QUALIFIED_SUPER: u32 = 4;
/// Compiler-inserted Apply(Id(callee), [OriginalTree(same source span)]).
pub const OP_SYNTHETIC_EXACT_ORIGINAL_ARGUMENT: u32 = 8;
/// Unknown expansion preserves the compile-time macro identity in `target`.
/// `a` may reference a tagged result-type Constant, never a runtime function.
pub const OP_MACRO_EXPANSION: u32 = 16;
/// Compile-only result TypeRef in Constant.target; its opaque unknown value is
/// opaque metadata, and cannot establish an allocation or absence certificate.
pub const OP_MACRO_RESULT_TYPE: u32 = 32;
/// Structural certificate: exact before-expansion IdTree and bare result TypeRef.
/// Library implementation/effects still require hash-bound native admission.
pub const OP_MACRO_DIRECT_TREE: u32 = 64;
/// Compiler synthetic Apply-over-Apply rooted at an exact method identity.
/// This marks a later parameter clause; native descriptor admission must prove
/// it belongs to the same call before folding an otherwise unknown callback.
pub const OP_SYNTHETIC_PARAMETER_APPLY: u32 = 128;
/// Hash-bound native descriptor/class authority for an additive sequence
/// element view. The original call, unknowns and effects remain authoritative;
/// this bit never asserts a concrete Seq class or complete implementation.
pub const OP_SEQUENCE_ELEMENT_VIEW: u32 = 1 << 9;
/// Exact trusted native primitive-array model: retain the element-read heap
/// dependency while its scalar data remains TOP. This never certifies generic
/// container reads, reference arrays, callback values or caller-array writes.
pub const OP_TRUSTED_PRIMITIVE_READ: u32 = 1 << 10;
/// An admitted native Call came from JVM invokestatic or invokespecial. This
/// records nonvirtual dispatch only: the call, receiver data, initialization,
/// missing targets and all callee effects remain observable. Consumers honor
/// it only inside a binary recipe in a binary-source file.
pub const OP_JVM_NONVIRTUAL: u32 = 1 << 11;
/// Exact source/compiler or versioned ABI proof of the modeled callback's
/// flattened argument slot. These bits transfer unchanged to a modeled edge;
/// they never declare the callee's remaining effects complete.
pub const CALLBACK_ARGUMENT_PRESENT: u32 = 1 << 8;
pub const CALLBACK_ARGUMENT_SHIFT: u32 = 16;
pub const CALLBACK_ARGUMENT_MASK: u32 = 0xffff_0000;
pub const fn encode_callback_argument(slot: usize) -> Option<u32> {
    if slot <= u16::MAX as usize {
        Some(CALLBACK_ARGUMENT_PRESENT | ((slot as u32) << CALLBACK_ARGUMENT_SHIFT))
    } else {
        None
    }
}
pub const fn callback_argument_slot(flags: u32) -> Option<usize> {
    if flags & CALLBACK_ARGUMENT_PRESENT != 0 {
        Some(((flags & CALLBACK_ARGUMENT_MASK) >> CALLBACK_ARGUMENT_SHIFT) as usize)
    } else {
        None
    }
}

/// Verified empty initialization effect, currently restricted to JVM bootstrap
/// Object/AnyRef leaves. It does not imply a precise return value.
pub const NODE_EFFECTS_COMPLETE: u32 = 1 << 31;
pub const EDGE_CALLBACK_IMMEDIATE: u32 = 2;
pub const EDGE_CALLBACK_DEFERRED: u32 = 4;
pub const EDGE_TEST_REGISTRATION: u32 = 8;
pub const EDGE_EFFECTS_COMPLETE: u32 = 16;
/// Operation-scoped Guard edge whose receiver may have an unadmitted native
/// override. Consumers must check that receiver before emitting uncertainty;
/// this edge is never itself an executable method candidate.
pub const EDGE_DEFERRED_DISPATCH: u32 = 32;

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn receiver_dispatch_relations_have_distinct_stable_wire_tags() {
        for (tag, relation) in [
            (8, RelationKind::DeferredDispatch),
            (9, RelationKind::DeferredReceiverDispatch),
            (10, RelationKind::KnownReceiverDispatch),
        ] {
            assert_eq!(relation as u32, tag);
            assert_eq!(RelationKind::decode(tag).unwrap(), relation);
        }
        assert!(RelationKind::decode(11).is_err());
    }
    #[test]
    fn saved_contracts_do_not_acquire_new_premises_or_discard_unknown_bits() {
        let legacy = SelectionContract::from_bits(0).unwrap();
        assert_eq!(legacy.assumptions().count(), 0);
        assert_eq!(legacy.suite_semantics(), SuiteSemantics::SharedState);
        let independent = SelectionContract::from_bits(16).unwrap();
        assert_eq!(
            independent.assumptions().collect::<Vec<_>>(),
            ["suite_independence"]
        );
        assert!(!independent.contains(SelectionContract::TRUSTED_RUNTIME_CONTRACTS));
        let owning = SelectionContract::owning_test_classpath();
        assert_eq!(owning.bits(), 1008);
        let compilation = SelectionContract::owning_test_classpath_with_compilation();
        assert_eq!(compilation.bits(), 2032);
        assert_eq!(
            compilation.assumptions().last(),
            Some("ordinary_compilation")
        );
        assert!(!owning.contains(SelectionContract::ORDINARY_COMPILATION));
        assert!(
            !SelectionContract::current(SuiteSemantics::Independent)
                .contains(SelectionContract::ORDINARY_COMPILATION)
        );
        assert_eq!(
            owning.assumptions().last(),
            Some("owning_test_full_classpath")
        );
        assert_eq!(owning.suite_semantics(), SuiteSemantics::Independent);
        assert!(SelectionContract::from_bits(1).is_none());
        assert!(SelectionContract::from_bits(SelectionContract::KNOWN_MASK | 2048).is_none());
        for mode in [SuiteSemantics::SharedState, SuiteSemantics::Independent] {
            let contract = SelectionContract::current(mode);
            assert_eq!(contract.suite_semantics(), mode);
            assert_eq!(
                SelectionContract::from_bits(contract.bits()),
                Some(contract)
            );
            assert!(contract.contains(SelectionContract::CURRENT_BASE_BITS));
            assert_eq!(
                contract.assumptions().count(),
                if mode == SuiteSemantics::Independent {
                    5
                } else {
                    4
                }
            );
        }
    }

    #[test]
    fn callback_slot_flags_preserve_zero_and_bounds_without_other_flag_aliases() {
        for slot in [0, 1, 255, u16::MAX as usize] {
            let flags = encode_callback_argument(slot).unwrap();
            assert_eq!(
                callback_argument_slot(flags | OP_SUPER | EDGE_CALLBACK_IMMEDIATE),
                Some(slot)
            );
        }
        assert_eq!(encode_callback_argument(u16::MAX as usize + 1), None);
        assert_eq!(callback_argument_slot(CALLBACK_ARGUMENT_MASK), None);
        assert_eq!(callback_argument_slot(EDGE_TEST_REGISTRATION), None);
    }

    #[test]
    fn checked_ids_and_ranges() {
        assert!(NodeId::checked(u32::MAX as usize).is_err());
        assert!(Span::new(5, 4).is_err());
        assert_eq!(
            Span::new(0, 10).unwrap().contains(Span::new(4, 8).unwrap()),
            true
        );
        assert_eq!(std::mem::size_of::<NodeId>(), 4);
    }
    #[test]
    fn hash_roundtrip() {
        let h = ContentHash([0xa3; 32]);
        assert_eq!(ContentHash::from_hex(&h.to_string()).unwrap(), h);
        assert!(ContentHash::from_hex(&"界".repeat(21)).is_err());
        assert!(ContentHash::from_hex(&format!("a{}", "界".repeat(21))).is_err());
    }
}
