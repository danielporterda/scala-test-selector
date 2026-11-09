//! Creation-specific Scala Function0 default-bridge authority.
//!
//! This does not canonicalize SAM names or grant library purity. A compatible
//! activation must execute the REAL reviewed default-method capsule with the
//! same callable payload as its receiver. Its calls, BoxedUnit read/initializer,
//! exceptions, loading and all other open effects remain ordinary dependencies.
use crate::ProvidedClass;
use selector_models::binary::{self, BootstrapArgument, ClassFile, MemberRef, ReferenceKind};
use sha2::{Digest, Sha256};

pub const FUNCTION0: &str = "scala/Function0";
pub const VOID_FUNCTION0: &str = "scala/runtime/java8/JFunction0$mcV$sp";
pub const GENERIC_DESCRIPTOR: &str = "()Ljava/lang/Object;";
pub const VOID_DESCRIPTOR: &str = "()V";
pub const STANDARD_FACTORY_CONTRACT: &str = "java21-standard-lambda-metafactory-method-set/v1:exact-java-base:requested-name-only:no-extra-markers:static-exact-capture-types:reference-or-void-return";
pub const LAMBDA_METAFACTORY: &str = "java/lang/invoke/LambdaMetafactory";
const META_DESCRIPTOR: &str = "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodHandle;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;";
const ALT_DESCRIPTOR: &str = "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;[Ljava/lang/Object;)Ljava/lang/invoke/CallSite;";
const LAMBDA_METAFACTORY_HASH: [u8; 32] = [
    0x85, 0x73, 0xd4, 0x64, 0x15, 0x5b, 0xd9, 0xb3, 0xc8, 0x75, 0x59, 0x53, 0xfd, 0x58, 0x8a, 0x0f,
    0x7d, 0x03, 0x76, 0x0b, 0x24, 0xf8, 0x27, 0x01, 0x5a, 0x87, 0xf1, 0xd1, 0xb5, 0x51, 0x5d, 0x9a,
];
pub const TRANSPORT_POLICY_VERSION: &str = "scala-function0-default/v1:exact-static-bsm-no-renamed-default-override:same-payload-receiver:zero-creator-captures:real-default-effects";
pub fn transport_policy_sha256() -> [u8; 32] {
    Sha256::digest(TRANSPORT_POLICY_VERSION.as_bytes()).into()
}
const MAX_CAPTURES: usize = 64;
const FUNCTION0_HASH: [u8; 32] = [
    0xa2, 0xe0, 0x79, 0xfb, 0xd9, 0xb6, 0xda, 0x1f, 0xbd, 0x23, 0xe2, 0xbe, 0x74, 0x07, 0x1a, 0x77,
    0x51, 0x4b, 0xa2, 0x7e, 0xf9, 0xa4, 0x4f, 0xc8, 0xff, 0xd2, 0x0e, 0x24, 0x92, 0x83, 0xfd, 0xa8,
];
const VOID_FUNCTION0_HASH: [u8; 32] = [
    0x68, 0xaf, 0x46, 0x18, 0x0a, 0xa1, 0x5e, 0xc6, 0xad, 0x62, 0xd8, 0xd7, 0x25, 0xd5, 0xe5, 0x7d,
    0x1e, 0xa6, 0x0e, 0x24, 0x94, 0x1a, 0xf6, 0x94, 0x59, 0x40, 0xbb, 0x83, 0x6d, 0x80, 0x50, 0xf7,
];

#[derive(Debug)]
pub enum Error {
    ProviderBinding,
    ReviewedClass,
    DefaultBody,
    Factory,
    UnsupportedAdaptation,
    Budget,
    StandardFactory,
    Provider(Box<crate::provider::Error>),
    Binary(binary::BinaryError),
}
impl From<binary::BinaryError> for Error {
    fn from(value: binary::BinaryError) -> Self {
        Self::Binary(value)
    }
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "native callable bridge {self:?}")
    }
}
impl std::error::Error for Error {}
type Result<T> = std::result::Result<T, Error>;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ClassIdentity {
    pub authority: u32,
    pub provider: u32,
    pub binding_sha256: [u8; 32],
    pub class_sha256: [u8; 32],
}

/// Borrows the immutable provider bytes and owns one bounded parsed table set.
/// The native emitter can reuse `parsed()` rather than parse every creation.
/// `ProvidedClass` still requires the existing ordered-provider admission; this
/// constructor does not manufacture loader, prefix or effect authority.
pub struct BoundClass<'a> {
    parsed: ClassFile<'a>,
    identity: ClassIdentity,
}
impl<'a> BoundClass<'a> {
    pub fn admit(
        provided: &'a ProvidedClass,
        authority: u32,
        owner: &str,
        limits: binary::Limits,
    ) -> Result<Self> {
        if authority == u32::MAX
            || provided.authority != authority
            || provided.provider == u32::MAX
            || provided.binding_sha256 == [0; 32]
            || <[u8; 32]>::from(Sha256::digest(&provided.bytes)) != provided.class_sha256
        {
            return Err(Error::ProviderBinding);
        }
        let parsed = binary::parse_class(&provided.bytes, limits)?;
        if parsed.name != owner {
            return Err(Error::ProviderBinding);
        }
        Ok(Self {
            parsed,
            identity: ClassIdentity {
                authority,
                provider: provided.provider,
                binding_sha256: provided.binding_sha256,
                class_sha256: provided.class_sha256,
            },
        })
    }
    pub fn parsed(&self) -> &ClassFile<'a> {
        &self.parsed
    }
    pub fn identity(&self) -> ClassIdentity {
        self.identity
    }
}

/// An explicit Java21 API axiom for the bounded generated-method set, not an
/// execution-effect, loader-isolation, class-initialization or JNI contract.
///
/// Java21 LambdaMetafactory specifies generated methods under the requested
/// interfaceMethodName (including alternate bridges), plus Object/serialization
/// methods. No methods named apply are added to an apply$mcV$sp creation, or the
/// reverse. This narrow law is supported only for the exact reviewed java.base
/// class below and the bounded factory shapes checked by `creation`.
/// <https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/lang/invoke/LambdaMetafactory.html>
///
/// Private issuance requires the actual first selected provider to be the
/// admitted declared java.base image. It does not assert that a historical test
/// runner used that image, or that agents/custom loaders cannot affect a future
/// process. Such execution floors stay TOP under their separate contracts.
pub struct Java21StandardLambdaMetafactory {
    class: ClassIdentity,
    platform_sha256: [u8; 32],
    method_code_sha256: [[u8; 32]; 2],
    binding_sha256: [u8; 32],
}
impl Java21StandardLambdaMetafactory {
    pub fn producer_sha256() -> [u8; 32] {
        let mut hash = Sha256::new();
        hash.update(STANDARD_FACTORY_CONTRACT.as_bytes());
        hash.update(LAMBDA_METAFACTORY_HASH);
        for bytes in [
            include_bytes!("framework_transport.rs").as_slice(),
            include_bytes!("provider.rs").as_slice(),
            include_bytes!("../../selector-models/src/binary.rs").as_slice(),
            include_bytes!("../../selector-models/src/binary_diagnostic.rs").as_slice(),
            include_bytes!("../../selector-models/src/binary_envelope.rs").as_slice(),
            include_bytes!("../../selector-runtime-platform/src/lib.rs").as_slice(),
        ] {
            hash.update((bytes.len() as u64).to_le_bytes());
            hash.update(bytes);
        }
        hash.finalize().into()
    }
    pub fn admit(
        provider: &mut crate::provider::VerifiedProvider<'_>,
        authority: u32,
        contract: &str,
        expected_producer: [u8; 32],
        limits: binary::Limits,
    ) -> Result<Self> {
        Self::validate_requested_contract(contract, expected_producer)?;
        let (input, platform_sha256) = provider
            .declared_java21_class(authority, LAMBDA_METAFACTORY)
            .map_err(|error| Error::Provider(Box::new(error)))?;
        Self::verified_class(&input, platform_sha256, limits)
    }
    fn validate_requested_contract(contract: &str, expected_producer: [u8; 32]) -> Result<()> {
        if contract != STANDARD_FACTORY_CONTRACT || expected_producer != Self::producer_sha256() {
            return Err(Error::StandardFactory);
        }
        Ok(())
    }
    fn verified_class(
        input: &ProvidedClass,
        platform_sha256: [u8; 32],
        limits: binary::Limits,
    ) -> Result<Self> {
        if platform_sha256 == [0; 32] || input.class_sha256 != LAMBDA_METAFACTORY_HASH {
            return Err(Error::StandardFactory);
        }
        let class = BoundClass::admit(input, input.authority, LAMBDA_METAFACTORY, limits)?;
        if class.parsed.major != 65 || class.parsed.flags & 0x11 != 0x11 {
            return Err(Error::StandardFactory);
        }
        let mut validator = binary::diagnostic::CodeValidator::default();
        let mut method_code_sha256 = [[0; 32]; 2];
        for (index, (name, descriptor)) in [
            ("metafactory", META_DESCRIPTOR),
            ("altMetafactory", ALT_DESCRIPTOR),
        ]
        .into_iter()
        .enumerate()
        {
            let method = class.parsed.method(name, Some(descriptor))?;
            // The axiom is not derived from the absence of handlers/effects;
            // it is the explicit standard API law under the pinned provider.
            if method.flags & 9 != 9 || method.flags & (0x100 | 0x400) != 0 {
                return Err(Error::StandardFactory);
            }
            validator.validate(&class.parsed, method, limits)?;
            method_code_sha256[index] =
                Sha256::digest(method.code.ok_or(Error::StandardFactory)?).into();
        }
        let mut hash = Sha256::new();
        hash.update(b"selector-java21-standard-lambda-factory-token/v1\0");
        hash.update(Self::producer_sha256());
        hash.update(platform_sha256);
        hash.update(class.identity.authority.to_le_bytes());
        hash.update(class.identity.provider.to_le_bytes());
        hash.update(class.identity.binding_sha256);
        hash.update(class.identity.class_sha256);
        for code in method_code_sha256 {
            hash.update(code);
        }
        Ok(Self {
            class: class.identity,
            platform_sha256,
            method_code_sha256,
            binding_sha256: hash.finalize().into(),
        })
    }
    pub fn class_identity(&self) -> ClassIdentity {
        self.class
    }
    pub fn platform_sha256(&self) -> [u8; 32] {
        self.platform_sha256
    }
    pub fn method_code_sha256(&self) -> [[u8; 32]; 2] {
        self.method_code_sha256
    }
    pub fn binding_sha256(&self) -> [u8; 32] {
        self.binding_sha256
    }
    /// Derived member authority from this privately admitted token. A separate
    /// adapter must still validate the full BSM arguments and value mapping.
    pub fn validate_bootstrap(
        &self,
        authority: u32,
        member: MemberRef<'_>,
        kind: ReferenceKind,
    ) -> Result<ClassIdentity> {
        if authority != self.class.authority
            || kind != ReferenceKind::InvokeStatic
            || member.owner != LAMBDA_METAFACTORY
            || !matches!(
                (member.name, member.descriptor),
                ("metafactory", META_DESCRIPTOR) | ("altMetafactory", ALT_DESCRIPTOR)
            )
        {
            return Err(Error::StandardFactory);
        }
        Ok(self.class)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Direction {
    /// A generic Function0 creation inherits apply$mcV$sp: invoke apply, discard.
    GenericToVoid,
    /// A JFunction0$mcV$sp creation inherits apply: invoke void, read BoxedUnit.
    VoidToGeneric,
}

/// Evidence for a real interface default. Private fields prevent replacing its
/// class/body identity after validation. It is NOT an execution-effect capsule.
pub struct DefaultBridge {
    direction: Direction,
    class: ClassIdentity,
    code_sha256: [u8; 32],
}
impl DefaultBridge {
    pub fn verify(class: &BoundClass<'_>, limits: binary::Limits) -> Result<Self> {
        let (direction, expected, name, descriptor, call_owner, call_name, call_descriptor) =
            match class.parsed.name {
                FUNCTION0 => (
                    Direction::GenericToVoid,
                    FUNCTION0_HASH,
                    "apply$mcV$sp",
                    VOID_DESCRIPTOR,
                    FUNCTION0,
                    "apply",
                    GENERIC_DESCRIPTOR,
                ),
                VOID_FUNCTION0 => (
                    Direction::VoidToGeneric,
                    VOID_FUNCTION0_HASH,
                    "apply",
                    GENERIC_DESCRIPTOR,
                    VOID_FUNCTION0,
                    "apply$mcV$sp",
                    VOID_DESCRIPTOR,
                ),
                _ => return Err(Error::ReviewedClass),
            };
        if class.identity.class_sha256 != expected || class.parsed.flags & 0x200 == 0 {
            return Err(Error::ReviewedClass);
        }
        let method = class.parsed.method(name, Some(descriptor))?;
        let code = method.code.ok_or(Error::DefaultBody)?;
        if method.flags & 1 == 0
            || method.flags & (8 | 0x20 | 0x100 | 0x400) != 0
            || method.exception_handlers != 0
            || !method.exception_table.is_empty()
        {
            return Err(Error::DefaultBody);
        }
        let geometry = match direction {
            Direction::GenericToVoid => {
                code.len() == 8 && code[0] == 42 && code[1] == 185 && code[4..] == [1, 0, 87, 177]
            }
            Direction::VoidToGeneric => {
                code.len() == 10
                    && code[0] == 42
                    && code[1] == 185
                    && code[4..7] == [1, 0, 178]
                    && code[9] == 176
            }
        };
        if !geometry {
            return Err(Error::DefaultBody);
        }
        let summary = binary::summarize(&class.parsed, method, limits);
        let Some(call) = summary.calls.first() else {
            return Err(Error::DefaultBody);
        };
        if !summary.complete()
            || !summary.unknown_offsets.is_empty()
            || summary.calls.len() != 1
            || !summary.field_writes.is_empty()
            || !summary.lambdas.is_empty()
            || call.offset != 1
            || call.kind != binary::InvokeKind::Interface
            || call.arguments.len != 0
            || call.member
                != (MemberRef {
                    owner: call_owner,
                    name: call_name,
                    descriptor: call_descriptor,
                })
            || call.receiver.and_then(|v| summary.values.get(v.0 as usize))
                != Some(&binary::Value::Receiver)
        {
            return Err(Error::DefaultBody);
        }
        let unit = unit_member();
        let mut static_read_count = 0;
        let mut static_reads_are_unit = true;
        for value in &summary.values {
            if let binary::Value::StaticField(member) = value {
                static_read_count += 1;
                static_reads_are_unit &= *member == unit;
            }
        }
        match direction {
            Direction::GenericToVoid if static_read_count != 0 => return Err(Error::DefaultBody),
            Direction::VoidToGeneric => {
                if static_read_count != 1
                    || !static_reads_are_unit
                    || summary
                        .returned
                        .and_then(|v| summary.values.get(v.0 as usize))
                        != Some(&binary::Value::StaticField(unit))
                {
                    return Err(Error::DefaultBody);
                }
            }
            _ => (),
        }
        Ok(Self {
            direction,
            class: class.identity,
            code_sha256: Sha256::digest(code).into(),
        })
    }
    pub fn direction(&self) -> Direction {
        self.direction
    }
    pub fn class_identity(&self) -> ClassIdentity {
        self.class
    }
    pub fn code_sha256(&self) -> [u8; 32] {
        self.code_sha256
    }
    pub fn method(&self) -> MemberRef<'static> {
        match self.direction {
            Direction::GenericToVoid => MemberRef {
                owner: FUNCTION0,
                name: "apply$mcV$sp",
                descriptor: VOID_DESCRIPTOR,
            },
            Direction::VoidToGeneric => MemberRef {
                owner: VOID_FUNCTION0,
                name: "apply",
                descriptor: GENERIC_DESCRIPTOR,
            },
        }
    }
    /// The consumer MUST compose this static read and owner initialization via
    /// the real default-method capsule; an unavailable provider stays TOP.
    pub fn required_static_read(&self) -> Option<MemberRef<'static>> {
        (self.direction == Direction::VoidToGeneric).then_some(unit_member())
    }

    /// Validates the exact factory's generated method set, not arbitrary
    /// Function0 values or an interface name. No new class parse or byte owner.
    pub fn creation<'a>(
        &self,
        standard_factory: &Java21StandardLambdaMetafactory,
        creator: &BoundClass<'a>,
        method_name: &'a str,
        method_descriptor: &'a str,
        pc: u32,
        requested: MemberRef<'_>,
        validator: &mut binary::diagnostic::CodeValidator,
        limits: binary::Limits,
    ) -> Result<BridgeProof<'a>> {
        if creator.identity.authority != self.class.authority
            || creator.identity.authority != standard_factory.class.authority
        {
            return Err(Error::ProviderBinding);
        }
        let (interface, sam_name, sam_descriptor) = match self.direction {
            Direction::GenericToVoid => (FUNCTION0, "apply", GENERIC_DESCRIPTOR),
            Direction::VoidToGeneric => (VOID_FUNCTION0, "apply$mcV$sp", VOID_DESCRIPTOR),
        };
        let expected_request = match self.direction {
            Direction::GenericToVoid => MemberRef {
                owner: FUNCTION0,
                name: "apply$mcV$sp",
                descriptor: VOID_DESCRIPTOR,
            },
            Direction::VoidToGeneric => MemberRef {
                owner: FUNCTION0,
                name: "apply",
                descriptor: GENERIC_DESCRIPTOR,
            },
        };
        if requested != expected_request {
            return Err(Error::Factory);
        }
        let method = creator
            .parsed
            .method(method_name, Some(method_descriptor))?;
        let code = method.code.ok_or(Error::Factory)?;
        validator.validate(&creator.parsed, method, limits)?;
        let at = usize::try_from(pc).map_err(|_| Error::Budget)?;
        let bytes = code
            .get(at..at.checked_add(5).ok_or(Error::Budget)?)
            .ok_or(Error::Factory)?;
        if !validator.instruction_start(at) || bytes[0] != 186 || bytes[3..] != [0, 0] {
            return Err(Error::Factory);
        }
        let dynamic = creator
            .parsed
            .invoke_dynamic(u16::from_be_bytes([bytes[1], bytes[2]]))?;
        if dynamic.name != sam_name
            || dynamic
                .descriptor
                .return_type
                .strip_prefix('L')
                .and_then(|s| s.strip_suffix(';'))
                != Some(interface)
        {
            return Err(Error::Factory);
        }
        if dynamic.descriptor.parameter_count > MAX_CAPTURES {
            return Err(Error::Budget);
        }
        let bootstrap = dynamic.bootstrap;
        standard_factory.validate_bootstrap(
            creator.identity.authority,
            bootstrap.method.member,
            bootstrap.method.kind,
        )?;
        let alternate = bootstrap.method.member.name == "altMetafactory"
            && bootstrap.method.member.descriptor == ALT_DESCRIPTOR;
        if bootstrap.method.kind != ReferenceKind::InvokeStatic
            || bootstrap.method.member.owner != LAMBDA_METAFACTORY
            || !(alternate
                || bootstrap.method.member.name == "metafactory"
                    && bootstrap.method.member.descriptor == META_DESCRIPTOR
                    && bootstrap.arguments.len() == 3)
        {
            return Err(Error::Factory);
        }
        let argument = |i| -> Result<BootstrapArgument<'a>> {
            Ok(creator
                .parsed
                .bootstrap_argument(bootstrap.arguments.get(i).ok_or(Error::Factory)?)?)
        };
        let sam = match argument(0)? {
            BootstrapArgument::MethodType(v) => v,
            _ => return Err(Error::Factory),
        };
        let implementation = match argument(1)? {
            BootstrapArgument::MethodHandle(v) => v,
            _ => return Err(Error::Factory),
        };
        let instantiated = match argument(2)? {
            BootstrapArgument::MethodType(v) => v,
            _ => return Err(Error::Factory),
        };
        if sam.text != sam_descriptor
            || instantiated.parameter_count != 0
            || implementation.kind != ReferenceKind::InvokeStatic
        {
            return Err(Error::UnsupportedAdaptation);
        }
        let target = binary::method_descriptor(implementation.member.descriptor)?;
        if !target.parameters().eq(dynamic.descriptor.parameters())
            || target.return_type != instantiated.return_type
            || match self.direction {
                Direction::GenericToVoid => {
                    !instantiated.return_type.starts_with('L')
                        && !instantiated.return_type.starts_with('[')
                }
                Direction::VoidToGeneric => instantiated.text != VOID_DESCRIPTOR,
            }
        {
            return Err(Error::UnsupportedAdaptation);
        }
        if alternate {
            let integer = |i| -> Result<i32> {
                match argument(i)? {
                    BootstrapArgument::Integer(v) => Ok(v),
                    _ => Err(Error::Factory),
                }
            };
            let flags = integer(3)?;
            if flags & !7 != 0 {
                return Err(Error::Factory);
            }
            let mut next = 4;
            if flags & 2 != 0 {
                // Additional marker interfaces can introduce conflicting or
                // more-specific defaults. None are admitted by this proof.
                if integer(next)? != 0 {
                    return Err(Error::Factory);
                }
                next += 1;
            }
            if flags & 4 != 0 {
                let count = usize::try_from(integer(next)?).map_err(|_| Error::Factory)?;
                next += 1;
                if count > 64 || count > bootstrap.arguments.len().saturating_sub(next) {
                    return Err(Error::Budget);
                }
                for i in next..next + count {
                    let bridge = match argument(i)? {
                        BootstrapArgument::MethodType(v) => v,
                        _ => return Err(Error::Factory),
                    };
                    if bridge.text != sam.text && bridge.text != instantiated.text {
                        return Err(Error::UnsupportedAdaptation);
                    }
                    // Every generated bridge has dynamic.name, so none can
                    // override the DIFFERENT requested default-method name.
                }
                next += count;
            }
            if next != bootstrap.arguments.len() {
                return Err(Error::Factory);
            }
        }
        let mut generated = Sha256::new();
        generated.update(b"selector-native-generated-function0-method-set/v1\0");
        generated.update(standard_factory.binding_sha256);
        generated.update(creator.identity.authority.to_le_bytes());
        generated.update(creator.identity.provider.to_le_bytes());
        generated.update(creator.identity.binding_sha256);
        generated.update(creator.identity.class_sha256);
        generated.update(<[u8; 32]>::from(Sha256::digest(code)));
        generated.update(pc.to_le_bytes());
        generated.update((bootstrap.arguments.len() as u32).to_le_bytes());
        for argument in bootstrap.arguments.iter() {
            generated.update(argument.to_le_bytes());
        }
        for text in [
            interface,
            sam_name,
            sam_descriptor,
            instantiated.text,
            bootstrap.method.member.owner,
            bootstrap.method.member.name,
            bootstrap.method.member.descriptor,
        ] {
            generated.update((text.len() as u64).to_le_bytes());
            generated.update(text.as_bytes());
        }
        let generated_method_set_sha256: [u8; 32] = generated.finalize().into();
        let mut hasher = Sha256::new();
        hasher.update(b"selector-native-function0-default-bridge/v1\0");
        hasher.update(transport_policy_sha256());
        hasher.update(standard_factory.binding_sha256);
        hasher.update(generated_method_set_sha256);
        for binding in [self.class, creator.identity] {
            hasher.update(binding.authority.to_le_bytes());
            hasher.update(binding.provider.to_le_bytes());
            hasher.update(binding.binding_sha256);
            hasher.update(binding.class_sha256);
        }
        hasher.update(self.code_sha256);
        hasher.update(<[u8; 32]>::from(Sha256::digest(code)));
        hasher.update(pc.to_le_bytes());
        for text in [
            creator.parsed.name,
            method_name,
            method_descriptor,
            interface,
            sam_name,
            sam_descriptor,
            requested.owner,
            requested.name,
            requested.descriptor,
            implementation.member.owner,
            implementation.member.name,
            implementation.member.descriptor,
        ] {
            hasher.update((text.len() as u64).to_le_bytes());
            hasher.update(text.as_bytes());
        }
        Ok(BridgeProof {
            binding_sha256: hasher.finalize().into(),
            direction: self.direction,
            generated_method_set_sha256,
            default_code_sha256: self.code_sha256,
            standard_factory_sha256: standard_factory.binding_sha256,
            creator: creator.identity,
            default_class: self.class,
            pc,
            creator_method: MemberRef {
                owner: creator.parsed.name,
                name: method_name,
                descriptor: method_descriptor,
            },
            implementation: implementation.member,
            captures: dynamic.descriptor.parameter_count as u16,
        })
    }
}
fn unit_member() -> MemberRef<'static> {
    MemberRef {
        owner: "scala/runtime/BoxedUnit",
        name: "UNIT",
        descriptor: "Lscala/runtime/BoxedUnit;",
    }
}

/// A compatibility entry may be issued only for this factory + requested SAM.
/// On activation the planner must select the ACTUAL default-method capsule,
/// bind its receiver_value to the SAME creation payload, and bind ZERO creator
/// captures to it. The bridge's internal original-SAM call performs ordinary
/// creation activation and restores lexical receiver/captures there.
pub struct BridgeProof<'a> {
    binding_sha256: [u8; 32],
    direction: Direction,
    generated_method_set_sha256: [u8; 32],
    default_code_sha256: [u8; 32],
    standard_factory_sha256: [u8; 32],
    creator: ClassIdentity,
    default_class: ClassIdentity,
    pc: u32,
    creator_method: MemberRef<'a>,
    implementation: MemberRef<'a>,
    captures: u16,
}
impl BridgeProof<'_> {
    pub fn binding_sha256(&self) -> [u8; 32] {
        self.binding_sha256
    }
    /// Hash of the reviewed standard-BSM method-set construction inputs, not
    /// a claim to have observed or hashed a JVM-generated hidden class.
    pub fn generated_method_set_sha256(&self) -> [u8; 32] {
        self.generated_method_set_sha256
    }
    pub fn default_code_sha256(&self) -> [u8; 32] {
        self.default_code_sha256
    }
    pub fn standard_factory_sha256(&self) -> [u8; 32] {
        self.standard_factory_sha256
    }
    pub fn direction(&self) -> Direction {
        self.direction
    }
    pub fn creator(&self) -> ClassIdentity {
        self.creator
    }
    pub fn default_class(&self) -> ClassIdentity {
        self.default_class
    }
    pub fn creation_pc(&self) -> u32 {
        self.pc
    }
    pub fn creator_method(&self) -> MemberRef<'_> {
        self.creator_method
    }
    pub fn implementation(&self) -> MemberRef<'_> {
        self.implementation
    }
    pub fn captures(&self) -> u16 {
        self.captures
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use selector_effects as effects;
    use std::sync::Arc;

    const GENERIC: &[u8] =
        include_bytes!("../../../fixtures/framework-transport/scala/Function0.class");
    const SPECIALIZED: &[u8] = include_bytes!(
        "../../../fixtures/framework-transport/scala/runtime/java8/JFunction0$mcV$sp.class"
    );
    const UNIT: &[u8] =
        include_bytes!("../../../fixtures/framework-transport/scala/runtime/BoxedUnit.class");
    const WORD: &[u8] = include_bytes!(
        "../../../fixtures/registration-smoke/bytecode/registrationcase/WordSuite.class"
    );
    const DORMANT: &[u8] = include_bytes!(
        "../../../fixtures/anonymous-construction/classes/anonymouscase/Dormant.class"
    );
    const METAFACTORY: &[u8] = include_bytes!(
        "../../../fixtures/framework-transport/java/lang/invoke/LambdaMetafactory.class"
    );

    // This normalized provider receipt tests transport binding, not physical
    // classpath-prefix admission. The production VerifiedProvider owns that.
    fn provided(bytes: &[u8]) -> ProvidedClass {
        ProvidedClass {
            bytes: Arc::from(bytes),
            class_sha256: Sha256::digest(bytes).into(),
            authority: 0,
            provider: 1,
            binding_sha256: [9; 32],
        }
    }
    fn bound<'a>(input: &'a ProvidedClass, owner: &str) -> BoundClass<'a> {
        BoundClass::admit(input, 0, owner, binary::Limits::default()).unwrap()
    }
    fn standard() -> Java21StandardLambdaMetafactory {
        // Explicit normalized provider+platform receipt for unit tests only.
        // The production issuer cannot take these hashes: it must obtain the
        // receipt from VerifiedProvider's private declared-java.base hook.
        Java21StandardLambdaMetafactory::verified_class(
            &provided(METAFACTORY),
            [11; 32],
            binary::Limits::default(),
        )
        .unwrap()
    }
    fn request(direction: Direction) -> MemberRef<'static> {
        match direction {
            Direction::GenericToVoid => MemberRef {
                owner: FUNCTION0,
                name: "apply$mcV$sp",
                descriptor: VOID_DESCRIPTOR,
            },
            Direction::VoidToGeneric => MemberRef {
                owner: FUNCTION0,
                name: "apply",
                descriptor: GENERIC_DESCRIPTOR,
            },
        }
    }
    fn proof<'a>(default: &DefaultBridge, creator: &BoundClass<'a>, pc: u32) -> BridgeProof<'a> {
        default
            .creation(
                &standard(),
                creator,
                "<init>",
                "()V",
                pc,
                request(default.direction()),
                &mut binary::diagnostic::CodeValidator::default(),
                binary::Limits::default(),
            )
            .unwrap()
    }

    #[test]
    fn exact_genuine_defaults_retain_real_callback_and_boxed_unit_dependencies() {
        for (bytes, owner, direction, code_len) in [
            (GENERIC, FUNCTION0, Direction::GenericToVoid, 8),
            (SPECIALIZED, VOID_FUNCTION0, Direction::VoidToGeneric, 10),
        ] {
            let input = provided(bytes);
            let class = bound(&input, owner);
            let default = DefaultBridge::verify(&class, binary::Limits::default()).unwrap();
            assert_eq!(default.direction(), direction);
            assert_eq!(default.class_identity().class_sha256, input.class_sha256);
            let member = default.method();
            let method = class
                .parsed()
                .method(member.name, Some(member.descriptor))
                .unwrap();
            assert_eq!(method.code.unwrap().len(), code_len);
            assert_eq!(
                default.code_sha256(),
                <[u8; 32]>::from(Sha256::digest(method.code.unwrap()))
            );
            let summary = binary::summarize(class.parsed(), method, binary::Limits::default());
            assert_eq!(summary.calls.len(), 1);
            assert_eq!(summary.calls[0].offset, 1);
            assert_eq!(
                default.required_static_read(),
                (direction == Direction::VoidToGeneric).then_some(unit_member())
            );
        }
        // The inverse bridge's read is backed by actual class bytes and an
        // executable initializer, not an invented constant Unit value.
        let input = provided(UNIT);
        let unit = bound(&input, "scala/runtime/BoxedUnit");
        let init = unit.parsed().method("<clinit>", Some("()V")).unwrap();
        let summary = binary::summarize(unit.parsed(), init, binary::Limits::default());
        assert!(
            summary
                .field_writes
                .iter()
                .any(|write| write.member == unit_member())
        );
    }

    #[test]
    fn genuine_compiler_factories_prove_both_directions_and_lexical_capture_ownership() {
        for (defaults, owner, factory, factory_owner, pc, captures, target) in [
            (
                GENERIC,
                FUNCTION0,
                DORMANT,
                "anonymouscase/Dormant",
                5,
                0,
                "$anonfun$later$1",
            ),
            (
                SPECIALIZED,
                VOID_FUNCTION0,
                WORD,
                "registrationcase/WordSuite",
                16,
                1,
                "$anonfun$new$11",
            ),
        ] {
            let default_input = provided(defaults);
            let default_class = bound(&default_input, owner);
            let default = DefaultBridge::verify(&default_class, binary::Limits::default()).unwrap();
            let factory_input = provided(factory);
            let factory_class = bound(&factory_input, factory_owner);
            let proved = proof(&default, &factory_class, pc);
            assert_eq!(proved.captures(), captures);
            assert_eq!(proved.implementation().name, target);
            assert_eq!(proved.creation_pc(), pc);
            assert_eq!(proved.default_code_sha256(), default.code_sha256());
            assert_ne!(proved.binding_sha256(), [0; 32]);
            assert_ne!(proved.generated_method_set_sha256(), [0; 32]);
            assert_ne!(proved.binding_sha256(), transport_policy_sha256());
        }
    }

    #[test]
    fn genuine_factory_proof_activates_actual_default_then_original_callable_payload() {
        use effects::{
            CallKind, CallRow, CallTarget, CallableBridge, CallableCreation, CapsuleData, Capsules,
            InvocationRoute, MethodId, MethodRow, NONE, Origin, Range, RefBounds, StorageKind,
            StorageRef, SubjectKind, SubjectRef, TopMask, ValueRef,
        };
        for (defaults, owner, factory, factory_owner, pc) in [
            (GENERIC, FUNCTION0, DORMANT, "anonymouscase/Dormant", 5),
            (
                SPECIALIZED,
                VOID_FUNCTION0,
                WORD,
                "registrationcase/WordSuite",
                16,
            ),
        ] {
            let default_input = provided(defaults);
            let default_class = bound(&default_input, owner);
            let default = DefaultBridge::verify(&default_class, binary::Limits::default()).unwrap();
            let factory_input = provided(factory);
            let factory_class = bound(&factory_input, factory_owner);
            let proved = proof(&default, &factory_class, pc);
            // Normalized callable-adapter control derived from the genuine
            // factory and verified default. No method is granted closed effects.
            let mut factory_row = MethodRow::unknown(
                SubjectRef {
                    kind: SubjectKind::ForeignMethod,
                    index: 0,
                },
                0,
                0,
                0,
                0,
            );
            factory_row.locals = 2;
            factory_row.creations = Range { start: 0, len: 2 };
            let implementation = MethodRow::unknown(
                SubjectRef {
                    kind: SubjectKind::CallableAdapter,
                    index: 0,
                },
                0,
                0,
                proved.captures() as u32,
                0,
            );
            let mut bridge = MethodRow::unknown(
                SubjectRef {
                    kind: SubjectKind::ForeignMethod,
                    index: 1,
                },
                0,
                0,
                0,
                0,
            );
            bridge.calls = Range { start: 0, len: 1 };
            let mut data = CapsuleData {
                methods: vec![factory_row, implementation, bridge],
                sam_arities: vec![0, 0],
                calls: vec![CallRow {
                    site: 1,
                    target: CallTarget::Callable {
                        value: ValueRef::RECEIVER,
                        sam: 0,
                    },
                    kind: CallKind::Callback,
                    receiver: Origin::RECEIVER,
                    receiver_value: ValueRef::RECEIVER,
                    result: NONE,
                    arguments: Range::EMPTY,
                    captures: Range::EMPTY,
                }],
                callable_bridges: vec![CallableBridge {
                    creation: 0,
                    sam: 1,
                    implementation: MethodId(2),
                    proof: 0,
                }],
                ..Default::default()
            };
            for _ in 0..proved.captures() {
                data.origins.push(Origin::RECEIVER);
                data.callable_values.push(ValueRef::RECEIVER);
            }
            let creation = CallableCreation {
                site: 0,
                destination: 0,
                implementation: MethodId(1),
                sam: 0,
                receiver: Origin::RECEIVER,
                receiver_value: ValueRef::RECEIVER,
                captures: Range {
                    start: 0,
                    len: proved.captures() as u32,
                },
            };
            data.creations = vec![
                creation,
                CallableCreation {
                    destination: 1,
                    ..creation
                },
            ];
            if default.required_static_read().is_some() {
                data.methods[2].reads = Range { start: 0, len: 1 };
                data.methods[2].initializes = Range { start: 0, len: 1 };
                data.reads.push(StorageRef {
                    kind: StorageKind::StaticField,
                    member: 0,
                    base: Origin::ANY,
                });
                data.initializes.push(MethodId(3));
                data.methods.push(MethodRow::unknown(
                    SubjectRef {
                        kind: SubjectKind::RuntimePhase,
                        index: 0,
                    },
                    0,
                    0,
                    0,
                    0,
                ));
            }
            let program = Capsules::new(
                data,
                RefBounds {
                    foreign_methods: 2,
                    authorities: 1,
                    members: 1,
                    sites: 2,
                    sams: 2,
                    adapters: 1,
                    bridge_proofs: 1,
                    phases: 1,
                    ..Default::default()
                },
                effects::Limits::default(),
            )
            .unwrap();
            let routed = program.resolve_callable_invocation(0, 1).unwrap().unwrap();
            assert_eq!(routed.route, InvocationRoute::DefaultBridge);
            assert_eq!(routed.creation, 0); // same payload, never a new creator
            assert_eq!(routed.implementation, MethodId(2));
            let body = program.view(routed.implementation).unwrap();
            assert_eq!(body.row.captures, 0);
            assert_eq!(body.row.top, TopMask::ALL);
            assert_eq!(body.calls[0].receiver_value, ValueRef::RECEIVER);
            let CallTarget::Callable { sam, .. } = body.calls[0].target else {
                panic!("real default must invoke its receiver");
            };
            let inner = program
                .resolve_callable_invocation(routed.creation, sam)
                .unwrap()
                .unwrap();
            assert_eq!(inner.route, InvocationRoute::Implementation);
            assert_eq!(inner.implementation, MethodId(1));
            assert_eq!(
                program.view(inner.implementation).unwrap().row.captures,
                proved.captures() as u32
            );
            assert_eq!(program.resolve_callable_invocation(1, 1).unwrap(), None); // custom/unproved creation
            if default.required_static_read().is_some() {
                assert_eq!(body.reads.len(), 1);
                assert_eq!(body.initializes, &[MethodId(3)]);
                assert_eq!(program.view(MethodId(3)).unwrap().row.top, TopMask::ALL);
            }
        }
    }

    #[test]
    fn inconsistent_provider_context_hash_and_unadmitted_defaults_are_rejected() {
        let mut input = provided(GENERIC);
        input.class_sha256[0] ^= 1;
        assert!(matches!(
            BoundClass::admit(&input, 0, FUNCTION0, binary::Limits::default()),
            Err(Error::ProviderBinding)
        ));
        input = provided(GENERIC);
        input.binding_sha256 = [0; 32];
        assert!(matches!(
            BoundClass::admit(&input, 0, FUNCTION0, binary::Limits::default()),
            Err(Error::ProviderBinding)
        ));
        input = provided(GENERIC);
        assert!(matches!(
            BoundClass::admit(&input, 1, FUNCTION0, binary::Limits::default()),
            Err(Error::ProviderBinding)
        ));
        assert!(matches!(
            BoundClass::admit(&input, 0, VOID_FUNCTION0, binary::Limits::default()),
            Err(Error::ProviderBinding)
        ));
        let default_class = bound(&input, FUNCTION0);
        let default = DefaultBridge::verify(&default_class, binary::Limits::default()).unwrap();
        let mut factory_input = provided(DORMANT);
        factory_input.authority = 1;
        let factory_class = BoundClass::admit(
            &factory_input,
            1,
            "anonymouscase/Dormant",
            binary::Limits::default(),
        )
        .unwrap();
        assert!(matches!(
            default.creation(
                &standard(),
                &factory_class,
                "<init>",
                "()V",
                5,
                request(default.direction()),
                &mut Default::default(),
                binary::Limits::default()
            ),
            Err(Error::ProviderBinding)
        ));
    }

    #[test]
    fn synthetic_default_mutation_even_with_resealed_bytes_cannot_receive_reviewed_authority() {
        let mut bytes = GENERIC.to_vec();
        let original = provided(GENERIC);
        let parsed = bound(&original, FUNCTION0);
        let code = parsed
            .parsed()
            .method("apply$mcV$sp", Some(VOID_DESCRIPTOR))
            .unwrap()
            .code
            .unwrap();
        let offset = code.as_ptr() as usize - original.bytes.as_ptr() as usize;
        bytes[offset + 6] = 0; // synthetic pop→nop, not compiler output
        let changed = provided(&bytes);
        let class = bound(&changed, FUNCTION0);
        assert!(matches!(
            DefaultBridge::verify(&class, binary::Limits::default()),
            Err(Error::ReviewedClass)
        ));
    }

    #[test]
    fn wrong_sam_misaligned_factory_and_synthetic_indy_mutations_never_issue_proof() {
        let default_input = provided(SPECIALIZED);
        let default_class = bound(&default_input, VOID_FUNCTION0);
        let default = DefaultBridge::verify(&default_class, binary::Limits::default()).unwrap();
        let factory_input = provided(WORD);
        let factory = bound(&factory_input, "registrationcase/WordSuite");
        for pc in [0, 17, u32::MAX] {
            assert!(
                default
                    .creation(
                        &standard(),
                        &factory,
                        "<init>",
                        "()V",
                        pc,
                        request(default.direction()),
                        &mut Default::default(),
                        binary::Limits::default()
                    )
                    .is_err()
            );
        }
        for requested in [
            MemberRef {
                owner: "custom/Function0",
                ..request(default.direction())
            },
            MemberRef {
                name: "apply$mcV$sp",
                ..request(default.direction())
            },
            MemberRef {
                descriptor: "()I",
                ..request(default.direction())
            },
        ] {
            assert!(
                default
                    .creation(
                        &standard(),
                        &factory,
                        "<init>",
                        "()V",
                        16,
                        requested,
                        &mut Default::default(),
                        binary::Limits::default()
                    )
                    .is_err()
            );
        }
        let code = factory
            .parsed()
            .method("<init>", Some("()V"))
            .unwrap()
            .code
            .unwrap();
        let code_at = code.as_ptr() as usize - factory_input.bytes.as_ptr() as usize;
        let mut bytes = WORD.to_vec();
        bytes[code_at + 16 + 3] = 1; // synthetic reserved invokedynamic byte
        let changed = provided(&bytes);
        let changed_class = bound(&changed, "registrationcase/WordSuite");
        assert!(
            default
                .creation(
                    &standard(),
                    &changed_class,
                    "<init>",
                    "()V",
                    16,
                    request(default.direction()),
                    &mut Default::default(),
                    binary::Limits::default()
                )
                .is_err()
        );
        let tiny = binary::Limits {
            max_code_bytes: 0,
            ..Default::default()
        };
        assert!(
            default
                .creation(
                    &standard(),
                    &factory,
                    "<init>",
                    "()V",
                    16,
                    request(default.direction()),
                    &mut Default::default(),
                    tiny
                )
                .is_err()
        );
    }

    #[test]
    fn creation_proof_seals_provider_binding_in_addition_to_class_and_default_code() {
        let default_input = provided(SPECIALIZED);
        let default_class = bound(&default_input, VOID_FUNCTION0);
        let default = DefaultBridge::verify(&default_class, binary::Limits::default()).unwrap();
        let first = provided(WORD);
        let first_class = bound(&first, "registrationcase/WordSuite");
        let first_proof = proof(&default, &first_class, 16);
        let mut second = provided(WORD);
        second.provider += 1;
        second.binding_sha256[0] ^= 1;
        let second_class = bound(&second, "registrationcase/WordSuite");
        let second_proof = proof(&default, &second_class, 16);
        assert_eq!(
            first_proof.default_code_sha256(),
            second_proof.default_code_sha256()
        );
        assert_ne!(
            first_proof.generated_method_set_sha256(),
            second_proof.generated_method_set_sha256()
        );
        assert_ne!(first_proof.binding_sha256(), second_proof.binding_sha256());
    }

    #[test]
    fn standard_factory_token_is_a_separate_method_set_axiom_with_pinned_java21_code() {
        let standard = standard();
        assert_eq!(
            standard.class_identity().class_sha256,
            LAMBDA_METAFACTORY_HASH
        );
        assert_ne!(standard.platform_sha256(), [0; 32]);
        assert!(
            standard
                .method_code_sha256()
                .iter()
                .all(|code| *code != [0; 32])
        );
        let producer = Java21StandardLambdaMetafactory::producer_sha256();
        assert_ne!(producer, crate::RuntimeAxiom::producer());
        assert!(
            Java21StandardLambdaMetafactory::validate_requested_contract(
                STANDARD_FACTORY_CONTRACT,
                producer
            )
            .is_ok()
        );
        for (contract, producer) in [
            (crate::axiom::CONTRACT, producer),
            (STANDARD_FACTORY_CONTRACT, [0; 32]),
            (STANDARD_FACTORY_CONTRACT, crate::RuntimeAxiom::producer()),
        ] {
            assert!(
                Java21StandardLambdaMetafactory::validate_requested_contract(contract, producer)
                    .is_err()
            );
        }
        let member = MemberRef {
            owner: LAMBDA_METAFACTORY,
            name: "metafactory",
            descriptor: META_DESCRIPTOR,
        };
        assert_eq!(
            standard
                .validate_bootstrap(0, member, ReferenceKind::InvokeStatic)
                .unwrap(),
            standard.class_identity()
        );
        for (authority, member, kind) in [
            (1, member, ReferenceKind::InvokeStatic),
            (
                0,
                MemberRef {
                    owner: "custom/LambdaMetafactory",
                    ..member
                },
                ReferenceKind::InvokeStatic,
            ),
            (
                0,
                MemberRef {
                    descriptor: ALT_DESCRIPTOR,
                    ..member
                },
                ReferenceKind::InvokeStatic,
            ),
            (0, member, ReferenceKind::InvokeVirtual),
        ] {
            assert!(
                standard
                    .validate_bootstrap(authority, member, kind)
                    .is_err()
            );
        }
    }

    #[test]
    fn standard_factory_rejects_missing_platform_wrong_jdk_class_and_synthetic_class_mutation() {
        assert!(
            Java21StandardLambdaMetafactory::verified_class(
                &provided(METAFACTORY),
                [0; 32],
                binary::Limits::default()
            )
            .is_err()
        );
        assert!(
            Java21StandardLambdaMetafactory::verified_class(
                &provided(GENERIC),
                [11; 32],
                binary::Limits::default()
            )
            .is_err()
        );
        let mut bytes = METAFACTORY.to_vec();
        bytes[7] = 61; // synthetic Java17 header; freshly rehashed, not genuine output
        assert!(
            Java21StandardLambdaMetafactory::verified_class(
                &provided(&bytes),
                [11; 32],
                binary::Limits::default()
            )
            .is_err()
        );
        let tiny = binary::Limits {
            max_code_bytes: 0,
            ..Default::default()
        };
        assert!(
            Java21StandardLambdaMetafactory::verified_class(&provided(METAFACTORY), [11; 32], tiny)
                .is_err()
        );
    }

    #[test]
    fn synthetic_wrong_bootstrap_owner_cannot_receive_a_creation_default_bridge() {
        let mut bytes = WORD.to_vec();
        let needle = b"java/lang/invoke/LambdaMetafactory";
        let at = bytes
            .windows(needle.len())
            .position(|window| window == needle)
            .unwrap();
        bytes[at + needle.len() - 1] = b'x'; // valid same-length CP owner mutation
        let input = provided(&bytes);
        let factory = bound(&input, "registrationcase/WordSuite");
        let default_input = provided(SPECIALIZED);
        let default_class = bound(&default_input, VOID_FUNCTION0);
        let default = DefaultBridge::verify(&default_class, binary::Limits::default()).unwrap();
        assert!(
            default
                .creation(
                    &standard(),
                    &factory,
                    "<init>",
                    "()V",
                    16,
                    request(default.direction()),
                    &mut Default::default(),
                    binary::Limits::default()
                )
                .is_err()
        );
    }
}
