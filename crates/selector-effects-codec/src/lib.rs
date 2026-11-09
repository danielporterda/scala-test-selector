//! Experimental flat effect storage. Structural validity is not proof authority.
//! A caller supplies the exact current world binding. Every scalar is decoded
//! little-endian without repr casts; verified rows borrow one artifact owner.
//! Effects artifacts have a distinct kind and strict callable-aware schema.
//! Stored authority flags are structural claims, never semantic certificates.
mod canonicalize;
mod keys;
mod materialize;
mod records;
mod validation;
mod wire;
pub use canonicalize::{OriginRemap, canonicalize_origins};
pub use keys::*;
pub use materialize::Materialized;
use selector_artifacts::{Artifact, ArtifactKind, StreamingSection};
pub use selector_effects;
use selector_effects::*;
use std::fmt;
use std::io::{self, Write};
use std::path::Path;

pub const NONE: u32 = u32::MAX;
const MAGIC: &[u8; 8] = b"SEFXP003";
const VERSION: u32 = 3;
const META_BYTES: usize = 336;
const SECTIONS: usize = 33;
const WIDTHS: [usize; SECTIONS] = [
    336, 1, 8, 36, 48, 64, 68, 60, 72, 8, 48, 16, 128, 60, 8, 8, 16, 16, 16, 4, 4, 12, 8, 20, 8, 4,
    40, 16, 60, 124, 16, 160, 12,
];

#[derive(Debug)]
pub enum Error {
    Artifact(selector_artifacts::Error),
    Invalid(&'static str),
    Limit(&'static str),
}
impl From<selector_artifacts::Error> for Error {
    fn from(e: selector_artifacts::Error) -> Self {
        Self::Artifact(e)
    }
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Artifact(e) => e.fmt(f),
            Self::Invalid(s) => write!(f, "invalid effect capsule: {s}"),
            Self::Limit(s) => write!(f, "effect capsule limit: {s}"),
        }
    }
}
impl std::error::Error for Error {}

#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub max_bytes: u64,
    pub max_records: u32,
    pub max_text_bytes: u32,
    pub effects: selector_effects::Limits,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            max_bytes: 256 << 20,
            max_records: 2_000_000,
            max_text_bytes: 64 << 20,
            effects: selector_effects::Limits::default(),
        }
    }
}

pub struct KeyTables<'a> {
    pub text: &'a [u8],
    pub strings: &'a [TextRange],
    pub contexts: &'a [ContextKey],
    pub providers: &'a [ProviderKey],
    pub foreign_methods: &'a [ForeignMethod],
    pub members: &'a [MemberKey],
    pub classes: &'a [ClassKey],
    pub authorities: &'a [AuthorityKey],
    pub exceptions: &'a [ExceptionKey],
    pub externals: &'a [ExternalKey],
    pub sites: &'a [SiteKey],
    pub sams: &'a [SamKey],
    pub adapters: &'a [CallableAdapterKey],
    pub bridge_proofs: &'a [CallableBridgeProofKey],
    pub phases: &'a [PhaseKey],
}
/// Complete owned producers may be validated and streamed without serializing
/// a second whole snapshot in memory. The scalar getters must stay immutable.
pub struct Snapshot<'a, T: TableView> {
    pub binding: Binding,
    pub keys: KeyTables<'a>,
    pub effects: &'a T,
}

pub trait ProvenanceView {
    fn text_count(&self) -> usize;
    fn text(&self, index: u32) -> Option<&str>;
    fn context_count(&self) -> usize;
    fn context(&self, index: usize) -> Option<ContextKey>;
    fn provider_count(&self) -> usize;
    fn provider(&self, index: usize) -> Option<ProviderKey>;
    fn foreign_method_count(&self) -> usize;
    fn foreign_method(&self, index: usize) -> Option<ForeignMethod>;
    fn member_count(&self) -> usize;
    fn member(&self, index: usize) -> Option<MemberKey>;
    fn class_count(&self) -> usize;
    fn class(&self, index: usize) -> Option<ClassKey>;
    fn authority_count(&self) -> usize;
    fn authority(&self, index: usize) -> Option<AuthorityKey>;
    fn exception_key_count(&self) -> usize;
    fn exception_key(&self, index: usize) -> Option<ExceptionKey>;
    fn external_key_count(&self) -> usize;
    fn external_key(&self, index: usize) -> Option<ExternalKey>;
    fn site_count(&self) -> usize;
    fn site(&self, index: usize) -> Option<SiteKey>;
    fn sam_key_count(&self) -> usize;
    fn sam_key(&self, index: usize) -> Option<SamKey>;
    fn adapter_count(&self) -> usize;
    fn adapter(&self, index: usize) -> Option<CallableAdapterKey>;
    fn bridge_proof_count(&self) -> usize;
    fn bridge_proof(&self, index: usize) -> Option<CallableBridgeProofKey>;
    fn phase_key_count(&self) -> usize;
    fn phase_key(&self, index: usize) -> Option<PhaseKey>;
}
impl ProvenanceView for KeyTables<'_> {
    fn text_count(&self) -> usize {
        self.strings.len()
    }
    fn text(&self, index: u32) -> Option<&str> {
        let r = self.strings.get(index as usize)?;
        let end = r.start.checked_add(r.len)?;
        std::str::from_utf8(self.text.get(r.start as usize..end as usize)?).ok()
    }
    fn context_count(&self) -> usize {
        self.contexts.len()
    }
    fn context(&self, index: usize) -> Option<ContextKey> {
        self.contexts.get(index).copied()
    }
    fn provider_count(&self) -> usize {
        self.providers.len()
    }
    fn provider(&self, index: usize) -> Option<ProviderKey> {
        self.providers.get(index).copied()
    }
    fn foreign_method_count(&self) -> usize {
        self.foreign_methods.len()
    }
    fn foreign_method(&self, index: usize) -> Option<ForeignMethod> {
        self.foreign_methods.get(index).copied()
    }
    fn member_count(&self) -> usize {
        self.members.len()
    }
    fn member(&self, index: usize) -> Option<MemberKey> {
        self.members.get(index).copied()
    }
    fn class_count(&self) -> usize {
        self.classes.len()
    }
    fn class(&self, index: usize) -> Option<ClassKey> {
        self.classes.get(index).copied()
    }
    fn authority_count(&self) -> usize {
        self.authorities.len()
    }
    fn authority(&self, index: usize) -> Option<AuthorityKey> {
        self.authorities.get(index).copied()
    }
    fn exception_key_count(&self) -> usize {
        self.exceptions.len()
    }
    fn exception_key(&self, index: usize) -> Option<ExceptionKey> {
        self.exceptions.get(index).copied()
    }
    fn external_key_count(&self) -> usize {
        self.externals.len()
    }
    fn external_key(&self, index: usize) -> Option<ExternalKey> {
        self.externals.get(index).copied()
    }
    fn site_count(&self) -> usize {
        self.sites.len()
    }
    fn site(&self, index: usize) -> Option<SiteKey> {
        self.sites.get(index).copied()
    }
    fn sam_key_count(&self) -> usize {
        self.sams.len()
    }
    fn sam_key(&self, index: usize) -> Option<SamKey> {
        self.sams.get(index).copied()
    }
    fn adapter_count(&self) -> usize {
        self.adapters.len()
    }
    fn adapter(&self, index: usize) -> Option<CallableAdapterKey> {
        self.adapters.get(index).copied()
    }
    fn bridge_proof_count(&self) -> usize {
        self.bridge_proofs.len()
    }
    fn bridge_proof(&self, index: usize) -> Option<CallableBridgeProofKey> {
        self.bridge_proofs.get(index).copied()
    }
    fn phase_key_count(&self) -> usize {
        self.phases.len()
    }
    fn phase_key(&self, index: usize) -> Option<PhaseKey> {
        self.phases.get(index).copied()
    }
}

/// One bounded byte owner. Getters below allocate no row, string, vector or map.
pub struct VerifiedCapsules {
    artifact: Artifact,
    binding: Binding,
    bounds: RefBounds,
    counts: [usize; SECTIONS],
}
impl VerifiedCapsules {
    pub fn binding(&self) -> Binding {
        self.binding
    }
    pub fn bounds(&self) -> RefBounds {
        self.bounds
    }
    pub fn identity(&self) -> Hash {
        Hash(self.artifact.identity())
    }
    pub fn byte_len(&self) -> usize {
        self.artifact.byte_len()
    }
    fn cursor(&self, section: u32, index: usize) -> Option<wire::Cursor<'_>> {
        if index >= self.counts[section as usize - 1] {
            return None;
        }
        wire::at(
            &self.artifact,
            section,
            u32::try_from(index).ok()?,
            WIDTHS[section as usize - 1],
        )
        .ok()
    }
}
impl ProvenanceView for VerifiedCapsules {
    fn text_count(&self) -> usize {
        self.counts[2]
    }
    fn text(&self, index: u32) -> Option<&str> {
        let r = records::decode_text_range(self.cursor(3, index as usize)?)?;
        let end = r.start.checked_add(r.len)?;
        std::str::from_utf8(
            self.artifact
                .section(2)
                .ok()?
                .get(r.start as usize..end as usize)?,
        )
        .ok()
    }
    fn context_count(&self) -> usize {
        self.counts[3]
    }
    fn context(&self, index: usize) -> Option<ContextKey> {
        records::decode_context(self.cursor(4, index)?)
    }
    fn provider_count(&self) -> usize {
        self.counts[4]
    }
    fn provider(&self, index: usize) -> Option<ProviderKey> {
        records::decode_provider(self.cursor(5, index)?)
    }
    fn foreign_method_count(&self) -> usize {
        self.counts[5]
    }
    fn foreign_method(&self, index: usize) -> Option<ForeignMethod> {
        records::decode_foreign_method(self.cursor(6, index)?)
    }
    fn member_count(&self) -> usize {
        self.counts[6]
    }
    fn member(&self, index: usize) -> Option<MemberKey> {
        records::decode_member(self.cursor(7, index)?)
    }
    fn class_count(&self) -> usize {
        self.counts[7]
    }
    fn class(&self, index: usize) -> Option<ClassKey> {
        records::decode_class(self.cursor(8, index)?)
    }
    fn authority_count(&self) -> usize {
        self.counts[8]
    }
    fn authority(&self, index: usize) -> Option<AuthorityKey> {
        records::decode_authority(self.cursor(9, index)?)
    }
    fn exception_key_count(&self) -> usize {
        self.counts[9]
    }
    fn exception_key(&self, index: usize) -> Option<ExceptionKey> {
        records::decode_exception_key(self.cursor(10, index)?)
    }
    fn external_key_count(&self) -> usize {
        self.counts[10]
    }
    fn external_key(&self, index: usize) -> Option<ExternalKey> {
        records::decode_external_key(self.cursor(11, index)?)
    }
    fn site_count(&self) -> usize {
        self.counts[11]
    }
    fn site(&self, index: usize) -> Option<SiteKey> {
        records::decode_site(self.cursor(12, index)?)
    }
    fn sam_key_count(&self) -> usize {
        self.counts[28]
    }
    fn sam_key(&self, index: usize) -> Option<SamKey> {
        records::decode_sam_key(self.cursor(29, index)?)
    }
    fn adapter_count(&self) -> usize {
        self.counts[29]
    }
    fn adapter(&self, index: usize) -> Option<CallableAdapterKey> {
        records::decode_adapter(self.cursor(30, index)?)
    }
    fn bridge_proof_count(&self) -> usize {
        self.counts[31]
    }
    fn bridge_proof(&self, index: usize) -> Option<CallableBridgeProofKey> {
        records::decode_bridge_proof(self.cursor(32, index)?)
    }
    fn phase_key_count(&self) -> usize {
        self.counts[32]
    }
    fn phase_key(&self, index: usize) -> Option<PhaseKey> {
        records::decode_phase(self.cursor(33, index)?)
    }
}
impl TableView for VerifiedCapsules {
    fn method_count(&self) -> usize {
        self.counts[12]
    }
    fn method(&self, index: usize) -> Option<MethodRow> {
        records::decode_method(self.cursor(13, index)?)
    }
    fn call_count(&self) -> usize {
        self.counts[13]
    }
    fn call(&self, index: usize) -> Option<CallRow> {
        records::decode_call(self.cursor(14, index)?)
    }
    fn origin_count(&self) -> usize {
        self.counts[14]
    }
    fn origin(&self, index: usize) -> Option<Origin> {
        records::decode_origin(self.cursor(15, index)?)
    }
    fn code_observation_count(&self) -> usize {
        self.counts[15]
    }
    fn code_observation(&self, index: usize) -> Option<CodeRef> {
        records::decode_code_observation(self.cursor(16, index)?)
    }
    fn read_count(&self) -> usize {
        self.counts[16]
    }
    fn read(&self, index: usize) -> Option<StorageRef> {
        records::decode_storage(self.cursor(17, index)?)
    }
    fn write_count(&self) -> usize {
        self.counts[17]
    }
    fn write(&self, index: usize) -> Option<StorageRef> {
        records::decode_storage(self.cursor(18, index)?)
    }
    fn escape_count(&self) -> usize {
        self.counts[18]
    }
    fn escape(&self, index: usize) -> Option<EscapeRef> {
        records::decode_escape(self.cursor(19, index)?)
    }
    fn initialize_count(&self) -> usize {
        self.counts[19]
    }
    fn initialize(&self, index: usize) -> Option<MethodId> {
        Some(MethodId(self.cursor(20, index)?.u32()))
    }
    fn throw_count(&self) -> usize {
        self.counts[20]
    }
    fn r#throw(&self, index: usize) -> Option<u32> {
        Some(self.cursor(21, index)?.u32())
    }
    fn synchronize_count(&self) -> usize {
        self.counts[21]
    }
    fn synchronize(&self, index: usize) -> Option<SyncRef> {
        records::decode_synchronize(self.cursor(22, index)?)
    }
    fn external_count(&self) -> usize {
        self.counts[22]
    }
    fn external(&self, index: usize) -> Option<ExternalRef> {
        records::decode_external(self.cursor(23, index)?)
    }
    fn flow_count(&self) -> usize {
        self.counts[23]
    }
    fn flow(&self, index: usize) -> Option<FlowRef> {
        records::decode_flow(self.cursor(24, index)?)
    }
    fn callable_value_count(&self) -> usize {
        self.counts[24]
    }
    fn callable_value(&self, index: usize) -> Option<ValueRef> {
        records::decode_value(self.cursor(25, index)?)
    }
    fn sam_count(&self) -> usize {
        self.counts[25]
    }
    fn sam_arity(&self, index: usize) -> Option<u32> {
        Some(self.cursor(26, index)?.u32())
    }
    fn creation_count(&self) -> usize {
        self.counts[26]
    }
    fn creation(&self, index: usize) -> Option<CallableCreation> {
        records::decode_creation(self.cursor(27, index)?)
    }
    fn value_flow_count(&self) -> usize {
        self.counts[27]
    }
    fn value_flow(&self, index: usize) -> Option<ValueFlow> {
        records::decode_value_flow(self.cursor(28, index)?)
    }
    fn callable_bridge_count(&self) -> usize {
        self.counts[30]
    }
    fn callable_bridge(&self, index: usize) -> Option<CallableBridge> {
        records::decode_callable_bridge(self.cursor(31, index)?)
    }
}

pub enum Availability {
    AbsentTop,
    Present(VerifiedCapsules),
}
impl Availability {
    pub fn absent_top(&self) -> Option<TopMask> {
        match self {
            Self::AbsentTop => Some(TopMask::ALL),
            Self::Present(_) => None,
        }
    }
}
pub fn open_optional(
    path: Option<&Path>,
    expected: Binding,
    limits: Limits,
) -> Result<Availability, Error> {
    expected.validate()?;
    match path {
        None => Ok(Availability::AbsentTop),
        Some(path) => open(path, expected, limits).map(Availability::Present),
    }
}
pub fn open(path: &Path, expected: Binding, limits: Limits) -> Result<VerifiedCapsules, Error> {
    expected.validate()?;
    let artifact = selector_artifacts::open_bounded(path, ArtifactKind::Effects, limits.max_bytes)?;
    admit(artifact, expected, limits)
}

/// Admit an already checksum-verified owner, including a mapped immutable owner
/// whose unsafe backing-file lifetime contract remains the caller's duty.
pub fn admit(
    artifact: Artifact,
    expected: Binding,
    limits: Limits,
) -> Result<VerifiedCapsules, Error> {
    expected.validate()?;
    if artifact.kind() != ArtifactKind::Effects || artifact.byte_len() as u64 > limits.max_bytes {
        return Err(Error::Invalid("capsule transport kind or byte admission"));
    }
    if !artifact.section_ids().eq(1..=SECTIONS as u32) {
        return Err(Error::Invalid("section schema"));
    }
    let mut counts = [0usize; SECTIONS];
    for (i, width) in WIDTHS.into_iter().enumerate() {
        counts[i] = wire::table(
            &artifact,
            i as u32 + 1,
            width,
            if i == 1 {
                limits.max_text_bytes
            } else {
                limits.max_records
            },
        )?;
    }
    let records = counts[2..]
        .iter()
        .try_fold(0usize, |sum, n| sum.checked_add(*n))
        .ok_or(Error::Limit("aggregate table rows"))?;
    if records > limits.max_records as usize {
        return Err(Error::Limit("aggregate table rows"));
    }
    if counts[0] != 1 {
        return Err(Error::Invalid("metadata count"));
    }
    let (binding, bounds) = decode_meta(artifact.section(1)?)?;
    binding.validate()?;
    if binding != expected {
        return Err(Error::Invalid("world identity transplant"));
    }
    let value = VerifiedCapsules {
        artifact,
        binding,
        bounds,
        counts,
    };
    let mut end = 0u32;
    for i in 0..value.text_count() {
        let r = records::decode_text_range(value.cursor(3, i).ok_or(Error::Invalid("text row"))?)
            .ok_or(Error::Invalid("text row"))?;
        if r.start != end {
            return Err(Error::Invalid("text pool partition"));
        }
        end = end
            .checked_add(r.len)
            .ok_or(Error::Limit("text pool end"))?;
    }
    if end as usize != value.artifact.section(2)?.len() {
        return Err(Error::Invalid("unreferenced text bytes"));
    }
    validation::validate(&value, &value, binding, bounds, limits)?;
    Ok(value)
}

fn decode_meta(bytes: &[u8]) -> Result<(Binding, RefBounds), Error> {
    if bytes.len() != META_BYTES || &bytes[..8] != MAGIC {
        return Err(Error::Invalid("capsule magic"));
    }
    let mut r = wire::Cursor::new(&bytes[8..]);
    if r.u32() != VERSION || r.u32() != 0 {
        return Err(Error::Invalid("capsule schema version or flags"));
    }
    let b = Binding {
        producer: Hash(r.hash()),
        facts: Hash(r.hash()),
        graph: Hash(r.hash()),
        runtime: Hash(r.hash()),
        inputs: Hash(r.hash()),
        root_universe: Hash(r.hash()),
        contracts: Hash(r.hash()),
        member_authority: Hash(r.hash()),
        fact_nodes: r.u32(),
        fact_symbols: r.u32(),
        fact_operations: r.u32(),
        roots: r.u32(),
    };
    let bounds = RefBounds {
        fact_nodes: r.u32(),
        foreign_methods: r.u32(),
        authorities: r.u32(),
        members: r.u32(),
        classes: r.u32(),
        exceptions: r.u32(),
        externals: r.u32(),
        sites: r.u32(),
        sams: r.u32(),
        adapters: r.u32(),
        bridge_proofs: r.u32(),
        phases: r.u32(),
    };
    Ok((b, bounds))
}
fn encode_meta(out: &mut dyn Write, b: Binding, v: RefBounds) -> io::Result<()> {
    wire::row::<META_BYTES>(out, |r| {
        r.bytes(MAGIC);
        r.u32(VERSION);
        r.u32(0);
        for h in [
            b.producer,
            b.facts,
            b.graph,
            b.runtime,
            b.inputs,
            b.root_universe,
            b.contracts,
            b.member_authority,
        ] {
            r.hash(&h.0);
        }
        for n in [
            b.fact_nodes,
            b.fact_symbols,
            b.fact_operations,
            b.roots,
            v.fact_nodes,
            v.foreign_methods,
            v.authorities,
            v.members,
            v.classes,
            v.exceptions,
            v.externals,
            v.sites,
            v.sams,
            v.adapters,
            v.bridge_proofs,
            v.phases,
        ] {
            r.u32(n);
        }
    })
}
fn count(value: usize) -> Result<u32, Error> {
    let n = u32::try_from(value).map_err(|_| Error::Limit("table identifiers"))?;
    if n == NONE {
        return Err(Error::Limit("reserved table identifier"));
    }
    Ok(n)
}
fn bounds<T: TableView>(s: &Snapshot<'_, T>) -> Result<RefBounds, Error> {
    Ok(RefBounds {
        fact_nodes: s.binding.fact_nodes,
        foreign_methods: count(s.keys.foreign_methods.len())?,
        authorities: count(s.keys.authorities.len())?,
        members: count(s.keys.members.len())?,
        classes: count(s.keys.classes.len())?,
        exceptions: count(s.keys.exceptions.len())?,
        externals: count(s.keys.externals.len())?,
        sites: count(s.keys.sites.len())?,
        sams: count(s.keys.sams.len())?,
        adapters: count(s.keys.adapters.len())?,
        bridge_proofs: count(s.keys.bridge_proofs.len())?,
        phases: count(s.keys.phases.len())?,
    })
}
fn missing() -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidInput,
        "effect source changed after validation",
    )
}

pub fn write<T: TableView>(
    path: &Path,
    s: &Snapshot<'_, T>,
    limits: Limits,
) -> Result<Hash, Error> {
    s.binding.validate()?;
    let b = bounds(s)?;
    let mut end = 0u32;
    for r in s.keys.strings {
        if r.start != end {
            return Err(Error::Invalid("text pool partition"));
        }
        end = end
            .checked_add(r.len)
            .ok_or(Error::Limit("text pool end"))?;
    }
    if end as usize != s.keys.text.len() {
        return Err(Error::Invalid("unreferenced text bytes"));
    }
    validation::validate(&s.keys, s.effects, s.binding, b, limits)?;
    let lengths = [
        1,
        s.keys.text.len(),
        s.keys.strings.len(),
        s.keys.contexts.len(),
        s.keys.providers.len(),
        s.keys.foreign_methods.len(),
        s.keys.members.len(),
        s.keys.classes.len(),
        s.keys.authorities.len(),
        s.keys.exceptions.len(),
        s.keys.externals.len(),
        s.keys.sites.len(),
        s.effects.method_count(),
        s.effects.call_count(),
        s.effects.origin_count(),
        s.effects.code_observation_count(),
        s.effects.read_count(),
        s.effects.write_count(),
        s.effects.escape_count(),
        s.effects.initialize_count(),
        s.effects.throw_count(),
        s.effects.synchronize_count(),
        s.effects.external_count(),
        s.effects.flow_count(),
        s.effects.callable_value_count(),
        s.effects.sam_count(),
        s.effects.creation_count(),
        s.effects.value_flow_count(),
        s.keys.sams.len(),
        s.keys.adapters.len(),
        s.effects.callable_bridge_count(),
        s.keys.bridge_proofs.len(),
        s.keys.phases.len(),
    ];
    let mut sections = [StreamingSection {
        id: 0,
        count: 0,
        length: 0,
    }; SECTIONS];
    let mut total = 80u64 + SECTIONS as u64 * 64;
    let mut records = 0u64;
    for (i, n) in lengths.into_iter().enumerate() {
        let n = count(n)?;
        if (i == 1 && n > limits.max_text_bytes) || (i != 1 && n > limits.max_records) {
            return Err(Error::Limit("section row admission"));
        }
        let length = u64::from(n)
            .checked_mul(WIDTHS[i] as u64)
            .ok_or(Error::Limit("section bytes"))?;
        if i >= 2 {
            records = records
                .checked_add(u64::from(n))
                .ok_or(Error::Limit("aggregate table rows"))?;
        }
        total = total
            .checked_add(7)
            .map(|v| v & !7)
            .and_then(|v| v.checked_add(length))
            .ok_or(Error::Limit("artifact size"))?;
        sections[i] = StreamingSection {
            id: i as u32 + 1,
            count: u64::from(n),
            length,
        };
    }
    if records > u64::from(limits.max_records) {
        return Err(Error::Limit("aggregate table rows"));
    }
    if total > limits.max_bytes {
        return Err(Error::Limit("artifact byte admission"));
    }
    let identity =
        selector_artifacts::write_streaming(path, ArtifactKind::Effects, &sections, |id, out| {
            match id {
                1 => encode_meta(out, s.binding, b)?,
                2 => out.write_all(s.keys.text)?,
                3 => {
                    for value in s.keys.strings {
                        records::encode_text_range(out, *value)?;
                    }
                }
                4 => {
                    for value in s.keys.contexts {
                        records::encode_context(out, *value)?;
                    }
                }
                5 => {
                    for value in s.keys.providers {
                        records::encode_provider(out, *value)?;
                    }
                }
                6 => {
                    for value in s.keys.foreign_methods {
                        records::encode_foreign_method(out, *value)?;
                    }
                }
                7 => {
                    for value in s.keys.members {
                        records::encode_member(out, *value)?;
                    }
                }
                8 => {
                    for value in s.keys.classes {
                        records::encode_class(out, *value)?;
                    }
                }
                9 => {
                    for value in s.keys.authorities {
                        records::encode_authority(out, *value)?;
                    }
                }
                10 => {
                    for value in s.keys.exceptions {
                        records::encode_exception_key(out, *value)?;
                    }
                }
                11 => {
                    for value in s.keys.externals {
                        records::encode_external_key(out, *value)?;
                    }
                }
                12 => {
                    for value in s.keys.sites {
                        records::encode_site(out, *value)?;
                    }
                }
                13 => {
                    for i in 0..s.effects.method_count() {
                        let value = s.effects.method(i).ok_or_else(missing)?;
                        records::encode_method(out, value)?;
                    }
                }
                14 => {
                    for i in 0..s.effects.call_count() {
                        let value = s.effects.call(i).ok_or_else(missing)?;
                        records::encode_call(out, value)?;
                    }
                }
                15 => {
                    for i in 0..s.effects.origin_count() {
                        let value = s.effects.origin(i).ok_or_else(missing)?;
                        records::encode_origin(out, value)?;
                    }
                }
                16 => {
                    for i in 0..s.effects.code_observation_count() {
                        let value = s.effects.code_observation(i).ok_or_else(missing)?;
                        records::encode_code_observation(out, value)?;
                    }
                }
                17 => {
                    for i in 0..s.effects.read_count() {
                        let value = s.effects.read(i).ok_or_else(missing)?;
                        records::encode_storage(out, value)?;
                    }
                }
                18 => {
                    for i in 0..s.effects.write_count() {
                        let value = s.effects.write(i).ok_or_else(missing)?;
                        records::encode_storage(out, value)?;
                    }
                }
                19 => {
                    for i in 0..s.effects.escape_count() {
                        let value = s.effects.escape(i).ok_or_else(missing)?;
                        records::encode_escape(out, value)?;
                    }
                }
                20 => {
                    for i in 0..s.effects.initialize_count() {
                        let value = s.effects.initialize(i).ok_or_else(missing)?;
                        out.write_all(&value.0.to_le_bytes())?;
                    }
                }
                21 => {
                    for i in 0..s.effects.throw_count() {
                        let value = s.effects.r#throw(i).ok_or_else(missing)?;
                        out.write_all(&value.to_le_bytes())?;
                    }
                }
                22 => {
                    for i in 0..s.effects.synchronize_count() {
                        let value = s.effects.synchronize(i).ok_or_else(missing)?;
                        records::encode_synchronize(out, value)?;
                    }
                }
                23 => {
                    for i in 0..s.effects.external_count() {
                        let value = s.effects.external(i).ok_or_else(missing)?;
                        records::encode_external(out, value)?;
                    }
                }
                24 => {
                    for i in 0..s.effects.flow_count() {
                        let value = s.effects.flow(i).ok_or_else(missing)?;
                        records::encode_flow(out, value)?;
                    }
                }
                25 => {
                    for i in 0..s.effects.callable_value_count() {
                        records::encode_value(
                            out,
                            s.effects.callable_value(i).ok_or_else(missing)?,
                        )?;
                    }
                }
                26 => {
                    for i in 0..s.effects.sam_count() {
                        out.write_all(&s.effects.sam_arity(i).ok_or_else(missing)?.to_le_bytes())?;
                    }
                }
                27 => {
                    for i in 0..s.effects.creation_count() {
                        records::encode_creation(out, s.effects.creation(i).ok_or_else(missing)?)?;
                    }
                }
                28 => {
                    for i in 0..s.effects.value_flow_count() {
                        records::encode_value_flow(
                            out,
                            s.effects.value_flow(i).ok_or_else(missing)?,
                        )?;
                    }
                }
                29 => {
                    for v in s.keys.sams {
                        records::encode_sam_key(out, *v)?;
                    }
                }
                30 => {
                    for v in s.keys.adapters {
                        records::encode_adapter(out, *v)?;
                    }
                }
                31 => {
                    for i in 0..s.effects.callable_bridge_count() {
                        records::encode_callable_bridge(
                            out,
                            s.effects.callable_bridge(i).ok_or_else(missing)?,
                        )?;
                    }
                }
                32 => {
                    for v in s.keys.bridge_proofs {
                        records::encode_bridge_proof(out, *v)?;
                    }
                }
                33 => {
                    for v in s.keys.phases {
                        records::encode_phase(out, *v)?;
                    }
                }
                _ => return Err(missing()),
            }
            Ok(())
        })?;
    Ok(Hash(identity))
}
