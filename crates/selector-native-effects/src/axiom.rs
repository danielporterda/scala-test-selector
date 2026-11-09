//! Explicit instruction-local JVMS contract, separate from loader/runner closure.
use crate::{Error, NONE};
use selector_runtime_platform::{self as binary_platform, PlatformOptions};
use sha2::{Digest, Sha256};

pub const CONTRACT: &str = "jvms21-instruction-local-primitive-effects/v1";

/// An instruction-law scope, not a claim that the image is an isolated runner.
/// The admitted runtime is NEW declared authority, never historical compilation.
pub struct RuntimeAxiom {
    platform: [u8; 32],
    platform_producer: [u8; 32],
    capture: [u8; 32],
    producer: [u8; 32],
    authorities: Vec<u32>,
    authorities_sha256: [u8; 32],
    java_feature: u16,
}
#[derive(Clone, Debug)]
pub struct AxiomReceipt {
    pub contract: &'static str,
    pub producer_sha256: [u8; 32],
    pub platform_identity: [u8; 32],
    pub platform_producer_sha256: [u8; 32],
    pub capture_sha256: [u8; 32],
    pub authority_context_bindings_sha256: [u8; 32],
    pub java_feature: u16,
    pub instruction_local_only: bool,
    pub runtime_isolation_proven: bool,
}
impl RuntimeAxiom {
    /// This pins the implemented laws/decoder, not merely a caller label.
    pub fn producer() -> [u8; 32] {
        let mut hash = Sha256::new();
        hash.update(CONTRACT.as_bytes());
        for bytes in [
            include_bytes!("axiom.rs").as_slice(),
            include_bytes!("lib.rs").as_slice(),
            include_bytes!("adapters.rs").as_slice(),
            include_bytes!("reachable.rs").as_slice(),
            include_bytes!("provider.rs").as_slice(),
            include_bytes!("members.rs").as_slice(),
            include_bytes!("framework_transport.rs").as_slice(),
            include_bytes!("../Cargo.toml").as_slice(),
            include_bytes!("../../selector-models/src/binary.rs").as_slice(),
            include_bytes!("../../selector-models/src/binary_envelope.rs").as_slice(),
            include_bytes!("../../selector-models/src/binary_diagnostic.rs").as_slice(),
            include_bytes!("../../selector-models/src/binary_envelope_aliases.rs").as_slice(),
            include_bytes!("../../selector-models/src/binary_metadata.rs").as_slice(),
            include_bytes!("../../selector-jvm-resolve/src/lib.rs").as_slice(),
            include_bytes!("../../selector-jvm-resolve/Cargo.toml").as_slice(),
            include_bytes!("../../selector-effects/src/lib.rs").as_slice(),
            include_bytes!("../../selector-effects/src/callables.rs").as_slice(),
            include_bytes!("../../selector-effects/Cargo.toml").as_slice(),
            include_bytes!("../../selector-runtime-platform/src/lib.rs").as_slice(),
            include_bytes!("../../selector-runtime-platform/Cargo.toml").as_slice(),
        ] {
            hash.update((bytes.len() as u64).to_le_bytes());
            hash.update(bytes);
        }
        hash.finalize().into()
    }
    /// No boolean can create this token. Normal platform admission rechecks the
    /// complete image/inventory/context/provider pins. The explicit fixed
    /// contract and expected code producer are additional admitted inputs.
    pub fn admit(
        options: &PlatformOptions,
        contract: &str,
        expected_producer: [u8; 32],
        authority_contexts: &[(u32, &str)],
    ) -> Result<Self, Error> {
        if contract != CONTRACT
            || expected_producer != Self::producer()
            || authority_contexts.is_empty()
            || authority_contexts.len() > 4096
        {
            return Err(Error::Binding);
        }
        let platform = binary_platform::admit(options).map_err(|_| Error::Binding)?;
        if platform.java_feature != 21 {
            return Err(Error::Binding);
        }
        let mut sorted = authority_contexts.to_vec();
        sorted.sort_unstable();
        if sorted
            .iter()
            .any(|&(id, context)| id == NONE || !platform.contains_context(context))
            || sorted.windows(2).any(|pair| pair[0].0 == pair[1].0)
        {
            return Err(Error::Binding);
        }
        let mut hash = Sha256::new();
        let mut authorities = Vec::with_capacity(sorted.len());
        for (id, context) in sorted {
            hash.update(id.to_le_bytes());
            hash.update((context.len() as u64).to_le_bytes());
            hash.update(context.as_bytes());
            authorities.push(id);
        }
        Ok(Self {
            platform: platform.binding.identity.0,
            platform_producer: platform.binding.producer_sha256.0,
            capture: platform.binding.capture_sha256.0,
            producer: expected_producer,
            authorities,
            authorities_sha256: hash.finalize().into(),
            java_feature: platform.java_feature,
        })
    }
    pub fn receipt(&self) -> AxiomReceipt {
        AxiomReceipt {
            contract: CONTRACT,
            producer_sha256: self.producer,
            platform_identity: self.platform,
            platform_producer_sha256: self.platform_producer,
            capture_sha256: self.capture,
            authority_context_bindings_sha256: self.authorities_sha256,
            java_feature: self.java_feature,
            instruction_local_only: true,
            runtime_isolation_proven: false,
        }
    }
    pub(crate) fn permits(&self, authority: u32, major: u16) -> bool {
        (45..=self.java_feature + 44).contains(&major)
            && self.authorities.binary_search(&authority).is_ok()
    }
    #[cfg(test)]
    pub(crate) fn normalized_test_token(authority: u32) -> Self {
        // A labeled instruction-classification unit fixture, not platform
        // admission. The ignored actual-image test exercises the real API.
        Self {
            platform: [7; 32],
            platform_producer: [7; 32],
            capture: [7; 32],
            producer: Self::producer(),
            authorities: vec![authority],
            authorities_sha256: [8; 32],
            java_feature: 21,
        }
    }
}
