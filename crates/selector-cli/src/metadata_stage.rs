//! Optional external signatures: a checked immutable input bundle precedes cache
//! lookup; only a cache miss prepares compiler requests and admits signatures.
use crate::external_metadata::{AuthorityLimits, CapturedMetadataAuthority};
use selector_extract::external_metadata::{
    self, AdmittedExternalMetadata, ExternalMetadataLimits, ExternalMetadataManifest,
    MANIFEST_SCHEMA, MetadataProviderAuthority, MetadataRequests,
};
use selector_types::{ContentHash, Error};
use sha2::{Digest, Sha256};
use std::collections::{HashMap, HashSet};
use std::fs::OpenOptions;
use std::io::Read;
use std::os::unix::fs::OpenOptionsExt;
use std::path::{Path, PathBuf};
use std::sync::Arc;

struct InputPin {
    role: String,
    path: PathBuf,
    hash: ContentHash,
    bytes: u64,
}

/// Input-bundle verification is deliberately weaker than signature admission:
/// no payload is decoded and no supplied root gains request membership here.
/// Its identity is safe as a key only for artifacts fully admitted on a prior
/// miss under the exact extraction and native metadata producer identities.
pub(super) struct CheckedInputs {
    manifest: PathBuf,
    expected_tool: ContentHash,
    authority: CapturedMetadataAuthority,
    limits: ExternalMetadataLimits,
    identity: ContentHash,
    pins: Vec<InputPin>,
}

fn regular(path: &Path, maximum: usize) -> Result<(std::fs::File, u64), Error> {
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK)
        .open(path)?;
    let metadata = file.metadata()?;
    if !metadata.is_file() || metadata.len() > maximum as u64 {
        return Err(Error::Limit("external metadata regular input bytes"));
    }
    Ok((file, metadata.len()))
}
fn pin(role: String, path: PathBuf, maximum: usize) -> Result<InputPin, Error> {
    let (mut file, bytes) = regular(&path, maximum)?;
    let mut hash = Sha256::new();
    let mut total = 0u64;
    let mut block = [0u8; 128 * 1024];
    loop {
        let n = file.read(&mut block)?;
        if n == 0 {
            break;
        }
        total = total
            .checked_add(n as u64)
            .ok_or(Error::Limit("external metadata bytes"))?;
        if total > bytes {
            return Err(Error::Invalid("external metadata changed while hashing"));
        }
        hash.update(&block[..n]);
    }
    if total != bytes || file.metadata()?.len() != bytes {
        return Err(Error::Invalid("external metadata changed while hashing"));
    }
    Ok(InputPin {
        role,
        path,
        hash: ContentHash(hash.finalize().into()),
        bytes,
    })
}
fn field(hash: &mut Sha256, bytes: &[u8]) {
    hash.update((bytes.len() as u64).to_le_bytes());
    hash.update(bytes);
}

impl CheckedInputs {
    pub(super) fn open(
        manifest: &Path,
        expected_tool: ContentHash,
        binary_map: &Path,
        contexts: &Path,
        root: &Path,
    ) -> Result<Self, Error> {
        let limits = ExternalMetadataLimits::default();
        let authority_limits = AuthorityLimits::default();
        let manifest_pin = pin(
            "metadata_manifest".into(),
            manifest.to_owned(),
            limits.max_manifest_bytes,
        )?;
        let (file, length) = regular(manifest, limits.max_manifest_bytes)?;
        let mut raw = Vec::with_capacity(length as usize);
        file.take(length + 1).read_to_end(&mut raw)?;
        if raw.len() as u64 != length
            || ContentHash(Sha256::digest(&raw).into()) != manifest_pin.hash
        {
            return Err(Error::Invalid("external metadata manifest changed"));
        }
        let parsed: ExternalMetadataManifest =
            serde_json::from_slice(&raw).map_err(|error| Error::Message(error.to_string()))?;
        if parsed.schema != MANIFEST_SCHEMA
            || expected_tool == ContentHash::default()
            || ContentHash::from_hex(&parsed.producer_sha256)? != expected_tool
        {
            return Err(Error::Invalid("external metadata producer or schema"));
        }
        let context_pin = pin(
            "metadata_contexts".into(),
            contexts.to_owned(),
            authority_limits.max_manifest_bytes,
        )?;
        if ContentHash::from_hex(&parsed.contexts_sha256)? != context_pin.hash {
            return Err(Error::Invalid(
                "external metadata compiler context input mismatch",
            ));
        }
        let map_pin = pin(
            "metadata_binary_map".into(),
            binary_map.to_owned(),
            authority_limits.max_manifest_bytes,
        )?;
        let authority = CapturedMetadataAuthority::open(
            binary_map,
            contexts,
            context_pin.hash,
            root,
            &authority_limits,
        )?;
        if ContentHash::from_hex(&parsed.authority_sha256)? != authority.identity()
            || authority.contexts_identity() != context_pin.hash
            || ContentHash::from_hex(&authority.receipt().binary_map_sha256)? != map_pin.hash
        {
            return Err(Error::Invalid("external metadata authority"));
        }
        let mut pins = vec![manifest_pin, context_pin, map_pin];
        let mut total = 0usize;
        for (index, payload) in parsed.payloads.iter().enumerate() {
            let p = pin(
                format!("metadata_payload_{index}"),
                manifest
                    .parent()
                    .unwrap_or(Path::new("."))
                    .join(&payload.path),
                limits.max_payload_bytes,
            )?;
            total = total
                .checked_add(
                    usize::try_from(p.bytes)
                        .map_err(|_| Error::Limit("external metadata payload bytes"))?,
                )
                .ok_or(Error::Limit("external metadata payload bytes"))?;
            if total > limits.max_total_payload_bytes {
                return Err(Error::Limit("external metadata payload bytes"));
            }
            if p.hash != ContentHash::from_hex(&payload.sha256)? {
                return Err(Error::Invalid("external metadata payload hash"));
            }
            pins.push(p);
        }
        let mut providers = HashMap::new();
        let mut roots = HashSet::new();
        for binding in &parsed.bindings {
            let components: Vec<_> = binding.context.split('\0').collect();
            if binding.context.is_empty()
                || components.iter().any(|part| part.is_empty())
                || components.windows(2).any(|pair| pair[0] >= pair[1])
                || binding.roots.is_empty()
                || binding.projections.len() != components.len()
            {
                return Err(Error::Invalid("external metadata context components"));
            }
            for root in &binding.roots {
                if !roots.insert((binding.context.as_str(), root.as_str())) {
                    return Err(Error::Invalid("duplicate external metadata root"));
                }
                if roots.len() > limits.max_symbols {
                    return Err(Error::Limit("external metadata roots"));
                }
            }
            let mut projected = HashSet::new();
            for projection in &binding.projections {
                if !components.contains(&projection.context.as_str())
                    || !projected.insert(projection.context.as_str())
                    || projection.payload as usize >= parsed.payloads.len()
                {
                    return Err(Error::Invalid(
                        "external metadata projection context or payload",
                    ));
                }
                let key = (projection.context.as_str(), projection.outer_class.as_str());
                if !providers.contains_key(&key) {
                    let resolved = authority
                        .resolve(key.0, key.1)?
                        .ok_or(Error::Invalid("external metadata provider unavailable"))?;
                    if resolved.class_bytes.len() > limits.max_provider_class_bytes {
                        return Err(Error::Limit("external metadata provider class bytes"));
                    }
                    providers.insert(
                        key,
                        (
                            resolved.classpath_identity,
                            resolved.provider_index,
                            resolved.provider_sha256,
                            ContentHash(Sha256::digest(&resolved.class_bytes).into()),
                        ),
                    );
                }
                let proof = providers[&key];
                if proof.0 != ContentHash::from_hex(&projection.classpath_sha256)?
                    || proof.1 != projection.provider_index
                    || proof.2 != ContentHash::from_hex(&projection.provider_sha256)?
                    || proof.3 != ContentHash::from_hex(&projection.outer_class_sha256)?
                {
                    return Err(Error::Invalid("external metadata provider proof mismatch"));
                }
            }
        }
        // Archive files remain physical receipt inputs as well as authority-bound
        // provider digests. Directory inventories are bound by original contexts,
        // authority identity and the normal compiler-input inventory receipt.
        for (index, provider) in authority.receipt().entries.iter().enumerate() {
            if provider.kind == "jar" {
                pins.push(InputPin {
                    role: format!("metadata_provider_{index}"),
                    path: provider.physical_path.clone(),
                    hash: ContentHash::from_hex(&provider.sha256)?,
                    bytes: std::fs::metadata(&provider.physical_path)?.len(),
                });
            }
        }
        let mut identity = Sha256::new();
        identity.update(b"selector-checked-metadata-inputs/v1\0");
        identity.update(ContentHash::from_hex(env!("SELECTOR_METADATA_PRODUCER"))?.0);
        identity.update(expected_tool.0);
        identity.update(authority.identity().0);
        for p in &pins {
            field(&mut identity, p.role.as_bytes());
            identity.update(p.hash.0);
            identity.update(p.bytes.to_le_bytes());
        }
        eprintln!(
            "{}",
            serde_json::json!({"stage":"metadata_inputs","input_bundle_checked":true,
            "full_signature_admission":false,"payloads":parsed.payloads.len(),"bindings":parsed.bindings.len(),
            "authority":authority.identity().to_string(),"contexts":authority.contexts_identity().to_string()})
        );
        Ok(Self {
            manifest: manifest.to_owned(),
            expected_tool,
            authority,
            limits,
            identity: ContentHash(identity.finalize().into()),
            pins,
        })
    }
    pub(super) fn identity(&self) -> ContentHash {
        self.identity
    }
    pub(super) fn artifact_inputs(&self) -> impl Iterator<Item = (&str, &Path)> {
        self.pins
            .iter()
            .map(|p| (p.role.as_str(), p.path.as_path()))
    }
    pub(super) fn admit(
        &self,
        requests: &MetadataRequests<'_>,
    ) -> Result<Arc<AdmittedExternalMetadata>, Error> {
        let metadata = external_metadata::admit(
            &self.manifest,
            requests,
            &self.authority,
            self.expected_tool,
            &self.limits,
        )?;
        // A changing manifest/payload may not publish an artifact under the
        // identity checked before cache lookup. Providers are immutable owners.
        for p in &self.pins {
            if p.role.starts_with("metadata_provider_") {
                continue;
            }
            let actual = pin(
                p.role.clone(),
                p.path.clone(),
                usize::try_from(p.bytes).map_err(|_| Error::Limit("external metadata bytes"))?,
            )?;
            if actual.hash != p.hash || actual.bytes != p.bytes {
                return Err(Error::Invalid("external metadata changed after precheck"));
            }
        }
        Ok(Arc::new(metadata))
    }
}

/// Provider inspection has no signature payload or executable authority. It
/// uses the same physical admission owner as extraction, once per invocation.
pub(super) fn write_authority_preview(
    input: &Path,
    binary_map: &Path,
    contexts: &Path,
    root: &Path,
    out: &mut impl std::io::Write,
) -> crate::Result<()> {
    use serde::{Deserialize, Serialize};
    #[derive(Deserialize)]
    #[serde(deny_unknown_fields)]
    struct Requests {
        schema: String,
        classes: Vec<Class>,
    }
    #[derive(Deserialize, Serialize)]
    #[serde(deny_unknown_fields)]
    struct Class {
        context: String,
        outer_class: String,
    }
    #[derive(Serialize)]
    struct Row<'a> {
        context: &'a str,
        outer_class: &'a str,
        available: bool,
        classpath_sha256: Option<String>,
        provider_index: Option<u32>,
        provider_sha256: Option<String>,
        class_sha256: Option<String>,
    }
    let limits = ExternalMetadataLimits::default();
    let (file, bytes) = regular(input, limits.max_manifest_bytes)?;
    let mut raw = Vec::with_capacity(bytes as usize);
    file.take(bytes + 1).read_to_end(&mut raw)?;
    if raw.len() as u64 != bytes {
        return Err(Error::Invalid("metadata provider requests changed").into());
    }
    let mut requests: Requests = serde_json::from_slice(&raw)?;
    if requests.schema != "external-metadata-provider-requests/v1" {
        return Err(Error::Invalid("metadata provider request schema").into());
    }
    if requests.classes.len() > limits.max_symbols {
        return Err(Error::Limit("metadata provider requests").into());
    }
    requests
        .classes
        .sort_unstable_by(|a, b| (&a.context, &a.outer_class).cmp(&(&b.context, &b.outer_class)));
    if requests.classes.windows(2).any(|pair| {
        pair[0].context == pair[1].context && pair[0].outer_class == pair[1].outer_class
    }) {
        return Err(Error::Invalid("duplicate metadata provider request").into());
    }
    let authority_limits = AuthorityLimits::default();
    let contexts_pin = pin(
        "contexts".into(),
        contexts.to_owned(),
        authority_limits.max_manifest_bytes,
    )?;
    let authority = CapturedMetadataAuthority::open(
        binary_map,
        contexts,
        contexts_pin.hash,
        root,
        &authority_limits,
    )?;
    out.write_all(
        b"{\"schema\":\"external-metadata-provider-authority/v1\",\"authority_sha256\":",
    )?;
    serde_json::to_writer(&mut *out, &authority.identity().to_string())?;
    out.write_all(b",\"contexts_sha256\":")?;
    serde_json::to_writer(&mut *out, &authority.contexts_identity().to_string())?;
    out.write_all(b",\"requests_sha256\":")?;
    serde_json::to_writer(
        &mut *out,
        &ContentHash(Sha256::digest(&raw).into()).to_string(),
    )?;
    out.write_all(b",\"physical_authority\":")?;
    serde_json::to_writer(&mut *out, authority.receipt())?;
    out.write_all(b",\"classes\":[")?;
    for (index, class) in requests.classes.iter().enumerate() {
        if index != 0 {
            out.write_all(b",")?;
        }
        let resolved = authority.resolve(&class.context, &class.outer_class)?;
        let row = Row {
            context: &class.context,
            outer_class: &class.outer_class,
            available: resolved.is_some(),
            classpath_sha256: resolved.as_ref().map(|r| r.classpath_identity.to_string()),
            provider_index: resolved.as_ref().map(|r| r.provider_index),
            provider_sha256: resolved.as_ref().map(|r| r.provider_sha256.to_string()),
            class_sha256: resolved
                .as_ref()
                .map(|r| ContentHash(Sha256::digest(&r.class_bytes).into()).to_string()),
        };
        serde_json::to_writer(&mut *out, &row)?;
    }
    out.write_all(b"]}\n")?;
    Ok(())
}
