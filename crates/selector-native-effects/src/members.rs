//! Canonical storage identity needs JVM declaring-field resolution plus the
//! contextual first-provider proof, never matching labels or class hashes alone.
use crate::provider::{Error, MemberInvocation, ResolutionReceipt, VerifiedProvider};
use crate::{NONE, Produced};
use selector_effects::StorageKind;
use selector_jvm_resolve::{Resolution, UnknownReason};
use selector_models::binary::MemberRef;
use std::sync::Arc;
#[derive(Clone, Debug)]
pub struct DeclaringField {
    pub field: u32,
    pub authority: u32,
    pub owner: Arc<str>,
    pub flags: u16,
    pub is_static: bool,
    pub class: Arc<ResolutionReceipt>,
}
#[derive(Clone, Debug)]
pub enum FieldAuthority {
    Declared(DeclaringField),
    /// No read/write instruction demanded this metadata-only symbolic field.
    Unused,
    RuntimeRegion,
    ConflictingAccessKinds,
    Pending(UnknownReason),
}
/// One flat scan over retained operations, then one cached query per distinct
/// contextual field ABI. Unknown aliases remain noncanonical in the world.
pub fn resolve_declaring_fields(
    out: &Produced<'_>,
    provider: &mut VerifiedProvider<'_>,
) -> Result<Vec<FieldAuthority>, Error> {
    let mut kinds = vec![0u8; out.fields.len()];
    for row in out.data.reads.iter().chain(&out.data.writes) {
        if row.member == NONE {
            continue;
        }
        let Some(kind) = kinds.get_mut(row.member as usize) else {
            return Err(Error::Invalid("native field reference"));
        };
        *kind |= match row.kind {
            StorageKind::StaticField => 1,
            StorageKind::InstanceField => 2,
            StorageKind::RuntimeState => 4,
            _ => continue,
        };
    }
    let mut result = Vec::with_capacity(out.fields.len());
    for (index, field) in out.fields.iter().enumerate() {
        let authority = if field.runtime_throwable_region {
            FieldAuthority::RuntimeRegion
        } else if kinds[index] == 0 {
            FieldAuthority::Unused
        } else if !matches!(kinds[index], 1 | 2) {
            FieldAuthority::ConflictingAccessKinds
        } else {
            let class = out
                .classes
                .get(field.class as usize)
                .ok_or(Error::Invalid("native field class"))?;
            let is_static = kinds[index] == 1;
            let member = MemberRef {
                owner: out.text(class.owner),
                name: out.text(field.name),
                descriptor: out.text(field.descriptor),
            };
            let resolution = provider.resolve_member(
                class.authority,
                member,
                if is_static {
                    MemberInvocation::StaticField
                } else {
                    MemberInvocation::InstanceField
                },
                None,
            )?;
            let declaration = match &resolution.resolution {
                Resolution::Found(found) => Ok((
                    resolution
                        .declared_owner
                        .clone()
                        .ok_or(Error::Invalid("declaring field owner proof"))?,
                    found.flags,
                )),
                Resolution::Unknown(reason) => Err(*reason),
            };
            match declaration {
                Err(reason) => FieldAuthority::Pending(reason),
                Ok((owner, flags)) => {
                    let (bytes, receipt) = provider.resolve(class.authority, &owner)?;
                    if bytes.is_none() || receipt.class_sha256.is_none() {
                        return Err(Error::Invalid("declaring field provider proof"));
                    }
                    FieldAuthority::Declared(DeclaringField {
                        field: index as u32,
                        authority: class.authority,
                        owner,
                        flags,
                        is_static,
                        class: receipt,
                    })
                }
            }
        };
        result.push(authority);
    }
    Ok(result)
}
