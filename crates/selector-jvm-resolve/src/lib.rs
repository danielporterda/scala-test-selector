//! JVM symbolic-member resolution over admitted, immutable class bytes.
//!
//! The loader must preserve its captured classpath order and verify every input
//! used to establish presence or absence. This layer never substitutes source
//! names or picks an arbitrary interface candidate. It implements JVMS 5.4.3.2,
//! 5.4.3.3, 5.4.3.4 and the ACC_SUPER selection in 6.5.invokespecial. Access
//! control, receiver dispatch and execution remain separate graph concerns.
use selector_models::binary::{self, ClassMetadata, InvokeKind, Limits, MemberRef};
use selector_types::Error;
use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::sync::Arc;

const STATIC: u16 = 0x0008;
const PRIVATE: u16 = 0x0002;
const PUBLIC: u16 = 0x0001;
const ABSTRACT: u16 = 0x0400;
const INTERFACE: u16 = 0x0200;
const MAX_CLASSES: usize = 4096;
const MAX_DEPTH: usize = 128;
const MAX_STEPS: usize = 16_384;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolvedMember {
    pub declared_owner: String,
    pub flags: u16,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnknownReason {
    MissingClass,
    MissingMember,
    AmbiguousMember,
    InvalidHierarchy,
    InvalidClass,
    InvocationMismatch,
    CallerRequired,
    ResourceLimit,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Resolution {
    Found(ResolvedMember),
    Unknown(UnknownReason),
}
enum Failure {
    Unknown(UnknownReason),
    Input(Error),
}
type Result<T> = std::result::Result<T, Failure>;
impl From<UnknownReason> for Failure {
    fn from(reason: UnknownReason) -> Self {
        Self::Unknown(reason)
    }
}

#[derive(Clone, Copy)]
enum Declaration {
    Missing,
    Found(u16),
    Ambiguous,
}
impl Declaration {
    fn flags(self) -> Result<Option<u16>> {
        match self {
            Self::Missing => Ok(None),
            Self::Found(flags) => Ok(Some(flags)),
            Self::Ambiguous => Err(UnknownReason::AmbiguousMember.into()),
        }
    }
}
struct Header {
    metadata: Arc<ClassMetadata>,
    flags: u16,
    major: u16,
    method: Declaration,
    field: Declaration,
}
// The index borrows its name from a shared metadata owner rather than copying
// every class/interface name again for every symbolic-member query.
struct ClassName(Arc<ClassMetadata>);
impl Borrow<str> for ClassName {
    fn borrow(&self) -> &str {
        self.0.name()
    }
}
impl Hash for ClassName {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.name().hash(state);
    }
}
impl PartialEq for ClassName {
    fn eq(&self, other: &Self) -> bool {
        self.0.name() == other.0.name()
    }
}
impl Eq for ClassName {}
struct Resolver<'a, F> {
    member: MemberRef<'a>,
    loader: F,
    headers: Vec<Header>,
    indices: HashMap<ClassName, usize>,
    steps: usize,
}
impl<'a, F> Resolver<'a, F>
where
    F: FnMut(&str) -> Result<Option<Arc<ClassMetadata>>>,
{
    fn new(member: MemberRef<'a>, loader: F) -> Self {
        Self {
            member,
            loader,
            headers: Vec::new(),
            indices: HashMap::new(),
            steps: 0,
        }
    }
    fn step(&mut self) -> Result<()> {
        self.steps += 1;
        if self.steps > MAX_STEPS {
            return Err(UnknownReason::ResourceLimit.into());
        }
        Ok(())
    }
    fn load(&mut self, name: &str) -> Result<usize> {
        self.step()?;
        if let Some(&index) = self.indices.get(name) {
            return Ok(index);
        }
        if self.headers.len() >= MAX_CLASSES {
            return Err(UnknownReason::ResourceLimit.into());
        }
        let class = (self.loader)(name)?.ok_or(UnknownReason::MissingClass)?;
        if class.name() != name {
            return Err(UnknownReason::InvalidClass.into());
        }
        let method = match class.method(self.member.name, Some(self.member.descriptor)) {
            Ok(method) => Declaration::Found(method.flags),
            Err(error) if error.kind == binary::ErrorKind::MissingMethod => Declaration::Missing,
            Err(error) if error.kind == binary::ErrorKind::AmbiguousMethod => {
                Declaration::Ambiguous
            }
            Err(_) => return Err(UnknownReason::InvalidClass.into()),
        };
        let field = match class.field(self.member.name, self.member.descriptor) {
            Ok(Some(field)) => Declaration::Found(field.flags),
            Ok(None) => Declaration::Missing,
            Err(_) => Declaration::Ambiguous,
        };
        let header = Header {
            flags: class.flags(),
            major: class.header().major,
            method,
            field,
            metadata: class.clone(),
        };
        let index = self.headers.len();
        self.indices.insert(ClassName(class), index);
        self.headers.push(header);
        Ok(index)
    }
    fn found(&self, index: usize, flags: u16) -> ResolvedMember {
        ResolvedMember {
            declared_owner: self.headers[index].metadata.name().to_owned(),
            flags,
        }
    }
    fn class_chain(&mut self, root: usize, stop: usize) -> Result<Vec<usize>> {
        let mut chain = Vec::new();
        let mut seen = HashSet::new();
        let mut next = Some(root);
        while let Some(index) = next {
            if chain.len() >= MAX_DEPTH {
                return Err(UnknownReason::ResourceLimit.into());
            }
            if !seen.insert(index) || self.headers[index].flags & INTERFACE != 0 {
                return Err(UnknownReason::InvalidHierarchy.into());
            }
            chain.push(index);
            if index == stop {
                break;
            }
            let metadata = self.headers[index].metadata.clone();
            next = metadata.parent().map(|name| self.load(name)).transpose()?;
        }
        Ok(chain)
    }
    // Stop at the first class declaration: missing metadata below that point
    // cannot alter symbolic resolution, so do not demand unrelated ancestors.
    fn class_method(&mut self, root: usize) -> Result<(Option<(usize, u16)>, Vec<usize>)> {
        let mut chain = Vec::new();
        let mut seen = HashSet::new();
        let mut next = Some(root);
        while let Some(index) = next {
            if chain.len() >= MAX_DEPTH {
                return Err(UnknownReason::ResourceLimit.into());
            }
            if !seen.insert(index) || self.headers[index].flags & INTERFACE != 0 {
                return Err(UnknownReason::InvalidHierarchy.into());
            }
            chain.push(index);
            if let Some(flags) = self.headers[index].method.flags()? {
                return Ok((Some((index, flags)), chain));
            }
            let metadata = self.headers[index].metadata.clone();
            next = metadata.parent().map(|name| self.load(name)).transpose()?;
        }
        Ok((None, chain))
    }
    fn interfaces(&mut self, classes: &[usize]) -> Result<HashMap<usize, Vec<usize>>> {
        let mut graph = HashMap::new();
        let mut active = HashSet::new();
        for &class in classes {
            let metadata = self.headers[class].metadata.clone();
            for name in metadata.interfaces() {
                let index = self.load(name)?;
                self.interface_visit(index, &mut graph, &mut active, 0)?;
            }
        }
        Ok(graph)
    }
    fn interface_visit(
        &mut self,
        index: usize,
        graph: &mut HashMap<usize, Vec<usize>>,
        active: &mut HashSet<usize>,
        depth: usize,
    ) -> Result<()> {
        self.step()?;
        if depth >= MAX_DEPTH {
            return Err(UnknownReason::ResourceLimit.into());
        }
        if active.contains(&index) || self.headers[index].flags & INTERFACE == 0 {
            return Err(UnknownReason::InvalidHierarchy.into());
        }
        if graph.contains_key(&index) {
            return Ok(());
        }
        active.insert(index);
        let metadata = self.headers[index].metadata.clone();
        let mut parents = Vec::with_capacity(metadata.interfaces().len());
        for name in metadata.interfaces() {
            let parent = self.load(name)?;
            self.interface_visit(parent, graph, active, depth + 1)?;
            parents.push(parent);
        }
        active.remove(&index);
        graph.insert(index, parents);
        Ok(())
    }
    fn maximal_method(&mut self, chain: &[usize]) -> Result<(usize, u16)> {
        let graph = self.interfaces(chain)?;
        let mut candidates = Vec::new();
        for &index in graph.keys() {
            if let Some(flags) = self.headers[index].method.flags()? {
                if flags & (PRIVATE | STATIC) == 0 {
                    candidates.push((index, flags));
                }
            }
        }
        let mut shadowed = HashSet::new();
        for &(index, _) in &candidates {
            let mut todo = graph[&index].clone();
            let mut visited = HashSet::new();
            while let Some(parent) = todo.pop() {
                self.step()?;
                if visited.insert(parent) {
                    shadowed.insert(parent);
                    todo.extend_from_slice(&graph[&parent]);
                }
            }
        }
        candidates.retain(|(index, _)| !shadowed.contains(index));
        let concrete: Vec<_> = candidates
            .iter()
            .copied()
            .filter(|(_, f)| f & ABSTRACT == 0)
            .collect();
        if concrete.len() == 1 {
            return Ok(concrete[0]);
        }
        match candidates.as_slice() {
            [one] => Ok(*one),
            [] => Err(UnknownReason::MissingMember.into()),
            _ => Err(UnknownReason::AmbiguousMember.into()),
        }
    }
    fn ordinary_method(&mut self, root: usize) -> Result<(usize, u16)> {
        if self.headers[root].flags & INTERFACE != 0 {
            if let Some(flags) = self.headers[root].method.flags()? {
                return Ok((root, flags));
            }
            let object = self.load("java/lang/Object")?;
            if self.headers[object].flags & INTERFACE != 0 {
                return Err(UnknownReason::InvalidHierarchy.into());
            }
            if let Some(flags) = self.headers[object].method.flags()? {
                if flags & PUBLIC != 0 && flags & STATIC == 0 {
                    return Ok((object, flags));
                }
            }
            self.maximal_method(&[root])
        } else {
            let (method, chain) = self.class_method(root)?;
            match method {
                Some(method) => Ok(method),
                None => self.maximal_method(&chain),
            }
        }
    }
    fn method(&mut self, kind: InvokeKind, caller: Option<&str>) -> Result<ResolvedMember> {
        let root = self.load(self.member.owner)?;
        if self.member.name == "<init>" || self.member.name == "<clinit>" {
            if self.member.name == "<init>"
                && (kind != InvokeKind::Special || self.headers[root].flags & INTERFACE != 0)
            {
                return Err(UnknownReason::InvocationMismatch.into());
            }
            if self.member.name == "<clinit>" && kind != InvokeKind::Static {
                return Err(UnknownReason::InvocationMismatch.into());
            }
            let flags = self.headers[root]
                .method
                .flags()?
                .ok_or(UnknownReason::MissingMember)?;
            return self.check_method(root, flags, kind);
        }
        if kind == InvokeKind::Interface && self.headers[root].flags & INTERFACE == 0 {
            return Err(UnknownReason::InvocationMismatch.into());
        }
        if kind == InvokeKind::Virtual && self.headers[root].flags & INTERFACE != 0 {
            return Err(UnknownReason::InvocationMismatch.into());
        }
        let (mut selected, mut flags) = self.ordinary_method(root)?;
        if kind == InvokeKind::Special && flags & PRIVATE == 0 {
            let caller = self.load(caller.ok_or(UnknownReason::CallerRequired)?)?;
            if root != caller {
                if self.headers[root].flags & INTERFACE != 0 {
                    if !self.headers[caller]
                        .metadata
                        .interfaces()
                        .any(|s| s == self.headers[root].metadata.name())
                    {
                        return Err(UnknownReason::InvocationMismatch.into());
                    }
                } else {
                    let chain = self.class_chain(caller, root)?;
                    if !chain.iter().skip(1).any(|&i| i == root) {
                        return Err(UnknownReason::InvocationMismatch.into());
                    }
                    if self.headers[caller].major >= 52 || self.headers[caller].flags & 0x0020 != 0
                    {
                        let parent = *chain.get(1).ok_or(UnknownReason::InvalidHierarchy)?;
                        (selected, flags) = self.ordinary_method(parent)?;
                    }
                }
            }
        }
        self.check_method(selected, flags, kind)
    }
    fn check_method(&self, index: usize, flags: u16, kind: InvokeKind) -> Result<ResolvedMember> {
        if (flags & STATIC != 0) != (kind == InvokeKind::Static) {
            return Err(UnknownReason::InvocationMismatch.into());
        }
        Ok(self.found(index, flags))
    }
    fn field_lookup(
        &mut self,
        index: usize,
        active: &mut HashSet<usize>,
        depth: usize,
    ) -> Result<Option<(usize, u16)>> {
        self.step()?;
        if depth >= MAX_DEPTH {
            return Err(UnknownReason::ResourceLimit.into());
        }
        if !active.insert(index) {
            return Err(UnknownReason::InvalidHierarchy.into());
        }
        if let Some(flags) = self.headers[index].field.flags()? {
            active.remove(&index);
            return Ok(Some((index, flags)));
        }
        let metadata = self.headers[index].metadata.clone();
        let mut matches = HashMap::new();
        for name in metadata.interfaces() {
            let interface = self.load(name)?;
            if self.headers[interface].flags & INTERFACE == 0 {
                return Err(UnknownReason::InvalidHierarchy.into());
            }
            if let Some((declared, flags)) = self.field_lookup(interface, active, depth + 1)? {
                matches.insert(declared, flags);
            }
        }
        let result = match matches.len() {
            0 => {
                // An interface's super_class is Object in its classfile, but
                // field resolution traverses only its superinterfaces.
                if self.headers[index].flags & INTERFACE != 0 {
                    None
                } else if let Some(parent) = metadata.parent() {
                    let parent = self.load(parent)?;
                    self.field_lookup(parent, active, depth + 1)?
                } else {
                    None
                }
            }
            1 => matches.into_iter().next(),
            _ => return Err(UnknownReason::AmbiguousMember.into()),
        };
        active.remove(&index);
        Ok(result)
    }
    fn field(&mut self, is_static: bool) -> Result<ResolvedMember> {
        let root = self.load(self.member.owner)?;
        let (declared, flags) = self
            .field_lookup(root, &mut HashSet::new(), 0)?
            .ok_or(UnknownReason::MissingMember)?;
        if (flags & STATIC != 0) != is_static {
            return Err(UnknownReason::InvocationMismatch.into());
        }
        Ok(self.found(declared, flags))
    }
}
fn finish(result: Result<ResolvedMember>) -> std::result::Result<Resolution, Error> {
    match result {
        Ok(member) => Ok(Resolution::Found(member)),
        Err(Failure::Unknown(reason)) => Ok(Resolution::Unknown(reason)),
        Err(Failure::Input(error)) => Err(error),
    }
}
pub fn resolve_method(
    member: MemberRef<'_>,
    kind: InvokeKind,
    caller: Option<&str>,
    loader: impl FnMut(&str) -> std::result::Result<Option<Arc<[u8]>>, Error>,
) -> std::result::Result<Resolution, Error> {
    finish(Resolver::new(member, checked_metadata(loader)).method(kind, caller))
}
pub fn resolve_field(
    member: MemberRef<'_>,
    is_static: bool,
    loader: impl FnMut(&str) -> std::result::Result<Option<Arc<[u8]>>, Error>,
) -> std::result::Result<Resolution, Error> {
    finish(Resolver::new(member, checked_metadata(loader)).field(is_static))
}
fn checked_metadata(
    mut loader: impl FnMut(&str) -> std::result::Result<Option<Arc<[u8]>>, Error>,
) -> impl FnMut(&str) -> Result<Option<Arc<ClassMetadata>>> {
    move |name| {
        loader(name)
            .map_err(Failure::Input)?
            .map(|bytes| {
                ClassMetadata::new(bytes, Limits::default())
                    .map(Arc::new)
                    .map_err(|_| Failure::Unknown(UnknownReason::InvalidClass))
            })
            .transpose()
    }
}
pub fn resolve_method_metadata(
    member: MemberRef<'_>,
    kind: InvokeKind,
    caller: Option<&str>,
    mut loader: impl FnMut(&str) -> std::result::Result<Option<Arc<ClassMetadata>>, Error>,
) -> std::result::Result<Resolution, Error> {
    finish(
        Resolver::new(member, move |name| loader(name).map_err(Failure::Input))
            .method(kind, caller),
    )
}
pub fn resolve_field_metadata(
    member: MemberRef<'_>,
    is_static: bool,
    mut loader: impl FnMut(&str) -> std::result::Result<Option<Arc<ClassMetadata>>, Error>,
) -> std::result::Result<Resolution, Error> {
    finish(Resolver::new(member, move |name| loader(name).map_err(Failure::Input)).field(is_static))
}

#[cfg(test)]
mod tests {
    use super::*;
    use binary::{CapturedClasspath, ClassLookup, ClasspathEntry, EntryKind};
    use selector_types::ContentHash;
    use sha2::{Digest, Sha256};
    use std::path::PathBuf;

    fn fixture() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/binary-resolution")
    }
    fn manifest() -> serde_json::Value {
        serde_json::from_str(include_str!(
            "../../../fixtures/binary-resolution/manifest.json"
        ))
        .unwrap()
    }
    fn loader(
        missing: Option<&'static str>,
        replacement: Option<(&'static str, &'static [u8])>,
    ) -> impl FnMut(&str) -> std::result::Result<Option<Arc<[u8]>>, Error> {
        let receipt = manifest();
        let digest = receipt["outputs"]
            .as_array()
            .unwrap()
            .iter()
            .find(|r| r["path"] == "resolution.jar")
            .unwrap()["sha256"]
            .as_str()
            .unwrap();
        let mut classpath = CapturedClasspath::new(
            vec![ClasspathEntry {
                path: fixture().join("resolution.jar"),
                sha256: ContentHash::from_hex(digest).unwrap(),
                kind: EntryKind::Jar,
            }],
            Limits::default(),
        )
        .unwrap();
        move |name| {
            if missing == Some(name) {
                return Ok(None);
            }
            if let Some((owner, bytes)) = replacement {
                if owner == name {
                    return Ok(Some(Arc::from(bytes)));
                }
            }
            match classpath
                .lookup(name)
                .map_err(|e| Error::Message(e.to_string()))?
            {
                ClassLookup::Found(class) => Ok(Some(Arc::from(class.bytes))),
                ClassLookup::Absent(_) => Ok(None),
            }
        }
    }
    fn method(
        owner: &str,
        name: &str,
        descriptor: &str,
        kind: InvokeKind,
        caller: Option<&str>,
    ) -> Resolution {
        resolve_method(
            MemberRef {
                owner,
                name,
                descriptor,
            },
            kind,
            caller,
            loader(None, None),
        )
        .unwrap()
    }
    fn field(owner: &str, name: &str) -> Resolution {
        resolve_field(
            MemberRef {
                owner,
                name,
                descriptor: "Ljava/lang/Object;",
            },
            true,
            loader(None, None),
        )
        .unwrap()
    }
    fn owner(result: Resolution) -> String {
        let Resolution::Found(member) = result else {
            panic!("expected exact member, got {result:?}");
        };
        member.declared_owner
    }
    #[test]
    fn genuine_outputs_and_jvm_declaring_owner_witness_are_sealed() {
        let manifest = manifest();
        for output in manifest["outputs"].as_array().unwrap() {
            let bytes = std::fs::read(fixture().join(output["path"].as_str().unwrap())).unwrap();
            assert_eq!(
                ContentHash(Sha256::digest(&bytes).into()).to_string(),
                output["sha256"].as_str().unwrap()
            );
            assert_eq!(bytes.len() as u64, output["bytes"].as_u64().unwrap());
        }
        assert_eq!(
            manifest["jvm_witness"],
            "inherited=fixture.ResolveBase\nstaticMethod=fixture.ResolveBase\nstaticField=fixture.ResolveBase\ndefaultMethod=fixture.DefaultOne\ndefaultResult=one\nsuperResult=mid\nfieldBeforeParent=fixture.FieldTop\nfieldOverride=fixture.FieldOverride\n"
        );
    }
    #[test]
    fn inherited_methods_and_fields_use_actual_declaring_class_and_exact_descriptor() {
        for (name, descriptor, kind) in [
            ("inherited", "()Ljava/lang/Object;", InvokeKind::Virtual),
            (
                "staticInherited",
                "()Ljava/lang/Object;",
                InvokeKind::Static,
            ),
            ("overload", "(I)Ljava/lang/Object;", InvokeKind::Virtual),
            (
                "overload",
                "(Ljava/lang/String;)Ljava/lang/Object;",
                InvokeKind::Virtual,
            ),
        ] {
            assert_eq!(
                owner(method("fixture/ResolveLeaf", name, descriptor, kind, None)),
                "fixture/ResolveBase"
            );
        }
        assert_eq!(
            owner(field("fixture/ResolveLeaf", "shared")),
            "fixture/ResolveBase"
        );
        assert_eq!(
            method(
                "fixture/ResolveLeaf",
                "overload",
                "(J)Ljava/lang/Object;",
                InvokeKind::Virtual,
                None
            ),
            Resolution::Unknown(UnknownReason::MissingMember)
        );
        assert_eq!(
            method(
                "fixture/ResolveLeaf",
                "staticInherited",
                "()Ljava/lang/Object;",
                InvokeKind::Virtual,
                None
            ),
            Resolution::Unknown(UnknownReason::InvocationMismatch)
        );
        assert_eq!(
            resolve_field(
                MemberRef {
                    owner: "fixture/ResolveLeaf",
                    name: "shared",
                    descriptor: "Ljava/lang/Object;"
                },
                false,
                loader(None, None)
            )
            .unwrap(),
            Resolution::Unknown(UnknownReason::InvocationMismatch)
        );
    }
    #[test]
    fn constructors_never_inherit_and_special_super_selection_starts_at_direct_parent() {
        assert_eq!(
            owner(method(
                "fixture/ResolveLeaf",
                "<init>",
                "()V",
                InvokeKind::Special,
                None
            )),
            "fixture/ResolveLeaf"
        );
        assert_eq!(
            method(
                "fixture/ResolveLeaf",
                "<init>",
                "(Ljava/lang/Object;)V",
                InvokeKind::Special,
                None
            ),
            Resolution::Unknown(UnknownReason::MissingMember)
        );
        // The independently executed super-call returns "mid". This explicit
        // symbolic-owner control also checks ACC_SUPER with an older ancestor.
        assert_eq!(
            owner(method(
                "fixture/ResolveBase",
                "ping",
                "()Ljava/lang/Object;",
                InvokeKind::Special,
                Some("fixture/ResolveLeaf")
            )),
            "fixture/ResolveMid"
        );
        assert_eq!(
            method(
                "fixture/ResolveBase",
                "ping",
                "()Ljava/lang/Object;",
                InvokeKind::Special,
                None
            ),
            Resolution::Unknown(UnknownReason::CallerRequired)
        );
        assert_eq!(
            owner(method(
                "fixture/DefaultOne",
                "choose",
                "()Ljava/lang/Object;",
                InvokeKind::Special,
                Some("fixture/DefaultLeaf")
            )),
            "fixture/DefaultOne"
        );
    }
    #[test]
    fn maximally_specific_default_and_interface_object_method_are_exact() {
        assert_eq!(
            owner(method(
                "fixture/DefaultLeaf",
                "choose",
                "()Ljava/lang/Object;",
                InvokeKind::Virtual,
                None
            )),
            "fixture/DefaultOne"
        );
        assert_eq!(
            owner(method(
                "fixture/DefaultOne",
                "toString",
                "()Ljava/lang/String;",
                InvokeKind::Interface,
                None
            )),
            "java/lang/Object"
        );
        assert_eq!(
            method(
                "fixture/DefaultOne",
                "staticOnly",
                "()Ljava/lang/Object;",
                InvokeKind::Static,
                None
            ),
            Resolution::Unknown(UnknownReason::MissingMember)
        );
        assert_eq!(
            owner(method(
                "fixture/DefaultTop",
                "staticOnly",
                "()Ljava/lang/Object;",
                InvokeKind::Static,
                None
            )),
            "fixture/DefaultTop"
        );
    }
    #[test]
    fn field_lookup_prioritizes_own_declaration_then_interfaces_then_superclass() {
        assert_eq!(
            owner(field("fixture/FieldLeaf", "shared")),
            "fixture/FieldTop"
        );
        assert_eq!(
            owner(field("fixture/FieldBeforeParent", "shared")),
            "fixture/FieldTop"
        );
        assert_eq!(
            owner(field("fixture/FieldOverride", "shared")),
            "fixture/FieldOverride"
        );
        assert_eq!(
            field("fixture/FieldBoth", "shared"),
            Resolution::Unknown(UnknownReason::AmbiguousMember)
        );
    }
    #[test]
    fn ambiguity_missing_hierarchy_and_named_cyclic_control_remain_unknown() {
        assert_eq!(
            method(
                "fixture/AbstractLeaf",
                "choose",
                "()Ljava/lang/Object;",
                InvokeKind::Virtual,
                None
            ),
            Resolution::Unknown(UnknownReason::AmbiguousMember)
        );
        let member = MemberRef {
            owner: "fixture/DefaultLeaf",
            name: "choose",
            descriptor: "()Ljava/lang/Object;",
        };
        let ambiguous =
            include_bytes!("../../../fixtures/binary-resolution/controls/ambiguous-default.class");
        assert_eq!(
            resolve_method(
                member,
                InvokeKind::Virtual,
                None,
                loader(None, Some(("fixture/DefaultLeaf", ambiguous)))
            )
            .unwrap(),
            Resolution::Unknown(UnknownReason::AmbiguousMember)
        );
        let cyclic =
            include_bytes!("../../../fixtures/binary-resolution/controls/cyclic-interface.class");
        assert_eq!(
            resolve_method(
                member,
                InvokeKind::Virtual,
                None,
                loader(None, Some(("fixture/DefaultOne", cyclic)))
            )
            .unwrap(),
            Resolution::Unknown(UnknownReason::InvalidHierarchy)
        );
        assert_eq!(
            resolve_method(
                member,
                InvokeKind::Virtual,
                None,
                loader(Some("java/lang/Object"), None)
            )
            .unwrap(),
            Resolution::Unknown(UnknownReason::MissingClass)
        );
        let member = MemberRef {
            owner: "fixture/ResolveLeaf",
            name: "inherited",
            descriptor: "()Ljava/lang/Object;",
        };
        assert_eq!(
            resolve_method(
                member,
                InvokeKind::Virtual,
                None,
                loader(Some("fixture/ResolveBase"), None)
            )
            .unwrap(),
            Resolution::Unknown(UnknownReason::MissingClass)
        );
        assert_eq!(
            resolve_method(member, InvokeKind::Virtual, None, |_| Err(Error::Invalid(
                "changed captured classpath"
            )))
            .unwrap_err()
            .to_string(),
            Error::Invalid("changed captured classpath").to_string()
        );
    }
    #[test]
    fn shared_metadata_reuses_headers_without_coalescing_invocation_or_caller_rules() {
        let mut bytes = loader(None, None);
        let mut cache = HashMap::<String, Arc<ClassMetadata>>::new();
        let builds = std::cell::Cell::new(0usize);
        let mut metadata = |name: &str| -> std::result::Result<Option<Arc<ClassMetadata>>, Error> {
            if let Some(class) = cache.get(name) {
                return Ok(Some(class.clone()));
            }
            let Some(bytes) = bytes(name)? else {
                return Ok(None);
            };
            let class = Arc::new(ClassMetadata::new(bytes, Limits::default()).unwrap());
            cache.insert(name.to_owned(), class.clone());
            builds.set(builds.get() + 1);
            Ok(Some(class))
        };
        let cases = [
            (
                "fixture/ResolveLeaf",
                "inherited",
                InvokeKind::Virtual,
                None,
                Resolution::Found(ResolvedMember {
                    declared_owner: "fixture/ResolveBase".into(),
                    flags: PUBLIC,
                }),
            ),
            (
                "fixture/ResolveLeaf",
                "staticInherited",
                InvokeKind::Static,
                None,
                Resolution::Found(ResolvedMember {
                    declared_owner: "fixture/ResolveBase".into(),
                    flags: PUBLIC | STATIC,
                }),
            ),
            (
                "fixture/ResolveLeaf",
                "staticInherited",
                InvokeKind::Virtual,
                None,
                Resolution::Unknown(UnknownReason::InvocationMismatch),
            ),
            (
                "fixture/ResolveBase",
                "ping",
                InvokeKind::Special,
                Some("fixture/ResolveLeaf"),
                Resolution::Found(ResolvedMember {
                    declared_owner: "fixture/ResolveMid".into(),
                    flags: PUBLIC,
                }),
            ),
            (
                "fixture/ResolveBase",
                "ping",
                InvokeKind::Special,
                None,
                Resolution::Unknown(UnknownReason::CallerRequired),
            ),
        ];
        let mut warm_builds = 0;
        for iteration in 0..100 {
            for (owner, name, kind, caller, expected) in &cases {
                let actual = resolve_method_metadata(
                    MemberRef {
                        owner,
                        name,
                        descriptor: "()Ljava/lang/Object;",
                    },
                    *kind,
                    *caller,
                    &mut metadata,
                )
                .unwrap();
                assert_eq!(&actual, expected);
            }
            let field = resolve_field_metadata(
                MemberRef {
                    owner: "fixture/ResolveLeaf",
                    name: "shared",
                    descriptor: "Ljava/lang/Object;",
                },
                true,
                &mut metadata,
            )
            .unwrap();
            assert_eq!(owner(field), "fixture/ResolveBase");
            if iteration == 0 {
                warm_builds = builds.get();
            } else {
                assert_eq!(
                    builds.get(),
                    warm_builds,
                    "repeated resolution must not request new parsed owners"
                );
            }
        }
        assert_eq!(builds.get(), 3);
    }
    #[test]
    fn metadata_entrypoints_keep_missing_wrong_owner_and_provider_failures_distinct() {
        let member = MemberRef {
            owner: "fixture/ResolveLeaf",
            name: "inherited",
            descriptor: "()Ljava/lang/Object;",
        };
        assert_eq!(
            resolve_method_metadata(member, InvokeKind::Virtual, None, |_| Ok(None)).unwrap(),
            Resolution::Unknown(UnknownReason::MissingClass)
        );
        let base = Arc::new(
            ClassMetadata::new(
                loader(None, None)("fixture/ResolveBase").unwrap().unwrap(),
                Limits::default(),
            )
            .unwrap(),
        );
        assert_eq!(
            resolve_method_metadata(member, InvokeKind::Virtual, None, |_| Ok(Some(
                base.clone()
            )))
            .unwrap(),
            Resolution::Unknown(UnknownReason::InvalidClass)
        );
        assert_eq!(
            resolve_method_metadata(member, InvokeKind::Virtual, None, |_| Err(Error::Invalid(
                "changed provider"
            )))
            .unwrap_err()
            .to_string(),
            Error::Invalid("changed provider").to_string()
        );
        assert_eq!(
            resolve_method(member, InvokeKind::Virtual, None, |_| Ok(Some(Arc::from(
                [0u8]
            ))))
            .unwrap(),
            Resolution::Unknown(UnknownReason::InvalidClass)
        );
    }
}
