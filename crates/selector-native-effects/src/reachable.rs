//! Bounded exact dependency work. Metadata-only subjects never execute here.
use super::*;
use std::collections::VecDeque;

#[derive(Clone, Copy, Debug)]
pub struct RootMethodDemand<'a> {
    pub authority: u32,
    pub owner: &'a str,
    pub name: &'a str,
    pub descriptor: &'a str,
}
#[derive(Clone, Copy, Debug)]
pub struct ReachabilityLimits {
    pub projection: Limits,
    pub max_method_work: usize,
    pub max_instruction_work: usize,
}
impl Default for ReachabilityLimits {
    fn default() -> Self {
        Self {
            projection: Limits::default(),
            max_method_work: 200_000,
            max_instruction_work: 16 << 20,
        }
    }
}
struct Queue {
    heads: Vec<u32>,
    tails: Vec<u32>,
    next: Vec<u32>,
    seen: Vec<bool>,
    classes: VecDeque<u32>,
}
impl Queue {
    fn new() -> Self {
        Self {
            heads: Vec::new(),
            tails: Vec::new(),
            next: Vec::new(),
            seen: Vec::new(),
            classes: VecDeque::new(),
        }
    }
    fn push(&mut self, b: &Builder<'_, '_>, id: effects::MethodId) {
        let Some(row) = b.function(id) else { return };
        if !matches!(
            row.kind,
            ForeignKind::Method | ForeignKind::ClassInitialization
        ) {
            return;
        }
        let method = id.0 as usize;
        self.next.resize(b.out.data.methods.len(), NONE);
        self.seen.resize(b.out.data.methods.len(), false);
        if self.seen[method] {
            return;
        }
        self.seen[method] = true;
        self.heads.resize(b.out.classes.len(), NONE);
        self.tails.resize(b.out.classes.len(), NONE);
        let class = row.class as usize;
        if self.heads[class] == NONE {
            self.heads[class] = id.0;
            self.classes.push_back(row.class);
        } else {
            self.next[self.tails[class] as usize] = id.0;
        }
        self.tails[class] = id.0;
    }
    fn bytes(&self) -> usize {
        (self.heads.capacity() + self.tails.capacity() + self.next.capacity()) * 4
            + self.seen.capacity()
            + self.classes.capacity() * 4
    }
    fn pop(&mut self, class: u32) -> Option<effects::MethodId> {
        let head = self.heads[class as usize];
        if head == NONE {
            return None;
        }
        self.heads[class as usize] = self.next[head as usize];
        if self.heads[class as usize] == NONE {
            self.tails[class as usize] = NONE;
        }
        Some(effects::MethodId(head))
    }
}
impl<'a, 'p> Builder<'a, 'p> {
    fn demand(&mut self, demand: RootMethodDemand<'a>) -> Result<effects::MethodId, Error> {
        if demand.authority == NONE
            || demand.owner.is_empty()
            || demand.owner.len() > u16::MAX as usize
            || demand.name.is_empty()
        {
            return Err(Error::Binding);
        }
        let owner = self.input(demand.owner);
        let name = self.input(demand.name);
        let desc = self.input(demand.descriptor);
        let class = self.class(demand.authority, owner)?;
        self.method(class, ForeignKind::Method, name, desc)
    }
    /// Numeric class ID makes all text borrow from retained blobs/input storage.
    fn load_class(
        &mut self,
        class_id: u32,
        provider: &mut impl ClassProvider,
    ) -> Result<bool, Error> {
        if self.out.classes[class_id as usize].blob != NONE {
            return Ok(true);
        }
        let row = self.out.classes[class_id as usize];
        let provided = provider.class(ClassDemand {
            authority: row.authority,
            owner: self.text(row.owner),
        })?;
        let Some(provided) = provided else {
            return Ok(false);
        };
        if provided.authority != row.authority || provided.provider == NONE {
            return Err(Error::Binding);
        }
        if self
            .class_bytes
            .checked_add(provided.bytes.len())
            .is_none_or(|bytes| bytes > self.limits.class_bytes)
        {
            return Err(Error::Budget);
        }
        if <[u8; 32]>::from(Sha256::digest(&provided.bytes)) != provided.class_sha256 {
            return Err(Error::ClassHash);
        }
        let metadata = Arc::new(binary::ClassMetadata::new(
            provided.bytes.clone(),
            self.limits.binary,
        )?);
        if metadata.name() != self.text(row.owner) {
            return Err(Error::ClassOwner);
        }
        let blob = self.out.blobs.len() as u32;
        self.class_bytes += provided.bytes.len();
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
        self.check()?;
        Ok(true)
    }
    fn owned_class(&mut self, authority: u32, owner: Arc<str>) -> Result<u32, Error> {
        let key = digest(&[&authority.to_le_bytes(), owner.as_bytes()]);
        let mut next = self.postings.classes.get(&key).copied().unwrap_or(NONE);
        while next != NONE {
            let row = self.out.classes[next as usize];
            if row.authority == authority && self.text(row.owner) == owner.as_ref() {
                return Ok(next);
            }
            next = self.postings.class_next[next as usize];
        }
        let index = self.out.owned_text.len() as u32;
        let len = owner.len() as u32;
        self.owned_text_bytes = self
            .owned_text_bytes
            .checked_add(owner.len())
            .ok_or(Error::Budget)?;
        self.out.owned_text.push(owner);
        self.class(
            authority,
            TextRef {
                source: TextSource::Owned,
                index,
                start: 0,
                len,
            },
        )
    }
}
/// Projects exact roots and their static/special/lifecycle dependencies. Other
/// known subjects remain explicit ALL-TOP placeholders, including changed-file
/// metadata-only seeds. No classpath universe scan or virtual closure is claimed.
pub fn produce_reachable<'a>(
    roots: &'a [RootMethodDemand<'a>],
    metadata_only: &'a [RootMethodDemand<'a>],
    provider: &mut impl ClassProvider,
    limits: ReachabilityLimits,
    axiom: Option<&RuntimeAxiom>,
) -> Result<Produced<'a>, Error> {
    if limits.projection.references >= NONE as usize
        || limits.projection.rows >= NONE as usize
        || limits.projection.classes >= NONE as usize
    {
        return Err(Error::Budget);
    }
    if roots
        .len()
        .checked_add(metadata_only.len())
        .is_none_or(|n| n > limits.projection.references)
    {
        return Err(Error::Budget);
    }
    let mut b = Builder::new(limits.projection, axiom);
    let mut queue = Queue::new();
    for &demand in roots {
        let id = b.demand(demand)?;
        b.out.roots.push(id);
        queue.push(&b, id);
    }
    for &demand in metadata_only {
        b.demand(demand)?;
    }
    b.queue_bytes = queue.bytes();
    b.check()?;
    let mut work = 0usize;
    let mut instructions = 0usize;
    // Missing lookups are remembered once. Their methods already exist as TOP.
    let mut unavailable = Vec::<bool>::new();
    while let Some(class_id) = queue.classes.pop_front() {
        if queue.heads[class_id as usize] == NONE {
            continue;
        }
        unavailable.resize(b.out.classes.len(), false);
        if unavailable[class_id as usize] || !b.load_class(class_id, provider)? {
            unavailable[class_id as usize] = true;
            while let Some(id) = queue.pop(class_id) {
                b.out.open.push(OpenSite {
                    method: id,
                    pc: 0,
                    reason: OpenReason::MissingClass,
                });
            }
            continue;
        }
        let class_row = b.out.classes[class_id as usize];
        let blob = class_row.blob;
        let metadata = b.out.blobs[blob as usize].metadata.clone();
        let bytes = b.out.blobs[blob as usize].bytes.clone();
        // One CP parse per class batch, never one full index rebuild per unit.
        let class = binary::parse_class(&bytes, b.limits.binary)?;
        binary::diagnostic::validate_constant_pool(&class)?;
        while let Some(id) = queue.pop(class_id) {
            if b.out.projected[id.0 as usize] {
                continue;
            }
            let foreign = b.function(id).expect("queued foreign subject");
            if work >= limits.max_method_work {
                b.out.open.push(OpenSite {
                    method: id,
                    pc: 0,
                    reason: OpenReason::AdmissionBudget,
                });
                continue;
            }
            work += 1;
            if foreign.kind == ForeignKind::ClassInitialization {
                // Phase stays ALL-TOP with empty DTO ranges. Lifecycle evidence
                // is a separate exact sidecar, never a phony JVM method body.
                let start = b.out.data.initializes.len();
                if let Ok(method) = metadata.method("<clinit>", Some("()V")) {
                    let name = b.borrowed(blob, method.name)?;
                    let descriptor = b.borrowed(blob, method.descriptor)?;
                    let target = b.method(class_id, ForeignKind::Method, name, descriptor)?;
                    b.out.data.initializes.push(target);
                    queue.push(&b, target);
                }
                for owner in metadata.parent().into_iter().chain(metadata.interfaces()) {
                    let owner = b.borrowed(blob, owner)?;
                    let parent = b.class(class_row.authority, owner)?;
                    let phase = b.method(
                        parent,
                        ForeignKind::ClassInitialization,
                        TextRef::builtin(0),
                        TextRef::builtin(1),
                    )?;
                    b.out.data.initializes.push(phase);
                    queue.push(&b, phase);
                }
                let index = b.out.data.methods[id.0 as usize].subject.index;
                b.out.phases[index as usize].dependencies =
                    range(start, b.out.data.initializes.len());
                b.out.data.methods[id.0 as usize].initializes =
                    range(start, b.out.data.initializes.len());
                b.queue_bytes = queue.bytes() + unavailable.capacity();
                b.check()?;
                continue;
            }
            let method =
                match metadata.method(b.text(foreign.name), Some(b.text(foreign.descriptor))) {
                    Ok(method) => method,
                    Err(error) if error.kind == binary::ErrorKind::MissingMethod => {
                        b.out.open.push(OpenSite {
                            method: id,
                            pc: 0,
                            reason: OpenReason::MissingCode,
                        });
                        continue;
                    }
                    Err(error) => return Err(error.into()),
                };
            let cost = method.code.map_or(0, <[u8]>::len);
            if instructions
                .checked_add(cost)
                .is_none_or(|n| n > limits.max_instruction_work)
            {
                b.out.open.push(OpenSite {
                    method: id,
                    pc: 0,
                    reason: OpenReason::AdmissionBudget,
                });
                continue;
            }
            instructions += cost;
            b.emit_method(blob, class_id, &class, &method, id)?;
            let row = b.out.data.methods[id.0 as usize];
            for index in row.calls.checked(b.out.data.calls.len())? {
                let call = b.out.data.calls[index];
                if !matches!(
                    call.kind,
                    effects::CallKind::Static | effects::CallKind::Special
                ) {
                    continue;
                }
                let effects::CallTarget::Direct(mut target) = call.target else {
                    continue;
                };
                let raw = *b.out.foreign(target).expect("native direct target");
                let target_class = b.out.classes[raw.class as usize];
                let member = MemberRef {
                    owner: b.text(target_class.owner),
                    name: b.text(raw.name),
                    descriptor: b.text(raw.descriptor),
                };
                let kind = if call.kind == effects::CallKind::Static {
                    binary::InvokeKind::Static
                } else {
                    binary::InvokeKind::Special
                };
                let declared = provider.declaration(
                    target_class.authority,
                    member,
                    kind,
                    Some(metadata.name()),
                )?;
                if let Some(owner) = declared {
                    let declared_class = b.owned_class(target_class.authority, owner)?;
                    target = b.method(
                        declared_class,
                        ForeignKind::Method,
                        raw.name,
                        raw.descriptor,
                    )?;
                    b.out.data.calls[index].target = effects::CallTarget::Direct(target);
                }
                queue.push(&b, target);
            }
            for index in row.initializes.checked(b.out.data.initializes.len())? {
                queue.push(&b, b.out.data.initializes[index]);
            }
            b.queue_bytes = queue.bytes() + unavailable.capacity();
            b.check()?;
        }
    }
    b.check()?;
    effects::validate(
        &b.out.data,
        b.out.bounds(),
        effects::Limits {
            max_methods: limits.projection.references,
            max_rows: limits.projection.rows,
            max_bytes: limits.projection.retained_bytes,
        },
    )?;
    Ok(b.out)
}
