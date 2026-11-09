//! JVM implementations of inherited abstract members omitted from source facts.
//!
//! Compiler-bound source products and constructor-proven native allocations
//! select candidates. Exact admitted superclass declarations supply member names,
//! descriptors, flags, bodies and fields; no Scala member identity is invented.
use super::*;

const VERSION: &[u8] = b"binary-generated-members/6-trusted-data-property-coverage";

fn abstract_instance(key: &MethodKey, data: &MethodData) -> bool {
    data.receiver_parameter.is_none()
        && data.flags & 0x0400 != 0
        && data.flags & (0x0002 | 0x0008) == 0
        && !matches!(key.name.as_str(), "<init>" | "<clinit>" | "$init$")
}

struct ConcreteClass {
    context: usize,
    owner: String,
    symbol: SymbolId,
    source_product: bool,
    inherited_owners: Option<Vec<String>>,
    next_contract: usize,
    queued: bool,
}

struct ContractProof {
    cross_context: bool,
    symbol: SymbolId,
    hash: ContentHash,
    flags: u16,
}
#[derive(Default)]
struct AbiAliases {
    methods: Vec<(SymbolId, ContentHash)>,
    unproved: bool,
}
fn exact_contract(class: &binary::ClassMetadata, key: &MethodKey, flags: u16) -> bool {
    class.name() == key.owner
        && flags & (0x0001 | 0x0002 | 0x0008 | 0x0400) == 0x0401
        && class
            .method(&key.name, Some(&key.descriptor))
            .is_ok_and(|m| m.flags == flags)
}
fn contract_proof(
    facts: &FactSnapshot,
    context: &AdmittedContext,
    key: &MethodKey,
    data: &MethodData,
    conflicts: &HashSet<SymbolId>,
) -> Option<ContractProof> {
    let CachedClass::Found(class) = context.classes.get(&key.owner)? else {
        return None;
    };
    let declaration = facts.symbols[data.symbol.index()];
    if declaration.context != context.id
        || declaration.owner != data.owner
        || facts.symbols[data.owner.index()].context != context.id
        || !abstract_instance(key, data)
        || declaration.file.is_none()
        || facts.files[declaration.file.index()].flags & FILE_BINARY_SOURCE == 0
        || facts.files[declaration.file.index()].source_hash != class.hash
        || class.hash == ContentHash::default()
        || class.metadata.hash() != class.hash
        || !exact_contract(&class.metadata, key, data.flags)
        || declaration.flags & (SYMBOL_DEFINED | SYMBOL_NATIVE_BINARY) != SYMBOL_NATIVE_BINARY
        || conflicts.contains(&data.symbol)
        || conflicts.contains(&data.owner)
    {
        return None;
    }
    Some(ContractProof {
        cross_context: true,
        symbol: data.symbol,
        hash: class.hash,
        flags: data.flags,
    })
}

struct RefusedCandidate {
    class: usize,
    contract: usize,
    provider: Arc<ClassBytes>,
}

/// Stage-local indexes shared by bounded discovery waves. Existing classes only
/// examine newly admitted contracts; newly allocated classes examine all known
/// contracts. No classpath inventory or unallocated implementation is scanned.
pub(super) struct Discovery {
    classes: Vec<ConcreteClass>,
    known_classes: HashMap<usize, HashSet<String>>,
    queues: Vec<VecDeque<usize>>,
    /// Exact compiler target IDs used on lexical `this`, indexed once before
    /// binary lowering. No source name, formal count or runtime type guess.
    this_requests: Vec<(SymbolId, usize)>,
    requested: Vec<VecDeque<(usize, usize)>>,
    requested_count: usize,
    /// Successful exact lookup, published only after the selected body exists
    /// and final contextual symbol facets have been checked.
    covered_requests: Vec<(SymbolId, SymbolId, SymbolId)>,
    next_context: usize,
    loaders: Vec<Option<CapturedClasspath>>,
    receiver_owners: HashMap<String, Vec<usize>>,
    aliases: HashMap<String, HashMap<String, AbiAliases>>,
    refused: Vec<RefusedCandidate>,
    refused_per_context: Vec<usize>,
    contracts: Vec<MethodKey>,
    known_contracts: HashSet<MethodKey>,
    contract_owners: HashMap<String, Vec<usize>>,
    contract_proofs: Vec<ContractProof>,
    source_members: HashMap<String, HashSet<String>>,
    links: HashSet<(SymbolId, SymbolId)>,
    conflicts: HashSet<SymbolId>,
}
impl Discovery {
    pub(super) fn new(facts: &FactSnapshot, inputs: &OwnedBinaryInputs) -> Self {
        let mut classes: Vec<_> = inputs
            .types
            .iter()
            .filter_map(|((context, owner), &symbol)| {
                let declaration = facts.symbols[symbol.index()];
                (declaration.flags & SYMBOL_DEFINED != 0
                    && declaration.kind == 13
                    && !declaration.file.is_none()
                    && facts.files[declaration.file.index()].flags
                        & (SOURCE_VERIFIED | SYNTAX_VERIFIED | FILE_BINARY_SOURCE)
                        == SOURCE_VERIFIED | SYNTAX_VERIFIED
                    && facts.files[declaration.file.index()].context == declaration.context
                    && selector_types::symbol::jvm_owner(facts.symbol_name(symbol)).as_deref()
                        == Some(owner.as_str()))
                .then(|| ConcreteClass {
                    context: *context,
                    owner: owner.clone(),
                    symbol,
                    source_product: true,
                    inherited_owners: None,
                    next_contract: 0,
                    queued: true,
                })
            })
            .collect();
        classes.sort_unstable_by(|a, b| {
            (a.context, &a.owner, a.symbol).cmp(&(b.context, &b.owner, b.symbol))
        });
        let mut known_classes: HashMap<usize, HashSet<String>> = HashMap::new();
        for class in &classes {
            known_classes
                .entry(class.context)
                .or_default()
                .insert(class.owner.clone());
        }
        // Source declarations win on every mapped class in the superclass
        // chain, even if their Scala signature cannot be erased. Names are
        // indexed once, not copied for every descendant or discovery wave.
        let mut source_members: HashMap<String, HashSet<String>> = HashMap::new();
        for declaration in &facts.symbols {
            if declaration.flags & SYMBOL_DEFINED == 0 || declaration.owner.is_none() {
                continue;
            }
            let owner = facts.symbols[declaration.owner.index()];
            if !matches!(owner.kind, 10 | 13 | 14)
                || owner.flags & SYMBOL_DEFINED == 0
                || owner.file.is_none()
                || facts.files[owner.file.index()].flags & SOURCE_VERIFIED == 0
            {
                continue;
            }
            if let (Some(owner), Some(name)) = (
                selector_types::symbol::jvm_owner(facts.symbol_name(declaration.owner)),
                selector_types::symbol::member_name(facts.text(declaration.name))
                    .and_then(selector_types::symbol::jvm_name),
            ) {
                // Negative precedence is deliberately conservative across source
                // contexts. This does not alias their classes, fields or methods.
                source_members.entry(owner).or_default().insert(name);
            }
        }
        let queues = (0..inputs.contexts.len())
            .map(|context| {
                classes
                    .iter()
                    .enumerate()
                    .filter_map(|(id, class)| (class.context == context).then_some(id))
                    .collect()
            })
            .collect();
        let this_requests = compiler_this_requests(facts, &classes);
        Self {
            classes,
            known_classes,
            queues,
            this_requests,
            requested: (0..inputs.contexts.len())
                .map(|_| VecDeque::new())
                .collect(),
            requested_count: 0,
            covered_requests: Vec::new(),
            next_context: 0,
            loaders: (0..inputs.contexts.len()).map(|_| None).collect(),
            receiver_owners: HashMap::new(),
            aliases: HashMap::new(),
            refused: Vec::new(),
            refused_per_context: vec![0; inputs.contexts.len()],
            contracts: Vec::new(),
            known_contracts: HashSet::new(),
            contract_owners: HashMap::new(),
            contract_proofs: Vec::new(),
            source_members,
            conflicts: facts
                .issues
                .iter()
                .filter(|i| i.kind == IssueKind::ContextConflict)
                .map(|i| i.symbol)
                .collect(),
            links: facts
                .relations
                .iter()
                .filter(|r| r.kind == RelationKind::Override)
                .map(|r| (r.source, r.target))
                .collect(),
        }
    }

    /// Called only after NEW has an exact admitted constructor target. Merely
    /// reading a header, returning a declared type or encountering an interface
    /// never expands the set of concrete native dispatch receivers. Source
    /// classes must retain the stronger own-product authority established above.
    pub(super) fn allocation(
        &mut self,
        facts: &FactSnapshot,
        context: usize,
        owner: &str,
        symbol: SymbolId,
    ) {
        let declaration = facts.symbols[symbol.index()];
        if declaration.flags & SYMBOL_DEFINED != 0
            || declaration.flags & SYMBOL_JVM_CLASS_HEADER_VERIFIED == 0
            || self
                .known_classes
                .get(&context)
                .is_some_and(|owners| owners.contains(owner))
        {
            return;
        }
        self.known_classes
            .entry(context)
            .or_default()
            .insert(owner.to_owned());
        self.queues[context].push_back(self.classes.len());
        self.classes.push(ConcreteClass {
            context,
            owner: owner.to_owned(),
            symbol,
            source_product: false,
            inherited_owners: None,
            next_contract: 0,
            queued: true,
        });
    }

    /// Consume each successful Registry declaration once. ABI postings own
    /// strings once per distinct ABI, never once per receiver or scheduling unit.
    fn refresh(
        &mut self,
        facts: &FactSnapshot,
        inputs: &OwnedBinaryInputs,
        registry: &mut Registry,
    ) {
        let mut contracts = Vec::new();
        for event in registry.method_events.drain(..) {
            let method = event.class.metadata.methods().nth(event.ordinal).unwrap();
            if event.data.flags & (0x0002 | 0x0008) == 0
                && !matches!(method.name, "<init>" | "<clinit>" | "$init$")
            {
                if !self.aliases.contains_key(method.name) {
                    self.aliases.insert(method.name.into(), HashMap::new());
                }
                let descriptors = self.aliases.get_mut(method.name).unwrap();
                if !descriptors.contains_key(method.descriptor) {
                    descriptors.insert(method.descriptor.into(), AbiAliases::default());
                }
                let group = descriptors.get_mut(method.descriptor).unwrap();
                if event.class.hash != ContentHash::default()
                    && event.class.metadata.hash() == event.class.hash
                    && method.flags == event.data.flags
                {
                    group.methods.push((event.data.symbol, event.class.hash));
                } else {
                    group.unproved = true;
                }
            }
            if event.data.receiver_parameter.is_none()
                && event.data.flags & (0x0002 | 0x0008) == 0
                && !matches!(method.name, "<init>" | "<clinit>" | "$init$")
                && (event.data.flags & 0x0400 != 0
                    || self
                        .this_requests
                        .binary_search_by_key(&event.data.symbol, |r| r.0)
                        .is_ok())
            {
                contracts.push((
                    MethodKey {
                        context: event.context,
                        owner: event.class.metadata.name().into(),
                        name: method.name.into(),
                        descriptor: method.descriptor.into(),
                    },
                    event.data,
                ));
            }
        }
        contracts.sort_unstable_by(|(a, _), (b, _)| {
            (a.context, &a.owner, &a.name, &a.descriptor).cmp(&(
                b.context,
                &b.owner,
                &b.name,
                &b.descriptor,
            ))
        });
        for (key, data) in contracts {
            if !self.known_contracts.insert(key.clone()) {
                continue;
            }
            let proof = contract_proof(
                facts,
                &inputs.contexts[key.context],
                &key,
                &data,
                &self.conflicts,
            )
            .unwrap_or(ContractProof {
                cross_context: false,
                symbol: data.symbol,
                hash: ContentHash::default(),
                flags: data.flags,
            });
            if data.flags & 0x0400 != 0 {
                // Concrete members enter only exact requested pairs, never the
                // opportunistic receiver-by-inherited-contract inventory.
                self.contract_owners
                    .entry(key.owner.clone())
                    .or_default()
                    .push(self.contracts.len());
                // Only receivers whose admitted positive ancestry contains
                // this owner need waking for optional abstract discovery.
                if let Some(receivers) = self.receiver_owners.get(&key.owner) {
                    for &id in receivers {
                        let class = &mut self.classes[id];
                        if !class.queued {
                            class.queued = true;
                            self.queues[class.context].push_back(id);
                        }
                    }
                }
            }
            self.contracts.push(key);
            self.contract_proofs.push(proof);
            let id = self.contracts.len() - 1;
            let target = self.contract_proofs[id].symbol;
            let start = self.this_requests.partition_point(|row| row.0 < target);
            let end = self.this_requests.partition_point(|row| row.0 <= target);
            for &(_, class) in &self.this_requests[start..end] {
                // Priority is bounded scheduling state, never coverage. Every
                // omitted priority still has the ordinary discovery cursor.
                if self.requested_count >= MAX_METHODS {
                    break;
                }
                self.requested[self.classes[class].context].push_back((class, id));
                self.requested_count += 1;
            }
        }
    }

    fn prepare_class(
        &mut self,
        id: usize,
        facts: &mut FactSnapshot,
        inputs: &mut OwnedBinaryInputs,
    ) -> Result<bool, Error> {
        let concrete = &mut self.classes[id];
        if self.conflicts.contains(&concrete.symbol) {
            return Ok(false);
        }
        if concrete.inherited_owners.is_some() {
            return Ok(true);
        }
        let context = &mut inputs.contexts[concrete.context];
        if context.id != facts.symbols[concrete.symbol.index()].context {
            return Err(Error::Invalid("generated JVM member compiler context"));
        }
        if self.loaders[concrete.context].is_none() {
            self.loaders[concrete.context] = Some(context_loader(context, &inputs.admitted)?);
        }
        let loader = self.loaders[concrete.context].as_mut().unwrap();
        let guard_file = facts.symbols[concrete.symbol.index()].file;
        let Some(bytes) = guarded_class(
            facts,
            context,
            loader,
            &concrete.owner,
            concrete.symbol,
            guard_file,
        )?
        else {
            return Ok(false);
        };
        let class = bytes.metadata.as_ref();
        if class.name() != concrete.owner || class.flags() & (0x0200 | 0x0400) != 0 {
            return Ok(false);
        }
        if concrete.inherited_owners.is_none() {
            let mut pending: Vec<_> = class
                .parent()
                .into_iter()
                .chain(class.interfaces())
                .map(str::to_owned)
                .collect();
            let mut visited = HashSet::new();
            let mut inherited = Vec::new();
            while let Some(parent) = pending.pop() {
                if !visited.insert(parent.clone()) {
                    continue;
                }
                let Some(bytes) =
                    guarded_class(facts, context, loader, &parent, concrete.symbol, guard_file)?
                else {
                    continue;
                };
                let header = bytes.metadata.as_ref();
                if header.name() != parent {
                    return Err(Error::Invalid("generated JVM member parent header"));
                }
                pending.extend(
                    header
                        .parent()
                        .into_iter()
                        .chain(header.interfaces())
                        .map(str::to_owned),
                );
                inherited.push(parent);
            }
            inherited.sort_unstable();
            inherited.dedup();
            for owner in &inherited {
                self.receiver_owners
                    .entry(owner.clone())
                    .or_default()
                    .push(id);
            }
            concrete.inherited_owners = Some(inherited);
        }
        Ok(true)
    }

    /// One NEW implementation per context turn. All already admitted bodies and
    /// their exact dependencies are drained before the driver calls this again.
    /// Numeric cursors and owner postings replace a receiver×contract queue.
    pub(super) fn admit(
        &mut self,
        facts: &mut FactSnapshot,
        inputs: &mut OwnedBinaryInputs,
        registry: &mut Registry,
        pending: &mut VecDeque<MethodKey>,
    ) -> Result<(), Error> {
        self.refresh(facts, inputs, registry);
        if self.contracts.is_empty() || self.queues.is_empty() {
            return Ok(());
        }
        if self.request_one(facts, inputs, registry, pending)? {
            return Ok(());
        }
        let contexts = self.queues.len();
        for offset in 0..contexts {
            let context_id = (self.next_context + offset) % contexts;
            while let Some(&class_id) = self.queues[context_id].front() {
                if !self.prepare_class(class_id, facts, inputs)? {
                    self.queues[context_id].pop_front();
                    self.classes[class_id].queued = false;
                    continue;
                }
                let concrete = &self.classes[class_id];
                let candidate = concrete
                    .inherited_owners
                    .as_ref()
                    .unwrap()
                    .iter()
                    .filter_map(|owner| self.contract_owners.get(owner))
                    .filter_map(|ids| {
                        ids.get(ids.partition_point(|&id| id < concrete.next_contract))
                    })
                    .copied()
                    .min();
                let Some(id) = candidate else {
                    self.classes[class_id].next_contract = self.contracts.len();
                    self.classes[class_id].queued = false;
                    self.queues[context_id].pop_front();
                    continue;
                };
                self.classes[class_id].next_contract = id + 1;
                let before = pending.len();
                self.candidate(class_id, id, false, facts, inputs, registry, pending)?;
                if pending.len() != before {
                    self.next_context = (context_id + 1) % contexts;
                    return Ok(());
                }
            }
        }
        Ok(())
    }

    /// Reserve declarations for actual source THIS calls before the mandatory
    /// native body inventory can consume their context's fair allowance. This
    /// does not admit an arbitrary percentage or increase any declaration cap.
    pub(super) fn admit_requested(
        &mut self,
        facts: &mut FactSnapshot,
        inputs: &mut OwnedBinaryInputs,
        registry: &mut Registry,
        pending: &mut VecDeque<MethodKey>,
    ) -> Result<bool, Error> {
        self.refresh(facts, inputs, registry);
        self.request_one(facts, inputs, registry, pending)
    }

    fn request_one(
        &mut self,
        facts: &mut FactSnapshot,
        inputs: &mut OwnedBinaryInputs,
        registry: &mut Registry,
        pending: &mut VecDeque<MethodKey>,
    ) -> Result<bool, Error> {
        let contexts = self.requested.len();
        // Compiler-bound actual this-calls precede unrelated inherited member
        // inventory. Yield on one new declaration so its exact helper/ctor
        // dependencies still drain before the next speculative admission.
        for offset in 0..contexts {
            let context = (self.next_context + offset) % contexts;
            while let Some((class, contract)) = self.requested[context].pop_front() {
                if !self.prepare_class(class, facts, inputs)?
                    || (self.classes[class].owner != self.contracts[contract].owner
                        && self.classes[class]
                            .inherited_owners
                            .as_ref()
                            .is_none_or(|owners| {
                                owners
                                    .binary_search(&self.contracts[contract].owner)
                                    .is_err()
                            }))
                {
                    continue;
                }
                let before = pending.len();
                self.candidate(class, contract, true, facts, inputs, registry, pending)?;
                if pending.len() != before {
                    self.next_context = (context + 1) % contexts;
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }

    fn candidate(
        &mut self,
        class_id: usize,
        id: usize,
        requested: bool,
        facts: &mut FactSnapshot,
        inputs: &mut OwnedBinaryInputs,
        registry: &mut Registry,
        pending: &mut VecDeque<MethodKey>,
    ) -> Result<(), Error> {
        let concrete = &self.classes[class_id];
        let contract = &self.contracts[id];
        let proof = &self.contract_proofs[id];
        let context = &mut inputs.contexts[concrete.context];
        if contract.context != concrete.context
            && !(concrete.source_product
                && proof.cross_context
                && facts.symbols[proof.symbol.index()].flags & SYMBOL_DEFINED == 0
                && context.classes.get(&contract.owner).is_some_and(|class| {
                    let CachedClass::Found(class) = class else {
                        return false;
                    };
                    class.hash == proof.hash
                        && class.metadata.hash() == proof.hash
                        && exact_contract(&class.metadata, contract, proof.flags)
                }))
        {
            if accessors::modeled_contract(registry, proof.symbol) {
                protect_property_fallback(
                    facts,
                    registry,
                    concrete.context,
                    context,
                    &concrete.owner,
                    concrete.symbol,
                    proof.symbol,
                )?;
            }
            return Ok(());
        }
        if self.loaders[concrete.context].is_none() {
            self.loaders[concrete.context] = Some(context_loader(context, &inputs.admitted)?);
        }
        let loader = self.loaders[concrete.context].as_mut().unwrap();
        let guard_file = facts.symbols[concrete.symbol.index()].file;
        // The explicit property law also covers ordinary native implementations;
        // only own-product receivers receive the separate wildcard coverage seal.
        let property_model = accessors::modeled_contract(registry, proof.symbol);
        let trusted_property = property_model
            && accessors::trusted_receiver(
                facts,
                registry,
                concrete.context,
                context,
                loader,
                &concrete.owner,
                proof.symbol,
                &contract.name,
                &contract.descriptor,
            )?;
        if concrete.source_product && self.covered_requests.len() < MAX_METHODS && trusted_property
        {
            self.covered_requests
                .push((concrete.symbol, proof.symbol, proof.symbol));
            return Ok(());
        }
        if property_model
            && !trusted_property
            && !accessors::bound_source_override(registry, concrete.symbol, proof.symbol)
        {
            // A model default must not hide an unbound custom source override.
            protect_property_fallback(
                facts,
                registry,
                concrete.context,
                context,
                &concrete.owner,
                concrete.symbol,
                proof.symbol,
            )?;
        }
        let implementations = class_chain_members(
            &concrete.owner,
            &[(contract.name.as_str(), contract.descriptor.as_str())],
            |owner| guarded_class(facts, context, loader, owner, concrete.symbol, guard_file),
            |owner, name| {
                self.source_members
                    .get(owner)
                    .is_some_and(|names| names.contains(name))
            },
        )?;
        let Some(provider) = implementations.targets[0] else {
            return Ok(());
        };
        let result = registry.method(
            facts,
            concrete.context,
            context,
            loader,
            MemberRef {
                owner: &implementations.owners[provider],
                name: &contract.name,
                descriptor: &contract.descriptor,
            },
            None,
            None,
            pending,
        );
        if matches!(&result, Err(error) if matches!(error, Error::Limit("optional native method admission frontier")))
            && self.refused.len() < context.admission.limits.methods
            && self.refused_per_context[concrete.context]
                < context.admission.method_allowance.max(1)
        {
            // Delay publication until all exact aliases are known. A later
            // declaration may expose another ancestor ABI that must be guarded.
            let Some(CachedClass::Found(provider)) =
                context.classes.get(&implementations.owners[provider])
            else {
                return Err(Error::Invalid("generated JVM member provider"));
            };
            self.refused.push(RefusedCandidate {
                class: class_id,
                contract: id,
                provider: provider.clone(),
            });
            self.refused_per_context[concrete.context] += 1;
            context.admission.deferred += 1;
            context.admission.method_refusals += 1;
            return Ok(());
        }
        // The receiver itself is already admitted. Exhausted contract
        // bookkeeping retains one wildcard at its actual instance dispatches.
        let dispatch_file = if guard_file.is_none() {
            let Some(CachedClass::Found(bytes)) = context.classes.get(&concrete.owner) else {
                return Err(Error::Invalid("generated JVM receiver header"));
            };
            let bytes = bytes.clone();
            registry.file(facts, concrete.context, context.id, &concrete.owner, &bytes)?
        } else {
            guard_file
        };
        if matches!(&result, Err(error) if matches!(error, Error::Limit("optional native method admission frontier")))
        {
            admission::deferred_receiver_frontier(
                facts,
                context,
                concrete.symbol,
                dispatch_file,
                true,
            )?;
            return Ok(());
        }
        // Class/byte/provenance boundaries keep their ordinary behavior.
        let implementation = admission::optional_generated_method(
            facts,
            context,
            concrete.symbol,
            dispatch_file,
            &[],
            true,
            result,
        )?;
        if requested && !implementation.is_none() {
            // The full pinned superclass lookup above proves no nearer
            // implementation was omitted. A mere inherited graph edge would
            // not supply this absence authority.
            self.covered_requests
                .push((concrete.symbol, proof.symbol, implementation));
        }
        self.link(facts, implementation, id)
    }

    fn link(
        &mut self,
        facts: &mut FactSnapshot,
        implementation: SymbolId,
        id: usize,
    ) -> Result<(), Error> {
        let target = self.contract_proofs[id].symbol;
        if !implementation.is_none()
            && implementation != target
            && self.links.insert((implementation, target))
        {
            facts.relations.push(RelationRecord {
                source: implementation,
                target,
                kind: RelationKind::Override,
                file: facts.symbols[implementation.index()].file,
            });
        }
        Ok(())
    }

    /// No new declarations here. Publish every refused candidate against the
    /// final exact ABI index, or link a target subsequently admitted by a direct
    /// dependency. Missing child overrides can never disappear at queue drain.
    pub(super) fn finish(
        &mut self,
        facts: &mut FactSnapshot,
        inputs: &mut OwnedBinaryInputs,
        registry: &mut Registry,
        admitted_bodies: &HashSet<SymbolId>,
    ) -> Result<(), Error> {
        self.refresh(facts, inputs, registry);
        // Sort final hash postings once; wide ABI groups must not be scanned
        // again for every refused receiver.
        for methods in self.aliases.values_mut().flat_map(HashMap::values_mut) {
            methods
                .methods
                .sort_unstable_by_key(|(symbol, hash)| (hash.0, *symbol));
            methods.methods.dedup();
        }
        let mut hashes = Vec::new();
        let mut contracts = Vec::new();
        for refused in std::mem::take(&mut self.refused) {
            let concrete = &self.classes[refused.class];
            let contract = &self.contracts[refused.contract];
            let key = MethodKey {
                context: concrete.context,
                owner: refused.provider.metadata.name().into(),
                name: contract.name.clone(),
                descriptor: contract.descriptor.clone(),
            };
            let context = &mut inputs.contexts[concrete.context];
            if let Some(data) = registry.methods.get(&key) {
                self.link(facts, data.symbol, refused.contract)?;
                continue;
            }
            let group = &self.aliases[contract.name.as_str()][contract.descriptor.as_str()];
            hashes.clear();
            hashes.extend(
                std::iter::once(concrete.owner.as_str())
                    .chain(
                        concrete
                            .inherited_owners
                            .as_ref()
                            .unwrap()
                            .iter()
                            .map(String::as_str),
                    )
                    .filter_map(|owner| match context.classes.get(owner) {
                        Some(CachedClass::Found(class)) => Some(class.hash),
                        _ => None,
                    }),
            );
            hashes.sort_unstable_by_key(|hash| hash.0);
            hashes.dedup();
            contracts.clear();
            contracts.push(self.contract_proofs[refused.contract].symbol);
            for hash in &hashes {
                let start = group.methods.partition_point(|(_, value)| value.0 < hash.0);
                let end = group
                    .methods
                    .partition_point(|(_, value)| value.0 <= hash.0);
                contracts.extend(group.methods[start..end].iter().map(|(symbol, _)| *symbol));
            }
            contracts.sort_unstable();
            contracts.dedup();
            let broad = group.unproved
                || std::iter::once(&concrete.owner)
                    .chain(concrete.inherited_owners.as_ref().unwrap())
                    .any(|owner| {
                        self.source_members
                            .get(owner)
                            .is_some_and(|names| names.contains(&contract.name))
                    });
            let file = if facts.symbols[concrete.symbol.index()].file.is_none() {
                let bytes = match context.classes.get(&concrete.owner) {
                    Some(CachedClass::Found(bytes)) => bytes.clone(),
                    _ => return Err(Error::Invalid("generated JVM receiver header")),
                };
                registry.file(facts, concrete.context, context.id, &concrete.owner, &bytes)?
            } else {
                facts.symbols[concrete.symbol.index()].file
            };
            admission::deferred_generated_frontier(
                facts,
                context,
                concrete.symbol,
                file,
                &contracts,
                broad,
            )?;
        }
        self.covered_requests.sort_unstable();
        self.covered_requests.dedup();
        for &(receiver, contract, implementation) in &self.covered_requests {
            if !admitted_bodies.contains(&implementation) {
                continue;
            }
            let file = facts.symbols[receiver.index()].file;
            // Native class-facet projection can make a compiler alias cease to
            // be a callable. Such an alias never receives a coverage seal.
            if admission::dispatch_scope_error(facts, receiver, contract, file).is_none() {
                facts.relations.push(RelationRecord {
                    source: receiver,
                    target: contract,
                    kind: RelationKind::KnownReceiverDispatch,
                    file,
                });
            }
        }
        Ok(())
    }
}

fn protect_property_fallback(
    facts: &mut FactSnapshot,
    registry: &mut Registry,
    index: usize,
    context: &mut AdmittedContext,
    owner: &str,
    receiver: SymbolId,
    contract: SymbolId,
) -> Result<(), Error> {
    let mut file = facts.symbols[receiver.index()].file;
    if file.is_none() {
        let Some(CachedClass::Found(bytes)) = context.classes.get(owner) else {
            return Err(Error::Invalid("accessor dispatch receiver header"));
        };
        let bytes = bytes.clone();
        file = registry.file(facts, index, context.id, owner, &bytes)?;
    }
    admission::deferred_generated_frontier(facts, context, receiver, file, &[contract], false)
}

/// Value zero is lexical `this` only in a source-owned, non-static and
/// non-deferred body. Capture/closure/native locals are deliberately excluded.
/// The bounded numeric postings affect ordering only, never target authority.
fn compiler_this_requests(
    facts: &FactSnapshot,
    classes: &[ConcreteClass],
) -> Vec<(SymbolId, usize)> {
    let mut owners: Vec<_> = classes
        .iter()
        .enumerate()
        .map(|(i, c)| (c.symbol, i))
        .collect();
    owners.sort_unstable();
    let mut requests = Vec::new();
    for body in &facts.bodies {
        if body.flags & (BODY_DEFERRED | BODY_BINARY_RECIPE | BODY_STATIC_INITIALIZER) != 0
            || facts.symbols[body.symbol.index()].flags & SYMBOL_DEFINED == 0
            || facts.files[body.file.index()].flags
                & (SOURCE_VERIFIED | SYNTAX_VERIFIED | FILE_BINARY_SOURCE)
                != SOURCE_VERIFIED | SYNTAX_VERIFIED
        {
            continue;
        }
        let mut owner = body.symbol;
        let mut class = None;
        for _ in 0..128 {
            let declaration = &facts.symbols[owner.index()];
            if matches!(declaration.kind, 10 | 13 | 14) {
                class = owners
                    .binary_search_by_key(&owner, |row| row.0)
                    .ok()
                    .map(|i| owners[i].1);
                break;
            }
            if declaration.owner.is_none() {
                break;
            }
            owner = declaration.owner;
        }
        let Some(class) = class else { continue };
        if body.file != facts.symbols[owner.index()].file
            || facts.files[body.file.index()].context != facts.symbols[owner.index()].context
        {
            continue;
        }
        for op in &facts.operations[body.operations.range()] {
            if op.a == ValueId(0)
                && !op.target.is_none()
                && op.flags & (OP_SUPER | OP_QUALIFIED_SUPER) == 0
                && matches!(
                    op.opcode,
                    Opcode::Call
                        | Opcode::VirtualCall
                        | Opcode::DefaultArgument
                        | Opcode::RegisterTest
                        | Opcode::InvokeCallback
                )
            {
                requests.push((op.target, class));
                if requests.len() >= MAX_METHODS {
                    requests.sort_unstable();
                    requests.dedup();
                    return requests;
                }
            }
        }
    }
    requests.sort_unstable();
    requests.dedup();
    requests
}

/// Resolve an implementation only along the verified superclass chain. A
/// conflicting exact declaration or a source-owned name stops the search;
/// interface defaults, absent providers and unverified ancestors never supply a
/// guessed implementation. The selected declaring owner keeps its own hash,
/// fields and ordinary native body when Registry admits it.
struct Implementations {
    owners: Vec<String>,
    targets: Vec<Option<usize>>,
}
fn class_chain_members(
    owner: &str,
    requests: &[(&str, &str)],
    mut load: impl FnMut(&str) -> Result<Option<Arc<ClassBytes>>, Error>,
    mut source_owned: impl FnMut(&str, &str) -> bool,
) -> Result<Implementations, Error> {
    let mut result = Implementations {
        owners: Vec::new(),
        targets: vec![None; requests.len()],
    };
    let mut unresolved = vec![true; requests.len()];
    let mut remaining = requests.len();
    let mut owner = owner.to_owned();
    while remaining != 0 {
        if result.owners.contains(&owner) {
            break;
        }
        let Some(bytes) = load(&owner)? else { break };
        let class = bytes.metadata.as_ref();
        if class.name() != owner || class.flags() & 0x0200 != 0 {
            break;
        }
        let provider = result.owners.len();
        result.owners.push(owner);
        // Parse each superclass once for the whole requested contract batch.
        // Classfile method/constant-pool arenas are never rebuilt per method.
        for (index, &(name, descriptor)) in requests.iter().enumerate() {
            if !unresolved[index] {
                continue;
            }
            if source_owned(class.name(), name) {
                unresolved[index] = false;
                remaining -= 1;
                continue;
            }
            match class.method(name, Some(descriptor)) {
                Err(error) if error.kind == binary::ErrorKind::MissingMethod => {}
                declaration => {
                    unresolved[index] = false;
                    remaining -= 1;
                    if let Ok(method) = declaration {
                        if method.flags & 0x0001 != 0
                            && method.flags & (0x0002 | 0x0008 | 0x0400) == 0
                            && method.code.is_some()
                        {
                            result.targets[index] = Some(provider);
                        }
                    }
                }
            }
        }
        let Some(parent) = class.parent() else { break };
        owner = parent.to_owned();
    }
    Ok(result)
}

#[cfg(test)]
fn class_chain_member(
    owner: &str,
    name: &str,
    descriptor: &str,
    load: impl FnMut(&str) -> Result<Option<Arc<ClassBytes>>, Error>,
    source_owned: impl FnMut(&str, &str) -> bool,
) -> Result<Option<String>, Error> {
    let result = class_chain_members(owner, &[(name, descriptor)], load, source_owned)?;
    Ok(result.targets[0].map(|provider| result.owners[provider].clone()))
}

/// Source calls whose external compiler declaration lacked member metadata may
/// have been normalized as direct calls. Only an admitted abstract instance
/// method can repair this boundary; native invokespecial and Scala super remain
/// direct, as do private/static methods and unknown method descriptors.
pub(super) fn repair_dispatch(facts: &mut FactSnapshot, registry: &Registry) -> Result<(), Error> {
    let mut authorities: HashMap<SymbolId, Option<(usize, ContentHash)>> = HashMap::new();
    for (key, data) in &registry.methods {
        let declaration = facts.symbols[data.symbol.index()];
        if !abstract_instance(key, data)
            || declaration.flags & SYMBOL_DEFINED != 0
            || declaration.kind != 0
        {
            continue;
        }
        let Ok(descriptor) = binary::method_descriptor(&key.descriptor) else {
            continue;
        };
        let Some(&file) = registry.files.get(&(key.context, key.owner.clone())) else {
            continue;
        };
        let mut hash = Sha256::new();
        hash.update(VERSION);
        for value in [&key.owner, &key.name, &key.descriptor] {
            hash.update((value.len() as u64).to_le_bytes());
            hash.update(value.as_bytes());
        }
        hash.update(facts.files[file.index()].source_hash.0);
        let proof = (
            descriptor.parameter_count,
            ContentHash(hash.finalize().into()),
        );
        match authorities.entry(data.symbol) {
            std::collections::hash_map::Entry::Vacant(slot) => {
                slot.insert(Some(proof));
            }
            std::collections::hash_map::Entry::Occupied(mut slot) => {
                slot.insert(None);
            }
        }
    }
    for body in &mut facts.bodies {
        if body.flags & BODY_BINARY_RECIPE != 0
            || facts.files[body.file.index()].flags & (SOURCE_VERIFIED | SYNTAX_VERIFIED)
                != SOURCE_VERIFIED | SYNTAX_VERIFIED
        {
            continue;
        }
        let mut hash = None;
        for (offset, op) in facts.operations[body.operations.range()]
            .iter_mut()
            .enumerate()
        {
            if op.opcode != Opcode::Call || op.a.is_none() || op.flags & OP_SUPER != 0 {
                continue;
            }
            let Some(Some((parameters, proof))) = authorities.get(&op.target) else {
                continue;
            };
            if op.arguments.len as usize != *parameters {
                continue;
            }
            op.opcode = Opcode::VirtualCall;
            let digest = hash.get_or_insert_with(|| {
                let mut hash = Sha256::new();
                hash.update(VERSION);
                hash.update(body.body_hash.0);
                hash
            });
            digest.update((offset as u64).to_le_bytes());
            digest.update(proof.0);
        }
        if let Some(hash) = hash {
            body.body_hash = ContentHash(hash.finalize().into());
        }
    }
    Ok(())
}

#[cfg(test)]
#[path = "binary_generated_members_tests.rs"]
mod tests;
