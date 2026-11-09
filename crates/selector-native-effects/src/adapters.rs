//! Native callable factories are code/capture identities, never invocations.
use super::*;

#[derive(Clone, Copy, Debug)]
pub struct SamRef {
    pub provider: u32,
    pub class_sha256: [u8; 32],
    pub binding_sha256: [u8; 32],
    pub class: u32,
    pub name: TextRef,
    pub descriptor: TextRef,
    pub resolved: bool,
}
#[derive(Clone, Copy, Debug)]
pub struct CallableAdapterRef {
    pub method: effects::MethodId,
    pub enclosing_method: effects::MethodId,
    pub implementation: effects::MethodId,
    pub site: u32,
    pub bootstrap: effects::MethodId,
    pub bootstrap_handle_kind: u32,
    pub bootstrap_arguments: [u8; 32],
    pub implementation_handle_kind: u32,
    pub sam: u32,
    pub invoked_name: TextRef,
    pub invoked_descriptor: TextRef,
    pub instantiated_descriptor: TextRef,
    pub adaptation: [u8; 32],
    pub normalized_arity: u32,
    pub normalized_captures: u32,
    /// Exact capture/SAM argument mapping only; not bootstrap authority.
    pub identity_mapping: bool,
    /// False until a private standard-bootstrap + exact SAM proof is admitted.
    pub resolved: bool,
}
#[derive(Clone, Copy)]
pub(crate) struct Draft {
    adapter: u32,
    receiver: effects::ValueRef,
    arguments: effects::Range,
}
impl Builder<'_, '_> {
    fn sam(&mut self, class: u32, name: TextRef, descriptor: TextRef) -> Result<u32, Error> {
        let key = digest(&[
            &class.to_le_bytes(),
            self.text(name).as_bytes(),
            self.text(descriptor).as_bytes(),
        ]);
        let mut next = self.postings.sams.get(&key).copied().unwrap_or(NONE);
        while next != NONE {
            let row = self.out.sams[next as usize];
            if row.class == class
                && self.text(row.name) == self.text(name)
                && self.text(row.descriptor) == self.text(descriptor)
            {
                return Ok(next);
            }
            next = self.postings.sam_next[next as usize];
        }
        let arity = binary::method_descriptor(self.text(descriptor))?.parameter_count as u32;
        let id = self.out.sams.len() as u32;
        self.out.sams.push(SamRef {
            provider: NONE,
            class_sha256: [0; 32],
            binding_sha256: [0; 32],
            class,
            name,
            descriptor,
            resolved: false,
        });
        self.out.data.sam_arities.push(arity);
        self.postings
            .sam_next
            .push(self.postings.sams.insert(key, id).unwrap_or(NONE));
        self.check()?;
        Ok(id)
    }
    pub(crate) fn creation(
        &mut self,
        blob: u32,
        class: &binary::ClassFile<'_>,
        method: &MethodInfo<'_>,
        summary: &binary::MethodSummary<'_>,
        values: &[effects::Origin],
        target: effects::MethodId,
        index: usize,
        lambda: &binary::Lambda<'_>,
    ) -> Result<(), Error> {
        let authority = self.out.classes[self
            .out
            .foreign(target)
            .expect("native enclosing method")
            .class as usize]
            .authority;
        let code = method.code.ok_or(Error::Binding)?;
        let pc = lambda.offset as usize;
        if code.get(pc) != Some(&186) {
            return Err(Error::Binding);
        }
        let operand = u16::from_be_bytes(
            code.get(pc + 1..pc + 3)
                .ok_or(Error::Binding)?
                .try_into()
                .map_err(|_| Error::Binding)?,
        );
        let dynamic = class.invoke_dynamic(operand)?;
        let implementation_handle = match class
            .bootstrap_argument(dynamic.bootstrap.arguments.get(1).ok_or(Error::Binding)?)?
        {
            binary::BootstrapArgument::MethodHandle(value) => value,
            _ => return Err(Error::Binding),
        };
        let implementation = self.member_method(blob, authority, lambda.implementation)?;
        let bootstrap = self.member_method(blob, authority, dynamic.bootstrap.method.member)?;
        let owner = self.borrowed(blob, lambda.interface)?;
        let sam_class = self.class(authority, owner)?;
        let sam_name = self.borrowed(blob, lambda.sam_name)?;
        let sam_desc = self.borrowed(blob, lambda.sam_descriptor)?;
        let sam = self.sam(sam_class, sam_name, sam_desc)?;
        let destination = summary
            .values
            .iter()
            .position(|v| matches!(v,Value::Lambda(i) if *i as usize==index))
            .ok_or(Error::Binding)? as u32;
        let capture_count = lambda.captures.len;
        if dynamic.descriptor.parameter_count != capture_count as usize {
            return Err(Error::Binding);
        }
        let arity = self.out.data.sam_arities[sam as usize];
        let adapter_index = self.out.adapters.len() as u32;
        let adapter_method = effects::MethodId(self.out.data.methods.len() as u32);
        let mut row = effects::MethodRow::unknown(
            effects::SubjectRef {
                kind: effects::SubjectKind::CallableAdapter,
                index: adapter_index,
            },
            authority,
            arity,
            capture_count,
            0,
        );
        row.locals =
            u32::from(binary::method_descriptor(lambda.sam_descriptor)?.return_type != "V");
        self.out.data.methods.push(row);
        self.out.projected.push(false);
        let site = self.site(target, lambda.offset);
        let start = self.out.data.origins.len();
        for &id in &summary.arguments[lambda.captures.range()] {
            self.out.data.origins.push(Self::origin(values, id));
            self.out
                .data
                .callable_values
                .push(Self::callable(summary, id));
        }
        self.out.data.creations.push(effects::CallableCreation {
            site,
            destination,
            implementation: adapter_method,
            sam: NONE,
            receiver: effects::Origin::ANY,
            receiver_value: effects::ValueRef::UNKNOWN,
            captures: range(start, self.out.data.origins.len()),
        });
        let mut bootstrap_hash = Sha256::new();
        bootstrap_hash.update(self.out.blobs[blob as usize].class_sha256);
        bootstrap_hash.update(operand.to_le_bytes());
        for arg in dynamic.bootstrap.arguments.iter() {
            bootstrap_hash.update(arg.to_le_bytes());
        }
        let bootstrap_arguments: [u8; 32] = bootstrap_hash.finalize().into();
        let mut adaptation = Sha256::new();
        adaptation.update(b"selector-native-callable-identity-adaptation/v1");
        adaptation.update(self.out.blobs[blob as usize].binding_sha256);
        adaptation.update(bootstrap_arguments);
        adaptation.update(lambda.offset.to_le_bytes());
        for text in [
            method.name,
            method.descriptor,
            lambda.sam_descriptor,
            lambda.instantiated_descriptor,
            lambda.implementation.owner,
            lambda.implementation.name,
            lambda.implementation.descriptor,
        ] {
            adaptation.update((text.len() as u64).to_le_bytes());
            adaptation.update(text.as_bytes());
        }
        let mut receiver = effects::ValueRef::UNKNOWN;
        let first = self.adapter_arguments.len();
        let sam_descriptor = binary::method_descriptor(lambda.sam_descriptor)?;
        let implementation_descriptor =
            binary::method_descriptor(lambda.implementation.descriptor)?;
        let capture_types: Vec<_> = dynamic.descriptor.parameters().collect();
        let sam_types: Vec<_> = sam_descriptor.parameters().collect();
        let implementation_types: Vec<_> = implementation_descriptor.parameters().collect();
        let mut bindings: Vec<_> = (0..capture_count)
            .map(effects::ValueRef::capture)
            .chain((0..arity).map(effects::ValueRef::argument))
            .collect();
        let mut input_types: Vec<_> = capture_types.into_iter().chain(sam_types).collect();
        // No boxing, casts, constructor allocation or bridge adaptation is
        // inferred by counts. Such a factory remains an explicit TOP adapter.
        let mut resolved = lambda.sam_descriptor == lambda.instantiated_descriptor
            && sam_descriptor.return_type == implementation_descriptor.return_type
            && lambda.implementation.name != "<init>";
        if lambda.kind != binary::InvokeKind::Static {
            if input_types.first().is_some_and(|ty| {
                ty.strip_prefix('L').and_then(|s| s.strip_suffix(';'))
                    == Some(lambda.implementation.owner)
            }) && !bindings.is_empty()
            {
                receiver = bindings.remove(0);
                input_types.remove(0);
            } else {
                resolved = false;
            }
        }
        resolved &= input_types == implementation_types;
        if resolved {
            self.adapter_arguments.extend(bindings);
        }
        let arguments = range(first, self.adapter_arguments.len());
        self.out.adapters.push(CallableAdapterRef {
            method: adapter_method,
            enclosing_method: target,
            implementation,
            site,
            bootstrap,
            bootstrap_handle_kind: dynamic.bootstrap.method.kind as u32,
            bootstrap_arguments,
            implementation_handle_kind: implementation_handle.kind as u32,
            sam,
            invoked_name: self.borrowed(blob, dynamic.name)?,
            invoked_descriptor: self.borrowed(blob, dynamic.descriptor.text)?,
            instantiated_descriptor: self.borrowed(blob, lambda.instantiated_descriptor)?,
            adaptation: adaptation.finalize().into(),
            normalized_arity: arity,
            normalized_captures: capture_count,
            identity_mapping: resolved,
            resolved: false,
        });
        self.adapter_drafts.push(Draft {
            adapter: adapter_index,
            receiver,
            arguments,
        });
        self.check()
    }
    /// Run after the enclosing row's contiguous ranges are sealed. Adapter rows
    /// must never leak into the factory's call/effect slices.
    pub(crate) fn finish_adapters(&mut self) -> Result<(), Error> {
        while self.adapter_cursor < self.adapter_drafts.len() {
            let draft = self.adapter_drafts[self.adapter_cursor];
            self.adapter_cursor += 1;
            let adapter = self.out.adapters[draft.adapter as usize];
            if !adapter.identity_mapping {
                continue;
            }
            let mut row = self.out.data.methods[adapter.method.0 as usize];
            let start = Starts::new(&self.out.data);
            let first = self.out.data.origins.len();
            for value in
                &self.adapter_arguments[draft.arguments.checked(self.adapter_arguments.len())?]
            {
                self.out.data.callable_values.push(*value);
                self.out.data.origins.push(match value.kind {
                    effects::ValueKind::Capture => effects::Origin::capture(value.index),
                    effects::ValueKind::Argument => effects::Origin::argument(value.index),
                    _ => effects::Origin::ANY,
                });
            }
            let receiver = match draft.receiver.kind {
                effects::ValueKind::Capture => effects::Origin::capture(draft.receiver.index),
                effects::ValueKind::Argument => effects::Origin::argument(draft.receiver.index),
                _ => effects::Origin::ANY,
            };
            self.out.data.calls.push(effects::CallRow {
                site: adapter.site,
                target: effects::CallTarget::Direct(adapter.implementation),
                kind: match adapter.implementation_handle_kind {
                    6 => effects::CallKind::Static,
                    9 => effects::CallKind::Interface,
                    7 => effects::CallKind::Special,
                    _ => effects::CallKind::Virtual,
                },
                receiver,
                receiver_value: draft.receiver,
                result: if row.locals == 0 { NONE } else { 0 },
                arguments: range(first, self.out.data.origins.len()),
                captures: effects::Range::EMPTY,
            });
            if row.locals != 0 {
                self.out.data.value_flows.push(effects::ValueFlow {
                    kind: effects::ValueFlowKind::Return,
                    value: effects::ValueRef::local(0),
                    index: 0,
                });
            }
            self.out.data.code_observations.push(effects::CodeRef {
                kind: effects::CodeKind::Method,
                index: adapter.implementation.0,
            });
            start.finish(&mut row, &self.out.data);
            self.out.data.methods[adapter.method.0 as usize] = row;
            self.out.projected[adapter.method.0 as usize] = true;
        }
        self.check()
    }
}

impl Produced<'_> {
    /// Admits activation identity, not effect closure. Missing SAM providers or
    /// unsupported factory adaptations stay SAM=NONE with the TOP adapter.
    /// The private token binds the standard bootstrap law to declared java.base.
    pub fn admit_standard_factories(
        &mut self,
        provider: &mut provider::VerifiedProvider<'_>,
        token: &framework_transport::Java21StandardLambdaMetafactory,
    ) -> Result<usize, Error> {
        let mut ready = Vec::new();
        let identity = token.class_identity();
        for (creation_index, creation) in self.data.creations.iter().enumerate() {
            let body = self
                .data
                .methods
                .get(creation.implementation.0 as usize)
                .ok_or(Error::Binding)?;
            if body.subject.kind != effects::SubjectKind::CallableAdapter
                || body.authority != identity.authority
            {
                continue;
            }
            let adapter = self
                .adapters
                .get(body.subject.index as usize)
                .ok_or(Error::Binding)?;
            if !adapter.identity_mapping
                || adapter.implementation_handle_kind != 6
                || adapter.normalized_captures > 64
            {
                continue;
            }
            let sam = self.sams.get(adapter.sam as usize).ok_or(Error::Binding)?;
            let descriptor = binary::method_descriptor(self.text(sam.descriptor))?;
            if descriptor.return_type != "V"
                && !descriptor.return_type.starts_with('L')
                && !descriptor.return_type.starts_with('[')
            {
                continue;
            }
            let bootstrap = self.foreign(adapter.bootstrap).ok_or(Error::Binding)?;
            let class = self
                .classes
                .get(bootstrap.class as usize)
                .ok_or(Error::Binding)?;
            let member = MemberRef {
                owner: self.text(class.owner),
                name: self.text(bootstrap.name),
                descriptor: self.text(bootstrap.descriptor),
            };
            token
                .validate_bootstrap(class.authority, member, binary::ReferenceKind::InvokeStatic)
                .map_err(|_| Error::Binding)?;
            let (actual, platform) = provider
                .declared_java21_class(class.authority, member.owner)
                .map_err(|e| Error::Provider(Box::new(e)))?;
            if platform != token.platform_sha256()
                || actual.authority != identity.authority
                || actual.provider != identity.provider
                || actual.class_sha256 != identity.class_sha256
                || actual.binding_sha256 != identity.binding_sha256
            {
                return Err(Error::Binding);
            }
            let sam_class = self.classes.get(sam.class as usize).ok_or(Error::Binding)?;
            let owner = self.text(sam_class.owner);
            let Some(metadata) = provider
                .metadata(sam_class.authority, owner)
                .map_err(|e| Error::Provider(Box::new(e)))?
            else {
                continue;
            };
            if metadata.flags() & 0x200 == 0 {
                continue;
            }
            let resolution = provider
                .resolve_member(
                    sam_class.authority,
                    MemberRef {
                        owner,
                        name: self.text(sam.name),
                        descriptor: self.text(sam.descriptor),
                    },
                    provider::MemberInvocation::Interface,
                    None,
                )
                .map_err(|e| Error::Provider(Box::new(e)))?;
            if !matches!(resolution.resolution,selector_jvm_resolve::Resolution::Found(ref found) if found.flags&0x401==0x401 && found.flags&8==0)
            {
                continue;
            }
            let proof = provider
                .receipt(sam_class.authority, owner)
                .ok_or(Error::Binding)?;
            ready.push((
                creation_index,
                body.subject.index as usize,
                adapter.sam as usize,
                proof.provider.ok_or(Error::Binding)?,
                proof.class_sha256.ok_or(Error::Binding)?,
                proof.binding_sha256,
            ));
        }
        // Apply only after all exact bootstrap checks have succeeded.
        for &(creation, adapter, sam, provider, class_sha256, binding_sha256) in &ready {
            self.sams[sam].resolved = true;
            self.sams[sam].provider = provider;
            self.sams[sam].class_sha256 = class_sha256;
            self.sams[sam].binding_sha256 = binding_sha256;
            self.adapters[adapter].resolved = true;
            self.data.creations[creation].sam = sam as u32;
        }
        Ok(ready.len())
    }
}
