use super::*;

const PROBE: &[u8] =
    include_bytes!("../../../fixtures/native-finite-effects/classes/finitecase/Probe.class");
struct Provider {
    bytes: Arc<[u8]>,
    bad_hash: bool,
    unavailable: bool,
    alternate: bool,
    calls: u32,
}
impl Provider {
    fn new() -> Self {
        Self {
            bytes: Arc::from(PROBE),
            bad_hash: false,
            unavailable: false,
            alternate: false,
            calls: 0,
        }
    }
}
impl ClassProvider for Provider {
    fn class(&mut self, demand: ClassDemand<'_>) -> Result<Option<ProvidedClass>, Error> {
        self.calls += 1;
        if self.unavailable {
            return Ok(None);
        }
        Ok(Some(ProvidedClass {
            bytes: self.bytes.clone(),
            class_sha256: if self.bad_hash {
                [0; 32]
            } else {
                Sha256::digest(&self.bytes).into()
            },
            authority: demand.authority,
            provider: if self.alternate { self.calls } else { 1 },
            binding_sha256: [9; 32],
        }))
    }
}
fn one<'a>(demands: &'a [ClassDemand<'a>]) -> Produced<'a> {
    produce(demands, &mut Provider::new(), Limits::default()).unwrap()
}
fn method(o: &Produced<'_>, name: &str) -> effects::MethodId {
    o.methods
        .iter()
        .find(|m| o.text(m.name) == name && m.kind == ForeignKind::Method)
        .unwrap()
        .method
}
fn direct(call: &effects::CallRow) -> effects::MethodId {
    match call.target {
        effects::CallTarget::Direct(id) => id,
        _ => panic!("fixture expected exact direct target"),
    }
}

#[test]
fn genuine_all_branch_and_handler_calls_and_stores_survive_primitive_unknowns() {
    assert_eq!(
        <[u8; 32]>::from(Sha256::digest(PROBE)),
        selector_types::ContentHash::from_hex(
            "e0019927542b275cb17ab2b6d2a2d3e3133050eaa59268306e096ec2c2f01aca"
        )
        .unwrap()
        .0
    );
    let demands = [ClassDemand {
        authority: 0,
        owner: "finitecase/Probe",
    }];
    let out = one(&demands);
    assert_eq!(out.roots.len(), 48);
    assert_eq!(out.blobs.len(), 1);
    for row in &out.data.methods {
        assert_eq!(row.top, effects::TopMask::ALL);
    }
    let branch = out.data.methods[method(&out, "branchAndCatch").0 as usize];
    let calls: Vec<_> = out.data.calls[branch.calls.checked(out.data.calls.len()).unwrap()]
        .iter()
        .map(|call| {
            let site = out.sites[call.site as usize];
            (site.pc, out.text(out.foreign(direct(call)).unwrap().name))
        })
        .collect();
    assert_eq!(calls, [(18, "readInt"), (24, "run"), (35, "run")]);
    assert_eq!(
        branch.writes.len, 2,
        "both normal and catch writes retained"
    );
    let allocation = out.data.methods[method(&out, "writeAfterAllocation").0 as usize];
    assert_eq!((allocation.writes.len, allocation.calls.len), (1, 1));
    let callback = out.data.methods[method(&out, "callbackAfterRead").0 as usize];
    assert_eq!(callback.calls.len, 1);
    assert!(
        out.data.reads[callback.reads.checked(out.data.reads.len()).unwrap()]
            .iter()
            .any(|r| r.kind == effects::StorageKind::ArrayElements)
    );
    effects::validate(&out.data, out.bounds(), effects::Limits::default()).unwrap();
}

#[test]
fn primitive_report_has_typed_reads_scalar_top_and_shared_exception_prerequisites() {
    let demands = [ClassDemand {
        authority: 0,
        owner: "finitecase/Probe",
    }];
    let out = one(&demands);
    let read = method(&out, "readInt");
    let primitive = out
        .primitives
        .iter()
        .find(|p| out.sites[p.site as usize].method == read)
        .unwrap();
    assert_eq!(primitive.kind, PrimitiveKind::Read(PrimitiveType::Int));
    assert!(
        primitive.scalar_top
            && primitive.shared_throwable_metadata
            && primitive.requires_verification_and_vm_contract
    );
    assert_eq!(primitive.base, effects::Origin::ANY);
    assert_eq!(
        primitive.exceptions,
        (1 << VmException::NullPointer as u32) | (1 << VmException::ArrayIndexOutOfBounds as u32)
    );
    let row = out.data.methods[read.0 as usize];
    assert_eq!(
        row.writes.len, 0,
        "array reads do not fabricate arbitrary heap writes"
    );
    assert_eq!(
        row.top,
        effects::TopMask::ALL,
        "structure is not verification"
    );
    let new_array = method(&out, "newInt");
    let row = out.data.methods[new_array.0 as usize];
    assert_eq!(
        row.initializes.len, 0,
        "no fabricated primitive component initializer"
    );
    assert_eq!(
        row.calls.len, 0,
        "no fabricated primitive-array constructor"
    );
    assert!(
        out.primitives
            .iter()
            .any(|p| out.sites[p.site as usize].method == new_array
                && p.kind == PrimitiveKind::Allocate(PrimitiveType::Int))
    );
}

#[test]
fn reference_stores_monitors_native_dynamic_and_reflection_do_not_become_closed() {
    let demands = [ClassDemand {
        authority: 0,
        owner: "finitecase/Probe",
    }];
    let out = one(&demands);
    for (name, reason) in [
        ("readReference", OpenReason::ReferenceArrayLoad),
        ("writeInt", OpenReason::ArrayWrite),
        ("monitorAfterRead", OpenReason::Monitor),
        ("opaque", OpenReason::NativeMethod),
        ("dynamicAfterRead", OpenReason::DynamicBootstrap),
    ] {
        let id = method(&out, name);
        assert!(
            out.open
                .iter()
                .any(|s| s.method == id && s.reason == reason),
            "{name}"
        );
        assert_eq!(out.data.methods[id.0 as usize].top, effects::TopMask::ALL);
    }
    let reflect = out.data.methods[method(&out, "reflectAfterRead").0 as usize];
    let call = out.data.calls[reflect.calls.start as usize];
    assert_eq!(
        out.text(out.foreign(direct(&call)).unwrap().name),
        "forName"
    );
    assert_eq!(
        out.data.methods[direct(&call).0 as usize].top,
        effects::TopMask::ALL
    );
}

#[test]
fn missing_provider_is_an_explicit_unknown_subject_and_foreign_phases_remain_top() {
    let demands = [ClassDemand {
        authority: 0,
        owner: "finitecase/Probe",
    }];
    let mut missing = Provider::new();
    missing.unavailable = true;
    let out = produce(&demands, &mut missing, Limits::default()).unwrap();
    assert_eq!(out.methods.len(), 0);
    assert_eq!(out.phases.len(), 1);
    assert_eq!(out.phases[0].kind, ForeignKind::UnavailableClass);
    assert_eq!(out.data.methods[0].top, effects::TopMask::ALL);
    let out = one(&demands);
    assert!(
        out.phases
            .iter()
            .any(|m| m.kind == ForeignKind::ClassInitialization)
    );
    for row in out
        .phases
        .iter()
        .filter(|m| m.kind == ForeignKind::ClassInitialization)
    {
        assert_eq!(
            out.data.methods[row.method.0 as usize].top,
            effects::TopMask::ALL
        );
        assert_eq!(
            out.data.methods[row.method.0 as usize].subject.kind,
            effects::SubjectKind::RuntimePhase
        );
    }
}

#[test]
fn authority_class_hash_provider_and_structural_corruption_fail_closed() {
    let demands = [ClassDemand {
        authority: 0,
        owner: "finitecase/Probe",
    }];
    let mut provider = Provider::new();
    provider.bad_hash = true;
    assert!(matches!(
        produce(&demands, &mut provider, Limits::default()),
        Err(Error::ClassHash)
    ));
    let wrong = [ClassDemand {
        authority: 0,
        owner: "different/Probe",
    }];
    assert!(matches!(
        produce(&wrong, &mut Provider::new(), Limits::default()),
        Err(Error::ClassOwner)
    ));
    let mut bytes = PROBE.to_vec();
    let class = binary::parse_class(PROBE, binary::Limits::default()).unwrap();
    let code = class
        .method("readInt", Some("([II)I"))
        .unwrap()
        .code
        .unwrap();
    let at = code.as_ptr() as usize - PROBE.as_ptr() as usize;
    bytes[at + 2] = 202; // reserved opcode, resealed class hash cannot repair code
    let mut malformed = Provider::new();
    malformed.bytes = bytes.into();
    assert!(matches!(
        produce(&demands, &mut malformed, Limits::default()),
        Err(Error::Binary(_))
    ));
    let twice = [demands[0], demands[0]];
    let mut changed = Provider::new();
    changed.alternate = true;
    assert!(matches!(
        produce(&twice, &mut changed, Limits::default()),
        Err(Error::ConflictingProvider)
    ));
}

#[test]
fn cache_references_and_rows_are_bounded_without_dropping_partial_effects() {
    let demands = [ClassDemand {
        authority: 0,
        owner: "finitecase/Probe",
    }];
    for limits in [
        Limits {
            class_bytes: 100,
            ..Default::default()
        },
        Limits {
            references: 2,
            ..Default::default()
        },
        Limits {
            rows: 20,
            ..Default::default()
        },
        Limits {
            retained_bytes: 100,
            ..Default::default()
        },
    ] {
        assert!(matches!(
            produce(&demands, &mut Provider::new(), limits),
            Err(Error::Budget)
        ));
    }
    let a = one(&demands);
    let b = one(&demands);
    assert_eq!(a.data.calls, b.data.calls);
    assert_eq!(a.data.methods, b.data.methods);
    assert_eq!(a.data.reads, b.data.reads);
    assert_eq!(a.data.writes, b.data.writes);
    let separate = [
        ClassDemand {
            authority: 0,
            owner: "finitecase/Probe",
        },
        ClassDemand {
            authority: 1,
            owner: "finitecase/Probe",
        },
    ];
    let out = one(&separate);
    assert_eq!(out.roots.len(), 96);
    assert_eq!(out.blobs.len(), 2, "contextual bindings remain distinct");
    let ids: Vec<_> = out
        .classes
        .iter()
        .enumerate()
        .filter(|(_, c)| out.text(c.owner) == "finitecase/Probe")
        .map(|(id, _)| id)
        .collect();
    assert_eq!(ids.len(), 2);
    assert_ne!(out.classes[ids[0]].authority, out.classes[ids[1]].authority);
}

#[test]
fn normalized_instruction_axiom_closes_local_primitive_channels_but_not_vm_boundary() {
    let demands = [ClassDemand {
        authority: 0,
        owner: "finitecase/Probe",
    }];
    let axiom = RuntimeAxiom::normalized_test_token(0);
    let out =
        produce_with_axiom(&demands, &mut Provider::new(), Limits::default(), &axiom).unwrap();
    for name in [
        "readInt",
        "readLong",
        "readFloat",
        "readDouble",
        "readByte",
        "readBoolean",
        "readChar",
        "readShort",
        "length",
        "newInt",
        "divideInt",
        "remainderLong",
    ] {
        let id = method(&out, name);
        let row = out.data.methods[id.0 as usize];
        assert!(!row.top.contains(effects::Channel::Calls), "{name}");
        assert!(!row.top.contains(effects::Channel::Reads), "{name}");
        assert!(!row.top.contains(effects::Channel::Writes), "{name}");
        assert!(row.top.contains(effects::Channel::Initializes));
        assert!(row.top.contains(effects::Channel::Throws));
        assert!(row.top.contains(effects::Channel::External));
        assert_eq!(row.calls.len, 0);
        assert!(
            out.data.writes[row.writes.checked(out.data.writes.len()).unwrap()]
                .iter()
                .all(|w| w.kind == effects::StorageKind::RuntimeState)
        );
        let boundary = out.data.initializes
            [row.initializes.checked(out.data.initializes.len()).unwrap()]
        .iter()
        .find(|id| {
            out.phase(**id)
                .is_some_and(|phase| phase.kind == ForeignKind::RuntimeBoundary)
        })
        .unwrap();
        assert_eq!(
            out.data.methods[boundary.0 as usize].top,
            effects::TopMask::ALL
        );
    }
    for name in [
        "readReference",
        "writeInt",
        "writeReference",
        "monitorAfterRead",
        "dynamicAfterRead",
        "opaque",
    ] {
        assert_eq!(
            out.data.methods[method(&out, name).0 as usize].top,
            effects::TopMask::ALL,
            "{name}"
        );
    }
    let foreign = [ClassDemand {
        authority: 1,
        owner: "finitecase/Probe",
    }];
    let out =
        produce_with_axiom(&foreign, &mut Provider::new(), Limits::default(), &axiom).unwrap();
    assert_eq!(
        out.data.methods[method(&out, "readInt").0 as usize].top,
        effects::TopMask::ALL,
        "another authority cannot borrow the axiom"
    );
}

#[test]
fn wrong_instruction_contract_or_producer_rejects_before_platform_io() {
    use selector_runtime_platform::PlatformOptions;
    let options = PlatformOptions {
        manifest: "/does/not/exist".into(),
        contexts: "/does/not/exist".into(),
        producer: Default::default(),
    };
    assert!(
        RuntimeAxiom::admit(
            &options,
            "wrong-contract",
            RuntimeAxiom::producer(),
            &[(0, "context")]
        )
        .is_err()
    );
    assert!(RuntimeAxiom::admit(&options, axiom::CONTRACT, [0; 32], &[(0, "context")]).is_err());
}

#[test]
fn truncated_summary_value_and_argument_budgets_never_certify_an_incomplete_inventory() {
    let demands = [ClassDemand {
        authority: 0,
        owner: "finitecase/Probe",
    }];
    let axiom = RuntimeAxiom::normalized_test_token(0);
    for max_values in [0, 1] {
        let mut limits = Limits::default();
        limits.binary.max_values = max_values;
        let out = produce_with_axiom(&demands, &mut Provider::new(), limits, &axiom).unwrap();
        let id = method(&out, "branchAndCatch");
        assert_eq!(out.data.methods[id.0 as usize].top, effects::TopMask::ALL);
        assert!(
            out.open
                .iter()
                .any(|site| site.method == id
                    && site.reason == OpenReason::IncompleteEffectInventory)
        );
    }
}

#[test]
fn labeled_legacy_subroutine_mutants_remain_open_despite_structural_acceptance() {
    let demands = [ClassDemand {
        authority: 0,
        owner: "finitecase/Probe",
    }];
    let axiom = RuntimeAxiom::normalized_test_token(0);
    let class = binary::parse_class(PROBE, binary::Limits::default()).unwrap();
    let code = class
        .method("readInt", Some("([II)I"))
        .unwrap()
        .code
        .unwrap();
    let start = code.as_ptr() as usize - PROBE.as_ptr() as usize;
    for replacement in [[168, 0, 3, 172], [169, 0, 3, 172], [196, 169, 0, 0]] {
        // These are explicitly normalized corruption/control fixtures, not
        // compiler-generated Java output or a claim they pass JVM verification.
        let mut changed = PROBE.to_vec();
        changed[start..start + 4].copy_from_slice(&replacement);
        let mut provider = Provider::new();
        provider.bytes = changed.into();
        let out = produce_with_axiom(&demands, &mut provider, Limits::default(), &axiom).unwrap();
        let id = method(&out, "readInt");
        assert_eq!(out.data.methods[id.0 as usize].top, effects::TopMask::ALL);
        assert!(
            out.open
                .iter()
                .any(|site| site.method == id && site.reason == OpenReason::UnsupportedInstruction)
        );
    }
}

#[test]
#[ignore = "requires explicit full captured platform; never probes the host by name"]
fn actual_declared_image_admits_only_context_bound_instruction_axiom() {
    use selector_runtime_platform::PlatformOptions;
    let manifest: std::path::PathBuf = std::env::var_os("SELECTOR_PLATFORM_MANIFEST")
        .expect("explicit manifest")
        .into();
    let value: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&manifest).unwrap()).unwrap();
    let context = value["context_ids"][0].as_str().unwrap();
    let options = PlatformOptions {
        manifest,
        contexts: std::env::var_os("SELECTOR_PLATFORM_CONTEXTS")
            .expect("explicit original contexts")
            .into(),
        producer: selector_types::ContentHash::from_hex(value["producer_sha256"].as_str().unwrap())
            .unwrap(),
    };
    let axiom = RuntimeAxiom::admit(
        &options,
        axiom::CONTRACT,
        RuntimeAxiom::producer(),
        &[(0, context)],
    )
    .unwrap();
    assert!(!axiom.receipt().runtime_isolation_proven);
    let demands = [ClassDemand {
        authority: 0,
        owner: "finitecase/Probe",
    }];
    let out =
        produce_with_axiom(&demands, &mut Provider::new(), Limits::default(), &axiom).unwrap();
    let row = out.data.methods[method(&out, "readInt").0 as usize];
    assert!(!row.top.contains(effects::Channel::Writes));
    assert!(row.top.contains(effects::Channel::Initializes));
    assert!(
        out.data.initializes[row.initializes.checked(out.data.initializes.len()).unwrap()]
            .iter()
            .any(|id| out
                .phase(*id)
                .is_some_and(|phase| phase.kind == ForeignKind::RuntimeBoundary))
    );
    assert!(
        RuntimeAxiom::admit(
            &options,
            axiom::CONTRACT,
            RuntimeAxiom::producer(),
            &[(0, "not-a-captured-context")]
        )
        .is_err()
    );
}

#[test]
fn exact_reachable_roots_retain_handlers_and_static_dependencies_without_projecting_metadata_seeds()
{
    struct Exact {
        bytes: Arc<[u8]>,
        lookups: Vec<String>,
    }
    impl ClassProvider for Exact {
        fn class(&mut self, d: ClassDemand<'_>) -> Result<Option<ProvidedClass>, Error> {
            self.lookups.push(d.owner.to_owned());
            Ok((d.owner == "finitecase/Probe").then(|| ProvidedClass {
                bytes: self.bytes.clone(),
                class_sha256: Sha256::digest(&self.bytes).into(),
                authority: d.authority,
                provider: 0,
                binding_sha256: [1; 32],
            }))
        }
    }
    let roots = [RootMethodDemand {
        authority: 0,
        owner: "finitecase/Probe",
        name: "branchAndCatch",
        descriptor: "([ILjava/lang/Runnable;)I",
    }];
    // Descriptor comes from the actual class inventory, not source arity.
    let class = binary::parse_class(PROBE, Default::default()).unwrap();
    let actual = class.method("branchAndCatch", None).unwrap();
    let roots = [RootMethodDemand {
        descriptor: actual.descriptor,
        ..roots[0]
    }];
    let metadata = [RootMethodDemand {
        authority: 0,
        owner: "finitecase/Probe",
        name: "writeInt",
        descriptor: class.method("writeInt", None).unwrap().descriptor,
    }];
    let mut provider = Exact {
        bytes: Arc::from(PROBE),
        lookups: Vec::new(),
    };
    let out = produce_reachable(
        &roots,
        &metadata,
        &mut provider,
        ReachabilityLimits::default(),
        None,
    )
    .unwrap();
    let root = out.data.methods[out.roots[0].0 as usize];
    assert_eq!(root.calls.len, 3);
    assert_eq!(root.writes.len, 2);
    assert!(
        out.projected[method(&out, "readInt").0 as usize],
        "exact static dependency projected"
    );
    assert!(
        !out.projected[method(&out, "writeInt").0 as usize],
        "metadata seed never drives execution"
    );
    assert!(
        out.methods.len() < 48,
        "no class-wide unused body expansion"
    );
    assert_eq!(
        provider
            .lookups
            .iter()
            .filter(|name| name.as_str() == "finitecase/Probe")
            .count(),
        1
    );
    assert!(
        out.data
            .methods
            .iter()
            .all(|m| m.top == effects::TopMask::ALL)
    );
    effects::validate(&out.data, out.bounds(), effects::Limits::default()).unwrap();
}

#[test]
fn reachable_work_denial_retains_the_exact_subject_as_top_without_projecting_its_body() {
    let class = binary::parse_class(PROBE, Default::default()).unwrap();
    let actual = class.method("readInt", None).unwrap();
    let roots = [RootMethodDemand {
        authority: 0,
        owner: class.name,
        name: actual.name,
        descriptor: actual.descriptor,
    }];
    for (max_method_work, max_instruction_work) in [(0, usize::MAX), (4, 0)] {
        let out = produce_reachable(
            &roots,
            &[],
            &mut Provider::new(),
            ReachabilityLimits {
                max_method_work,
                max_instruction_work,
                ..Default::default()
            },
            None,
        )
        .unwrap();
        assert_eq!(out.roots.len(), 1);
        let id = out.roots[0];
        assert_eq!(
            out.foreign(id).unwrap().descriptor.len,
            actual.descriptor.len() as u32
        );
        assert_eq!(out.data.methods[id.0 as usize].top, effects::TopMask::ALL);
        assert!(!out.projected[id.0 as usize]);
        assert!(
            out.open
                .iter()
                .any(|row| row.method == id && row.reason == OpenReason::AdmissionBudget)
        );
    }
}

#[test]
fn genuine_factories_create_separate_normalized_adapters_without_eager_invocation_or_bootstrap_authority()
 {
    let bytes: Arc<[u8]> = Arc::from(
        include_bytes!("../../../fixtures/binary/classes/fixture/Probe.class").as_slice(),
    );
    struct Real(Arc<[u8]>);
    impl ClassProvider for Real {
        fn class(&mut self, d: ClassDemand<'_>) -> Result<Option<ProvidedClass>, Error> {
            Ok(Some(ProvidedClass {
                bytes: self.0.clone(),
                class_sha256: Sha256::digest(&self.0).into(),
                authority: d.authority,
                provider: 0,
                binding_sha256: [1; 32],
            }))
        }
    }
    let demands = [ClassDemand {
        authority: 0,
        owner: "fixture/Probe",
    }];
    let out = produce(&demands, &mut Real(bytes), Limits::default()).unwrap();
    let factory = method(&out, "indy");
    let row = out.data.methods[factory.0 as usize];
    assert_eq!(row.calls.len, 0, "creation never invokes implementation");
    assert_eq!(row.creations.len, 1);
    let creation = out.data.creations[row.creations.start as usize];
    assert_eq!(
        creation.sam, NONE,
        "no standard-bootstrap authority was admitted"
    );
    let adapter = &out.adapters[out.data.methods[creation.implementation.0 as usize]
        .subject
        .index as usize];
    assert_eq!(adapter.enclosing_method, factory);
    assert!(adapter.identity_mapping);
    assert!(!adapter.resolved);
    let body = out.data.methods[adapter.method.0 as usize];
    assert_eq!(body.calls.len, 1);
    assert_eq!(body.top, effects::TopMask::ALL);
    assert_eq!(
        out.foreign(adapter.implementation).unwrap().method,
        adapter.implementation
    );
    assert_eq!(
        out.data.methods[factory.0 as usize].calls.len, 0,
        "adapter rows remain outside factory range"
    );
    assert_eq!(creation.captures.len, adapter.normalized_captures);
    effects::validate(&out.data, out.bounds(), effects::Limits::default()).unwrap();
}
