//! Admitted-IR protocol control, not a real compiler/JVM/runtime authority.
use selector_effect_plan as planner;
use selector_effects::*;
use selector_effects_codec as wire;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Temp(std::path::PathBuf);
impl Drop for Temp {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

#[test]
fn checked_wire_owner_and_world_binding_survive_bounded_materialization() {
    let roots = [
        planner::Root {
            key: [1; 32],
            method: MethodId(0),
        },
        planner::Root {
            key: [2; 32],
            method: MethodId(1),
        },
    ];
    let h = |n| wire::Hash([n; 32]);
    let binding = wire::Binding {
        producer: h(1),
        facts: h(2),
        graph: h(3),
        runtime: h(4),
        inputs: h(5),
        root_universe: wire::Hash(planner::catalogue_identity(&roots)),
        contracts: h(6),
        member_authority: h(7),
        fact_nodes: 2,
        fact_symbols: 2,
        fact_operations: 0,
        roots: 2,
    };
    let texts = [
        wire::TextRange { start: 0, len: 3 },
        wire::TextRange { start: 3, len: 8 },
    ];
    let contexts = [wire::ContextKey {
        name: 0,
        inputs: h(8),
    }];
    let members = [0, 1].map(|i| wire::MemberKey {
        identity: wire::MemberIdentity::FactSymbol,
        fact_symbol: i,
        context: 0,
        provider: NONE,
        class: wire::Hash::default(),
        owner: NONE,
        name: NONE,
        descriptor: NONE,
        kind: wire::MemberKind::StaticField,
        canonical: true,
    });
    let authorities = [wire::AuthorityKey {
        producer: h(1),
        contract: h(6),
        kind: wire::AuthorityKind::ReviewedContract,
        name: 1,
    }];
    let mut data = CapsuleData::default();
    for i in 0..2 {
        let mut method = MethodRow::unknown(
            SubjectRef {
                kind: SubjectKind::FactNode,
                index: i,
            },
            0,
            0,
            0,
            0,
        );
        method.top = TopMask::NONE;
        data.methods.push(method);
    }
    data.methods[0].reads = Range { start: 0, len: 1 };
    data.methods[1].writes = Range { start: 0, len: 1 };
    data.reads.push(StorageRef {
        kind: StorageKind::StaticField,
        member: 0,
        base: Origin::ANY,
    });
    data.writes.push(StorageRef {
        kind: StorageKind::StaticField,
        member: 1,
        base: Origin::ANY,
    });
    let snapshot = wire::Snapshot {
        binding,
        keys: wire::KeyTables {
            text: b"ctxprotocol",
            strings: &texts,
            contexts: &contexts,
            providers: &[],
            foreign_methods: &[],
            members: &members,
            classes: &[],
            authorities: &authorities,
            exceptions: &[],
            externals: &[],
            sites: &[],
            sams: &[],
            adapters: &[],
            bridge_proofs: &[],
            phases: &[],
        },
        effects: &data,
    };
    let temp = Temp(std::env::temp_dir().join(format!(
        "selector-effect-plan-wire-{}-{}.bin",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    )));
    let artifact = wire::write(&temp.0, &snapshot, wire::Limits::default()).unwrap();
    let checked = wire::open(&temp.0, binding, wire::Limits::default()).unwrap();
    let minimum = checked.minimum_materialized_bytes().unwrap();
    let retained = checked
        .materialize(selector_effects::Limits::default(), minimum + 4096)
        .unwrap();
    assert_eq!(retained.wire().identity(), artifact);
    assert_eq!(retained.wire().binding(), binding);
    let canonical = [true, true];
    let changes = planner::Changes {
        methods: vec![MethodId(1)],
        classes: vec![],
    };
    let wb = planner::WorldBinding {
        producer: binding.producer.0,
        facts: binding.facts.0,
        graph: binding.graph.0,
        runtime: binding.runtime.0,
        inputs: binding.inputs.0,
        catalogue: binding.root_universe.0,
        contracts: binding.contracts.0,
        member_authority: binding.member_authority.0,
        capsules: artifact.0,
        root_count: binding.roots,
    };
    let world = planner::World {
        capsules: retained.capsules(),
        binding: wb,
        roots: &roots,
        changes: &changes,
        canonical_members: &canonical,
        ambient: planner::AmbientCoverage::NoAdditionalRunnableEntries {
            contract: binding.contracts.0,
        },
        transport_bytes: retained.transport_bytes(),
    };
    let plan = planner::plan(world, planner::PlanLimits::default()).unwrap();
    assert_eq!(plan.decisions()[0].decision, planner::Decision::Excluded);
    assert_eq!(plan.decisions()[1].decision, planner::Decision::Retained);
    assert!(plan.metrics().charged_bytes >= retained.owned_bytes() as u64);
    plan.validate(world).unwrap();
    let mut transplant = world;
    transplant.binding.facts = [99; 32];
    assert!(plan.validate(transplant).is_err());
    let mut transplant = world;
    transplant.canonical_members = &[true, false];
    assert!(plan.validate(transplant).is_err());
}
