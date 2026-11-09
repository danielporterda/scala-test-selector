use super::*;

struct Build {
    data: CapsuleData,
    roots: Vec<Root>,
    changes: Changes,
    canonical: Vec<bool>,
}
struct Owned {
    capsules: Capsules,
    roots: Vec<Root>,
    changes: Changes,
    canonical: Vec<bool>,
    binding: WorldBinding,
}
impl Build {
    fn new(n: usize) -> Self {
        let mut data = CapsuleData::default();
        for i in 0..n {
            let mut m = MethodRow::unknown(
                SubjectRef {
                    kind: SubjectKind::FactNode,
                    index: i as u32,
                },
                0,
                0,
                0,
                0,
            );
            m.top = TopMask::NONE;
            data.methods.push(m);
        }
        Self {
            data,
            roots: Vec::new(),
            changes: Changes::default(),
            canonical: vec![true; 8],
        }
    }
    fn root(&mut self, method: u32) {
        let key = [(self.roots.len() + 1) as u8; 32];
        self.roots.push(Root {
            key,
            method: MethodId(method),
        });
    }
    fn changed(&mut self, method: u32) {
        self.changes.methods.push(MethodId(method));
        self.changes.methods.sort_unstable();
        self.changes.methods.dedup();
    }
    fn top(&mut self, method: usize, c: Channel) {
        self.data.methods[method].top.insert(c);
    }
    fn storage(&mut self, method: usize, write: bool, member: u32, base: Origin) {
        let row = StorageRef {
            kind: if base == Origin::ANY {
                StorageKind::StaticField
            } else {
                StorageKind::InstanceField
            },
            member,
            base,
        };
        self.storage_row(method, write, row);
    }
    fn storage_row(&mut self, method: usize, write: bool, row: StorageRef) {
        let target = if write {
            &mut self.data.writes
        } else {
            &mut self.data.reads
        };
        let range = Range {
            start: target.len() as u32,
            len: 1,
        };
        target.push(row);
        if write {
            self.data.methods[method].writes = range;
        } else {
            self.data.methods[method].reads = range;
        }
    }
    fn call(
        &mut self,
        caller: usize,
        target: u32,
        kind: CallKind,
        receiver: Origin,
        args: &[Origin],
        captures: &[Origin],
    ) {
        let arguments = Range {
            start: self.data.origins.len() as u32,
            len: args.len() as u32,
        };
        self.data.origins.extend_from_slice(args);
        self.data
            .callable_values
            .extend(args.iter().map(|_| ValueRef::UNKNOWN));
        let capture_range = Range {
            start: self.data.origins.len() as u32,
            len: captures.len() as u32,
        };
        self.data.origins.extend_from_slice(captures);
        self.data
            .callable_values
            .extend(captures.iter().map(|_| ValueRef::UNKNOWN));
        let r = &mut self.data.methods[caller].calls;
        if r.len == 0 {
            r.start = self.data.calls.len() as u32;
        } else {
            assert_eq!((r.start + r.len) as usize, self.data.calls.len());
        }
        self.data.calls.push(CallRow {
            site: self.data.calls.len() as u32,
            target: CallTarget::Direct(MethodId(target)),
            kind,
            receiver,
            receiver_value: ValueRef::CONSTANT,
            result: NONE,
            arguments,
            captures: capture_range,
        });
        r.len += 1;
    }
    fn init(&mut self, caller: usize, target: u32) {
        let r = &mut self.data.methods[caller].initializes;
        if r.len == 0 {
            r.start = self.data.initializes.len() as u32;
        }
        self.data.initializes.push(MethodId(target));
        r.len += 1;
    }
    fn escape(&mut self, method: usize, origin: Origin, sink: EscapeSink, index: u32) {
        let r = Range {
            start: self.data.escapes.len() as u32,
            len: 1,
        };
        self.data.escapes.push(EscapeRef {
            origin,
            sink,
            index,
        });
        self.data.methods[method].escapes = r;
    }
    fn finish(self, version: u8) -> Owned {
        let bounds = RefBounds {
            fact_nodes: self.data.methods.len() as u32,
            foreign_methods: self
                .data
                .methods
                .iter()
                .filter(|m| m.subject.kind == SubjectKind::ForeignMethod)
                .map(|m| m.subject.index + 1)
                .max()
                .unwrap_or(0),
            authorities: 1,
            members: self.canonical.len() as u32,
            classes: 8,
            exceptions: 8,
            externals: 8,
            sites: (self.data.calls.len() + self.data.creations.len()).max(1) as u32,
            sams: self.data.sam_arities.len() as u32,
            adapters: 0,
            bridge_proofs: self.data.callable_bridges.len() as u32,
            phases: 0,
        };
        let capsules =
            Capsules::new(self.data, bounds, selector_effects::Limits::default()).unwrap();
        let id = [version.max(1); 32];
        let binding = WorldBinding {
            producer: [1; 32],
            facts: id,
            graph: id,
            runtime: [2; 32],
            inputs: [3; 32],
            catalogue: catalogue_identity(&self.roots),
            contracts: [4; 32],
            member_authority: [5; 32],
            capsules: id,
            root_count: self.roots.len() as u32,
        };
        Owned {
            capsules,
            roots: self.roots,
            changes: self.changes,
            canonical: self.canonical,
            binding,
        }
    }
}
impl Owned {
    fn world(&self) -> World<'_> {
        World {
            capsules: &self.capsules,
            binding: self.binding,
            roots: &self.roots,
            changes: &self.changes,
            canonical_members: &self.canonical,
            ambient: AmbientCoverage::NoAdditionalRunnableEntries { contract: [9; 32] },
            transport_bytes: 0,
        }
    }
}

impl Build {
    fn create(&mut self, owner: usize, dest: u32, target: u32, sam: u32, captures: &[ValueRef]) {
        self.data.methods[owner].locals = self.data.methods[owner].locals.max(dest + 1);
        let cap = Range {
            start: self.data.origins.len() as u32,
            len: captures.len() as u32,
        };
        self.data
            .origins
            .extend(captures.iter().map(|_| Origin::ANY));
        self.data.callable_values.extend_from_slice(captures);
        let r = &mut self.data.methods[owner].creations;
        if r.len == 0 {
            r.start = self.data.creations.len() as u32;
        } else {
            assert_eq!((r.start + r.len) as usize, self.data.creations.len());
        }
        self.data.creations.push(CallableCreation {
            site: self.data.creations.len() as u32,
            destination: dest,
            implementation: MethodId(target),
            sam,
            receiver: Origin::ANY,
            receiver_value: ValueRef::CONSTANT,
            captures: cap,
        });
        r.len += 1;
    }
    fn flow(&mut self, owner: usize, kind: ValueFlowKind, value: ValueRef, index: u32) {
        let r = &mut self.data.methods[owner].value_flows;
        if r.len == 0 {
            r.start = self.data.value_flows.len() as u32;
        } else {
            assert_eq!((r.start + r.len) as usize, self.data.value_flows.len());
        }
        self.data.value_flows.push(ValueFlow { kind, value, index });
        r.len += 1;
    }
    fn invoke(&mut self, owner: usize, value: ValueRef, sam: u32) {
        self.call(owner, 0, CallKind::Callback, Origin::ANY, &[], &[]);
        self.data.calls.last_mut().unwrap().target = CallTarget::Callable { value, sam };
    }
    fn bridge(&mut self, creation: u32, sam: u32, implementation: u32) {
        self.data.methods[implementation as usize].subject = SubjectRef {
            kind: SubjectKind::ForeignMethod,
            index: 0,
        };
        self.data.callable_bridges.push(CallableBridge {
            creation,
            sam,
            implementation: MethodId(implementation),
            proof: self.data.callable_bridges.len() as u32,
        });
    }
    fn result_call(&mut self, owner: usize, target: u32, values: &[ValueRef], result: u32) {
        let start = self.data.origins.len();
        self.call(
            owner,
            target,
            CallKind::Static,
            Origin::ANY,
            &vec![Origin::ANY; values.len()],
            &[],
        );
        self.data.callable_values[start..start + values.len()].copy_from_slice(values);
        self.data.calls.last_mut().unwrap().result = result;
        self.data.methods[owner].locals = self.data.methods[owner].locals.max(result + 1);
    }
}

fn returned_factory(active: bool, wrong_sam: bool) -> Owned {
    let mut b = Build::new(5);
    b.root(0);
    b.root(4);
    b.data.sam_arities = vec![0, 0];
    b.data.methods[1].arity = 1;
    b.data.methods[2].captures = 1;
    b.create(0, 0, 3, 0, &[]);
    b.result_call(0, 1, &[ValueRef::local(0)], 1);
    if active {
        b.invoke(0, ValueRef::local(1), u32::from(wrong_sam));
    }
    b.create(1, 0, 2, 0, &[ValueRef::argument(0)]);
    b.flow(1, ValueFlowKind::Return, ValueRef::local(0), 0);
    b.invoke(2, ValueRef::capture(0), 0);
    b.changed(3);
    b.finish(1)
}

#[test]
fn returned_factory_keeps_its_known_captured_callback_without_dynamic_contexts() {
    let o = returned_factory(true, false);
    let p = run(&o);
    assert_eq!(status(&p, 0), Decision::Retained);
    assert_eq!(p.decisions()[0].reason, Reason::ChangedDependency);
    assert_eq!(p.decisions()[0].top, TopMask::NONE);
    assert_eq!(p.decisions()[0].reachable_methods, 4);
    assert_eq!(status(&p, 1), Decision::Excluded);
}

#[test]
fn creation_and_return_without_activation_preserves_dormant_callback_body() {
    let p = run(&returned_factory(false, false));
    assert_eq!(status(&p, 0), Decision::Excluded);
    assert_eq!(p.decisions()[0].reachable_methods, 2);
}

#[test]
fn equal_arity_different_sam_is_not_an_invocation_certificate() {
    let p = run(&returned_factory(true, true));
    assert_eq!(status(&p, 0), Decision::Retained);
    assert!(p.decisions()[0].top.contains(Channel::Calls));
}

fn bridged_capture(changed: u32, with_bridge: bool) -> Owned {
    // Admitted-IR protocol: bridge method 6 has the original closure as its
    // receiver. It invokes the original SAM, whose implementation uses its
    // creator-bound capture. A second dormant payload shares the same template.
    let mut b = Build::new(7);
    b.root(0);
    b.root(5);
    b.data.sam_arities = vec![0, 0];
    b.data.methods[2].captures = 1;
    b.create(0, 0, 3, 0, &[]);
    b.create(0, 1, 4, 0, &[]);
    b.create(0, 2, 2, 0, &[ValueRef::local(0)]);
    b.create(0, 3, 2, 0, &[ValueRef::local(1)]);
    b.invoke(0, ValueRef::local(2), 1);
    b.invoke(2, ValueRef::capture(0), 0);
    b.invoke(6, ValueRef::RECEIVER, 0);
    if with_bridge {
        b.bridge(2, 1, 6);
    }
    b.changed(changed);
    b.finish(1)
}

#[test]
fn default_bridge_invokes_the_same_payload_and_its_creator_bound_capture() {
    let p = run(&bridged_capture(3, true));
    assert_eq!(status(&p, 0), Decision::Retained);
    assert_eq!(p.decisions()[0].top, TopMask::NONE);
    assert_eq!(p.decisions()[0].reachable_methods, 4);
    assert_eq!(status(&p, 1), Decision::Excluded);
}

#[test]
fn default_bridge_does_not_activate_a_dormant_sibling_payload() {
    let p = run(&bridged_capture(4, true));
    assert_eq!(status(&p, 0), Decision::Excluded);
    assert_eq!(p.decisions()[0].top, TopMask::NONE);
}

#[test]
fn a_missing_default_bridge_remains_an_open_call() {
    let p = run(&bridged_capture(3, false));
    assert_eq!(status(&p, 0), Decision::Retained);
    assert!(p.decisions()[0].top.contains(Channel::Calls));
}

#[test]
fn default_bridge_native_effects_and_initialization_are_composed() {
    let mut b = Build::new(6);
    b.root(0);
    b.root(4);
    b.data.sam_arities = vec![0, 0];
    b.create(0, 0, 2, 0, &[]);
    b.invoke(0, ValueRef::local(0), 1);
    b.invoke(5, ValueRef::RECEIVER, 0);
    b.init(5, 3);
    b.storage(5, true, 0, Origin::ANY);
    b.storage(4, false, 0, Origin::ANY);
    b.bridge(0, 1, 5);
    b.changed(3);
    let p = run(&b.finish(1));
    assert_eq!(status(&p, 0), Decision::Retained);
    assert_eq!(p.decisions()[0].reachable_methods, 4);
    assert_eq!(status(&p, 1), Decision::Retained);
    assert_eq!(p.decisions()[1].reason, Reason::ChangedSharedStorage);
}

#[test]
fn code_survives_capture_memory_origin_widening() {
    let mut b = Build::new(5);
    b.root(0);
    b.root(4);
    b.data.sam_arities = vec![0];
    b.data.methods[1].arity = 1;
    b.data.methods[1].fresh_sites = 1;
    b.data.methods[2].captures = 1;
    b.create(0, 0, 3, 0, &[]);
    b.result_call(0, 1, &[ValueRef::local(0)], 1);
    b.invoke(0, ValueRef::local(1), 0);
    b.create(1, 0, 2, 0, &[ValueRef::argument(0)]);
    b.flow(1, ValueFlowKind::Return, ValueRef::local(0), 0);
    b.escape(1, Origin::fresh(0), EscapeSink::Return, 0);
    b.invoke(2, ValueRef::capture(0), 0);
    b.storage(3, true, 0, Origin::ANY);
    b.storage(4, false, 0, Origin::ANY);
    b.changed(3);
    let p = run(&b.finish(1));
    assert_eq!(p.decisions()[0].top, TopMask::NONE);
    assert_eq!(status(&p, 1), Decision::Retained);
    assert_eq!(p.decisions()[1].reason, Reason::ChangedSharedStorage);
}

#[test]
fn shared_heap_retains_creator_capture_coordinates_and_initial_uncertainty() {
    let mut b = Build::new(5);
    b.root(0);
    b.root(1);
    b.data.sam_arities = vec![0];
    b.data.methods[3].captures = 1;
    b.create(0, 0, 2, 0, &[]);
    b.create(0, 1, 3, 0, &[ValueRef::local(0)]);
    b.storage(0, true, 0, Origin::ANY);
    b.flow(0, ValueFlowKind::Store, ValueRef::local(1), 0);
    b.create(1, 1, 4, 0, &[]);
    b.data.methods[1].locals = 2;
    b.storage(1, false, 0, Origin::ANY);
    b.flow(1, ValueFlowKind::Load, ValueRef::local(0), 0);
    b.invoke(1, ValueRef::local(0), 0);
    b.invoke(3, ValueRef::capture(0), 0);
    b.changed(2);
    let o = b.finish(1);
    let mut budget = Budget::new(PlanLimits::default());
    let r = callables::resolve(o.world(), &mut budget).unwrap();
    assert!(
        r.edges
            .iter()
            .any(|e| e.root == 1 && e.caller == MethodId(3) && e.target == MethodId(2))
    );
    assert!(
        !r.edges
            .iter()
            .any(|e| e.root == 1 && e.target == MethodId(4))
    );
    assert!(r.top[1].contains(Channel::Calls));
    let p = run(&o);
    assert_eq!(status(&p, 1), Decision::Retained);
}

#[test]
fn missing_local_definition_does_not_become_an_empty_known_callback_set() {
    let mut b = Build::new(1);
    b.root(0);
    b.data.methods[0].locals = 1;
    b.data.sam_arities = vec![0];
    b.invoke(0, ValueRef::local(0), 0);
    let p = run(&b.finish(1));
    assert!(p.decisions()[0].top.contains(Channel::Calls));
}

#[test]
fn cyclic_callable_copy_without_a_creator_remains_unresolved() {
    let mut b = Build::new(1);
    b.root(0);
    b.data.methods[0].locals = 2;
    b.data.sam_arities = vec![0];
    b.flow(0, ValueFlowKind::Copy, ValueRef::local(1), 0);
    b.flow(0, ValueFlowKind::Copy, ValueRef::local(0), 1);
    b.invoke(0, ValueRef::local(0), 0);
    let p = run(&b.finish(1));
    assert!(p.decisions()[0].top.contains(Channel::Calls));
}

#[test]
fn callable_cell_budget_is_fail_closed() {
    let o = returned_factory(true, false);
    let mut limits = PlanLimits::default();
    limits.max_callable_cells = 1;
    assert!(plan(o.world(), limits).is_err());
}
fn status(p: &Plan, root: usize) -> Decision {
    p.decisions()[root].decision
}
fn run(o: &Owned) -> Plan {
    plan(o.world(), PlanLimits::default()).unwrap()
}

#[test]
fn closed_canonical_field_reader_is_disjoint_from_a_changed_finite_writer() {
    let mut b = Build::new(2);
    b.root(0);
    b.root(1);
    b.storage(0, false, 0, Origin::ANY);
    b.storage(1, true, 1, Origin::ANY);
    b.changed(1);
    let o = b.finish(1);
    let p = run(&o);
    assert_eq!(status(&p, 0), Decision::Excluded);
    assert_eq!(status(&p, 1), Decision::Retained);
    p.validate(o.world()).unwrap();
}

#[test]
fn bounded_opaque_write_keeps_all_readers_but_not_a_closed_no_read_root() {
    let mut b = Build::new(3);
    b.root(0);
    b.root(1);
    b.root(2);
    b.top(1, Channel::Writes);
    b.storage(2, false, 0, Origin::ANY);
    b.changed(1);
    let p = run(&b.finish(1));
    assert_eq!(status(&p, 0), Decision::Excluded);
    assert_eq!(status(&p, 1), Decision::Retained);
    assert_eq!(status(&p, 2), Decision::Retained);
    assert_eq!(p.decisions()[2].reason, Reason::ChangedSharedStorage);
}

#[test]
fn unknown_call_is_not_a_finite_write_capsule_and_retains_even_pure_control() {
    let mut b = Build::new(2);
    b.root(0);
    b.root(1);
    b.top(1, Channel::Calls);
    b.changed(0);
    let p = run(&b.finish(1));
    assert!(
        p.decisions()
            .iter()
            .all(|r| r.decision == Decision::Retained)
    );
    assert_eq!(p.decisions()[0].reason, Reason::ChangedDependency);
}

#[test]
fn unknown_call_can_invoke_changed_nonroot_code_then_write_a_readers_field() {
    let mut b = Build::new(3);
    b.root(0);
    b.root(1);
    b.storage(0, false, 0, Origin::ANY);
    b.top(1, Channel::Calls);
    b.changed(2);
    let p = run(&b.finish(1));
    assert_eq!(status(&p, 0), Decision::Retained);
    assert_eq!(p.decisions()[1].reason, Reason::ChangedDependency);
}

#[test]
fn top_read_retains_when_a_changed_finite_writer_can_feed_it() {
    let mut b = Build::new(2);
    b.root(0);
    b.root(1);
    b.top(0, Channel::Reads);
    b.storage(1, true, 3, Origin::ANY);
    b.changed(1);
    let p = run(&b.finish(1));
    assert_eq!(status(&p, 0), Decision::Retained);
}

#[test]
fn changed_return_through_unchanged_caller_can_change_shared_state() {
    let mut b = Build::new(3);
    b.root(0);
    b.root(1);
    b.storage(0, false, 0, Origin::ANY);
    b.storage(1, true, 0, Origin::ANY);
    b.call(1, 2, CallKind::Static, Origin::ANY, &[], &[]);
    b.changed(2);
    let p = run(&b.finish(1));
    assert_eq!(status(&p, 0), Decision::Retained);
    assert_eq!(p.decisions()[0].reason, Reason::ChangedSharedStorage);
}

#[test]
fn exact_callback_target_and_captures_participate_in_change_closure() {
    let mut b = Build::new(2);
    b.root(0);
    b.data.methods[1].captures = 1;
    b.call(0, 1, CallKind::Callback, Origin::ANY, &[], &[Origin::ANY]);
    b.changed(1);
    let p = run(&b.finish(1));
    assert_eq!(status(&p, 0), Decision::Retained);
    assert_eq!(p.decisions()[0].reachable_methods, 2);
}

#[test]
fn unknown_callback_and_missing_transitive_foreign_recipe_do_not_close() {
    let mut b = Build::new(3);
    b.root(0);
    b.call(0, 1, CallKind::Static, Origin::ANY, &[], &[]);
    b.call(1, 2, CallKind::Callback, Origin::ANY, &[], &[]);
    b.data.methods[2].top = TopMask::ALL;
    b.changed(2);
    let p = run(&b.finish(1));
    assert_eq!(status(&p, 0), Decision::Retained);
    assert_eq!(p.decisions()[0].top, TopMask::ALL);
}

fn fresh_case(escape: bool) -> Owned {
    let mut b = Build::new(3);
    b.root(0);
    b.root(1);
    b.data.methods[0].fresh_sites = 1;
    b.data.methods[1].fresh_sites = 1;
    b.data.methods[2].arity = 1;
    b.storage(0, false, 0, Origin::fresh(0));
    b.call(
        1,
        2,
        CallKind::Static,
        Origin::ANY,
        &[Origin::fresh(0)],
        &[],
    );
    b.storage(2, true, 0, Origin::argument(0));
    if escape {
        b.escape(1, Origin::fresh(0), EscapeSink::Return, 0);
    }
    b.changed(2);
    b.finish(1)
}
#[test]
fn receiver_argument_substitution_preserves_only_proven_non_escaping_fresh_sites() {
    let p = run(&fresh_case(false));
    assert_eq!(status(&p, 0), Decision::Excluded);
    let p = run(&fresh_case(true));
    assert_eq!(status(&p, 0), Decision::Retained);
}

#[test]
fn callee_local_fresh_is_not_a_globally_unique_allocation_identity() {
    let mut b = Build::new(3);
    b.root(0);
    b.root(1);
    b.data.methods[0].fresh_sites = 1;
    b.data.methods[2].fresh_sites = 1;
    b.storage(0, false, 0, Origin::fresh(0));
    b.storage(2, true, 0, Origin::fresh(0));
    b.call(1, 2, CallKind::Static, Origin::ANY, &[], &[]);
    b.changed(2);
    let p = run(&b.finish(1));
    assert_eq!(status(&p, 0), Decision::Retained);
}

#[test]
fn recursive_fresh_and_scc_backedges_are_not_private_instance_proofs() {
    let mut b = Build::new(2);
    b.root(0);
    b.root(1);
    b.data.methods[0].fresh_sites = 1;
    b.data.methods[1].fresh_sites = 1;
    b.storage(0, false, 0, Origin::fresh(0));
    b.storage(1, true, 0, Origin::fresh(0));
    b.call(1, 1, CallKind::Static, Origin::ANY, &[], &[]);
    b.changed(1);
    let p = run(&b.finish(1));
    assert_eq!(status(&p, 0), Decision::Retained);
    assert_eq!(p.metrics().components, 2);
}

#[test]
fn source_native_field_aliases_must_have_global_canonical_authority() {
    let mut b = Build::new(2);
    b.root(0);
    b.root(1);
    b.storage(0, false, 0, Origin::ANY);
    b.storage(1, true, 1, Origin::ANY);
    b.canonical[0] = false;
    b.changed(1);
    let p = run(&b.finish(1));
    assert_eq!(status(&p, 0), Decision::Retained);
    assert!(p.decisions()[0].top.contains(Channel::Reads));
}

#[test]
fn implicit_vm_state_cannot_be_hidden_from_ordinary_field_aliases() {
    let mut b = Build::new(2);
    b.root(0);
    b.root(1);
    b.storage(0, false, 0, Origin::ANY);
    b.storage_row(
        1,
        true,
        StorageRef {
            kind: StorageKind::RuntimeState,
            member: 1,
            base: Origin::ANY,
        },
    );
    b.changed(1);
    let p = run(&b.finish(1));
    assert_eq!(status(&p, 0), Decision::Retained);
}

#[test]
fn array_length_and_elements_stay_in_the_same_conservative_region() {
    let mut b = Build::new(2);
    b.root(0);
    b.root(1);
    let array = StorageRef {
        kind: StorageKind::ArrayElements,
        member: NONE,
        base: Origin::ANY,
    };
    b.storage_row(0, false, array);
    b.storage_row(1, true, array);
    b.changed(1);
    let p = run(&b.finish(1));
    assert_eq!(status(&p, 0), Decision::Retained);
}

#[test]
fn class_initialization_and_vm_exception_control_cannot_be_dropped() {
    let mut b = Build::new(3);
    b.root(0);
    b.root(1);
    b.init(1, 2);
    b.data.methods[2].throws = Range { start: 0, len: 1 };
    b.data.throws.push(0);
    b.changed(2);
    let p = run(&b.finish(1));
    assert_eq!(status(&p, 0), Decision::Retained);
    assert_eq!(p.decisions()[0].reason, Reason::ChangedControl);
}

#[test]
fn changed_code_can_be_observed_with_unchanged_normal_arguments() {
    let mut b = Build::new(3);
    b.root(0);
    b.root(1);
    b.storage(0, false, 0, Origin::ANY);
    b.storage(1, true, 0, Origin::ANY);
    b.data.methods[1].code_observations = Range { start: 0, len: 1 };
    b.data.code_observations.push(CodeRef {
        kind: CodeKind::Method,
        index: 2,
    });
    b.changed(2);
    let p = run(&b.finish(1));
    assert_eq!(status(&p, 0), Decision::Retained);
    assert_eq!(p.decisions()[1].reason, Reason::ChangedDependency);
}

#[test]
fn external_keys_do_not_disappear_behind_finite_heap_effects() {
    let mut b = Build::new(2);
    b.root(0);
    b.root(1);
    b.changed(1);
    b.data.methods[0].external = Range { start: 0, len: 1 };
    b.data.external.push(ExternalRef {
        kind: ExternalKind::Read,
        key: 0,
    });
    b.data.methods[1].external = Range { start: 1, len: 1 };
    b.data.external.push(ExternalRef {
        kind: ExternalKind::Write,
        key: 0,
    });
    let p = run(&b.finish(1));
    assert_eq!(status(&p, 0), Decision::Retained);
    assert_eq!(p.decisions()[0].reason, Reason::ChangedExternal);
}

#[test]
fn pairing_requires_both_revisions_and_exact_full_catalogue() {
    let mut b = Build::new(2);
    b.root(0);
    b.root(1);
    b.changed(1);
    let base = b.finish(1);
    let mut b = Build::new(2);
    b.root(0);
    b.root(1);
    b.changed(1);
    b.top(0, Channel::Reads);
    let head = b.finish(2);
    let (bp, hp) = (run(&base), run(&head));
    let pair = paired(&bp, base.world(), &hp, head.world()).unwrap();
    assert_eq!(pair.decisions()[0].decision, Decision::Retained);
    pair.validate(&bp, base.world(), &hp, head.world()).unwrap();
    let mut reduced = head.world();
    reduced.roots = &head.roots[..1];
    assert!(matches!(hp.validate(reduced), Err(Error::Catalogue)));
}

#[test]
fn proofs_reject_mutation_transplant_and_conflicting_duplicate_subjects() {
    let mut b = Build::new(1);
    b.root(0);
    let mut o = b.finish(1);
    let mut p = run(&o);
    p.decisions[0].decision = Decision::Retained;
    assert_eq!(p.validate(o.world()), Err(Error::Seal));
    let p = run(&o);
    o.binding.contracts = [8; 32];
    assert_eq!(p.validate(o.world()), Err(Error::Seal));
    let mut b = Build::new(2);
    b.root(0);
    b.data.methods[1].subject = b.data.methods[0].subject;
    assert!(matches!(
        plan(b.finish(1).world(), PlanLimits::default()),
        Err(Error::Binding)
    ));
}

#[test]
fn budget_exhaustion_is_an_error_never_a_truncated_exclusion_proof() {
    let mut b = Build::new(2);
    b.root(0);
    b.call(0, 1, CallKind::Static, Origin::ANY, &[], &[]);
    let o = b.finish(1);
    let mut limits = PlanLimits::default();
    limits.max_work = 1;
    assert!(matches!(plan(o.world(), limits), Err(Error::Budget)));
    limits = PlanLimits::default();
    limits.max_bytes = 8;
    assert!(matches!(plan(o.world(), limits), Err(Error::Budget)));
    limits = PlanLimits::default();
    limits.max_refs = 0;
    assert!(matches!(plan(o.world(), limits), Err(Error::Budget)));
}

#[test]
fn finite_abi_mismatch_cannot_be_reinterpreted_as_an_empty_target() {
    let mut b = Build::new(2);
    b.root(0);
    b.data.methods[1].arity = 1;
    b.call(0, 1, CallKind::Static, Origin::ANY, &[], &[]);
    let bounds = RefBounds {
        fact_nodes: 2,
        foreign_methods: 0,
        authorities: 1,
        members: 8,
        classes: 8,
        exceptions: 8,
        externals: 8,
        sites: 1,
        sams: 0,
        adapters: 0,
        bridge_proofs: 0,
        phases: 0,
    };
    assert!(Capsules::new(b.data, bounds, selector_effects::Limits::default()).is_err());
}

#[test]
fn a_suite_catalogue_is_not_an_ambient_entrypoint_absence_certificate() {
    let mut b = Build::new(2);
    b.root(0);
    b.root(1);
    b.changed(1);
    let o = b.finish(1);
    let p = run(&o);
    assert_eq!(status(&p, 0), Decision::Excluded);
    let mut w = o.world();
    w.ambient = AmbientCoverage::Unverified;
    let p = plan(w, PlanLimits::default()).unwrap();
    assert_eq!(status(&p, 0), Decision::Retained);
    assert_eq!(p.decisions()[0].reason, Reason::OpenUniverse);
}

#[test]
fn class_resource_observers_need_method_owner_coverage_not_only_class_seed_equality() {
    let mut b = Build::new(3);
    b.root(0);
    b.root(1);
    b.changed(2);
    b.storage(0, false, 0, Origin::ANY);
    b.storage(1, true, 0, Origin::ANY);
    b.data.methods[1].code_observations = Range { start: 0, len: 1 };
    b.data.code_observations.push(CodeRef {
        kind: CodeKind::Class,
        index: 7,
    });
    let p = run(&b.finish(1));
    assert_eq!(status(&p, 0), Decision::Retained);
}

#[test]
fn method_local_flow_ordinal_zero_never_rebinds_to_a_sibling_callee_write() {
    let mut b = Build::new(5);
    b.root(0);
    b.root(1);
    b.changed(4);
    b.storage(0, false, 0, Origin::ANY);
    b.call(1, 2, CallKind::Static, Origin::ANY, &[], &[]);
    b.call(1, 3, CallKind::Static, Origin::ANY, &[], &[]);
    b.storage(2, true, 1, Origin::ANY);
    b.storage(3, true, 0, Origin::ANY);
    b.call(3, 4, CallKind::Callback, Origin::ANY, &[], &[]);
    b.data.methods[2].flows = Range { start: 0, len: 1 };
    b.data.methods[3].flows = Range { start: 1, len: 1 };
    b.data.flows.push(FlowRef {
        source: Origin::ANY,
        sink: FlowSink::HeapWrite,
        via: 0,
        index: 0,
    });
    b.data.flows.push(FlowRef {
        source: Origin::ANY,
        sink: FlowSink::HeapWrite,
        via: 0,
        index: 0,
    });
    let p = run(&b.finish(1));
    assert_eq!(status(&p, 0), Decision::Retained);
}

#[test]
fn unknown_escape_cannot_hide_later_callback_activation_without_a_contract() {
    let mut b = Build::new(3);
    b.root(0);
    b.root(1);
    b.changed(2);
    b.storage(0, false, 0, Origin::ANY);
    b.top(1, Channel::Escapes);
    let p = run(&b.finish(1));
    assert_eq!(status(&p, 0), Decision::Retained);
    assert_eq!(p.decisions()[1].top, TopMask::ALL);
}

#[test]
fn retained_wire_ownership_is_charged_alongside_decoded_tables() {
    let mut b = Build::new(1);
    b.root(0);
    let o = b.finish(1);
    let p = run(&o);
    let mut w = o.world();
    w.transport_bytes = PlanLimits::default().max_bytes;
    assert!(matches!(plan(w, PlanLimits::default()), Err(Error::Budget)));
    assert_eq!(p.validate(w), Err(Error::Seal));
}
