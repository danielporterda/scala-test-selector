use selector_effects::*;
use selector_effects_codec::*;
use selector_effects_codec::{Limits, NONE};
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

thread_local! {static COUNT:Cell<Option<usize>>=const{Cell::new(None)};static LIVE:Cell<isize>=const{Cell::new(0)};}
struct Allocator;
unsafe impl GlobalAlloc for Allocator {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        COUNT.with(|c| {
            if let Some(n) = c.get() {
                c.set(Some(n + 1));
            }
        });
        let p = unsafe { System.alloc(l) };
        if !p.is_null() {
            LIVE.with(|v| v.set(v.get() + l.size() as isize));
        }
        p
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        unsafe { System.dealloc(p, l) }
        LIVE.with(|v| v.set(v.get() - l.size() as isize));
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 {
        COUNT.with(|c| {
            if let Some(n) = c.get() {
                c.set(Some(n + 1));
            }
        });
        let p = unsafe { System.realloc(p, l, n) };
        if !p.is_null() {
            LIVE.with(|v| v.set(v.get() + n as isize - l.size() as isize));
        }
        p
    }
}
#[global_allocator]
static ALLOCATOR: Allocator = Allocator;
static NEXT: AtomicU64 = AtomicU64::new(0);
struct Directory(PathBuf);
impl Directory {
    fn new() -> Self {
        let p = std::env::temp_dir().join(format!(
            "selector-effect-codec-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&p).unwrap();
        Self(p)
    }
    fn file(&self, n: &str) -> PathBuf {
        self.0.join(n)
    }
}
impl Drop for Directory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn h(n: u8) -> Hash {
    Hash([n; 32])
}
fn range(n: u32) -> Range {
    Range { start: 0, len: n }
}

#[derive(Clone)]
struct Fixture {
    binding: Binding,
    text: Vec<u8>,
    strings: Vec<TextRange>,
    contexts: Vec<ContextKey>,
    providers: Vec<ProviderKey>,
    foreign: Vec<ForeignMethod>,
    members: Vec<MemberKey>,
    classes: Vec<ClassKey>,
    authorities: Vec<AuthorityKey>,
    exceptions: Vec<ExceptionKey>,
    externals: Vec<ExternalKey>,
    sites: Vec<SiteKey>,
    sams: Vec<SamKey>,
    adapters: Vec<CallableAdapterKey>,
    bridge_proofs: Vec<CallableBridgeProofKey>,
    phases: Vec<PhaseKey>,
    data: CapsuleData,
}
impl Fixture {
    fn new() -> Self {
        let mut words = vec![
            "(Ljava/lang/Object;Ljava/lang/Object;)V",
            "()V",
            "()Lp/C;",
            "(Ljava/lang/Object;Ljava/lang/Object;)Lp/C;",
            "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;",
            "bootstrap",
            "factory",
            "specialized",
            "/capture.jar",
            "callee",
            "ctx",
            "p/C",
            "source",
            "vm",
            "évidence",
        ];
        words.sort_unstable();
        let id = |word: &str| words.binary_search(&word).unwrap() as u32;
        let mut text = Vec::new();
        let mut strings = Vec::new();
        for word in &words {
            strings.push(TextRange {
                start: text.len() as u32,
                len: word.len() as u32,
            });
            text.extend_from_slice(word.as_bytes());
        }
        let binding = Binding {
            producer: h(1),
            facts: h(2),
            graph: h(3),
            runtime: Hash::default(),
            inputs: h(4),
            root_universe: h(5),
            contracts: h(6),
            member_authority: h(7),
            fact_nodes: 4,
            fact_symbols: 4,
            fact_operations: 8,
            roots: 2,
        };
        let mut method = MethodRow::unknown(
            SubjectRef {
                kind: SubjectKind::FactNode,
                index: 0,
            },
            0,
            1,
            1,
            1,
        );
        method.top = TopMask::NONE;
        method.locals = 2;
        method.creations = range(1);
        method.value_flows = range(4);
        method.calls = range(1);
        method.code_observations = range(2);
        method.reads = range(2);
        method.writes = range(1);
        method.escapes = range(3);
        method.initializes = range(1);
        method.throws = range(1);
        method.synchronizes = range(2);
        method.external = range(1);
        method.flows = range(8);
        let mut target = MethodRow::unknown(
            SubjectRef {
                kind: SubjectKind::ForeignMethod,
                index: 0,
            },
            0,
            2,
            0,
            0,
        );
        target.top = TopMask::NONE;
        let mut initializer = MethodRow::unknown(
            SubjectRef {
                kind: SubjectKind::FactNode,
                index: 1,
            },
            0,
            0,
            0,
            0,
        );
        initializer.top = TopMask::NONE;
        let data = CapsuleData {
            methods: vec![method, initializer, target],
            calls: vec![CallRow {
                site: 0,
                target: CallTarget::Direct(MethodId(2)),
                receiver_value: ValueRef::RECEIVER,
                result: 1,
                kind: CallKind::Callback,
                receiver: Origin::RECEIVER,
                arguments: range(2),
                captures: Range::EMPTY,
            }],
            origins: vec![Origin::argument(0), Origin::capture(0)],
            callable_values: vec![ValueRef::argument(0), ValueRef::capture(0)],
            callable_bridges: vec![],
            sam_arities: vec![0],
            creations: vec![CallableCreation {
                site: 0,
                destination: 0,
                implementation: MethodId(1),
                sam: 0,
                receiver: Origin::ANY,
                receiver_value: ValueRef::CONSTANT,
                captures: Range::EMPTY,
            }],
            value_flows: vec![
                ValueFlow {
                    kind: ValueFlowKind::Copy,
                    value: ValueRef::argument(0),
                    index: 0,
                },
                ValueFlow {
                    kind: ValueFlowKind::Return,
                    value: ValueRef::local(0),
                    index: 0,
                },
                ValueFlow {
                    kind: ValueFlowKind::Store,
                    value: ValueRef::local(0),
                    index: 0,
                },
                ValueFlow {
                    kind: ValueFlowKind::Load,
                    value: ValueRef::local(1),
                    index: 0,
                },
            ],
            code_observations: vec![
                CodeRef {
                    kind: CodeKind::Method,
                    index: 1,
                },
                CodeRef {
                    kind: CodeKind::Class,
                    index: 0,
                },
            ],
            reads: vec![
                StorageRef {
                    kind: StorageKind::InstanceField,
                    member: 0,
                    base: Origin::argument(0),
                },
                StorageRef {
                    kind: StorageKind::ArrayElements,
                    member: NONE,
                    base: Origin::capture(0),
                },
            ],
            writes: vec![StorageRef {
                kind: StorageKind::InstanceField,
                member: 0,
                base: Origin::RECEIVER,
            }],
            escapes: vec![
                EscapeRef {
                    origin: Origin::fresh(0),
                    sink: EscapeSink::Return,
                    index: 0,
                },
                EscapeRef {
                    origin: Origin::argument(0),
                    sink: EscapeSink::Heap,
                    index: 0,
                },
                EscapeRef {
                    origin: Origin::capture(0),
                    sink: EscapeSink::Callback,
                    index: 0,
                },
            ],
            initializes: vec![MethodId(1)],
            throws: vec![0],
            synchronizes: vec![
                SyncRef {
                    kind: SyncKind::AcquireFence,
                    base: Origin::ANY,
                },
                SyncRef {
                    kind: SyncKind::Monitor,
                    base: Origin::RECEIVER,
                },
            ],
            external: vec![ExternalRef {
                kind: ExternalKind::Read,
                key: 0,
            }],
            flows: vec![
                FlowRef {
                    source: Origin::argument(0),
                    sink: FlowSink::Return,
                    via: NONE,
                    index: 0,
                },
                FlowRef {
                    source: Origin::RECEIVER,
                    sink: FlowSink::CallReceiver,
                    via: 0,
                    index: 0,
                },
                FlowRef {
                    source: Origin::argument(0),
                    sink: FlowSink::CallArgument,
                    via: 0,
                    index: 0,
                },
                FlowRef {
                    source: Origin::capture(0),
                    sink: FlowSink::CallArgument,
                    via: 0,
                    index: 1,
                },
                FlowRef {
                    source: Origin::argument(0),
                    sink: FlowSink::HeapWrite,
                    via: 0,
                    index: 0,
                },
                FlowRef {
                    source: Origin::RECEIVER,
                    sink: FlowSink::Throw,
                    via: NONE,
                    index: 0,
                },
                FlowRef {
                    source: Origin::argument(0),
                    sink: FlowSink::External,
                    via: 0,
                    index: 0,
                },
                FlowRef {
                    source: Origin::RECEIVER,
                    sink: FlowSink::Control,
                    via: NONE,
                    index: 0,
                },
            ],
        };
        Self {
            binding,
            text,
            strings,
            contexts: vec![ContextKey {
                name: id("ctx"),
                inputs: h(11),
            }],
            providers: vec![ProviderKey {
                context: 0,
                ordinal: 3,
                kind: ProviderKind::Archive,
                path: id("/capture.jar"),
                digest: h(12),
            }],
            foreign: vec![ForeignMethod {
                context: 0,
                provider: 0,
                class: h(13),
                owner: id("p/C"),
                name: id("callee"),
                descriptor: id("(Ljava/lang/Object;Ljava/lang/Object;)V"),
                node: NONE,
                method_flags: 8,
                resolved: true,
            }],
            members: vec![MemberKey {
                identity: MemberIdentity::FactSymbol,
                fact_symbol: 0,
                context: 0,
                provider: NONE,
                class: Hash::default(),
                owner: NONE,
                name: NONE,
                descriptor: NONE,
                kind: MemberKind::InstanceField,
                canonical: true,
            }],
            classes: vec![ClassKey {
                identity: ClassIdentity::FactSymbol,
                fact_symbol: 1,
                context: 0,
                provider: NONE,
                class: Hash::default(),
                owner: NONE,
                node: 1,
                resolved: true,
            }],
            authorities: vec![AuthorityKey {
                producer: h(21),
                contract: Hash::default(),
                kind: AuthorityKind::SourceRecipe,
                name: id("source"),
            }],
            exceptions: vec![ExceptionKey {
                class: 0,
                known: true,
            }],
            externals: vec![ExternalKey {
                context: 0,
                kind: 5,
                name: id("vm"),
                digest: h(22),
                canonical: true,
            }],
            sites: vec![SiteKey {
                method: 0,
                offset: 0,
                fact_operation: 0,
                kind: SiteKind::FactOperation,
            }],
            sams: vec![SamKey {
                authority: 0,
                context: 0,
                provider: 0,
                class: h(13),
                owner: id("p/C"),
                name: id("callee"),
                descriptor: id("()V"),
                resolved: true,
            }],
            adapters: vec![],
            bridge_proofs: vec![],
            phases: vec![],
            data,
        }
    }
    fn snapshot(&self) -> Snapshot<'_, CapsuleData> {
        Snapshot {
            binding: self.binding,
            keys: KeyTables {
                text: &self.text,
                strings: &self.strings,
                contexts: &self.contexts,
                providers: &self.providers,
                foreign_methods: &self.foreign,
                members: &self.members,
                classes: &self.classes,
                authorities: &self.authorities,
                exceptions: &self.exceptions,
                externals: &self.externals,
                sites: &self.sites,
                sams: &self.sams,
                adapters: &self.adapters,
                bridge_proofs: &self.bridge_proofs,
                phases: &self.phases,
            },
            effects: &self.data,
        }
    }
    fn publish(&self, path: &Path) -> Hash {
        write(path, &self.snapshot(), Limits::default()).unwrap()
    }
}

fn rewrite(
    original: &Path,
    destination: &Path,
    change: impl FnOnce(&mut Vec<(u32, u64, Vec<u8>)>),
) {
    let a = selector_artifacts::open(original, selector_artifacts::ArtifactKind::Effects).unwrap();
    let mut owned: Vec<_> = a
        .section_ids()
        .map(|id| (id, a.count(id).unwrap(), a.section(id).unwrap().to_vec()))
        .collect();
    change(&mut owned);
    let sections: Vec<_> = owned
        .iter()
        .map(|(id, count, bytes)| selector_artifacts::Section {
            id: *id,
            count: *count,
            bytes,
        })
        .collect();
    selector_artifacts::write(
        destination,
        selector_artifacts::ArtifactKind::Effects,
        &sections,
    )
    .unwrap();
}
fn put(rows: &mut [(u32, u64, Vec<u8>)], section: u32, offset: usize, value: u32) {
    rows.iter_mut().find(|r| r.0 == section).unwrap().2[offset..offset + 4]
        .copy_from_slice(&value.to_le_bytes());
}

#[test]
fn all_channels_roundtrip_and_borrowed_lookup_has_zero_allocations() {
    let f = Fixture::new();
    let d = Directory::new();
    let path = d.file("one.bin");
    let identity = f.publish(&path);
    let a = open(&path, f.binding, Limits::default()).unwrap();
    assert_eq!(identity, a.identity());
    assert_eq!(a.method(0), Some(f.data.methods[0]));
    assert_eq!(a.method(1), Some(f.data.methods[1]));
    assert_eq!(a.call(0), Some(f.data.calls[0]));
    assert_eq!(a.flow(7), Some(f.data.flows[7]));
    assert_eq!(a.foreign_method(0), Some(f.foreign[0]));
    assert_eq!(a.member(0), Some(f.members[0]));
    assert!(a.text((f.strings.len() - 1) as u32).unwrap().contains('é'));
    COUNT.with(|c| c.set(Some(0)));
    for _ in 0..1000 {
        std::hint::black_box((
            a.method(0),
            a.call(0),
            a.origin(1),
            a.read(1),
            a.write(0),
            a.escape(0),
            a.initialize(0),
            a.r#throw(0),
            a.synchronize(0),
            a.external(0),
            a.flow(7),
            a.context(0),
            a.provider(0),
            a.foreign_method(0),
            a.member(0),
            a.class(0),
            a.authority(0),
            a.exception_key(0),
            a.external_key(0),
            a.site(0),
            a.text(0),
        ));
    }
    let n = COUNT.with(|c| c.replace(None)).unwrap();
    assert_eq!(n, 0);
}

#[test]
fn bindings_reject_each_transplant_and_runtime_zero_is_exact_absence() {
    let f = Fixture::new();
    let d = Directory::new();
    let path = d.file("one.bin");
    f.publish(&path);
    assert_eq!(
        open(&path, f.binding, Limits::default())
            .unwrap()
            .binding()
            .runtime,
        Hash::default()
    );
    for index in 0..8 {
        let mut expected = f.binding;
        match index {
            0 => expected.producer = h(90),
            1 => expected.facts = h(90),
            2 => expected.graph = h(90),
            3 => expected.runtime = h(90),
            4 => expected.inputs = h(90),
            5 => expected.root_universe = h(90),
            6 => expected.contracts = h(90),
            _ => expected.member_authority = h(90),
        }
        assert!(open(&path, expected, Limits::default()).is_err());
    }
}

#[test]
fn absence_is_all_top_and_unknown_schema_or_legacy_present_is_rejected() {
    let f = Fixture::new();
    assert_eq!(
        open_optional(None, f.binding, Limits::default())
            .unwrap()
            .absent_top(),
        Some(TopMask::ALL)
    );
    let d = Directory::new();
    let path = d.file("one.bin");
    f.publish(&path);
    let bad = d.file("schema.bin");
    rewrite(&path, &bad, |rows| put(rows, 1, 8, 99));
    assert!(open(&bad, f.binding, Limits::default()).is_err());
    let legacy = d.file("legacy.bin");
    selector_artifacts::write(
        &legacy,
        selector_artifacts::ArtifactKind::Effects,
        &[selector_artifacts::Section {
            id: 1,
            count: 1,
            bytes: &14u32.to_le_bytes(),
        }],
    )
    .unwrap();
    assert!(open_optional(Some(&legacy), f.binding, Limits::default()).is_err());
}

#[test]
fn corrupt_truncated_and_oversized_inputs_rejected() {
    let f = Fixture::new();
    let d = Directory::new();
    let path = d.file("one.bin");
    f.publish(&path);
    let bytes = fs::read(&path).unwrap();
    let p = d.file("truncated.bin");
    fs::write(&p, &bytes[..bytes.len() - 1]).unwrap();
    assert!(open(&p, f.binding, Limits::default()).is_err());
    let p = d.file("checksum.bin");
    let mut corrupt = bytes.clone();
    corrupt[200] ^= 1;
    fs::write(&p, corrupt).unwrap();
    assert!(open(&p, f.binding, Limits::default()).is_err());
    let mut limits = Limits::default();
    limits.max_bytes = bytes.len() as u64 - 1;
    assert!(open(&path, f.binding, limits).is_err());
    let mut limits = Limits::default();
    limits.max_records = 1;
    assert!(open(&path, f.binding, limits).is_err());
    let mut limits = Limits::default();
    limits.max_text_bytes = 1;
    assert!(open(&path, f.binding, limits).is_err());
    let p = d.file("huge-count.bin");
    rewrite(&path, &p, |rows| {
        rows.iter_mut().find(|r| r.0 == 13).unwrap().1 = u64::MAX
    });
    assert!(open(&p, f.binding, Limits::default()).is_err());
}

#[test]
fn resealed_bad_bool_enum_range_utf8_and_provider_context_rejected() {
    let f = Fixture::new();
    let d = Directory::new();
    let path = d.file("one.bin");
    f.publish(&path);
    for (name, section, offset, value) in [
        ("bool", 6, 60, 2),
        ("enum", 14, 20, 99),
        ("range", 13, 44, u32::MAX),
        ("provider", 5, 0, 1),
        ("topbits", 13, 24, 1 << 31),
        ("source-hash", 7, 16, 1),
        ("site-owner", 12, 0, 1),
        ("origin", 15, 4, 99),
        ("init-arity", 13, 140, 1),
    ] {
        let p = d.file(name);
        rewrite(&path, &p, |rows| put(rows, section, offset, value));
        assert!(open(&p, f.binding, Limits::default()).is_err(), "{name}");
    }
    let p = d.file("utf8.bin");
    rewrite(&path, &p, |rows| {
        rows.iter_mut().find(|r| r.0 == 2).unwrap().2[0] = 0xff
    });
    assert!(open(&p, f.binding, Limits::default()).is_err());
}

#[test]
fn duplicate_conflicting_subject_and_orphan_rows_rejected_after_reseal() {
    let f = Fixture::new();
    let d = Directory::new();
    let path = d.file("one.bin");
    f.publish(&path);
    let p = d.file("duplicate.bin");
    rewrite(&path, &p, |rows| {
        put(rows, 13, 128, 0);
        put(rows, 13, 132, 0);
        put(rows, 13, 152, TopMask::ALL.bits());
    });
    assert!(open(&p, f.binding, Limits::default()).is_err());
    let p = d.file("orphan.bin");
    rewrite(&path, &p, |rows| {
        let r = rows.iter_mut().find(|r| r.0 == 17).unwrap();
        r.1 += 1;
        let extra = r.2[..16].to_vec();
        r.2.extend_from_slice(&extra);
    });
    assert!(open(&p, f.binding, Limits::default()).is_err());
}

#[test]
fn unresolved_foreign_and_noncanonical_alias_must_keep_independent_top_channels() {
    let f = Fixture::new();
    let d = Directory::new();
    let path = d.file("one.bin");
    f.publish(&path);
    let p = d.file("missing.bin");
    rewrite(&path, &p, |rows| put(rows, 6, 60, 0));
    assert!(open(&p, f.binding, Limits::default()).is_err());
    let p = d.file("missing-open.bin");
    rewrite(&path, &p, |rows| {
        put(rows, 6, 60, 0);
        put(rows, 13, 280, TopMask::ALL.bits());
    });
    assert!(open(&p, f.binding, Limits::default()).is_ok());
    let mut bad = f.clone();
    bad.members[0].canonical = false;
    let p = d.file("alias.bin");
    assert!(write(&p, &bad.snapshot(), Limits::default()).is_err());
    assert!(!p.exists());
    for c in [
        Channel::Reads,
        Channel::Writes,
        Channel::Escapes,
        Channel::Flows,
    ] {
        bad.data.methods[0].top.insert(c);
    }
    bad.publish(&p);
    assert!(open(&p, bad.binding, Limits::default()).is_ok());
    let mut external = f.clone();
    external.externals[0].canonical = false;
    let p = d.file("external.bin");
    assert!(write(&p, &external.snapshot(), Limits::default()).is_err());
    external.data.methods[0].top.insert(Channel::External);
    external.data.methods[0].top.insert(Channel::Flows);
    external.publish(&p);
    assert!(open(&p, external.binding, Limits::default()).is_ok());
}

#[test]
fn source_members_never_fabricate_jvm_identity_and_static_call_flags_checked() {
    let mut f = Fixture::new();
    let d = Directory::new();
    let p = d.file("source.bin");
    f.members[0].class = h(9);
    assert!(write(&p, &f.snapshot(), Limits::default()).is_err());
    let mut f = Fixture::new();
    f.data.calls[0].kind = CallKind::Static;
    f.data.calls[0].receiver = Origin::ANY;
    let p = d.file("static.bin");
    f.publish(&p);
    let bad = d.file("wrongflags.bin");
    rewrite(&p, &bad, |rows| put(rows, 6, 56, 0));
    assert!(open(&bad, f.binding, Limits::default()).is_err());
}

#[test]
fn immutable_publication_rejects_different_content_and_keeps_original() {
    let f = Fixture::new();
    let d = Directory::new();
    let path = d.file("one.bin");
    let first = f.publish(&path);
    assert_eq!(f.publish(&path), first);
    let before = fs::read(&path).unwrap();
    let mut changed = f.clone();
    changed.data.methods[0].top.insert(Channel::Reads);
    assert!(write(&path, &changed.snapshot(), Limits::default()).is_err());
    assert_eq!(fs::read(&path).unwrap(), before);
}

#[test]
fn foreign_node_hint_cannot_replace_open_source_subject() {
    let mut f = Fixture::new();
    f.foreign[0].node = 0;
    f.data.methods[0].top = TopMask::ALL;
    let d = Directory::new();
    let path = d.file("hint.bin");
    f.publish(&path);
    let a = open(&path, f.binding, Limits::default()).unwrap();
    assert_eq!(a.method_count(), 3);
    assert_eq!(a.foreign_method(0).unwrap().node, 0);
    assert_eq!(a.method(0).unwrap().top, TopMask::ALL);
    assert_eq!(a.method(2).unwrap().top, TopMask::NONE);
    assert_ne!(a.method(0).unwrap().subject, a.method(2).unwrap().subject);
}

#[test]
fn identical_physical_provider_bytes_do_not_merge_compiler_contexts() {
    let mut f = Fixture::new();
    let second_name = f.authorities[0].name;
    f.contexts.push(ContextKey {
        name: second_name,
        inputs: h(42),
    });
    f.providers.push(ProviderKey {
        context: 1,
        ..f.providers[0]
    });
    f.foreign.push(ForeignMethod {
        context: 1,
        provider: 1,
        ..f.foreign[0]
    });
    f.data.methods.push(MethodRow::unknown(
        SubjectRef {
            kind: SubjectKind::ForeignMethod,
            index: 1,
        },
        0,
        1,
        1,
        0,
    ));
    let d = Directory::new();
    let path = d.file("contexts.bin");
    f.publish(&path);
    let a = open(&path, f.binding, Limits::default()).unwrap();
    assert_eq!(a.provider_count(), 2);
    assert_eq!(a.foreign_method_count(), 2);
    assert_eq!(a.provider(0).unwrap().digest, a.provider(1).unwrap().digest);
    assert_ne!(
        a.provider(0).unwrap().context,
        a.provider(1).unwrap().context
    );
    assert_eq!(
        a.foreign_method(0).unwrap().class,
        a.foreign_method(1).unwrap().class
    );
    assert_ne!(
        a.foreign_method(0).unwrap().context,
        a.foreign_method(1).unwrap().context
    );
}

#[test]
fn explicit_materialization_preflights_total_bytes_uses_sixteen_flat_allocations_and_tears_down() {
    let f = Fixture::new();
    let d = Directory::new();
    let path = d.file("materialized.bin");
    let identity = f.publish(&path);
    let baseline = LIVE.with(Cell::get);
    let wire = open(&path, f.binding, Limits::default()).unwrap();
    let minimum = wire.minimum_materialized_bytes().unwrap();
    COUNT.with(|c| c.set(Some(0)));
    let denied = wire.materialize(selector_effects::Limits::default(), minimum - 1);
    let allocations = COUNT.with(|c| c.replace(None)).unwrap();
    assert!(denied.is_err());
    assert_eq!(allocations, 0);
    assert_eq!(LIVE.with(Cell::get), baseline);

    let wire = open(&path, f.binding, Limits::default()).unwrap();
    COUNT.with(|c| c.set(Some(0)));
    let materialized = wire
        .materialize(selector_effects::Limits::default(), 1 << 20)
        .unwrap();
    let allocations = COUNT.with(|c| c.replace(None)).unwrap();
    assert_eq!(
        allocations, 16,
        "one reservation per nonempty flat DTO column"
    );
    assert_eq!(materialized.wire().identity(), identity);
    assert_eq!(materialized.wire().binding(), f.binding);
    assert_eq!(materialized.capsules().data().methods, f.data.methods);
    assert_eq!(materialized.capsules().data().flows, f.data.flows);
    assert_eq!(materialized.wire().foreign_method(0), Some(f.foreign[0]));
    assert_eq!(
        materialized.owned_bytes(),
        materialized.transport_bytes() + materialized.capsules().owned_bytes()
    );
    assert!(LIVE.with(Cell::get) - baseline <= materialized.owned_bytes() as isize);
    drop(materialized);
    assert_eq!(
        LIVE.with(Cell::get),
        baseline,
        "wire owner, keys and all decoded capacities released"
    );
}

#[test]
fn callable_creation_and_parametric_invocation_roundtrip_without_heap_origin_aliasing() {
    let mut f = Fixture::new();
    f.data.methods[0].calls.len = 2;
    f.data.calls.push(CallRow {
        site: 0,
        target: CallTarget::Callable {
            value: ValueRef::local(0),
            sam: 0,
        },
        kind: CallKind::Callback,
        receiver: Origin::ANY,
        receiver_value: ValueRef::local(0),
        result: NONE,
        arguments: Range::EMPTY,
        captures: Range::EMPTY,
    });
    let d = Directory::new();
    let path = d.file("callable.bin");
    f.publish(&path);
    let wire = open(&path, f.binding, Limits::default()).unwrap();
    assert_eq!(wire.call(1), Some(f.data.calls[1]));
    assert_eq!(wire.creation(0), Some(f.data.creations[0]));
    assert_eq!(wire.value_flow(3), Some(f.data.value_flows[3]));
    assert_eq!(wire.callable_value(1), Some(ValueRef::capture(0)));
    assert_eq!(wire.sam_key(0), Some(f.sams[0]));
    COUNT.with(|c| c.set(Some(0)));
    for _ in 0..1000 {
        std::hint::black_box((
            wire.call(1),
            wire.creation(0),
            wire.value_flow(3),
            wire.callable_value(1),
            wire.sam_key(0),
        ));
    }
    assert_eq!(COUNT.with(|c| c.replace(None)), Some(0));
    let owned = wire
        .materialize(selector_effects::Limits::default(), 1 << 20)
        .unwrap();
    assert_eq!(owned.capsules().data().creations, f.data.creations);
    assert_eq!(
        owned.capsules().data().callable_values,
        f.data.callable_values
    );
    assert_eq!(owned.capsules().data().value_flows, f.data.value_flows);
}

#[test]
fn resealed_callable_tags_capture_scope_and_value_flow_indices_rejected() {
    let f = Fixture::new();
    let d = Directory::new();
    let path = d.file("good.bin");
    f.publish(&path);
    for (name, section, offset, value) in [
        ("targettag", 14, 4, 99),
        ("direct-reserved", 14, 12, 1),
        ("receiver-value-kind", 14, 48, 99),
        ("result-local", 14, 56, 2),
        ("capture-local-scope", 25, 12, 99),
        ("creation-destination", 27, 4, 2),
        ("creation-foreign-site", 27, 0, NONE),
        ("creation-impl-arity", 27, 8, 2),
        ("creation-capture-range", 27, 36, 1),
        ("flow-kind", 28, 0, 99),
        ("flow-store-ordinal", 28, 2 * 16 + 12, 1),
        (
            "flow-load-notlocal",
            28,
            3 * 16 + 4,
            ValueKind::Argument as u32,
        ),
        ("sam-arity", 26, 0, 1),
        ("sam-authority", 29, 0, NONE),
        ("sam-bool", 29, 56, 2),
    ] {
        let bad = d.file(name);
        rewrite(&path, &bad, |rows| put(rows, section, offset, value));
        assert!(open(&bad, f.binding, Limits::default()).is_err(), "{name}");
    }
    let bad = d.file("unpaired-values");
    rewrite(&path, &bad, |rows| {
        let r = rows.iter_mut().find(|r| r.0 == 25).unwrap();
        r.1 -= 1;
        r.2.truncate(r.2.len() - 8);
    });
    assert!(open(&bad, f.binding, Limits::default()).is_err());
    let bad = d.file("orphan-creations");
    rewrite(&path, &bad, |rows| {
        let r = rows.iter_mut().find(|r| r.0 == 27).unwrap();
        r.1 += 1;
        let extra = r.2.clone();
        r.2.extend(extra);
    });
    assert!(open(&bad, f.binding, Limits::default()).is_err());
}

#[test]
fn unadmitted_sam_never_becomes_finite_on_invocation_and_creation_does_not_execute() {
    let mut f = Fixture::new();
    f.data.creations[0].sam = NONE;
    let d = Directory::new();
    f.publish(&d.file("creation-only"));
    f.data.methods[0].calls.len = 2;
    f.data.calls.push(CallRow {
        site: 0,
        target: CallTarget::Callable {
            value: ValueRef::local(0),
            sam: NONE,
        },
        kind: CallKind::Callback,
        receiver: Origin::ANY,
        receiver_value: ValueRef::UNKNOWN,
        result: NONE,
        arguments: Range::EMPTY,
        captures: Range::EMPTY,
    });
    assert!(write(&d.file("unadmitted"), &f.snapshot(), Limits::default()).is_err());
    f.data.methods[0].top.insert(Channel::Calls);
    f.publish(&d.file("open"));
    let mut f = Fixture::new();
    f.sams[0].resolved = false;
    f.publish(&d.file("unresolved-dormant"));
    f.data.methods[0].calls.len = 2;
    f.data.calls.push(CallRow {
        site: 0,
        target: CallTarget::Callable {
            value: ValueRef::local(0),
            sam: 0,
        },
        kind: CallKind::Callback,
        receiver: Origin::ANY,
        receiver_value: ValueRef::UNKNOWN,
        result: NONE,
        arguments: Range::EMPTY,
        captures: Range::EMPTY,
    });
    assert!(
        write(
            &d.file("unresolved-activation"),
            &f.snapshot(),
            Limits::default()
        )
        .is_err()
    );
    f.data.methods[0].top.insert(Channel::Calls);
    f.publish(&d.file("unresolved-open"));
}

fn adapter_fixture() -> Fixture {
    let mut f = Fixture::new();
    let id = |word: &str| {
        f.strings
            .iter()
            .position(|r| {
                std::str::from_utf8(&f.text[r.start as usize..(r.start + r.len) as usize]).unwrap()
                    == word
            })
            .unwrap() as u32
    };
    let original = f.foreign[0];
    let mut bootstrap = original;
    bootstrap.name = id("bootstrap");
    bootstrap.descriptor = id(
        "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;",
    );
    let mut factory = original;
    factory.name = id("factory");
    factory.descriptor = id("(Ljava/lang/Object;Ljava/lang/Object;)Lp/C;");
    f.foreign = vec![bootstrap, original, factory];
    f.data.methods[2].subject.index = 1;
    let mut enclosing = MethodRow::unknown(
        SubjectRef {
            kind: SubjectKind::ForeignMethod,
            index: 2,
        },
        0,
        2,
        0,
        0,
    );
    enclosing.top = TopMask::NONE;
    f.data.methods.push(enclosing);
    let mut adapter = MethodRow::unknown(
        SubjectRef {
            kind: SubjectKind::CallableAdapter,
            index: 0,
        },
        0,
        0,
        2,
        0,
    );
    adapter.top = TopMask::NONE;
    f.data.methods.push(adapter);
    f.sites.push(SiteKey {
        method: 3,
        offset: 7,
        fact_operation: NONE,
        kind: SiteKind::NativeBytecode,
    });
    f.adapters.push(CallableAdapterKey {
        authority: 0,
        enclosing_method: 3,
        enclosing_foreign_method: 2,
        site: 1,
        bootstrap_foreign_method: 0,
        bootstrap_handle_kind: 6,
        bootstrap_arguments: h(31),
        implementation_foreign_method: 1,
        implementation_handle_kind: 6,
        sam: 0,
        invoked_name: id("callee"),
        invoked_descriptor: id("(Ljava/lang/Object;Ljava/lang/Object;)Lp/C;"),
        instantiated_descriptor: id("()V"),
        adaptation: h(32),
        normalized_arity: 0,
        normalized_captures: 2,
        resolved: true,
    });
    f.data.creations[0].implementation = MethodId(4);
    f.data.creations[0].captures = Range { start: 2, len: 2 };
    f.data
        .origins
        .extend([Origin::argument(0), Origin::capture(0)]);
    f.data
        .callable_values
        .extend([ValueRef::argument(0), ValueRef::capture(0)]);
    f
}

#[test]
fn exact_adapter_keys_roundtrip_and_resealed_transplants_or_missing_proof_reject() {
    let f = adapter_fixture();
    let d = Directory::new();
    let path = d.file("adapter.bin");
    f.publish(&path);
    let wire = open(&path, f.binding, Limits::default()).unwrap();
    assert_eq!(wire.adapter(0), Some(f.adapters[0]));
    assert_eq!(wire.creation(0), Some(f.data.creations[0]));
    for (name, offset, value) in [
        ("authority", 0, NONE),
        ("enclosing-site", 4, 0),
        ("bsm-kind", 20, 1),
        ("sam", 64, NONE),
        ("normalized-shape", 112, 1),
        ("resolved", 120, 2),
    ] {
        let bad = d.file(name);
        rewrite(&path, &bad, |rows| put(rows, 30, offset, value));
        assert!(open(&bad, f.binding, Limits::default()).is_err(), "{name}");
    }
    let bad = d.file("zero-adaptation");
    rewrite(&path, &bad, |rows| {
        rows.iter_mut().find(|r| r.0 == 30).unwrap().2[80..112].fill(0)
    });
    assert!(open(&bad, f.binding, Limits::default()).is_err());
    let mut missing = f.clone();
    missing.adapters[0].resolved = false;
    assert!(
        write(
            &d.file("missing-adapter"),
            &missing.snapshot(),
            Limits::default()
        )
        .is_err()
    );
    missing.data.methods[4].top = TopMask::ALL;
    missing.publish(&d.file("missing-adapter-open"));
}

#[test]
fn effects_kind_and_callable_schema_are_strict_and_never_upgrade_historical_v1_v2() {
    let f = Fixture::new();
    let d = Directory::new();
    let path = d.file("v2.bin");
    f.publish(&path);
    let artifact =
        selector_artifacts::open(&path, selector_artifacts::ArtifactKind::Effects).unwrap();
    assert!(selector_artifacts::open(&path, selector_artifacts::ArtifactKind::Summaries).is_err());
    let sections: Vec<_> = artifact
        .section_ids()
        .map(|id| selector_artifacts::Section {
            id,
            count: artifact.count(id).unwrap(),
            bytes: artifact.section(id).unwrap(),
        })
        .collect();
    let legacy = d.file("same-payload-wrong-kind");
    selector_artifacts::write(
        &legacy,
        selector_artifacts::ArtifactKind::Summaries,
        &sections,
    )
    .unwrap();
    assert!(open(&legacy, f.binding, Limits::default()).is_err());
    let v2 = d.file("v2-payload");
    rewrite(&path, &v2, |rows| {
        rows[0].2[..8].copy_from_slice(b"SEFXP002");
        put(rows, 1, 8, 2);
    });
    assert!(open(&v2, f.binding, Limits::default()).is_err());
    let v1 = d.file("v1-payload");
    rewrite(&path, &v1, |rows| {
        rows[0].2[..8].copy_from_slice(b"SEFXP001");
        put(rows, 1, 8, 1);
    });
    assert!(open(&v1, f.binding, Limits::default()).is_err());
}

fn interleaved_fixture() -> Fixture {
    let mut f = adapter_fixture();
    f.data.origins[2] = Origin::RECEIVER;
    f.data.origins[3] = Origin::fresh(0);
    f.data.callable_values[2] = ValueRef::RECEIVER;
    f.data.callable_values[3] = ValueRef::CONSTANT;
    f.data.origins.rotate_right(2);
    f.data.callable_values.rotate_right(2);
    f.data.calls[0].arguments = Range { start: 2, len: 2 };
    f.data.creations[0].captures = Range { start: 0, len: 2 };
    f
}

#[test]
fn same_method_creation_before_call_repack_preserves_code_capture_and_sidecar_coordinates() {
    let mut f = interleaved_fixture();
    let d = Directory::new();
    assert!(write(&d.file("not-canonical"), &f.snapshot(), Limits::default()).is_err());
    let old = f.data.creations[0].captures;
    COUNT.with(|c| c.set(Some(0)));
    let remap = canonicalize_origins(&mut f.data, 1 << 20).unwrap();
    assert_eq!(
        COUNT.with(|c| c.replace(None)),
        Some(3),
        "only two scalar columns and one row map"
    );
    assert_eq!(remap.range(old).unwrap(), Range { start: 2, len: 2 });
    assert_eq!(f.data.creations[0].captures, remap.range(old).unwrap());
    assert_eq!(f.data.calls[0].arguments, Range { start: 0, len: 2 });
    assert_eq!(
        f.data.origins,
        vec![
            Origin::argument(0),
            Origin::capture(0),
            Origin::RECEIVER,
            Origin::fresh(0)
        ]
    );
    assert_eq!(
        f.data.callable_values,
        vec![
            ValueRef::argument(0),
            ValueRef::capture(0),
            ValueRef::RECEIVER,
            ValueRef::CONSTANT
        ]
    );
    assert_eq!(f.data.creations[0].implementation, MethodId(4));
    let p = d.file("repacked");
    f.publish(&p);
    let wire = open(&p, f.binding, Limits::default()).unwrap();
    assert_eq!(wire.creation(0), Some(f.data.creations[0]));
    assert_eq!(wire.callable_value(2), Some(ValueRef::RECEIVER));
    drop(remap);
    COUNT.with(|c| c.set(Some(0)));
    let remap = canonicalize_origins(&mut f.data, 1 << 20).unwrap();
    assert_eq!(COUNT.with(|c| c.replace(None)), Some(0));
    assert!(remap.is_identity());
    assert_eq!(remap.owned_bytes(), 0);
}

#[test]
fn repack_budget_overlap_orphans_and_bad_scope_fail_atomically_without_header_changes() {
    let original = interleaved_fixture();
    let mut f = original.clone();
    let budget = f.data.owned_bytes().unwrap();
    COUNT.with(|c| c.set(Some(0)));
    let denied = canonicalize_origins(&mut f.data, budget);
    assert_eq!(COUNT.with(|c| c.replace(None)), Some(0));
    assert!(denied.is_err());
    for fault in 0..5 {
        let mut data = original.data.clone();
        match fault {
            0 => data.creations[0].captures.start = 2, // aliases call actuals, leaves first capture rows orphaned
            1 => {
                data.origins.push(Origin::ANY);
                data.callable_values.push(ValueRef::UNKNOWN);
            }
            2 => data.callable_values.pop().map(|_| ()).unwrap(),
            3 => data.calls[0].arguments.start = NONE,
            _ => data.methods[0].creations = Range::EMPTY,
        }
        let before = data.clone();
        assert!(
            canonicalize_origins(&mut data, 1 << 20).is_err(),
            "fault {fault}"
        );
        assert_eq!(data.methods, before.methods);
        assert_eq!(data.calls, before.calls);
        assert_eq!(data.creations, before.creations);
        assert_eq!(data.origins, before.origins);
        assert_eq!(data.callable_values, before.callable_values);
    }
    assert_eq!(f.data.methods, original.data.methods);
    assert_eq!(f.data.calls, original.data.calls);
    assert_eq!(f.data.creations, original.data.creations);
    assert_eq!(f.data.origins, original.data.origins);
    assert_eq!(f.data.callable_values, original.data.callable_values);
}

#[test]
fn adapter_enclosing_identity_factory_capture_arity_and_handle_constructor_cannot_conflict() {
    let f = adapter_fixture();
    let d = Directory::new();
    let good = d.file("good");
    f.publish(&good);
    let wrong = d.file("enclosing-same-context");
    rewrite(&good, &wrong, |rows| {
        put(rows, 30, 4, 0);
        put(rows, 12, 16, 0);
    });
    assert!(open(&wrong, f.binding, Limits::default()).is_err());
    let wrong = d.file("factory-capture-arity");
    rewrite(&good, &wrong, |rows| {
        put(rows, 30, 116, 1);
        put(rows, 13, 4 * 128 + 16, 1);
        put(rows, 27, 36, 1);
        for section in [15, 25] {
            let r = rows.iter_mut().find(|r| r.0 == section).unwrap();
            r.1 -= 1;
            r.2.truncate(r.2.len() - 8);
        }
    });
    assert!(open(&wrong, f.binding, Limits::default()).is_err());
    let wrong = d.file("constructor-handle-to-ordinary");
    rewrite(&good, &wrong, |rows| {
        put(rows, 30, 60, 8);
        put(rows, 6, 64 + 56, 0);
    });
    assert!(open(&wrong, f.binding, Limits::default()).is_err());
    let wrong = d.file("bootstrap-constructor-handle-to-ordinary");
    rewrite(&good, &wrong, |rows| {
        put(rows, 30, 20, 8);
        put(rows, 6, 56, 0);
    });
    assert!(open(&wrong, f.binding, Limits::default()).is_err());
}

fn bridge_fixture() -> Fixture {
    let mut f = adapter_fixture();
    let name = f
        .strings
        .iter()
        .position(|r| &f.text[r.start as usize..(r.start + r.len) as usize] == b"specialized")
        .unwrap() as u32;
    let mut default = f.foreign[1];
    default.name = name;
    default.descriptor = f.sams[0].descriptor;
    default.method_flags = 1;
    f.foreign.push(default);
    let mut method = MethodRow::unknown(
        SubjectRef {
            kind: SubjectKind::ForeignMethod,
            index: 3,
        },
        0,
        0,
        0,
        0,
    );
    method.top = TopMask::NONE;
    f.data.methods.insert(4, method);
    f.data.creations[0].implementation = MethodId(5);
    let mut requested = f.sams[0];
    requested.name = name;
    f.sams.push(requested);
    f.data.sam_arities.push(0);
    f.bridge_proofs.push(CallableBridgeProofKey {
        authority: 0,
        creation: 0,
        creator_adapter: 0,
        from_sam: 0,
        to_sam: 1,
        default_foreign_method: 3,
        generated_method_set: h(40),
        default_code: h(41),
        transport_policy: h(42),
        proof: h(43),
        no_override: true,
        resolved: true,
    });
    f.data.callable_bridges.push(CallableBridge {
        creation: 0,
        sam: 1,
        implementation: MethodId(4),
        proof: 0,
    });
    f
}

#[test]
fn creation_specific_default_bridge_preserves_actual_default_body_and_all_sealed_key_columns() {
    let f = bridge_fixture();
    let d = Directory::new();
    let path = d.file("bridge");
    let identity = f.publish(&path);
    let wire = open(&path, f.binding, Limits::default()).unwrap();
    assert_eq!(wire.callable_bridge(0), Some(f.data.callable_bridges[0]));
    assert_eq!(wire.bridge_proof(0), Some(f.bridge_proofs[0]));
    assert_eq!(
        wire.method(4).unwrap().subject,
        SubjectRef {
            kind: SubjectKind::ForeignMethod,
            index: 3
        }
    );
    COUNT.with(|c| c.set(Some(0)));
    for _ in 0..1000 {
        std::hint::black_box((wire.callable_bridge(0), wire.bridge_proof(0)));
    }
    assert_eq!(COUNT.with(|c| c.replace(None)), Some(0));
    COUNT.with(|c| c.set(Some(0)));
    let materialized = wire
        .materialize(selector_effects::Limits::default(), 1 << 20)
        .unwrap();
    assert_eq!(COUNT.with(|c| c.replace(None)), Some(17));
    assert_eq!(materialized.wire().identity(), identity);
    assert_eq!(
        materialized.capsules().data().callable_bridges,
        f.data.callable_bridges
    );
}

#[test]
fn bridge_proof_transplants_missing_override_and_noninstance_default_cannot_authorize_routes() {
    let f = bridge_fixture();
    let d = Directory::new();
    let path = d.file("good");
    f.publish(&path);
    for (name, section, offset, value) in [
        ("bridge-creation", 31, 0, 1),
        ("bridge-sam", 31, 4, 0),
        ("bridge-target", 31, 8, 2),
        ("bridge-proof", 31, 12, NONE),
        ("key-authority", 32, 0, NONE),
        ("key-adapter", 32, 8, NONE),
        ("key-from", 32, 12, 1),
        ("key-to", 32, 16, 0),
        ("key-default", 32, 20, 1),
        ("no-override", 32, 152, 0),
        ("proof-bool", 32, 156, 2),
        ("static-default", 6, 3 * 64 + 56, 9),
    ] {
        let bad = d.file(name);
        rewrite(&path, &bad, |rows| put(rows, section, offset, value));
        assert!(open(&bad, f.binding, Limits::default()).is_err(), "{name}");
    }
    for (name, start) in [
        ("generated-set", 24),
        ("default-code", 56),
        ("policy", 88),
        ("combined-proof", 120),
    ] {
        let bad = d.file(name);
        rewrite(&path, &bad, |rows| {
            rows.iter_mut().find(|r| r.0 == 32).unwrap().2[start..start + 32].fill(0)
        });
        assert!(open(&bad, f.binding, Limits::default()).is_err(), "{name}");
    }
    let mut unknown = f.clone();
    unknown.bridge_proofs[0].resolved = false;
    unknown.bridge_proofs[0].no_override = false;
    assert!(
        write(
            &d.file("unresolved-finite"),
            &unknown.snapshot(),
            Limits::default()
        )
        .is_err()
    );
    unknown.data.methods[4].top = TopMask::ALL;
    unknown.publish(&d.file("unresolved-open-target"));
    assert_eq!(
        unknown.data.methods[0].top,
        TopMask::NONE,
        "dormant creation itself does not execute unknown default body"
    );
}

#[test]
fn runtime_phase_is_explicit_scoped_all_top_and_never_a_fabricated_jvm_method() {
    let mut f = Fixture::new();
    f.phases.push(PhaseKey {
        class: 0,
        authority: 0,
        kind: PhaseKind::LoadingVerification,
    });
    let mut phase = MethodRow::unknown(
        SubjectRef {
            kind: SubjectKind::RuntimePhase,
            index: 0,
        },
        0,
        0,
        0,
        0,
    );
    phase.calls = Range { start: 1, len: 1 };
    phase.code_observations = Range { start: 2, len: 1 };
    phase.initializes = Range { start: 1, len: 1 };
    f.data.methods.push(phase);
    f.sites.push(SiteKey {
        method: 3,
        offset: 0,
        fact_operation: NONE,
        kind: SiteKind::NativeBytecode,
    });
    f.data.calls.push(CallRow {
        site: 1,
        target: CallTarget::Direct(MethodId(1)),
        kind: CallKind::Static,
        receiver: Origin::ANY,
        receiver_value: ValueRef::CONSTANT,
        result: NONE,
        arguments: Range::EMPTY,
        captures: Range::EMPTY,
    });
    f.data.code_observations.push(CodeRef {
        kind: CodeKind::Method,
        index: 1,
    });
    f.data.initializes.push(MethodId(1));
    let d = Directory::new();
    let path = d.file("phase");
    f.publish(&path);
    let wire = open(&path, f.binding, Limits::default()).unwrap();
    assert_eq!(wire.phase_key(0), Some(f.phases[0]));
    assert_eq!(wire.method(3).unwrap().top, TopMask::ALL);
    for (name, section, offset, value) in [
        ("class", 33, 0, NONE),
        ("authority", 33, 4, NONE),
        ("kind", 33, 8, 99),
        ("finite-phase", 13, 3 * 128 + 24, 0),
        ("phase-args", 13, 3 * 128 + 12, 1),
        ("phase-locals", 13, 3 * 128 + 108, 1),
    ] {
        let bad = d.file(name);
        rewrite(&path, &bad, |rows| put(rows, section, offset, value));
        assert!(open(&bad, f.binding, Limits::default()).is_err(), "{name}");
    }
}

#[test]
fn runtime_phase_valid_authority_id_transplant_still_rejects_producer_mismatch() {
    let mut f = Fixture::new();
    let other = AuthorityKey {
        producer: h(22),
        ..f.authorities[0]
    };
    f.authorities.push(other);
    f.phases.push(PhaseKey {
        class: 0,
        authority: 0,
        kind: PhaseKind::ClassInitialization,
    });
    f.data.methods.push(MethodRow::unknown(
        SubjectRef {
            kind: SubjectKind::RuntimePhase,
            index: 0,
        },
        0,
        0,
        0,
        0,
    ));
    let d = Directory::new();
    let good = d.file("phase-authority");
    f.publish(&good);
    assert!(open(&good, f.binding, Limits::default()).is_ok());
    let bad = d.file("different-valid-authority");
    rewrite(&good, &bad, |rows| put(rows, 33, 4, 1));
    assert!(open(&bad, f.binding, Limits::default()).is_err());
}
