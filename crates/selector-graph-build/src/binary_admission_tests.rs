use super::*;
fn fixture() -> (FactSnapshot, SymbolId, AdmittedContext, CapturedClasspath) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../fixtures/binary-resolution/resolution.jar");
    let digest = ContentHash(Sha256::digest(std::fs::read(&path).unwrap()).into());
    let entries = vec![ClasspathEntry {
        path,
        sha256: digest,
        kind: EntryKind::Jar,
    }];
    let loader = CapturedClasspath::new(entries.clone(), Limits::default()).unwrap();
    let mut builder = FactBuilder::new();
    let context = builder.intern("captured-context").unwrap();
    let path = builder.intern("Caller.scala").unwrap();
    let source = builder.intern("object Caller").unwrap();
    builder.facts.files.push(FileRecord {
        path,
        source,
        context,
        revision: StrId::NONE,
        source_hash: ContentHash([1; 32]),
        flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
    });
    let caller = builder.ensure_symbol("p/Caller.", FileId(0)).unwrap();
    let facts = builder.finish().unwrap();
    (
        facts,
        caller,
        AdmittedContext {
            id: context,
            name: "captured-context".into(),
            cache_metrics: ClassCacheMetrics::default(),
            phase: "test",
            active_method: caller,
            active_file: FileId(0),
            pending_methods: 0,
            admission: Admission::default(),
            entries,
            classes: HashMap::new(),
            shared_metadata: SharedMetadata::default(),
            java_feature: None,
            entries_at: Vec::new(),
        },
        loader,
    )
}
#[test]
fn optional_class_frontier_is_not_a_negative_entry_and_keeps_cached_headers() {
    let (mut facts, caller, mut context, mut loader) = fixture();
    context.admission.limits.classes_per_context = 1;
    let original = cache_class(&mut context, &mut loader, "fixture/ResolveLeaf")
        .unwrap()
        .unwrap();
    context.admission.derived = true;
    for _ in 0..3 {
        let result = cache_class(&mut context, &mut loader, "fixture/ResolveMid");
        assert!(
            matches!(result, Err(ref error) if matches!(DeferredReason::from_error(error),Some(DeferredReason::Classes)))
        );
        let fallback =
            optional_effect(&mut facts, &mut context, caller, FileId(0), result, None).unwrap();
        assert!(fallback.is_none());
    }
    assert_eq!(context.classes.len(), 1);
    assert_eq!(
        context.cache_metrics.unknown, 0,
        "budget deferral is not missing-class evidence"
    );
    let cached = cache_class(&mut context, &mut loader, "fixture/ResolveLeaf")
        .unwrap()
        .unwrap();
    assert!(Arc::ptr_eq(&original, &cached));
    assert_eq!(facts.issues.len(), 1, "one scoped guard per affected node");
    let issue = facts.issues[0];
    assert_eq!(
        (issue.kind, issue.symbol, issue.file),
        (IssueKind::UnknownExecution, caller, FileId(0))
    );
    assert!(
        facts
            .text(issue.detail)
            .contains("presence or absence was not established")
    );
    assert_eq!(context.admission.deferred, 3);
}

#[test]
fn hierarchy_deferral_is_retained_and_cannot_suppress_execution_guard_in_either_order() {
    for hierarchy_first in [false, true] {
        for bytes in [false, true] {
            let (mut facts, caller, mut context, mut loader) = fixture();
            let child = cache_class(&mut context, &mut loader, "fixture/ResolveLeaf")
                .unwrap()
                .unwrap();
            let file = FileId(facts.files.len() as u32);
            let path = append_text(&mut facts, &child.origin).unwrap();
            facts.files.push(FileRecord {
                path,
                source: StrId::NONE,
                revision: StrId::NONE,
                context: context.id,
                source_hash: child.hash,
                flags: FILE_BINARY_SOURCE,
            });
            facts.symbols[caller.index()].context = context.id;
            context.admission.derived = true;
            if bytes {
                context.admission.limits.bytes_per_context = 1;
            } else {
                context.admission.limits.classes_per_context = 1;
            }
            for hierarchy in [
                hierarchy_first,
                !hierarchy_first,
                hierarchy_first,
                !hierarchy_first,
            ] {
                let result = if hierarchy {
                    guarded_hierarchy_class(
                        &mut facts,
                        &mut context,
                        &mut loader,
                        "fixture/ResolveMid",
                        caller,
                        file,
                    )
                } else {
                    guarded_class(
                        &mut facts,
                        &mut context,
                        &mut loader,
                        "fixture/ResolveMid",
                        caller,
                        file,
                    )
                }
                .unwrap();
                assert!(result.is_none());
            }
            assert_eq!(facts.issues.len(), 2, "scope-specific deduplication");
            for kind in [IssueKind::IncompleteHierarchy, IssueKind::UnknownExecution] {
                let issue = facts.issues.iter().find(|i| i.kind == kind).unwrap();
                assert_eq!((issue.symbol, issue.file), (caller, file));
                assert_eq!(
                    facts.text(issue.detail).contains("ancestry metadata"),
                    kind == IssueKind::IncompleteHierarchy
                );
            }
            assert_eq!(context.admission.deferred, 4);
            assert_eq!(context.cache_metrics.unknown, 0);
            assert_eq!(context.classes.len(), 1);
            facts.validate().unwrap();
        }
    }
}

#[test]
fn hierarchy_scope_does_not_catch_provenance_or_mandatory_errors() {
    let (mut facts, caller, mut context, _) = fixture();
    for error in [
        Error::Invalid("binary class header owner"),
        Error::Limit("mandatory class budget"),
    ] {
        assert!(
            optional_result(
                &mut facts,
                &mut context,
                caller,
                FileId(0),
                Err::<(), _>(error),
                (),
                DiagnosticScope::Hierarchy
            )
            .is_err()
        );
    }
    assert!(facts.issues.is_empty());
    assert_eq!(context.admission.deferred, 0);
}
#[test]
fn optional_bytes_are_a_distinct_frontier_and_do_not_claim_absence() {
    let (mut facts, caller, mut context, mut loader) = fixture();
    context.admission.derived = true;
    context.admission.limits.bytes_per_context = 1;
    let result = cache_class(&mut context, &mut loader, "fixture/ResolveLeaf");
    assert!(
        matches!(result, Err(ref error) if matches!(DeferredReason::from_error(error),Some(DeferredReason::Bytes)))
    );
    optional_effect(&mut facts, &mut context, caller, FileId(0), result, None).unwrap();
    assert!(context.classes.is_empty());
    assert!(facts.text(facts.issues[0].detail).contains("byte budget"));
}
#[test]
fn mandatory_limits_and_provenance_errors_remain_fatal() {
    let (mut facts, caller, mut context, mut loader) = fixture();
    context.admission.limits.classes_per_context = 1;
    cache_class(&mut context, &mut loader, "fixture/ResolveLeaf").unwrap();
    let result = cache_class(&mut context, &mut loader, "fixture/ResolveMid");
    assert!(optional_effect(&mut facts, &mut context, caller, FileId(0), result, None).is_err());
    context.admission.derived = true;
    let failure: Result<Option<Arc<ClassBytes>>, Error> =
        Err(Error::Invalid("binary provider hash mismatch"));
    assert!(optional_effect(&mut facts, &mut context, caller, FileId(0), failure, None).is_err());
    assert!(facts.issues.is_empty());
}
#[test]
fn optional_method_budget_is_typed_and_policy_limits_seal_the_program() {
    let mut admission = Admission::default();
    admission.limits.methods = 3;
    assert!(DeferredReason::from_error(&admission.check_method(3).unwrap_err()).is_none());
    admission.derived = true;
    admission.method_allowance = 1;
    admission.check_method(0).unwrap();
    admission.admitted_method();
    assert!(matches!(
        DeferredReason::from_error(&admission.check_method(1).unwrap_err()),
        Some(DeferredReason::Methods)
    ));
    let facts = FactSnapshot::default();
    let normal = enriched_identity_with_limits(
        ContentHash::default(),
        ContentHash::default(),
        &facts,
        NativeAdmissionLimits::default(),
    );
    let smaller = enriched_identity_with_limits(
        ContentHash::default(),
        ContentHash::default(),
        &facts,
        admission.limits,
    );
    assert_ne!(normal, smaller);
}

#[test]
fn deferred_superclass_phase_keeps_the_known_class_initializer_edge() {
    let (mut facts, caller, mut context, mut loader) = fixture();
    let empty = append_text(&mut facts, "").unwrap();
    let mut registry = Registry {
        types: HashMap::new(),
        methods: HashMap::new(),
        method_events: Vec::new(),
        synthetic_methods: 0,
        fields: HashMap::new(),
        accessors: accessors::State::default(),
        files: HashMap::new(),
        empty,
        initialized: HashSet::new(),
        static_phases: HashMap::new(),
        static_active: HashSet::new(),
        bootstrap: HashMap::new(),
    };
    let mut pending = VecDeque::new();
    let initializer = registry
        .method(
            &mut facts,
            0,
            &mut context,
            &mut loader,
            MemberRef {
                owner: "fixture/FieldOverride",
                name: "<clinit>",
                descriptor: "()V",
            },
            None,
            None,
            &mut pending,
        )
        .unwrap();
    assert!(!initializer.is_none());
    context.admission.derived = true;
    context.admission.method_allowance = 10;
    context.admission.limits.classes_per_context = 1;
    let phase = registry
        .static_phase(
            &mut facts,
            0,
            &mut context,
            &mut loader,
            "fixture/FieldOverride",
            &mut pending,
        )
        .unwrap();
    let Initialization::Target(phase) = phase else {
        panic!("known own initializer must remain explicit")
    };
    let body = facts
        .bodies
        .iter()
        .find(|body| body.symbol == phase)
        .unwrap();
    let operations = &facts.operations[body.operations.range()];
    assert!(operations.iter().any(|op| op.opcode == Opcode::Unknown));
    assert!(
        operations
            .iter()
            .any(|op| op.opcode == Opcode::Initialize && op.target == initializer)
    );
    assert!(
        facts
            .issues
            .iter()
            .any(|issue| issue.symbol == caller && issue.kind == IssueKind::UnknownExecution)
    );
    assert!(!context.classes.contains_key("fixture/ResolveBase"));
}

#[test]
fn temporary_method_refusals_do_not_publish_or_poison_final_guards() {
    let (mut facts, caller, mut context, _) = fixture();
    context.admission.derived = true;
    context.admission.probe_method_quota = true;
    for _ in 0..2 {
        optional_effect(
            &mut facts,
            &mut context,
            caller,
            FileId(0),
            Err::<(), _>(DeferredReason::Methods.error()),
            (),
        )
        .unwrap();
    }
    assert!(facts.issues.is_empty());
    assert_eq!(context.admission.method_refusals, 2);
    context.admission.probe_method_quota = false;
    optional_effect(
        &mut facts,
        &mut context,
        caller,
        FileId(0),
        Err::<(), _>(DeferredReason::Methods.error()),
        (),
    )
    .unwrap();
    assert_eq!(facts.issues.len(), 1);
    assert!(
        facts
            .text(facts.issues[0].detail)
            .contains("method admission budget")
    );
    assert_eq!(context.admission.method_refusals, 3);
}

#[test]
fn probing_never_suppresses_class_byte_or_provenance_boundaries() {
    for reason in [DeferredReason::Classes, DeferredReason::Bytes] {
        let (mut facts, caller, mut context, _) = fixture();
        context.admission.probe_method_quota = true;
        optional_effect(
            &mut facts,
            &mut context,
            caller,
            FileId(0),
            Err::<(), _>(reason.error()),
            (),
        )
        .unwrap();
        assert_eq!(facts.issues.len(), 1);
        assert_eq!(context.admission.method_refusals, 0);
        assert!(
            optional_effect(
                &mut facts,
                &mut context,
                caller,
                FileId(0),
                Err::<(), _>(Error::Invalid("binary provider hash mismatch")),
                (),
            )
            .is_err()
        );
    }
}

#[derive(Debug, PartialEq, Eq)]
struct ObservedAdmission {
    methods: usize,
    refusals: u64,
    released: usize,
    received: usize,
    retried: usize,
    guards: usize,
}
/// The genuine javac/JVM fixture proves invokeSuper -> ResolveMid.ping. Three
/// separate contexts demand only a leaf method. Its global budget has room for
/// the fourth context's one callee, but that context's initial fair share is 0.
fn redistributed_fixture(workers: usize, methods: usize) -> (FactSnapshot, Vec<ObservedAdmission>) {
    redistributed_fixture_for(
        workers,
        methods,
        "binary-resolution/resolution.jar",
        ("fixture/ResolveBase", "inherited", "()Ljava/lang/Object;"),
        ("fixture/ResolveLeaf", "invokeSuper", "()Ljava/lang/Object;"),
        &[],
    )
}
fn redistributed_fixture_for(
    workers: usize,
    methods: usize,
    jar: &str,
    leaf: (&str, &str, &str),
    blocked: (&str, &str, &str),
    more_blocked: &[(&str, &str, &str)],
) -> (FactSnapshot, Vec<ObservedAdmission>) {
    let directory = tempfile::tempdir().unwrap();
    let jar = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../fixtures")
        .join(jar);
    let digest = ContentHash(Sha256::digest(std::fs::read(&jar).unwrap()).into());
    let witness: serde_json::Value = serde_json::from_slice(
        &std::fs::read(jar.parent().unwrap().join("manifest.json")).unwrap(),
    )
    .unwrap();
    let records = witness["outputs"]
        .as_array()
        .or_else(|| witness["files"].as_array())
        .unwrap();
    let pinned = records
        .iter()
        .find(|record| record["path"].as_str() == jar.file_name().and_then(|name| name.to_str()))
        .unwrap();
    assert_eq!(
        pinned["sha256"].as_str().unwrap(),
        digest.to_string(),
        "use the exact classfiles bound to the independent JVM witness"
    );
    if blocked.1 == "invokeSuper" {
        assert!(
            witness["jvm_witness"]
                .as_str()
                .unwrap()
                .contains("superResult=mid\n")
        );
    }
    let mut builder = FactBuilder::new();
    let revision = builder.intern("native-admission-redistribution").unwrap();
    builder.facts.revision = revision;
    let mut contexts = Vec::new();
    let mut roots = Vec::new();
    for index in 0..4 {
        let name = format!("context-{index}");
        let context = builder.intern(&name).unwrap();
        let path = builder.intern(&format!("Context{index}.scala")).unwrap();
        builder.facts.files.push(FileRecord {
            path,
            source: StrId::NONE,
            revision,
            context,
            source_hash: ContentHash::default(),
            flags: 0,
        });
        contexts.push(serde_json::json!({"id":name,"entries":[{
            "path":jar,"kind":"jar","sha256":digest.to_string()
        }]}));
        let (owner, method, descriptor) = if index == 3 { blocked } else { leaf };
        roots.push(serde_json::json!({
            "context":name,"jvm_owner":owner,"jvm_name":method,"descriptor":descriptor
        }));
        if index == 3 {
            for &(owner, method, descriptor) in more_blocked {
                roots.push(serde_json::json!({
                    "context":name,"jvm_owner":owner,"jvm_name":method,"descriptor":descriptor
                }));
            }
        }
    }
    let mut facts = builder.finish().unwrap();
    let path = directory.path().join("binary.json");
    std::fs::write(
        &path,
        serde_json::to_vec(&serde_json::json!({
            "version":1,"revision":"native-admission-redistribution",
            "contexts":contexts,"methods":roots
        }))
        .unwrap(),
    )
    .unwrap();
    let mut inputs = load_binary_manifest_with_options(
        &path,
        &facts,
        &BinaryInputOptions {
            workers,
            ..Default::default()
        },
    )
    .unwrap();
    augment_binary_facts_with_limits(
        &mut facts,
        &mut inputs,
        NativeAdmissionLimits {
            methods,
            ..Default::default()
        },
    )
    .unwrap();
    let metrics = inputs
        .context_metrics()
        .map(|context| ObservedAdmission {
            methods: context.derived_methods,
            refusals: context.deferred_admissions,
            released: context.method_slots_released,
            received: context.method_slots_received,
            retried: context.retried_callers,
            guards: context.method_guard_rows,
        })
        .collect();
    (facts, metrics)
}

#[test]
fn unused_context_shares_admit_genuine_super_callee_once_under_the_same_global_cap() {
    let (facts, metrics) = redistributed_fixture(1, 5);
    let (parallel, other_metrics) = redistributed_fixture(4, 5);
    assert_eq!(facts.identity, parallel.identity);
    assert_eq!(metrics, other_metrics);
    assert_eq!(
        metrics.iter().map(|metric| metric.released).sum::<usize>(),
        1
    );
    assert_eq!(
        (metrics[3].received, metrics[3].retried, metrics[3].guards),
        (1, 1, 0)
    );
    let directory = tempfile::tempdir().unwrap();
    let one = directory.path().join("one.bin");
    let four = directory.path().join("four.bin");
    selector_facts::codec::write(&one, &facts).unwrap();
    selector_facts::codec::write(&four, &parallel).unwrap();
    assert_eq!(std::fs::read(one).unwrap(), std::fs::read(four).unwrap());
    assert_eq!(
        metrics.iter().map(|metric| metric.methods).sum::<usize>(),
        1
    );
    assert_eq!(
        (metrics[3].methods, metrics[3].refusals),
        (1, 1),
        "first refusal is historical, not a remaining guard"
    );
    let root = facts
        .symbols
        .iter()
        .enumerate()
        .find(|(_, symbol)| {
            facts.text(symbol.context) == "context-3"
                && facts.text(symbol.name)
                    == native_name("fixture/ResolveLeaf", "invokeSuper", "()Ljava/lang/Object;")
        })
        .map(|(index, _)| SymbolId(index as u32))
        .unwrap();
    let body = facts
        .bodies
        .iter()
        .find(|body| body.symbol == root)
        .unwrap();
    let operations = &facts.operations[body.operations.range()];
    let call = operations
        .iter()
        .find(|op| op.opcode == Opcode::Call)
        .unwrap();
    assert!(!call.target.is_none());
    assert_eq!(
        facts.symbol_name(call.target),
        native_name("fixture/ResolveMid", "ping", "()Ljava/lang/Object;")
    );
    assert!(!operations.iter().any(|op| op.opcode == Opcode::Unknown));
    assert!(!facts.issues.iter().any(|issue| issue.symbol == root));
    assert_eq!(
        facts
            .bodies
            .iter()
            .filter(|body| body.symbol == call.target)
            .count(),
        1
    );
    facts.validate().unwrap();
}

#[test]
fn genuinely_exhausted_global_budget_publishes_the_unresolved_recipe_and_guard() {
    let (facts, metrics) = redistributed_fixture(1, 4);
    assert_eq!(
        metrics.iter().map(|metric| metric.methods).sum::<usize>(),
        0
    );
    assert_eq!(
        (metrics[3].received, metrics[3].retried, metrics[3].guards),
        (0, 1, 1)
    );
    assert_eq!(
        metrics[3].refusals, 2,
        "one provisional refusal plus one final refusal"
    );
    let root = facts
        .symbols
        .iter()
        .enumerate()
        .find(|(_, symbol)| {
            facts.text(symbol.context) == "context-3"
                && facts.text(symbol.name)
                    == native_name("fixture/ResolveLeaf", "invokeSuper", "()Ljava/lang/Object;")
        })
        .map(|(index, _)| SymbolId(index as u32))
        .unwrap();
    let body = facts
        .bodies
        .iter()
        .find(|body| body.symbol == root)
        .unwrap();
    let operations = &facts.operations[body.operations.range()];
    assert!(operations.iter().any(|op| op.opcode == Opcode::Unknown));
    assert!(facts.issues.iter().any(|issue| issue.symbol == root
        && issue.kind == IssueKind::UnknownExecution
        && facts.text(issue.detail).contains("method admission budget")));
    facts.validate().unwrap();
}

#[test]
fn zero_global_method_budget_is_rejected_before_any_optional_admission() {
    assert!(
        NativeAdmissionLimits {
            methods: 0,
            ..Default::default()
        }
        .validate()
        .is_err()
    );
}

#[test]
fn lambda_bearing_recipe_is_never_redeclared_or_silently_retried() {
    let (facts, metrics) = redistributed_fixture_for(
        4,
        6,
        "native-lambdas/bytecode.jar",
        ("lambdacase/Probe", "receiverEffects", "()I"),
        ("lambdacase/Probe", "boundClosure", "()Ljava/lang/Runnable;"),
        &[],
    );
    assert_eq!(
        metrics.iter().map(|metric| metric.methods).sum::<usize>(),
        0,
        "the bounded retry policy is explicitly lambda-free"
    );
    assert_eq!(
        (metrics[3].received, metrics[3].retried, metrics[3].guards),
        (0, 0, 1)
    );
    assert_eq!(
        metrics[3].refusals, 1,
        "lambda caller runs once even with unused global slots"
    );
    let root = facts
        .symbols
        .iter()
        .enumerate()
        .find(|(_, symbol)| {
            facts.text(symbol.context) == "context-3"
                && facts.text(symbol.name)
                    == native_name("lambdacase/Probe", "boundClosure", "()Ljava/lang/Runnable;")
        })
        .map(|(index, _)| SymbolId(index as u32))
        .unwrap();
    assert_eq!(
        facts
            .bodies
            .iter()
            .filter(|body| body.symbol == root)
            .count(),
        1
    );
    assert!(facts.issues.iter().any(|issue| issue.symbol == root
        && issue.kind == IssueKind::UnknownExecution
        && facts.text(issue.detail).contains("method admission budget")));
    assert!(
        !facts
            .symbols
            .iter()
            .any(|symbol| facts.text(symbol.name).starts_with("@jvm-lambda/"))
    );
    facts.validate().unwrap();
}

#[test]
fn redistributed_allowances_release_unused_reservations_in_stable_context_order() {
    let mut contexts: Vec<_> = (0..4).map(|_| fixture().2).collect();
    for (index, context) in contexts.iter_mut().enumerate() {
        context.admission.methods = index;
        context.admission.method_allowance = 100;
        context.admission.probe_method_quota = true;
    }
    redistribute_methods(&mut contexts, &[false, true, false, true], 3);
    assert_eq!(
        contexts
            .iter()
            .map(|c| c.admission.method_allowance)
            .collect::<Vec<_>>(),
        [0, 3, 2, 4]
    );
    assert!(contexts.iter().all(|c| !c.admission.probe_method_quota));
    assert_eq!(
        contexts
            .iter()
            .map(|c| c.admission.method_allowance - c.admission.methods)
            .sum::<usize>(),
        3
    );
}

#[test]
fn a_published_partial_static_phase_keeps_its_method_guard_after_redistribution() {
    let (mut facts, caller, mut context, mut loader) = fixture();
    let empty = append_text(&mut facts, "").unwrap();
    let mut registry = Registry {
        types: HashMap::new(),
        methods: HashMap::new(),
        method_events: Vec::new(),
        synthetic_methods: 0,
        fields: HashMap::new(),
        accessors: accessors::State::default(),
        files: HashMap::new(),
        empty,
        initialized: HashSet::new(),
        static_phases: HashMap::new(),
        static_active: HashSet::new(),
        bootstrap: HashMap::new(),
    };
    let mut pending = VecDeque::new();
    let own = registry
        .method(
            &mut facts,
            0,
            &mut context,
            &mut loader,
            MemberRef {
                owner: "fixture/FieldOverride",
                name: "<clinit>",
                descriptor: "()V",
            },
            None,
            None,
            &mut pending,
        )
        .unwrap();
    context.admission.derived = true;
    context.admission.method_allowance = 0;
    context.admission.probe_method_quota = true;
    let phase = registry
        .static_phase(
            &mut facts,
            0,
            &mut context,
            &mut loader,
            "fixture/FieldOverride",
            &mut pending,
        )
        .unwrap();
    assert!(
        context.admission.probe_method_quota,
        "caller probe restored"
    );
    assert!(context.admission.method_refusals > 0);
    assert!(
        facts.issues.iter().any(|issue| issue.symbol == caller
            && facts.text(issue.detail).contains("method admission budget")),
        "a published phase retains its actual boundary even during caller probing"
    );
    let Initialization::Target(phase) = phase else {
        panic!("known own phase")
    };
    let body = facts
        .bodies
        .iter()
        .find(|body| body.symbol == phase)
        .unwrap();
    assert!(
        facts.operations[body.operations.range()]
            .iter()
            .any(|op| op.opcode == Opcode::Initialize && op.target == own)
    );
    let unknown_before = facts
        .operations
        .iter()
        .filter(|op| op.opcode == Opcode::Unknown)
        .count();
    assert!(
        unknown_before > 0,
        "superclass initialization stays explicitly incomplete"
    );
    let issues_before = facts.issues.len();
    context.admission.probe_method_quota = false;
    context.admission.method_allowance = 10;
    assert!(matches!(registry.static_phase(
        &mut facts, 0, &mut context, &mut loader, "fixture/FieldOverride", &mut pending,
    ).unwrap(), Initialization::Target(id) if id == phase));
    assert_eq!(
        facts
            .operations
            .iter()
            .filter(|op| op.opcode == Opcode::Unknown)
            .count(),
        unknown_before
    );
    assert_eq!(facts.issues.len(), issues_before);
    assert_eq!(
        registry.methods.len(),
        1,
        "partial initialization is not rebuilt or double charged"
    );
}

#[test]
fn two_deferred_callers_share_one_new_callee_declaration_and_preserve_each_effect() {
    let (facts, metrics) = redistributed_fixture_for(
        4,
        6,
        "native-envelope/bytecode.jar",
        ("envelopecase/Probe$Scalar", "disjointScalar", "(I)I"),
        ("envelopecase/Probe", "branch", "(Z)I"),
        &[("envelopecase/Probe", "sparseSwitch", "(I)I")],
    );
    assert_eq!((metrics[3].methods, metrics[3].refusals), (1, 2));
    assert_eq!(
        (metrics[3].received, metrics[3].retried, metrics[3].guards),
        (1, 2, 0)
    );
    assert_eq!(
        metrics.iter().map(|metric| metric.methods).sum::<usize>(),
        1,
        "five mandatory methods plus one shared target exactly fill cap6"
    );
    let changed = facts
        .symbols
        .iter()
        .enumerate()
        .find(|(_, symbol)| {
            facts.text(symbol.context) == "context-3"
                && facts.text(symbol.name) == native_name("envelopecase/Probe", "changed", "()I")
        })
        .map(|(index, _)| SymbolId(index as u32))
        .unwrap();
    assert_eq!(
        facts
            .bodies
            .iter()
            .filter(|body| body.symbol == changed)
            .count(),
        1
    );
    for (name, descriptor) in [("branch", "(Z)I"), ("sparseSwitch", "(I)I")] {
        let root = facts
            .symbols
            .iter()
            .enumerate()
            .find(|(_, symbol)| {
                facts.text(symbol.context) == "context-3"
                    && facts.text(symbol.name)
                        == native_name("envelopecase/Probe", name, descriptor)
            })
            .map(|(index, _)| SymbolId(index as u32))
            .unwrap();
        let body = facts
            .bodies
            .iter()
            .find(|body| body.symbol == root)
            .unwrap();
        let ops = &facts.operations[body.operations.range()];
        assert!(
            ops.iter()
                .any(|op| op.opcode == Opcode::Call && op.target == changed)
        );
        assert!(!ops.iter().any(|op| op.opcode == Opcode::Unknown));
        assert!(!facts.issues.iter().any(|issue| issue.symbol == root));
    }
    let body = facts
        .bodies
        .iter()
        .find(|body| body.symbol == changed)
        .unwrap();
    assert!(
        facts.operations[body.operations.range()]
            .iter()
            .any(|op| op.opcode == Opcode::StoreField),
        "the newly admitted callee keeps its actual native field effects"
    );
    facts.validate().unwrap();
}

#[test]
fn exact_generated_method_quota_retains_deduplicated_dispatch_rows_and_truthful_counters() {
    let (mut facts, receiver, mut context, _) = fixture();
    facts.symbols[receiver.index()].kind = 13;
    facts.symbols[receiver.index()].flags = SYMBOL_DEFINED;
    facts.symbols[receiver.index()].context = context.id;
    let mut target = facts.symbols[receiver.index()];
    target.name = append_text(&mut facts, "p/Caller#missing().").unwrap();
    target.owner = receiver;
    target.kind = 3;
    let target_id = SymbolId(facts.symbols.len() as u32);
    facts.symbols.push(target);
    for _ in 0..3 {
        let result = optional_generated_method(
            &mut facts,
            &mut context,
            receiver,
            FileId(0),
            &[target_id, target_id],
            false,
            Err(DeferredReason::Methods.error()),
        )
        .unwrap();
        assert!(result.is_none());
    }
    assert!(
        facts.issues.is_empty(),
        "no unconditional receiver-root guard"
    );
    assert_eq!(facts.relations.len(), 1);
    assert_eq!(facts.relations[0].kind, RelationKind::DeferredDispatch);
    assert_eq!(
        (facts.relations[0].source, facts.relations[0].target),
        (receiver, target_id)
    );
    assert_eq!(context.admission.deferred, 3);
    assert_eq!(context.admission.method_refusals, 3);
    assert_eq!(context.admission.method_guard_rows, 0);
    assert_eq!(context.admission.scoped_dispatch_rows, 1);
    deferred_generated_frontier(
        &mut facts,
        &mut context,
        receiver,
        FileId(0),
        &[target_id],
        false,
    )
    .unwrap();
    assert_eq!(
        (
            context.admission.deferred,
            context.admission.method_refusals
        ),
        (3, 3),
        "publishing an already counted refusal cannot count it again"
    );
    facts.validate().unwrap();
    let tmp = tempfile::tempdir().unwrap();
    selector_facts::codec::write(&tmp.path().join("facts.bin"), &facts).unwrap();
    let restored = selector_facts::codec::read(&tmp.path().join("facts.bin")).unwrap();
    assert_eq!(restored.relations[0].kind, RelationKind::DeferredDispatch);
    for case in 0..6 {
        let mut malformed = selector_facts::codec::read(&tmp.path().join("facts.bin")).unwrap();
        match case {
            0 => malformed.symbols[receiver.index()].kind = 14,
            1 => malformed.symbols[target_id.index()].kind = 8,
            2 => malformed.symbols[target_id.index()].owner = SymbolId::NONE,
            3 => malformed.relations[0].file = FileId::NONE,
            4 => malformed.files[0].context = StrId::NONE,
            5 => malformed.symbols[target_id.index()].context = StrId::NONE,
            _ => unreachable!(),
        }
        assert!(
            malformed.validate().is_err(),
            "invalid scoped provenance case {case}"
        );
    }
}

#[test]
fn unproved_aliases_other_budgets_and_invalid_inputs_never_silently_lose_guards() {
    for case in 0..5 {
        let (mut facts, receiver, mut context, _) = fixture();
        let reason = match case {
            1 => DeferredReason::Classes,
            2 => DeferredReason::Bytes,
            _ => DeferredReason::Methods,
        };
        let contracts: &[SymbolId] = if case == 3 { &[] } else { &[receiver] };
        let result = if case == 4 {
            Err(Error::Invalid("changed provider hash"))
        } else {
            Err(reason.error())
        };
        let result = optional_generated_method(
            &mut facts,
            &mut context,
            receiver,
            FileId(0),
            contracts,
            case == 0,
            result,
        );
        if case == 4 {
            assert!(result.is_err());
        } else {
            assert!(result.unwrap().is_none());
            assert_eq!(facts.issues.len(), 1);
        }
        assert!(facts.relations.is_empty(), "case {case}");
        assert_eq!(context.admission.scoped_dispatch_rows, 0);
    }
}

#[test]
fn scoped_frontier_rows_are_bounded_and_overflow_keeps_one_receiver_marker() {
    let (mut facts, receiver, mut context, _) = fixture();
    context.admission.method_allowance = 1;
    facts.symbols[receiver.index()].kind = 13;
    facts.symbols[receiver.index()].flags = SYMBOL_DEFINED;
    facts.symbols[receiver.index()].context = context.id;
    let mut targets = Vec::new();
    for index in 0..3 {
        let mut declaration = facts.symbols[receiver.index()];
        declaration.name = append_text(&mut facts, &format!("p/Caller#missing{index}().")).unwrap();
        declaration.kind = 3;
        declaration.owner = receiver;
        targets.push(SymbolId(facts.symbols.len() as u32));
        facts.symbols.push(declaration);
    }
    for contract in [targets[0], targets[1], targets[2], targets[0]] {
        optional_generated_method(
            &mut facts,
            &mut context,
            receiver,
            FileId(0),
            &[contract],
            false,
            Err(DeferredReason::Methods.error()),
        )
        .unwrap();
    }
    assert_eq!(
        facts.relations.len(),
        2,
        "the exact-row allowance plus one wildcard bounds retained bookkeeping"
    );
    assert_eq!(facts.relations[0].target, targets[0]);
    assert_eq!(context.admission.dispatch_frontiers.len(), 1);
    assert_eq!(context.admission.scoped_dispatch_rows, 1);
    assert_eq!(context.admission.receiver_dispatch_rows, 1);
    assert_eq!(
        facts.relations[1].kind,
        RelationKind::DeferredReceiverDispatch
    );
    assert_eq!(
        (facts.relations[1].source, facts.relations[1].target),
        (receiver, receiver)
    );
    assert_eq!(context.admission.deferred, 4);
    assert_eq!(context.admission.method_refusals, 4);
    assert_eq!(context.admission.method_guard_rows, 0);
    assert!(facts.issues.is_empty());
    facts.validate().unwrap();
}

#[test]
fn receiver_frontier_is_contextual_deduplicated_and_strictly_validated() {
    let (mut facts, receiver, mut context, _) = fixture();
    facts.symbols[receiver.index()].kind = 13;
    facts.symbols[receiver.index()].flags = SYMBOL_DEFINED;
    facts.symbols[receiver.index()].context = context.id;
    for counted in [true, true, false] {
        deferred_receiver_frontier(&mut facts, &mut context, receiver, FileId(0), counted).unwrap();
    }
    assert_eq!(context.admission.receiver_dispatch_rows, 1);
    assert_eq!(
        (
            context.admission.deferred,
            context.admission.method_refusals
        ),
        (2, 2)
    );
    assert!(facts.issues.is_empty());
    facts.validate().unwrap();
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("receiver-frontier.bin");
    selector_facts::codec::write(&path, &facts).unwrap();
    let restored = selector_facts::codec::read(&path).unwrap();
    assert_eq!(
        restored.relations[0].kind,
        RelationKind::DeferredReceiverDispatch
    );
    for case in 0..5 {
        let mut bad = selector_facts::codec::read(&path).unwrap();
        match case {
            0 => bad.relations[0].target = SymbolId::NONE,
            1 => bad.symbols[receiver.index()].kind = 3,
            2 => bad.symbols[receiver.index()].flags = 0,
            3 => bad.relations[0].file = FileId::NONE,
            4 => bad.symbols[receiver.index()].context = StrId::NONE,
            _ => unreachable!(),
        }
        assert!(bad.validate().is_err(), "case {case}");
    }
}

fn scoped_fixture() -> (FactSnapshot, SymbolId, SymbolId, SymbolId, AdmittedContext) {
    let (mut facts, receiver, context, _) = fixture();
    facts.symbols[receiver.index()].kind = 13;
    facts.symbols[receiver.index()].flags = SYMBOL_DEFINED;
    facts.symbols[receiver.index()].context = context.id;
    facts.symbols[receiver.index()].file = FileId(0);
    let mut owner = facts.symbols[receiver.index()];
    owner.name = append_text(&mut facts, "p/Contract#").unwrap();
    owner.flags = SYMBOL_JVM_CLASS_HEADER_VERIFIED;
    owner.kind = 14;
    owner.file = FileId::NONE;
    let owner_id = SymbolId(facts.symbols.len() as u32);
    facts.symbols.push(owner);
    let mut target = owner;
    target.name = append_text(&mut facts, "p/Contract#missing().").unwrap();
    target.owner = owner_id;
    target.flags = 0;
    target.kind = 3;
    let target_id = SymbolId(facts.symbols.len() as u32);
    facts.symbols.push(target);
    (facts, receiver, owner_id, target_id, context)
}

#[test]
fn final_noncallable_aliases_and_foreign_scope_files_keep_broad_guards() {
    for case in 0..7 {
        let (mut facts, receiver, owner, target, mut context) = scoped_fixture();
        let other_context = append_text(&mut facts, "other-context").unwrap();
        let mut file = FileId(0);
        match case {
            // An identity initially callable may acquire a verified class facet
            // during the final native hierarchy wave. It is no longer a legal
            // callable alias, even though its exact ABI was seen earlier.
            0 => facts.symbols[target.index()].kind = 13,
            1 => facts.symbols[target.index()].kind = 8,
            2 => facts.symbols[target.index()].owner = SymbolId::NONE,
            3 => facts.symbols[owner.index()].kind = 0,
            4 => facts.symbols[owner.index()].context = other_context,
            5 => {
                let mut foreign = facts.files[0];
                foreign.context = other_context;
                file = FileId(facts.files.len() as u32);
                facts.files.push(foreign);
            }
            6 => file = FileId::NONE,
            _ => unreachable!(),
        }
        for _ in 0..2 {
            assert!(
                optional_generated_method(
                    &mut facts,
                    &mut context,
                    receiver,
                    file,
                    &[target],
                    false,
                    Err(DeferredReason::Methods.error()),
                )
                .unwrap()
                .is_none()
            );
        }
        assert!(facts.relations.is_empty(), "case {case}");
        assert_eq!(context.admission.scoped_dispatch_rows, 0);
        assert_eq!(context.admission.method_guard_rows, 1);
        assert_eq!(context.admission.method_refusals, 2);
        assert_eq!(facts.issues.len(), 1);
        assert_eq!(facts.issues[0].kind, IssueKind::UnknownExecution);
        assert_eq!(facts.issues[0].symbol, receiver);
        assert_eq!(facts.issues[0].file, FileId(0));
        assert!(
            facts
                .text(facts.issues[0].detail)
                .contains("method admission budget")
        );
        deferred_generated_frontier(&mut facts, &mut context, receiver, file, &[target], false)
            .unwrap();
        assert_eq!(context.admission.method_refusals, 2, "no recount");
        facts.validate().unwrap();
    }
}

#[test]
fn valid_foreign_contract_owner_keeps_its_exact_scoped_frontier() {
    let (mut facts, receiver, owner, target, mut context) = scoped_fixture();
    let other = append_text(&mut facts, "other-context").unwrap();
    facts.symbols[owner.index()].context = other;
    facts.symbols[target.index()].context = other;
    deferred_generated_frontier(
        &mut facts,
        &mut context,
        receiver,
        FileId(0),
        &[target],
        false,
    )
    .unwrap();
    assert!(facts.issues.is_empty());
    assert_eq!(facts.relations.len(), 1);
    assert_eq!(facts.relations[0].target, target);
    assert_eq!(context.admission.scoped_dispatch_rows, 1);
    assert_eq!(context.admission.method_refusals, 0);
    facts.validate().unwrap();
}

#[test]
fn invalid_dispatch_references_and_unadmitted_receivers_remain_fatal() {
    for case in 0..7 {
        let (mut facts, mut receiver, _, mut target, mut context) = scoped_fixture();
        let mut file = FileId(0);
        match case {
            0 => receiver = SymbolId(999),
            1 => target = SymbolId(999),
            2 => facts.symbols[target.index()].owner = SymbolId(999),
            3 => file = FileId(999),
            4 => facts.symbols[receiver.index()].kind = 14,
            5 => facts.symbols[receiver.index()].flags = 0,
            6 => {
                facts.symbols[receiver.index()].context =
                    append_text(&mut facts, "wrong-context").unwrap();
                facts.symbols[target.index()].kind = 13;
            }
            _ => unreachable!(),
        }
        assert!(
            deferred_generated_frontier(
                &mut facts,
                &mut context,
                receiver,
                file,
                &[target],
                false,
            )
            .is_err(),
            "case {case}"
        );
        assert!(facts.relations.is_empty());
        assert!(facts.issues.is_empty());
    }
}

#[test]
fn existing_method_reuse_never_spends_another_slot_or_discovery_event() {
    let (mut facts, _, mut context, mut loader) = fixture();
    let empty = append_text(&mut facts, "").unwrap();
    let mut registry = Registry {
        types: HashMap::new(),
        methods: HashMap::new(),
        method_events: Vec::new(),
        synthetic_methods: 0,
        fields: HashMap::new(),
        accessors: accessors::State::default(),
        files: HashMap::new(),
        empty,
        initialized: HashSet::new(),
        static_phases: HashMap::new(),
        static_active: HashSet::new(),
        bootstrap: HashMap::new(),
    };
    let mut pending = VecDeque::new();
    let member = MemberRef {
        owner: "fixture/ResolveBase",
        name: "inherited",
        descriptor: "()Ljava/lang/Object;",
    };
    let first = registry
        .method(
            &mut facts,
            0,
            &mut context,
            &mut loader,
            member,
            None,
            None,
            &mut pending,
        )
        .unwrap();
    assert!(!first.is_none());
    context.admission.derived = true;
    context.admission.method_allowance = 0;
    context.admission.limits.methods = 1;
    for _ in 0..1024 {
        assert_eq!(
            registry
                .method(
                    &mut facts,
                    0,
                    &mut context,
                    &mut loader,
                    member,
                    None,
                    None,
                    &mut pending
                )
                .unwrap(),
            first
        );
    }
    assert_eq!(registry.methods.len(), 1);
    assert_eq!(registry.method_events.len(), 1);
    assert_eq!(pending.len(), 1);
    assert_eq!(context.admission.methods, 0);
    let event = &registry.method_events[0];
    let observed = event.class.metadata.methods().nth(event.ordinal).unwrap();
    assert_eq!(
        (observed.name, observed.descriptor),
        (member.name, member.descriptor)
    );
    assert_eq!(event.data.symbol, first);
}

#[test]
fn final_broad_frontier_keeps_its_issue_without_recounting_the_attempt() {
    let (mut facts, receiver, mut context, _) = fixture();
    context.admission.deferred = 7;
    context.admission.method_refusals = 7;
    context.admission.probe_method_quota = true;
    deferred_generated_frontier(&mut facts, &mut context, receiver, FileId(0), &[], true).unwrap();
    assert_eq!(
        (
            context.admission.deferred,
            context.admission.method_refusals
        ),
        (7, 7)
    );
    assert_eq!(context.admission.method_guard_rows, 1);
    assert_eq!(facts.issues.len(), 1);
    assert_eq!(facts.issues[0].kind, IssueKind::UnknownExecution);
    facts.validate().unwrap();
}
