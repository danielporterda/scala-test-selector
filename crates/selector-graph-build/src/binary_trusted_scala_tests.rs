use super::*;
const STATICS_BYTES: &[u8] =
    include_bytes!("../../../fixtures/trusted-scala-runtime/scala/runtime/Statics.class");
const VM_BYTES: &[u8] =
    include_bytes!("../../../fixtures/trusted-scala-runtime/scala/runtime/Statics$VM.class");
const VH_BYTES: &[u8] =
    include_bytes!("../../../fixtures/trusted-scala-runtime/java/lang/invoke/VarHandle.class");
fn digest(bytes: &[u8]) -> ContentHash {
    ContentHash(Sha256::digest(bytes).into())
}
fn class_bytes(bytes: &[u8], origin: &str) -> Arc<ClassBytes> {
    let bytes: Arc<[u8]> = Arc::from(bytes);
    Arc::new(ClassBytes {
        hash: digest(&bytes),
        origin: origin.into(),
        metadata: Arc::new(binary::ClassMetadata::new(bytes.clone(), Limits::default()).unwrap()),
        bytes,
    })
}
// Explicitly normalized private admission records over unmodified genuine bytes.
// Production obtains these records only through the pinned ordered-classpath lane.
fn context() -> (AdmittedContext, CapturedClasspath) {
    let root = PathBuf::from("/normalized/declared-java.base.jar");
    let mut classes = HashMap::new();
    classes.insert(
        STATICS.into(),
        CachedClass::Found(class_bytes(
            STATICS_BYTES,
            "/normalized/scala.jar!/scala/runtime/Statics.class",
        )),
    );
    classes.insert(
        VM.into(),
        CachedClass::Found(class_bytes(
            VM_BYTES,
            "/normalized/scala.jar!/scala/runtime/Statics$VM.class",
        )),
    );
    classes.insert(
        VAR_HANDLE.into(),
        CachedClass::Found(class_bytes(
            VH_BYTES,
            "/normalized/declared-java.base.jar!/java/lang/invoke/VarHandle.class",
        )),
    );
    (
        AdmittedContext {
            id: StrId(0),
            name: "normalized-context".into(),
            cache_metrics: Default::default(),
            phase: "model-test",
            active_method: SymbolId::NONE,
            active_file: FileId::NONE,
            pending_methods: 0,
            admission: Admission::default(),
            entries: vec![ClasspathEntry {
                path: root,
                sha256: ContentHash([3; 32]),
                kind: EntryKind::Jar,
            }],
            classes,
            shared_metadata: SharedMetadata::default(),
            java_feature: Some(21),
            entries_at: Vec::new(),
        },
        CapturedClasspath::new(Vec::new(), Limits::default()).unwrap(),
    )
}
#[test]
fn exact_fence_retains_handle_read_and_bootstrap_keeps_opaque_return_and_real_init() {
    for (bytes, owner, name, descriptor, effect) in [
        (
            STATICS_BYTES,
            STATICS,
            "releaseFence",
            "()V",
            MemoryEffect::ReleaseFence,
        ),
        (
            VM_BYTES,
            VM,
            "mkHandle",
            "()Ljava/lang/invoke/MethodHandle;",
            MemoryEffect::HandleBootstrap,
        ),
    ] {
        let class = binary::parse_class(bytes, Limits::default()).unwrap();
        let method = class.method(name, Some(descriptor)).unwrap();
        let input = class_bytes(bytes, "matched-library");
        let (mut context, mut loader) = context();
        let modeled = model(&mut context, &mut loader, &class, method, &input, true)
            .unwrap()
            .unwrap();
        assert_eq!(modeled.memory_effect, effect);
        assert!(modeled.summary.unknown.is_none());
        assert!(modeled.summary.calls.is_empty());
        assert!(modeled.summary.field_writes.is_empty());
        if owner == STATICS {
            assert!(matches!(
                modeled.summary.values.as_slice(),
                [Value::StaticField(MemberRef {
                    owner: VM,
                    name: "RELEASE_FENCE",
                    descriptor: HANDLE
                })]
            ));
            assert!(modeled.additional_initialization_owners.is_empty());
        } else {
            assert_eq!(modeled.additional_initialization_owners, &[VAR_HANDLE]);
            assert!(matches!(
                modeled.summary.values.as_slice(),
                [Value::UnknownData]
            ));
            assert_eq!(modeled.summary.returned, Some(binary::BinaryValueId(0)));
        }
    }
    let vm = binary::parse_class(VM_BYTES, Limits::default()).unwrap();
    let init = vm.method("<clinit>", Some("()V")).unwrap();
    assert!(matched(&vm, init, digest(VM_BYTES)).is_none());
    let original = binary::summarize(&vm, init, Limits::default());
    assert_eq!(original.calls[0].member.name, "mkHandle");
    assert_eq!(original.field_writes[0].member.name, "RELEASE_FENCE");
}
#[test]
fn missing_platform_sibling_foreign_prefix_and_changed_runtime_never_activate_model() {
    for case in 0..5 {
        let (mut context, mut loader) = context();
        let mut platform = true;
        match case {
            0 => platform = false,
            1 => {
                context.classes.insert(
                    VM.into(),
                    CachedClass::Unknown(binary::ErrorKind::UnavailableInput),
                );
            }
            2 => {
                context.classes.insert(
                    VAR_HANDLE.into(),
                    CachedClass::Found(class_bytes(
                        VH_BYTES,
                        "/normalized/later-provider.jar!/java/lang/invoke/VarHandle.class",
                    )),
                );
            }
            3 => context.java_feature = Some(17),
            4 => {
                let mut bytes = VM_BYTES.to_vec();
                bytes[5] ^= 1;
                context.classes.insert(
                    VM.into(),
                    CachedClass::Found(class_bytes(
                        &bytes,
                        "/normalized/scala.jar!/scala/runtime/Statics$VM.class",
                    )),
                );
            }
            _ => unreachable!(),
        }
        let class = binary::parse_class(STATICS_BYTES, Limits::default()).unwrap();
        let method = class.method("releaseFence", Some("()V")).unwrap();
        assert!(
            model(
                &mut context,
                &mut loader,
                &class,
                method,
                &class_bytes(STATICS_BYTES, "library"),
                platform
            )
            .unwrap()
            .is_none(),
            "case{case}"
        );
        assert!(
            binary::summarize(&class, method, Limits::default())
                .calls
                .iter()
                .any(|call| call.member.owner == "java/lang/invoke/MethodHandle"),
            "the original invoke recipe stays available"
        );
    }
}
#[test]
fn exact_code_abi_flags_and_class_hash_are_required_not_only_member_spelling() {
    let class = binary::parse_class(STATICS_BYTES, Limits::default()).unwrap();
    let method = class.method("releaseFence", Some("()V")).unwrap();
    assert!(matched(&class, method, ContentHash([9; 32])).is_none());
    let mut wrong = *method;
    wrong.flags = 1;
    assert!(matched(&class, &wrong, digest(STATICS_BYTES)).is_none());
    let mut wrong = *method;
    wrong.code = Some(&[177]);
    assert!(matched(&class, &wrong, digest(STATICS_BYTES)).is_none());
    let mut wrong = *method;
    wrong.descriptor = "(Ljava/lang/Runnable;)V";
    assert!(matched(&class, &wrong, digest(STATICS_BYTES)).is_none());
    assert!(!candidate("application/Statics", "releaseFence", "()V"));
    assert!(!candidate(
        VM,
        "findUnsafe",
        "(Ljava/lang/Class;)Ljava/lang/Object;"
    ));
}
#[test]
fn modeled_body_identity_binds_contract_and_effect_while_original_recipe_remains_distinct() {
    let original = digest(STATICS_BYTES);
    let modeled = body_hash(original, &[MemoryEffect::ReleaseFence as u8]);
    assert_ne!(original, modeled);
    assert_ne!(
        modeled,
        body_hash(original, &[MemoryEffect::HandleBootstrap as u8])
    );
    assert_eq!(
        modeled,
        body_hash(original, &[MemoryEffect::ReleaseFence as u8])
    );
}
