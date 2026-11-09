//! Structural compiler-authority controls over genuine pinned module bytes.
use super::*;

fn fixture() -> FactSnapshot {
    let mut b = FactBuilder::new();
    let context = b.intern("compile").unwrap();
    let path = b.intern("Caller.scala").unwrap();
    let source = b.intern("Effects").unwrap();
    b.facts.files.push(FileRecord {
        path,
        source,
        revision: StrId::NONE,
        context,
        source_hash: ContentHash([1; 32]),
        flags: SOURCE_VERIFIED | SYNTAX_VERIFIED,
    });
    let package = b.ensure_symbol("selectedexternal/", FileId::NONE).unwrap();
    let module = b
        .ensure_symbol("selectedexternal/Effects.", FileId::NONE)
        .unwrap();
    let method = b
        .ensure_symbol("selectedexternal/Effects.note().", FileId::NONE)
        .unwrap();
    let root = b
        .ensure_symbol("selectedexternal/Caller#read().", FileId(0))
        .unwrap();
    for id in [package, module, method, root] {
        b.facts.symbols[id.index()].context = context;
    }
    b.facts.symbols[module.index()].owner = package;
    b.facts.symbols[method.index()].owner = module;
    b.facts.symbols[method.index()].kind = 3;
    b.facts.symbols[method.index()].signature = b
        .intern(r#"{"method_signature":{"return_type":{"type_ref":{"symbol":"scala/Unit#"}}}}"#)
        .unwrap();
    b.facts.operations.push(OperationRecord {
        body: BodyId(0),
        opcode: Opcode::LoadField,
        target: module,
        dest: ValueId(2),
        a: ValueId(0),
        b: ValueId::NONE,
        arguments: IdRange::default(),
        span: Span { start: 0, end: 7 },
        flags: 0,
    });
    b.facts.bodies.push(BodyRecord {
        symbol: root,
        file: FileId(0),
        span: Span { start: 0, end: 7 },
        name_span: Span::default(),
        operations: IdRange { start: 0, len: 1 },
        parameters: IdRange::default(),
        body_hash: ContentHash([2; 32]),
        flags: 0,
    });
    b.finish().unwrap()
}

fn admitted(facts: &mut FactSnapshot, prefix: bool) -> (OwnedBinaryInputs, Registry) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../fixtures/selected-external-apply/library.jar");
    let hash = ContentHash(Sha256::digest(std::fs::read(&path).unwrap()).into());
    let mut entries = Vec::new();
    if prefix {
        entries.push(serde_json::json!({"path":"unavailable.jar","sha256":ContentHash([3;32]).to_string(),"kind":"unavailable"}));
    }
    entries.push(serde_json::json!({"path":path,"sha256":hash.to_string(),"kind":"jar"}));
    let directory = tempfile::tempdir().unwrap();
    let manifest = directory.path().join("binary.json");
    std::fs::write(&manifest,serde_json::json!({"version":1,"facts_identity":facts.identity.to_string(),"contexts":[{"id":"compile","entries":entries}],"methods":[]}).to_string()).unwrap();
    let mut inputs = crate::binary_inputs::load_binary_manifest(&manifest, facts).unwrap();
    inputs.contexts[0].admission.derived = true;
    inputs.contexts[0].admission.method_allowance = 100;
    let empty = append_text(facts, "").unwrap();
    let registry = Registry {
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
    (inputs, registry)
}

#[test]
fn witnessed_global_read_keeps_real_initialization_static_slot_and_source_value_identity() {
    let mut facts = fixture();
    let candidates = super::super::candidates(&facts);
    assert_eq!(candidates.len(), 1);
    assert!(candidates[0].global);
    let original = facts.operations[0];
    let (mut inputs, mut registry) = admitted(&mut facts, false);
    let mut pending = VecDeque::new();
    let bindings = declare_globals(
        &mut facts,
        &mut inputs,
        &mut registry,
        &candidates,
        &mut pending,
    )
    .unwrap();
    let &(adapter, _) = bindings.get(&original.target).unwrap();
    assert!(facts.symbol_name(adapter).starts_with("@jvm-module-read/"));
    assert!(
        registry
            .methods
            .keys()
            .any(|key| key.owner == "selectedexternal/Effects$" && key.name == "<clinit>")
    );
    let body = facts
        .bodies
        .iter()
        .find(|body| body.symbol == adapter)
        .unwrap();
    let ops = &facts.operations[body.operations.range()];
    assert_eq!(
        ops.iter().map(|op| op.opcode).collect::<Vec<_>>(),
        [Opcode::Initialize, Opcode::LoadField, Opcode::Return]
    );
    assert_eq!(ops[1].flags, OP_STATIC_FIELD);
    assert!(facts.symbol_name(ops[1].target).contains("MODULE$"));
    let phase = ops[0].target;
    let phase = facts
        .bodies
        .iter()
        .find(|body| body.symbol == phase)
        .unwrap();
    assert!(
        facts.operations[phase.operations.range()]
            .iter()
            .any(|op| matches!(op.opcode, Opcode::Call | Opcode::Initialize)
                && !op.target.is_none()
                && facts.symbol_name(op.target).contains("<clinit>"))
    );
    super::super::augment(&mut facts, &registry, &inputs, &candidates, &bindings).unwrap();
    let source = facts.operations[0];
    assert_eq!(source.opcode, Opcode::Call);
    assert_eq!(source.target, adapter);
    assert_eq!(
        (source.dest, source.a, source.span),
        (original.dest, original.a, original.span)
    );
    assert_eq!(facts.symbols[original.target.index()].kind, 0);
}

#[test]
fn missing_compiler_witness_opaque_provider_and_method_frontier_never_become_empty_globals() {
    let mut missing = fixture();
    let method = missing
        .find_symbol("selectedexternal/Effects.note().")
        .unwrap();
    missing.symbols[method.index()].signature = StrId::NONE;
    assert!(super::super::candidates(&missing).is_empty());
    for prefix in [false, true] {
        let mut facts = fixture();
        let candidates = super::super::candidates(&facts);
        let (mut inputs, mut registry) = admitted(&mut facts, prefix);
        if !prefix {
            inputs.contexts[0].admission.method_allowance = 0;
        }
        let bindings = declare_globals(
            &mut facts,
            &mut inputs,
            &mut registry,
            &candidates,
            &mut VecDeque::new(),
        )
        .unwrap();
        assert!(bindings.is_empty());
        assert_eq!(facts.operations[0].opcode, Opcode::LoadField);
        assert!(
            facts
                .issues
                .iter()
                .filter(|issue| issue.kind == IssueKind::UnknownExecution)
                .all(|issue| !issue.symbol.is_none()),
            "optional module budget guards stay target-bound"
        );
        assert!(!facts.bodies.iter().any(|body| {
            facts
                .symbol_name(body.symbol)
                .starts_with("@jvm-module-read/")
        }));
    }
}

#[test]
fn malformed_module_fields_and_initializer_metadata_cannot_authorize_a_global_read() {
    let facts = fixture();
    let candidate = super::super::candidates(&facts).pop().unwrap();
    for case in 0..10 {
        let mut fields = vec![("MODULE$", candidate.descriptor.as_str(), 0x0019)];
        let mut methods = vec![("<clinit>", "()V", 0x0008, true)];
        let mut flags = 0x0031;
        match case {
            0 => fields[0].2 = 0x0009,
            1 => fields[0].2 = 0x0011,
            2 => fields[0].2 = 0x001a,
            3 => fields[0].1 = "Ljava/lang/Object;",
            4 => fields.push(fields[0]),
            5 => methods.clear(),
            6 => methods[0].2 = 0,
            7 => methods[0].3 = false,
            8 => methods.push(methods[0]),
            9 => flags |= 0x0400,
            _ => unreachable!(),
        }
        assert!(
            !header_rows(
                &candidate.module_owner,
                flags,
                fields.into_iter(),
                methods.into_iter(),
                &candidate
            ),
            "case{case}"
        );
    }
}

fn header_fixture(opcode: Opcode) -> FactSnapshot {
    let mut facts = fixture();
    let module = facts.operations[0].target;
    facts.symbols[module.index()].kind = 10;
    let method = facts
        .find_symbol("selectedexternal/Effects.note().")
        .unwrap();
    facts.symbols[method.index()].signature = StrId::NONE;
    facts.operations[0].opcode = opcode;
    facts
}

#[test]
fn compiler_object_header_authorizes_only_the_global_reference_encoding_before_native_facets() {
    for opcode in [Opcode::LoadField, Opcode::Allocate] {
        // Structural consumer control: the independent metadata admission tests
        // establish this kind10/header row from genuine compiler ScalaSig bytes.
        let mut facts = header_fixture(opcode);
        let original = facts.operations[0];
        let candidates = super::super::candidates(&facts);
        assert_eq!(candidates.len(), 1);
        let (mut inputs, mut registry) = admitted(&mut facts, false);
        let bindings = declare_globals(
            &mut facts,
            &mut inputs,
            &mut registry,
            &candidates,
            &mut VecDeque::new(),
        )
        .unwrap();
        let &(adapter, _) = bindings.get(&original.target).unwrap();
        let body = facts.bodies.iter().find(|b| b.symbol == adapter).unwrap();
        let ops = &facts.operations[body.operations.range()];
        assert_eq!(ops[0].opcode, Opcode::Initialize);
        assert_eq!(
            (ops[1].opcode, ops[1].flags),
            (Opcode::LoadField, OP_STATIC_FIELD)
        );
        // The raw compiler proof is kept in stage-local candidates: an ordinary
        // native class facet does not gain new source reference authority.
        facts.symbols[original.target.index()].kind = 13;
        facts.symbols[original.target.index()].properties = 4;
        let facet = facts.symbols[original.target.index()];
        assert_eq!(
            super::super::augment(&mut facts, &registry, &inputs, &candidates, &bindings).unwrap(),
            1
        );
        let source = facts.operations[0];
        assert_eq!((source.opcode, source.target), (Opcode::Call, adapter));
        assert_eq!(
            (source.a, source.dest, source.span, source.arguments),
            (original.a, original.dest, original.span, original.arguments)
        );
        assert_eq!(
            format!("{:?}", facts.symbols[original.target.index()]),
            format!("{facet:?}")
        );
        assert_eq!(facts.bodies[0].operations.len, 1);
    }
}

#[test]
fn incomplete_foreign_native_and_nonreference_rows_cannot_borrow_object_header_authority() {
    for case in 0..22 {
        let mut facts = header_fixture(Opcode::Allocate);
        let module = facts.operations[0].target;
        let owner = facts.symbols[module.index()].owner;
        match case {
            0 => facts.symbols[module.index()].kind = 0,
            1 => facts.symbols[module.index()].kind = 13,
            2 => facts.symbols[module.index()].kind = 21,
            3 => facts.symbols[module.index()].flags = SYMBOL_NATIVE_BINARY,
            4 => facts.symbols[module.index()].flags = SYMBOL_DEFINED,
            5 => facts.symbols[module.index()].properties = 4,
            6 => facts.symbols[module.index()].file = FileId(0),
            7 => {
                facts.symbols[module.index()].signature =
                    append_text(&mut facts, r#"{"class_signature":{}}"#).unwrap()
            }
            8 => facts.symbols[module.index()].context = StrId::NONE,
            9 => facts.symbols[owner.index()].context = StrId::NONE,
            10 => facts.symbols[module.index()].owner = SymbolId::NONE,
            11 => {
                facts.symbols[owner.index()].name =
                    append_text(&mut facts, "selectedexternal/Outer#").unwrap()
            }
            12 => facts.operations[0].arguments.len = 1,
            13 => facts.operations[0].b = ValueId(1),
            14 => facts.operations[0].flags = OP_SYNTHETIC_PARAMETER_APPLY,
            15 => facts.operations[0].a = ValueId::NONE,
            16 => facts.operations[0].dest = ValueId::NONE,
            17 => facts.operations[0].opcode = Opcode::Initialize,
            18 => facts.files[0].flags = SOURCE_VERIFIED,
            19 => facts.bodies[0].flags = BODY_BINARY_RECIPE,
            20 | 21 => facts.issues.push(IssueRecord {
                kind: IssueKind::ContextConflict,
                file: FileId::NONE,
                symbol: if case == 20 { module } else { owner },
                detail: StrId::NONE,
            }),
            _ => unreachable!(),
        }
        assert!(super::super::candidates(&facts).is_empty(), "case {case}");
    }
}

#[test]
fn object_header_does_not_replace_missing_native_provider_or_initialization_authority() {
    let mut facts = header_fixture(Opcode::Allocate);
    let original = facts.operations[0];
    let candidates = super::super::candidates(&facts);
    let (mut inputs, mut registry) = admitted(&mut facts, true);
    let bindings = declare_globals(
        &mut facts,
        &mut inputs,
        &mut registry,
        &candidates,
        &mut VecDeque::new(),
    )
    .unwrap();
    assert!(bindings.is_empty());
    assert_eq!(
        super::super::augment(&mut facts, &registry, &inputs, &candidates, &bindings).unwrap(),
        0
    );
    assert_eq!(
        format!("{:?}", facts.operations[0]),
        format!("{original:?}")
    );
}
