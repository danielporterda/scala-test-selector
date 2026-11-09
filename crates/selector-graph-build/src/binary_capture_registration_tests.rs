//! An isolated demand projection of the frozen compiler's real WordSpec `.in`
//! occurrence. The provider and method body are the actual portable class bytes;
//! this test does not fabricate compiler declarations or claim suite execution.
use super::*;
use selector_facts::{BodyRecord, FactBuilder, FileRecord, OperationRecord};

const METHOD: &str = "org/scalatest/wordspec/AnyWordSpecLike#WordSpecStringWrapper#in().";
const OWNER: &str = "org/scalatest/wordspec/AnyWordSpecLike$WordSpecStringWrapper";
const DESCRIPTOR: &str = "(Lscala/Function0;Lorg/scalactic/source/Position;)V";
const CONTEXT: &str = "project:curried-synthetics/configuration:test";
const ARCHIVE: &str = "08050f3d05c72575cac29a1483185b443d5f9f34c1fcf80c683083330385ef93";

fn projection() -> (FactSnapshot, SymbolId) {
    let document: Value = serde_json::from_str(
        include_str!("../../../fixtures/curried-synthetics/documents.jsonl")
            .lines()
            .find(|line| line.contains(METHOD))
            .unwrap(),
    )
    .unwrap();
    assert!(
        document["source_contexts"]
            .as_array()
            .unwrap()
            .iter()
            .any(|c| c == CONTEXT)
    );
    let occurrence = document["document"]["occurrences"]
        .as_array()
        .unwrap()
        .iter()
        .find(|o| o["symbol"] == METHOD && o["role"] == 1)
        .unwrap();
    let source = document["source_text"].as_str().unwrap();
    let range = &occurrence["range"];
    let line = range["start_line"].as_u64().unwrap() as usize;
    let start = source
        .lines()
        .take(line)
        .map(|s| s.len() + 1)
        .sum::<usize>()
        + range["start_character"].as_u64().unwrap() as usize;
    let span = Span {
        start: start as u32,
        end: start as u32 + 2,
    };
    assert_eq!(&source[span.start as usize..span.end as usize], "in");
    let mut builder = FactBuilder::new();
    builder.facts.revision = builder
        .intern(document["revision"].as_str().unwrap())
        .unwrap();
    let context = builder.intern(CONTEXT).unwrap();
    let path = builder.intern(document["path"].as_str().unwrap()).unwrap();
    let source_id = builder.intern(source).unwrap();
    builder.facts.files.push(FileRecord {
        path,
        source: source_id,
        context,
        revision: builder.facts.revision,
        source_hash: ContentHash::from_hex(document["source_sha256"].as_str().unwrap()).unwrap(),
        flags: SOURCE_VERIFIED,
    });
    let caller = builder
        .ensure_symbol("curriedcase/WordSuite#", FileId(0))
        .unwrap();
    builder.facts.symbols[caller.index()].file = FileId(0);
    builder.facts.symbols[caller.index()].kind = 13;
    builder.facts.symbols[caller.index()].flags = SYMBOL_DEFINED;
    let owner = builder
        .ensure_symbol(
            "org/scalatest/wordspec/AnyWordSpecLike#WordSpecStringWrapper#",
            FileId(0),
        )
        .unwrap();
    let target = builder.ensure_symbol(METHOD, FileId(0)).unwrap();
    builder.facts.symbols[target.index()].owner = owner;
    builder.facts.operands.extend([ValueId(2), ValueId(3)]);
    builder.facts.operations.push(OperationRecord {
        body: BodyId(0),
        opcode: Opcode::RegisterTest,
        target,
        dest: ValueId::NONE,
        a: ValueId(1),
        b: ValueId::NONE,
        arguments: IdRange { start: 0, len: 2 },
        span,
        flags: encode_callback_argument(0).unwrap(),
    });
    builder.facts.bodies.push(BodyRecord {
        symbol: caller,
        file: FileId(0),
        span,
        name_span: span,
        operations: IdRange { start: 0, len: 1 },
        parameters: IdRange::default(),
        body_hash: ContentHash([1; 32]),
        flags: 0,
    });
    (builder.finish().unwrap(), target)
}

fn capture(directory: &Path, facts: &FactSnapshot, opaque_prefix: bool) -> PathBuf {
    let archive = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../fixtures/scalatest-execution/scalatest-wordspec_2.13-3.2.19.jar")
        .canonicalize()
        .unwrap();
    let mut objects = vec![
        json!({"path":archive,"kind":"file","sha256":ARCHIVE,"bytes":std::fs::metadata(&archive).unwrap().len()}),
    ];
    let mut entries = vec![json!({"index":0,"path":archive,"sha256":ARCHIVE})];
    if opaque_prefix {
        let missing = directory.join("unavailable-earlier.jar");
        objects.insert(0, json!({"path":missing,"kind":"file","sha256":ContentHash([9;32]).to_string(),"bytes":1}));
        entries[0]["index"] = json!(1);
        entries.insert(
            0,
            json!({"index":0,"path":missing,"sha256":ContentHash([9;32]).to_string()}),
        );
    }
    let path = directory.join("contexts.json");
    std::fs::write(
        &path,
        json!({"schema_version":"sbt-compiler-context/v1",
        "revision":facts.text(facts.revision),"source_root":"/frozen/compiler/capture","errors":[],
        "contexts":[{"context_id":CONTEXT,"full_classpath":entries}],"input_objects":objects})
        .to_string(),
    )
    .unwrap();
    path
}

#[test]
fn frozen_wordspec_registration_demands_and_admits_its_actual_native_body() {
    let directory = tempfile::tempdir().unwrap();
    let (mut facts, target) = projection();
    let original = facts.operations[0];
    let capture = capture(directory.path(), &facts, false);
    let serial = generate(
        &facts,
        &capture,
        directory.path(),
        &CaptureOptions {
            workers: 1,
            ..Default::default()
        },
    )
    .unwrap();
    let parallel = generate(
        &facts,
        &capture,
        directory.path(),
        &CaptureOptions {
            workers: 4,
            ..Default::default()
        },
    )
    .unwrap();
    assert_eq!(serial.manifest, parallel.manifest);
    assert_eq!(serial.receipt.requested, 1);
    assert_eq!(serial.receipt.bound_methods, 1);
    let rows = serial.manifest["methods"].as_array().unwrap();
    assert_eq!(rows[0]["compiler_symbol"], METHOD);
    assert_eq!(rows[0]["jvm_owner"], OWNER);
    assert_eq!(rows[0]["jvm_name"], "in");
    assert_eq!(rows[0]["descriptor"], DESCRIPTOR);
    let map = directory.path().join("binary.json");
    std::fs::write(&map, serial.manifest.to_string()).unwrap();
    let mut admitted = crate::binary_inputs::load_binary_manifest(&map, &facts).unwrap();
    crate::binary_inputs::augment_binary_facts_with_limits(
        &mut facts,
        &mut admitted,
        crate::binary_inputs::NativeAdmissionLimits {
            classes_per_context: 32,
            bytes_per_context: 4 * 1024 * 1024,
            methods: 32,
        },
    )
    .unwrap();
    let operation_key = |op: OperationRecord| {
        (
            op.body,
            op.opcode,
            op.target,
            op.dest,
            op.a,
            op.b,
            op.arguments,
            op.span,
            op.flags,
        )
    };
    assert_eq!(operation_key(facts.operations[0]), operation_key(original));
    let body = facts.bodies.iter().find(|b| b.symbol == target).unwrap();
    assert_ne!(body.flags & BODY_BINARY_RECIPE, 0);
    assert_ne!(body.operations.len, 0);
    let protocol: Value = serde_json::from_str(include_str!(
        "../../../fixtures/scalatest-execution/methods.json"
    ))
    .unwrap();
    let proof = protocol["methods"]
        .as_array()
        .unwrap()
        .iter()
        .find(|m| m["owner"] == OWNER && m["name"] == "in" && m["descriptor"] == DESCRIPTOR)
        .unwrap();
    assert_eq!(
        facts.files[body.file.index()].source_hash.to_string(),
        proof["class_sha256"].as_str().unwrap()
    );
}

#[test]
fn registration_demand_retains_opaque_provider_and_source_body_precedence() {
    let directory = tempfile::tempdir().unwrap();
    let (mut facts, target) = projection();
    let capture = capture(directory.path(), &facts, true);
    let generated = generate(
        &facts,
        &capture,
        directory.path(),
        &CaptureOptions::default(),
    )
    .unwrap();
    assert_eq!(generated.receipt.requested, 1);
    assert_eq!(generated.receipt.bound_methods, 0);
    assert_eq!(
        generated
            .receipt
            .unresolved
            .get("unavailable_preceding_classpath_input"),
        Some(&1)
    );
    // A captured source implementation keeps its own normal execution recipe.
    facts.bodies[0].symbol = target;
    facts.symbols[target.index()].file = FileId(0);
    let generated = generate(
        &facts,
        &capture,
        directory.path(),
        &CaptureOptions::default(),
    )
    .unwrap();
    assert_eq!(generated.receipt.requested, 0);
    assert_eq!(generated.receipt.skipped_source_recipes, 1);
    assert_eq!(generated.receipt.bound_methods, 0);
}

#[test]
fn registration_demand_does_not_override_an_incompatible_compiler_descriptor() {
    let directory = tempfile::tempdir().unwrap();
    let (mut facts, target) = projection();
    let signature = r#"{"method_signature":{"parameter_lists":[],"return_type":{"type_ref":{"symbol":"scala/Int#"}}}}"#;
    let id = StrId(facts.strings.entries.len() as u32);
    facts.strings.entries.push(selector_facts::TextRange {
        start: facts.strings.bytes.len() as u64,
        len: signature.len() as u32,
    });
    facts.strings.bytes.extend_from_slice(signature.as_bytes());
    facts.symbols[target.index()].signature = id;
    let capture = capture(directory.path(), &facts, false);
    let generated = generate(
        &facts,
        &capture,
        directory.path(),
        &CaptureOptions::default(),
    )
    .unwrap();
    assert_eq!(generated.receipt.requested, 1);
    assert_eq!(generated.receipt.bound_methods, 0);
    assert_eq!(generated.receipt.unresolved.values().sum::<usize>(), 1);
}
