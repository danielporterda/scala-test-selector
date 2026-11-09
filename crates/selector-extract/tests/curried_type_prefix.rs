//! An unchanged real PR7743 compiler document and native syntax row prove the
//! type-only prefix of a curried call is not a second executable invocation.
use selector_extract::{ExtractOptions, import_capture};
use selector_facts::FactSnapshot;
use selector_types::*;
use sha2::{Digest, Sha256};
use std::path::{Path, PathBuf};

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/curried-type-prefix")
}
fn imported(workers: usize) -> FactSnapshot {
    import_capture(
        &fixture().join("documents.jsonl"),
        Some(&fixture().join("syntax.jsonl")),
        &ExtractOptions {
            workers,
            ..Default::default()
        },
    )
    .unwrap()
}

#[test]
fn actual_captured_curried_calls_execute_once_and_keep_their_callbacks_deferred() {
    let facts = imported(1);
    let manifest: serde_json::Value =
        serde_json::from_slice(&std::fs::read(fixture().join("manifest.json")).unwrap()).unwrap();
    for file in manifest["files"].as_array().unwrap() {
        let bytes = std::fs::read(fixture().join(file["path"].as_str().unwrap())).unwrap();
        assert_eq!(bytes.len() as u64, file["bytes"].as_u64().unwrap());
        assert_eq!(
            ContentHash(Sha256::digest(bytes).into()).to_string(),
            file["sha256"].as_str().unwrap()
        );
    }
    let mut callbacks = Vec::new();
    for expected in manifest["expected_calls"].as_array().unwrap() {
        let span = |key: &str| Span {
            start: expected[key][0].as_u64().unwrap() as u32,
            end: expected[key][1].as_u64().unwrap() as u32,
        };
        let whole = span("complete_apply");
        let calls: Vec<_> = facts
            .operations
            .iter()
            .filter(|op| {
                matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
                    && op.span == whole
                    && facts.symbol_name(op.target) == expected["callee"].as_str().unwrap()
            })
            .collect();
        assert_eq!(calls.len(), 1, "one complete invocation at {whole:?}");
        let call = calls[0];
        assert!(
            !facts.operations.iter().any(|op| {
                op.body == call.body && op.opcode == Opcode::Unknown && op.span == span("prefix")
            }),
            "type arguments do not introduce an executable token-only frontier"
        );
        assert!(
            !facts.operations.iter().any(|op| {
                matches!(op.opcode, Opcode::Call | Opcode::VirtualCall)
                    && facts.symbol_name(op.target) == expected["callee"].as_str().unwrap()
                    && op.span == span("first_apply")
            }),
            "coalesced first-clause syntax is not a second invocation"
        );
        let args = &facts.operands[call.arguments.range()];
        assert_eq!(
            args.len(),
            5,
            "table, callback and three actual implicit providers retained"
        );
        let body = facts.bodies[call.body.index()];
        let binding = facts.operations[body.operations.range()]
            .iter()
            .find(|op| op.opcode == Opcode::BindCallback && op.dest == args[1])
            .expect("original explicit callback actual");
        let callback = facts
            .bodies
            .iter()
            .find(|body| body.symbol == binding.target)
            .unwrap();
        assert_ne!(callback.flags & BODY_DEFERRED, 0);
        assert_ne!(binding.target, body.symbol);
        assert!(
            !facts.operations[body.operations.range()].iter().any(|op| {
                !op.target.is_none()
                    && facts
                        .symbol_name(op.target)
                        .starts_with("org/lfdecentralizedtrust/splice/config/Thresholds.")
            }),
            "assertion function effects remain in the deferred callback"
        );
        assert!(
            facts.operations[callback.operations.range()]
                .iter()
                .any(|op| {
                    !op.target.is_none()
                        && facts
                            .symbol_name(op.target)
                            .starts_with("org/lfdecentralizedtrust/splice/config/Thresholds.")
                })
        );
        callbacks.push(binding.target);
    }
    callbacks.sort_unstable();
    callbacks.dedup();
    assert_eq!(callbacks.len(), 4);
    assert!(!facts.issues.iter().any(|issue| {
        facts.text(issue.detail)
            == "compiler type-only function prefix has no unique same-body complete application"
    }));
    assert!(
        facts.issues.iter().any(|issue| {
            facts.text(issue.detail)
                == "compiler-selected method has no authoritative source argument signature"
        }),
        "absent external argument-signature authority is not supplied by this join"
    );
    assert!(
        facts.issues.iter().any(|issue| {
            facts.text(issue.detail) == "unsupported_result_expression:Term.Tuple"
        }),
        "independent unsupported tuple recipe remains guarded"
    );
}

#[test]
fn genuine_curried_capture_is_deterministic_at_one_and_four_workers() {
    let one = imported(1);
    let four = imported(4);
    let directory = tempfile::tempdir().unwrap();
    let a = directory.path().join("one.bin");
    let b = directory.path().join("four.bin");
    selector_facts::codec::write(&a, &one).unwrap();
    selector_facts::codec::write(&b, &four).unwrap();
    assert_eq!(std::fs::read(a).unwrap(), std::fs::read(b).unwrap());
}
