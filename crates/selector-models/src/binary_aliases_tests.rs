use super::*;
const PROBE: &[u8] =
    include_bytes!("../../../fixtures/native-branch-alias/classes/aliascase/Probe.class");
fn class() -> ClassFile<'static> {
    parse_class(PROBE, Limits::default()).unwrap()
}
fn summary<'a>(class: &ClassFile<'a>, name: &str) -> MethodSummary<'a> {
    summarize_with_envelope(class, class.method(name, None).unwrap(), Limits::default())
}
fn alternatives<'a>(summary: &'a MethodSummary<'_>, id: BinaryValueId) -> Vec<Value<'a>> {
    match summary.values[id.0 as usize] {
        Value::Alternatives(range) => summary.arguments[range.range()]
            .iter()
            .map(|id| summary.values[id.0 as usize])
            .collect(),
        one => vec![one],
    }
}
#[test]
fn genuine_branch_getter_keeps_receiver_field_return_and_lazy_call_aliases() {
    let class = class();
    let out = summary(&class, "lazy");
    assert!(out.complete());
    let returned = out.returned.unwrap();
    let Value::Field { member, receiver } = out.values[returned.0 as usize] else {
        panic!("{:?}", out.values)
    };
    assert_eq!(member.name, "value");
    assert_eq!(out.values[receiver.0 as usize], Value::Receiver);
    let call = out
        .calls
        .iter()
        .find(|c| c.member.name == "initialize")
        .unwrap();
    assert_eq!(
        out.values[call.receiver.unwrap().0 as usize],
        Value::Receiver
    );
}
#[test]
fn genuine_return_branches_keep_both_field_or_formal_alternatives() {
    let class = class();
    let out = summary(&class, "choose");
    let values = alternatives(&out, out.returned.unwrap());
    let fields: Vec<_> = values
        .iter()
        .map(|v| match v {
            Value::Field { member, receiver } => {
                assert_eq!(out.values[receiver.0 as usize], Value::Receiver);
                member.name
            }
            _ => panic!("{v:?}"),
        })
        .collect();
    assert_eq!(fields, ["left", "right"]);
    for name in ["chooseArgs", "scalarPredicate"] {
        let out = summary(&class, name);
        assert_eq!(
            alternatives(&out, out.returned.unwrap()),
            [Value::Argument(1), Value::Argument(2)],
            "{name}"
        );
    }
}
#[test]
fn genuine_merged_receivers_and_store_value_preserve_every_possible_alias() {
    let class = class();
    let out = summary(&class, "mergedField");
    let Value::Field { receiver, .. } = out.values[out.returned.unwrap().0 as usize] else {
        panic!()
    };
    assert_eq!(
        alternatives(&out, receiver),
        [Value::Argument(1), Value::Argument(2)]
    );
    let out = summary(&class, "mergedCall");
    let call = out.calls.iter().find(|c| c.member.name == "lazy").unwrap();
    assert_eq!(
        alternatives(&out, call.receiver.unwrap()),
        [Value::Argument(1), Value::Argument(2)]
    );
    let out = summary(&class, "mergedStore");
    assert_eq!(out.field_writes.len(), 1);
    assert_eq!(
        alternatives(&out, out.field_writes[0].value),
        [Value::Argument(1), Value::Argument(2)]
    );
    assert_eq!(
        alternatives(&out, out.returned.unwrap()),
        [Value::Argument(1), Value::Argument(2)]
    );
}
#[test]
fn refinement_keeps_all_structural_effects_and_open_offsets_even_on_throwing_paths() {
    let class = class();
    for name in [
        "lazy",
        "choose",
        "mergedField",
        "mergedCall",
        "mergedStore",
        "throwing",
        "reflecting",
        "mixed",
    ] {
        let method = class.method(name, None).unwrap();
        let scan = decode(&class, method, Limits::default()).unwrap();
        let coarse = project_coarse(&class, method, &scan, Limits::default()).unwrap();
        let out = summary(&class, name);
        assert_eq!(
            out.calls
                .iter()
                .map(|c| (c.member, c.kind, c.offset, c.arguments.len))
                .collect::<Vec<_>>(),
            coarse
                .calls
                .iter()
                .map(|c| (c.member, c.kind, c.offset, c.arguments.len))
                .collect::<Vec<_>>(),
            "calls{name}"
        );
        assert_eq!(
            out.field_writes
                .iter()
                .map(|w| (w.member, w.offset, w.receiver.is_some()))
                .collect::<Vec<_>>(),
            coarse
                .field_writes
                .iter()
                .map(|w| (w.member, w.offset, w.receiver.is_some()))
                .collect::<Vec<_>>(),
            "writes{name}"
        );
        assert_eq!(out.unknown_offsets, coarse.unknown_offsets, "{name}");
        assert_eq!(out.unknown, coarse.unknown, "{name}");
    }
    let out = summary(&class, "throwing");
    assert!(out.calls.iter().any(|c| c.member.name == "initialize"));
    assert!(out.field_writes.iter().any(|w| w.member.name == "global"));
    let out = summary(&class, "reflecting");
    assert!(!out.complete());
    assert!(out.field_writes.iter().any(|w| w.member.name == "global"));
}
#[test]
fn unknown_array_path_loops_and_handlers_keep_original_top_return() {
    let class = class();
    for name in ["unknownBranch", "loop", "caught"] {
        let method = class.method(name, None).unwrap();
        let scan = decode(&class, method, Limits::default()).unwrap();
        let coarse = project_coarse(&class, method, &scan, Limits::default()).unwrap();
        let mut out = coarse.clone();
        refine(&class, method, &scan, Limits::default(), &mut out);
        assert_eq!(format!("{out:?}"), format!("{coarse:?}"), "{name} rollback");
        assert_eq!(
            out.values[out.returned.unwrap().0 as usize],
            Value::UnknownData
        );
    }
}

#[test]
fn actual_captured_url_lazy_getter_has_an_exact_receiver_and_returned_field() {
    let class = parse_class(
        include_bytes!("../../../fixtures/native-branch-alias/captured/UrlValidatorTest.class"),
        Limits::default(),
    )
    .unwrap();
    let method = class
        .method(
            "PatienceConfig",
            Some("()Lorg/scalatest/concurrent/AbstractPatienceConfiguration$PatienceConfig$;"),
        )
        .unwrap();
    let out = summarize_with_envelope(&class, method, Limits::default());
    let Value::Field { member, receiver } = out.values[out.returned.unwrap().0 as usize] else {
        panic!("{:?}", out.values)
    };
    assert_eq!(member.name, "PatienceConfig$module");
    assert_eq!(out.values[receiver.0 as usize], Value::Receiver);
    let call = out
        .calls
        .iter()
        .find(|c| c.member.name == "PatienceConfig$lzycompute$1")
        .unwrap();
    assert_eq!(
        out.values[call.receiver.unwrap().0 as usize],
        Value::Receiver
    );
}
#[test]
fn reference_literals_retain_top_and_opaque_call_return_is_not_dropped() {
    let class = class();
    let out = summary(&class, "literal");
    assert_eq!(
        out.values[out.returned.unwrap().0 as usize],
        Value::UnknownData,
        "String and Class ldc values have no exact runtime object model"
    );
    let out = summary(&class, "mixed");
    let values = alternatives(&out, out.returned.unwrap());
    assert_eq!(values.len(), 2);
    assert!(
        values
            .iter()
            .any(|v| matches!(v,Value::Field{member,..}if member.name=="left"))
    );
    assert!(
        values.iter().any(
            |v| matches!(v,Value::CallResult(i)if out.calls[*i as usize].member.name=="opaque")
        ),
        "the opaque branch cannot be replaced by the precise left-field alternative"
    );
}
