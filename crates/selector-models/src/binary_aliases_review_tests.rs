//! Independent adverse controls for the all-path alias refinement. These use a
//! genuine parsed class only as a constant-pool context; MethodInfo/Code rows
//! below are explicitly synthetic controls, not claimed compiler observations.
use super::*;

const CLASS: &[u8] =
    include_bytes!("../../../fixtures/native-lnt/variants/base/classes/lntcase/Probe.class");
const DESCRIPTOR: &str = "(Ljava/lang/Object;Ljava/lang/Object;Z)Ljava/lang/Object;";

fn method<'a>(code: &'a [u8], descriptor: &'a str, locals: u16) -> MethodInfo<'a> {
    MethodInfo {
        flags: 8,
        name: "syntheticReviewControl",
        descriptor,
        max_stack: 4,
        max_locals: locals,
        code: Some(code),
        exception_handlers: 0,
        exception_table: &[],
    }
}
fn coarse<'a>(descriptor: &'a str) -> MethodSummary<'a> {
    MethodSummary {
        descriptor,
        values: vec![Value::UnknownData],
        value_offsets: vec![0],
        calls: Vec::new(),
        arguments: Vec::new(),
        field_writes: Vec::new(),
        lambdas: Vec::new(),
        unknown_offsets: Vec::new(),
        returned: Some(BinaryValueId(0)),
        unknown: None,
        envelope: None,
    }
}
fn refined<'a>(method: &MethodInfo<'a>, limits: Limits) -> MethodSummary<'a> {
    let class = parse_class(CLASS, Limits::default()).unwrap();
    // Structural decoding uses the ordinary complete decoder, independently of
    // the smaller all-path evaluation budget under test.
    let scan = decode(&class, method, Limits::default()).unwrap();
    let mut summary = coarse(method.descriptor);
    refine(&class, method, &scan, limits, &mut summary);
    summary
}
fn assert_coarse(summary: &MethodSummary<'_>) {
    assert_eq!(
        format!("{summary:?}"),
        format!("{:?}", coarse(summary.descriptor)),
        "a failed refinement must not publish any partially narrowed row"
    );
}

#[test]
fn partial_success_then_step_budget_restores_the_entire_coarse_summary() {
    // if (third) return first; else return second. The first return completes
    // before evaluating the pending path exhausts the five-step budget.
    let code = [28, 153, 0, 5, 42, 176, 43, 176];
    let method = method(&code, DESCRIPTOR, 3);
    let complete = refined(&method, Limits::default());
    let returned = complete.returned.unwrap();
    let Value::Alternatives(range) = complete.values[returned.0 as usize] else {
        panic!("both genuine parameter alternatives must survive this synthetic CFG")
    };
    assert_eq!(range.len, 2);
    assert_coarse(&refined(
        &method,
        Limits {
            max_steps: 5,
            ..Limits::default()
        },
    ));
}

#[test]
fn path_budget_after_completed_returns_cannot_publish_a_partial_alias() {
    // Each conditional has the same target as its fallthrough. Both paths are
    // valid; eight diamonds exceed the all-path cap after some returns finish.
    let mut code = Vec::new();
    for _ in 0..8 {
        code.extend_from_slice(&[28, 153, 0, 3]);
    }
    code.extend_from_slice(&[42, 176]);
    assert_coarse(&refined(&method(&code, DESCRIPTOR, 3), Limits::default()));
}

#[test]
fn late_unsupported_stack_shape_does_not_keep_an_earlier_precise_return() {
    // One sibling uses valid category-2 DUP2, which this refinement does not
    // support; the other returns a precise parameter. Preflight or path failure
    // must reject the whole refinement rather than keep the precise sibling.
    let code = [28, 153, 0, 5, 42, 176, 9, 92, 88, 88, 43, 176];
    assert_coarse(&refined(&method(&code, DESCRIPTOR, 3), Limits::default()));
}

#[test]
fn handlers_and_late_backedges_keep_the_unmodified_coarse_value_contract() {
    let handler_code = [42, 176, 78, 43, 176];
    let table = [0, 0, 0, 1, 0, 2, 0, 0];
    let mut guarded = method(&handler_code, DESCRIPTOR, 4);
    guarded.exception_handlers = 1;
    guarded.exception_table = &table;
    assert_coarse(&refined(&guarded, Limits::default()));
    // First sibling returns; the other reaches a backward GOTO to entry.
    let backedge = [28, 153, 0, 5, 42, 176, 167, 255, 250];
    assert_coarse(&refined(
        &method(&backedge, DESCRIPTOR, 3),
        Limits::default(),
    ));
}

#[test]
fn overwriting_the_second_slot_invalidates_a_wide_local_without_narrowing() {
    let valid_wide = [9, 66, 33, 88, 42, 176];
    let valid = refined(&method(&valid_wide, DESCRIPTOR, 5), Limits::default());
    assert!(matches!(
        valid.values[valid.returned.unwrap().0 as usize],
        Value::Argument(0)
    ));
    // Explicit malformed/type-invalid mutation: ISTORE 4 overwrites the second
    // half of long local 3. A structural decoder alone is not a JVM verifier.
    let overwritten = [9, 66, 3, 54, 4, 33, 88, 42, 176];
    assert_coarse(&refined(
        &method(&overwritten, DESCRIPTOR, 5),
        Limits::default(),
    ));
    // A valid existing category-1 local remains supported for both IINC forms.
    for code in [
        vec![132, 2, 1, 42, 176],
        vec![196, 132, 0, 2, 0, 1, 42, 176],
    ] {
        let value = refined(&method(&code, DESCRIPTOR, 3), Limits::default());
        assert!(matches!(
            value.values[value.returned.unwrap().0 as usize],
            Value::Argument(0)
        ));
    }
    // IINC is another single-slot write, including its wide form. It must not
    // leave the first half of a formerly wide local as a valid alias.
    for overwritten in [
        vec![9, 66, 132, 4, 1, 33, 88, 42, 176],
        vec![9, 66, 196, 132, 0, 4, 0, 1, 33, 88, 42, 176],
    ] {
        assert_coarse(&refined(
            &method(&overwritten, DESCRIPTOR, 5),
            Limits::default(),
        ));
    }
}

#[test]
fn too_many_return_alternatives_publish_top_instead_of_an_arbitrary_subset() {
    let mut descriptor = String::from("(");
    for _ in 0..66 {
        descriptor.push_str("Ljava/lang/Object;");
    }
    descriptor.push_str("Z)Ljava/lang/Object;");
    let mut code = Vec::new();
    for argument in 0..65 {
        code.extend_from_slice(&[21, 66, 153, 0, 6, 25, argument, 176]);
    }
    code.extend_from_slice(&[25, 65, 176]);
    let out = refined(&method(&code, &descriptor, 67), Limits::default());
    assert!(out.values.len() > 1, "this analysis finished and committed");
    assert!(matches!(
        out.values[out.returned.unwrap().0 as usize],
        Value::UnknownData
    ));
}
