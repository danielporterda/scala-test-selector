//! Native compiler expansion and hash-admitted constructor controls. These do
//! not grant effects-complete status to arbitrary macros or framework methods.
use selector_extract::{ExtractOptions, import_capture};
use selector_facts::FactSnapshot;
use selector_graph_build::binary_inputs::{augment_binary_facts, load_binary_manifest};
use selector_types::*;
use serde_json::{Value, json};
use std::path::PathBuf;

const MACRO: &str = "org/scalactic/source/Position.here().";
const GUARD: &str = "compiler macro expansion runtime effects require explicit model";
fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/position-macro")
}
fn captured() -> FactSnapshot {
    import_capture(
        &fixture().join("documents.jsonl"),
        Some(&fixture().join("syntax.jsonl")),
        &ExtractOptions {
            workers: 2,
            ..Default::default()
        },
    )
    .unwrap()
}
fn enrich(facts: &mut FactSnapshot, unavailable: bool) {
    let fixture = fixture();
    let witness: Value =
        serde_json::from_slice(&std::fs::read(fixture.join("manifest.json")).unwrap()).unwrap();
    let mut entries = Vec::new();
    if unavailable {
        entries.push(json!({"path":"missing.jar","kind":"unavailable"}));
    }
    for jar in witness["jars"].as_array().unwrap().iter().filter(|jar| {
        let p = jar["path"].as_str().unwrap();
        p.contains("/scalactic_") || p.contains("/scala-library/")
    }) {
        entries.push(json!({"path":jar["path"],"sha256":jar["sha256"],"kind":"jar"}));
    }
    let context = facts.text(facts.files[0].context);
    let manifest = json!({"version":1,"revision":facts.text(facts.revision),"java_feature":21,
        "contexts":[{"id":context,"entries":entries}],"methods":[]});
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("binary.json");
    std::fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    let mut inputs = load_binary_manifest(&path, facts).unwrap();
    augment_binary_facts(facts, &mut inputs).unwrap();
}
fn macro_ids(facts: &FactSnapshot) -> Vec<usize> {
    facts
        .operations
        .iter()
        .enumerate()
        .filter(|(_, op)| {
            op.opcode == Opcode::Unknown
                && op.flags & OP_MACRO_EXPANSION != 0
                && facts.symbol_name(op.target) == MACRO
        })
        .map(|(i, _)| i)
        .collect()
}

#[test]
fn genuine_position_macros_remain_unknown_until_ordered_binary_authority_is_admitted() {
    let mut facts = captured();
    let macros = macro_ids(&facts);
    assert_eq!(macros.len(), 5);
    let bodies = facts.bodies.clone();
    let operations = facts.operations.len();
    let metadata: Vec<_> = macros.iter().map(|&i| facts.operations[i].a).collect();
    assert!(
        macros
            .iter()
            .all(|&i| facts.operations[i].flags & OP_MACRO_DIRECT_TREE != 0)
    );
    enrich(&mut facts, false);
    for (&id, &value) in macros.iter().zip(&metadata) {
        let op = facts.operations[id];
        assert_eq!(op.opcode, Opcode::Allocate);
        assert_eq!(op.flags, 0);
        assert_eq!(op.arguments.len, 3);
        assert_eq!(facts.operands[op.arguments.range()], [value; 3]);
        assert_eq!(facts.operations[id - 1].opcode, Opcode::Constant);
        assert!(facts.operations[id - 1].target.is_none());
        assert_eq!(facts.operations[id - 1].flags, 0);
        let ctor = facts
            .bodies
            .iter()
            .find(|body| body.symbol == op.target)
            .expect("native constructor recipe");
        let ops = &facts.operations[ctor.operations.range()];
        assert_eq!(
            ops.iter()
                .filter(|o| o.opcode == Opcode::Parameter && o.flags == 0)
                .count(),
            3
        );
        assert_eq!(
            ops.iter()
                .filter(|o| o.opcode == Opcode::StoreField)
                .count(),
            3
        );
    }
    // New native bodies append after the source table; every source op/range
    // and all pre-existing operation IDs retain their original membership.
    for (old, new) in bodies.iter().zip(&facts.bodies) {
        assert_eq!(old.operations, new.operations);
    }
    assert!(facts.operations.len() >= operations);
    for body in &facts.bodies[..bodies.len()] {
        let unresolved = facts.operations[body.operations.range()]
            .iter()
            .any(|o| o.flags & OP_MACRO_EXPANSION != 0);
        if !unresolved
            && macros
                .iter()
                .any(|&id| bodies[facts.operations[id].body.index()].symbol == body.symbol)
        {
            assert!(facts.issues.iter().all(|issue| issue.file != body.file
                || issue.symbol != body.symbol
                || facts.text(issue.detail) != GUARD));
        }
    }
    let witness: Value =
        serde_json::from_slice(&std::fs::read(fixture().join("manifest.json")).unwrap()).unwrap();
    assert!(
        witness["independent_runtime_observations"]
            .to_string()
            .contains("PositionSuite.scala:10")
    );
}

#[test]
fn unavailable_preceding_input_and_same_name_source_definition_cannot_admit_the_intrinsic() {
    let mut facts = captured();
    let macros = macro_ids(&facts);
    enrich(&mut facts, true);
    assert!(
        macros
            .iter()
            .all(|&id| facts.operations[id].opcode == Opcode::Unknown)
    );
    let mut facts = captured();
    let macros = macro_ids(&facts);
    let symbol = facts.operations[macros[0]].target;
    facts.symbols[symbol.index()].flags |= SYMBOL_DEFINED;
    enrich(&mut facts, false);
    assert!(
        macros
            .iter()
            .all(|&id| facts.operations[id].opcode == Opcode::Unknown)
    );
}

#[test]
fn wrong_result_owner_or_orphan_metadata_keeps_the_exact_macro_guard() {
    for control in 0..3 {
        let mut facts = captured();
        let id = macro_ids(&facts)[0];
        let body = facts.operations[id].body;
        let other = facts
            .symbols
            .iter()
            .position(|s| {
                facts.text(s.name)
                    == if control == 0 {
                        "positioncase/UserMacros.effect()."
                    } else {
                        "scala/Int#"
                    }
            })
            .unwrap();
        match control {
            0 => facts.operations[id].target = SymbolId(other as u32),
            1 => facts.operations[id - 1].target = SymbolId(other as u32),
            _ => facts.operations[id].a = ValueId::NONE,
        }
        enrich(&mut facts, false);
        assert_eq!(facts.operations[id].opcode, Opcode::Unknown);
        let owner = facts.bodies[body.index()];
        assert!(facts.issues.iter().any(|i| i.file == owner.file
            && i.symbol == owner.symbol
            && facts.text(i.detail) == GUARD));
    }
}

#[test]
fn resolving_one_macro_never_erases_another_opaque_expansion_in_the_same_body() {
    let mut facts = captured();
    let id = macro_ids(&facts)[0];
    let body = facts.operations[id].body;
    let owned = facts.bodies[body.index()];
    let other = owned
        .operations
        .range()
        .find(|&i| i != id && i != id - 1)
        .unwrap();
    facts.operations[other].opcode = Opcode::Unknown;
    facts.operations[other].flags = EDGE_UNKNOWN | OP_MACRO_EXPANSION;
    facts.operations[other].target = SymbolId::NONE;
    enrich(&mut facts, false);
    assert_eq!(facts.operations[id].opcode, Opcode::Allocate);
    assert!(facts.issues.iter().any(|issue| issue.file == owned.file
        && issue.symbol == owned.symbol
        && facts.text(issue.detail) == GUARD));
}
