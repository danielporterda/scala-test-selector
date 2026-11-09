//! Compare enriched records over one identical captured source snapshot.
use selector_facts::{FactSnapshot, codec};
use selector_types::*;
use std::{collections::BTreeSet, path::Path};
fn recipes(f: &FactSnapshot) -> BTreeSet<(&str, &str)> {
    f.bodies
        .iter()
        .filter(|b| b.flags & BODY_BINARY_RECIPE != 0)
        .map(|b| {
            let s = &f.symbols[b.symbol.index()];
            (f.text(s.context), f.text(s.name))
        })
        .collect()
}
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.len() != 3 {
        return Err("usage: binary_replay_diff SOURCE_FACTS OLD_ENRICHED NEW_ENRICHED".into());
    }
    let original = codec::read(Path::new(&args[0]))?;
    let ns = original.symbols.len();
    let no = original.operations.len();
    let nb = original.bodies.len();
    drop(original);
    let old = codec::read(Path::new(&args[1]))?;
    let new = codec::read(Path::new(&args[2]))?;
    let mut defined = Vec::new();
    let mut placeholders = Vec::new();
    for i in 0..ns {
        let a = &old.symbols[i];
        let b = &new.symbols[i];
        if (
            a.name,
            a.display,
            a.owner,
            a.file,
            a.context,
            a.kind,
            a.properties,
            a.signature,
            a.span,
            a.flags,
        ) != (
            b.name,
            b.display,
            b.owner,
            b.file,
            b.context,
            b.kind,
            b.properties,
            b.signature,
            b.span,
            b.flags,
        ) {
            let row = serde_json::json!({"context":old.text(a.context),"symbol":old.text(a.name),"old_kind":a.kind,"new_kind":b.kind});
            if a.flags & SYMBOL_DEFINED != 0 {
                defined.push(row)
            } else {
                placeholders.push(row)
            }
        }
    }
    let operations = (0..no).all(|i| {
        let a = old.operations[i];
        let b = new.operations[i];
        (
            a.body,
            a.opcode,
            a.target,
            a.dest,
            a.a,
            a.b,
            a.arguments,
            a.span,
            a.flags,
        ) == (
            b.body,
            b.opcode,
            b.target,
            b.dest,
            b.a,
            b.b,
            b.arguments,
            b.span,
            b.flags,
        )
    });
    let bodies = (0..nb).all(|i| {
        let a = old.bodies[i];
        let b = new.bodies[i];
        (
            a.symbol,
            a.file,
            a.span,
            a.name_span,
            a.operations,
            a.parameters,
            a.body_hash,
            a.flags,
        ) == (
            b.symbol,
            b.file,
            b.span,
            b.name_span,
            b.operations,
            b.parameters,
            b.body_hash,
            b.flags,
        )
    });
    let old_recipes = recipes(&old);
    let new_recipes = recipes(&new);
    println!(
        "{}",
        serde_json::to_string_pretty(&serde_json::json!({"source_defined_symbol_changes":defined,
        "source_placeholder_changes":placeholders,"source_operations_identical":operations,"source_bodies_identical":bodies,
        "added_binary_recipes":new_recipes.difference(&old_recipes).collect::<Vec<_>>(),
        "removed_binary_recipes":old_recipes.difference(&new_recipes).collect::<Vec<_>>() }))?
    );
    Ok(())
}
