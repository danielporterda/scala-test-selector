//! Standalone extraction measurement; caller supplies actual capture paths.
use selector_extract::{ExtractOptions, import_capture};
use std::path::PathBuf;
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args_os().skip(1);
    let path = PathBuf::from(args.next().ok_or("capture path required")?);
    let syntax = args.next().filter(|s| s != "-").map(PathBuf::from);
    let workers = args
        .next()
        .map(|s| s.to_str().unwrap().parse())
        .transpose()?
        .unwrap_or(1);
    let start = std::time::Instant::now();
    let facts = import_capture(
        &path,
        syntax.as_deref(),
        &ExtractOptions {
            workers,
            ..Default::default()
        },
    )?;
    let cross_context_refs = facts
        .occurrences
        .iter()
        .filter(|o| {
            o.role != 2
                && facts.files[o.file.index()].context != facts.symbols[o.symbol.index()].context
                && facts.symbols[o.symbol.index()].flags & selector_types::SYMBOL_DEFINED != 0
        })
        .count();
    println!(
        "workers={workers} elapsed_s={:.3} files={} symbols={} occurrences={} relations={} bodies={} operations={} issues={} owned_bytes={} cross_context_refs={}",
        start.elapsed().as_secs_f64(),
        facts.files.len(),
        facts.symbols.len(),
        facts.occurrences.len(),
        facts.relations.len(),
        facts.bodies.len(),
        facts.operations.len(),
        facts.issues.len(),
        facts.owned_bytes(),
        cross_context_refs
    );
    Ok(())
}
