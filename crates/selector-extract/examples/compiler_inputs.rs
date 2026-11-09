//! Reproduce complete product admission independently of graph/query work.
use selector_extract::compiler_inputs::{InventoryLimits, InventoryStatus, admit};
use std::path::PathBuf;
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args_os().skip(1);
    let manifest = PathBuf::from(args.next().ok_or("compiler-contexts path required")?);
    let root = PathBuf::from(args.next().ok_or("relocated source root required")?);
    let output = args.next().map(PathBuf::from);
    let workers = args
        .next()
        .map(|s| s.to_str().unwrap().parse())
        .transpose()?
        .unwrap_or(4);
    let start = std::time::Instant::now();
    let admitted = admit(
        &manifest,
        &root,
        &InventoryLimits {
            workers,
            ..Default::default()
        },
    )?;
    if let Some(path) = output {
        serde_json::to_writer_pretty(std::fs::File::create(path)?, &admitted.receipt)?;
    }
    println!(
        "products={} verified={} unverified={} classes={} identity={} elapsed_s={:.3}",
        admitted.receipt.products.len(),
        admitted
            .receipt
            .products
            .iter()
            .filter(|p| p.status == InventoryStatus::Verified)
            .count(),
        admitted
            .receipt
            .products
            .iter()
            .filter(|p| p.status != InventoryStatus::Verified)
            .count(),
        admitted
            .receipt
            .products
            .iter()
            .map(|p| p.classes)
            .sum::<usize>(),
        admitted.identity,
        start.elapsed().as_secs_f64()
    );
    Ok(())
}
