//! Isolated compiler-bound projection allocation assay. Artifact I/O/admission
//! happen outside the counter window; instrumented time is not throughput.
use std::alloc::{GlobalAlloc, Layout, System};
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering::Relaxed};
struct Counter;
static ACTIVE: AtomicBool = AtomicBool::new(false);
static ALLOCATIONS: AtomicU64 = AtomicU64::new(0);
static BYTES: AtomicU64 = AtomicU64::new(0);
unsafe impl GlobalAlloc for Counter {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // SAFETY: Forward the caller's valid allocation layout to System.
        let pointer = unsafe { System.alloc(layout) };
        if !pointer.is_null() && ACTIVE.load(Relaxed) {
            ALLOCATIONS.fetch_add(1, Relaxed);
            BYTES.fetch_add(layout.size() as u64, Relaxed);
        }
        pointer
    }
    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        // SAFETY: The caller supplies the allocated pointer and original layout.
        unsafe { System.dealloc(pointer, layout) }
    }
    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        // SAFETY: Forward the allocation pointer, original layout and new size.
        let result = unsafe { System.realloc(pointer, layout, size) };
        if !result.is_null() && ACTIVE.load(Relaxed) {
            ALLOCATIONS.fetch_add(1, Relaxed);
            BYTES.fetch_add(size as u64, Relaxed);
        }
        result
    }
}
#[global_allocator]
static COUNTER: Counter = Counter;
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let argument = std::env::args()
        .nth(1)
        .ok_or("fact artifact path or --synthetic=N required")?;
    let mut facts = if let Some(count) = argument.strip_prefix("--synthetic=") {
        use selector_types::*;
        let mut builder = selector_facts::FactBuilder::new();
        let class = builder.ensure_symbol("p/Class#", FileId::NONE)?;
        builder.facts.symbols[class.index()].kind = 13;
        builder.facts.symbols[class.index()].flags = SYMBOL_DEFINED;
        let signature = builder
            .intern(r#"{"method_signature":{"return_type":{"type_ref":{"symbol":"p/Class#"}}}}"#)?;
        for index in 0..count.parse::<usize>()? {
            let method = builder.ensure_symbol(&format!("p/F.f{index}()."), FileId::NONE)?;
            let record = &mut builder.facts.symbols[method.index()];
            record.kind = 3;
            record.flags = SYMBOL_DEFINED;
            record.signature = signature;
        }
        builder.finish()?
    } else {
        selector_facts::codec::read(&PathBuf::from(argument))?
    };
    let symbols = facts.symbols.len();
    let signatures = facts
        .symbols
        .iter()
        .filter(|symbol| !symbol.signature.is_none())
        .count();
    let start = std::time::Instant::now();
    ACTIVE.store(true, Relaxed);
    let result = selector_extract::project_result_bounds(&mut facts);
    ACTIVE.store(false, Relaxed);
    result?;
    let elapsed = start.elapsed().as_nanos();
    let allocations = ALLOCATIONS.load(Relaxed);
    let bytes = BYTES.load(Relaxed);
    facts.validate()?;
    println!(
        "{{\"symbols\":{symbols},\"signatures\":{signatures},\"result_bounds\":{},\"bound_classes\":{},\"allocations\":{allocations},\"cumulative_allocated_bytes\":{bytes},\"instrumented_elapsed_ns\":{elapsed}}}",
        facts.result_bounds.len(),
        facts.bound_classes.len()
    );
    Ok(())
}
