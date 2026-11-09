//! Isolated transient AST decode allocation assay. I/O and captured-row decoding
//! are outside the window; instrumented times are not throughput benchmarks.
#[path = "../src/syntax_tree.rs"]
#[allow(dead_code)] // The assay imports the production tree but needs only its diagnostic views.
mod syntax_tree;
use serde::Deserialize;
use serde_json::{Value, value::RawValue};
use std::alloc::{GlobalAlloc, Layout, System};
use std::io::{BufRead, BufReader};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering::Relaxed};
struct Counter;
static ACTIVE: AtomicBool = AtomicBool::new(false);
static ALLOCS: AtomicU64 = AtomicU64::new(0);
static BYTES: AtomicU64 = AtomicU64::new(0);
unsafe impl GlobalAlloc for Counter {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let p = unsafe { System.alloc(layout) };
        if !p.is_null() && ACTIVE.load(Relaxed) {
            ALLOCS.fetch_add(1, Relaxed);
            BYTES.fetch_add(layout.size() as u64, Relaxed);
        }
        p
    }
    unsafe fn dealloc(&self, p: *mut u8, layout: Layout) {
        unsafe { System.dealloc(p, layout) }
    }
    unsafe fn realloc(&self, p: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        let p = unsafe { System.realloc(p, layout, size) };
        if !p.is_null() && ACTIVE.load(Relaxed) {
            ALLOCS.fetch_add(1, Relaxed);
            BYTES.fetch_add(size as u64, Relaxed);
        }
        p
    }
}
#[global_allocator]
static ALLOCATOR: Counter = Counter;
#[derive(Deserialize)]
struct Row<'a> {
    #[serde(borrow)]
    ast: &'a RawValue,
}
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let path = std::env::args_os()
        .nth(1)
        .ok_or("syntax JSONL path required")?;
    let mut input = BufReader::new(std::fs::File::open(path)?);
    let mut line = String::new();
    let mut rows = 0u64;
    let mut raw_bytes = 0u64;
    let mut allocations = 0u64;
    let mut bytes = 0u64;
    let mut projected_allocations = 0u64;
    let mut projected_bytes = 0u64;
    let mut nodes = 0usize;
    while input.read_line(&mut line)? > 0 {
        let row: Row<'_> = serde_json::from_str(&line)?;
        rows += 1;
        raw_bytes += row.ast.get().len() as u64;
        let a = ALLOCS.load(Relaxed);
        let b = BYTES.load(Relaxed);
        ACTIVE.store(true, Relaxed);
        let value: Value = serde_json::from_str(row.ast.get())?;
        std::hint::black_box(&value);
        ACTIVE.store(false, Relaxed);
        allocations += ALLOCS.load(Relaxed) - a;
        bytes += BYTES.load(Relaxed) - b;
        let a = ALLOCS.load(Relaxed);
        let b = BYTES.load(Relaxed);
        ACTIVE.store(true, Relaxed);
        let projected = syntax_tree::Tree::parse(row.ast.get())?;
        std::hint::black_box(&projected);
        ACTIVE.store(false, Relaxed);
        projected_allocations += ALLOCS.load(Relaxed) - a;
        projected_bytes += BYTES.load(Relaxed) - b;
        nodes += projected.node_count();
        compare(projected.root(), &value);
        drop(projected);
        drop(value);
        line.clear();
    }
    println!(
        "syntax_rows={rows} raw_ast_bytes={raw_bytes} transient_dom_allocations={allocations} cumulative_dom_allocated_bytes={bytes} projected_allocations={projected_allocations} cumulative_projected_bytes={projected_bytes} projected_nodes={nodes} semantic_differences=0"
    );
    Ok(())
}
fn compare(node: syntax_tree::Node<'_>, old: &Value) {
    match old {
        Value::Object(map) => {
            for (key, child) in node.fields() {
                compare(child, &map[key]);
            }
        }
        Value::Array(array) => {
            let projected = node.as_array().expect("array kind");
            assert_eq!(projected.len(), array.len());
            for (new, old) in projected.iter().zip(array) {
                compare(new, old);
            }
        }
        Value::String(s) => assert_eq!(node.as_str(), Some(s.as_str())),
        Value::Bool(b) => assert_eq!(node.as_bool(), Some(*b)),
        Value::Null => assert!(node.is_null()),
        Value::Number(n) => assert_eq!(node.as_i64(), n.as_i64()),
    }
}
