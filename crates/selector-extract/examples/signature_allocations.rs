//! Isolated allocation audit of the current transient signature DOM decoder.
//! Captured row decoding and I/O run outside the allocation window. Timings are
//! instrumented and are not comparable to uninstrumented throughput runs.
#[allow(dead_code)]
#[path = "../src/buffer.rs"]
mod buffer;
#[path = "../src/callable.rs"]
mod callable;
#[path = "../src/signature.rs"]
mod signature;
fn json_error(error: serde_json::Error) -> selector_types::Error {
    selector_types::Error::Message(error.to_string())
}
use flate2::read::MultiGzDecoder;
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
    document: &'a RawValue,
}
#[derive(Deserialize)]
struct Doc<'a> {
    #[serde(default, borrow)]
    symbols: Vec<Info<'a>>,
}
#[derive(Deserialize)]
struct Info<'a> {
    #[serde(default, borrow)]
    signature: Option<&'a RawValue>,
}
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let path = std::env::args_os().nth(1).ok_or("capture path required")?;
    let mut input = BufReader::new(MultiGzDecoder::new(std::fs::File::open(path)?));
    let mut line = String::new();
    let mut signatures = 0u64;
    let mut source_bytes = 0u64;
    let mut dom_allocations = 0;
    let mut dom_bytes = 0;
    let mut projected_allocations = 0;
    let mut projected_bytes = 0;
    let mut callable_allocations = 0;
    let mut callable_bytes = 0;
    let mut references = 0;
    while input.read_line(&mut line)? > 0 {
        let row: Row<'_> = serde_json::from_str(&line)?;
        let mut decoder = serde_json::Deserializer::from_str(row.document.get());
        decoder.disable_recursion_limit();
        let document = Doc::deserialize(&mut decoder)?;
        for info in &document.symbols {
            if let Some(signature) = info.signature {
                signatures += 1;
                source_bytes += signature.get().len() as u64;
                let before_allocs = ALLOCS.load(Relaxed);
                let before_bytes = BYTES.load(Relaxed);
                ACTIVE.store(true, Relaxed);
                let mut decoder = serde_json::Deserializer::from_str(signature.get());
                decoder.disable_recursion_limit();
                let value = Value::deserialize(&mut decoder)?;
                std::hint::black_box(&value);
                ACTIVE.store(false, Relaxed);
                dom_allocations += ALLOCS.load(Relaxed) - before_allocs;
                dom_bytes += BYTES.load(Relaxed) - before_bytes;
                let before_allocs = ALLOCS.load(Relaxed);
                let before_bytes = BYTES.load(Relaxed);
                ACTIVE.store(true, Relaxed);
                let projected = signature::project(signature.get())?;
                std::hint::black_box(&projected);
                ACTIVE.store(false, Relaxed);
                projected_allocations += ALLOCS.load(Relaxed) - before_allocs;
                projected_bytes += BYTES.load(Relaxed) - before_bytes;
                let before_allocs = ALLOCS.load(Relaxed);
                let before_bytes = BYTES.load(Relaxed);
                ACTIVE.store(true, Relaxed);
                let metadata = callable::project(signature.get())?;
                std::hint::black_box(&metadata);
                ACTIVE.store(false, Relaxed);
                callable_allocations += ALLOCS.load(Relaxed) - before_allocs;
                callable_bytes += BYTES.load(Relaxed) - before_bytes;
                let method = value.get("method_signature");
                assert_eq!(
                    metadata.shape,
                    callable::Shape {
                        known_method: method.is_some(),
                        clauses: method
                            .and_then(|m| m.get("parameter_lists"))
                            .and_then(Value::as_array)
                            .map_or(0, Vec::len),
                        returns_function: method
                            .and_then(|m| m.get("return_type"))
                            .is_some_and(function_type),
                        value_function: value
                            .pointer("/value_signature/tpe")
                            .is_some_and(function_type),
                    },
                    "callable shape differs"
                );
                assert_eq!(
                    metadata.by_name,
                    value.pointer("/value_signature/tpe/by_name_type").is_some(),
                    "parameter mode differs"
                );
                let old_parameters: Vec<_> = method
                    .and_then(|m| m.get("parameter_lists"))
                    .and_then(Value::as_array)
                    .into_iter()
                    .flatten()
                    .flat_map(|clause| {
                        clause
                            .get("symlinks")
                            .and_then(Value::as_array)
                            .into_iter()
                            .flatten()
                    })
                    .filter_map(Value::as_str)
                    .collect();
                let new_parameters: Vec<_> = metadata
                    .parameters
                    .iter()
                    .map(|name| name.0.as_ref())
                    .collect();
                assert_eq!(
                    old_parameters, new_parameters,
                    "parameter identities/order differ"
                );
                let mut old = Vec::new();
                declared_symbols(&value, &mut old);
                old.sort_unstable();
                old.dedup();
                let mut new: Vec<_> = projected.references.iter().map(|s| s.0.as_ref()).collect();
                new.sort_unstable();
                new.dedup();
                assert_eq!(old, new, "signature reference projection differs");
                references += old.len();
                let mut old_parents = Vec::new();
                if let Some(parents) = value
                    .pointer("/class_signature/parents")
                    .and_then(Value::as_array)
                {
                    for parent in parents {
                        outer_types(parent, &mut old_parents)
                    }
                }
                let new_parents: Vec<_> = projected.parents.iter().map(|s| s.0.as_ref()).collect();
                assert_eq!(old_parents, new_parents, "parent constructors differ");
            }
        }
        line.clear();
    }
    println!(
        "signatures={signatures} raw_signature_bytes={source_bytes} references={references} transient_dom_allocations={dom_allocations} cumulative_dom_allocated_bytes={dom_bytes} projected_allocations={projected_allocations} cumulative_projected_bytes={projected_bytes} callable_allocations={callable_allocations} cumulative_callable_bytes={callable_bytes} semantic_differences=0"
    );
    Ok(())
}

fn function_type(value: &Value) -> bool {
    if let Some(symbol) = value.pointer("/type_ref/symbol").and_then(Value::as_str) {
        return symbol
            .strip_prefix("scala/Function")
            .and_then(|s| s.strip_suffix('#'))
            .is_some_and(|s| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()));
    }
    [
        "annotated_type",
        "by_name_type",
        "existential_type",
        "universal_type",
    ]
    .iter()
    .any(|key| {
        value
            .get(key)
            .and_then(|v| v.get("tpe"))
            .is_some_and(function_type)
    })
}

fn declared_symbols<'a>(value: &'a Value, out: &mut Vec<&'a str>) {
    match value {
        Value::Object(map) => {
            for (key, child) in map {
                match key.as_str() {
                    "symbol" => {
                        if let Some(s) = child.as_str() {
                            out.push(s)
                        }
                    }
                    "symlinks" | "overridden_symbols" => {
                        if let Some(xs) = child.as_array() {
                            out.extend(xs.iter().filter_map(Value::as_str))
                        }
                    }
                    "documentation" | "constant" | "literal_tree" | "constant_type" => (),
                    _ => declared_symbols(child, out),
                }
            }
        }
        Value::Array(xs) => {
            for child in xs {
                declared_symbols(child, out)
            }
        }
        _ => (),
    }
}
fn outer_types<'a>(value: &'a Value, out: &mut Vec<&'a str>) {
    for key in ["type_ref", "single_type", "this_type", "super_type"] {
        if let Some(name) = value
            .get(key)
            .and_then(|v| v.get("symbol"))
            .and_then(Value::as_str)
        {
            out.push(name);
            return;
        }
    }
    for key in ["intersection_type", "with_type"] {
        if let Some(xs) = value
            .get(key)
            .and_then(|v| v.get("types"))
            .and_then(Value::as_array)
        {
            for child in xs {
                outer_types(child, out)
            }
        }
    }
    for key in [
        "annotated_type",
        "existential_type",
        "structural_type",
        "universal_type",
    ] {
        if let Some(inner) = value.get(key).and_then(|v| v.get("tpe")) {
            outer_types(inner, out)
        }
    }
}
