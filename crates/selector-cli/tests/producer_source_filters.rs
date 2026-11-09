//! Exercise the exact build-script source selector without adding a runtime
//! dependency or reproducing its allowlist in the test.
#[allow(dead_code)]
#[path = "../build.rs"]
mod producer_build;
