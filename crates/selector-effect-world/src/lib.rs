//! Compiled root/change correspondence only. This is not a complete effect world
//! and has no omission, source-guard suppression, or whole-checkout authority.
mod compiled;
pub use compiled::*;
#[cfg(test)]
mod tests;
