//! Standalone source-fact capsule prototype. No production selection authority.
mod index;
mod project;
pub use index::*;
pub use project::*;
#[cfg(test)]
mod tests;
