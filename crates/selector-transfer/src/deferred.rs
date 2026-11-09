//! Narrow possible-execution policies, independent of native return semantics.
use selector_facts::FactSnapshot;
use selector_graph::ProgramGraph;
use selector_types::{EDGE_CALLBACK_DEFERRED, NodeId, SYMBOL_DEFINED, SymbolId};

pub(super) fn possible_future_callback(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    declared: SymbolId,
    target: NodeId,
    flags: u32,
) -> bool {
    if flags & EDGE_CALLBACK_DEFERRED == 0 || declared.is_none() {
        return false;
    }
    let symbol = &facts.symbols[declared.index()];
    symbol.flags & SYMBOL_DEFINED == 0
        && graph.nodes[target.index()].symbol == declared
        && matches!(
            facts.symbol_name(declared),
            "scala/concurrent/Future#map()." | "scala/concurrent/Future#flatMap()."
        )
}
