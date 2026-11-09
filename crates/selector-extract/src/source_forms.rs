//! Small admission rules for structural source forms. Identities and method
//! shapes come from the compiler; source spelling never chooses a target.
use crate::callable::Shape;
use selector_types::{Span, SymbolId};

/// `f[T]` invokes a compiler-proven nullary method. A parameterized method may
/// instead eta-expand, or receive compiler-inserted implicit arguments. Without
/// that extra recipe, executing it eagerly would invent effects at closure creation.
pub(crate) fn nullary_type_application(shape: Shape) -> bool {
    shape.known_method && shape.clauses == 0
}

/// Bounded implicit eta expansion needs the compiler's expected FunctionN and
/// one complete value parameter clause. Curried/implicit/by-name adaptation
/// remains unknown until its complete compiler expression recipe is available.
pub(crate) fn direct_eta(shape: Shape, parameters: usize, expected: Option<usize>) -> bool {
    shape.known_method && shape.clauses == 1 && expected == Some(parameters)
}

/// Scalameta gives immediate placeholder formals exact ranges even though
/// SemanticDB has no occurrence on `_`. Those admitted parameter slots bind by
/// range. Captures have an enclosing body range and must never use this rule.
pub(crate) fn anonymous_parameter_span(
    symbol: SymbolId,
    span: Span,
    capture: bool,
) -> Option<Span> {
    (symbol.is_none() && !capture).then_some(span)
}
