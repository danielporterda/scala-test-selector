//! Constructor occurrence identity does not require a declaration inventory.
//! In particular, SemanticDB keeps external Java selections without exporting
//! SymbolInformation. No signature, JVM descriptor or executable authority is
//! inferred from the selected compiler descriptor.
use super::*;

fn identity(facts: &FactSnapshot, symbol: SymbolId) -> bool {
    let name = facts.symbol_name(symbol);
    name.ends_with(").") && selector_types::symbol::member_name(name) == Some("<init>")
}
fn type_identity(facts: &FactSnapshot, symbol: SymbolId) -> bool {
    let record = facts.symbols[symbol.index()];
    matches!(record.kind, 13 | 14)
        || (record.kind == 0
            && record.flags & SYMBOL_DEFINED == 0
            && facts.symbol_name(symbol).ends_with('#'))
}
pub(super) fn target(
    lookup: &Lookup,
    name: Span,
    end: u32,
    facts: &FactSnapshot,
) -> Option<SymbolId> {
    let mut class = None;
    for id in lookup.exact(name, 1).filter(|&id| type_identity(facts, id)) {
        if class.is_some_and(|previous| previous != id) {
            return None;
        }
        class = Some(id);
    }
    let mut selected = None;
    for anchor in [
        Span { start: end, end },
        Span {
            start: name.end,
            end: name.end,
        },
        name,
    ] {
        for candidate in lookup.exact(anchor, 1).filter(|&id| identity(facts, id)) {
            let record = facts.symbols[candidate.index()];
            let declared = record.kind == 21;
            let external = record.kind == 0 && record.flags & SYMBOL_DEFINED == 0;
            // Missing kind may license only an exact, zero-width selection
            // with the same contextual type owner. Never choose by arity.
            if !declared && !external {
                return None;
            }
            if record.owner.is_none()
                || (external && (anchor.start != anchor.end || class != Some(record.owner)))
                || class.is_some_and(|class| record.owner != class)
                || facts.symbols[record.owner.index()].context != record.context
                || selector_types::symbol::global_owner(facts.symbol_name(candidate))
                    != Some(facts.symbol_name(record.owner))
            {
                return None;
            }
            if selected.is_some_and(|previous| previous != candidate) {
                return None;
            }
            selected = Some(candidate);
        }
    }
    selected
}

#[cfg(test)]
mod tests {
    use super::*;
    fn fixture(control: u8) -> (FactBuilder, Lookup, SymbolId) {
        let mut builder = FactBuilder::new();
        let context = builder.intern("a").unwrap();
        let other = builder.intern("b").unwrap();
        let class = builder
            .ensure_global_symbol("java/p/Native#", context)
            .unwrap();
        let constructor = builder
            .ensure_global_symbol("java/p/Native#`<init>`(+1).", context)
            .unwrap();
        let wrong = builder
            .ensure_global_symbol("java/p/Other#", context)
            .unwrap();
        builder.facts.symbols[constructor.index()].owner = if control == 2 { wrong } else { class };
        builder.facts.symbols[constructor.index()].kind = if control == 3 { 3 } else { 0 };
        if control == 4 {
            builder.facts.symbols[constructor.index()].context = other;
        }
        let name = Span { start: 10, end: 16 };
        let zero = Span { start: 16, end: 16 };
        let occurrence = |span, symbol, role| OccurrenceRecord {
            file: FileId::NONE,
            span,
            symbol,
            role,
            ordinal: 0,
        };
        let mut occurrences = vec![occurrence(name, class, 1)];
        if control != 1 {
            occurrences.push(occurrence(
                if control == 6 { name } else { zero },
                constructor,
                if control == 5 { 2 } else { 1 },
            ));
        }
        if control == 7 {
            let second = builder
                .ensure_global_symbol("java/p/Native#`<init>`().", context)
                .unwrap();
            builder.facts.symbols[second.index()].owner = class;
            occurrences.push(occurrence(zero, second, 1));
        }
        if control == 8 {
            occurrences.retain(|op| op.symbol != class);
        }
        if control == 9 {
            builder.facts.symbols[constructor.index()].flags |= SYMBOL_DEFINED;
        }
        occurrences.sort_unstable_by_key(|o| (o.span.start, o.span.end, o.role, o.symbol));
        (builder, Lookup { occurrences }, constructor)
    }
    #[test]
    fn undefined_external_constructor_requires_exact_zero_anchor_owner_and_context() {
        for control in 0..10 {
            let (builder, lookup, constructor) = fixture(control);
            let result = target(&lookup, Span { start: 10, end: 16 }, 16, &builder.facts);
            assert_eq!(
                result,
                (control == 0).then_some(constructor),
                "control {control}"
            );
            let record = builder.facts.symbols[constructor.index()];
            assert!(record.signature.is_none());
            assert_eq!(
                record.flags & (SYMBOL_NATIVE_BINARY | SYMBOL_JVM_CLASS_HEADER_VERIFIED),
                0
            );
        }
    }
}
