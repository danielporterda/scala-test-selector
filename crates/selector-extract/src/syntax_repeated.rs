//! Compiler repeated formals are one ABI argument, never a join of arguments.
//! The syntax producer explicitly distinguishes a spread provider from an
//! expanded element. Missing proof keeps the old evaluated-provider frontier.
use super::*;

fn coordinates(argument: AstValue<'_>) -> Option<(u32, u32)> {
    Some((
        u32::try_from(number(argument, "clause_index")?).ok()?,
        u32::try_from(number(argument, "argument_index")?).ok()?,
    ))
}
fn formal_at(metadata: &[CallParameter], clause: u32, argument: u32) -> Option<usize> {
    metadata.iter().position(|formal| {
        formal.clause == clause
            && (formal.argument == argument || (formal.repeated && formal.argument < argument))
    })
}

/// This certifies argument arrangement only. It does not grant a concrete Seq
/// class, backend wrapper purity, or any collection operation implementation.
pub(super) fn admitted(
    site: AstValue<'_>,
    metadata: &[CallParameter],
    facts: &FactSnapshot,
) -> bool {
    if !metadata.iter().any(|formal| formal.repeated) {
        return false;
    }
    let Some(first) = metadata.first().filter(|formal| !formal.symbol.is_none()) else {
        return false;
    };
    let owner = facts.symbols[first.symbol.index()].owner;
    if owner.is_none() {
        return false;
    }
    let context = facts.symbols[owner.index()].context;
    for (index, formal) in metadata.iter().enumerate() {
        if formal.symbol.is_none() {
            return false;
        }
        let record = facts.symbols[formal.symbol.index()];
        if record.kind != 8 || record.owner != owner || record.context != context {
            return false;
        }
        if formal.repeated
            && (!formal.mode_known
                || formal.by_name
                || formal.has_default
                || metadata[index + 1..]
                    .first()
                    .is_some_and(|next| next.clause == formal.clause))
        {
            return false;
        }
    }
    let actuals = rows(site, "arguments");
    let mut previous = None;
    for (index, actual) in actuals.iter().enumerate() {
        if actual
            .get("label_range")
            .is_some_and(|value| !value.is_null())
        {
            return false;
        }
        let Some((clause, argument)) = coordinates(actual) else {
            return false;
        };
        if previous.is_some_and(|(old_clause, old_argument)| {
            clause < old_clause || (clause == old_clause && argument != old_argument + 1)
        }) {
            return false;
        }
        if previous.is_none_or(|(old_clause, _)| old_clause != clause) && argument != 0 {
            return false;
        }
        previous = Some((clause, argument));
        let Some(formal) = formal_at(metadata, clause, argument) else {
            return false;
        };
        if metadata[formal].repeated {
            let Some(spread) = actual
                .get("repeated_spread")
                .and_then(|value| value.as_bool())
            else {
                return false;
            };
            if spread
                && (argument != metadata[formal].argument
                    || actuals.get(index + 1).is_some_and(|next| {
                        coordinates(next).is_some_and(|(next_clause, _)| next_clause == clause)
                    }))
            {
                return false;
            }
            // A prior spread cannot be followed by expanded elements.
            if index > 0
                && actuals
                    .get(index - 1)
                    .unwrap()
                    .get("repeated_spread")
                    .and_then(|value| value.as_bool())
                    == Some(true)
                && coordinates(actuals.get(index - 1).unwrap())
                    .is_some_and(|(prior_clause, _)| prior_clause == clause)
            {
                return false;
            }
        } else if actual
            .get("repeated_spread")
            .and_then(|value| value.as_bool())
            == Some(true)
        {
            return false;
        }
    }
    true
}

impl BodyLowerer<'_> {
    pub(super) fn packed_arguments(
        &mut self,
        site: AstValue<'_>,
        target: Option<SymbolId>,
        receiver: ValueId,
        metadata: &[CallParameter],
    ) -> Result<Buffer<ValueId>, Error> {
        let mut arguments = Buffer::with_capacity(metadata.len());
        let mut elements = Buffer::<ValueId>::new();
        let actuals = rows(site, "arguments");
        for (index, actual) in actuals.iter().enumerate() {
            let (clause, argument) =
                coordinates(actual).ok_or(Error::Invalid("repeated coordinates"))?;
            let completed = metadata.partition_point(|parameter| parameter.clause < clause);
            // Packing/default evaluation in an earlier curried clause precedes
            // every provider in the next clause, including implicit providers.
            self.empty_repeated(site, metadata, &mut arguments, completed)?;
            self.fill_defaults(site, target, receiver, metadata, &mut arguments, completed)?;
            let expression = range(actual, "expression_start", "expression_end", self.coords)
                .or_else(|_| span(actual, self.coords))?;
            let value = self.expression(expression)?;
            let position = formal_at(metadata, clause, argument)
                .ok_or(Error::Invalid("repeated formal binding"))?;
            if arguments.len() <= position {
                arguments.resize(position + 1, ValueId::NONE);
            }
            if metadata[position].repeated {
                if actual
                    .get("repeated_spread")
                    .and_then(|value| value.as_bool())
                    == Some(true)
                {
                    // The provider already denotes the sequence. A spread is
                    // identity forwarding, not a one-element nested carrier.
                    arguments[position] = value;
                } else {
                    elements.push(value);
                    let last = actuals.get(index + 1).is_none_or(|next| {
                        coordinates(next).is_none_or(|(next_clause, _)| next_clause != clause)
                    });
                    if last {
                        arguments[position] = self.pack_repeated(site, &elements)?;
                        elements = Buffer::new();
                    }
                }
            } else {
                arguments[position] = value;
            }
        }
        let formal_end = self
            .pending_implicit_clause(site, target, metadata)
            .unwrap_or(metadata.len());
        self.empty_repeated(site, metadata, &mut arguments, formal_end)?;
        self.fill_defaults(site, target, receiver, metadata, &mut arguments, formal_end)?;
        Ok(arguments)
    }

    fn empty_repeated(
        &mut self,
        site: AstValue<'_>,
        metadata: &[CallParameter],
        arguments: &mut Buffer<ValueId>,
        formal_end: usize,
    ) -> Result<(), Error> {
        for (index, formal) in metadata[..formal_end].iter().enumerate() {
            if formal.repeated && arguments.get(index).is_none_or(|value| value.is_none()) {
                if arguments.len() <= index {
                    arguments.resize(index + 1, ValueId::NONE);
                }
                arguments[index] = self.pack_repeated(site, &[])?;
            }
        }
        Ok(())
    }

    fn pack_repeated(
        &mut self,
        site: AstValue<'_>,
        elements: &[ValueId],
    ) -> Result<ValueId, Error> {
        let target = self
            .builder
            .ensure_symbol(SEQUENCE_ELEMENTS_SYMBOL, self.file)?;
        let value = self.value()?;
        self.emit(
            Opcode::PackSequence,
            target,
            value,
            ValueId::NONE,
            ValueId::NONE,
            elements,
            span(site, self.coords)?,
            0,
        )?;
        // RepeatedType and the parsed source prove the ABI arrangement, but
        // not the effects of a possibly shadowed backend runtime wrapper.
        self.builder.issue(
            IssueKind::UnknownExecution,
            self.file,
            self.bodies[self.index].symbol,
            "repeated argument container backend effects remain unverified",
        )?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn exact_arrangement_requires_owned_repeated_formals_and_explicit_spread_proof() {
        let mut builder = FactBuilder::new();
        let owner = builder.ensure_symbol("p/Api#run().", FileId::NONE).unwrap();
        let parameter = builder
            .ensure_symbol("p/Api#run().(callbacks)", FileId::NONE)
            .unwrap();
        builder.facts.symbols[parameter.index()].owner = owner;
        builder.facts.symbols[parameter.index()].kind = 8;
        let mut formals = [CallParameter {
            symbol: parameter,
            mode_known: true,
            repeated: true,
            ..Default::default()
        }];
        let flat = json!({"arguments":[
            {"clause_index":0,"argument_index":0,"repeated_spread":false},
            {"clause_index":0,"argument_index":1,"repeated_spread":false}]});
        let check = |value: &serde_json::Value, formals: &[CallParameter], facts: &FactSnapshot| {
            let encoded = value.to_string();
            let ast = AstTree::parse(&encoded).unwrap();
            admitted(ast.root(), formals, facts)
        };
        assert!(check(&flat, &formals, &builder.facts));
        assert!(check(&json!({"arguments":[]}), &formals, &builder.facts));
        assert!(check(
            &json!({"arguments":[{"clause_index":0,"argument_index":0,"repeated_spread":true}]}),
            &formals,
            &builder.facts
        ));
        for invalid in [
            json!({"arguments":[{"clause_index":0,"argument_index":0}]}),
            json!({"arguments":[{"clause_index":0,"argument_index":0,"repeated_spread":null}]}),
            json!({"arguments":[{"clause_index":0,"argument_index":0,"repeated_spread":"false"}]}),
            json!({"arguments":[{"clause_index":0,"argument_index":1,"repeated_spread":false}]}),
            json!({"arguments":[{"clause_index":1,"argument_index":0,"repeated_spread":false}]}),
            json!({"arguments":[{"clause_index":0,"argument_index":0,"repeated_spread":true},
                {"clause_index":0,"argument_index":1,"repeated_spread":false}]}),
            json!({"arguments":[{"clause_index":0,"argument_index":0,"repeated_spread":false},
                {"clause_index":0,"argument_index":1,"repeated_spread":true}]}),
            json!({"arguments":[{"clause_index":0,"argument_index":0,"repeated_spread":false,"label_range":{"start":1,"end":2}}]}),
        ] {
            assert!(!check(&invalid, &formals, &builder.facts), "{invalid}");
        }
        formals[0].by_name = true;
        assert!(!check(&flat, &formals, &builder.facts));
        formals[0].by_name = false;
        formals[0].mode_known = false;
        assert!(!check(&flat, &formals, &builder.facts));
        formals[0].mode_known = true;
        builder.facts.symbols[parameter.index()].owner = SymbolId::NONE;
        assert!(!check(&flat, &formals, &builder.facts));
    }
}
