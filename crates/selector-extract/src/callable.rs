//! Small borrowing projection used by syntax lowering. Reading call arity and
//! parameter modes must not materialize the compiler's entire type/signature DOM.
use crate::{buffer::Buffer, json_error, signature::Text};
use selector_types::Error;
use serde::de::{DeserializeSeed, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer};
use serde_json::value::RawValue;
use std::{borrow::Cow, fmt};

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub(crate) struct Shape {
    pub clauses: usize,
    pub returns_function: bool,
    pub value_function: bool,
    pub known_method: bool,
}
pub(crate) struct Metadata<'a> {
    pub shape: Shape,
    pub parameters: Buffer<Text<'a>>,
    /// Flattened parameter start of each compiler value clause (empty allowed).
    pub clause_starts: Buffer<usize>,
    pub by_name: bool,
    pub repeated: bool,
    pub function_arity: Option<usize>,
}
#[derive(Deserialize)]
struct Signature<'a> {
    #[serde(default, borrow)]
    method_signature: Option<Method<'a>>,
    #[serde(default, borrow)]
    value_signature: Option<Typed<'a>>,
}
#[derive(Deserialize)]
struct Method<'a> {
    #[serde(default, borrow)]
    parameter_lists: Option<&'a RawValue>,
    #[serde(default, borrow)]
    return_type: Option<&'a RawValue>,
}
#[derive(Deserialize)]
struct Typed<'a> {
    #[serde(default, borrow)]
    tpe: Option<&'a RawValue>,
}
#[derive(Deserialize)]
struct Scope<'a> {
    #[serde(default, borrow)]
    symlinks: Option<&'a RawValue>,
}
#[derive(Deserialize)]
struct Symbol<'a> {
    #[serde(default, borrow)]
    symbol: Cow<'a, str>,
}
#[derive(Deserialize)]
struct Type<'a> {
    #[serde(default, borrow)]
    type_ref: Option<Symbol<'a>>,
    #[serde(default, borrow)]
    annotated_type: Option<Typed<'a>>,
    #[serde(default, borrow)]
    by_name_type: Option<Typed<'a>>,
    #[serde(default, borrow)]
    existential_type: Option<Typed<'a>>,
    #[serde(default, borrow)]
    universal_type: Option<Typed<'a>>,
    #[serde(default, borrow)]
    repeated_type: Option<Typed<'a>>,
}
fn parse<'de, T: Deserialize<'de>>(raw: &'de str) -> Result<T, Error> {
    // These slices are retained signatures from already depth-checked documents.
    let mut decoder = serde_json::Deserializer::from_str(raw);
    decoder.disable_recursion_limit();
    let value = T::deserialize(&mut decoder).map_err(json_error)?;
    decoder.end().map_err(json_error)?;
    Ok(value)
}
fn function_arity(raw: &RawValue) -> Result<Option<usize>, Error> {
    let tpe: Type<'_> = parse(raw.get())?;
    if let Some(reference) = tpe.type_ref {
        return Ok(reference
            .symbol
            .strip_prefix("scala/Function")
            .and_then(|s| s.strip_suffix('#'))
            .filter(|s| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()))
            .and_then(|s| s.parse().ok()));
    }
    for wrapper in [
        tpe.annotated_type,
        tpe.by_name_type,
        tpe.existential_type,
        tpe.universal_type,
    ]
    .into_iter()
    .flatten()
    {
        if let Some(inner) = wrapper.tpe {
            if let Some(arity) = function_arity(inner)? {
                return Ok(Some(arity));
            }
        }
    }
    Ok(None)
}

fn by_name(raw: &RawValue) -> Result<bool, Error> {
    let tpe: Type<'_> = parse(raw.get())?;
    if tpe.by_name_type.is_some() {
        return Ok(true);
    }
    for wrapper in [tpe.annotated_type, tpe.existential_type, tpe.universal_type]
        .into_iter()
        .flatten()
    {
        if let Some(inner) = wrapper.tpe {
            if by_name(inner)? {
                return Ok(true);
            }
        }
    }
    Ok(false)
}
struct Names<'a, 'de>(&'a mut Buffer<Text<'de>>);
impl<'de> DeserializeSeed<'de> for Names<'_, 'de> {
    type Value = ();
    fn deserialize<D: Deserializer<'de>>(self, decoder: D) -> Result<(), D::Error> {
        decoder.deserialize_seq(self)
    }
}
impl<'de> Visitor<'de> for Names<'_, 'de> {
    type Value = ();
    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("parameter symbol names")
    }
    fn visit_seq<S: SeqAccess<'de>>(self, mut seq: S) -> Result<(), S::Error> {
        while let Some(name) = seq.next_element::<Text<'de>>()? {
            self.0.push(name);
        }
        Ok(())
    }
}
struct Clauses<'a, 'de>(&'a mut Metadata<'de>);
impl<'de> DeserializeSeed<'de> for Clauses<'_, 'de> {
    type Value = ();
    fn deserialize<D: Deserializer<'de>>(self, decoder: D) -> Result<(), D::Error> {
        decoder.deserialize_seq(self)
    }
}
impl<'de> Visitor<'de> for Clauses<'_, 'de> {
    type Value = ();
    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("compiler parameter clauses")
    }
    fn visit_seq<S: SeqAccess<'de>>(self, mut seq: S) -> Result<(), S::Error> {
        while let Some(scope) = seq.next_element::<Scope<'de>>()? {
            self.0.clause_starts.push(self.0.parameters.len());
            self.0.shape.clauses += 1;
            if let Some(names) = scope.symlinks {
                let mut decoder = serde_json::Deserializer::from_str(names.get());
                Names(&mut self.0.parameters)
                    .deserialize(&mut decoder)
                    .map_err(serde::de::Error::custom)?;
            }
        }
        Ok(())
    }
}
pub(crate) fn project(raw: &str) -> Result<Metadata<'_>, Error> {
    let signature: Signature<'_> = parse(raw)?;
    let mut result = Metadata {
        shape: Shape::default(),
        parameters: Buffer::new(),
        clause_starts: Buffer::new(),
        by_name: false,
        repeated: false,
        function_arity: None,
    };
    if let Some(method) = signature.method_signature {
        result.shape.known_method = true;
        if let Some(clauses) = method.parameter_lists {
            let mut decoder = serde_json::Deserializer::from_str(clauses.get());
            Clauses(&mut result)
                .deserialize(&mut decoder)
                .map_err(json_error)?;
        }
        if let Some(returned) = method.return_type {
            result.function_arity = function_arity(returned)?;
            result.shape.returns_function = result.function_arity.is_some();
        }
    }
    if let Some(value) = signature.value_signature.and_then(|v| v.tpe) {
        result.function_arity = function_arity(value)?;
        result.shape.value_function = result.function_arity.is_some();
        result.by_name = by_name(value)?;
        result.repeated = parse::<Type<'_>>(value.get())?.repeated_type.is_some();
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn ordered_clauses_and_wrapped_function_modes_preserve_compiler_identity() {
        let raw = r#"{"method_signature":{"type_parameters":{"symlinks":["ignore[T]"]},"parameter_lists":[{"symlinks":["p/C#f().(x)","local0"]},{"symlinks":[]}],"return_type":{"annotated_type":{"tpe":{"type_ref":{"symbol":"scala/Function0#","type_arguments":[{"type_ref":{"symbol":"p/Unrelated#"}}]}}}}}}"#;
        let result = project(raw).unwrap();
        assert_eq!(
            result.shape,
            Shape {
                clauses: 2,
                returns_function: true,
                known_method: true,
                value_function: false
            }
        );
        assert_eq!(
            result
                .parameters
                .iter()
                .map(|n| n.0.as_ref())
                .collect::<Vec<_>>(),
            ["p/C#f().(x)", "local0"]
        );
        assert_eq!(&*result.clause_starts, &[0, 2]);
        assert!(!result.by_name);
        assert_eq!(result.function_arity, Some(0));
        let result = project(r#"{"value_signature":{"tpe":{"by_name_type":{"tpe":{"type_ref":{"symbol":"scala/Function2#"}}}}}}"#).unwrap();
        assert!(result.by_name && result.shape.value_function);
        assert_eq!(result.function_arity, Some(2));
        assert!(project(r#"{"value_signature":{"tpe":{"annotated_type":{"tpe":{"by_name_type":{"tpe":{"type_ref":{"symbol":"scala/Int#"}}}}}}}}"#).unwrap().by_name);
        for name in ["some/Function0#", "scala/Function#", "scala/Function0ish#"] {
            assert!(
                !project(&format!(
                    r#"{{"value_signature":{{"tpe":{{"type_ref":{{"symbol":"{name}"}}}}}}}}"#
                ))
                .unwrap()
                .shape
                .value_function
            );
        }
    }
}
