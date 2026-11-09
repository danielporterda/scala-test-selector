//! Borrowing streaming projection of compiler signatures. The raw signature is
//! already retained once in the string pool; constructing a JSON object/tree
//! for every TypeRef would otherwise create millions of transient allocations.
use crate::{buffer::Buffer, json_error};
use selector_types::Error;
use serde::de::{DeserializeSeed, IgnoredAny, MapAccess, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer};
use serde_json::value::RawValue;
use std::borrow::Cow;
use std::fmt;

#[derive(Default, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Text<'a>(pub Cow<'a, str>);
impl<'de> Deserialize<'de> for Text<'de> {
    fn deserialize<D: Deserializer<'de>>(decoder: D) -> Result<Self, D::Error> {
        struct StringVisitor;
        impl<'de> Visitor<'de> for StringVisitor {
            type Value = Text<'de>;
            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("compiler symbol string")
            }
            fn visit_borrowed_str<E: serde::de::Error>(
                self,
                s: &'de str,
            ) -> Result<Self::Value, E> {
                Ok(Text(Cow::Borrowed(s)))
            }
            fn visit_str<E: serde::de::Error>(self, s: &str) -> Result<Self::Value, E> {
                Ok(Text(Cow::Owned(s.to_owned())))
            }
            fn visit_string<E: serde::de::Error>(self, s: String) -> Result<Self::Value, E> {
                Ok(Text(Cow::Owned(s)))
            }
        }
        decoder.deserialize_str(StringVisitor)
    }
}
pub(crate) struct Projection<'a> {
    pub references: Buffer<Text<'a>, 8>,
    pub parents: Buffer<Text<'a>, 4>,
    pub scoped_links: Buffer<Text<'a>, 8>,
    pub hardlinks: Vec<&'a RawValue>,
    pub complete_scala_parents: bool,
}
impl<'a> Projection<'a> {
    fn new() -> Self {
        Self {
            references: Buffer::new(),
            parents: Buffer::new(),
            scoped_links: Buffer::new(),
            hardlinks: Vec::new(),
            complete_scala_parents: false,
        }
    }
}
#[derive(Clone, Copy)]
enum Mode {
    Signature,
    Generic,
    Class,
    Scope,
    ParentType,
    ParentConstructor,
    ParentContainer,
    ParentWrapper,
}
struct Node<'a, 'de> {
    output: &'a mut Projection<'de>,
    mode: Mode,
    collect_scopes: bool,
}
impl<'de> DeserializeSeed<'de> for Node<'_, 'de> {
    type Value = ();
    fn deserialize<D: Deserializer<'de>>(self, decoder: D) -> Result<(), D::Error> {
        decoder.deserialize_any(self)
    }
}
impl<'de> Visitor<'de> for Node<'_, 'de> {
    type Value = ();
    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("compiler signature node")
    }
    fn visit_map<M: MapAccess<'de>>(self, mut map: M) -> Result<(), M::Error> {
        let mut parent_form = false;
        let mut parent_symbol = false;
        let mut parent_contents = false;
        while let Some(key) = map.next_key::<Text<'de>>()? {
            if matches!(
                (self.mode, key.0.as_ref()),
                (Mode::ParentWrapper, "tpe") | (Mode::ParentContainer, "types")
            ) {
                parent_contents = true;
            }
            if matches!(self.mode, Mode::ParentType)
                && matches!(
                    key.0.as_ref(),
                    "type_ref"
                        | "single_type"
                        | "this_type"
                        | "super_type"
                        | "intersection_type"
                        | "with_type"
                        | "annotated_type"
                        | "existential_type"
                        | "structural_type"
                        | "universal_type"
                )
            {
                parent_form = true;
            }
            match key.0.as_ref() {
                "documentation" | "constant" | "literal_tree" | "constant_type" => {
                    map.next_value::<IgnoredAny>()?;
                }
                "symbol" => {
                    let symbol = map.next_value::<Text<'de>>()?;
                    if matches!(self.mode, Mode::ParentConstructor) {
                        parent_symbol = !symbol.0.is_empty();
                        self.output.parents.push(symbol.clone());
                    }
                    self.output.references.push(symbol);
                }
                "symlinks" | "overridden_symbols" => {
                    map.next_value_seed(SymbolList {
                        output: self.output,
                        scope: self.collect_scopes
                            && matches!(self.mode, Mode::Scope)
                            && key.0 == "symlinks",
                    })?;
                }
                "hardlinks" if self.collect_scopes => {
                    map.next_value_seed(Hardlinks {
                        output: self.output,
                    })?;
                }
                key => {
                    if matches!(self.mode, Mode::Signature) && key == "class_signature" {
                        self.output.complete_scala_parents = true;
                    }
                    let mode = match (self.mode, key) {
                        (_, "class_signature") => Mode::Class,
                        (Mode::Class, "parents") => Mode::ParentType,
                        (
                            Mode::ParentType,
                            "type_ref" | "single_type" | "this_type" | "super_type",
                        ) => Mode::ParentConstructor,
                        (Mode::ParentType, "intersection_type" | "with_type") => {
                            Mode::ParentContainer
                        }
                        (
                            Mode::ParentType,
                            "annotated_type" | "existential_type" | "structural_type"
                            | "universal_type",
                        ) => Mode::ParentWrapper,
                        (Mode::ParentContainer, "types") | (Mode::ParentWrapper, "tpe") => {
                            Mode::ParentType
                        }
                        (_, "declarations" | "type_parameters" | "parameter_lists")
                            if self.collect_scopes =>
                        {
                            Mode::Scope
                        }
                        _ => Mode::Generic,
                    };
                    map.next_value_seed(Node {
                        output: self.output,
                        mode,
                        collect_scopes: self.collect_scopes,
                    })?;
                }
            }
        }
        if (matches!(self.mode, Mode::ParentType) && !parent_form)
            || (matches!(self.mode, Mode::ParentConstructor) && !parent_symbol)
            || (matches!(self.mode, Mode::ParentWrapper | Mode::ParentContainer)
                && !parent_contents)
        {
            self.output.complete_scala_parents = false;
        }
        Ok(())
    }
    fn visit_seq<S: SeqAccess<'de>>(self, mut seq: S) -> Result<(), S::Error> {
        if matches!(
            self.mode,
            Mode::Class | Mode::ParentConstructor | Mode::ParentWrapper
        ) {
            self.output.complete_scala_parents = false;
        }
        while seq
            .next_element_seed(Node {
                output: self.output,
                mode: self.mode,
                collect_scopes: self.collect_scopes,
            })?
            .is_some()
        {}
        Ok(())
    }
    fn visit_bool<E: serde::de::Error>(self, _: bool) -> Result<(), E> {
        self.visit_unit()
    }
    fn visit_i64<E: serde::de::Error>(self, _: i64) -> Result<(), E> {
        self.visit_unit()
    }
    fn visit_u64<E: serde::de::Error>(self, _: u64) -> Result<(), E> {
        self.visit_unit()
    }
    fn visit_f64<E: serde::de::Error>(self, _: f64) -> Result<(), E> {
        self.visit_unit()
    }
    fn visit_str<E: serde::de::Error>(self, _: &str) -> Result<(), E> {
        self.visit_unit()
    }
    fn visit_none<E: serde::de::Error>(self) -> Result<(), E> {
        self.visit_unit()
    }
    fn visit_unit<E: serde::de::Error>(self) -> Result<(), E> {
        if matches!(
            self.mode,
            Mode::Class
                | Mode::ParentType
                | Mode::ParentConstructor
                | Mode::ParentWrapper
                | Mode::ParentContainer
        ) {
            self.output.complete_scala_parents = false;
        }
        Ok(())
    }
}
struct SymbolList<'a, 'de> {
    output: &'a mut Projection<'de>,
    scope: bool,
}
impl<'de> DeserializeSeed<'de> for SymbolList<'_, 'de> {
    type Value = ();
    fn deserialize<D: Deserializer<'de>>(self, d: D) -> Result<(), D::Error> {
        d.deserialize_seq(self)
    }
}
impl<'de> Visitor<'de> for SymbolList<'_, 'de> {
    type Value = ();
    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("compiler symbol list")
    }
    fn visit_seq<S: SeqAccess<'de>>(self, mut seq: S) -> Result<(), S::Error> {
        while let Some(symbol) = seq.next_element::<Text<'de>>()? {
            if self.scope {
                self.output.scoped_links.push(symbol.clone());
            }
            self.output.references.push(symbol);
        }
        Ok(())
    }
}
struct Hardlinks<'a, 'de> {
    output: &'a mut Projection<'de>,
}
impl<'de> DeserializeSeed<'de> for Hardlinks<'_, 'de> {
    type Value = ();
    fn deserialize<D: Deserializer<'de>>(self, d: D) -> Result<(), D::Error> {
        d.deserialize_seq(self)
    }
}
impl<'de> Visitor<'de> for Hardlinks<'_, 'de> {
    type Value = ();
    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("compiler hardlink information")
    }
    fn visit_seq<S: SeqAccess<'de>>(self, mut seq: S) -> Result<(), S::Error> {
        while let Some(raw) = seq.next_element::<&'de RawValue>()? {
            self.output.hardlinks.push(raw);
            // Outer signatures also depend on symbols referenced by hardlinks;
            // ownership of the hardlink's own nested scopes is handled when its
            // Information is independently admitted, not reassigned to this owner.
            let mut decoder = serde_json::Deserializer::from_str(raw.get());
            decoder.disable_recursion_limit();
            Node {
                output: self.output,
                mode: Mode::Generic,
                collect_scopes: false,
            }
            .deserialize(&mut decoder)
            .map_err(serde::de::Error::custom)?;
        }
        Ok(())
    }
}
/// Input is already depth-bounded by SemanticDB document admission.
pub(crate) fn project(raw: &str) -> Result<Projection<'_>, Error> {
    let mut output = Projection::new();
    let mut decoder = serde_json::Deserializer::from_str(raw);
    decoder.disable_recursion_limit();
    Node {
        output: &mut output,
        mode: Mode::Signature,
        collect_scopes: true,
    }
    .deserialize(&mut decoder)
    .map_err(json_error)?;
    decoder.end().map_err(json_error)?;
    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    fn texts<'a>(values: &'a [Text<'a>]) -> Vec<&'a str> {
        values.iter().map(|s| s.0.as_ref()).collect()
    }
    #[test]
    fn streaming_projection_preserves_scopes_hardlinks_and_outer_constructor_only() {
        let raw=json!({"class_signature":{
            "type_parameters":{"symlinks":["p/C#[T]"]},
            "parents":[{"type_ref":{"symbol":"p/Base#","type_arguments":[{"type_ref":{"symbol":"p/Arg#"}}]}},
                {"intersection_type":{"types":[{"type_ref":{"symbol":"p/Trait1#"}},{"annotated_type":{"tpe":{"type_ref":{"symbol":"p/Trait2#"}},"annotations":[{"tpe":{"type_ref":{"symbol":"p/Marker#"}}}]}}]}}],
            "declarations":{"symlinks":["p/C#f()."],"hardlinks":[{"symbol":"local0","kind":19,
                "signature":{"method_signature":{"parameter_lists":[{"symlinks":["local1"]}],"return_type":{"type_ref":{"symbol":"p/Result#"}}}}}]}}}).to_string();
        let projected = project(&raw).unwrap();
        assert_eq!(
            texts(&projected.parents),
            ["p/Base#", "p/Trait1#", "p/Trait2#"]
        );
        let mut links = texts(&projected.scoped_links);
        links.sort_unstable();
        assert_eq!(links, ["p/C#[T]", "p/C#f()."]);
        assert_eq!(projected.hardlinks.len(), 1);
        let refs = texts(&projected.references);
        for symbol in ["p/Arg#", "p/Marker#", "p/Result#", "local0", "local1"] {
            assert!(refs.contains(&symbol));
        }
        assert!(
            !links.contains(&"local1"),
            "hardlink owns its nested parameter, not outer class"
        );
    }
    #[test]
    fn escaped_compiler_names_survive_and_literal_payloads_are_opaque() {
        let raw = r#"{"value_signature":{"tpe":{"type_ref":{"symbol":"p/C#`quoted\"name`()."},"constant_type":{"constant":{"symbol":"fake"}}}}}"#;
        let projected = project(raw).unwrap();
        assert_eq!(texts(&projected.references), ["p/C#`quoted\"name`()."]);
        assert!(matches!(projected.references[0].0, Cow::Owned(_)));
    }
}
