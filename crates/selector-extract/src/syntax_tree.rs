//! Borrowed, flat AST projection. Only fields consumed by syntax lowering are
//! retained; repeated JSON keys and ordinary strings never own heap objects.
//! Containers use sibling indices in one arena, not a Vec/BTreeMap per object.
use serde::de::{DeserializeSeed, IgnoredAny, MapAccess, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer};
use std::fmt;

const NONE: u32 = u32::MAX;
macro_rules! keys {
    ($($variant:ident => $name:literal),* $(,)?) => {
        #[derive(Clone,Copy,Debug,PartialEq,Eq)]#[repr(u8)]
        enum Key{Unknown,$($variant),*}
        impl Key {
            fn parse(name:&str)->Self {match name {$($name=>Self::$variant,)* _=>Self::Unknown}}
            #[allow(dead_code)] // Projection equivalence diagnostics, not the production lowerer.
            fn name(self)->&'static str {match self {$(Self::$variant=>$name,)*Self::Unknown=>""}}
        }
    }
}
// This whitelist is the syntax lowerer's input contract, not a source language
// parser. Keep it beside tests comparing every retained field against the DOM.
keys! {
    AllocationEnd=>"allocation_end",AllocationStart=>"allocation_start",Arguments=>"arguments",ArgumentIndex=>"argument_index",ClauseIndex=>"clause_index",
    BodyEnd=>"body_end",BodyStart=>"body_start",CallSites=>"call_sites",
    Constructors=>"constructors",Default=>"default",DeferredRanges=>"deferred_ranges",Diagnostics=>"diagnostics",
    Eager=>"eager",EffectRanges=>"effect_ranges",End=>"end",Executable=>"executable",ExpressionEnd=>"expression_end",ExpressionStart=>"expression_start",
    FunctionEnd=>"function_end",FunctionStart=>"function_start",InitializerRanges=>"initializer_ranges",
    Kind=>"kind",LabelRange=>"label_range",Lazy=>"lazy",Members=>"members",Message=>"message",
    NameEnd=>"name_end",NameStart=>"name_start",Owners=>"owners",ParameterRanges=>"parameter_ranges",
    ParameterUnknowns=>"parameter_unknowns",Parameters=>"parameters",Path=>"path",PlaceholderRanges=>"placeholder_ranges",
    ReceiverEnd=>"receiver_end",ReceiverStart=>"receiver_start",RepeatedSpread=>"repeated_spread",ResultRanges=>"result_ranges",ReturnRanges=>"return_ranges",
    ReturnUnknowns=>"return_unknowns",Sha256=>"sha256",Start=>"start",TypeRanges=>"type_ranges",
    UnknownValues=>"unknown",ValueExpressions=>"value_expressions",
}

#[derive(Debug)]
enum Scalar<'a> {
    Null,
    Bool(bool),
    Number(serde_json::Number),
    Text(&'a str),
    OwnedText(u32),
    Array,
    Object,
}
#[derive(Debug)]
struct Record<'a> {
    scalar: Scalar<'a>,
    first: u32,
    next: u32,
    len: u32,
    key: Key,
}
#[derive(Debug)]
pub struct Tree<'a> {
    nodes: Vec<Record<'a>>,
    strings: Vec<String>,
    max_nodes: usize,
    max_depth: usize,
}
impl<'a> Tree<'a> {
    pub fn parse(input: &'a str) -> Result<Self, serde_json::Error> {
        Self::with_limits(input, 4_000_000, 128)
    }
    pub fn with_limits(
        input: &'a str,
        max_nodes: usize,
        max_depth: usize,
    ) -> Result<Self, serde_json::Error> {
        // A bounded counting pass avoids reallocating/copying millions of records
        // as an arena grows. It creates no container/string objects and also
        // validates ignored JSON rather than treating it as an unchecked blob.
        let mut count = 0;
        let mut counter = serde_json::Deserializer::from_str(input);
        CountSeed {
            count: &mut count,
            max_nodes,
            max_depth,
            depth: 0,
        }
        .deserialize(&mut counter)?;
        counter.end()?;
        let mut tree = Self {
            nodes: Vec::with_capacity(count),
            strings: Vec::new(),
            max_nodes,
            max_depth,
        };
        let mut decoder = serde_json::Deserializer::from_str(input);
        Seed {
            tree: &mut tree,
            key: Key::Unknown,
            depth: 0,
        }
        .deserialize(&mut decoder)?;
        decoder.end()?;
        Ok(tree)
    }
    pub fn root(&self) -> Node<'_> {
        Node {
            tree: self,
            index: 0,
        }
    }
    #[allow(dead_code)] // Allocation assay, intentionally outside normal extraction.
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }
    #[allow(dead_code)] // Allocation assay, intentionally outside normal extraction.
    pub fn retained_bytes(&self) -> usize {
        self.nodes.capacity() * std::mem::size_of::<Record<'_>>()
            + self.strings.capacity() * std::mem::size_of::<String>()
            + self.strings.iter().map(String::capacity).sum::<usize>()
    }
}
#[derive(Clone, Copy)]
pub struct Node<'a> {
    tree: &'a Tree<'a>,
    index: u32,
}
impl fmt::Debug for Node<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.record().fmt(f)
    }
}
impl<'a> Node<'a> {
    fn record(self) -> &'a Record<'a> {
        &self.tree.nodes[self.index as usize]
    }
    pub fn get(self, name: &str) -> Option<Self> {
        if !matches!(self.record().scalar, Scalar::Object) {
            return None;
        }
        let key = Key::parse(name);
        if key == Key::Unknown {
            return None;
        }
        self.children().find(|child| child.record().key == key)
    }
    pub fn as_i64(self) -> Option<i64> {
        match &self.record().scalar {
            Scalar::Number(n) => n.as_i64(),
            _ => None,
        }
    }
    pub fn as_bool(self) -> Option<bool> {
        match self.record().scalar {
            Scalar::Bool(b) => Some(b),
            _ => None,
        }
    }
    pub fn as_str(self) -> Option<&'a str> {
        match &self.record().scalar {
            Scalar::Text(s) => Some(*s),
            Scalar::OwnedText(index) => Some(self.tree.strings[*index as usize].as_str()),
            _ => None,
        }
    }
    pub fn is_null(self) -> bool {
        matches!(self.record().scalar, Scalar::Null)
    }
    pub fn as_array(self) -> Option<Array<'a>> {
        matches!(self.record().scalar, Scalar::Array).then(|| Array { parent: self })
    }
    pub fn rows(self, name: &str) -> Array<'a> {
        self.get(name)
            .and_then(Self::as_array)
            .unwrap_or_else(|| self.empty_array())
    }
    pub fn empty_array(self) -> Array<'a> {
        Array {
            parent: Node {
                tree: self.tree,
                index: NONE,
            },
        }
    }
    pub fn children(self) -> Children<'a> {
        Children {
            tree: self.tree,
            next: self.record().first,
            left: self.record().len,
        }
    }
    #[allow(dead_code)] // Projection equivalence diagnostics, not the production lowerer.
    pub fn fields(self) -> impl Iterator<Item = (&'static str, Node<'a>)> {
        self.children().map(|n| (n.record().key.name(), n))
    }
}
#[derive(Clone, Copy)]
pub struct Array<'a> {
    parent: Node<'a>,
}
impl<'a> Array<'a> {
    pub fn len(self) -> usize {
        if self.parent.index == NONE {
            0
        } else {
            self.parent.record().len as usize
        }
    }
    pub fn iter(self) -> Children<'a> {
        if self.parent.index == NONE {
            Children {
                tree: self.parent.tree,
                next: NONE,
                left: 0,
            }
        } else {
            self.parent.children()
        }
    }
    pub fn get(self, index: usize) -> Option<Node<'a>> {
        self.iter().nth(index)
    }
    pub fn first(self) -> Option<Node<'a>> {
        self.iter().next()
    }
}
impl<'a> IntoIterator for Array<'a> {
    type Item = Node<'a>;
    type IntoIter = Children<'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
#[derive(Clone)]
pub struct Children<'a> {
    tree: &'a Tree<'a>,
    next: u32,
    left: u32,
}
impl<'a> Iterator for Children<'a> {
    type Item = Node<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.next == NONE {
            return None;
        }
        let node = Node {
            tree: self.tree,
            index: self.next,
        };
        self.next = node.record().next;
        self.left -= 1;
        Some(node)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.left as usize, Some(self.left as usize))
    }
}
impl ExactSizeIterator for Children<'_> {}

struct Seed<'t, 'de> {
    tree: &'t mut Tree<'de>,
    key: Key,
    depth: usize,
}
impl<'de> DeserializeSeed<'de> for Seed<'_, 'de> {
    type Value = u32;
    fn deserialize<D: Deserializer<'de>>(self, decoder: D) -> Result<u32, D::Error> {
        if self.depth > self.tree.max_depth
            || self.tree.nodes.len() >= self.tree.max_nodes
            || self.tree.nodes.len() >= u32::MAX as usize
        {
            return Err(serde::de::Error::custom("syntax projection limit"));
        }
        let index = self.tree.nodes.len() as u32;
        self.tree.nodes.push(Record {
            scalar: Scalar::Null,
            first: NONE,
            next: NONE,
            len: 0,
            key: self.key,
        });
        decoder.deserialize_any(NodeVisitor {
            tree: self.tree,
            index,
            depth: self.depth,
        })?;
        Ok(index)
    }
}
struct NodeVisitor<'t, 'de> {
    tree: &'t mut Tree<'de>,
    index: u32,
    depth: usize,
}
impl NodeVisitor<'_, '_> {
    fn link(&mut self, previous: &mut u32, child: u32) {
        if *previous == NONE {
            self.tree.nodes[self.index as usize].first = child;
        } else {
            self.tree.nodes[*previous as usize].next = child;
        }
        *previous = child;
        self.tree.nodes[self.index as usize].len += 1;
    }
}
impl<'de> Visitor<'de> for NodeVisitor<'_, 'de> {
    type Value = ();
    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("validated syntax JSON")
    }
    fn visit_unit<E: serde::de::Error>(self) -> Result<(), E> {
        Ok(())
    }
    fn visit_none<E: serde::de::Error>(self) -> Result<(), E> {
        Ok(())
    }
    fn visit_bool<E: serde::de::Error>(self, b: bool) -> Result<(), E> {
        self.tree.nodes[self.index as usize].scalar = Scalar::Bool(b);
        Ok(())
    }
    fn visit_i64<E: serde::de::Error>(self, n: i64) -> Result<(), E> {
        self.tree.nodes[self.index as usize].scalar = Scalar::Number(n.into());
        Ok(())
    }
    fn visit_u64<E: serde::de::Error>(self, n: u64) -> Result<(), E> {
        self.tree.nodes[self.index as usize].scalar = Scalar::Number(n.into());
        Ok(())
    }
    fn visit_f64<E: serde::de::Error>(self, n: f64) -> Result<(), E> {
        self.tree.nodes[self.index as usize].scalar = Scalar::Number(
            serde_json::Number::from_f64(n).ok_or_else(|| E::custom("invalid syntax number"))?,
        );
        Ok(())
    }
    fn visit_borrowed_str<E: serde::de::Error>(self, text: &'de str) -> Result<(), E> {
        self.tree.nodes[self.index as usize].scalar = Scalar::Text(text);
        Ok(())
    }
    fn visit_str<E: serde::de::Error>(self, text: &str) -> Result<(), E> {
        let index = self.tree.strings.len() as u32;
        self.tree.strings.push(text.to_owned());
        self.tree.nodes[self.index as usize].scalar = Scalar::OwnedText(index);
        Ok(())
    }
    fn visit_string<E: serde::de::Error>(self, text: String) -> Result<(), E> {
        let index = self.tree.strings.len() as u32;
        self.tree.strings.push(text);
        self.tree.nodes[self.index as usize].scalar = Scalar::OwnedText(index);
        Ok(())
    }
    fn visit_seq<A: SeqAccess<'de>>(mut self, mut sequence: A) -> Result<(), A::Error> {
        self.tree.nodes[self.index as usize].scalar = Scalar::Array;
        let mut previous = NONE;
        while let Some(child) = sequence.next_element_seed(Seed {
            tree: self.tree,
            key: Key::Unknown,
            depth: self.depth + 1,
        })? {
            self.link(&mut previous, child);
        }
        Ok(())
    }
    fn visit_map<A: MapAccess<'de>>(mut self, mut map: A) -> Result<(), A::Error> {
        self.tree.nodes[self.index as usize].scalar = Scalar::Object;
        let mut previous = NONE;
        let mut seen = 0u64;
        while let Some(key) = map.next_key::<FieldKey>()? {
            let key = key.0;
            if key == Key::Unknown {
                map.next_value::<IgnoredAny>()?;
                continue;
            }
            let bit = 1u64 << (key as u8);
            if seen & bit != 0 {
                return Err(serde::de::Error::custom("duplicate syntax field"));
            }
            seen |= bit;
            let child = map.next_value_seed(Seed {
                tree: self.tree,
                key,
                depth: self.depth + 1,
            })?;
            self.link(&mut previous, child);
        }
        Ok(())
    }
}
struct FieldKey(Key);
impl<'de> Deserialize<'de> for FieldKey {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        struct KeyVisitor;
        impl Visitor<'_> for KeyVisitor {
            type Value = FieldKey;
            fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.write_str("syntax field name")
            }
            fn visit_str<E: serde::de::Error>(self, s: &str) -> Result<Self::Value, E> {
                Ok(FieldKey(Key::parse(s)))
            }
        }
        d.deserialize_identifier(KeyVisitor)
    }
}

struct CountSeed<'a> {
    count: &'a mut usize,
    max_nodes: usize,
    max_depth: usize,
    depth: usize,
}
impl<'de> DeserializeSeed<'de> for CountSeed<'_> {
    type Value = ();
    fn deserialize<D: Deserializer<'de>>(self, d: D) -> Result<(), D::Error> {
        if self.depth > self.max_depth || *self.count >= self.max_nodes {
            return Err(serde::de::Error::custom("syntax projection limit"));
        }
        *self.count += 1;
        d.deserialize_any(self)
    }
}
impl<'de> Visitor<'de> for CountSeed<'_> {
    type Value = ();
    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("bounded syntax JSON")
    }
    fn visit_unit<E: serde::de::Error>(self) -> Result<(), E> {
        Ok(())
    }
    fn visit_bool<E: serde::de::Error>(self, _: bool) -> Result<(), E> {
        Ok(())
    }
    fn visit_i64<E: serde::de::Error>(self, _: i64) -> Result<(), E> {
        Ok(())
    }
    fn visit_u64<E: serde::de::Error>(self, _: u64) -> Result<(), E> {
        Ok(())
    }
    fn visit_f64<E: serde::de::Error>(self, _: f64) -> Result<(), E> {
        Ok(())
    }
    fn visit_str<E: serde::de::Error>(self, _: &str) -> Result<(), E> {
        Ok(())
    }
    fn visit_seq<A: SeqAccess<'de>>(self, mut s: A) -> Result<(), A::Error> {
        while s
            .next_element_seed(CountSeed {
                count: self.count,
                max_nodes: self.max_nodes,
                max_depth: self.max_depth,
                depth: self.depth + 1,
            })?
            .is_some()
        {}
        Ok(())
    }
    fn visit_map<A: MapAccess<'de>>(self, mut m: A) -> Result<(), A::Error> {
        while let Some(key) = m.next_key::<FieldKey>()? {
            if key.0 == Key::Unknown {
                m.next_value::<IgnoredAny>()?;
            } else {
                m.next_value_seed(CountSeed {
                    count: self.count,
                    max_nodes: self.max_nodes,
                    max_depth: self.max_depth,
                    depth: self.depth + 1,
                })?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn compare(node: Node<'_>, old: &serde_json::Value) {
        match &node.record().scalar {
            Scalar::Object => {
                let object = old.as_object().unwrap();
                let count = object
                    .keys()
                    .filter(|k| Key::parse(k) != Key::Unknown)
                    .count();
                assert_eq!(count, node.record().len as usize);
                for (key, child) in node.fields() {
                    compare(child, &object[key]);
                }
            }
            Scalar::Array => {
                let array = old.as_array().unwrap();
                assert_eq!(array.len(), node.as_array().unwrap().len());
                for (new, old) in node.children().zip(array) {
                    compare(new, old);
                }
            }
            Scalar::Text(_) | Scalar::OwnedText(_) => assert_eq!(node.as_str(), old.as_str()),
            Scalar::Bool(b) => assert_eq!(Some(*b), old.as_bool()),
            Scalar::Number(n) => assert_eq!(Some(n), old.as_number()),
            Scalar::Null => assert!(old.is_null()),
        }
    }
    #[test]
    fn borrowed_flat_nodes_preserve_escaped_strings_scalars_and_order() {
        let input = r#"{"members":[{"kind":"def","start":-1,"end":123,"executable":true,"default":null,"parameters":[],"return_unknowns":["plain","escaped\nline","\u96ea"]}],"body":["discarded"]}"#;
        let tree = Tree::parse(input).unwrap();
        compare(tree.root(), &serde_json::from_str(input).unwrap());
        assert!(tree.root().get("body").is_none());
        let node = tree.root().rows("members").get(0).unwrap();
        assert_eq!(node.get("start").unwrap().as_i64(), Some(-1));
        let text = node
            .rows("return_unknowns")
            .get(0)
            .unwrap()
            .as_str()
            .unwrap();
        let start = input.as_ptr() as usize;
        assert!((start..start + input.len()).contains(&(text.as_ptr() as usize)));
    }
    #[test]
    fn real_ast_projection_retains_every_lowering_field() {
        #[derive(Deserialize)]
        struct Row<'a> {
            #[serde(borrow)]
            ast: &'a serde_json::value::RawValue,
        }
        for line in include_str!("../../../fixtures/compiler-smoke/syntax.jsonl").lines() {
            let row: Row<'_> = serde_json::from_str(line).unwrap();
            let tree = Tree::parse(row.ast.get()).unwrap();
            let old: serde_json::Value = serde_json::from_str(row.ast.get()).unwrap();
            compare(tree.root(), &old);
        }
    }
    #[test]
    fn limits_duplicate_fields_and_malformed_json_are_explicit() {
        assert!(Tree::with_limits("[1,2]", 2, 128).is_err());
        assert!(Tree::with_limits("[[[0]]]", 100, 1).is_err());
        assert!(Tree::parse(r#"{"start":1,"start":2}"#).is_err());
        assert!(Tree::parse(r#"{"ignored":{"invalid":[1,]}}"#).is_err());
        assert!(Tree::parse("[1] trailing").is_err());
        assert!(Tree::parse("{\"tokens\":[\"unterminated]").is_err());
    }
}
