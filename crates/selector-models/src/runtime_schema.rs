//! Strict bounded OpenAPI trees, root references, and transitive reference identity.
//! YAML is data. Alias/tag rejection happens before loading; unused anchors are
//! stripped so the loader cannot clone nested anchored trees. Compiler targets
//! are resolved separately by runtime_routes from actual admitted compiler facts.
use crate::runtime::RuntimeSource;
use selector_types::{ContentHash, Error};
use serde::Serialize;
use serde_json::{Map, Number, Value};
use sha2::{Digest, Sha256};
use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::io::{self, Write};
use yaml_rust2::parser::{Event, MarkedEventReceiver, Parser};
use yaml_rust2::scanner::Marker;
use yaml_rust2::{Yaml, YamlLoader};

pub const VERSION: &str = "openapi-schema-tree/rust-v1";
const HTTP: &[&str] = &[
    "delete", "get", "head", "options", "patch", "post", "put", "trace",
];
#[derive(Debug, Clone, Copy)]
pub struct SchemaLimits {
    pub document_bytes: usize,
    pub depth: usize,
    pub nodes: usize,
    pub refs: usize,
    pub closure_nodes: usize,
}
impl Default for SchemaLimits {
    fn default() -> Self {
        Self {
            document_bytes: 4 * 1024 * 1024,
            depth: 512,
            nodes: 1_000_000,
            refs: 10_000,
            closure_nodes: 10_000_000,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SchemaDependency {
    pub path: String,
    pub pointer: String,
    pub identity: ContentHash,
    pub source_sha256: ContentHash,
}
#[derive(Debug, Clone)]
pub struct SchemaOperation {
    pub schema_path: String,
    pub path: String,
    pub verb: String,
    pub operation_id: String,
    pub tags: Vec<String>,
    pub namespace: Option<String>,
    pub server_urls: Vec<String>,
    pub fingerprint: ContentHash,
    pub schema_sha256: ContentHash,
    pub dependencies: Vec<SchemaDependency>,
    pub dependencies_complete: bool,
}
#[derive(Debug, Clone)]
pub struct SchemaDiff {
    pub changed: Vec<SchemaOperation>,
    pub all: Vec<SchemaOperation>,
}
struct Document {
    value: Value,
    sha256: ContentHash,
    root: bool,
}
pub struct SchemaTree {
    docs: BTreeMap<String, Document>,
    limits: SchemaLimits,
}
struct Target<'a> {
    path: &'a str,
    pointer: String,
    value: &'a Value,
}
struct Root<'a> {
    path: &'a str,
    value: Cow<'a, Value>,
}

pub fn yaml_document(text: &str, limits: SchemaLimits) -> Result<Value, Error> {
    let value = yaml_value(text, limits)?;
    validate_root(&value)?;
    Ok(value)
}
fn yaml_value(text: &str, limits: SchemaLimits) -> Result<Value, Error> {
    if text.len() > limits.document_bytes {
        return Err(Error::Limit("OpenAPI YAML bytes"));
    }
    let mut parser = Parser::new_from_str(text);
    let mut depth = 0usize;
    let mut nodes = 0usize;
    let mut documents = 0;
    loop {
        let (event, _) = parser
            .next_token()
            .map_err(|error| Error::Message(format!("safe YAML parse: {error}")))?;
        nodes += 1;
        if nodes > limits.nodes {
            return Err(Error::Limit("YAML node count"));
        }
        match event {
            Event::Alias(_) => return Err(Error::Invalid("YAML alias not supported")),
            Event::Scalar(_, _, _, Some(_))
            | Event::MappingStart(_, Some(_))
            | Event::SequenceStart(_, Some(_)) => {
                return Err(Error::Invalid("YAML explicit tag not supported"));
            }
            Event::MappingStart(_, _) | Event::SequenceStart(_, _) => {
                depth += 1;
                if depth > limits.depth {
                    return Err(Error::Limit("YAML nesting depth"));
                }
            }
            Event::MappingEnd | Event::SequenceEnd => {
                depth = depth
                    .checked_sub(1)
                    .ok_or(Error::Invalid("YAML delimiter"))?
            }
            Event::DocumentStart => {
                documents += 1;
                if documents > 1 {
                    return Err(Error::Invalid("multiple YAML documents"));
                }
            }
            Event::StreamEnd => break,
            _ => {}
        }
    }
    struct Unanchored {
        loader: YamlLoader,
    }
    impl MarkedEventReceiver for Unanchored {
        fn on_event(&mut self, event: Event, marker: Marker) {
            let event = match event {
                Event::Scalar(value, style, _, tag) => Event::Scalar(value, style, 0, tag),
                Event::MappingStart(_, tag) => Event::MappingStart(0, tag),
                Event::SequenceStart(_, tag) => Event::SequenceStart(0, tag),
                other => other,
            };
            self.loader.on_event(event, marker);
        }
    }
    let mut sink = Unanchored {
        loader: YamlLoader::default(),
    };
    Parser::new_from_str(text)
        .load(&mut sink, true)
        .map_err(|error| Error::Message(format!("safe YAML load: {error}")))?;
    if sink.loader.documents().len() != 1 {
        return Err(Error::Invalid("YAML duplicate key or invalid document"));
    }
    let value = normalize(&sink.loader.documents()[0], 0, limits.depth)?;
    Ok(value)
}
fn validate_root(value: &Value) -> Result<(), Error> {
    let root = value
        .as_object()
        .ok_or(Error::Invalid("OpenAPI root mapping"))?;
    if !root
        .get("openapi")
        .and_then(Value::as_str)
        .is_some_and(|version| version.starts_with("3."))
    {
        return Err(Error::Invalid("OpenAPI 3.x version"));
    }
    for key in ["paths", "components"] {
        if root.get(key).is_some_and(|value| !value.is_object()) {
            return Err(Error::Invalid("OpenAPI paths/components mapping"));
        }
    }
    Ok(())
}

fn normalize(value: &Yaml, depth: usize, maximum: usize) -> Result<Value, Error> {
    if depth > maximum {
        return Err(Error::Limit("YAML normalized depth"));
    }
    Ok(match value {
        Yaml::String(value) => Value::String(value.clone()),
        Yaml::Integer(value) => Value::Number((*value).into()),
        Yaml::Boolean(value) => Value::Bool(*value),
        Yaml::Null => Value::Null,
        Yaml::Real(value) => Value::Number(
            Number::from_f64(
                value
                    .parse::<f64>()
                    .map_err(|_| Error::Invalid("YAML real scalar"))?,
            )
            .ok_or(Error::Invalid("non-finite YAML scalar"))?,
        ),
        Yaml::Array(values) => Value::Array(
            values
                .iter()
                .map(|value| normalize(value, depth + 1, maximum))
                .collect::<Result<_, _>>()?,
        ),
        Yaml::Hash(values) => {
            let mut result = Map::new();
            for (key, value) in values {
                let key = match key {
                    Yaml::String(key) => key.clone(),
                    Yaml::Integer(value) => value.to_string(),
                    Yaml::Boolean(value) => if *value { "True" } else { "False" }.into(),
                    Yaml::Real(value) => Number::from_f64(
                        value
                            .parse::<f64>()
                            .map_err(|_| Error::Invalid("YAML real mapping key"))?,
                    )
                    .ok_or(Error::Invalid("non-finite YAML mapping key"))?
                    .to_string(),
                    _ => return Err(Error::Invalid("non-scalar YAML mapping key")),
                };
                if key == "<<" || result.contains_key(&key) {
                    return Err(Error::Invalid(
                        "duplicate or merged YAML key after normalization",
                    ));
                }
                result.insert(key, normalize(value, depth + 1, maximum)?);
            }
            Value::Object(result)
        }
        Yaml::Alias(_) | Yaml::BadValue => return Err(Error::Invalid("unsupported YAML value")),
    })
}
impl SchemaTree {
    pub fn new(sources: &[RuntimeSource<'_>]) -> Result<Self, Error> {
        Self::with_limits(sources, SchemaLimits::default())
    }
    pub fn with_limits(sources: &[RuntimeSource<'_>], limits: SchemaLimits) -> Result<Self, Error> {
        let mut docs = BTreeMap::new();
        for source in sources {
            let path = normalize_path("", source.path)?;
            if path != source.path {
                return Err(Error::Invalid("noncanonical schema path"));
            }
            let value = yaml_value(source.text, limits)?;
            let root = value.get("openapi").is_some();
            if root {
                validate_root(&value)?;
            }
            if docs
                .insert(
                    path,
                    Document {
                        value,
                        sha256: ContentHash(Sha256::digest(source.text.as_bytes()).into()),
                        root,
                    },
                )
                .is_some()
            {
                return Err(Error::Invalid("duplicate OpenAPI schema path"));
            }
        }
        Ok(Self { docs, limits })
    }
    pub fn source_identity(&self, path: &str) -> Option<ContentHash> {
        self.docs.get(path).map(|document| document.sha256)
    }
    fn target<'a>(&'a self, source: &str, reference: &str) -> Result<Target<'a>, Error> {
        let (relative, pointer) = reference.split_once('#').unwrap_or((reference, ""));
        if relative.contains(['?', ':', '\\'])
            || relative.starts_with('/')
            || reference.starts_with("//")
        {
            return Err(Error::Invalid("external or absolute repository reference"));
        }
        let relative = percent_decode(relative)?;
        if relative.starts_with('/') || relative.contains([':', '\\']) {
            return Err(Error::Invalid(
                "encoded external or absolute repository reference",
            ));
        }
        let path = if relative.is_empty() {
            source.to_owned()
        } else {
            normalize_path(
                source.rsplit_once('/').map_or("", |(parent, _)| parent),
                &relative,
            )?
        };
        let (path, document) = self.docs.get_key_value(&path).ok_or_else(|| {
            Error::Message(format!("unresolved repository reference: {reference}"))
        })?;
        let pointer = percent_decode(pointer)?;
        if !pointer.is_empty() && !pointer.starts_with('/') {
            return Err(Error::Invalid("reference is not a JSON pointer"));
        }
        let mut value = &document.value;
        let mut depth = 0;
        for raw in pointer.split('/').skip(1) {
            depth += 1;
            if depth > self.limits.depth {
                return Err(Error::Limit("reference pointer depth"));
            }
            let key = pointer_key(raw)?;
            value = match value {
                Value::Object(values) => values.get(&key),
                Value::Array(values) => {
                    if key.is_empty() || !key.bytes().all(|byte| byte.is_ascii_digit()) {
                        None
                    } else {
                        key.parse::<usize>()
                            .ok()
                            .and_then(|index| values.get(index))
                    }
                }
                _ => None,
            }
            .ok_or_else(|| Error::Message(format!("unresolved JSON pointer: {reference}")))?;
        }
        Ok(Target {
            path,
            pointer,
            value,
        })
    }
    fn root<'a>(&'a self, mut path: &'a str, mut value: &'a Value) -> Result<Root<'a>, Error> {
        let mut seen = BTreeSet::new();
        let mut annotations = Map::new();
        while let Some(object) = value
            .as_object()
            .filter(|object| object.contains_key("$ref"))
        {
            let reference = object["$ref"]
                .as_str()
                .ok_or(Error::Invalid("non-string reference"))?;
            for (key, value) in object {
                if key == "$ref" {
                    continue;
                }
                if key != "summary" && key != "description" && !key.starts_with("x-") {
                    return Err(Error::Invalid(
                        "behavioral path/operation reference sibling",
                    ));
                }
                annotations.insert(key.clone(), value.clone());
            }
            let target = self.target(path, reference)?;
            if !seen.insert((target.path, target.pointer.clone())) {
                return Err(Error::Invalid("recursive path or operation reference"));
            }
            if seen.len() > self.limits.refs {
                return Err(Error::Limit("root reference budget"));
            }
            path = target.path;
            value = target.value;
        }
        if annotations.is_empty() {
            Ok(Root {
                path,
                value: Cow::Borrowed(value),
            })
        } else {
            let mut value = value
                .as_object()
                .ok_or(Error::Invalid("annotated reference is not a mapping"))?
                .clone();
            value.extend(annotations);
            Ok(Root {
                path,
                value: Cow::Owned(Value::Object(value)),
            })
        }
    }
    fn closure<'a>(
        &'a self,
        path: &'a str,
        values: impl IntoIterator<Item = &'a Value>,
    ) -> Result<BTreeMap<String, SchemaDependency>, Error> {
        let mut pending: Vec<_> = values.into_iter().map(|value| (path, value)).collect();
        let mut result = BTreeMap::new();
        let mut visited = 0usize;
        while let Some((source, value)) = pending.pop() {
            visited += 1;
            if visited > self.limits.closure_nodes {
                return Err(Error::Limit("reference closure node budget"));
            }
            match value {
                Value::Object(object) => {
                    if let Some(reference) = object.get("$ref") {
                        let target = self.target(
                            source,
                            reference
                                .as_str()
                                .ok_or(Error::Invalid("non-string reference"))?,
                        )?;
                        let key = format!("{}#{}", target.path, target.pointer);
                        if !result.contains_key(&key) {
                            if result.len() >= self.limits.refs {
                                return Err(Error::Limit("reference closure budget"));
                            }
                            result.insert(
                                key,
                                SchemaDependency {
                                    path: target.path.to_owned(),
                                    pointer: target.pointer,
                                    identity: hash_json(target.value)?,
                                    source_sha256: self.docs[target.path].sha256,
                                },
                            );
                            pending.push((target.path, target.value));
                        }
                        pending.extend(
                            object
                                .iter()
                                .filter(|(key, _)| key.as_str() != "$ref")
                                .map(|(_, child)| (source, child)),
                        );
                    } else {
                        pending.extend(object.values().map(|child| (source, child)));
                    }
                }
                Value::Array(values) => pending.extend(values.iter().map(|child| (source, child))),
                _ => {}
            }
        }
        Ok(result)
    }
    pub fn operations(&self) -> Result<Vec<SchemaOperation>, Error> {
        self.operations_impl(true)
    }
    /// Static endpoint binding needs wire metadata and resolved operation roots,
    /// while component payload dependencies are required only for delta proofs.
    /// The returned fingerprint must not be used as a complete delta identity.
    pub fn binding_operations(&self) -> Result<Vec<SchemaOperation>, Error> {
        self.operations_impl(false)
    }
    fn operations_impl(&self, require_dependencies: bool) -> Result<Vec<SchemaOperation>, Error> {
        let mut result = Vec::new();
        for (schema_path, document) in &self.docs {
            if !document.root {
                continue;
            }
            let mut ids = BTreeSet::new();
            let Some(paths) = document.value.get("paths").and_then(Value::as_object) else {
                continue;
            };
            for (path, raw_item) in paths {
                if !path.starts_with('/') {
                    return Err(Error::Invalid("OpenAPI route must begin with slash"));
                }
                let item = self.root(schema_path, raw_item)?;
                let object = item
                    .value
                    .as_object()
                    .ok_or(Error::Invalid("OpenAPI path-item mapping"))?;
                let common: Map<_, _> = object
                    .iter()
                    .filter(|(key, _)| !HTTP.contains(&key.as_str()))
                    .map(|(key, value)| (key.clone(), value.clone()))
                    .collect();
                for &verb in HTTP {
                    let Some(raw_operation) = object.get(verb) else {
                        continue;
                    };
                    let operation = self.root(item.path, raw_operation)?;
                    let fields = operation
                        .value
                        .as_object()
                        .ok_or(Error::Invalid("OpenAPI operation mapping"))?;
                    if fields.get("callbacks").is_some_and(truthy) {
                        return Err(Error::Invalid("OpenAPI callbacks not supported"));
                    }
                    let operation_id = fields
                        .get("operationId")
                        .and_then(Value::as_str)
                        .ok_or(Error::Invalid("missing OpenAPI operationId"))?;
                    if !ids.insert(operation_id.to_owned()) {
                        return Err(Error::Invalid("duplicate OpenAPI operationId"));
                    }
                    let tags = match fields.get("tags") {
                        None => Vec::new(),
                        Some(Value::Array(tags)) => tags
                            .iter()
                            .map(|tag| {
                                tag.as_str()
                                    .map(str::to_owned)
                                    .ok_or(Error::Invalid("OpenAPI tag string"))
                            })
                            .collect::<Result<_, _>>()?,
                        _ => return Err(Error::Invalid("OpenAPI tags array")),
                    };
                    let namespace = match fields.get("x-jvm-package") {
                        None | Some(Value::Null) => None,
                        Some(Value::String(value)) => Some(value.clone()),
                        _ => return Err(Error::Invalid("OpenAPI JVM namespace string")),
                    };
                    let server_values = fields
                        .get("servers")
                        .or_else(|| object.get("servers"))
                        .or_else(|| document.value.get("servers"));
                    let server_urls = server_urls(server_values)?;
                    let mut dependencies = if require_dependencies {
                        self.closure(item.path, common.values())?
                    } else {
                        BTreeMap::new()
                    };
                    if require_dependencies {
                        dependencies
                            .extend(self.closure(operation.path, [operation.value.as_ref()])?);
                    }
                    if dependencies.len() > self.limits.refs {
                        return Err(Error::Limit("operation reference closure budget"));
                    }
                    let refs: BTreeMap<_, _> = dependencies
                        .iter()
                        .map(|(key, value)| (key.as_str(), value.identity.to_string()))
                        .collect();
                    #[derive(Serialize)]
                    struct Fingerprint<'a> {
                        operation: &'a Value,
                        path_item: &'a Map<String, Value>,
                        refs: &'a BTreeMap<&'a str, String>,
                    }
                    let fingerprint = hash_json(&Fingerprint {
                        operation: &operation.value,
                        path_item: &common,
                        refs: &refs,
                    })?;
                    result.push(SchemaOperation {
                        schema_path: schema_path.clone(),
                        path: path.clone(),
                        verb: verb.to_owned(),
                        operation_id: operation_id.to_owned(),
                        tags,
                        namespace,
                        server_urls,
                        fingerprint,
                        schema_sha256: document.sha256,
                        dependencies: dependencies.into_values().collect(),
                        dependencies_complete: require_dependencies,
                    });
                }
            }
        }
        result.sort_unstable_by(|a, b| {
            (&a.schema_path, &a.path, &a.verb).cmp(&(&b.schema_path, &b.path, &b.verb))
        });
        Ok(result)
    }
    pub fn diff(&self, after: &Self, changed_paths: &[&str]) -> Result<SchemaDiff, Error> {
        for &path in changed_paths {
            let before = self.docs.get(path).ok_or(Error::Invalid(
                "added or removed schema requires full selection",
            ))?;
            let after = after.docs.get(path).ok_or(Error::Invalid(
                "added or removed schema requires full selection",
            ))?;
            if before.root != after.root {
                return Err(Error::Invalid("changed OpenAPI root identity"));
            }
            if !before.root {
                continue;
            }
            let top = |value: &Value| -> Result<ContentHash, Error> {
                let values: BTreeMap<_, _> = value
                    .as_object()
                    .ok_or(Error::Invalid("schema mapping"))?
                    .iter()
                    .filter(|(key, _)| !matches!(key.as_str(), "paths" | "components"))
                    .collect();
                hash_json(&values)
            };
            if top(&before.value)? != top(&after.value)? {
                return Err(Error::Invalid(
                    "top-level server/security/generator change requires full selection",
                ));
            }
            if before
                .value
                .get("components")
                .and_then(|value| value.get("securitySchemes"))
                != after
                    .value
                    .get("components")
                    .and_then(|value| value.get("securitySchemes"))
            {
                return Err(Error::Invalid(
                    "security scheme change requires full selection",
                ));
            }
        }
        let before = self.operations()?;
        let all = after.operations()?;
        fn key(value: &SchemaOperation) -> (&str, &str, &str) {
            (&value.schema_path, &value.path, &value.verb)
        }
        for old in &before {
            if all
                .binary_search_by(|value| key(value).cmp(&key(old)))
                .is_err()
            {
                return Err(Error::Invalid("removed operation requires full selection"));
            }
        }
        let mut changed = Vec::new();
        for value in &all {
            let old = before
                .binary_search_by(|old| key(old).cmp(&key(value)))
                .ok()
                .map(|index| &before[index]);
            if old.is_none_or(|old| old.fingerprint != value.fingerprint) {
                if old.is_some_and(|old| {
                    old.operation_id != value.operation_id
                        || old.tags != value.tags
                        || old.namespace != value.namespace
                }) {
                    return Err(Error::Invalid("changed operation binding identity"));
                }
                changed.push(value.clone());
            }
        }
        if !changed_paths.is_empty() && changed.is_empty() {
            return Err(Error::Invalid(
                "schema change without bound operation effect",
            ));
        }
        Ok(SchemaDiff { changed, all })
    }
}
fn truthy(value: &Value) -> bool {
    match value {
        Value::Null => false,
        Value::Bool(value) => *value,
        Value::String(value) => !value.is_empty(),
        Value::Array(value) => !value.is_empty(),
        Value::Object(value) => !value.is_empty(),
        Value::Number(_) => true,
    }
}
fn server_urls(value: Option<&Value>) -> Result<Vec<String>, Error> {
    match value {
        None => Ok(Vec::new()),
        Some(Value::Array(values)) => values
            .iter()
            .map(|value| {
                value
                    .get("url")
                    .and_then(Value::as_str)
                    .map(str::to_owned)
                    .ok_or(Error::Invalid("OpenAPI server URL string"))
            })
            .collect(),
        _ => Err(Error::Invalid("OpenAPI servers array")),
    }
}
fn normalize_path(parent: &str, relative: &str) -> Result<String, Error> {
    if relative.starts_with('/') || relative.contains([':', '\\', '\0']) {
        return Err(Error::Invalid("absolute schema path"));
    }
    let mut parts: Vec<_> = parent.split('/').filter(|part| !part.is_empty()).collect();
    for part in relative.split('/') {
        match part {
            "" | "." => {}
            ".." => {
                parts
                    .pop()
                    .ok_or(Error::Invalid("reference escapes repository"))?;
            }
            part => parts.push(part),
        }
    }
    if parts.is_empty() {
        return Err(Error::Invalid("empty schema path"));
    }
    Ok(parts.join("/"))
}
fn percent_decode(value: &str) -> Result<String, Error> {
    let mut result = Vec::with_capacity(value.len());
    let bytes = value.as_bytes();
    let mut at = 0;
    let hex = |byte: u8| match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    };
    while at < bytes.len() {
        if bytes[at] == b'%' {
            let a = *bytes
                .get(at + 1)
                .ok_or(Error::Invalid("reference percent escape"))?;
            let b = *bytes
                .get(at + 2)
                .ok_or(Error::Invalid("reference percent escape"))?;
            result.push(
                hex(a)
                    .zip(hex(b))
                    .map(|(a, b)| a * 16 + b)
                    .ok_or(Error::Invalid("reference percent escape"))?,
            );
            at += 3;
        } else {
            result.push(bytes[at]);
            at += 1;
        }
    }
    String::from_utf8(result).map_err(|_| Error::Invalid("reference UTF-8"))
}
fn pointer_key(value: &str) -> Result<String, Error> {
    let mut result = String::with_capacity(value.len());
    let mut chars = value.chars();
    while let Some(character) = chars.next() {
        if character == '~' {
            result.push(match chars.next() {
                Some('0') => '~',
                Some('1') => '/',
                _ => return Err(Error::Invalid("JSON pointer escape")),
            });
        } else {
            result.push(character);
        }
    }
    Ok(result)
}
fn hash_json(value: &impl Serialize) -> Result<ContentHash, Error> {
    struct Hash<'a>(&'a mut Sha256);
    impl Write for Hash<'_> {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            self.0.update(bytes);
            Ok(bytes.len())
        }
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }
    let mut hash = Sha256::new();
    serde_json::to_writer(Hash(&mut hash), value)
        .map_err(|error| Error::Message(error.to_string()))?;
    Ok(ContentHash(hash.finalize().into()))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn source<'a>(path: &'a str, text: &'a str) -> RuntimeSource<'a> {
        RuntimeSource { path, text }
    }
    const ROOT: &str = "openapi: 3.0.3\npaths:\n  /offer:\n    post:\n      operationId: acceptOffer\n      tags: [wallet, public]\n      x-jvm-package: wallet\n      responses:\n        '200':\n          description: ok\n          content:\n            application/json:\n              schema:\n                $ref: 'common.yaml#/components/schemas/Node'\n";
    const COMMON: &str = "components:\n  schemas:\n    Node:\n      type: object\n      properties:\n        next:\n          $ref: '#/components/schemas/Node'\n";
    #[test]
    fn strict_yaml_rejects_duplicate_normalized_merge_alias_tag_and_depth() {
        for text in [
            "openapi: 3.0.3\npaths: {}\npaths: {}\n",
            "openapi: 3.0.3\npaths: {1: {}, '1': {}}\n",
            "openapi: 3.0.3\npaths: {<<: {}}\n",
            "openapi: 3.0.3\nx: &x {}\npaths: *x\n",
            "openapi: 3.0.3\npaths: !!map {}\n",
            "openapi: 3.0.3\npaths: {}\n---\nopenapi: 3.0.3\npaths: {}\n",
        ] {
            assert!(
                yaml_document(text, SchemaLimits::default()).is_err(),
                "{text}"
            );
        }
        assert!(
            yaml_document(
                "openapi: 3.0.3\nx: &unused {nested: value}\npaths: {}\n",
                SchemaLimits::default()
            )
            .is_ok()
        );
        assert!(
            yaml_document(
                "openapi: 3.0.3\npaths: {a: {b: {c: {d: {}}}}}\n",
                SchemaLimits {
                    depth: 3,
                    ..SchemaLimits::default()
                }
            )
            .is_err()
        );
        assert!(
            yaml_document(
                "openapi: 3.0.3\npaths: {}",
                SchemaLimits {
                    document_bytes: 4,
                    ..SchemaLimits::default()
                }
            )
            .is_err()
        );
    }
    #[test]
    fn cyclic_models_are_hashed_once_and_multi_tags_are_retained() {
        let tree = SchemaTree::new(&[
            source("api/root.yaml", ROOT),
            source("api/common.yaml", COMMON),
        ])
        .unwrap();
        let operations = tree.operations().unwrap();
        assert_eq!(operations.len(), 1);
        let operation = &operations[0];
        assert_eq!(operation.operation_id, "acceptOffer");
        assert_eq!(operation.tags, ["wallet", "public"]);
        assert_eq!(operation.namespace.as_deref(), Some("wallet"));
        assert_eq!(operation.dependencies.len(), 1);
        assert_eq!(operation.dependencies[0].path, "api/common.yaml");
        assert_eq!(
            operation.dependencies[0].pointer,
            "/components/schemas/Node"
        );
        let changed = COMMON.replace("type: object", "type: string");
        let after = SchemaTree::new(&[
            source("api/root.yaml", ROOT),
            source("api/common.yaml", &changed),
        ])
        .unwrap();
        assert_ne!(
            operation.fingerprint,
            after.operations().unwrap()[0].fingerprint
        );
        assert_eq!(
            tree.diff(&after, &["api/common.yaml"])
                .unwrap()
                .changed
                .len(),
            1
        );
    }
    #[test]
    fn static_binding_can_omit_payload_projection_but_never_root_reference_admission() {
        let tree = SchemaTree::new(&[source("api/root.yaml", ROOT)]).unwrap();
        assert!(tree.operations().is_err());
        let bindings = tree.binding_operations().unwrap();
        assert_eq!(bindings.len(), 1);
        assert!(!bindings[0].dependencies_complete);
        assert!(bindings[0].dependencies.is_empty());
        assert!(tree.diff(&tree, &[]).is_err());
        let missing = "openapi: 3.0.3\npaths:\n  /offer:\n    $ref: 'missing.yaml#/path'\n";
        assert!(
            SchemaTree::new(&[source("api/root.yaml", missing)])
                .unwrap()
                .binding_operations()
                .is_err()
        );
    }
    #[test]
    fn imported_path_operation_and_relative_refs_use_imported_document_context() {
        let root = "openapi: 3.0.3\nservers: [{url: 'https://host/api'}]\npaths:\n  /offer:\n    $ref: 'shared/path.yaml#/x-path'\n    description: outer\n";
        let shared = "x-path:\n  post:\n    $ref: 'operation.yaml#/x-op'\n";
        let operation = "x-op:\n  operationId: acceptOffer\n  responses:\n    '200':\n      $ref: 'models.yaml#/response'\n";
        let models = "response:\n  description: nested\n";
        let tree = SchemaTree::new(&[
            source("api/root.yaml", root),
            source("api/shared/path.yaml", shared),
            source("api/shared/operation.yaml", operation),
            source("api/shared/models.yaml", models),
        ])
        .unwrap();
        let operations = tree.operations().unwrap();
        assert_eq!(operations.len(), 1);
        assert_eq!(operations[0].dependencies[0].path, "api/shared/models.yaml");
        assert_eq!(operations[0].server_urls, ["https://host/api"]);
    }
    #[test]
    fn behavioral_siblings_and_recursive_operation_roots_fail_closed() {
        for shared in [
            "x-path:\n  $ref: '#/x-path'\n",
            "x-path:\n  post:\n    $ref: '#/x-op'\nx-op:\n  $ref: '#/x-op'\n",
        ] {
            let root = "openapi: 3.0.3\npaths:\n  /offer:\n    $ref: 'shared.yaml#/x-path'\n";
            assert!(
                SchemaTree::new(&[
                    source("api/root.yaml", root),
                    source("api/shared.yaml", shared)
                ])
                .unwrap()
                .operations()
                .is_err()
            );
        }
        let root = "openapi: 3.0.3\npaths:\n  /offer:\n    $ref: 'shared.yaml#/x-path'\n    parameters: []\n";
        assert!(
            SchemaTree::new(&[
                source("api/root.yaml", root),
                source("api/shared.yaml", "x-path: {}\n")
            ])
            .unwrap()
            .operations()
            .is_err()
        );
    }
    #[test]
    fn references_reject_external_escape_queries_and_invalid_json_pointers() {
        for reference in [
            "https://host/model.yaml#/Node",
            "/model.yaml#/Node",
            "../../model.yaml#/Node",
            "%2Fmodel.yaml#/Node",
            "common.yaml?query=1#/Node",
            "common.yaml#not-a-pointer",
            "common.yaml#/components/schemas/Bad~2Node",
        ] {
            let root = ROOT.replace("common.yaml#/components/schemas/Node", reference);
            assert!(
                SchemaTree::new(&[
                    source("api/root.yaml", &root),
                    source("api/common.yaml", COMMON)
                ])
                .unwrap()
                .operations()
                .is_err(),
                "{reference}"
            );
        }
        let root = ROOT.replace(
            "common.yaml#/components/schemas/Node",
            "common.yaml#/components/schemas/A~1B~0C",
        );
        let common = "components:\n  schemas:\n    'A/B~C': {type: string}\n";
        assert!(
            SchemaTree::new(&[
                source("api/root.yaml", &root),
                source("api/common.yaml", common)
            ])
            .unwrap()
            .operations()
            .is_ok()
        );
    }
    #[test]
    fn diff_keeps_security_removed_operations_and_unbound_changes_broad() {
        let before = SchemaTree::new(&[
            source("api/root.yaml", ROOT),
            source("api/common.yaml", COMMON),
        ])
        .unwrap();
        let root = format!("{ROOT}servers: [{{url: 'https://host/api'}}]\n");
        let after = SchemaTree::new(&[
            source("api/root.yaml", &root),
            source("api/common.yaml", COMMON),
        ])
        .unwrap();
        assert!(before.diff(&after, &["api/root.yaml"]).is_err());
        let after = SchemaTree::new(&[
            source("api/root.yaml", "openapi: 3.0.3\npaths: {}\n"),
            source("api/common.yaml", COMMON),
        ])
        .unwrap();
        assert!(before.diff(&after, &["api/root.yaml"]).is_err());
        let common = format!("{COMMON}x-unreferenced: updated\n");
        let after = SchemaTree::new(&[
            source("api/root.yaml", ROOT),
            source("api/common.yaml", &common),
        ])
        .unwrap();
        assert!(before.diff(&after, &["api/common.yaml"]).is_err());
        let root = ROOT.replace("operationId: acceptOffer", "operationId: renamedOffer");
        let after = SchemaTree::new(&[
            source("api/root.yaml", &root),
            source("api/common.yaml", COMMON),
        ])
        .unwrap();
        assert!(before.diff(&after, &["api/root.yaml"]).is_err());
    }
    #[test]
    fn duplicate_operations_callbacks_and_reference_budget_are_explicit() {
        let root = format!("{ROOT}  /other:\n    get:\n      operationId: acceptOffer\n");
        assert!(
            SchemaTree::new(&[
                source("api/root.yaml", &root),
                source("api/common.yaml", COMMON)
            ])
            .unwrap()
            .operations()
            .is_err()
        );
        let root = ROOT.replace(
            "operationId: acceptOffer",
            "operationId: acceptOffer\n      callbacks: {unknown: {}}",
        );
        assert!(
            SchemaTree::new(&[
                source("api/root.yaml", &root),
                source("api/common.yaml", COMMON)
            ])
            .unwrap()
            .operations()
            .is_err()
        );
        assert!(
            SchemaTree::with_limits(
                &[
                    source("api/root.yaml", ROOT),
                    source("api/common.yaml", COMMON)
                ],
                SchemaLimits {
                    refs: 0,
                    ..SchemaLimits::default()
                }
            )
            .unwrap()
            .operations()
            .is_err()
        );
    }
}
