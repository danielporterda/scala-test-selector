//! Stateful, pinned synchronous WordSpec protocol recipes.
//!
//! The model owns only registry channels; these are not JVM fields/classes.
//! Application initialization, real wrapper construction and virtual accessors
//! remain ordinary recipes. Partial outward boundaries remain explicit Unknown.
use super::*;
use selector_framework::scalatest_execution::{self as contract, Recipe};
use selector_models::binary::{
    BinaryValueId as V, Call, ClassFile, FieldWrite, InvokeKind, MethodInfo, MethodSummary, Value,
    ValueRange,
};

const STATE: &str = "@selector:model/scalatest/wordspec-registry";
const CHANNELS: &[&str] = &[
    "payloads",
    "scopes",
    "names",
    "tags",
    "metadata",
    "engine-input",
];
const OBJECT: &str = "Ljava/lang/Object;";
pub(super) fn candidate(owner: &str, name: &str, descriptor: &str) -> bool {
    contract::lookup(owner, name, descriptor).is_some()
}

/// Source metadata conflict scopes, indexed once before derived native issues.
/// The model never treats a conflicted scope as fresh compiler authority.
pub(super) struct Conflicts {
    rows: Vec<(SymbolId, FileId)>,
}
impl Conflicts {
    pub(super) fn new(facts: &FactSnapshot) -> Self {
        Self {
            rows: facts
                .issues
                .iter()
                .filter(|issue| issue.kind == IssueKind::ContextConflict)
                .map(|issue| (issue.symbol, issue.file))
                .collect(),
        }
    }
    fn relevant(
        &self,
        facts: &FactSnapshot,
        context: StrId,
        method: SymbolId,
        owner: SymbolId,
    ) -> bool {
        let method_file = facts.symbols[method.index()].file;
        let owner_file = facts.symbols[owner.index()].file;
        self.rows.iter().any(|&(symbol, file)| {
            if symbol == method || symbol == owner {
                return true;
            }
            if symbol.is_none() {
                return file.is_none()
                    || facts.files.get(file.index()).is_none_or(|record| {
                        record.context.is_none() || record.context == context
                    });
            }
            !file.is_none() && (file == method_file || file == owner_file)
        })
    }
}

pub(super) struct Model<'a> {
    pub summary: MethodSummary<'a>,
    pub body_hash: ContentHash,
}
fn state(name: &'static str) -> MemberRef<'static> {
    MemberRef {
        owner: STATE,
        name,
        descriptor: OBJECT,
    }
}
fn hash(bytes: &[u8]) -> ContentHash {
    ContentHash(Sha256::digest(bytes).into())
}

/// Only called after ordinary ordered classpath admission. It does not load a
/// different provider, infer absence, or install a model on a source override.
fn matched<'a>(
    facts: &FactSnapshot,
    conflicts: &Conflicts,
    context: &AdmittedContext,
    data: &MethodData,
    bytes: &ClassBytes,
    class: &ClassFile<'a>,
    method: &MethodInfo<'a>,
) -> Option<Model<'a>> {
    let spec = contract::lookup(class.name, method.name, method.descriptor)?;
    let symbol = facts.symbols.get(data.symbol.index())?;
    let owner = facts.symbols.get(data.owner.index())?;
    if conflicts.relevant(facts, context.id, data.symbol, data.owner) {
        return None;
    }
    if owner.context != context.id || owner.flags & SYMBOL_DEFINED != 0 {
        return None;
    }
    // The admitted trait initializer may deliberately use its compiler CLASS
    // endpoint, with the trait instance supplied as static argument zero.
    // Ordinary methods still require their exact declaring owner.
    let initializer_class_endpoint = spec.recipe == Recipe::Initialize
        && data.receiver_parameter == Some(0)
        && data.symbol == data.owner;
    if symbol.flags & SYMBOL_DEFINED != 0
        || symbol.context != context.id
        || (symbol.owner != data.owner && !initializer_class_endpoint)
        || data
            .receiver_parameter
            .is_some_and(|p| p != 0 || spec.recipe != Recipe::Initialize)
        || data.flags != method.flags
        || bytes.metadata.hash() != bytes.hash
        || bytes.metadata.name() != class.name
        || hash(&bytes.bytes) != bytes.hash
    {
        return None;
    }
    let selected = context.entries.iter().position(|entry| {
        matches!(entry.kind, EntryKind::Jar)
            && bytes.origin == format!("{}!/{name}.class", entry.path.display(), name = class.name)
    })?;
    if context.entries[..selected]
        .iter()
        .any(|entry| matches!(entry.kind, EntryKind::Unavailable))
    {
        return None;
    }
    if !spec.matches(
        context.entries[selected].sha256,
        bytes.hash,
        hash(method.code?),
        method.flags,
    ) {
        return None;
    }
    // A detached/mutated MethodInfo cannot inherit a valid class pin.
    let actual = class.method(method.name, Some(method.descriptor)).ok()?;
    if (
        actual.max_stack,
        actual.max_locals,
        actual.exception_handlers,
        actual.exception_table,
        actual.code,
    ) != (
        method.max_stack,
        method.max_locals,
        method.exception_handlers,
        method.exception_table,
        method.code,
    ) {
        return None;
    }
    let summary = match spec.recipe {
        Recipe::Initialize => initializer(class, method)?,
        role => protocol(method.descriptor, role)?,
    };
    let mut seal = Sha256::new();
    seal.update(contract::VERSION);
    seal.update(SelectionContract::VERSION);
    seal.update(SelectionContract::CURRENT_BASE_BITS.to_le_bytes());
    seal.update(bytes.hash.0);
    seal.update(context.entries[selected].sha256.0);
    seal.update(method.name.as_bytes());
    seal.update(method.descriptor.as_bytes());
    seal.update(hash(method.code?).0);
    Some(Model {
        summary,
        body_hash: ContentHash(seal.finalize().into()),
    })
}

/// Bind only a member introduced by the admitted recipe. The caller must never
/// use this lane for an ordinary native/source summary. Flags deliberately do
/// not claim SYMBOL_NATIVE_BINARY: the channel has no JVM backing field.
pub(super) fn field(
    facts: &mut FactSnapshot,
    registry: &mut Registry,
    context_index: usize,
    context: StrId,
    _file: FileId,
    member: MemberRef<'_>,
) -> Result<Option<SymbolId>, Error> {
    if member.owner != STATE || member.descriptor != OBJECT || !CHANNELS.contains(&member.name) {
        return Ok(None);
    }
    let key = MethodKey {
        context: context_index,
        owner: STATE.into(),
        name: member.name.into(),
        // This cache key is deliberately not a valid JVM field descriptor;
        // a real admitted native member cannot collide with model state.
        descriptor: "@selector:model-field-cache/1".into(),
    };
    if let Some(&id) = registry.fields.get(&key) {
        return Ok(Some(id));
    }
    let name = append_text(facts, &format!("{STATE}:{}", member.name))?;
    let id = SymbolId::checked(facts.symbols.len())?;
    facts.symbols.push(SymbolRecord {
        name,
        display: StrId::NONE,
        owner: SymbolId::NONE,
        file: FileId::NONE,
        context,
        kind: 20,
        properties: 0,
        signature: StrId::NONE,
        span: Span::default(),
        flags: 0,
    });
    registry.fields.insert(key, id);
    Ok(Some(id))
}

const CORE_ARCHIVE: &str = "30230081d029f6341b83fe7f157d336113e1c97497fe950169293d28a5bf2936";
const OWNED_IMPLEMENTATION: &[(&str, &str)] = &[
    (
        "org/scalatest/Engine",
        "b26797c52219220c24d310dff3623c303f811e89bc3c8943ac58fbd9c1605d4a",
    ),
    (
        "org/scalatest/SuperEngine",
        "82e64009083e453349ab527dd758242a3e55386e8b2460c76e78ab69978a1f97",
    ),
    (
        "org/scalatest/Transformer",
        "40816b929af931a08f7e531b68fd723dd0bbfd5eeedfb20265f557b3e2cf6bc6",
    ),
];
/// The reviewed boundary replaces implementation classes only when the normal
/// ordered native loader selects the pinned core provider for each one. An
/// earlier opaque/changed provider leaves the original native recipe in place.
pub(super) fn model<'a>(
    facts: &FactSnapshot,
    conflicts: &Conflicts,
    context: &mut AdmittedContext,
    loader: &mut CapturedClasspath,
    data: &MethodData,
    bytes: &ClassBytes,
    class: &ClassFile<'a>,
    method: &MethodInfo<'a>,
) -> Result<Option<Model<'a>>, Error> {
    let Some(model) = matched(facts, conflicts, context, data, bytes, class, method) else {
        return Ok(None);
    };
    for &(owner, expected) in OWNED_IMPLEMENTATION {
        let bytes = match cache_class(context, loader, owner) {
            Ok(Some(bytes)) => bytes,
            Ok(None) | Err(Error::Limit(_)) => return Ok(None),
            Err(error) => return Err(error),
        };
        if !ContentHash::from_hex(expected).is_ok_and(|h| h == bytes.hash)
            || !context.entries.iter().any(|entry| {
                matches!(entry.kind, EntryKind::Jar)
                    && ContentHash::from_hex(CORE_ARCHIVE).is_ok_and(|h| h == entry.sha256)
                    && bytes.origin == format!("{}!/{owner}.class", entry.path.display())
            })
        {
            return Ok(None);
        }
        // The protocol omits Engine construction plumbing, including the NEW
        // initialization trigger. These exact pinned classes have no initializer
        // or interface initialization work to erase.
        if let Some(parent) = match owner {
            "org/scalatest/Engine" => Some("org/scalatest/SuperEngine"),
            "org/scalatest/SuperEngine" => Some("java/lang/Object"),
            _ => None,
        } {
            if bytes.metadata.parent() != Some(parent)
                || bytes.metadata.interfaces().len() != 0
                || bytes
                    .metadata
                    .methods()
                    .any(|method| method.name == "<clinit>")
            {
                return Ok(None);
            }
        }
    }
    Ok(Some(model))
}

fn initializer<'a>(class: &ClassFile<'a>, method: &MethodInfo<'a>) -> Option<MethodSummary<'a>> {
    let mut summary = binary::summarize(class, method, Limits::default());
    if !summary.complete() || !summary.unknown_offsets.is_empty() {
        return None;
    }
    let engine = summary.calls.iter().position(|call| {
        call.offset == 13
            && call.kind == InvokeKind::Special
            && call.member.owner == "org/scalatest/Engine"
            && call.member.name == "<init>"
            && call.member.descriptor == "(Lscala/Function0;Ljava/lang/String;)V"
    })?;
    let call = summary.calls[engine];
    let args = summary.arguments.get(call.arguments.range())?;
    let engine_input = *args.first()?;
    let allocation = call.receiver?;
    if !matches!(summary.values.get(allocation.0 as usize), Some(Value::Allocation { class: "org/scalatest/Engine", constructor: Some(index), .. }) if *index as usize == engine)
    {
        return None;
    }
    summary.values[allocation.0 as usize] = Value::UnknownData;
    summary.calls.remove(engine);
    for value in &mut summary.values {
        match value {
            Value::CallResult(index)
            | Value::Allocation {
                constructor: Some(index),
                ..
            } => {
                if *index as usize == engine {
                    return None;
                }
                if *index as usize > engine {
                    *index -= 1;
                }
            }
            _ => (),
        }
    }
    // The framework-generated engine callback is retained as data, never lost
    // along with the private Engine constructor. All 8 real setter calls and
    // every other original allocation/call/lambda retain their ordering.
    let empty = V(summary.values.len() as u32);
    summary.values.push(Value::Null);
    summary.value_offsets.push(0);
    let receiver = summary
        .values
        .iter()
        .position(|v| *v == Value::Argument(0))
        .map(|i| V(i as u32))?;
    for &name in CHANNELS {
        summary.field_writes.push(FieldWrite {
            member: state(name),
            receiver: Some(receiver),
            value: empty,
            offset: 0,
        });
    }
    summary.field_writes.push(FieldWrite {
        member: state("engine-input"),
        receiver: Some(receiver),
        value: engine_input,
        offset: 6,
    });
    Some(summary)
}

struct Builder<'a> {
    summary: MethodSummary<'a>,
    args: Vec<V>,
    next: u32,
}
impl<'a> Builder<'a> {
    fn new(descriptor: &'a str) -> Option<Self> {
        let parameters = binary::method_descriptor(descriptor).ok()?.parameter_count;
        let mut values = vec![Value::Receiver];
        let args: Vec<_> = (0..parameters)
            .map(|i| {
                let id = V(values.len() as u32);
                values.push(Value::Argument(i as u16));
                id
            })
            .collect();
        Some(Self {
            summary: MethodSummary {
                descriptor,
                value_offsets: vec![0; values.len()],
                values,
                calls: Vec::new(),
                arguments: Vec::new(),
                field_writes: Vec::new(),
                lambdas: Vec::new(),
                unknown_offsets: Vec::new(),
                returned: None,
                unknown: None,
                envelope: None,
            },
            args,
            next: 1,
        })
    }
    fn value(&mut self, value: Value<'a>) -> V {
        let id = V(self.summary.values.len() as u32);
        self.summary.values.push(value);
        self.summary.value_offsets.push(self.next);
        id
    }
    fn opaque(&mut self) -> V {
        self.value(Value::UnknownData)
    }
    fn read(&mut self, name: &'static str) -> V {
        self.value(Value::Field {
            member: state(name),
            receiver: V(0),
        })
    }
    fn write(&mut self, name: &'static str, value: V) {
        self.summary.field_writes.push(FieldWrite {
            member: state(name),
            receiver: Some(V(0)),
            value,
            offset: self.next,
        });
        self.next += 1;
    }
    fn call(
        &mut self,
        owner: &'static str,
        name: &'static str,
        descriptor: &'static str,
        receiver: V,
        arguments: &[V],
    ) -> V {
        let start = self.summary.arguments.len() as u32;
        self.summary.arguments.extend_from_slice(arguments);
        let index = self.summary.calls.len() as u32;
        self.summary.calls.push(Call {
            member: MemberRef {
                owner,
                name,
                descriptor,
            },
            kind: if matches!(owner, "scala/Function0" | contract::WORDSPEC) {
                InvokeKind::Interface
            } else {
                InvokeKind::Virtual
            },
            receiver: Some(receiver),
            arguments: ValueRange {
                start,
                len: arguments.len() as u32,
            },
            offset: self.next,
        });
        self.next += 1;
        self.value(Value::CallResult(index))
    }
    fn callback(&mut self, callback: V) -> V {
        self.call(
            "scala/Function0",
            "apply",
            "()Ljava/lang/Object;",
            callback,
            &[],
        )
    }
    fn metadata(&mut self) {
        let start = self.summary.arguments.len() as u32;
        self.summary.arguments.extend_from_slice(&self.args);
        let meta = self.value(Value::Alternatives(ValueRange {
            start,
            len: self.args.len() as u32,
        }));
        self.write("metadata", meta);
    }
    fn open(&mut self) {
        self.summary.unknown_offsets.push(self.next);
        self.next += 1;
    }
}
fn protocol(descriptor: &str, role: Recipe) -> Option<MethodSummary<'_>> {
    let mut b = Builder::new(descriptor)?;
    if !matches!(role, Recipe::Initialize | Recipe::OpaqueEngineInput) {
        // Keep the original outward accessor dispatch. The normal accessor law
        // handles the library declaration; an application override remains an
        // ordinary virtual call with its own effects.
        b.call(
            contract::WORDSPEC,
            "org$scalatest$wordspec$AnyWordSpecLike$$engine",
            "()Lorg/scalatest/Engine;",
            V(0),
            &[],
        );
    }
    match role {
        Recipe::OpaqueEngineInput => {
            // The private diagnostic callback stays callable and explicitly open.
            // Creation does not force its resource/formatting implementation.
            b.open();
            let result = b.opaque();
            b.summary.returned = Some(result);
        }
        Recipe::Register { callback } => {
            let callback = *b.args.get(callback as usize)?;
            b.write("names", *b.args.first()?);
            b.write("tags", *b.args.get(1)?);
            b.metadata();
            b.write("payloads", callback);
            b.callback(callback);
            // Tag/custom dynamic registration/error-reporting execution is not
            // certified empty by a function-slot certificate.
            b.open();
        }
        Recipe::Scope { callback } => {
            let callback = *b.args.get(callback as usize)?;
            b.write("names", *b.args.first()?);
            b.metadata();
            b.write("scopes", callback);
            b.callback(callback);
            // Catch/reporting paths can invoke an application's Throwable method.
            let exception = b.opaque();
            b.call(
                "java/lang/Throwable",
                "getMessage",
                "()Ljava/lang/String;",
                exception,
                &[],
            );
            b.open();
        }
        Recipe::Names => {
            b.read("names");
            b.read("metadata");
            let result = b.opaque();
            b.summary.returned = Some(result);
        }
        Recipe::Tags | Recipe::TestData => {
            b.read("names");
            b.read("tags");
            b.read("metadata");
            // Class annotations and a custom TestData/configuration view remain
            // an explicit open boundary, not an empty tags map or fake class.
            b.open();
            let result = b.opaque();
            b.summary.returned = Some(result);
        }
        Recipe::Run | Recipe::RunTests | Recipe::RunTest => {
            let payloads = b.read("payloads");
            b.read("names");
            b.read("tags");
            b.read("metadata");
            b.callback(payloads);
            let a = *b.args.first()?;
            let args = *b.args.get(1)?;
            match role {
                Recipe::Run => {
                    b.call(
                        contract::WORDSPEC,
                        "org$scalatest$wordspec$AnyWordSpecLike$$super$run",
                        "(Lscala/Option;Lorg/scalatest/Args;)Lorg/scalatest/Status;",
                        V(0),
                        &[a, args],
                    );
                }
                Recipe::RunTests => {
                    b.call(
                        contract::WORDSPEC,
                        "info",
                        "()Lorg/scalatest/Informer;",
                        V(0),
                        &[],
                    );
                    let name = b.opaque();
                    b.call(
                        contract::WORDSPEC,
                        "runTest",
                        "(Ljava/lang/String;Lorg/scalatest/Args;)Lorg/scalatest/Status;",
                        V(0),
                        &[name, args],
                    );
                }
                Recipe::RunTest => {
                    let config = b.call(
                        "org/scalatest/Args",
                        "configMap",
                        "()Lorg/scalatest/ConfigMap;",
                        args,
                        &[],
                    );
                    b.call(
                        contract::WORDSPEC,
                        "testDataFor",
                        "(Ljava/lang/String;Lorg/scalatest/ConfigMap;)Lorg/scalatest/TestData;",
                        V(0),
                        &[a, config],
                    );
                    let wrapper = b.opaque();
                    b.call(
                        contract::WORDSPEC,
                        "withFixture",
                        "(Lorg/scalatest/TestSuite$NoArgTest;)Lorg/scalatest/Outcome;",
                        V(0),
                        &[wrapper],
                    );
                }
                _ => unreachable!(),
            }
            // No invented concrete NoArgTest/Status, default Args, Reporter,
            // Stopper, Filter, distributor or nested-suite absence authority.
            b.open();
            let result = b.opaque();
            b.summary.returned = Some(result);
        }
        Recipe::Initialize => return None,
    }
    Some(b.summary)
}

#[cfg(test)]
#[path = "binary_scalatest_tests.rs"]
mod tests;
