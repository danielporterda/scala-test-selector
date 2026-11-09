//! Standalone saved-report explanations. Raw JSON records borrow one file buffer;
//! only the requested suite's proof chain is decoded and rendered in detail.
use serde::Deserialize;
use serde_json::value::RawValue;
use std::borrow::Cow;
use std::error::Error;
use std::io::{self, Write};
use std::path::Path;

#[derive(Clone, Copy, Default)]
struct SavedSuiteSemantics {
    mode: selector_types::SuiteSemantics,
    present: bool,
}
impl<'de> Deserialize<'de> for SavedSuiteSemantics {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        #[serde(rename_all = "snake_case")]
        enum Mode {
            SharedState,
            IndependentSuites,
        }
        let mode = match Mode::deserialize(deserializer)? {
            Mode::SharedState => selector_types::SuiteSemantics::SharedState,
            Mode::IndependentSuites => selector_types::SuiteSemantics::Independent,
        };
        Ok(Self {
            mode,
            present: true,
        })
    }
}

#[derive(Default)]
struct SavedContract<'a>(Option<SavedSelectionContract<'a>>);
impl<'de: 'a, 'a> Deserialize<'de> for SavedContract<'a> {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Ok(Self(Some(SavedSelectionContract::deserialize(
            deserializer,
        )?)))
    }
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct SavedSelectionContract<'a> {
    #[serde(borrow)]
    version: Cow<'a, str>,
    bits: u32,
    #[serde(borrow, deserialize_with = "bounded_assumptions")]
    assumptions: Vec<Cow<'a, str>>,
}
fn bounded_assumptions<'de, D: serde::Deserializer<'de>>(
    deserializer: D,
) -> Result<Vec<Cow<'de, str>>, D::Error> {
    struct Names;
    impl<'de> serde::de::Visitor<'de> for Names {
        type Value = Vec<Cow<'de, str>>;
        fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            formatter.write_str("at most seven contract assumption names")
        }
        fn visit_seq<A: serde::de::SeqAccess<'de>>(
            self,
            mut seq: A,
        ) -> Result<Self::Value, A::Error> {
            let mut names = Vec::new();
            while let Some(name) = seq.next_element()? {
                if names.len() == 7 {
                    return Err(serde::de::Error::custom("too many selection assumptions"));
                }
                names.push(name);
            }
            Ok(names)
        }
    }
    deserializer.deserialize_seq(Names)
}
fn checked_selection_contract(
    saved: &SavedContract<'_>,
    mode: selector_types::SuiteSemantics,
) -> Result<selector_types::SelectionContract, Box<dyn Error>> {
    let Some(raw) = &saved.0 else {
        return Ok(
            selector_types::SelectionContract::from_bits(mode.assumption_bit())
                .expect("known legacy mode"),
        );
    };
    let contract = selector_types::SelectionContract::from_bits(raw.bits)
        .ok_or_else(|| invalid("unknown selection contract assumptions"))?;
    if raw.version != selector_types::SelectionContract::VERSION
        || contract.suite_semantics() != mode
        || !raw
            .assumptions
            .iter()
            .map(|name| name.as_ref())
            .eq(contract.assumptions())
    {
        return Err(invalid("saved selection contract binding"));
    }
    Ok(contract)
}
fn write_saved_contract(
    out: &mut dyn Write,
    saved: &SavedContract<'_>,
    mode: selector_types::SuiteSemantics,
) -> Result<(), Box<dyn Error>> {
    let contract = checked_selection_contract(saved, mode)?;
    if saved.0.is_some() {
        selector_report::write_selection_contract_text(out, contract)?;
    } else {
        selector_report::write_suite_semantics_text(&mut *out, mode)?;
        writeln!(
            out,
            "Selection contract: legacy (no additional assumptions recorded)."
        )?;
    }
    Ok(())
}

#[derive(Deserialize)]
struct Report<'a> {
    schema_version: u32,
    #[serde(default, borrow)]
    base_snapshot: Option<Cow<'a, str>>,
    #[serde(default, borrow)]
    head_snapshot: Option<Cow<'a, str>>,
    #[serde(default, borrow)]
    completion: Option<Cow<'a, str>>,
    #[serde(default)]
    suite_semantics: SavedSuiteSemantics,
    #[serde(default, borrow)]
    selection_contract: SavedContract<'a>,
    #[serde(default, borrow)]
    classpath_exclusions: Option<Vec<SavedClasspathExclusion<'a>>>,
    #[serde(default, borrow)]
    obligations: Vec<SavedIssueKind<'a>>,
    #[serde(default, borrow)]
    guard_causes: Vec<SavedIssueKind<'a>>,
    #[serde(default, borrow)]
    change_scope: Option<SavedSourceScope<'a>>,
    #[serde(borrow)]
    suites: Vec<Suite<'a>>,
    #[serde(borrow)]
    base: Option<Analysis<'a>>,
    #[serde(borrow)]
    head: Analysis<'a>,
}
#[derive(Deserialize)]
struct Suite<'a> {
    suite_id: u32,
    node: Option<u32>,
    #[serde(default)]
    base_node: Option<u32>,
    #[serde(borrow)]
    name: Cow<'a, str>,
    #[serde(borrow)]
    symbol: Cow<'a, str>,
    #[serde(borrow)]
    context: Cow<'a, str>,
    #[serde(default, borrow)]
    path: Cow<'a, str>,
    guarded: bool,
    #[serde(default)]
    opaque_shared_heap: bool,
}
#[derive(Deserialize)]
struct Analysis<'a> {
    affected: Vec<u32>,
    #[serde(default, borrow)]
    obligations: Vec<SavedIssueKind<'a>>,
    #[serde(default)]
    guarded_roots: Vec<u32>,
    #[serde(default)]
    unscoped_uncertainty: bool,
    #[serde(borrow)]
    witnesses: Vec<&'a RawValue>,
    #[serde(default, borrow)]
    evidence: Option<Evidence<'a>>,
    #[serde(default, borrow)]
    runtime_diagnostics: Vec<&'a RawValue>,
}
#[derive(Deserialize)]
struct SavedIssueKind<'a> {
    #[serde(borrow)]
    kind: Cow<'a, str>,
}
#[derive(Deserialize)]
struct Evidence<'a> {
    #[serde(default, borrow)]
    requested_roots: Vec<SavedRoot<'a>>,
    #[serde(default, borrow)]
    root_impacts: Option<Vec<SavedRoot<'a>>>,
    #[serde(default, borrow)]
    heap_origins: Vec<HeapOrigin<'a>>,
    #[serde(default, borrow)]
    guard_causes: Vec<Boundary<'a>>,
    #[serde(borrow)]
    contexts: Vec<&'a RawValue>,
    witnesses: Vec<ContextLink>,
    root_contexts: Vec<u32>,
    #[serde(borrow)]
    values: Vec<&'a RawValue>,
    #[serde(borrow)]
    atoms: Vec<&'a RawValue>,
    value_ids: Vec<u32>,
    #[serde(borrow)]
    captures: Vec<&'a RawValue>,
}
#[derive(Deserialize, PartialEq, Eq)]
struct SavedRoot<'a> {
    #[serde(default)]
    node: Option<u32>,
    receiver: Option<u32>,
    #[serde(default, borrow)]
    receiver_symbol: Option<Cow<'a, str>>,
    #[serde(default, borrow)]
    receiver_context: Option<Cow<'a, str>>,
}
impl SavedRoot<'_> {
    fn key(&self) -> (Option<u32>, u32) {
        (self.node, self.receiver.unwrap_or(u32::MAX))
    }
}

impl Analysis<'_> {
    fn checked_root_impacts(&self) -> Result<(), Box<dyn Error>> {
        let Some(e) = &self.evidence else {
            return Ok(());
        };
        let Some(roots) = &e.root_impacts else {
            return Ok(());
        };
        if self.affected.windows(2).any(|pair| pair[0] >= pair[1])
            || e.requested_roots
                .windows(2)
                .any(|pair| pair[0].key() >= pair[1].key())
            || e.requested_roots.iter().any(|row| row.node.is_none())
            || roots.windows(2).any(|pair| pair[0].key() >= pair[1].key())
            || roots.iter().any(|row| {
                row.node
                    .is_none_or(|node| self.affected.binary_search(&node).is_err())
                    || row.receiver_symbol.is_none()
                    || row.receiver_context.is_none()
                    || e.requested_roots
                        .binary_search_by_key(&row.key(), SavedRoot::key)
                        .ok()
                        .is_none_or(|index| e.requested_roots[index] != *row)
            })
        {
            return Err(invalid("saved exact root impact binding"));
        }
        Ok(())
    }

    fn root_reached(&self, node: Option<u32>, symbol: &str, context: &str) -> bool {
        let Some(node) = node else { return false };
        match self.evidence.as_ref().and_then(|e| e.root_impacts.as_ref()) {
            None => self.affected.binary_search(&node).is_ok(),
            Some(roots) => roots.iter().any(|root| {
                root.node == Some(node)
                    && root.receiver_symbol.as_deref() == Some(symbol)
                    && root.receiver_context.as_deref() == Some(context)
            }),
        }
    }
}
#[derive(Deserialize)]
struct HeapOrigin<'a> {
    symbol_id: u32,
    #[serde(borrow)]
    symbol: Cow<'a, str>,
    #[serde(borrow)]
    context: Cow<'a, str>,
}
#[derive(Deserialize, Clone, Copy)]
struct ContextLink {
    context: u32,
    next: u32,
    edge: u32,
    #[serde(default)]
    binding: Option<u32>,
}
#[derive(Deserialize)]
struct Step<'a> {
    node: u32,
    next: u32,
    edge: u32,
    #[serde(borrow)]
    kind: Cow<'a, str>,
    #[serde(borrow)]
    source: Cow<'a, str>,
    #[serde(borrow)]
    target: Cow<'a, str>,
}
#[derive(Deserialize)]
struct StepIndex {
    node: u32,
    next: u32,
    edge: u32,
}
#[derive(Deserialize)]
struct ContextIndex {
    id: u32,
    node: u32,
}
#[derive(Deserialize)]
struct Context<'a> {
    id: u32,
    node: u32,
    receiver: u32,
    arguments: Range,
    #[serde(borrow)]
    symbol: Cow<'a, str>,
    #[serde(default, borrow)]
    path: Cow<'a, str>,
}
#[derive(Deserialize)]
struct RuntimeDiagnostic<'a> {
    #[serde(borrow)]
    kind: Cow<'a, str>,
    #[serde(default, borrow)]
    scope: Cow<'a, str>,
    #[serde(default)]
    node: Option<u32>,
    #[serde(default)]
    file_id: Option<u32>,
    #[serde(default)]
    symbol_id: Option<u32>,
    #[serde(default, borrow)]
    path: Cow<'a, str>,
    #[serde(default, borrow)]
    symbol: Cow<'a, str>,
    #[serde(borrow)]
    reason: Cow<'a, str>,
    #[serde(default, borrow)]
    metadata_path: Cow<'a, str>,
}
#[derive(Deserialize, Clone, Copy)]
struct Range {
    start: u32,
    len: u32,
}
#[derive(Deserialize)]
struct Value {
    atoms: Range,
    unknown: u32,
}
#[derive(Deserialize)]
struct Atom<'a> {
    kind: u32,
    binding: u32,
    #[serde(default)]
    site: Option<u32>,
    #[serde(default, borrow)]
    carrier: Option<Cow<'a, str>>,
    #[serde(default, borrow)]
    identity: Option<Cow<'a, str>>,
    #[serde(borrow)]
    symbol: Cow<'a, str>,
    #[serde(default, borrow)]
    constraint: Option<Cow<'a, str>>,
    #[serde(default, borrow)]
    upper_bounds: Vec<Cow<'a, str>>,
}
#[derive(Deserialize)]
struct Capture {
    binding: u32,
    receiver: u32,
    arguments: Range,
}

fn invalid(message: &str) -> Box<dyn Error> {
    Box::new(io::Error::new(io::ErrorKind::InvalidData, message))
}
fn range(range: Range, length: usize) -> Result<std::ops::Range<usize>, Box<dyn Error>> {
    let start = range.start as usize;
    let end = start
        .checked_add(range.len as usize)
        .ok_or_else(|| invalid("proof range overflow"))?;
    if end > length {
        return Err(invalid("proof range exceeds retained evidence"));
    }
    Ok(start..end)
}

fn write_value(out: &mut dyn Write, e: &Evidence<'_>, id: u32) -> Result<(), Box<dyn Error>> {
    let raw = e
        .values
        .get(id as usize)
        .ok_or_else(|| invalid("invalid receiver/value evidence ID"))?;
    let value: Value = serde_json::from_str(raw.get())?;
    write!(out, "value{id}[")?;
    for (i, raw) in e.atoms[range(value.atoms, e.atoms.len())?]
        .iter()
        .enumerate()
    {
        if i > 0 {
            write!(out, ", ")?;
        }
        let atom: Atom<'_> = serde_json::from_str(raw.get())?;
        match atom.kind {
            1 | 4 => {
                if atom.kind == 4
                    && (atom.carrier.as_deref() != Some("sequence_elements")
                        || atom.identity.as_deref() != Some("pack_site_and_receiver_root")
                        || atom.symbol != selector_types::SEQUENCE_ELEMENTS_SYMBOL
                        || atom.site.is_none()
                        || atom.site == Some(u32::MAX))
                {
                    return Err(invalid("invalid sequence element carrier"));
                }
                write!(
                    out,
                    "{} {}",
                    if atom.kind == 1 {
                        "object"
                    } else {
                        "sequence element carrier"
                    },
                    atom.symbol
                )?;
                if atom.binding != 0 {
                    if e.heap_origins
                        .windows(2)
                        .any(|pair| pair[0].symbol_id >= pair[1].symbol_id)
                    {
                        return Err(invalid("object heap origin dictionary order"));
                    }
                    let index = e
                        .heap_origins
                        .binary_search_by_key(&(atom.binding - 1), |origin| origin.symbol_id)
                        .map_err(|_| invalid("missing object heap origin"))?;
                    let origin = &e.heap_origins[index];
                    if origin.symbol.is_empty()
                        || e.requested_roots.iter().any(|root| {
                            root.receiver == Some(origin.symbol_id)
                                && (root
                                    .receiver_symbol
                                    .as_deref()
                                    .is_some_and(|name| name != origin.symbol)
                                    || root
                                        .receiver_context
                                        .as_deref()
                                        .is_some_and(|context| context != origin.context))
                        })
                    {
                        return Err(invalid("invalid object heap origin reference"));
                    }
                    write!(out, " with receiver origin {}", origin.symbol)?;
                }
            }
            2 => write!(out, "callback {} capture{}", atom.symbol, atom.binding)?,
            3 => {
                if atom.binding != 0
                    || atom.constraint.as_deref() != Some("static_result_constraint")
                    || atom.upper_bounds.is_empty()
                    || atom.upper_bounds.iter().any(|bound| bound.is_empty())
                {
                    return Err(invalid("invalid static result constraint"));
                }
                write!(out, "static result constraint {} <= [", atom.symbol)?;
                for (i, bound) in atom.upper_bounds.iter().enumerate() {
                    if i > 0 {
                        out.write_all(b" & ")?;
                    }
                    out.write_all(bound.as_bytes())?;
                }
                out.write_all(b"]")?;
            }
            _ => return Err(invalid("invalid evidence atom kind")),
        }
    }
    if value.unknown != 0 {
        write!(out, " unknown={}", value.unknown)?;
    }
    write!(out, "]")?;
    Ok(())
}
fn write_arguments(out: &mut dyn Write, e: &Evidence<'_>, r: Range) -> Result<(), Box<dyn Error>> {
    write!(out, "[")?;
    for (i, id) in e.value_ids[range(r, e.value_ids.len())?].iter().enumerate() {
        if i > 0 {
            write!(out, ", ")?;
        }
        write_value(out, e, *id)?;
    }
    write!(out, "]")?;
    Ok(())
}

fn render_contexts(
    out: &mut dyn Write,
    label: &str,
    a: &Analysis<'_>,
    node: u32,
    scope: &mut Vec<u32>,
) -> Result<bool, Box<dyn Error>> {
    let Some(e) = &a.evidence else {
        return Ok(false);
    };
    let mut contexts = Vec::with_capacity(e.contexts.len());
    for raw in &e.contexts {
        let c: ContextIndex = serde_json::from_str(raw.get())?;
        contexts.push((c.id, c.node, *raw));
    }
    contexts.sort_unstable_by_key(|c| c.0);
    if contexts.windows(2).any(|w| w[0].0 == w[1].0) {
        return Err(invalid("duplicate context identity in saved report"));
    }
    let context = |id: u32| {
        contexts
            .binary_search_by_key(&id, |c| c.0)
            .map(|i| contexts[i].2)
            .map_err(|_| invalid("missing context in saved proof"))
    };
    let mut links = e.witnesses.clone();
    links.sort_unstable_by_key(|w| w.context);
    if links.windows(2).any(|w| w[0].context == w[1].context) {
        return Err(invalid("duplicate contextual proof link"));
    }
    let mut rendered = false;
    let mut used = Vec::new();
    let mut bindings = Vec::new();
    for root in &e.root_contexts {
        let c: ContextIndex = serde_json::from_str(context(*root)?.get())?;
        if c.node != node {
            continue;
        }
        rendered = true;
        writeln!(out, "  {label}: context {}", root)?;
        let mut current = *root;
        let mut remaining = contexts.len() + 1;
        loop {
            if remaining == 0 {
                return Err(invalid("cyclic context proof in saved report"));
            }
            remaining -= 1;
            let c: Context<'_> = serde_json::from_str(context(current)?.get())?;
            scope.push(c.node);
            writeln!(out, "    context {} {} (node {})", c.id, c.symbol, c.node)?;
            write!(out, "      receiver=")?;
            write_value(out, e, c.receiver)?;
            write!(out, " arguments=")?;
            write_arguments(out, e, c.arguments)?;
            writeln!(out)?;
            // Capture records are printed only when this context's receiver or
            // argument values reference their bindings; no recursive tree copy.
            used.clear();
            used.push(c.receiver);
            used.extend_from_slice(&e.value_ids[range(c.arguments, e.value_ids.len())?]);
            bindings.clear();
            for id in used.iter().copied() {
                let value: Value = serde_json::from_str(
                    e.values
                        .get(id as usize)
                        .ok_or_else(|| invalid("missing contextual value"))?
                        .get(),
                )?;
                for atom in &e.atoms[range(value.atoms, e.atoms.len())?] {
                    let atom: Atom<'_> = serde_json::from_str(atom.get())?;
                    if atom.kind == 2 {
                        bindings.push(atom.binding);
                    }
                }
            }
            bindings.sort_unstable();
            bindings.dedup();
            for raw in &e.captures {
                let capture: Capture = serde_json::from_str(raw.get())?;
                if bindings.binary_search(&capture.binding).is_ok() {
                    write!(out, "      capture{} receiver=", capture.binding)?;
                    write_value(out, e, capture.receiver)?;
                    write!(out, " arguments=")?;
                    write_arguments(out, e, capture.arguments)?;
                    writeln!(out)?;
                }
            }
            let Ok(at) = links.binary_search_by_key(&current, |w| w.context) else {
                break;
            };
            let link = links[at];
            context(link.next)?;
            write!(out, "      --edge {}", link.edge)?;
            if let Some(binding) = link.binding {
                let mut found = false;
                for raw in &e.captures {
                    let capture: Capture = serde_json::from_str(raw.get())?;
                    if capture.binding == binding {
                        found = true;
                        write!(out, " capture{binding} receiver=")?;
                        write_value(out, e, capture.receiver)?;
                        write!(out, " arguments=")?;
                        write_arguments(out, e, capture.arguments)?;
                        break;
                    }
                }
                if !found {
                    return Err(invalid(
                        "context witness references missing capture binding",
                    ));
                }
            }
            writeln!(out, "--> context {}", link.next)?;
            current = link.next;
        }
    }
    Ok(rendered)
}

fn render_diagnostics(
    out: &mut dyn Write,
    label: &str,
    a: &Analysis<'_>,
    scope: &mut Vec<u32>,
    suite: &Suite<'_>,
) -> Result<(), Box<dyn Error>> {
    if !suite.guarded {
        return Ok(());
    }
    scope.sort_unstable();
    scope.dedup();
    for raw in &a.runtime_diagnostics {
        let d: RuntimeDiagnostic<'_> = serde_json::from_str(raw.get())?;
        if d.reason.is_empty() {
            return Err(invalid("runtime diagnostic has empty reason"));
        }
        let expected = if d.node.is_some() {
            "node"
        } else if d.symbol_id.is_some() {
            "symbol"
        } else if d.file_id.is_some() {
            "file"
        } else {
            "unscoped"
        };
        if !d.scope.is_empty() && d.scope != expected {
            return Err(invalid("runtime diagnostic scope disagrees with its IDs"));
        }
        // A node scope is authoritative: sharing the suite's file or symbol is
        // not enough to make an unrelated node's metadata part of this proof.
        let mut relevant = match expected {
            "node" => d
                .node
                .is_some_and(|node| scope.binary_search(&node).is_ok()),
            "symbol" => !d.symbol.is_empty() && d.symbol == suite.symbol,
            "file" => !d.path.is_empty() && d.path == suite.path,
            _ => true,
        };
        if !relevant && matches!(expected, "file" | "symbol") {
            if let Some(e) = &a.evidence {
                for raw in &e.contexts {
                    let c: ContextIndex = serde_json::from_str(raw.get())?;
                    if scope.binary_search(&c.node).is_err() {
                        continue;
                    }
                    let c: Context<'_> = serde_json::from_str(raw.get())?;
                    if (expected == "file" && !d.path.is_empty() && d.path == c.path)
                        || (expected == "symbol" && !d.symbol.is_empty() && d.symbol == c.symbol)
                    {
                        relevant = true;
                        break;
                    }
                }
            }
        }
        if !relevant {
            continue;
        }
        writeln!(
            out,
            "  runtime diagnostic [{label}] {} ({}): {}",
            d.kind, expected, d.reason
        )?;
        if !d.metadata_path.is_empty() {
            writeln!(out, "    metadata: {}", d.metadata_path)?;
        }
    }
    Ok(())
}

fn render_side(
    out: &mut dyn Write,
    label: &str,
    a: &Analysis<'_>,
    node: Option<u32>,
    suite: &Suite<'_>,
    kernel_only: bool,
) -> Result<(), Box<dyn Error>> {
    let Some(root) = node else {
        render_diagnostics(out, label, a, &mut Vec::new(), suite)?;
        return Ok(());
    };
    if a.affected.windows(2).any(|w| w[0] >= w[1]) {
        return Err(invalid("unordered affected nodes in saved report"));
    }
    let affected = a.root_reached(node, &suite.symbol, &suite.context);
    let guarded = a.unscoped_uncertainty || a.guarded_roots.contains(&root);
    let mut scope = vec![root];
    if !affected && !guarded {
        render_diagnostics(out, label, a, &mut scope, suite)?;
        return Ok(());
    }
    let contextual = render_contexts(out, label, a, root, &mut scope)?;
    if contextual {
        if guarded {
            writeln!(
                out,
                "    {}",
                if kernel_only {
                    "kernel scoped unresolved execution boundary"
                } else {
                    "scoped unresolved execution boundary; suite retained conservatively"
                }
            )?;
        }
    }
    if affected && !contextual {
        let mut index = Vec::with_capacity(a.witnesses.len());
        for raw in &a.witnesses {
            let step: StepIndex = serde_json::from_str(raw.get())?;
            index.push((step.node, step.next, step.edge, *raw));
        }
        index.sort_unstable_by_key(|w| w.0);
        if index.windows(2).any(|w| w[0].0 == w[1].0) {
            return Err(invalid("duplicate witness source in saved report"));
        }
        if a.evidence
            .as_ref()
            .is_some_and(|e| e.root_impacts.is_some())
        {
            writeln!(
                out,
                "  {label}: node projection of reached execution contexts"
            )?;
        } else {
            writeln!(out, "  {label}:")?;
        }
        let mut current = root;
        let mut remaining = index.len() + 1;
        loop {
            if remaining == 0 {
                return Err(invalid("cyclic witness chain in saved report"));
            }
            remaining -= 1;
            scope.push(current);
            let Ok(at) = index.binary_search_by_key(&current, |w| w.0) else {
                writeln!(out, "    changed seed node {current}")?;
                break;
            };
            let step: Step<'_> = serde_json::from_str(index[at].3.get())?;
            if step.node != current || a.affected.binary_search(&step.next).is_err() {
                return Err(invalid("witness chain leaves affected scope"));
            }
            writeln!(
                out,
                "    {} --{} (edge {})--> {}",
                step.source, step.kind, step.edge, step.target
            )?;
            current = step.next;
        }
    }
    if guarded {
        if let Some(evidence) = &a.evidence {
            if evidence
                .guard_causes
                .windows(2)
                .any(|w| w[0].root >= w[1].root)
            {
                return Err(invalid("saved guard boundary order"));
            }
            if let Ok(index) = evidence
                .guard_causes
                .binary_search_by_key(&root, |cause| cause.root)
            {
                let boundary = &evidence.guard_causes[index];
                scope.push(boundary.node);
                writeln!(
                    out,
                    "  {label} reached boundary {} [node {}]: {} {} {}",
                    boundary.boundary_symbol,
                    boundary.node,
                    boundary.kind,
                    boundary.path,
                    boundary.detail
                )?;
                write_saved_runtime_guard(out, boundary)?;
            }
        }
        writeln!(
            out,
            "  {label}: {} uncertainty; {}",
            if a.unscoped_uncertainty {
                "unscoped"
            } else {
                "scoped unresolved execution"
            },
            if kernel_only {
                "kernel diagnostic only"
            } else {
                "suite retained conservatively"
            }
        )?;
    }
    render_diagnostics(out, label, a, &mut scope, suite)?;
    Ok(())
}

pub fn explain_report(path: &Path, suite: &str, out: &mut dyn Write) -> Result<(), Box<dyn Error>> {
    let bytes = std::fs::read(path)?;
    let header: SavedHeader = serde_json::from_slice(&bytes)?;
    if header.schema_version == 2 {
        let report = checked_compact(&bytes)?;
        return explain_compact(&report, suite, out);
    }
    let report: Report<'_> = serde_json::from_slice(&bytes)?;
    if report.schema_version != 1 {
        return Err(invalid("unsupported selection report schema"));
    }
    let contract =
        checked_selection_contract(&report.selection_contract, report.suite_semantics.mode)?;
    for analysis in std::iter::once(&report.head).chain(report.base.iter()) {
        analysis.checked_root_impacts()?;
    }
    checked_full_classpath_exclusions(&report, contract)?;
    checked_source_scope(report.change_scope.as_ref())?;
    if report
        .obligations
        .iter()
        .chain(&report.guard_causes)
        .any(|issue| issue.kind == "incomplete_hierarchy")
    {
        return Err(invalid("saved metadata issue used as runtime obligation"));
    }
    for analysis in std::iter::once(&report.head).chain(report.base.iter()) {
        if analysis
            .obligations
            .iter()
            .any(|issue| issue.kind == "incomplete_hierarchy")
        {
            return Err(invalid("saved metadata issue used as runtime obligation"));
        }
        if let Some(evidence) = &analysis.evidence {
            for boundary in &evidence.guard_causes {
                checked_runtime_boundary(boundary)?;
            }
        }
        for raw in &analysis.runtime_diagnostics {
            let diagnostic: SavedIssueKind<'_> = serde_json::from_str(raw.get())?;
            if diagnostic.kind == "incomplete_hierarchy" {
                return Err(invalid("saved metadata issue used as runtime diagnostic"));
            }
        }
    }
    let numeric = suite.parse::<u32>().ok();
    if let Some(exclusions) = &report.classpath_exclusions {
        let mut matching = exclusions.iter().filter(|row| {
            row.name == suite || row.symbol == suite || numeric == Some(row.suite_id)
        });
        if let Some(row) = matching.next() {
            if matching.next().is_some()
                || report.suites.iter().any(|selected| {
                    selected.name == suite
                        || selected.symbol == suite
                        || numeric == Some(selected.suite_id)
                })
            {
                return Err(invalid(
                    "suite is ambiguous across compiler contexts; pass numeric suite_id",
                ));
            }
            write_saved_contract(out, &report.selection_contract, report.suite_semantics.mode)?;
            write_saved_source_scope(out, report.change_scope.as_ref())?;
            writeln!(
                out,
                "{} [{}]: excluded (classpath absence)",
                row.name, row.context
            )?;
            writeln!(
                out,
                "  Kernel completion: {}; execution uncertainty is preserved separately.",
                report.completion.as_deref().unwrap()
            )?;
            for proof in &row.exclusions {
                writeln!(
                    out,
                    "  {} classpath-absence certificate {} (assumptions {})",
                    proof.snapshot, proof.certificate, proof.assumptions
                )?;
            }
            let identity = Suite {
                suite_id: row.suite_id,
                node: row.node,
                base_node: row.base_node,
                name: Cow::Borrowed(&row.name),
                symbol: Cow::Borrowed(&row.symbol),
                context: Cow::Borrowed(&row.context),
                path: Cow::Borrowed(&row.path),
                guarded: false,
                opaque_shared_heap: false,
            };
            render_side(out, "head", &report.head, row.node, &identity, true)?;
            if let Some(base) = &report.base {
                render_side(out, "base", base, row.base_node, &identity, true)?;
            }
            return Ok(());
        }
    }
    let mut matching = report
        .suites
        .iter()
        .filter(|s| s.name == suite || s.symbol == suite || numeric == Some(s.suite_id));
    let selected = matching
        .next()
        .ok_or_else(|| invalid("suite is not selected in this report"))?;
    if matching.next().is_some() {
        return Err(invalid(
            "suite name is ambiguous across compiler contexts; pass its numeric suite_id",
        ));
    }
    let head_proven = report
        .head
        .root_reached(selected.node, &selected.symbol, &selected.context);
    let base_proven = report.base.as_ref().is_some_and(|base| {
        base.root_reached(selected.base_node, &selected.symbol, &selected.context)
    });
    if selected.opaque_shared_heap && !selected.guarded {
        return Err(invalid("saved opaque shared-heap suite is not guarded"));
    }
    if !selected.guarded && !head_proven && !base_proven {
        return Err(invalid("selected suite has no retained execution proof"));
    }
    write_saved_contract(out, &report.selection_contract, report.suite_semantics.mode)?;
    write_saved_source_scope(out, report.change_scope.as_ref())?;
    writeln!(
        out,
        "{} [{}]{}",
        selected.name,
        selected.context,
        if selected.guarded {
            " (conservative)"
        } else {
            ""
        }
    )?;
    if selected.opaque_shared_heap {
        writeln!(
            out,
            "  This root may read shared state that a changed or unresolved writer can mutate; observed execution does not establish that it is unaffected."
        )?;
    }
    render_side(out, "head", &report.head, selected.node, selected, false)?;
    if let Some(base) = &report.base {
        render_side(out, "base", base, selected.base_node, selected, false)?;
    }
    if selected.node.is_none() {
        writeln!(
            out,
            "  scoped uncertainty: suite is named by the catalogue but its compiler definition is unavailable"
        )?;
    } else if selected.guarded {
        writeln!(
            out,
            "  Selection retains this suite because an execution or changed-input scope is incomplete."
        )?;
    }
    Ok(())
}

#[derive(Deserialize)]
struct SavedHeader {
    schema_version: u32,
}

#[derive(Deserialize)]
struct CompactReport<'a> {
    schema_version: u32,
    #[serde(default)]
    suite_semantics: SavedSuiteSemantics,
    #[serde(default, borrow)]
    selection_contract: SavedContract<'a>,
    #[serde(borrow)]
    report_kind: Cow<'a, str>,
    #[serde(borrow)]
    base_snapshot: Cow<'a, str>,
    #[serde(borrow)]
    head_snapshot: Cow<'a, str>,
    #[serde(borrow)]
    base_facts: Cow<'a, str>,
    #[serde(borrow)]
    head_facts: Cow<'a, str>,
    #[serde(borrow)]
    completion: Cow<'a, str>,
    #[serde(default, borrow)]
    change_scope: Option<SavedSourceScope<'a>>,
    #[serde(borrow)]
    guard_causes: Vec<CompactCause<'a>>,
    #[serde(borrow)]
    decisions: Vec<CompactDecision<'a>>,
    #[serde(default, borrow)]
    full_evidence: Option<CompactEvidenceRef<'a>>,
    execution_seeds: CompactSeeds,
    #[serde(borrow)]
    suites: Vec<Suite<'a>>,
}

#[derive(Deserialize)]
struct SavedSourceScope<'a> {
    #[serde(borrow)]
    mode: Cow<'a, str>,
    #[serde(borrow)]
    effective_requested_source_paths: Vec<Cow<'a, str>>,
    outside_count: u64,
    outside_sample_complete: bool,
    covers_captured_source_delta: bool,
    whole_checkout_omission_authority: bool,
    #[serde(borrow)]
    notice: Cow<'a, str>,
    #[serde(borrow, deserialize_with = "bounded_source_rows")]
    outside: Vec<SavedSourceDelta<'a>>,
}

fn bounded_source_rows<'de: 'a, 'a, D>(
    deserializer: D,
) -> Result<Vec<SavedSourceDelta<'a>>, D::Error>
where
    D: serde::Deserializer<'de>,
{
    struct Rows<'a>(std::marker::PhantomData<&'a str>);
    impl<'de: 'a, 'a> serde::de::Visitor<'de> for Rows<'a> {
        type Value = Vec<SavedSourceDelta<'a>>;
        fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            formatter.write_str("at most 64 outside source deltas")
        }
        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: serde::de::SeqAccess<'de>,
        {
            let mut rows = Vec::new();
            while let Some(row) = sequence.next_element()? {
                if rows.len() == selector_result::MAX_OUTSIDE_SOURCE_DELTAS {
                    return Err(serde::de::Error::custom(
                        "outside source sample exceeds 64 rows",
                    ));
                }
                rows.push(row);
            }
            Ok(rows)
        }
    }
    deserializer.deserialize_seq(Rows(std::marker::PhantomData))
}
#[derive(Deserialize)]
struct SavedSourceDelta<'a> {
    base_file_id: Option<u32>,
    head_file_id: Option<u32>,
    #[serde(borrow)]
    path: Cow<'a, str>,
    #[serde(borrow)]
    context: Cow<'a, str>,
    #[serde(borrow)]
    base_source_sha256: Option<Cow<'a, str>>,
    #[serde(borrow)]
    head_source_sha256: Option<Cow<'a, str>>,
}
fn scope_notice(scope: &SavedSourceScope<'_>) -> &'static str {
    if scope.outside_count != 0 {
        "Other captured source changes need a separate selection. This result does not authorize omissions for the whole checkout."
    } else if scope.mode == "requested_paths" {
        "This result records the effective requested source paths. Source scope alone does not authorize omissions for the whole checkout."
    } else {
        "This result covers the captured source delta. Source scope alone does not authorize omissions for the whole checkout."
    }
}
fn checked_source_scope(scope: Option<&SavedSourceScope<'_>>) -> Result<(), Box<dyn Error>> {
    let Some(scope) = scope else { return Ok(()) };
    let paths = &scope.effective_requested_source_paths;
    if !matches!(scope.mode.as_ref(), "requested_paths" | "snapshot_delta")
        || paths.iter().any(|p| p.is_empty())
        || paths.windows(2).any(|w| w[0] >= w[1])
        || scope.outside.len()
            != scope
                .outside_count
                .min(selector_result::MAX_OUTSIDE_SOURCE_DELTAS as u64) as usize
        || scope.outside_sample_complete != (scope.outside_count == scope.outside.len() as u64)
        || scope.covers_captured_source_delta != (scope.outside_count == 0)
        || scope.whole_checkout_omission_authority
        || scope.notice != scope_notice(scope)
        || (scope.mode == "snapshot_delta" && (!paths.is_empty() || scope.outside_count != 0))
        || scope
            .outside
            .windows(2)
            .any(|w| (&w[0].path, &w[0].context) >= (&w[1].path, &w[1].context))
    {
        return Err(invalid("saved source change scope"));
    }
    for row in &scope.outside {
        if row.path.is_empty()
            || (row.base_file_id.is_none() && row.head_file_id.is_none())
            || row.base_file_id == Some(u32::MAX)
            || row.head_file_id == Some(u32::MAX)
            || row.base_file_id.is_some() != row.base_source_sha256.is_some()
            || row.head_file_id.is_some() != row.head_source_sha256.is_some()
            || (row.base_source_sha256.is_some()
                && row.base_source_sha256 == row.head_source_sha256)
            || paths
                .binary_search_by(|p| p.as_ref().cmp(row.path.as_ref()))
                .is_ok()
        {
            return Err(invalid("saved source delta provenance"));
        }
        for hash in [&row.base_source_sha256, &row.head_source_sha256]
            .into_iter()
            .flatten()
        {
            selector_types::ContentHash::from_hex(hash)?;
        }
    }
    Ok(())
}
fn write_saved_source_scope(
    out: &mut dyn Write,
    scope: Option<&SavedSourceScope<'_>>,
) -> Result<(), Box<dyn Error>> {
    checked_source_scope(scope)?;
    let Some(scope) = scope else {
        writeln!(
            out,
            "Source change scope was not recorded; whole-checkout omission authority is unknown."
        )?;
        return Ok(());
    };
    writeln!(
        out,
        "Source scope: {}; {} effective requested source paths; {} captured source changes outside the request.",
        scope.mode,
        scope.effective_requested_source_paths.len(),
        scope.outside_count
    )?;
    writeln!(out, "{}", scope.notice)?;
    for path in &scope.effective_requested_source_paths {
        writeln!(out, "  requested source: {path}")?;
    }
    for row in &scope.outside {
        writeln!(out, "  outside source: {} [{}]", row.path, row.context)?;
    }
    Ok(())
}
#[derive(Deserialize)]
struct CompactSeeds {
    base: Vec<u32>,
    head: Vec<u32>,
}
#[derive(Deserialize)]
struct CompactEvidenceRef<'a> {
    #[serde(borrow)]
    path: Cow<'a, str>,
    #[serde(borrow)]
    sha256: Cow<'a, str>,
    bytes: u64,
}
#[derive(Deserialize)]
struct CompactCause<'a> {
    #[serde(borrow)]
    snapshot: Cow<'a, str>,
    #[serde(borrow)]
    reason: Cow<'a, str>,
    #[serde(borrow)]
    kind: Cow<'a, str>,
    #[serde(borrow)]
    path: Cow<'a, str>,
    #[serde(borrow)]
    symbol: Cow<'a, str>,
    #[serde(borrow)]
    detail: Cow<'a, str>,
    #[serde(default, borrow)]
    external: Option<CompactExternal<'a>>,
}
#[derive(Deserialize)]
struct CompactExternal<'a> {
    #[serde(borrow)]
    reason: Cow<'a, str>,
    #[serde(borrow)]
    message: Cow<'a, str>,
    #[serde(default, borrow)]
    suite_name: Option<Cow<'a, str>>,
    #[serde(default, borrow)]
    schema_path: Option<Cow<'a, str>>,
    #[serde(default, borrow)]
    operation_path: Option<Cow<'a, str>>,
    #[serde(default, borrow)]
    verb: Option<Cow<'a, str>>,
}
#[derive(Deserialize)]
struct CompactDecision<'a> {
    suite_id: u32,
    node: Option<u32>,
    base_node: Option<u32>,
    #[serde(borrow)]
    name: Cow<'a, str>,
    #[serde(borrow)]
    symbol: Cow<'a, str>,
    #[serde(borrow)]
    context: Cow<'a, str>,
    #[serde(borrow)]
    status: Cow<'a, str>,
    guarded: bool,
    #[serde(borrow)]
    reasons: Vec<Cow<'a, str>>,
    #[serde(borrow)]
    explanation: Vec<Cow<'a, str>>,
    #[serde(borrow)]
    proofs: Vec<CompactProof<'a>>,
    #[serde(borrow)]
    exclusions: Vec<CompactExclusion<'a>>,
    #[serde(default, borrow)]
    uncertainty: Vec<CompactUncertainty<'a>>,
}
#[derive(Deserialize)]
struct CompactUncertainty<'a> {
    #[serde(borrow)]
    snapshot: Cow<'a, str>,
    #[serde(borrow)]
    boundary: Boundary<'a>,
    #[serde(borrow)]
    metadata: Vec<BoundaryMetadata<'a>>,
}
#[derive(Deserialize)]
struct Boundary<'a> {
    root: u32,
    node: u32,
    #[serde(borrow)]
    kind: Cow<'a, str>,
    #[serde(borrow)]
    boundary_symbol: Cow<'a, str>,
    #[serde(borrow)]
    path: Cow<'a, str>,
    #[serde(borrow)]
    detail: Cow<'a, str>,
    #[serde(default, borrow)]
    runtime_reason: Option<Cow<'a, str>>,
    #[serde(default)]
    operation: Option<u32>,
    #[serde(default, borrow)]
    opcode: Option<Cow<'a, str>>,
    #[serde(default, borrow)]
    operation_path: Option<Cow<'a, str>>,
    #[serde(default)]
    span: Option<SourceSpan>,
}
#[derive(Deserialize, Clone, Copy)]
struct SourceSpan {
    start: u32,
    end: u32,
}

fn checked_runtime_boundary(boundary: &Boundary<'_>) -> Result<(), Box<dyn Error>> {
    use selector_issue::{RuntimeIssueReason, RuntimeIssueSite};
    use selector_types::{IssueKind, Opcode, OperationId};
    if boundary.kind == "incomplete_hierarchy" {
        return Err(invalid("saved metadata issue used as runtime boundary"));
    }
    let Some(raw_reason) = &boundary.runtime_reason else {
        if boundary.operation.is_some()
            || boundary.opcode.is_some()
            || boundary.operation_path.is_some()
            || boundary.span.is_some()
        {
            return Err(invalid("saved runtime guard has no reason"));
        }
        return Ok(());
    };
    let reason = (1..=13)
        .filter_map(|id| RuntimeIssueReason::decode(id).ok())
        .find(|r| r.as_str() == raw_reason.as_ref())
        .ok_or_else(|| invalid("saved runtime guard reason"))?;
    let expected_kind = match reason.kind() {
        IssueKind::UnresolvedSymbol => "unresolved_symbol",
        _ => "unknown_execution",
    };
    if boundary.kind != expected_kind || boundary.operation == Some(u32::MAX) {
        return Err(invalid("saved runtime guard issue kind or operation"));
    }
    RuntimeIssueSite {
        kind: reason.kind(),
        operation: boundary
            .operation
            .map(OperationId)
            .unwrap_or(OperationId::NONE),
        reason,
    }
    .validate()?;
    let opcode = match boundary.opcode.as_deref() {
        None => None,
        Some("call") => Some(Opcode::Call),
        Some("virtual_call") => Some(Opcode::VirtualCall),
        Some("allocate") => Some(Opcode::Allocate),
        Some("assign") => Some(Opcode::Assign),
        Some("parameter") => Some(Opcode::Parameter),
        Some("return") => Some(Opcode::Return),
        Some("bind_callback") => Some(Opcode::BindCallback),
        Some("invoke_callback") => Some(Opcode::InvokeCallback),
        Some("load_field") => Some(Opcode::LoadField),
        Some("store_field") => Some(Opcode::StoreField),
        Some("initialize") => Some(Opcode::Initialize),
        Some("unknown") => Some(Opcode::Unknown),
        Some("constant") => Some(Opcode::Constant),
        Some("join") => Some(Opcode::Join),
        Some("default_argument") => Some(Opcode::DefaultArgument),
        Some("register_test") => Some(Opcode::RegisterTest),
        Some("pack_sequence") => Some(Opcode::PackSequence),
        Some("read_elements") => Some(Opcode::ReadElements),
        Some(_) => return Err(invalid("saved runtime guard opcode")),
    };
    if boundary.operation.is_some() != opcode.is_some()
        || opcode.is_some_and(|opcode| !reason.accepts_opcode(opcode))
        || boundary
            .operation_path
            .as_ref()
            .is_some_and(|path| path.is_empty())
        || (boundary.operation.is_none()
            && (boundary.operation_path.is_some() || boundary.span.is_some()))
        || boundary
            .span
            .is_some_and(|span| span.start > span.end || boundary.operation_path.is_none())
    {
        return Err(invalid("saved runtime guard operation provenance"));
    }
    Ok(())
}

fn write_saved_runtime_guard(
    out: &mut dyn Write,
    boundary: &Boundary<'_>,
) -> Result<(), Box<dyn Error>> {
    checked_runtime_boundary(boundary)?;
    let Some(reason) = &boundary.runtime_reason else {
        return Ok(());
    };
    write!(out, "    runtime reason: {reason}")?;
    if let Some(operation) = boundary.operation {
        write!(
            out,
            "; operation {operation} ({})",
            boundary.opcode.as_deref().unwrap()
        )?;
        if let Some(path) = &boundary.operation_path {
            write!(out, "; {path}")?;
        }
        if let Some(span) = boundary.span {
            write!(out, " bytes {}..{}", span.start, span.end)?;
        }
    }
    out.write_all(b"\n")?;
    Ok(())
}
#[derive(Deserialize)]
struct BoundaryMetadata<'a> {
    #[serde(borrow)]
    reason: Cow<'a, str>,
    #[serde(borrow)]
    metadata_path: Cow<'a, str>,
}
#[derive(Deserialize)]
struct CompactProof<'a> {
    #[serde(borrow)]
    snapshot: Cow<'a, str>,
    #[serde(borrow)]
    snapshot_identity: Cow<'a, str>,
    root: u32,
    seed: u32,
    #[serde(default, borrow)]
    chain_precision: Option<Cow<'a, str>>,
    #[serde(borrow)]
    seed_symbol: Cow<'a, str>,
    #[serde(borrow)]
    chain: Vec<Step<'a>>,
}
#[derive(Deserialize)]
struct CompactExclusion<'a> {
    #[serde(borrow)]
    snapshot: Cow<'a, str>,
    #[serde(borrow)]
    snapshot_identity: Cow<'a, str>,
    root: u32,
    #[serde(borrow)]
    certificate: Cow<'a, str>,
    assumptions: u32,
}

#[derive(Deserialize)]
struct SavedClasspathExclusion<'a> {
    suite_id: u32,
    node: Option<u32>,
    base_node: Option<u32>,
    #[serde(borrow)]
    name: Cow<'a, str>,
    #[serde(borrow)]
    symbol: Cow<'a, str>,
    #[serde(borrow)]
    context: Cow<'a, str>,
    #[serde(borrow)]
    path: Cow<'a, str>,
    guarded: bool,
    #[serde(borrow)]
    reason: Cow<'a, str>,
    #[serde(borrow)]
    exclusions: Vec<CompactExclusion<'a>>,
}

fn is_classpath_contract(contract: selector_types::SelectionContract) -> bool {
    contract == selector_types::SelectionContract::owning_test_classpath()
        || contract == selector_types::SelectionContract::owning_test_classpath_with_compilation()
}

fn checked_classpath_certificates(
    contract: selector_types::SelectionContract,
    base_snapshot: &str,
    head_snapshot: &str,
    base_root: Option<u32>,
    head_root: Option<u32>,
    exclusions: &[CompactExclusion<'_>],
) -> Result<(), Box<dyn Error>> {
    use selector_types::ContentHash;
    if !is_classpath_contract(contract)
        || exclusions.len() != 2
        || base_root.is_none_or(|root| root == u32::MAX)
        || head_root.is_none_or(|root| root == u32::MAX)
    {
        return Err(invalid("saved paired classpath absence proof"));
    }
    for (side, snapshot, root) in [
        ("base", base_snapshot, base_root),
        ("head", head_snapshot, head_root),
    ] {
        let mut matches = exclusions.iter().filter(|proof| proof.snapshot == side);
        let proof = matches
            .next()
            .ok_or_else(|| invalid("saved classpath proof side"))?;
        if matches.next().is_some()
            || proof.snapshot_identity != snapshot
            || Some(proof.root) != root
            || proof.assumptions != contract.bits()
            || ContentHash::from_hex(&proof.certificate)? == ContentHash::default()
        {
            return Err(invalid("saved classpath proof binding"));
        }
    }
    Ok(())
}

fn checked_compact_classpath_absence(
    report: &CompactReport<'_>,
    decision: &CompactDecision<'_>,
    contract: selector_types::SelectionContract,
) -> Result<bool, Box<dyn Error>> {
    let count = decision
        .reasons
        .iter()
        .filter(|reason| *reason == "classpath_absence")
        .count();
    if count == 0 {
        return Ok(false);
    }
    if count != 1
        || decision.status != "excluded"
        || decision.guarded
        || !decision.proofs.is_empty()
        || decision.reasons.iter().any(|reason| {
            matches!(
                reason.as_ref(),
                "complete_execution_unaffected"
                    | "closed_component_exclusion"
                    | "head_execution_impact"
                    | "base_execution_impact"
            )
        })
    {
        return Err(invalid("saved classpath absence decision"));
    }
    checked_classpath_certificates(
        contract,
        &report.base_snapshot,
        &report.head_snapshot,
        decision.base_node,
        decision.node,
        &decision.exclusions,
    )?;
    Ok(true)
}

fn checked_full_classpath_exclusions(
    report: &Report<'_>,
    contract: selector_types::SelectionContract,
) -> Result<(), Box<dyn Error>> {
    use selector_types::{ContentHash, SelectionContract};
    let opted_in = contract.contains(SelectionContract::OWNING_TEST_CLASSPATH);
    let Some(rows) = &report.classpath_exclusions else {
        return if opted_in {
            Err(invalid("saved classpath proof table absent"))
        } else {
            Ok(())
        };
    };
    if !opted_in
        || !is_classpath_contract(contract)
        || rows
            .windows(2)
            .any(|pair| pair[0].suite_id >= pair[1].suite_id)
        || report
            .suites
            .windows(2)
            .any(|pair| pair[0].suite_id >= pair[1].suite_id)
        || !matches!(
            report.completion.as_deref(),
            Some("complete" | "conservative" | "resource_limited")
        )
    {
        return Err(invalid("saved classpath proof table contract"));
    }
    let base_snapshot = report
        .base_snapshot
        .as_deref()
        .ok_or_else(|| invalid("saved base snapshot absent"))?;
    let head_snapshot = report
        .head_snapshot
        .as_deref()
        .ok_or_else(|| invalid("saved head snapshot absent"))?;
    ContentHash::from_hex(base_snapshot)?;
    ContentHash::from_hex(head_snapshot)?;
    for analysis in std::iter::once(&report.head).chain(report.base.iter()) {
        if analysis.affected.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(invalid("saved classpath affected-node order"));
        }
    }
    for row in rows {
        if row.guarded
            || row.reason != "classpath_absence"
            || report
                .suites
                .binary_search_by_key(&row.suite_id, |suite| suite.suite_id)
                .is_ok()
            || report
                .head
                .root_reached(row.node, &row.symbol, &row.context)
            || report
                .base
                .as_ref()
                .is_none_or(|base| base.root_reached(row.base_node, &row.symbol, &row.context))
        {
            return Err(invalid(
                "saved classpath exclusion conflicts with selection",
            ));
        }
        checked_classpath_certificates(
            contract,
            base_snapshot,
            head_snapshot,
            row.base_node,
            row.node,
            &row.exclusions,
        )?;
    }
    Ok(())
}

fn checked_compact(bytes: &[u8]) -> Result<CompactReport<'_>, Box<dyn Error>> {
    if bytes.len() > 64 * 1024 * 1024 {
        return Err(invalid("compact report exceeds 64 MiB admission limit"));
    }
    let report: CompactReport<'_> = serde_json::from_slice(bytes)?;
    if report.schema_version != 2 || report.report_kind != "decisions" {
        return Err(invalid("unsupported saved decision report"));
    }
    let selection_contract =
        checked_selection_contract(&report.selection_contract, report.suite_semantics.mode)?;
    checked_source_scope(report.change_scope.as_ref())?;
    for hash in [
        &report.base_snapshot,
        &report.head_snapshot,
        &report.base_facts,
        &report.head_facts,
    ] {
        selector_types::ContentHash::from_hex(hash)?;
    }
    if !matches!(
        report.completion.as_ref(),
        "complete" | "conservative" | "resource_limited"
    ) {
        return Err(invalid("invalid saved report completion"));
    }
    if let Some(evidence) = &report.full_evidence {
        if evidence.path.is_empty() || evidence.bytes == 0 {
            return Err(invalid("saved evidence reference is incomplete"));
        }
        selector_types::ContentHash::from_hex(&evidence.sha256)?;
    }
    for seeds in [&report.execution_seeds.base, &report.execution_seeds.head] {
        if seeds.windows(2).any(|w| w[0] >= w[1]) {
            return Err(invalid("saved execution seeds are not canonical"));
        }
    }
    let mut selected = report.suites.iter();
    for (i, decision) in report.decisions.iter().enumerate() {
        let cp_absent = checked_compact_classpath_absence(&report, decision, selection_contract)?;
        if !report.guard_causes.is_empty() && !decision.guarded && !cp_absent {
            return Err(invalid(
                "saved decision contradicts a global changed-input guard",
            ));
        }
        if decision.suite_id as usize != i
            || decision.reasons.is_empty()
            || decision.explanation.len() != decision.reasons.len()
        {
            return Err(invalid("saved decision catalogue or reason identity"));
        }
        match decision.status.as_ref() {
            "required" if !decision.proofs.is_empty() => {}
            "unknown" if decision.guarded && decision.proofs.is_empty() => {}
            "excluded" if !decision.guarded && decision.proofs.is_empty() => {}
            _ => return Err(invalid("saved suite status has no compatible proof")),
        }
        if decision
            .reasons
            .iter()
            .any(|reason| reason == "opaque_shared_heap")
            && !cp_absent
            && (!decision.guarded
                || decision.status == "excluded"
                || !decision.exclusions.is_empty()
                || decision.reasons.iter().any(|reason| {
                    matches!(
                        reason.as_ref(),
                        "complete_execution_unaffected" | "closed_component_exclusion"
                    )
                }))
        {
            return Err(invalid("saved opaque shared-heap decision"));
        }
        if decision.status != "excluded" {
            let suite = selected
                .next()
                .ok_or_else(|| invalid("saved selected catalogue is incomplete"))?;
            if suite.suite_id != decision.suite_id
                || suite.node != decision.node
                || suite.base_node != decision.base_node
                || suite.name != decision.name
                || suite.symbol != decision.symbol
                || suite.context != decision.context
                || suite.guarded != decision.guarded
            {
                return Err(invalid("saved selected suite differs from its decision"));
            }
        }
        if decision.status == "excluded"
            && !decision.reasons.iter().any(|reason| {
                matches!(
                    reason.as_ref(),
                    "complete_execution_unaffected"
                        | "closed_component_exclusion"
                        | "classpath_absence"
                )
            })
        {
            return Err(invalid("saved exclusion has no absence justification"));
        }
        for proof in &decision.proofs {
            if proof
                .chain_precision
                .as_deref()
                .is_some_and(|p| p != "node_projection")
            {
                return Err(invalid("unknown saved execution chain precision"));
            }
            let (identity, root) = match proof.snapshot.as_ref() {
                "head" => (&report.head_snapshot, decision.node),
                "base" => (&report.base_snapshot, decision.base_node),
                _ => return Err(invalid("saved proof snapshot side")),
            };
            if &proof.snapshot_identity != identity || root != Some(proof.root) {
                return Err(invalid("saved proof snapshot or root binding"));
            }
            if proof
                .chain
                .first()
                .map_or(proof.seed_symbol.as_ref(), |step| step.source.as_ref())
                != decision.symbol
            {
                return Err(invalid(
                    "saved proof root symbol disagrees with suite identity",
                ));
            }
            let mut node = proof.root;
            let mut visited = std::collections::HashSet::with_capacity(proof.chain.len());
            let mut symbol: Option<&str> = None;
            for step in &proof.chain {
                if step.node != node
                    || !visited.insert(node)
                    || symbol.is_some_and(|symbol| symbol != step.source)
                {
                    return Err(invalid(
                        "saved decision witness chain is disconnected or cyclic",
                    ));
                }
                node = step.next;
                symbol = Some(&step.target);
            }
            if node != proof.seed
                || visited.contains(&node)
                || symbol.is_some_and(|symbol| symbol != proof.seed_symbol)
            {
                return Err(invalid(
                    "saved proof does not reach its retained execution seed",
                ));
            }
            let seeds = if proof.snapshot == "head" {
                &report.execution_seeds.head
            } else {
                &report.execution_seeds.base
            };
            if seeds.binary_search(&proof.seed).is_err() {
                return Err(invalid(
                    "saved proof terminal is absent from changed execution seeds",
                ));
            }
        }
        for certificate in &decision.exclusions {
            let (identity, root) = match certificate.snapshot.as_ref() {
                "head" => (&report.head_snapshot, decision.node),
                "base" => (&report.base_snapshot, decision.base_node),
                _ => return Err(invalid("saved exclusion snapshot side")),
            };
            if &certificate.snapshot_identity != identity
                || root != Some(certificate.root)
                || certificate.assumptions == 0
                || certificate.assumptions & selector_types::SelectionContract::KNOWN_MASK
                    != selection_contract.bits()
            {
                return Err(invalid("saved exclusion certificate binding"));
            }
            if is_classpath_contract(selection_contract)
                && certificate.assumptions == selection_contract.bits()
                && !cp_absent
            {
                return Err(invalid("saved classpath proof reason absent"));
            }
            selector_types::ContentHash::from_hex(&certificate.certificate)?;
        }
        for uncertainty in &decision.uncertainty {
            let root = match uncertainty.snapshot.as_ref() {
                "head" => decision.node,
                "base" => decision.base_node,
                _ => return Err(invalid("saved guard boundary snapshot")),
            };
            if (!decision.guarded && !cp_absent)
                || root != Some(uncertainty.boundary.root)
                || uncertainty.boundary.node == u32::MAX
                || uncertainty.boundary.kind.is_empty()
                || uncertainty.boundary.boundary_symbol.is_empty()
            {
                return Err(invalid("saved guard boundary scope"));
            }
            checked_runtime_boundary(&uncertainty.boundary)?;
            if uncertainty
                .metadata
                .iter()
                .any(|metadata| metadata.reason.is_empty())
            {
                return Err(invalid("saved guard metadata reason"));
            }
        }
    }
    if selected.next().is_some() {
        return Err(invalid(
            "saved selected catalogue contains excluded or unknown decisions",
        ));
    }
    for cause in &report.guard_causes {
        if !matches!(cause.snapshot.as_ref(), "base" | "head")
            || cause.reason.is_empty()
            || cause.kind.is_empty()
            || cause.kind == "incomplete_hierarchy"
        {
            return Err(invalid("saved changed-input cause identity"));
        }
    }
    Ok(report)
}

fn render_compact_decision(
    out: &mut dyn Write,
    report: &CompactReport<'_>,
    decision: &CompactDecision<'_>,
) -> Result<(), Box<dyn Error>> {
    let cp_absent = decision
        .reasons
        .iter()
        .any(|reason| reason == "classpath_absence");
    writeln!(
        out,
        "{} [{}]: {}{}",
        decision.name,
        decision.context,
        decision.status,
        if decision.guarded { " (guarded)" } else { "" }
    )?;
    for (reason, explanation) in decision.reasons.iter().zip(&decision.explanation) {
        if cp_absent && reason != "classpath_absence" {
            writeln!(out, "  Kernel diagnostic: {explanation}")?;
        } else {
            writeln!(out, "  {explanation}")?;
        }
    }
    for proof in &decision.proofs {
        if proof.chain_precision.as_deref() == Some("node_projection") {
            writeln!(
                out,
                "  {} root reaches a changed seed; node projection (snapshot {}):",
                proof.snapshot, proof.snapshot_identity
            )?;
        } else {
            writeln!(
                out,
                "  {} execution proof (snapshot {}):",
                proof.snapshot, proof.snapshot_identity
            )?;
        }
        for step in &proof.chain {
            writeln!(
                out,
                "    {} --{} [edge {}]--> {}",
                step.source, step.kind, step.edge, step.target
            )?;
        }
        writeln!(
            out,
            "    changed execution seed {}: {}",
            proof.seed, proof.seed_symbol
        )?;
    }
    if decision
        .reasons
        .iter()
        .any(|reason| reason == "changed_input_unknown")
    {
        for cause in &report.guard_causes {
            writeln!(
                out,
                "  {} guard {}: {} {} {} {}",
                cause.snapshot, cause.reason, cause.kind, cause.path, cause.symbol, cause.detail
            )?;
            if let Some(external) = &cause.external {
                writeln!(
                    out,
                    "    {}: {} suite={} schema={} operation={} {}",
                    external.reason,
                    external.message,
                    external.suite_name.as_deref().unwrap_or(""),
                    external.schema_path.as_deref().unwrap_or(""),
                    external.verb.as_deref().unwrap_or(""),
                    external.operation_path.as_deref().unwrap_or("")
                )?;
            }
        }
    }
    for certificate in &decision.exclusions {
        writeln!(
            out,
            "  {} {} certificate {} (assumptions {})",
            certificate.snapshot,
            if cp_absent {
                "classpath-absence"
            } else {
                "closed-component"
            },
            certificate.certificate,
            certificate.assumptions
        )?;
    }
    for uncertainty in &decision.uncertainty {
        let boundary = &uncertainty.boundary;
        writeln!(
            out,
            "  {} {} {} [node {}]: {} {} {}",
            uncertainty.snapshot,
            if cp_absent {
                "kernel diagnostic at"
            } else {
                "reached boundary"
            },
            boundary.boundary_symbol,
            boundary.node,
            boundary.kind,
            boundary.path,
            boundary.detail
        )?;
        write_saved_runtime_guard(out, boundary)?;
        for metadata in &uncertainty.metadata {
            writeln!(out, "    {} ({})", metadata.reason, metadata.metadata_path)?;
        }
    }
    Ok(())
}

fn explain_compact(
    report: &CompactReport<'_>,
    suite: &str,
    out: &mut dyn Write,
) -> Result<(), Box<dyn Error>> {
    let numeric = suite.parse::<u32>().ok();
    let mut matching = report.decisions.iter().filter(|decision| {
        decision.name == suite || decision.symbol == suite || numeric == Some(decision.suite_id)
    });
    let decision = matching
        .next()
        .ok_or_else(|| invalid("suite is absent from the saved catalogue"))?;
    if matching.next().is_some() {
        return Err(invalid(
            "suite is ambiguous across compiler contexts; pass numeric suite_id",
        ));
    }
    write_saved_contract(out, &report.selection_contract, report.suite_semantics.mode)?;
    write_saved_source_scope(out, report.change_scope.as_ref())?;
    render_compact_decision(out, report, decision)
}

/// Rerender a SHA-pinnable standalone compact report without loading snapshots or
/// invoking analysis. Parsing borrows one bounded buffer and validates all links.
pub fn render_saved(path: &Path, out: &mut dyn Write, text: bool) -> Result<(), Box<dyn Error>> {
    let file = std::fs::File::open(path)?;
    if file.metadata()?.len() > 64 * 1024 * 1024 {
        return Err(invalid(
            "saved compact report exceeds 64 MiB admission limit",
        ));
    }
    use std::io::Read;
    let mut bytes = Vec::new();
    file.take(64 * 1024 * 1024 + 1).read_to_end(&mut bytes)?;
    let report = checked_compact(&bytes)?;
    if text {
        writeln!(out, "Selection: {}", report.completion)?;
        write_saved_contract(out, &report.selection_contract, report.suite_semantics.mode)?;
        write_saved_source_scope(out, report.change_scope.as_ref())?;
        for decision in &report.decisions {
            render_compact_decision(out, &report, decision)?;
        }
    } else {
        if report.suite_semantics.present {
            out.write_all(&bytes)?;
        } else {
            // Keep the original bounded JSON bytes, adding only the explicit
            // legacy default so a rerender cannot hide its selection policy.
            let start = bytes
                .iter()
                .position(|byte| *byte == b'{')
                .ok_or_else(|| invalid("saved report object"))?
                + 1;
            out.write_all(&bytes[..start])?;
            out.write_all(b"\"suite_semantics\":\"shared_state\",")?;
            out.write_all(&bytes[start..])?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn compact_fixture() -> serde_json::Value {
        let hash = "1".repeat(64);
        serde_json::json!({"schema_version":2,"report_kind":"decisions","suite_semantics":"shared_state","base_snapshot":hash,"head_snapshot":hash,"base_facts":hash,"head_facts":hash,"completion":"complete","guard_causes":[],"execution_seeds":{"base":[],"head":[1]},"suites":[{"suite_id":0,"node":0,"base_node":0,"name":"Suite","symbol":"p/Suite#","context":"test","guarded":false}],"decisions":[
            {"suite_id":0,"node":0,"base_node":0,"name":"Suite","symbol":"p/Suite#","context":"test","status":"required","guarded":false,"reasons":["head_execution_impact"],"explanation":["Head execution reaches a changed seed."],"proofs":[{"snapshot":"head","snapshot_identity":hash,"root":0,"seed":1,"seed_symbol":"p/changed().","chain":[{"node":0,"next":1,"edge":42,"kind":"call","source":"p/Suite#","target":"p/changed()."}]}],"exclusions":[]},
            {"suite_id":1,"node":2,"base_node":2,"name":"Independent","symbol":"p/Independent#","context":"test","status":"excluded","guarded":false,"reasons":["complete_execution_unaffected"],"explanation":["Completed execution has no changed dependency."],"proofs":[],"exclusions":[]}
        ]})
    }
    fn classpath_compact_fixture() -> serde_json::Value {
        let mut report = compact_fixture();
        let contract = selector_types::SelectionContract::owning_test_classpath();
        report["suite_semantics"] = "independent_suites".into();
        report["selection_contract"] = serde_json::json!({"version":selector_types::SelectionContract::VERSION,"bits":contract.bits(),"assumptions":contract.assumptions().collect::<Vec<_>>()});
        report["completion"] = "resource_limited".into();
        let row = &mut report["decisions"][1];
        row["reasons"] = serde_json::json!([
            "scoped_execution_unknown",
            "resource_limit",
            "classpath_absence"
        ]);
        row["explanation"] = serde_json::json!([
            "Execution has unresolved effects.",
            "Kernel reached its resource cap.",
            "Requested application products are absent under the owning Test/fullClasspath premise."
        ]);
        row["exclusions"] = serde_json::json!([
            {"snapshot":"base","snapshot_identity":"1".repeat(64),"root":2,"certificate":"2".repeat(64),"assumptions":1008},
            {"snapshot":"head","snapshot_identity":"1".repeat(64),"root":2,"certificate":"3".repeat(64),"assumptions":1008}]);
        row["uncertainty"] = serde_json::json!([{"snapshot":"head","boundary":{"root":2,"node":2,"kind":"unknown_execution","boundary_symbol":"p/Independent#","path":"Independent.scala","detail":"Kernel callback unresolved"},"metadata":[]}]);
        report
    }
    #[test]
    fn saved_exact_root_impacts_separate_projection_and_reject_unrequested_rows() {
        let mut fixture = serde_json::json!({
            "affected":[0,1], "witnesses":[],
            "evidence":{
                "requested_roots":[{"node":0,"receiver":1,"receiver_symbol":"p/Suite#","receiver_context":"test"}],
                "root_impacts":[], "contexts":[], "witnesses":[], "root_contexts":[],
                "values":[], "atoms":[], "value_ids":[], "captures":[]
            }
        });
        let evaluate = |fixture: &serde_json::Value| -> Result<bool, Box<dyn Error>> {
            let raw = serde_json::to_vec(fixture)?;
            let analysis: Analysis<'_> = serde_json::from_slice(&raw)?;
            analysis.checked_root_impacts()?;
            Ok(analysis.root_reached(Some(0), "p/Suite#", "test"))
        };
        assert!(!evaluate(&fixture).unwrap());
        fixture["evidence"]["root_impacts"] = fixture["evidence"]["requested_roots"].clone();
        assert!(evaluate(&fixture).unwrap());
        fixture["evidence"]["root_impacts"][0]["receiver"] = 2.into();
        assert!(evaluate(&fixture).is_err());
        fixture["evidence"]
            .as_object_mut()
            .unwrap()
            .remove("root_impacts");
        assert!(
            evaluate(&fixture).unwrap(),
            "legacy projection remains readable"
        );
    }
    #[test]
    fn saved_classpath_absence_keeps_kernel_diagnostics_and_rejects_forged_paired_proofs() {
        let report = classpath_compact_fixture();
        let bytes = serde_json::to_vec(&report).unwrap();
        checked_compact(&bytes).unwrap();
        let temporary = tempfile::tempdir().unwrap();
        let path = temporary.path().join("classpath.json");
        std::fs::write(&path, &bytes).unwrap();
        let mut text = Vec::new();
        explain_report(&path, "Independent", &mut text).unwrap();
        let text = String::from_utf8(text).unwrap();
        assert!(text.contains("owning_test_full_classpath"));
        assert!(text.contains("Kernel diagnostic"));
        assert!(text.contains("classpath-absence certificate"));
        assert!(!text.contains("closed-component certificate"));
        let mut rerendered = Vec::new();
        render_saved(&path, &mut rerendered, false).unwrap();
        assert_eq!(rerendered, bytes);
        for change in 0..8 {
            let mut bad = report.clone();
            match change {
                0 => {
                    bad.as_object_mut().unwrap().remove("selection_contract");
                }
                1 => {
                    bad["decisions"][1]["exclusions"]
                        .as_array_mut()
                        .unwrap()
                        .pop();
                }
                2 => bad["decisions"][1]["exclusions"][0]["assumptions"] = 1023.into(),
                3 => bad["decisions"][1]["exclusions"][0]["root"] = 0.into(),
                4 => bad["decisions"][1]["exclusions"][0]["snapshot"] = "head".into(),
                5 => bad["decisions"][1]["exclusions"][0]["certificate"] = "0".repeat(64).into(),
                6 => bad["decisions"][1]["base_node"] = serde_json::Value::Null,
                _ => {
                    bad["decisions"][1]["reasons"][2] = "complete_execution_unaffected".into();
                }
            }
            assert!(
                checked_compact(&serde_json::to_vec(&bad).unwrap()).is_err(),
                "case {change}"
            );
        }
    }

    #[test]
    fn saved_compilation_contract_requires_both_certificates_to_keep_its_assumption() {
        let mut report = classpath_compact_fixture();
        let contract = selector_types::SelectionContract::owning_test_classpath_with_compilation();
        report["selection_contract"] = serde_json::json!({
            "version": selector_types::SelectionContract::VERSION,
            "bits": contract.bits(),
            "assumptions": contract.assumptions().collect::<Vec<_>>()
        });
        for proof in report["decisions"][1]["exclusions"].as_array_mut().unwrap() {
            proof["assumptions"] = contract.bits().into();
        }
        checked_compact(&serde_json::to_vec(&report).unwrap()).unwrap();
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("compilation.json");
        std::fs::write(&path, serde_json::to_vec(&report).unwrap()).unwrap();
        let mut rendered = Vec::new();
        explain_report(&path, "Independent", &mut rendered).unwrap();
        assert!(
            String::from_utf8(rendered)
                .unwrap()
                .contains("ordinary_compilation")
        );
        for side in 0..2 {
            let mut downgraded = report.clone();
            downgraded["decisions"][1]["exclusions"][side]["assumptions"] = 1008.into();
            assert!(checked_compact(&serde_json::to_vec(&downgraded).unwrap()).is_err());
        }
    }
    #[test]
    fn saved_full_classpath_table_explains_excluded_root_without_hiding_kernel_guards() {
        let compact = classpath_compact_fixture();
        let mut row = compact["decisions"][1].clone();
        row["path"] = "Independent.scala".into();
        row["reason"] = "classpath_absence".into();
        let boundary = compact["decisions"][1]["uncertainty"][0]["boundary"].clone();
        let analysis = serde_json::json!({"affected":[],"witnesses":[],"guarded_roots":[2],"evidence":{"contexts":[],"witnesses":[],"root_contexts":[],"values":[],"atoms":[],"value_ids":[],"captures":[],"guard_causes":[boundary]}});
        let mut full = serde_json::json!({"schema_version":1,"base_snapshot":"1".repeat(64),"head_snapshot":"1".repeat(64),"completion":"resource_limited","suite_semantics":"independent_suites","selection_contract":compact["selection_contract"],"suites":[],"base":analysis,"head":analysis,"classpath_exclusions":[row]});
        let temporary = tempfile::tempdir().unwrap();
        let path = temporary.path().join("full-classpath.json");
        std::fs::write(&path, serde_json::to_vec(&full).unwrap()).unwrap();
        let mut text = Vec::new();
        explain_report(&path, "Independent", &mut text).unwrap();
        let text = String::from_utf8(text).unwrap();
        assert!(text.contains("excluded (classpath absence)"));
        assert!(text.contains("Kernel completion: resource_limited"));
        assert!(text.contains("Kernel callback unresolved"));
        assert!(text.contains("kernel diagnostic only"));
        assert!(!text.contains("suite retained conservatively"));
        full["classpath_exclusions"][0]["exclusions"][1]["snapshot_identity"] =
            "9".repeat(64).into();
        std::fs::write(&path, serde_json::to_vec(&full).unwrap()).unwrap();
        let mut output = Vec::new();
        assert!(explain_report(&path, "Independent", &mut output).is_err());
        assert!(output.is_empty());
    }
    #[test]
    fn saved_sequence_carrier_is_explicit_and_rejects_fake_class_or_absent_pack_site() {
        let fixture = serde_json::json!({"contexts":[],"witnesses":[],"root_contexts":[],"captures":[],"value_ids":[],
            "values":[{"atoms":{"start":0,"len":1},"unknown":0}],
            "atoms":[{"kind":4,"site":7,"binding":0,"symbol":"@selector:sequence-elements","carrier":"sequence_elements","identity":"pack_site_and_receiver_root"}]});
        let data = serde_json::to_vec(&fixture).unwrap();
        let evidence: Evidence<'_> = serde_json::from_slice(&data).unwrap();
        let mut out = Vec::new();
        write_value(&mut out, &evidence, 0).unwrap();
        assert!(
            String::from_utf8(out)
                .unwrap()
                .contains("sequence element carrier")
        );
        for field in ["symbol", "site", "carrier", "identity"] {
            let mut bad = fixture.clone();
            bad["atoms"][0][field] = serde_json::Value::Null;
            let data = serde_json::to_vec(&bad).unwrap();
            match serde_json::from_slice::<Evidence<'_>>(&data) {
                Ok(evidence) => assert!(write_value(&mut Vec::new(), &evidence, 0).is_err()),
                Err(_) => {}
            }
        }
    }
    #[test]
    fn saved_requested_source_scope_preserves_notice_hashes_and_legacy_unknown_scope() {
        let mut report = compact_fixture();
        report["change_scope"] = serde_json::json!({
            "mode":"requested_paths","effective_requested_source_paths":["src/Changed.scala"],
            "outside_count":1,"outside_sample_complete":true,"covers_captured_source_delta":false,
            "whole_checkout_omission_authority":false,
            "notice":"Other captured source changes need a separate selection. This result does not authorize omissions for the whole checkout.",
            "outside":[{"base_file_id":4,"head_file_id":9,"path":"target/BuildInfo.scala","context":"project:generated:compile","base_source_sha256":"1".repeat(64),"head_source_sha256":"2".repeat(64)}]
        });
        let temporary = tempfile::tempdir().unwrap();
        let path = temporary.path().join("scope.json");
        let bytes = serde_json::to_vec(&report).unwrap();
        std::fs::write(&path, &bytes).unwrap();
        let mut text = Vec::new();
        explain_report(&path, "Independent", &mut text).unwrap();
        let text = String::from_utf8(text).unwrap();
        assert!(text.contains("separate selection"));
        assert!(text.contains("target/BuildInfo.scala [project:generated:compile]"));
        assert!(text.contains("src/Changed.scala"));
        let mut rendered = Vec::new();
        render_saved(&path, &mut rendered, false).unwrap();
        assert_eq!(rendered, bytes);
        report["change_scope"]["whole_checkout_omission_authority"] = true.into();
        assert!(checked_compact(&serde_json::to_vec(&report).unwrap()).is_err());
        report["change_scope"]["whole_checkout_omission_authority"] = false.into();
        report["change_scope"]["outside"][0]["head_source_sha256"] = "1".repeat(64).into();
        assert!(checked_compact(&serde_json::to_vec(&report).unwrap()).is_err());
        let template = report["change_scope"]["outside"][0].clone();
        report["change_scope"]["outside"] = (0..65)
            .map(|i| {
                let mut row = template.clone();
                row["path"] = format!("target/Generated{i:02}.scala").into();
                row
            })
            .collect::<Vec<_>>()
            .into();
        report["change_scope"]["outside_count"] = 65.into();
        report["change_scope"]["outside_sample_complete"] = false.into();
        let error = checked_compact(&serde_json::to_vec(&report).unwrap())
            .err()
            .unwrap();
        assert!(error.to_string().contains("64 rows"));
        report.as_object_mut().unwrap().remove("change_scope");
        std::fs::write(&path, serde_json::to_vec(&report).unwrap()).unwrap();
        let mut text = Vec::new();
        render_saved(&path, &mut text, true).unwrap();
        assert!(
            String::from_utf8(text)
                .unwrap()
                .contains("scope was not recorded")
        );
    }
    #[test]
    fn compact_saved_outcome_explains_required_and_excluded_and_rerenders_without_analysis() {
        let temporary = tempfile::tempdir().unwrap();
        let path = temporary.path().join("outcome.json");
        let bytes = serde_json::to_vec(&compact_fixture()).unwrap();
        std::fs::write(&path, &bytes).unwrap();
        let mut out = Vec::new();
        explain_report(&path, "Suite", &mut out).unwrap();
        let text = String::from_utf8(out).unwrap();
        assert!(text.contains("required"));
        assert!(text.contains("edge 42"));
        assert!(!text.contains("Independent"));
        let mut out = Vec::new();
        explain_report(&path, "Independent", &mut out).unwrap();
        let text = String::from_utf8(out).unwrap();
        assert!(text.contains("excluded"));
        assert!(!text.contains("edge 42"));
        let mut out = Vec::new();
        render_saved(&path, &mut out, false).unwrap();
        assert_eq!(out, bytes);
        let mut out = Vec::new();
        render_saved(&path, &mut out, true).unwrap();
        assert!(String::from_utf8(out).unwrap().contains("Independent"));
    }
    #[test]
    fn saved_suite_policy_is_explicit_without_exclusions_and_legacy_defaults_shared() {
        let temporary = tempfile::tempdir().unwrap();
        let path = temporary.path().join("policy.json");
        let mut report = compact_fixture();
        report["decisions"].as_array_mut().unwrap().truncate(1);
        report["suite_semantics"] = "independent_suites".into();
        std::fs::write(&path, serde_json::to_vec(&report).unwrap()).unwrap();
        for explain in [false, true] {
            let mut out = Vec::new();
            if explain {
                explain_report(&path, "Suite", &mut out).unwrap();
            } else {
                render_saved(&path, &mut out, true).unwrap();
            }
            let text = String::from_utf8(out).unwrap();
            assert!(text.contains("Suite semantics: independent_suites"));
            assert!(text.contains("Conditional assumption:"));
            assert!(text.contains("isolation has not been verified"));
        }
        report.as_object_mut().unwrap().remove("suite_semantics");
        std::fs::write(&path, serde_json::to_vec(&report).unwrap()).unwrap();
        let mut out = Vec::new();
        render_saved(&path, &mut out, true).unwrap();
        let text = String::from_utf8(out).unwrap();
        assert!(text.contains("Suite semantics: shared_state"));
        assert!(!text.contains("Conditional assumption:"));
        let mut out = Vec::new();
        render_saved(&path, &mut out, false).unwrap();
        let rerendered: serde_json::Value = serde_json::from_slice(&out).unwrap();
        report["suite_semantics"] = "shared_state".into();
        assert_eq!(rerendered, report);
        // Full evidence schema1 uses the same exact legacy default and notice.
        let mut full = serde_json::json!({"schema_version":1,"suites":[{"suite_id":0,"node":0,"name":"Suite","symbol":"p/Suite#","context":"test","guarded":true}],"base":null,"head":{"affected":[],"guarded_roots":[0],"witnesses":[]}});
        for mode in [None, Some("independent_suites")] {
            if let Some(mode) = mode {
                full["suite_semantics"] = mode.into();
            }
            std::fs::write(&path, serde_json::to_vec(&full).unwrap()).unwrap();
            let mut out = Vec::new();
            explain_report(&path, "Suite", &mut out).unwrap();
            let text = String::from_utf8(out).unwrap();
            assert_eq!(text.contains("Conditional assumption:"), mode.is_some());
            assert!(text.contains(mode.unwrap_or("shared_state")));
        }
    }
    #[test]
    fn saved_suite_policy_rejects_invalid_modes_and_conflicting_certificate_bits() {
        let mut report = compact_fixture();
        for bad in [
            serde_json::Value::Null,
            "physical_isolation".into(),
            16.into(),
        ] {
            report["suite_semantics"] = bad;
            assert!(checked_compact(&serde_json::to_vec(&report).unwrap()).is_err());
        }
        report["decisions"][1]["exclusions"] = serde_json::json!([{
            "snapshot":"head","snapshot_identity":"1".repeat(64),"root":2,
            "certificate":"2".repeat(64),"assumptions":17}]);
        report["suite_semantics"] = "shared_state".into();
        assert!(checked_compact(&serde_json::to_vec(&report).unwrap()).is_err());
        report["suite_semantics"] = "independent_suites".into();
        checked_compact(&serde_json::to_vec(&report).unwrap()).unwrap();
        report["decisions"][1]["exclusions"][0]["assumptions"] = 1.into();
        assert!(checked_compact(&serde_json::to_vec(&report).unwrap()).is_err());
        report["suite_semantics"] = "shared_state".into();
        checked_compact(&serde_json::to_vec(&report).unwrap()).unwrap();
        report.as_object_mut().unwrap().remove("suite_semantics");
        checked_compact(&serde_json::to_vec(&report).unwrap()).unwrap();
        report["decisions"][1]["exclusions"][0]["assumptions"] = 17.into();
        assert!(checked_compact(&serde_json::to_vec(&report).unwrap()).is_err());
    }
    #[test]
    fn saved_named_contract_preserves_exact_assumptions_and_rejects_hidden_or_stale_models() {
        use selector_types::{SelectionContract, SuiteSemantics};
        let mut report = compact_fixture();
        let contract = SelectionContract::current(SuiteSemantics::Independent);
        report["suite_semantics"] = "independent_suites".into();
        report["selection_contract"] = serde_json::json!({
            "version":SelectionContract::VERSION,"bits":contract.bits(),
            "assumptions":contract.assumptions().collect::<Vec<_>>()});
        report["decisions"][1]["exclusions"] = serde_json::json!([{
            "snapshot":"head","snapshot_identity":"1".repeat(64),"root":2,
            "certificate":"2".repeat(64),"assumptions":15|contract.bits()}]);
        let bytes = serde_json::to_vec(&report).unwrap();
        checked_compact(&bytes).unwrap();
        let temporary = tempfile::tempdir().unwrap();
        let path = temporary.path().join("named-contract.json");
        std::fs::write(&path, &bytes).unwrap();
        let mut out = Vec::new();
        render_saved(&path, &mut out, false).unwrap();
        assert_eq!(out, bytes);
        let mut out = Vec::new();
        render_saved(&path, &mut out, true).unwrap();
        let text = String::from_utf8(out).unwrap();
        for name in contract.assumptions() {
            assert!(text.contains(name));
        }
        assert!(
            text.contains(
                "explicitly retained timing/performance-sensitive suites remain selected"
            )
        );
        for change in 0..7 {
            let mut bad = report.clone();
            match change {
                0 => {
                    bad.as_object_mut().unwrap().remove("selection_contract");
                }
                1 => bad["selection_contract"]["version"] = "unrecognized/2".into(),
                2 => bad["selection_contract"]["bits"] = (contract.bits() | 1).into(),
                3 => bad["selection_contract"]["assumptions"][0] = "functional_behavior".into(),
                4 => bad["suite_semantics"] = "shared_state".into(),
                5 => bad["decisions"][1]["exclusions"][0]["assumptions"] = 31.into(),
                _ => bad["selection_contract"] = serde_json::Value::Null,
            }
            assert!(
                checked_compact(&serde_json::to_vec(&bad).unwrap()).is_err(),
                "case {change}"
            );
        }
        report.as_object_mut().unwrap().remove("selection_contract");
        report["decisions"][1]["exclusions"][0]["assumptions"] = 31.into();
        let bytes = serde_json::to_vec(&report).unwrap();
        let legacy = checked_compact(&bytes).unwrap();
        assert_eq!(
            checked_selection_contract(&legacy.selection_contract, legacy.suite_semantics.mode)
                .unwrap()
                .bits(),
            16
        );
        let mut out = Vec::new();
        write_saved_contract(
            &mut out,
            &legacy.selection_contract,
            legacy.suite_semantics.mode,
        )
        .unwrap();
        let text = String::from_utf8(out).unwrap();
        assert!(text.contains("legacy (no additional assumptions recorded)"));
        assert!(!text.contains("functional_behavior"));
    }
    #[test]
    fn compact_saved_outcome_rejects_wrong_snapshot_seed_cycle_and_selected_status() {
        for mutation in ["snapshot", "seed", "cycle", "status"] {
            let mut report = compact_fixture();
            match mutation {
                "snapshot" => {
                    report["decisions"][0]["proofs"][0]["snapshot_identity"] = "2".repeat(64).into()
                }
                "seed" => report["execution_seeds"]["head"] = serde_json::json!([7]),
                "cycle" => report["decisions"][0]["proofs"][0]["chain"][0]["next"] = 0.into(),
                _ => report["suites"][0]["guarded"] = true.into(),
            }
            let bytes = serde_json::to_vec(&report).unwrap();
            assert!(checked_compact(&bytes).is_err(), "{mutation}");
        }
    }
    #[test]
    fn saved_shared_heap_guard_explains_potential_exposure_without_an_execution_proof() {
        let mut report = compact_fixture();
        report["completion"] = "conservative".into();
        report["decisions"].as_array_mut().unwrap().truncate(1);
        report["decisions"][0]["status"] = "unknown".into();
        report["decisions"][0]["guarded"] = true.into();
        report["suites"][0]["guarded"] = true.into();
        report["decisions"][0]["proofs"] = serde_json::json!([]);
        report["decisions"][0]["reasons"] = serde_json::json!(["opaque_shared_heap"]);
        report["decisions"][0]["explanation"] = serde_json::json!([
            "This root may read shared state that another runnable opaque component can mutate."
        ]);
        let temporary = tempfile::tempdir().unwrap();
        let path = temporary.path().join("report.json");
        std::fs::write(&path, serde_json::to_vec(&report).unwrap()).unwrap();
        let mut out = Vec::new();
        explain_report(&path, "Suite", &mut out).unwrap();
        let text = String::from_utf8(out).unwrap();
        assert!(text.contains("unknown") && text.contains("shared state"));
        assert!(!text.contains("edge 42") && !text.contains("reached boundary"));
        let mut rerendered = Vec::new();
        render_saved(&path, &mut rerendered, false).unwrap();
        assert_eq!(
            serde_json::from_slice::<serde_json::Value>(&rerendered).unwrap(),
            report
        );
        report["decisions"][0]["status"] = "excluded".into();
        report["decisions"][0]["guarded"] = false.into();
        report["decisions"][0]["reasons"] =
            serde_json::json!(["opaque_shared_heap", "complete_execution_unaffected"]);
        report["decisions"][0]["explanation"] =
            serde_json::json!(["Shared heap unknown.", "No observed impact."]);
        report["suites"] = serde_json::json!([]);
        assert!(checked_compact(&serde_json::to_vec(&report).unwrap()).is_err());

        let mut full = serde_json::json!({"schema_version":1,"suites":[{"suite_id":0,"node":0,"name":"Suite","symbol":"p/Suite#","context":"test","guarded":true,"opaque_shared_heap":true}],"base":null,"head":{"affected":[],"witnesses":[]}});
        std::fs::write(&path, serde_json::to_vec(&full).unwrap()).unwrap();
        let mut out = Vec::new();
        explain_report(&path, "Suite", &mut out).unwrap();
        let text = String::from_utf8(out).unwrap();
        assert!(text.contains("shared state") && !text.contains("execution proof"));
        full["suites"][0]["guarded"] = false.into();
        std::fs::write(&path, serde_json::to_vec(&full).unwrap()).unwrap();
        assert!(explain_report(&path, "Suite", &mut Vec::new()).is_err());
    }
    #[test]
    fn compact_guard_only_explanation_preserves_exact_runtime_reason_without_fake_proof() {
        let mut report = compact_fixture();
        report["completion"] = "conservative".into();
        report["decisions"].as_array_mut().unwrap().truncate(1);
        report["decisions"][0]["status"] = "unknown".into();
        report["decisions"][0]["guarded"] = true.into();
        report["suites"][0]["guarded"] = true.into();
        report["decisions"][0]["proofs"] = serde_json::json!([]);
        report["decisions"][0]["reasons"] = serde_json::json!(["changed_input_unknown"]);
        report["decisions"][0]["explanation"] =
            serde_json::json!(["Changed metadata has incomplete runtime binding."]);
        report["guard_causes"] = serde_json::json!([{"snapshot":"head","reason":"external_input","kind":"unsupported_model","path":"model.yaml","symbol":"","detail":"","external":{"reason":"missing_operation_binding","message":"operation has no compiler route identity","schema_path":"api.yaml","operation_path":"/value","verb":"get","suite_name":"Suite"}}]);
        let temporary = tempfile::tempdir().unwrap();
        let path = temporary.path().join("report.json");
        std::fs::write(&path, serde_json::to_vec(&report).unwrap()).unwrap();
        let mut out = Vec::new();
        explain_report(&path, "Suite", &mut out).unwrap();
        let text = String::from_utf8(out).unwrap();
        for expected in [
            "unknown",
            "model.yaml",
            "missing_operation_binding",
            "api.yaml",
            "/value",
            "get",
        ] {
            assert!(text.contains(expected), "{expected}");
        }
        assert!(!text.contains("edge 42"));
    }
    #[test]
    fn compact_saved_actual_boundary_is_bound_to_its_suite_snapshot() {
        let mut report = compact_fixture();
        report["decisions"][0]["guarded"] = true.into();
        report["suites"][0]["guarded"] = true.into();
        report["decisions"][0]["uncertainty"] = serde_json::json!([{"snapshot":"head","boundary":{"root":0,"node":9,"kind":"unsupported_model","boundary_symbol":"p/OpaqueRouter#","path":"Router.scala","detail":"missing callback route recipe"},"metadata":[{"reason":"actual_router_join_missing","metadata_path":"routes.ts"}]}]);
        let temporary = tempfile::tempdir().unwrap();
        let path = temporary.path().join("report.json");
        std::fs::write(&path, serde_json::to_vec(&report).unwrap()).unwrap();
        let mut out = Vec::new();
        explain_report(&path, "Suite", &mut out).unwrap();
        let text = String::from_utf8(out).unwrap();
        assert!(text.contains("OpaqueRouter"));
        assert!(text.contains("routes.ts"));
        assert!(text.contains("missing callback route recipe"));
        assert!(!text.contains("Independent"));
        report["decisions"][0]["uncertainty"][0]["boundary"]["root"] = 2.into();
        let bytes = serde_json::to_vec(&report).unwrap();
        assert!(checked_compact(&bytes).is_err());
    }
    #[test]
    fn saved_metadata_issue_cannot_be_rendered_as_runtime_boundary() {
        let mut report = compact_fixture();
        report["decisions"][0]["guarded"] = true.into();
        report["suites"][0]["guarded"] = true.into();
        report["decisions"][0]["uncertainty"] = serde_json::json!([{"snapshot":"head","boundary":{"root":0,"node":9,"kind":"missing_binary","boundary_symbol":"p/Library#","path":"Library.class","detail":""},"metadata":[]}]);
        for kind in [
            "missing_source",
            "stale_source",
            "unsupported_schema",
            "missing_syntax",
            "unresolved_symbol",
            "unknown_execution",
            "missing_binary",
            "unsupported_model",
            "context_conflict",
            "resource_limit",
            "invalid_input",
        ] {
            report["decisions"][0]["uncertainty"][0]["boundary"]["kind"] = kind.into();
            checked_compact(&serde_json::to_vec(&report).unwrap()).unwrap();
        }
        report["decisions"][0]["uncertainty"][0]["boundary"]["kind"] =
            "incomplete_hierarchy".into();
        let boundary = report["decisions"][0]["uncertainty"][0]["boundary"].clone();
        let mut full = serde_json::json!({"schema_version":1,"suites":[{"suite_id":0,"node":0,"base_node":null,"name":"Suite","symbol":"p/Suite#","context":"test","guarded":true}],"base":null,"head":{"affected":[],"guarded_roots":[0],"witnesses":[],"evidence":{"contexts":[],"witnesses":[],"root_contexts":[],"values":[],"atoms":[],"value_ids":[],"captures":[],"guard_causes":[boundary]}}});
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("saved.json");
        for saved in [&report, &full] {
            std::fs::write(&path, serde_json::to_vec(saved).unwrap()).unwrap();
            let mut out = Vec::new();
            assert!(
                explain_report(&path, "Suite", &mut out)
                    .unwrap_err()
                    .to_string()
                    .contains("metadata issue")
            );
            assert!(out.is_empty());
        }
        full["head"]["evidence"]["guard_causes"] = serde_json::json!([]);
        full["head"]["runtime_diagnostics"] = serde_json::json!([{"kind":"incomplete_hierarchy"}]);
        std::fs::write(&path, serde_json::to_vec(&full).unwrap()).unwrap();
        let mut out = Vec::new();
        assert!(
            explain_report(&path, "Suite", &mut out)
                .unwrap_err()
                .to_string()
                .contains("metadata issue")
        );
        assert!(out.is_empty());
        full["head"]["runtime_diagnostics"] = serde_json::json!([]);
        for table in ["obligations", "guard_causes"] {
            full[table] = serde_json::json!([{"kind":"incomplete_hierarchy"}]);
            std::fs::write(&path, serde_json::to_vec(&full).unwrap()).unwrap();
            assert!(
                explain_report(&path, "Suite", &mut out)
                    .unwrap_err()
                    .to_string()
                    .contains("metadata issue")
            );
            assert!(out.is_empty());
            full[table] = serde_json::json!([]);
        }
        full["head"]["obligations"] = serde_json::json!([{"kind":"incomplete_hierarchy"}]);
        std::fs::write(&path, serde_json::to_vec(&full).unwrap()).unwrap();
        assert!(
            explain_report(&path, "Suite", &mut out)
                .unwrap_err()
                .to_string()
                .contains("metadata issue")
        );
        assert!(out.is_empty());
        report["decisions"][0]["uncertainty"] = serde_json::json!([]);
        report["guard_causes"] = serde_json::json!([{"snapshot":"head","reason":"unscoped_fact_issue","kind":"incomplete_hierarchy","path":"Library.class","symbol":"p/Library#","detail":""}]);
        std::fs::write(&path, serde_json::to_vec(&report).unwrap()).unwrap();
        assert!(explain_report(&path, "Suite", &mut out).is_err());
        assert!(out.is_empty());
    }
    #[test]
    fn saved_runtime_guard_keeps_actual_site_and_rejects_inconsistent_provenance() {
        let mut report = compact_fixture();
        report["decisions"][0]["guarded"] = true.into();
        report["suites"][0]["guarded"] = true.into();
        report["decisions"][0]["uncertainty"] = serde_json::json!([{"snapshot":"head","boundary":{"root":0,"node":9,"kind":"unknown_execution","boundary_symbol":"p/Router#","path":"Router.scala","detail":"","runtime_reason":"unknown_callback_value","operation":42,"opcode":"invoke_callback","operation_path":"Router.scala","span":{"start":4,"end":9}},"metadata":[]}]);
        let temporary = tempfile::tempdir().unwrap();
        let path = temporary.path().join("report.json");
        std::fs::write(&path, serde_json::to_vec(&report).unwrap()).unwrap();
        let mut out = Vec::new();
        explain_report(&path, "Suite", &mut out).unwrap();
        let text = String::from_utf8(out).unwrap();
        assert!(text.contains("runtime reason: unknown_callback_value; operation 42 (invoke_callback); Router.scala bytes 4..9"));
        let full = serde_json::json!({"schema_version":1,"suites":[{"suite_id":0,"node":0,"base_node":null,"name":"Suite","symbol":"p/Suite#","context":"test","guarded":true}],"base":null,"head":{"affected":[],"guarded_roots":[0],"witnesses":[],"evidence":{"contexts":[],"witnesses":[],"root_contexts":[],"values":[],"atoms":[],"value_ids":[],"captures":[],"guard_causes":[report["decisions"][0]["uncertainty"][0]["boundary"]]}}});
        std::fs::write(&path, serde_json::to_vec(&full).unwrap()).unwrap();
        let mut out = Vec::new();
        explain_report(&path, "Suite", &mut out).unwrap();
        assert!(String::from_utf8(out).unwrap().contains("runtime reason: unknown_callback_value; operation 42 (invoke_callback); Router.scala bytes 4..9"));
        let boundary = &mut report["decisions"][0]["uncertainty"][0]["boundary"];
        boundary["span"]["end"] = 3.into();
        assert!(checked_compact(&serde_json::to_vec(&report).unwrap()).is_err());
        report["decisions"][0]["uncertainty"][0]["boundary"]["span"]["end"] = 9.into();
        report["decisions"][0]["uncertainty"][0]["boundary"]["opcode"] = "load_field".into();
        assert!(checked_compact(&serde_json::to_vec(&report).unwrap()).is_err());
        report["decisions"][0]["uncertainty"][0]["boundary"]["opcode"] = "invoke_callback".into();
        report["decisions"][0]["uncertainty"][0]["boundary"]["operation"] = serde_json::Value::Null;
        assert!(checked_compact(&serde_json::to_vec(&report).unwrap()).is_err());
    }
    #[test]
    fn saved_partial_future_reason_accepts_calls_and_rejects_callback_or_unknown_opcodes() {
        let mut report = compact_fixture();
        report["decisions"][0]["guarded"] = true.into();
        report["suites"][0]["guarded"] = true.into();
        report["decisions"][0]["uncertainty"] = serde_json::json!([{"snapshot":"head","boundary":{"root":0,"node":9,"kind":"unknown_execution","boundary_symbol":"p/Continuation#","path":"Pipeline.scala","detail":"","runtime_reason":"incomplete_deferred_callback","operation":42,"opcode":"call","operation_path":"Pipeline.scala","span":{"start":4,"end":9}},"metadata":[]}]);
        let temporary = tempfile::tempdir().unwrap();
        let path = temporary.path().join("report.json");
        std::fs::write(&path, serde_json::to_vec(&report).unwrap()).unwrap();
        let mut out = Vec::new();
        explain_report(&path, "Suite", &mut out).unwrap();
        assert!(
            String::from_utf8(out)
                .unwrap()
                .contains("runtime reason: incomplete_deferred_callback; operation 42 (call)")
        );
        for opcode in ["invoke_callback", "unknown", "load_field"] {
            report["decisions"][0]["uncertainty"][0]["boundary"]["opcode"] = opcode.into();
            assert!(checked_compact(&serde_json::to_vec(&report).unwrap()).is_err());
        }
    }
    #[test]
    fn saved_typed_constraints_require_explicit_bounds_and_no_capture_binding() {
        let mut json = serde_json::json!({
            "contexts": [], "witnesses": [], "root_contexts": [],
            "values": [{"atoms":{"start":0,"len":1},"unknown":16}],
            "atoms": [{"kind":3,"binding":0,"symbol":"p/Factory#make().",
                "constraint":"static_result_constraint","upper_bounds":["p/Narrow#","p/Marker#"]}],
            "value_ids": [], "captures": []
        });
        let render = |json: &serde_json::Value| {
            let bytes = serde_json::to_vec(json).unwrap();
            let evidence: Evidence<'_> = serde_json::from_slice(&bytes).unwrap();
            let mut out = Vec::new();
            write_value(&mut out, &evidence, 0)?;
            Ok::<_, Box<dyn Error>>(String::from_utf8(out)?)
        };
        let text = render(&json).unwrap();
        assert!(
            text.contains("static result constraint p/Factory#make(). <= [p/Narrow# & p/Marker#]")
        );
        assert!(!text.contains("object "));
        assert!(!text.contains("capture"));
        json["atoms"][0]["binding"] = 1.into();
        assert!(render(&json).is_err());
        json["atoms"][0]["binding"] = 0.into();
        json["atoms"][0]["upper_bounds"] = serde_json::json!([""]);
        assert!(render(&json).is_err());
        json["atoms"][0]["upper_bounds"] = serde_json::json!([]);
        assert!(render(&json).is_err());
        json["atoms"][0]
            .as_object_mut()
            .unwrap()
            .remove("constraint");
        assert!(render(&json).is_err());
    }
    #[test]
    fn saved_object_origins_require_a_checked_dictionary_and_keep_coarse_legacy_values() {
        let mut json = serde_json::json!({
            "requested_roots":[{"receiver":0,"receiver_symbol":"p/Suite#","receiver_context":"test"}],
            "heap_origins":[{"symbol_id":0,"symbol":"p/Suite#","context":"test"},
                {"symbol_id":4,"symbol":"p/PriorSuite#","context":"test"}],
            "contexts":[],"witnesses":[],"root_contexts":[],"value_ids":[],"captures":[],
            "values":[{"atoms":{"start":0,"len":1},"unknown":0}],
            "atoms":[{"kind":1,"binding":1,"symbol":"p/Carrier#"}]
        });
        let render = |json: &serde_json::Value| {
            let bytes = serde_json::to_vec(json).unwrap();
            let evidence: Evidence<'_> = serde_json::from_slice(&bytes).unwrap();
            let mut out = Vec::new();
            write_value(&mut out, &evidence, 0)?;
            Ok::<_, Box<dyn Error>>(String::from_utf8(out)?)
        };
        assert!(
            render(&json)
                .unwrap()
                .contains("with receiver origin p/Suite#")
        );
        json["atoms"][0]["binding"] = 5.into();
        assert!(
            render(&json)
                .unwrap()
                .contains("with receiver origin p/PriorSuite#")
        );
        json["atoms"][0]["binding"] = 3.into();
        assert!(render(&json).is_err());
        json["atoms"][0]["binding"] = 1.into();
        json["heap_origins"][0]["context"] = "forged".into();
        assert!(render(&json).is_err());
        json["heap_origins"][0]["context"] = "test".into();
        json["heap_origins"][1]["symbol_id"] = 0.into();
        assert!(render(&json).is_err());
        json["atoms"][0]["binding"] = 0.into();
        json.as_object_mut().unwrap().remove("heap_origins");
        assert_eq!(render(&json).unwrap(), "value0[object p/Carrier#]");
        json["atoms"][0]["binding"] = 1.into();
        assert!(render(&json).is_err());
    }
    #[test]
    fn saved_explanation_renders_only_the_selected_chain() {
        let report=br#"{"schema_version":1,"suites":[{"suite_id":0,"node":0,"base_node":null,"name":"Suite","symbol":"p/Suite#","context":"test","guarded":false}],"base":null,"head":{"affected":[0,1,2,3],"witnesses":[{"node":0,"next":1,"edge":0,"kind":"call","source":"p/Suite#","target":"changed"},{"node":2,"next":3,"edge":1,"kind":"call","source":"UNRELATED","target":"other"}]}}"#;
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("result.json");
        std::fs::write(&path, report).unwrap();
        let mut out = Vec::new();
        explain_report(&path, "Suite", &mut out).unwrap();
        let text = String::from_utf8(out).unwrap();
        assert!(text.contains("p/Suite# --call"));
        assert!(!text.contains("UNRELATED"));
    }
    #[test]
    fn malformed_saved_chain_is_rejected() {
        let report=br#"{"schema_version":1,"suites":[{"suite_id":0,"node":0,"name":"Suite","symbol":"p/Suite#","context":"test","guarded":false}],"base":null,"head":{"affected":[0,1],"witnesses":[{"node":0,"next":1,"edge":0,"kind":"call","source":"A","target":"B"},{"node":1,"next":0,"edge":1,"kind":"call","source":"B","target":"A"}]}}"#;
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("result.json");
        std::fs::write(&path, report).unwrap();
        assert!(explain_report(&path, "Suite", &mut Vec::new()).is_err());
    }
    #[test]
    fn unresolved_catalogue_suite_has_uncertainty_but_no_invented_proof() {
        let report=br#"{"schema_version":1,"suites":[{"suite_id":0,"node":null,"name":"MissingSuite","symbol":"","context":"","guarded":true}],"base":null,"head":{"affected":[],"witnesses":[]}}"#;
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("result.json");
        std::fs::write(&path, report).unwrap();
        let mut out = Vec::new();
        explain_report(&path, "MissingSuite", &mut out).unwrap();
        let text = String::from_utf8(out).unwrap();
        assert!(text.contains("compiler definition is unavailable"));
        assert!(!text.contains("--"));
    }
    #[test]
    fn unguarded_suite_without_retained_proof_is_rejected() {
        let report=br#"{"schema_version":1,"suites":[{"suite_id":0,"node":0,"name":"Suite","symbol":"p/Suite#","context":"test","guarded":false}],"base":null,"head":{"affected":[],"witnesses":[]}}"#;
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("result.json");
        std::fs::write(&path, report).unwrap();
        assert!(explain_report(&path, "Suite", &mut Vec::new()).is_err());
    }
    #[test]
    fn saved_context_chain_uses_its_capture_binding_and_excludes_other_roots() {
        let mut report = serde_json::json!({"schema_version":1,"suites":[{"suite_id":0,"node":0,"name":"Suite","symbol":"p/Suite#","context":"test","guarded":false}],"base":null,
            "head":{"affected":[0,1,2,3],"witnesses":[],"evidence":{
                "contexts":[{"id":3,"node":0,"symbol":"p/Suite#","receiver":0,"arguments":{"start":0,"len":0}},
                    {"id":7,"node":1,"symbol":"Changed","receiver":0,"arguments":{"start":0,"len":0}},
                    {"id":20,"node":2,"symbol":"UNRELATED","receiver":0,"arguments":{"start":0,"len":0}},
                    {"id":21,"node":3,"symbol":"Other","receiver":0,"arguments":{"start":0,"len":0}}],
                "witnesses":[{"context":3,"next":7,"edge":5,"binding":5},{"context":20,"next":21,"edge":6,"binding":null}],
                "root_contexts":[3,20],"values":[{"atoms":{"start":0,"len":0},"unknown":0}],"atoms":[],"value_ids":[],
                "captures":[{"binding":5,"receiver":0,"arguments":{"start":0,"len":0}}]}}});
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("result.json");
        std::fs::write(&path, serde_json::to_vec(&report).unwrap()).unwrap();
        let mut out = Vec::new();
        explain_report(&path, "Suite", &mut out).unwrap();
        let text = String::from_utf8(out).unwrap();
        assert!(text.contains("capture5 receiver=value0"));
        assert!(text.contains("Changed"));
        assert!(!text.contains("UNRELATED"));
        report["head"]["evidence"]["captures"] = serde_json::json!([]);
        std::fs::write(&path, serde_json::to_vec(&report).unwrap()).unwrap();
        assert!(explain_report(&path, "Suite", &mut Vec::new()).is_err());
    }
    #[test]
    fn guarded_explanation_preserves_runtime_causes_without_unrelated_node_metadata() {
        let report = serde_json::json!({"schema_version":1,"suites":[{"suite_id":0,"node":0,"name":"Suite","symbol":"p/Suite#","context":"test","path":"Suite.scala","guarded":true}],"base":null,
            "head":{"affected":[0],"guarded_roots":[0],"witnesses":[],"runtime_diagnostics":[
                {"kind":"unsupported_model","scope":"node","node":0,"file_id":0,"path":"Suite.scala","symbol_id":0,"symbol":"p/Suite#","reason":"OpenAPI callback registration is absent","metadata_path":"runtime/openapi.json"},
                {"kind":"unsupported_model","scope":"node","node":1,"file_id":0,"path":"Suite.scala","symbol_id":0,"symbol":"p/Suite#","reason":"UNRELATED node-only cause","metadata_path":"runtime/unrelated.json"},
                {"kind":"unsupported_model","scope":"unscoped","node":null,"file_id":null,"symbol_id":null,"path":"","symbol":"","reason":"runtime manifest is unavailable","metadata_path":"runtime/manifest.json"}]}});
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("result.json");
        std::fs::write(&path, serde_json::to_vec(&report).unwrap()).unwrap();
        let mut out = Vec::new();
        explain_report(&path, "Suite", &mut out).unwrap();
        let text = String::from_utf8(out).unwrap();
        assert!(text.contains("OpenAPI callback registration is absent"));
        assert!(text.contains("runtime/openapi.json"));
        assert!(text.contains("runtime manifest is unavailable"));
        assert!(!text.contains("UNRELATED"));
        assert!(!text.contains("runtime/unrelated.json"));
    }
}
