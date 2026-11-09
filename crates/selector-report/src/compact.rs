//! Standalone suite decisions retain only the proof chains needed by the answer.
use super::*;
use selector_result::*;

pub(crate) fn side_name(side: SnapshotSide) -> &'static str {
    match side {
        SnapshotSide::Base => "base",
        SnapshotSide::Head => "head",
    }
}
pub(crate) fn guard_reason(reason: ChangeGuardReason) -> &'static str {
    match reason {
        ChangeGuardReason::UncapturedChangedPath => "uncaptured_changed_path",
        ChangeGuardReason::UnverifiedSource => "unverified_source",
        ChangeGuardReason::UnverifiedSyntax => "unverified_syntax",
        ChangeGuardReason::NoDeclarations => "no_declarations",
        ChangeGuardReason::UnscopedFactIssue => "unscoped_fact_issue",
        ChangeGuardReason::MissingDeclarationNode => "missing_declaration_node",
        ChangeGuardReason::ExternalInput => "external_input",
        ChangeGuardReason::UnspecifiedFallback => "unspecified_fallback",
    }
}

pub(crate) fn write_guard_causes<W: Write>(
    out: &mut W,
    s: &ReportSnapshots<'_>,
    causes: &[ChangeGuardCause],
) -> Result<(), Error> {
    out.write_all(b"[")?;
    for (i, cause) in causes.iter().enumerate() {
        if i != 0 {
            out.write_all(b",")?;
        }
        let facts = match cause.side {
            SnapshotSide::Base => s.base_facts,
            SnapshotSide::Head => s.head_facts,
        };
        validate_obligation(
            facts,
            &Obligation {
                kind: cause.kind,
                file: cause.file,
                symbol: cause.symbol,
                detail: cause.detail,
            },
        )?;
        out.write_all(b"{\"snapshot\":")?;
        json_string(out, side_name(cause.side))?;
        out.write_all(b",\"reason\":")?;
        json_string(out, guard_reason(cause.reason))?;
        out.write_all(b",\"kind\":")?;
        json_string(out, issue_name(cause.kind))?;
        out.write_all(b",\"file_id\":")?;
        json_id(out, cause.file.0)?;
        out.write_all(b",\"path\":")?;
        json_string(
            out,
            cause
                .path
                .as_deref()
                .unwrap_or_else(|| facts.path(cause.file)),
        )?;
        out.write_all(b",\"symbol_id\":")?;
        json_id(out, cause.symbol.0)?;
        out.write_all(b",\"symbol\":")?;
        json_string(out, facts.symbol_name(cause.symbol))?;
        out.write_all(b",\"detail\":")?;
        json_string(out, facts.text(cause.detail))?;
        if let Some(external) = &cause.external {
            out.write_all(b",\"external\":{\"reason\":")?;
            json_string(out, &external.reason)?;
            out.write_all(b",\"message\":")?;
            json_string(out, &external.message)?;
            for (key, value) in [
                ("suite_name", &external.suite_name),
                ("schema_path", &external.schema_path),
                ("operation_path", &external.operation_path),
                ("verb", &external.verb),
            ] {
                if let Some(value) = value {
                    out.write_all(b",")?;
                    json_string(out, key)?;
                    out.write_all(b":")?;
                    json_string(out, value)?;
                }
            }
            out.write_all(b"}")?;
        }
        out.write_all(b"}")?;
    }
    out.write_all(b"]")?;
    Ok(())
}

fn write_suite_identity<W: Write>(
    out: &mut W,
    s: &ReportSnapshots<'_>,
    decision: &SuiteDecision,
) -> Result<(), Error> {
    let suite = &s.head_facts.suites[decision.suite.index()];
    write!(out, "\"suite_id\":{},\"node\":", decision.suite.0)?;
    json_id(out, decision.node.0)?;
    out.write_all(b",\"base_node\":")?;
    json_id(out, decision.base_node.0)?;
    out.write_all(b",\"name\":")?;
    json_string(out, s.head_facts.text(suite.name))?;
    out.write_all(b",\"symbol\":")?;
    json_string(out, s.head_facts.symbol_name(suite.symbol))?;
    out.write_all(b",\"context\":")?;
    json_string(
        out,
        s.head_facts.symbols.get(suite.symbol.index()).map_or_else(
            || {
                s.head_facts
                    .files
                    .get(suite.file.index())
                    .map_or("", |f| s.head_facts.text(f.context))
            },
            |symbol| s.head_facts.text(symbol.context),
        ),
    )?;
    out.write_all(b",\"path\":")?;
    json_string(out, s.head_facts.path(suite.file))?;
    write!(out, ",\"guarded\":{}", decision.guarded)?;
    Ok(())
}

const CLASSPATH_ABSENCE_TEXT: &str = "Under the owning Test/fullClasspath premise, paired product proofs show the requested changed application inputs absent from this suite's runtime classpath. Kernel execution uncertainty is preserved separately.";

const REASONS: &[(u32, &str, &str)] = &[
    (
        DECISION_HEAD_IMPACT,
        "head_execution_impact",
        "A head execution path reaches a changed execution seed.",
    ),
    (
        DECISION_BASE_IMPACT,
        "base_execution_impact",
        "A base execution path reaches a changed execution seed; the matching head suite remains runnable.",
    ),
    (
        DECISION_SCOPED_GUARD,
        "scoped_execution_unknown",
        "This root reaches an unresolved execution boundary.",
    ),
    (
        DECISION_CHANGED_INPUT_GUARD,
        "changed_input_unknown",
        "A changed input lacks a complete source or identity scope; see guard_causes.",
    ),
    (
        DECISION_QUERY_UNSCOPED,
        "query_scope_unknown",
        "Execution uncertainty has no complete root scope.",
    ),
    (
        DECISION_RESOURCE_LIMIT,
        "resource_limit",
        "The analysis exhausted a resource budget before proving this root unaffected.",
    ),
    (
        DECISION_MISSING_ROOT,
        "missing_suite_definition",
        "The catalogue names this suite, but its compiler execution root is unavailable.",
    ),
    (
        DECISION_COMPLETE_UNAFFECTED,
        "complete_execution_unaffected",
        "The completed base/head analysis found no changed execution dependency or relevant unresolved boundary for this root.",
    ),
    (
        DECISION_CERTIFIED_EXCLUSION,
        "closed_component_exclusion",
        "A planner certificate proves the potential execution component independent of these changed seeds.",
    ),
    (
        DECISION_PLAN_REFUTED,
        "planner_exclusion_refuted",
        "Observed execution or uncertainty invalidated this root's potential-dependency exclusion; the suite is retained.",
    ),
    (
        DECISION_OPAQUE_SHARED_HEAP,
        "opaque_shared_heap",
        "This root may read shared state that a changed or unresolved writer can mutate; observed execution does not establish that it is unaffected.",
    ),
    (
        DECISION_CLASSPATH_ABSENCE,
        "classpath_absence",
        CLASSPATH_ABSENCE_TEXT,
    ),
];

fn write_proof<W: Write>(
    out: &mut W,
    side: &str,
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    index: &WitnessIndex<'_>,
    root: NodeId,
    seeds: &[NodeId],
) -> Result<(), Error> {
    out.write_all(b"{\"snapshot\":")?;
    json_string(out, side)?;
    write!(
        out,
        ",\"root\":{},\"snapshot_identity\":\"{}\"",
        root.0, graph.identity
    )?;
    if index.analysis.root_impacts().is_some() {
        out.write_all(b",\"chain_precision\":\"node_projection\"")?;
    }
    out.write_all(b",\"chain\":[")?;
    let mut terminal = root;
    for (i, step) in index.chain(root)?.enumerate() {
        let step = step?;
        if i != 0 {
            out.write_all(b",")?;
        }
        write_step(out, facts, graph, index.analysis, &step)?;
        terminal = step.next;
    }
    if seeds.binary_search(&terminal).is_err() {
        return Err(Error::Invalid(
            "compact proof does not terminate at a changed execution seed",
        ));
    }
    write!(out, "],\"seed\":{},\"seed_symbol\":", terminal.0)?;
    json_string(out, facts.symbol_name(graph.nodes[terminal.index()].symbol))?;
    out.write_all(b"}")?;
    Ok(())
}

fn write_exclusions<W: Write>(out: &mut W, decision: &SuiteDecision) -> Result<(), Error> {
    out.write_all(b"[")?;
    let mut first = true;
    for (side, certificate) in [
        ("base", decision.base_exclusion),
        ("head", decision.head_exclusion),
    ] {
        if let Some(certificate) = certificate {
            if !first {
                out.write_all(b",")?;
            }
            first = false;
            out.write_all(b"{\"snapshot\":")?;
            json_string(out, side)?;
            write!(
                out,
                ",\"snapshot_identity\":\"{}\",\"root\":{},\"certificate\":\"{}\",\"assumptions\":{}}}",
                certificate.snapshot,
                certificate.root.0,
                certificate.certificate,
                certificate.assumptions
            )?;
        }
    }
    out.write_all(b"]")?;
    Ok(())
}

/// Full evidence preserves its historical selected-only catalogue. Conditional
/// classpath exclusions have their own small paired-proof table in this mode.
pub(super) fn write_classpath_exclusions<W: Write>(
    out: &mut W,
    s: &ReportSnapshots<'_>,
    result: &SelectionResult,
) -> Result<(), Error> {
    out.write_all(b"[")?;
    let mut first = true;
    for decision in &result.decisions {
        if !classpath_absence(result, decision)? {
            continue;
        }
        if !first {
            out.write_all(b",")?;
        }
        first = false;
        out.write_all(b"{")?;
        write_suite_identity(out, s, decision)?;
        out.write_all(b",\"reason\":\"classpath_absence\",\"exclusions\":")?;
        write_exclusions(out, decision)?;
        out.write_all(b"}")?;
    }
    out.write_all(b"]")?;
    Ok(())
}

pub(super) fn write_classpath_exclusion_text<W: Write>(
    out: &mut W,
    s: &ReportSnapshots<'_>,
    result: &SelectionResult,
    decision: &SuiteDecision,
) -> Result<(), Error> {
    let suite = &s.head_facts.suites[decision.suite.index()];
    writeln!(
        out,
        "{}: excluded (classpath absence)",
        s.head_facts.text(suite.name)
    )?;
    writeln!(out, "  {CLASSPATH_ABSENCE_TEXT}")?;
    writeln!(
        out,
        "  Kernel completion: {} (not an execution-closure proof)",
        completion(result.completion)
    )?;
    for (side, certificate, facts, graph, analysis, root) in [
        (
            "base",
            decision.base_exclusion,
            s.base_facts,
            s.base_graph,
            result.base.as_ref(),
            decision.base_node,
        ),
        (
            "head",
            decision.head_exclusion,
            s.head_facts,
            s.head_graph,
            Some(&result.head),
            decision.node,
        ),
    ] {
        if let Some(proof) = certificate {
            writeln!(
                out,
                "  {side} classpath-absence certificate {} (assumptions {})",
                proof.certificate, proof.assumptions
            )?;
        }
        if let Some(analysis) = analysis {
            if let Ok(index) = analysis
                .evidence
                .guard_causes
                .binary_search_by_key(&root, |cause| cause.root)
            {
                let cause = &analysis.evidence.guard_causes[index];
                writeln!(
                    out,
                    "  {side} kernel diagnostic: {} {} {}",
                    issue_name(cause.kind),
                    facts.path(cause.file),
                    facts.text(cause.detail)
                )?;
                write_runtime_guard_text(out, facts, graph, cause)?;
            }
        }
    }
    Ok(())
}

fn check_proof(
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    index: &WitnessIndex<'_>,
    root: NodeId,
    seeds: &[NodeId],
) -> Result<(), Error> {
    let mut terminal = root;
    for step in index.chain(root)? {
        let step = step?;
        let edge = resolve_witness(graph, index.analysis, &step)?;
        for node in [step.node, step.next] {
            let node = &graph.nodes[node.index()];
            if node.symbol.index() >= facts.symbols.len()
                || (!node.file.is_none() && node.file.index() >= facts.files.len())
            {
                return Err(Error::Invalid("compact proof graph fact reference"));
            }
        }
        if (!edge.receiver.is_none() && edge.receiver.index() >= facts.symbols.len())
            || (!edge.operation.is_none() && edge.operation.index() >= facts.operations.len())
            || (!edge.occurrence.is_none() && edge.occurrence.index() >= facts.occurrences.len())
        {
            return Err(Error::Invalid("compact proof edge fact reference"));
        }
        terminal = step.next;
    }
    if seeds.binary_search(&terminal).is_err() {
        return Err(Error::Invalid(
            "compact proof does not terminate at a changed execution seed",
        ));
    }
    Ok(())
}

pub(super) fn check_decisions(
    s: &ReportSnapshots<'_>,
    result: &SelectionResult,
) -> Result<(), Error> {
    source_scope::validate(s, result.change_scope.as_ref())?;
    if result.decisions.len() != s.head_facts.suites.len() {
        return Err(Error::Invalid("compact decision catalogue coverage"));
    }
    if result.base_snapshot != s.base_graph.identity
        || result.head_snapshot != s.head_graph.identity
        || result.head.snapshot != s.head_graph.identity
        || s.head_graph.facts_identity != s.head_facts.identity
        || s.base_graph.facts_identity != s.base_facts.identity
    {
        return Err(Error::Invalid("compact snapshot identity"));
    }
    for (nodes, graph) in [
        (&result.head_seeds, s.head_graph),
        (&result.base_seeds, s.base_graph),
    ] {
        if nodes.windows(2).any(|w| w[0] >= w[1])
            || nodes.iter().any(|n| n.index() >= graph.nodes.len())
        {
            return Err(Error::Invalid("compact execution seed index"));
        }
    }
    let mut selected = result.suites.iter();
    let base_index = base_suite_index(s);
    for (analysis, graph) in [
        (Some(&result.head), s.head_graph),
        (result.base.as_ref(), s.base_graph),
    ] {
        if let Some(analysis) = analysis {
            if analysis.guarded_roots.windows(2).any(|w| w[0] >= w[1])
                || analysis
                    .guarded_roots
                    .iter()
                    .any(|node| node.index() >= graph.nodes.len())
            {
                return Err(Error::Invalid("compact guarded root index"));
            }
        }
    }
    for (i, decision) in result.decisions.iter().enumerate() {
        let cp_absent = classpath_absence(result, decision)?;
        if !result.guard_causes.is_empty() && !decision.guarded && !cp_absent {
            return Err(Error::Invalid(
                "compact decision contradicts global changed-input guard",
            ));
        }
        if decision.suite.index() != i || decision.reasons == 0 || decision.reasons & !4095 != 0 {
            return Err(Error::Invalid("compact decision identity or reason"));
        }
        if decision.reasons & DECISION_OPAQUE_SHARED_HEAP != 0
            && !cp_absent
            && (!decision.guarded
                || decision.status == SuiteDecisionStatus::Excluded
                || decision.reasons & (DECISION_COMPLETE_UNAFFECTED | DECISION_CERTIFIED_EXCLUSION)
                    != 0
                || decision.head_exclusion.is_some()
                || decision.base_exclusion.is_some())
        {
            return Err(Error::Invalid("compact opaque shared-heap decision"));
        }
        let suite = &s.head_facts.suites[i];
        let node = s
            .head_graph
            .node_for_symbol(suite.symbol)
            .unwrap_or(NodeId::NONE);
        if node != decision.node
            || decision.base_node
                != indexed_base_suite_node(s, decision.suite, &base_index).unwrap_or(NodeId::NONE)
            || (!decision.base_node.is_none()
                && decision.base_node.index() >= s.base_graph.nodes.len())
        {
            return Err(Error::Invalid("compact decision root"));
        }
        let observed_guard = (!node.is_none()
            && result.head.guarded_roots.binary_search(&node).is_ok())
            || result.base.as_ref().is_some_and(|base| {
                !decision.base_node.is_none()
                    && base
                        .guarded_roots
                        .binary_search(&decision.base_node)
                        .is_ok()
            });
        if observed_guard && !decision.guarded && !cp_absent {
            return Err(Error::Invalid(
                "compact exclusion contradicts observed uncertainty",
            ));
        }
        let head_hit = suite_root_reached(&result.head, s.head_graph, node);
        let base_hit = result
            .base
            .as_ref()
            .is_some_and(|base| suite_root_reached(base, s.base_graph, decision.base_node));
        let required = decision.status == SuiteDecisionStatus::Required;
        if required != (head_hit || base_hit)
            || (decision.reasons & DECISION_HEAD_IMPACT != 0) != head_hit
            || (decision.reasons & DECISION_BASE_IMPACT != 0) != base_hit
            || (decision.status == SuiteDecisionStatus::Unknown && !decision.guarded)
            || (decision.status == SuiteDecisionStatus::Excluded && decision.guarded)
        {
            return Err(Error::Invalid("compact decision evidence"));
        }
        for (certificate, snapshot, root) in [
            (decision.head_exclusion, result.head_snapshot, decision.node),
            (
                decision.base_exclusion,
                result.base_snapshot,
                decision.base_node,
            ),
        ] {
            if let Some(certificate) = certificate {
                if certificate.snapshot != snapshot
                    || certificate.root != root
                    || certificate.assumptions == 0
                    || decision.status != SuiteDecisionStatus::Excluded
                {
                    return Err(Error::Invalid("compact exclusion certificate binding"));
                }
            }
        }
        if decision.status != SuiteDecisionStatus::Excluded {
            let entry = selected
                .next()
                .ok_or(Error::Invalid("compact selected decision coverage"))?;
            if entry.suite != decision.suite
                || entry.node != node
                || entry.guarded != decision.guarded
            {
                return Err(Error::Invalid("compact selected decision mismatch"));
            }
        }
    }
    if selected.next().is_some() {
        return Err(Error::Invalid("compact extra selected suite"));
    }
    Ok(())
}

fn checked_compact<'a>(
    s: &ReportSnapshots<'a>,
    result: &'a SelectionResult,
) -> Result<(WitnessIndex<'a>, Option<WitnessIndex<'a>>), Error> {
    validate_suite_semantics(result)?;
    result.head.validate_execution_effects()?;
    if let Some(base) = &result.base {
        base.validate_execution_effects()?;
    }
    s.base_facts.validate()?;
    s.head_facts.validate()?;
    s.base_graph.validate()?;
    s.head_graph.validate()?;
    for (facts, obligations) in [
        (s.head_facts, result.head.obligations.as_slice()),
        (s.head_facts, result.obligations.as_slice()),
    ] {
        for obligation in obligations {
            validate_obligation(facts, obligation)?;
        }
    }
    if let Some(base) = &result.base {
        for obligation in &base.obligations {
            validate_obligation(s.base_facts, obligation)?;
        }
    }
    for (facts, graph) in [(s.base_facts, s.base_graph), (s.head_facts, s.head_graph)] {
        for d in &graph.diagnostics {
            validate_obligation(
                facts,
                &Obligation {
                    kind: d.kind,
                    file: d.file,
                    symbol: d.symbol,
                    detail: StrId::NONE,
                },
            )?;
        }
    }
    check_decisions(s, result)?;
    validate_guard_evidence(s.head_facts, s.head_graph, &result.head)?;
    if let Some(base) = &result.base {
        validate_guard_evidence(s.base_facts, s.base_graph, base)?;
    }
    let head = WitnessIndex::new(s.head_graph, &result.head)?;
    let base = result
        .base
        .as_ref()
        .map(|a| WitnessIndex::new(s.base_graph, a))
        .transpose()?;
    for decision in &result.decisions {
        if decision.reasons & DECISION_HEAD_IMPACT != 0 {
            check_proof(
                s.head_facts,
                s.head_graph,
                &head,
                decision.node,
                &result.head_seeds,
            )?;
        }
        if decision.reasons & DECISION_BASE_IMPACT != 0 {
            check_proof(
                s.base_facts,
                s.base_graph,
                base.as_ref()
                    .ok_or(Error::Invalid("compact base proof absent"))?,
                decision.base_node,
                &result.base_seeds,
            )?;
        }
    }
    for cause in &result.guard_causes {
        let facts = match cause.side {
            SnapshotSide::Base => s.base_facts,
            SnapshotSide::Head => s.head_facts,
        };
        validate_obligation(
            facts,
            &Obligation {
                kind: cause.kind,
                file: cause.file,
                symbol: cause.symbol,
                detail: cause.detail,
            },
        )?;
    }
    Ok((head, base))
}

fn relevant_metadata(d: &GraphDiagnostic, cause: &RootGuardEvidence) -> bool {
    if !d.node.is_none() {
        d.node == cause.node
    } else if !d.symbol.is_none() {
        d.symbol == cause.symbol
    } else if !d.file.is_none() {
        d.file == cause.file
    } else {
        true
    }
}

fn write_boundary<W: Write>(
    out: &mut W,
    side: &str,
    facts: &FactSnapshot,
    graph: &ProgramGraph,
    cause: &RootGuardEvidence,
) -> Result<(), Error> {
    out.write_all(b"{\"snapshot\":")?;
    json_string(out, side)?;
    out.write_all(b",\"boundary\":")?;
    write_guard_evidence(out, facts, graph, cause)?;
    out.write_all(b",\"metadata\":[")?;
    let mut first = true;
    for d in graph
        .diagnostics
        .iter()
        .filter(|d| relevant_metadata(d, cause))
    {
        if !first {
            out.write_all(b",")?;
        }
        first = false;
        out.write_all(b"{\"reason\":")?;
        json_string(out, graph.diagnostic_text(d.reason))?;
        out.write_all(b",\"metadata_path\":")?;
        json_string(out, graph.diagnostic_text(d.metadata_path))?;
        out.write_all(b"}")?;
    }
    out.write_all(b"]}")?;
    Ok(())
}

/// Compact standalone decisions. Large detached context/value tables are not
/// serialized or expanded; required roots retain checked execution chains.
pub fn write_compact_json<W: Write>(
    out: W,
    s: &ReportSnapshots<'_>,
    result: &SelectionResult,
) -> Result<(), Error> {
    write_compact_json_with_evidence(out, s, result, None)
}

pub fn write_compact_text<W: Write>(
    mut out: W,
    s: &ReportSnapshots<'_>,
    result: &SelectionResult,
) -> Result<(), Error> {
    let (head, base) = checked_compact(s, result)?;
    writeln!(out, "Selection: {}", completion(result.completion))?;
    write_selection_contract_text(&mut out, result.selection_contract)?;
    source_scope::write_text(&mut out, s, result.change_scope.as_ref())?;
    for cause in &result.guard_causes {
        let facts = match cause.side {
            SnapshotSide::Base => s.base_facts,
            SnapshotSide::Head => s.head_facts,
        };
        writeln!(
            out,
            "  {} changed-input guard {}: {} {} {}",
            side_name(cause.side),
            guard_reason(cause.reason),
            cause
                .path
                .as_deref()
                .unwrap_or_else(|| facts.path(cause.file)),
            facts.symbol_name(cause.symbol),
            facts.text(cause.detail)
        )?;
        if let Some(external) = &cause.external {
            write!(out, "    {}: {}", external.reason, external.message)?;
            if let Some(schema) = &external.schema_path {
                write!(out, "; schema {schema}")?;
            }
            if external.verb.is_some() || external.operation_path.is_some() {
                write!(
                    out,
                    "; operation {} {}",
                    external.verb.as_deref().unwrap_or(""),
                    external.operation_path.as_deref().unwrap_or("")
                )?;
            }
            if let Some(suite) = &external.suite_name {
                write!(out, "; suite {suite}")?;
            }
            writeln!(out)?;
        }
    }
    for decision in &result.decisions {
        let suite = &s.head_facts.suites[decision.suite.index()];
        let status = match decision.status {
            SuiteDecisionStatus::Required => "required",
            SuiteDecisionStatus::Unknown => "unknown",
            SuiteDecisionStatus::Excluded => "excluded",
        };
        writeln!(
            out,
            "{}: {}{}",
            s.head_facts.text(suite.name),
            status,
            if decision.guarded { " (guarded)" } else { "" }
        )?;
        let cp_absent = classpath_absence(result, decision)?;
        for &(bit, _, text) in REASONS {
            if decision.reasons & bit != 0 {
                if cp_absent && bit != DECISION_CLASSPATH_ABSENCE {
                    writeln!(out, "  Kernel diagnostic: {text}")?;
                } else {
                    writeln!(out, "  {text}")?;
                }
            }
        }
        for (label, facts, graph, analysis, root) in [
            (
                "head",
                s.head_facts,
                s.head_graph,
                Some(&result.head),
                decision.node,
            ),
            (
                "base",
                s.base_facts,
                s.base_graph,
                result.base.as_ref(),
                decision.base_node,
            ),
        ] {
            let Some(analysis) = analysis else {
                continue;
            };
            if let Ok(index) = analysis
                .evidence
                .guard_causes
                .binary_search_by_key(&root, |cause| cause.root)
            {
                let cause = &analysis.evidence.guard_causes[index];
                writeln!(
                    out,
                    "  {label} {} {} [node {}]: {} {} {}",
                    if cp_absent {
                        "kernel diagnostic at"
                    } else {
                        "reached boundary"
                    },
                    facts.symbol_name(graph.nodes[cause.node.index()].symbol),
                    cause.node.0,
                    issue_name(cause.kind),
                    facts.path(cause.file),
                    facts.text(cause.detail)
                )?;
                write_runtime_guard_text(&mut out, facts, graph, cause)?;
                for d in graph
                    .diagnostics
                    .iter()
                    .filter(|d| relevant_metadata(d, cause))
                {
                    writeln!(
                        out,
                        "    {} ({})",
                        graph.diagnostic_text(d.reason),
                        graph.diagnostic_text(d.metadata_path)
                    )?;
                }
            }
        }
        for (label, facts, graph, index, root, bit) in [
            (
                "head",
                s.head_facts,
                s.head_graph,
                Some(&head),
                decision.node,
                DECISION_HEAD_IMPACT,
            ),
            (
                "base",
                s.base_facts,
                s.base_graph,
                base.as_ref(),
                decision.base_node,
                DECISION_BASE_IMPACT,
            ),
        ] {
            if decision.reasons & bit == 0 {
                continue;
            }
            let index = index.ok_or(Error::Invalid("compact text proof"))?;
            if index.analysis.root_impacts().is_some() {
                writeln!(
                    out,
                    "  {label} root reaches a changed seed; node projection:"
                )?;
            } else {
                writeln!(out, "  {label} execution proof:")?;
            }
            let mut terminal = root;
            for step in index.chain(root)? {
                let step = step?;
                let edge = resolve_witness(
                    graph,
                    if label == "head" {
                        &result.head
                    } else {
                        result
                            .base
                            .as_ref()
                            .ok_or(Error::Invalid("compact text base proof"))?
                    },
                    &step,
                )?;
                writeln!(
                    out,
                    "    {} --{} [edge {}]--> {}",
                    facts.symbol_name(graph.nodes[step.node.index()].symbol),
                    edge_name(edge.kind),
                    step.edge.0,
                    facts.symbol_name(graph.nodes[step.next.index()].symbol)
                )?;
                terminal = step.next;
            }
            writeln!(
                out,
                "    changed execution seed {}",
                facts.symbol_name(graph.nodes[terminal.index()].symbol)
            )?;
        }
        for (side, certificate) in [
            ("base", decision.base_exclusion),
            ("head", decision.head_exclusion),
        ] {
            if let Some(certificate) = certificate {
                writeln!(
                    out,
                    "  {side} {} certificate {}",
                    if cp_absent {
                        "classpath-absence"
                    } else {
                        "closed-component"
                    },
                    certificate.certificate
                )?;
            }
        }
    }
    Ok(())
}

pub fn write_compact_json_with_evidence<W: Write>(
    mut out: W,
    s: &ReportSnapshots<'_>,
    result: &SelectionResult,
    evidence: Option<&ReportEvidenceRef<'_>>,
) -> Result<(), Error> {
    if evidence.is_some_and(|evidence| evidence.path.is_empty() || evidence.bytes == 0) {
        return Err(Error::Invalid("compact full evidence reference"));
    }
    let (head, base) = checked_compact(s, result)?;
    write!(
        out,
        "{{\"schema_version\":2,\"report_kind\":\"decisions\",\"base_snapshot\":\"{}\",\"head_snapshot\":\"{}\",\"base_facts\":\"{}\",\"head_facts\":\"{}\",\"completion\":",
        result.base_snapshot, result.head_snapshot, s.base_facts.identity, s.head_facts.identity
    )?;
    json_string(&mut out, completion(result.completion))?;
    out.write_all(b",\"suite_semantics\":")?;
    json_string(&mut out, result.suite_semantics.as_str())?;
    out.write_all(b",\"selection_contract\":")?;
    write_selection_contract_json(&mut out, result.selection_contract)?;
    out.write_all(b",\"execution_effects\":{\"head\":")?;
    write_execution_effects(&mut out, &result.head)?;
    out.write_all(b",\"base\":")?;
    if let Some(base) = &result.base {
        write_execution_effects(&mut out, base)?;
    } else {
        out.write_all(b"null")?;
    }
    out.write_all(b"}")?;
    out.write_all(b",\"change_scope\":")?;
    source_scope::write_json(&mut out, s, result.change_scope.as_ref())?;
    if let Some(evidence) = evidence {
        out.write_all(b",\"full_evidence\":{\"path\":")?;
        json_string(&mut out, evidence.path)?;
        write!(
            out,
            ",\"sha256\":\"{}\",\"bytes\":{}}}",
            evidence.sha256, evidence.bytes
        )?;
    }
    out.write_all(b",\"guard_causes\":")?;
    write_guard_causes(&mut out, s, &result.guard_causes)?;
    out.write_all(b",\"execution_seeds\":{\"base\":[")?;
    for (i, node) in result.base_seeds.iter().enumerate() {
        if i != 0 {
            out.write_all(b",")?;
        }
        write!(out, "{}", node.0)?;
    }
    out.write_all(b"],\"head\":[")?;
    for (i, node) in result.head_seeds.iter().enumerate() {
        if i != 0 {
            out.write_all(b",")?;
        }
        write!(out, "{}", node.0)?;
    }
    out.write_all(b"]}")?;
    out.write_all(b",\"suites\":[")?;
    let mut first = true;
    for decision in &result.decisions {
        if decision.status == SuiteDecisionStatus::Excluded {
            continue;
        }
        if !first {
            out.write_all(b",")?;
        }
        first = false;
        out.write_all(b"{")?;
        write_suite_identity(&mut out, s, decision)?;
        out.write_all(b"}")?;
    }
    out.write_all(b"],\"decisions\":[")?;
    for (i, decision) in result.decisions.iter().enumerate() {
        if i != 0 {
            out.write_all(b",")?;
        }
        out.write_all(b"{")?;
        write_suite_identity(&mut out, s, decision)?;
        out.write_all(b",\"status\":")?;
        json_string(
            &mut out,
            match decision.status {
                SuiteDecisionStatus::Required => "required",
                SuiteDecisionStatus::Unknown => "unknown",
                SuiteDecisionStatus::Excluded => "excluded",
            },
        )?;
        out.write_all(b",\"reasons\":[")?;
        let mut first = true;
        for &(bit, name, _) in REASONS {
            if decision.reasons & bit != 0 {
                if !first {
                    out.write_all(b",")?;
                }
                first = false;
                json_string(&mut out, name)?;
            }
        }
        out.write_all(b"],\"explanation\":[")?;
        let mut first = true;
        for &(bit, _, text) in REASONS {
            if decision.reasons & bit != 0 {
                if !first {
                    out.write_all(b",")?;
                }
                first = false;
                json_string(&mut out, text)?;
            }
        }
        out.write_all(b"],\"proofs\":[")?;
        let mut proof = false;
        if decision.reasons & DECISION_HEAD_IMPACT != 0 {
            write_proof(
                &mut out,
                "head",
                s.head_facts,
                s.head_graph,
                &head,
                decision.node,
                &result.head_seeds,
            )?;
            proof = true;
        }
        if decision.reasons & DECISION_BASE_IMPACT != 0 {
            if proof {
                out.write_all(b",")?;
            }
            write_proof(
                &mut out,
                "base",
                s.base_facts,
                s.base_graph,
                base.as_ref()
                    .ok_or(Error::Invalid("compact base proof absent"))?,
                decision.base_node,
                &result.base_seeds,
            )?;
        }
        out.write_all(b"],\"uncertainty\":[")?;
        let mut first = true;
        for (label, facts, graph, analysis, root) in [
            (
                "head",
                s.head_facts,
                s.head_graph,
                Some(&result.head),
                decision.node,
            ),
            (
                "base",
                s.base_facts,
                s.base_graph,
                result.base.as_ref(),
                decision.base_node,
            ),
        ] {
            let Some(analysis) = analysis else {
                continue;
            };
            if let Ok(index) = analysis
                .evidence
                .guard_causes
                .binary_search_by_key(&root, |cause| cause.root)
            {
                if !first {
                    out.write_all(b",")?;
                }
                first = false;
                write_boundary(
                    &mut out,
                    label,
                    facts,
                    graph,
                    &analysis.evidence.guard_causes[index],
                )?;
            }
        }
        out.write_all(b"],\"exclusions\":")?;
        write_exclusions(&mut out, decision)?;
        out.write_all(b"}")?;
    }
    out.write_all(b"]}\n")?;
    Ok(())
}
