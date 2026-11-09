//! Bounded derived work is an open frontier, never evidence of class absence.
use super::*;

pub const POLICY: &[u8] = b"fair-native-admission/5-this-demands-receiver-frontiers";
#[derive(Clone, Copy, Debug)]
pub struct NativeAdmissionLimits {
    pub classes_per_context: usize,
    pub bytes_per_context: usize,
    pub methods: usize,
}
impl Default for NativeAdmissionLimits {
    fn default() -> Self {
        Self {
            classes_per_context: MAX_CLASSES,
            bytes_per_context: MAX_CLASS_BYTES,
            methods: MAX_METHODS,
        }
    }
}
impl NativeAdmissionLimits {
    pub(super) fn validate(self) -> Result<(), Error> {
        if self.classes_per_context == 0
            || self.classes_per_context > MAX_CLASSES
            || self.bytes_per_context == 0
            || self.bytes_per_context > MAX_CLASS_BYTES
            || self.methods == 0
            || self.methods > MAX_METHODS
        {
            return Err(Error::Invalid("native admission limits"));
        }
        Ok(())
    }
    pub(super) fn hash(self, hash: &mut Sha256) {
        hash.update(POLICY);
        for limit in [
            self.classes_per_context,
            self.bytes_per_context,
            self.methods,
        ] {
            hash.update((limit as u64).to_le_bytes());
        }
    }
}
#[derive(Clone, Copy, Debug)]
pub(super) enum DeferredReason {
    Classes,
    Bytes,
    Methods,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum DiagnosticScope {
    Execution,
    Hierarchy,
}
impl DiagnosticScope {
    fn kind(self) -> IssueKind {
        match self {
            Self::Execution => IssueKind::UnknownExecution,
            Self::Hierarchy => IssueKind::IncompleteHierarchy,
        }
    }
}
impl DeferredReason {
    pub(super) fn error(self) -> Error {
        Error::Limit(match self {
            Self::Classes => "optional native class admission frontier",
            Self::Bytes => "optional native byte admission frontier",
            Self::Methods => "optional native method admission frontier",
        })
    }
    fn from_error(error: &Error) -> Option<Self> {
        match error {
            Error::Limit("optional native class admission frontier") => Some(Self::Classes),
            Error::Limit("optional native byte admission frontier") => Some(Self::Bytes),
            Error::Limit("optional native method admission frontier") => Some(Self::Methods),
            _ => None,
        }
    }
    fn detail(self, scope: DiagnosticScope) -> &'static str {
        match (scope, self) {
            (DiagnosticScope::Execution, Self::Classes) => {
                "Native class admission budget deferred derived execution; class presence or absence was not established."
            }
            (DiagnosticScope::Execution, Self::Bytes) => {
                "Native class byte budget deferred derived execution; class presence or absence was not established."
            }
            (DiagnosticScope::Execution, Self::Methods) => {
                "Fair native method admission budget deferred derived execution; the missing body remains an open execution frontier."
            }
            (DiagnosticScope::Hierarchy, Self::Classes) => {
                "Native class admission budget deferred ancestry metadata; hierarchy completeness was not established."
            }
            (DiagnosticScope::Hierarchy, Self::Bytes) => {
                "Native class byte budget deferred ancestry metadata; hierarchy completeness was not established."
            }
            (DiagnosticScope::Hierarchy, Self::Methods) => {
                "Native method admission budget deferred ancestry metadata; hierarchy completeness was not established."
            }
        }
    }
}
pub(super) struct Admission {
    pub limits: NativeAdmissionLimits,
    pub derived: bool,
    pub method_allowance: usize,
    pub methods: usize,
    pub deferred: u64,
    /// Changes on every typed method-quota refusal, including deduplicated
    /// diagnostics. A first-round caller uses this to delay recipe publication.
    pub method_refusals: u64,
    /// Only lambda-free, unpublished caller recipes may probe. Other admission
    /// boundaries (class/bytes/provenance) retain their ordinary behavior.
    pub probe_method_quota: bool,
    pub method_slots_released: usize,
    pub method_slots_received: usize,
    pub retried_callers: usize,
    /// Actual retained typed execution-guard rows, after per-symbol dedup.
    /// This is not the number of callsites or all remaining runtime boundaries.
    pub method_guard_rows: usize,
    /// Receiver/contract frontier rows, distinct from unconditional issue rows.
    pub scoped_dispatch_rows: usize,
    dispatch_frontiers: HashSet<(SymbolId, SymbolId)>,
    /// One wildcard per admitted receiver when bounded contract bookkeeping
    /// overflows. This is not an unconditional execution issue.
    pub receiver_dispatch_rows: usize,
    receiver_frontiers: HashSet<SymbolId>,
    scope_diagnostics: HashSet<&'static str>,
    guarded: HashSet<(DiagnosticScope, SymbolId)>,
    details: [[StrId; 3]; 2],
}
impl Default for Admission {
    fn default() -> Self {
        Self {
            limits: NativeAdmissionLimits::default(),
            derived: false,
            method_allowance: 0,
            methods: 0,
            deferred: 0,
            method_refusals: 0,
            probe_method_quota: false,
            method_slots_released: 0,
            method_slots_received: 0,
            retried_callers: 0,
            method_guard_rows: 0,
            scoped_dispatch_rows: 0,
            dispatch_frontiers: HashSet::new(),
            receiver_dispatch_rows: 0,
            receiver_frontiers: HashSet::new(),
            scope_diagnostics: HashSet::new(),
            guarded: HashSet::new(),
            details: [[StrId::NONE; 3]; 2],
        }
    }
}
impl Admission {
    pub fn check_method(&mut self, total: usize) -> Result<(), Error> {
        if total >= self.limits.methods || self.derived && self.methods >= self.method_allowance {
            if self.derived {
                return Err(DeferredReason::Methods.error());
            }
            return Err(Error::Limit("mandatory binary method expansion"));
        }
        Ok(())
    }
    pub fn admitted_method(&mut self) {
        self.methods += usize::from(self.derived);
    }
}
/// Release unused first-round reservations once. The total new allowance is
/// exactly the remaining global declaration budget, shared in stable context
/// order only by contexts with unpublished quota-blocked caller recipes.
pub(super) fn redistribute_methods(
    contexts: &mut [AdmittedContext],
    blocked: &[bool],
    remaining: usize,
) {
    debug_assert_eq!(contexts.len(), blocked.len());
    let count = blocked.iter().filter(|&&blocked| blocked).count();
    let mut ordinal = 0;
    for (context, &blocked) in contexts.iter_mut().zip(blocked) {
        context.admission.probe_method_quota = false;
        let extra = if blocked {
            let extra = remaining / count + usize::from(ordinal < remaining % count);
            ordinal += 1;
            extra
        } else {
            0
        };
        context.admission.method_slots_released = context
            .admission
            .method_allowance
            .saturating_sub(context.admission.methods);
        context.admission.method_slots_received = extra;
        context.admission.method_allowance = context.admission.methods + extra;
    }
}

fn guard(
    facts: &mut FactSnapshot,
    context: &mut AdmittedContext,
    symbol: SymbolId,
    file: FileId,
    reason: DeferredReason,
    scope: DiagnosticScope,
) -> Result<(), Error> {
    guard_recorded(facts, context, symbol, file, reason, scope, true)
}
fn guard_recorded(
    facts: &mut FactSnapshot,
    context: &mut AdmittedContext,
    symbol: SymbolId,
    file: FileId,
    reason: DeferredReason,
    scope: DiagnosticScope,
    count_attempt: bool,
) -> Result<(), Error> {
    context.admission.deferred += u64::from(count_attempt);
    if matches!(reason, DeferredReason::Methods) {
        context.admission.method_refusals += u64::from(count_attempt);
        if count_attempt && context.admission.probe_method_quota {
            // The caller has not published a recipe yet. Its final retry must
            // either resolve this dependency or publish the ordinary guard.
            // Do not poison diagnostic deduplication with a temporary refusal.
            return Ok(());
        }
    }
    if !context.admission.guarded.insert((scope, symbol)) {
        return Ok(());
    }
    let details = &mut context.admission.details[scope as usize];
    let index = reason as usize;
    let detail = if details[index].is_none() {
        let id = append_text(facts, reason.detail(scope))?;
        details[index] = id;
        id
    } else {
        details[index]
    };
    context.admission.method_guard_rows += usize::from(
        scope == DiagnosticScope::Execution && matches!(reason, DeferredReason::Methods),
    );
    facts.issues.push(IssueRecord {
        kind: scope.kind(),
        symbol,
        file,
        detail,
    });
    Ok(())
}
/// Catch only the typed optional admission errors. Provenance failures and
/// invalid mandatory inputs always remain fatal. Known effects after this
/// frontier are still projected by the caller's ordinary effect loop.
pub(super) fn optional_effect<T>(
    facts: &mut FactSnapshot,
    context: &mut AdmittedContext,
    symbol: SymbolId,
    file: FileId,
    result: Result<T, Error>,
    fallback: T,
) -> Result<T, Error> {
    optional_result(
        facts,
        context,
        symbol,
        file,
        result,
        fallback,
        DiagnosticScope::Execution,
    )
}

/// A discovered implementation may be left unadmitted only if its uncertainty
/// remains at every relevant receiver/contract dispatch. Other optional errors,
/// and unproved aliases, keep the ordinary conservative execution issue.
pub(super) fn optional_generated_method(
    facts: &mut FactSnapshot,
    context: &mut AdmittedContext,
    receiver: SymbolId,
    file: FileId,
    contracts: &[SymbolId],
    broad: bool,
    result: Result<SymbolId, Error>,
) -> Result<SymbolId, Error> {
    generated_method_result(
        facts, context, receiver, file, contracts, broad, result, true,
    )
}
/// Publish a previously counted refusal once the final alias inventory is known.
pub(super) fn deferred_generated_frontier(
    facts: &mut FactSnapshot,
    context: &mut AdmittedContext,
    receiver: SymbolId,
    file: FileId,
    contracts: &[SymbolId],
    broad: bool,
) -> Result<(), Error> {
    generated_method_result(
        facts,
        context,
        receiver,
        file,
        contracts,
        broad,
        Err(DeferredReason::Methods.error()),
        false,
    )
    .map(|_| ())
}

/// Bookkeeping exhaustion proves neither an empty method set nor execution of
/// an omitted override. Retain that uncertainty once per already admitted
/// receiver, for the consumer to check only at an actual instance dispatch.
pub(super) fn deferred_receiver_frontier(
    facts: &mut FactSnapshot,
    context: &mut AdmittedContext,
    receiver: SymbolId,
    file: FileId,
    count_attempt: bool,
) -> Result<(), Error> {
    let class = facts
        .symbols
        .get(receiver.index())
        .ok_or(Error::Invalid("deferred receiver reference"))?;
    if !matches!(class.kind, 10 | 13)
        || class.flags & (SYMBOL_DEFINED | SYMBOL_JVM_CLASS_HEADER_VERIFIED) == 0
        || class.context != context.id
        || file.is_none()
        || facts
            .files
            .get(file.index())
            .is_none_or(|f| f.context != class.context)
    {
        return Err(Error::Invalid("deferred receiver dispatch scope"));
    }
    context.admission.deferred += u64::from(count_attempt);
    context.admission.method_refusals += u64::from(count_attempt);
    if context.admission.receiver_frontiers.insert(receiver) {
        facts.relations.push(RelationRecord {
            source: receiver,
            target: receiver,
            kind: RelationKind::DeferredReceiverDispatch,
            file,
        });
        context.admission.receiver_dispatch_rows += 1;
    }
    Ok(())
}
// Mirror the strict facts validator. This is publication admission, not a
// relaxation of the relation schema; any non-callable alias keeps a broad guard.
pub(super) fn dispatch_scope_error(
    facts: &FactSnapshot,
    receiver: SymbolId,
    target: SymbolId,
    file: FileId,
) -> Option<&'static str> {
    let Some(receiver) = facts.symbols.get(receiver.index()) else {
        return Some("receiver_reference");
    };
    let Some(target) = facts.symbols.get(target.index()) else {
        return Some("target_reference");
    };
    if !matches!(receiver.kind, 10 | 13) {
        return Some("receiver_kind");
    }
    if receiver.flags & (SYMBOL_DEFINED | SYMBOL_JVM_CLASS_HEADER_VERIFIED) == 0 {
        return Some("receiver_authority");
    }
    if !matches!(target.kind, 0 | 3 | 6) {
        return Some("contract_kind");
    }
    if target.owner.is_none() {
        return Some("contract_owner_missing");
    }
    let Some(owner) = facts.symbols.get(target.owner.index()) else {
        return Some("contract_owner_reference");
    };
    if !matches!(owner.kind, 10 | 13 | 14) {
        return Some("contract_owner_kind");
    }
    if owner.context != target.context {
        return Some("contract_owner_context");
    }
    if file.is_none() {
        return Some("scope_file_missing");
    }
    let Some(file) = facts.files.get(file.index()) else {
        return Some("scope_file_reference");
    };
    if file.context != receiver.context {
        return Some("scope_file_context");
    }
    None
}
fn diagnose_dispatch_scope(
    facts: &FactSnapshot,
    context: &mut AdmittedContext,
    receiver: SymbolId,
    target: SymbolId,
    file: FileId,
    reason: &'static str,
) {
    if !context.admission.scope_diagnostics.insert(reason) {
        return;
    }
    let describe = |id: SymbolId| {
        facts.symbols.get(id.index()).map(|row| serde_json::json!({
            "id":id.0,"name":facts.text(row.name).chars().take(256).collect::<String>(),
            "kind":row.kind,"flags":row.flags,"owner":row.owner.0,
            "context":facts.text(row.context).chars().take(256).collect::<String>(),"file":row.file.0
        }))
    };
    let owner = facts
        .symbols
        .get(target.index())
        .map(|row| row.owner)
        .unwrap_or(SymbolId::NONE);
    eprintln!(
        "{}",
        serde_json::json!({"stage":"native_dispatch_scope_fallback", "reason":reason,
        "context":context.name.chars().take(256).collect::<String>(),"receiver":describe(receiver),"contract":describe(target),
        "contract_owner":describe(owner),"scope_file":file.0,
        "scope_file_context":facts.files.get(file.index()).map(|row| facts.text(row.context).chars().take(256).collect::<String>()),
        "coverage":"scoped publication rejected; representable receiver uncertainty retains a broad guard"})
    );
}
fn generated_method_result(
    facts: &mut FactSnapshot,
    context: &mut AdmittedContext,
    receiver: SymbolId,
    file: FileId,
    contracts: &[SymbolId],
    broad: bool,
    result: Result<SymbolId, Error>,
    count_attempt: bool,
) -> Result<SymbolId, Error> {
    match result {
        Err(error)
            if !broad
                && !contracts.is_empty()
                && matches!(
                    DeferredReason::from_error(&error),
                    Some(DeferredReason::Methods)
                ) =>
        {
            if let Some((contract, reason)) = contracts.iter().find_map(|&contract| {
                dispatch_scope_error(facts, receiver, contract, file)
                    .map(|reason| (contract, reason))
            }) {
                diagnose_dispatch_scope(facts, context, receiver, contract, file, reason);
                if matches!(
                    reason,
                    "receiver_reference"
                        | "target_reference"
                        | "contract_owner_reference"
                        | "scope_file_reference"
                ) {
                    return Err(Error::Message(format!(
                        "invalid generated dispatch reference ({reason}): receiver {}, contract {}, file {}",
                        receiver.0, contract.0, file.0
                    )));
                }
                let class = facts
                    .symbols
                    .get(receiver.index())
                    .ok_or(Error::Invalid("generated dispatch receiver"))?;
                if !matches!(class.kind, 10 | 13)
                    || class.flags & (SYMBOL_DEFINED | SYMBOL_JVM_CLASS_HEADER_VERIFIED) == 0
                    || class.context != context.id
                {
                    return Err(Error::Message(format!(
                        "invalid generated dispatch receiver {} ({reason})",
                        receiver.0
                    )));
                }
                // The class still has an omitted implementation, but this
                // alias cannot be represented as a typed callable frontier.
                // Keep the receiver-wide guard rather than dropping the alias
                // or inventing method ownership/signature metadata.
                let file = [file, class.file]
                    .into_iter()
                    .find(|id| {
                        !id.is_none()
                            && facts
                                .files
                                .get(id.index())
                                .is_some_and(|f| f.context == class.context)
                    })
                    .unwrap_or(FileId::NONE);
                guard_recorded(
                    facts,
                    context,
                    receiver,
                    file,
                    DeferredReason::Methods,
                    DiagnosticScope::Execution,
                    count_attempt,
                )?;
                return Ok(SymbolId::NONE);
            }
            for &contract in contracts {
                if !context
                    .admission
                    .dispatch_frontiers
                    .contains(&(receiver, contract))
                    && context.admission.dispatch_frontiers.len()
                        >= context.admission.method_allowance.max(1)
                {
                    // Missing methods must not grow a receiver-by-contract
                    // table beyond this context's fair work allowance. Already
                    // retained rows remain sound. One receiver wildcard
                    // protects every unrepresented override at actual dispatch.
                    deferred_receiver_frontier(facts, context, receiver, file, count_attempt)?;
                    return Ok(SymbolId::NONE);
                }
                if context
                    .admission
                    .dispatch_frontiers
                    .insert((receiver, contract))
                {
                    facts.relations.push(RelationRecord {
                        source: receiver,
                        target: contract,
                        kind: RelationKind::DeferredDispatch,
                        file,
                    });
                    context.admission.scoped_dispatch_rows += 1;
                }
            }
            context.admission.deferred += u64::from(count_attempt);
            context.admission.method_refusals += u64::from(count_attempt);
            Ok(SymbolId::NONE)
        }
        Err(error)
            if !count_attempt
                && matches!(
                    DeferredReason::from_error(&error),
                    Some(DeferredReason::Methods)
                ) =>
        {
            guard_recorded(
                facts,
                context,
                receiver,
                file,
                DeferredReason::Methods,
                DiagnosticScope::Execution,
                false,
            )?;
            Ok(SymbolId::NONE)
        }
        value => optional_effect(facts, context, receiver, file, value, SymbolId::NONE),
    }
}
fn optional_result<T>(
    facts: &mut FactSnapshot,
    context: &mut AdmittedContext,
    symbol: SymbolId,
    file: FileId,
    result: Result<T, Error>,
    fallback: T,
    scope: DiagnosticScope,
) -> Result<T, Error> {
    match result {
        Ok(value) => Ok(value),
        Err(error) => {
            if let Some(reason) = DeferredReason::from_error(&error) {
                guard(facts, context, symbol, file, reason, scope)?;
                Ok(fallback)
            } else {
                Err(error)
            }
        }
    }
}
pub(super) fn guarded_class(
    facts: &mut FactSnapshot,
    context: &mut AdmittedContext,
    loader: &mut CapturedClasspath,
    owner: &str,
    symbol: SymbolId,
    file: FileId,
) -> Result<Option<Arc<ClassBytes>>, Error> {
    let result = cache_class(context, loader, owner);
    optional_effect(facts, context, symbol, file, result, None)
}

/// Header-only traversal never projects an execution frontier. A later real
/// call or initialization lookup uses guarded_class and keeps its own guard.
pub(super) fn guarded_hierarchy_class(
    facts: &mut FactSnapshot,
    context: &mut AdmittedContext,
    loader: &mut CapturedClasspath,
    owner: &str,
    symbol: SymbolId,
    file: FileId,
) -> Result<Option<Arc<ClassBytes>>, Error> {
    let result = cache_class(context, loader, owner);
    optional_result(
        facts,
        context,
        symbol,
        file,
        result,
        None,
        DiagnosticScope::Hierarchy,
    )
}

pub(super) fn optional_phase(
    facts: &mut FactSnapshot,
    context: &mut AdmittedContext,
    result: Result<Initialization, Error>,
) -> Result<Initialization, Error> {
    optional_effect(
        facts,
        context,
        context.active_method,
        context.active_file,
        result,
        Initialization::Unknown,
    )
}

#[cfg(test)]
#[path = "binary_admission_tests.rs"]
mod tests;
