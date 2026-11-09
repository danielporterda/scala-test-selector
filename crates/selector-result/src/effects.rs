//! A runtime producer attests exhaustive effect coverage separately from
//! diagnostic data guards. Private content binding prevents a public-field
//! toggle or stale evidence transplant from granting new omission authority.
use super::*;
use sha2::{Digest, Sha256};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum EffectClosure {
    #[default]
    Unverified,
    Open,
    Closed,
}
impl EffectClosure {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Unverified => "unverified",
            Self::Open => "open",
            Self::Closed => "closed",
        }
    }
}

/// Counts cover every retained context, including transitive effect-only calls
/// and restored contexts. They describe monotone evaluations, not first sites.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EffectClosureCoverage {
    pub contexts: u64,
    pub evaluated_contexts: u64,
    pub open_contexts: u64,
    pub pending_work: u64,
    pub external_open: bool,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ExecutionEffectEvidence {
    state: EffectClosure,
    coverage: Option<EffectClosureCoverage>,
    seal: Option<ContentHash>,
}
impl ExecutionEffectEvidence {
    /// Descriptive state; consumers granting authority must additionally call
    /// `AnalysisResult::validate_execution_effects` on the complete result.
    pub fn state(&self) -> EffectClosure {
        self.state
    }
    pub fn coverage(&self) -> Option<EffectClosureCoverage> {
        self.coverage
    }
}
impl AnalysisResult {
    /// A downstream conservative overlay may add uncertainty, but cannot infer
    /// new closure. Validate the original producer binding before mutation;
    /// after the overlay this method can only issue Open evidence.
    pub fn mark_execution_effects_open(&mut self) -> Result<(), Error> {
        let mut coverage =
            self.evidence
                .execution_effects
                .coverage
                .unwrap_or(EffectClosureCoverage {
                    contexts: 0,
                    evaluated_contexts: 0,
                    open_contexts: 0,
                    pending_work: 0,
                    external_open: true,
                });
        coverage.external_open = true;
        self.record_execution_effects(coverage)
    }
    /// Trusted runtime-producer boundary. The producer must accumulate every
    /// operation's effect openness, preserve it through cache/resume, and count
    /// all retained transitive contexts. This does not establish that the caller
    /// supplied every runnable root; selection separately validates that scope.
    pub fn record_execution_effects(
        &mut self,
        coverage: EffectClosureCoverage,
    ) -> Result<(), Error> {
        if coverage.evaluated_contexts > coverage.contexts
            || coverage.open_contexts > coverage.contexts
        {
            return Err(Error::Invalid("execution effect coverage"));
        }
        let closed = coverage.evaluated_contexts == coverage.contexts
            && coverage.open_contexts == 0
            && coverage.pending_work == 0
            && !coverage.external_open
            && self.completion != Completion::ResourceLimited
            && !self.unscoped_uncertainty
            && (self.evidence.requested_roots.is_empty() || coverage.contexts != 0);
        self.evidence.execution_effects = ExecutionEffectEvidence {
            state: if closed {
                EffectClosure::Closed
            } else {
                EffectClosure::Open
            },
            coverage: Some(coverage),
            seal: None,
        };
        let seal = Some(effect_seal(self));
        self.evidence.execution_effects.seal = seal;
        self.evidence.execution_effect_binding = seal;
        Ok(())
    }
    pub fn validate_execution_effects(&self) -> Result<EffectClosure, Error> {
        let evidence = &self.evidence.execution_effects;
        if evidence == &ExecutionEffectEvidence::default()
            && self.evidence.execution_effect_binding.is_none()
        {
            return Ok(EffectClosure::Unverified);
        }
        if evidence.state == EffectClosure::Unverified
            || evidence.coverage.is_none()
            || evidence.seal != self.evidence.execution_effect_binding
            || evidence.seal != Some(effect_seal(self))
        {
            return Err(Error::Invalid("execution effect evidence binding"));
        }
        Ok(evidence.state)
    }
}

// Streaming hashing has no temporary buffers or allocation. Metrics are not
// authority and intentionally excluded; every detached execution-proof field
// and every coverage claim is bound to the exact result snapshot and frontier.
fn effect_seal(result: &AnalysisResult) -> ContentHash {
    let mut hash = Sha256::new();
    hash.update(b"selector-execution-effects/v1");
    hash.update(result.snapshot.0);
    let status = &result.evidence.execution_effects;
    hash.update([
        status.state as u8,
        result.completion as u8,
        result.unscoped_uncertainty as u8,
    ]);
    if let Some(c) = status.coverage {
        for n in [
            c.contexts,
            c.evaluated_contexts,
            c.open_contexts,
            c.pending_work,
        ] {
            hash.update(n.to_le_bytes());
        }
        hash.update([c.external_open as u8]);
    }
    macro_rules! rows {
        ($values:expr, $r:ident, $body:block) => {{
            let values = $values;
            hash.update((values.len() as u64).to_le_bytes());
            for $r in values $body
        }};
    }
    macro_rules! words {
        ($($v:expr),* $(,)?) => { $(hash.update(($v).to_le_bytes());)* };
    }
    rows!(&result.evidence.requested_roots, r, {
        words!(r.node.0, r.receiver.0);
    });
    hash.update([result.root_impacts().is_some() as u8]);
    if let Some(roots) = result.root_impacts() {
        rows!(roots, r, {
            words!(r.node.0, r.receiver.0);
        });
    }
    rows!(&result.guarded_roots, r, {
        words!(r.0);
    });
    rows!(&result.affected, r, {
        words!(r.0);
    });
    rows!(&result.witnesses, r, {
        words!(r.node.0, r.next.0, r.edge.0);
    });
    rows!(&result.obligations, r, {
        words!(r.kind as u32, r.file.0, r.symbol.0, r.detail.0);
    });
    rows!(&result.derived_edges, r, {
        words!(
            r.source.0,
            r.target.0,
            r.kind as u32,
            r.operation.0,
            r.receiver.0
        );
    });
    rows!(&result.evidence.guard_causes, r, {
        words!(
            r.root.0,
            r.node.0,
            r.kind as u32,
            r.file.0,
            r.symbol.0,
            r.detail.0
        );
        hash.update([r.runtime.is_some() as u8]);
        if let Some(s) = r.runtime {
            words!(s.kind as u32, s.operation.0, s.reason as u32);
        }
    });
    let e = &result.evidence;
    rows!(&e.atoms, r, {
        words!(r.kind, r.site.0, r.symbol.0, r.binding);
    });
    rows!(&e.values, r, {
        words!(r.atoms.start, r.atoms.len, r.unknown);
    });
    rows!(&e.value_ids, r, {
        words!(*r);
    });
    rows!(&e.contexts, r, {
        words!(
            r.id.0,
            r.node.0,
            r.receiver,
            r.arguments.start,
            r.arguments.len
        );
    });
    rows!(&e.captures, r, {
        words!(r.binding, r.receiver, r.arguments.start, r.arguments.len);
    });
    rows!(&e.witnesses, r, {
        words!(r.context.0, r.next.0, r.edge.0, r.binding);
    });
    rows!(&e.root_contexts, r, {
        words!(r.0);
    });
    ContentHash(hash.finalize().into())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn result() -> AnalysisResult {
        let mut evidence = AnalysisEvidence::default();
        evidence.requested_roots.push(AnalyzedRoot {
            node: NodeId(0),
            receiver: SymbolId(1),
        });
        AnalysisResult {
            snapshot: ContentHash([1; 32]),
            completion: Completion::Conservative,
            affected: vec![],
            witnesses: vec![],
            derived_edges: vec![],
            obligations: vec![Obligation {
                kind: IssueKind::UnknownExecution,
                file: FileId(0),
                symbol: SymbolId(0),
                detail: StrId::NONE,
            }],
            guarded_roots: vec![NodeId(0)],
            unscoped_uncertainty: false,
            evidence,
            compilation: CompilationImpact::default(),
            metrics: AnalysisMetrics::default(),
        }
    }
    fn closed() -> EffectClosureCoverage {
        EffectClosureCoverage {
            contexts: 1,
            evaluated_contexts: 1,
            open_contexts: 0,
            pending_work: 0,
            external_open: false,
        }
    }
    #[test]
    fn effects_certificates_bind_all_authority_and_reject_public_token_transplants() {
        let mut a = result();
        assert_eq!(
            a.validate_execution_effects().unwrap(),
            EffectClosure::Unverified
        );
        a.record_execution_effects(closed()).unwrap();
        assert_eq!(
            a.validate_execution_effects().unwrap(),
            EffectClosure::Closed
        );
        a.metrics.elapsed_ns = 123;
        a.validate_execution_effects().unwrap();
        let token = a.evidence.execution_effects.clone();
        let mutations: [fn(&mut AnalysisResult); 8] = [
            |r| r.snapshot = ContentHash([2; 32]),
            |r| r.evidence.requested_roots[0].receiver = SymbolId(2),
            |r| r.completion = Completion::ResourceLimited,
            |r| r.unscoped_uncertainty = true,
            |r| r.guarded_roots.clear(),
            |r| r.obligations.clear(),
            |r| {
                r.derived_edges.push(DerivedEdge {
                    source: NodeId(0),
                    target: NodeId(1),
                    kind: EdgeKind::Call,
                    operation: OperationId(0),
                    receiver: SymbolId::NONE,
                })
            },
            |r| r.evidence.value_ids.push(1),
        ];
        for mutate in mutations {
            let mut b = result();
            b.record_execution_effects(closed()).unwrap();
            mutate(&mut b);
            assert!(b.validate_execution_effects().is_err());
        }
        let mut b = result();
        b.record_execution_effects(EffectClosureCoverage {
            open_contexts: 1,
            ..closed()
        })
        .unwrap();
        b.evidence.execution_effects = token;
        assert!(
            b.validate_execution_effects().is_err(),
            "identical public guards do not authorize a stale Closed token"
        );
    }
    #[test]
    fn incomplete_effect_coverage_never_certifies_closed() {
        for c in [
            EffectClosureCoverage {
                evaluated_contexts: 0,
                ..closed()
            },
            EffectClosureCoverage {
                open_contexts: 1,
                ..closed()
            },
            EffectClosureCoverage {
                pending_work: 1,
                ..closed()
            },
            EffectClosureCoverage {
                external_open: true,
                ..closed()
            },
        ] {
            let mut r = result();
            r.record_execution_effects(c).unwrap();
            assert_eq!(r.validate_execution_effects().unwrap(), EffectClosure::Open);
        }
        let mut r = result();
        r.completion = Completion::ResourceLimited;
        r.record_execution_effects(closed()).unwrap();
        assert_eq!(r.validate_execution_effects().unwrap(), EffectClosure::Open);
        assert!(
            r.record_execution_effects(EffectClosureCoverage {
                evaluated_contexts: 2,
                ..closed()
            })
            .is_err()
        );
    }
}
