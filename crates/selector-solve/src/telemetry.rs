//! Allocation-free observer events emitted by the coordinator at publication barriers.
use crate::cache::CacheEvent;
use std::fmt::Debug;
use std::sync::atomic::{AtomicU8, AtomicU64, Ordering};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SolvePhase {
    Preparing,
    CacheAdmission,
    Executing,
    Publication,
    Reporting,
    Stopped,
    Complete,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StopReason {
    ContextLimit,
    StepLimit,
    MemoryLimit,
    AllocationLimit,
    Cancelled,
    CheckpointRequested,
}

/// Stop requests are observed only at a coordinator publication barrier.
/// A checkpoint request preserves the same sound partial state as cancellation.
#[derive(Debug)]
pub struct SolveControl {
    request: AtomicU8,
    after_round: AtomicU64,
}
impl Default for SolveControl {
    fn default() -> Self {
        Self {
            request: AtomicU8::new(0),
            after_round: AtomicU64::new(u64::MAX),
        }
    }
}
impl SolveControl {
    pub fn cancel(&self) {
        self.request.store(1, Ordering::Release);
    }
    pub fn request_checkpoint(&self) {
        self.request.store(2, Ordering::Release);
    }
    pub fn checkpoint_after_round(&self, round: u64) {
        self.after_round.store(round, Ordering::Release);
    }
    pub fn reset(&self) {
        self.request.store(0, Ordering::Release);
        self.after_round.store(u64::MAX, Ordering::Release);
    }
    pub fn requested(&self) -> Option<StopReason> {
        match self.request.load(Ordering::Acquire) {
            1 => Some(StopReason::Cancelled),
            2 => Some(StopReason::CheckpointRequested),
            _ => None,
        }
    }
    pub(crate) fn at_round(&self, round: u64) -> Option<StopReason> {
        self.requested().or_else(|| {
            (round >= self.after_round.load(Ordering::Acquire))
                .then_some(StopReason::CheckpointRequested)
        })
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WorkCounters {
    pub contexts: u64,
    pub context_hits: u64,
    pub evaluations: u64,
    pub reevaluations: u64,
    pub novel_publications: u64,
    pub repeated_publications: u64,
    pub dispatch_targets: u64,
    pub callback_targets: u64,
    pub operations: u64,
    pub pending: u64,
    pub owned_bytes: u64,
    pub widened_contexts: u64,
}

#[derive(Clone, Copy, Debug)]
pub struct SolveEvent {
    pub phase: SolvePhase,
    pub round: u64,
    pub elapsed_ns: u64,
    pub counters: WorkCounters,
    pub stop: Option<StopReason>,
    pub cache: Option<CacheEvent>,
}

#[derive(Clone, Copy, Debug)]
pub struct WorkOrigin<'a> {
    pub symbol: &'a str,
    pub context: &'a str,
    pub path: &'a str,
}

/// Implementations must be short and must not call back into the same session.
/// Progress events are throttled to once per second; phase, stop and cache
/// decisions are emitted immediately. The solver does not allocate event payloads.
pub trait SolveObserver: Send + Sync + Debug {
    fn observe(&self, event: SolveEvent);
    /// At most census.capacity rows are emitted at a stop or completion.
    fn work_row(&self, _row: crate::WorkRow) {}
    fn work_row_with_origin(&self, row: crate::WorkRow, _origin: WorkOrigin<'_>) {
        self.work_row(row);
    }
}
