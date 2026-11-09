//! Development-only acceptance contracts. No production crate depends on this leaf.
//!
//! Layout checks are in-memory allocation budgets, not a promise that Rust's memory
//! layout is a stable on-disk format. Artifact codecs define their own wire layout.
use selector_facts::{
    BodyRecord, FileRecord, OccurrenceRecord, OperationRecord, RelationRecord, ResultBoundRecord,
    SymbolRecord, TextRange,
};
use selector_graph::{EdgeRecord, GraphDiagnostic, NodeRecord};
use selector_result::{
    CaptureEvidence, ContextEvidence, ContextWitness, DerivedEdge, EvidenceAtom, EvidenceValue,
    Obligation, WitnessStep,
};
use selector_types::{ContentHash, IdRange, NodeId, Span};
use std::mem::{align_of, size_of};

#[derive(Clone, Copy, Debug)]
pub struct RecordLayout {
    pub name: &'static str,
    pub bytes: usize,
    pub alignment: usize,
    pub budget: usize,
}

/// Explicit budgets catch accidental per-record String/Vec/Arc fields and padding.
/// Increasing one requires a recorded memory-cost decision, not a regenerated test.
pub fn record_layouts() -> [RecordLayout; 23] {
    macro_rules! record {
        ($ty:ty, $budget:expr) => {
            RecordLayout {
                name: stringify!($ty),
                bytes: size_of::<$ty>(),
                alignment: align_of::<$ty>(),
                budget: $budget,
            }
        };
    }
    [
        record!(NodeId, 4),
        record!(Span, 8),
        record!(IdRange, 8),
        record!(ContentHash, 32),
        record!(TextRange, 16),
        record!(FileRecord, 52),
        record!(SymbolRecord, 48),
        record!(OccurrenceRecord, 24),
        record!(RelationRecord, 16),
        record!(BodyRecord, 76),
        record!(OperationRecord, 44),
        record!(ResultBoundRecord, 16),
        record!(NodeRecord, 16),
        record!(EdgeRecord, 28),
        record!(GraphDiagnostic, 32),
        record!(WitnessStep, 12),
        record!(Obligation, 16),
        record!(DerivedEdge, 20),
        record!(EvidenceAtom, 16),
        record!(EvidenceValue, 12),
        record!(ContextEvidence, 20),
        record!(CaptureEvidence, 16),
        record!(ContextWitness, 16),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fixed_record_layouts_stay_within_explicit_budgets() {
        for record in record_layouts() {
            assert!(
                record.bytes <= record.budget,
                "{} grew to {} bytes, budget {}",
                record.name,
                record.bytes,
                record.budget
            );
            assert!(
                record.alignment <= 8,
                "{} gained excess alignment",
                record.name
            );
        }
        assert_eq!(size_of::<selector_graph::GraphIssue>(), 20);
    }

    #[test]
    fn hot_records_remain_copy_values() {
        fn copy_record<T: Copy>() {}
        copy_record::<FileRecord>();
        copy_record::<SymbolRecord>();
        copy_record::<OccurrenceRecord>();
        copy_record::<RelationRecord>();
        copy_record::<BodyRecord>();
        copy_record::<OperationRecord>();
        copy_record::<ResultBoundRecord>();
        copy_record::<NodeRecord>();
        copy_record::<EdgeRecord>();
        copy_record::<GraphDiagnostic>();
        copy_record::<WitnessStep>();
        copy_record::<Obligation>();
        copy_record::<DerivedEdge>();
        copy_record::<EvidenceAtom>();
        copy_record::<EvidenceValue>();
        copy_record::<ContextEvidence>();
        copy_record::<CaptureEvidence>();
        copy_record::<ContextWitness>();
    }
}
