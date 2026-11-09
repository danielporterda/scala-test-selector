//! Bounded Space-Saving counters. All storage is reserved once per query.
use selector_types::NodeId;
use std::collections::HashMap;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WorkRow {
    pub node: NodeId,
    pub new_contexts: u64,
    pub evaluations: u64,
    pub reevaluations: u64,
    pub novel_publications: u64,
    pub repeated_publications: u64,
    pub dispatch_targets: u64,
    pub callback_targets: u64,
    pub widened_contexts: u64,
    /// Upper-bound tracking weight inherited when a table entry is replaced.
    pub inherited_weight: u64,
}
impl WorkRow {
    fn weight(&self) -> u64 {
        self.inherited_weight
            .saturating_add(self.new_contexts)
            .saturating_add(self.evaluations)
            .saturating_add(self.dispatch_targets)
            .saturating_add(self.callback_targets)
            .saturating_add(self.novel_publications)
            .saturating_add(self.repeated_publications)
            .saturating_add(self.widened_contexts)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct CensusOptions {
    /// Zero disables the census. This bounds rows, map entries and heap entries.
    pub capacity: usize,
    /// Record one out of this many evaluations. Context admission is always counted.
    pub evaluation_stride: u64,
}
impl Default for CensusOptions {
    fn default() -> Self {
        Self {
            capacity: 64,
            evaluation_stride: 16,
        }
    }
}

pub(crate) struct WorkCensus {
    rows: Vec<WorkRow>,
    index: HashMap<NodeId, usize>,
    heap: Vec<usize>,
    positions: Vec<usize>,
    capacity: usize,
}
impl WorkCensus {
    pub fn new(capacity: usize) -> Self {
        Self {
            rows: Vec::with_capacity(capacity),
            // Keep live entries below half of the admitted table. Deletion
            // tombstones can then be rehashed in place during a long stream;
            // reserving only `capacity` permits a late table growth allocation.
            index: HashMap::with_capacity(capacity.saturating_mul(2)),
            heap: Vec::with_capacity(capacity),
            positions: Vec::with_capacity(capacity),
            capacity,
        }
    }
    pub fn rows(&self) -> &[WorkRow] {
        &self.rows
    }
    pub fn update(&mut self, delta: WorkRow) {
        if self.capacity == 0 {
            return;
        }
        let i = if let Some(i) = self.index.get(&delta.node) {
            *i
        } else if self.rows.len() < self.capacity {
            let i = self.rows.len();
            self.rows.push(WorkRow {
                node: delta.node,
                ..Default::default()
            });
            self.index.insert(delta.node, i);
            self.positions.push(self.heap.len());
            self.heap.push(i);
            i
        } else {
            let i = self.heap[0];
            let inherited_weight = self.rows[i].weight();
            self.index.remove(&self.rows[i].node);
            self.rows[i] = WorkRow {
                node: delta.node,
                inherited_weight,
                ..Default::default()
            };
            self.index.insert(delta.node, i);
            i
        };
        let r = &mut self.rows[i];
        r.new_contexts += delta.new_contexts;
        r.evaluations += delta.evaluations;
        r.reevaluations += delta.reevaluations;
        r.novel_publications += delta.novel_publications;
        r.repeated_publications += delta.repeated_publications;
        r.dispatch_targets += delta.dispatch_targets;
        r.callback_targets += delta.callback_targets;
        r.widened_contexts += delta.widened_contexts;
        // A new row can be lighter than its parent. Existing/replaced rows only
        // increase; doing both directions keeps the same bounded heap code.
        let mut p = self.positions[i];
        while p > 0 {
            let parent = (p - 1) / 2;
            if (
                self.rows[self.heap[parent]].weight(),
                self.rows[self.heap[parent]].node.0,
            ) <= (
                self.rows[self.heap[p]].weight(),
                self.rows[self.heap[p]].node.0,
            ) {
                break;
            }
            self.heap.swap(p, parent);
            self.positions[self.heap[p]] = p;
            self.positions[self.heap[parent]] = parent;
            p = parent;
        }
        loop {
            let left = p * 2 + 1;
            if left >= self.heap.len() {
                break;
            }
            let right = left + 1;
            let less = |a: usize, b: usize, this: &Self| {
                (
                    this.rows[this.heap[a]].weight(),
                    this.rows[this.heap[a]].node.0,
                ) < (
                    this.rows[this.heap[b]].weight(),
                    this.rows[this.heap[b]].node.0,
                )
            };
            let child = if right < self.heap.len() && less(right, left, self) {
                right
            } else {
                left
            };
            if !less(child, p, self) {
                break;
            }
            self.heap.swap(p, child);
            self.positions[self.heap[p]] = p;
            self.positions[self.heap[child]] = child;
            p = child;
        }
    }
    pub fn owned_bytes(&self) -> usize {
        self.rows.capacity() * std::mem::size_of::<WorkRow>()
            + self.index.capacity() * 16
            + (self.heap.capacity() + self.positions.capacity()) * std::mem::size_of::<usize>()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::alloc::{GlobalAlloc, Layout, System};
    use std::cell::Cell;
    thread_local! {
        static TRACK:Cell<bool>=const {Cell::new(false)};
        static ALLOCATIONS:Cell<usize>=const {Cell::new(0)};
    }
    struct CensusAllocator;
    fn count_allocation() {
        let _ = TRACK.try_with(|t| {
            if t.get() {
                let _ = ALLOCATIONS.try_with(|n| n.set(n.get() + 1));
            }
        });
    }
    unsafe impl GlobalAlloc for CensusAllocator {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            count_allocation();
            unsafe { System.alloc(layout) }
        }
        unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
            count_allocation();
            unsafe { System.alloc_zeroed(layout) }
        }
        unsafe fn realloc(&self, p: *mut u8, layout: Layout, size: usize) -> *mut u8 {
            count_allocation();
            unsafe { System.realloc(p, layout, size) }
        }
        unsafe fn dealloc(&self, p: *mut u8, layout: Layout) {
            unsafe { System.dealloc(p, layout) }
        }
    }
    #[global_allocator]
    static ALLOCATOR: CensusAllocator = CensusAllocator;
    #[test]
    fn streaming_replacements_allocate_nothing_after_admission() {
        let mut c = WorkCensus::new(64);
        ALLOCATIONS.with(|n| n.set(0));
        TRACK.with(|t| t.set(true));
        for node in 0..100_000 {
            c.update(WorkRow {
                node: NodeId(node),
                new_contexts: 1,
                ..Default::default()
            });
        }
        TRACK.with(|t| t.set(false));
        let allocations = ALLOCATIONS.with(Cell::get);
        assert_eq!(
            allocations, 0,
            "census replacements must use only admitted storage"
        );
        assert_eq!(c.rows.len(), 64);
    }
    #[test]
    fn bounded_census_retains_a_late_hot_family() {
        let mut c = WorkCensus::new(4);
        for i in 0..10_000 {
            c.update(WorkRow {
                node: NodeId(i),
                new_contexts: 1,
                ..Default::default()
            });
        }
        for _ in 0..1_000 {
            c.update(WorkRow {
                node: NodeId(50_000),
                evaluations: 1,
                ..Default::default()
            });
        }
        assert_eq!(c.rows.len(), 4);
        assert!(
            c.rows
                .iter()
                .any(|r| r.node == NodeId(50_000) && r.evaluations == 1_000)
        );
        for p in 1..c.heap.len() {
            assert!(c.rows[c.heap[(p - 1) / 2]].weight() <= c.rows[c.heap[p]].weight());
        }
    }
}
