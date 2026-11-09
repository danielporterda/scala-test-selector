//! Borrowed publication-barrier views and checked reconstruction of domain IDs.
//!
//! These APIs preserve dense IDs without exposing interner hash buckets or Rust
//! memory layouts as a persistence format. Callers encode fields explicitly and
//! validate program-specific atom/slot references against their bound snapshot.
use super::*;

impl ValuePool {
    pub fn snapshot_sets(&self) -> impl ExactSizeIterator<Item = &[Atom]> {
        self.entries.iter().map(|entry| {
            &self.atoms[entry.start as usize..entry.start as usize + entry.len as usize]
        })
    }

    /// Reconstruct one canonical set in original ID order. Set zero is empty.
    pub fn restore_set(&mut self, expected: SetId, members: &[Atom]) -> Result<(), Error> {
        if (expected.0 == 0 && !members.is_empty())
            || (expected.0 != 0 && expected.index() != self.entries.len())
            || members.windows(2).any(|pair| pair[0] >= pair[1])
        {
            return Err(Error::Invalid("snapshot value set order"));
        }
        let unknown = if members.iter().any(|atom| atom.kind == AtomKind::UpperBound) {
            UNKNOWN_VALUE | UNKNOWN_TYPED
        } else {
            0
        };
        self.heads
            .try_reserve(1)
            .map_err(|_| Error::Limit("snapshot value index"))?;
        if self.intern(members, unknown)?.set != expected {
            return Err(Error::Invalid("snapshot duplicate or oversized value set"));
        }
        Ok(())
    }

    pub fn validate_snapshot_value(&self, value: Value) -> Result<(), Error> {
        if value.set.index() >= self.entries.len()
            || value.unknown
                & !(UNKNOWN_VALUE
                    | WIDENED_VALUE
                    | UNKNOWN_FIELD
                    | UNKNOWN_CALLBACK
                    | UNKNOWN_TYPED)
                != 0
        {
            return Err(Error::Invalid("snapshot value reference"));
        }
        let bounded = self
            .members(value)
            .iter()
            .any(|atom| atom.kind == AtomKind::UpperBound);
        if (value.unknown & UNKNOWN_TYPED != 0 && !bounded)
            || (bounded && value.unknown & !UNKNOWN_TYPED == 0)
        {
            return Err(Error::Invalid("snapshot typed unknown coverage"));
        }
        Ok(())
    }
}

impl FramePool {
    pub fn snapshot_frames(&self) -> impl ExactSizeIterator<Item = &[Value]> {
        self.entries.iter().map(|entry| {
            &self.values[entry.start as usize..entry.start as usize + entry.len as usize]
        })
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn restore_frame(&mut self, expected: FrameId, values: &[Value]) -> Result<(), Error> {
        self.entries
            .try_reserve(1)
            .map_err(|_| Error::Limit("snapshot frame records"))?;
        self.heads
            .try_reserve(1)
            .map_err(|_| Error::Limit("snapshot frame index"))?;
        if (expected.0 == 0 && !values.is_empty())
            || (expected.0 != 0 && expected.0 as usize != self.entries.len())
            || self.intern(values)? != expected
        {
            return Err(Error::Invalid("snapshot frame order or duplicate"));
        }
        Ok(())
    }
}

impl Dependencies {
    pub fn snapshot_contexts(&self) -> impl ExactSizeIterator<Item = (u64, bool)> + '_ {
        self.generation
            .iter()
            .copied()
            .zip(self.invalid.iter().copied())
    }

    /// Only live subscriptions affect future publication. Stale generations
    /// are intentionally compacted; current generations and invalid bits stay exact.
    pub fn snapshot_reads(&self) -> impl Iterator<Item = (ContextId, Read)> + '_ {
        self.active_reads()
    }

    pub fn restore_epoch(&mut self, epoch: u64) -> Result<(), Error> {
        if !self.generation.is_empty() || !self.edges.is_empty() || epoch >= u64::MAX / 2 {
            return Err(Error::Invalid("snapshot dependency epoch"));
        }
        self.epoch = epoch;
        Ok(())
    }

    pub fn restore_context_state(&mut self, generation: u64, invalid: bool) -> Result<(), Error> {
        ContextId::checked(self.generation.len())?;
        self.generation
            .try_reserve(1)
            .map_err(|_| Error::Limit("snapshot dependency contexts"))?;
        self.invalid
            .try_reserve(1)
            .map_err(|_| Error::Limit("snapshot dependency contexts"))?;
        self.generation.push(generation);
        self.invalid.push(invalid);
        Ok(())
    }

    pub fn restore_read(&mut self, context: ContextId, read: Read) -> Result<(), Error> {
        if context.index() >= self.generation.len()
            || self.members.contains_key(&(context, read.slot))
        {
            return Err(Error::Invalid("snapshot duplicate dependency or context"));
        }
        self.heads
            .try_reserve(1)
            .map_err(|_| Error::Limit("snapshot dependency heads"))?;
        self.members
            .try_reserve(1)
            .map_err(|_| Error::Limit("snapshot dependency index"))?;
        self.edges
            .try_reserve(1)
            .map_err(|_| Error::Limit("snapshot dependency reads"))?;
        self.subscribe(context, read)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pool_and_frames_restore_exact_ids_and_reject_noncanonical_rows() {
        let mut original = ValuePool::new(8);
        let object = original
            .singleton(Atom {
                kind: AtomKind::Object,
                site: OperationId(4),
                symbol: SymbolId(7),
                binding: 0,
            })
            .unwrap();
        let bound = original
            .intern(
                &[Atom {
                    kind: AtomKind::UpperBound,
                    site: OperationId::NONE,
                    symbol: SymbolId(9),
                    binding: 0,
                }],
                UNKNOWN_FIELD | UNKNOWN_TYPED,
            )
            .unwrap();
        let mixed = original.join(object, bound).unwrap();
        let mut restored = ValuePool::new(8);
        for (id, atoms) in original.snapshot_sets().enumerate() {
            restored.restore_set(SetId(id as u32), atoms).unwrap();
        }
        for value in [object, bound, mixed, Value::TOP, Value::EMPTY] {
            restored.validate_snapshot_value(value).unwrap();
            assert_eq!(original.members(value), restored.members(value));
        }
        assert!(
            restored
                .restore_set(SetId(restored.len() as u32), &[])
                .is_err()
        );
        assert!(
            restored
                .validate_snapshot_value(Value {
                    set: SetId(999),
                    unknown: 0
                })
                .is_err()
        );
        assert!(
            restored
                .validate_snapshot_value(Value {
                    unknown: 0,
                    ..bound
                })
                .is_err()
        );

        let mut frames = FramePool::default();
        let frame = frames.intern(&[object, mixed]).unwrap();
        let mut loaded = FramePool::default();
        for (id, values) in frames.snapshot_frames().enumerate() {
            loaded.restore_frame(FrameId(id as u32), values).unwrap();
        }
        assert_eq!(loaded.get(frame), frames.get(frame));
        assert!(
            loaded
                .restore_frame(FrameId(loaded.len() as u32), &[])
                .is_err()
        );
    }

    #[test]
    fn dependency_snapshot_preserves_epoch_invalid_bits_and_negative_reads() {
        let slot = Slot {
            kind: SlotKind::Field,
            owner: 5,
            member: 8,
        };
        let mut source = Dependencies::default();
        let absent = Read {
            slot,
            version: 0,
            present: false,
        };
        source.replace(ContextId(0), &[absent]).unwrap();
        source.replace(ContextId(1), &[absent]).unwrap();
        let mut invalidated = Vec::new();
        source.publish(&[slot], 0, 1, &mut invalidated);
        source.acknowledge(ContextId(0));
        let mut loaded = Dependencies::default();
        loaded.restore_epoch(source.epoch()).unwrap();
        for (generation, invalid) in source.snapshot_contexts() {
            loaded.restore_context_state(generation, invalid).unwrap();
        }
        for (context, read) in source.snapshot_reads() {
            loaded.restore_read(context, read).unwrap();
        }
        assert!(loaded.restore_read(ContextId(0), absent).is_err());
        invalidated.clear();
        loaded.publish(&[slot], 1, 2, &mut invalidated);
        assert_eq!(invalidated, [ContextId(0)]);
        assert_eq!(loaded.epoch(), 2);
    }
}
