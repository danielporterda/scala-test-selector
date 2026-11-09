//! Exact native overrides without all-pairs ABI-group ancestry searches.
use super::*;

#[derive(Default, Debug)]
pub(super) struct Work {
    pub owner_walks: usize,
    pub ancestor_visits: usize,
    pub abi_lookups: usize,
    pub matching_members: usize,
}

pub(super) fn augment(facts: &mut FactSnapshot, registry: &Registry) -> Work {
    // Borrow registry names/descriptors. Numeric owner grouping lets one
    // traversal serve every member declared on the same context-qualified type.
    let mut members: Vec<_> = registry.methods.iter().collect();
    members.sort_unstable_by(|(a, av), (b, bv)| {
        (
            a.context,
            av.owner,
            &a.name,
            &a.descriptor,
            &a.owner,
            av.symbol,
        )
            .cmp(&(
                b.context,
                bv.owner,
                &b.name,
                &b.descriptor,
                &b.owner,
                bv.symbol,
            ))
    });
    let types = BinaryAdjacency::new(facts, RelationKind::Parent, false);
    let mut pending = Vec::new();
    let mut ancestors = Vec::new();
    let mut seen = HashSet::new();
    let mut edges = Vec::new();
    let mut work = Work::default();
    let mut start = 0;
    while start < members.len() {
        let context = members[start].0.context;
        let owner = members[start].1.owner;
        let end = start
            + members[start..]
                .partition_point(|(key, data)| key.context == context && data.owner == owner);
        let children = &members[start..end];
        start = end;
        if children
            .iter()
            .all(|(_, data)| data.flags & (0x0002 | 0x0008) != 0)
        {
            continue;
        }
        work.owner_walks += 1;
        pending.clear();
        ancestors.clear();
        seen.clear();
        seen.insert(owner);
        pending.extend_from_slice(types.get(owner));
        while let Some(ancestor) = pending.pop() {
            if !seen.insert(ancestor) {
                continue;
            }
            work.ancestor_visits += 1;
            ancestors.push(ancestor);
            pending.extend_from_slice(types.get(ancestor));
        }
        for (key, child) in children {
            if child.flags & (0x0002 | 0x0008) != 0 {
                continue;
            }
            for &ancestor in &ancestors {
                work.abi_lookups += 1;
                let sought = (
                    context,
                    ancestor,
                    key.name.as_str(),
                    key.descriptor.as_str(),
                );
                let begin = members.partition_point(|(other, data)| {
                    (
                        other.context,
                        data.owner,
                        other.name.as_str(),
                        other.descriptor.as_str(),
                    ) < sought
                });
                let end = members.partition_point(|(other, data)| {
                    (
                        other.context,
                        data.owner,
                        other.name.as_str(),
                        other.descriptor.as_str(),
                    ) <= sought
                });
                for (_, parent) in &members[begin..end] {
                    work.matching_members += 1;
                    if child.owner == parent.owner || parent.flags & (0x0002 | 0x0008 | 0x0010) != 0
                    {
                        continue;
                    }
                    edges.push((
                        child.symbol,
                        parent.symbol,
                        facts.symbols[child.symbol.index()].file,
                    ));
                }
            }
        }
    }
    edges.sort_unstable();
    edges.dedup();
    let mut existing: Vec<_> = facts
        .relations
        .iter()
        .filter(|relation| relation.kind == RelationKind::Override)
        .map(|relation| (relation.source, relation.target, relation.file))
        .collect();
    existing.sort_unstable();
    for (source, target, file) in edges {
        if existing.binary_search(&(source, target, file)).is_ok() {
            continue;
        }
        facts.relations.push(RelationRecord {
            source,
            target,
            file,
            kind: RelationKind::Override,
        });
    }
    work
}

#[cfg(test)]
#[path = "binary_overrides_tests.rs"]
mod tests;
