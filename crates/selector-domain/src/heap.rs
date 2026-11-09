//! Finite receiver-root heap partitions. Neither context IDs nor nested heap
//! histories participate in identity; all metadata is owned by one query.
use selector_types::*;
use std::collections::HashMap;

pub const LOCAL_HEAP_OWNER: u32 = 1 << 31;
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HeapOwnerKey {
    pub site: OperationId,
    pub root: SymbolId,
}
pub fn root_binding(root: SymbolId) -> Result<u32, Error> {
    root.0
        .checked_add(1)
        .ok_or(Error::Invalid("heap root origin"))
}
pub fn binding_root(binding: u32) -> Option<SymbolId> {
    binding.checked_sub(1).map(SymbolId)
}
pub fn object_origin(binding: u32) -> SymbolId {
    binding_root(binding).unwrap_or(SymbolId::NONE)
}
pub fn origin_binding(root: SymbolId) -> Result<u32, Error> {
    if root.is_none() {
        Ok(0)
    } else {
        root_binding(root)
    }
}
#[derive(Debug)]
pub struct HeapOwners {
    base: u32,
    operations: usize,
    symbols: usize,
    rows: Vec<HeapOwnerKey>,
    index: HashMap<HeapOwnerKey, u32>,
}
impl HeapOwners {
    pub fn new(operations: usize, symbols: usize) -> Result<Self, Error> {
        let base = operations
            .checked_add(symbols)
            .filter(|n| *n < LOCAL_HEAP_OWNER as usize)
            .ok_or(Error::Limit("heap owner namespaces"))? as u32;
        Ok(Self {
            base,
            operations,
            symbols,
            rows: Vec::new(),
            index: HashMap::new(),
        })
    }
    pub fn base(&self) -> u32 {
        self.base
    }
    pub fn rows(&self) -> &[HeapOwnerKey] {
        &self.rows
    }
    pub fn lookup(&self, key: HeapOwnerKey) -> Option<u32> {
        self.index.get(&key).copied()
    }
    pub fn key(&self, owner: u32) -> Option<HeapOwnerKey> {
        self.rows
            .get(owner.checked_sub(self.base)? as usize)
            .copied()
    }
    pub fn intern(&mut self, key: HeapOwnerKey) -> Result<u32, Error> {
        if key.site.index() >= self.operations || key.root.index() >= self.symbols {
            return Err(Error::Invalid("heap owner key"));
        }
        if let Some(id) = self.lookup(key) {
            return Ok(id);
        }
        let owner = self
            .base
            .checked_add(u32::try_from(self.rows.len()).map_err(|_| Error::Limit("heap owners"))?)
            .filter(|id| *id < LOCAL_HEAP_OWNER)
            .ok_or(Error::Limit("heap owners"))?;
        self.rows
            .try_reserve(1)
            .map_err(|_| Error::Limit("heap owner rows"))?;
        self.index
            .try_reserve(1)
            .map_err(|_| Error::Limit("heap owner index"))?;
        self.rows.push(key);
        self.index.insert(key, owner);
        Ok(owner)
    }
    pub fn owned_bytes(&self) -> usize {
        self.rows.capacity() * std::mem::size_of::<HeapOwnerKey>() + self.index.capacity() * 24
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn partitions_are_checked_finite_and_keep_root_namespaces_disjoint() {
        let mut owners = HeapOwners::new(20, 10).unwrap();
        let a = HeapOwnerKey {
            site: OperationId(3),
            root: SymbolId(0),
        };
        let b = HeapOwnerKey {
            site: OperationId(3),
            root: SymbolId(1),
        };
        assert_eq!(owners.intern(a).unwrap(), 30);
        assert_eq!(owners.intern(b).unwrap(), 31);
        assert_eq!(owners.intern(a).unwrap(), 30);
        assert_eq!(owners.rows(), [a, b]);
        assert_eq!(owners.key(29), None);
        assert_eq!(owners.key(LOCAL_HEAP_OWNER), None);
        assert_eq!(
            object_origin(root_binding(SymbolId(0)).unwrap()),
            SymbolId(0)
        );
        assert_eq!(object_origin(0), SymbolId::NONE);
        assert!(root_binding(SymbolId::NONE).is_err());
        assert!(
            owners
                .intern(HeapOwnerKey {
                    site: OperationId::NONE,
                    ..a
                })
                .is_err()
        );
        assert!(
            owners
                .intern(HeapOwnerKey {
                    root: SymbolId(10),
                    ..a
                })
                .is_err()
        );
        assert!(HeapOwners::new(LOCAL_HEAP_OWNER as usize, 0).is_err());
    }
    #[test]
    fn closure_creation_keys_preserve_finite_object_sites_and_root_origins() {
        use crate::*;
        let mut source = ValuePool::new(64);
        let mut destination = ValuePool::new(64);
        let a = Atom {
            kind: AtomKind::Object,
            site: OperationId(2),
            symbol: SymbolId(3),
            binding: root_binding(SymbolId(0)).unwrap(),
        };
        let b = Atom {
            binding: root_binding(SymbolId(1)).unwrap(),
            ..a
        };
        let av = source.singleton(a).unwrap();
        let bv = source.singleton(b).unwrap();
        let af = destination.family(&source, av).unwrap();
        let bf = destination.family(&source, bv).unwrap();
        assert_ne!(af, bf);
        assert_eq!(destination.members(af), [a]);
        let callback = source
            .singleton(Atom {
                kind: AtomKind::Callback,
                site: OperationId(5),
                symbol: SymbolId(6),
                binding: 42,
            })
            .unwrap();
        let normalized = destination.family(&source, callback).unwrap();
        assert_eq!(destination.members(normalized)[0].binding, 0);
    }
}
