//! Flat normalized compiler facts. Builders own memory; readers borrow it.
pub mod codec;
mod validation;
use selector_types::*;
use std::collections::HashMap;
use std::hash::{BuildHasher, Hasher};

#[derive(Clone, Copy, Debug, Default)]
pub struct TextRange {
    pub start: u64,
    pub len: u32,
}
#[derive(Debug, Default)]
pub struct StringPool {
    pub bytes: Vec<u8>,
    pub entries: Vec<TextRange>,
}
impl StringPool {
    pub fn get(&self, id: StrId) -> &str {
        if id.is_none() {
            return "";
        }
        let r = self.entries[id.index()];
        std::str::from_utf8(&self.bytes[r.start as usize..r.start as usize + r.len as usize])
            .expect("validated string pool")
    }
    pub fn len(&self) -> usize {
        self.entries.len()
    }
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

#[derive(Clone, Copy, Debug)]
pub struct FileRecord {
    pub path: StrId,
    pub source: StrId,
    pub revision: StrId,
    pub context: StrId,
    pub source_hash: ContentHash,
    pub flags: u32,
}
#[derive(Clone, Copy, Debug)]
pub struct SymbolRecord {
    pub name: StrId,
    pub display: StrId,
    pub owner: SymbolId,
    pub file: FileId,
    pub context: StrId,
    pub kind: u32,
    pub properties: u64,
    pub signature: StrId,
    pub span: Span,
    pub flags: u32,
}
#[derive(Clone, Copy, Debug)]
pub struct OccurrenceRecord {
    pub file: FileId,
    pub symbol: SymbolId,
    pub span: Span,
    pub role: u32,
    pub ordinal: u32,
}
#[derive(Clone, Copy, Debug)]
pub struct RelationRecord {
    pub source: SymbolId,
    pub target: SymbolId,
    pub kind: RelationKind,
    pub file: FileId,
}
#[derive(Clone, Copy, Debug)]
pub struct BodyRecord {
    pub symbol: SymbolId,
    pub file: FileId,
    pub span: Span,
    pub name_span: Span,
    pub operations: IdRange,
    pub parameters: IdRange,
    pub body_hash: ContentHash,
    pub flags: u32,
}
#[derive(Clone, Copy, Debug)]
pub struct OperationRecord {
    pub body: BodyId,
    pub opcode: Opcode,
    pub target: SymbolId,
    pub dest: ValueId,
    pub a: ValueId,
    pub b: ValueId,
    pub arguments: IdRange,
    pub span: Span,
    pub flags: u32,
}
/// One complete conjunction of compiler-normalized result classes. A declared
/// result uses `OperationId::NONE`; an operation row refines that exact result.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ResultBoundRecord {
    pub symbol: SymbolId,
    pub operation: OperationId,
    pub classes: IdRange,
}
pub const MAX_RESULT_BOUND_CLASSES: usize = 64;
#[derive(Clone, Copy, Debug)]
pub struct SuiteRecord {
    pub name: StrId,
    pub symbol: SymbolId,
    pub file: FileId,
    pub flags: u32,
}
#[derive(Clone, Copy, Debug)]
pub struct IssueRecord {
    pub kind: IssueKind,
    pub file: FileId,
    pub symbol: SymbolId,
    pub detail: StrId,
}

#[derive(Debug)]
pub struct FactSnapshot {
    pub identity: ContentHash,
    pub revision: StrId,
    pub strings: StringPool,
    pub files: Vec<FileRecord>,
    pub symbols: Vec<SymbolRecord>,
    pub occurrences: Vec<OccurrenceRecord>,
    pub relations: Vec<RelationRecord>,
    pub bodies: Vec<BodyRecord>,
    pub operations: Vec<OperationRecord>,
    pub operands: Vec<ValueId>,
    pub result_bounds: Vec<ResultBoundRecord>,
    pub bound_classes: Vec<SymbolId>,
    pub suites: Vec<SuiteRecord>,
    pub issues: Vec<IssueRecord>,
}
impl Default for FactSnapshot {
    fn default() -> Self {
        Self {
            identity: ContentHash::default(),
            revision: StrId::NONE,
            strings: StringPool::default(),
            files: Vec::new(),
            symbols: Vec::new(),
            occurrences: Vec::new(),
            relations: Vec::new(),
            bodies: Vec::new(),
            operations: Vec::new(),
            operands: Vec::new(),
            result_bounds: Vec::new(),
            bound_classes: Vec::new(),
            suites: Vec::new(),
            issues: Vec::new(),
        }
    }
}
impl FactSnapshot {
    pub fn text(&self, id: StrId) -> &str {
        self.strings.get(id)
    }
    pub fn symbol_name(&self, id: SymbolId) -> &str {
        if id.is_none() {
            ""
        } else {
            self.text(self.symbols[id.index()].name)
        }
    }
    pub fn path(&self, id: FileId) -> &str {
        if id.is_none() {
            ""
        } else {
            self.text(self.files[id.index()].path)
        }
    }
    pub fn find_symbol(&self, name: &str) -> Option<SymbolId> {
        self.symbols
            .iter()
            .position(|s| self.text(s.name) == name)
            .map(|i| SymbolId(i as u32))
    }
    /// Exact compiler-selected private call on `this` within the same source
    /// owner. Lexical selection removes override uncertainty, not the callee's
    /// execution, initialization or callback effects.
    pub fn compiler_private_dispatch(&self, op: &OperationRecord) -> bool {
        if op.opcode != Opcode::VirtualCall
            || op.flags != 0
            || op.a != ValueId(0)
            || !op.b.is_none()
        {
            return false;
        }
        let Some(target) = self.symbols.get(op.target.index()) else {
            return false;
        };
        if target.kind != 3
            || target.flags & (SYMBOL_DEFINED | SYMBOL_NATIVE_BINARY | SYMBOL_SCALA_PRIVATE_METHOD)
                != SYMBOL_DEFINED | SYMBOL_SCALA_PRIVATE_METHOD
        {
            return false;
        }
        let Some(body) = self.bodies.get(op.body.index()) else {
            return false;
        };
        if body.flags & (BODY_BINARY_RECIPE | BODY_STATIC_INITIALIZER) != 0
            || body.file != target.file
        {
            return false;
        }
        let Some(caller) = self.symbols.get(body.symbol.index()) else {
            return false;
        };
        if caller.flags & (SYMBOL_DEFINED | SYMBOL_NATIVE_BINARY) != SYMBOL_DEFINED
            || caller.kind != 3
            || caller.file != body.file
            || caller.owner != target.owner
            || caller.context != target.context
        {
            return false;
        }
        self.symbols.get(target.owner.index()).is_some_and(|owner| {
            matches!(owner.kind, 10 | 13 | 14)
                && owner.flags & (SYMBOL_DEFINED | SYMBOL_NATIVE_BINARY) == SYMBOL_DEFINED
                && owner.file == body.file
                && owner.context == target.context
        }) && self.files.get(body.file.index()).is_some_and(|file| {
            file.flags & FILE_BINARY_SOURCE == 0
                && file.context == target.context
                && file.source_hash != ContentHash::default()
        })
    }
    /// Borrow the exact admitted key's clause. Operation-to-declaration fallback
    /// and current runtime class validity are decisions for the query engine.
    pub fn result_bound(&self, symbol: SymbolId, operation: OperationId) -> Option<&[SymbolId]> {
        let key = (symbol, operation);
        let index = self
            .result_bounds
            .binary_search_by_key(&key, |row| (row.symbol, row.operation))
            .ok()?;
        let range = self.result_bounds[index].classes;
        let end = range.start.checked_add(range.len)?;
        self.bound_classes.get(range.start as usize..end as usize)
    }
    pub fn owned_bytes(&self) -> usize {
        self.strings.bytes.capacity()
            + self.strings.entries.capacity() * std::mem::size_of::<TextRange>()
            + self.files.capacity() * std::mem::size_of::<FileRecord>()
            + self.symbols.capacity() * std::mem::size_of::<SymbolRecord>()
            + self.occurrences.capacity() * std::mem::size_of::<OccurrenceRecord>()
            + self.relations.capacity() * std::mem::size_of::<RelationRecord>()
            + self.bodies.capacity() * std::mem::size_of::<BodyRecord>()
            + self.operations.capacity() * std::mem::size_of::<OperationRecord>()
            + self.operands.capacity() * 4
            + self.result_bounds.capacity() * std::mem::size_of::<ResultBoundRecord>()
            + self.bound_classes.capacity() * std::mem::size_of::<SymbolId>()
            + self.suites.capacity() * std::mem::size_of::<SuiteRecord>()
            + self.issues.capacity() * std::mem::size_of::<IssueRecord>()
    }
    pub fn validate(&self) -> Result<(), Error> {
        validation::validate(self)
    }
}

/// The interning index contains hashes and IDs, never a second owned string.
pub struct FactBuilder {
    pub facts: FactSnapshot,
    string_heads: HashMap<u64, StrId>,
    string_next: Vec<StrId>,
    symbols: HashMap<(StrId, StrId, u32), SymbolId>,
    hasher: std::collections::hash_map::RandomState,
}
impl Default for FactBuilder {
    fn default() -> Self {
        Self::new()
    }
}
impl FactBuilder {
    pub fn new() -> Self {
        Self {
            facts: FactSnapshot {
                revision: StrId::NONE,
                ..Default::default()
            },
            string_heads: HashMap::new(),
            string_next: Vec::new(),
            symbols: HashMap::new(),
            hasher: Default::default(),
        }
    }
    pub fn intern(&mut self, text: &str) -> Result<StrId, Error> {
        let mut h = self.hasher.build_hasher();
        h.write(text.as_bytes());
        let key = h.finish();
        let first = self.string_heads.get(&key).copied().unwrap_or(StrId::NONE);
        let mut next = first;
        while !next.is_none() {
            if self.facts.text(next) == text {
                return Ok(next);
            }
            next = self.string_next[next.index()];
        }
        let id = StrId::checked(self.facts.strings.entries.len())?;
        let len = u32::try_from(text.len()).map_err(|_| Error::Limit("string length"))?;
        self.facts.strings.entries.push(TextRange {
            start: self.facts.strings.bytes.len() as u64,
            len,
        });
        self.facts.strings.bytes.extend_from_slice(text.as_bytes());
        self.string_next.push(first);
        self.string_heads.insert(key, id);
        Ok(id)
    }
    pub fn ensure_symbol(&mut self, name: &str, file: FileId) -> Result<SymbolId, Error> {
        let name = self.intern(name)?;
        self.ensure_pooled_symbol(name, file)
    }
    pub fn lookup_symbol(&self, name: &str, file: FileId) -> Option<SymbolId> {
        if !file.is_none() && file.index() >= self.facts.files.len() {
            return None;
        }
        let mut hasher = self.hasher.build_hasher();
        hasher.write(name.as_bytes());
        let mut pooled = *self.string_heads.get(&hasher.finish())?;
        while !pooled.is_none() && self.facts.text(pooled) != name {
            pooled = self.string_next[pooled.index()];
        }
        if pooled.is_none() {
            return None;
        }
        let context = if file.is_none() {
            StrId::NONE
        } else {
            self.facts.files[file.index()].context
        };
        let local = if selector_types::symbol::is_local(name) {
            file.0
        } else {
            u32::MAX
        };
        self.symbols.get(&(pooled, context, local)).copied()
    }
    /// Look up a global compiler identity in an explicit context without
    /// associating external metadata with a source document.
    pub fn lookup_global_symbol(&self, name: &str, context: StrId) -> Option<SymbolId> {
        if (!context.is_none() && context.index() >= self.facts.strings.len())
            || selector_types::symbol::is_local(name)
        {
            return None;
        }
        let mut hasher = self.hasher.build_hasher();
        hasher.write(name.as_bytes());
        let mut pooled = *self.string_heads.get(&hasher.finish())?;
        while !pooled.is_none() && self.facts.text(pooled) != name {
            pooled = self.string_next[pooled.index()];
        }
        self.symbols.get(&(pooled, context, u32::MAX)).copied()
    }
    pub fn ensure_global_symbol(&mut self, name: &str, context: StrId) -> Result<SymbolId, Error> {
        let name = self.intern(name)?;
        self.ensure_pooled_global_symbol(name, context)
    }
    /// Admit a pooled global identity without inventing a source-file origin.
    pub fn ensure_pooled_global_symbol(
        &mut self,
        name: StrId,
        context: StrId,
    ) -> Result<SymbolId, Error> {
        if name.is_none()
            || name.index() >= self.facts.strings.len()
            || (!context.is_none() && context.index() >= self.facts.strings.len())
            || selector_types::symbol::is_local(self.facts.text(name))
        {
            return Err(Error::Invalid("global symbol context identity"));
        }
        let key = (name, context, u32::MAX);
        if let Some(id) = self.symbols.get(&key) {
            return Ok(*id);
        }
        let id = SymbolId::checked(self.facts.symbols.len())?;
        self.facts.symbols.push(SymbolRecord {
            name,
            display: StrId::NONE,
            owner: SymbolId::NONE,
            file: FileId::NONE,
            context,
            kind: 0,
            properties: 0,
            signature: StrId::NONE,
            span: Span::default(),
            flags: 0,
        });
        self.symbols.insert(key, id);
        Ok(id)
    }
    /// Admit an already interned compiler spelling without rehashing its text.
    pub fn ensure_pooled_symbol(&mut self, name: StrId, file: FileId) -> Result<SymbolId, Error> {
        if name.is_none()
            || name.index() >= self.facts.strings.len()
            || (!file.is_none() && file.index() >= self.facts.files.len())
        {
            return Err(Error::Invalid("pooled symbol identity"));
        }
        let context = if file.is_none() {
            StrId::NONE
        } else {
            self.facts.files[file.index()].context
        };
        let spelling = self.facts.text(name);
        let is_local = selector_types::symbol::is_local(spelling);
        if is_local && file.is_none() {
            return Err(Error::Invalid("local symbol without source file"));
        }
        let local = if is_local { file.0 } else { u32::MAX };
        let key = (name, context, local);
        if let Some(id) = self.symbols.get(&key) {
            return Ok(*id);
        }
        let id = SymbolId::checked(self.facts.symbols.len())?;
        self.facts.symbols.push(SymbolRecord {
            name,
            display: StrId::NONE,
            owner: SymbolId::NONE,
            file: if is_local { file } else { FileId::NONE },
            context,
            kind: 0,
            properties: 0,
            signature: StrId::NONE,
            span: Span::default(),
            flags: 0,
        });
        self.symbols.insert(key, id);
        Ok(id)
    }
    pub fn issue(
        &mut self,
        kind: IssueKind,
        file: FileId,
        symbol: SymbolId,
        detail: &str,
    ) -> Result<(), Error> {
        let detail = self.intern(detail)?;
        self.facts.issues.push(IssueRecord {
            kind,
            file,
            symbol,
            detail,
        });
        Ok(())
    }
    pub fn finish(self) -> Result<FactSnapshot, Error> {
        self.facts.validate()?;
        Ok(self.facts)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn global_metadata_interning_preserves_context_without_source_authority() {
        let mut builder = FactBuilder::new();
        let a = builder.intern("compile:a").unwrap();
        let b = builder.intern("compile:b").unwrap();
        let name = builder.intern("library/Factory.apply().").unwrap();
        let first = builder.ensure_pooled_global_symbol(name, a).unwrap();
        assert_eq!(
            first,
            builder
                .ensure_global_symbol("library/Factory.apply().", a)
                .unwrap()
        );
        let second = builder.ensure_pooled_global_symbol(name, b).unwrap();
        assert_ne!(first, second);
        assert_eq!(
            builder.lookup_global_symbol("library/Factory.apply().", a),
            Some(first)
        );
        assert_eq!(
            builder.lookup_global_symbol("library/Factory.apply().", b),
            Some(second)
        );
        for id in [first, second] {
            let record = builder.facts.symbols[id.index()];
            assert!(record.file.is_none());
            assert_eq!(record.flags, 0);
        }
        assert!(builder.ensure_global_symbol("local4", a).is_err());
        assert!(
            builder
                .ensure_pooled_global_symbol(name, StrId(999))
                .is_err()
        );
        assert!(
            builder
                .lookup_global_symbol("library/Factory.apply().", StrId(999))
                .is_none()
        );
    }
    #[test]
    fn interning_does_not_duplicate_text() {
        let mut b = FactBuilder::new();
        let x = b.intern("hello").unwrap();
        for _ in 0..1000 {
            assert_eq!(b.intern("hello").unwrap(), x);
        }
        assert_eq!(b.facts.strings.bytes, b"hello");
        assert_eq!(b.facts.strings.len(), 1);
    }
    #[test]
    fn owned_bytes_includes_both_flat_bound_columns() {
        let mut facts = FactSnapshot::default();
        let before = facts.owned_bytes();
        facts.result_bounds.reserve_exact(5);
        facts.bound_classes.reserve_exact(9);
        assert_eq!(
            facts.owned_bytes() - before,
            facts.result_bounds.capacity() * std::mem::size_of::<ResultBoundRecord>()
                + facts.bound_classes.capacity() * std::mem::size_of::<SymbolId>()
        );
        assert_eq!(std::mem::size_of::<ResultBoundRecord>(), 16);
    }
}
