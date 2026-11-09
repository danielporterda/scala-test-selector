//! Finite lexical lineage for wrappers that capture callbacks.
//!
//! Raw capture IDs would turn recursive wrappers into unbounded call strings.
//! A set of code sites grows by idempotent union instead. Overflow deliberately
//! coalesces family keys; the actual capture payload still keeps its usual
//! conservative joins. No provenance value is used as executable data.
use super::*;

const MAX_ORIGINS: usize = 8;
const UNUSED: Atom = Atom {
    kind: AtomKind::Callback,
    site: OperationId::NONE,
    symbol: SymbolId::NONE,
    binding: 0,
};

struct Origins {
    atoms: [Atom; MAX_ORIGINS],
    len: usize,
    limit: usize,
    overflow: bool,
}

impl Origins {
    fn insert(&mut self, mut atom: Atom) {
        atom.binding = 0;
        if self.overflow {
            return;
        }
        if let Err(index) = self.atoms[..self.len].binary_search(&atom) {
            if self.len == self.limit {
                self.overflow = true;
                self.len = 0;
                return;
            }
            self.atoms.copy_within(index..self.len, index + 1);
            self.atoms[index] = atom;
            self.len += 1;
        }
    }
    fn collect(
        global: &ValuePool,
        local: &ValuePool,
        receiver: Value,
        arguments: &[Value],
        binding: impl Fn(u32) -> Option<Value>,
    ) -> Option<Self> {
        let mut out = Self {
            atoms: [UNUSED; MAX_ORIGINS],
            len: 0,
            limit: MAX_ORIGINS.min(global.member_limit()),
            overflow: false,
        };
        for value in std::iter::once(&receiver).chain(arguments) {
            for atom in local.members(*value) {
                if atom.kind != AtomKind::Callback {
                    continue;
                }
                out.insert(*atom);
                let origins = binding(atom.binding)?;
                if origins == Value::TOP || out.overflow {
                    out.overflow = true;
                    out.len = 0;
                    return Some(out);
                }
                for ancestor in global.members(origins) {
                    out.insert(*ancestor);
                }
            }
        }
        Some(out)
    }
}

pub(super) fn lookup(
    global: &ValuePool,
    local: &ValuePool,
    receiver: Value,
    args: &[Value],
    by_binding: &[Value],
) -> Option<Value> {
    let origins = Origins::collect(global, local, receiver, args, |id| {
        by_binding.get(id as usize).copied()
    })?;
    if origins.overflow {
        Some(Value::TOP)
    } else {
        global.lookup(&origins.atoms[..origins.len], 0)
    }
}

pub(super) fn intern(
    global: &mut ValuePool,
    local: &ValuePool,
    receiver: Value,
    args: &[Value],
    by_binding: &[Value],
    draft_bindings: &[u32],
) -> Result<Value, Error> {
    let origins = Origins::collect(global, local, receiver, args, |id| {
        let id = if id & LOCAL_BINDING != 0 {
            *draft_bindings.get((id & !LOCAL_BINDING) as usize)?
        } else {
            id
        };
        by_binding.get(id as usize).copied()
    })
    .ok_or(Error::Invalid("capture origin binding"))?;
    if origins.overflow {
        Ok(Value::TOP)
    } else {
        global.intern(&origins.atoms[..origins.len], 0)
    }
}

/// Do not join wrapper frames based on only their outer lexical code. The
/// existing overall context limit still bounds how many exact frames we keep.
pub(super) fn needs_exact_arguments(pool: &ValuePool, bindings: &[Value], args: &[Value]) -> bool {
    args.iter().any(|arg| {
        pool.members(*arg).iter().any(|atom| {
            atom.kind == AtomKind::Callback
                && bindings
                    .get(atom.binding as usize)
                    .is_some_and(|origins| *origins != Value::EMPTY)
        })
    })
}

pub(super) fn validate(
    facts: &FactSnapshot,
    pool: &ValuePool,
    frames: &FramePool,
    family: ClosureFamily,
) -> Result<(), Error> {
    if family.origins == Value::TOP {
        return Ok(());
    }
    let atoms = pool.members(family.origins);
    if family.origins.unknown != 0
        || atoms.len() > MAX_ORIGINS
        || atoms.iter().any(|a| {
            a.kind != AtomKind::Callback
                || a.binding != 0
                || !facts
                    .operations
                    .get(a.site.index())
                    .is_some_and(|op| op.opcode == Opcode::BindCallback && op.target == a.symbol)
        })
    {
        return Err(Error::Invalid("capture lexical origins"));
    }
    if std::iter::once(&family.receiver)
        .chain(frames.get(family.arguments))
        .flat_map(|v| pool.members(*v))
        .any(|a| a.kind == AtomKind::Callback && atoms.binary_search(a).is_err())
    {
        return Err(Error::Invalid(
            "capture lexical origins omit direct callback",
        ));
    }
    Ok(())
}
