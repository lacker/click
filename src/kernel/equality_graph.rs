//! Trusted kernel equality graph.
//!
//! This graph is part of the trusted kernel. Kernel rules may accept its
//! equality answers directly in the current proof context; it does not emit
//! a separate proof or run proof search. Only established equalities may be
//! added. Branches clone persistent state so local assumptions do not leak.
//!
//! The current supported fragment is pointers, affine byte offsets, and
//! registered same-snapshot pointer loads, plus whole-offset equality, int32 addition, unsigned division/remainder, bitwise XOR
//! and same-snapshot int32 load congruence.
//! Pointer and offset queries are typed separately; the offset fragment only
//! supports stated equalities, offset addition and int32 scaling congruence. Pointer spelling
//! helpers serve legacy consumers and are not the general equality interface.
//!
//! The pointer fragment uses a persistent union-find with offsets.
//!
//! A pointer is a block and a byte offset, and its address is the block's
//! base address plus the offset. A true pointer equality `p == q` between
//! two blocks therefore states a relation between the two blocks' bases:
//! `base(p.block) = base(q.block) + (q.offset - p.offset)`. The index keeps
//! every block that such facts connect in one class, with each member's base
//! stated relative to the class representative:
//! `base(member) = base(representative) + delta`.
//!
//! Two pointers are then equal exactly when their blocks share a
//! representative and `delta + offset` normalizes to the same affine form on
//! both sides. That answers transitive chains (`a == b`, `b == c`) and
//! displaced spellings (`a + 8` against `c + 8`) with two lookups, with no
//! walk over the facts and no displacement rule. It is the pointer sort of
//! the equality closure described in `docs/internals/equality-closure.md`.
//!
//! Offsets are compared in an exact integer affine normal form: constants
//! folded, each scaled index an atom with its accumulated byte coefficient,
//! and each atom in the kernel's canonical term form, so a load and the load
//! variable naming it are one atom.
//! The form is exact integer arithmetic with overflow checked, so two offsets
//! with one normal form denote one integer under any reading of the offset,
//! wrapping or not. An offset whose arithmetic overflows the form is not
//! normalized, and a fact about it is not filed.
//!
//! The index is persistent and append-only. A union relabels every member of
//! the lighter class (blocks plus application uses), so member lookup is one
//! map access and each moved block/use is charged to a growing class. Affine
//! payload work is charged separately. Same-snapshot load signatures propagate
//! merges iteratively through indexed parent uses, with no nesting cutoff. An
//! equality between two blocks already in one class adds no base relation.
//! An explicit equality of pointers in the same block instead joins their
//! whole offsets in the term classes.

use super::prelude::*;

#[cfg(test)]
mod fact_congruence_tests;
mod inputs;
#[cfg(test)]
mod int32_addition_tests;
#[cfg(test)]
mod int32_load_tests;
#[cfg(test)]
mod int32_tests;
#[cfg(test)]
mod scaled_int32_tests;
#[cfg(test)]
mod storage_tests;
#[cfg(test)]
mod uint64_tests;
pub(in crate::kernel) use inputs::InputKey;
mod terms;

/// A retained, interned machine atom. Equality and ordering use the stable
/// ID; the original term is retained for exact premise support and spelling
/// reconstruction.
#[derive(Clone)]
pub(in crate::kernel) struct MachineAtom(crate::kernel::SharedMachineIntegerTerm);

impl MachineAtom {
    fn new(ty: crate::kernel::MachineIntegerType, value: Bitvector32Term) -> Self {
        Self(crate::kernel::SharedMachineIntegerTerm::intern(ty, value))
    }
    pub(in crate::kernel) fn uint64(value: Bitvector32Term) -> Self {
        Self::new(crate::kernel::MachineIntegerType::UInt64, value)
    }
    pub(in crate::kernel) fn int32(value: Bitvector32Term) -> Self {
        Self::new(crate::kernel::MachineIntegerType::Int32, value)
    }
    pub(in crate::kernel) fn value(&self) -> &Bitvector32Term {
        self.0.value()
    }
}
impl std::fmt::Debug for MachineAtom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.id().fmt(f)
    }
}
impl PartialEq for MachineAtom {
    fn eq(&self, other: &Self) -> bool {
        self.0.id() == other.0.id()
    }
}
impl Eq for MachineAtom {}
impl PartialOrd for MachineAtom {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for MachineAtom {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.id().cmp(&other.0.id())
    }
}
impl std::hash::Hash for MachineAtom {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.id().hash(state);
    }
}

/// One atom of an affine offset: a quantity the normal form does not
/// decompose, with the numeric reading the offset term gives it.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(in crate::kernel) enum OffsetAtom {
    /// A 64-bit offset variable.
    Variable(Variable),
    /// A 32-bit index, sign-extended.
    Int32(MachineAtom),
    /// A 64-bit index, signed or unsigned.
    Int64 { value: MachineAtom, unsigned: bool },
}

impl OffsetAtom {
    fn spelling_cmp(&self, other: &Self) -> std::cmp::Ordering {
        use OffsetAtom::*;
        match (self, other) {
            (Variable(a), Variable(b)) => a.cmp(b),
            (Int32(a), Int32(b)) => a.value().cmp(b.value()),
            (
                Int64 {
                    value: a,
                    unsigned: au,
                },
                Int64 {
                    value: b,
                    unsigned: bu,
                },
            ) => a.value().cmp(b.value()).then(au.cmp(bu)),
            (Variable(_), _) | (Int32(_), Int64 { .. }) => std::cmp::Ordering::Less,
            _ => std::cmp::Ordering::Greater,
        }
    }
}

/// `constant + sum(coefficient * atom)` over exact integers, with no zero
/// coefficient stored.
#[derive(Clone, Debug, Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(in crate::kernel) struct AffineOffset {
    constant: i128,
    terms: std::collections::BTreeMap<OffsetAtom, i128>,
}

impl AffineOffset {
    pub(in crate::kernel) fn constant(value: i128) -> Self {
        Self {
            constant: value,
            terms: std::collections::BTreeMap::new(),
        }
    }

    pub(in crate::kernel) fn is_constant(&self) -> bool {
        self.terms.is_empty()
    }

    /// Candidate key for addresses that differ only in their constant part.
    /// Hash collisions are not equality evidence; callers check occurrences.
    pub(in crate::kernel) fn origin_fingerprint(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        self.terms.hash(&mut hasher);
        hasher.finish()
    }

    /// Keep addresses with the same symbolic origin adjacent in span indexes.
    pub(in crate::kernel) fn address_order(&self, other: &Self) -> std::cmp::Ordering {
        self.terms
            .cmp(&other.terms)
            .then_with(|| self.constant.cmp(&other.constant))
    }

    pub(in crate::kernel) fn constant_difference(&self, other: &Self) -> Option<i128> {
        (self.terms == other.terms)
            .then(|| self.constant.checked_sub(other.constant))
            .flatten()
    }

    fn add_atom(&mut self, atom: OffsetAtom, coefficient: i128) -> Option<()> {
        if coefficient != 0 {
            let entry = self.terms.entry(atom.clone()).or_insert(0);
            *entry = entry.checked_add(coefficient)?;
            if *entry == 0 {
                self.terms.remove(&atom);
            }
        }
        Some(())
    }

    /// Normalize the explicit offset in one iterative traversal. Building a
    /// fresh form at every Add node would copy a growing prefix quadratically.
    pub(in crate::kernel) fn of(offset: &PointerOffsetTerm) -> Option<Self> {
        let mut result = Self::default();
        let mut pending = vec![offset];
        while let Some(offset) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match offset {
                PointerOffsetTerm::Constant(value) => {
                    result.constant = result.constant.checked_add(i128::from(*value))?;
                }
                PointerOffsetTerm::Variable(variable) => {
                    result.add_atom(OffsetAtom::Variable(*variable), 1)?;
                }
                PointerOffsetTerm::Add(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                    let width = i128::from(*byte_width);
                    if let Some(value) = value.as_const() {
                        result.constant = result
                            .constant
                            .checked_add(i128::from(value as i32).checked_mul(width)?)?;
                    } else {
                        result.add_atom(
                            OffsetAtom::Int32(MachineAtom::new(
                                crate::kernel::MachineIntegerType::Int32,
                                crate::kernel::canonical_term(value),
                            )),
                            width,
                        )?;
                    }
                }
                PointerOffsetTerm::Int64Scaled {
                    value,
                    byte_width,
                    unsigned,
                } => {
                    let width = i128::from(*byte_width);
                    let constant = if *unsigned {
                        value.uint64_as_const().map(i128::from)
                    } else {
                        value.int64_as_const().map(i128::from)
                    };
                    if let Some(value) = constant {
                        result.constant = result.constant.checked_add(value.checked_mul(width)?)?;
                    } else {
                        result.add_atom(
                            OffsetAtom::Int64 {
                                value: MachineAtom::new(
                                    if *unsigned {
                                        crate::kernel::MachineIntegerType::UInt64
                                    } else {
                                        crate::kernel::MachineIntegerType::Int64
                                    },
                                    crate::kernel::canonical_term(value),
                                ),
                                unsigned: *unsigned,
                            },
                            width,
                        )?;
                    }
                }
            }
        }
        Some(result)
    }

    pub(in crate::kernel) fn checked_add(&self, other: &Self) -> Option<Self> {
        crate::instrumentation::record_deterministic_work(self.terms.len() + other.terms.len());
        let mut sum = self.clone();
        sum.constant = sum.constant.checked_add(other.constant)?;
        for (atom, coefficient) in &other.terms {
            let entry = sum.terms.entry(atom.clone()).or_insert(0);
            *entry = entry.checked_add(*coefficient)?;
            if *entry == 0 {
                sum.terms.remove(atom);
            }
        }
        Some(sum)
    }

    pub(in crate::kernel) fn checked_negate(&self) -> Option<Self> {
        crate::instrumentation::record_deterministic_work(self.terms.len());
        let mut negated = Self::constant(self.constant.checked_neg()?);
        for (atom, coefficient) in &self.terms {
            negated
                .terms
                .insert(atom.clone(), coefficient.checked_neg()?);
        }
        Some(negated)
    }

    pub(in crate::kernel) fn checked_sub(&self, other: &Self) -> Option<Self> {
        self.checked_add(&other.checked_negate()?)
    }

    /// The offset term this form denotes, or `None` when an atom's
    /// coefficient has no offset spelling (a variable scaled by anything but
    /// one) or a value leaves `i64`.
    pub(in crate::kernel) fn to_offset_term(&self) -> Option<PointerOffsetTerm> {
        let mut term = PointerOffsetTerm::Constant(i64::try_from(self.constant).ok()?);
        // Compact IDs depend on interning order. Legacy spelling output must
        // retain structural order so proof routes do not depend on that order.
        let mut terms: Vec<_> = self.terms.iter().collect();
        terms.sort_by(|(left, _), (right, _)| left.spelling_cmp(right));
        for (atom, coefficient) in terms {
            let coefficient = i64::try_from(*coefficient).ok()?;
            let addend = match atom {
                OffsetAtom::Variable(variable) if coefficient == 1 => {
                    PointerOffsetTerm::Variable(*variable)
                }
                OffsetAtom::Variable(_) => return None,
                OffsetAtom::Int32(value) => PointerOffsetTerm::Int32Scaled {
                    value: Box::new(value.value().clone()),
                    byte_width: coefficient,
                },
                OffsetAtom::Int64 { value, unsigned } => PointerOffsetTerm::Int64Scaled {
                    value: Box::new(value.value().clone()),
                    byte_width: coefficient,
                    unsigned: *unsigned,
                },
            };
            term = PointerOffsetTerm::add(term, addend);
        }
        Some(term)
    }
}

/// A pointer in class-relative form: the representative block, and the
/// address's offset from that representative's base.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(in crate::kernel) struct CanonicalPointer {
    pub(in crate::kernel) representative: PointerBlock,
    pub(in crate::kernel) offset: AffineOffset,
}

/// Closed, persistent pointer, offset, and int32 equality state. Query registration
/// adds only terms and definitional load applications; hypotheses enter through
/// `add_equality`, `add_offset_equality`, and `add_int32_equality`.
/// Cloning copies equality roots into a new lock; hypotheses and unions are
/// never shared mutably. Only unconditional term definitions share the session
/// interner. The locks preserve `PureFactContext`'s Send/Sync contract.
pub(in crate::kernel) struct EqualityGraph {
    state: std::sync::Mutex<EqualityGraphState>,
    // Definitional term annotations, supplied by typed logical-load producers
    // or retained from certified reads after checked expression evaluation.
    // They contain no hypotheses, read authority, or snapshot transport. Like term interning, discovery is shared by evaluation
    // forks; each fork still closes these definitions against its own facts.
    logical_reads: std::sync::Arc<std::sync::Mutex<LogicalPointerReads>>,
}

#[derive(Clone, Default)]
struct LogicalPointerReads {
    definitions: crate::persistent::PersistentMap<Pointer, (Pointer, Pointer)>,
    // Producer-retained read atoms used inside selected address expressions.
    // A matching shape without this metadata is never a load definition.
    offset_definitions: crate::persistent::PersistentMap<(PointerBlock, Variable, i64), Pointer>,
    // Offset-only goals have no block key. Conflicting definitions stay ambiguous.
    offset_read_values: crate::persistent::PersistentMap<(Variable, i64), Option<Pointer>>,
    generation: u64,
}

static NEXT_LOGICAL_READ_GENERATION: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(1);

thread_local! {
    // Session-local term definitions, like the kernel's load-variable
    // interner. Context reconstruction may not forget how a logical term was
    // constructed. Hypotheses and class unions remain entirely path-local.
    static LOGICAL_POINTER_READS: std::cell::RefCell<
        std::sync::Arc<std::sync::Mutex<LogicalPointerReads>>
    > = std::cell::RefCell::new(std::sync::Arc::new(std::sync::Mutex::new(LogicalPointerReads::default())));
}

/// The logical pointer reads discovered so far, as a value a reusable
/// session captures and restores.
#[derive(Clone)]
pub(in crate::kernel) struct LogicalPointerReadsState(LogicalPointerReads);

pub(in crate::kernel) fn capture_logical_pointer_reads() -> LogicalPointerReadsState {
    LOGICAL_POINTER_READS.with(|reads| {
        LogicalPointerReadsState(
            reads
                .borrow()
                .lock()
                .expect("logical pointer reads are never poisoned")
                .clone(),
        )
    })
}

/// Installs the captured reads as this thread's own table. A fresh table is
/// installed rather than the shared one overwritten, so an evaluation that
/// still holds the previous table keeps what it discovered.
pub(in crate::kernel) fn restore_logical_pointer_reads(state: &LogicalPointerReadsState) {
    LOGICAL_POINTER_READS.with(|reads| {
        *reads.borrow_mut() = std::sync::Arc::new(std::sync::Mutex::new(state.0.clone()));
    });
}

pub(in crate::kernel) fn clear_logical_pointer_reads() {
    LOGICAL_POINTER_READS.with(|reads| *reads.borrow_mut() = Default::default());
}

/// The defining load of a producer-retained typed pointer value. The
/// definition is term metadata, not a hypothesis about the loaded address.
pub(crate) fn logical_pointer_read_term(value: &Pointer) -> Option<Bitvector32Term> {
    let application = LOGICAL_POINTER_READS.with(|reads| {
        reads
            .borrow()
            .lock()
            .expect("logical pointer reads")
            .definitions
            .get(value)
            .map(|(application, _)| application.clone())
    })?;
    let load = application.as_loaded_value()?;
    Some(Bitvector32Term::MemoryLoad(
        load.defining_memory,
        Box::new(load.defining_address),
        LoadKind::Pointer,
    ))
}

/// Recover only the exact offset of a producer-registered typed read.
/// An arithmetically similar term or a different pointee stride is not a definition.
pub(in crate::kernel) fn logical_pointer_read_for_offset(
    offset: &PointerOffsetTerm,
) -> Option<Pointer> {
    let PointerOffsetTerm::Int32Scaled { value, byte_width } = offset else {
        return None;
    };
    let Bitvector32Term::Variable(variable) = value.as_ref() else {
        return None;
    };
    LOGICAL_POINTER_READS.with(|reads| {
        reads
            .borrow()
            .lock()
            .expect("logical pointer reads")
            .offset_read_values
            .get(&(*variable, *byte_width))
            .cloned()
            .flatten()
    })
}

impl Default for EqualityGraph {
    fn default() -> Self {
        Self {
            state: Default::default(),
            logical_reads: LOGICAL_POINTER_READS.with(|reads| reads.borrow().clone()),
        }
    }
}

impl Clone for EqualityGraph {
    fn clone(&self) -> Self {
        Self {
            logical_reads: self.logical_reads.clone(),
            state: std::sync::Mutex::new(self.state.lock().expect("equality graph").clone()),
        }
    }
}

impl std::fmt::Debug for EqualityGraph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let state = self.state.lock().expect("equality graph");
        f.debug_struct("EqualityGraph")
            .field("members", &state.parent.len())
            .field("loads", &state.loads.len())
            .finish()
    }
}

/// A signature compares only snapshot identities, block identities and an
/// interned affine-offset ID. It never compares snapshots or load trees.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct LoadSignature {
    memory: (u32, u32),
    address_block: PointerBlock,
    address_offset: u64,
    kind: crate::kernel::LoadKind,
}

#[derive(Clone)]
struct LoadApplication {
    memory: (u32, u32),
    address_block: PointerBlock,
    address_offset: AffineOffset,
    /// Two reads of one address are one value only when they are one kind.
    kind: crate::kernel::LoadKind,
}

/// Hash-consing the affine sequence uses shallow keys. Offset atoms hold
/// interned machine terms, so a map comparison never descends into a term.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum OffsetPart {
    Constant(i128),
    Term(u64, OffsetAtom, i128),
}

type PointerReadKey = ((u32, u32), Pointer);
type PointerReadPair = (PointerReadKey, PointerReadKey);

#[derive(Clone, Debug)]
pub(in crate::kernel) struct SupportedPointerReadEquality {
    pub(in crate::kernel) proof: std::sync::Arc<super::memory_provenance::CheckedLoadEquality>,
    pub(in crate::kernel) supports: std::sync::Arc<[Proposition]>,
}

#[derive(Clone, Default)]
struct EqualityGraphState {
    terms: terms::TermClasses,
    input_history: Option<std::sync::Arc<inputs::History>>,
    logical_values: crate::persistent::PersistentSet<Pointer>,
    /// Compound query dependencies already registered at this metadata
    /// generation. Later producer definitions invalidate a miss lazily.
    logical_query_dependencies: crate::persistent::PersistentMap<Pointer, u64>,
    logical_offset_dependencies: crate::persistent::PersistentMap<PointerOffsetTerm, u64>,
    typed_reads: crate::persistent::PersistentSet<PointerBlock>,
    checked_read_generation: u64,
    // These checked pairs never enter union-find. A consumer must check
    // their selected authority against its current context before use.
    supported_read_equalities:
        crate::persistent::PersistentMap<PointerReadPair, SupportedPointerReadEquality>,
    // One selected older read per produced read, for contextual supplier
    // lookup. This index conveys no unconditional equality or authority.
    supported_read_sources: crate::persistent::PersistentMap<PointerReadKey, Bitvector32Term>,
    /// The exact class-merge delta stream. A consumer with a persistent
    /// class-keyed index can update only entries in the moved class. Clones
    /// share the prefix; a rebuilt (restricted) graph has a new origin.
    merge_origin: std::sync::Arc<()>,
    merge_history: Option<std::sync::Arc<PointerMergeHistory>>,
    parent: crate::persistent::PersistentMap<PointerBlock, (PointerBlock, AffineOffset)>,
    members: crate::persistent::PersistentMap<
        PointerBlock,
        crate::persistent::PersistentMap<PointerBlock, AffineOffset>,
    >,
    // Weight includes application uses, so repeatedly joining a fresh block
    // to one with many parents never reindexes the large side.
    weights: crate::persistent::PersistentMap<PointerBlock, usize>,
    // A storage coordinate is retained evidence, not the union-find root.
    // None records an ambiguous class. Append-only merges cannot regain a
    // unique anchor; no member enumeration is needed to answer a query.
    storage_anchors: crate::persistent::PersistentMap<PointerBlock, Option<PointerBlock>>,
    loads: crate::persistent::PersistentMap<PointerBlock, LoadApplication>,
    uses: crate::persistent::PersistentMap<
        PointerBlock,
        crate::persistent::PersistentSet<PointerBlock>,
    >,
    signatures: crate::persistent::PersistentMap<LoadSignature, PointerBlock>,
    load_signatures: crate::persistent::PersistentMap<PointerBlock, LoadSignature>,
    offset_parts: crate::persistent::PersistentMap<OffsetPart, u64>,
}

/// `base(moved) = base(kept) + moved_from_kept` at one trusted class merge.
/// The graph has already checked and closed the equality before recording
/// this delta; the record is an index update, not independent evidence.
#[derive(Clone, Debug)]
pub(in crate::kernel) struct PointerClassMerge {
    pub(in crate::kernel) moved: PointerBlock,
    pub(in crate::kernel) kept: PointerBlock,
    pub(in crate::kernel) moved_from_kept: AffineOffset,
}

#[derive(Clone)]
struct PointerMergeHistory {
    depth: usize,
    merge: PointerClassMerge,
    parent: Option<std::sync::Arc<PointerMergeHistory>>,
}

impl EqualityGraph {
    /// Register the exact symbolic pointer value just constructed by a typed
    /// load. This is trusted-kernel term metadata, not an assumed
    /// equality: the producer supplies the canonical defining snapshot and
    /// address. Never recover this equation by decoding pointer arithmetic.
    pub(in crate::kernel) fn register_pointer_read_definition(
        &self,
        value: &Pointer,
        memory: &crate::kernel::SharedCMemory,
        address: &Pointer,
    ) {
        let application = Pointer::loaded_value(memory, address);
        let mut reads = self.logical_reads.lock().expect("logical pointer reads");
        if let Some(existing) = reads.definitions.get(value) {
            assert_eq!(
                &existing.0, &application,
                "conflicting logical pointer definition"
            );
            return;
        }
        if let PointerOffsetTerm::Int32Scaled {
            value: atom,
            byte_width,
        } = &value.offset
            && let Bitvector32Term::Variable(variable) = atom.as_ref()
        {
            reads
                .offset_definitions
                .insert((value.block.clone(), *variable, *byte_width), value.clone());
            let offset_key = (*variable, *byte_width);
            let offset_value = match reads.offset_read_values.get(&offset_key) {
                None => Some(value.clone()),
                Some(Some(existing))
                    if reads
                        .definitions
                        .get(existing)
                        .is_some_and(|(definition, _)| definition == &application) =>
                {
                    Some(existing.clone())
                }
                _ => None,
            };
            reads.offset_read_values.insert(offset_key, offset_value);
        }
        reads.definitions = reads
            .definitions
            .with_inserted(value.clone(), (application, address.clone()));
        reads.generation =
            NEXT_LOGICAL_READ_GENERATION.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }

    /// The exact definition retained by a typed pointer-read producer.
    /// A displaced read application is not the value of its original cell.
    pub(in crate::kernel) fn pointer_read_term(&self, value: &Pointer) -> Option<Bitvector32Term> {
        let application = if value.as_loaded_value().is_some() {
            value.clone()
        } else {
            self.logical_reads
                .lock()
                .expect("logical pointer reads")
                .definitions
                .get(value)?
                .0
                .clone()
        };
        let load = application.as_loaded_value()?;
        if load.displacement != PointerOffsetTerm::Constant(0) {
            return None;
        }
        Some(Bitvector32Term::MemoryLoad(
            load.defining_memory,
            Box::new(load.defining_address),
            LoadKind::Pointer,
        ))
    }

    fn pointer_read_pair(
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> Option<PointerReadPair> {
        let endpoint = |term: &Bitvector32Term| match term {
            Bitvector32Term::MemoryLoad(memory, address, LoadKind::Pointer) => {
                Some((memory.arena_id(), address.as_ref().clone()))
            }
            _ => None,
        };
        let left = endpoint(left)?;
        let right = endpoint(right)?;
        Some(if left <= right {
            (left, right)
        } else {
            (right, left)
        })
    }

    pub(in crate::kernel) fn add_supported_pointer_read_equality(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        proof: super::memory_provenance::CheckedLoadEquality,
        supports: Vec<Proposition>,
    ) {
        let Some(pair) = Self::pointer_read_pair(left, right) else {
            return;
        };
        let mut state = self.state.lock().expect("equality graph");
        if state.supported_read_equalities.contains_key(&pair) {
            return;
        }
        state.supported_read_equalities.insert(
            pair.clone(),
            SupportedPointerReadEquality {
                proof: std::sync::Arc::new(proof),
                supports: supports.into(),
            },
        );
        if pair.0.0 < pair.1.0 && pair.0.1 == pair.1.1 {
            let older = match (left, right) {
                (Bitvector32Term::MemoryLoad(memory, _, _), _) if memory.arena_id() == pair.0.0 => {
                    left
                }
                _ => right,
            };
            if state
                .supported_read_sources
                .get(&pair.1)
                .is_none_or(|held| {
                    matches!(held, Bitvector32Term::MemoryLoad(memory, _, _)
                    if pair.0.0 < memory.arena_id())
                })
            {
                state.supported_read_sources.insert(pair.1, older.clone());
            }
        }
        state.checked_read_generation =
            NEXT_LOGICAL_READ_GENERATION.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }

    /// Select only the producer-retained older read of this exact cell.
    /// Consumers must check its supported pair in the live fact context.
    pub(in crate::kernel) fn supported_pointer_read_source(
        &self,
        pointer: &Pointer,
    ) -> Option<Pointer> {
        let Bitvector32Term::MemoryLoad(memory, address, LoadKind::Pointer) =
            self.pointer_read_term(pointer)?
        else {
            return None;
        };
        let state = self.state.lock().expect("equality graph");
        let Bitvector32Term::MemoryLoad(memory, address, LoadKind::Pointer) = state
            .supported_read_sources
            .get(&(memory.arena_id(), *address))?
        else {
            return None;
        };
        Some(Pointer::loaded_value(memory, address))
    }

    pub(in crate::kernel) fn supported_pointer_read_equality(
        &self,
        left: &Pointer,
        right: &Pointer,
    ) -> Option<SupportedPointerReadEquality> {
        let pair = Self::pointer_read_pair(
            &self.pointer_read_term(left)?,
            &self.pointer_read_term(right)?,
        )?;
        crate::instrumentation::record_deterministic_work(1);
        self.state
            .lock()
            .expect("equality graph")
            .supported_read_equalities
            .get(&pair)
            .cloned()
    }

    /// Whether this graph reads the thread's current logical-read table: a
    /// session restore or clear installs a fresh table, which a graph built
    /// before it does not see.
    pub(in crate::kernel) fn reads_current_logical_reads(&self) -> bool {
        LOGICAL_POINTER_READS
            .with(|reads| std::sync::Arc::ptr_eq(&reads.borrow(), &self.logical_reads))
    }

    pub(in crate::kernel) fn logical_read_generation(&self) -> u64 {
        let definitions = self
            .logical_reads
            .lock()
            .expect("logical pointer reads")
            .generation;
        let checked = self
            .state
            .lock()
            .expect("equality graph")
            .checked_read_generation;
        definitions.max(checked)
    }

    /// Admit an equality checked by a read producer into this branch's graph.
    /// Register definitions before closing it, so all consumers see the same
    /// congruence consequences. Memos made before a new union are invalidated.
    pub(in crate::kernel) fn add_checked_read_equality(&self, left: &Pointer, right: &Pointer) {
        let mut state = self.state.lock().expect("equality graph");
        self.register_logical_read_values(&mut state, [left, right]);
        state.register_blocks([left.block.clone(), right.block.clone()]);
        let left_address = state.register_pointer_address(left);
        let right_address = state.register_pointer_address(right);
        let address_changed = state
            .terms
            .add_address_equality(left_address, right_address);
        if state.close(vec![(left.clone(), right.clone())]) || address_changed {
            state.remember_input(inputs::Input::CheckedRead(left.clone(), right.clone()));
            state.checked_read_generation =
                NEXT_LOGICAL_READ_GENERATION.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
    }

    fn register_logical_read_values<'a>(
        &self,
        state: &mut EqualityGraphState,
        values: impl IntoIterator<Item = &'a Pointer>,
    ) {
        let reads = self.logical_reads.lock().expect("logical pointer reads");
        if reads.definitions.is_empty() {
            return;
        }
        let mut pending: Vec<_> = values.into_iter().cloned().collect();
        let mut definitions = Vec::new();
        while let Some(value) = pending.pop() {
            if state.logical_values.contains(&value) {
                continue;
            }
            let Some((application, address)) = reads.definitions.get(&value) else {
                if matches!(value.offset, PointerOffsetTerm::Add(..)) {
                    if state.logical_query_dependencies.get(&value) == Some(&reads.generation) {
                        continue;
                    }
                    state
                        .logical_query_dependencies
                        .insert(value.clone(), reads.generation);
                }
                // Register only producer-retained dependencies of the selected
                // expression. The lookup identifies an original definition;
                // it does not assert that arbitrary scaled arithmetic is a
                // pointer load, nor manufacture a shifted equality premise.
                if matches!(value.block, PointerBlock::Symbolic(_))
                    && value.offset != PointerOffsetTerm::Constant(0)
                {
                    let base = Pointer {
                        block: value.block.clone(),
                        offset: PointerOffsetTerm::Constant(0),
                    };
                    if reads.definitions.contains_key(&base) {
                        pending.push(base);
                    }
                }
                let mut offsets = vec![&value.offset];
                while let Some(offset) = offsets.pop() {
                    crate::instrumentation::record_deterministic_work(1);
                    match offset {
                        PointerOffsetTerm::Add(left, right) => {
                            offsets.push(right);
                            offsets.push(left);
                        }
                        PointerOffsetTerm::Int32Scaled {
                            value: atom,
                            byte_width,
                        } => {
                            if let Bitvector32Term::Variable(variable) = atom.as_ref()
                                && let Some(definition) = reads.offset_definitions.get(&(
                                    value.block.clone(),
                                    *variable,
                                    *byte_width,
                                ))
                            {
                                pending.push(definition.clone());
                            }
                        }
                        _ => {}
                    }
                }
                continue;
            };
            state.logical_values = state.logical_values.with_value(value.clone());
            // A nested load may use a previously constructed logical pointer
            // as its source address. Register only that explicit dependency.
            pending.push(address.clone());
            if value != *application {
                definitions.push((value, application.clone()));
            }
            // Canonical projection is unconditional producer metadata. An
            // exact registry lookup connects the application to its original
            // snapshot without searching history or inspecting other reads.
            if let Some(load) = application.as_loaded_value()
                && let Some(source) = crate::kernel::prelude::canonical_load_projection_source(
                    &load.defining_memory,
                    address,
                )
            {
                definitions.push((application.clone(), Pointer::loaded_value(&source, address)));
            }
            crate::instrumentation::record_deterministic_work(1);
        }
        drop(reads);
        for (value, application) in &definitions {
            state.register_blocks([value.block.clone(), application.block.clone()]);
        }
        for (value, application) in &definitions {
            let value = state.register_pointer_address(value);
            let application = state.register_pointer_address(application);
            state.terms.add_address_equality(value, application);
        }
        state.close(definitions);
    }

    /// Merges added after `ancestor`, oldest first. `None` means the graphs
    /// do not share a persistent merge prefix (for example, after restricting
    /// premises); a class-keyed consumer must not reuse that ancestor index.
    pub(in crate::kernel) fn pointer_merges_since(
        &self,
        ancestor: &Self,
    ) -> Option<Vec<PointerClassMerge>> {
        let (origin, mut cursor) = {
            let state = self.state.lock().expect("equality graph");
            (state.merge_origin.clone(), state.merge_history.clone())
        };
        let (previous_origin, previous) = {
            let state = ancestor.state.lock().expect("equality graph");
            (state.merge_origin.clone(), state.merge_history.clone())
        };
        if !std::sync::Arc::ptr_eq(&origin, &previous_origin) {
            return None;
        }
        let previous_depth = previous.as_ref().map_or(0, |node| node.depth);
        let mut merges = Vec::new();
        while !match (&cursor, &previous) {
            (None, None) => true,
            (Some(current), Some(previous)) => std::sync::Arc::ptr_eq(current, previous),
            _ => false,
        } {
            let merge = cursor.as_ref()?;
            // A sibling or newer checkpoint cannot be this prefix. Stop at
            // its depth instead of walking the shared history to the root.
            if merge.depth <= previous_depth {
                return None;
            }
            crate::instrumentation::record_deterministic_work(1);
            merges.push(merge.merge.clone());
            cursor = merge.parent.clone();
        }
        merges.reverse();
        Some(merges)
    }

    /// Retain an explicit alignment premise on its typed address class. Only
    /// power-of-two alignments enter; merging keeps the strongest source in
    /// constant work and never infers alignment from a pointee type.
    pub(in crate::kernel) fn register_alignment(&self, pointer: &Pointer, alignment: u64) {
        if !alignment.is_power_of_two() {
            return;
        }
        self.address_class(pointer);
        let mut state = self.state.lock().expect("equality graph");
        let id = state.register_pointer_address(pointer);
        state.terms.retain_alignment(id, alignment, pointer);
    }

    pub(in crate::kernel) fn alignment_witness(&self, pointer: &Pointer) -> Option<(u64, Pointer)> {
        self.address_class(pointer)?;
        let mut state = self.state.lock().expect("equality graph");
        let id = state.register_pointer_address(pointer);
        state.terms.alignment_witness(id)
    }

    /// Typed address applications share the graph's offset closure. This is
    /// trusted index registration, not an additional premise or a new pointer
    /// representation. Only registered addresses are propagated by merges.
    pub(in crate::kernel) fn address_class(&self, pointer: &Pointer) -> Option<u64> {
        let mut state = self.state.lock().expect("equality graph");
        // Class lookup and equality must see the same producer definitions.
        // Register only this term's retained dependencies; never recover them
        // by scanning premises, resources, or other logical reads.
        self.register_logical_read_values(&mut state, [pointer]);
        state.register_blocks([pointer.block.clone()]);
        // Keep one stable raw application for this explicit address. Its
        // checked affine projection joins the same class; later coordinate
        // changes must not strand a resource payload on an older projection.
        let id = state.register_pointer_address(pointer);
        Some(state.terms.class_root(id))
    }

    /// An explicit additive address already registered in this address's
    /// checked class. It selects a base, never bounds or access authority.
    pub(in crate::kernel) fn additive_address(&self, pointer: &Pointer) -> Option<Pointer> {
        let id = self.address_class(pointer)?;
        self.state
            .lock()
            .expect("equality graph")
            .terms
            .additive_address(id)
    }

    /// A typed pair of byte endpoints used only to select retained resource
    /// occurrences. Congruence follows late endpoint equalities. Equal
    /// footprints do not establish authority, bounds, or initialization.
    pub(in crate::kernel) fn footprint_class(
        &self,
        range: &crate::kernel::CMemoryRange,
    ) -> Option<u64> {
        let start = self.address_class(&range.start_pointer())?;
        let end = self.address_class(&range.end_pointer())?;
        Some(
            self.state
                .lock()
                .expect("equality graph")
                .terms
                .footprint(start, end),
        )
    }

    pub(in crate::kernel) fn address_class_root(&self, id: u64) -> u64 {
        self.state
            .lock()
            .expect("equality graph")
            .terms
            .class_root(id)
    }

    pub(in crate::kernel) fn address_merges_since(
        &self,
        ancestor: &Self,
    ) -> Option<Vec<terms::TermClassMerge>> {
        let previous = ancestor.state.lock().expect("equality graph").terms.clone();
        self.state
            .lock()
            .expect("equality graph")
            .terms
            .merges_since(&previous)
    }

    /// Read the class coordinate without registering new applications.
    pub(in crate::kernel) fn canonical_pointer(
        &self,
        pointer: &Pointer,
    ) -> Option<CanonicalPointer> {
        self.state
            .lock()
            .expect("equality graph")
            .canonical(pointer)
    }

    /// Preserve the supplied address unless its class has one concrete storage
    /// anchor. Re-expression uses the checked affine class relation, never an
    /// arbitrary representative or an alias walk. This does not establish
    /// object provenance, lifetime, bounds, ownership, or writability.
    pub(in crate::kernel) fn storage_address(&self, pointer: &Pointer) -> Pointer {
        if EqualityGraphState::is_storage_block(&pointer.block) {
            return pointer.clone();
        }
        self.address_class(pointer);
        let mut state = self.state.lock().expect("equality graph");
        let address = state.register_pointer_address(pointer);
        if let Some(mut storage) = state.terms.storage_address(address) {
            if let Some(offset) =
                AffineOffset::of(&storage.offset).and_then(|offset| offset.to_offset_term())
            {
                storage.offset = offset;
            }
            return storage;
        }
        let base = pointer.object_base();
        if base != *pointer {
            let id = state.register_pointer_address(&base);
            if let Some(storage) = state.terms.storage_address(id)
                && let Some(offset) = AffineOffset::of(&pointer.offset)
                    .and_then(|offset| offset.checked_sub(&AffineOffset::of(&base.offset)?))
                    .and_then(|delta| delta.checked_add(&AffineOffset::of(&storage.offset)?))
                    .and_then(|offset| offset.to_offset_term())
            {
                return Pointer {
                    block: storage.block,
                    offset,
                };
            }
        }
        let Some(coordinate) = state.canonical(pointer) else {
            return pointer.clone();
        };
        let Some(block) = state.storage_anchor(&coordinate.representative) else {
            return pointer.clone();
        };
        let (root, delta) = state.find(&block);
        if root != coordinate.representative {
            return pointer.clone();
        }
        coordinate
            .offset
            .checked_sub(&delta)
            .and_then(|offset| offset.to_offset_term())
            .map(|offset| Pointer { block, offset })
            .unwrap_or_else(|| pointer.clone())
    }

    /// Re-express one known address in a selected block's coordinates. This
    /// uses the trusted affine class relation, never enumerates class members.
    pub(in crate::kernel) fn pointer_in_block(
        &self,
        pointer: &Pointer,
        block: &PointerBlock,
    ) -> Option<Pointer> {
        let state = self.state.lock().expect("equality graph");
        let pointer = state.canonical(pointer)?;
        let (representative, delta) = state.find(block);
        if pointer.representative != representative {
            return None;
        }
        Some(Pointer {
            block: block.clone(),
            offset: pointer.offset.checked_sub(&delta)?.to_offset_term()?,
        })
    }

    /// Preserve a supplier's base spelling for a constant byte displacement.
    /// The trusted affine class relation answers without enumerating names;
    /// keeping the base first also preserves external-argument object tokens.
    pub(in crate::kernel) fn pointer_at_constant_base(
        &self,
        pointer: &Pointer,
        base: &Pointer,
    ) -> Option<Pointer> {
        let state = self.state.lock().expect("equality graph");
        let point = state.canonical(pointer)?;
        let origin = state.canonical(base)?;
        if point.representative != origin.representative {
            return None;
        }
        let displacement = i64::try_from(point.offset.constant_difference(&origin.offset)?).ok()?;
        Some(Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::add(
                base.offset.clone(),
                PointerOffsetTerm::Constant(displacement),
            ),
        })
    }

    /// Align the explicit address expression to a supplier's base. A term
    /// such as q + i retains i when the graph knows q = p, including when
    /// p and q are offsets within the same external-argument block. Work is
    /// bounded by the queried expression; no class members are enumerated.
    pub(in crate::kernel) fn pointer_at_base(
        &self,
        pointer: &Pointer,
        base: &Pointer,
    ) -> Option<Pointer> {
        self.pointer_at_base_with_spelling(pointer, base, true)
    }

    fn pointer_at_base_with_spelling(
        &self,
        pointer: &Pointer,
        base: &Pointer,
        allow_spelling: bool,
    ) -> Option<Pointer> {
        if self.are_equal(pointer, base) {
            return Some(base.clone());
        }
        if let PointerOffsetTerm::Add(left, right) = &pointer.offset {
            for (part, rest) in [(left, right), (right, left)] {
                let part = Pointer {
                    block: pointer.block.clone(),
                    offset: part.as_ref().clone(),
                };
                if let Some(aligned) =
                    self.pointer_at_base_with_spelling(&part, base, allow_spelling)
                {
                    // Only a graph-checked base replacement or block relation
                    // changes coordinates. Adding the original rest preserves
                    // the exact byte displacement and its no-wrap obligations.
                    if aligned.offset == base.offset {
                        return Some(Pointer {
                            block: aligned.block,
                            offset: PointerOffsetTerm::add(aligned.offset, rest.as_ref().clone()),
                        });
                    }
                }
            }
            // Keep an explicit additive query in its original coordinates when
            // neither operand is the supplier base. Reassociating a shifted
            // range here would hide the source index from its checked bounds.
            return self.pointer_in_block(pointer, &base.block);
        }
        // A captured interior pointer has no additive spine of its own.
        // Its class's retained producer expression carries that spine without
        // recovering aliases from ambient premises or flattening read tokens.
        // Expand at most one retained spelling per path: a zero displacement
        // may equate an additive expression with its own base.
        if allow_spelling
            && let Some(spelling) = self.additive_address(pointer)
            && let Some(aligned) = self.pointer_at_base_with_spelling(&spelling, base, false)
        {
            return Some(aligned);
        }
        let state = self.state.lock().expect("equality graph");
        let point = state.canonical(pointer)?;
        let origin = state.canonical(base)?;
        if point.representative != origin.representative {
            return None;
        }
        // A captured pointer may have no additive spine. Cancel the trusted
        // coordinates and retain the supplier base instead of flattening it
        // into unrelated opaque pointer-read tokens in the containing block.
        let displacement = point.offset.checked_sub(&origin.offset)?.to_offset_term()?;
        Some(Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::add(base.offset.clone(), displacement),
        })
    }

    /// The initial pairing boundary applies this graph's merge deltas once.
    /// Successors use `pointer_merges_since`, sharing the persistent prefix.
    pub(in crate::kernel) fn pointer_merges(&self) -> Vec<PointerClassMerge> {
        let state = self.state.lock().expect("equality graph");
        let mut cursor = state.merge_history.as_ref();
        let mut merges = Vec::new();
        while let Some(node) = cursor {
            crate::instrumentation::record_deterministic_work(1);
            merges.push(node.merge.clone());
            cursor = node.parent.as_ref();
        }
        merges.reverse();
        merges
    }

    /// Whether term classes have established any nontrivial equivalence.
    /// Callers can avoid interning unrelated query terms in an empty graph.
    pub(in crate::kernel) fn has_term_equivalences(&self) -> bool {
        self.state
            .lock()
            .expect("equality graph")
            .terms
            .has_equivalences()
    }

    /// Whether registered addresses in this affine block class are fully
    /// described by affine coordinates. A false answer means unknown coverage,
    /// not disequality. Metadata follows term dependencies and pointer relabels;
    /// unrelated scalar classes do not disable the query's interval fragment.
    pub(in crate::kernel) fn affine_addresses_complete(&self, block: &PointerBlock) -> bool {
        let state = self.state.lock().expect("equality graph");
        let (block, _) = state.find(block);
        state.terms.affine_addresses_complete(&block)
    }

    /// Query the maintained closure, registering supported load applications
    /// on demand. A false answer means equality is not established here,
    /// not that the operands are unequal. No frame or heuristic search runs.
    pub(in crate::kernel) fn are_equal(&self, left: &Pointer, right: &Pointer) -> bool {
        if left == right {
            return true;
        }
        let mut state = self.state.lock().expect("equality graph");
        self.register_logical_read_values(&mut state, [left, right]);
        // At an unclassed ordinary base, equality is just offset equality.
        // Avoid registering pointer/address nodes for unrelated field checks.
        // Load blocks still need application registration and congruence.
        let is_load_block = match &left.block {
            PointerBlock::LoadedPointer(_) => true,
            PointerBlock::Symbolic(variable) => crate::kernel::is_load_variable(variable),
            _ => false,
        };
        if left.block == right.block
            && !is_load_block
            && !state.parent.contains_key(&left.block)
            && !state.members.contains_key(&left.block)
        {
            // With no offset merges, known equality is only reflexivity
            // (handled above). Explicit offset normalization remains available
            // through `are_offsets_equal`; ordinary unrelated field checks
            // must not pay for it before their separation check.
            return state.terms.has_equivalences()
                && state.terms.are_equal(&left.offset, &right.offset);
        }
        state.register_blocks([left.block.clone(), right.block.clone()]);
        // Different classes cannot meet by offset normalization. In
        // particular, do not traverse an unrelated allocation's offset just
        // to discover that its block has no equality with the query's block.
        let (left_rep, left_delta) = state.find(&left.block);
        let (right_rep, right_delta) = state.find(&right.block);
        if left_rep != right_rep {
            return false;
        }
        let affine_equal = match (
            AffineOffset::of(&left.offset).and_then(|offset| left_delta.checked_add(&offset)),
            AffineOffset::of(&right.offset).and_then(|offset| right_delta.checked_add(&offset)),
        ) {
            (Some(left), Some(right)) => left == right,
            _ => false,
        };
        if affine_equal {
            return true;
        }
        if state.offsets_equal_in_class(left, right, &left_delta, &right_delta) {
            return true;
        }
        if !state.terms.has_equivalences() {
            return false;
        }
        // The same address applications carry exact pointer premises and
        // offset congruence. Preserve the raw applications even when a block
        // displacement has no offset spelling (for example, -offset_variable).
        let left = state.register_pointer_address(left);
        let right = state.register_pointer_address(right);
        state.terms.class_root(left) == state.terms.class_root(right)
    }

    /// Ask whether two pointer-typed reads in the same defining snapshot
    /// must have the same value. The application nodes are query terms: this
    /// does not change the representation of either loaded `CValue`.
    /// Callers must supply the addresses and snapshot of actual pointer reads;
    /// decoding a storage-relative pointer value as a load is ambiguous with
    /// ordinary indexed pointer arithmetic.
    #[allow(dead_code, reason = "live comparisons use filed graph bridges")]
    pub(in crate::kernel) fn are_pointer_loads_equal(
        &self,
        memory: &crate::kernel::SharedCMemory,
        left_address: &Pointer,
        right_address: &Pointer,
    ) -> bool {
        self.are_equal(
            &Pointer::loaded_value(memory, left_address),
            &Pointer::loaded_value(memory, right_address),
        )
    }

    /// Query explicit offset equality, addition and int32 scaling congruence.
    /// This fragment does not solve arithmetic or perform cancellation.
    pub(in crate::kernel) fn are_offsets_equal(
        &self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
    ) -> bool {
        if left == right {
            return true;
        }
        // Offset addition is exact byte arithmetic. Its affine form catches
        // reordering and regrouping without a premise or term-class merge.
        if let (Some(left), Some(right)) = (AffineOffset::of(left), AffineOffset::of(right))
            && left == right
        {
            return true;
        }
        // Offset goals can be projections of typed pointer reads. Retain
        // only producer-registered definitions of the selected operands;
        // equal offsets alone never establish equality of pointer blocks.
        let mut state = self.state.lock().expect("equality graph");
        let reads = self.logical_reads.lock().expect("logical pointer reads");
        let mut pending = Vec::new();
        for offset in [left, right] {
            if state.logical_offset_dependencies.get(offset) != Some(&reads.generation) {
                state
                    .logical_offset_dependencies
                    .insert(offset.clone(), reads.generation);
                pending.push(offset);
            }
        }
        let mut values = Vec::new();
        while let Some(offset) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match offset {
                PointerOffsetTerm::Add(left, right) => {
                    pending.push(left);
                    pending.push(right);
                }
                PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                    if let Bitvector32Term::Variable(variable) = value.as_ref()
                        && let Some(Some(value)) =
                            reads.offset_read_values.get(&(*variable, *byte_width))
                    {
                        values.push(value.clone());
                    }
                }
                _ => {}
            }
        }
        drop(reads);
        self.register_logical_read_values(&mut state, values.iter());
        state.terms.are_equal(left, right)
    }

    /// Query int32 equality, addition and registered same-snapshot load congruence.
    /// A false answer is unknown. Other scalar operations remain opaque.
    pub(in crate::kernel) fn are_int32_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        if left == right {
            return true;
        }
        let mut state = self.state.lock().expect("equality graph");
        self.register_int32_operands(&mut state, left, right);
        let equal = state.terms.are_int32_equal(left, right);
        state.close(Vec::new());
        equal
    }

    fn register_int32_operands(
        &self,
        state: &mut EqualityGraphState,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) {
        // Existing opaque scalar queries need no traversal or registration.
        // Only these constructors can contain new pointer-valued arguments.
        let contains_arguments = |term: &Bitvector32Term| {
            matches!(
                term,
                Bitvector32Term::ClickFunctionApplication { .. }
                    | Bitvector32Term::Add(..)
                    | Bitvector32Term::UnsignedDivide(..)
                    | Bitvector32Term::UnsignedRemainder(..)
                    | Bitvector32Term::BitwiseXor(..)
            )
        };
        if contains_arguments(left) || contains_arguments(right) {
            self.register_machine_operands(state, left, right);
        }
    }

    /// Prepare only the addresses used by the selected machine expressions.
    /// Logical read definitions and affine aliases use the same address classes
    /// as pointer queries; no history search or ambient-fact scan is needed.
    fn register_machine_operands(
        &self,
        state: &mut EqualityGraphState,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) {
        let mut pending = vec![left, right];
        let mut pointers = Vec::new();
        while let Some(term) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if let Bitvector32Term::ClickFunctionApplication { arguments, .. } = term {
                for argument in arguments {
                    match argument {
                        PureFunctionArgument::Value(value)
                        | PureFunctionArgument::ArrayRef { pointer: value, .. } => match value {
                            CValue::Pointer(pointer) => pointers.push(pointer.pointer().clone()),
                            CValue::Int32(t) | CValue::UInt32(t) | CValue::UInt64(t) => {
                                pending.push(t)
                            }
                            _ => {}
                        },
                        _ => {}
                    }
                }
            } else if let Bitvector32Term::Add(a, b)
            | Bitvector32Term::UnsignedDivide(a, b)
            | Bitvector32Term::UnsignedRemainder(a, b)
            | Bitvector32Term::BitwiseXor(a, b) = term
            {
                pending.extend([a.as_ref(), b.as_ref()]);
            } else if let Some((_, a, b)) = terms::uint64_binary(term) {
                pending.extend([a, b]);
            } else if let Some((_, pointer)) = terms::uint64_read(term) {
                pointers.push(pointer);
            } else if let Bitvector32Term::PointerAddress(pointer) = term {
                pointers.push(pointer.as_ref().clone());
            }
        }
        if pointers.is_empty() {
            return;
        }
        self.register_logical_read_values(state, pointers.iter());
        state.register_blocks(pointers.iter().map(|pointer| pointer.block.clone()));
        for pointer in pointers {
            state.register_pointer_address(&pointer);
        }
        state.close(Vec::new());
    }

    pub(in crate::kernel) fn are_uint64_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        if left == right {
            return true;
        }
        let left = crate::kernel::canonical_term(left);
        let right = crate::kernel::canonical_term(right);
        let mut state = self.state.lock().expect("equality graph");
        self.register_machine_operands(&mut state, &left, &right);
        state.terms.are_uint64_equal(&left, &right)
    }

    pub(in crate::kernel) fn add_uint64_equality(
        &mut self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let left = crate::kernel::canonical_term(left);
        let right = crate::kernel::canonical_term(right);
        let mut state = self.state.lock().expect("equality graph");
        self.register_machine_operands(&mut state, &left, &right);
        let changed = state.terms.add_uint64_equality(&left, &right);
        state.close(Vec::new());
        if changed {
            state.remember_input(inputs::Input::UInt64(left.clone(), right.clone()));
        }
        changed
    }

    /// Bounds retained on any checked equivalent int32 value. Registration
    /// visits only this term's dependencies; lookup never enumerates a class.
    pub(in crate::kernel) fn signed_int32_interval(
        &self,
        term: &Bitvector32Term,
    ) -> Option<(i64, i64)> {
        let mut state = self.state.lock().expect("equality graph");
        let node = state.terms.int32_class(term);
        state.close(Vec::new());
        state.terms.signed_int32_interval(node)
    }

    /// Admit an already established int32 equality in this proof context.
    pub(in crate::kernel) fn add_int32_equality(
        &mut self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let mut state = self.state.lock().expect("equality graph");
        self.register_int32_operands(&mut state, left, right);
        let changed = state.terms.add_int32_equality(left, right);
        state.close(Vec::new());
        if changed {
            state.remember_input(inputs::Input::Int32(left.clone(), right.clone()));
        }
        changed
    }

    fn prepare_condition(&self, state: &mut EqualityGraphState, condition: &ConditionTerm) {
        match condition {
            ConditionTerm::PointerEqual(a, b) => {
                self.register_logical_read_values(state, [a.as_ref(), b.as_ref()]);
                state.register_blocks([a.block.clone(), b.block.clone()]);
                state.register_pointer_address(a);
                state.register_pointer_address(b);
                state.close(Vec::new());
            }
            _ => {
                if let Some((a, b)) = condition.bitvector_sides_for_congruence() {
                    self.register_machine_operands(state, a, b);
                }
            }
        }
    }

    pub(in crate::kernel) fn add_condition(
        &mut self,
        condition: &ConditionTerm,
        value: bool,
    ) -> bool {
        // True equations already enter through the typed equality inputs.
        // They need no second truth node or retained support index.
        if value
            && matches!(
                condition,
                ConditionTerm::Bitvector32Equal(..)
                    | ConditionTerm::Bitvector64Equal(..)
                    | ConditionTerm::PointerEqual(..)
                    | ConditionTerm::PointerOffsetEqual(..)
            )
        {
            return false;
        }
        let mut state = self.state.lock().expect("equality graph");
        self.prepare_condition(&mut state, condition);
        let supported = state.terms.admit_condition(condition, value);
        state.close(Vec::new());
        // Predicate truth is scoped state, not a value equality. Resource
        // indexes apply only admitted equations; unrelated comparisons must
        // not invalidate their checkpoints or lengthen their history walks.
        supported
    }

    pub(in crate::kernel) fn knows_condition(
        &self,
        condition: &ConditionTerm,
        value: bool,
    ) -> bool {
        // True equations are represented directly by classes, never truth
        // nodes. A miss must not register an unrelated condition application.
        if value {
            match condition {
                ConditionTerm::Bitvector32Equal(a, b) => return self.are_int32_equal(a, b),
                ConditionTerm::Bitvector64Equal(a, b) => return self.are_uint64_equal(a, b),
                ConditionTerm::PointerEqual(a, b) => return self.are_equal(a, b),
                ConditionTerm::PointerOffsetEqual(a, b) => return self.are_offsets_equal(a, b),
                _ => {}
            }
        }
        let mut state = self.state.lock().expect("equality graph");
        if !state.terms.may_know_condition(condition, value) {
            return false;
        }
        self.prepare_condition(&mut state, condition);
        let known = state.terms.knows_condition(condition, value);
        state.close(Vec::new());
        known
    }

    /// Admit an already established offset equality in this proof context.
    pub(in crate::kernel) fn add_offset_equality(
        &mut self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
    ) -> bool {
        let state = self.state.get_mut().expect("equality graph");
        let changed = state.terms.add_equality(left, right);
        state.close(Vec::new());
        if changed {
            state.remember_input(inputs::Input::Offset(left.clone(), right.clone()));
        }
        changed
    }

    /// Admit an equality already established in this proof context and
    /// propagate its supported congruence consequences. A same-block premise
    /// also equates its whole offsets. Returns whether any class merge
    /// occurred, not whether the supplied equality is valid.
    pub(in crate::kernel) fn add_equality(&mut self, left: &Pointer, right: &Pointer) -> bool {
        let mut state = self.state.lock().expect("equality graph");
        // A read used by a checked premise is a dependency of later queries,
        // even when those queries name only another member of its class.
        // Register these two explicit operands now; never search the ambient
        // classes for read spellings when answering a transitive query.
        self.register_logical_read_values(&mut state, [left, right]);
        state.register_blocks([left.block.clone(), right.block.clone()]);
        // The affine fragment already carries spellable base displacements.
        // Retain raw address applications only for relations whose symbolic
        // displacement cannot be expressed as a whole offset term. Without
        // these nodes, an offset-class merge cannot reach such a premise.
        let needs_raw_addresses = match (
            AffineOffset::of(&left.offset),
            AffineOffset::of(&right.offset),
        ) {
            (Some(left), Some(right)) => right.checked_sub(&left).is_some_and(|delta| {
                delta.to_offset_term().is_none()
                    || delta
                        .checked_negate()
                        .is_some_and(|reverse| reverse.to_offset_term().is_none())
            }),
            _ => true,
        };
        // External C pointers share a block. Preserve their raw addresses
        // so a transitive chain can equate two offsets in that original
        // block, independently of the affine representative's coordinates.
        let address_changed = if left.block != right.block
            && (needs_raw_addresses
                || matches!(left.block, PointerBlock::ExternalArgument)
                || matches!(right.block, PointerBlock::ExternalArgument)
                || EqualityGraphState::is_storage_block(&left.block)
                || EqualityGraphState::is_storage_block(&right.block))
        {
            let left_address = state.register_pointer_address(left);
            let right_address = state.register_pointer_address(right);
            state
                .terms
                .add_address_equality(left_address, right_address)
        } else {
            false
        };
        let offset_changed =
            left.block == right.block && state.terms.add_equality(&left.offset, &right.offset);
        let pointer_changed = state.close(vec![(left.clone(), right.clone())]);
        if EqualityGraphState::is_storage_block(&left.block)
            || EqualityGraphState::is_storage_block(&right.block)
        {
            let left_address = state.register_pointer_address(left);
            let right_address = state.register_pointer_address(right);
            state
                .terms
                .add_address_equality(left_address, right_address);
        }
        let changed = address_changed || offset_changed || pointer_changed;
        if changed {
            state.remember_input(inputs::Input::Pointer(left.clone(), right.clone()));
        }
        changed
    }
}

/// Pointer-specific compatibility queries for consumers not yet indexed by
/// equality. These enumerate spellings separately from `are_equal`.
impl EqualityGraph {
    pub(in crate::kernel) fn pointer_is_classed(&self, block: &PointerBlock) -> bool {
        let mut state = self.state.lock().expect("equality graph");
        state.register_blocks([block.clone()]);
        state.parent.contains_key(block) || state.members.contains_key(block)
    }

    /// Transitional resource consumers still enumerate spellings. This is
    /// deliberately separate from congruence lookup, which never enumerates.
    fn pointer_class_members(&self, block: &PointerBlock) -> Vec<(PointerBlock, AffineOffset)> {
        let mut state = self.state.lock().expect("equality graph");
        state.register_blocks([block.clone()]);
        let (representative, own) = state.find(block);
        let mut blocks = Vec::new();
        let mut push = |member: &PointerBlock, delta: &AffineOffset| {
            if let Some(delta) = own.checked_sub(delta) {
                blocks.push((member.clone(), delta));
            }
        };
        push(&representative, &AffineOffset::default());
        if let Some(members) = state.members.get(&representative) {
            for (member, delta) in members {
                push(member, delta);
            }
        }
        blocks
    }

    pub(in crate::kernel) fn pointer_spellings(&self, pointer: &Pointer) -> Vec<Pointer> {
        if !self.pointer_is_classed(&pointer.block) {
            return Vec::new();
        }
        let Some(offset) = AffineOffset::of(&pointer.offset) else {
            return Vec::new();
        };
        self.pointer_class_members(&pointer.block)
            .into_iter()
            .filter(|(member, _)| member != &pointer.block)
            .filter_map(|(member, delta)| {
                Some(Pointer {
                    block: member,
                    // Cancel inverse symbolic displacements before querying
                    // a cell map keyed by the address's structural spelling.
                    offset: offset.checked_add(&delta)?.to_offset_term()?,
                })
            })
            .collect()
    }
}

impl EqualityGraphState {
    fn find(&self, block: &PointerBlock) -> (PointerBlock, AffineOffset) {
        crate::instrumentation::record_deterministic_work(1);
        self.parent
            .get(block)
            .cloned()
            .unwrap_or_else(|| (block.clone(), AffineOffset::default()))
    }

    fn canonical(&self, pointer: &Pointer) -> Option<CanonicalPointer> {
        let offset = AffineOffset::of(&pointer.offset)?;
        let (representative, delta) = self.find(&pointer.block);
        Some(CanonicalPointer {
            representative,
            offset: delta.checked_add(&offset)?,
        })
    }

    fn weight(&self, block: &PointerBlock) -> usize {
        self.weights.get(block).copied().unwrap_or(1)
    }

    fn intern_offset(&mut self, offset: &AffineOffset) -> u64 {
        let mut part = OffsetPart::Constant(offset.constant);
        let mut id = self.intern_offset_part(part);
        for (atom, coefficient) in &offset.terms {
            part = OffsetPart::Term(id, atom.clone(), *coefficient);
            id = self.intern_offset_part(part);
        }
        id
    }

    fn intern_offset_part(&mut self, part: OffsetPart) -> u64 {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(id) = self.offset_parts.get(&part) {
            return *id;
        }
        let id = u64::try_from(self.offset_parts.len()).expect("affine identity capacity");
        self.offset_parts.insert(part, id);
        id
    }

    /// Register the explicit roots and their load-address dependencies once,
    /// with an iterative traversal rather than a semantic nesting limit.
    fn register_blocks(&mut self, roots: impl IntoIterator<Item = PointerBlock>) {
        let is_load = |block: &PointerBlock| match block {
            PointerBlock::LoadedPointer(_) => true,
            PointerBlock::Symbolic(variable) => crate::kernel::is_load_variable(variable),
            _ => false,
        };
        let mut pending: Vec<_> = roots.into_iter().filter(is_load).collect();
        let mut equalities = Vec::new();
        while let Some(block) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if self.loads.contains_key(&block) || self.typed_reads.contains(&block) {
                continue;
            }
            let definition = match &block {
                PointerBlock::LoadedPointer(identity) => {
                    crate::kernel::eval::registered_pointer_load(*identity).map(
                        |(memory, address)| (memory, address, crate::kernel::LoadKind::Pointer),
                    )
                }
                PointerBlock::Symbolic(variable)
                    if crate::kernel::is_load_variable(variable)
                        && crate::kernel::registered_load_bytes_for_variable(variable)
                            == Some(8) =>
                {
                    crate::kernel::registered_load_for_variable(variable).and_then(
                        |(memory, address)| {
                            crate::kernel::registered_load_kind_for_variable(variable)
                                .map(|kind| (memory, address, kind))
                        },
                    )
                }
                _ => None,
            };
            let Some((memory, address, kind)) = definition else {
                continue;
            };
            if matches!(block, PointerBlock::LoadedPointer(_)) {
                self.typed_reads = self.typed_reads.with_value(block.clone());
                let address_term = self.register_pointer_address(&address);
                let value_term = self.register_pointer_address(&Pointer {
                    block: block.clone(),
                    offset: PointerOffsetTerm::Constant(0),
                });
                self.terms.pointer_read(
                    memory.read_identity(),
                    address_term,
                    kind,
                    value_term,
                    block.clone(),
                );
                if is_load(&address.block) {
                    pending.push(address.block);
                }
                continue;
            }
            let Some(address_offset) = AffineOffset::of(&address.offset) else {
                continue;
            };
            self.loads.insert(
                block.clone(),
                LoadApplication {
                    memory: memory.read_identity(),
                    address_block: address.block.clone(),
                    address_offset,
                    kind,
                },
            );
            let users = self.uses.get(&address.block).cloned().unwrap_or_default();
            self.uses
                .insert(address.block.clone(), users.with_value(block.clone()));
            let (representative, _) = self.find(&address.block);
            self.weights
                .insert(representative.clone(), self.weight(&representative) + 1);
            self.reindex_load(&block, &mut equalities);
            if is_load(&address.block) {
                pending.push(address.block);
            }
        }
        self.close(equalities);
    }

    fn reindex_load(&mut self, block: &PointerBlock, equalities: &mut Vec<(Pointer, Pointer)>) {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(old) = self.load_signatures.get(block).cloned() {
            if self.signatures.get(&old) == Some(block) {
                self.signatures.remove(&old);
            }
            self.load_signatures.remove(block);
        }
        let load = self.loads.get(block).expect("registered load").clone();
        let (address_block, delta) = self.find(&load.address_block);
        let Some(offset) = delta.checked_add(&load.address_offset) else {
            return;
        };
        let signature = LoadSignature {
            memory: load.memory,
            address_block,
            address_offset: self.intern_offset(&offset),
            kind: load.kind,
        };
        if let Some(other) = self.signatures.get(&signature) {
            if other != block {
                equalities.push((
                    Pointer {
                        block: block.clone(),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                    Pointer {
                        block: other.clone(),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                ));
            }
        } else {
            self.signatures.insert(signature.clone(), block.clone());
        }
        self.load_signatures.insert(block.clone(), signature);
    }

    /// Check offset-class equality at a known common affine block base.
    /// This queries selected terms only; no cancellation or class walk runs.
    fn offsets_equal_in_class(
        &mut self,
        left: &Pointer,
        right: &Pointer,
        left_delta: &AffineOffset,
        right_delta: &AffineOffset,
    ) -> bool {
        // A congruence merge can equate two loads after each was already
        // bridged to a storage-relative C value. Their blocks then share a
        // representative but carry different symbolic displacements. The
        // exact offset fragment retains that same-class equality.
        if let (Some(left), Some(right)) = (
            AffineOffset::of(&left.offset)
                .and_then(|offset| left_delta.checked_add(&offset))
                .and_then(|offset| offset.to_offset_term()),
            AffineOffset::of(&right.offset)
                .and_then(|offset| right_delta.checked_add(&offset))
                .and_then(|offset| offset.to_offset_term()),
        ) && self.terms.are_equal(&left, &right)
        {
            return true;
        }
        // An exact offset equality can cross blocks only after accounting
        // for their known base displacement. The equal-base case uses the
        // whole offsets directly; a constant displacement can be added to
        // either side. Query both spellings so the answer is symmetric even
        // when only one translated equality was explicitly stated.
        if (left.block == right.block
            || (left_delta == right_delta && self.terms.has_equivalences()))
            && self.terms.are_equal(&left.offset, &right.offset)
        {
            return true;
        }
        if left.block == right.block
            || !self.terms.has_equivalences()
            || !left_delta.terms.is_empty()
            || !right_delta.terms.is_empty()
        {
            return false;
        }
        let Some(displacement) = left_delta.constant.checked_sub(right_delta.constant) else {
            return false;
        };
        let Ok(displacement) = i64::try_from(displacement) else {
            return false;
        };
        let Some(reverse) = displacement.checked_neg() else {
            return false;
        };
        let shifted_left = PointerOffsetTerm::Add(
            Box::new(left.offset.clone()),
            Box::new(PointerOffsetTerm::Constant(displacement)),
        );
        let shifted_right = PointerOffsetTerm::Add(
            Box::new(right.offset.clone()),
            Box::new(PointerOffsetTerm::Constant(reverse)),
        );
        self.terms.are_equal(&shifted_left, &right.offset)
            || self.terms.are_equal(&left.offset, &shifted_right)
    }

    /// Register one address and its affine class coordinate, when spellable.
    /// Exact pointer premises can always refer to the raw address application.
    /// Work is in the selected offset and new parent uses, never class members.
    fn register_pointer_address(&mut self, pointer: &Pointer) -> u64 {
        let (representative, delta) = self.find(&pointer.block);
        let (raw, new) = self
            .terms
            .address(pointer.block.clone(), pointer.offset.clone());
        if Self::is_storage_block(&pointer.block) {
            self.terms.retain_storage_address(raw, pointer);
        }
        self.terms.retain_additive_address(raw, pointer);
        if new {
            self.weights
                .insert(representative.clone(), self.weight(&representative) + 1);
        }
        if representative != pointer.block
            && let Some(delta) = delta.to_offset_term()
        {
            let translated =
                PointerOffsetTerm::Add(Box::new(pointer.offset.clone()), Box::new(delta));
            let (canonical, new) = self.terms.address(representative.clone(), translated);
            if new {
                self.weights
                    .insert(representative.clone(), self.weight(&representative) + 1);
            }
            self.terms.add_address_equality(raw, canonical);
        }
        raw
    }

    fn close(&mut self, mut equalities: Vec<(Pointer, Pointer)>) -> bool {
        let mut changed = false;
        loop {
            equalities.extend(
                self.terms
                    .take_read_merges()
                    .into_iter()
                    .map(|(left, right)| {
                        (
                            Pointer {
                                block: left,
                                offset: PointerOffsetTerm::Constant(0),
                            },
                            Pointer {
                                block: right,
                                offset: PointerOffsetTerm::Constant(0),
                            },
                        )
                    }),
            );
            let Some((left, right)) = equalities.pop() else {
                break;
            };
            crate::instrumentation::record_deterministic_work(1);
            let (Some(left), Some(right)) = (self.canonical(&left), self.canonical(&right)) else {
                continue;
            };
            if left.representative == right.representative {
                if let (Some(left), Some(right)) =
                    (left.offset.to_offset_term(), right.offset.to_offset_term())
                {
                    changed |= self.terms.add_equality(&left, &right);
                }
                continue;
            }
            let Some(left_from_right) = right.offset.checked_sub(&left.offset) else {
                continue;
            };
            let (moved, kept, delta) =
                if self.weight(&left.representative) <= self.weight(&right.representative) {
                    (left.representative, right.representative, left_from_right)
                } else {
                    let Some(delta) = left_from_right.checked_negate() else {
                        continue;
                    };
                    (right.representative, left.representative, delta)
                };
            changed |= self.relabel(moved, kept, delta, &mut equalities);
        }
        changed
    }

    fn is_storage_block(block: &PointerBlock) -> bool {
        matches!(
            block,
            PointerBlock::Heap(_) | PointerBlock::Temporary(_) | PointerBlock::StringLiteral { .. }
        ) || matches!(block, PointerBlock::Concrete(name) if name != "null")
    }

    fn storage_anchor(&self, root: &PointerBlock) -> Option<PointerBlock> {
        self.storage_anchors
            .get(root)
            .cloned()
            .unwrap_or_else(|| Self::is_storage_block(root).then(|| root.clone()))
    }

    fn relabel(
        &mut self,
        moved: PointerBlock,
        kept: PointerBlock,
        moved_from_kept: AffineOffset,
        equalities: &mut Vec<(Pointer, Pointer)>,
    ) -> bool {
        let anchors = match (self.storage_anchor(&moved), self.storage_anchor(&kept)) {
            (Some(left), Some(right)) if left == right => Some(left),
            (Some(_), Some(_)) => None,
            (left, right) => {
                // An existing None is ambiguous, not an empty anchor set.
                if self
                    .storage_anchors
                    .get(&moved)
                    .is_some_and(Option::is_none)
                    || self.storage_anchors.get(&kept).is_some_and(Option::is_none)
                {
                    None
                } else {
                    left.or(right)
                }
            }
        };
        let mut deltas = vec![(moved.clone(), moved_from_kept.clone())];
        if let Some(members) = self.members.get(&moved) {
            for (member, delta) in members {
                let Some(delta) = delta.checked_add(&moved_from_kept) else {
                    return false;
                };
                deltas.push((member.clone(), delta));
            }
        }
        // Store a summary only for classes containing concrete evidence.
        if anchors.is_some()
            || self.storage_anchors.contains_key(&moved)
            || self.storage_anchors.contains_key(&kept)
            || Self::is_storage_block(&moved)
            || Self::is_storage_block(&kept)
        {
            self.storage_anchors.insert(kept.clone(), anchors);
        }
        self.storage_anchors.remove(&moved);
        crate::instrumentation::record_deterministic_work(deltas.len());
        let mut kept_members = self.members.get(&kept).cloned().unwrap_or_default();
        self.weights
            .insert(kept.clone(), self.weight(&moved) + self.weight(&kept));
        self.weights.remove(&moved);
        let mut affected = Vec::new();
        for (member, delta) in deltas {
            if let Some(users) = self.uses.get(&member) {
                affected.extend(users.iter().cloned());
            }
            self.parent
                .insert(member.clone(), (kept.clone(), delta.clone()));
            kept_members.insert(member, delta);
        }
        self.members.remove(&moved);
        self.members.insert(kept.clone(), kept_members);
        self.terms.shift_addresses(&moved, &kept, &moved_from_kept);
        self.merge_history = Some(std::sync::Arc::new(PointerMergeHistory {
            depth: self.merge_history.as_ref().map_or(1, |node| node.depth + 1),
            merge: PointerClassMerge {
                moved,
                kept,
                moved_from_kept,
            },
            parent: self.merge_history.clone(),
        }));
        for load in affected {
            self.reindex_load(&load, equalities);
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn symbolic(id: u64) -> PointerBlock {
        PointerBlock::Symbolic(Variable(id))
    }

    fn at(block: PointerBlock, offset: i64) -> Pointer {
        Pointer {
            block,
            offset: PointerOffsetTerm::Constant(offset),
        }
    }

    fn index(id: u64) -> Bitvector32Term {
        Bitvector32Term::Variable(Variable(id))
    }

    // Retained zero-displacement spellings may share their base's class.
    // Alignment against an unrelated supplier must not expand that cycle.
    #[test]
    fn additive_spelling_alignment_is_bounded_when_its_base_is_equal() {
        let mut graph = EqualityGraph::default();
        let base = Pointer::symbolic(Variable(999_101));
        let index = Bitvector32Term::Variable(Variable(999_102));
        let address = base.offset_by_elements(index, 4);
        assert!(graph.add_equality(&base, &address));
        let unrelated = Pointer::symbolic(Variable(999_103));
        assert!(graph.pointer_at_base(&base, &unrelated).is_none());
    }

    // Every pointer equality query registers both addresses. Repeating a
    // query reuses the registered address nodes: it neither grows the graph
    // nor renormalizes and recloses the offsets, so its work is a fraction of
    // the first query's and linear in the offsets it reinterns.
    #[test]
    fn repeated_address_queries_reuse_registered_addresses() {
        let mut costs = Vec::new();
        for size in [8u64, 32, 128] {
            let mut graph = EqualityGraph::default();
            assert!(graph.add_equality(&at(symbolic(1), 0), &at(symbolic(2), 16)));
            // An unrelated offset equality enables registered comparisons.
            graph.add_int32_equality(&index(1), &index(2));
            // Distinct indices give the sides different affine forms, so the
            // query reaches address registration, whose normal form of each
            // offset is a fresh flattened term.
            let offset = |first: u64| {
                (0..size).fold(PointerOffsetTerm::Constant(0), |sum, item| {
                    PointerOffsetTerm::Add(
                        Box::new(sum),
                        Box::new(PointerOffsetTerm::Int32Scaled {
                            value: Box::new(index(first + item)),
                            byte_width: 4,
                        }),
                    )
                })
            };
            let left = Pointer {
                block: symbolic(1),
                offset: offset(1_000),
            };
            let right = Pointer {
                block: symbolic(2),
                offset: offset(5_000),
            };
            let (first, first_work) = crate::instrumentation::measure_deterministic_work(|| {
                graph.are_equal(&left, &right)
            });
            let nodes = graph
                .state
                .lock()
                .expect("equality graph")
                .terms
                .node_count();
            let (repeated, repeated_work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    graph.are_equal(&left, &right)
                });
            assert_eq!(first, repeated);
            assert_eq!(
                graph
                    .state
                    .lock()
                    .expect("equality graph")
                    .terms
                    .node_count(),
                nodes,
                "a repeated query must not register new nodes"
            );
            // Reinterning the raw offsets is about half the first query;
            // renormalizing and reinterning both normal forms would be more.
            assert!(
                repeated_work * 5 <= first_work * 3,
                "repeated {repeated_work}, first {first_work}"
            );
            costs.push((size, repeated_work));
        }
        for pair in costs.windows(2) {
            let ((small, small_work), (large, large_work)) = (pair[0], pair[1]);
            assert!(
                large_work <= small_work * (large / small) as usize * 2,
                "{costs:?}"
            );
        }
    }

    #[test]
    fn offsets_spelled_differently_share_one_normal_form() {
        let nested = PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::Int32Scaled {
                    value: Box::new(index(7)),
                    byte_width: 4,
                }),
                Box::new(PointerOffsetTerm::Constant(4)),
            )),
            Box::new(PointerOffsetTerm::Constant(4)),
        );
        let flat = PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::Constant(8)),
            Box::new(PointerOffsetTerm::Int32Scaled {
                value: Box::new(index(7)),
                byte_width: 4,
            }),
        );
        assert_eq!(AffineOffset::of(&nested), AffineOffset::of(&flat));
        let other_index = PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::Constant(8)),
            Box::new(PointerOffsetTerm::Int32Scaled {
                value: Box::new(index(8)),
                byte_width: 4,
            }),
        );
        assert_ne!(AffineOffset::of(&flat), AffineOffset::of(&other_index));
    }

    #[test]
    fn a_constant_index_folds_with_its_sign() {
        let minus_one = PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Constant(u32::MAX)),
            byte_width: 8,
        };
        assert_eq!(
            AffineOffset::of(&minus_one),
            Some(AffineOffset::constant(-8))
        );
    }

    #[test]
    fn a_chain_and_a_displacement_are_proved_without_a_walk() {
        let mut classes = EqualityGraph::default();
        assert!(classes.add_equality(&at(symbolic(1), 0), &at(symbolic(2), 0)));
        assert!(classes.add_equality(&at(symbolic(2), 0), &at(symbolic(3), 16)));
        assert!(classes.are_equal(&at(symbolic(1), 0), &at(symbolic(3), 16)));
        assert!(classes.are_equal(&at(symbolic(1), 8), &at(symbolic(3), 24)));
        assert!(!classes.are_equal(&at(symbolic(1), 8), &at(symbolic(3), 8)));
        assert!(!classes.are_equal(&at(symbolic(1), 0), &at(symbolic(4), 0)));
    }

    #[test]
    fn class_merge_deltas_follow_only_the_persistent_branch() {
        let root = EqualityGraph::default();
        assert!(root.pointer_merges_since(&root).unwrap().is_empty());
        let mut left = root.clone();
        let mut right = root.clone();
        assert!(left.add_equality(&at(symbolic(31), 8), &at(symbolic(32), 0)));
        let first = left.clone();
        assert!(left.add_equality(&at(symbolic(32), 0), &at(symbolic(33), 4)));
        let merges = left.pointer_merges_since(&root).unwrap();
        assert_eq!(merges.len(), 2);
        for merge in &merges {
            let displaced = merge
                .moved_from_kept
                .to_offset_term()
                .expect("constant displacement has a pointer spelling");
            assert!(left.are_equal(
                &at(merge.moved.clone(), 0),
                &Pointer {
                    block: merge.kept.clone(),
                    offset: displaced,
                },
            ));
        }
        assert_eq!(left.pointer_merges_since(&first).unwrap().len(), 1);
        assert!(first.pointer_merges_since(&left).is_none());

        assert!(right.add_equality(&at(symbolic(40), 0), &at(symbolic(41), 0)));
        assert_eq!(right.pointer_merges_since(&root).unwrap().len(), 1);
        assert!(left.pointer_merges_since(&right).is_none());
        assert!(
            EqualityGraph::default()
                .pointer_merges_since(&root)
                .is_none()
        );
    }

    #[test]
    fn reading_one_class_merge_does_not_walk_the_shared_history() {
        let samples = [16_u64, 64, 256]
            .into_iter()
            .map(|size| {
                let mut graph = EqualityGraph::default();
                for block in 1..size {
                    assert!(
                        graph.add_equality(
                            &at(symbolic(50_000), 0),
                            &at(symbolic(50_000 + block), 0),
                        )
                    );
                }
                let parent = graph.clone();
                assert!(
                    graph.add_equality(&at(symbolic(50_000), 0), &at(symbolic(50_000 + size), 0),)
                );
                let mut sibling = parent.clone();
                sibling.add_equality(&at(symbolic(60_000), 0), &at(symbolic(60_001), 0));
                let (mismatch, mismatch_work) =
                    crate::instrumentation::measure_deterministic_work(|| {
                        graph.pointer_merges_since(&sibling)
                    });
                assert!(mismatch.is_none());
                assert_eq!(mismatch_work, 0, "sibling check walked the shared prefix");
                let (merges, work) = crate::instrumentation::measure_deterministic_work(|| {
                    graph.pointer_merges_since(&parent).unwrap()
                });
                assert_eq!(merges.len(), 1);
                (size, work)
            })
            .collect::<Vec<_>>();
        assert!(
            samples.iter().all(|(_, work)| *work == samples[0].1),
            "one merge delta grew with the shared prefix: {samples:?}"
        );
    }

    fn at_offset(block: PointerBlock, offset: PointerOffsetTerm) -> Pointer {
        Pointer { block, offset }
    }

    #[test]
    fn affine_offset_equality_reaches_same_block_simp() {
        let base = symbolic(11_080);
        let x = PointerOffsetTerm::Variable(Variable(11_081));
        let nested = PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::Add(
                Box::new(x.clone()),
                Box::new(PointerOffsetTerm::Constant(4)),
            )),
            Box::new(PointerOffsetTerm::Constant(4)),
        );
        let reordered = PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::Constant(8)),
            Box::new(x.clone()),
        );
        let wrong = PointerOffsetTerm::add(x, PointerOffsetTerm::Constant(9));
        let context = PureFactContext::new();
        assert!(
            context
                .equality_graph
                .are_offsets_equal(&nested, &reordered)
        );
        assert!(
            context
                .equality_graph
                .are_offsets_equal(&reordered, &nested)
        );
        assert_eq!(
            context.decide_condition_for_simp(&ConditionTerm::pointer_equal(
                at_offset(base.clone(), nested.clone()),
                at_offset(base.clone(), reordered.clone()),
            )),
            Some(true)
        );
        assert!(!context.equality_graph.are_offsets_equal(&nested, &wrong));
        assert_ne!(
            context.decide_condition_for_simp(&ConditionTerm::pointer_equal(
                at_offset(base.clone(), nested),
                at_offset(base, wrong),
            )),
            Some(true)
        );
    }

    #[test]
    fn same_block_pointer_query_uses_exact_offset_classes() {
        let left_offset = PointerOffsetTerm::Variable(Variable(11_001));
        let right_offset = PointerOffsetTerm::Variable(Variable(11_002));
        let base = symbolic(11_003);
        let left = at_offset(base.clone(), left_offset.clone());
        let right = at_offset(base.clone(), right_offset.clone());
        let other_block = at_offset(symbolic(11_004), right_offset.clone());
        let trunk = EqualityGraph::default();
        assert!(!trunk.are_equal(&left, &right));
        let mut branch = trunk.clone();
        branch.add_offset_equality(&left_offset, &right_offset);
        assert!(branch.are_equal(&left, &right));
        assert!(!trunk.are_equal(&left, &right));
        assert!(!branch.are_equal(&left, &other_block));
    }

    #[test]
    fn same_block_pointer_premise_joins_offsets_and_survives_only_in_its_context() {
        let block = symbolic(11_020);
        let x = PointerOffsetTerm::Variable(Variable(11_021));
        let y = PointerOffsetTerm::Variable(Variable(11_022));
        let z = PointerOffsetTerm::Variable(Variable(11_023));
        let left = at_offset(block.clone(), x.clone());
        let middle = at_offset(block, y.clone());
        let pointer_fact = ConditionTerm::pointer_equal(left.clone(), middle.clone());
        let offset_fact = ConditionTerm::pointer_offset_equal(y.clone(), z.clone());
        let trunk = PureFactContext::new().assume_condition(offset_fact.clone(), true);
        let branch = trunk.clone().assume_condition(pointer_fact.clone(), true);
        assert!(!trunk.equality_graph.are_offsets_equal(&x, &z));
        assert!(branch.equality_graph.are_offsets_equal(&x, &z));
        assert!(branch.equality_graph.are_equal(
            &at_offset(
                left.block.clone(),
                PointerOffsetTerm::add(x.clone(), PointerOffsetTerm::Constant(8))
            ),
            &at_offset(
                left.block.clone(),
                PointerOffsetTerm::add(z.clone(), PointerOffsetTerm::Constant(8))
            ),
        ));
        let withdrawn = branch.without_exact_fact(&Proposition::ConditionIs(pointer_fact, true));
        assert!(!withdrawn.equality_graph.are_offsets_equal(&x, &z));
        assert!(withdrawn.equality_graph.are_offsets_equal(&y, &z));
        let restricted = branch.restricted_to_facts(&[(offset_fact, true)], &[]);
        assert!(!restricted.equality_graph.are_offsets_equal(&x, &z));

        let mut cross_block = EqualityGraph::default();
        cross_block.add_equality(&left, &at_offset(symbolic(11_024), y.clone()));
        assert!(!cross_block.are_offsets_equal(&x, &y));
    }

    #[test]
    fn same_block_pointer_premise_chains_have_indexed_work() {
        for size in [16u64, 64, 256, 1024] {
            let block = symbolic(11_030);
            let offset = |i| PointerOffsetTerm::Variable(Variable(20_000 + i));
            let mut graph = EqualityGraph::default();
            let (_, insertion_work) = crate::instrumentation::measure_deterministic_work(|| {
                for i in 0..size {
                    assert!(graph.add_equality(
                        &at_offset(block.clone(), offset(i)),
                        &at_offset(block.clone(), offset(i + 1)),
                    ));
                }
            });
            assert!(
                insertion_work <= 128 * size as usize,
                "size={size}, insertion work={insertion_work}"
            );
            let (equal, query_work) = crate::instrumentation::measure_deterministic_work(|| {
                graph.are_offsets_equal(&offset(0), &offset(size))
            });
            assert!(equal);
            assert!(query_work < 64, "size={size}, query work={query_work}");
        }
    }

    #[test]
    fn equal_base_displacements_transport_exact_offset_edges_across_blocks() {
        let a = symbolic(11_040);
        let b = symbolic(11_041);
        let c = symbolic(11_042);
        let x = PointerOffsetTerm::Variable(Variable(11_043));
        let y = PointerOffsetTerm::Variable(Variable(11_044));
        let offset_fact = ConditionTerm::pointer_offset_equal(x.clone(), y.clone());
        let ab = ConditionTerm::pointer_equal(at(a.clone(), 0), at(b.clone(), 0));
        let bc = ConditionTerm::pointer_equal(at(b.clone(), 0), at(c.clone(), 0));
        let trunk = PureFactContext::new().assume_condition(offset_fact.clone(), true);
        let branch = trunk
            .clone()
            .assume_condition(ab.clone(), true)
            .assume_condition(bc.clone(), true);
        let left = at_offset(a.clone(), x.clone());
        let right = at_offset(c.clone(), y.clone());
        assert!(!trunk.equality_graph.are_equal(&left, &right));
        assert!(branch.equality_graph.are_equal(&left, &right));
        let withdrawn = branch.without_exact_fact(&Proposition::ConditionIs(bc, true));
        assert!(!withdrawn.equality_graph.are_equal(&left, &right));
        let restricted = branch.restricted_to_facts(&[(offset_fact, true)], &[]);
        assert!(!restricted.equality_graph.are_equal(&left, &right));

        let mut displaced = EqualityGraph::default();
        displaced.add_offset_equality(&x, &y);
        displaced.add_equality(&at(a.clone(), 0), &at(b.clone(), 8));
        assert!(!displaced.are_equal(&at_offset(a, x), &at_offset(b, y)));
    }

    #[test]
    fn equal_base_offset_queries_ignore_unrelated_class_members() {
        for size in [16u64, 64, 256, 1024] {
            let x = PointerOffsetTerm::Variable(Variable(11_050));
            let y = PointerOffsetTerm::Variable(Variable(11_051));
            let mut graph = EqualityGraph::default();
            for i in 0..size {
                graph.add_equality(&at(symbolic(30_000 + i), 0), &at(symbolic(30_001 + i), 0));
            }
            graph.add_offset_equality(&x, &y);
            let left = at_offset(symbolic(30_000), x.clone());
            let right = at_offset(symbolic(30_000 + size), y.clone());
            let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
                graph.are_equal(&left, &right)
            });
            assert!(equal);
            assert!(work < 64, "size={size}, work={work}");
            let (equal, map_work) =
                crate::persistent::measure_persistent_work(|| graph.are_equal(&left, &right));
            assert!(equal);
            assert!(
                map_work < 64 * (size.ilog2() as usize + 1),
                "size={size}, map work={map_work}"
            );
        }
    }

    #[test]
    fn constant_displacement_uses_only_a_stated_translated_offset_equality() {
        let a = symbolic(11_060);
        let b = symbolic(11_061);
        let x = PointerOffsetTerm::Variable(Variable(11_062));
        let y = PointerOffsetTerm::Variable(Variable(11_063));
        let translated = PointerOffsetTerm::add(x.clone(), PointerOffsetTerm::Constant(8));
        let offset_fact = ConditionTerm::pointer_offset_equal(translated, y.clone());
        let pointer_fact = ConditionTerm::pointer_equal(at(a.clone(), 0), at(b.clone(), 8));
        let trunk = PureFactContext::new().assume_condition(offset_fact.clone(), true);
        let branch = trunk.clone().assume_condition(pointer_fact.clone(), true);
        let left = at_offset(a.clone(), x.clone());
        let right = at_offset(b.clone(), y.clone());
        assert!(!trunk.equality_graph.are_equal(&left, &right));
        assert!(branch.equality_graph.are_equal(&left, &right));
        assert!(branch.equality_graph.are_equal(&right, &left));
        assert_eq!(
            branch.decide(&ConditionTerm::pointer_equal(left.clone(), right.clone())),
            Some(true)
        );
        assert!(
            !branch
                .equality_graph
                .are_equal(&left, &at_offset(b.clone(), x.clone()))
        );
        let withdrawn = branch.without_exact_fact(&Proposition::ConditionIs(pointer_fact, true));
        assert!(!withdrawn.equality_graph.are_equal(&left, &right));
        let restricted = branch.restricted_to_facts(&[(offset_fact, true)], &[]);
        assert!(!restricted.equality_graph.are_equal(&left, &right));

        let mut other_spelling = EqualityGraph::default();
        other_spelling.add_equality(&at(a.clone(), 0), &at(b.clone(), 8));
        other_spelling.add_offset_equality(
            &x,
            &PointerOffsetTerm::add(y.clone(), PointerOffsetTerm::Constant(-8)),
        );
        assert!(other_spelling.are_equal(&left, &right));
        assert!(other_spelling.are_equal(&right, &left));

        let mut unspellable = EqualityGraph::default();
        unspellable.add_equality(&at(a, 0), &at(b, i64::MIN));
        unspellable.add_offset_equality(
            &PointerOffsetTerm::Add(
                Box::new(x.clone()),
                Box::new(PointerOffsetTerm::Constant(i64::MIN)),
            ),
            &y,
        );
        // The raw address applications can use the stated MIN translation
        // directly, without constructing its unrepresentable opposite sign.
        assert!(unspellable.are_equal(&left, &right));
        assert!(unspellable.are_equal(&right, &left));
        assert!(!unspellable.are_equal(&left, &right.offset_by_bytes(1)));
    }

    #[test]
    fn pointer_transitivity_recovers_same_block_offsets() {
        let offset = |id| PointerOffsetTerm::Int32Scaled {
            value: Box::new(index(id)),
            byte_width: 4,
        };
        for reverse in [false, true] {
            let mut samples = Vec::new();
            for size in [8u64, 32, 128, 512] {
                let x = at_offset(PointerBlock::ExternalArgument, offset(960_000));
                let y = at_offset(PointerBlock::ExternalArgument, offset(960_001));
                let z = at(symbolic(960_002), 0);
                let mut graph = EqualityGraph::default();
                for id in 0..size {
                    graph.add_equality(
                        &at_offset(
                            symbolic(961_000 + id),
                            PointerOffsetTerm::Variable(Variable(963_000 + id)),
                        ),
                        &z,
                    );
                }
                if reverse {
                    graph.add_equality(&z, &y);
                } else {
                    graph.add_equality(&x, &z);
                }
                let sibling = graph.clone();
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    if reverse {
                        graph.add_equality(&x, &z);
                    } else {
                        graph.add_equality(&z, &y);
                    }
                });
                // A new non-affine offset relation can invalidate affine
                // completeness for the registered dependent addresses once.
                assert!(work <= 16 * size as usize + 512, "size={size}, work={work}");
                let (_, query_work) = crate::instrumentation::measure_deterministic_work(|| {
                    assert!(graph.are_offsets_equal(&x.offset, &y.offset));
                    assert!(graph.are_equal(&x, &y));
                    assert!(!graph.are_equal(&x, &y.offset_by_bytes(1)));
                });
                samples.push(query_work);
                assert!(!sibling.are_offsets_equal(&x.offset, &y.offset));
                assert!(!sibling.are_equal(&x, &y));
            }
            assert!(
                samples.iter().all(|work| *work <= samples[0] + 40),
                "reverse={reverse}, query work={samples:?}"
            );
        }
        // Equal addresses from different blocks do not equate their offsets.
        let mut graph = EqualityGraph::default();
        graph.add_equality(&at(symbolic(962_000), 4), &at(symbolic(962_001), 8));
        assert!(!graph.are_offsets_equal(
            &PointerOffsetTerm::Constant(4),
            &PointerOffsetTerm::Constant(8)
        ));
    }

    #[test]
    fn mixed_offset_and_block_premises_compose_in_any_order() {
        let x = at_offset(
            PointerBlock::ExternalArgument,
            PointerOffsetTerm::Variable(Variable(930_001)),
        );
        let y = at_offset(
            PointerBlock::ExternalArgument,
            PointerOffsetTerm::Variable(Variable(930_002)),
        );
        let z = at(symbolic(930_003), 0);
        for order in [
            [0, 1, 2],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ] {
            let mut graph = EqualityGraph::default();
            for premise in order {
                match premise {
                    0 => {
                        graph.add_offset_equality(&x.offset, &y.offset);
                    }
                    1 => {
                        graph.add_equality(&y, &z);
                    }
                    2 => {
                        graph.add_equality(&z, &Pointer::null());
                    }
                    _ => unreachable!(),
                }
            }
            assert!(graph.are_equal(&x, &Pointer::null()), "order={order:?}");
            assert!(graph.are_equal(&Pointer::null(), &x), "order={order:?}");
            assert!(!graph.are_equal(&x, &Pointer::null().offset_by_bytes(1)));
        }
    }

    #[test]
    fn mixed_pointer_queries_do_not_walk_growing_offset_classes() {
        for size in [8u64, 32, 128, 512] {
            let offset = |i| PointerOffsetTerm::Variable(Variable(940_000 + i));
            let x = at_offset(PointerBlock::ExternalArgument, offset(0));
            let y = at_offset(PointerBlock::ExternalArgument, offset(size));
            let z = at(symbolic(950_000), 0);
            let mut graph = EqualityGraph::default();
            let (_, construction) = crate::instrumentation::measure_deterministic_work(|| {
                for i in 1..size {
                    graph.add_offset_equality(&offset(i), &offset(i + 1));
                }
                graph.add_equality(&y, &z);
                graph.add_equality(&z, &Pointer::null());
            });
            assert!(
                construction < 128 * size as usize,
                "size={size}, work={construction}"
            );
            assert!(!graph.are_equal(&x, &Pointer::null()));
            let sibling = graph.clone();
            let mut branch = graph.clone();
            let (_, query) = crate::instrumentation::measure_deterministic_work(|| {
                branch.add_offset_equality(&offset(0), &offset(1));
                assert!(branch.are_equal(&x, &Pointer::null()));
                assert!(branch.are_equal(&Pointer::null(), &x));
            });
            assert!(query < 128, "size={size}, work={query}");
            assert!(!graph.are_equal(&x, &Pointer::null()));
            assert!(!sibling.are_equal(&x, &Pointer::null()));
        }
    }

    #[test]
    fn constant_displacement_queries_ignore_unrelated_class_members() {
        for size in [16u64, 64, 256, 1024] {
            let a = symbolic(40_000);
            let b = symbolic(40_001);
            let x = PointerOffsetTerm::Variable(Variable(11_070));
            let y = PointerOffsetTerm::Variable(Variable(11_071));
            let mut graph = EqualityGraph::default();
            graph.add_equality(&at(a.clone(), 0), &at(b.clone(), 8));
            for i in 1..size {
                graph.add_equality(&at(symbolic(40_000 + i), 0), &at(symbolic(40_001 + i), 0));
            }
            graph.add_offset_equality(
                &PointerOffsetTerm::add(x.clone(), PointerOffsetTerm::Constant(8)),
                &y,
            );
            let left = at_offset(a, x);
            let right = at_offset(symbolic(40_000 + size), y);
            let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
                graph.are_equal(&left, &right)
            });
            assert!(equal);
            assert!(work < 96, "size={size}, work={work}");
            let (equal, map_work) =
                crate::persistent::measure_persistent_work(|| graph.are_equal(&left, &right));
            assert!(equal);
            assert!(
                map_work < 96 * (size.ilog2() as usize + 1),
                "size={size}, map work={map_work}"
            );
        }
    }

    #[test]
    fn same_block_pointer_query_uses_scaled_int32_congruence() {
        let base = symbolic(11_010);
        let offset = |id| {
            PointerOffsetTerm::add(
                PointerOffsetTerm::scale_int32(index(id), 4),
                PointerOffsetTerm::Constant(8),
            )
        };
        let left = at_offset(base.clone(), offset(11_011));
        let right = at_offset(base.clone(), offset(11_012));
        let wrong_width = at_offset(
            base.clone(),
            PointerOffsetTerm::add(
                PointerOffsetTerm::scale_int32(index(11_012), 8),
                PointerOffsetTerm::Constant(8),
            ),
        );
        let mut graph = EqualityGraph::default();
        assert!(!graph.are_equal(&left, &right));
        graph.add_int32_equality(&index(11_011), &index(11_012));
        assert!(graph.are_equal(&left, &right));
        assert!(!graph.are_equal(&left, &wrong_width));
        assert!(!graph.are_equal(&left, &at_offset(symbolic(11_013), offset(11_012))));
    }

    #[test]
    fn same_block_pointer_query_does_not_turn_wrapping_index_into_exact_offset() {
        let base = symbolic(11_014);
        let max = Bitvector32Term::Constant(i32::MAX as u32);
        let wrapped = at_offset(
            base.clone(),
            PointerOffsetTerm::scale_int32(
                Bitvector32Term::add(max.clone(), Bitvector32Term::Constant(1)),
                4,
            ),
        );
        let exact_sum = at_offset(
            base,
            PointerOffsetTerm::add(
                PointerOffsetTerm::scale_int32(max, 4),
                PointerOffsetTerm::Constant(4),
            ),
        );
        assert!(!EqualityGraph::default().are_equal(&wrapped, &exact_sum));
    }

    #[test]
    fn same_block_pointer_queries_scale_with_registered_offset_classes() {
        for size in [16u64, 64, 256, 1024] {
            let base = symbolic(11_020);
            let mut graph = EqualityGraph::default();
            for id in 0..size {
                graph.add_int32_equality(&index(id), &index(id + 1));
            }
            let first = at_offset(base.clone(), PointerOffsetTerm::scale_int32(index(0), 4));
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                for id in 1..=size {
                    let other =
                        at_offset(base.clone(), PointerOffsetTerm::scale_int32(index(id), 4));
                    assert!(graph.are_equal(&first, &other));
                }
            });
            assert!(work < 200 * size as usize, "size={size}, work={work}");
        }
    }

    #[test]
    fn a_symbolic_displacement_carries_through_the_class() {
        let mut classes = EqualityGraph::default();
        let element = Pointer {
            block: symbolic(2),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(index(9)),
                byte_width: 4,
            },
        };
        classes.add_equality(&at(symbolic(1), 0), &element);
        let next = Pointer {
            block: symbolic(2),
            offset: PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::Int32Scaled {
                    value: Box::new(index(9)),
                    byte_width: 4,
                }),
                Box::new(PointerOffsetTerm::Constant(4)),
            ),
        };
        assert!(classes.are_equal(&at(symbolic(1), 4), &next));
        assert!(!classes.are_equal(&at(symbolic(1), 4), &element));
    }

    #[test]
    fn an_equality_inside_one_class_records_its_exact_offset() {
        let mut classes = EqualityGraph::default();
        classes.add_equality(&at(symbolic(1), 0), &at(symbolic(2), 0));
        let indexed = at_offset(symbolic(2), PointerOffsetTerm::scale_int32(index(91), 4));
        assert!(classes.add_equality(&at(symbolic(1), 0), &indexed));
        assert!(classes.are_equal(&at(symbolic(1), 0), &at(symbolic(2), 0)));
        assert!(classes.are_equal(&at(symbolic(1), 0), &indexed));
        assert!(!classes.are_equal(&at(symbolic(1), 0), &at(symbolic(2), 8)));
    }

    #[test]
    fn pointer_class_members_restate_a_pointer_in_every_member() {
        let mut classes = EqualityGraph::default();
        classes.add_equality(&at(symbolic(1), 0), &at(symbolic(2), 8));
        classes.add_equality(&at(symbolic(3), 4), &at(symbolic(2), 0));
        let blocks = classes.pointer_class_members(&symbolic(1));
        assert_eq!(blocks.len(), 3);
        for (member, delta) in blocks {
            let restated = Pointer {
                block: member,
                offset: PointerOffsetTerm::Constant(
                    i64::try_from(delta.constant).expect("small constant"),
                ),
            };
            assert!(delta.terms.is_empty());
            assert!(classes.are_equal(&at(symbolic(1), 0), &restated));
        }
    }

    #[test]
    fn pointer_spellings_name_the_same_address_in_each_member() {
        let mut classes = EqualityGraph::default();
        assert!(classes.pointer_spellings(&at(symbolic(1), 4)).is_empty());
        let element = Pointer {
            block: symbolic(2),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(index(9)),
                byte_width: 8,
            },
        };
        classes.add_equality(&at(symbolic(1), 0), &element);
        classes.add_equality(&at(symbolic(3), 16), &at(symbolic(1), 0));
        let spellings = classes.pointer_spellings(&at(symbolic(1), 4));
        assert_eq!(spellings.len(), 2);
        for spelling in &spellings {
            assert_ne!(spelling.block, symbolic(1));
            assert!(classes.are_equal(spelling, &at(symbolic(1), 4)));
        }
        assert!(spellings.contains(&at(symbolic(3), 20)));
        assert!(
            classes
                .pointer_spellings(&element)
                .contains(&at(symbolic(1), 0)),
            "inverse symbolic displacements must cancel before a cell-map lookup"
        );
    }

    #[test]
    fn explicit_pointer_load_identity_is_typed_and_congruent() {
        let p = at(symbolic(51_100), 0);
        let q = at(symbolic(51_101), 0);
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block(p.block.clone(), 8));
        let later = crate::kernel::intern_c_memory(
            memory
                .memory()
                .clone()
                .store(p.clone(), CValue::Int32(Bitvector32Term::Constant(7))),
        );
        let from_p = Pointer::loaded_value(&memory, &p);
        let from_p_again = Pointer::loaded_value(&memory, &p);
        let from_q = Pointer::loaded_value(&memory, &q);
        let from_later = Pointer::loaded_value(&later, &p);
        assert_eq!(from_p, from_p_again);
        assert_ne!(from_p, from_q);
        assert_ne!(from_p, from_later);
        let definition = from_p.as_loaded_value().unwrap();
        assert_eq!(
            definition.identity,
            from_p_again.as_loaded_value().unwrap().identity
        );
        assert_eq!(definition.defining_address, p);
        assert_eq!(definition.defining_memory.arena_id(), memory.arena_id());
        let byte_view =
            CPointerValue::new(from_p.clone(), CType::Int32Pointer).with_type(CType::UInt8Pointer);
        assert_eq!(byte_view.pointer(), &from_p);
        let displaced = from_p.offset_by_bytes(8);
        assert_eq!(
            displaced.as_loaded_value().unwrap().displacement,
            PointerOffsetTerm::Constant(8)
        );
        assert!(from_p.has_symbolic_block());
        let scalar_indexed_address = Pointer::loaded(
            p.block.clone(),
            Bitvector32Term::MemoryLoad(
                memory.clone(),
                Box::new(p.clone()),
                crate::kernel::LoadKind::Bits32,
            ),
            8,
        );
        assert!(scalar_indexed_address.as_loaded_value().is_none());
        assert_ne!(scalar_indexed_address, from_p);
        let CValue::Pointer(execution_value) =
            memory
                .memory()
                .symbolic_pointer_load(&p, 8, CType::Int64Pointer)
        else {
            panic!("pointer-typed load must produce a pointer value");
        };
        assert_ne!(execution_value.pointer(), &scalar_indexed_address);
        let complete_pointer_address = Pointer::loaded(
            p.block.clone(),
            Bitvector32Term::MemoryLoad(
                memory.clone(),
                Box::new(p.clone()),
                crate::kernel::LoadKind::Pointer,
            ),
            8,
        );
        assert_eq!(execution_value.pointer(), &complete_pointer_address);

        // A scalar read of the same cell may have a four-byte interpretation;
        // it cannot determine whether the distinct pointer-load name enters
        // the graph's eight-byte application index.
        crate::kernel::load_variable_for_cell_with_origin(
            &memory,
            &p,
            crate::kernel::LoadKind::Bits32,
            4,
            &memory,
        );
        let mut graph = EqualityGraph::default();
        assert!(!graph.are_pointer_loads_equal(&memory, &p, &q));
        assert!(!graph.are_equal(&from_p, &from_q));
        graph.add_equality(&p, &q);
        assert!(graph.are_pointer_loads_equal(&memory, &p, &q));
        assert!(graph.are_equal(&from_p, &from_q));
        assert!(graph.are_equal(&displaced, &from_q.offset_by_bytes(8)));
        assert!(!graph.are_equal(&from_p, &from_later));
    }

    #[test]
    fn explicit_pointer_load_congruence_is_branch_local_and_order_independent() {
        let memory = crate::kernel::intern_c_memory(CMemory::new());
        let p = at(symbolic(51_201), 0);
        let q = at(symbolic(51_202), 0);
        let left = Pointer::loaded_value(&memory, &p);
        let right = Pointer::loaded_value(&memory, &q);
        let x = at(symbolic(51_203), 0);
        let y = at(symbolic(51_204), 0);
        for address_first in [false, true] {
            let mut trunk = EqualityGraph::default();
            trunk.add_equality(&left, &x);
            trunk.add_equality(&right, &y);
            let sibling = trunk.clone();
            let mut branch = trunk.clone();
            if address_first {
                branch.add_equality(&p, &q);
            }
            assert!(!sibling.are_pointer_loads_equal(&memory, &p, &q));
            assert!(!sibling.are_equal(&x, &y));
            assert!(!trunk.are_equal(&x, &y));
            if !address_first {
                assert!(!branch.are_pointer_loads_equal(&memory, &p, &q));
                assert!(!branch.are_equal(&x, &y));
                branch.add_equality(&p, &q);
            }
            assert!(branch.are_pointer_loads_equal(&memory, &p, &q));
            assert!(branch.are_equal(&x, &y));
            assert!(branch.are_equal(&left.offset_by_bytes(8), &right.offset_by_bytes(8)));
            assert!(!trunk.are_equal(&left, &right));
        }
    }

    // A byte-offset goal must discover its typed read dependencies without
    // needing an earlier full-pointer query. Late metadata invalidates misses.
    #[test]
    fn offset_queries_retain_typed_read_definitions_and_keep_blocks_distinct() {
        let memory = crate::kernel::intern_c_memory(CMemory::new());
        let p = at(symbolic(919_001), 0);
        let q = at(symbolic(919_002), 0);
        let variable = |address: &Pointer| {
            crate::kernel::load_variable_for_cell_with_origin(
                &memory,
                address,
                crate::kernel::LoadKind::Bits32,
                8,
                &memory,
            )
        };
        let xv = variable(&p);
        let yv = variable(&q);
        let x = Pointer::loaded(
            PointerBlock::ExternalArgument,
            Bitvector32Term::Variable(xv),
            8,
        );
        let y = Pointer::loaded(
            PointerBlock::ExternalArgument,
            Bitvector32Term::Variable(yv),
            8,
        );
        let mut graph = EqualityGraph::default();
        let sibling = graph.clone();
        graph.add_equality(&p, &q);
        for _ in 0..2 {
            assert!(!graph.are_offsets_equal(&x.offset, &y.offset));
        }
        graph.register_pointer_read_definition(&x, &memory, &p);
        graph.register_pointer_read_definition(&y, &memory, &q);
        assert!(graph.are_offsets_equal(&x.offset, &y.offset));
        assert!(
            graph.are_offsets_equal(&x.offset_by_bytes(8).offset, &y.offset_by_bytes(8).offset)
        );
        assert!(!sibling.are_offsets_equal(&x.offset, &y.offset));
        assert!(!graph.are_offsets_equal(
            &x.offset,
            &PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(yv), 4)
        ));
        // New unrelated definitions invalidate the dependency cache, but
        // rediscovery must still visit only these two selected operands.
        for size in [16u64, 64, 256, 1024] {
            for i in 0..size {
                let address = at(symbolic(920_000 + i), 0);
                let value = Pointer::loaded_value(&memory, &address);
                graph.register_pointer_read_definition(&value, &memory, &address);
            }
            let ((equal, work), map_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    graph.are_offsets_equal(
                        &x.offset_by_bytes(16).offset,
                        &y.offset_by_bytes(16).offset,
                    )
                })
            });
            assert!(equal);
            assert!(work < 200, "size={size}, work={work}");
            assert!(
                map_work < 512 * (size.ilog2() as usize + 1),
                "size={size}, map work={map_work}"
            );
        }
        assert!(!graph.are_equal(
            &at_offset(symbolic(919_003), x.offset),
            &at_offset(symbolic(919_004), y.offset)
        ));
    }

    // Whole-offset equality is not an affine block merge. All read consumers
    // must nevertheless see it, including when learned after registration.
    #[test]
    fn typed_reads_follow_whole_address_congruence() {
        let memory = crate::kernel::intern_c_memory(CMemory::new());
        let p = at_offset(
            symbolic(910_001),
            PointerOffsetTerm::scale_int32(index(910_002), 8),
        );
        let q = at_offset(
            symbolic(910_001),
            PointerOffsetTerm::scale_int32(index(910_003), 8),
        );
        let left = Pointer::loaded_value(&memory, &p);
        let right = Pointer::loaded_value(&memory, &q);
        for early in [false, true] {
            let mut graph = EqualityGraph::default();
            let sibling = graph.clone();
            if !early {
                assert!(!graph.are_equal(&left, &right));
            }
            graph.add_offset_equality(&p.offset, &q.offset);
            assert!(graph.are_equal(&p, &q));
            assert!(graph.are_equal(&left, &right));
            assert!(!sibling.are_equal(&left, &right));
            assert!(!graph.are_equal(
                &left,
                &Pointer::loaded_value(&memory, &q.offset_by_bytes(8))
            ));
            let changed = crate::kernel::intern_c_memory(
                memory
                    .memory()
                    .clone()
                    .store(p.clone(), CValue::Int32(Bitvector32Term::Constant(7))),
            );
            assert!(!graph.are_equal(&left, &Pointer::loaded_value(&changed, &q)));
        }
    }

    #[test]
    fn loads_at_equal_pointers_of_one_snapshot_are_one_value() {
        let memory = crate::kernel::intern_c_memory(
            crate::kernel::CMemory::new().with_block(symbolic(51), 16),
        );
        // A later snapshot where the cell `p` addresses was written.
        let other_memory = crate::kernel::intern_c_memory(memory.memory().clone().store(
            at(symbolic(41), 0),
            CValue::Int32(Bitvector32Term::Constant(7)),
        ));
        let name = |memory: &crate::kernel::SharedCMemory, address: Pointer| {
            PointerBlock::Symbolic(crate::kernel::load_variable_for_cell_with_origin(
                memory,
                &address,
                crate::kernel::LoadKind::Pointer,
                8,
                memory,
            ))
        };
        let through_p = name(&memory, at(symbolic(41), 0));
        let through_q = name(&memory, at(symbolic(42), 0));
        let through_p_later = name(&other_memory, at(symbolic(41), 0));
        let through_r = name(&memory, at(symbolic(43), 0));
        let mut classes = EqualityGraph::default();
        assert!(!classes.are_equal(&at(through_p.clone(), 8), &at(through_q.clone(), 8)));
        classes.add_equality(&at(symbolic(41), 0), &at(symbolic(42), 0));
        assert!(classes.are_equal(&at(through_p.clone(), 8), &at(through_q.clone(), 8)));
        assert!(!classes.are_equal(&at(through_p.clone(), 8), &at(through_q, 0)));
        assert!(!classes.are_equal(&at(through_p.clone(), 8), &at(through_p_later, 8)));
        assert!(!classes.are_equal(&at(through_p.clone(), 8), &at(through_r.clone(), 8)));
        // A loaded pointer an equality puts in a class brings the loads
        // congruent to it along.
        classes.add_equality(&at(through_r.clone(), 0), &at(symbolic(60), 0));
        let through_r_again = name(&memory, at(symbolic(43), 0));
        assert!(classes.are_equal(&at(through_r_again, 4), &at(symbolic(60), 4)));
    }

    #[test]
    fn congruent_loads_merge_their_existing_explicit_classes() {
        let memory = crate::kernel::intern_c_memory(
            crate::kernel::CMemory::new().with_block(symbolic(101), 16),
        );
        let p = at(symbolic(102), 0);
        let q = at(symbolic(103), 0);
        let load = |address: &Pointer| {
            at(
                PointerBlock::Symbolic(crate::kernel::load_variable_for_cell_with_origin(
                    &memory,
                    address,
                    crate::kernel::LoadKind::Pointer,
                    8,
                    &memory,
                )),
                0,
            )
        };
        let lp = load(&p);
        let lq = load(&q);
        let x = at(symbolic(104), 0);
        let y = at(symbolic(105), 0);
        let mut classes = EqualityGraph::default();
        classes.add_equality(&p, &q);
        assert!(classes.are_equal(&lp, &lq));
        classes.add_equality(&lp, &x);
        classes.add_equality(&lq, &y);
        assert!(classes.are_equal(&lp, &lq));
        assert!(classes.are_equal(&x, &y));
    }

    #[test]
    fn cross_snapshot_load_equality_requires_a_supplied_conclusion() {
        // Structure cannot separate the store from the read. Their addresses
        // being unequal alone does not exclude overlapping bytes; complete
        // range separation lets a checked caller establish load equality,
        // which the equality graph still needs supplied explicitly.
        let cell = Pointer {
            block: PointerBlock::Heap(95_001),
            offset: PointerOffsetTerm::Constant(0),
        };
        // The complete pointer read has an immutable eight-byte kind.
        let other = at(symbolic(95_003), 0);
        let before = crate::kernel::CMemory::new().with_block(PointerBlock::Heap(95_001), 16);
        let after = before
            .clone()
            .store(other.clone(), CValue::Int32(Bitvector32Term::Constant(3)));
        let name = |memory: &crate::kernel::CMemory| {
            let memory = crate::kernel::intern_c_memory(memory.clone());
            PointerBlock::Symbolic(crate::kernel::load_variable_for_cell_with_origin(
                &memory,
                &cell,
                crate::kernel::LoadKind::Pointer,
                8,
                &memory,
            ))
        };
        let (read_before, read_after) = (name(&before), name(&after));
        assert_ne!(read_before, read_after);
        let mut classes = EqualityGraph::default();
        let left = at(read_before, 8);
        let right = at(read_after, 8);
        // Pointer comparison never searches memory history, even when a
        // separate frame derivation could prove the cell unchanged.
        assert!(!classes.are_equal(&left, &right));
        let address_only = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(other.clone(), cell.clone()),
            false,
        );
        let load = |pointer: &Pointer| {
            let PointerBlock::Symbolic(variable) = &pointer.block else {
                unreachable!()
            };
            let (memory, address) =
                crate::kernel::registered_load_origin_for_variable(variable).unwrap();
            Bitvector32Term::MemoryLoad(memory, Box::new(address), crate::kernel::LoadKind::Pointer)
        };
        assert!(!crate::kernel::reasoning::memory_resolution::bitvector_terms_proven_equal_for_memory_resolution(
            &load(&left), &load(&right), &address_only,
        ));
        // Complete pointer observations retain their eight-byte span.
        let byte_range = |base, bytes| {
            crate::kernel::CMemoryRange::new_with_element_width(
                base,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(bytes),
                1,
            )
        };
        let separated = address_only.clone().assume_proposition(
            crate::kernel::Proposition::CResourceSeparate {
                left: Box::new(crate::kernel::CResource::Memory(byte_range(other, 4))),
                right: Box::new(crate::kernel::CResource::Memory(byte_range(cell, 8))),
            },
        );
        // The shallow resolver does not spend the explicit range proof.
        assert!(!crate::kernel::reasoning::memory_resolution::bitvector_terms_proven_equal_for_memory_resolution(
            &load(&left), &load(&right), &separated,
        ));
        assert!(
            !crate::kernel::explicit_atomic_equality_from_memory_derivations(
                &load(&left),
                &load(&right),
                &address_only,
            )
        );
        // A checked caller uses the explicit atomic proof path, which retains
        // the complete separation witness for independent checking.
        let capture = crate::kernel::memory_provenance::CheckedLoadEqualityCapture::start();
        assert!(
            crate::kernel::memory_provenance::checked_recorded_atomic_load_equality(
                &load(&left),
                &load(&right),
                &separated,
            )
        );
        let equalities = capture.finish();
        assert_eq!(equalities.len(), 1);
        assert!(equalities[0].checks(&separated));
        assert!(!equalities[0].checks(&address_only));
        assert!(!classes.are_equal(&left, &right));
        // A checked caller can contribute that conclusion explicitly.
        classes.add_equality(&left, &right);
        assert!(classes.are_equal(&left, &right));
    }

    #[test]
    fn a_branch_extends_its_own_copy() {
        let mut trunk = EqualityGraph::default();
        trunk.add_equality(&at(symbolic(1), 0), &at(symbolic(2), 0));
        let mut branch = trunk.clone();
        branch.add_equality(&at(symbolic(2), 0), &at(symbolic(3), 0));
        assert!(branch.are_equal(&at(symbolic(1), 0), &at(symbolic(3), 0)));
        assert!(!trunk.are_equal(&at(symbolic(1), 0), &at(symbolic(3), 0)));
    }

    /// Load congruence for one query visits only the classed loads of the
    /// queried load's own snapshot: the work is the same beside 16 or 256
    /// classed loads read from other snapshots.
    #[test]
    fn load_congruence_work_ignores_classed_loads_of_other_snapshots() {
        let name = |memory: &crate::kernel::SharedCMemory, address: Pointer| {
            PointerBlock::Symbolic(crate::kernel::load_variable_for_cell_with_origin(
                memory,
                &address,
                crate::kernel::LoadKind::Pointer,
                8,
                memory,
            ))
        };
        let mut costs = Vec::new();
        for unrelated in [16u64, 64, 256] {
            let mut classes = EqualityGraph::default();
            for index in 0..unrelated {
                let memory = crate::kernel::intern_c_memory(
                    crate::kernel::CMemory::new()
                        .with_block(symbolic(70_000 + index), 16)
                        .store(
                            at(symbolic(70_000 + index), 0),
                            CValue::Int32(Bitvector32Term::Constant(index as u32)),
                        ),
                );
                let loaded = name(&memory, at(symbolic(70_000 + index), 0));
                classes.add_equality(&at(loaded, 0), &at(symbolic(80_000 + index), 0));
            }
            let memory = crate::kernel::intern_c_memory(
                crate::kernel::CMemory::new().with_block(symbolic(90_000), 16),
            );
            classes.add_equality(&at(symbolic(90_001), 0), &at(symbolic(90_002), 0));
            let left = name(&memory, at(symbolic(90_001), 0));
            let right = name(&memory, at(symbolic(90_002), 0));
            let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
                classes.are_equal(&at(left.clone(), 8), &at(right.clone(), 8))
            });
            assert!(equal);
            costs.push(work);
        }
        assert!(costs.windows(2).all(|pair| pair[0] == pair[1]), "{costs:?}");
    }

    fn named_load(memory: &SharedCMemory, address: &Pointer) -> Pointer {
        at(
            PointerBlock::Symbolic(crate::kernel::load_variable_for_cell_with_origin(
                memory,
                address,
                crate::kernel::LoadKind::Pointer,
                8,
                memory,
            )),
            0,
        )
    }

    #[test]
    fn load_congruence_is_independent_of_equality_insertion_order() {
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block(symbolic(201), 16));
        let p = at(symbolic(202), 0);
        let q = at(symbolic(203), 16);
        let lp = named_load(&memory, &at(p.block.clone(), 8));
        let lq = named_load(&memory, &at(q.block.clone(), 24));
        let x = at(symbolic(204), 0);
        let y = at(symbolic(205), 0);
        let equations = [
            (p, q),
            (at(lp.block.clone(), 4), x.clone()),
            (at(lq.block.clone(), 12), y.clone()),
        ];
        for order in [
            [0, 1, 2],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ] {
            let mut classes = EqualityGraph::default();
            for index in order {
                classes.are_equal(&lp, &lq); // registration before and between merges
                classes.add_equality(&equations[index].0, &equations[index].1);
            }
            assert!(classes.are_equal(&lp, &lq), "{order:?}");
            assert!(classes.are_equal(&at(x.block.clone(), 8), &y), "{order:?}");
            assert!(!classes.are_equal(&x, &y), "different load displacements");
            classes.add_equality(&at(symbolic(206), 0), &at(symbolic(207), 0));
            assert!(
                classes.are_equal(&lp, &lq),
                "extra facts must preserve equality"
            );
        }
    }

    #[test]
    fn nested_load_congruence_propagates_a_late_merge_without_a_depth_cutoff() {
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block(symbolic(301), 16));
        let p = at(symbolic(302), 0);
        let q = at(symbolic(303), 0);
        let mut left = p.clone();
        let mut right = q.clone();
        for _ in 0..12 {
            left = named_load(&memory, &left);
            right = named_load(&memory, &right);
        }
        let mut classes = EqualityGraph::default();
        assert!(!classes.are_equal(&left, &right));
        classes.add_equality(&p, &q);
        assert!(classes.are_equal(&left, &right));
        // A newly named parent after closure must see the existing congruence.
        let later_left = named_load(&memory, &at(left.block, 8));
        let later_right = named_load(&memory, &at(right.block, 8));
        assert!(classes.are_equal(&later_left, &later_right));
    }

    #[test]
    fn congruence_registration_and_merges_are_isolated_between_branches() {
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block(symbolic(401), 16));
        let p = at(symbolic(402), 0);
        let q = at(symbolic(403), 0);
        let lp = named_load(&memory, &p);
        let lq = named_load(&memory, &q);
        let x = at(symbolic(404), 0);
        let y = at(symbolic(405), 0);
        let mut trunk = EqualityGraph::default();
        trunk.add_equality(&lp, &x);
        trunk.add_equality(&lq, &y);
        let sibling = trunk.clone();
        let mut branch = trunk.clone();
        branch.add_equality(&p, &q);
        assert!(branch.are_equal(&x, &y));
        assert!(!trunk.are_equal(&x, &y));
        assert!(!sibling.are_equal(&x, &y));
        assert!(!EqualityGraph::default().are_equal(&lp, &lq));
    }

    #[test]
    fn same_snapshot_load_queries_ignore_unrelated_applications() {
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block(symbolic(501), 16));
        let p = at(symbolic(502), 0);
        let q = at(symbolic(503), 0);
        let left = named_load(&memory, &p);
        let right = named_load(&memory, &q);
        let mut costs = Vec::new();
        for size in [16, 64, 256, 1024] {
            let mut classes = EqualityGraph::default();
            for i in 0..size {
                let load = named_load(&memory, &at(symbolic(100_000 + i), 0));
                classes.add_equality(&load, &at(symbolic(200_000 + i), 0));
            }
            classes.add_equality(&p, &q);
            let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
                classes.are_equal(&left, &right)
            });
            assert!(equal);
            costs.push(work);
            let (equal, map_work) =
                crate::persistent::measure_persistent_work(|| classes.are_equal(&left, &right));
            assert!(equal);
            assert!(
                map_work < 32 * (size.ilog2() as usize + 1),
                "size={size}, map work={map_work}"
            );
        }
        assert!(costs.windows(2).all(|pair| pair[0] == pair[1]), "{costs:?}");
    }

    #[test]
    fn late_merges_and_repeated_queries_have_near_linear_total_work() {
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block(symbolic(601), 16));
        for size in [16u64, 64, 256, 1024] {
            let left = at(symbolic(602), 0);
            let right = at(symbolic(603), 0);
            let mut classes = EqualityGraph::default();
            let mut pairs = Vec::new();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for i in 0..size {
                    let a = named_load(&memory, &at(left.block.clone(), i as i64 * 8));
                    let b = named_load(&memory, &at(right.block.clone(), i as i64 * 8));
                    assert!(!classes.are_equal(&a, &b));
                    pairs.push((a, b));
                }
                classes.add_equality(&left, &right);
                for (a, b) in &pairs {
                    assert!(classes.are_equal(a, b));
                }
            });
            assert!(
                work <= 128 * size as usize,
                "size={size}, total work={work}"
            );
        }
    }

    #[test]
    fn late_typed_load_merges_scale_with_existing_storage_relative_bridges() {
        let memory = crate::kernel::intern_c_memory(CMemory::new());
        let mut costs = Vec::new();
        for size in [4u64, 16, 64, 256] {
            let mut graph = EqualityGraph::default();
            let mut pairs = Vec::new();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for i in 0..size {
                    let p = at(symbolic(810_000 + i), 0);
                    let q = at(symbolic(820_000 + i), 0);
                    let old_value = |address: &Pointer| {
                        Pointer::loaded(
                            address.block.clone(),
                            Bitvector32Term::Variable(
                                crate::kernel::load_variable_for_cell_with_origin(
                                    &memory,
                                    address,
                                    crate::kernel::LoadKind::Bits32,
                                    8,
                                    &memory,
                                ),
                            ),
                            8,
                        )
                    };
                    let left = old_value(&p);
                    let right = old_value(&q);
                    graph.add_equality(&left, &Pointer::loaded_value(&memory, &p));
                    graph.add_equality(&right, &Pointer::loaded_value(&memory, &q));
                    graph.add_equality(&p, &q);
                    pairs.push((left, right));
                }
                for (left, right) in &pairs {
                    assert!(graph.are_equal(left, right));
                }
            });
            costs.push(work);
        }
        // Read applications now include complete address terms. Check growth
        // across sizes rather than the old affine-only operation constant.
        assert!(
            costs.windows(2).all(|pair| pair[1] <= 5 * pair[0]),
            "{costs:?}"
        );
    }

    #[test]
    fn branch_merges_do_not_reindex_the_large_shared_prefix() {
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block(symbolic(701), 16));
        let root = at(symbolic(702), 0);
        let mut costs = Vec::new();
        for size in [16u64, 64, 256, 1024] {
            let mut trunk = EqualityGraph::default();
            for i in 0..size {
                let load = named_load(&memory, &at(root.block.clone(), i as i64 * 8));
                trunk.add_equality(&load, &at(symbolic(300_000 + i), 0));
            }
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for i in 0..16 {
                    let mut branch = trunk.clone();
                    let alias = at(symbolic(400_000 + i), 0);
                    branch.add_equality(&root, &alias);
                    assert!(branch.are_equal(&root, &alias));
                }
            });
            costs.push(work);
        }
        assert!(costs.windows(2).all(|pair| pair[0] == pair[1]), "{costs:?}");
    }

    #[test]
    fn restricted_context_and_fact_withdrawal_drop_derived_load_equalities() {
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block(symbolic(801), 16));
        let p = at(symbolic(802), 0);
        let q = at(symbolic(803), 0);
        let x = at(symbolic(804), 0);
        let y = at(symbolic(805), 0);
        let lp = named_load(&memory, &p);
        let lq = named_load(&memory, &q);
        let address = ConditionTerm::pointer_equal(p, q);
        let selected = [
            (ConditionTerm::pointer_equal(lp, x.clone()), true),
            (ConditionTerm::pointer_equal(lq, y.clone()), true),
        ];
        let mut context = PureFactContext::new().assume_condition(address.clone(), true);
        for (condition, value) in &selected {
            context = context.assume_condition(condition.clone(), *value);
        }
        assert!(context.pointers_known_equal(&x, &y));
        let restricted = context.restricted_to_facts(&selected, &[]);
        assert!(!restricted.pointers_known_equal(&x, &y));
        let withdrawn = context.without_exact_fact(&Proposition::ConditionIs(address, true));
        assert!(!withdrawn.pointers_known_equal(&x, &y));
        assert!(context.pointers_known_equal(&x, &y));
    }

    #[test]
    fn separation_equality_query_uses_offset_classes_without_walking_aliases() {
        for size in [16u64, 64, 256, 1024] {
            let offset = |i| PointerOffsetTerm::Variable(Variable(500_000 + i));
            let mut context = PureFactContext::new();
            for i in 0..size {
                context = context.assume_condition(
                    ConditionTerm::pointer_offset_equal(offset(i), offset(i + 1)),
                    true,
                );
            }
            let left = at_offset(symbolic(499_999), offset(0));
            let right = at_offset(symbolic(499_999), offset(size));
            let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.pointers_proven_equal_ignoring_memory_separation(&left, &right)
            });
            assert!(equal);
            assert!(work < 64, "size={size}, work={work}");
        }
    }

    #[test]
    fn a_small_load_stays_numeric_beside_a_distinct_complete_pointer_read() {
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block(symbolic(901), 16));
        let p = at(symbolic(902), 0);
        let q = at(symbolic(903), 0);
        let small = at(
            PointerBlock::Symbolic(crate::kernel::load_variable_for_cell_with_origin(
                &memory,
                &p,
                crate::kernel::LoadKind::Bits32,
                4,
                &memory,
            )),
            0,
        );
        let pointer = named_load(&memory, &q);
        let mut classes = EqualityGraph::default();
        classes.add_equality(&p, &q);
        assert!(!classes.are_equal(&small, &pointer));
        let widened = named_load(&memory, &p);
        assert_ne!(small, widened);
        assert!(classes.are_equal(&widened, &pointer));
        assert!(!classes.are_equal(&small, &pointer));
        let PointerBlock::Symbolic(variable) = &small.block else {
            unreachable!()
        };
        let Some(Bitvector32Term::MemoryLoad(_, _, kind)) =
            crate::kernel::registered_load_origin_term_for_variable(variable)
        else {
            panic!("the numeric read retains its exact origin")
        };
        assert_eq!(kind, crate::kernel::LoadKind::Bits32);
        assert_eq!(
            crate::kernel::registered_load_bytes_for_variable(variable),
            Some(4)
        );
    }

    #[test]
    fn affine_spelling_order_does_not_depend_on_atom_interning_order() {
        let high = PointerOffsetTerm::Int32Scaled {
            value: Box::new(index(987_002)),
            byte_width: 4,
        };
        let low = PointerOffsetTerm::Int32Scaled {
            value: Box::new(index(987_001)),
            byte_width: 4,
        };
        let high_form = AffineOffset::of(&high).unwrap();
        let low_form = AffineOffset::of(&low).unwrap();
        let sum = high_form.checked_add(&low_form).unwrap();
        assert_eq!(
            sum.to_offset_term(),
            Some(PointerOffsetTerm::add(
                PointerOffsetTerm::add(PointerOffsetTerm::Constant(0), low),
                high,
            ))
        );
    }

    #[test]
    fn affine_input_normalization_is_linear_in_its_explicit_syntax() {
        for size in [16u64, 64, 256, 1024] {
            let mut input = PointerOffsetTerm::Constant(0);
            for i in 0..size {
                input = PointerOffsetTerm::Add(
                    Box::new(input),
                    Box::new(PointerOffsetTerm::Variable(Variable(900_000 + i))),
                );
            }
            let (form, work) = crate::instrumentation::measure_deterministic_work(|| {
                AffineOffset::of(&input).unwrap()
            });
            assert_eq!(form.terms.len(), size as usize);
            assert_eq!(work, 2 * size as usize + 1);
        }
    }

    /// Relabelling work along a chain of `n` equalities is `O(n log n)`:
    /// union by size moves each block at most `log2 n` times. Joining two
    /// balanced halves repeatedly is the worst case for relabelling.
    #[test]
    fn relabelling_work_is_n_log_n_across_sizes() {
        for exponent in [6u32, 8, 10, 12] {
            let n = 1u64 << exponent;
            let (classes, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut classes = EqualityGraph::default();
                let mut width = 1;
                while width < n {
                    let mut start = 0;
                    while start + width < n {
                        classes
                            .add_equality(&at(symbolic(start), 0), &at(symbolic(start + width), 0));
                        start += 2 * width;
                    }
                    width *= 2;
                }
                classes
            });
            assert!(classes.are_equal(&at(symbolic(0), 0), &at(symbolic(n - 1), 0)));
            let bound = 16 * n * u64::from(exponent);
            assert!(
                work as u64 <= bound,
                "n = {n}: relabelled {work} blocks, above 16 n log2 n = {bound}"
            );
            // Balanced joins move a whole class each time, so the charge for
            // the moved members beyond the first is visible, not constant.
            assert!(work as u64 >= n / 2, "n = {n}: only {work} units charged");
        }
    }
}
