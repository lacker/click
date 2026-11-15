//! Trusted kernel equality graph.
//!
//! This graph is part of the trusted kernel. Kernel rules may accept its
//! equality answers directly in the current proof context; it does not emit
//! a separate proof or run proof search. Only established equalities may be
//! added. Branches clone persistent state so local assumptions do not leak.
//!
//! The supported fragment includes typed algebraic model equality,
//! constructor/pure-call congruence, constructor injectivity and distinctness, pointers, affine byte offsets, registered
//! same-state pointer loads, whole-offset equality, int32 addition,
//! unsigned division/remainder, bitwise XOR and same-state int32 loads,
//! plus uint64 equality with congruence over 64-bit arithmetic, bitwise
//! operations and same-state 64-bit loads. Mathematical Integer operations,
//! machine integer unary/binary operators, typed conversions and integer-valued
//! pure-call arguments use these same classes and indexed parent uses.
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
//! payload work is charged separately. Same-state load signatures propagate
//! merges iteratively through indexed parent uses, with no nesting cutoff. An
//! equality between two blocks already in one class adds no base relation.
//! An explicit equality of pointers in the same block instead joins their
//! whole offsets in the term classes.

use super::prelude::*;
use crate::kernel::CompareRelation;

mod admitted;
#[cfg(test)]
mod algebraic_tests;
mod constant_queries;
mod evidence;
#[cfg(test)]
mod fact_congruence_tests;
mod input_queries;
mod inputs;
#[cfg(test)]
mod int32_addition_tests;
#[cfg(test)]
mod int32_load_tests;
#[cfg(test)]
mod int32_tests;
#[cfg(test)]
mod integer_tests;
#[cfg(test)]
mod ordinary_expression_tests;
#[cfg(test)]
mod pointer_call_tests;
#[cfg(test)]
mod scaled_int32_tests;
#[cfg(test)]
mod storage_tests;
#[cfg(test)]
mod uint64_tests;
mod wide_sources;
pub(in crate::kernel) use evidence::scalar_evidence_pair;
pub(in crate::kernel) use inputs::InputKey;
pub(crate) use inputs::{ReadEqualityCheckpoint, ReadEqualityDelta};
#[cfg(test)]
mod machine_relations_tests;
#[cfg(test)]
mod narrow_cast_tests;
#[cfg(test)]
mod narrow_tests;
#[cfg(test)]
mod object_type_tests;
mod pointer_facts;
mod separation;
#[cfg(test)]
mod separation_tests;
#[cfg(test)]
mod shared_index_tests;
mod terms;
pub(in crate::kernel) use terms::constants::fold_arithmetic;

/// A retained, interned machine atom. Equality and ordering use the stable
/// ID; the original term is retained for exact premise support and spelling
/// reconstruction.
#[derive(Clone)]
pub(in crate::kernel) struct MachineAtom(crate::kernel::SharedMachineIntegerTerm);

/// The product `x * K`, the index `x` and the stride `K` of a false `int32`
/// multiplication-overflow condition on `x` and a constant `K` from two to
/// `INT_MAX`, in either operand order: the byte offset of the product and
/// element `x` at stride `K` are then one exact offset.
///
/// Both offsets sign-extend before scaling, so they differ only where the
/// `int32` product wraps. `(char *)p + i * 4` keeps that byte offset when it
/// is formed (`docs/internals/spellability.md#lowering-is-fact-stable`); this
/// is the relation that names it as element `i`. The terms are imported as
/// shared terms, so naming them attaches no spelling to an operand another
/// check holds in shared form. A constant-size match on the condition;
/// `None` for any other condition.
pub(in crate::kernel) fn byte_product_offsets(
    condition: &ConditionTerm,
) -> Option<(
    crate::kernel::SharedMachineIntegerTerm,
    crate::kernel::SharedMachineIntegerTerm,
    i64,
)> {
    let ConditionTerm::Overflows {
        format: MachineIntegerType::Int32,
        op: crate::kernel::OverflowOperation::Multiply,
        left,
        right,
    } = condition
    else {
        return None;
    };
    if left.as_const().is_some() == right.as_const().is_some() {
        return None;
    }
    let product = MachineTerm::multiply(left.as_ref().clone(), right.as_ref().clone());
    let imported = crate::kernel::KernelTermImport::default()
        .machine_arithmetic(MachineIntegerType::Int32, &product)?;
    let product =
        crate::kernel::SharedMachineIntegerTerm::from_shared(MachineIntegerType::Int32, imported)?;
    let (index, stride) = terms::byte_product_operands(&product)?;
    Some((product, index, stride))
}

impl MachineAtom {
    fn new(ty: crate::kernel::MachineIntegerType, value: MachineTerm) -> Self {
        Self(crate::kernel::SharedMachineIntegerTerm::intern(ty, value))
    }
    pub(in crate::kernel) fn from_operand(
        ty: crate::kernel::MachineIntegerType,
        value: crate::kernel::MachineOperandView<'_>,
    ) -> Self {
        Self(value.retain(ty))
    }
    /// Numeric endpoint identity. Exact written carriers remain available via
    /// from_operand; indexed bounds use the same observation for both inputs.
    pub(in crate::kernel) fn from_numeric_operand(
        ty: crate::kernel::MachineIntegerType,
        value: crate::kernel::MachineOperandView<'_>,
    ) -> Self {
        match value {
            crate::kernel::MachineOperandView::Legacy(value) => Self::new(ty, value.clone()),
            crate::kernel::MachineOperandView::Shared(root) => Self(
                crate::kernel::SharedMachineIntegerTerm::observe_shared(
                    ty,
                    root.with_machine_observation_type(ty),
                )
                .expect("typed numeric endpoint"),
            ),
        }
    }
    pub(in crate::kernel) fn uint64(value: MachineTerm) -> Self {
        Self::new(crate::kernel::MachineIntegerType::UInt64, value)
    }
    /// A 32-bit atom, interned by its word: a `uint32` constant is its
    /// word's `Constant` (rule K1), so the two are one class.
    pub(in crate::kernel) fn int32(value: MachineTerm) -> Self {
        Self::new(
            crate::kernel::MachineIntegerType::Int32,
            value.constant_word32(),
        )
    }
    pub(in crate::kernel) fn operand_view(&self) -> crate::kernel::MachineOperandView<'_> {
        self.0.operand_view()
    }
    pub(in crate::kernel) fn retains_written(&self, term: &MachineTerm) -> bool {
        self.0.retained_written_operand() == Some(term)
    }
    pub(in crate::kernel) fn value(&self) -> &MachineTerm {
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
                    if let Some(value) = value.operand_view().word32_constant() {
                        result.constant = result
                            .constant
                            .checked_add(i128::from(value as i32).checked_mul(width)?)?;
                    } else {
                        result.add_atom(
                            OffsetAtom::Int32(MachineAtom::from_operand(
                                crate::kernel::MachineIntegerType::Int32,
                                value.operand_view(),
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
                        value.operand_view().uint64_constant().map(i128::from)
                    } else {
                        value.operand_view().int64_constant().map(i128::from)
                    };
                    if let Some(value) = constant {
                        result.constant = result.constant.checked_add(value.checked_mul(width)?)?;
                    } else {
                        result.add_atom(
                            OffsetAtom::Int64 {
                                value: MachineAtom::from_operand(
                                    if *unsigned {
                                        crate::kernel::MachineIntegerType::UInt64
                                    } else {
                                        crate::kernel::MachineIntegerType::Int64
                                    },
                                    value.operand_view(),
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
                OffsetAtom::Int32(value) => {
                    PointerOffsetTerm::scaled_int32_node(value.value().clone(), coefficient)
                }
                OffsetAtom::Int64 { value, unsigned } => PointerOffsetTerm::scaled_int64_node(
                    value.value().clone(),
                    coefficient,
                    *unsigned,
                ),
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
    pub(in crate::kernel) admitted: admitted::AdmittedInputs,
    state: std::sync::Mutex<EqualityGraphState>,
    // Definitional term annotations, supplied by typed logical-load producers
    // or retained from certified reads after checked expression evaluation.
    // They contain no hypotheses, read authority, or state transport. Like term interning, discovery is shared by evaluation
    // forks; each fork still closes these definitions against its own facts.
    logical_reads: std::sync::Arc<std::sync::Mutex<LogicalPointerReads>>,
    resolve_stored_values: bool,
}

#[derive(Clone, Default)]
struct LogicalPointerReads {
    definitions: crate::persistent::PersistentMap<Pointer, (Pointer, Pointer)>,
    generation: u64,
}

static NEXT_LOGICAL_READ_GENERATION: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(1);

/// Shared clock for checked read equations and structural read definitions.
/// A later definition can invalidate a previously memoized equality miss.
pub(in crate::kernel) fn next_read_definition_generation() -> u64 {
    NEXT_LOGICAL_READ_GENERATION.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

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
pub(crate) fn logical_pointer_read_term(value: &Pointer) -> Option<MachineTerm> {
    if let Some(read) = value.as_loaded_value() {
        return (read.displacement == PointerOffsetTerm::Constant(0)).then(|| {
            MachineTerm::MemoryLoad(
                read.defining_memory,
                Box::new(read.defining_address),
                LoadKind::Int32,
            )
        });
    }
    let application = LOGICAL_POINTER_READS.with(|reads| {
        reads
            .borrow()
            .lock()
            .expect("logical pointer reads")
            .definitions
            .get(value)
            .map(|(application, _)| application.clone())
    });
    let Some(application) = application else {
        // A function read's value is exactly its load variable. Recover its
        // original definition when a restored table predates the read, while
        // preserving any producer definition already retained for the value.
        return match (&value.block, &value.offset) {
            (PointerBlock::FunctionSymbolic(variable), PointerOffsetTerm::Constant(0)) => {
                crate::kernel::registered_load_term_for_variable(variable)
            }
            _ => None,
        };
    };
    let load = application.as_loaded_value()?;
    Some(MachineTerm::MemoryLoad(
        load.defining_memory,
        Box::new(load.defining_address),
        LoadKind::Int32,
    ))
}

impl EqualityGraph {
    /// Naming consumes producer definitions, but cannot ask for stored-value
    /// equations: establishing those equations itself calls the naming walk.
    /// Checking graphs add them after naming has established their authority.
    pub(in crate::kernel) fn for_naming() -> Self {
        Self {
            resolve_stored_values: false,
            ..Self::default()
        }
    }
}

impl Default for EqualityGraph {
    fn default() -> Self {
        Self {
            state: Default::default(),
            admitted: Default::default(),
            logical_reads: LOGICAL_POINTER_READS.with(|reads| reads.borrow().clone()),
            resolve_stored_values: true,
        }
    }
}

impl Clone for EqualityGraph {
    fn clone(&self) -> Self {
        Self {
            logical_reads: self.logical_reads.clone(),
            resolve_stored_values: self.resolve_stored_values,
            admitted: self.admitted.clone(),
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

/// A signature compares only state identities, block identities and an
/// interned affine-offset ID. It never compares states or load trees.
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

#[derive(Clone, Default)]
struct EqualityGraphState {
    registered_shared_pointer_operands: crate::persistent::PersistentSet<u64>,
    separation_sources: crate::persistent::PersistentSet<usize>,
    /// Exact source handles survive closure reconstruction and branch cloning.
    pointer_fact_inputs: terms::PointerFactSources,
    condition_pointer_fact_inputs: terms::PointerFactSources,
    /// Pointer definitions alone must not activate scalar constant discovery.
    has_scalar_inputs: bool,
    terms: terms::TermClasses,
    input_history: Option<std::sync::Arc<inputs::History>>,
    logical_values: crate::persistent::PersistentSet<Pointer>,
    /// Definitions consumed for this selected read. New observations may
    /// name an existing version; seeing the value once does not freeze them.
    logical_pointer_sources:
        crate::persistent::PersistentMap<Pointer, [Option<crate::kernel::SharedMemory>; 3]>,
    /// Compound query dependencies already registered at this metadata
    /// generation. Later producer definitions invalidate a miss lazily.
    logical_query_dependencies: crate::persistent::PersistentMap<Pointer, u64>,
    typed_reads: crate::persistent::PersistentSet<PointerBlock>,
    checked_read_generation: u64,
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
    /// equality: the producer supplies the canonical defining state and
    /// address. Never recover this equation by decoding pointer arithmetic.
    pub(in crate::kernel) fn register_pointer_read_definition(
        &self,
        value: &Pointer,
        memory: &crate::kernel::SharedMemory,
        address: &Pointer,
    ) {
        // A loaded-pointer identity is its own definition.
        if value.as_loaded_value().is_some() {
            return;
        }
        let application = Pointer::loaded_value(memory, address);
        let mut reads = self.logical_reads.lock().expect("logical pointer reads");
        if let Some(existing) = reads.definitions.get(value) {
            assert_eq!(
                &existing.0, &application,
                "conflicting logical pointer definition"
            );
            return;
        }
        reads.definitions = reads
            .definitions
            .with_inserted(value.clone(), (application, address.clone()));
        reads.generation =
            NEXT_LOGICAL_READ_GENERATION.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
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
        definitions
            .max(checked)
            .max(crate::kernel::prelude::load_definition_generation())
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
        // Keep the selected producer terms even when definitions already
        // imply the union: checkpoint replay must register these dependencies.
        state.remember_input(inputs::Input::CheckedRead(left.clone(), right.clone()));
        if state.close(vec![(left.clone(), right.clone())]) || address_changed {
            state.checked_read_generation =
                NEXT_LOGICAL_READ_GENERATION.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
    }

    /// Retain the complete value supplied by the selected typed read producer.
    /// The equality and its memo invalidation stay local to this branch.
    pub(in crate::kernel) fn add_checked_pointer_value_equality(
        &self,
        left: &PointerValue,
        right: &PointerValue,
    ) {
        self.add_checked_read_equality(left.pointer(), right.pointer());
        let mut state = self.state.lock().expect("equality graph");
        state.remember_input(inputs::Input::PointerValue(left.clone(), right.clone()));
        if state.terms.add_pointer_value_equality(left, right) {
            state.checked_read_generation =
                NEXT_LOGICAL_READ_GENERATION.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
        state.close(Vec::new());
    }

    /// Whole pointer reads linked by the selected memory producer share
    /// their origin and opaque extent, independently of the eventual type.
    pub(in crate::kernel) fn add_checked_pointer_read_equality(
        &self,
        left: &Pointer,
        right: &Pointer,
    ) {
        self.add_checked_read_equality(left, right);
        let mut state = self.state.lock().expect("equality graph");
        state.remember_input(inputs::Input::PointerReadValue(left.clone(), right.clone()));
        if state.terms.merge_pointer_read_domains(left, right) {
            state.checked_read_generation =
                NEXT_LOGICAL_READ_GENERATION.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
        state.close(Vec::new());
    }

    pub(in crate::kernel) fn opaque_extent_is_root(&self, origin: &Pointer) -> bool {
        let mut state = self.state.lock().expect("equality graph");
        self.register_logical_read_values(&mut state, [origin]);
        state.terms.opaque_extent_is_root(origin)
    }

    pub(in crate::kernel) fn opaque_extents_equal(&self, left: &Pointer, right: &Pointer) -> bool {
        let mut state = self.state.lock().expect("equality graph");
        self.register_logical_read_values(&mut state, [left, right]);
        state.terms.opaque_extents_equal(left, right)
    }

    fn register_logical_read_values<'a>(
        &self,
        state: &mut EqualityGraphState,
        values: impl IntoIterator<Item = &'a Pointer>,
    ) {
        let mut reads = self.logical_reads.lock().expect("logical pointer reads");
        let mut pending: Vec<_> = values.into_iter().cloned().collect();
        let mut definitions = Vec::new();
        let mut stored_values = Vec::new();
        let mut read_domains = Vec::new();
        while let Some(value) = pending.pop() {
            let direct_read = value.as_loaded_value();
            let sources = direct_read.as_ref().map(|load| {
                [
                    crate::kernel::prelude::canonical_load_projection_source(
                        &load.defining_memory,
                        &load.defining_address,
                    ),
                    crate::kernel::prelude::value_load_origin(
                        &load.defining_memory,
                        &load.defining_address,
                        crate::kernel::C_POINTER_BYTE_WIDTH,
                    ),
                    crate::kernel::prelude::value_load_name(
                        &load.defining_memory,
                        &load.defining_address,
                        crate::kernel::C_POINTER_BYTE_WIDTH,
                    ),
                ]
            });
            if state.logical_values.contains(&value)
                && sources.as_ref().is_none_or(|sources| {
                    state.logical_pointer_sources.get(&value) == Some(sources)
                })
            {
                continue;
            }
            // A pointer read equals the pointer its state stores at the
            // read's address (the read-over-write authority): memory records
            // it, so it is term metadata like a definition, never a fact.
            if self.resolve_stored_values
                && let PointerBlock::LoadedPointer(_) = &value.block
            {
                let read = Pointer {
                    block: value.block.clone(),
                    offset: PointerOffsetTerm::Constant(0),
                };
                if !state.logical_values.contains(&read) {
                    state.logical_values = state.logical_values.with_value(read.clone());
                    // The authority uses the producer-only naming context,
                    // which reads this thread's read table itself.
                    drop(reads);
                    let stored = crate::kernel::eval::pointer_read_over_write_program_value(&read);
                    reads = self.logical_reads.lock().expect("logical pointer reads");
                    if let Some(stored) = stored {
                        pending.push(stored.pointer().clone());
                        definitions.push((read.clone(), stored.pointer().clone()));
                        stored_values.push((read, stored));
                    }
                }
            }
            // Direct pointer-read names carry their own definition instead
            // of a scalar-load entry. Their projection edge is the same
            // unconditional producer metadata used below for scalar names.
            if let Some(load) = direct_read {
                state.logical_values = state.logical_values.with_value(value.clone());
                pending.push(load.defining_address.clone());
                let sources = sources.expect("a direct read has source metadata");
                state.logical_pointer_sources = state
                    .logical_pointer_sources
                    .with_inserted(value.clone(), sources.clone());
                for source in sources.into_iter().flatten() {
                    let source_read = Pointer::loaded_value(&source, &load.defining_address);
                    let application = Pointer {
                        block: source_read.block,
                        offset: load.displacement.clone(),
                    };
                    pending.push(application.clone());
                    read_domains.push((value.clone(), application.clone()));
                    definitions.push((value.clone(), application));
                }
                crate::instrumentation::record_deterministic_work(1);
            }
            if reads.definitions.is_empty() {
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
            // state without searching history or inspecting other reads.
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
        // Projection and selected-width naming preserve the complete pointer
        // read, including its object and extent, not only its address.
        for (read, source) in read_domains {
            state.terms.merge_pointer_read_domains(&read, &source);
        }
        // A complete stored pointer supplies the read's object and bounds,
        // not merely its numeric address. Keep this producer definition in
        // the graph so lowering can retain the read's structural identity.
        for (read, stored) in stored_values {
            state.terms.add_pointer_value_equality(
                &PointerValue::new(read, stored.program_type()),
                &stored,
            );
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

    /// Address lookup for one retained order-bound operand. Candidate discovery
    /// does not manufacture a native pointer or any ownership evidence.
    pub(in crate::kernel) fn indexed_address_class(
        &self,
        base: &Pointer,
        index: crate::kernel::MachineOperandView<'_>,
        successor: bool,
        width: u32,
    ) -> Option<u64> {
        use crate::kernel::{
            KernelTerm, KernelTermImport, MachineBinaryOp, MachineOperandView as V,
        };
        if let V::Legacy(index) = index {
            let index = if successor {
                MachineTerm::add(index.clone(), 1u32.into())
            } else {
                index.clone()
            };
            return self.address_class(&base.offset_by_elements(index, width));
        }
        let V::Shared(index) = index else {
            unreachable!()
        };
        let root = if successor {
            let one = KernelTermImport::default()
                .machine_arithmetic(MachineIntegerType::Int32, &1u32.into())?;
            KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [index.clone(), one],
            )
        } else {
            index.clone()
        };
        let observation =
            crate::kernel::IntegerTerm::Machine(V::Shared(&root).retain(MachineIntegerType::Int32));
        let mut state = self.state.lock().expect("equality graph");
        self.register_expression_operands(&mut state, [], [], [&observation]);
        self.register_logical_read_values(&mut state, [base]);
        state.register_blocks([base.block.clone()]);
        state.register_pointer_address(base);
        let (representative, delta) = state.find(&base.block);
        Some(
            state
                .terms
                .index_address_query(base, &root, width, representative, &delta),
        )
    }

    /// An explicit additive address already registered in this address's
    /// checked class. It selects a base, never bounds or access authority.
    pub(in crate::kernel) fn additive_address(&self, pointer: &Pointer) -> Option<Pointer> {
        let id = self.address_class(pointer)?;
        let mut state = self.state.lock().expect("equality graph");
        state.terms.additive_address(id).or_else(|| {
            state
                .terms
                .additive_offset(&pointer.offset, false)
                .map(|offset| Pointer {
                    block: pointer.block.clone(),
                    offset,
                })
        })
    }

    /// The same checked address in a retained wide-index coordinate, when
    /// the supplying range carries wide bounds. This adds no bound or authority.
    fn wide_additive_address(&self, pointer: &Pointer) -> Option<Pointer> {
        let id = self.address_class(pointer)?;
        let mut state = self.state.lock().expect("equality graph");
        state
            .terms
            .additive_offset(&pointer.offset, true)
            .map(|offset| Pointer {
                block: pointer.block.clone(),
                offset,
            })
            .or_else(|| state.terms.wide_additive_address(id))
            .or_else(|| {
                // A symbolic cursor can be equal to a narrow external address
                // whose offset class retains the wide producer. Same-block
                // pointer equations enter as offset equations, so that wide
                // spelling need not have its own registered address node.
                // Follow the one retained address and its one retained offset;
                // never enumerate aliases in either equality class.
                let spelling = state.terms.additive_address(id)?;
                let offset = state.terms.additive_offset(&spelling.offset, true)?;
                Some(Pointer {
                    block: spelling.block,
                    offset,
                })
            })
    }

    /// A typed pair of byte endpoints used only to select retained resource
    /// occurrences. Congruence follows late endpoint equalities. Equal
    /// footprints do not establish authority, bounds, or initialization.
    pub(in crate::kernel) fn footprint_class(
        &self,
        range: &crate::kernel::MemoryRange,
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

    /// Keep the wide producer's source index when borrowing from a wide range.
    /// The class retains at most one producer per width; no aliases are searched.
    pub(in crate::kernel) fn pointer_at_base_with_wide_index(
        &self,
        pointer: &Pointer,
        base: &Pointer,
    ) -> Option<Pointer> {
        // A native step from a captured cursor has its own wide offset,
        // but aligning that offset alone can select a narrow spelling of
        // the cursor. Retain the cursor's native producer before adding
        // the original step. Bounds still apply to the complete result.
        if pointer.block != base.block
            && matches!(
                pointer.offset,
                PointerOffsetTerm::Int64Scaled { unsigned: true, .. }
            )
        {
            let cursor = Pointer {
                block: pointer.block.clone(),
                offset: PointerOffsetTerm::Constant(0),
            };
            if let Some(spelling) = self.wide_additive_address(&cursor)
                && let Some(aligned) = self.pointer_at_base_with_spelling(&spelling, base, false)
            {
                return Some(Pointer {
                    block: aligned.block,
                    offset: PointerOffsetTerm::add(aligned.offset, pointer.offset.clone()),
                });
            }
        }
        if let Some(spelling) = self.wide_additive_address(pointer)
            && let Some(aligned) = self.pointer_at_base_with_spelling(&spelling, base, false)
        {
            return Some(aligned);
        }
        // A byte lane of a symbolic cursor has a constant offset but no
        // additive producer of its own. Align the cursor's retained producer,
        // then restore the exact byte displacement. Containment still checks
        // the resulting native index and its non-wrapping addition.
        if let Some(bytes) = pointer.offset.as_const().filter(|bytes| *bytes != 0) {
            let cursor = Pointer {
                block: pointer.block.clone(),
                offset: PointerOffsetTerm::Constant(0),
            };
            if let Some(spelling) = self.wide_additive_address(&cursor)
                && let Some(aligned) = self.pointer_at_base_with_spelling(&spelling, base, false)
            {
                return Some(Pointer {
                    block: aligned.block,
                    offset: PointerOffsetTerm::add(
                        aligned.offset,
                        PointerOffsetTerm::Constant(bytes),
                    ),
                });
            }
        }
        self.pointer_at_base(pointer, base)
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
    /// The retained merge prefix's size, without enumerating its history.
    pub(in crate::kernel) fn pointer_merge_count(&self) -> usize {
        self.state
            .lock()
            .expect("equality graph")
            .merge_history
            .as_ref()
            .map_or(0, |node| node.depth)
    }

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

    /// A contradiction maintained as typed classes merge: unequal scalar
    /// constants, including through model getters, or two constructors of
    /// one model class. No term registration or fact scan.
    pub(in crate::kernel) fn has_scalar_constant_conflict(&self) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        self.state
            .lock()
            .expect("equality graph")
            .terms
            .has_scalar_constant_conflict()
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

    /// Ask whether two pointer-typed reads in the same defining state
    /// must have the same value. The application nodes are query terms: this
    /// does not change the representation of either loaded `ProgramValue`.
    /// Callers must supply the addresses and state of actual pointer reads;
    /// decoding a storage-relative pointer value as a load is ambiguous with
    /// ordinary indexed pointer arithmetic.
    #[allow(dead_code, reason = "live comparisons use filed graph bridges")]
    pub(in crate::kernel) fn are_pointer_loads_equal(
        &self,
        memory: &crate::kernel::SharedMemory,
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
        // As for shared scalar queries, retain shared syntax and states.
        // Canonicalize genuinely native inputs before locking; the interner
        // itself never walks memory history.
        let selected = |value: &crate::kernel::SharedMachineIntegerTerm| match value.operand_view()
        {
            crate::kernel::MachineOperandView::Shared(_) => value.clone(),
            crate::kernel::MachineOperandView::Legacy(term) => {
                crate::kernel::SharedMachineIntegerTerm::index(
                    value.ty(),
                    exact_read_comparison_input(term),
                )
            }
        };
        let left = left.map_scaled_operands(selected);
        let right = right.map_scaled_operands(selected);
        let (left, right) = (&left, &right);
        // Offset addition is exact byte arithmetic. Its affine form catches
        // reordering and regrouping without a premise or term-class merge.
        if let (Some(left), Some(right)) = (AffineOffset::of(left), AffineOffset::of(right))
            && left == right
        {
            return true;
        }
        let mut state = self.state.lock().expect("equality graph");
        state.terms.are_equal(left, right)
    }

    pub(in crate::kernel) fn are_algebraic_equal(
        &self,
        left: &AlgebraicTerm,
        right: &AlgebraicTerm,
    ) -> bool {
        let mut state = self.state.lock().expect("equality graph");
        self.register_expression_operands(&mut state, [], [left, right], []);
        let equal = state.terms.are_algebraic_equal(left, right);
        state.close(Vec::new());
        equal
    }

    pub(in crate::kernel) fn designations_equal(&self, left: &Pointer, right: &Pointer) -> bool {
        if left == right {
            return true;
        }
        let mut state = self.state.lock().expect("equality graph");
        self.register_logical_read_values(&mut state, [left, right]);
        state.register_blocks([left.block.clone(), right.block.clone()]);
        let equal = state.terms.designations_equal(left, right);
        state.close(Vec::new());
        equal
    }

    pub(in crate::kernel) fn pointer_value_representative(
        &self,
        value: &PointerValue,
    ) -> PointerValue {
        let mut state = self.state.lock().expect("equality graph");
        self.register_logical_read_values(&mut state, value.pointers());
        state.register_blocks(value.pointers().map(|p| p.block.clone()));
        state.close(Vec::new());
        state.terms.pointer_value_representative(value)
    }

    pub(in crate::kernel) fn add_pointer_value_equality(
        &mut self,
        left: &PointerValue,
        right: &PointerValue,
    ) {
        self.add_equality(left.pointer(), right.pointer());
        if left.pointer().block == right.pointer().block {
            self.add_offset_equality(&left.pointer().offset, &right.pointer().offset);
        }
        let mut state = self.state.lock().expect("equality graph");
        let origins_changed = state
            .terms
            .merge_designations(left.designation(), right.designation());
        let changed = state.terms.add_pointer_value_equality(left, right) || origins_changed;
        state.close(Vec::new());
        if changed {
            state.remember_input(inputs::Input::PointerValue(left.clone(), right.clone()));
        }
    }

    pub(in crate::kernel) fn known_algebraic_constructor(
        &self,
        model: &AlgebraicTerm,
    ) -> Option<AlgebraicTerm> {
        let mut state = self.state.lock().expect("equality graph");
        self.register_expression_operands(&mut state, [], [model], []);
        let constructor = state.terms.known_algebraic_constructor(model);
        state.close(Vec::new());
        constructor
    }

    pub(in crate::kernel) fn add_algebraic_equality(
        &mut self,
        left: &AlgebraicTerm,
        right: &AlgebraicTerm,
    ) -> bool {
        if !left.is_well_formed() || !right.is_well_formed() {
            return false;
        }
        let mut state = self.state.lock().expect("equality graph");
        self.register_expression_operands(&mut state, [], [left, right], []);
        let changed = state.terms.add_algebraic_equality(left, right);
        state.close(Vec::new());
        if changed {
            state.remember_input(inputs::Input::Algebraic(left.clone(), right.clone()));
        }
        changed
    }

    /// Query int32 equality, addition and registered same-state load congruence.
    /// A false answer is unknown. Integer operators use typed operand classes.
    pub(in crate::kernel) fn are_int32_equal(
        &self,
        left: &MachineTerm,
        right: &MachineTerm,
    ) -> bool {
        if left == right {
            return true;
        }
        // Canonicalize before taking the lock, as the uint64 queries do:
        // canonicalizing a load can consult this graph's own read
        // generation, and a std mutex is not reentrant.
        let left = exact_read_comparison_input(left);
        let right = exact_read_comparison_input(right);
        let mut state = self.state.lock().expect("equality graph");
        if left == right {
            return true;
        }
        self.register_int32_operands(&mut state, &left, &right);
        let equal = state.terms.are_int32_equal(&left, &right);
        state.close(Vec::new());
        equal
    }

    /// Register the selected operands directly, retaining shared syntax and
    /// the same logical-read dependencies as the native equality query.
    pub(in crate::kernel) fn are_int32_equal_views(
        &self,
        left: crate::kernel::MachineOperandView<'_>,
        right: crate::kernel::MachineOperandView<'_>,
    ) -> bool {
        use crate::kernel::MachineOperandView as V;
        if let (V::Legacy(a), V::Legacy(b)) = (left, right) {
            return self.are_int32_equal(a, b);
        }
        // Fixed-size leaves already have a native spelling. Preserve the
        // direct scalar route without constructing Integer observations or
        // exporting any shared expression.
        let atoms = [left, right].map(|v| match v {
            V::Legacy(term) => Some(std::borrow::Cow::Borrowed(term)),
            V::Shared(_) => v
                .literal()
                .or_else(|| v.variable().copied().map(MachineTerm::Variable))
                .map(std::borrow::Cow::Owned)
                .or_else(|| v.read_source()),
        });
        if let [Some(left), Some(right)] = &atoms {
            return self.are_int32_equal(left, right);
        }

        let written = [left, right].map(|operand| match operand {
            V::Legacy(term) => Some(exact_read_comparison_input(term)),
            V::Shared(_) => None,
        });
        let observations = [left, right].map(|operand| match operand {
            V::Shared(_) => Some(crate::kernel::IntegerTerm::Machine(
                operand.retain(crate::kernel::MachineIntegerType::Int32),
            )),
            V::Legacy(_) => None,
        });
        let mut state = self.state.lock().expect("equality graph");
        self.register_expression_operands(
            &mut state,
            written.iter().flatten(),
            [],
            observations.iter().flatten(),
        );
        let ids: [u64; 2] = std::array::from_fn(|i| match [left, right][i] {
            V::Legacy(_) => state.terms.int32_class(written[i].as_ref().unwrap()),
            V::Shared(root) => state.terms.shared_int32_class(root),
        });
        state.close(Vec::new());
        state.terms.scalar_class_root(ids[0]) == state.terms.scalar_class_root(ids[1])
    }

    fn register_int32_operands(
        &self,
        state: &mut EqualityGraphState,
        left: &MachineTerm,
        right: &MachineTerm,
    ) {
        if terms::has_machine_operands(left) || terms::has_machine_operands(right) {
            self.register_machine_operands(state, left, right);
        }
    }

    /// Prepare only the addresses used by the selected machine expressions.
    /// Logical read definitions and affine aliases use the same address classes
    /// as pointer queries; no history search or ambient-fact scan is needed.
    fn register_machine_operands(
        &self,
        state: &mut EqualityGraphState,
        left: &MachineTerm,
        right: &MachineTerm,
    ) {
        self.register_expression_operands(state, [left, right], [], []);
    }

    fn expression_pointer_operands<'a>(
        machine: impl IntoIterator<Item = &'a MachineTerm>,
        algebraic: impl IntoIterator<Item = &'a AlgebraicTerm>,
        integer: impl IntoIterator<Item = &'a crate::kernel::IntegerTerm>,
        pointer_calls: impl IntoIterator<Item = &'a SharedPureApplication>,
        shared_seen: &mut crate::persistent::PersistentSet<u64>,
    ) -> Vec<Pointer> {
        enum Work<'a> {
            SharedMachine(&'a crate::kernel::KernelTerm),
            Machine(&'a MachineTerm),
            Algebraic(&'a AlgebraicTerm),
            Integer(&'a crate::kernel::IntegerTerm),
            Value(&'a ProgramValue),
            Argument(&'a PureFunctionArgument),
        }
        let mut pending: Vec<_> = machine.into_iter().map(Work::Machine).collect();
        pending.extend(algebraic.into_iter().map(Work::Algebraic));
        pending.extend(integer.into_iter().map(Work::Integer));
        for call in pointer_calls {
            pending.extend(call.arguments().iter().map(Work::Argument));
        }
        let mut integer_seen = std::collections::BTreeSet::new();
        let mut pointers = Vec::new();
        while let Some(work) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match work {
                Work::Integer(term) => {
                    use crate::kernel::IntegerTerm as I;
                    if !integer_seen.insert(crate::kernel::SharedIntegerTerm::intern(term.clone()))
                    {
                        continue;
                    }
                    match term {
                        I::Machine(value) => {
                            if let Some(term) = value.shared_operand() {
                                pending.push(Work::SharedMachine(term));
                            } else {
                                pending.push(Work::Machine(value.value()));
                            }
                        }
                        I::Negate(value) => pending.push(Work::Integer(value)),
                        I::Add(a, b)
                        | I::Subtract(a, b)
                        | I::Multiply(a, b)
                        | I::TruncatingQuotient(a, b)
                        | I::TruncatingRemainder(a, b) => {
                            pending.extend([Work::Integer(a), Work::Integer(b)])
                        }
                        I::PureFunctionApplication(application) => {
                            pending.extend(application.arguments().iter().map(Work::Argument))
                        }
                        // Match/fold bodies have their own binding scope.
                        _ => {}
                    }
                }
                Work::Algebraic(term) => match &term.node {
                    AlgebraicTermNode::Constructor { fields, .. } => {
                        for field in fields {
                            match field {
                                AlgebraicValue::Program(value) => pending.push(Work::Value(value)),
                                AlgebraicValue::Algebraic(term) => {
                                    pending.push(Work::Algebraic(term))
                                }
                                AlgebraicValue::Integer(term) => pending.push(Work::Integer(term)),
                            }
                        }
                    }
                    AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
                        pending.extend(arguments.iter().map(Work::Argument));
                    }
                    AlgebraicTermNode::MemoryLoad { pointer, .. } => {
                        pointers.push((**pointer).clone());
                    }
                    // Binder-bearing match bodies remain opaque.
                    _ => {}
                },
                Work::Argument(argument) => match argument {
                    PureFunctionArgument::SharedMachine(value) => {
                        if let Some(root) = value.shared_operand() {
                            pending.push(Work::SharedMachine(root));
                        } else {
                            pending.push(Work::Machine(value.value()));
                        }
                    }
                    PureFunctionArgument::Value(value)
                    | PureFunctionArgument::ArrayRef { pointer: value, .. } => {
                        pending.push(Work::Value(value))
                    }
                    PureFunctionArgument::Algebraic(term) => pending.push(Work::Algebraic(term)),
                    PureFunctionArgument::Integer(term) => pending.push(Work::Integer(term)),
                },
                Work::Value(value) => match value {
                    ProgramValue::Pointer(pointer) => pointers.push(pointer.pointer().clone()),
                    ProgramValue::Bool(t)
                    | ProgramValue::Int8(t)
                    | ProgramValue::UInt8(t)
                    | ProgramValue::Int16(t)
                    | ProgramValue::UInt16(t)
                    | ProgramValue::Int32(t)
                    | ProgramValue::UInt32(t)
                    | ProgramValue::Int64(t)
                    | ProgramValue::UInt64(t)
                    | ProgramValue::Int128(t)
                    | ProgramValue::UInt128(t) => pending.push(Work::Machine(t)),
                    ProgramValue::Parameter(term) => pending.push(Work::Algebraic(term)),
                    _ => {}
                },
                Work::SharedMachine(term) => {
                    use crate::kernel::KernelTermNode as N;
                    if shared_seen.contains(&term.id()) {
                        continue;
                    }
                    *shared_seen = shared_seen.with_value(term.id());
                    // Plain shared arithmetic can contain pointers only through
                    // registered load names. Its syntax summary is independent
                    // of this branch, so skip a pointer-free prefix without
                    // installing every node again in each sibling context.
                    // Integer conversions can contain other pointer-bearing
                    // payloads and retain the ordinary scoped walk below.
                    if !term.has_machine_reads()
                        && !term.has_machine_conversions()
                        && crate::kernel::shared_machine_syntax_variables(term, || {
                            crate::instrumentation::record_deterministic_work(1);
                            true
                        })
                        .is_some_and(|variables| {
                            let range = crate::kernel::eval::LOAD_VARIABLE_RANGE;
                            variables
                                .get_greater_than(&Variable(range.start - 1))
                                .is_none_or(|variable| variable.0 >= range.end)
                        })
                    {
                        continue;
                    }
                    match term.node() {
                        N::MachineBinary { arguments, .. } => {
                            pending.extend(arguments.iter().map(Work::SharedMachine))
                        }
                        N::MachineUnary { operand, .. } | N::MachineCast { operand, .. } => {
                            pending.push(Work::SharedMachine(operand))
                        }
                        N::Variable(variable) => {
                            let leaf = MachineTerm::Variable(*variable);
                            if let Some((_, pointer)) =
                                terms::uint64_read(&leaf).or_else(|| terms::int32_read(&leaf))
                            {
                                pointers.push(pointer);
                            }
                        }
                        N::MemoryLoad { .. } => {
                            let MachineTerm::MemoryLoad(_, address, _) =
                                term.machine_read_leaf().expect("read descriptor")
                            else {
                                unreachable!("read descriptor")
                            };
                            pointers.push(address.as_ref().clone());
                        }
                        N::MachineLiteral(_) => {}
                        // Native pointer discovery treats conditionals, Boolean
                        // casts and folds as opaque; do not inspect their children.
                        N::MachineIf { .. } | N::BoolCast { .. } | N::Fold(_) | N::Match(_) => {}
                        N::IntegerToMachine { .. }
                        | N::Legacy(_)
                        | N::Call { .. }
                        | N::PointerAddress { .. } => pending.push(Work::Machine(
                            term.machine_conversion_leaf().expect("conversion leaf"),
                        )),
                        _ => unreachable!("shared machine operand fragment"),
                    }
                }
                Work::Machine(term) => {
                    if let MachineTerm::ClickFunctionApplication { arguments, .. } = term {
                        pending.extend(arguments.iter().map(Work::Argument));
                    } else if let Some((op, a, b)) = term.as_binary()
                        && !op.is_float()
                    {
                        pending.extend([Work::Machine(a), Work::Machine(b)]);
                    } else if let Some((op, value)) = term.as_unary()
                        && !matches!(
                            op,
                            crate::kernel::BitvectorUnaryOp::Float32Negate
                                | crate::kernel::BitvectorUnaryOp::Float64Negate
                        )
                    {
                        pending.push(Work::Machine(value));
                    } else if let MachineTerm::IntegerToMachine { value, .. } = term {
                        pending.push(Work::Integer(value));
                    } else if let Some((_, pointer)) =
                        terms::uint64_read(term).or_else(|| terms::int32_read(term))
                    {
                        pointers.push(pointer);
                    } else if let Some(pointer) = term.address_pointer() {
                        pointers.push(pointer.clone());
                    }
                }
            }
        }
        pointers
    }

    fn register_expression_operands<'a>(
        &self,
        state: &mut EqualityGraphState,
        machine: impl IntoIterator<Item = &'a MachineTerm>,
        algebraic: impl IntoIterator<Item = &'a AlgebraicTerm>,
        integer: impl IntoIterator<Item = &'a crate::kernel::IntegerTerm>,
    ) {
        let pointers = Self::expression_pointer_operands(
            machine,
            algebraic,
            integer,
            [],
            &mut state.registered_shared_pointer_operands,
        );
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
        left: &MachineTerm,
        right: &MachineTerm,
    ) -> bool {
        if left == right {
            return true;
        }
        let left = exact_read_comparison_input(left);
        let right = exact_read_comparison_input(right);
        let mut state = self.state.lock().expect("equality graph");
        self.register_machine_operands(&mut state, &left, &right);
        state.terms.are_uint64_equal(&left, &right)
    }

    /// Files `term` as an endpoint of a recorded true 64-bit equality, so
    /// `wide_equation_endpoints_equal_to` finds it from any equal word.
    pub(in crate::kernel) fn record_wide_equation_endpoint(&self, term: &MachineTerm) {
        let term = exact_read_comparison_input(term);
        let mut state = self.state.lock().expect("equality graph");
        self.register_machine_operands(&mut state, &term, &term);
        state.terms.record_wide_equation_endpoint(&term);
    }

    /// The recorded 64-bit equality endpoints the graph proves equal to
    /// `term`: one class lookup, no scan of the recorded facts.
    fn wide_equation_endpoints_equal_to_written(&self, term: &MachineTerm) -> Vec<MachineTerm> {
        let term = exact_read_comparison_input(term);
        let mut state = self.state.lock().expect("equality graph");
        self.register_machine_operands(&mut state, &term, &term);
        state
            .terms
            .wide_equation_endpoints_equal_to(&term)
            .iter()
            .cloned()
            .collect()
    }

    /// Shared query operands retain their syntax; only the explicitly
    /// recorded source endpoints are returned for citation.
    pub(in crate::kernel) fn wide_equation_endpoints_equal_to(
        &self,
        term: crate::kernel::MachineOperandView<'_>,
    ) -> Vec<MachineTerm> {
        use crate::kernel::MachineOperandView as V;
        match term {
            V::Legacy(term) => self.wide_equation_endpoints_equal_to_written(term),
            V::Shared(root) => {
                let observation = crate::kernel::IntegerTerm::Machine(
                    term.retain(crate::kernel::MachineIntegerType::UInt64),
                );
                let mut state = self.state.lock().expect("equality graph");
                self.register_expression_operands(&mut state, [], [], [&observation]);
                let id = state.terms.shared_uint64_class(root);
                state.close(Vec::new());
                state
                    .terms
                    .wide_equation_endpoints_of_class(id)
                    .iter()
                    .cloned()
                    .collect()
            }
        }
    }

    pub(in crate::kernel) fn uint64_constant(&self, term: &MachineTerm) -> Option<u64> {
        let term = exact_read_comparison_input(term);
        let mut state = self.state.lock().expect("equality graph");
        self.register_machine_operands(&mut state, &term, &term);
        state.terms.uint64_constant(&term)
    }

    pub(in crate::kernel) fn uint64_constant_view(
        &self,
        term: crate::kernel::MachineOperandView<'_>,
    ) -> Option<u64> {
        match term {
            crate::kernel::MachineOperandView::Legacy(term) => self.uint64_constant(term),
            crate::kernel::MachineOperandView::Shared(term) => {
                let mut state = self.state.lock().expect("equality graph");
                let node = state.terms.shared_uint64_class(term);
                state.close(Vec::new());
                state.terms.uint64_constant_of_class(node)
            }
        }
    }

    /// Selected explicit spellings of two numeric addresses. The maintained
    /// class metadata costs one lookup per operand, never a class enumeration.
    /// These spellings authorize byte comparisons, not pointer conversions.
    pub(in crate::kernel) fn numeric_address_spellings(
        &self,
        left: &Pointer,
        right: &Pointer,
    ) -> (Pointer, Pointer) {
        let a = MachineTerm::pointer_address(left.clone());
        let b = MachineTerm::pointer_address(right.clone());
        let mut state = self.state.lock().expect("equality graph");
        self.register_machine_operands(&mut state, &a, &b);
        // Register both before selecting: the second registration can close
        // congruence involving the first.
        state.terms.numeric_address(left);
        state.terms.numeric_address(right);
        (
            state.terms.numeric_address_spelling(left),
            state.terms.numeric_address_spelling(right),
        )
    }

    pub(in crate::kernel) fn add_uint64_equality(
        &mut self,
        left: &MachineTerm,
        right: &MachineTerm,
    ) -> bool {
        let left = exact_read_comparison_input(left);
        let right = exact_read_comparison_input(right);
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
        term: &MachineTerm,
    ) -> Option<(i64, i64)> {
        // See `are_int32_equal`: canonicalize outside the lock.
        let term = exact_read_comparison_input(term);
        let mut state = self.state.lock().expect("equality graph");
        let node = if !state.has_scalar_inputs {
            match state.terms.existing_scalar_interval_node(&term) {
                Some(existing) => existing?,
                None => state.terms.int32_class(&term),
            }
        } else {
            state.terms.int32_class(&term)
        };
        state.close(Vec::new());
        state.terms.signed_int32_interval(node)
    }

    pub(in crate::kernel) fn signed_int32_interval_view(
        &self,
        term: crate::kernel::MachineOperandView<'_>,
    ) -> Option<(i64, i64)> {
        let crate::kernel::MachineOperandView::Shared(term) = term else {
            let crate::kernel::MachineOperandView::Legacy(term) = term else {
                unreachable!()
            };
            return self.signed_int32_interval(term);
        };
        let mut state = self.state.lock().expect("equality graph");
        let node = state.terms.shared_int32_class(term);
        state.close(Vec::new());
        state.terms.signed_int32_interval(node)
    }

    pub(in crate::kernel) fn add_int32_equality_views(
        &mut self,
        left: crate::kernel::MachineOperandView<'_>,
        right: crate::kernel::MachineOperandView<'_>,
    ) -> bool {
        use crate::kernel::MachineOperandView as V;
        if let (V::Legacy(left), V::Legacy(right)) = (left, right) {
            return self.add_int32_equality(left, right);
        }
        // Fixed-size leaves already have a native spelling. Preserve the
        // direct scalar route without constructing Integer observations or
        // exporting any shared expression.
        let atoms = [left, right].map(|v| match v {
            V::Legacy(term) => Some(std::borrow::Cow::Borrowed(term)),
            V::Shared(_) => v
                .literal()
                .or_else(|| v.variable().copied().map(MachineTerm::Variable))
                .map(std::borrow::Cow::Owned)
                .or_else(|| v.read_source()),
        });
        if let [Some(left), Some(right)] = &atoms {
            return self.add_int32_equality(left, right);
        }

        // Retain the scalar admission itself, rather than admitting a second
        // Integer equality and reconstructing its scalar consequence.
        let operands = [left, right].map(|v| v.retain(crate::kernel::MachineIntegerType::Int32));
        let observations = operands.clone().map(crate::kernel::IntegerTerm::Machine);
        let roots = [left, right].map(|v| {
            crate::kernel::KernelTerm::retained_machine_operand(
                crate::kernel::MachineIntegerType::Int32,
                v,
            )
        });
        let mut state = self.state.lock().expect("equality graph");
        self.register_expression_operands(&mut state, [], [], observations.iter());
        state.has_scalar_inputs = true;
        let changed = state.terms.add_shared_word_identity(&roots[0], &roots[1]);
        state.close(Vec::new());
        if changed {
            let [left, right] = operands;
            state.remember_input(inputs::Input::Int32Operands(left, right));
        }
        changed
    }

    /// Admit an already established int32 equality in this proof context.
    pub(in crate::kernel) fn add_int32_equality(
        &mut self,
        left: &MachineTerm,
        right: &MachineTerm,
    ) -> bool {
        // See `are_int32_equal`: canonicalize outside the lock.
        let left = &exact_read_comparison_input(left);
        let right = &exact_read_comparison_input(right);
        let mut state = self.state.lock().expect("equality graph");
        self.register_int32_operands(&mut state, left, right);
        state.has_scalar_inputs = true;
        let changed = state.terms.add_int32_equality(left, right);
        state.close(Vec::new());
        if changed {
            state.remember_input(inputs::Input::Int32(left.clone(), right.clone()));
        }
        changed
    }

    pub(in crate::kernel) fn are_integer_equal(
        &self,
        left: &crate::kernel::IntegerTerm,
        right: &crate::kernel::IntegerTerm,
    ) -> bool {
        let mut state = self.state.lock().expect("equality graph");
        self.register_expression_operands(&mut state, [], [], [left, right]);
        let equal = state.terms.are_integer_equal(left, right);
        state.close(Vec::new());
        equal
    }

    pub(in crate::kernel) fn add_integer_equality(
        &mut self,
        left: &crate::kernel::SharedIntegerTerm,
        right: &crate::kernel::SharedIntegerTerm,
    ) -> bool {
        let mut state = self.state.lock().expect("equality graph");
        self.register_expression_operands(&mut state, [], [], [left.as_ref(), right.as_ref()]);
        let changed = state.terms.add_integer_equality(left, right);
        let modular = state.terms.add_modular_integer_equality(left, right);
        let observation = crate::kernel::machine_integer::comparison::native_comparison_view(
            &ConditionTerm::IntegerEqual(left.clone(), right.clone()),
            true,
        );
        let native = observation
            .as_ref()
            .is_some_and(|view| state.terms.admit_observation_comparison(view));
        state.has_scalar_inputs |= modular
            || (native
                && observation
                    .as_ref()
                    .is_some_and(|view| view.format.format().bits() <= 32));
        let changed = changed || modular || native;
        state.close(Vec::new());
        if changed {
            state.remember_input(inputs::Input::Integer(left.clone(), right.clone()));
        }
        changed
    }

    fn prepare_condition(&self, state: &mut EqualityGraphState, condition: &ConditionTerm) {
        match condition {
            crate::kernel::integer_comparison_condition!(a, b) => {
                self.register_expression_operands(state, [], [], [a.as_ref(), b.as_ref()]);
            }
            ConditionTerm::AlgebraicEqual(a, b) => {
                self.register_expression_operands(state, [], [a.as_ref(), b.as_ref()], []);
            }
            ConditionTerm::PointerValueEqual(a, b) => {
                self.register_logical_read_values(state, a.pointers().chain(b.pointers()));
                state.register_blocks(a.pointers().chain(b.pointers()).map(|p| p.block.clone()));
                // Late value queries need the current address-class bridges,
                // just as raw pointer equality queries do.
                state.register_pointer_address(a.pointer());
                state.register_pointer_address(b.pointer());
                state.close(Vec::new());
            }
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
        // `x * K` does not wrap: the byte offset of the product and the
        // offset of element `x` at stride `K` are one exact offset. The fact
        // is filed by the product; its byte-offset node joins the element
        // offset now if it is registered, or when it is registered.
        if !value && let Some((product, index, stride)) = byte_product_offsets(condition) {
            let state = self.state.get_mut().expect("equality graph");
            state
                .terms
                .admit_defined_byte_product(&product, index, stride);
            state.close(Vec::new());
            return true;
        }
        // A native 8- or 16-bit comparison is also admitted as the `int32`
        // comparison of its widenings, the same fact (rule K8), so a
        // rebuild from the admitted inputs restores both truths.
        if let Some(widened) =
            crate::kernel::machine_integer::comparison::narrow_fact_widening(condition)
        {
            self.add_condition(&widened, value);
        }
        if let ConditionTerm::IntegerEqual(a, b) = condition
            && value
        {
            self.add_integer_equality(a, b);
            return true;
        }
        if let ConditionTerm::IntegerNotEqual(a, b) = condition
            && !value
        {
            self.add_integer_equality(a, b);
            return true;
        }
        // True equations already enter through the typed equality inputs.
        // They need no second truth node or retained support index.
        if value
            && matches!(
                condition,
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::Equal,
                    ..
                } | ConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::Equal,
                    ..
                } | ConditionTerm::PointerEqual(..)
                    | ConditionTerm::PointerValueEqual(..)
                    | ConditionTerm::PointerOffsetEqual(..)
                    | ConditionTerm::AlgebraicEqual(..)
            )
        {
            return false;
        }
        let mut state = self.state.lock().expect("equality graph");
        self.prepare_condition(&mut state, condition);
        if let Some(view) =
            crate::kernel::machine_integer::comparison::native_comparison_view(condition, value)
        {
            state.terms.admit_observation_comparison(&view);
        }
        // A `Bool` value or binder (`design/machine-integers.md`, Stage 5):
        // its class's truth, and for a true equality the merge of its
        // operands (rule L-Eq).
        let supported =
            if condition.is_bool_value_form() || matches!(condition, ConditionTerm::Variable(_)) {
                state.terms.admit_bool_condition(condition, value)
            } else {
                state.terms.admit_condition(condition, value)
            };
        state.close(Vec::new());
        // Predicate truth is scoped state, not a value equality. Resource
        // indexes apply only admitted equations; unrelated comparisons must
        // not invalidate their checkpoints or lengthen their history walks.
        supported
    }

    pub(in crate::kernel) fn knows_int32_add_overflow_views(
        &self,
        operands: [crate::kernel::MachineOperandView<'_>; 2],
        value: bool,
    ) -> bool {
        use crate::kernel::MachineOperandView as V;
        let mut state = self.state.lock().expect("equality graph");
        if !state.terms.may_know_int32_add_overflow(value) {
            return false;
        }
        match operands {
            [V::Legacy(left), V::Legacy(right)] => {
                self.register_machine_operands(&mut state, left, right)
            }
            _ => {
                for operand in operands {
                    if let V::Legacy(term) = operand {
                        self.register_machine_operands(&mut state, term, term);
                    }
                }
            }
        }
        let result = state.terms.knows_int32_add_overflow_views(operands, value);
        state.close(Vec::new());
        result
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
                ConditionTerm::PointerValueEqual(a, b) => {
                    let mut state = self.state.lock().expect("equality graph");
                    self.prepare_condition(&mut state, condition);
                    return state.terms.pointer_values_equal(a, b);
                }
                ConditionTerm::IntegerEqual(a, b) => return self.are_integer_equal(a, b),
                ConditionTerm::AlgebraicEqual(a, b) => return self.are_algebraic_equal(a, b),
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::Equal,
                    left: a,
                    right: b,
                } => return self.are_int32_equal(a, b),
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::Equal,
                    left: a,
                    right: b,
                } => return self.are_uint64_equal(a, b),
                ConditionTerm::PointerEqual(a, b) => return self.are_equal(a, b),
                ConditionTerm::PointerOffsetEqual(a, b) => return self.are_offsets_equal(a, b),
                _ => {}
            }
        }
        if let ConditionTerm::IntegerNotEqual(a, b) = condition
            && !value
        {
            return self.are_integer_equal(a, b);
        }
        // Exact mathematical observations use the same native comparison
        // classes without constructing a boxed native condition.
        if let Some(view) =
            crate::kernel::machine_integer::comparison::native_comparison_view(condition, true)
        {
            let view = if matches!(
                view.relation,
                crate::kernel::machine_integer::Relation::Less
                    | crate::kernel::machine_integer::Relation::LessEqual
            ) {
                view.widened().unwrap_or(view)
            } else {
                view
            };
            let mut state = self.state.lock().expect("equality graph");
            if state.terms.may_know_observation_comparison(&view, value) {
                self.prepare_condition(&mut state, condition);
                let known = state.terms.knows_observation_comparison(&view, value);
                state.close(Vec::new());
                if known {
                    return true;
                }
            }
        }
        let mut state = self.state.lock().expect("equality graph");
        // A `Bool` value's truth can reach its class through a merge, which
        // the admitted-kind filter below does not see.
        if condition.is_bool_value_form() {
            let known = state.terms.knows_bool_condition(condition, value);
            state.close(Vec::new());
            return known;
        }
        if let ConditionTerm::Variable(variable) = condition {
            return state.terms.knows_bool_binder(*variable, value);
        }
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

    /// The affine class containing one selected base, without rebuilding
    /// unrelated admitted merges. Used only for a disposable cold resource
    /// view; published indexes retain their incremental merge protocol.
    pub(in crate::kernel) fn pointer_merges_for_block(
        &self,
        block: &PointerBlock,
    ) -> Vec<PointerClassMerge> {
        let mut state = self.state.lock().expect("equality graph");
        state.register_blocks([block.clone()]);
        let (kept, _) = state.find(block);
        state
            .members
            .get(&kept)
            .into_iter()
            .flat_map(|members| members.iter())
            .map(|(moved, delta)| {
                crate::instrumentation::record_deterministic_work(1);
                PointerClassMerge {
                    moved: moved.clone(),
                    kept: kept.clone(),
                    moved_from_kept: delta.clone(),
                }
            })
            .collect()
    }

    /// The blocks of `block`'s affine class, itself included: the blocks
    /// `pointer_in_block` can move a pointer of this block into. Charged one
    /// unit per member.
    pub(in crate::kernel) fn pointer_class_blocks(
        &self,
        block: &PointerBlock,
    ) -> Vec<PointerBlock> {
        let mut state = self.state.lock().expect("equality graph");
        state.register_blocks([block.clone()]);
        let (representative, _) = state.find(block);
        let mut blocks = vec![representative.clone()];
        if let Some(members) = state.members.get(&representative) {
            for (member, _) in members {
                crate::instrumentation::record_deterministic_work(1);
                blocks.push(member.clone());
            }
        }
        blocks
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

    /// The local scalar storage blocks among a pointer's alias spellings.
    /// Seek the concrete `local:` key interval instead of enumerating opaque
    /// pointer loads in the same class. Offset representability is checked
    /// exactly as in `pointer_spellings`; this only selects blocks to refresh.
    pub(in crate::kernel) fn local_slot_alias_blocks(
        &self,
        pointer: &Pointer,
    ) -> Vec<PointerBlock> {
        let Some(offset) = AffineOffset::of(&pointer.offset) else {
            return Vec::new();
        };
        let mut state = self.state.lock().expect("equality graph");
        state.register_blocks([pointer.block.clone()]);
        let (representative, own) = state.find(&pointer.block);
        let mut blocks = Vec::new();
        let mut push = |member: &PointerBlock, delta: &AffineOffset| {
            if member != &pointer.block
                && member.is_local_block()
                && own
                    .checked_sub(delta)
                    .and_then(|delta| offset.checked_add(&delta))
                    .and_then(|offset| offset.to_offset_term())
                    .is_some()
            {
                blocks.push(member.clone());
            }
        };
        push(&representative, &AffineOffset::default());
        if let Some(members) = state.members.get(&representative) {
            let first = PointerBlock::Concrete("local:".into());
            let mut next = members
                .get(&first)
                .map(|value| (&first, value))
                .or_else(|| members.get_greater_than(&first));
            while let Some((member, delta)) = next {
                if !member.is_local_block() {
                    break;
                }
                push(member, delta);
                next = members.get_greater_than(member);
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
        let is_application = |block: &PointerBlock| match block {
            PointerBlock::LoadedPointer(_) | PointerBlock::PureFunctionApplication(_) => true,
            PointerBlock::Symbolic(variable) | PointerBlock::FunctionSymbolic(variable) => {
                crate::kernel::is_load_variable(variable)
            }
            _ => false,
        };
        let mut pending: Vec<_> = roots.into_iter().filter(is_application).collect();
        let mut equalities = Vec::new();
        let mut calls_seen = std::collections::BTreeSet::new();
        while let Some(block) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if self.loads.contains_key(&block) || self.typed_reads.contains(&block) {
                continue;
            }
            if let PointerBlock::PureFunctionApplication(application) = &block {
                if !calls_seen.insert(application.clone()) {
                    continue;
                }
                for pointer in EqualityGraph::expression_pointer_operands(
                    [],
                    [],
                    [],
                    [application],
                    &mut Default::default(),
                ) {
                    self.register_pointer_address(&pointer);
                    if is_application(&pointer.block) {
                        pending.push(pointer.block);
                    }
                }
                self.register_pointer_address(&Pointer {
                    block,
                    offset: PointerOffsetTerm::Constant(0),
                });
                continue;
            }
            let definition = match &block {
                PointerBlock::LoadedPointer(identity) => {
                    crate::kernel::eval::registered_pointer_load(*identity)
                        .map(|(memory, address)| (memory, address, crate::kernel::LoadKind::Int32))
                }
                // A function pointer read is a typed read of its address,
                // like a loaded data pointer.
                PointerBlock::FunctionSymbolic(variable)
                    if crate::kernel::is_load_variable(variable) =>
                {
                    crate::kernel::registered_load_for_variable(variable).and_then(
                        |(memory, address)| {
                            crate::kernel::registered_load_kind_for_variable(variable)
                                .map(|kind| (memory, address, kind))
                        },
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
            if matches!(
                block,
                PointerBlock::LoadedPointer(_) | PointerBlock::FunctionSymbolic(_)
            ) {
                self.typed_reads = self.typed_reads.with_value(block.clone());
                let address_term = self.register_pointer_address(&address);
                let value_term = self.register_pointer_address(&Pointer {
                    block: block.clone(),
                    offset: PointerOffsetTerm::Constant(0),
                });
                // A function pointer read can meet a function pointer cell
                // (`CellRead::FunctionPointer`). A data pointer read, which
                // every pointer comparison registers, does not look.
                let cell = matches!(block, PointerBlock::FunctionSymbolic(_))
                    .then(|| (memory.clone(), address.clone()));
                self.terms.pointer_read(
                    memory.read_identity(),
                    address_term,
                    kind,
                    value_term,
                    block.clone(),
                    cell,
                );
                if is_application(&address.block) {
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
            if is_application(&address.block) {
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
            equalities.extend(self.terms.take_pointer_value_merges().into_iter().map(
                |(left, right)| {
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
                },
            ));
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
        let moved_deltas = deltas.clone();
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
        self.terms.join_block_classes(&moved, &kept, &moved_deltas);
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

impl EqualityGraph {
    pub(in crate::kernel) fn scalar_constant_class(
        &self,
        term: &MachineTerm,
    ) -> Option<(u64, crate::kernel::assumptions::SignedConstantResolution)> {
        if !self.state.lock().expect("equality graph").has_scalar_inputs {
            return None;
        }
        let term = exact_read_comparison_input(term);
        let mut state = self.state.lock().expect("equality graph");
        let node = match state.terms.existing_scalar_atom(&term) {
            Some(existing) => existing?,
            None => state.terms.int32_class(&term),
        };
        state.close(Vec::new());
        Some((
            state.terms.scalar_class_root(node),
            state.terms.scalar_constant_of_class(node),
        ))
    }
    /// A bounded checking reading: consult the root's word class and at most
    /// two levels of selected operands. Registration retains shared prefixes; leaf
    /// witnesses follow class unions and branch cloning, never a fact-set scan.
    /// This constructs a comparison form, not a replacement for the stored term.
    pub(in crate::kernel) fn checking_word32_root(
        &self,
        term: &crate::kernel::KernelTerm,
        direct_constant: impl Fn(&crate::kernel::KernelTerm) -> Option<u32>,
    ) -> crate::kernel::KernelTerm {
        use crate::kernel::{KernelTermImport, KernelTermNode};
        let mut state = self.state.lock().expect("equality graph");
        let node = state.terms.shared_int32_class(term);
        state.close(Vec::new());
        let leaf = |state: &mut EqualityGraphState,
                    term: &crate::kernel::KernelTerm,
                    child: bool| {
            let ty = MachineIntegerType::from_program_type(match term.ty() {
                crate::kernel::KernelType::Program(ty) => *ty,
                _ => return None,
            })?;
            if ty.format().bits() != 32 {
                return None;
            }
            let node = state.terms.shared_int32_class(term);
            state.close(Vec::new());
            let value = state.terms.scalar_leaf_of_class(node)?;
            // Child substitution uses the written equality policy of the
            // native simplifier, not an arbitrary transitive class constant.
            if child
                && let Some(bits) = value.as_const()
                && crate::kernel::MachineOperandView::Shared(term).word32_constant() != Some(bits)
                && direct_constant(term) != Some(bits)
            {
                return None;
            }
            KernelTermImport::default().machine_arithmetic(ty, &value)
        };
        if state.terms.scalar_leaf_of_class(node).is_some() {
            return leaf(&mut state, term, false).unwrap_or_else(|| term.clone());
        }
        let KernelTermNode::MachineBinary {
            format,
            operator,
            arguments,
        } = term.node()
        else {
            return term.clone();
        };
        if format.format().bits() != 32 {
            return term.clone();
        }
        // Read the written child operation, not the representative of its
        // equality class: which term was queried first must not select whether
        // a two-level cancellation is available.
        use crate::kernel::MachineBinaryOp as Op;
        let same = |state: &mut EqualityGraphState,
                    a: &crate::kernel::KernelTerm,
                    b: &crate::kernel::KernelTerm| {
            let a = state.terms.shared_int32_class(a);
            let b = state.terms.shared_int32_class(b);
            state.close(Vec::new());
            state.terms.scalar_class_root(a) == state.terms.scalar_class_root(b)
        };
        let cancellation = |state: &mut EqualityGraphState,
                            inner: &crate::kernel::KernelTerm,
                            other: &crate::kernel::KernelTerm| {
            let KernelTermNode::MachineBinary {
                format,
                operator: inner_op,
                arguments: pair,
            } = inner.node()
            else {
                return None;
            };
            if format.format().bits() != 32 {
                return None;
            }
            match (*operator, *inner_op) {
                (Op::Add, Op::Subtract) if same(state, &pair[1], other) => Some(pair[0].clone()),
                (Op::Subtract, Op::Add) | (Op::BitwiseXor, Op::BitwiseXor) => {
                    if same(state, &pair[0], other) {
                        Some(pair[1].clone())
                    } else if same(state, &pair[1], other) {
                        Some(pair[0].clone())
                    } else {
                        None
                    }
                }
                _ => None,
            }
        };
        let cancelled = cancellation(&mut state, &arguments[0], &arguments[1]).or_else(|| {
            matches!(operator, Op::Add | Op::BitwiseXor)
                .then(|| cancellation(&mut state, &arguments[1], &arguments[0]))
                .flatten()
        });
        if let Some(cancelled) = cancelled {
            state.terms.add_shared_word_identity(term, &cancelled);
            state.close(Vec::new());
            return leaf(&mut state, &cancelled, false).unwrap_or(cancelled);
        }
        let updated = arguments
            .each_ref()
            .map(|child| leaf(&mut state, child, true).unwrap_or_else(|| child.clone()));
        if &updated == arguments {
            return term.clone();
        }
        let result = MachineIntegerType::from_program_type(match term.ty() {
            crate::kernel::KernelType::Program(ty) => *ty,
            _ => return term.clone(),
        })
        .expect("machine operand");
        crate::kernel::KernelTerm::machine_binary_shared_as(result, *format, *operator, updated)
    }

    pub(in crate::kernel) fn scalar_normalization_class_view(
        &self,
        term: crate::kernel::MachineOperandView<'_>,
    ) -> Option<(u64, crate::kernel::assumptions::SignedConstantResolution)> {
        match term {
            crate::kernel::MachineOperandView::Legacy(term) => self.scalar_constant_class(term),
            crate::kernel::MachineOperandView::Shared(term) => {
                let mut state = self.state.lock().expect("equality graph");
                let node = state.terms.shared_int32_class(term);
                state.close(Vec::new());
                Some((
                    state.terms.scalar_class_root(node),
                    state.terms.scalar_constant_of_class(node),
                ))
            }
        }
    }

    /// The constant an atom's class is known to equal, read without
    /// interning: an atom the graph has no node for has had no equality
    /// filed about it, and a compound term is not looked up. One lookup and
    /// no change to the graph, so a run's work does not depend on what an
    /// earlier query interned.
    pub(in crate::kernel) fn known_atom_constant(&self, term: &MachineTerm) -> Option<i64> {
        let term = exact_read_comparison_input(term);
        let state = self.state.lock().expect("equality graph");
        if !state.has_scalar_inputs {
            return None;
        }
        let node = state.terms.existing_scalar_atom(&term)??;
        match state.terms.scalar_constant_of_class(node) {
            crate::kernel::assumptions::SignedConstantResolution::Known(value) => Some(value),
            _ => None,
        }
    }

    pub(in crate::kernel) fn scalar_conditional_members(&self, id: u64) -> Vec<MachineAtom> {
        self.state
            .lock()
            .expect("equality graph")
            .terms
            .scalar_conditional_members(id)
    }
}

/// A raw descriptor of an already registered read is the same selected input
/// as its retained name. Preserve that exact state before applying the
/// legacy comparison form to inputs that do not already have an identity.
fn exact_read_comparison_input(term: &MachineTerm) -> MachineTerm {
    if let MachineTerm::MemoryLoad(memory, pointer, kind) = term
        && crate::kernel::eval::is_selected_scalar_read(memory, pointer, *kind)
    {
        term.clone()
    } else {
        crate::kernel::canonical_term(term)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pointer_fact_search_uses_admission_order_across_allocations_and_rebuilds() {
        let domain = crate::kernel::PointerValue::new(
            Pointer::symbolic(Variable(985_000)),
            crate::kernel::ProgramType::Int32Pointer,
        );
        let origin = domain
            .opaque_extent()
            .expect("an unseen pointer has an opaque domain")
            .clone();
        let mut sources = (1..=4)
            .map(|end| {
                std::sync::Arc::new(crate::kernel::ExecutionPureFact::certified(
                    domain
                        .opaque_coverage_fact(&crate::kernel::MemoryRange::new(
                            at(symbolic(985_100), 0),
                            MachineTerm::constant(0),
                            MachineTerm::constant(end),
                        ))
                        .expect("coverage names the opaque domain"),
                ))
            })
            .collect::<Vec<_>>();
        // Force admission to oppose allocation-address order, irrespective of
        // the allocator's layout. The old address-keyed index reverses this.
        sources.sort_by_key(|source| std::cmp::Reverse(std::sync::Arc::as_ptr(source) as usize));
        let expected = sources
            .iter()
            .map(|source| source.proposition().clone())
            .collect::<Vec<_>>();
        let graph = EqualityGraph::default();
        for source in &sources {
            graph.adjust_pointer_fact(source, true);
            graph.adjust_pointer_fact(source, true); // Exact re-admission is idempotent.
        }
        assert_eq!(graph.subobject_coverage_facts(&origin), expected);
        let fork = graph.clone();
        fork.adjust_pointer_fact(&sources[1], false);
        assert_eq!(
            fork.subobject_coverage_facts(&origin),
            vec![
                expected[0].clone(),
                expected[2].clone(),
                expected[3].clone()
            ]
        );
        assert_eq!(graph.subobject_coverage_facts(&origin), expected);
        fork.clear_proposition_pointer_facts();
        assert!(fork.subobject_coverage_facts(&origin).is_empty());
        assert_eq!(graph.subobject_coverage_facts(&origin), expected);
    }

    fn symbolic(id: u64) -> PointerBlock {
        PointerBlock::Symbolic(Variable(id))
    }

    fn at(block: PointerBlock, offset: i64) -> Pointer {
        Pointer {
            block,
            offset: PointerOffsetTerm::Constant(offset),
        }
    }

    fn index(id: u64) -> MachineTerm {
        MachineTerm::Variable(Variable(id))
    }

    // Retained zero-displacement spellings may share their base's class.
    // Alignment against an unrelated supplier must not expand that cycle.
    #[test]
    fn additive_spelling_alignment_is_bounded_when_its_base_is_equal() {
        let mut graph = EqualityGraph::default();
        let base = Pointer::symbolic(Variable(999_101));
        let index = MachineTerm::Variable(Variable(999_102));
        let address = base.offset_by_elements(index, 4);
        assert!(graph.add_equality(&base, &address));
        let unrelated = Pointer::symbolic(Variable(999_103));
        assert!(graph.pointer_at_base(&base, &unrelated).is_none());
    }

    #[test]
    fn wide_borrow_alignment_uses_native_displacement_after_a_mixed_prefix() {
        let mut graph = EqualityGraph::default();
        let bytes = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(index(999_400), 1),
        };
        let mixed = bytes
            .offset_by_typed_elements(index(999_401), 1, true, true)
            .offset_by_elements(index(999_402), 1);
        let wide = bytes.offset_by_typed_elements(index(999_403), 1, true, true);
        assert!(graph.add_offset_equality(&mixed.offset, &wide.offset));
        assert_eq!(
            graph.pointer_at_base_with_wide_index(&mixed, &bytes),
            Some(wide)
        );
    }

    #[test]
    fn retained_offset_spelling_does_not_identify_unrelated_pointer_blocks() {
        let mut graph = EqualityGraph::default();
        let base = Pointer::symbolic(Variable(999_300));
        let bytes = Pointer::symbolic(Variable(999_301));
        let computed = base.offset_by_elements(index(999_302), 1);
        let wide = bytes.offset_by_typed_elements(index(999_303), 1, true, true);
        assert!(graph.add_offset_equality(&computed.offset, &wide.offset));
        assert!(!graph.are_equal(&computed, &wide));
        assert!(
            graph
                .pointer_at_base_with_wide_index(&computed, &bytes)
                .is_none()
        );
    }

    #[test]
    fn offsets_spelled_differently_share_one_normal_form() {
        let nested = PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::scaled_int32_node(index(7), 4)),
                Box::new(PointerOffsetTerm::Constant(4)),
            )),
            Box::new(PointerOffsetTerm::Constant(4)),
        );
        let flat = PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::Constant(8)),
            Box::new(PointerOffsetTerm::scaled_int32_node(index(7), 4)),
        );
        assert_eq!(AffineOffset::of(&nested), AffineOffset::of(&flat));
        let other_index = PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::Constant(8)),
            Box::new(PointerOffsetTerm::scaled_int32_node(index(8), 4)),
        );
        assert_ne!(AffineOffset::of(&flat), AffineOffset::of(&other_index));
    }

    #[test]
    fn a_constant_index_folds_with_its_sign() {
        let minus_one = PointerOffsetTerm::scaled_int32_node(MachineTerm::constant(u32::MAX), 8);
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

    fn at_offset(block: PointerBlock, offset: PointerOffsetTerm) -> Pointer {
        Pointer { block, offset }
    }

    #[test]
    fn affine_offset_equality_reaches_same_block_solve() {
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
            context
                .selected_for_test()
                .decide_selected_condition(&ConditionTerm::pointer_equal(
                    at_offset(base.clone(), nested.clone()),
                    at_offset(base.clone(), reordered.clone()),
                )),
            Some(true)
        );
        assert!(!context.equality_graph.are_offsets_equal(&nested, &wrong));
        assert_ne!(
            context
                .selected_for_test()
                .decide_selected_condition(&ConditionTerm::pointer_equal(
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
        let restricted = branch.restricted_to_facts(&[(offset_fact, true)], &[]);
        assert!(!restricted.equality_graph.are_offsets_equal(&x, &z));

        let mut cross_block = EqualityGraph::default();
        cross_block.add_equality(&left, &at_offset(symbolic(11_024), y.clone()));
        assert!(!cross_block.are_offsets_equal(&x, &y));
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
        let restricted = branch.restricted_to_facts(&[(offset_fact, true)], &[]);
        assert!(!restricted.equality_graph.are_equal(&left, &right));

        let mut displaced = EqualityGraph::default();
        displaced.add_offset_equality(&x, &y);
        displaced.add_equality(&at(a.clone(), 0), &at(b.clone(), 8));
        assert!(!displaced.are_equal(&at_offset(a, x), &at_offset(b, y)));
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
        let max = MachineTerm::constant(i32::MAX as u32);
        let wrapped = at_offset(
            base.clone(),
            PointerOffsetTerm::scale_int32(
                MachineTerm::add(max.clone(), MachineTerm::constant(1)),
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
    fn a_symbolic_displacement_carries_through_the_class() {
        let mut classes = EqualityGraph::default();
        let element = Pointer {
            block: symbolic(2),
            offset: PointerOffsetTerm::scaled_int32_node(index(9), 4),
        };
        classes.add_equality(&at(symbolic(1), 0), &element);
        let next = Pointer {
            block: symbolic(2),
            offset: PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::scaled_int32_node(index(9), 4)),
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
            offset: PointerOffsetTerm::scaled_int32_node(index(9), 8),
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
        let memory = crate::kernel::intern_memory(Memory::new().with_block(p.block.clone(), 8));
        let later = crate::kernel::intern_memory(
            memory
                .memory()
                .clone()
                .store(p.clone(), ProgramValue::Int32(MachineTerm::constant(7))),
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
        let byte_view = PointerValue::new(from_p.clone(), ProgramType::Int32Pointer)
            .with_type(ProgramType::UInt8Pointer);
        assert_eq!(byte_view.pointer(), &from_p);
        let displaced = from_p.offset_by_bytes(8);
        assert_eq!(
            displaced.as_loaded_value().unwrap().displacement,
            PointerOffsetTerm::Constant(8)
        );
        assert!(from_p.has_symbolic_block());
        let cell_bits = MachineTerm::MemoryLoad(
            memory.clone(),
            Box::new(p.clone()),
            crate::kernel::LoadKind::Int32,
        );
        // A pointer read of the cell names the typed read, whatever the
        // pointee width; an address indexed by the cell's scalar does not.
        let named_read = Pointer::loaded(&cell_bits.clone()).unwrap();
        assert_eq!(Pointer::loaded(&cell_bits.clone()).unwrap(), named_read);
        let read = named_read.as_loaded_value().expect("a typed pointer read");
        assert_eq!(read.defining_address, p);
        assert_eq!(read.displacement, PointerOffsetTerm::Constant(0));
        let scalar_indexed_address = p.offset_by_elements(cell_bits, 8);
        assert!(scalar_indexed_address.as_loaded_value().is_none());
        assert_ne!(scalar_indexed_address, named_read);
        assert_ne!(scalar_indexed_address, from_p);
        let ProgramValue::Pointer(execution_value) = memory
            .memory()
            .symbolic_pointer_load(&p, ProgramType::Int64Pointer)
        else {
            panic!("pointer-typed load must produce a pointer value");
        };
        assert_eq!(execution_value.pointer(), &named_read);

        // A scalar read of the same cell may have a four-byte interpretation;
        // it cannot determine whether the distinct pointer-load name enters
        // the graph's eight-byte application index.
        crate::kernel::load_variable_for_cell_with_origin(
            &memory,
            &p,
            crate::kernel::LoadKind::Int32,
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
        let memory = crate::kernel::intern_memory(Memory::new());
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

    // Whole-offset equality is not an affine block merge. All read consumers
    // must nevertheless see it, including when learned after registration.
    #[test]
    fn typed_reads_follow_whole_address_congruence() {
        let memory = crate::kernel::intern_memory(Memory::new());
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
            let changed = crate::kernel::intern_memory(
                memory
                    .memory()
                    .clone()
                    .store(p.clone(), ProgramValue::Int32(MachineTerm::constant(7))),
            );
            assert!(!graph.are_equal(&left, &Pointer::loaded_value(&changed, &q)));
        }
    }

    #[test]
    fn loads_at_equal_pointers_of_one_state_are_one_value() {
        let memory =
            crate::kernel::intern_memory(crate::kernel::Memory::new().with_block(symbolic(51), 16));
        // A later state where the cell `p` addresses was written.
        let other_memory = crate::kernel::intern_memory(memory.memory().clone().store(
            at(symbolic(41), 0),
            ProgramValue::Int32(MachineTerm::constant(7)),
        ));
        let name = |memory: &crate::kernel::SharedMemory, address: Pointer| {
            PointerBlock::Symbolic(crate::kernel::load_variable_for_cell_with_origin(
                memory,
                &address,
                crate::kernel::LoadKind::Int32,
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
        let memory = crate::kernel::intern_memory(
            crate::kernel::Memory::new().with_block(symbolic(101), 16),
        );
        let p = at(symbolic(102), 0);
        let q = at(symbolic(103), 0);
        let load = |address: &Pointer| {
            at(
                PointerBlock::Symbolic(crate::kernel::load_variable_for_cell_with_origin(
                    &memory,
                    address,
                    crate::kernel::LoadKind::Int32,
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
    fn cross_state_load_equality_requires_a_supplied_conclusion() {
        // The store goes through a pointer structure cannot separate from the
        // cell; only a stated disequality does. The two reads therefore get
        // different names, and only the path's facts make them one value.
        let cell = Pointer {
            block: PointerBlock::Heap(95_001),
            offset: PointerOffsetTerm::Constant(0),
        };
        let other = at(symbolic(95_003), 0);
        let before = crate::kernel::Memory::new().with_block(PointerBlock::Heap(95_001), 16);
        let after = before
            .clone()
            .store(other.clone(), ProgramValue::Int32(MachineTerm::constant(3)));
        let name = |memory: &crate::kernel::Memory| {
            let memory = crate::kernel::intern_memory(memory.clone());
            PointerBlock::Symbolic(crate::kernel::load_variable_for_cell_with_origin(
                &memory,
                &cell,
                crate::kernel::LoadKind::Int32,
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
        let separated = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_equal(other, cell.clone()), false);
        let load = |pointer: &Pointer| {
            let PointerBlock::Symbolic(variable) = &pointer.block else {
                unreachable!()
            };
            let (memory, address) =
                crate::kernel::registered_load_origin_for_variable(variable).unwrap();
            MachineTerm::MemoryLoad(memory, Box::new(address), crate::kernel::LoadKind::Int32)
        };
        assert!(!crate::kernel::reasoning::memory_resolution::bitvector_terms_proven_equal_for_memory_resolution(
            &load(&left), &load(&right), &separated,
        ));
        // Separation alone is not an implicit request to reconstruct a frame.
        // An explicit preservation proof supplies the read equality itself.
        let supplied =
            separated.assume_condition(ConditionTerm::equal(load(&left), load(&right)), true);
        assert!(crate::kernel::reasoning::memory_resolution::bitvector_terms_proven_equal_for_memory_resolution(
            &load(&left), &load(&right), &supplied,
        ));
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

    fn named_load(memory: &SharedMemory, address: &Pointer) -> Pointer {
        at(
            PointerBlock::Symbolic(crate::kernel::load_variable_for_cell_with_origin(
                memory,
                address,
                crate::kernel::LoadKind::Int32,
                8,
                memory,
            )),
            0,
        )
    }

    #[test]
    fn load_congruence_is_independent_of_equality_insertion_order() {
        let memory = crate::kernel::intern_memory(Memory::new().with_block(symbolic(201), 16));
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
        let memory = crate::kernel::intern_memory(Memory::new().with_block(symbolic(301), 16));
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
        let memory = crate::kernel::intern_memory(Memory::new().with_block(symbolic(401), 16));
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
    fn restricted_context_drops_derived_load_equalities() {
        let memory = crate::kernel::intern_memory(Memory::new().with_block(symbolic(801), 16));
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
        assert!(context.pointers_known_equal(&x, &y));
    }

    #[test]
    fn a_small_load_is_not_a_pointer_load_and_can_later_be_registered_as_one() {
        let memory = crate::kernel::intern_memory(Memory::new().with_block(symbolic(901), 16));
        let p = at(symbolic(902), 0);
        let q = at(symbolic(903), 0);
        let small = at(
            PointerBlock::Symbolic(crate::kernel::load_variable_for_cell_with_origin(
                &memory,
                &p,
                crate::kernel::LoadKind::Int32,
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
        assert_eq!(small, widened);
        assert!(classes.are_equal(&widened, &pointer));
    }

    #[test]
    fn affine_spelling_order_does_not_depend_on_atom_interning_order() {
        let high = PointerOffsetTerm::scaled_int32_node(index(987_002), 4);
        let low = PointerOffsetTerm::scaled_int32_node(index(987_001), 4);
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
    fn shifted_raw_pointer_reads_import_only_exact_retained_dependencies() {
        let base = Pointer::symbolic(Variable(51_401));
        let address = base.offset_by_bytes(8);
        let memory = crate::kernel::intern_memory(Memory::new());
        let ProgramValue::Pointer(raw) = memory
            .memory()
            .symbolic_pointer_load(&address, ProgramType::Int32Pointer)
        else {
            panic!("typed pointer read");
        };
        let named = Pointer::loaded_value(&memory, &address);
        let model = Pointer::symbolic(Variable(51_402));
        let mut graph = EqualityGraph::default();
        let sibling = graph.clone();
        graph.add_equality(&named, &model);
        // Do not query the undisplaced raw pointer first: that would import
        // its definition and mask a missed dependency of the field address.
        assert!(graph.are_equal(
            &raw.pointer().offset_by_bytes(24),
            &model.offset_by_bytes(24)
        ));
        assert!(!sibling.are_equal(
            &raw.pointer().offset_by_bytes(24),
            &model.offset_by_bytes(24)
        ));
        let cell_bits = MachineTerm::MemoryLoad(
            memory.clone(),
            Box::new(address.clone()),
            crate::kernel::LoadKind::Int32,
        );
        // The pointee width does not enter a read's identity; displacement does.
        let other_stride = Pointer::loaded(&cell_bits.clone()).unwrap();
        assert_eq!(&other_stride, raw.pointer());
        assert!(!graph.are_equal(
            &other_stride.offset_by_bytes(16),
            &model.offset_by_bytes(24)
        ));
        // Arithmetic resemblance supplies no read identity: an address
        // indexed by the cell's scalar is not the read.
        let scalar_indexed = base.offset_by_elements(cell_bits, 8);
        assert!(!graph.are_equal(
            &scalar_indexed.offset_by_bytes(24),
            &model.offset_by_bytes(24)
        ));
        let later = crate::kernel::intern_memory(memory.memory().clone().store(
            address.clone(),
            ProgramValue::UInt64(MachineTerm::int64_constant(9)),
        ));
        let ProgramValue::Pointer(changed) = later
            .memory()
            .symbolic_pointer_load(&address, ProgramType::Int32Pointer)
        else {
            panic!("typed pointer read");
        };
        assert!(!graph.are_equal(
            &changed.pointer().offset_by_bytes(24),
            &model.offset_by_bytes(24)
        ));
    }

    #[test]
    fn scalar_read_congruence_imports_shifted_raw_pointer_dependencies() {
        let address = Pointer::symbolic(Variable(51_411)).offset_by_bytes(8);
        let memory = crate::kernel::intern_memory(Memory::new());
        let ProgramValue::Pointer(raw) = memory
            .memory()
            .symbolic_pointer_load(&address, ProgramType::Int32Pointer)
        else {
            panic!("typed pointer read");
        };
        let named = Pointer::loaded_value(&memory, &address);
        let model = Pointer::symbolic(Variable(51_412));
        let read = |pointer: &Pointer| {
            crate::kernel::eval::declare_load_access_width(pointer, 4);
            crate::kernel::canonical_term(&MachineTerm::MemoryLoad(
                memory.clone(),
                Box::new(pointer.clone()),
                crate::kernel::LoadKind::Int32,
            ))
        };
        let source = read(&raw.pointer().offset_by_bytes(24));
        let target = read(&model.offset_by_bytes(24));
        let expected = MachineTerm::constant(7);
        for read in [&source, &target] {
            assert!(matches!(read, MachineTerm::MemoryLoad(..)));
            assert_eq!(
                crate::kernel::eval::scalar_read_observation(
                    crate::kernel::MachineOperandView::Legacy(read)
                )
                .unwrap()
                .bytes,
                4
            );
        }
        let mut graph = EqualityGraph::default();
        graph.add_equality(&named, &model);
        let sibling = graph.clone();
        // Neither a pointer comparison nor a redundant field-address fact
        // may be needed before the scalar producer and consumer connect.
        graph.add_int32_equality(&source, &expected);
        let equal = graph.are_int32_equal(&target, &expected);
        assert!(equal, "source={source:?}; target={target:?}");
        assert!(!sibling.are_int32_equal(&target, &expected));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../scaling_tests/kernel/equality_graph/tests.rs");
    }
}

#[cfg(test)]
mod boolean_cast_dependency_tests {
    use super::*;
    #[test]
    fn shared_boolean_cast_pointer_discovery_keeps_native_opacity() {
        use crate::kernel::{KernelTermExport, KernelTermImport, SharedMachineIntegerTerm};
        let _session = crate::kernel::VerificationSession::enter();
        let native = MachineTerm::bool_cast(
            MachineIntegerType::Int32,
            ConditionTerm::PointerEqual(
                Box::new(Pointer::symbolic(Variable(999462))),
                Box::new(Pointer::symbolic(Variable(999463))),
            ),
        );
        let root = KernelTermImport::default()
            .machine_arithmetic(MachineIntegerType::Int32, &native)
            .unwrap();
        let exports = KernelTermExport::machine_export_count();
        for argument in [
            PureFunctionArgument::Value(ProgramValue::Int32(native)),
            PureFunctionArgument::SharedMachine(
                SharedMachineIntegerTerm::from_shared(MachineIntegerType::Int32, root).unwrap(),
            ),
        ] {
            let application =
                SharedPureApplication::intern("boolean_pointer_discovery".into(), vec![argument]);
            assert!(
                EqualityGraph::expression_pointer_operands(
                    [],
                    [],
                    [],
                    [&application],
                    &mut Default::default()
                )
                .is_empty()
            );
        }
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}
