use super::ExecutionFacts;
use super::api::{
    int8, int16, int32, normalize_exact_memory_loads_in_pointer_offset, uint8, uint16, uint32,
};
use super::memory_provenance::{AtomicMemoryLoadEqualityEvidence, PointerOffsetEqualityEvidence};
use super::reasoning::{
    bitvector_terms_proven_equal_for_memory_resolution, bitvector_variable, collect_or_cases,
    instantiate_range_fold_step, memory_snapshots_proven_equal_at_pointer,
    pointers_proven_distinct_for_memory_resolution, pointers_proven_equal_for_memory_resolution,
    resource_context_has_read, signed_bitvector_constant, signed_i64_bitvector_constant,
};
use crate::persistent::{PersistentMap, PersistentSet};
use std::collections::{BTreeMap, BTreeSet};
use std::hash::{Hash, Hasher};
use std::sync::{Arc, OnceLock};

pub(crate) const SAME_OBJECT_PREDICATE_NAME: &str = "__click_same_object";
pub(crate) const MUTEX_HELD_PREDICATE_NAME: &str = "__click_mutex_held";

mod contracts;
#[cfg(test)]
mod memory_construction_tests;
mod native_input_identity;
#[cfg(test)]
pub(crate) use contracts::memory_range_byte_count_guards;
pub(crate) use contracts::{
    MemoryRangeExtent, element_count_limit_constrains_int32, is_unnamed_footprint_base,
    memory_range_byte_count, memory_range_byte_count_extent, memory_range_element_count,
    memory_range_element_count_guards, memory_range_element_count_limit,
    memory_range_extent_guard_spellings, memory_range_extent_guards, narrow_range_constant,
    scaled_extent_element_width, stated_loadable_extent_guard_spellings,
    stated_loadable_extent_guards, stated_separation_extent_bounds,
    stated_separation_extent_guards, wide_loadable_element_count, wide_range_bounds,
};
mod integer;
mod machine_integer;
pub use machine_integer::{
    MachineIntegerConstant, MachineIntegerDivisionError, MachineIntegerFormat, MachineIntegerWidth,
};
mod remainder_rules;
pub use integer::{
    AlgebraicIntegerMatchArm, IntegerComparisonOperator, IntegerRangeFoldIndex, IntegerTerm,
    SharedIntegerApplication, SharedIntegerRangeEndpoint, SharedIntegerTerm, SharedPureApplication,
};
pub use integer::{MachineIntegerType, SharedMachineIntegerTerm, SignedDefinedWidth};
mod alias_candidates;
pub(crate) use alias_candidates::{AliasCandidates, BlockKeyed};
mod cell_store;
#[cfg(debug_assertions)]
pub(crate) use cell_store::CHECKED_RUN_SLOTS;
pub use cell_store::CellRun;
pub(crate) use cell_store::{
    CellStore, DroppedRunSlots, IndexIntervals, RuleAnswer, RunValueMode, SlotSet, cell_run_value,
    offset_stem_and_constant,
};
mod derivations;
mod initialized_bytes;
mod observed_population_families;
pub(crate) use initialized_bytes::InitializedBytes;
mod array_domains;
mod memory_state;
pub(crate) use observed_population_families::ObservedPopulationFamilies;
mod persistent_map;
pub(in crate::kernel) use memory_state::CallKeptOwnership;
pub use memory_state::CallKeptRanges;
pub(crate) use memory_state::{
    BlockRegistriesState, block_is_never_address_taken_local, capture_block_registries,
    clear_block_alignment_registry, clear_never_address_taken_locals,
    never_address_taken_locals_key, register_aggregate_argument_source, register_block_alignment,
    registered_aggregate_argument_source, registered_block_alignment,
    registered_block_alignment_charged, restore_block_registries, set_never_address_taken_locals,
    withdraw_never_address_taken_locals,
};
pub(crate) use persistent_map::{SnapshotMap, SnapshotMapChange, SnapshotSet};
mod iterated;
pub use iterated::{CIteratedGuard, CIteratedMemory};
mod memory_equality_index;
mod resource_algebra;
mod term_operations;
mod term_shape;
pub(super) use derivations::*;
pub(crate) use memory_state::resource_context_has_symbolic_range_read;
pub use memory_state::value_independent_click_memory;
pub(super) use resource_algebra::*;
pub(in crate::kernel) use term_operations::round_right_to_even;
pub(in crate::kernel) use term_operations::{
    int64_add_interval_fits, int64_subtract_interval_fits,
};
pub(crate) use term_operations::{listed_premise_holds, proposition_holds_without_facts};
pub(crate) use term_shape::{BitvectorBinaryOp, BitvectorComparisonOp, BitvectorUnaryOp};

pub(super) const C_POINTER_BYTE_WIDTH: u32 = 8;

/// The allocator alignment guaranteed by the LP64 heap model.  Keep this
/// beside the pointer primitives so all proof routes use the same profile
/// contract rather than copying a second limit into a checker.
pub(crate) const HEAP_ALLOCATION_ALIGNMENT: u64 = 16;

/// A symbolic identity. Source and execution producers still use the numeric
/// constructor below; a kernel-allocated fresh variable carries a private
/// origin as well, so even a caller-constructed variable with the same number
/// cannot capture it. Names in source text are separate from this identity.
#[derive(Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Variable {
    number: (u64,),
    origin: VariableOrigin,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
enum VariableOrigin {
    Ordinary,
    KernelFresh,
}

impl std::fmt::Debug for Variable {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.origin {
            VariableOrigin::Ordinary => formatter.debug_tuple("Variable").field(&self.0).finish(),
            VariableOrigin::KernelFresh => formatter
                .debug_tuple("FreshVariable")
                .field(&self.0)
                .finish(),
        }
    }
}

// Preserve existing numeric producers while migrating them to explicit kernel
// allocation APIs. New code needing a fresh identity uses `allocate_fresh`
// rather than inventing another numeric band. Variable(n) cannot forge one.
#[allow(non_snake_case)]
pub const fn Variable(number: u64) -> Variable {
    Variable {
        number: (number,),
        origin: VariableOrigin::Ordinary,
    }
}

impl std::ops::Deref for Variable {
    type Target = (u64,);

    fn deref(&self) -> &Self::Target {
        &self.number
    }
}

impl Variable {
    /// Mint a free symbolic identity. This stream is process-wide so nested
    /// and forked checks cannot reuse an identity; the private origin
    /// separates it from every existing numeric producer. New kernel rules
    /// that need arbitrary fresh variables should allocate through here.
    pub(in crate::kernel) fn allocate_fresh() -> Option<Self> {
        use std::sync::atomic::{AtomicU64, Ordering};
        static NEXT: AtomicU64 = AtomicU64::new(1 << 44);
        let number = NEXT
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |number| {
                (number < (1 << 45)).then_some(number + 1)
            })
            .ok()?;
        Some(Self {
            number: (number,),
            origin: VariableOrigin::KernelFresh,
        })
    }
}

/// A derived index of the free symbolic variables stored in one immutable
/// execution-environment version. Environment clones share the initialized
/// index; builder-style mutations replace it along with the changed semantic
/// storage.
#[derive(Clone, Default)]
pub(super) struct CExecutionEnvironmentVariableIndex {
    values: Arc<OnceLock<Arc<BTreeSet<Variable>>>>,
    #[cfg(test)]
    builds: Arc<std::sync::atomic::AtomicUsize>,
}

impl CExecutionEnvironmentVariableIndex {
    pub(super) fn get_or_init(
        &self,
        initialize: impl FnOnce() -> BTreeSet<Variable>,
    ) -> Arc<BTreeSet<Variable>> {
        self.values
            .get_or_init(|| {
                #[cfg(test)]
                self.builds
                    .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                Arc::new(initialize())
            })
            .clone()
    }

    #[cfg(test)]
    pub(super) fn build_count(&self) -> usize {
        self.builds.load(std::sync::atomic::Ordering::Relaxed)
    }

    #[cfg(test)]
    pub(super) fn shares_storage_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.values, &other.values)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Sort {
    Condition,
    Bitvector32,
    Bitvector64,
    Integer,
    PointerOffset,
    CType,
    CInt32,
    CInt64,
    CMachineInteger(MachineIntegerType),
    CPointer(CType),
    CValue,
    Sequence(Option<CType>),
    Algebraic(AlgebraicType),
    CMemory,
    CState,
    CStatementOutcome,
    CFunctionOutcome,
}

impl Sort {
    pub fn machine_integer(integer_type: MachineIntegerType) -> Self {
        match integer_type {
            MachineIntegerType::Int32 => Self::CInt32,
            MachineIntegerType::Int64 => Self::CInt64,
            other => Self::CMachineInteger(other),
        }
    }

    pub fn machine_integer_type(&self) -> Option<MachineIntegerType> {
        match self {
            Self::CInt32 => Some(MachineIntegerType::Int32),
            Self::CInt64 => Some(MachineIntegerType::Int64),
            Self::CMachineInteger(integer_type) => Some(*integer_type),
            _ => None,
        }
    }
}

/// What a load term reads at its address: how many bytes, and how the term
/// represents them.
///
/// A load term is a value, and the value a read returns depends on more than
/// the address. A one-byte read of `0xFF` is `-1` as `int8` and `255` as
/// `uint8`, and an `int32` read at the same address returns all four bytes.
/// Two reads of one address therefore name one value only when they agree on
/// this kind.
///
/// Four- and eight-byte integer reads keep their two's-complement bit pattern
/// in the term and let the `CValue` wrapper choose the interpretation, so a
/// signed and an unsigned read of that width are one kind (`Bits32`,
/// `Bits64`). Narrower reads store the extended value, which signedness
/// changes, so they keep it. Wide 128-bit reads also keep signedness: their
/// checked constant payloads retain the exact machine format. This profile
/// supports exact typed cells, not signed/unsigned memory reinterpretation.
/// Floating-point reads are kinds of their own.
///
/// Pointer reads retain their complete eight-byte interpretation independently
/// of the bitvector proxy used to name their address.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum LoadKind {
    Int8,
    UInt8,
    Int16,
    UInt16,
    Bits32,
    Bits64,
    /// Wide loads retain signedness because their constant payloads are typed.
    Int128,
    UInt128,
    Float32,
    Float64,
    Pointer,
}

impl LoadKind {
    /// The kind of a C read of `value_type`, for every scalar or pointer type
    /// a load can have. `_Bool` reads its byte unsigned and normalizes it.
    pub fn of_type(value_type: CType) -> Option<Self> {
        Some(match value_type {
            CType::Bool | CType::UInt8 => Self::UInt8,
            CType::Int8 => Self::Int8,
            CType::Int16 => Self::Int16,
            CType::UInt16 => Self::UInt16,
            CType::Int32 | CType::UInt32 => Self::Bits32,
            CType::Int64 | CType::UInt64 => Self::Bits64,
            CType::Int128 => Self::Int128,
            CType::UInt128 => Self::UInt128,
            CType::Float32 => Self::Float32,
            CType::Float64 => Self::Float64,
            CType::Void
            | CType::Int8Array(_)
            | CType::Int16Array(_)
            | CType::Int32Array(_)
            | CType::UInt8Array(_)
            | CType::UInt16Array(_)
            | CType::UInt32Array(_)
            | CType::Int128Array(_)
            | CType::Int64Array(_)
            | CType::UInt128Array(_)
            | CType::UInt64Array(_)
            | CType::Float32Array(_)
            | CType::Float64Array(_)
            | CType::PointerArray(_, _) => return None,
            _ if value_type.is_pointer() => Self::Pointer,
            _ => return None,
        })
    }

    /// The kind of read that returns exactly `value`, a cell's stored value:
    /// a read of any other kind at the cell's address does not.
    pub fn of_value(value: &CValue) -> Option<Self> {
        Some(match value {
            CValue::Void => return None,
            CValue::Bool(_) | CValue::UInt8(_) => Self::UInt8,
            CValue::Int8(_) => Self::Int8,
            CValue::Int16(_) => Self::Int16,
            CValue::UInt16(_) => Self::UInt16,
            CValue::Int32(_) | CValue::UInt32(_) => Self::Bits32,
            CValue::Int64(_) | CValue::UInt64(_) | CValue::PointerInteger(_) => Self::Bits64,
            CValue::Int128(_) => Self::Int128,
            CValue::UInt128(_) => Self::UInt128,
            CValue::Float32(_) => Self::Float32,
            CValue::Float64(_) => Self::Float64,
            CValue::Pointer(_) => Self::Pointer,
        })
    }

    /// Whether a read of this kind returns `value` itself, where `value` is
    /// what a cell holds. This is the one test every route that answers a
    /// load term from a cell or a store applies.
    pub fn reads_value(self, value: &CValue) -> bool {
        Self::of_value(value) == Some(self)
    }

    /// The value a read of this kind returns from a cell holding `value`:
    /// the value itself when the read is of its kind, or, for a one- or
    /// two-byte read of a cell of the same width and the other signedness,
    /// the same bits reinterpreted ([`CType::read_cell`]). A 32- or 64-bit
    /// kind already reads a cell of either signedness as its bits.
    pub(crate) fn read_cell(self, value: &CValue) -> Option<CValue> {
        if self.reads_value(value) {
            return Some(value.clone());
        }
        match self {
            Self::Int8 => CType::Int8.read_cell(value),
            Self::UInt8 => CType::UInt8.read_cell(value),
            Self::Int16 => CType::Int16.read_cell(value),
            Self::UInt16 => CType::UInt16.read_cell(value),
            _ => None,
        }
    }

    /// Width when the kind is known but no typed producer recorded an access.
    /// The read kind preserves its intrinsic storage width.
    #[cfg(test)]
    pub(crate) fn unrecorded_access_byte_width(self) -> u32 {
        self.byte_width()
    }

    /// How many bytes a read of this kind returns.
    pub fn byte_width(self) -> u32 {
        match self {
            Self::Int8 | Self::UInt8 => 1,
            Self::Int16 | Self::UInt16 => 2,
            Self::Bits32 | Self::Float32 => 4,
            Self::Bits64 | Self::Float64 | Self::Pointer => 8,
            Self::Int128 | Self::UInt128 => 16,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Bitvector32Term {
    Constant(u32),
    /// Signed 64-bit constants are kept in the same term arena as the
    /// original 32-bit terms so equality, substitution, and memory-load
    /// indexing continue to share one checked representation.
    Int64Constant(i64),
    /// Unsigned 64-bit constants retain all 64 bits; interpreting these as a
    /// signed value would lose the distinction above `i64::MAX`.
    UInt64Constant(u64),
    /// Checked wide payload; never truncated into the legacy 32/64-bit carriers.
    MachineIntegerConstant(MachineIntegerConstant),
    Variable(Variable),
    Add(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Subtract(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Multiply(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Divide(Box<Bitvector32Term>, Box<Bitvector32Term>),
    UnsignedDivide(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Remainder(Box<Bitvector32Term>, Box<Bitvector32Term>),
    UnsignedRemainder(Box<Bitvector32Term>, Box<Bitvector32Term>),
    ShiftLeft(Box<Bitvector32Term>, Box<Bitvector32Term>),
    ArithmeticShiftRight(Box<Bitvector32Term>, Box<Bitvector32Term>),
    LogicalShiftRight(Box<Bitvector32Term>, Box<Bitvector32Term>),
    BitwiseAnd(Box<Bitvector32Term>, Box<Bitvector32Term>),
    BitwiseOr(Box<Bitvector32Term>, Box<Bitvector32Term>),
    BitwiseXor(Box<Bitvector32Term>, Box<Bitvector32Term>),
    BitwiseNot(Box<Bitvector32Term>),
    If {
        condition: Box<ConditionTerm>,
        then_term: Box<Bitvector32Term>,
        else_term: Box<Bitvector32Term>,
    },
    RangeFold {
        start: Box<Bitvector32Term>,
        end: Box<Bitvector32Term>,
        initial: Box<Bitvector32Term>,
        accumulator: Variable,
        item: Variable,
        body: Box<Bitvector32Term>,
    },
    /// An opaque application retained across one-step unfolding of a total
    /// pure Click function at symbolic arguments.
    PureFunctionApplication {
        name: String,
        arguments: Vec<Bitvector32Term>,
    },
    /// A Click function application remains a logical term until a checked
    /// function-unfold step exposes its definition. Unlike the legacy
    /// bitvector-only application above, Click arguments retain their source
    /// sorts and state-indexed array references.
    ClickFunctionApplication {
        name: String,
        arguments: Vec<PureFunctionArgument>,
    },
    /// Exhaustive elimination of an algebraic value. Unknown scrutinees stay
    /// symbolic; a checked reduction selects an arm only after the scrutinee
    /// is known to be a constructor.
    AlgebraicMatch {
        scrutinee: Box<AlgebraicTerm>,
        arms: Vec<AlgebraicBitvectorMatchArm>,
    },
    /// The value a read of `LoadKind` at the pointer returns in the snapshot.
    /// The kind is part of the load's identity: two reads of one address
    /// that differ in width or, below four bytes, in signedness return
    /// different values, so they are different terms. See [`LoadKind`].
    MemoryLoad(SharedCMemory, Box<Pointer>, LoadKind),
    /// The 64-bit integer representation of a non-null object pointer under
    /// the LP64 profile.  The term keeps the exact source pointer, so the
    /// integer carries provenance: a cast back recovers that pointer, and two
    /// addresses compare as their pointers do.  No arithmetic on the term
    /// is interpreted as address arithmetic; tag bits are handled by checked
    /// rewrites on top of this term.
    PointerAddress(Box<Pointer>),
    IntegerToMachine {
        value: SharedIntegerTerm,
        destination: MachineIntegerType,
    },
    /// Explicit integral conversion modulo the destination width. Wide casts
    /// retain the operand's format instead of reusing a legacy word cast.
    MachineIntegerCast {
        value: Box<Bitvector32Term>,
        source: MachineIntegerType,
        destination: MachineIntegerType,
    },
    Int64From32(Box<Bitvector32Term>),
    UInt64From32(Box<Bitvector32Term>),
    /// Unsigned narrowing modulo 2^32; the operand is a signed or unsigned
    /// 64-bit integer and the result is a 32-bit bitvector.
    UInt32From64(Box<Bitvector32Term>),
    Int64FromUInt32(Box<Bitvector32Term>),
    UInt64FromInt32(Box<Bitvector32Term>),
    UInt64FromInt64(Box<Bitvector32Term>),
    Int64Add(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Int64Subtract(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Int64Multiply(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Int64Divide(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Int64Remainder(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Int64ShiftLeft(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Int64ArithmeticShiftRight(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Int64BitwiseAnd(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Int64BitwiseOr(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Int64BitwiseXor(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Int64BitwiseNot(Box<Bitvector32Term>),
    UInt64Add(Box<Bitvector32Term>, Box<Bitvector32Term>),
    UInt64Subtract(Box<Bitvector32Term>, Box<Bitvector32Term>),
    UInt64Multiply(Box<Bitvector32Term>, Box<Bitvector32Term>),
    UInt64Divide(Box<Bitvector32Term>, Box<Bitvector32Term>),
    UInt64Remainder(Box<Bitvector32Term>, Box<Bitvector32Term>),
    UInt64ShiftLeft(Box<Bitvector32Term>, Box<Bitvector32Term>),
    UInt64LogicalShiftRight(Box<Bitvector32Term>, Box<Bitvector32Term>),
    UInt64BitwiseAnd(Box<Bitvector32Term>, Box<Bitvector32Term>),
    UInt64BitwiseOr(Box<Bitvector32Term>, Box<Bitvector32Term>),
    UInt64BitwiseXor(Box<Bitvector32Term>, Box<Bitvector32Term>),
    UInt64BitwiseNot(Box<Bitvector32Term>),
    Float32Negate(Box<Bitvector32Term>),
    Float32Binary {
        operator: CFloatBinaryOperator,
        left: Box<Bitvector32Term>,
        right: Box<Bitvector32Term>,
    },
    Float64Negate(Box<Bitvector32Term>),
    Float64Binary {
        operator: CFloatBinaryOperator,
        left: Box<Bitvector32Term>,
        right: Box<Bitvector32Term>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum PointerOffsetTerm {
    Constant(i64),
    Variable(Variable),
    Add(Box<PointerOffsetTerm>, Box<PointerOffsetTerm>),
    Int32Scaled {
        value: Box<Bitvector32Term>,
        byte_width: i64,
    },
    /// A pointer displacement formed from a signed or unsigned 64-bit
    /// element index.  The term arena intentionally remains shared with the
    /// existing 32-bit form, but its numeric interpretation must not be
    /// truncated to `i32` while forming an address.
    Int64Scaled {
        value: Box<Bitvector32Term>,
        byte_width: i64,
        unsigned: bool,
    },
}

impl PointerOffsetTerm {
    /// Maps scaled index values without changing the offset expression.
    pub(crate) fn map_scaled_values(
        &self,
        mut map: impl FnMut(&Bitvector32Term) -> Bitvector32Term,
    ) -> Self {
        enum Task<'a> {
            Visit(&'a PointerOffsetTerm),
            Add,
        }
        let mut pending = vec![Task::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match task {
                Task::Visit(Self::Add(left, right)) => {
                    pending.push(Task::Add);
                    pending.push(Task::Visit(right));
                    pending.push(Task::Visit(left));
                }
                Task::Visit(Self::Int32Scaled { value, byte_width }) => {
                    values.push(Self::Int32Scaled {
                        value: Box::new(map(value)),
                        byte_width: *byte_width,
                    });
                }
                Task::Visit(Self::Int64Scaled {
                    value,
                    byte_width,
                    unsigned,
                }) => {
                    values.push(Self::Int64Scaled {
                        value: Box::new(map(value)),
                        byte_width: *byte_width,
                        unsigned: *unsigned,
                    });
                }
                Task::Visit(other) => values.push(other.clone()),
                Task::Add => {
                    let right = values.pop().expect("right offset");
                    let left = values.pop().expect("left offset");
                    values.push(Self::Add(Box::new(left), Box::new(right)));
                }
            }
        }
        values.pop().expect("one mapped offset")
    }

    /// Every bitvector term nested in this offset, for traversals that must
    /// look through a pointer embedded in a term.
    pub(crate) fn scaled_values(&self) -> Vec<&Bitvector32Term> {
        let mut values = Vec::new();
        let mut pending = vec![self];
        while let Some(offset) = pending.pop() {
            match offset {
                Self::Constant(_) | Self::Variable(_) => {}
                Self::Add(left, right) => {
                    pending.push(left);
                    pending.push(right);
                }
                Self::Int32Scaled { value, .. } | Self::Int64Scaled { value, .. } => {
                    values.push(value.as_ref());
                }
            }
        }
        values
    }

    /// Visits each scaled index of this offset, left to right.
    pub(crate) fn for_each_scaled_value(&self, mut visit: impl FnMut(&Bitvector32Term)) {
        self.any_scaled_value(|value| {
            visit(value);
            false
        });
    }

    /// Whether some scaled index of this offset satisfies `test`, asked left to
    /// right and stopping at the first that does.
    pub(crate) fn any_scaled_value(&self, mut test: impl FnMut(&Bitvector32Term) -> bool) -> bool {
        fn walk(
            offset: &PointerOffsetTerm,
            test: &mut impl FnMut(&Bitvector32Term) -> bool,
        ) -> bool {
            match offset {
                PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => false,
                PointerOffsetTerm::Add(left, right) => walk(left, test) || walk(right, test),
                PointerOffsetTerm::Int32Scaled { value, .. }
                | PointerOffsetTerm::Int64Scaled { value, .. } => test(value),
            }
        }
        walk(self, &mut test)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ConditionTerm {
    Constant(bool),
    Variable(Variable),
    /// Logical equality of immutable algebraic values, not a C comparison.
    AlgebraicEqual(Box<AlgebraicTerm>, Box<AlgebraicTerm>),
    Bitvector32SignedLessThan(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32SignedLessEqual(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32SignedGreaterThan(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32SignedGreaterEqual(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32Equal(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32SignedAddOverflows(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32SignedSubtractOverflows(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32SignedMultiplyOverflows(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32SignedDivideOverflows(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32SignedShiftLeftOverflows(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64SignedLessThan(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64SignedLessEqual(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64SignedGreaterThan(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64SignedGreaterEqual(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64UnsignedLessThan(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64UnsignedLessEqual(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64UnsignedGreaterThan(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64UnsignedGreaterEqual(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64Equal(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64SignedAddOverflows(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64SignedSubtractOverflows(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64SignedMultiplyOverflows(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64SignedDivideOverflows(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector64SignedShiftLeftOverflows(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Float32(CFloatCondition),
    Float64(CFloatCondition),
    PointerOffsetEqual(Box<PointerOffsetTerm>, Box<PointerOffsetTerm>),
    PointerEqual(Box<Pointer>, Box<Pointer>),
    IntegerLessThan(SharedIntegerTerm, SharedIntegerTerm),
    IntegerLessEqual(SharedIntegerTerm, SharedIntegerTerm),
    IntegerGreaterThan(SharedIntegerTerm, SharedIntegerTerm),
    IntegerGreaterEqual(SharedIntegerTerm, SharedIntegerTerm),
    IntegerEqual(SharedIntegerTerm, SharedIntegerTerm),
    IntegerNotEqual(SharedIntegerTerm, SharedIntegerTerm),
}

/// Matches every two-operand 32-bit [`ConditionTerm`] (the comparisons and the
/// overflow tests), binding the operands to `$left` and `$right`.
macro_rules! binary_bitvector32_condition {
    ($left:pat, $right:pat) => {
        $crate::kernel::ConditionTerm::Bitvector32SignedLessThan($left, $right)
            | $crate::kernel::ConditionTerm::Bitvector32SignedLessEqual($left, $right)
            | $crate::kernel::ConditionTerm::Bitvector32SignedGreaterThan($left, $right)
            | $crate::kernel::ConditionTerm::Bitvector32SignedGreaterEqual($left, $right)
            | $crate::kernel::ConditionTerm::Bitvector32Equal($left, $right)
            | $crate::kernel::ConditionTerm::Bitvector32SignedAddOverflows($left, $right)
            | $crate::kernel::ConditionTerm::Bitvector32SignedSubtractOverflows($left, $right)
            | $crate::kernel::ConditionTerm::Bitvector32SignedMultiplyOverflows($left, $right)
            | $crate::kernel::ConditionTerm::Bitvector32SignedDivideOverflows($left, $right)
            | $crate::kernel::ConditionTerm::Bitvector32SignedShiftLeftOverflows($left, $right)
    };
}
pub(crate) use binary_bitvector32_condition;

/// Matches every two-operand 64-bit [`ConditionTerm`], signed and unsigned,
/// binding the operands to `$left` and `$right`.
macro_rules! binary_bitvector64_condition {
    ($left:pat, $right:pat) => {
        $crate::kernel::ConditionTerm::Bitvector64SignedLessThan($left, $right)
            | $crate::kernel::ConditionTerm::Bitvector64SignedLessEqual($left, $right)
            | $crate::kernel::ConditionTerm::Bitvector64SignedGreaterThan($left, $right)
            | $crate::kernel::ConditionTerm::Bitvector64SignedGreaterEqual($left, $right)
            | $crate::kernel::ConditionTerm::Bitvector64UnsignedLessThan($left, $right)
            | $crate::kernel::ConditionTerm::Bitvector64UnsignedLessEqual($left, $right)
            | $crate::kernel::ConditionTerm::Bitvector64UnsignedGreaterThan($left, $right)
            | $crate::kernel::ConditionTerm::Bitvector64UnsignedGreaterEqual($left, $right)
            | $crate::kernel::ConditionTerm::Bitvector64Equal($left, $right)
            | $crate::kernel::ConditionTerm::Bitvector64SignedAddOverflows($left, $right)
            | $crate::kernel::ConditionTerm::Bitvector64SignedSubtractOverflows($left, $right)
            | $crate::kernel::ConditionTerm::Bitvector64SignedMultiplyOverflows($left, $right)
            | $crate::kernel::ConditionTerm::Bitvector64SignedDivideOverflows($left, $right)
            | $crate::kernel::ConditionTerm::Bitvector64SignedShiftLeftOverflows($left, $right)
    };
}
pub(crate) use binary_bitvector64_condition;

/// Matches every two-operand bitvector [`ConditionTerm`] of either width.
macro_rules! binary_bitvector_condition {
    ($left:pat, $right:pat) => {
        $crate::kernel::binary_bitvector32_condition!($left, $right)
            | $crate::kernel::binary_bitvector64_condition!($left, $right)
    };
}
pub(crate) use binary_bitvector_condition;

/// Matches every two-operand 32-bit [`Bitvector32Term`] operation, binding the operands to `$left`
/// and `$right`.
macro_rules! binary_bitvector32_term {
    ($left:pat, $right:pat) => {
        $crate::kernel::Bitvector32Term::Add($left, $right)
            | $crate::kernel::Bitvector32Term::Subtract($left, $right)
            | $crate::kernel::Bitvector32Term::Multiply($left, $right)
            | $crate::kernel::Bitvector32Term::Divide($left, $right)
            | $crate::kernel::Bitvector32Term::UnsignedDivide($left, $right)
            | $crate::kernel::Bitvector32Term::Remainder($left, $right)
            | $crate::kernel::Bitvector32Term::UnsignedRemainder($left, $right)
            | $crate::kernel::Bitvector32Term::BitwiseAnd($left, $right)
            | $crate::kernel::Bitvector32Term::BitwiseOr($left, $right)
            | $crate::kernel::Bitvector32Term::BitwiseXor($left, $right)
            | $crate::kernel::Bitvector32Term::ShiftLeft($left, $right)
            | $crate::kernel::Bitvector32Term::ArithmeticShiftRight($left, $right)
            | $crate::kernel::Bitvector32Term::LogicalShiftRight($left, $right)
    };
}
pub(crate) use binary_bitvector32_term;

/// Matches every two-operand signed 64-bit [`Bitvector32Term`] operation, binding the operands to
/// `$left` and `$right`.
macro_rules! binary_int64_term {
    ($left:pat, $right:pat) => {
        $crate::kernel::Bitvector32Term::Int64Add($left, $right)
            | $crate::kernel::Bitvector32Term::Int64Subtract($left, $right)
            | $crate::kernel::Bitvector32Term::Int64Multiply($left, $right)
            | $crate::kernel::Bitvector32Term::Int64Divide($left, $right)
            | $crate::kernel::Bitvector32Term::Int64Remainder($left, $right)
            | $crate::kernel::Bitvector32Term::Int64BitwiseAnd($left, $right)
            | $crate::kernel::Bitvector32Term::Int64BitwiseOr($left, $right)
            | $crate::kernel::Bitvector32Term::Int64BitwiseXor($left, $right)
            | $crate::kernel::Bitvector32Term::Int64ShiftLeft($left, $right)
            | $crate::kernel::Bitvector32Term::Int64ArithmeticShiftRight($left, $right)
    };
}
pub(crate) use binary_int64_term;

/// Matches every two-operand unsigned 64-bit [`Bitvector32Term`] operation, binding the operands to
/// `$left` and `$right`.
macro_rules! binary_uint64_term {
    ($left:pat, $right:pat) => {
        $crate::kernel::Bitvector32Term::UInt64Add($left, $right)
            | $crate::kernel::Bitvector32Term::UInt64Subtract($left, $right)
            | $crate::kernel::Bitvector32Term::UInt64Multiply($left, $right)
            | $crate::kernel::Bitvector32Term::UInt64Divide($left, $right)
            | $crate::kernel::Bitvector32Term::UInt64Remainder($left, $right)
            | $crate::kernel::Bitvector32Term::UInt64BitwiseAnd($left, $right)
            | $crate::kernel::Bitvector32Term::UInt64BitwiseOr($left, $right)
            | $crate::kernel::Bitvector32Term::UInt64BitwiseXor($left, $right)
            | $crate::kernel::Bitvector32Term::UInt64ShiftLeft($left, $right)
            | $crate::kernel::Bitvector32Term::UInt64LogicalShiftRight($left, $right)
    };
}
pub(crate) use binary_uint64_term;

/// Matches every two-operand 64-bit [`Bitvector32Term`] operation, signed or unsigned, binding the
/// operands to `$left` and `$right`.
macro_rules! binary_wide_term {
    ($left:pat, $right:pat) => {
        $crate::kernel::binary_int64_term!($left, $right)
            | $crate::kernel::binary_uint64_term!($left, $right)
    };
}
pub(crate) use binary_wide_term;

/// Matches every two-operand [`Bitvector32Term`] operation of any width, binding the operands to
/// `$left` and `$right`.
macro_rules! binary_machine_term {
    ($left:pat, $right:pat) => {
        $crate::kernel::binary_bitvector32_term!($left, $right)
            | $crate::kernel::binary_wide_term!($left, $right)
    };
}
pub(crate) use binary_machine_term;

/// Matches every [`ConditionTerm`] comparison of two mathematical integers, binding the operands to
/// `$left` and `$right`.
macro_rules! integer_comparison_condition {
    ($left:pat, $right:pat) => {
        $crate::kernel::ConditionTerm::IntegerLessThan($left, $right)
            | $crate::kernel::ConditionTerm::IntegerLessEqual($left, $right)
            | $crate::kernel::ConditionTerm::IntegerGreaterThan($left, $right)
            | $crate::kernel::ConditionTerm::IntegerGreaterEqual($left, $right)
            | $crate::kernel::ConditionTerm::IntegerEqual($left, $right)
            | $crate::kernel::ConditionTerm::IntegerNotEqual($left, $right)
    };
}
pub(crate) use integer_comparison_condition;

/// Matches every two-operand [`IntegerTerm`] operation, binding the operands to `$left` and
/// `$right`.
macro_rules! binary_integer_term {
    ($left:pat, $right:pat) => {
        $crate::kernel::IntegerTerm::Add($left, $right)
            | $crate::kernel::IntegerTerm::Subtract($left, $right)
            | $crate::kernel::IntegerTerm::Multiply($left, $right)
            | $crate::kernel::IntegerTerm::TruncatingQuotient($left, $right)
            | $crate::kernel::IntegerTerm::TruncatingRemainder($left, $right)
    };
}
pub(crate) use binary_integer_term;

/// Matches every binary operator [`CExpression`]: arithmetic, bitwise, comparison and logical,
/// binding the operands to `$left` and `$right`.
macro_rules! binary_c_operation {
    ($left:pat, $right:pat) => {
        $crate::kernel::CExpression::Add($left, $right)
            | $crate::kernel::CExpression::Subtract($left, $right)
            | $crate::kernel::CExpression::Multiply($left, $right)
            | $crate::kernel::CExpression::Divide($left, $right)
            | $crate::kernel::CExpression::Remainder($left, $right)
            | $crate::kernel::CExpression::BitwiseAnd($left, $right)
            | $crate::kernel::CExpression::BitwiseOr($left, $right)
            | $crate::kernel::CExpression::BitwiseXor($left, $right)
            | $crate::kernel::CExpression::ShiftLeft($left, $right)
            | $crate::kernel::CExpression::ShiftRight($left, $right)
            | $crate::kernel::CExpression::Equal($left, $right)
            | $crate::kernel::CExpression::NotEqual($left, $right)
            | $crate::kernel::CExpression::LessThan($left, $right)
            | $crate::kernel::CExpression::LessEqual($left, $right)
            | $crate::kernel::CExpression::GreaterThan($left, $right)
            | $crate::kernel::CExpression::GreaterEqual($left, $right)
            | $crate::kernel::CExpression::And($left, $right)
            | $crate::kernel::CExpression::Or($left, $right)
    };
}
pub(crate) use binary_c_operation;

/// Matches every two-operand [`CExpression`]: the binary operators and indexing, binding the
/// operands to `$left` and `$right`.
macro_rules! binary_c_expression {
    ($left:pat, $right:pat) => {
        $crate::kernel::binary_c_operation!($left, $right)
            | $crate::kernel::CExpression::Index($left, $right)
            | $crate::kernel::CExpression::RecordPointerOffset {
                pointer: $left,
                index: $right,
                ..
            }
            | $crate::kernel::CExpression::ArrayRowAddress {
                array: $left,
                index: $right,
                ..
            }
    };
}
pub(crate) use binary_c_expression;

/// Matches every arithmetic and bitwise binary [`SpecExpression`], binding the operands to `$left`
/// and `$right`.
macro_rules! binary_spec_expression {
    ($left:pat, $right:pat) => {
        $crate::kernel::SpecExpression::Add($left, $right)
            | $crate::kernel::SpecExpression::Subtract($left, $right)
            | $crate::kernel::SpecExpression::Multiply($left, $right)
            | $crate::kernel::SpecExpression::Divide($left, $right)
            | $crate::kernel::SpecExpression::Remainder($left, $right)
            | $crate::kernel::SpecExpression::BitwiseAnd($left, $right)
            | $crate::kernel::SpecExpression::BitwiseOr($left, $right)
            | $crate::kernel::SpecExpression::BitwiseXor($left, $right)
            | $crate::kernel::SpecExpression::ShiftLeft($left, $right)
            | $crate::kernel::SpecExpression::ShiftRight($left, $right)
    };
}
pub(crate) use binary_spec_expression;

/// Matches every two-operand [`SpecIntegerExpression`], binding the operands to `$left` and
/// `$right`.
macro_rules! binary_spec_integer_expression {
    ($left:pat, $right:pat) => {
        $crate::kernel::SpecIntegerExpression::Add($left, $right)
            | $crate::kernel::SpecIntegerExpression::Subtract($left, $right)
            | $crate::kernel::SpecIntegerExpression::Multiply($left, $right)
            | $crate::kernel::SpecIntegerExpression::TruncatingQuotient($left, $right)
            | $crate::kernel::SpecIntegerExpression::TruncatingRemainder($left, $right)
    };
}
pub(crate) use binary_spec_integer_expression;

/// Matches every integer [`CValue`] that promotes to `int`, binding its operand to `$term`.
macro_rules! int_promoted_c_value {
    ($term:pat) => {
        $crate::kernel::CValue::Int8($term)
            | $crate::kernel::CValue::Int16($term)
            | $crate::kernel::CValue::Int32($term)
            | $crate::kernel::CValue::UInt8($term)
            | $crate::kernel::CValue::UInt16($term)
    };
}
pub(crate) use int_promoted_c_value;

/// Matches every integer [`CValue`] of at most 32 bits, binding its operand to `$term`.
macro_rules! integer32_c_value {
    ($term:pat) => {
        $crate::kernel::CValue::Int8($term)
            | $crate::kernel::CValue::Int16($term)
            | $crate::kernel::CValue::Int32($term)
            | $crate::kernel::CValue::UInt8($term)
            | $crate::kernel::CValue::UInt16($term)
            | $crate::kernel::CValue::UInt32($term)
    };
}
pub(crate) use integer32_c_value;

/// Matches every integer [`CValue`] of at most 64 bits, binding its operand to `$term`.
macro_rules! integer64_c_value {
    ($term:pat) => {
        $crate::kernel::CValue::Int8($term)
            | $crate::kernel::CValue::Int16($term)
            | $crate::kernel::CValue::Int32($term)
            | $crate::kernel::CValue::UInt8($term)
            | $crate::kernel::CValue::UInt16($term)
            | $crate::kernel::CValue::UInt32($term)
            | $crate::kernel::CValue::Int64($term)
            | $crate::kernel::CValue::UInt64($term)
    };
}
pub(crate) use integer64_c_value;

/// Matches every integer [`CValue`], binding its operand to `$term`.
macro_rules! integer_c_value {
    ($term:pat) => {
        $crate::kernel::CValue::Int8($term)
            | $crate::kernel::CValue::Int16($term)
            | $crate::kernel::CValue::Int32($term)
            | $crate::kernel::CValue::UInt8($term)
            | $crate::kernel::CValue::UInt16($term)
            | $crate::kernel::CValue::UInt32($term)
            | $crate::kernel::CValue::Int64($term)
            | $crate::kernel::CValue::UInt64($term)
            | $crate::kernel::CValue::Int128($term)
            | $crate::kernel::CValue::UInt128($term)
    };
}
pub(crate) use integer_c_value;

/// Matches every arithmetic [`CValue`]: `_Bool`, the integers and the floating types, binding its
/// operand to `$term`.
macro_rules! arithmetic_c_value {
    ($term:pat) => {
        $crate::kernel::CValue::Bool($term)
            | $crate::kernel::CValue::Int8($term)
            | $crate::kernel::CValue::Int16($term)
            | $crate::kernel::CValue::Int32($term)
            | $crate::kernel::CValue::UInt8($term)
            | $crate::kernel::CValue::UInt16($term)
            | $crate::kernel::CValue::UInt32($term)
            | $crate::kernel::CValue::Int64($term)
            | $crate::kernel::CValue::UInt64($term)
            | $crate::kernel::CValue::Int128($term)
            | $crate::kernel::CValue::UInt128($term)
            | $crate::kernel::CValue::Float32($term)
            | $crate::kernel::CValue::Float64($term)
    };
}
pub(crate) use arithmetic_c_value;

/// Matches every one-operand [`Bitvector32Term`] operation and conversion, binding its operand to
/// `$term`.
macro_rules! unary_machine_term {
    ($term:pat) => {
        $crate::kernel::Bitvector32Term::BitwiseNot($term)
            | $crate::kernel::Bitvector32Term::Int64BitwiseNot($term)
            | $crate::kernel::Bitvector32Term::UInt64BitwiseNot($term)
            | $crate::kernel::Bitvector32Term::Int64From32($term)
            | $crate::kernel::Bitvector32Term::MachineIntegerCast { value: $term, .. }
            | $crate::kernel::Bitvector32Term::UInt64From32($term)
            | $crate::kernel::Bitvector32Term::UInt32From64($term)
            | $crate::kernel::Bitvector32Term::Int64FromUInt32($term)
            | $crate::kernel::Bitvector32Term::UInt64FromInt32($term)
            | $crate::kernel::Bitvector32Term::UInt64FromInt64($term)
            | $crate::kernel::Bitvector32Term::Float32Negate($term)
            | $crate::kernel::Bitvector32Term::Float64Negate($term)
    };
}
pub(crate) use unary_machine_term;

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Pointer {
    pub block: PointerBlock,
    pub offset: PointerOffsetTerm,
}

/// An assumption-free name for one pointer-valued, eight-byte load.
/// It is a different sort from scalar load variables even when both reads
/// use the same snapshot and address.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct PointerLoadId(pub(crate) u64);

/// The immutable defining snapshot and cell of a pointer-valued load. The
/// retained origin is its meaning; the interned name is only an address-graph
/// handle and is never consulted to recover or change a designation.
#[derive(Clone, Debug)]
pub(crate) struct PointerLoadIdentity {
    id: PointerLoadId,
    memory: SharedCMemory,
    address: Pointer,
}

impl PointerLoadIdentity {
    pub(crate) fn new(memory: SharedCMemory, address: Pointer) -> Self {
        let id = crate::kernel::eval::pointer_load_identity(&memory, &address);
        Self {
            id,
            memory,
            address,
        }
    }

    pub(crate) fn id(&self) -> PointerLoadId {
        self.id
    }

    pub(crate) fn memory(&self) -> &SharedCMemory {
        &self.memory
    }

    pub(crate) fn address(&self) -> &Pointer {
        &self.address
    }
}

impl PartialEq for PointerLoadIdentity {
    fn eq(&self, other: &Self) -> bool {
        self.memory.arena_id() == other.memory.arena_id() && self.address == other.address
    }
}

impl Eq for PointerLoadIdentity {}

impl std::hash::Hash for PointerLoadIdentity {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Content hashes are cached and stable across fresh arenas. Different
        // exact origins may legally collide; equality still checks arena ids.
        self.memory.hash(state);
        self.address.hash(state);
    }
}

impl Ord for PointerLoadIdentity {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.memory.arena_id(), &self.address).cmp(&(other.memory.arena_id(), &other.address))
    }
}

impl PartialOrd for PointerLoadIdentity {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Semantic decoder for an opaque pointer value read from memory. The
/// displacement belongs to later pointer arithmetic, not to the identity of
/// the load or to the storage address that held the value.
#[derive(Clone, Debug)]
#[allow(
    dead_code,
    reason = "the graph query names loads without decoding them in live consumers yet"
)]
pub(crate) struct LoadedPointerView {
    pub(crate) identity: PointerLoadId,
    pub(crate) defining_memory: SharedCMemory,
    pub(crate) defining_address: Pointer,
    pub(crate) displacement: PointerOffsetTerm,
}

/// A C pointer value carries both its raw address and the type through which
/// the address is being viewed, plus an optional immutable object/array
/// designation. `Pointer` remains the untyped address
/// identity used by memory, aliasing, and provenance; pointer casts retag the
/// value without changing that identity.
///
/// Whether the pointee is `const` is carried beside the value and is not part
/// of its identity: equality, ordering and hashing ignore it. It is a property
/// of the access path, which the write-through-`const` and implicit-discard
/// checks read from the value or from the static type of the lvalue, and two
/// values that differ only in it designate the same object. A fact about a
/// pointer therefore matches the pointer however its type is qualified.
#[derive(Clone, Debug)]
pub struct CPointerValue {
    pointer: Pointer,
    c_type: CType,
    pointee_volatile: bool,
    pointee_constant: bool,
    designation: Option<std::sync::Arc<PointerDesignation>>,
}

/// An immutable description of the object/array selected by a pointer value.
/// These terms carry no proof of liveness, initialization, or access authority.
/// The absent legacy designation is distinct from an unresolved C binder.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) enum PointerDesignation {
    Unresolved(Variable),
    /// Unknown referent paired with the exact read that supplies its address.
    /// This grants no access authority and cannot be resolved by numeric
    /// equality of the loaded address.
    Loaded(PointerLoadIdentity),
    Object {
        root: Pointer,
        path: std::sync::Arc<[PointerDomainSelection]>,
        base: Pointer,
        element_type: CType,
        stride: u32,
        count: SharedIntegerTerm,
    },
    /// An actual subobject selected through one exact native input promise.
    /// The input key supplies no complete-array extent or access authority.
    InputSelected {
        input: CNativeInputIdentity,
        origin: Pointer,
        path: Arc<[PointerDomainSelection]>,
        base: Pointer,
        element_type: CType,
        stride: u32,
        count: SharedIntegerTerm,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) enum PointerDomainSelection {
    Member(String),
    Element(SharedIntegerTerm),
}

impl PointerDesignation {
    pub(crate) fn pointer_terms(&self) -> impl Iterator<Item = &Pointer> {
        match self {
            Self::Unresolved(_) => [None, None, None],
            Self::Loaded(identity) => [Some(identity.address()), None, None],
            Self::Object { root, base, .. } => [Some(root), Some(base), None],
            Self::InputSelected {
                input,
                origin,
                base,
                ..
            } => [
                Some(origin),
                Some(base),
                match input {
                    CNativeInputIdentity::Loaded(identity) => Some(identity.address()),
                    _ => None,
                },
            ],
        }
        .into_iter()
        .flatten()
    }

    pub(crate) fn integer_terms(&self) -> impl Iterator<Item = &SharedIntegerTerm> {
        let (path, count) = match self {
            Self::Unresolved(_) | Self::Loaded(_) => (&[][..], None),
            Self::Object { path, count, .. } | Self::InputSelected { path, count, .. } => {
                (path.as_ref(), Some(count))
            }
        };
        path.iter()
            .filter_map(|selection| match selection {
                PointerDomainSelection::Member(_) => None,
                PointerDomainSelection::Element(index) => Some(index),
            })
            .chain(count)
    }

    pub(crate) fn unresolved_variable(&self) -> Option<Variable> {
        match self {
            Self::Unresolved(variable) => Some(*variable),
            Self::InputSelected {
                input: CNativeInputIdentity::Unresolved(variable),
                ..
            } => Some(*variable),
            Self::InputSelected { .. } => None,
            Self::Object { .. } | Self::Loaded(_) => None,
        }
    }

    pub(crate) fn loaded_identity(&self) -> Option<&PointerLoadIdentity> {
        match self {
            Self::Loaded(identity)
            | Self::InputSelected {
                input: CNativeInputIdentity::Loaded(identity),
                ..
            } => Some(identity),
            _ => None,
        }
    }
}

impl CPointerValue {
    pub(crate) fn new(pointer: Pointer, c_type: CType) -> Self {
        assert!(
            c_type.is_pointer(),
            "C pointer values require a pointer type"
        );
        Self {
            pointer,
            c_type,
            pointee_volatile: false,
            pointee_constant: false,
            designation: None,
        }
    }

    pub(crate) fn pointer(&self) -> &Pointer {
        &self.pointer
    }

    pub(crate) fn into_pointer(self) -> Pointer {
        self.pointer
    }

    pub(crate) fn c_type(&self) -> CType {
        self.c_type
    }

    pub(crate) fn pointee_volatile(&self) -> bool {
        self.pointee_volatile
    }

    pub(crate) fn pointee_constant(&self) -> bool {
        self.pointee_constant
    }

    pub(crate) fn designation(&self) -> Option<&PointerDesignation> {
        self.designation.as_deref()
    }

    pub(crate) fn same_designation(&self, other: &Self) -> bool {
        self.designation == other.designation
    }

    pub(crate) fn with_designation(mut self, designation: PointerDesignation) -> Self {
        self.designation = Some(std::sync::Arc::new(designation));
        self
    }

    pub(crate) fn with_designation_of(mut self, other: &Self) -> Self {
        self.designation = other.designation.clone();
        self
    }

    pub(crate) fn map_designation(
        mut self,
        map: impl FnOnce(&PointerDesignation) -> PointerDesignation,
    ) -> Self {
        if let Some(designation) = &self.designation {
            let mapped = map(designation);
            if mapped != **designation {
                self.designation = Some(std::sync::Arc::new(mapped));
            }
        }
        self
    }

    pub(crate) fn map_designation_pointers(self, mut map: impl FnMut(&Pointer) -> Pointer) -> Self {
        self.map_designation(|designation| match designation {
            PointerDesignation::Unresolved(variable) => PointerDesignation::Unresolved(*variable),
            PointerDesignation::Loaded(identity) => PointerDesignation::Loaded(
                PointerLoadIdentity::new(identity.memory().clone(), map(identity.address())),
            ),
            PointerDesignation::Object {
                root,
                path,
                base,
                element_type,
                stride,
                count,
            } => PointerDesignation::Object {
                root: map(root),
                path: path.clone(),
                base: map(base),
                element_type: *element_type,
                stride: *stride,
                count: count.clone(),
            },
            PointerDesignation::InputSelected {
                input,
                origin,
                path,
                base,
                element_type,
                stride,
                count,
            } => PointerDesignation::InputSelected {
                input: match input {
                    CNativeInputIdentity::Unresolved(variable) => {
                        CNativeInputIdentity::Unresolved(*variable)
                    }
                    CNativeInputIdentity::Loaded(identity) => {
                        CNativeInputIdentity::Loaded(PointerLoadIdentity::new(
                            identity.memory().clone(),
                            map(identity.address()),
                        ))
                    }
                },
                origin: map(origin),
                path: path.clone(),
                base: map(base),
                element_type: *element_type,
                stride: *stride,
                count: count.clone(),
            },
        })
    }

    pub(crate) fn with_type(self, c_type: CType) -> Self {
        Self {
            pointer: self.pointer,
            c_type,
            pointee_volatile: self.pointee_volatile,
            pointee_constant: self.pointee_constant,
            designation: self.designation,
        }
    }

    pub(crate) fn with_pointee_volatile(mut self, pointee_volatile: bool) -> Self {
        self.pointee_volatile = pointee_volatile;
        self
    }

    pub(crate) fn with_pointee_constant(mut self, pointee_constant: bool) -> Self {
        self.pointee_constant = pointee_constant;
        self
    }

    pub(crate) fn replace_pointer(&mut self, pointer: Pointer) {
        self.pointer = pointer;
    }

    /// Transform only the address, retaining all other pointer-value metadata.
    /// Substitution of any future designation terms must map those terms
    /// separately; arithmetic must not rebase the designated object's domain.
    pub(crate) fn with_pointer(mut self, pointer: Pointer) -> Self {
        self.replace_pointer(pointer);
        self
    }

    pub(crate) fn is_null(&self) -> bool {
        self.pointer.block == PointerBlock::Concrete("null".to_string())
            && self.pointer.offset == PointerOffsetTerm::Constant(0)
    }
}

impl CPointerValue {
    /// Full value identity includes designation as well as address and view.
    /// Native pointer comparisons continue to compare the raw address.
    fn identity(
        &self,
    ) -> (
        &Pointer,
        &CType,
        bool,
        &Option<std::sync::Arc<PointerDesignation>>,
    ) {
        (
            &self.pointer,
            &self.c_type,
            self.pointee_volatile,
            &self.designation,
        )
    }
}

impl PartialEq for CPointerValue {
    fn eq(&self, other: &Self) -> bool {
        self.identity() == other.identity()
    }
}

impl Eq for CPointerValue {}

impl std::hash::Hash for CPointerValue {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Preserve legacy pointer hashes used by deterministic load names.
        (&self.pointer, &self.c_type, self.pointee_volatile).hash(state);
        if let Some(designation) = &self.designation {
            designation.hash(state);
        }
    }
}

impl PartialOrd for CPointerValue {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CPointerValue {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.identity().cmp(&other.identity())
    }
}

impl std::ops::Deref for CPointerValue {
    type Target = Pointer;

    fn deref(&self) -> &Self::Target {
        &self.pointer
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum PointerBlock {
    Concrete(String),
    /// A string literal occurrence. Distinct occurrences with identical
    /// bytes are intentionally not proven distinct: C permits an
    /// implementation to merge them. The occurrence identity still keeps
    /// one literal's pointer stable, and differing bytes prove that two
    /// occurrences cannot be the same object.
    StringLiteral {
        identity: String,
        bytes: Vec<u8>,
    },
    Function(String),
    FunctionSymbolic(Variable),
    ExternalArgument,
    /// Opaque C object provenance paired with an external argument address.
    /// Distinct tokens are not assumed distinct: two parameters may still
    /// have been derived from the same caller object.
    ExternalObject(Variable),
    Symbolic(Variable),
    /// The value read by a pointer-typed load, independent of the storage
    /// block that held it and of the pointee type used after the read.
    LoadedPointer(PointerLoadId),
    /// An opaque pointer-valued pure call. This is not an allocation identity
    /// and grants neither distinctness nor memory access.
    PureFunctionApplication(SharedPureApplication),

    /// A trusted allocation identity. Unlike a symbolic/opaque block, this is
    /// fresh and distinct from every other block identity.
    Heap(u64),
    /// Storage the verifier introduced for an object the C abstract machine
    /// creates but the program never names: today, the temporary that holds an
    /// aggregate a call returns by value.
    ///
    /// Soundness of treating this as fresh and distinct from every other
    /// block: the object does not exist before the call that produces it, so
    /// no pointer the program already holds can point into it, and C gives the
    /// program no way to obtain its address afterwards either. A by-value
    /// return is a copy: the callee's own storage, whatever it was, is a
    /// different object from this temporary, and the copy is what the caller
    /// reads. Every later use spells the temporary through this identity or
    /// copies out of it; a program that stores the aggregate into a local and
    /// then takes `&local.field` is addressing the local's block, not this
    /// one. Identities come from the single kernel variable allocator, so two
    /// temporaries are never confused, and a fresh identity is never the
    /// identity of storage that already existed.
    Temporary(u64),
}

impl std::hash::Hash for PointerBlock {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Keep the hash domain of the pre-string-literal variants stable.
        // Pointer hashes feed deterministic load-variable identities, so
        // inserting a new enum variant must not renumber existing blocks.
        match self {
            Self::PureFunctionApplication(application) => {
                10u64.hash(state);
                application.hash(state);
            }
            Self::Concrete(name) => {
                0u64.hash(state);
                name.hash(state);
            }
            Self::Function(name) => {
                1u64.hash(state);
                name.hash(state);
            }
            Self::FunctionSymbolic(variable) => {
                2u64.hash(state);
                variable.hash(state);
            }
            Self::ExternalArgument => 3u64.hash(state),
            Self::Symbolic(variable) => {
                4u64.hash(state);
                variable.hash(state);
            }
            Self::LoadedPointer(identity) => {
                9u64.hash(state);
                identity.hash(state);
            }
            Self::Heap(identity) => {
                5u64.hash(state);
                identity.hash(state);
            }
            Self::StringLiteral { identity, bytes } => {
                6u64.hash(state);
                identity.hash(state);
                bytes.hash(state);
            }
            Self::ExternalObject(variable) => {
                7u64.hash(state);
                variable.hash(state);
            }
            Self::Temporary(identity) => {
                8u64.hash(state);
                identity.hash(state);
            }
        }
    }
}

impl PointerBlock {
    pub(crate) fn is_function(&self) -> bool {
        matches!(self, Self::Function(_) | Self::FunctionSymbolic(_))
    }

    pub(crate) fn starts_with(&self, prefix: &str) -> bool {
        match self {
            Self::Concrete(name) => name.starts_with(prefix),
            Self::StringLiteral { .. } => prefix == "string:",
            _ => false,
        }
    }

    pub(crate) fn strip_prefix<'a>(&'a self, prefix: &str) -> Option<&'a str> {
        match self {
            Self::Concrete(name) => name.strip_prefix(prefix),
            Self::StringLiteral { .. }
            | Self::Function(_)
            | Self::FunctionSymbolic(_)
            | Self::ExternalArgument
            | Self::ExternalObject(_)
            | Self::Symbolic(_)
            | Self::LoadedPointer(_)
            | Self::PureFunctionApplication(_)
            | Self::Heap(_)
            | Self::Temporary(_) => None,
        }
    }

    /// Whether no execution can make these two block identities name one
    /// object. This is the kernel's only structural separation rule for
    /// blocks, and `Pointer::blocks_proven_distinct` is its pointer-level
    /// form.
    ///
    /// Two identities that are merely spelled differently are not distinct.
    /// A parameter's `ExternalArgument` memory and a file-scope
    /// `global:` block are the standard example: the caller decides whether
    /// they are the same object, and nothing in the callee does.
    ///
    /// The two identities that are distinct from every other one are the ones
    /// that name storage nothing else could already be pointing into:
    /// [`Self::Heap`], a trusted fresh allocation, and [`Self::Temporary`], an
    /// object the verifier introduced for a value the C abstract machine
    /// creates without naming it.
    pub(in crate::kernel) fn proven_distinct(&self, other: &Self) -> bool {
        // A local whose address the function never takes is reachable by no
        // pointer value at all: no symbolic, external, or function pointer
        // can point into it, whatever the facts say, because no expression
        // ever produced its address. This holds before the symbolic rule
        // below, which is about where a pointer value may point.
        let pointer_value_versus_hidden_local = |value: &Self, local: &Self| {
            matches!(
                value,
                Self::Symbolic(_)
                    | Self::LoadedPointer(_)
                    | Self::FunctionSymbolic(_)
                    | Self::ExternalArgument
                    | Self::ExternalObject(_)
            ) && super::primitives::block_is_never_address_taken_local(local)
        };
        if pointer_value_versus_hidden_local(self, other)
            || pointer_value_versus_hidden_local(other, self)
        {
            return true;
        }
        // A loaded pointer is a value obtained at the snapshot it was read
        // in, and cannot point into an object that did not exist then.
        let loaded_before = |value: &Self, object: &Self| {
            matches!(value, Self::Symbolic(variable)
                if crate::kernel::is_load_variable(variable)
                    && crate::kernel::eval::loaded_pointer_predates_block(variable, object))
        };
        if loaded_before(self, other) || loaded_before(other, self) {
            return true;
        }
        // A symbolic block is a logic variable that later facts may constrain
        // to any address, including a heap block named below (a contract
        // postcondition such as `result == destination` does exactly that).
        // It is therefore never proven distinct by structure alone; only an
        // explicit disequality in the assumptions can separate it.
        if matches!(
            self,
            Self::Symbolic(_) | Self::LoadedPointer(_) | Self::PureFunctionApplication(_)
        ) || matches!(
            other,
            Self::Symbolic(_) | Self::LoadedPointer(_) | Self::PureFunctionApplication(_)
        ) {
            return false;
        }
        // A function's own scalar locals (`local:` blocks) are storage the
        // function declared; memory reached through a parameter
        // (`ExternalArgument`) existed before the call and cannot be one of
        // them.
        let local_versus_argument = |left: &Self, right: &Self| {
            left.starts_with("local:")
                && matches!(right, Self::ExternalArgument | Self::ExternalObject(_))
        };
        self != other
            && (matches!(self, Self::Heap(_) | Self::Temporary(_))
                || matches!(other, Self::Heap(_) | Self::Temporary(_))
                || match (self, other) {
                    (
                        Self::StringLiteral { bytes: left, .. },
                        Self::StringLiteral { bytes: right, .. },
                    ) => left != right,
                    _ => false,
                }
                || matches!(
                    (self, other),
                    (Self::Concrete(left), Self::Concrete(right)) if left != right
                )
                || local_versus_argument(self, other)
                || local_versus_argument(other, self))
    }

    /// Whether a cell in this block may be the cell a load in `other`'s block
    /// reads, so a memory comparison made on behalf of that load must still
    /// account for it.
    ///
    /// This is the predicate every "restrict attention to one block" filter
    /// owes: keeping only the load's own block silently assumes that every
    /// differently spelled block is a different object.
    pub(in crate::kernel) fn may_alias(&self, other: &Self) -> bool {
        !self.proven_distinct(other)
    }

    /// Whether a cell in this block has to be accounted for by a memory
    /// comparison made on behalf of a load in the `load` block. This is the
    /// one filter the load-framing routes share, so that a write to a block
    /// that merely has another spelling cannot be dropped from the question.
    ///
    /// It is exactly [`Self::may_alias`]; there is no longer an exception for a
    /// load whose own block is `Symbolic`. That exception used to filter such a
    /// load by block name, which silently assumed the pointer a call returned
    /// could not point into any other block: a fact about `a[0]` then survived
    /// a store to `g[0]` even with `a == &g[0]` in the context
    /// (`mdtests/returned_pointer_may_alias_a_global.md`).
    ///
    /// Withdrawing it means a load through a pointer whose target the verifier
    /// does not know keeps every cell not proven distinct from it, so framing
    /// such a load needs evidence: an effect summary, a pointer equality that
    /// resolves the pointer to storage the program names, a separation or
    /// disequality fact, or resource ownership. The objects the verifier
    /// introduces itself are not in that position, because they are
    /// [`Self::Temporary`] rather than `Symbolic` and `proven_distinct`
    /// separates them from everything.
    pub(in crate::kernel) fn observable_by_load(&self, load: &Self) -> bool {
        self.may_alias(load)
    }
}

impl From<String> for PointerBlock {
    fn from(name: String) -> Self {
        Self::Concrete(name)
    }
}

impl From<&str> for PointerBlock {
    fn from(name: &str) -> Self {
        Self::Concrete(name.to_string())
    }
}

impl std::fmt::Display for PointerBlock {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::PureFunctionApplication(application) => write!(
                formatter,
                "pure-pointer:{}:{}",
                application.name(),
                application.id()
            ),
            Self::Concrete(name) => formatter.write_str(name),
            Self::StringLiteral { identity, .. } => write!(formatter, "string:{identity}"),
            Self::Function(name) => write!(formatter, "function:{name}"),
            Self::FunctionSymbolic(variable) => {
                write!(formatter, "symbolic-function-pointer:{}", variable.0)
            }
            Self::ExternalArgument => formatter.write_str("arg-memory"),
            Self::ExternalObject(variable) => write!(formatter, "arg-object:{}", variable.0),
            Self::Symbolic(variable) => write!(formatter, "symbolic-pointer:{}", variable.0),
            Self::LoadedPointer(identity) => write!(formatter, "loaded-pointer:{}", identity.0),
            Self::Heap(identity) => write!(formatter, "heap-allocation:{identity}"),
            Self::Temporary(identity) => write!(formatter, "temporary:{identity}"),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CValue {
    Void,
    /// C `_Bool` values are represented by a 32-bit term whose value is
    /// always normalized to zero or one.  The storage width remains the
    /// ABI-defined one byte width exposed by `CType::Bool`.
    Bool(Bitvector32Term),
    Int8(Bitvector32Term),
    Int16(Bitvector32Term),
    Int32(Bitvector32Term),
    UInt8(Bitvector32Term),
    UInt16(Bitvector32Term),
    UInt32(Bitvector32Term),
    Int64(Bitvector32Term),
    UInt64(Bitvector32Term),
    /// A complete integer representation produced from an actual pointer.
    /// Numeric observations project its bits; equality cannot issue its origin.
    PointerInteger(std::sync::Arc<CPointerIntegerValue>),
    Int128(Bitvector32Term),
    UInt128(Bitvector32Term),
    /// IEEE-754 binary32 payload represented in the shared checked term arena.
    Float32(Bitvector32Term),
    /// IEEE-754 binary64 payload represented in the shared checked term arena.
    Float64(Bitvector32Term),
    Pointer(CPointerValue),
}

/// Executable origin is separate from numeric bits and survives only checked
/// whole-value transport and the explicitly supported integer operations.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CPointerIntegerValue {
    bits: Bitvector32Term,
    signed: bool,
    origin: CPointerValue,
}

impl CPointerIntegerValue {
    pub(in crate::kernel) fn from_pointer(origin: CPointerValue, c_type: CType) -> Option<Self> {
        let signed = match c_type {
            CType::Int64 => true,
            CType::UInt64 => false,
            _ => return None,
        };
        Some(Self {
            bits: Bitvector32Term::pointer_address(origin.pointer().clone()),
            signed,
            origin,
        })
    }

    pub(crate) fn bits(&self) -> &Bitvector32Term {
        &self.bits
    }
    pub(crate) fn origin(&self) -> &CPointerValue {
        &self.origin
    }
    pub(crate) fn c_type(&self) -> CType {
        if self.signed {
            CType::Int64
        } else {
            CType::UInt64
        }
    }
    pub(crate) fn numeric_value(&self) -> CValue {
        if self.signed {
            CValue::Int64(self.bits.clone())
        } else {
            CValue::UInt64(self.bits.clone())
        }
    }

    pub(crate) fn with_numeric_value(&self, value: CValue) -> Option<Self> {
        let (bits, signed) = match value {
            CValue::Int64(bits) => (bits, true),
            CValue::UInt64(bits) => (bits, false),
            _ => return None,
        };
        Some(Self {
            bits,
            signed,
            origin: self.origin.clone(),
        })
    }

    /// Structural binder/substitution transport, never numeric-origin recovery.
    pub(crate) fn with_parts(&self, bits: Bitvector32Term, origin: CPointerValue) -> Self {
        Self {
            bits,
            signed: self.signed,
            origin,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CType {
    Void,
    Bool,
    /// An opaque object pointer with provenance but no modeled pointee type.
    /// It is valid for identity-preserving casts and comparisons, but not for
    /// dereference, indexing, or pointer arithmetic.
    VoidPointer,
    /// Pointer to an opaque object-pointer slot, needed to retain the exact
    /// `pthread_join` result parameter type even in null-only calls.
    VoidPointerPointer,
    Int8,
    Int16,
    Int32,
    UInt8,
    UInt16,
    UInt32,
    Int64,
    UInt64,
    Int128,
    UInt128,
    Float32,
    Float64,
    Int8Pointer,
    Int16Pointer,
    UInt16Pointer,
    Int32Pointer,
    UInt8Pointer,
    UInt32Pointer,
    Int64Pointer,
    Int128Pointer,
    UInt64Pointer,
    UInt128Pointer,
    Float32Pointer,
    Float64Pointer,
    Int8PointerPointer,
    Int16PointerPointer,
    UInt16PointerPointer,
    Int32PointerPointer,
    UInt8PointerPointer,
    UInt32PointerPointer,
    Int64PointerPointer,
    Int128PointerPointer,
    UInt64PointerPointer,
    UInt128PointerPointer,
    Float32PointerPointer,
    Float64PointerPointer,
    FunctionPointer(CallbackSignature),
    Int32Array(u32),
    UInt8Array(u32),
    Int8Array(u32),
    Int16Array(u32),
    UInt16Array(u32),
    UInt32Array(u32),
    Int64Array(u32),
    Int128Array(u32),
    UInt64Array(u32),
    UInt128Array(u32),
    Float32Array(u32),
    Float64Array(u32),
    /// Fixed array of object-pointer cells. The element kind remains typed;
    /// an incomplete struct tag is tracked by the C frontend, not erased to
    /// integer storage.
    PointerArray(CPointerArrayElement, u32),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CPointerArrayElement {
    Void,
    /// Plain `char` under a target where it is unsigned. Kept apart from
    /// `UInt8` only so the C frontend recovers `char *` from the element;
    /// its cells are `uint8*` pointers.
    UnsignedPlainChar,
    /// Plain `char` under a target where it is signed; its cells are
    /// `int8*` pointers.
    SignedPlainChar,
    Int8,
    Int16,
    Int32,
    UInt8,
    UInt16,
    UInt32,
    Int64,
    Int128,
    UInt64,
    UInt128,
    Float32,
    Float64,
}

impl CPointerArrayElement {
    pub fn from_pointer_type(c_type: CType) -> Option<Self> {
        Some(match c_type {
            CType::VoidPointer => Self::Void,
            CType::Int8Pointer => Self::Int8,
            CType::Int16Pointer => Self::Int16,
            CType::Int32Pointer => Self::Int32,
            CType::UInt8Pointer => Self::UInt8,
            CType::UInt16Pointer => Self::UInt16,
            CType::UInt32Pointer => Self::UInt32,
            CType::Int64Pointer => Self::Int64,
            CType::Int128Pointer => Self::Int128,
            CType::UInt64Pointer => Self::UInt64,
            CType::UInt128Pointer => Self::UInt128,
            CType::Float32Pointer => Self::Float32,
            CType::Float64Pointer => Self::Float64,
            _ => return None,
        })
    }

    pub fn pointer_type(self) -> CType {
        match self {
            Self::Void => CType::VoidPointer,
            Self::UnsignedPlainChar => CType::UInt8Pointer,
            Self::SignedPlainChar => CType::Int8Pointer,
            Self::Int8 => CType::Int8Pointer,
            Self::Int16 => CType::Int16Pointer,
            Self::Int32 => CType::Int32Pointer,
            Self::UInt8 => CType::UInt8Pointer,
            Self::UInt16 => CType::UInt16Pointer,
            Self::UInt32 => CType::UInt32Pointer,
            Self::Int64 => CType::Int64Pointer,
            Self::Int128 => CType::Int128Pointer,
            Self::UInt64 => CType::UInt64Pointer,
            Self::UInt128 => CType::UInt128Pointer,
            Self::Float32 => CType::Float32Pointer,
            Self::Float64 => CType::Float64Pointer,
        }
    }

    pub fn decayed_type_spelling(self) -> &'static str {
        match self {
            Self::Void => "void**",
            Self::UnsignedPlainChar | Self::UInt8 => "uint8**",
            Self::SignedPlainChar | Self::Int8 => "int8**",
            Self::Int16 => "int16**",
            Self::Int32 => "int32**",
            Self::UInt16 => "uint16**",
            Self::UInt32 => "uint32**",
            Self::Int64 => "int64**",
            Self::Int128 => "int128**",
            Self::UInt64 => "uint64**",
            Self::UInt128 => "uint128**",
            Self::Float32 => "float32**",
            Self::Float64 => "float64**",
        }
    }
}

/// Exact packed callback type identity. Byte alignment keeps the common C type
/// enum compact; using a u128 payload would enlarge every execution frame.
#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct CallbackSignature([u8; 10]);

impl CallbackSignature {
    pub const UNSPECIFIED: Self = Self([0; 10]);

    pub(crate) fn from_encoded(encoded: u128) -> Self {
        assert!(
            encoded < (1u128 << 80),
            "callback signature capacity exceeded"
        );
        Self(encoded.to_le_bytes()[..10].try_into().unwrap())
    }
}

impl std::fmt::Display for CallbackSignature {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut bytes = [0; 16];
        bytes[..10].copy_from_slice(&self.0);
        std::fmt::Display::fmt(&u128::from_le_bytes(bytes), formatter)
    }
}

impl std::fmt::Debug for CallbackSignature {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, formatter)
    }
}

/// The exceptional result channel declared by a function signature.
///
/// This is deliberately kernel-internal until the surface language has a
/// settled way to spell exceptional contracts.  The closed representation
/// prevents body execution from silently inventing new exceptional payload
/// types in the meantime.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) enum CExceptionalSignature {
    #[default]
    None,
    // Staged for kernel callers before any source importer can construct it.
    Int32,
}

impl CExceptionalSignature {
    pub(crate) fn is_empty(self) -> bool {
        self == Self::None
    }

    pub(crate) fn permits(self, value: &CValue) -> bool {
        matches!((self, value), (Self::Int32, CValue::Int32(_)))
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CLValue {
    pub(super) storage: CLValueStorage,
    pub(super) value_type: CType,
    pub(super) volatile: bool,
    pub(super) pointee_volatile: bool,
    pub(super) constant: bool,
    pub(super) pointee_constant: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) enum CLValueStorage {
    Local { name: String },
    Memory { pointer: CPointerValue },
}

/// The language-specific integer rule at an explicit kernel cast boundary.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CIntegerCastMode {
    #[default]
    Standard,
    /// Preserve the numeric value modulo the destination width. Used by
    /// Rust integer casts and C++20 integer conversions.
    Modulo,
    /// C's integer conversion, written or inserted by lowering, as GCC and
    /// Clang compile it: also the value modulo the destination width, owing
    /// no range. A narrower result is the typed conversion node, which the
    /// reasoning layer identifies with its operand inside the destination
    /// range (`narrowed_cast_identity`). `Standard` remains the
    /// specification's checked conversion.
    CConversion,
    /// Legacy exact uint64-to-int64 boundary.
    UInt64BitsToInt64,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CExpression {
    Value(CValue),
    Variable(String),
    FunctionAddress(String),
    Cast {
        expression: Box<CExpression>,
        target_type: CType,
        integer_mode: CIntegerCastMode,
        /// The struct tag of a pointer cast target, as the source spelled it.
        /// Evaluation ignores it: a struct pointer is a kernel `Int32Pointer`
        /// and the layout lives with the field accesses. It is kept so a
        /// contract cast prints back as `(struct name *)` and so the parser
        /// resolves `->field` through the cast result.
        pointee_struct: Option<String>,
        /// Whether the cast result points at a volatile pointer-valued cell.
        /// This carries the C qualifier in `T * volatile *` into a following
        /// dereference without confusing it with volatile `T` storage.
        pointee_volatile: bool,
        /// Whether the cast result points at const-qualified storage. Source
        /// pointee constness is retained independently when the cast is
        /// evaluated, unless `explicit_qualification` is set.
        pointee_constant: bool,
        /// Whether this is a cast the C source wrote, whose result has
        /// exactly the destination's pointee qualification. C lets such a
        /// cast drop `const`; the storage's own read-only status still
        /// decides every store. A cast that lowering inserts leaves this
        /// unset and keeps the source pointer's qualification.
        explicit_qualification: bool,
    },
    Conditional {
        condition: Box<CExpression>,
        then_branch: Box<CExpression>,
        else_branch: Box<CExpression>,
    },
    FloatNegate(Box<CExpression>),
    FloatClassification {
        expression: Box<CExpression>,
        classification: CFloatClassification,
    },
    AddressOf(Box<CExpression>),
    /// Form an address only after checking that the complete lvalue denotes
    /// live storage. Unlike C's &* cancellation, this excludes one-past and
    /// expired addresses. It performs no load and grants no access authority.
    CheckedObjectAddress(Box<CExpression>),
    PointerOffsetBytes {
        pointer: Box<CExpression>,
        bytes: u32,
    },
    /// Observe address alignment as a Boolean without exposing a reversible
    /// integer representation or changing the pointer's semantic carrier.
    PointerAligned {
        pointer: Box<CExpression>,
        alignment: u64,
    },
    LessThan(Box<CExpression>, Box<CExpression>),
    LessEqual(Box<CExpression>, Box<CExpression>),
    GreaterThan(Box<CExpression>, Box<CExpression>),
    GreaterEqual(Box<CExpression>, Box<CExpression>),
    Equal(Box<CExpression>, Box<CExpression>),
    NotEqual(Box<CExpression>, Box<CExpression>),
    Not(Box<CExpression>),
    And(Box<CExpression>, Box<CExpression>),
    Or(Box<CExpression>, Box<CExpression>),
    Add(Box<CExpression>, Box<CExpression>),
    Subtract(Box<CExpression>, Box<CExpression>),
    Multiply(Box<CExpression>, Box<CExpression>),
    Divide(Box<CExpression>, Box<CExpression>),
    Remainder(Box<CExpression>, Box<CExpression>),
    ShiftLeft(Box<CExpression>, Box<CExpression>),
    ShiftRight(Box<CExpression>, Box<CExpression>),
    BitwiseAnd(Box<CExpression>, Box<CExpression>),
    BitwiseOr(Box<CExpression>, Box<CExpression>),
    BitwiseXor(Box<CExpression>, Box<CExpression>),
    BitwiseNot(Box<CExpression>),
    Load(Box<CExpression>),
    TypedLoad {
        pointer: Box<CExpression>,
        value_type: CType,
        /// A sequential kernel access primitive forces one observable access
        /// even when the source lvalue itself was not declared volatile.
        volatile: bool,
        /// Qualification of a loaded pointer's pointee, not of this cell.
        pointee_constant: bool,
        /// Source provenance is presentation metadata only. Its comparison
        /// traits intentionally ignore the value.
        source: CExpressionLoadSource,
    },
    Index(Box<CExpression>, Box<CExpression>),
    /// Checked native member selection. The layout/path come from resolved
    /// declarations; evaluation must authenticate the incoming object domain.
    MemberAddress {
        object: Box<CExpression>,
        selection: Arc<CAggregateMemberSelection>,
    },
    /// Select and decay one row of an actual multidimensional scalar array.
    /// The supplied shape must match its retained declaration/path; it grants
    /// no storage authority or initialized bytes.
    ArrayRowAddress {
        array: Box<CExpression>,
        index: Box<CExpression>,
        element_type: CType,
        shape: Arc<[u32]>,
    },
    /// A native record element step, with scaling outside the observed
    /// machine index. This is distinct from byte representation arithmetic.
    RecordPointerOffset {
        pointer: Box<CExpression>,
        index: Box<CExpression>,
        layout: Arc<CAggregateLayout>,
        subtract: bool,
    },
}

/// A frozen output selected by an explicit initialization postcondition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CInitializationOutput {
    pub(crate) parameter: usize,
    pub(crate) field: Option<Arc<CAggregateMemberSelection>>,
    pub(crate) bytes: u32,
}
impl CInitializationOutput {
    pub(crate) fn parameter_index(&self) -> usize {
        self.parameter
    }
    pub(crate) fn field(&self) -> Option<&CAggregateMemberSelection> {
        self.field.as_deref()
    }
    pub(crate) fn bytes(&self) -> u32 {
        self.bytes
    }
}

#[derive(Clone, Debug)]
pub struct CAggregateMemberSelection {
    pub(crate) layout: Arc<CAggregateLayout>,
    pub(crate) path: Arc<[String]>,
    pub(crate) value_type: CType,
}

impl CAggregateMemberSelection {
    pub fn layout(&self) -> &CAggregateLayout {
        &self.layout
    }
    pub fn path(&self) -> &[String] {
        &self.path
    }
    pub fn value_type(&self) -> CType {
        self.value_type
    }
}

impl PartialEq for CAggregateMemberSelection {
    fn eq(&self, other: &Self) -> bool {
        self.path == other.path
            && self.value_type == other.value_type
            && self.layout.definition_hash() == other.layout.definition_hash()
            && self.layout.selects_layout_path(&[], &other.layout)
    }
}
impl Eq for CAggregateMemberSelection {}
impl Hash for CAggregateMemberSelection {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.layout.definition_hash().hash(state);
        self.path.hash(state);
        self.value_type.hash(state);
    }
}
impl Ord for CAggregateMemberSelection {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let order = self
            .path
            .cmp(&other.path)
            .then_with(|| self.value_type.cmp(&other.value_type))
            .then_with(|| {
                self.layout
                    .definition_hash()
                    .cmp(&other.layout.definition_hash())
            });
        if order != std::cmp::Ordering::Equal {
            return order;
        }
        if self.layout.selects_layout_path(&[], &other.layout) {
            return std::cmp::Ordering::Equal;
        }
        // A content digest only narrows a key comparison. Collision handling
        // retains exact structural ordering; the digest is never evidence.
        self.layout.cmp(&other.layout)
    }
}
impl PartialOrd for CAggregateMemberSelection {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod aggregate_member_key_tests {
    use super::*;

    fn layout() -> CAggregateLayout {
        CAggregateLayout::new(
            8,
            4,
            vec![CAggregateField::new("selected", 0, CType::Int32)],
        )
        .with_declaration_identity(Some(Arc::new(CppRecordDeclarationIdentity::new(
            "key-test", "Root",
        ))))
    }

    fn key(layout: CAggregateLayout) -> CAggregateMemberSelection {
        CAggregateMemberSelection {
            layout: Arc::new(layout),
            path: vec!["selected".into()].into(),
            value_type: CType::Int32,
        }
    }

    #[test]
    fn member_key_cache_tracks_definition_mutations_and_checks_hash_collisions_exactly() {
        let _session = crate::kernel::VerificationSession::enter();
        let original = layout();
        let original_key = key(original.clone());
        assert_eq!(original_key, key(original.clone()));
        let nested = original
            .clone()
            .with_records(vec![CAggregateRecord::new("nested", 4, 4, 4, None)]);
        assert_ne!(original_key, key(nested));
        let other = original.clone().with_declaration_identity(Some(Arc::new(
            CppRecordDeclarationIdentity::new("key-test", "Other"),
        )));
        assert_ne!(original_key, key(other.clone()));
        // Simulate a content-hash collision. A matching digest grants neither
        // semantic key equality nor an authenticated layout selection.
        let mut collision = other;
        let index = Arc::make_mut(&mut collision.index.0);
        index.definition_hash = OnceLock::new();
        index
            .definition_hash
            .set(original.definition_hash())
            .unwrap();
        let collision_key = key(collision);
        assert_ne!(original_key, collision_key);
        assert_ne!(original_key.cmp(&collision_key), std::cmp::Ordering::Equal);
        assert!(!original.selects_layout_path(&[], &collision_key.layout));
        let hash = |value: &CAggregateMemberSelection| {
            let mut state = std::collections::hash_map::DefaultHasher::new();
            value.hash(&mut state);
            state.finish()
        };
        assert_eq!(hash(&original_key), hash(&collision_key));

        let unwarmed = layout().with_records(vec![CAggregateRecord::new("nested", 4, 4, 4, None)]);
        let selection = Arc::new(key(unwarmed));
        let address = CMemory::frame_local_pointer(96, "member-key");
        let memory =
            CMemory::new().with_declared_aggregate_block(address.block.clone(), &selection.layout);
        let object = memory
            .declared_aggregate_pointer(&address, &selection.layout)
            .unwrap();
        let member = memory.checked_member_pointer(&object, &selection).unwrap();
        let mut state = CState::new();
        state.set_memory(memory);
        let proposition = Proposition::CExpressionEvaluates {
            state: Box::new(state),
            expression: CExpression::MemberAddress {
                object: Box::new(CExpression::Value(CValue::Pointer(object))),
                selection: selection.clone(),
            },
            outcome: CExpressionOutcome::Value(CValue::Pointer(member)),
        };
        let fingerprint = |proposition: &Proposition| {
            let mut state = std::collections::hash_map::DefaultHasher::new();
            proposition.hash(&mut state);
            state.finish()
        };
        assert!(selection.layout.index.0.definition_hash.get().is_none());
        let before = fingerprint(&proposition);
        let same = proposition.clone();
        selection.layout.definition_hash();
        assert_eq!(proposition, same);
        assert_eq!(before, fingerprint(&same));
    }
}

/// Optional source provenance attached to a typed load. Two expressions that
/// differ only in this metadata remain equal in kernel collections and caches.
#[derive(Clone, Debug)]
pub struct CExpressionLoadSource(Option<Arc<LoadSourceId>>);

impl CExpressionLoadSource {
    pub(crate) fn none() -> Self {
        Self(None)
    }

    pub(crate) fn new(source: LoadSourceId) -> Self {
        Self(Some(Arc::new(source)))
    }

    pub(crate) fn as_ref(&self) -> Option<&LoadSourceId> {
        self.0.as_deref()
    }
}

impl Default for CExpressionLoadSource {
    fn default() -> Self {
        Self::none()
    }
}

impl PartialEq for CExpressionLoadSource {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl Eq for CExpressionLoadSource {}

impl std::hash::Hash for CExpressionLoadSource {
    fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {}
}

impl Ord for CExpressionLoadSource {
    fn cmp(&self, _other: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

impl PartialOrd for CExpressionLoadSource {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CComparisonOperator {
    Equal,
    NotEqual,
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CFloatBinaryOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CFloatClassification {
    Finite,
    Infinite,
    Zero,
    Subnormal,
    Nan,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CFloatCondition {
    Comparison {
        operator: CComparisonOperator,
        left: Box<Bitvector32Term>,
        right: Box<Bitvector32Term>,
    },
    Classification {
        classification: CFloatClassification,
        value: Box<Bitvector32Term>,
    },
}

impl CFloatCondition {
    pub(crate) fn for_each_bitvector_term(&self, mut visit: impl FnMut(&Bitvector32Term)) {
        match self {
            Self::Comparison { left, right, .. } => {
                visit(left);
                visit(right);
            }
            Self::Classification { value, .. } => visit(value),
        }
    }

    pub(crate) fn map_bitvector_terms(
        &self,
        mut map: impl FnMut(&Bitvector32Term) -> Bitvector32Term,
    ) -> Self {
        match self {
            Self::Comparison {
                operator,
                left,
                right,
            } => Self::Comparison {
                operator: *operator,
                left: Box::new(map(left)),
                right: Box::new(map(right)),
            },
            Self::Classification {
                classification,
                value,
            } => Self::Classification {
                classification: *classification,
                value: Box::new(map(value)),
            },
        }
    }

    pub(crate) fn try_map_bitvector_terms(
        &self,
        mut map: impl FnMut(&Bitvector32Term) -> Option<Bitvector32Term>,
    ) -> Option<Self> {
        Some(match self {
            Self::Comparison {
                operator,
                left,
                right,
            } => Self::Comparison {
                operator: *operator,
                left: Box::new(map(left)?),
                right: Box::new(map(right)?),
            },
            Self::Classification {
                classification,
                value,
            } => Self::Classification {
                classification: *classification,
                value: Box::new(map(value)?),
            },
        })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CUpdateOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
    ShiftLeft,
    ShiftRight,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecMemory {
    Current,
    FunctionEntry,
    LoopEntry,
    Fixed(CMemory),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecExpression {
    Value(CValue),
    /// Convert a mathematical Integer expression back to a machine integer.
    /// The initial kernel stage accepts only exact constant values; symbolic
    /// range-checked conversion is added once its ordinary proof obligations
    /// have a representation in the surrounding spec path.
    IntegerToMachine {
        value: Box<SpecIntegerExpression>,
        destination: MachineIntegerType,
    },
    ResourceField {
        projection: ResourceFieldProjection,
        c_type: CType,
    },
    AlgebraicMatch {
        scrutinee: Box<SpecAlgebraicExpression>,
        arms: Vec<SpecAlgebraicMatchArm>,
    },
    CExpression(CExpression),
    CountedResourceCount {
        name: String,
        arguments: Vec<Option<SpecExpression>>,
    },
    Add(Box<SpecExpression>, Box<SpecExpression>),
    Subtract(Box<SpecExpression>, Box<SpecExpression>),
    Multiply(Box<SpecExpression>, Box<SpecExpression>),
    Divide(Box<SpecExpression>, Box<SpecExpression>),
    Remainder(Box<SpecExpression>, Box<SpecExpression>),
    ShiftLeft(Box<SpecExpression>, Box<SpecExpression>),
    ShiftRight(Box<SpecExpression>, Box<SpecExpression>),
    BitwiseAnd(Box<SpecExpression>, Box<SpecExpression>),
    BitwiseOr(Box<SpecExpression>, Box<SpecExpression>),
    BitwiseXor(Box<SpecExpression>, Box<SpecExpression>),
    BitwiseNot(Box<SpecExpression>),
    Cast(Box<SpecExpression>, CType),
    If {
        condition: Box<SpecProposition>,
        then_branch: Box<SpecExpression>,
        else_branch: Box<SpecExpression>,
    },
    RangeFold {
        start: Box<SpecExpression>,
        end: Box<SpecExpression>,
        initial: Box<SpecExpression>,
        accumulator: String,
        item: String,
        body: Box<SpecExpression>,
    },
    Let {
        name: String,
        value: Box<SpecExpression>,
        body: Box<SpecExpression>,
    },
    PureFunctionApplication {
        name: String,
        arguments: Vec<SpecPureFunctionArgument>,
        result_type: CType,
    },
    LoopEntrySnapshot(Box<SpecExpression>),
    PointerOffset {
        pointer: Box<SpecExpression>,
        elements: Box<SpecExpression>,
        byte_width: u32,
    },
    MemoryLoad {
        memory: SpecMemory,
        pointer: Box<SpecExpression>,
        value_type: CType,
    },
    /// A field of a by-value parameter, not a dereference of a C pointer.
    /// Its logical value remains available after the parameter storage ends.
    AggregateFieldValue {
        parameter: String,
        pointer: Box<SpecExpression>,
        value_type: CType,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct SpecAlgebraicExpression {
    pub algebraic_type: AlgebraicType,
    pub node: SpecAlgebraicExpressionNode,
}

/// A specification-side mathematical integer expression.
///
/// This stays separate from [`SpecExpression`], whose scalar nodes carry C
/// values and therefore have machine-width semantics. Surface lowering
/// resolves names to kernel variables before constructing this form; there is
/// no lookup in `CState.locals` and no C representation.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecIntegerExpression {
    ResourceField(ResourceFieldProjection),
    /// A pure mathematical value. Shared children preserve specification
    /// abbreviations without copying their expanded expression trees.
    Term(IntegerTerm),
    /// An opaque pure function returning a mathematical Integer. Arguments
    /// are evaluated for facts and definedness, while the call remains a
    /// symbolic application until an explicit unfold step.
    PureFunctionApplication {
        name: String,
        arguments: Vec<SpecPureFunctionArgument>,
    },
    AlgebraicMatch {
        scrutinee: Box<SpecAlgebraicExpression>,
        arms: Vec<SpecIntegerMatchArm>,
    },
    FromMachine(Box<SpecExpression>),
    Negate(Box<Self>),
    Add(Box<Self>, Box<Self>),
    Subtract(Box<Self>, Box<Self>),
    Multiply(Box<Self>, Box<Self>),
    TruncatingQuotient(Box<Self>, Box<Self>),
    TruncatingRemainder(Box<Self>, Box<Self>),
    /// A symbolic fold over either machine Int32 or mathematical Integer
    /// endpoints.  The kernel keeps this opaque; bounded expansion belongs
    /// to explicit fold reasoning, so evaluating this node never unrolls a
    /// range in proportion to its endpoint values.
    RangeFold {
        index: SpecIntegerRangeFoldIndex,
        initial: Box<Self>,
        accumulator: Variable,
        item: Variable,
        body: Box<Self>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecIntegerRangeFoldIndex {
    Int32 {
        start: Box<SpecExpression>,
        end: Box<SpecExpression>,
    },
    /// A range of unsigned 64-bit values; see
    /// [`IntegerRangeFoldIndex::UInt64`].
    UInt64 {
        start: Box<SpecExpression>,
        end: Box<SpecExpression>,
    },
    Integer {
        start: Box<SpecIntegerExpression>,
        end: Box<SpecIntegerExpression>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecAlgebraicExpressionNode {
    Variable(Variable),
    Binding(String),
    ResourceField(ResourceFieldProjection),
    Constructor {
        variant: String,
        fields: Vec<SpecAlgebraicValue>,
    },
    Match {
        scrutinee: Box<SpecAlgebraicExpression>,
        arms: Vec<SpecAlgebraicResultMatchArm>,
    },
    PureFunctionApplication {
        name: String,
        arguments: Vec<SpecPureFunctionArgument>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ResourceFieldProjection {
    pub identity: Variable,
    pub children: Vec<String>,
    pub field_index: usize,
    /// Select the explicit entry state supplied to spec evaluation. There is
    /// no fallback to the current state when that snapshot is unavailable.
    pub at_entry: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecPureFunctionArgument {
    Value(SpecExpression),
    Integer(SpecIntegerExpression),
    Algebraic(SpecAlgebraicExpression),
    ArrayRef {
        memory: SpecMemory,
        pointer: SpecExpression,
        element_type: CType,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecAlgebraicValue {
    C(SpecExpression),
    Integer(SpecIntegerExpression),
    Algebraic(SpecAlgebraicExpression),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct SpecAlgebraicMatchArm {
    pub variant: String,
    pub bindings: Vec<String>,
    pub binding_types: Vec<AlgebraicValueType>,
    pub body: SpecExpression,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct SpecAlgebraicResultMatchArm {
    pub variant: String,
    pub bindings: Vec<String>,
    pub binding_types: Vec<AlgebraicValueType>,
    /// Kernel identities of Integer fields in the lowered arm body.
    /// Other carriers are bound through their typed environments.
    pub binding_variables: Vec<Option<Variable>>,
    pub body: Box<SpecAlgebraicExpression>,
}

impl SpecAlgebraicResultMatchArm {
    pub(crate) fn bindings_are_well_formed(&self) -> bool {
        let mut names = BTreeSet::new();
        let mut variables = BTreeSet::new();
        self.bindings.len() == self.binding_types.len()
            && self.bindings.len() == self.binding_variables.len()
            && self.bindings.iter().all(|name| names.insert(name))
            && self
                .binding_types
                .iter()
                .zip(&self.binding_variables)
                .all(|(ty, variable)| {
                    if ty == &AlgebraicValueType::Integer {
                        variable.is_some_and(|variable| variables.insert(variable))
                    } else {
                        variable.is_none()
                    }
                })
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct SpecIntegerMatchArm {
    pub variant: String,
    pub bindings: Vec<String>,
    pub binding_types: Vec<AlgebraicValueType>,
    /// Kernel identities used by Integer binders in the lowered arm body.
    /// C and algebraic binders are represented by their typed environments.
    pub binding_variables: Vec<Option<Variable>>,
    pub body: Box<SpecIntegerExpression>,
}

/// A fully resolved application of a Click algebraic datatype. Keeping the
/// instantiated constructor schema in the kernel term lets the kernel check
/// constructor formation and exhaustive elimination without trusting names
/// supplied by surface lowering.
#[derive(Clone, Debug)]
pub struct AlgebraicType {
    pub rigid: bool,
    pub name: String,
    pub arguments: Vec<AlgebraicValueType>,
    pub variants: std::sync::Arc<[AlgebraicVariantType]>,
    pub schemas: std::sync::Arc<AlgebraicSchemas>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum AlgebraicValueType {
    Parameter(String),
    C(CType),
    Integer,
    Algebraic {
        name: String,
        arguments: Vec<AlgebraicValueType>,
    },
}

/// A resource field has a logical type, never a C storage location.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ResourceFieldType {
    Integer,
    C(CType),
    Algebraic(AlgebraicType),
}

/// Checked declaration metadata. This does not create an owned instance or
/// authorize a memory access; `ResourceInstance` carries identity and state.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ResourceFieldSchema {
    fields: std::sync::Arc<[(String, ResourceFieldType)]>,
}

impl ResourceFieldSchema {
    pub fn new(fields: Vec<(String, ResourceFieldType)>) -> Option<Self> {
        let mut names = BTreeSet::new();
        for (name, ty) in &fields {
            if name.is_empty() || !names.insert(name) {
                return None;
            }
            let valid = match ty {
                ResourceFieldType::C(ty) => !matches!(
                    ty,
                    CType::Void
                        | CType::FunctionPointer(_)
                        | CType::Int8Array(_)
                        | CType::Int16Array(_)
                        | CType::Int32Array(_)
                        | CType::UInt8Array(_)
                        | CType::UInt16Array(_)
                        | CType::UInt32Array(_)
                        | CType::Int128Array(_)
                        | CType::Int64Array(_)
                        | CType::UInt128Array(_)
                        | CType::UInt64Array(_)
                        | CType::Float32Array(_)
                        | CType::Float64Array(_)
                ),
                ResourceFieldType::Integer => true,
                ResourceFieldType::Algebraic(ty) => ty.has_consistent_root_schema(),
            };
            if !valid {
                return None;
            }
        }
        Some(Self {
            fields: fields.into(),
        })
    }

    pub fn fields(&self) -> &[(String, ResourceFieldType)] {
        &self.fields
    }

    pub fn is_fieldless(&self) -> bool {
        self.fields.is_empty()
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct AlgebraicVariantType {
    pub name: String,
    pub fields: Vec<AlgebraicValueType>,
}

/// The finite nominal schema graph shared by every term of one resolved
/// algebraic type family. Groundedness is computed once when the graph is
/// formed so checking each constructor or variable does not rescan schemas
/// unrelated to that term.
#[derive(Debug)]
pub struct AlgebraicSchemas {
    variants:
        std::collections::BTreeMap<AlgebraicValueType, std::sync::Arc<[AlgebraicVariantType]>>,
    grounded: std::collections::BTreeSet<AlgebraicValueType>,
}

impl AlgebraicSchemas {
    pub(crate) fn new(
        variants: std::collections::BTreeMap<
            AlgebraicValueType,
            std::sync::Arc<[AlgebraicVariantType]>,
        >,
    ) -> Self {
        let mut grounded = std::collections::BTreeSet::new();
        loop {
            let before = grounded.len();
            for (value_type, constructors) in &variants {
                if constructors.iter().any(|constructor| {
                    constructor.fields.iter().all(|field| match field {
                        AlgebraicValueType::C(_)
                        | AlgebraicValueType::Integer
                        | AlgebraicValueType::Parameter(_) => true,
                        AlgebraicValueType::Algebraic { .. } => grounded.contains(field),
                    })
                }) {
                    grounded.insert(value_type.clone());
                }
            }
            if grounded.len() == before {
                break;
            }
        }
        Self { variants, grounded }
    }

    pub(crate) fn get(
        &self,
        value_type: &AlgebraicValueType,
    ) -> Option<&std::sync::Arc<[AlgebraicVariantType]>> {
        self.variants.get(value_type)
    }

    #[cfg(test)]
    pub(crate) fn definitions(
        &self,
    ) -> &std::collections::BTreeMap<AlgebraicValueType, std::sync::Arc<[AlgebraicVariantType]>>
    {
        &self.variants
    }

    fn is_grounded(&self, value_type: &AlgebraicValueType) -> bool {
        self.grounded.contains(value_type)
    }
}

/// A logical algebraic value. An arbitrary Click binder is one typed
/// variable; it is not eagerly expanded into a tag and fields for every
/// possible constructor.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct AlgebraicTerm {
    pub algebraic_type: AlgebraicType,
    pub node: AlgebraicTermNode,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum AlgebraicTermNode {
    Variable(Variable),
    Constructor {
        variant: String,
        fields: Vec<AlgebraicValue>,
    },
    Match {
        scrutinee: Box<AlgebraicTerm>,
        arms: Vec<AlgebraicResultMatchArm>,
    },
    PureFunctionApplication {
        name: String,
        arguments: Vec<PureFunctionArgument>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum PureFunctionArgument {
    Value(CValue),
    Integer(SharedIntegerTerm),
    Algebraic(AlgebraicTerm),
    ArrayRef {
        memory: CMemory,
        pointer: CValue,
        element_type: CType,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum AlgebraicValue {
    C(CValue),
    Integer(IntegerTerm),
    Algebraic(AlgebraicTerm),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct AlgebraicBitvectorMatchArm {
    pub variant: String,
    pub bindings: Vec<AlgebraicValue>,
    pub body: Bitvector32Term,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct AlgebraicResultMatchArm {
    pub variant: String,
    pub bindings: Vec<AlgebraicValue>,
    pub body: AlgebraicTerm,
}

impl AlgebraicTerm {
    /// Visit scalar payload roots without expanding datatype schemas or copying
    /// terms. Callers decide how far to traverse each scalar expression.
    pub(crate) fn for_each_bitvector_term(&self, mut visit: impl FnMut(&Bitvector32Term)) {
        enum Node<'a> {
            Algebraic(&'a AlgebraicTerm),
            Value(&'a CValue),
            Offset(&'a PointerOffsetTerm),
            Pointer(&'a Pointer),
            Integer(&'a IntegerTerm),
            SharedInteger(&'a SharedIntegerTerm),
            Argument(&'a PureFunctionArgument),
        }
        let mut pending = vec![Node::Algebraic(self)];
        let mut integers = std::collections::BTreeSet::new();
        let mut pointer_applications = std::collections::BTreeSet::new();
        while let Some(node) = pending.pop() {
            match node {
                Node::Algebraic(term) => match &term.node {
                    AlgebraicTermNode::Variable(_) => {}
                    AlgebraicTermNode::Constructor { fields, .. } => {
                        for field in fields {
                            match field {
                                AlgebraicValue::C(v) => pending.push(Node::Value(v)),
                                AlgebraicValue::Integer(_) => {}
                                AlgebraicValue::Algebraic(v) => pending.push(Node::Algebraic(v)),
                            }
                        }
                    }
                    AlgebraicTermNode::Match { scrutinee, arms } => {
                        pending.push(Node::Algebraic(scrutinee));
                        for arm in arms {
                            pending.push(Node::Algebraic(&arm.body));
                            for binding in &arm.bindings {
                                match binding {
                                    AlgebraicValue::C(v) => pending.push(Node::Value(v)),
                                    AlgebraicValue::Integer(_) => {}
                                    AlgebraicValue::Algebraic(v) => {
                                        pending.push(Node::Algebraic(v))
                                    }
                                }
                            }
                        }
                    }
                    AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
                        for argument in arguments {
                            pending.push(match argument {
                                PureFunctionArgument::Value(v)
                                | PureFunctionArgument::ArrayRef { pointer: v, .. } => {
                                    Node::Value(v)
                                }
                                PureFunctionArgument::Algebraic(v) => Node::Algebraic(v),
                                PureFunctionArgument::Integer(_) => continue,
                            });
                        }
                    }
                },
                Node::Value(value) => match value {
                    CValue::Void => {}
                    CValue::Bool(v) => visit(v),
                    CValue::PointerInteger(value) => {
                        visit(value.bits());
                        let origin = value.origin();
                        pending.push(Node::Pointer(origin.pointer()));
                        if let Some(designation) = origin.designation() {
                            pending.extend(designation.pointer_terms().map(Node::Pointer));
                            pending.extend(designation.integer_terms().map(Node::SharedInteger));
                        }
                    }
                    CValue::Pointer(v) => {
                        pending.push(Node::Pointer(v.pointer()));
                        if let Some(designation) = v.designation() {
                            pending.extend(designation.pointer_terms().map(Node::Pointer));
                            pending.extend(designation.integer_terms().map(Node::SharedInteger));
                        }
                    }
                    CValue::Int8(v) => visit(v),
                    CValue::Int16(v)
                    | CValue::UInt16(v)
                    | CValue::UInt8(v)
                    | CValue::Int32(v)
                    | CValue::UInt32(v)
                    | CValue::Int64(v)
                    | CValue::UInt64(v)
                    | CValue::Int128(v)
                    | CValue::UInt128(v)
                    | CValue::Float32(v)
                    | CValue::Float64(v) => visit(v),
                },
                Node::Offset(offset) => match offset {
                    PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {}
                    PointerOffsetTerm::Add(a, b) => {
                        pending.push(Node::Offset(a));
                        pending.push(Node::Offset(b));
                    }
                    PointerOffsetTerm::Int32Scaled { value, .. }
                    | PointerOffsetTerm::Int64Scaled { value, .. } => visit(value),
                },
                Node::Pointer(pointer) => {
                    crate::instrumentation::record_deterministic_work(1);
                    pending.push(Node::Offset(&pointer.offset));
                    if let PointerBlock::PureFunctionApplication(application) = &pointer.block
                        && pointer_applications.insert(application.id())
                    {
                        pending.extend(application.arguments().iter().map(Node::Argument));
                    }
                }
                Node::Argument(argument) => match argument {
                    PureFunctionArgument::Value(value)
                    | PureFunctionArgument::ArrayRef { pointer: value, .. } => {
                        pending.push(Node::Value(value))
                    }
                    PureFunctionArgument::Integer(integer) => {
                        pending.push(Node::SharedInteger(integer))
                    }
                    PureFunctionArgument::Algebraic(algebraic) => {
                        pending.push(Node::Algebraic(algebraic))
                    }
                },
                Node::SharedInteger(integer) => {
                    crate::instrumentation::record_deterministic_work(1);
                    if integers.insert(integer.id()) {
                        pending.push(Node::Integer(integer.as_ref()));
                    }
                }
                Node::Integer(integer) => {
                    crate::instrumentation::record_deterministic_work(1);
                    match integer {
                        IntegerTerm::Constant(_) | IntegerTerm::Variable(_) => {}
                        IntegerTerm::Machine(machine) => visit(machine.value()),
                        IntegerTerm::Negate(value) => pending.push(Node::SharedInteger(value)),
                        IntegerTerm::Add(left, right)
                        | IntegerTerm::Subtract(left, right)
                        | IntegerTerm::Multiply(left, right)
                        | IntegerTerm::TruncatingQuotient(left, right)
                        | IntegerTerm::TruncatingRemainder(left, right) => {
                            pending.push(Node::SharedInteger(left));
                            pending.push(Node::SharedInteger(right));
                        }
                        IntegerTerm::PureFunctionApplication(application) => {
                            pending.extend(application.arguments().iter().map(Node::Argument));
                        }
                        IntegerTerm::AlgebraicMatch { scrutinee, arms } => {
                            pending.push(Node::Algebraic(scrutinee));
                            for arm in arms {
                                pending.push(Node::SharedInteger(&arm.body));
                                for binding in &arm.bindings {
                                    pending.push(match binding {
                                        AlgebraicValue::C(value) => Node::Value(value),
                                        AlgebraicValue::Integer(integer) => Node::Integer(integer),
                                        AlgebraicValue::Algebraic(algebraic) => {
                                            Node::Algebraic(algebraic)
                                        }
                                    });
                                }
                            }
                        }
                        IntegerTerm::RangeFold {
                            index,
                            initial,
                            body,
                            ..
                        } => {
                            match index {
                                IntegerRangeFoldIndex::Int32 { start, end }
                                | IntegerRangeFoldIndex::UInt64 { start, end } => {
                                    visit(start.value());
                                    visit(end.value());
                                }
                                IntegerRangeFoldIndex::Integer { start, end } => {
                                    pending.push(Node::SharedInteger(start));
                                    pending.push(Node::SharedInteger(end));
                                }
                            }
                            pending.push(Node::SharedInteger(initial));
                            pending.push(Node::SharedInteger(body));
                        }
                    }
                }
            }
        }
    }

    /// Returns a constructor's fields only when the constructor is formed
    /// against this term's resolved datatype schema. Logical variables are
    /// well formed but have no constructor fields.
    pub(in crate::kernel) fn checked_constructor_fields(&self) -> Option<&[AlgebraicValue]> {
        if !self.algebraic_type.has_consistent_root_schema() {
            return None;
        }
        let AlgebraicTermNode::Constructor { variant, fields } = &self.node else {
            return None;
        };
        let schema = self
            .algebraic_type
            .variants
            .iter()
            .find(|schema| schema.name == *variant)?;
        (schema.fields.len() == fields.len()
            && schema.fields.iter().zip(fields).all(|(expected, field)| {
                field.is_well_formed_for(expected, &self.algebraic_type.schemas)
            }))
        .then_some(fields)
    }

    pub(in crate::kernel) fn is_well_formed(&self) -> bool {
        if !self.algebraic_type.has_consistent_root_schema() {
            return false;
        }
        match &self.node {
            AlgebraicTermNode::Variable(_) => true,
            AlgebraicTermNode::Constructor { .. } => self.checked_constructor_fields().is_some(),
            AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
                arguments.iter().all(PureFunctionArgument::is_well_formed)
            }
            AlgebraicTermNode::Match { scrutinee, arms } => {
                !scrutinee.algebraic_type.rigid
                    && scrutinee.is_well_formed()
                    && arms.len() == scrutinee.algebraic_type.variants.len()
                    && scrutinee.algebraic_type.variants.iter().all(|variant| {
                        arms.iter()
                            .filter(|arm| arm.variant == variant.name)
                            .count()
                            == 1
                            && arms
                                .iter()
                                .find(|arm| arm.variant == variant.name)
                                .is_some_and(|arm| {
                                    arm.bindings.len() == variant.fields.len()
                                        && arm.bindings.iter().zip(&variant.fields).all(
                                            |(binding, expected)| {
                                                binding.is_well_formed_for(
                                                    expected,
                                                    &scrutinee.algebraic_type.schemas,
                                                )
                                            },
                                        )
                                        && arm.body.algebraic_type == self.algebraic_type
                                        && arm.body.is_well_formed()
                                })
                    })
            }
        }
    }
}

impl AlgebraicType {
    pub(crate) fn parameter(name: String) -> Self {
        Self {
            rigid: true,
            name,
            arguments: Vec::new(),
            variants: Vec::new().into(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(Default::default())),
        }
    }

    pub(crate) fn value_type(&self) -> AlgebraicValueType {
        if self.rigid {
            return AlgebraicValueType::Parameter(self.name.clone());
        }
        AlgebraicValueType::Algebraic {
            name: self.name.clone(),
            arguments: self.arguments.clone(),
        }
    }

    pub(in crate::kernel) fn resolve_nested_type(
        &self,
        value_type: &AlgebraicValueType,
    ) -> Option<Self> {
        if let AlgebraicValueType::Parameter(name) = value_type {
            return Some(Self::parameter(name.clone()));
        }
        let AlgebraicValueType::Algebraic { name, arguments } = value_type else {
            return None;
        };
        Some(Self {
            rigid: false,
            name: name.clone(),
            arguments: arguments.clone(),
            variants: self.schemas.get(value_type)?.clone(),
            schemas: self.schemas.clone(),
        })
    }

    pub(in crate::kernel) fn has_consistent_root_schema(&self) -> bool {
        if self.rigid {
            return self.arguments.is_empty() && self.variants.is_empty();
        }
        let value_type = self.value_type();
        self.schemas
            .get(&value_type)
            .is_some_and(|variants| variants == &self.variants)
            && self.schemas.is_grounded(&value_type)
    }
}

impl PartialEq for AlgebraicType {
    fn eq(&self, other: &Self) -> bool {
        self.rigid == other.rigid
            && self.name == other.name
            && self.arguments == other.arguments
            && self.variants == other.variants
    }
}

impl Eq for AlgebraicType {}

impl std::hash::Hash for AlgebraicType {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.rigid.hash(state);
        self.name.hash(state);
        self.arguments.hash(state);
        self.variants.hash(state);
    }
}

impl PartialOrd for AlgebraicType {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AlgebraicType {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.rigid, &self.name, &self.arguments, &self.variants).cmp(&(
            other.rigid,
            &other.name,
            &other.arguments,
            &other.variants,
        ))
    }
}

impl From<CValue> for AlgebraicValue {
    fn from(value: CValue) -> Self {
        Self::C(value)
    }
}

impl AlgebraicValue {
    pub fn as_c_value(&self) -> Option<&CValue> {
        match self {
            Self::C(value) => Some(value),
            Self::Integer(_) => None,
            Self::Algebraic(_) => None,
        }
    }

    pub(in crate::kernel) fn value_type(&self) -> AlgebraicValueType {
        match self {
            Self::C(value) => AlgebraicValueType::C(value.c_type()),
            Self::Integer(_) => AlgebraicValueType::Integer,
            Self::Algebraic(value) => value.algebraic_type.value_type(),
        }
    }

    fn is_well_formed_for(
        &self,
        expected: &AlgebraicValueType,
        schemas: &AlgebraicSchemas,
    ) -> bool {
        if &self.value_type() != expected {
            return false;
        }
        match self {
            Self::C(_) => true,
            Self::Integer(_) => true,
            Self::Algebraic(value) => {
                (matches!(expected, AlgebraicValueType::Parameter(_))
                    || schemas
                        .get(expected)
                        .is_some_and(|variants| variants == &value.algebraic_type.variants))
                    && value.is_well_formed()
            }
        }
    }
}

impl PureFunctionArgument {
    fn is_well_formed(&self) -> bool {
        match self {
            Self::Value(_) => true,
            Self::Integer(_) => true,
            Self::Algebraic(term) => term.is_well_formed(),
            Self::ArrayRef {
                pointer,
                element_type,
                ..
            } => pointer.c_type().is_pointer() && *element_type != CType::Void,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecSequenceExpression {
    Literal(Vec<SpecExpression>),
    Concat(Box<SpecSequenceExpression>, Box<SpecSequenceExpression>),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecPredicateArgument {
    Value(SpecExpression),
    ArrayRef {
        memory: SpecMemory,
        pointer: SpecExpression,
    },
}

/// The source-selected type of a location, independent of byte permission
/// and initialization. Record types retain the checked complete layout.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CPlaceType {
    Scalar(CType),
    Record(Arc<CAggregateLayout>),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecProposition {
    IntegerComparison {
        left: SpecIntegerExpression,
        operator: IntegerComparisonOperator,
        right: SpecIntegerExpression,
    },
    AlgebraicComparison {
        left: SpecAlgebraicExpression,
        equal: bool,
        right: SpecAlgebraicExpression,
    },
    SequenceMembership {
        element: SpecExpression,
        sequence: SpecSequenceExpression,
    },
    SequenceComparison {
        left: SpecSequenceExpression,
        equal: bool,
        right: SpecSequenceExpression,
    },
    Comparison {
        left: SpecExpression,
        operator: CComparisonOperator,
        right: SpecExpression,
    },
    FloatClassification {
        expression: SpecExpression,
        classification: CFloatClassification,
    },
    And(Box<SpecProposition>, Box<SpecProposition>),
    Or(Box<SpecProposition>, Box<SpecProposition>),
    Not(Box<SpecProposition>),
    Implies(Box<SpecProposition>, Box<SpecProposition>),
    ForAllInt32 {
        name: String,
        variable: Variable,
        body: Box<SpecProposition>,
    },
    ForAllMachineInteger {
        name: String,
        variable: Variable,
        integer_type: MachineIntegerType,
        body: Box<SpecProposition>,
    },
    ForAllInteger {
        name: String,
        variable: Variable,
        body: Box<SpecProposition>,
    },
    ForAllAlgebraic {
        name: String,
        variable: Variable,
        algebraic_type: AlgebraicType,
        body: Box<SpecProposition>,
    },
    ForAllPointer {
        name: String,
        variable: Variable,
        c_type: CType,
        body: Box<SpecProposition>,
    },
    ExistsInt32 {
        name: String,
        variable: Variable,
        body: Box<SpecProposition>,
    },
    ExistsMachineInteger {
        name: String,
        variable: Variable,
        integer_type: MachineIntegerType,
        body: Box<SpecProposition>,
    },
    ExistsInteger {
        name: String,
        variable: Variable,
        body: Box<SpecProposition>,
    },
    ExistsAlgebraic {
        name: String,
        variable: Variable,
        algebraic_type: AlgebraicType,
        body: Box<SpecProposition>,
    },
    ExistsPointer {
        name: String,
        variable: Variable,
        c_type: CType,
        body: Box<SpecProposition>,
    },
    Predicate {
        name: String,
        arguments: Vec<SpecPredicateArgument>,
        /// Whether the definition observes the resource model. Memory snapshots
        /// remain explicit predicate arguments independently of this flag.
        resource_state_dependent: bool,
    },
    ResourceSeparate {
        left: SpecResource,
        right: SpecResource,
    },
    ResourceContains {
        parent: SpecResource,
        child: SpecResource,
    },
    MemoryLoadable {
        memory: SpecMemory,
        base: SpecExpression,
        start: SpecExpression,
        end: SpecExpression,
        element_width: u32,
    },
    /// Every byte in the fixed range is initialized in the selected snapshot.
    /// This states no byte values and grants no access permission.
    MemoryInitialized {
        memory: SpecMemory,
        base: SpecExpression,
        bytes: u32,
    },
    ValidPlace {
        memory: SpecMemory,
        pointer: SpecExpression,
        range: Option<(SpecExpression, SpecExpression)>,
        place_type: CPlaceType,
        access_policy: CTypedAccessPolicy,
    },
    Defined(SpecExpression),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct SequenceTerm {
    pub element_type: Option<CType>,
    pub node: std::sync::Arc<SequenceTermNode>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SequenceTermNode {
    Literal(std::sync::Arc<[CValue]>),
    Concat(SequenceTerm, SequenceTerm),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecResource {
    Memory {
        base: SpecExpression,
        start: SpecExpression,
        end: SpecExpression,
        element_width: u32,
    },
    Composite {
        name: String,
        arguments: Vec<SpecExpression>,
    },
    Token {
        name: String,
        arguments: Vec<SpecExpression>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CSwitchCase {
    /// `None` is the default case; integer values are represented in the
    /// promoted int32 bit pattern used by C0.
    pub value: Option<u32>,
    pub body: Box<CStatement>,
}

/// Stable identity of one source control-flow target inside a function.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CControlTargetId(pub(crate) u32);

/// The exact executable frontier named by a control-flow target.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct CControlTarget {
    pub(crate) statement_index: usize,
    pub(crate) remaining: std::sync::Arc<CStatement>,
}

/// Allocation and initialization policy for an automatic aggregate object.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CAggregateDeclarationKind {
    /// Ordinary local storage, with no explicit constructor ownership grant.
    Local,
    /// Existing frontend protocol: seed placeholders and require the frontend
    /// to prove that constructors overwrite them before observation.
    Constructor,
    /// Fresh owned storage. Only actual writes initialize its fields.
    ConstructionDestination,
}

/// The source array's element classification, independent of its lowered
/// storage type. Aggregate arrays currently use a byte-array backing without
/// claiming that their source elements are byte scalars.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CArrayObjectKind {
    Scalar,
    AggregateBacking,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CStatement {
    /// An explicit lexical block; automatic locals retire on every exit.
    Scope {
        body: Box<CStatement>,
    },
    Skip,
    Break,
    Continue,
    /// A source-directed edge whose target is resolved in the containing
    /// function's checked control-flow table.
    Goto {
        target: CControlTargetId,
    },
    /// A for-loop update, after leaving the body scope. On a source
    /// `continue` this also transfers control to the loop head; on ordinary
    /// fallthrough it is the first statement of the update clause.
    ForStep {
        step: Box<CStatement>,
        exited_locals: Vec<String>,
        continue_after: bool,
    },
    Declare {
        /// A scalar construction initializer, evaluated after fresh allocation.
        /// This is the only declaration transition permitted to initialize const storage.
        initializer: Option<CExpression>,
        name: String,
        c_type: CType,
        array_object_kind: CArrayObjectKind,
        /// Actual scalar-array dimensions, validated against the declaration.
        array_shape: Option<Arc<[u32]>>,
        volatile: bool,
        pointee_volatile: bool,
        constant: bool,
        pointee_constant: bool,
        /// Present for an automatic array declared with an initializer: the
        /// declaration zero-fills the object, and the initializer's written
        /// elements follow as ordinary stores. Absent, the object is
        /// uninitialized.
        zero_fill: Option<CZeroFill>,
    },
    /// Declare an address-backed scalar-only aggregate. Aggregate values are
    /// not runtime `CValue`s; their local binding exposes the block base so
    /// field lowering can continue to use typed memory accesses.
    DeclareAggregate {
        name: String,
        layout: CAggregateLayout,
        kind: CAggregateDeclarationKind,
    },
    /// Copy an address-backed aggregate, preserving typed views for any
    /// overlapping union members in its layout.
    CopyAggregate {
        target: CExpression,
        source: CExpression,
        layout: CAggregateLayout,
    },
    /// Write a scalar-array region with one evaluated repeated value or a
    /// uniform initialized local source. `fresh` additionally requires complete
    /// fresh local storage. Authority is checked; count never expands into nodes.
    InitializeScalarArray {
        target: CExpression,
        source: CExpression,
        element_type: CType,
        count: u32,
        copy: bool,
        fresh: bool,
    },
    Assign {
        name: String,
        expression: CExpression,
    },
    CallAssign {
        target: String,
        function_name: String,
        arguments: Vec<CExpression>,
    },
    Call {
        function_name: String,
        arguments: Vec<CExpression>,
    },
    /// Allocate a runtime-sized heap block and assign either null or its fresh
    /// base pointer to `target`.
    HeapAllocate {
        target: String,
        bytes: CExpression,
        zeroed: bool,
        allocated_scalar_type: Option<CType>,
    },
    /// End the heap allocation named by `pointer`. Null is a no-op.
    HeapFree {
        pointer: CExpression,
    },
    Assert {
        condition: CExpression,
        label: Option<String>,
    },
    /// Two statement regions whose immutable subtrees are shared by execution
    /// frontiers as they advance through a block.
    Seq(Arc<CStatement>, Arc<CStatement>),
    Return(CExpression),
    /// Produce a checked exceptional outcome. The first internal slice carries
    /// one int32 payload; source-language handler matching lands separately.
    Throw(CExpression),
    /// Catch an int32 exceptional outcome from `try_body` and bind its payload
    /// for the handler. Other outcomes retain their original path and state.
    TryCatchInt32 {
        try_body: Box<CStatement>,
        binding: String,
        handler: Box<CStatement>,
        /// This is an implementation cleanup edge inserted by a frontend,
        /// rather than a source-level handler. Its handler runs cleanup and
        /// rethrows the original payload.
        cleanup_unwind: bool,
    },
    Store {
        pointer: CExpression,
        value: CExpression,
    },
    TypedStore {
        pointer: CExpression,
        value: CExpression,
        value_type: CType,
        /// See [`CExpression::TypedLoad::volatile`].
        volatile: bool,
        /// The destination pointer cell's declared pointee qualification.
        pointee_constant: bool,
    },
    /// Evaluate a compound-assignment or increment target as one lvalue,
    /// read it, apply the operator with the operand, and write the result back.
    Update {
        target: CExpression,
        operator: CUpdateOperator,
        operand: CExpression,
    },
    If {
        condition: CExpression,
        then_branch: Box<CStatement>,
        else_branch: Box<CStatement>,
    },
    While {
        condition: CExpression,
        invariant: Vec<Proposition>,
        invariant_checks: Vec<CLoopInvariantCheck>,
        effect_checks: Vec<CLoopEffectCheck>,
        /// Resources the loop declares for itself. An empty list means the
        /// body executes with the enclosing resource context; a declaration
        /// narrows that context to exactly these resources, with everything
        /// else the enclosing frame owns viewed rather than owned.
        resource_specs: Vec<CResourceSpec>,
        /// The loop's declared `decreases` components, in source order. An
        /// empty list means the loop is unranked. Each component is one
        /// int32-valued expression evaluated at the iteration entry and again
        /// at the back edge; the back-edge invariant bundle carries one
        /// nonnegativity obligation per component and one lexicographic
        /// decrease obligation over them.
        ranking_measures: Vec<CRankingComponent>,
        /// The loop's declared structural `decreases` binder, when the clause
        /// named a loop resource binder instead of int32 components (D6).
        /// The back edge checks that the instance the binder ends holding is
        /// a direct contained child, in the exact resource definition, of the
        /// instance it held at the loop head.
        structural_measure: Option<String>,
        /// Whether the body runs before the first condition check, as in C's
        /// `do ... while` statement.
        do_while: bool,
        /// When present, this is a proof-only natural cycle whose source body
        /// retains a checked `goto` to the target. The matching jump is the
        /// back edge; ordinary completion of the body is the cycle exit.
        backedge_target: Option<CControlTargetId>,
        /// When present, a proof-only natural cycle has one checked forward
        /// `goto` that leaves the cycle at this target.
        natural_exit_target: Option<CControlTargetId>,
        body: Box<CStatement>,
    },
    Switch {
        expression: CExpression,
        cases: Vec<CSwitchCase>,
    },
    /// End selected automatic objects at a frontend-recorded lifetime boundary,
    /// including a full expression's materialized temporaries. This retires
    /// their storage and ownership, never the allocations their fields name.
    EndAutomaticLifetimes {
        names: Vec<String>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CLoopInvariantCheck {
    pub(super) proposition: SpecProposition,
    pub(super) entry_context: Option<String>,
    pub(super) preservation_context: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CLoopEffectCheck {
    pub(super) effect: CLoopEffect,
    pub(super) span: CLoopEffectSpan,
    pub(super) context: Option<String>,
    /// Semantic provenance is typed so diagnostics cannot be mistaken for
    /// authority.  Inherited resource frames are replaced by
    /// `validated_ranges` at the function entry before loop proof starts.
    pub(super) origin: CLoopEffectOrigin,
    pub(super) validated_ranges: Option<Vec<CMemoryRange>>,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CLoopEffectOrigin {
    #[default]
    Unspecified,
    Explicit,
    DeclaredResource,
    InheritedResourceDerived,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CLoopEffect {
    Immutable,
    Mutable(Vec<CMemorySegment>),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CLoopEffectSpan {
    Whole,
    Step,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CMemorySegment {
    pub(super) base: CExpression,
    pub(super) start: CExpression,
    pub(super) end: CExpression,
    /// The ABI width of one logical range element. The compatibility
    /// constructor defaults to the historical int32 width; typed surface
    /// lowering preserves wider struct-array strides here.
    pub(super) element_width: u32,
    /// An optional entry-state condition guarding a contract footprint.
    /// Resource and loop segments are normally unconditional.
    pub(super) guard: Option<SpecProposition>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CMemoryRange {
    pub(super) base: Pointer,
    /// The bounds, in elements. Read them through [`CMemoryRange::start`]
    /// and [`CMemoryRange::end`], which hold only for an `Int32` range, or
    /// through [`CMemoryRange::wide_bounds`]: a term carries no width, so a
    /// wide bound read as a signed 32-bit index is a different number.
    start_bound: Bitvector32Term,
    end_bound: Bitvector32Term,
    /// The size in bytes of one logical element in `start..end`.
    ///
    /// Resource ranges remain expressed in logical element coordinates, but
    /// retaining this width lets kernel consumers derive their physical byte
    /// footprint without recovering the source C type.
    pub(super) element_width: u32,
    /// How the bounds are read. Last, so ranges order by base first and
    /// `Int32` ranges keep the order they had among themselves.
    kind: RangeIndexKind,
}

/// The integer type of a range's bounds. Two ranges with the same terms in
/// different kinds are different ranges.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum RangeIndexKind {
    /// Signed 32-bit element indices, as a C `int` index is.
    Int32,
    /// Unsigned 64-bit element indices, as a C `size_t` or a Rust `usize`.
    UInt64,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct CParameter {
    pub(super) name: String,
    pub(super) c_type: CType,
    pub(super) aggregate_layout: Option<CAggregateLayout>,
    pub(super) volatile: bool,
    pub(super) pointee_volatile: bool,
    pub(super) constant: bool,
    pub(super) pointee_constant: bool,
    /// Source enrollment in the checked native pointer model. This promises
    /// no referent type, extent, lifetime, initialization, or permission.
    pub(super) native_pointer_input: bool,
}

impl std::hash::Hash for CParameter {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.c_type.hash(state);
        self.aggregate_layout.hash(state);
        self.volatile.hash(state);
        self.pointee_volatile.hash(state);
        self.constant.hash(state);
        self.pointee_constant.hash(state);
        // Keep the hash of existing unenrolled interfaces unchanged.
        if self.native_pointer_input {
            "native_pointer_input".hash(state);
            true.hash(state);
        }
    }
}

/// A linked file-scope scalar. Globals use one stable memory block across all
/// function frames; the initial value is installed when the first function
/// entry state is created.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CGlobal {
    pub(super) source_name: String,
    pub(super) kernel_name: String,
    pub(super) c_type: CType,
    pub(super) initial_value: CValue,
    pub(super) volatile: bool,
    pub(super) pointee_volatile: bool,
    pub(super) constant: bool,
    pub(super) pointee_constant: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct CGlobalArray {
    pub(super) source_name: String,
    pub(super) kernel_name: String,
    pub(super) element_type: CType,
    pub(super) length: u32,
    pub(super) array_shape: Option<Arc<[u32]>>,
    pub(super) initial_values: CArrayContents,
    pub(super) constant: bool,
}

impl std::hash::Hash for CGlobalArray {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.source_name.hash(state);
        self.kernel_name.hash(state);
        self.element_type.hash(state);
        self.length.hash(state);
        self.initial_values.hash(state);
        self.constant.hash(state);
        if let Some(shape) = &self.array_shape {
            0x6172_7261_795f_726fu64.hash(state);
            shape.hash(state);
        }
    }
}

/// A linked file-scope aggregate. The layout describes the typed leaf cells
/// that occupy the stable global block; aggregate values themselves have no
/// scalar `CValue` representation.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CGlobalAggregate {
    pub(super) source_name: String,
    pub(super) kernel_name: String,
    pub(super) layout: CAggregateLayout,
    pub(super) initializers: Vec<CAggregateInitializer>,
    pub(super) constant: bool,
}

/// A linked file-scope array of supported struct aggregates. Initializer
/// offsets are relative to the complete array block; omitted cells are
/// zero-filled when the block is first materialized.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CGlobalAggregateArray {
    pub(super) source_name: String,
    pub(super) kernel_name: String,
    pub(super) layout: CAggregateLayout,
    pub(super) length: u32,
    pub(super) initializers: Vec<CAggregateInitializer>,
    pub(super) constant: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CStaticLocal {
    pub(super) source_name: String,
    pub(super) kernel_name: String,
    pub(super) c_type: CType,
    pub(super) initial_value: CValue,
    pub(super) volatile: bool,
    pub(super) pointee_volatile: bool,
    pub(super) constant: bool,
    pub(super) pointee_constant: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct CStaticArray {
    pub(super) source_name: String,
    pub(super) kernel_name: String,
    pub(super) element_type: CType,
    pub(super) length: u32,
    pub(super) array_shape: Option<Arc<[u32]>>,
    pub(super) initial_values: CArrayContents,
    pub(super) constant: bool,
}

impl std::hash::Hash for CStaticArray {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.source_name.hash(state);
        self.kernel_name.hash(state);
        self.element_type.hash(state);
        self.length.hash(state);
        self.initial_values.hash(state);
        self.constant.hash(state);
        if let Some(shape) = &self.array_shape {
            0x6172_7261_795f_726fu64.hash(state);
            shape.hash(state);
        }
    }
}

/// The initial contents of a static-storage scalar array: every element
/// holds `default` except the few an initializer names, which are listed
/// ascending by index, each distinct from `default`.
///
/// A declaration such as `int32 buf[1000000];` or `int32 t[1000] = {1, 2};`
/// writes a handful of elements and leaves the rest zero, so the contents
/// are held as that default and the written elements, shared behind an
/// `Arc`: storing, cloning, comparing and hashing a declaration costs what
/// its initializer wrote, not its declared length. The frontend gives the
/// lowered zero initializer of the element type as the default. The default
/// is part of the identity, and with it the element list is canonical: an
/// element equal to the default is never listed, so two contents with one
/// default are equal exactly when every element holds the same value.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CArrayContents {
    length: u32,
    default: CValue,
    elements: std::sync::Arc<[(u32, CValue)]>,
}

impl CArrayContents {
    /// `length` elements holding `default`, except each listed `(index,
    /// value)`. The indices must be ascending, distinct and below `length`;
    /// a listed value equal to `default` is dropped.
    pub fn new(
        length: u32,
        default: CValue,
        elements: impl IntoIterator<Item = (u32, CValue)>,
    ) -> Self {
        let elements = elements
            .into_iter()
            .filter(|(_, value)| *value != default)
            .collect::<std::sync::Arc<[_]>>();
        assert!(
            elements.windows(2).all(|pair| pair[0].0 < pair[1].0)
                && elements.last().is_none_or(|(index, _)| *index < length),
            "array contents list distinct in-bounds elements in ascending order"
        );
        Self {
            length,
            default,
            elements,
        }
    }

    pub fn length(&self) -> u32 {
        self.length
    }

    /// The value of every element the list does not name.
    pub fn default_value(&self) -> &CValue {
        &self.default
    }

    /// The elements holding something other than the default, ascending.
    pub fn explicit_elements(&self) -> &[(u32, CValue)] {
        &self.elements
    }

    /// Whether some element holds the default.
    pub fn has_default_elements(&self) -> bool {
        self.elements.len() < self.length as usize
    }

    /// The value element `index` holds.
    pub fn value_at(&self, index: u32) -> &CValue {
        match self
            .elements
            .binary_search_by_key(&index, |(element, _)| *element)
        {
            Ok(position) => &self.elements[position].1,
            Err(_) => &self.default,
        }
    }

    /// Every distinct way an element is spelled: the default when some
    /// element holds it, then each listed value.
    pub fn values(&self) -> impl Iterator<Item = &CValue> + '_ {
        self.has_default_elements()
            .then_some(&self.default)
            .into_iter()
            .chain(self.elements.iter().map(|(_, value)| value))
    }

    /// Every element's value in index order, one per element.
    #[cfg(test)]
    pub fn dense_values(&self) -> Vec<CValue> {
        (0..self.length)
            .map(|index| self.value_at(index).clone())
            .collect()
    }
}

impl From<Vec<CValue>> for CArrayContents {
    /// One value per element, index order. The last value is the default,
    /// so a trailing stretch of equal values is not listed.
    fn from(values: Vec<CValue>) -> Self {
        let length = u32::try_from(values.len()).expect("array contents length fits in u32");
        let default = values
            .last()
            .cloned()
            .expect("array contents hold at least one element");
        Self::new(
            length,
            default,
            values
                .into_iter()
                .enumerate()
                .map(|(index, value)| (index as u32, value)),
        )
    }
}

/// `count` cells holding `value`, `stride` bytes apart from `offset` bytes
/// into an object: one [`CellRun`] of an object's known initial contents
/// ([`CMemory::with_constant_runs`]).
///
/// [`CellRun`]: crate::kernel::primitives::CellRun
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CConstantRun {
    pub(crate) offset: u32,
    pub(crate) stride: u32,
    pub(crate) count: u32,
    pub(crate) value: CValue,
}

/// What an automatic array declared with an initializer holds before the
/// initializer's written elements are stored: C zero-initializes every
/// element the initializer does not name (C11 6.7.9p21), so the declaration
/// fills the whole object with zeros at a cost that does not depend on its
/// length, and the written elements follow as ordinary stores. An automatic
/// array declared without an initializer carries none and stays
/// uninitialized.
///
/// The object is `count` elements `stride` bytes apart, and every element
/// receives the same stores of `cells`: each a typed store of a zero
/// initializer at a byte offset within the element, exactly as the frontend
/// would spell element 0's zero stores. The declaration leaves the cells
/// those stores into every element leave.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CZeroFill {
    pub(super) stride: u32,
    pub(super) count: u32,
    pub(super) cells: std::sync::Arc<[CZeroCell]>,
}

/// One zero store of every element of a [`CZeroFill`]: `zero`, the zero
/// initializer's value, stored as a `value_type` cell `offset` bytes into
/// the element, with the store's pointee qualification.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CZeroCell {
    pub(super) offset: u32,
    pub(super) value_type: CType,
    pub(super) pointee_constant: bool,
    pub(super) zero: CValue,
}

impl CZeroFill {
    pub fn new(stride: u32, count: u32, cells: Vec<CZeroCell>) -> Self {
        Self {
            stride,
            count,
            cells: cells.into(),
        }
    }
}

impl CZeroCell {
    pub fn new(offset: u32, value_type: CType, pointee_constant: bool, zero: CValue) -> Self {
        Self {
            offset,
            value_type,
            pointee_constant,
            zero,
        }
    }
}

/// A function-local aggregate with one stable function-qualified block.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CStaticAggregate {
    pub(super) source_name: String,
    pub(super) kernel_name: String,
    pub(super) layout: CAggregateLayout,
    pub(super) initializers: Vec<CAggregateInitializer>,
    pub(super) constant: bool,
}

/// A function-local static array of supported struct aggregates.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CStaticAggregateArray {
    pub(super) source_name: String,
    pub(super) kernel_name: String,
    pub(super) layout: CAggregateLayout,
    pub(super) length: u32,
    pub(super) initializers: Vec<CAggregateInitializer>,
    pub(super) constant: bool,
}

/// Static-storage metadata shared by all copies of a function descriptor.
/// Keeping the collections behind the existing static-storage pointer avoids
/// increasing the size of the recursive `Proposition` enum's
/// function-execution variants.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) struct CFunctionStaticStorage {
    pub(super) static_arrays: Vec<CStaticArray>,
    pub(super) global_aggregates: Vec<CGlobalAggregate>,
    pub(super) global_aggregate_arrays: Vec<CGlobalAggregateArray>,
    pub(super) static_aggregates: Vec<CStaticAggregate>,
    pub(super) static_aggregate_arrays: Vec<CStaticAggregateArray>,
}

/// A function's embedded C string constant. The bytes include the trailing
/// NUL and are installed in a stable read-only memory block at function entry.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CStringLiteral {
    pub(super) name: String,
    pub(super) bytes: Vec<u8>,
    /// The character type of the literal's elements: `UInt8` where plain
    /// `char` is unsigned and `Int8` where it is signed. Each byte is stored
    /// as a cell of this type, holding the byte's value under it.
    pub(super) element_type: CType,
}

/// Check only the selected declaration's compact dimensions. This is object
/// geometry, independent of values, initialization, allocation and authority.
pub(crate) fn checked_scalar_array_shape(element: CType, count: u32, shape: &[u32]) -> Option<u32> {
    if shape.is_empty() || element.scalar_array_type(count).is_none() {
        return None;
    }
    let mut product = 1u32;
    for dimension in shape {
        crate::instrumentation::record_deterministic_work(1);
        if *dimension == 0 {
            return None;
        }
        product = product.checked_mul(*dimension)?;
    }
    (product == count).then_some(())?;
    count
        .checked_mul(element.byte_width())
        .filter(|bytes| *bytes != 0)
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CAggregateField {
    pub(super) name: String,
    pub(super) offset_bytes: u32,
    pub(super) c_type: CType,
    /// The source dimensions of an array field with more than one, outermost
    /// first. `c_type` retains its flat storage extent. Native row selection
    /// validates the nonzero dimensions/product against that actual extent
    /// before using them; presentation alone is not evidence.
    pub(super) array_shape: Option<Vec<u32>>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CAggregateUnionField {
    pub(super) name: String,
    pub(super) offset_bytes: u32,
    pub(super) c_type: CType,
}

impl CAggregateUnionField {
    pub fn new(name: impl Into<String>, offset_bytes: u32, c_type: CType) -> Self {
        Self {
            name: name.into(),
            offset_bytes,
            c_type,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn offset_bytes(&self) -> u32 {
        self.offset_bytes
    }

    pub fn c_type(&self) -> CType {
        self.c_type
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CAggregateUnion {
    pub(super) name: String,
    pub(super) offset_bytes: u32,
    pub(super) size_bytes: u32,
    pub(super) fields: Vec<CAggregateUnionField>,
}

impl CAggregateUnion {
    pub fn new(
        name: impl Into<String>,
        offset_bytes: u32,
        size_bytes: u32,
        fields: Vec<CAggregateUnionField>,
    ) -> Self {
        Self {
            name: name.into(),
            offset_bytes,
            size_bytes,
            fields,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn offset_bytes(&self) -> u32 {
        self.offset_bytes
    }

    pub fn size_bytes(&self) -> u32 {
        self.size_bytes
    }

    pub fn fields(&self) -> &[CAggregateUnionField] {
        &self.fields
    }
}

impl CAggregateField {
    pub fn new(name: impl Into<String>, offset_bytes: u32, c_type: CType) -> Self {
        Self {
            name: name.into(),
            offset_bytes,
            c_type,
            array_shape: None,
        }
    }

    /// Records the source dimensions of a multidimensional array field.
    pub fn with_array_shape(mut self, shape: Option<&[u32]>) -> Self {
        self.array_shape = shape.filter(|shape| shape.len() > 1).map(<[u32]>::to_vec);
        self
    }

    pub fn array_shape(&self) -> Option<&[u32]> {
        self.array_shape.as_deref()
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn offset_bytes(&self) -> u32 {
        self.offset_bytes
    }

    pub fn c_type(&self) -> CType {
        self.c_type
    }
}

/// One explicitly initialized scalar cell in a static-storage aggregate.
/// The aggregate materializer zero-fills the complete layout first, then
/// applies these entries at their ABI-relative offsets.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CAggregateInitializer {
    pub(super) offset_bytes: u32,
    pub(super) value: CValue,
}

impl CAggregateInitializer {
    pub fn new(offset_bytes: u32, value: CValue) -> Self {
        Self {
            offset_bytes,
            value,
        }
    }

    pub fn offset_bytes(&self) -> u32 {
        self.offset_bytes
    }

    pub fn value(&self) -> &CValue {
        &self.value
    }
}

/// A native record declaration in one authenticated C++ semantic import.
/// The importer supplies the validated Clang USR, never a flattened field name.
/// Equal USRs from different imports deliberately do not establish nominal
/// equivalence. This identity supplies no initialization or access authority.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct CppRecordDeclarationIdentity {
    import: Arc<str>,
    declaration: Arc<str>,
}

impl CppRecordDeclarationIdentity {
    pub(crate) fn new(import: &str, declaration: &str) -> Self {
        Self {
            import: import.into(),
            declaration: declaration.into(),
        }
    }
}

/// One explicitly declared embedded record, including its padding. Coordinates
/// are relative to the complete layout; `parent` names an earlier record in
/// its pre-order list, or the complete layout when absent. This is structural
/// metadata; an optional native identity is retained separately and supplies
/// neither initialization nor access authority.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct CAggregateRecord {
    name: String,
    offset_bytes: u32,
    size_bytes: u32,
    alignment_bytes: u32,
    parent: Option<u32>,
    declaration_identity: Option<Arc<CppRecordDeclarationIdentity>>,
}

impl std::hash::Hash for CAggregateRecord {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Preserve the original structural hash when no native token exists.
        self.name.hash(state);
        self.offset_bytes.hash(state);
        self.size_bytes.hash(state);
        self.alignment_bytes.hash(state);
        self.parent.hash(state);
        if let Some(identity) = &self.declaration_identity {
            "cpp_record_declaration".hash(state);
            identity.hash(state);
        }
    }
}

impl CAggregateRecord {
    pub fn new(
        name: impl Into<String>,
        offset_bytes: u32,
        size_bytes: u32,
        alignment_bytes: u32,
        parent: Option<u32>,
    ) -> Self {
        Self {
            name: name.into(),
            offset_bytes,
            size_bytes,
            alignment_bytes,
            parent,
            declaration_identity: None,
        }
    }

    pub(crate) fn with_declaration_identity(
        mut self,
        identity: Option<Arc<CppRecordDeclarationIdentity>>,
    ) -> Self {
        self.declaration_identity = identity;
        self
    }

    pub(crate) fn declaration_identity(&self) -> Option<&Arc<CppRecordDeclarationIdentity>> {
        self.declaration_identity.as_ref()
    }

    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn offset_bytes(&self) -> u32 {
        self.offset_bytes
    }
    pub fn size_bytes(&self) -> u32 {
        self.size_bytes
    }
    pub fn alignment_bytes(&self) -> u32 {
        self.alignment_bytes
    }
    pub fn parent(&self) -> Option<u32> {
        self.parent
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct CAggregateLayout {
    size_bytes: u32,
    alignment_bytes: u32,
    fields: Vec<CAggregateField>,
    unions: Vec<CAggregateUnion>,
    records: Vec<CAggregateRecord>,
    declaration_identity: Option<Arc<CppRecordDeclarationIdentity>>,
    /// An explicit scalar-array declaration, never inferred from empty fields
    /// or a byte-sized record storage type. This grants no memory authority.
    scalar_array: Option<(CType, u32)>,
    index: CAggregateLayoutCache,
}

impl std::hash::Hash for CAggregateLayout {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // The derived index contributes no hash. Extend the previous field
        // sequence only when nominal metadata is present, retaining legacy
        // C/Rust snapshot and load names when the feature is absent.
        self.size_bytes.hash(state);
        self.alignment_bytes.hash(state);
        self.fields.hash(state);
        self.unions.hash(state);
        self.records.hash(state);
        if let Some(identity) = &self.declaration_identity {
            "cpp_record_declaration".hash(state);
            identity.hash(state);
        }
        if let Some(shape) = &self.scalar_array {
            "scalar_array_declaration".hash(state);
            shape.hash(state);
        }
    }
}

/// A derived, immutable query cache, excluded from semantic comparisons. All
/// source collections are private and only the two constructors/with_records
/// can change them; those producers build the corresponding indexes. Layout
/// clones share the cache and record updates share the unchanged leaf indexes.
#[derive(Clone, Debug)]
struct CAggregateLayoutCache(Arc<CAggregateLayoutIndex>);

#[derive(Clone)]
struct CAggregateLayoutIndex {
    fields: Arc<BTreeMap<String, usize>>,
    unions: Arc<BTreeMap<String, usize>>,
    records: BTreeMap<String, usize>,
    records_at: BTreeMap<u32, Vec<usize>>,
    unique_leaves: bool,
    unique_paths: bool,
    definition_hash: OnceLock<u64>,
}

impl std::fmt::Debug for CAggregateLayoutIndex {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Proposition's atomic payload hash uses Debug. Memo warmth must not
        // alter an equal proposition's identity; keep the immutable index
        // rendering and omit only the derived digest cell.
        formatter
            .debug_struct("CAggregateLayoutIndex")
            .field("fields", &self.fields)
            .field("unions", &self.unions)
            .field("records", &self.records)
            .field("records_at", &self.records_at)
            .field("unique_leaves", &self.unique_leaves)
            .field("unique_paths", &self.unique_paths)
            .finish()
    }
}

impl PartialEq for CAggregateLayoutCache {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl Eq for CAggregateLayoutCache {}
impl std::hash::Hash for CAggregateLayoutCache {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}
impl Ord for CAggregateLayoutCache {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}
impl PartialOrd for CAggregateLayoutCache {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl CAggregateLayoutCache {
    fn new(fields: &[CAggregateField], unions: &[CAggregateUnion]) -> Self {
        let mut field_index = BTreeMap::new();
        let mut union_index = BTreeMap::new();
        let mut unique_paths = true;
        for (index, field) in fields.iter().enumerate() {
            crate::instrumentation::record_deterministic_work(1);
            unique_paths &= field_index.insert(field.name.clone(), index).is_none();
        }
        for (index, union) in unions.iter().enumerate() {
            crate::instrumentation::record_deterministic_work(1);
            unique_paths &= union_index.insert(union.name.clone(), index).is_none();
        }
        Self(Arc::new(CAggregateLayoutIndex {
            fields: Arc::new(field_index),
            unions: Arc::new(union_index),
            records: BTreeMap::new(),
            records_at: BTreeMap::new(),
            unique_leaves: unique_paths,
            unique_paths,
            definition_hash: OnceLock::new(),
        }))
    }

    fn with_records(&self, records: &[CAggregateRecord]) -> Self {
        let mut names = BTreeMap::new();
        let mut offsets = BTreeMap::<_, Vec<_>>::new();
        let mut unique_paths = self.0.unique_leaves;
        for (index, record) in records.iter().enumerate() {
            crate::instrumentation::record_deterministic_work(1);
            unique_paths &= names.insert(record.name.clone(), index).is_none();
            offsets.entry(record.offset_bytes).or_default().push(index);
        }
        Self(Arc::new(CAggregateLayoutIndex {
            fields: self.0.fields.clone(),
            unions: self.0.unions.clone(),
            records: names,
            records_at: offsets,
            unique_leaves: self.0.unique_leaves,
            unique_paths,
            definition_hash: OnceLock::new(),
        }))
    }
}

// Successful layout comparisons only: immutable definition handles are retained
// with the numeric keys so allocator address reuse cannot validate a new layout.
// The cache carries no pointer, lifetime, permission or initialization evidence.
thread_local! {
    static AGGREGATE_SELECTION_MATCHES: std::cell::RefCell<BTreeMap<(usize, String, usize), (Arc<CAggregateLayoutIndex>, Arc<CAggregateLayoutIndex>)>> = const { std::cell::RefCell::new(BTreeMap::new()) };
}

pub(super) fn clear_aggregate_selection_matches() {
    AGGREGATE_SELECTION_MATCHES.with(|matches| matches.borrow_mut().clear());
}

impl CAggregateLayout {
    pub fn new_scalar_array(element_type: CType, count: u32) -> Option<Self> {
        Self::new_scalar_array_with_fields(element_type, count, Vec::new())
    }

    pub fn new_scalar_array_with_fields(
        element_type: CType,
        count: u32,
        fields: Vec<CAggregateField>,
    ) -> Option<Self> {
        element_type.pointer_to()?;
        let size = element_type.byte_width().checked_mul(count)?;
        Self::new(size, element_type.abi_alignment(), fields).with_scalar_array(element_type, count)
    }

    /// Retain either compact array storage or its explicitly enumerated copy
    /// fields. Array kind comes from this checked declaration producer.
    fn with_scalar_array(mut self, element_type: CType, count: u32) -> Option<Self> {
        let width = element_type.byte_width();
        if width == 0
            || element_type.pointer_to().is_none()
            || self.size_bytes != width.checked_mul(count)?
            || self.alignment_bytes != element_type.abi_alignment()
            || !self.unions.is_empty()
            || !self.records.is_empty()
            || self.declaration_identity.is_some()
            || (!self.fields.is_empty() && self.fields.len() != usize::try_from(count).ok()?)
        {
            return None;
        }
        for (index, field) in self.fields.iter().enumerate() {
            crate::instrumentation::record_deterministic_work(1);
            if field.c_type != element_type
                || field.offset_bytes != u32::try_from(index).ok()?.checked_mul(width)?
            {
                return None;
            }
        }
        self.scalar_array = Some((element_type, count));
        let mut index = (*self.index.0).clone();
        index.definition_hash = OnceLock::new();
        self.index = CAggregateLayoutCache(Arc::new(index));
        Some(self)
    }

    pub fn scalar_array(&self) -> Option<(CType, u32)> {
        self.scalar_array
    }

    pub fn new(size_bytes: u32, alignment_bytes: u32, fields: Vec<CAggregateField>) -> Self {
        Self::with_unions(size_bytes, alignment_bytes, fields, Vec::new())
    }

    pub fn with_unions(
        size_bytes: u32,
        alignment_bytes: u32,
        fields: Vec<CAggregateField>,
        unions: Vec<CAggregateUnion>,
    ) -> Self {
        assert!(alignment_bytes.is_power_of_two());
        let index = CAggregateLayoutCache::new(&fields, &unions);
        Self {
            size_bytes,
            alignment_bytes,
            fields,
            unions,
            records: Vec::new(),
            declaration_identity: None,
            scalar_array: None,
            index,
        }
    }

    pub(crate) fn with_declaration_identity(
        mut self,
        identity: Option<Arc<CppRecordDeclarationIdentity>>,
    ) -> Self {
        assert!(identity.is_none() || self.scalar_array.is_none());
        // Nominal metadata is part of the definition identity used by checked
        // selection memoization, although the derived indexes stay unchanged.
        let mut index = (*self.index.0).clone();
        index.definition_hash = OnceLock::new();
        self.index = CAggregateLayoutCache(Arc::new(index));
        self.declaration_identity = identity;
        if self.declaration_identity.is_some() {
            self.definition_hash();
        }
        self
    }

    /// Hashing member-expression keys must not rehash an unrelated record.
    /// This immutable digest covers the legacy semantic layout hash exactly;
    /// selection still requires an exact checked shape/nominal comparison.
    fn definition_hash(&self) -> u64 {
        *self.index.0.definition_hash.get_or_init(|| {
            crate::instrumentation::record_deterministic_work(
                1 + self.fields.len()
                    + self.unions.len()
                    + self.records.len()
                    + self
                        .unions
                        .iter()
                        .map(|union| union.fields.len())
                        .sum::<usize>(),
            );
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            self.hash(&mut hasher);
            hasher.finish()
        })
    }

    pub(crate) fn declaration_identity(&self) -> Option<&Arc<CppRecordDeclarationIdentity>> {
        self.declaration_identity.as_ref()
    }

    pub fn size_bytes(&self) -> u32 {
        self.size_bytes
    }

    pub fn alignment_bytes(&self) -> u32 {
        self.alignment_bytes
    }

    pub fn fields(&self) -> &[CAggregateField] {
        &self.fields
    }

    pub fn unions(&self) -> &[CAggregateUnion] {
        &self.unions
    }

    /// Retains explicitly supplied boundaries; leaf names never create them.
    pub fn with_records(mut self, records: Vec<CAggregateRecord>) -> Self {
        assert!(records.is_empty() || self.scalar_array.is_none());
        let mut ancestors = Vec::new();
        for (index, record) in records.iter().enumerate() {
            crate::instrumentation::record_deterministic_work(1);
            while ancestors.last().copied() != record.parent {
                assert!(ancestors.pop().is_some(), "record list must be pre-order");
                crate::instrumentation::record_deterministic_work(1);
            }
            let (start, size, alignment) = match record.parent {
                Some(parent) => {
                    assert!(
                        (parent as usize) < index,
                        "record parent must precede its child"
                    );
                    let parent = &records[parent as usize];
                    (
                        parent.offset_bytes,
                        parent.size_bytes,
                        parent.alignment_bytes,
                    )
                }
                None => (0, self.size_bytes, self.alignment_bytes),
            };
            assert!(record.alignment_bytes.is_power_of_two());
            assert!(record.size_bytes.is_multiple_of(record.alignment_bytes));
            assert!(alignment >= record.alignment_bytes);
            assert!(record.offset_bytes.is_multiple_of(record.alignment_bytes));
            assert!(record.offset_bytes >= start);
            assert!(
                record
                    .offset_bytes
                    .checked_add(record.size_bytes)
                    .is_some_and(|end| start
                        .checked_add(size)
                        .is_some_and(|parent_end| end <= parent_end))
            );
            ancestors.push(u32::try_from(index).expect("record boundary count fits u32"));
        }
        self.index = self.index.with_records(&records);
        self.records = records;
        self
    }

    pub fn records(&self) -> &[CAggregateRecord] {
        &self.records
    }

    /// Follow explicitly supplied declaration selections, never infer a member
    /// path from an address or from a dotted scalar leaf alone.
    pub(crate) fn member_at_path(&self, path: &[String]) -> Option<(u32, CType)> {
        if !self.index.0.unique_paths {
            return None;
        }
        let mut prefix = String::new();
        let mut parent = None;
        for (position, member) in path.iter().enumerate() {
            crate::instrumentation::record_deterministic_work(1);
            if member.is_empty() || member.contains('.') || member.contains('[') {
                return None;
            }
            if !prefix.is_empty() {
                prefix.push('.');
            }
            prefix.push_str(member);
            if let Some(index) = self.index.0.records.get(&prefix) {
                let record = &self.records[*index];
                if record.parent != parent {
                    return None;
                }
                if position + 1 == path.len() {
                    return Some((record.offset_bytes, CType::UInt8Array(record.size_bytes)));
                }
                parent = Some(*index as u32);
            } else if position + 1 == path.len() {
                let field = &self.fields[*self.index.0.fields.get(&prefix)?];
                return Some((field.offset_bytes, field.c_type));
            } else {
                return None;
            }
        }
        None
    }

    pub(in crate::kernel) fn array_member_at_path(&self, path: &[String]) -> Option<(CType, u32)> {
        self.member_at_path(path)?;
        let name = path.join(".");
        // Record boundaries use UInt8Array as their aggregate storage type;
        // they are not scalar byte-array declarations.
        if self.index.0.records.contains_key(&name) {
            return None;
        }
        self.fields[*self.index.0.fields.get(&name)?]
            .c_type
            .array_element_and_count()
    }

    pub(in crate::kernel) fn array_member_shape_at_path(
        &self,
        path: &[String],
    ) -> Option<(CType, u32, Arc<[u32]>)> {
        let (element, count) = self.array_member_at_path(path)?;
        let field = &self.fields[*self.index.0.fields.get(&path.join("."))?];
        let shape: Arc<[u32]> = match field.array_shape.as_deref() {
            Some(shape) => shape.into(),
            None => Arc::from([count]),
        };
        checked_scalar_array_shape(element, count, &shape)?;
        Some((element, count, shape))
    }

    pub(in crate::kernel) fn selects_layout_path(&self, path: &[String], expected: &Self) -> bool {
        if path.is_empty() && Arc::ptr_eq(&self.index.0, &expected.index.0) {
            return true;
        }
        let selected = if path.is_empty() {
            None
        } else {
            let Some((_, CType::UInt8Array(_))) = self.member_at_path(path) else {
                return false;
            };
            Some(
                *self
                    .index
                    .0
                    .records
                    .get(&path.join("."))
                    .expect("selected explicit record"),
            )
        };
        let key = (
            Arc::as_ptr(&self.index.0) as usize,
            path.join("."),
            Arc::as_ptr(&expected.index.0) as usize,
        );
        if AGGREGATE_SELECTION_MATCHES.with(|matches| matches.borrow().contains_key(&key)) {
            return true;
        }
        // First admission compares the selected shape. Repeated accesses index
        // only their explicit path; current pointer/lifetime authentication is
        // deliberately outside this geometry-only memo.
        let valid = match selected {
            Some(index) => self.record_matches_layout(index, expected),
            None => {
                crate::instrumentation::record_deterministic_work(
                    self.fields.len() + self.unions.len() + self.records.len(),
                );
                self == expected
            }
        };
        if valid {
            AGGREGATE_SELECTION_MATCHES.with(|matches| {
                matches
                    .borrow_mut()
                    .insert(key, (self.index.0.clone(), expected.index.0.clone()));
            });
        }
        valid
    }

    /// Exact selection from a complete declaration, including any retained
    /// native identity. Only explicit boundary nodes can select children; the
    /// name indexes merely project that selected node.
    pub(in crate::kernel) fn selects_layout_at(&self, offset: u32, expected: &Self) -> bool {
        if offset == 0 && self == expected {
            return true;
        }
        self.index.0.records_at.get(&offset).is_some_and(|indexes| {
            indexes.iter().any(|index| {
                crate::instrumentation::record_deterministic_work(1);
                self.record_matches_layout(*index, expected)
            })
        })
    }

    fn record_matches_layout(&self, selected: usize, expected: &Self) -> bool {
        if expected.scalar_array.is_some() {
            return false;
        }
        let record = &self.records[selected];
        if record.size_bytes != expected.size_bytes
            || record.alignment_bytes != expected.alignment_bytes
            || record.declaration_identity() != expected.declaration_identity()
            || !self.index.0.unique_paths
            || !expected.index.0.unique_paths
        {
            return false;
        }
        let prefix = format!("{}.", record.name);
        let count = |map: &BTreeMap<String, usize>| {
            map.range(prefix.clone()..)
                .take_while(|(name, _)| name.starts_with(&prefix))
                .map(|_| {
                    crate::instrumentation::record_deterministic_work(1);
                    1usize
                })
                .sum::<usize>()
        };
        if count(&self.index.0.fields) != expected.fields.len()
            || count(&self.index.0.unions) != expected.unions.len()
            || count(&self.index.0.records) != expected.records.len()
        {
            return false;
        }
        for field in &expected.fields {
            crate::instrumentation::record_deterministic_work(1);
            let Some(index) = self.index.0.fields.get(&format!("{prefix}{}", field.name)) else {
                return false;
            };
            let held = &self.fields[*index];
            if held.offset_bytes.checked_sub(record.offset_bytes) != Some(field.offset_bytes)
                || held.c_type != field.c_type
                || held.array_shape != field.array_shape
            {
                return false;
            }
        }
        for union in &expected.unions {
            crate::instrumentation::record_deterministic_work(1);
            let Some(index) = self.index.0.unions.get(&format!("{prefix}{}", union.name)) else {
                return false;
            };
            let held = &self.unions[*index];
            if held.offset_bytes.checked_sub(record.offset_bytes) != Some(union.offset_bytes)
                || held.size_bytes != union.size_bytes
                || held.fields != union.fields
            {
                return false;
            }
        }
        for child in &expected.records {
            crate::instrumentation::record_deterministic_work(1);
            let Some(index) = self.index.0.records.get(&format!("{prefix}{}", child.name)) else {
                return false;
            };
            let held = &self.records[*index];
            let parent = match child.parent {
                None => Some(selected),
                Some(parent) => self
                    .index
                    .0
                    .records
                    .get(&format!(
                        "{prefix}{}",
                        expected.records[parent as usize].name
                    ))
                    .copied(),
            };
            if held.offset_bytes.checked_sub(record.offset_bytes) != Some(child.offset_bytes)
                || held.size_bytes != child.size_bytes
                || held.alignment_bytes != child.alignment_bytes
                || held.declaration_identity != child.declaration_identity
                || held.parent.map(|index| index as usize) != parent
            {
                return false;
            }
        }
        true
    }
}

/// A single scalar referent required by an admitted native reference or an
/// explicit typed constructor access clause. This is independent of byte
/// permission and initialization, and must be checked for the actual value.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CScalarObjectInput {
    pub(crate) parameter_index: usize,
    pub(crate) element_type: CType,
}

/// Source slice validity, independent of permissions and initialized bytes.
/// The native length counts elements and the backing extent fits isize.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CNativeSpanInput {
    pub(crate) parameter_index: usize,
    pub(crate) length_parameter_index: usize,
    pub(crate) element_type: CType,
}

/// Native record-reference validity, independent of storage permissions/init.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CAggregateObjectInput {
    pub(crate) parameter_index: usize,
    pub(crate) layout: Arc<CAggregateLayout>,
}

/// The body-independent interface shared by every way Click can apply a
/// function contract.
///
/// A [`CFunction`] keeps the implementation body and storage alongside this
/// value, but all typed call parameters/result metadata, proof binders,
/// logical clauses, normalized resource terms, effect information, and source
/// provenance live here. Keeping this carrier separate from the body is
/// important for opaque calls: applying a checked summary must not implicitly
/// execute (or even inspect) the concrete body.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CFunctionContractInterface {
    pub(crate) typed_access_policy: CTypedAccessPolicy,
    pub(crate) return_type: CType,
    pub(crate) return_pointee_constant: bool,
    pub(crate) return_aggregate_layout: Option<CAggregateLayout>,
    pub(crate) aggregate_return_mode: CAggregateReturnMode,
    pub(crate) construction_parameter: Option<(usize, CAggregateLayout)>,
    pub(crate) scalar_object_inputs: Vec<CScalarObjectInput>,
    pub(crate) native_span_inputs: Vec<CNativeSpanInput>,
    /// Typed geometry prerequisites, independent of byte authority and initialization.
    pub(crate) native_span_expression_inputs: Arc<[CNativeSpanRequirement]>,
    pub(crate) aggregate_object_inputs: Vec<CAggregateObjectInput>,
    pub(crate) exceptional_signature: CExceptionalSignature,
    pub(crate) parameters: Vec<CParameter>,
    /// Explicit resource-instance binders introduced by a named contract.
    /// These are part of the application interface, not a body assumption.
    pub(crate) proof_parameters: std::sync::Arc<[CResourceSpec]>,
    pub(crate) resource_requires: Vec<CResourceSpec>,
    pub(crate) resource_ensures: Vec<CResourceSpec>,
    pub(crate) resource_constructors: Vec<CResourceSpec>,
    pub(crate) contract_requires: Vec<SpecProposition>,
    /// For each lowered contract requirement, the originating source
    /// `requires` clause, or `None` for a generated definedness clause.
    pub(super) contract_requirement_sources: ContractRequirementSources,
    pub(crate) contract_ensures: Vec<SpecProposition>,
    /// Postconditions for the exceptional channel. These are checked only at
    /// `Throw` outcomes, where the kernel-only exceptional-result binding
    /// names the declared payload. No source frontend exposes this carrier yet.
    pub(crate) exceptional_ensures: Vec<SpecProposition>,
    /// Explicit checked effect information, or source-oriented metadata for
    /// resource-derived frames. Resource-derived memory authority is computed
    /// from the checked transition; this vector remains available to body and
    /// diagnostic consumers without becoming a modular-call input.
    pub(crate) contract_mutable: Vec<CMemorySegment>,
    /// mixtures with startup or explicit effect segments.
    pub(crate) contract_effect_claim_required: bool,
    pub(crate) resource_derived_mutable_frame: bool,
    pub(crate) resource_derived_frame_mixed: bool,
    pub(crate) contract_claims: Vec<CFunctionContractClaim>,
    pub(crate) opaque_contract_supported: bool,
    pub(crate) composite_resource_definitions: Vec<CCompositeResourceDefinition>,
    /// Sorted names of the abstract families that are not `authorized`.
    /// Abstract families have no definition here, so only a name on this list
    /// is known to take no part in population accounting.
    pub(crate) ordinary_abstract_families: Vec<String>,
    /// Contract-local definitions for opaque Click predicate requirements.
    /// Both sides are instantiated at the exact function entry state.
    pub(crate) predicate_unfoldings: Vec<CPredicateUnfolding>,
    /// The function's declared `decreases` measure, when it is a pure
    /// expression rather than one int32 parameter or a structural resource.
    ///
    /// It lives on the interface, beside `contract_requires`, because that is
    /// what a call site reads: applying this contract is the only way a
    /// recursive call happens, and the descent obligation is owed there. It
    /// is lowered exactly as a `requires` is, in the function-contract
    /// elaboration context, so it names no state of its own and the kernel
    /// picks the two states it is read at.
    ///
    /// A lexicographic measure has several components, ranked as a loop's
    /// tuple is; an empty list declares no expression measure.
    pub(crate) recursion_measure: Vec<CRankingComponent>,
    /// The other functions of this function's recursive component, sorted,
    /// when it declares an expression measure. A call to one of them owes the
    /// same descent a self-call owes, against this function's entry reading,
    /// so the measures of a mutually recursive component rank one order.
    /// The termination check refuses a component whose members do not all
    /// name each other here, so a peer left out is a refusal, never an
    /// unranked edge.
    pub(crate) recursion_peers: Vec<String>,
    /// The contract resource binder a structural `decreases t` measure names,
    /// when the measure is ranked at each call rather than by reading the
    /// body: every call to a member of the component passes, for the callee's
    /// own measured binder, an instance whose model is strictly contained in
    /// this function's entry model.
    pub(crate) recursion_binder: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CFunction {
    pub(super) program_entry: bool,
    pub(super) name: String,
    /// Header-provided `static inline` or `static __always_inline` functions
    /// have a checked body but no
    /// Click contract. Calls to them execute that body at the call site
    /// instead of requiring an opaque verified-function rule.
    pub(super) inline_body: bool,
    pub(super) body: CStatement,
    pub(super) source_body: CStatement,
    pub(super) control_targets: std::sync::Arc<BTreeMap<CControlTargetId, CControlTarget>>,
    pub(super) contract_interface: CFunctionContractInterface,
    pub(super) global_variables: Vec<CGlobal>,
    pub(super) global_arrays: Vec<CGlobalArray>,
    pub(super) static_variables: Vec<CStaticLocal>,
    pub(super) static_storage: std::sync::Arc<CFunctionStaticStorage>,
    pub(super) string_literals: Vec<CStringLiteral>,
}

/// Source provenance is planning metadata, not part of a function's checked
/// semantic identity. Its vector remains available through the function
/// accessor, while equality, hashing, and ordering stay neutral so adding a
/// source map cannot invalidate semantic caches or certificates.
#[derive(Clone, Debug, Default)]
pub(super) struct ContractRequirementSources(Vec<Option<usize>>);

impl ContractRequirementSources {
    pub(super) fn as_slice(&self) -> &[Option<usize>] {
        &self.0
    }
}

impl PartialEq for ContractRequirementSources {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl Eq for ContractRequirementSources {}

impl std::hash::Hash for ContractRequirementSources {
    fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {}
}

impl PartialOrd for ContractRequirementSources {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ContractRequirementSources {
    fn cmp(&self, _other: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CPredicateUnfolding {
    pub(super) predicate: SpecProposition,
    pub(super) body: SpecProposition,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CCompositeResourceDefinition {
    /// Typed resource-reference parameters. These describe arguments, not
    /// owned ingredients; custody requires an explicit body clause.
    pub(super) resource_parameters: Vec<CResourceSpec>,
    pub(super) instance_schema: Option<ResourceFieldSchema>,
    pub(super) matched: Option<CResourceMatchBody>,
    pub(super) name: String,
    pub(super) parameters: Vec<CParameter>,
    /// Existential witnesses bound inside the body (`let next: T where P`).
    /// Each is bound like a parameter when the body is instantiated: to the
    /// recorded origin of the word its `where` fact relates it to, or to a
    /// fresh symbolic pointer when no origin is recorded yet.
    pub(super) witnesses: Vec<CParameter>,
    pub(super) condition: Option<SpecProposition>,
    pub(super) recursive: bool,
    /// A same-family child declared inside a matched arm rather than in the
    /// unmatched memory body. `recursive` describes that body, which instance
    /// fold/unfold rewrites; [`CCompositeResourceDefinition::is_recursive`]
    /// answers for the definition as a whole.
    pub(super) matched_recursive: bool,
    /// Whether a body fact reads a population count. Such a fact can change
    /// while the head is lent, so a stable loan cannot carry it.
    pub(super) facts_read_counts: bool,
    /// A definition-level restriction on direct transfer to another thread.
    /// Computed when definitions are installed, including contained families.
    pub(super) thread_confined: bool,
    /// Transitive mutex-authority ingredient marker; contract protocol effects are not modeled yet.
    pub(super) contains_mutex_authority: bool,
    /// Declared `authorized resource`: only these families take part in
    /// population accounting.
    pub(super) authorized: bool,
    /// Whether the family is authorized, holds a population authority, or
    /// contains or names such a family. Computed when definitions are
    /// installed; any other family has no population effect.
    pub(super) reaches_population: bool,
    /// Whether the owned footprint reaches memory no clause instance names:
    /// the definition is on a cycle of families, binds an existential witness
    /// in an instance body, or contains or names a child of such a
    /// definition. Computed when definitions are installed
    /// (`owned_footprint_reach`).
    pub(super) owned_footprint_unnamed: bool,
    /// Whether a body fact mentions an allocation-liveness claim
    /// (`loadable(...)`, directly or through a predicate). A loan of the
    /// composite stabilizes its memory and tokens, not the liveness of
    /// storage the fact names, so such facts are not restored by recovery.
    pub(super) facts_claim_liveness: bool,
    pub(super) contains: Vec<CResourceSpec>,
    /// Named child instances of the unmatched body. A matched definition
    /// keeps its children in its arms instead. Each is of another family: an
    /// unmatched body has no submodel to descend to.
    pub(super) children: Vec<CResourceChildSpec>,
    pub(super) facts: Vec<SpecProposition>,
    /// Compiled fact index to original resource-body fact index. Predicate
    /// unfolding can produce two compiled facts for one source fact.
    pub(super) fact_source_indices: Vec<usize>,
    /// Source spellings are diagnostic metadata. They never justify a fact.
    pub(super) fact_source_spellings: Vec<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CResourceMatchBody {
    pub field_index: usize,
    pub algebraic_type: AlgebraicType,
    pub arms: Vec<CResourceMatchArm>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CResourceMatchArm {
    pub variant: String,
    pub bindings: Vec<String>,
    pub binding_types: Vec<AlgebraicValueType>,
    /// Kernel identities for mathematical Integer constructor bindings.
    /// C and algebraic bindings carry `None`; the identities are fresh
    /// lowering atoms that the selected constructor fields replace after the
    /// kernel has checked the arm schema.
    pub binding_variables: Vec<Option<Variable>>,
    pub contains: Vec<CResourceSpec>,
    pub facts: Vec<SpecProposition>,
    pub children: Vec<CResourceChildSpec>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CResourceChildSpec {
    pub name: String,
    /// The child's own composite resource definition. It may be the parent's
    /// definition or another declared resource; the rewrite resolves it and
    /// checks the child's arguments and fields against that definition.
    pub resource: String,
    pub binding: Variable,
    pub arguments: Vec<CExpression>,
    /// Where each of the child's fields comes from, in the child schema's
    /// order. A same-family child's matched model field must be a proper
    /// submodel: an immediate constructor binding of the same algebraic type.
    pub field_bindings: Vec<CResourceChildField>,
}

/// The source of one field of a child instance a resource body declares.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CResourceChildField {
    /// The selected constructor's binding at this index.
    Constructor(usize),
    /// The parent instance's own field at this index. The child's field then
    /// equals the parent's, as a scalar model value does; it never makes a
    /// same-family child a submodel.
    Parent(usize),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CFunctionContractClaimKey {
    BodySafety,
    Effect(usize),
    Ensure(usize),
    ExceptionalEnsure(usize),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CFunctionContractClaim {
    pub(super) key: CFunctionContractClaimKey,
    pub(super) target: CFunctionContractClaimTarget,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CFunctionContractClaimTarget {
    BodySafety,
    Effect,
    EnsureProposition(usize),
    EnsureResource(usize),
    ExceptionalEnsureProposition(usize),
}

/// Contract return value, separate from every source C identifier.
pub(crate) const C_CONTRACT_RESULT_NAME: &str = "@click:result";

/// Kernel-only binding used while lowering an exceptional postcondition.
/// A future surface syntax may choose its own binder spelling and lower it to
/// this name, just as ordinary postconditions lower their result binding.
pub(crate) const C_EXCEPTIONAL_RESULT_NAME: &str = "__click_exception";

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CFunctionSpecification {
    pub(super) state: CState,
    pub(super) arguments: Vec<CExpression>,
    pub(super) requires: Vec<Proposition>,
    pub(super) outcome: CFunctionOutcome,
}

/// One checked binder transport selected at an ordinary C call site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CCallBinderTransport {
    /// The callee the step named. A call to any other function is refused.
    pub(crate) function: std::sync::Arc<str>,
    /// How many arguments the step wrote, checked against the call it selects.
    pub(crate) arity: usize,
    /// Every instance binder of that callee, mapped to the caller instance
    /// that supplies it. A `produces` binder maps to the fresh identity the
    /// caller's `let` introduced.
    pub(crate) bindings: std::sync::Arc<BTreeMap<Variable, Variable>>,
    /// Runtime binders that name a resource type, evaluated at the call.
    pub(crate) type_arguments: std::sync::Arc<BTreeMap<Variable, super::ResourceDescription>>,
}

impl CCallBinderTransport {
    /// Whether a call statement's target is the callee the step named. A
    /// sidecar names a header-provided `static inline` helper by its source
    /// spelling, while the call carries the helper's translation-unit-local
    /// execution name `name#inline:unit`, so that suffix is not part of the
    /// comparison. The call at the frontier is one call to one body either
    /// way; this only decides whether the step named it.
    pub(crate) fn names_call_to(&self, function_name: &str) -> bool {
        let source_spelling = function_name
            .split_once("#inline:")
            .map_or(function_name, |(source, _)| source);
        source_spelling == self.function.as_ref()
    }
}

/// The order in which a target lays out the bytes of a multi-byte integer
/// object. The kernel owns what a byte view of an integer cell means, so the
/// order is a kernel value that the surface installs from the selected C
/// target. Only [`ByteOrder::Little`] has a byte view; `Big` exists so a
/// byte access under any other order is a refusal rather than a guess.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ByteOrder {
    /// Byte `k` of an integer object holds bits `8k .. 8k + 8` of its value.
    #[default]
    Little,
    /// No selectable target uses it; every byte view is refused under it.
    Big,
}

#[derive(Clone, Default)]
pub struct CExecutionEnvironment {
    // A proof-local rule choice. This is not installed in the project environment.
    pub(crate) selected_call_contract: Option<std::sync::Arc<str>>,
    pub(crate) selected_call_resource_arguments: Option<std::sync::Arc<[Variable]>>,
    /// A proof-local binder map for one ordinary C call: the callee named by
    /// the step, and one caller instance per instance binder the callee
    /// declares. Binding is a lookup per entry; nothing is searched for.
    pub(crate) selected_call_binders: Option<std::sync::Arc<CCallBinderTransport>>,
    pub(super) functions: std::sync::Arc<BTreeMap<String, CFunction>>,
    pub(super) function_contracts: std::sync::Arc<BTreeMap<String, CFunctionContract>>,
    pub(super) external_function_rules: std::sync::Arc<BTreeMap<String, CExternalFunctionRule>>,
    pub(super) verified_function_rules: std::sync::Arc<BTreeMap<String, CVerifiedFunctionRule>>,
    pub(super) verified_function_termination_rules:
        std::sync::Arc<BTreeMap<String, CVerifiedFunctionTerminationRule>>,
    /// Installed only after the surface checks the exact built-in header and
    /// selected runtime. A pthread call must use its checked transition; an
    /// ordinary external function contract is never a substitute.
    pub(super) modeled_pthread_binding:
        Option<crate::languages::c::thread_runtime::ModeledPthreadBinding>,
    /// Resource-definition metadata for selected modeled mutex calls. Named
    /// lookup avoids scanning unrelated project definitions at each call.
    pub(super) modeled_mutex_definitions:
        std::sync::Arc<BTreeMap<String, CCompositeResourceDefinition>>,
    /// The same definitions as one name-sorted slice, for deriving the
    /// footprint of a protected resource whose body reaches other families.
    pub(super) modeled_mutex_definition_list: std::sync::Arc<[CCompositeResourceDefinition]>,
    /// The selected target's byte order. It decides whether a one-byte C
    /// access inside a wider integer cell reads or updates that cell's
    /// representation; see `crate::kernel::eval::byte_view`.
    pub(super) byte_order: ByteOrder,
    pub(super) verified_loop_rules: std::sync::Arc<Vec<CVerifiedLoopRule>>,
    /// The function currently being certified, when it declares an expression
    /// `decreases` measure. It is part of this environment's identity below,
    /// so a checked execution recorded without it is not reused to certify a
    /// contract whose function declares one: an artifact stepped with no
    /// anchor emitted no descent obligation, and certification must not take
    /// it for one that did.
    pub(super) recursion_anchor: Option<std::sync::Arc<CRecursionAnchor>>,
    /// Exact contract certification may split an undecided conditional
    /// resource effect at a verified call boundary. Ordinary proof execution
    /// leaves this off, so an undecided guard remains an actionable call
    /// failure there.
    pub(super) allow_conditional_resource_cases: bool,
    pub(super) variable_index: CExecutionEnvironmentVariableIndex,
}

impl std::fmt::Debug for CExecutionEnvironment {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("CExecutionEnvironment")
            .field("selected_call_contract", &self.selected_call_contract)
            .field(
                "selected_call_resource_arguments",
                &self.selected_call_resource_arguments,
            )
            .field("selected_call_binders", &self.selected_call_binders)
            .field("functions", &self.functions)
            .field("function_contracts", &self.function_contracts)
            .field("external_function_rules", &self.external_function_rules)
            .field("verified_function_rules", &self.verified_function_rules)
            .field(
                "verified_function_termination_rules",
                &self.verified_function_termination_rules,
            )
            .field("modeled_pthread_binding", &self.modeled_pthread_binding)
            .field("modeled_mutex_definitions", &self.modeled_mutex_definitions)
            .field("byte_order", &self.byte_order)
            .field("verified_loop_rules", &self.verified_loop_rules)
            .field("recursion_anchor", &self.recursion_anchor)
            .field(
                "allow_conditional_resource_cases",
                &self.allow_conditional_resource_cases,
            )
            .finish()
    }
}

impl PartialEq for CExecutionEnvironment {
    fn eq(&self, other: &Self) -> bool {
        self.selected_call_contract == other.selected_call_contract
            && self.selected_call_resource_arguments == other.selected_call_resource_arguments
            && self.selected_call_binders == other.selected_call_binders
            && self.functions == other.functions
            && self.function_contracts == other.function_contracts
            && self.external_function_rules == other.external_function_rules
            && self.verified_function_rules == other.verified_function_rules
            && self.verified_function_termination_rules == other.verified_function_termination_rules
            && self.modeled_pthread_binding == other.modeled_pthread_binding
            && self.modeled_mutex_definitions == other.modeled_mutex_definitions
            && self.byte_order == other.byte_order
            && self.verified_loop_rules == other.verified_loop_rules
            && self.recursion_anchor == other.recursion_anchor
            && self.allow_conditional_resource_cases == other.allow_conditional_resource_cases
    }
}

impl Eq for CExecutionEnvironment {}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CCallSemantics {
    ExecuteBodies,
    ApplyVerifiedRules,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CLoopSemantics {
    Verify,
    ApplyVerifiedRules,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CExecutionSemantics {
    pub calls: CCallSemantics,
    pub loops: CLoopSemantics,
}

impl CExecutionSemantics {
    pub const EXECUTE_BODIES: Self = Self {
        calls: CCallSemantics::ExecuteBodies,
        loops: CLoopSemantics::Verify,
    };

    pub const APPLY_VERIFIED_RULES: Self = Self {
        calls: CCallSemantics::ApplyVerifiedRules,
        loops: CLoopSemantics::ApplyVerifiedRules,
    };

    pub const APPLY_CALL_RULES_AND_VERIFY_LOOPS: Self = Self {
        calls: CCallSemantics::ApplyVerifiedRules,
        loops: CLoopSemantics::Verify,
    };
}

/// The environment a C execution runs in and the semantics it runs under,
/// which kernel execution threads through every statement and call
/// together.
#[derive(Clone, Copy)]
pub(crate) struct CExecutionContext<'a> {
    pub(crate) environment: &'a CExecutionEnvironment,
    pub(crate) semantics: CExecutionSemantics,
}

impl<'a> CExecutionContext<'a> {
    pub(crate) fn new(
        environment: &'a CExecutionEnvironment,
        semantics: CExecutionSemantics,
    ) -> Self {
        Self {
            environment,
            semantics,
        }
    }

    /// Runs callee bodies and verifies loops.
    pub(crate) fn execute_bodies(environment: &'a CExecutionEnvironment) -> Self {
        Self::new(environment, CExecutionSemantics::EXECUTE_BODIES)
    }

    /// Applies verified call and loop rules.
    pub(crate) fn apply_verified_rules(environment: &'a CExecutionEnvironment) -> Self {
        Self::new(environment, CExecutionSemantics::APPLY_VERIFIED_RULES)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CVerifiedFunctionRule {
    pub(super) function: CFunction,
    /// Original source declaration paired with successful certification. The
    /// certified interface may include proof-entry loop/frame annotations.
    pub(super) source_declaration: Option<std::sync::Arc<CFunction>>,
    pub(super) pointer_result_effects: std::sync::Arc<[CPointerResultEffect]>,
    pub(super) pointer_store_effects: std::sync::Arc<[CPointerStoreEffect]>,
    pub(super) native_output_places_certified: bool,
    /// The loop semantics every claim of this rule was certified under, or
    /// `Verify` when any was, or when the rule is a recursion hypothesis
    /// that certified nothing. Written by the kernel from its own
    /// certification, so the termination check may trust it: under
    /// `ApplyVerifiedRules` a loop with no verified loop rule ran to its
    /// exit on every certified path.
    pub(super) loop_semantics: CLoopSemantics,
    /// The user-defined tactics this rule's certified proofs applied, by
    /// name. A tactic's procedure runs no code, so its body has no calls;
    /// these applications are its call edges, written by the kernel from the
    /// checked traces, so the termination check may trust them.
    pub(super) applied_tactics: std::collections::BTreeSet<String>,
    /// Complete conservative call dependencies from kernel-checked execution.
    /// None retains source-call analysis; a present empty set proves no calls.
    /// Shared across claims and certificate reuse, never copied per step.
    pub(super) checked_callees: Option<Arc<BTreeSet<String>>>,
}

/// A designation relationship certified from every normal body outcome.
/// This is deliberately separate from address-only source postconditions.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) enum CPointerResultEffect {
    /// Exact initialized pointer-valued field read from the input snapshot.
    ExactFromPointerField { source: CPointerFieldSource },
    /// Preserve the initialized input field's full domain, allowing a checked displacement.
    FromPointerField { source: CPointerFieldSource },
    /// Every checked return preserves both the selected address and designation.
    ExactFromParameter {
        parameter: usize,
        child_path: std::sync::Arc<[String]>,
    },
    /// Only the selected domain is preserved; the returned address can move
    /// within it and remains independently constrained by the source contract.
    FromParameter {
        parameter: usize,
        child_path: std::sync::Arc<[String]>,
    },
    /// The body returns a semantic carrier, but no transport relationship
    /// is expressible in this bounded interface. Its result stays unresolved.
    Opaque,
}

/// Full pointer cells retained only from complete authenticated body execution.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) enum CPointerEffectRoot {
    Parameter(usize),
    ConstructionDestination,
}

/// A pointer value stored in a member, distinct from its member address.
/// The retained nominal layout and declared full-width pointer type are part
/// of the selector; numeric address equality never authenticates this source.
#[derive(Clone, Debug)]
pub(super) struct CPointerFieldSource {
    pub(super) parameter: usize,
    pub(super) layout: Arc<CAggregateLayout>,
    pub(super) path: Arc<[String]>,
    pub(super) value_type: CType,
    pub(super) pointee_constant: bool,
    pub(super) pointee_volatile: bool,
}

impl CPointerFieldSource {
    fn selection(&self) -> CAggregateMemberSelection {
        CAggregateMemberSelection {
            layout: self.layout.clone(),
            path: self.path.clone(),
            value_type: self.value_type,
        }
    }
}
impl PartialEq for CPointerFieldSource {
    fn eq(&self, other: &Self) -> bool {
        self.parameter == other.parameter
            && self.pointee_constant == other.pointee_constant
            && self.pointee_volatile == other.pointee_volatile
            && self.selection() == other.selection()
    }
}
impl Eq for CPointerFieldSource {}
impl Hash for CPointerFieldSource {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.parameter.hash(state);
        self.selection().hash(state);
        self.pointee_constant.hash(state);
        self.pointee_volatile.hash(state);
    }
}
impl Ord for CPointerFieldSource {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.parameter
            .cmp(&other.parameter)
            .then_with(|| self.selection().cmp(&other.selection()))
            .then_with(|| self.pointee_constant.cmp(&other.pointee_constant))
            .then_with(|| self.pointee_volatile.cmp(&other.pointee_volatile))
    }
}
impl PartialOrd for CPointerFieldSource {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) struct CPointerStoreEffect {
    /// Present only for a body-checked input-field preservation equation.
    pub(super) destination_field: Option<CPointerFieldSource>,
    pub(super) destination: CPointerEffectRoot,
    pub(super) destination_path: std::sync::Arc<[String]>,
    pub(super) value_type: CType,
    pub(super) source: CPointerEffectRoot,
    pub(super) source_path: std::sync::Arc<[String]>,
    pub(super) source_field: Option<CPointerFieldSource>,
}

#[cfg(test)]
mod pointer_field_source_key_tests {
    use super::*;

    #[test]
    fn pointer_field_source_keys_cache_the_declared_layout() {
        let mut warm_work = Vec::new();
        for size in [0, 16, 64, 256] {
            let mut fields = vec![CAggregateField::new("data", 0, CType::Int32Pointer)];
            fields.extend((0..size).map(|index| {
                CAggregateField::new(format!("unused{index}"), 8 + index * 4, CType::Int32)
            }));
            let layout = Arc::new(CAggregateLayout::new(8 + size * 4, 8, fields));
            let key = CPointerFieldSource {
                parameter: 0,
                layout: layout.clone(),
                path: vec!["data".into()].into(),
                value_type: CType::Int32Pointer,
                pointee_constant: false,
                pointee_volatile: false,
            };
            let digest = |key: &CPointerFieldSource| {
                let mut hash = std::collections::hash_map::DefaultHasher::new();
                key.hash(&mut hash);
                hash.finish()
            };
            assert!(layout.index.0.definition_hash.get().is_none());
            let cold = digest(&key);
            assert!(layout.index.0.definition_hash.get().is_some());
            let (warm, work) = crate::instrumentation::measure_deterministic_work(|| {
                assert_eq!(key, key.clone());
                assert_eq!(key.cmp(&key.clone()), std::cmp::Ordering::Equal);
                digest(&key)
            });
            assert_eq!(cold, warm);
            warm_work.push(work);
            let mut other = key.clone();
            other.parameter = 1;
            assert_ne!(key, other);
            other = key.clone();
            other.pointee_constant = true;
            assert_ne!(key, other);
        }
        assert!(
            warm_work.windows(2).all(|pair| pair[1] <= pair[0] + 8),
            "{warm_work:?}"
        );
    }
}

impl CVerifiedFunctionRule {
    /// How the certification behind this rule ran the function's loops.
    pub fn loop_semantics(&self) -> CLoopSemantics {
        self.loop_semantics
    }
}

/// A nominal, body-independent behavioral interface for an indirect call.
///
/// Named contracts retain only their nominal name and this checked interface.
/// A source function may be used to build the interface, but its body, globals,
/// and static storage are not part of a callback contract and are discarded at
/// construction. This keeps indirect application independent of an arbitrary
/// source/template representation.
#[derive(Clone, Debug)]
pub struct CFunctionContract {
    pub(super) name: String,
    /// Source-name provenance retained only for diagnostics. It is not part
    /// of the contract identity and cannot alter callback behavior.
    pub(super) callee_name: String,
    pub(super) interface: CFunctionContractInterface,
}

impl PartialEq for CFunctionContract {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.interface == other.interface
    }
}

impl Eq for CFunctionContract {}

impl std::hash::Hash for CFunctionContract {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.interface.hash(state);
    }
}

impl PartialOrd for CFunctionContract {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CFunctionContract {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.name
            .cmp(&other.name)
            .then_with(|| self.interface.cmp(&other.interface))
    }
}

/// A recognized byte-representation copy primitive's checked effect.
///
/// The effect transfers initialized typed cells from the source byte range of
/// a call to its destination byte range whenever the copy covers each cell's
/// complete representation. It is attached to the exact declaration the
/// surface matched, not inferred from a function name, so a user function that
/// happens to be called `memcpy` never acquires it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RepresentationCopyEffect {
    /// Argument position of the destination byte pointer (`uint8[]`).
    pub destination_argument: usize,
    /// Argument position of the source byte pointer (`uint8[]`).
    pub source_argument: usize,
    /// Argument position of the runtime byte count (`int32`).
    pub bytes_argument: usize,
}

/// A contract supplied for a C function whose implementation is outside the
/// verified source set. External rules are intentionally distinct from
/// [`CVerifiedFunctionRule`]: they are assumptions accepted at call sites,
/// not evidence that Click checked a function body.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CExternalFunctionRule {
    pub(super) function: CFunction,
    /// This assumption names a concrete, well-formed function whose proof is
    /// outside the current partial-verification selection. It never escapes
    /// that selection's environment.
    pub(super) scoped_unselected: bool,
    /// Set only for a recognized byte-copy declaration whose checked effect
    /// the kernel applies after the external contract.
    pub(super) representation_copy: Option<RepresentationCopyEffect>,
}

impl CExternalFunctionRule {
    pub(in crate::kernel) fn is_scoped_unselected(&self) -> bool {
        self.scoped_unselected
    }
    /// Attaches the checked representation-copy effect to this rule. The
    /// caller must have matched an exact declaration, not a bare name.
    pub(crate) fn with_representation_copy(mut self, effect: RepresentationCopyEffect) -> Self {
        self.representation_copy = Some(effect);
        self
    }

    pub(in crate::kernel) fn representation_copy(&self) -> Option<RepresentationCopyEffect> {
        self.representation_copy
    }
}

/// Kernel evidence that a partially-correct C function also returns.
///
/// Construction is deliberately separate from [`CVerifiedFunctionRule`], so
/// ordinary opaque calls never acquire a total-correctness assumption.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CVerifiedFunctionTerminationRule {
    pub(super) function: CFunction,
}

/// An untrusted surface-language proposal for ranking the cycles in one C
/// function. The kernel checks every supplied index and expression against the
/// exact body before producing termination evidence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CFunctionTerminationPlan {
    pub(super) function_name: String,
    pub(super) recursive_measure: Option<CFunctionTerminationMeasure>,
    pub(super) loop_measures: BTreeMap<usize, CLoopTerminationMeasure>,
}

/// One loop's declared `decreases` measure (D6).
///
/// The clause is one expression at the surface; what it names decides which
/// of these the loop carries, and the loop head carries the same choice, so
/// the back-edge check and this plan cannot describe different measures.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CLoopTerminationMeasure {
    /// Scalar int32 components, in source order, ranked lexicographically by
    /// the back-edge invariant bundle.
    Ranking(Vec<CRankingMeasureKey>),
    /// A loop resource binder whose instance must descend to a direct
    /// contained child of the instance it held at the loop head.
    Structural(String),
}

/// One `decreases` component as the loop head carries it.
///
/// A component is either a current-state C expression, which the ranking
/// reader folds structurally, or a pure specification expression lowered
/// exactly as a loop invariant's expression is. Either way the kernel holds
/// ONE component per declared slot and evaluates that one object itself at
/// the iteration-entry state and again at the back-edge state; the surface
/// never hands the kernel a separate "pre" and "post" term.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CRankingComponent {
    /// Today's measure: a scalar int32 C expression over locals and reads.
    CExpression(CExpression),
    /// A pure int32 specification expression: C fragments, memory reads and
    /// pure function applications, evaluated by the spec evaluator at each of
    /// the two states the ranking obligation compares.
    Pure {
        /// The declared spelling. The whole-function termination plan is
        /// built before specification lowering has an environment, so it
        /// names a pure component by this spelling and the check matches it
        /// against the spelling this certified component carries.
        source: String,
        expression: SpecExpression,
    },
    /// A pure mathematical `Integer` specification expression, evaluated by
    /// the same Integer evaluator a `requires` clause's Integer operand is,
    /// at each of the two states the ranking obligation compares.
    ///
    /// A counting measure over an array range is naturally an `Integer`: an
    /// int32 fold's `+` is partial in specifications, so its bounds are not
    /// provable at a symbolic length. The two obligations are the same two,
    /// built over `Integer` instead of int32; `<` on the nonnegative Integers
    /// is well founded for the same reason `<` on the nonnegative int32s is.
    PureInteger {
        /// The declared spelling, read exactly as [`Self::Pure`]'s is.
        source: String,
        expression: SpecIntegerExpression,
    },
}

impl CRankingComponent {
    /// How the whole-function termination plan names this component.
    pub(super) fn key(&self) -> CRankingMeasureKey {
        match self {
            Self::CExpression(expression) => CRankingMeasureKey::CExpression(expression.clone()),
            Self::Pure { source, .. } | Self::PureInteger { source, .. } => {
                CRankingMeasureKey::Pure(source.clone())
            }
        }
    }
}

/// The value of one `decreases` component at one state, in the carrier its
/// declaration chose.
///
/// The carrier is a function of the component, not of the state: a
/// [`CRankingComponent::PureInteger`] reads as an `Integer` at every state and
/// the other two read as the machine type C's usual arithmetic conversions
/// give the expression -- int32, uint32, or uint64 -- which is a function of
/// the declared types it names, so it is the same at every state. A reading
/// whose carrier differs from the other reading's is refused rather than
/// coerced. That is what lets the
/// two obligations be built from the two readings of one component without
/// asking which carrier each reading happened to land in.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CRankingMeasureValue {
    /// A machine int32 quantity, ranked by signed comparison.
    Machine(Bitvector32Term),
    /// A machine uint32 quantity, ranked by unsigned comparison of the value
    /// C computes, wraparound included. Every such value is a natural number
    /// below 2^32, so it is nonnegative by construction.
    Unsigned32(Bitvector32Term),
    /// A machine uint64 quantity, ranked by unsigned 64-bit comparison of the
    /// value C computes, wraparound included; nonnegative by construction.
    Unsigned64(Bitvector32Term),
    /// A machine int64 quantity, ranked by signed 64-bit comparison. Like an
    /// int32 it owes `0 <= m`.
    Signed64(Bitvector32Term),
    /// A mathematical Integer quantity, ranked by Integer comparison.
    Integer(IntegerTerm),
}

/// How an untrusted termination plan names one declared `decreases`
/// component, for matching the plan against the loop rule that certified the
/// back-edge bundle. A C component is matched as the expression it is; a pure
/// component is matched by its declared spelling, because both the plan and
/// the loop head read that spelling from the same source clause.
///
/// # Why the weaker match is not a soundness question
///
/// `Pure` matches by declared spelling, which is weaker than the structural
/// equality `CExpression` gets: two different lowered expressions declared
/// with the same spelling compare equal here. That is deliberate, and it does
/// not widen what can be proved, because this comparison is not the
/// termination evidence.
///
/// The evidence is the certified loop's own back-edge invariant bundle. That
/// bundle carries one `0 <= m` member and one lexicographic `m_post < m_pre`
/// member per declared component, built by the kernel from the
/// `CRankingComponent` the rule's loop head carries and evaluated by the
/// kernel at the iteration-entry and back-edge states. A loop whose bundle
/// closed has a nonnegative int32 quantity that strictly decreases on every
/// back edge, which is what makes it terminate; *which* int32 quantity it was
/// does not enter that argument, so no spelling can make a loop that does not
/// descend look as if it does.
///
/// What the plan supplies is only an index: for each loop of the source body,
/// which rule's certification to point at. `check_loops` in
/// `crate::kernel::termination` matches by loop index and refuses any loop
/// that the plan ranks but no rule certified; `verified_loop_ranking_measures`
/// binds a rule to its source loop by index and executable shape, and the
/// shape comparison ignores the measure entirely. Comparing measures on top of
/// that is a consistency check that turns a plan describing one measure and a
/// certificate carrying another into a named refusal rather than a silent
/// mismatch. Weakening it can only produce a worse diagnostic, never a
/// theorem.
///
/// The one thing the plan is trusted for beyond identification, the
/// address-escape refusal, does not read this key for a pure component: the
/// check runs on the certified side against the lowered expression, in
/// `reject_address_escaped_ranking_component`. See
/// `docs/internals/kernel.md`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CRankingMeasureKey {
    CExpression(CExpression),
    Pure(String),
}

impl CFunctionTerminationPlan {
    pub fn function_name(&self) -> &str {
        &self.function_name
    }

    pub fn extend_loop_measures(
        &mut self,
        measures: impl IntoIterator<Item = (usize, CLoopTerminationMeasure)>,
    ) {
        self.loop_measures.extend(measures);
    }

    /// Drops the function-level measure, keeping every loop measure.
    pub fn clear_recursive_measure(&mut self) {
        self.recursive_measure = None;
    }
}

/// An untrusted description of the function-level ranking candidate. The
/// termination checker resolves the selected parameter or exact contract
/// resource again against the verified function.
///
/// `Expression` names the declared spelling only. Unlike the other two, it
/// selects no analysis of the body: the descent is owed as an ordinary
/// obligation at each self-call, and the check this variant asks for is that
/// the certified function's own interface carries the measure, so that those
/// obligations were emitted. See [`CRecursionAnchor`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CFunctionTerminationMeasure {
    NumericParameter(usize),
    ResourceRequirement(usize),
    Expression(String),
}

/// The kernel's record, while one C function is being certified, that a call
/// to that same function owes a descent obligation.
///
/// `measure` is the declared measure read once at the function's own entry
/// state, so it is the value the recursion starts from. A self-call is
/// checked against this one term, never against a term the call site
/// supplies: the surface can ask for an anchor (naming a function and an
/// entry) but cannot choose what the anchor holds, because
/// [`crate::kernel::c_execution_environment_with_recursion_anchor`] reads the
/// measure off the function's own contract interface and evaluates it itself.
///
/// `entry_obligations` are what reading the measure at the entry owes: the
/// loadability of its reads. They travel with the anchor and are emitted at
/// the self-call, where the path context can discharge them, rather than
/// being dropped.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CRecursionAnchor {
    pub(super) function: String,
    pub(super) components: Vec<CRankingComponent>,
    /// The other functions whose calls owe descent against `measure`, read
    /// off the same interface as `components`.
    pub(super) peers: Vec<String>,
    pub(super) measure: Vec<CRankingMeasureValue>,
    /// For a structural measure, the instance the measured binder held at
    /// the function's own entry; `components` and `measure` are then empty.
    pub(super) structural_entry: Option<ResourceInstance>,
    pub(super) entry_obligations: Vec<ProofObligation>,
}

impl CRecursionAnchor {
    pub(super) fn function(&self) -> &str {
        &self.function
    }

    pub(super) fn measure(&self) -> &[CRankingMeasureValue] {
        &self.measure
    }

    pub(super) fn components(&self) -> &[CRankingComponent] {
        &self.components
    }

    /// Whether a call to `callee` owes descent against this anchor: a
    /// self-call, or a call to a declared member of the same component.
    pub(super) fn ranks_call_to(&self, callee: &str) -> bool {
        self.function == callee
            || self
                .peers
                .binary_search_by(|peer| peer.as_str().cmp(callee))
                .is_ok()
    }

    pub(super) fn entry_obligations(&self) -> &[ProofObligation] {
        &self.entry_obligations
    }

    /// Whether this anchor ranks `function` by `measure`.
    ///
    /// The certified [`CFunction`] is what a judgment has in hand, and its
    /// interface is where the anchor's component was read from, so comparing
    /// both is what binds an anchor to one declared measure of one function.
    pub(super) fn ranks(&self, function: &str, interface: &CFunctionContractInterface) -> bool {
        self.function == function
            && interface.recursion_measure().unwrap_or_default() == self.components.as_slice()
            && interface.recursion_binder().is_some() == self.structural_entry.is_some()
            && interface.recursion_peers() == self.peers.as_slice()
    }

    pub(super) fn structural_entry(&self) -> Option<&ResourceInstance> {
        self.structural_entry.as_ref()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CTerminationError {
    pub(super) message: String,
    /// The function whose termination was being decided when the check
    /// failed, for a diagnostic to locate. It is not part of the verdict.
    pub(super) function: Option<String>,
    /// The check refused a function-level measure because the function has
    /// no recursive edge to rank.
    pub(super) superfluous_recursive_measure: bool,
}

impl CVerifiedFunctionTerminationRule {
    pub fn function_name(&self) -> &str {
        self.function.name()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CVerifiedFunctionContractClaim {
    pub(super) function: CFunction,
    pub(super) pointer_result_effects: std::sync::Arc<[CPointerResultEffect]>,
    pub(super) pointer_store_effects: std::sync::Arc<[CPointerStoreEffect]>,
    pub(super) native_output_places_certified: bool,
    pub(super) key: CFunctionContractClaimKey,
    /// Exact load equalities consumed while checking this claim. Keeping the
    /// witnesses on the proof object makes contract finalization the owner of
    /// its equality decisions rather than relying on an ambient prover later.
    pub(super) load_equalities: Vec<super::CheckedLoadEquality>,
    /// The loop semantics of the certification this claim came from.
    pub(super) loop_semantics: CLoopSemantics,
    /// The user-defined tactics the certification this claim came from
    /// applied.
    pub(super) applied_tactics: std::collections::BTreeSet<String>,
    /// Complete conservative call dependencies from kernel-checked execution.
    /// None retains source-call analysis; a present empty set proves no calls.
    /// Shared across claims and certificate reuse, never copied per step.
    pub(super) checked_callees: Option<Arc<BTreeSet<String>>>,
}

/// Kernel-checked evidence that a checked proof discharged one proposition at
/// one exact function outcome. Contract finalization finds this evidence by
/// the claim it closed and matches it to the path it was completed on.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CCheckedFunctionProposition {
    pub(super) function: CFunction,
    pub(super) specification: CFunctionSpecification,
    pub(super) proposition: Proposition,
    /// The contract claim this proposition closed: the proof was opened
    /// from the kernel's goal for that claim, which carries the claim's
    /// identity through to here. `None` for any other proposition.
    pub(super) claim: Option<CFunctionContractClaimTarget>,
}

impl CVerifiedFunctionContractClaim {
    pub fn key(&self) -> &CFunctionContractClaimKey {
        &self.key
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CVerifiedLoopRule {
    pub(super) symbolic_entry_state: CState,
    pub(super) loop_statement: CStatement,
    /// Source traversal index for the loop this rule certifies. The index is
    /// assigned by the proof driver after the kernel constructs the rule so
    /// termination checking can safely recover annotations from a nested
    /// frontier rule without changing the contract function's shape.
    pub(super) loop_index: Option<usize>,
    pub(super) required_assumptions: PureFactContext,
    pub(super) paths: Vec<CStatementExecutionPath>,
    pub(super) composite_resource_definitions: Vec<CCompositeResourceDefinition>,
    /// The recursion anchor the loop's body was stepped under, when the
    /// function this loop belongs to declares an expression `decreases`
    /// measure.
    ///
    /// The kernel writes this from the environment the paths above were
    /// produced in; there is no other way to set it, so it is a record of what
    /// the body actually owed rather than a claim about it. A self-call inside
    /// the body raised its descent obligations exactly when this is `Some`,
    /// and the rule exists at all only because every obligation on its paths
    /// was discharged or assumable. Applying the rule and the termination
    /// judgment both read it; see
    /// [`CExecutionEnvironment::applicable_verified_loop_rule`].
    pub(super) recursion_anchor: Option<std::sync::Arc<CRecursionAnchor>>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CUndefinedBehavior {
    SignedOverflow,
    /// The signed overflow of an `int32` division or remainder, which
    /// happens at exactly one operand pair, `INT_MIN / -1`. Kept apart from
    /// [`Self::SignedOverflow`] so the refusal names the pair the facts
    /// leave open instead of a bare `signed overflow`.
    SignedDivisionOverflow,
    PointerArithmetic,
    DivisionByZero,
    InvalidShift,
    InvalidMemory,
    UninitializedRead,
    /// An operation on a pointer value whose pointee's lifetime has ended
    /// (C11 6.2.4p2, Annex J.2): comparing, subtracting, offsetting, testing
    /// or converting a pointer into a freed allocation. A refusal names the
    /// operation through [`crate::kernel::locate_undefined_behavior`]; the
    /// kernel's name for the allocation is not something the reader wrote.
    FreedPointerUse,
    /// An equality comparison whose answer C11 6.5.9p6 leaves to the
    /// implementation's object layout: one operand may be one past the end
    /// of its object and the other the start of a different object, and the
    /// two are equal exactly when the objects are adjacent. The result is
    /// unspecified rather than undefined, and refused because the kernel does
    /// not model object placement. A refusal names the comparison through
    /// [`crate::kernel::locate_undefined_behavior`].
    OnePastEndComparison,
}

impl CUndefinedBehavior {
    pub fn description(&self) -> String {
        match self {
            Self::SignedOverflow => "signed overflow".to_string(),
            Self::SignedDivisionOverflow => {
                "signed overflow (INT_MIN / -1 is the one int32 division or remainder that overflows)"
                    .to_string()
            }
            Self::PointerArithmetic => "pointer arithmetic left the pointed-to object".to_string(),
            Self::DivisionByZero => "division by zero".to_string(),
            Self::InvalidShift => "invalid shift".to_string(),
            Self::InvalidMemory => "invalid memory access".to_string(),
            Self::UninitializedRead => "read of uninitialized storage".to_string(),
            Self::FreedPointerUse => "use of a pointer into a freed allocation: its value is \
                 indeterminate after the free"
                .to_string(),
            Self::OnePastEndComparison => "comparison of a one-past-the-end pointer with the start \
                 of another object: whether the two objects are adjacent is unspecified"
                .to_string(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CInvalidFree {
    InteriorPointer,
    NonHeapPointer,
    DoubleFree,
}

/// How a [`CRuntimeError::FunctionContract`] message ends when a function
/// returned a value its declared return type does not admit; the message
/// starts with the function's name.
pub const RETURN_TYPE_MISMATCH: &str = "returned a value that does not match its declared type";

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CRuntimeError {
    UnboundVariable(String),
    UnknownFunction(String),
    TypeMismatch,
    /// A typed memory load whose type does not fit the value the cell
    /// holds: a 4-byte load of an 8-byte cell, or a pointer cell read as an
    /// integer. `stored` is the cell's value when the snapshot knows it.
    LoadTypeMismatch {
        pointer: Pointer,
        value_type: CType,
        stored: Option<Box<CValue>>,
    },
    /// A pointer/integer cast outside the modeled LP64 conversions: the
    /// message names the rejected direction and what evidence it needed.
    PointerConversion(String),
    IndeterminatePointeeType,
    WrongArity {
        expected: usize,
        actual: usize,
    },
    MissingReturn,
    MissingResource {
        resource: Box<CResourceFact>,
    },
    /// An operation requires the current initialization's lifecycle owner.
    MissingMutexLive {
        mutex: Pointer,
    },
    /// An operation requires a use loan for this mutex initialization.
    MissingMutexUse {
        mutex: Pointer,
    },
    /// An operation requires an acquisition that is not available as owned authority.
    MissingMutexGuard {
        mutex: Pointer,
    },
    /// Unlock requires owned folded authority satisfying its protected assertion.
    /// The diagnostic witness's cached fields do not require historical values.
    MissingMutexInvariant {
        resource: Box<CResourceFact>,
        /// The resource the call map selected instead, when it is owned but
        /// of another protected type.
        supplied: Option<Box<CResourceFact>>,
    },
    /// A stable-view call returned a view that no checked input child,
    /// preserved outer binding, owner projection, or read-only block backs.
    UnbackedReturnedView {
        view: Box<CResourceFact>,
    },
    MissingVerifiedFunctionRule(String),
    UnsupportedOpaqueFunctionContract(String),
    AbstractFunctionPointerCall(String),
    FunctionContract(String),
    /// Exact operands retained at a rejected contract boundary. Diagnostic
    /// only: these values never establish a fact or grant access.
    ContractResourceDiagnostic {
        reason: String,
        held: Option<Box<CResourceFact>>,
        required: Box<CResourceFact>,
        memory: Option<Box<CMemory>>,
    },
    /// Lock or destroy encountered no successful modeled initialization for
    /// this mutex on the current path.
    UninitializedMutex {
        mutex: Pointer,
    },
    /// The modeled runtime has no sound shared-mutex transition for workers.
    /// This is a verifier limitation, not a missing client proof premise.
    UnsupportedConcurrentMutex,
    MutexStorageInUse {
        mutex: Pointer,
        allocation: Pointer,
    },
    MutexStorageSeparationRequired {
        allocation: Box<CMemoryRange>,
        storage: Box<CMemoryRange>,
    },
    MutexStorageWrite {
        write: Box<CMemoryRange>,
        storage: Box<CMemoryRange>,
    },
    MissingMutexStorageAlignment {
        mutex: Pointer,
        alignment: u32,
    },
    UnsupportedMutexStorageRetirement,
    /// The automatic object cannot expire while initialized mutex storage
    /// is known (or may be constrained) to lie in it.
    MutexStorageScopeEnd {
        local: String,
        mutex: Pointer,
        may_alias: bool,
    },
    InvalidFree(CInvalidFree),
    UnresolvedAllocationOutcome,
    LiveAllocationLeak {
        allocation: Box<CResourceFact>,
        /// The declared resource obligation whose body keeps `allocation`
        /// live, when the kernel can identify one.  Keeping this alongside
        /// the allocation lets surface diagnostics name the obligation that
        /// was lost instead of reverse-engineering resource definitions from
        /// a lowered allocation fact.
        resource: Option<Box<CResourceFact>>,
    },
    StaleResourceAfterFree {
        resource: Box<CResourceFact>,
    },
    DuplicateResource {
        resource: Box<CResourceFact>,
    },
    OverlappingOwnedMemoryResources {
        left: Box<CMemoryRange>,
        right: Box<CMemoryRange>,
    },
    /// A callee's produced or ensured composite carries a body that overlaps
    /// a resource the destination context already holds. Composing the head
    /// would leave two owners over the same bytes, so the context would stop
    /// denoting a partition.
    ProducedCompositeOverlapsHeldResource {
        produced: Box<CResourceFact>,
        piece: Box<CResourceFact>,
        held: Box<CResourceFact>,
    },
    LoanRefusal(Box<crate::kernel::LoanRefusalDiagnostic>),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ExecutionLimit {
    Deadline,
    ExpressionSteps,
    StatementSteps,
    FunctionCalls,
    LoopUnrolls,
    Paths,
    UnsupportedIntegerExistentialBody,
    UnsupportedPureFunctionResult(CType),
    /// The execution's fresh-identity counter reached the first identity a
    /// producer outside the execution reserves by a constant base. Every
    /// kernel allocation counts up from one base, and the ranges above it
    /// belong to the surface's quantifier and algebraic binders and higher
    /// disjoint producers; an execution that entered one of them
    /// would name their variables without knowing it.
    KernelVariables {
        ceiling: u64,
    },
    /// One lowering asked for more match-arm binders than its reserved range
    /// holds. The range is disjoint from every other producer's, so counting
    /// past it would start naming their variables.
    MatchBinderVariables {
        ceiling: u64,
    },
    /// A budget built by `ExecutionBudget::beside_live_state` was asked for
    /// an execution identity. Its counter starts at the base of the
    /// range while the state it evaluates against belongs to an execution
    /// that has already issued identities from there, so the request would
    /// have named a havocked local, a join abstraction or a heap block. It is
    /// a defect in the caller -- either the identity belongs in a reserved
    /// bound-variable range, or the site needs the execution's mark and
    /// `ExecutionBudget::continuing_from`.
    ExecutionIdentityBesideLiveState,
    /// A model-field projection was evaluated at a state that holds no
    /// instance of its identity, or whose instance has no field of the
    /// projected type at that index. This is not a budget: it is the
    /// ordinary consequence of `unfold`, `consumes` or a transfer having
    /// taken the instance away, and a reader needs to be told *that* rather
    /// than which counter the evaluation was holding at the time.
    ResourceFieldInstanceUnavailable,
    /// A worker may still change this total. No current observation is
    /// available until the checked completion right is joined.
    ResourceCountPendingWorker,
    /// Another tracked population of the family is neither proven equal to
    /// nor proven different from the counted one, so no total is a count.
    ResourceCountPossiblyAliased,
    /// A count names one concrete population anchor.
    AuthorityCountNeedsExactPointer,
    AuthorityCountNeedsResolvedMember,
    /// Both the visible authority fact and checked ledger custody are needed.
    AuthorityCountNeedsOwnership,
    /// The population's authority is lent to an outstanding worker.
    AuthorityCountLentToWorker,
    /// An outstanding locked worker changes the population before its join.
    AuthorityCountPendingLockedWorker,
    /// The exact population total cannot be represented as C int32.
    AuthorityCountOverflows,
}

impl ExecutionLimit {
    /// The one naming table for a bounded evaluation's stopping point, as a
    /// noun phrase that reads after "stopped at". Every message a user can
    /// see goes through here: a `{:?}` of this enum in user text is a leak,
    /// because the variant names are the kernel's counters rather than
    /// anything the reader wrote.
    pub fn describe(self) -> String {
        match self {
            Self::Deadline => "the verification deadline".to_string(),
            Self::ExpressionSteps => "the expression step budget".to_string(),
            Self::StatementSteps => "the statement step budget".to_string(),
            Self::FunctionCalls => "the function call budget".to_string(),
            Self::LoopUnrolls => "the loop unrolling budget".to_string(),
            // `Paths` is returned both by the path-width budget and, all over
            // spec evaluation, by a shape the evaluator has no single value
            // for. The phrase has to cover both without claiming a counter
            // ran out.
            Self::Paths => "no single evaluation path".to_string(),
            Self::UnsupportedPureFunctionResult(result_type) => {
                format!("unsupported pure-function result type {result_type:?}")
            }
            Self::UnsupportedIntegerExistentialBody => {
                "an Integer existential body that must be pure and total".to_string()
            }
            Self::KernelVariables { ceiling } => {
                format!("the execution's fresh-identity range, which ends below {ceiling}")
            }
            Self::MatchBinderVariables { ceiling } => {
                format!("the match-binder identity range, which ends below {ceiling}")
            }
            Self::ExecutionIdentityBesideLiveState => {
                "an internal request for an execution identity beside a live state".to_string()
            }
            Self::ResourceCountPendingWorker => {
                "count(...) requires joining its outstanding worker".to_string()
            }
            Self::ResourceCountPossiblyAliased => {
                "count(...) of a population that may alias another tracked population of its family; state whether their arguments are equal or different".to_string()
            }
            Self::AuthorityCountNeedsExactPointer => {
                "count(...) needs one exact base pointer".to_string()
            }
            Self::AuthorityCountNeedsResolvedMember => {
                "count(...) requires resolved member indices or the helper's selected member"
                    .to_string()
            }
            Self::AuthorityCountNeedsOwnership => {
                "count(...) requires owning authority for that population".to_string()
            }
            Self::AuthorityCountPendingLockedWorker => {
                "count(...) is unknown until pthread_join returns the workers that change this population under its mutex".to_string()
            }
            Self::AuthorityCountLentToWorker => {
                "count(...) requires owning authority for that population, which an outstanding worker holds until its pthread_join".to_string()
            }
            Self::AuthorityCountOverflows => "the population count exceeds int32".to_string(),
            Self::ResourceFieldInstanceUnavailable => {
                "a model field of a resource instance this state does not hold".to_string()
            }
        }
    }
}

impl CRuntimeError {
    /// The sentence for [`CRuntimeError::UnbackedReturnedView`], which the
    /// surface completes with the view in source terms.
    pub const UNBACKED_RETURNED_VIEW: &'static str =
        "stable-view call returned a view without a checked input child or preserved outer binding";

    /// A kernel-side one-line rendering, for messages built where no C
    /// parameter names are at hand, so it names no pointer: the kernel's
    /// spelling of an address is lowering state, not anything the reader
    /// wrote. The surface describers spell pointers through the parameters.
    pub fn kernel_summary(&self) -> String {
        match self {
            CRuntimeError::LoadTypeMismatch {
                value_type, stored, ..
            } => {
                let found = match stored.as_deref() {
                    Some(CValue::Pointer(_)) => "found a pointer in the cell".to_string(),
                    Some(stored) => {
                        format!("found a value of {} bytes in the cell", stored.byte_width())
                    }
                    None => "did not fit the cell's value".to_string(),
                };
                format!("a {}-byte load {found}", value_type.byte_width())
            }
            other => {
                crate::kernel::api::contract_certification::describe_certification_runtime_error(
                    other,
                )
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExecutionBudget {
    pub(super) expression_steps: usize,
    pub(super) statement_steps: usize,
    pub(super) function_calls: usize,
    pub(super) loop_unrolls: usize,
    /// Dynamic call-site context of a contract-less inline body. Its loops
    /// may unroll only while their guards are decided by the current facts;
    /// a symbolic guard needs the helper's own checked loop contract.
    pub(super) inline_call_name: Option<String>,
    pub(super) paths: usize,
    pub(super) next_opaque_call: u64,
    pub(super) next_kernel_variable: u64,
    /// This lowering's own counter for match-arm binders, counting through
    /// [`ExecutionBudget::MATCH_BINDER_VARIABLE_BASE`]. Binders are bound
    /// variables, so they are drawn from a range no execution, quantifier,
    /// fold, load or pointer producer can reach rather than from the
    /// execution counter beside them.
    pub(super) next_match_binder_variable: u64,
    /// Whether this budget refuses to invent an execution identity at all.
    /// Set by `ExecutionBudget::beside_live_state`, whose state belongs to an
    /// execution whose mark the caller does not carry: an
    /// identity from the base of the range would name something that state
    /// already holds.
    pub(super) refuses_execution_identities: bool,
    /// The first runtime error a specification evaluation dropped while
    /// every path of some sub-evaluation ended in one. An evaluation with no
    /// value path is reported by its count; the count says nothing about
    /// why, and this is the why (a load of the wrong width, a read no
    /// resource permits). Diagnostic only: no evaluation reads it back.
    pub(super) dropped_runtime_error: Option<CRuntimeError>,
    /// The first constant element range a specification lowering dropped
    /// because it is not a valid 32-bit byte extent: reversed, or wider than
    /// `u32::MAX` bytes once scaled. Such a range prunes its own evaluation
    /// path, and the surviving path count says nothing about why. Diagnostic
    /// only: no evaluation reads it back.
    pub(super) dropped_range_extent: Option<DroppedRangeExtent>,
    /// The first range fold a specification lowering dropped because its body
    /// did not evaluate to one symbolic iteration under the fold's binders.
    /// Such a fold prunes its own evaluation path, and the surviving path
    /// count says nothing about why. Diagnostic only: no evaluation reads it
    /// back.
    pub(super) dropped_fold_body: Option<DroppedFoldBody>,
    /// Set when a stated resource relation was dropped because this context
    /// already proves one of its memory ranges is not a valid byte extent.
    /// Unlike [`Self::dropped_range_extent`] the endpoints here need not be
    /// constants — the surrounding facts are what decide it — so there is no
    /// element count to report, only the reason. Diagnostic only: no
    /// evaluation reads it back.
    pub(super) dropped_relation_range_extent: bool,
    /// The byte order of the environment whose statements this budget is
    /// executing, installed from `CExecutionEnvironment` at each statement.
    /// `None` until a statement installs it: an expression evaluated with no
    /// environment in hand has no byte view of integer cells at all.
    pub(super) c_byte_order: Option<ByteOrder>,
}

/// A constant element range a lowering refused as a byte extent, for the
/// message a caller writes when the lowering produced no path.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DroppedRangeExtent {
    pub element_count: i64,
    pub element_width: u32,
    pub byte_limit: u32,
}

/// A range fold whose body did not lower to one symbolic iteration, for the
/// message a caller writes when the lowering produced no path.
///
/// A fold body runs under the fold's accumulator and item binders, so a fact
/// it raises is a statement about one unknown item rather than about this
/// state. The lowering may export only facts the ambient premises already
/// state exactly, and it may keep only a single non-branching body path. Both
/// refusals prune the fold's path silently; this records which one fired and
/// what it was about.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DroppedFoldBody {
    /// How many evaluation paths the body produced under its binders. Any
    /// count other than one is a case split on the item.
    pub body_paths: usize,
    /// The first body path fact the ambient premises do not already state
    /// exactly, when the body produced exactly one path. This is the
    /// case-split condition the body carried out with it.
    pub unavailable_body_fact: Option<Proposition>,
    /// The item binder the body was evaluated under, so a message can say
    /// which index the condition is about.
    pub item: Variable,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CExpressionOutcome {
    Value(CValue),
    UndefinedBehavior(CUndefinedBehavior),
    RuntimeError(CRuntimeError),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CConditionOutcome {
    Value(bool),
    UndefinedBehavior(CUndefinedBehavior),
    RuntimeError(CRuntimeError),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) enum CLValueOutcome {
    LValue(CLValue),
    UndefinedBehavior(CUndefinedBehavior),
    RuntimeError(CRuntimeError),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CStatementOutcome {
    Normal(Box<CState>),
    Break(Box<CState>),
    Continue(Box<CState>),
    /// A checked source edge awaiting resumption at its function-owned target.
    Jump {
        target: CControlTargetId,
        state: Box<CState>,
    },
    Return {
        value: CValue,
        state: Box<CState>,
    },
    /// An exceptional transfer that has not yet been handled in this function.
    Throw {
        value: CValue,
        state: Box<CState>,
    },
    /// Internal to `CStatementVerifies`: the statement has no finite
    /// successor, but all of its finite prefixes have been checked.
    VerificationDiverges,
    UndefinedBehavior(CUndefinedBehavior),
    RuntimeError(CRuntimeError),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CFunctionOutcome {
    Return {
        value: CValue,
        state: Box<CState>,
    },
    /// An exceptional outcome crossing this function boundary.
    Throw {
        value: CValue,
        state: Box<CState>,
    },
    /// Internal to `CFunctionVerifies`: no return frontier exists, but the
    /// function's finite prefixes satisfy its safety proof.
    VerificationDiverges,
    UndefinedBehavior(CUndefinedBehavior),
    RuntimeError(CRuntimeError),
}

impl CFunctionOutcome {
    /// Equality that identifies end states differing only in creation
    /// ledgers that record nothing (`CState::equal_up_to_unused_creation_ledgers`).
    pub(crate) fn equal_up_to_unused_creation_ledgers(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Self::Return { value, state },
                Self::Return {
                    value: other_value,
                    state: other_state,
                },
            )
            | (
                Self::Throw { value, state },
                Self::Throw {
                    value: other_value,
                    state: other_state,
                },
            ) => value == other_value && state.equal_up_to_unused_creation_ledgers(other_state),
            _ => self == other,
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CLocalEnvironment {
    pub(super) bindings: std::sync::Arc<BTreeMap<String, CLocalBinding>>,
    pub(super) slots: std::sync::Arc<BTreeMap<Pointer, String>>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) enum CLocalBinding {
    Object {
        /// True only for an allocated scalar binding, not a logical parameter
        /// whose compatibility pseudo-slot happens to have the same name.
        storage_declared: bool,
        value: CValue,
        c_type: CType,
        slot: Pointer,
        volatile: bool,
        pointee_volatile: bool,
        constant: bool,
        pointee_constant: bool,
    },
    UninitializedObject {
        c_type: CType,
        slot: Pointer,
        volatile: bool,
        pointee_volatile: bool,
        constant: bool,
        pointee_constant: bool,
    },
    GlobalObject {
        c_type: CType,
        slot: Pointer,
        volatile: bool,
        pointee_volatile: bool,
        constant: bool,
        pointee_constant: bool,
    },
    ArrayObject {
        element_type: CType,
        length: u32,
        slot: Pointer,
        constant: bool,
    },
    AggregateObject {
        layout: CAggregateLayout,
        slot: Pointer,
        constant: bool,
    },
}

/// The snapshot a snapshot forgot knowledge from.
///
/// A snapshot is interned by content, so two states with the same known
/// cells are one node. That is only sound while the known cells decide what
/// every address holds *relative to a fixed starting state* — and dropping a
/// cached value breaks exactly that. After `a[i] = 7; a[j] = 0;` the write to
/// `a[j]` drops the possibly aliasing `a[i]` cell, and the cell map is empty
/// again, just as it was at function entry. Without this mark that state *is*
/// the entry node, so `a[m]` is named `old(a[m])` and the two are equal by
/// spelling with no rule having decided it.
///
/// So the forget is part of the content. `{cells, forgotten_from = S}` reads
/// "the memory `S` denotes, with these cells known on top of it". Two
/// executions that reach the same cells over the same `S` really are in the
/// same state, so interning stays sound, deterministic and
/// path-independent — and an entry state, which carries no mark, can no
/// longer be the state something was forgotten into.
/// The mark is the base's *identity*, never the base itself. Holding the
/// snapshot would put a chain of `Arc<CMemory>` inside every snapshot that
/// ever forgot anything, and equality, ordering and dropping would all
/// recurse down it — one stack frame per forget, on a hot path, in a
/// structure the arena already keeps alive. Every field here is O(1) to
/// compare and to hash.
///
/// It is held behind an `Arc` rather than inline for the same reason the
/// cell map is: `CMemory` travels by value through deeply recursive
/// evaluation, so a snapshot pays one pointer for the mark and the snapshots
/// that inherit it share the one allocation.
///
/// `content_hash` comes first so that the derived ordering is the one a
/// verification can reproduce: it is a function of the base's content, while
/// arena tokens count process-wide and would order snapshots differently from
/// run to run. Within one verification every mark shares the token, so the
/// remaining comparison is by dense arena id.
#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) struct ForgottenFrom {
    content_hash: u64,
    arena_id: (u32, u32),
}

impl std::hash::Hash for ForgottenFrom {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Only the content hash, because this feeds the identity a load is
        // named by: a name has to be the same in every run that reaches this
        // state, and an arena token is not.
        state.write_u64(self.content_hash);
    }
}

impl std::fmt::Debug for ForgottenFrom {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (arena, id) = self.arena_id;
        write!(formatter, "forgotten-from({arena}.{id})")
    }
}

/// What a snapshot no longer knows, beside its cells.
///
/// Two facts of the same kind, behind one pointer. `CMemory` travels by value
/// inside `Term`, whose clone recurses once per nested operator, so a snapshot
/// pays one word for both rather than one each.
#[derive(Clone, Debug, Default, Eq, PartialEq, Ord, PartialOrd)]
pub struct CForgottenKnowledge {
    /// Automatic-storage blocks whose lifetimes have ended. Unlike removing
    /// the block alone, retaining this tombstone makes stale aliases invalid
    /// even when a later proof step forgets or rejoins ordinary cells.
    pub(super) ended_local_blocks: SnapshotSet<PointerBlock>,
    /// Set where cached values were dropped without the memory itself being
    /// known unchanged; see [`ForgottenFrom`]. Carried by later stores and by
    /// the projections used for load naming, so a state that has forgotten
    /// something can never re-intern as the state it forgot it from.
    pub(super) forgotten_from: Option<ForgottenFrom>,
    /// Inputs of the most recent branch abstraction. Their exact arena
    /// identities prevent first-wins provenance from mixing different joins;
    /// their content hashes keep read names reproducible across sessions.
    /// The persistent set caches its hash and does not retain recursive
    /// snapshot contents. Read projections must retain this identity.
    pub(super) join_inputs: SnapshotSet<ForgottenFrom>,
}

#[derive(Clone, Debug, Default)]
pub struct CMemory {
    pub(super) construction: Option<Arc<CMemoryConstruction>>,
    pub(super) blocks: std::sync::Arc<SnapshotMap<PointerBlock, CBlock>>,
    pub(super) cells: std::sync::Arc<CellStore>,
    /// Typed views of address-overlapping union storage. A union member is
    /// keyed by its address and type rather than placed in `cells`, because
    /// two members at one address must remain independently readable after a
    /// by-value aggregate copy.
    pub(super) union_cells: std::sync::Arc<SnapshotMap<(Pointer, CType), CValue>>,
    pub(super) forgotten: std::sync::Arc<CForgottenKnowledge>,
    pub(super) heap: std::sync::Arc<CHeapMemory>,
}

/// A retained explanation, deliberately excluded from memory equality, hashing,
/// interning keys, and every proof rule. It travels with the snapshot, including
/// across threads. Roots guard against accidentally inheriting a stale origin
/// when a constructor edits a cloned snapshot without recording its operation.
#[derive(Clone)]
pub(crate) struct CMemoryConstruction {
    roots: CMemory,
    pub(crate) kind: CMemoryConstructionKind,
}

// Avoid recursively dumping the entire construction history in an assertion.
impl std::fmt::Debug for CMemoryConstruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let operation = match &self.kind {
            CMemoryConstructionKind::Transition(edge) => edge.kind_name(),
            CMemoryConstructionKind::Transform { operation, .. } => operation,
        };
        f.debug_tuple("MemoryConstruction")
            .field(&operation)
            .finish()
    }
}

#[derive(Clone, Debug)]
pub(crate) enum CMemoryConstructionKind {
    Transition(Arc<CMemoryDerivation>),
    Transform {
        operation: &'static str,
        sources: Vec<CMemory>,
        arguments: Vec<CValue>,
    },
}

impl CMemory {
    // Pin the described roots so an in-place Arc mutation or allocator address
    // reuse cannot make a stale construction appear to describe new contents.
    // Dropping the origin here avoids a self-reference through this pin.
    fn diagnostic_roots(&self) -> Self {
        let mut roots = self.clone();
        roots.construction = None;
        roots
    }

    pub(crate) fn diagnostic_construction(&self) -> Option<&CMemoryConstructionKind> {
        self.construction
            .as_ref()
            .filter(|origin| origin.roots.same_storage_roots(self))
            .map(|origin| &origin.kind)
    }

    pub(crate) fn is_initial_diagnostic_memory(&self) -> bool {
        self.is_symbolic_input_memory()
    }

    /// The unconstrained input root, rather than a forgotten or overwritten
    /// cell, declared object, or allocated block. Empty persistent roots make
    /// this a constant-work query; absence of a history edge is insufficient.
    pub(in crate::kernel) fn is_symbolic_input_memory(&self) -> bool {
        self.blocks.is_empty()
            && self.cells.len() == 0
            && self.union_cells.is_empty()
            && *self.forgotten == CForgottenKnowledge::default()
            && *self.heap == CHeapMemory::default()
    }

    pub(in crate::kernel) fn record_diagnostic_transform(
        &mut self,
        operation: &'static str,
        sources: Vec<CMemory>,
        arguments: Vec<CValue>,
    ) {
        crate::instrumentation::record_deterministic_work(1 + sources.len());
        if sources.len() == 1 && self.same_storage_roots(&sources[0]) {
            return;
        }
        self.construction = Some(Arc::new(CMemoryConstruction {
            roots: self.diagnostic_roots(),
            kind: CMemoryConstructionKind::Transform {
                operation,
                sources,
                arguments,
            },
        }));
    }

    /// O(1) diagnostic identity for a snapshot without interning or walking
    /// its contents. This is intentionally only an identity label; equal
    /// labels imply shared storage roots, not semantic inequality otherwise.
    pub(crate) fn diagnostic_identity(&self) -> (usize, usize, usize, usize, usize) {
        (
            std::sync::Arc::as_ptr(&self.blocks) as usize,
            std::sync::Arc::as_ptr(&self.cells) as usize,
            std::sync::Arc::as_ptr(&self.union_cells) as usize,
            std::sync::Arc::as_ptr(&self.forgotten) as usize,
            std::sync::Arc::as_ptr(&self.heap) as usize,
        )
    }

    /// Records that this snapshot dropped cached values that `base` knew,
    /// without the memory the two describe having changed.
    ///
    /// Overwriting an older mark keeps the whole history: `base` carries its
    /// own mark, and `base`'s content hash — which is what is stored here —
    /// already depends on it.
    pub(in crate::kernel) fn mark_forgotten_from(&mut self, base: &SharedCMemory) {
        std::sync::Arc::make_mut(&mut self.forgotten).forgotten_from = Some(ForgottenFrom {
            content_hash: base.content_hash,
            arena_id: base.arena_id(),
        });
    }

    /// Whether the two snapshots describe one memory: the same blocks, heap
    /// lifetimes, union views and forgotten-knowledge marks, and the same
    /// cells whatever representation each cell store keeps them in
    /// ([`CellStore::same_cells_as`]). Everything but the cell cache's layout
    /// is compared exactly as `==` compares it.
    pub(in crate::kernel) fn same_contents_as(&self, other: &Self) -> bool {
        self == other
            || (self.blocks == other.blocks
                && self.union_cells == other.union_cells
                && self.forgotten == other.forgotten
                && self.heap == other.heap
                && self.cells.same_cells_as(&other.cells))
    }

    /// Whether `self == other`, for two snapshots each derived from `base`'s
    /// storage, comparing only what each changed from `base` (see
    /// [`SnapshotMap::eq_relative_to`]). Exact whatever the snapshots share;
    /// the cost is the changed paths when both were derived from `base`.
    pub(super) fn eq_relative_to(&self, other: &Self, base: &Self) -> bool {
        if c_memory_content_hash(self) != c_memory_content_hash(other) {
            return false;
        }
        (std::sync::Arc::ptr_eq(&self.blocks, &other.blocks)
            || self.blocks.eq_relative_to(&other.blocks, &base.blocks))
            && (std::sync::Arc::ptr_eq(&self.cells, &other.cells)
                || self.cells.eq_relative_to(&other.cells, &base.cells))
            && (std::sync::Arc::ptr_eq(&self.union_cells, &other.union_cells)
                || self
                    .union_cells
                    .eq_relative_to(&other.union_cells, &base.union_cells))
            && (std::sync::Arc::ptr_eq(&self.forgotten, &other.forgotten)
                || (self.forgotten.forgotten_from == other.forgotten.forgotten_from
                    && self.forgotten.join_inputs == other.forgotten.join_inputs
                    && self.forgotten.ended_local_blocks.eq_relative_to(
                        &other.forgotten.ended_local_blocks,
                        &base.forgotten.ended_local_blocks,
                    )))
            && (std::sync::Arc::ptr_eq(&self.heap, &other.heap)
                || self.heap.eq_relative_to(&other.heap, &base.heap))
    }

    /// The same content behind freshly allocated storage roots, so it is not
    /// the stored snapshot by [`Self::same_storage_roots`]. Tests use it to
    /// stand for an equal snapshot reached without going through a
    /// derivation, which would hand back the arena's canonical instance.
    #[cfg(test)]
    pub(crate) fn with_fresh_storage_roots(&self) -> Self {
        let mut result = Self {
            construction: None,
            blocks: std::sync::Arc::new((*self.blocks).clone()),
            cells: std::sync::Arc::new((*self.cells).clone()),
            union_cells: std::sync::Arc::new((*self.union_cells).clone()),
            forgotten: std::sync::Arc::new((*self.forgotten).clone()),
            heap: std::sync::Arc::new((*self.heap).clone()),
        };
        result.record_diagnostic_transform("copy snapshot storage", vec![self.clone()], Vec::new());
        result
    }

    /// Whether two snapshots are the same stored snapshot, by the storage
    /// roots alone. This is the O(1) half of a diagnostic label's identity:
    /// a report that must show "same memory" compares contents when this
    /// says nothing, and never the other way round.
    pub(crate) fn same_storage_roots(&self, other: &Self) -> bool {
        self.diagnostic_identity() == other.diagnostic_identity()
    }
}

/// A pinned, shallow identity for the lifetime metadata relevant to a read.
/// Keeping the heap alive prevents allocation-address reuse in an index, and
/// the local-lifetime bit distinguishes a retired automatic block from a
/// snapshot where its block is still live.
#[derive(Clone)]
pub(in crate::kernel) struct ReadRegionIdentity {
    block_size: Option<Bitvector32Term>,
    local_lifetime_ended: bool,
    heap: Arc<CHeapMemory>,
}

impl ReadRegionIdentity {
    fn retirement_identity(&self) -> usize {
        if self.heap.deallocated_allocations.is_empty() {
            0
        } else {
            Arc::as_ptr(&self.heap) as usize
        }
    }
}

impl PartialEq for ReadRegionIdentity {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}
impl Eq for ReadRegionIdentity {}
impl PartialOrd for ReadRegionIdentity {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for ReadRegionIdentity {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.block_size
            .cmp(&other.block_size)
            .then_with(|| self.local_lifetime_ended.cmp(&other.local_lifetime_ended))
            .then_with(|| self.retirement_identity().cmp(&other.retirement_identity()))
    }
}

impl CMemory {
    /// Names the parts in which two memories differ, for a refusal that
    /// would otherwise only say that they do.
    pub(crate) fn differing_parts(&self, other: &Self) -> Vec<&'static str> {
        let mut parts = Vec::new();
        if self.blocks != other.blocks {
            parts.push("allocated blocks");
        }
        if self.cells != other.cells {
            parts.push("cell values");
        }
        if self.union_cells != other.union_cells {
            parts.push("union views");
        }
        if self.forgotten.ended_local_blocks != other.forgotten.ended_local_blocks {
            parts.push("ended local lifetimes");
        }
        if self.forgotten.forgotten_from != other.forgotten.forgotten_from {
            parts.push("which earlier memory each forgot values from");
        }
        if self.forgotten.join_inputs != other.forgotten.join_inputs {
            parts.push("incoming branch memories");
        }
        if self.heap != other.heap {
            parts.push("heap records");
        }
        parts
    }
}

impl PartialEq for CMemory {
    /// Rejects on the O(1) content hash before any elementwise comparison.
    /// Without that, a candidate that differs only in a later component
    /// would pay for comparing the equal earlier ones, and which candidates a
    /// randomly seeded hash table happens to probe would change the charged
    /// work from run to run.
    fn eq(&self, other: &Self) -> bool {
        if c_memory_content_hash(self) != c_memory_content_hash(other) {
            return false;
        }
        self.blocks == other.blocks
            && self.cells == other.cells
            && self.union_cells == other.union_cells
            && self.forgotten == other.forgotten
            && self.heap == other.heap
    }
}

impl Eq for CMemory {}

impl std::hash::Hash for CMemory {
    /// O(1): every map and set carries its own cached content hash, and the
    /// forget mark hashes by its base's content hash.
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.blocks.hash(state);
        self.cells.hash(state);
        self.union_cells.hash(state);
        self.forgotten.ended_local_blocks.hash(state);
        self.heap.hash(state);
        self.forgotten.forgotten_from.hash(state);
        self.forgotten.join_inputs.hash(state);
    }
}

impl Ord for CMemory {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.blocks
            .cmp(&other.blocks)
            .then_with(|| self.cells.cmp(&other.cells))
            .then_with(|| self.union_cells.cmp(&other.union_cells))
            .then_with(|| {
                self.forgotten
                    .ended_local_blocks
                    .cmp(&other.forgotten.ended_local_blocks)
            })
            .then_with(|| self.heap.cmp(&other.heap))
            .then_with(|| {
                self.forgotten
                    .forgotten_from
                    .cmp(&other.forgotten.forgotten_from)
            })
            .then_with(|| self.forgotten.join_inputs.cmp(&other.forgotten.join_inputs))
    }
}

impl PartialOrd for CMemory {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) struct CPendingReallocation {
    pub(super) old_pointer: CPointerValue,
    pub(super) old_bytes: Bitvector32Term,
    /// Bytes at the start of the new block that retain calloc's guaranteed
    /// zero value. A prefix equal to the new allocation size means the whole
    /// block is zeroed; a shorter prefix leaves the grown tail uninitialized.
    pub(super) zeroed_prefix: Option<Bitvector32Term>,
    pub(super) copied_cells: Vec<(PointerOffsetTerm, CValue)>,
    /// The runs of constant byte offsets of the old block that were
    /// initialized and lie in the new allocation, cut at its size: a
    /// successful resize preserves them whether or not a cached cell still
    /// names their value, and the bytes the new block grows by stay
    /// uninitialized.
    pub(super) initialized_prefix: Vec<(i64, u32)>,
}

/// A source-typed native record promise for one complete input carrier.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) enum CNativeInputIdentity {
    Unresolved(Variable),
    Loaded(PointerLoadIdentity),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(in crate::kernel) enum CNativeInputKind {
    /// An admitted source slice, including a valid nonnull empty carrier.
    /// Its signature guarantees a byte extent bounded by isize::MAX.
    TypedSlice {
        element_type: CType,
        count: SharedIntegerTerm,
    },
    Record {
        layout: Arc<CAggregateLayout>,
    },
    RecordPrefix {
        layout: Arc<CAggregateLayout>,
        count: SharedIntegerTerm,
    },
    AllocatedScalar {
        element_type: CType,
        bytes: SharedIntegerTerm,
    },
    TypedPrefix {
        element_type: CType,
        count: SharedIntegerTerm,
        policy: CTypedAccessPolicy,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(in crate::kernel) struct CNativeRecordInput {
    pub(in crate::kernel) origin: CPointerValue,
    pub(in crate::kernel) kind: CNativeInputKind,
}

#[cfg(test)]
#[path = "primitives/native_record_input_tests.rs"]
mod native_record_input_tests;

/// Every field is a snapshot collection, so hashing is O(1).
#[derive(Clone, Debug, Default, Eq, PartialEq, Ord, PartialOrd)]
pub(super) struct CHeapMemory {
    /// Live heap blocks are also present in `blocks`; this set distinguishes
    /// them from automatic storage and memory-havoc markers.
    pub(super) live_allocations: SnapshotMap<Pointer, Bitvector32Term>,
    /// Heap identities are never reused within a proof. These are semantic
    /// tombstones for double-free and stale-pointer diagnostics, not
    /// resources or surviving allocation authority.
    pub(super) deallocated_allocations: SnapshotMap<Pointer, Bitvector32Term>,
    /// A malloc result whose null/success outcome has not yet been refined by
    /// control flow or direct return. Pending allocations carry no authority
    /// until resolved.
    pub(super) pending_allocations: SnapshotMap<Pointer, Bitvector32Term>,
    /// Successful malloc storage remains uninitialized until individual
    /// cells are written. Contract-imported allocations are not placed here.
    pub(super) uninitialized_allocations: SnapshotSet<Pointer>,
    /// Explicit proof-entry objects whose bytes start unwritten. Unlike heap
    /// allocations these carry neither freshness nor deallocation authority.
    pub(super) uninitialized_objects: SnapshotMap<Pointer, u32>,
    /// Interface-entry structural object requirements, independent of raw
    /// footprints, allocation extent, initialization and access authority.
    pub(super) object_input_domains: SnapshotMap<Pointer, Arc<CAggregateLayout>>,
    /// Exact native typed-input identities. Address equality cannot select a
    /// row; the separate origin index supports bounded lifetime retirement.
    pub(super) native_record_inputs: SnapshotMap<CNativeInputIdentity, CNativeRecordInput>,
    pub(super) native_record_input_origins: SnapshotMap<Pointer, SnapshotSet<CNativeInputIdentity>>,
    /// Candidate aliases for opaque loaded inputs. Selection never proves a
    /// carrier relationship; consumers recheck the complete read frame.
    pub(super) native_record_input_reads:
        SnapshotMap<PointerLoadId, SnapshotSet<CNativeInputIdentity>>,
    /// Scalar native-interface requirements. Lookup is usable only with the
    /// matching complete pointer designation, never an address alone.
    pub(super) scalar_input_domains: SnapshotMap<Pointer, CType>,
    /// Bytes of storage with an initialization history — fresh heap
    /// allocations and automatic (`local:`) objects — that a C store has
    /// initialized, whether or not their cached value survives. A store the
    /// facts cannot place, a call or loop havoc, or a join forgets values,
    /// never initialization, so a later load must not mistake such a byte
    /// for never-written storage. Heap stores record here as they write;
    /// automatic storage records a cell when its value is forgotten (a
    /// cached local cell is itself the evidence until then). See
    /// [`InitializedBytes`].
    pub(super) initialized: InitializedBytes,
    /// Successful calloc storage reads as zero until individual cells are
    /// written. The set is separate from `uninitialized_allocations` so the
    /// same heap-lifetime machinery can represent both APIs.
    pub(super) zeroed_allocations: SnapshotSet<Pointer>,
    /// Successful reallocations of zeroed storage may preserve only a prefix
    /// of the old block. The remainder of a grown block is uninitialized.
    pub(super) zeroed_prefix_allocations: SnapshotMap<Pointer, Bitvector32Term>,
    /// Pending calloc results whose null/success outcome has not yet been
    /// refined.
    pub(super) zeroed_pending_allocations: SnapshotSet<Pointer>,
    /// Pending reallocations retain the old live block until their result is
    /// refined. Success then retires it and installs the copied prefix;
    /// failure simply resolves the new result to null.
    pub(super) pending_reallocations: SnapshotMap<Pointer, CPendingReallocation>,
}

impl std::hash::Hash for CHeapMemory {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Snapshot hashes name symbolic loads and order forgotten snapshots.
        // Preserve existing names when construction tracking is absent: an
        // unused extension must not reshuffle ordinary proof-search inputs.
        self.live_allocations.hash(state);
        self.deallocated_allocations.hash(state);
        self.pending_allocations.hash(state);
        self.uninitialized_allocations.hash(state);
        self.initialized.hash(state);
        self.zeroed_allocations.hash(state);
        self.zeroed_prefix_allocations.hash(state);
        self.zeroed_pending_allocations.hash(state);
        self.pending_reallocations.hash(state);
        if !self.uninitialized_objects.is_empty() {
            "uninitialized_objects".hash(state);
            self.uninitialized_objects.hash(state);
        }
        if !self.scalar_input_domains.is_empty() {
            "scalar_input_domains".hash(state);
            self.scalar_input_domains.hash(state);
        }
        if !self.object_input_domains.is_empty() {
            "object_input_domains".hash(state);
            self.object_input_domains.hash(state);
        }
        if !self.native_record_inputs.is_empty() {
            "native_record_inputs".hash(state);
            self.native_record_inputs.hash(state);
            self.native_record_input_origins.hash(state);
            self.native_record_input_reads.hash(state);
        }
    }
}

impl CHeapMemory {
    /// Equality of two heap states derived from `base`; see
    /// [`SnapshotMap::eq_relative_to`].
    fn eq_relative_to(&self, other: &Self, base: &Self) -> bool {
        self.live_allocations
            .eq_relative_to(&other.live_allocations, &base.live_allocations)
            && self.deallocated_allocations.eq_relative_to(
                &other.deallocated_allocations,
                &base.deallocated_allocations,
            )
            && self
                .pending_allocations
                .eq_relative_to(&other.pending_allocations, &base.pending_allocations)
            && self.uninitialized_allocations.eq_relative_to(
                &other.uninitialized_allocations,
                &base.uninitialized_allocations,
            )
            && self
                .uninitialized_objects
                .eq_relative_to(&other.uninitialized_objects, &base.uninitialized_objects)
            && self
                .object_input_domains
                .eq_relative_to(&other.object_input_domains, &base.object_input_domains)
            && self
                .scalar_input_domains
                .eq_relative_to(&other.scalar_input_domains, &base.scalar_input_domains)
            && self
                .native_record_inputs
                .eq_relative_to(&other.native_record_inputs, &base.native_record_inputs)
            && self.native_record_input_origins.eq_relative_to(
                &other.native_record_input_origins,
                &base.native_record_input_origins,
            )
            && self.native_record_input_reads.eq_relative_to(
                &other.native_record_input_reads,
                &base.native_record_input_reads,
            )
            && self
                .initialized
                .eq_relative_to(&other.initialized, &base.initialized)
            && self
                .zeroed_allocations
                .eq_relative_to(&other.zeroed_allocations, &base.zeroed_allocations)
            && self.zeroed_prefix_allocations.eq_relative_to(
                &other.zeroed_prefix_allocations,
                &base.zeroed_prefix_allocations,
            )
            && self.zeroed_pending_allocations.eq_relative_to(
                &other.zeroed_pending_allocations,
                &base.zeroed_pending_allocations,
            )
            && self
                .pending_reallocations
                .eq_relative_to(&other.pending_reallocations, &base.pending_reallocations)
    }

    /// C allocated-access prefixes record checked access knowledge, not a
    /// native object promise. Learning one in a loop body does not construct
    /// or retire an object. All other input kinds remain lifetime-sensitive.
    fn is_c_access_knowledge(&self, identity: &CNativeInputIdentity) -> bool {
        self.native_record_inputs
            .get(identity)
            .is_some_and(|input| {
                matches!(
                    input.kind,
                    CNativeInputKind::TypedPrefix {
                        policy: CTypedAccessPolicy::CAllocatedAccessAllowed,
                        ..
                    }
                )
            })
    }

    fn have_same_lifetime_inputs(&self, other: &Self) -> bool {
        for change in self.native_record_inputs.diff(&other.native_record_inputs) {
            let identity = change.key();
            if (self.native_record_inputs.contains_key(identity)
                && !self.is_c_access_knowledge(identity))
                || (other.native_record_inputs.contains_key(identity)
                    && !other.is_c_access_knowledge(identity))
            {
                return false;
            }
        }
        // Keep the lifetime-sensitive parts of the retirement and read-alias
        // indexes exact. Persistent diffs visit only changed paths and bucket
        // memberships; unrelated input witnesses are never scanned.
        self.have_same_lifetime_input_index(
            other,
            &self.native_record_input_origins,
            &other.native_record_input_origins,
        ) && self.have_same_lifetime_input_index(
            other,
            &self.native_record_input_reads,
            &other.native_record_input_reads,
        )
    }

    fn have_same_lifetime_input_index<K: Ord>(
        &self,
        other: &Self,
        before: &SnapshotMap<K, SnapshotSet<CNativeInputIdentity>>,
        after: &SnapshotMap<K, SnapshotSet<CNativeInputIdentity>>,
    ) -> bool {
        let empty = SnapshotSet::new();
        before.diff(after).all(|change| {
            let key = change.key();
            let left = before.get(key).unwrap_or(&empty);
            let right = after.get(key).unwrap_or(&empty);
            left.symmetric_difference(right)
                .into_iter()
                .all(|identity| {
                    // Unknown index entries fail closed too.
                    (self.is_c_access_knowledge(identity) || other.is_c_access_knowledge(identity))
                        && (!self.native_record_inputs.contains_key(identity)
                            || self.is_c_access_knowledge(identity))
                        && (!other.native_record_inputs.contains_key(identity)
                            || other.is_c_access_knowledge(identity))
                })
        })
    }

    /// Whether two heap states have the same allocation lifetime and shape.
    ///
    /// Typed initialization metadata is deliberately excluded: it describes
    /// knowledge about cells inside an allocation, not whether the allocation
    /// exists or has changed size. Loop back-edge checks use this distinction
    /// so a body may establish or forget cell initialization without being
    /// mistaken for an allocation-lifetime transition.
    pub(super) fn have_same_allocation_lifetimes(&self, other: &Self) -> bool {
        self.live_allocations == other.live_allocations
            && self.deallocated_allocations == other.deallocated_allocations
            && self.pending_allocations == other.pending_allocations
            && self.uninitialized_allocations == other.uninitialized_allocations
            && self.uninitialized_objects == other.uninitialized_objects
            && self.object_input_domains == other.object_input_domains
            && self.scalar_input_domains == other.scalar_input_domains
            && self.have_same_lifetime_inputs(other)
            && self.zeroed_allocations == other.zeroed_allocations
            && self.zeroed_prefix_allocations == other.zeroed_prefix_allocations
            && self.zeroed_pending_allocations == other.zeroed_pending_allocations
            && self.pending_reallocations == other.pending_reallocations
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(super) enum CDeclaredObject {
    Scalar(CType),
    Aggregate(Arc<CAggregateLayout>),
    Array {
        element_type: CType,
        count: u32,
        shape: Option<Arc<[u32]>>,
    },
}

impl std::hash::Hash for CDeclaredObject {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Self::Scalar(value) => value.hash(state),
            Self::Aggregate(layout) => layout.hash(state),
            Self::Array {
                element_type,
                count,
                shape,
            } => {
                element_type.hash(state);
                count.hash(state);
                if let Some(shape) = shape {
                    0x6172_7261_795f_726fu64.hash(state);
                    shape.hash(state);
                }
            }
        }
    }
}

/// The byte representation policy pinned by an actual native declaration.
/// It does not establish initialized bytes or access authority.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) enum UInt32RepresentationProfile {
    LittleEndian,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct CBlock {
    pub(super) size: Bitvector32Term,
    pub(super) read_only: bool,
    /// A complete object's actual declaration, independent of its values,
    /// initialization and ownership. Generic storage blocks carry none.
    pub(super) declared_object: Option<CDeclaredObject>,
    /// Automatic scalar declarations require their allocated permission;
    /// native global/static declarations retain their existing access policy.
    pub(super) explicit_scalar_ownership: bool,
    pub(super) uint32_representation: Option<UInt32RepresentationProfile>,
}

impl std::hash::Hash for CBlock {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.size.hash(state);
        self.read_only.hash(state);
        self.declared_object.hash(state);
        // Optional bookkeeping leaves legacy undeclared-block hashes stable.
        if self.explicit_scalar_ownership {
            "automatic scalar ownership".hash(state);
        }
        if let Some(profile) = self.uint32_representation {
            "uint32 representation".hash(state);
            profile.hash(state);
        }
    }
}

/// An interned, immutable memory snapshot for embedding inside terms.
///
/// Equality and hashing are O(1) via the arena identity and a precomputed
/// content hash; ordering keeps a same-identity fast path but falls back to
/// structural comparison so BTreeMap iteration order stays the structural
/// order (proof search is sensitive to iteration order, and arena-insertion
/// order would be nondeterministic across checks).
#[derive(Clone)]
pub struct SharedCMemory {
    arena: u32,
    id: u32,
    content_hash: u64,
    memory: std::sync::Arc<CMemory>,
}

impl SharedCMemory {
    /// How this snapshot was produced, when the arena that named it is this
    /// thread's and an edge producer recorded one.
    ///
    /// `None` is always a legitimate answer — for entry states, for
    /// snapshots built by paths that record no edge, and for handles that
    /// crossed a thread. Consumers fall back rather than conclude anything
    /// from the absence.
    pub(crate) fn derivation(&self) -> Option<std::sync::Arc<CMemoryDerivation>> {
        C_MEMORY_ARENA.with(|arena| {
            let arena = arena.borrow();
            if arena.0 != self.arena {
                return None;
            }
            arena.1.derivations.get(self.id as usize).cloned().flatten()
        })
    }

    /// The arena id naming this snapshot, valid only against ids from the
    /// same arena. Strictly decreasing along `derivation().base()`, which is
    /// what makes DAG walks terminate.
    pub(crate) fn arena_id(&self) -> (u32, u32) {
        (self.arena, self.id)
    }

    /// Producer-recorded identity of unchanged program bytes, for graph load
    /// congruence only. This is trusted-kernel metadata, not snapshot equality
    /// or access authority. It is fixed at first interning and looked up in O(1).
    pub(crate) fn read_identity(&self) -> (u32, u32) {
        C_MEMORY_ARENA.with(|arena| {
            let arena = arena.borrow();
            if arena.0 != self.arena {
                return self.arena_id();
            }
            (self.arena, arena.1.read_identities[self.id as usize])
        })
    }

    pub(crate) fn memory(&self) -> &CMemory {
        &self.memory
    }
}

impl PartialEq for SharedCMemory {
    fn eq(&self, other: &Self) -> bool {
        if self.arena == other.arena {
            return self.id == other.id;
        }
        self.content_hash == other.content_hash && self.memory == other.memory
    }
}

impl Eq for SharedCMemory {}

impl std::hash::Hash for SharedCMemory {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.content_hash);
    }
}

impl Ord for SharedCMemory {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.arena == other.arena && self.id == other.id {
            return std::cmp::Ordering::Equal;
        }
        self.memory.cmp(&other.memory)
    }
}

impl PartialOrd for SharedCMemory {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl std::fmt::Debug for SharedCMemory {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.memory.fmt(formatter)
    }
}

/// The compact identity of a memory snapshot at a retained proof frontier.
/// This only records the persistent-node pointers already held by `CMemory`;
/// it does not intern, clone, or scan the snapshot.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct CMemorySnapshotIdentity {
    shallow: CMemoryShallowIdentity,
}

#[cfg(test)]
thread_local! {
    static CALL_REQUIREMENT_SITE_CONSTRUCTION_COUNT: std::cell::Cell<u64> =
        const { std::cell::Cell::new(0) };
}

impl CMemorySnapshotIdentity {
    pub(crate) fn of(memory: &CMemory) -> Self {
        Self {
            shallow: CMemoryShallowIdentity::of(memory),
        }
    }
}

/// The exact source-side identity needed to retry one unresolved call
/// requirement.  This is deliberately limited to the selected callee, its
/// source argument expressions, and the call's source snapshot identity; it
/// does not retain a C state or an ambient fact set.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CallRequirementSite {
    pub(crate) callee: String,
    pub(crate) interface: std::sync::Arc<str>,
    pub(crate) candidate_ordinal: usize,
    pub(crate) source_arguments: std::sync::Arc<Vec<CExpression>>,
    pub(crate) source_snapshot: CMemorySnapshotIdentity,
}

impl CallRequirementSite {
    pub(crate) fn for_requirement(
        callee: impl Into<String>,
        interface: &str,
        candidate_ordinal: usize,
        source_arguments: &[CExpression],
        source_memory: &CMemory,
    ) -> Self {
        #[cfg(test)]
        CALL_REQUIREMENT_SITE_CONSTRUCTION_COUNT.with(|count| {
            count.set(count.get().saturating_add(1));
        });
        Self {
            callee: callee.into(),
            interface: std::sync::Arc::from(interface),
            candidate_ordinal,
            source_arguments: std::sync::Arc::new(source_arguments.to_vec()),
            source_snapshot: CMemorySnapshotIdentity::of(source_memory),
        }
    }

    #[cfg(test)]
    pub(crate) fn reset_test_construction_count() {
        CALL_REQUIREMENT_SITE_CONSTRUCTION_COUNT.with(|count| count.set(0));
    }

    #[cfg(test)]
    pub(crate) fn test_construction_count() -> u64 {
        CALL_REQUIREMENT_SITE_CONSTRUCTION_COUNT.with(std::cell::Cell::get)
    }
}

/// The selected top-level requirement attached to one unresolved call site.
/// The site identity is shared across requirements from that call, while the
/// ordinal remains specific to this requirement and its path obligations.
/// `None` denotes a generated clause or a kernel-built contract without a
/// source registry entry; ordinary callee source resolution is a later
/// planner concern.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CallRequirementSource {
    pub(crate) site: std::sync::Arc<CallRequirementSite>,
    pub(crate) requirement_ordinal: usize,
    pub(crate) source_requirement_ordinal: Option<usize>,
    /// Exact snapshot identity of the source-side load carrier, when this
    /// requirement is stateful and its lowering registered one.  This is
    /// separate from `site.source_snapshot`, which identifies the caller's
    /// frontier and must remain stable for source lookup.
    pub(crate) source_load_snapshot: Option<CMemorySnapshotIdentity>,
    /// Whether the complete selected source requirement is state independent.
    /// This is a capability of the top-level requirement, not of any one
    /// lowered leaf, so every obligation emitted from the requirement shares
    /// the same answer.
    pub(crate) source_requirement_is_state_independent: bool,
}

impl CallRequirementSource {
    pub(crate) fn new(
        site: std::sync::Arc<CallRequirementSite>,
        requirement_ordinal: usize,
        source_requirement_ordinal: Option<usize>,
        source_requirement_is_state_independent: bool,
        source_load_snapshot: Option<CMemorySnapshotIdentity>,
    ) -> Self {
        Self {
            site,
            requirement_ordinal,
            source_requirement_ordinal,
            source_load_snapshot,
            // Generated requirements and contracts without a source registry
            // must never advertise source-side capabilities.
            source_requirement_is_state_independent: source_requirement_ordinal.is_some()
                && source_requirement_is_state_independent,
        }
    }
}

impl std::ops::Deref for CallRequirementSource {
    type Target = CallRequirementSite;

    fn deref(&self) -> &Self::Target {
        &self.site
    }
}

impl std::ops::Deref for SharedCMemory {
    type Target = CMemory;

    fn deref(&self) -> &CMemory {
        &self.memory
    }
}

impl AsRef<CMemory> for SharedCMemory {
    fn as_ref(&self) -> &CMemory {
        &self.memory
    }
}

impl From<CMemory> for SharedCMemory {
    fn from(memory: CMemory) -> Self {
        intern_c_memory(memory)
    }
}

impl From<&CMemory> for SharedCMemory {
    fn from(memory: &CMemory) -> Self {
        intern_c_memory_ref(memory)
    }
}

/// How a memory snapshot was produced from an earlier one: the edges of the
/// named-memory-state DAG (`docs/internals/memory-dag.md`). Each
/// variant names its base snapshot, so following `base` walks backwards
/// through the write history that execution already knew when it built the
/// snapshot — instead of reconstructing that history at proof time from
/// recorded effect facts.
///
/// A derivation is **advisory**. It only ever states a true fact about how a
/// snapshot arose, so every consumer must fall back to its previous
/// reasoning when none is present; nothing may depend on one existing. That
/// is why a snapshot interned on another thread (the arena is thread-local)
/// is merely slower to reason about rather than wrong.
///
/// `LoopHavoc` is deliberately its own edge kind rather than a bulk store.
/// Interface havoc has no checked write set, so no load-preservation walk may
/// cross that form. Verified whole-loop effects may carry a checked write set;
/// those edges are crossed only with range-disjointness evidence. Enforcing
/// that at the edge is how havoc identity survives this arc by construction,
/// upstream of any snapshot comparison (see conventions.md's soundness trap).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CMemoryDerivation {
    /// `base` with one cell written. Aliasing between the written cell and
    /// a later load is decided in the querying proof context, never from
    /// facts captured on the edge: interning is first-wins on equal
    /// snapshots, so an edge can be shared by paths with different
    /// assumptions.
    Store {
        base: SharedCMemory,
        pointer: Pointer,
        value: CValue,
    },
    /// `base` with one block declared; no cell changes, so every load reads
    /// exactly what it read in `base`. This fourth edge kind was added after
    /// the initial DAG arc; without it, block declaration split the DAG into
    /// disjoint components ("arena identity is connected, arena derivations
    /// are not"). The havoc producers insert their marker
    /// blocks directly rather than through [`CMemory::with_block`], so this
    /// edge can never alias a havoc hop.
    BlockDeclared {
        base: SharedCMemory,
        block: PointerBlock,
    },
    /// `base` with one fresh, uninitialized heap block made live.
    HeapAllocated {
        base: SharedCMemory,
        block: PointerBlock,
        bytes: Bitvector32Term,
    },
    /// `base` with one unresolved allocation result registered. Pending
    /// metadata changes no program-observable memory, so every existing load
    /// is preserved across this edge.
    HeapAllocationPending {
        base: SharedCMemory,
        allocation_base: Pointer,
        bytes: Bitvector32Term,
    },
    /// `base` with a failed pending allocation removed. No storage was
    /// allocated or written; existing reads retain their validity and value.
    HeapAllocationFailed { base: SharedCMemory },
    /// `base` with only the allocation claims imported from contracts
    /// changed. Consuming an input claim and installing an output claim do
    /// not write bytes, allocate storage, or free storage, so every load is
    /// preserved across this edge.
    ContractAllocationClaimsChanged { base: SharedCMemory },
    /// `base` after an input allocation claim was consumed by a contract
    /// that does not decide continuity. The callee may have freed the object,
    /// so cached contents and status for that allocation cannot cross this
    /// edge even though no definite C `free` is asserted.
    ContractAllocationRetired {
        base: SharedCMemory,
        allocation_base: Pointer,
        bytes: Bitvector32Term,
    },
    /// `base` with one complete heap allocation lifetime ended.
    ///
    /// `allocation_base` is kept rather than only its broad pointer block:
    /// allocations imported from contracts can be subranges of external
    /// memory, where retiring the whole `ExternalArgument` block would also
    /// deallocate unrelated objects.
    HeapFreed {
        base: SharedCMemory,
        allocation_base: Pointer,
        bytes: Bitvector32Term,
    },
    /// `base` with only the initialized-byte record extended. The writes
    /// establishing those bytes have their own earlier edges; recording this
    /// metadata changes no stored value and must not disconnect that history.
    ObjectInitializationRecorded {
        base: SharedCMemory,
        pointer: Pointer,
        bytes: u32,
    },
    /// `base` with some cached cell values forgotten at one program point:
    /// the write path narrows the cell map before storing
    /// (`without_possible_aliasing_cells`), which changes the form but
    /// not the state, so every load still reads exactly what it read in
    /// `base`. Recorded ONLY where forgetting is unconditional; the
    /// case-split prune in the load path (`without_cell` under an assumed
    /// distinctness branch) must never record one, because its two forms
    /// agree only under that branch's assumption. Havoc forgetting keeps its
    /// own never-crossed / guarded edge kinds, so this edge cannot launder a
    /// havoc (conventions.md's soundness trap).
    CellsForgotten { base: SharedCMemory },
    /// `base` after a loop body that may write anything it can reach.
    ///
    /// `mutable_ranges` is present only when the loop's whole-effect summary
    /// supplied a checked footprint. `None` remains an unconditional barrier;
    /// `Some(empty)` is a checked no-write footprint.
    LoopHavoc {
        base: SharedCMemory,
        variable: Variable,
        mutable_ranges: Option<Vec<CMemoryRange>>,
    },
    /// `base` after an automatic-storage object's lifetime ended. The block
    /// is named so the memory-DAG can preserve unrelated loads while stopping
    /// every load through an alias to this retired object.
    LocalLifetimeEnded {
        base: SharedCMemory,
        block: PointerBlock,
    },
    /// A memory abstraction of all incoming branch states. A read crosses
    /// only with typed evidence that every incoming memory agrees with `base`
    /// on the complete access. The constructor retains all inputs in the
    /// snapshot identity; this edge carries no branch-local assumptions.
    BranchJoin {
        base: SharedCMemory,
        incoming: Vec<SharedCMemory>,
    },
    /// `base` after a call that may write only within `mutable_ranges`.
    ///
    /// Preservation of a load outside those ranges must be justified in the
    /// querying proof context. Two paths with different assumptions (for
    /// example `length == 0` and `length == 1`) can produce this exact
    /// snapshot, so no path's assumptions may be attached to the edge.
    ///
    /// `kept_by_caller` is the owned memory the caller kept outside the
    /// transfer, when it held any: the one-layer bodies of its residual owned
    /// instances and composites, and every flat owned residual member in a
    /// block the write set may alias, whether or not its cell was cached.
    /// The callee cannot write a byte of it, since owned memory is a
    /// partition at the call; the write-set marker spells these ranges, so
    /// the edge is shared only by paths that kept the same memory.
    CallHavoc {
        base: SharedCMemory,
        variable: Variable,
        mutable_ranges: Vec<CMemoryRange>,
        kept_by_caller: Option<CallKeptRanges>,
    },
    /// `base` with a run of seeded cells added: exactly the stores, in
    /// element order, of each slot the run held live when it was seeded
    /// ([`CellRun`]). One edge stands for the whole run so that seeding a
    /// constant range costs the same whatever its length; every consumer
    /// reads it as that sequence of stores ([`Self::seeded_stores`]).
    CellsSeeded {
        base: SharedCMemory,
        run: std::sync::Arc<CellRun>,
    },
}

impl CMemoryDerivation {
    /// The stores a `CellsSeeded` edge stands for, newest first: the order a
    /// walk from the produced snapshot meets them in. `None` for every other
    /// edge kind.
    pub(crate) fn seeded_stores(&self) -> Option<Vec<(Pointer, CValue)>> {
        let Self::CellsSeeded { run, .. } = self else {
            return None;
        };
        let mut stores = run
            .live_indexes()
            .map(|index| (run.slot_pointer(index), run.value(index)))
            .collect::<Vec<_>>();
        stores.reverse();
        Some(stores)
    }

    /// The edge kind's name, for census rows that must stay readable
    /// without carrying a snapshot.
    pub(crate) fn kind_name(&self) -> &'static str {
        match self {
            Self::CellsSeeded { .. } => "CellsSeeded",
            Self::Store { .. } => "Store",
            Self::BlockDeclared { .. } => "BlockDeclared",
            Self::HeapAllocated { .. } => "HeapAllocated",
            Self::HeapAllocationPending { .. } => "HeapAllocationPending",
            Self::HeapAllocationFailed { .. } => "HeapAllocationFailed",
            Self::ContractAllocationClaimsChanged { .. } => "ContractAllocationClaimsChanged",
            Self::ContractAllocationRetired { .. } => "ContractAllocationRetired",
            Self::HeapFreed { .. } => "HeapFreed",
            Self::ObjectInitializationRecorded { .. } => "ObjectInitializationRecorded",
            Self::CellsForgotten { .. } => "CellsForgotten",
            Self::LocalLifetimeEnded { .. } => "LocalLifetimeEnded",
            Self::LoopHavoc { .. } => "LoopHavoc",
            Self::CallHavoc { .. } => "CallHavoc",
            Self::BranchJoin { .. } => "BranchJoin",
        }
    }

    /// The snapshot this one was derived from.
    pub fn base(&self) -> &SharedCMemory {
        match self {
            Self::Store { base, .. }
            | Self::BlockDeclared { base, .. }
            | Self::HeapAllocated { base, .. }
            | Self::HeapAllocationPending { base, .. }
            | Self::HeapAllocationFailed { base }
            | Self::ContractAllocationClaimsChanged { base }
            | Self::ContractAllocationRetired { base, .. }
            | Self::HeapFreed { base, .. }
            | Self::ObjectInitializationRecorded { base, .. }
            | Self::CellsForgotten { base }
            | Self::LocalLifetimeEnded { base, .. }
            | Self::LoopHavoc { base, .. }
            | Self::CallHavoc { base, .. }
            | Self::BranchJoin { base, .. }
            | Self::CellsSeeded { base, .. } => base,
        }
    }
}

static NEXT_MEMORY_ARENA_TOKEN: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);

#[derive(Clone, Default)]
struct CMemoryArena {
    identities: std::collections::HashMap<std::sync::Arc<CMemory>, (u32, u64)>,
    shallow_identities: std::collections::HashMap<CMemoryShallowIdentity, (u32, u64)>,
    /// Snapshots whose storage roots were registered in `shallow_identities`
    /// on a structural hit. Holding them keeps those roots allocated, so a
    /// registered address cannot be reused by a different map. Each pin is
    /// an O(1) handle clone.
    shallow_pins: Vec<CMemory>,
    memories: Vec<std::sync::Arc<CMemory>>,
    /// The recorded children of each base, by the child's content hash: a
    /// derivation re-run from the same base (planning and then checking one
    /// statement, say) is recognized here by comparing its changes from the
    /// base, instead of its whole content, before the structural lookup.
    derived_children: std::collections::HashMap<(u32, u64), Vec<u32>>,
    /// Indexed by arena id; `None` for entry states and for any snapshot
    /// whose first interning did not come from a recorded edge.
    derivations: Vec<Option<std::sync::Arc<CMemoryDerivation>>>,
    /// Immutable load-congruence keys. Producers reuse the base's key only
    /// for an unconditional byte-preserving transition. No history is queried.
    read_identities: Vec<u32>,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct CMemoryShallowIdentity {
    blocks: usize,
    cells: usize,
    union_cells: usize,
    forgotten: usize,
    heap: usize,
}

impl CMemoryShallowIdentity {
    fn of(memory: &CMemory) -> Self {
        Self {
            blocks: std::sync::Arc::as_ptr(&memory.blocks) as usize,
            cells: std::sync::Arc::as_ptr(&memory.cells) as usize,
            union_cells: std::sync::Arc::as_ptr(&memory.union_cells) as usize,
            forgotten: std::sync::Arc::as_ptr(&memory.forgotten) as usize,
            heap: std::sync::Arc::as_ptr(&memory.heap) as usize,
        }
    }
}

thread_local! {
    static C_MEMORY_ARENA: std::cell::RefCell<(u32, CMemoryArena)> = std::cell::RefCell::new((
        NEXT_MEMORY_ARENA_TOKEN.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
        CMemoryArena::default(),
    ));
    static C_MEMORY_DERIVATION_GENERATION: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Replaces this thread's memory arena with an empty one under a fresh
/// token. Snapshots interned before keep comparing by content but lose
/// their derivations, so nothing recorded for an earlier verification can
/// answer a DAG walk in a later one. Called by [`super::VerificationSession`]
/// at the outermost verification entry; see its documentation.
/// This thread's memory arena as one value: its token, every interned
/// snapshot with its derivation, and the derivation generation. Clones share
/// the snapshots' storage, so a capture costs one handle per arena entry.
#[derive(Clone)]
pub(super) struct CMemoryArenaState {
    arena: (u32, CMemoryArena),
    derivation_generation: u64,
}

/// How many entries the arena holds: interned snapshots and pinned roots.
#[cfg(test)]
pub(super) fn c_memory_arena_entry_count() -> usize {
    C_MEMORY_ARENA.with(|arena| {
        let arena = arena.borrow();
        arena.1.memories.len() + arena.1.shallow_pins.len()
    })
}

pub(super) fn capture_c_memory_arena() -> CMemoryArenaState {
    CMemoryArenaState {
        arena: C_MEMORY_ARENA.with(|arena| arena.borrow().clone()),
        derivation_generation: C_MEMORY_DERIVATION_GENERATION.with(std::cell::Cell::get),
    }
}

/// Reinstalls a captured arena under its own token, so every snapshot id the
/// capture's holder kept still names the same snapshot and derivation, and
/// nothing interned since remains.
pub(super) fn restore_c_memory_arena(state: &CMemoryArenaState) {
    C_MEMORY_ARENA.with(|arena| *arena.borrow_mut() = state.arena.clone());
    C_MEMORY_DERIVATION_GENERATION.with(|generation| generation.set(state.derivation_generation));
}

pub(super) fn start_fresh_c_memory_arena() {
    C_MEMORY_ARENA.with(|arena| {
        *arena.borrow_mut() = (
            NEXT_MEMORY_ARENA_TOKEN.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
            CMemoryArena::default(),
        );
    });
}

/// Bumped every time a derivation slot is filled on a snapshot that was
/// interned before the edge was recorded. Memo tables over DAG walks key on
/// this so an edge recorded later invalidates earlier "no path" answers
/// instead of leaving them stale.
///
/// A recording that interns the snapshot it derives does not bump it: no
/// earlier question could name that snapshot, and an existing snapshot's
/// history never changes, so no earlier answer can. Bumping on those too
/// emptied every negative memo at every program step, and a call step re-ran
/// each failed alias question its walks had already answered.
pub(super) fn c_memory_derivation_generation() -> u64 {
    C_MEMORY_DERIVATION_GENERATION.with(std::cell::Cell::get)
}

/// Interns `memory` as the base of a derivation about to be applied to it,
/// and replaces it with the arena's canonical storage for that content (an
/// O(1) handle clone). Every recorded result is therefore derived from its
/// base's canonical storage and shares every unchanged subtree with it, which
/// is what lets [`record_c_memory_derivation`] compare a re-derived result
/// against an earlier child of the same base along the changed paths only.
pub(crate) fn intern_derivation_base(memory: &mut CMemory) -> SharedCMemory {
    let base = intern_c_memory_ref(memory);
    if !memory.same_storage_roots(base.memory()) {
        *memory = base.memory().clone();
    }
    base
}

/// Records that `result` is `derivation` applied to its base, unless
/// `result` already carries a derivation.
///
/// **First-wins is load-bearing, not a cache policy.** A derivation's base
/// must already be interned in order to be named, so it always holds a
/// strictly smaller arena id than a *newly* assigned one. Keeping the first
/// derivation therefore makes `base.id < derived.id` an arena-wide
/// invariant, and cycles unrepresentable rather than merely unlikely. Two
/// otherwise easy cycles are closed by exactly this: a store whose value
/// equals the cell already there (the result re-interns to its own base, so
/// `base.id == result.id` and the edge is dropped), and a store-then-store-
/// back pair (the second result re-interns to the earlier node and keeps
/// that node's older derivation). Callers may rely on any walk over `base`
/// terminating; a hop cap still depth-gates them, per conventions.md.
///
/// `result` is replaced by the arena's canonical instance of its content, an
/// O(1) handle clone. The edge recorded is the same either way; carrying the
/// canonical instance forward means every later snapshot derived from this
/// one shares storage roots with whatever the arena already holds, so facts
/// and terms that embed equal snapshots compare by root identity.
pub(crate) fn record_c_memory_derivation(result: &mut CMemory, derivation: CMemoryDerivation) {
    let derivation = Arc::new(derivation);
    result.construction = Some(Arc::new(CMemoryConstruction {
        roots: result.diagnostic_roots(),
        kind: CMemoryConstructionKind::Transition(derivation.clone()),
    }));
    if let Some(child) = recorded_child_matching(result, derivation.base()) {
        // Already this base's recorded child: its derivation slot is filled,
        // so recording would change nothing but the storage handed back.
        *result = child;
        return;
    }
    // Interning borrows the arena, so it has to finish before the write.
    let read_identity = match derivation.as_ref() {
        CMemoryDerivation::CellsForgotten { base } => Some(base.read_identity()),
        CMemoryDerivation::CellsSeeded { base, run }
            if matches!(run.value_mode(), cell_store::RunValueMode::Load)
                && run.element_width() == run.value_width()
                && base.read_identity() == run.source().read_identity() =>
        {
            // Copying the same bytes already in the base is materialization,
            // including sibling runs copied from an equivalent earlier source.
            Some(base.read_identity())
        }
        _ => None,
    };
    // A snapshot this call interns is one no query has seen yet, so filling
    // its derivation cannot change an earlier answer.
    let next_id = C_MEMORY_ARENA.with(|arena| arena.borrow().1.identities.len());
    let derived = intern_c_memory_ref_with_read_identity(result, read_identity);
    let interned_here = derived.id as usize >= next_id;
    if !result.same_storage_roots(derived.memory()) {
        *result = derived.memory().clone();
    }
    C_MEMORY_ARENA.with(|arena| {
        let mut arena = arena.borrow_mut();
        if arena.0 != derived.arena || arena.0 != derivation.base().arena {
            return;
        }
        let arena = &mut arena.1;
        let Some(slot) = arena.derivations.get_mut(derived.id as usize) else {
            return;
        };
        if slot.is_some() {
            return;
        }
        if derivation.base().id >= derived.id {
            // A step that ends on a node older than itself is recorded
            // nowhere — so whatever happened in between is on no history,
            // and every history-based rule inherits a chain that silently
            // re-rooted. Where the step lost knowledge that is a
            // false-theorem shape, which is what the forget mark rules out
            // at the producer. Where it lost nothing the older node is an
            // ancestor whose history is this path's own prefix, which is
            // why this stays a census rather than an assertion here.
            crate::instrumentation::record_backwards_memory_derivation(
                derivation.kind_name(),
                derivation.base().id == derived.id,
            );
            return;
        }
        let base_id = derivation.base().id;
        *slot = Some(derivation);
        arena
            .derived_children
            .entry((base_id, derived.content_hash))
            .or_default()
            .push(derived.id);
        if !interned_here {
            C_MEMORY_DERIVATION_GENERATION.with(|generation| generation.set(generation.get() + 1));
        }
    });
}

/// The canonical storage of a recorded child of `base` equal to `result`,
/// when there is one.
///
/// `result` was derived from `base`'s canonical storage
/// ([`intern_derivation_base`]) and so was every recorded child, so both share
/// all of `base` that their updates did not touch and the comparison walks
/// only the changed paths. The answer is exact either way.
fn recorded_child_matching(result: &CMemory, base: &SharedCMemory) -> Option<CMemory> {
    let content_hash = c_memory_content_hash(result);
    C_MEMORY_ARENA.with(|arena| {
        let arena = arena.borrow();
        if arena.0 != base.arena {
            return None;
        }
        let arena = &arena.1;
        let children = arena.derived_children.get(&(base.id, content_hash))?;
        crate::instrumentation::record_deterministic_work(1);
        children.iter().find_map(|child| {
            let stored = &arena.memories[*child as usize];
            result
                .eq_relative_to(stored, base.memory())
                .then(|| stored.as_ref().clone())
        })
    })
}

fn c_memory_content_hash(memory: &CMemory) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    memory.hash(&mut hasher);
    hasher.finish()
}

/// The component collections a snapshot hashes: three memory maps, the
/// ended-lifetime set, the nine heap collections, and the forget mark.
const C_MEMORY_HASHED_COMPONENTS: usize = 14;

/// Charges a structural arena lookup. Hashing is O(1) per component because
/// each collection caches its content hash; the comparison a bucket hit
/// performs is charged by the collections' own `eq`, per element actually
/// compared, and is O(1) for snapshots sharing their persistent roots.
fn record_c_memory_structural_lookup_work() {
    crate::instrumentation::record_deterministic_work(C_MEMORY_HASHED_COMPONENTS);
}

/// Interns a memory snapshot in the thread-local arena. Structurally equal
/// snapshots interned on the same thread share one allocation and identity;
/// snapshots that cross threads still compare correctly through the content
/// hash and structural fallback.
pub fn intern_c_memory(memory: CMemory) -> SharedCMemory {
    C_MEMORY_ARENA.with(|arena| {
        let mut arena = arena.borrow_mut();
        let (token, arena) = &mut *arena;
        let shallow_identity = CMemoryShallowIdentity::of(&memory);
        if let Some((id, content_hash)) = arena.shallow_identities.get(&shallow_identity).copied() {
            return SharedCMemory {
                arena: *token,
                id,
                content_hash,
                memory: arena.memories[id as usize].clone(),
            };
        }
        record_c_memory_structural_lookup_work();
        if let Some((stored, (id, content_hash))) = arena.identities.get_key_value(&memory) {
            let (id, content_hash, stored) = (*id, *content_hash, stored.clone());
            // Remember the caller's storage roots, so the next lookup of this
            // same snapshot is an O(1) shallow hit instead of another
            // comparison. The pin keeps those roots alive: a registered
            // address must never be freed and reused by different content.
            arena
                .shallow_identities
                .insert(shallow_identity, (id, content_hash));
            arena.shallow_pins.push(memory);
            return SharedCMemory {
                arena: *token,
                id,
                content_hash,
                memory: stored,
            };
        }
        let id = u32::try_from(arena.identities.len()).expect("memory arena exhausted");
        let content_hash = c_memory_content_hash(&memory);
        let stored = std::sync::Arc::new(memory);
        arena.identities.insert(stored.clone(), (id, content_hash));
        arena
            .shallow_identities
            .insert(shallow_identity, (id, content_hash));
        arena.memories.push(stored.clone());
        arena.derivations.push(None);
        arena.read_identities.push(id);
        SharedCMemory {
            arena: *token,
            id,
            content_hash,
            memory: stored,
        }
    })
}

/// The interned snapshot `memory` is the canonical storage of, found by its
/// storage roots alone, or `None`. Interns nothing and compares no content:
/// a snapshot a derivation produced carries its interned storage forward
/// ([`record_c_memory_derivation`]), so a live state's memory is found here
/// in O(1), and any other memory is left to the caller.
pub(crate) fn interned_storage_of(memory: &CMemory) -> Option<SharedCMemory> {
    C_MEMORY_ARENA.with(|arena| {
        let arena = arena.borrow();
        let (token, arena) = &*arena;
        let (id, content_hash) = arena
            .shallow_identities
            .get(&CMemoryShallowIdentity::of(memory))
            .copied()?;
        Some(SharedCMemory {
            arena: *token,
            id,
            content_hash,
            memory: arena.memories[id as usize].clone(),
        })
    })
}

/// Interns by reference: an already-interned snapshot is found without
/// cloning it, so hot memoization lookups keyed by interned identity pay a
/// hash and comparison but no allocation.
pub fn intern_c_memory_ref(memory: &CMemory) -> SharedCMemory {
    intern_c_memory_ref_with_read_identity(memory, None)
}

/// First interning wins, including its read identity. Existing snapshots never
/// change keys underneath registered applications; an earlier unannotated hit
/// conservatively loses this equality rather than requiring graph rescans.
fn intern_c_memory_ref_with_read_identity(
    memory: &CMemory,
    read_identity: Option<(u32, u32)>,
) -> SharedCMemory {
    C_MEMORY_ARENA.with(|arena| {
        let mut arena = arena.borrow_mut();
        let (token, arena) = &mut *arena;
        let shallow_identity = CMemoryShallowIdentity::of(memory);
        if let Some((id, content_hash)) = arena.shallow_identities.get(&shallow_identity).copied() {
            return SharedCMemory {
                arena: *token,
                id,
                content_hash,
                memory: arena.memories[id as usize].clone(),
            };
        }
        record_c_memory_structural_lookup_work();
        if let Some((stored, (id, content_hash))) = arena.identities.get_key_value(memory) {
            let (id, content_hash, stored) = (*id, *content_hash, stored.clone());
            // Remember the caller's storage roots, so the next lookup of this
            // same snapshot is an O(1) shallow hit instead of another
            // comparison. The pin keeps those roots alive: a registered
            // address must never be freed and reused by different content.
            arena
                .shallow_identities
                .insert(shallow_identity, (id, content_hash));
            arena.shallow_pins.push(memory.clone());
            return SharedCMemory {
                arena: *token,
                id,
                content_hash,
                memory: stored,
            };
        }
        let id = u32::try_from(arena.identities.len()).expect("memory arena exhausted");
        let content_hash = c_memory_content_hash(memory);
        let stored = std::sync::Arc::new(memory.clone());
        arena.identities.insert(stored.clone(), (id, content_hash));
        arena
            .shallow_identities
            .insert(shallow_identity, (id, content_hash));
        arena.memories.push(stored.clone());
        arena.derivations.push(None);
        arena.read_identities.push(
            read_identity
                .filter(|(source_arena, source)| *source_arena == *token && *source < id)
                .map_or(id, |(_, source)| source),
        );
        SharedCMemory {
            arena: *token,
            id,
            content_hash,
            memory: stored,
        }
    })
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) struct PopulationEffects {
    /// Read permissions captured for evaluating a predicate's immutable count
    /// snapshot. The creation root supplies its logical identity; this witness
    /// cannot supply resources to an execution or resource rewrite.
    pub(super) predicate_count_permissions: Option<PredicateCountPermissions>,

    /// Creation provenance is shared out-of-line to keep CState's recursive
    /// checker stack footprint unchanged. Legacy states use None.
    pub(super) creation: Option<super::population_authority::c_creation::CreationEvents>,
}

/// Whether an aggregate return copies a value or completes caller storage.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CAggregateReturnMode {
    #[default]
    Copy,
    Construction,
}

/// Call metadata only. Selecting it grants neither storage nor ownership.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) struct CAggregateDestination {
    pub(super) pointer: Pointer,
    pub(super) layout: CAggregateLayout,
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CState {
    pub(super) typed_access_policy: CTypedAccessPolicy,
    pub(super) aggregate_destination: Option<Arc<CAggregateDestination>>,
    /// Lexical field values for scratch resource-body evaluation only.
    /// This is not ownership and is never populated by unfolding a resource.
    pub(super) instance_field_scope: ResourceContext,
    /// Call-local formal identities; the ledger retains actual caller identities.
    pub(super) resource_bindings: Option<std::sync::Arc<BTreeMap<Variable, Variable>>>,
    pub(super) locals: CLocalEnvironment,
    pub(super) memory: CMemory,
    pub(super) resources: ResourceContext,
    /// Active stable-view authority. `None` is the canonical empty ledger so
    /// independently constructed states retain ordinary structural equality.
    pub(super) loan_ledger: Option<super::loans::LoanLedger>,
    /// Holder identity for the authority carried by this state. Keeping it
    /// beside the immutable ledger lets nested candidate calls reuse the
    /// caller's participant when lending a view.
    pub(super) loan_participant: Option<super::loans::LoanParticipantId>,
    /// Exact resource-occurrence bindings for live borrowed views. This map
    /// is carried with checked state so nested calls can reborrow by identity.
    pub(super) loan_view_bindings: super::loans::LoanViewBindings,
    /// Live child completion rights travel with the C path through ordinary
    /// statements. `None` is the canonical state before any thread operation.
    pub(super) thread_ledger: Option<super::threads::ThreadLedger>,
    /// Initialized mutex invariants and live guards on this C path. `None`
    /// denotes the canonical state before the first mutex operation.
    pub(super) mutex_ledger: Option<super::mutexes::MutexLedger>,
    /// Entry mutex protocols are preserved. Direct use inputs permit only
    /// balanced opaque acquisitions; entry guards and lifetimes stay framed.
    pub(super) preserves_mutex_protocols: bool,
    /// Storage reserved by abstract contract inputs, retained independently
    /// of their current folded/unfolded representation.
    pub(super) mutex_input_reservations: Option<super::mutexes::MutexInputReservations>,
    /// Exact local receipts for opaque acquisitions; no payload authority.
    pub(super) opaque_mutex_acquisitions: Option<super::mutexes::OpaqueMutexAcquisitions>,
    /// Proof names for exact owned mutex authority occurrences. Names never
    /// contribute ownership and are checked against resources on resolution.
    pub(super) named_mutex_authorities: Option<Arc<super::named_authority::NamedMutexAuthorities>>,
    /// One unresolved modeled pthread creation. The visible state carries
    /// only authority safe in either outcome; this record selects the exact
    /// checked delta when a C condition establishes the returned status.
    pub(super) pending_thread_create: Option<super::threads::PendingThreadCreate>,
    pub(super) population_access: super::population_access::PopulationAccess,
    /// Resource families the proof has observed, for authority loan
    /// classification (`functions::observes_population_family`).
    pub(super) observed_population_families: ObservedPopulationFamilies,
    /// Shared persistent roots keep population effect accounting to one word
    /// in each execution state, including recursive specification evaluation.
    pub(super) population_effects: Arc<PopulationEffects>,
    /// Monotonic identity source for stack frames created by nested calls.
    /// Keeping this in the symbolic state makes frame identities deterministic
    /// and ensures recursive calls cannot reuse a caller's stack slots.
    pub(super) next_local_frame: u64,
    /// Monotonic identity source for automatic-storage objects whose
    /// declaration can be re-entered by a loop. This is path state so joins
    /// and nested calls cannot accidentally reuse an ended local block.
    pub(super) next_local_lifetime: u64,
    /// Whether some frame this one was called from holds automatic objects.
    ///
    /// A called frame runs on the caller's memory with its own locals map, so
    /// it cannot see which objects the caller already has, and an object the
    /// caller holds only as a value has no block to find in memory either.
    /// Where the answer is yes, every declaration takes a fresh generation
    /// rather than the plain `local:<name>` spelling, which then belongs to
    /// the frame that already had it. A frame called from one that has bound
    /// nothing — the outermost one — has nothing to collide with and keeps
    /// the plain spelling.
    pub(super) enclosing_frame_holds_locals: bool,
}

#[derive(Clone)]
pub(super) struct PredicateCountPermissions(pub(super) std::sync::Arc<ResourceContext>);

// Permissions justify observing the count but do not change its value. The
// enclosing CState compares the captured creation root independently.
impl PartialEq for PredicateCountPermissions {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl Eq for PredicateCountPermissions {}
impl PartialOrd for PredicateCountPermissions {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for PredicateCountPermissions {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}
impl std::hash::Hash for PredicateCountPermissions {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}
impl std::fmt::Debug for PredicateCountPermissions {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("<captured count read permissions>")
    }
}

type ResourceEntryId = u64;
type ResourceEntryIds = PersistentSet<ResourceEntryId>;
type ResourceOccurrenceIds = PersistentSet<ResourceOccurrenceId>;

/// Identity of an owned resource occurrence, distinct from local entry IDs.
/// Occurrences are never recycled by replacement or normalization.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct ResourceOccurrenceId {
    arena: u64,
    ordinal: u64,
}

impl ResourceOccurrenceId {
    pub(crate) fn arena(self) -> u64 {
        self.arena
    }

    pub(crate) fn ordinal(self) -> u64 {
        self.ordinal
    }

    fn fresh() -> Self {
        static NEXT_ARENA: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
        thread_local! {
            static ALLOCATOR: std::cell::Cell<Option<(u64, u64)>> =
                const { std::cell::Cell::new(None) };
        }
        ALLOCATOR.with(|allocator| {
            let (arena, ordinal) = allocator.get().unwrap_or_else(|| {
                (
                    NEXT_ARENA.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
                    0,
                )
            });
            allocator.set(Some((arena, ordinal + 1)));
            Self { arena, ordinal }
        })
    }
}

/// An immutable resource composition snapshot.
///
/// One pointer-sized storage root keeps recursive execution frames shallow.
/// Forks share that root; a local insertion or removal replaces only the
/// logarithmic paths in the fact store and affected indexes.
#[derive(Default)]
pub struct ResourceContext {
    /// Diagnostic path state, omitted from semantic equality, hashing and ordering.
    /// A shared persistent root keeps clones constant-work and never copies facts.
    instance_consumptions: Option<std::sync::Arc<PersistentMap<Variable, InstanceConsumption>>>,
    /// Derived trusted-kernel index. It never supplies ownership evidence.
    memory_equalities: std::sync::Mutex<memory_equality_index::MemoryPairings>,
    pub(super) storage: std::sync::Arc<ResourceContextStorage>,
    /// Disposable projection, never ownership evidence or semantic identity.
    /// Immutable forks share even the cold cache; producers detach it before
    /// advancing only their own delta.
    pub(super) observable_projection:
        std::sync::Arc<std::sync::Mutex<Option<ObservableResourceProjection>>>,
    /// Checked dependency bundles for resource occurrences that are views of
    /// an active stable loan.  This is deliberately separate from the
    /// resource algebra's support graph: equal resource terms can have
    /// different loan origins, and a rewrite must preserve the opaque
    /// occurrence identity rather than rediscovering it from the term.
    pub(super) loan_dependencies: std::sync::Arc<crate::kernel::loans::LoanViewBindingsState>,
}

impl Clone for ResourceContext {
    fn clone(&self) -> Self {
        Self {
            instance_consumptions: self.instance_consumptions.clone(),
            storage: self.storage.clone(),
            observable_projection: self.observable_projection.clone(),
            loan_dependencies: self.loan_dependencies.clone(),
            memory_equalities: std::sync::Mutex::new(
                self.memory_equalities
                    .lock()
                    .expect("memory equality index")
                    .clone(),
            ),
        }
    }
}

impl ResourceContext {
    /// Diagnostic provenance only; this never grants ownership or supplies a fact.
    pub(crate) fn instance_consumption(&self, identity: Variable) -> Option<&InstanceConsumption> {
        self.instance_consumptions.as_ref()?.get(&identity)
    }

    pub(super) fn record_instance_consumption(
        &mut self,
        identity: Variable,
        cause: Option<InstanceConsumption>,
    ) {
        let Some(map) = self.instance_consumptions.as_deref() else {
            if let Some(cause) = cause {
                self.instance_consumptions = Some(std::sync::Arc::new(
                    PersistentMap::default().with_inserted(identity, cause),
                ));
            }
            return;
        };
        let updated = match cause {
            Some(cause) => map.with_inserted(identity, cause),
            None => map.without_key(&identity),
        };
        self.instance_consumptions = (!updated.is_empty()).then(|| std::sync::Arc::new(updated));
    }

    /// True only for the constant-work empty semantic form. Mutation ancestry
    /// and next-entry counters are intentionally omitted, as in `PartialEq`.
    pub(crate) fn is_pristine_semantically_empty(&self) -> bool {
        self.storage.facts.is_empty()
            && self.storage.supported_by.is_empty()
            && self.storage.support_occurrence_by_projection.is_empty()
            && self.storage.expansions_by_support_entry.is_empty()
            && self.loan_dependencies.map.is_empty()
    }

    /// Return a live dependency for an exact occurrence.  The occurrence
    /// lookup is checked against this context so stale sidecar entries can
    /// never authorize a rewritten or removed resource.
    pub(crate) fn loan_dependency(
        &self,
        occurrence: ResourceOccurrenceId,
    ) -> Option<&crate::kernel::loans::LoanViewBinding> {
        self.storage
            .entry_by_occurrence
            .contains_key(&occurrence)
            .then(|| self.loan_dependencies.map.get(&occurrence))
            .flatten()
    }

    /// Attach one checked dependency to a freshly inserted occurrence.
    /// Callers must identify the destination occurrence returned by the
    /// resource insertion operation; value equality is intentionally not a
    /// valid substitute for that identity.
    pub(crate) fn with_loan_dependency(
        mut self,
        occurrence: ResourceOccurrenceId,
        dependency: crate::kernel::loans::LoanViewBinding,
    ) -> Self {
        if self.storage.entry_by_occurrence.contains_key(&occurrence) {
            if let Some(existing) = self.loan_dependencies.map.get(&occurrence) {
                if existing != &dependency {
                    return self;
                }
                return self;
            }
            self.loan_dependencies = self.loan_dependencies.updated(
                self.loan_dependencies
                    .map
                    .with_inserted(occurrence, dependency),
                [occurrence],
            );
        }
        self
    }

    pub(crate) fn loan_dependency_state(
        &self,
    ) -> std::sync::Arc<crate::kernel::loans::LoanViewBindingsState> {
        self.loan_dependencies.clone()
    }

    pub(crate) fn with_loan_dependency_state(
        mut self,
        state: std::sync::Arc<crate::kernel::loans::LoanViewBindingsState>,
    ) -> Self {
        self.loan_dependencies = state;
        self
    }

    pub(crate) fn live_loan_dependencies(
        &self,
    ) -> impl Iterator<Item = (ResourceOccurrenceId, &crate::kernel::loans::LoanViewBinding)> {
        // A filtered observation shares the current loan state, which may
        // also contain excluded occurrences. Query the smaller side of the
        // intersection; never walk all excluded loans for a small frame.
        let by_entries = self.storage.facts.len() < self.loan_dependencies.map.len();
        let mut selected = Vec::new();
        if by_entries {
            for (_, occurrence) in self.storage.occurrence_by_entry.iter() {
                crate::instrumentation::record_deterministic_work(1);
                if let Some(binding) = self.loan_dependencies.map.get(occurrence) {
                    selected.push((*occurrence, binding));
                }
            }
            // Preserve the original occurrence ordering for every caller.
            selected.sort_unstable_by_key(|(occurrence, _)| *occurrence);
        }
        self.loan_dependencies
            .map
            .iter()
            .take(if by_entries {
                0
            } else {
                self.loan_dependencies.map.len()
            })
            .filter_map(|(occurrence, binding)| {
                crate::instrumentation::record_deterministic_work(1);
                self.storage
                    .entry_by_occurrence
                    .contains_key(occurrence)
                    .then_some((*occurrence, binding))
            })
            .chain(selected)
    }
}

/// The memory-dependent part of a supported observation.  The resource
/// occurrence identifies the owner; this record pins the memory snapshot and
/// the exact footprint(s) read while the projection was made.  Unknown
/// dependencies are deliberately conservative and are invalidated by any
/// opaque memory transition.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) enum ResourceMemoryFootprint {
    None,
    Exact(std::sync::Arc<[CMemoryRange]>),
    Unknown,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ResourceSupportMetadata {
    pub(super) memory_snapshot: CMemorySnapshotIdentity,
    pub(super) footprint: ResourceMemoryFootprint,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct ResourceMemoryIntervalNode {
    pub(super) block: PointerBlock,
    pub(super) level: u8,
    pub(super) start: u32,
}

#[derive(Clone)]
pub(super) struct ObservableResourceProjection {
    classification: u64,
    /// A weak checkpoint detects any producer that replaces storage without
    /// advancing the view, without retaining the unfiltered context.
    source: std::sync::Weak<ResourceContextStorage>,
    storage: std::sync::Arc<ResourceContextStorage>,
}

#[derive(Clone, Default)]
pub(super) struct ResourceContextStorage {
    /// Stable ordinals preserve insertion order without shifting surviving
    /// entries after a removal.
    pub(super) facts: PersistentMap<ResourceEntryId, CResourceFact>,
    pub(super) next_entry_id: ResourceEntryId,
    pub(super) occurrence_by_entry: PersistentMap<ResourceEntryId, ResourceOccurrenceId>,
    pub(super) entry_by_occurrence: PersistentMap<ResourceOccurrenceId, ResourceEntryId>,
    pub(super) index: ResourceContextIndex,
    /// Derived view entries name the exact owned resource that supports them.
    /// Ordinary entries are explicit and therefore absent from this map.
    pub(super) supported_by: PersistentMap<ResourceEntryId, CResourceFact>,
    /// Exact owned-entry identity for each supported projection. The fact
    /// cache above is useful for diagnostics, but this occurrence index is
    /// authoritative when one of several equal owned entries is consumed.
    pub(super) support_occurrence_by_projection:
        PersistentMap<ResourceEntryId, ResourceOccurrenceId>,
    /// Value-keyed reverse support index retained for compatibility with
    /// normalization and diagnostics. Removal and evidence use the
    /// occurrence-keyed index below, so equal authorities cannot alias.
    pub(super) projections_by_support: PersistentMap<CResourceFact, ResourceEntryIds>,
    /// Occurrence-keyed reverse index; unlike the fact-keyed compatibility
    /// index above, this cannot conflate equal support occurrences.
    pub(super) projections_by_support_occurrence:
        PersistentMap<ResourceOccurrenceId, ResourceEntryIds>,
    /// Memory-dependent projections, indexed by their exact entry.  The
    /// companion block index lets a store/call/loop invalidation visit only
    /// projections whose recorded footprint can be affected.
    pub(super) support_metadata_by_projection:
        PersistentMap<ResourceOccurrenceId, ResourceSupportMetadata>,
    pub(super) projections_by_memory_block: PersistentMap<PointerBlock, ResourceOccurrenceIds>,
    /// Dyadic interval indexes provide logarithmic affected-support lookup.
    pub(super) projections_by_memory_interval:
        PersistentMap<ResourceMemoryIntervalNode, ResourceOccurrenceIds>,
    pub(super) projections_by_memory_interval_subtree:
        PersistentMap<ResourceMemoryIntervalNode, ResourceOccurrenceIds>,
    pub(super) symbolic_memory_support: ResourceOccurrenceIds,
    pub(super) unknown_memory_support: ResourceOccurrenceIds,
    /// Certified, snapshot-stable owned expansions for folded resource
    /// generations. Reusing these avoids re-lowering the same body into
    /// fresh symbolic load identities at each later transition.
    pub(super) expansions_by_support_occurrence:
        PersistentMap<ResourceOccurrenceId, std::sync::Arc<Vec<CResourceFact>>>,
    /// Canonical cache buckets keyed by support fact and rank among equal
    /// owned authorities. Independently built equivalent snapshots can
    /// compare their support graph without exposing opaque occurrence
    /// allocation order, while invalidation remains occurrence-keyed above.
    /// Nesting by fact lets rekeying touch only the affected bucket.
    pub(super) expansions_by_support_entry:
        PersistentMap<CResourceFact, PersistentMap<usize, std::sync::Arc<Vec<CResourceFact>>>>,
    /// Persistent mutation ancestry used by checked Proof joins. The origin
    /// distinguishes unrelated snapshots; the history names only exact facts
    /// whose multiplicity or representation changed.
    pub(super) origin: std::sync::Arc<()>,
    pub(super) history: Option<std::sync::Arc<ResourceContextChange>>,
    /// A scratch observable projection's unfiltered input and addressability
    /// registry. Used only to compare admissions; the projection's live exact
    /// index still decides which changed facts it actually supplies.
    pub(super) observable_projection_source:
        Option<(std::sync::Arc<()>, std::sync::Arc<ResourceContextStorage>)>,
    /// Legacy callers that explicitly enumerate every fact pay the
    /// output-sized materialization once per immutable snapshot.
    pub(super) materialized: std::sync::OnceLock<Vec<CResourceFact>>,
}

#[derive(Clone)]
pub(crate) enum InstanceConsumption {
    Unfold,
    FoldChild {
        parent: Variable,
        slot: std::sync::Arc<str>,
    },
}

#[derive(Clone)]
pub(super) struct ResourceContextChange {
    pub(super) depth: usize,
    /// Exact occurrence delta for derived indexes; metadata changes use None.
    pub(super) entry_delta: Option<(ResourceEntryId, bool)>,
    pub(super) fact: CResourceFact,
    pub(super) parent: Option<std::sync::Arc<ResourceContextChange>>,
}

#[derive(Clone, Debug, Default)]
pub(super) struct ResourceContextIndex {
    owned_count: usize,
    owned_composite_count: usize,
    pub(super) instances: PersistentMap<Variable, ResourceEntryIds>,
    /// Only duplicated or malformed mutex authority atoms need a validity check.
    pub(super) suspect_mutex_authorities: PersistentMap<CResource, ()>,
    pub(super) invalid_mutex_authority_access: PersistentMap<CResource, usize>,
    /// Instance identities with an entry whose access is not one owned unit.
    /// With `instances`, these select the identities that can fail a
    /// validity check without visiting every instance.
    pub(super) invalid_instance_access: PersistentMap<Variable, usize>,
    /// The identities held more than once or held with invalid access: the
    /// only ones whose entries can fail `exclusive_validity_error`.
    pub(super) suspect_instances: PersistentMap<Variable, ()>,
    /// Owned instances keyed by the resource family and arity they name. A
    /// loop binder selects its instance by family and arguments, so that
    /// selection costs the instances of one family rather than the whole
    /// resource context.
    pub(super) instance_shapes: PersistentMap<(String, usize), ResourceEntryIds>,
    /// Owned instances keyed by each C pointer argument they name. A store
    /// asks which held instances a cached cell's base spellings name, so the
    /// question costs the instances whose arguments spell that base, never
    /// the other instances of the context
    /// (`functions::store_opened_instance_composition`).
    pub(super) owned_instances_by_pointer_argument: PersistentMap<Pointer, ResourceEntryIds>,
    pub(super) exact: PersistentMap<CResourceFact, ResourceEntryIds>,
    pub(super) by_resource: PersistentMap<CResource, ResourceEntryIds>,
    /// Constant owned units of quantity-bearing families. A quantity query
    /// reads one exact key rather than enumerating separately retained units.
    /// u128 covers every u64 entry ID times a positive signed-32 quantity.
    pub(super) numeric_owned_units: PersistentMap<CResource, (u128, usize)>,
    pub(super) mutex_authorities: PersistentMap<(ResourceFamily, Pointer), ResourceEntryIds>,
    /// Subscriber rights an acquire load has read through, awaiting the C
    /// branch that tests the value (`publication::resolve_observed_publications`).
    pub(super) observed_publications: PersistentMap<(), ResourceEntryIds>,
    pub(super) exact_shapes: PersistentMap<(ResourceFamily, String, usize), ResourceEntryIds>,
    /// Tokens and composites keyed by shape and by the root of their first
    /// argument when it is a pointer (`None` otherwise). Every pointer
    /// parameter shares one block, so a lookup by shape alone would compare
    /// a parameter's fact with every other parameter's.
    pub(super) exact_shapes_by_root: PersistentMap<ShapeRootKey, ResourceEntryIds>,
    /// Exact producer read identities for loaded first arguments. Checked frame
    /// canonicalization can recover these even when raw address encodings differ.
    pub(super) exact_shapes_by_pointer_read:
        PersistentMap<(ResourceFamily, String, usize, PointerLoadId), ResourceEntryIds>,
    /// Publication keys are retained for exact withdrawal even when a later
    /// producer edge changes the read's canonical frame endpoint.
    pub(super) pointer_read_keys_by_entry: PersistentMap<ResourceEntryId, Arc<[PointerLoadId]>>,
    pub(super) memory_by_block: PersistentMap<PointerBlock, ResourceEntryIds>,
    /// Iterated guarded-ownership facts keyed by both blocks their
    /// denotation depends on: the element base and the guard cells. A store,
    /// havoc, or free visits only the facts filed under its own block.
    pub(super) iterated_by_block: PersistentMap<PointerBlock, ResourceEntryIds>,
    /// Memory facts keyed by their exact base spelling. Direct pointer
    /// equalities can then find only the facts whose bases they identify,
    /// without scanning every resource in an aliased block.
    pub(super) memory_by_base: PersistentMap<Pointer, ResourceEntryIds>,
    /// Raw address anchors maintained during resource publication, for queries
    /// before a proof boundary has paired the input with an equality graph.
    /// Structural candidates maintained at resource publication, independent
    /// of proof-graph registration. Keys never establish access authority.
    structural_memory: memory_equality_index::structural::StructuralMemory,
    /// Raw persistent roots for pairing with an equality graph, maintained
    /// alongside the spelling index so pairing never scans the resource store.
    memory_addresses: memory_equality_index::MemoryAddresses,
    memory_objects: memory_equality_index::symbolic::ObjectSuppliers,
    pub(super) owned_memory_by_block: PersistentMap<PointerBlock, ResourceEntryIds>,
    /// Automatic memory owners, indexed independently of external and global
    /// holdings. Addressability is checked when projecting observable facts.
    pub(super) owned_automatic_memory_by_block: PersistentMap<PointerBlock, ResourceEntryIds>,
    /// The blocks holding two or more owned memory ranges. Only those can
    /// contribute same-block separation candidates, so projecting a
    /// composition's pairs visits these blocks and not one per allocation.
    pub(super) shared_owned_memory_blocks: PersistentMap<PointerBlock, ()>,
    /// Owned and viewed ranges with constant endpoints, keyed by base, mode,
    /// and the **signed** values of those endpoints. The key's order is what
    /// the partition check's predecessor and successor probes stand in for a
    /// pairwise scan with, so it is an ordering question wearing a key's
    /// clothes: read as `u32`, a range starting below its base sorted past
    /// every range there is and its overlapping neighbour was never probed.
    pub(super) concrete_memory: PersistentMap<(Pointer, bool, i64, i64), ResourceEntryIds>,
    pub(super) concrete_memory_by_base: PersistentMap<(Pointer, bool), usize>,
    /// Owned memory ranges keyed by their base's root: the block and the
    /// first symbolic atom of the base offset, in canonical form (absent for
    /// a wholly constant offset). Two owned ranges whose bases share no
    /// root, no recorded-equality class of a root, and no exact alias have
    /// no fact the overlap decision could relate them by, so validity
    /// compares a range only with the ranges these keys select
    /// (`owned_validity_candidates`).
    pub(super) owned_memory_by_root: PersistentMap<MemoryBaseRoot, ResourceEntryIds>,
    /// Owned memory ranges with a first element, keyed by that element's
    /// offset (the range's anchor). Two distinct owned members of one block
    /// have different anchors, which a pointer comparison asks by key
    /// rather than through every pair of members.
    pub(super) owned_memory_by_anchor: PersistentMap<PointerOffsetTerm, ResourceEntryIds>,
}

/// A condition fact's kind and canonical sides; see
/// `PureFactContext::condition_facts_by_sides`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum ConditionMatchKey {
    /// A 32-bit equality, sides in ascending order.
    Equal(Bitvector32Term, Bitvector32Term),
    /// An offset equality, sides in ascending order.
    OffsetEqual(PointerOffsetTerm, PointerOffsetTerm),
    /// A signed order: strict, then its lower and its upper side.
    Order(bool, Bitvector32Term, Bitvector32Term),
    /// Signed addition overflow, with commutative operands ordered.
    OverflowAdd(Bitvector32Term, Bitvector32Term),
}

impl ConditionMatchKey {
    /// The family of kinds a fact under this key can match: equalities,
    /// offset equalities, or signed orders.
    pub(super) fn family(&self) -> u8 {
        match self {
            Self::Equal(_, _) => 0,
            Self::OffsetEqual(_, _) => 1,
            Self::Order(_, _, _) => 2,
            Self::OverflowAdd(_, _) => 3,
        }
    }
}

/// The block and first symbolic atom (canonical) of a memory base; see
/// `ResourceContextIndex::owned_memory_by_root`.
pub(super) type MemoryBaseRoot = (PointerBlock, Option<PointerOffsetTerm>);

/// A token or composite's shape and first-pointer root; see
/// `ResourceContextIndex::exact_shapes_by_root`.
pub(super) type ShapeRootKey = (ResourceFamily, String, usize, Option<MemoryBaseRoot>);

impl std::fmt::Debug for ResourceContext {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ResourceContext")
            .field("facts", &self.facts())
            .finish()
    }
}

impl PartialEq for ResourceContext {
    fn eq(&self, other: &Self) -> bool {
        if std::sync::Arc::ptr_eq(&self.storage, &other.storage)
            && std::sync::Arc::ptr_eq(&self.loan_dependencies, &other.loan_dependencies)
        {
            return true;
        }
        self.facts() == other.facts()
            && self.storage.supported_by == other.storage.supported_by
            && compare_support_graph(self, other) == std::cmp::Ordering::Equal
            && self.storage.expansions_by_support_entry == other.storage.expansions_by_support_entry
            && compare_loan_dependencies(self, other) == std::cmp::Ordering::Equal
    }
}

impl Eq for ResourceContext {}

impl std::hash::Hash for ResourceContext {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.facts().hash(state);
        for entry in self.storage.supported_by.iter() {
            entry.hash(state);
        }
        for (projection, occurrence) in self.storage.support_occurrence_by_projection.iter() {
            projection.hash(state);
            self.storage.entry_by_occurrence.get(occurrence).hash(state);
            self.storage
                .support_metadata_by_projection
                .get(occurrence)
                .map(|metadata| &metadata.footprint)
                .hash(state);
        }
        for (fact, bucket) in self.storage.expansions_by_support_entry.iter() {
            fact.hash(state);
            for entry in bucket.iter() {
                entry.hash(state);
            }
        }
        // Hash the same structure-derived keys `compare_loan_dependencies`
        // orders by, so two contexts that compare equal never hash apart.
        for dependency in stable_loan_dependencies(self) {
            dependency.hash(state);
        }
    }
}

impl Ord for ResourceContext {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.facts()
            .cmp(other.facts())
            .then_with(|| {
                self.storage
                    .supported_by
                    .iter()
                    .cmp(other.storage.supported_by.iter())
            })
            .then_with(|| compare_support_graph(self, other))
            .then_with(|| compare_cached_expansions(self, other))
            .then_with(|| compare_loan_dependencies(self, other))
    }
}

fn compare_cached_expansions(
    left: &ResourceContext,
    right: &ResourceContext,
) -> std::cmp::Ordering {
    let mut left_facts = left.storage.expansions_by_support_entry.iter();
    let mut right_facts = right.storage.expansions_by_support_entry.iter();
    loop {
        match (left_facts.next(), right_facts.next()) {
            (None, None) => return std::cmp::Ordering::Equal,
            (None, Some(_)) => return std::cmp::Ordering::Less,
            (Some(_), None) => return std::cmp::Ordering::Greater,
            (Some((left_fact, left_bucket)), Some((right_fact, right_bucket))) => {
                let ordering = left_fact
                    .cmp(right_fact)
                    .then_with(|| left_bucket.iter().cmp(right_bucket.iter()));
                if ordering != std::cmp::Ordering::Equal {
                    return ordering;
                }
            }
        }
    }
}

/// One live loan dependency, reduced to keys that do not name a process-local
/// counter.
///
/// `ResourceOccurrenceId`, `LoanId`, `LoanScopeId`, and `LoanShareId` are all
/// fresh arena/ordinal pairs. Comparing them directly makes two structurally
/// identical contexts unequal whenever their bindings came from different
/// ledgers or were allocated in a different order, which silently costs loop
/// fixpoints, interning, and cross-run artifact reuse. The occurrence and the
/// dependency's support become the stable entry ordinals `compare_support_graph`
/// already uses; the loan, scope, and share become the position of their first
/// appearance in that stable order, which preserves exactly which dependencies
/// share a loan, scope, or share without naming any of them.
///
/// This changes only how dependencies compare. Their meaning, and every
/// authority check that reads `loan_dependency`, still uses the exact
/// identities.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
struct StableLoanDependency<'a> {
    entry: ResourceEntryId,
    viewed: &'a CResourceFact,
    support: StableLoanSupport,
    loan: usize,
    scope: usize,
    share: usize,
    hold: Option<usize>,
}

/// Where a dependency's supporting occurrence lives, without naming its arena.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum StableLoanSupport {
    /// The support is an entry of this context; its stable ordinal names it.
    Entry(ResourceEntryId),
    /// The support is not an entry here, so only the position of its first
    /// appearance among the dependencies is available.
    Position(usize),
}

/// The position at which `key` was first seen, assigning the next one if it is
/// new. Callers must visit their keys in a stable order.
fn first_appearance<K: Ord>(seen: &mut std::collections::BTreeMap<K, usize>, key: K) -> usize {
    let next = seen.len();
    *seen.entry(key).or_insert(next)
}

/// The context's live loan dependencies in a canonical, structure-derived
/// order. Ordering by the stable entry ordinal is a total order because
/// `entry_by_occurrence` maps distinct occurrences to distinct entries.
fn stable_loan_dependencies(context: &ResourceContext) -> Vec<StableLoanDependency<'_>> {
    let mut ordered = context
        .live_loan_dependencies()
        .filter_map(|(occurrence, binding)| {
            context
                .storage
                .entry_by_occurrence
                .get(&occurrence)
                .map(|entry| (*entry, binding))
        })
        .collect::<Vec<_>>();
    ordered.sort_unstable_by_key(|(entry, _)| *entry);
    let mut loans = std::collections::BTreeMap::new();
    let mut scopes = std::collections::BTreeMap::new();
    let mut shares = std::collections::BTreeMap::new();
    let mut supports = std::collections::BTreeMap::new();
    let mut holds = std::collections::BTreeMap::new();
    ordered
        .into_iter()
        .map(|(entry, binding)| {
            let loan = first_appearance(&mut loans, binding.loan);
            let scope = first_appearance(&mut scopes, binding.scope);
            let share = first_appearance(&mut shares, binding.share);
            let hold = binding.hold.map(|hold| first_appearance(&mut holds, hold));
            let support = match context.storage.entry_by_occurrence.get(&binding.support) {
                Some(entry) => StableLoanSupport::Entry(*entry),
                None => {
                    StableLoanSupport::Position(first_appearance(&mut supports, binding.support))
                }
            };
            StableLoanDependency {
                entry,
                viewed: &binding.viewed,
                support,
                loan,
                scope,
                share,
                hold,
            }
        })
        .collect()
}

fn compare_loan_dependencies(
    left: &ResourceContext,
    right: &ResourceContext,
) -> std::cmp::Ordering {
    stable_loan_dependencies(left).cmp(&stable_loan_dependencies(right))
}

impl PartialOrd for ResourceContext {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Compare only the support graph, using each snapshot's stable entry
/// ordinals instead of the process-local opaque occurrence allocation. This
/// avoids materializing or sorting the ambient resource population.
fn compare_support_graph(left: &ResourceContext, right: &ResourceContext) -> std::cmp::Ordering {
    let mut left_entries = left.storage.support_occurrence_by_projection.iter();
    let mut right_entries = right.storage.support_occurrence_by_projection.iter();
    loop {
        match (left_entries.next(), right_entries.next()) {
            (None, None) => return std::cmp::Ordering::Equal,
            (None, Some(_)) => return std::cmp::Ordering::Less,
            (Some(_), None) => return std::cmp::Ordering::Greater,
            (
                Some((left_projection, left_occurrence)),
                Some((right_projection, right_occurrence)),
            ) => {
                let ordering = left_projection
                    .cmp(right_projection)
                    .then_with(|| {
                        left.storage
                            .entry_by_occurrence
                            .get(left_occurrence)
                            .cmp(&right.storage.entry_by_occurrence.get(right_occurrence))
                    })
                    .then_with(|| {
                        left.storage
                            .support_metadata_by_projection
                            .get(left_occurrence)
                            .map(|metadata| &metadata.footprint)
                            .cmp(
                                &right
                                    .storage
                                    .support_metadata_by_projection
                                    .get(right_occurrence)
                                    .map(|metadata| &metadata.footprint),
                            )
                    });
                if ordering != std::cmp::Ordering::Equal {
                    return ordering;
                }
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CResourceFact {
    Own(CResource, Box<Bitvector32Term>),
    View(CResource),
}

/// Immutable logical indices shared by resource snapshots and population keys.
/// Cloning a resource must not clone a recursive model stored in its indices.
pub type ResourceArguments = std::sync::Arc<[AlgebraicValue]>;

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CResource {
    Memory(CMemoryRange),
    /// Exclusive control of a population described by a checked resource type.
    PopulationAuthority(super::ResourceDescription),
    Composite {
        name: String,
        arguments: ResourceArguments,
    },
    Token {
        name: String,
        arguments: ResourceArguments,
    },
    Instance(ResourceInstance),
    /// Opaque exclusive authority for one acquisition of a modeled mutex.
    MutexGuard(MutexIdentity),
    /// Exclusive lifecycle authority for one initialized mutex.
    MutexLive(MutexIdentity),
    /// Owned permission to use one checked loan share of an initialized mutex.
    MutexUse(MutexUseIdentity),
    /// Iterated guarded ownership: one fact for every element of a bounded
    /// index range whose guard cell holds (`iterated.rs`).
    Iterated(Arc<CIteratedMemory>),
    /// One half of a one-shot release/acquire publication channel.
    Publication(PublicationRight),
}

/// Which half of a one-shot publication channel a right is.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum PublicationSide {
    /// May release-store once, surrendering one owned payload.
    Publisher,
    /// Receives the payload from the acquire load that observes it.
    Subscriber,
}

impl PublicationSide {
    pub(crate) fn for_keyword(keyword: &str) -> Option<Self> {
        match keyword {
            "publisher" => Some(Self::Publisher),
            "subscriber" => Some(Self::Subscriber),
            _ => None,
        }
    }
    pub(crate) const fn keyword(self) -> &'static str {
        match self {
            Self::Publisher => "publisher",
            Self::Subscriber => "subscriber",
        }
    }
}

/// Owned authority over one half of the one-shot publication channel an
/// `atomic_init` created at `flag`. Initialization mints exactly one right of
/// each side and consumes the flag's storage for good, so the address names
/// one channel and its payload type; nothing else mints a right.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct PublicationRight {
    pub(in crate::kernel) side: PublicationSide,
    pub(in crate::kernel) flag: Pointer,
    pub(in crate::kernel) payload: super::ResourceDescription,
    /// A subscriber right an acquire load has read `observed` through, until
    /// a C branch decides whether that value is zero.
    pub(in crate::kernel) observed: Option<CValue>,
}

impl PublicationRight {
    pub(crate) fn new(
        side: PublicationSide,
        flag: Pointer,
        payload: super::ResourceDescription,
    ) -> Self {
        Self {
            side,
            flag,
            payload,
            observed: None,
        }
    }
    pub(crate) fn observed(&self) -> Option<&CValue> {
        self.observed.as_ref()
    }
    pub(crate) fn side(&self) -> PublicationSide {
        self.side
    }
    pub(crate) fn flag(&self) -> &Pointer {
        &self.flag
    }
    pub(crate) fn payload(&self) -> &super::ResourceDescription {
        &self.payload
    }
}

/// Opaque identity for one mutex initialization or acquisition. The resource
/// variant distinguishes these namespaces. Copying syntax never duplicates ownership.
/// Epochs are generative for concrete transitions and rooted direct mutex inputs.
/// Unbound descriptions are valid only while protocol transitions are prohibited.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct MutexIdentity {
    /// `None` is an unbound description at abstract contract entry.
    pub(in crate::kernel) epoch: Option<u64>,
    /// Bound addresses are immutable diagnostic provenance; only an
    /// unbound description's address participates in substitution.
    pub(in crate::kernel) mutex: Pointer,
}

/// Opaque identity of one use-share resource occurrence. The pointer is
/// diagnostic provenance, not a constructor for loan authority. Substitution
/// must preserve this identity just as it preserves a concrete acquisition.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct MutexUseIdentity {
    pub(in crate::kernel) protected: Option<super::ResourceDescription>,
    pub(in crate::kernel) binding: Option<super::loans::MutexUseBinding>,
    pub(in crate::kernel) initialization: Option<u64>,
    pub(in crate::kernel) mutex: Pointer,
}

impl MutexUseIdentity {
    pub(crate) fn protected_type(&self) -> Option<&super::ResourceDescription> {
        self.protected.as_ref()
    }
    pub(crate) fn mutex(&self) -> &Pointer {
        &self.mutex
    }
}

impl MutexIdentity {
    pub(crate) fn mutex(&self) -> &Pointer {
        &self.mutex
    }
}

impl CResource {
    /// One iterated guarded-ownership fact. The fact is shared, so cloning a
    /// resource context never copies its terms.
    pub(crate) fn iterated(iterated: CIteratedMemory) -> Self {
        Self::Iterated(Arc::new(iterated))
    }
}

/// A proof-only, exclusive resource instance. Identity is independent of its
/// field state; equal fields do not identify distinct instances. This is an
/// opaque ownership atom: its arguments and fields grant no memory authority.
/// Constructing an atom is not a proof that it is owned or that a resource
/// definition's body holds.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ResourceInstance {
    pub(super) identity: Variable,
    pub(super) name: String,
    pub(super) arguments: ResourceArguments,
    pub(super) schema: ResourceFieldSchema,
    pub(super) fields: ResourceArguments,
    pub(super) resource_arguments: Arc<[super::ResourceReference]>,
}

impl ResourceInstance {
    pub fn new(
        identity: Variable,
        name: String,
        arguments: ResourceArguments,
        schema: ResourceFieldSchema,
        fields: ResourceArguments,
    ) -> Option<Self> {
        Self::new_with_resource_arguments(identity, name, arguments, schema, fields, Vec::new())
    }

    /// Construct an exclusive atom with proof-only arguments. As for `new`, a
    /// countable schema is rejected; references do not change countability.
    pub fn new_with_resource_arguments(
        identity: Variable,
        name: String,
        arguments: ResourceArguments,
        schema: ResourceFieldSchema,
        fields: ResourceArguments,
        resource_arguments: Vec<super::ResourceReference>,
    ) -> Option<Self> {
        if schema.is_fieldless() || schema.fields().len() != fields.len() {
            return None;
        }
        for ((_, ty), value) in schema.fields().iter().zip(fields.iter()) {
            let valid = match (ty, value) {
                (ResourceFieldType::Integer, AlgebraicValue::Integer(_)) => true,
                (ResourceFieldType::C(ty), AlgebraicValue::C(value)) => *ty == value.c_type(),
                (ResourceFieldType::Algebraic(ty), AlgebraicValue::Algebraic(value)) => {
                    *ty == value.algebraic_type && value.is_well_formed()
                }
                _ => false,
            };
            if !valid {
                return None;
            }
        }
        Some(Self {
            identity,
            name,
            arguments,
            schema,
            fields,
            resource_arguments: resource_arguments.into(),
        })
    }

    pub fn identity(&self) -> Variable {
        self.identity
    }
    /// Attach proof-only references. This constructs an opaque atom, not
    /// evidence that the resource or any referenced resource is owned.
    pub fn with_resource_arguments(mut self, arguments: Vec<super::ResourceReference>) -> Self {
        self.resource_arguments = arguments.into();
        self
    }

    pub fn resource_arguments(&self) -> &[super::ResourceReference] {
        &self.resource_arguments
    }
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn arguments(&self) -> &[AlgebraicValue] {
        &self.arguments
    }
    pub fn fields(&self) -> &[AlgebraicValue] {
        &self.fields
    }
    pub fn schema(&self) -> &ResourceFieldSchema {
        &self.schema
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResourceContextValidityError {
    InvalidExclusiveAccess(CResourceFact),
    DuplicateOwnedResourceFact(CResourceFact),
    OverlappingOwnedMemoryResources {
        left: CMemoryRange,
        right: CMemoryRange,
    },
}

/// The result of consuming one available resource fact to satisfy a required
/// fact. Viewed facts are normally preserved; owned facts may be removed or
/// replaced by residual ownership.
pub(super) enum ResourceFactConsumption {
    Preserve,
    Replace(Vec<CResourceFact>),
}

/// The algebraic behavior supplied by one resource family.
///
/// `ResourceContext` provides state-level composition. Families define when
/// same-family facts are valid together, how one fact entails or satisfies
/// another, how consumed ownership leaves residues, how redundant facts are
/// normalized, and which facts are observable from a valid composition.
pub(super) trait ResourceFamilyAlgebra {
    fn family(&self) -> ResourceFamily;

    /// Checks the access/quantity envelope before a specification reaches a
    /// family operation.  The common normalized carrier delegates this check
    /// to the selected family rather than allowing its representational shape
    /// to broaden family semantics.
    fn validate_spec(&self, spec: &CResourceSpec) -> Result<(), CResourceSpecError> {
        if spec.term.family() != self.family() {
            return Err(CResourceSpecError::InvalidNestedTerm(
                "resource term and family algebra disagree".into(),
            ));
        }
        if let CResourceTerm::PopulationAuthority { protected, .. } = &spec.term
            && (!matches!(
                protected.resource.term(),
                CResourceTerm::Composite { .. } | CResourceTerm::Token { .. }
            ) || (matches!(protected.resource.term(), CResourceTerm::Token { .. })
                && !protected.schema.fields().is_empty())
                || protected.resource.access() != CResourceAccessMode::Own
                || protected.resource.quantity() != &CResourceQuantity::One)
        {
            return Err(CResourceSpecError::InvalidNestedTerm(
                "population authority requires an owned unit composite or token resource type"
                    .into(),
            ));
        }
        match self.family() {
            ResourceFamily::PopulationAuthority
            | ResourceFamily::MutexGuard
            | ResourceFamily::MutexLive
            | ResourceFamily::MutexUse
            | ResourceFamily::Publication => {
                if spec.access != CResourceAccessMode::Own {
                    return Err(CResourceSpecError::InvalidAccess {
                        family: self.family(),
                        access: spec.access,
                    });
                }
                if spec.quantity != CResourceQuantity::One {
                    return Err(CResourceSpecError::InvalidQuantity {
                        family: self.family(),
                        reason: "authority has unit quantity".into(),
                    });
                }
            }
            ResourceFamily::Memory => {
                if !matches!(spec.quantity, CResourceQuantity::One) {
                    return Err(CResourceSpecError::InvalidQuantity {
                        family: ResourceFamily::Memory,
                        reason: "memory ranges have unit quantity".into(),
                    });
                }
            }
            ResourceFamily::Instance => {
                if spec.access != CResourceAccessMode::Own {
                    return Err(CResourceSpecError::InvalidAccess {
                        family: ResourceFamily::Instance,
                        access: spec.access,
                    });
                }
                if !matches!(spec.quantity, CResourceQuantity::One) {
                    return Err(CResourceSpecError::InvalidQuantity {
                        family: ResourceFamily::Instance,
                        reason: "field-bearing instances have unit quantity".into(),
                    });
                }
                if !matches!(spec.term, CResourceTerm::Instance { ref resource, .. } if matches!(resource.as_ref(), CResourceTerm::Composite { .. }))
                {
                    return Err(CResourceSpecError::InvalidNestedTerm(
                        "field-bearing instances require a declared composite term".into(),
                    ));
                }
            }
            ResourceFamily::Iterated => {
                if !matches!(spec.quantity, CResourceQuantity::One) {
                    return Err(CResourceSpecError::InvalidQuantity {
                        family: ResourceFamily::Iterated,
                        reason: "iterated ownership has unit quantity".into(),
                    });
                }
            }
            ResourceFamily::Composite | ResourceFamily::Token => {
                if matches!(spec.quantity, CResourceQuantity::Count(_))
                    && spec.access != CResourceAccessMode::Own
                {
                    return Err(CResourceSpecError::InvalidAccess {
                        family: self.family(),
                        access: spec.access,
                    });
                }
            }
        }
        Ok(())
    }

    fn pair_validity_error(
        &self,
        left: &CResourceFact,
        right: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceContextValidityError>;

    fn entails(
        &self,
        available: &CResourceFact,
        required: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> bool;

    fn consume(
        &self,
        available: &CResourceFact,
        required: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceFactConsumption>;

    /// Returns one fact equivalent to composing this pair when the pair can be
    /// losslessly normalized. `None` leaves both facts in the resource state.
    fn normalize_pair(
        &self,
        left: &CResourceFact,
        right: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<CResourceFact>;

    fn core(&self, fact: &CResourceFact) -> Option<CResourceFact>;
}

struct MemoryResourceAlgebra;

struct TokenResourceAlgebra;
/// The kernel algebra for a folded composite fact is exact-match ownership and
/// viewing. Source-declared body equivalences are applied as fold, unfold, and
/// observation laws by the Click proof layer.
struct CompositeResourceAlgebra;
struct InstanceResourceAlgebra;
struct MutexUseResourceAlgebra;
static MUTEX_USE_RESOURCE_ALGEBRA: MutexUseResourceAlgebra = MutexUseResourceAlgebra;

struct MutexLiveResourceAlgebra;
static MUTEX_LIVE_RESOURCE_ALGEBRA: MutexLiveResourceAlgebra = MutexLiveResourceAlgebra;

struct MutexGuardResourceAlgebra;
static MUTEX_GUARD_RESOURCE_ALGEBRA: MutexGuardResourceAlgebra = MutexGuardResourceAlgebra;
struct PublicationResourceAlgebra;
static PUBLICATION_RESOURCE_ALGEBRA: PublicationResourceAlgebra = PublicationResourceAlgebra;

static MEMORY_RESOURCE_ALGEBRA: MemoryResourceAlgebra = MemoryResourceAlgebra;
struct PopulationAuthorityResourceAlgebra;
static POPULATION_AUTHORITY_RESOURCE_ALGEBRA: PopulationAuthorityResourceAlgebra =
    PopulationAuthorityResourceAlgebra;
static TOKEN_RESOURCE_ALGEBRA: TokenResourceAlgebra = TokenResourceAlgebra;
static COMPOSITE_RESOURCE_ALGEBRA: CompositeResourceAlgebra = CompositeResourceAlgebra;
static INSTANCE_RESOURCE_ALGEBRA: InstanceResourceAlgebra = InstanceResourceAlgebra;
/// Iterated guarded ownership is exact-match: one fact is equal to another
/// when every term it carries is proved equal. Taking and giving elements are
/// checked kernel operations (`crate::kernel::iterated`), never algebraic
/// splitting, so the algebra itself neither splits nor joins.
struct IteratedResourceAlgebra;
static ITERATED_RESOURCE_ALGEBRA: IteratedResourceAlgebra = IteratedResourceAlgebra;

/// Primitive resource families. Adding a variant also requires registering one
/// `ResourceFamilyAlgebra` implementation in `resource_family_algebra`.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ResourceFamily {
    Memory,
    PopulationAuthority,
    Composite,
    Token,
    Instance,
    MutexGuard,
    MutexLive,
    MutexUse,
    /// Iterated guarded ownership (`CResource::Iterated`).
    Iterated,
    /// One half of a one-shot publication channel (`CResource::Publication`).
    Publication,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CResourceAccessMode {
    Own,
    View,
}

/// The resource term carried by a normalized specification.
///
/// Access is deliberately not part of this enum.  A memory range, declared
/// resource, and field-bearing instance all share the same representation
/// above the family algebra; the family still decides which access and
/// quantity combinations are valid.  An instance's inner term is retained so
/// its declaration identity and schema remain explicit without encoding them
/// in vector position or in a memory-only variant.
/// A declared resource type without an occurrence binder or field observations.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CResourceTypeSpec {
    pub resource: Box<CResourceSpec>,
    pub schema: ResourceFieldSchema,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CResourceTerm {
    Memory(CMemorySegment),
    PopulationAuthority {
        protected: Box<CResourceTypeSpec>,
        population_arity: Option<usize>,
        snapshot: CResourceSnapshot,
    },
    MutexGuard {
        mutex: Box<CExpression>,
        snapshot: CResourceSnapshot,
    },
    MutexLive {
        mutex: Box<CExpression>,
        snapshot: CResourceSnapshot,
    },
    MutexUse {
        protected: Option<Box<CResourceTypeSpec>>,
        mutex: Box<CExpression>,
        snapshot: CResourceSnapshot,
    },
    /// `publisher(flag, P)` or `subscriber(flag, P)`.
    Publication {
        side: PublicationSide,
        payload: Box<CResourceTypeSpec>,
        flag: Box<CExpression>,
        snapshot: CResourceSnapshot,
    },
    Composite {
        name: String,
        arguments: Vec<CExpression>,
        argument_snapshots: Vec<CResourceSnapshot>,
        parameter_types: Vec<CType>,
    },
    Token {
        name: String,
        arguments: Vec<CExpression>,
        argument_snapshots: Vec<CResourceSnapshot>,
        parameter_types: Vec<CType>,
    },
    Instance {
        identity: Variable,
        /// The spelling the declaration gave this binder. The identity is the
        /// semantic key; this is the name a binder or proof-parameter map is
        /// written with, retained the same way [`CResourceChildSpec::name`]
        /// retains a child slot's spelling, so diagnostics can print the map
        /// the user has to write.
        ///
        /// The surface binding the clause carries is the single source for
        /// this spelling: lowering copies it here, and the parser copies the
        /// same name into its own per-callee binder index for the call maps it
        /// checks before lowering runs.
        binder: String,
        schema: ResourceFieldSchema,
        resource: Box<CResourceTerm>,
    },
    /// An iterated guarded-ownership clause of a resource body. It evaluates
    /// to one `CResource::Iterated` fact; see `primitives/iterated.rs`.
    Iterated(Box<CIteratedSpec>),
}

/// The unevaluated form of an iterated guarded-ownership clause: C
/// expressions over the body's parameters, with the element and guard shape
/// fixed by validation.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CIteratedSpec {
    pub(crate) owner: String,
    /// `element.base[element.start..element.end]` is the index range
    /// `lo..hi` read against the element base; the element width is the
    /// base's.
    pub(crate) element: CMemorySegment,
    pub(crate) stride: u32,
    pub(crate) start_offset: i32,
    pub(crate) end_offset: i32,
    pub(crate) guard_base: CExpression,
    pub(crate) guard_cell_type: CType,
    pub(crate) guard_cell_width: u32,
    pub(crate) holds_when_equal: bool,
    pub(crate) guard_value: CExpression,
}

/// Quantity is explicit in the normalized form.  `One` is the ordinary unit
/// quantity; `Count` is reserved for the existing counted composite/token
/// resources.  In particular, memory and exclusive instances cannot acquire a
/// quantity merely because a wrapper could represent one.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CResourceQuantity {
    One,
    Count(CExpression),
}

/// The transfer operation associated with a normalized specification.
/// Resource vectors remain grouped by their source-level section for stable
/// ordering, but the semantic operation is carried on each element.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CResourceTransferRole {
    Borrow,
    Consume,
    Produce,
}

/// Which state supplies the resource term's address, arguments, or quantity.
/// Callers may still pass an explicitly selected state to the evaluator; this
/// metadata records the selection made by lowering and prevents entry/post
/// meaning from being inferred from a vector's position.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CResourceSnapshot {
    Entry,
    Current,
    Post,
}

/// A typed native record place required by an explicit source clause.
/// Retaining this metadata grants no object validity or memory permission.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct CNativeRecordPlaceRequirement {
    pub(crate) carrier: CExpression,
    pub(crate) layout: Arc<CAggregateLayout>,
    /// An explicit typed record sequence prefix, not an exact array extent.
    /// None retains the ordinary single-record place requirement.
    pub(crate) prefix_count: Option<CExpression>,
}

/// Which language access rules may discharge a typed-place obligation.
/// This policy grants neither permission nor initialization.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CTypedAccessPolicy {
    NativeObjectOnly,
    #[default]
    CAllocatedAccessAllowed,
}

/// A source-typed scalar prefix, separate from exact array extent, byte
/// authority and initialized storage.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct CNativeSpanRequirement {
    pub(crate) carrier: CExpression,
    pub(crate) element_type: CType,
    pub(crate) count: CExpression,
    pub(crate) access_policy: CTypedAccessPolicy,
}

#[derive(Clone, Debug)]
pub struct CResourceSpec {
    /// Declared leaf observation type, separate from resource coordinate units.
    declared_storage_observation: Option<(CType, u32)>,
    native_record_places: Arc<[CNativeRecordPlaceRequirement]>,
    native_span_requirements: Arc<[CNativeSpanRequirement]>,
    /// Actual resource-reference binders, separate from C-valued arguments.
    /// Naming a binder here grants no ownership of its occurrence.
    resource_arguments: Arc<[Variable]>,
    term: CResourceTerm,
    /// A proof binder for one raw mutex authority. This does not change the
    /// resource family or turn the authority into a composite instance.
    mutex_authority_binding: Option<Arc<(Variable, String)>>,
    access: CResourceAccessMode,
    quantity: CResourceQuantity,
    quantity_snapshot: CResourceSnapshot,
    role: CResourceTransferRole,
    snapshot: CResourceSnapshot,
    /// A pre-state proposition controlling a conditional resource effect.
    /// `None` is the ordinary unconditional clause.
    guard: Option<SpecProposition>,
    /// Source-level clause identity, when lowering expanded one source
    /// clause into more than one normalized specification.  Keeping this on
    /// the spec lets kernel diagnostics retain the surface clause numbering
    /// without making the evaluator know about surface syntax.
    clause_position: Option<(usize, usize)>,
    /// Source spellings for declared-resource arguments, used only when an
    /// argument cannot be evaluated. They do not affect contract identity.
    source_arguments: Option<Arc<[String]>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CResourceSpecError {
    InvalidAccess {
        family: ResourceFamily,
        access: CResourceAccessMode,
    },
    InvalidQuantity {
        family: ResourceFamily,
        reason: String,
    },
    InvalidNestedTerm(String),
}

impl std::fmt::Display for CResourceSpecError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidAccess { family, access } => {
                write!(
                    formatter,
                    "{family:?} resources do not permit {access:?} access"
                )
            }
            Self::InvalidQuantity { family, reason } => {
                write!(
                    formatter,
                    "{family:?} resource has invalid quantity: {reason}"
                )
            }
            Self::InvalidNestedTerm(reason) => formatter.write_str(reason),
        }
    }
}

impl std::error::Error for CResourceSpecError {}

impl CResourceTerm {
    pub fn family(&self) -> ResourceFamily {
        match self {
            Self::Memory(_) => ResourceFamily::Memory,
            Self::PopulationAuthority { .. } => ResourceFamily::PopulationAuthority,
            Self::MutexGuard { .. } => ResourceFamily::MutexGuard,
            Self::MutexLive { .. } => ResourceFamily::MutexLive,
            Self::MutexUse { .. } => ResourceFamily::MutexUse,
            Self::Composite { .. } => ResourceFamily::Composite,
            Self::Token { .. } => ResourceFamily::Token,
            Self::Instance { .. } => ResourceFamily::Instance,
            Self::Iterated(_) => ResourceFamily::Iterated,
            Self::Publication { .. } => ResourceFamily::Publication,
        }
    }

    pub fn memory_segment(&self) -> Option<&CMemorySegment> {
        match self {
            Self::Memory(segment) => Some(segment),
            _ => None,
        }
    }

    pub fn instance_identity(&self) -> Option<Variable> {
        match self {
            Self::Instance { identity, .. } => Some(*identity),
            _ => None,
        }
    }

    pub fn instance_binder(&self) -> Option<&str> {
        match self {
            Self::Instance { binder, .. } => Some(binder),
            _ => None,
        }
    }

    pub fn instance_schema(&self) -> Option<&ResourceFieldSchema> {
        match self {
            Self::Instance { schema, .. } => Some(schema),
            _ => None,
        }
    }

    pub fn instance_resource(&self) -> Option<&CResourceTerm> {
        match self {
            Self::Instance { resource, .. } => Some(resource),
            _ => None,
        }
    }

    pub fn declared_name(&self) -> Option<&str> {
        match self {
            Self::Composite { name, .. } | Self::Token { name, .. } => Some(name),
            _ => None,
        }
    }

    pub fn declared_arguments(&self) -> Option<&[CExpression]> {
        match self {
            Self::Composite { arguments, .. } | Self::Token { arguments, .. } => Some(arguments),
            _ => None,
        }
    }

    pub fn declared_argument_snapshots(&self) -> Option<&[CResourceSnapshot]> {
        match self {
            Self::Composite {
                argument_snapshots, ..
            }
            | Self::Token {
                argument_snapshots, ..
            } => Some(argument_snapshots),
            _ => None,
        }
    }

    pub fn declared_parameter_types(&self) -> Option<&[CType]> {
        match self {
            Self::Composite {
                parameter_types, ..
            }
            | Self::Token {
                parameter_types, ..
            } => Some(parameter_types),
            _ => None,
        }
    }
}

impl CResourceSpec {
    pub(crate) fn with_declared_storage_observation(
        mut self,
        observation: Option<(CType, u32)>,
    ) -> Self {
        self.declared_storage_observation = observation;
        self
    }
    pub(crate) fn declared_storage_observation(&self) -> Option<(CType, u32)> {
        self.declared_storage_observation
    }
    pub(crate) fn declared_storage_type(&self) -> Option<CType> {
        self.declared_storage_observation.map(|(ty, _)| ty)
    }
    pub(crate) fn declared_storage_count(&self) -> Option<u32> {
        self.declared_storage_observation.map(|(_, count)| count)
    }
    pub(crate) fn with_native_record_places(
        mut self,
        places: Vec<CNativeRecordPlaceRequirement>,
    ) -> Self {
        self.native_record_places = places.into();
        self
    }

    pub(crate) fn native_record_places(&self) -> &[CNativeRecordPlaceRequirement] {
        &self.native_record_places
    }

    pub(crate) fn with_native_span_requirements(
        mut self,
        requirements: Vec<CNativeSpanRequirement>,
    ) -> Self {
        self.native_span_requirements = requirements.into();
        self
    }

    pub(crate) fn native_span_requirements(&self) -> &[CNativeSpanRequirement] {
        &self.native_span_requirements
    }

    pub fn new(
        term: CResourceTerm,
        access: CResourceAccessMode,
        quantity: CResourceQuantity,
        role: CResourceTransferRole,
        snapshot: CResourceSnapshot,
    ) -> Result<Self, CResourceSpecError> {
        let spec = Self {
            declared_storage_observation: None,
            native_record_places: Arc::from([]),
            native_span_requirements: Arc::from([]),
            term,
            mutex_authority_binding: None,
            resource_arguments: Arc::from([]),
            access,
            quantity,
            quantity_snapshot: CResourceSnapshot::Current,
            role,
            snapshot,
            guard: None,
            clause_position: None,
            source_arguments: None,
        };
        spec.validate()?;
        Ok(spec)
    }

    pub fn memory(
        segment: CMemorySegment,
        access: CResourceAccessMode,
        role: CResourceTransferRole,
        snapshot: CResourceSnapshot,
    ) -> Self {
        Self::new(
            CResourceTerm::Memory(segment),
            access,
            CResourceQuantity::One,
            role,
            snapshot,
        )
        .expect("unit memory terms are valid by construction")
    }

    /// Constructors for kernel callers that do not have a surrounding
    /// transfer section.  Surface lowering uses the fully annotated
    /// constructor below; these defaults describe the caller-selected
    /// current state, with the transfer role made explicit as `Consume`.
    pub fn viewed_memory(segment: CMemorySegment) -> Self {
        Self::memory(
            segment,
            CResourceAccessMode::View,
            CResourceTransferRole::Borrow,
            CResourceSnapshot::Current,
        )
    }

    pub fn owned_memory(segment: CMemorySegment) -> Self {
        Self::memory(
            segment,
            CResourceAccessMode::Own,
            CResourceTransferRole::Consume,
            CResourceSnapshot::Current,
        )
    }

    pub fn declared(
        family: ResourceFamily,
        access: CResourceAccessMode,
        name: String,
        arguments: Vec<CExpression>,
        parameter_types: Vec<CType>,
        role: CResourceTransferRole,
        snapshot: CResourceSnapshot,
    ) -> Result<Self, CResourceSpecError> {
        Self::declared_with_argument_snapshots(
            family,
            access,
            name,
            arguments,
            Vec::new(),
            parameter_types,
            role,
            snapshot,
        )
    }

    pub fn declared_with_argument_snapshots(
        family: ResourceFamily,
        access: CResourceAccessMode,
        name: String,
        arguments: Vec<CExpression>,
        mut argument_snapshots: Vec<CResourceSnapshot>,
        parameter_types: Vec<CType>,
        role: CResourceTransferRole,
        snapshot: CResourceSnapshot,
    ) -> Result<Self, CResourceSpecError> {
        if argument_snapshots.is_empty() {
            argument_snapshots = vec![CResourceSnapshot::Current; arguments.len()];
        }
        if arguments.len() != argument_snapshots.len() || arguments.len() != parameter_types.len() {
            return Err(CResourceSpecError::InvalidNestedTerm(
                "resource argument metadata has the wrong length".into(),
            ));
        }
        let term = match family {
            ResourceFamily::Composite => CResourceTerm::Composite {
                name,
                arguments,
                argument_snapshots,
                parameter_types,
            },
            ResourceFamily::Token => CResourceTerm::Token {
                name,
                arguments,
                argument_snapshots,
                parameter_types,
            },
            ResourceFamily::Publication
            | ResourceFamily::Memory
            | ResourceFamily::PopulationAuthority
            | ResourceFamily::Instance
            | ResourceFamily::Iterated
            | ResourceFamily::MutexGuard
            | ResourceFamily::MutexLive
            | ResourceFamily::MutexUse => {
                return Err(CResourceSpecError::InvalidNestedTerm(
                    "only composite and token families have declared resource terms".into(),
                ));
            }
        };
        Self::new(term, access, CResourceQuantity::One, role, snapshot)
    }

    pub fn instance(
        identity: Variable,
        binder: String,
        schema: ResourceFieldSchema,
        resource: CResourceSpec,
        role: CResourceTransferRole,
        snapshot: CResourceSnapshot,
    ) -> Result<Self, CResourceSpecError> {
        if resource.access != CResourceAccessMode::Own
            || resource.quantity != CResourceQuantity::One
            || !matches!(resource.term, CResourceTerm::Composite { .. })
        {
            return Err(CResourceSpecError::InvalidNestedTerm(
                "named resource instances require an owned unit composite term".into(),
            ));
        }
        let references = resource.resource_arguments.clone();
        Self::new(
            CResourceTerm::Instance {
                identity,
                binder,
                schema,
                resource: Box::new(resource.term),
            },
            CResourceAccessMode::Own,
            CResourceQuantity::One,
            role,
            snapshot,
        )
        .map(|spec| spec.with_resource_arguments(references.to_vec()))
    }

    pub fn quantified(
        quantity: CExpression,
        resource: CResourceSpec,
        role: CResourceTransferRole,
        snapshot: CResourceSnapshot,
    ) -> Result<Self, CResourceSpecError> {
        if !resource.resource_arguments.is_empty() {
            return Err(CResourceSpecError::InvalidNestedTerm(
                "resource arguments require an exclusive instance, not a counted clause".into(),
            ));
        }
        if resource.access != CResourceAccessMode::Own {
            return Err(CResourceSpecError::InvalidAccess {
                family: resource.family(),
                access: resource.access,
            });
        }
        if resource.quantity != CResourceQuantity::One {
            return Err(CResourceSpecError::InvalidQuantity {
                family: resource.family(),
                reason: "a counted resource must wrap a unit term".into(),
            });
        }
        if matches!(
            resource.family(),
            ResourceFamily::Memory | ResourceFamily::Instance
        ) {
            return Err(CResourceSpecError::InvalidQuantity {
                family: resource.family(),
                reason: "this resource family does not support quantities".into(),
            });
        }
        if !matches!(
            resource.term,
            CResourceTerm::Composite { .. } | CResourceTerm::Token { .. }
        ) {
            return Err(CResourceSpecError::InvalidNestedTerm(
                "quantities require an owned unit composite or token term".into(),
            ));
        }
        Self::new(
            resource.term,
            CResourceAccessMode::Own,
            CResourceQuantity::Count(quantity),
            role,
            snapshot,
        )
    }

    pub fn quantified_with_quantity_snapshot(
        quantity: CExpression,
        resource: CResourceSpec,
        role: CResourceTransferRole,
        snapshot: CResourceSnapshot,
        quantity_snapshot: CResourceSnapshot,
    ) -> Result<Self, CResourceSpecError> {
        let mut spec = Self::quantified(quantity, resource, role, snapshot)?;
        spec.quantity_snapshot = quantity_snapshot;
        Ok(spec)
    }

    pub fn term(&self) -> &CResourceTerm {
        &self.term
    }

    pub(in crate::kernel) fn with_captured_memory_segment(&self, segment: CMemorySegment) -> Self {
        debug_assert!(matches!(self.term, CResourceTerm::Memory(_)));
        let mut captured = self.clone();
        captured.term = CResourceTerm::Memory(segment);
        captured
    }

    pub fn with_mutex_authority_binding(
        mut self,
        identity: Variable,
        binder: String,
    ) -> Result<Self, CResourceSpecError> {
        if !matches!(
            self.term,
            CResourceTerm::MutexGuard { .. }
                | CResourceTerm::MutexLive { .. }
                | CResourceTerm::MutexUse { .. }
        ) || self.access != CResourceAccessMode::Own
            || self.quantity != CResourceQuantity::One
            || self.mutex_authority_binding.is_some()
        {
            return Err(CResourceSpecError::InvalidNestedTerm(
                "named mutex authority requires one owned, unbound mutex resource".into(),
            ));
        }
        self.mutex_authority_binding = Some(Arc::new((identity, binder)));
        Ok(self)
    }

    pub fn mutex_authority_binding(&self) -> Option<(Variable, &str)> {
        self.mutex_authority_binding
            .as_ref()
            .map(|entry| (entry.0, entry.1.as_str()))
    }

    pub fn without_mutex_authority_binding(&self) -> Self {
        let mut unnamed = self.clone();
        unnamed.mutex_authority_binding = None;
        unnamed
    }

    pub fn binding_name(&self) -> Option<&str> {
        self.instance_binder()
            .or_else(|| self.mutex_authority_binding().map(|(_, name)| name))
    }

    pub fn binding_identity(&self) -> Option<Variable> {
        self.instance_identity()
            .or_else(|| self.mutex_authority_binding().map(|(identity, _)| identity))
    }

    pub fn access(&self) -> CResourceAccessMode {
        self.access
    }

    pub fn quantity(&self) -> &CResourceQuantity {
        &self.quantity
    }

    pub fn quantity_snapshot(&self) -> CResourceSnapshot {
        self.quantity_snapshot
    }

    pub(crate) fn with_quantity_snapshot(mut self, snapshot: CResourceSnapshot) -> Self {
        self.quantity_snapshot = snapshot;
        self
    }

    pub fn role(&self) -> CResourceTransferRole {
        self.role
    }

    pub fn snapshot(&self) -> CResourceSnapshot {
        self.snapshot
    }

    pub fn guard(&self) -> Option<&SpecProposition> {
        self.guard.as_ref()
    }

    pub fn with_guard(mut self, guard: SpecProposition) -> Self {
        self.guard = Some(guard);
        self
    }

    /// Attach the zero-based source clause position and the total number of
    /// source resource clauses represented by this normalized specification.
    /// All leaves produced from one aggregate carry the same position.
    pub fn with_clause_position(mut self, index: usize, total: usize) -> Self {
        self.clause_position = Some((index, total));
        self
    }

    pub(crate) fn clause_position(&self) -> Option<(usize, usize)> {
        self.clause_position
    }

    pub fn with_resource_arguments(mut self, arguments: Vec<Variable>) -> Self {
        self.resource_arguments = arguments.into();
        self
    }

    pub fn resource_arguments(&self) -> &[Variable] {
        &self.resource_arguments
    }

    pub fn with_source_arguments(mut self, arguments: Vec<String>) -> Self {
        self.source_arguments = Some(arguments.into());
        self
    }

    pub(crate) fn source_arguments(&self) -> Option<&[String]> {
        self.source_arguments.as_deref()
    }

    pub fn family(&self) -> ResourceFamily {
        self.term.family()
    }

    pub fn is_view(&self) -> bool {
        self.access == CResourceAccessMode::View
    }

    pub fn is_instance(&self) -> bool {
        matches!(self.term, CResourceTerm::Instance { .. })
    }

    pub fn instance_identity(&self) -> Option<Variable> {
        self.term.instance_identity()
    }

    pub fn instance_binder(&self) -> Option<&str> {
        self.term.instance_binder()
    }

    pub fn instance_schema(&self) -> Option<&ResourceFieldSchema> {
        self.term.instance_schema()
    }

    pub fn instance_resource(&self) -> Option<CResourceTerm> {
        self.term.instance_resource().cloned()
    }

    pub fn instance_resource_spec(&self) -> Option<Self> {
        let resource = self.instance_resource()?;
        Some(
            Self::new(
                resource,
                CResourceAccessMode::Own,
                CResourceQuantity::One,
                self.role,
                self.snapshot,
            )
            .expect("validated instance terms have valid owned unit bodies")
            .with_resource_arguments(self.resource_arguments().to_vec())
            .with_declared_storage_observation(self.declared_storage_observation())
            .with_native_record_places(self.native_record_places().to_vec())
            .with_native_span_requirements(self.native_span_requirements().to_vec()),
        )
    }

    pub fn memory_segment(&self) -> Option<&CMemorySegment> {
        self.term.memory_segment()
    }

    pub fn memory_segment_mut(&mut self) -> Option<&mut CMemorySegment> {
        match &mut self.term {
            CResourceTerm::Memory(segment) => Some(segment),
            _ => None,
        }
    }

    pub fn declared_name(&self) -> Option<&str> {
        self.term.declared_name()
    }

    pub(crate) fn contained_definition_name(&self) -> Option<&str> {
        let mut term = &self.term;
        while let CResourceTerm::Instance { resource, .. } = term {
            term = resource;
        }
        term.declared_name()
    }

    pub fn declared_arguments(&self) -> Option<&[CExpression]> {
        self.term.declared_arguments()
    }

    pub fn declared_argument_snapshots(&self) -> Option<&[CResourceSnapshot]> {
        self.term.declared_argument_snapshots()
    }

    pub fn declared_parameter_types(&self) -> Option<&[CType]> {
        self.term.declared_parameter_types()
    }

    pub fn composite(
        access: CResourceAccessMode,
        name: String,
        arguments: Vec<CExpression>,
        parameter_types: Vec<CType>,
    ) -> Self {
        Self::declared(
            ResourceFamily::Composite,
            access,
            name,
            arguments,
            parameter_types,
            CResourceTransferRole::Consume,
            CResourceSnapshot::Current,
        )
        .expect("composite resource terms are valid by construction")
    }

    pub fn token(
        access: CResourceAccessMode,
        name: String,
        arguments: Vec<CExpression>,
        parameter_types: Vec<CType>,
    ) -> Self {
        Self::declared(
            ResourceFamily::Token,
            access,
            name,
            arguments,
            parameter_types,
            CResourceTransferRole::Consume,
            CResourceSnapshot::Current,
        )
        .expect("token resource terms are valid by construction")
    }

    pub fn with_role(mut self, role: CResourceTransferRole) -> Self {
        self.role = role;
        self
    }

    pub fn with_snapshot(mut self, snapshot: CResourceSnapshot) -> Self {
        self.snapshot = snapshot;
        self
    }

    fn validate(&self) -> Result<(), CResourceSpecError> {
        crate::kernel::primitives::resource_algebra::validate_resource_spec(self)
    }
}

// Clause positions are diagnostic provenance, not part of a resource's
// identity.  In particular, the same normalized term may occur in a
// precondition and a postcondition (or in two separately expanded source
// clauses); changing its source position must not change contract identity,
// resource indexing, or equality used by the algebra.
impl PartialEq for CResourceSpec {
    fn eq(&self, other: &Self) -> bool {
        self.term == other.term
            && self.declared_storage_observation == other.declared_storage_observation
            && self.native_record_places == other.native_record_places
            && self.native_span_requirements == other.native_span_requirements
            && self.resource_arguments == other.resource_arguments
            && self.mutex_authority_binding == other.mutex_authority_binding
            && self.access == other.access
            && self.quantity == other.quantity
            && self.quantity_snapshot == other.quantity_snapshot
            && self.role == other.role
            && self.snapshot == other.snapshot
            && self.guard == other.guard
    }
}

impl Eq for CResourceSpec {}

impl Hash for CResourceSpec {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.declared_storage_observation.hash(state);
        self.native_record_places.hash(state);
        self.term.hash(state);
        self.resource_arguments.hash(state);
        self.mutex_authority_binding.hash(state);
        self.access.hash(state);
        self.quantity.hash(state);
        self.quantity_snapshot.hash(state);
        self.role.hash(state);
        self.snapshot.hash(state);
        self.guard.hash(state);
        if !self.native_span_requirements.is_empty() {
            "native_span_requirements".hash(state);
            self.native_span_requirements.hash(state);
        }
    }
}

impl Ord for CResourceSpec {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (
            &self.term,
            &self.native_record_places,
            &self.native_span_requirements,
            &self.declared_storage_observation,
            &self.resource_arguments,
            &self.mutex_authority_binding,
            self.access,
            &self.quantity,
            self.quantity_snapshot,
            self.role,
            self.snapshot,
            &self.guard,
        )
            .cmp(&(
                &other.term,
                &other.native_record_places,
                &other.native_span_requirements,
                &other.declared_storage_observation,
                &other.resource_arguments,
                &other.mutex_authority_binding,
                other.access,
                &other.quantity,
                other.quantity_snapshot,
                other.role,
                other.snapshot,
                &other.guard,
            ))
    }
}

impl PartialOrd for CResourceSpec {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod named_mutex_authority_spec_tests {
    use super::*;

    fn authority(term: CResourceTerm) -> CResourceSpec {
        CResourceSpec::new(
            term,
            CResourceAccessMode::Own,
            CResourceQuantity::One,
            CResourceTransferRole::Borrow,
            CResourceSnapshot::Current,
        )
        .unwrap()
    }

    #[test]
    fn raw_mutex_authority_bindings_are_typed_and_retained() {
        let mutex = Box::new(CExpression::Value(CValue::pointer(Pointer::symbolic(
            Variable(700),
        ))));
        for term in [
            CResourceTerm::MutexLive {
                mutex: mutex.clone(),
                snapshot: CResourceSnapshot::Current,
            },
            CResourceTerm::MutexUse {
                protected: None,
                mutex: mutex.clone(),
                snapshot: CResourceSnapshot::Current,
            },
            CResourceTerm::MutexGuard {
                mutex: mutex.clone(),
                snapshot: CResourceSnapshot::Current,
            },
        ] {
            let unnamed = authority(term);
            let named = unnamed
                .clone()
                .with_mutex_authority_binding(Variable(9), "guard".into())
                .unwrap();
            assert_eq!(named.term(), unnamed.term());
            assert_eq!(named.family(), unnamed.family());
            assert_eq!(named.binding_identity(), Some(Variable(9)));
            assert_eq!(named.instance_identity(), None);
            assert_eq!(
                named.mutex_authority_binding(),
                Some((Variable(9), "guard"))
            );
            assert_ne!(named, unnamed);
            assert_ne!(named.cmp(&unnamed), std::cmp::Ordering::Equal);
            assert_eq!(
                named
                    .clone()
                    .with_role(CResourceTransferRole::Consume)
                    .with_snapshot(CResourceSnapshot::Entry)
                    .mutex_authority_binding(),
                Some((Variable(9), "guard"))
            );
            assert!(
                named
                    .with_mutex_authority_binding(Variable(10), "another".into())
                    .is_err()
            );
        }
    }

    #[test]
    fn non_mutex_and_non_exclusive_specs_cannot_be_named_authority() {
        let token = CResourceSpec::token(CResourceAccessMode::Own, "token".into(), vec![], vec![]);
        assert!(
            token
                .with_mutex_authority_binding(Variable(1), "token".into())
                .is_err()
        );
        let composite =
            CResourceSpec::composite(CResourceAccessMode::Own, "state".into(), vec![], vec![]);
        assert!(
            composite
                .with_mutex_authority_binding(Variable(1), "state".into())
                .is_err()
        );
        let mutex = Box::new(CExpression::Value(CValue::pointer(Pointer::symbolic(
            Variable(701),
        ))));
        let viewed = CResourceSpec::new(
            CResourceTerm::MutexGuard {
                mutex: mutex.clone(),
                snapshot: CResourceSnapshot::Current,
            },
            CResourceAccessMode::View,
            CResourceQuantity::One,
            CResourceTransferRole::Borrow,
            CResourceSnapshot::Current,
        );
        assert!(viewed.is_err());
        let counted = CResourceSpec::new(
            CResourceTerm::MutexGuard {
                mutex,
                snapshot: CResourceSnapshot::Current,
            },
            CResourceAccessMode::Own,
            CResourceQuantity::Count(CExpression::Value(int32(2))),
            CResourceTransferRole::Borrow,
            CResourceSnapshot::Current,
        );
        assert!(counted.is_err());
    }
}

#[cfg(test)]
mod population_authority_spec_tests {
    use super::*;

    fn authority_type(resource: CResourceSpec) -> CResourceTerm {
        CResourceTerm::PopulationAuthority {
            population_arity: None,
            protected: Box::new(CResourceTypeSpec {
                resource: Box::new(resource),
                schema: ResourceFieldSchema::new(vec![]).unwrap(),
            }),
            snapshot: CResourceSnapshot::Current,
        }
    }

    #[test]
    fn authority_requires_exclusive_unit_declared_type() {
        for resource in [
            CResourceSpec::composite(CResourceAccessMode::Own, "node".into(), vec![], vec![]),
            CResourceSpec::token(CResourceAccessMode::Own, "node".into(), vec![], vec![]),
        ] {
            let term = authority_type(resource);
            assert!(
                CResourceSpec::new(
                    term.clone(),
                    CResourceAccessMode::Own,
                    CResourceQuantity::One,
                    CResourceTransferRole::Borrow,
                    CResourceSnapshot::Current,
                )
                .is_ok()
            );
            assert!(
                CResourceSpec::new(
                    term.clone(),
                    CResourceAccessMode::View,
                    CResourceQuantity::One,
                    CResourceTransferRole::Borrow,
                    CResourceSnapshot::Current,
                )
                .is_err()
            );
            assert!(
                CResourceSpec::new(
                    term,
                    CResourceAccessMode::Own,
                    CResourceQuantity::Count(CExpression::Value(int32(2))),
                    CResourceTransferRole::Borrow,
                    CResourceSnapshot::Current,
                )
                .is_err()
            );
        }
    }

    #[test]
    fn authority_cannot_be_composed_twice_or_split() {
        let description = super::super::ResourceDescription::new(
            "node".into(),
            Arc::from([]),
            ResourceFieldSchema::new(vec![]).unwrap(),
        );
        let fact = CResourceFact::own(CResource::PopulationAuthority(description.clone()));
        let assumptions = PureFactContext::new();
        let context = ResourceContext::new()
            .try_compose_with_fact(fact.clone(), &assumptions)
            .unwrap();
        assert!(
            context
                .clone()
                .try_compose_with_fact(fact.clone(), &assumptions)
                .is_err()
        );
        assert!(context.satisfies_fact(&fact, &assumptions));
        assert!(
            ResourceContext::new()
                .try_compose_with_fact(
                    CResourceFact::View(CResource::PopulationAuthority(description.clone())),
                    &assumptions,
                )
                .is_err()
        );
        assert!(
            ResourceContext::new()
                .try_compose_with_fact(
                    CResourceFact::Own(
                        CResource::PopulationAuthority(description.clone()),
                        Box::new(Bitvector32Term::Constant(2)),
                    ),
                    &assumptions,
                )
                .is_err()
        );
        assert!(
            CResourceFact::View(CResource::PopulationAuthority(description))
                .core()
                .is_none()
        );
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Term {
    Condition(ConditionTerm),
    Bitvector32(Bitvector32Term),
    Integer(IntegerTerm),
    PointerOffset(PointerOffsetTerm),
    CValue(CValue),
    Sequence(SequenceTerm),
    Algebraic(AlgebraicTerm),
    CExpressionOutcome(CExpressionOutcome),
    // Outcomes carry CState. Keep them out of Term's inline size so cloning
    // a deep pure proposition does not spend stack on unused C variants.
    CStatementOutcome(Box<CStatementOutcome>),
    CFunctionOutcome(Box<CFunctionOutcome>),
    CMemory(CMemory),
    CState(Box<CState>),
}

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum Proposition {
    Equal(Term, Term),
    ConditionIs(ConditionTerm, bool),
    Predicate {
        name: String,
        arguments: Vec<Term>,
    },
    CExpressionEvaluates {
        state: Box<CState>,
        expression: CExpression,
        outcome: CExpressionOutcome,
    },
    CConditionEvaluates {
        state: Box<CState>,
        condition: CExpression,
        outcome: CConditionOutcome,
    },
    CStatementExecutes {
        state: Box<CState>,
        statement: Box<CStatement>,
        outcome: CStatementOutcome,
    },
    /// An abstract verification transition. Unlike `CStatementExecutes`, this
    /// does not assert that the represented outcome is concretely reachable.
    CStatementVerifies {
        state: Box<CState>,
        statement: Box<CStatement>,
        outcome: CStatementOutcome,
    },
    CFunctionExecutes {
        state: Box<CState>,
        function: Box<CFunction>,
        arguments: Vec<CExpression>,
        outcome: CFunctionOutcome,
    },
    /// A return branch admitted by modular verification. This is conditional
    /// on the function returning and is not a termination or reachability
    /// theorem.
    CFunctionVerifies {
        state: Box<CState>,
        function: Box<CFunction>,
        arguments: Vec<CExpression>,
        outcome: CFunctionOutcome,
    },
    CFunctionSatisfiesSpecification {
        function: Box<CFunction>,
        // Large C payloads stay out of every pure proposition clone frame.
        specification: Box<CFunctionSpecification>,
    },
    /// The specification describes one allowed return branch and makes no
    /// claim that the branch is reachable or that the function terminates.
    CFunctionPartiallySatisfiesSpecification {
        function: Box<CFunction>,
        specification: Box<CFunctionSpecification>,
    },
    CMemoryLoads {
        memory: CMemory,
        pointer: Pointer,
        outcome: CExpressionOutcome,
    },
    CMemoryCanStore {
        memory: CMemory,
        pointer: Pointer,
        byte_width: u32,
    },
    /// `bytes` bytes at `base` are live in `memory`. The count is a 32-bit
    /// term, or, when `wide`, an unsigned 64-bit one: a term carries no
    /// width, so a reader that takes a wide count as 32 bits misreads it.
    CMemoryLoadable {
        memory: CMemory,
        base: Pointer,
        bytes: Bitvector32Term,
        wide: bool,
    },
    /// Every byte in this live fixed range has been initialized. Pure
    /// snapshot evidence, separate from access permission and byte values.
    CMemoryInitialized {
        memory: CMemory,
        base: Pointer,
        bytes: u32,
    },
    /// A complete carrier designates a live location of the selected type.
    /// This grants neither byte permission nor initialization.
    CValidPlace {
        memory: CMemory,
        pointer: CPointerValue,
        range: Option<(SharedIntegerTerm, SharedIntegerTerm)>,
        place_type: CPlaceType,
        access_policy: CTypedAccessPolicy,
    },
    /// A typed read is valid in this snapshot, including initialization.
    /// This is a pure fact; it grants no resource access permission.
    CMemoryReadDefined {
        memory: CMemory,
        pointer: Pointer,
        value_type: CType,
    },
    CResourceSeparate {
        left: Box<CResource>,
        right: Box<CResource>,
    },
    /// Internal carrier for an already-validated resource composition.
    /// PureFactContext store this as indexed kernel authority rather than as an
    /// ambient proposition visible to proof search.
    CResourceComposition(ResourceContext),
    CResourceContains {
        parent: Box<CResource>,
        child: Box<CResource>,
    },
    CMemoryMutatesOnly {
        before: CMemory,
        after: CMemory,
        writes: Vec<(Pointer, u32)>,
    },
    CMemoryEffectSummary {
        before: CMemory,
        after: CMemory,
        mutable_ranges: Vec<CMemoryRange>,
    },
    CHeapAllocationFreed {
        before: CMemory,
        after: CMemory,
        allocation_base: Pointer,
        bytes: Bitvector32Term,
    },
    And(Box<Proposition>, Box<Proposition>),
    Or(Box<Proposition>, Box<Proposition>),
    Not(Box<Proposition>),
    Implies(Box<Proposition>, Box<Proposition>),
    ForAll {
        var: Variable,
        sort: Sort,
        body: Box<Proposition>,
    },
    Exists {
        name: String,
        var: Variable,
        sort: Sort,
        body: Box<Proposition>,
    },
}

impl Proposition {
    /// The two ranges of a separation between two memory resources.
    pub(crate) fn memory_separation(&self) -> Option<(&CMemoryRange, &CMemoryRange)> {
        match self {
            Self::CResourceSeparate { left, right } => match (&**left, &**right) {
                (CResource::Memory(left), CResource::Memory(right)) => Some((left, right)),
                _ => None,
            },
            _ => None,
        }
    }

    /// The parent and the child range of a containment of a memory resource.
    pub(crate) fn memory_containment(&self) -> Option<(&CResource, &CMemoryRange)> {
        match self {
            Self::CResourceContains { parent, child } => match &**child {
                CResource::Memory(range) => Some((parent, range)),
                _ => None,
            },
            _ => None,
        }
    }
}

impl Clone for Proposition {
    fn clone(&self) -> Self {
        clone_proposition_iteratively(self)
    }
}

impl Hash for Proposition {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut pending = vec![self];
        while let Some(proposition) = pending.pop() {
            match proposition {
                Proposition::And(left, right) => {
                    0u8.hash(state);
                    pending.push(right);
                    pending.push(left);
                }
                Proposition::Or(left, right) => {
                    1u8.hash(state);
                    pending.push(right);
                    pending.push(left);
                }
                Proposition::Not(body) => {
                    2u8.hash(state);
                    pending.push(body);
                }
                Proposition::Implies(left, right) => {
                    3u8.hash(state);
                    pending.push(right);
                    pending.push(left);
                }
                Proposition::ForAll { var, sort, body } => {
                    4u8.hash(state);
                    var.hash(state);
                    sort.hash(state);
                    pending.push(body);
                }
                Proposition::Exists {
                    name,
                    var,
                    sort,
                    body,
                } => {
                    5u8.hash(state);
                    name.hash(state);
                    var.hash(state);
                    sort.hash(state);
                    pending.push(body);
                }
                atomic => {
                    // Atomic proposition variants contain no Proposition
                    // children, so their fields hash directly while the deep
                    // connective topology above stays iterative.
                    6u8.hash(state);
                    hash_atomic_proposition(atomic, state);
                }
            }
        }
    }
}

/// Hashes one atomic proposition by its fields, consistently with the derived
/// equality. Every field hashes structurally; a memory snapshot hashes by its
/// cached content hash in O(1). Hashing an atom's debug text instead printed
/// every snapshot it names, so inserting or looking up a call's effect summary
/// cost the size of the whole memory, and each later call in a long function
/// paid more than the last.
fn hash_atomic_proposition<H: Hasher>(atomic: &Proposition, state: &mut H) {
    std::mem::discriminant(atomic).hash(state);
    match atomic {
        Proposition::Equal(left, right) => {
            left.hash(state);
            right.hash(state);
        }
        Proposition::ConditionIs(condition, value) => {
            condition.hash(state);
            value.hash(state);
        }
        Proposition::Predicate { name, arguments } => {
            name.hash(state);
            arguments.hash(state);
        }
        Proposition::CExpressionEvaluates {
            state: c_state,
            expression,
            outcome,
        } => {
            c_state.hash(state);
            expression.hash(state);
            outcome.hash(state);
        }
        Proposition::CConditionEvaluates {
            state: c_state,
            condition,
            outcome,
        } => {
            c_state.hash(state);
            condition.hash(state);
            outcome.hash(state);
        }
        Proposition::CStatementExecutes {
            state: c_state,
            statement,
            outcome,
        }
        | Proposition::CStatementVerifies {
            state: c_state,
            statement,
            outcome,
        } => {
            c_state.hash(state);
            statement.hash(state);
            outcome.hash(state);
        }
        Proposition::CFunctionExecutes {
            state: c_state,
            function,
            arguments,
            outcome,
        }
        | Proposition::CFunctionVerifies {
            state: c_state,
            function,
            arguments,
            outcome,
        } => {
            c_state.hash(state);
            function.hash(state);
            arguments.hash(state);
            outcome.hash(state);
        }
        Proposition::CFunctionSatisfiesSpecification {
            function,
            specification,
        }
        | Proposition::CFunctionPartiallySatisfiesSpecification {
            function,
            specification,
        } => {
            function.hash(state);
            specification.hash(state);
        }
        Proposition::CMemoryLoads {
            memory,
            pointer,
            outcome,
        } => {
            memory.hash(state);
            pointer.hash(state);
            outcome.hash(state);
        }
        Proposition::CMemoryCanStore {
            memory,
            pointer,
            byte_width,
        } => {
            memory.hash(state);
            pointer.hash(state);
            byte_width.hash(state);
        }
        Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
            wide,
        } => {
            memory.hash(state);
            base.hash(state);
            bytes.hash(state);
            wide.hash(state);
        }
        Proposition::CMemoryInitialized {
            memory,
            base,
            bytes,
        } => {
            memory.hash(state);
            base.hash(state);
            bytes.hash(state);
        }
        Proposition::CValidPlace {
            range,
            memory,
            pointer,
            place_type,
            access_policy,
        } => {
            memory.hash(state);
            pointer.hash(state);
            range.hash(state);
            place_type.hash(state);
            access_policy.hash(state);
        }
        Proposition::CMemoryReadDefined {
            memory,
            pointer,
            value_type,
        } => {
            memory.hash(state);
            pointer.hash(state);
            value_type.hash(state);
        }
        Proposition::CResourceSeparate { left, right } => {
            left.hash(state);
            right.hash(state);
        }
        Proposition::CResourceComposition(resources) => resources.hash(state),
        Proposition::CResourceContains { parent, child } => {
            parent.hash(state);
            child.hash(state);
        }
        Proposition::CMemoryMutatesOnly {
            before,
            after,
            writes,
        } => {
            before.hash(state);
            after.hash(state);
            writes.hash(state);
        }
        Proposition::CMemoryEffectSummary {
            before,
            after,
            mutable_ranges,
        } => {
            before.hash(state);
            after.hash(state);
            mutable_ranges.hash(state);
        }
        Proposition::CHeapAllocationFreed {
            before,
            after,
            allocation_base,
            bytes,
        } => {
            before.hash(state);
            after.hash(state);
            allocation_base.hash(state);
            bytes.hash(state);
        }
        Proposition::And(..)
        | Proposition::Or(..)
        | Proposition::Not(..)
        | Proposition::Implies(..)
        | Proposition::ForAll { .. }
        | Proposition::Exists { .. } => {
            unreachable!("connectives are hashed iteratively by `Hash for Proposition`")
        }
    }
}

#[cfg(test)]
thread_local! {
    static PROPOSITION_CLONE_NODES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
#[cfg(test)]
pub(crate) fn count_proposition_clone_nodes<T>(body: impl FnOnce() -> T) -> (T, usize) {
    let before = PROPOSITION_CLONE_NODES.with(std::cell::Cell::get);
    let value = body();
    (
        value,
        PROPOSITION_CLONE_NODES.with(std::cell::Cell::get) - before,
    )
}

/// Clones the logical tree without recursing through a long connective chain.
/// This is also `Proposition::clone`, so callers cannot accidentally restore
/// recursive cloning by using the trait method on a deep implication.
pub(crate) fn clone_proposition_iteratively(proposition: &Proposition) -> Proposition {
    enum Frame<'a> {
        Visit(&'a Proposition),
        BuildAnd,
        BuildOr,
        BuildNot,
        BuildImplies,
        BuildForAll {
            var: Variable,
            sort: Sort,
        },
        BuildExists {
            name: String,
            var: Variable,
            sort: Sort,
        },
    }

    let mut frames = vec![Frame::Visit(proposition)];
    let mut values = Vec::new();
    while let Some(frame) = frames.pop() {
        #[cfg(test)]
        if matches!(frame, Frame::Visit(_)) {
            PROPOSITION_CLONE_NODES.with(|count| count.set(count.get() + 1));
        }
        match frame {
            Frame::Visit(proposition) => match proposition {
                Proposition::And(left, right) => {
                    frames.push(Frame::BuildAnd);
                    frames.push(Frame::Visit(right));
                    frames.push(Frame::Visit(left));
                }
                Proposition::Or(left, right) => {
                    frames.push(Frame::BuildOr);
                    frames.push(Frame::Visit(right));
                    frames.push(Frame::Visit(left));
                }
                Proposition::Not(body) => {
                    frames.push(Frame::BuildNot);
                    frames.push(Frame::Visit(body));
                }
                Proposition::Implies(left, right) => {
                    frames.push(Frame::BuildImplies);
                    frames.push(Frame::Visit(right));
                    frames.push(Frame::Visit(left));
                }
                Proposition::ForAll { var, sort, body } => {
                    frames.push(Frame::BuildForAll {
                        var: *var,
                        sort: sort.clone(),
                    });
                    frames.push(Frame::Visit(body));
                }
                Proposition::Exists {
                    name,
                    var,
                    sort,
                    body,
                } => {
                    frames.push(Frame::BuildExists {
                        name: name.clone(),
                        var: *var,
                        sort: sort.clone(),
                    });
                    frames.push(Frame::Visit(body));
                }
                atomic => values.push(clone_atomic_proposition(atomic)),
            },
            Frame::BuildAnd => {
                let right = values.pop().expect("the right proposition is cloned");
                let left = values.pop().expect("the left proposition is cloned");
                values.push(Proposition::And(Box::new(left), Box::new(right)));
            }
            Frame::BuildOr => {
                let right = values.pop().expect("the right proposition is cloned");
                let left = values.pop().expect("the left proposition is cloned");
                values.push(Proposition::Or(Box::new(left), Box::new(right)));
            }
            Frame::BuildNot => {
                let body = values.pop().expect("the proposition body is cloned");
                values.push(Proposition::Not(Box::new(body)));
            }
            Frame::BuildImplies => {
                let right = values.pop().expect("the implication consequent is cloned");
                let left = values.pop().expect("the implication antecedent is cloned");
                values.push(Proposition::Implies(Box::new(left), Box::new(right)));
            }
            Frame::BuildForAll { var, sort } => {
                let body = values.pop().expect("the forall body is cloned");
                values.push(Proposition::ForAll {
                    var,
                    sort,
                    body: Box::new(body),
                });
            }
            Frame::BuildExists { name, var, sort } => {
                let body = values.pop().expect("the exists body is cloned");
                values.push(Proposition::Exists {
                    name,
                    var,
                    sort,
                    body: Box::new(body),
                });
            }
        }
    }
    values.pop().expect("the root proposition is cloned")
}

fn clone_atomic_proposition(proposition: &Proposition) -> Proposition {
    match proposition {
        Proposition::Equal(left, right) => Proposition::Equal(left.clone(), right.clone()),
        Proposition::ConditionIs(condition, value) => {
            Proposition::ConditionIs(condition.clone(), *value)
        }
        Proposition::Predicate { name, arguments } => Proposition::Predicate {
            name: name.clone(),
            arguments: arguments.clone(),
        },
        Proposition::CExpressionEvaluates {
            state,
            expression,
            outcome,
        } => Proposition::CExpressionEvaluates {
            state: state.clone(),
            expression: expression.clone(),
            outcome: outcome.clone(),
        },
        Proposition::CConditionEvaluates {
            state,
            condition,
            outcome,
        } => Proposition::CConditionEvaluates {
            state: state.clone(),
            condition: condition.clone(),
            outcome: outcome.clone(),
        },
        Proposition::CStatementExecutes {
            state,
            statement,
            outcome,
        } => Proposition::CStatementExecutes {
            state: state.clone(),
            statement: statement.clone(),
            outcome: outcome.clone(),
        },
        Proposition::CStatementVerifies {
            state,
            statement,
            outcome,
        } => Proposition::CStatementVerifies {
            state: state.clone(),
            statement: statement.clone(),
            outcome: outcome.clone(),
        },
        Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome,
        } => Proposition::CFunctionExecutes {
            state: state.clone(),
            function: function.clone(),
            arguments: arguments.clone(),
            outcome: outcome.clone(),
        },
        Proposition::CFunctionVerifies {
            state,
            function,
            arguments,
            outcome,
        } => Proposition::CFunctionVerifies {
            state: state.clone(),
            function: function.clone(),
            arguments: arguments.clone(),
            outcome: outcome.clone(),
        },
        Proposition::CFunctionSatisfiesSpecification {
            function,
            specification,
        } => Proposition::CFunctionSatisfiesSpecification {
            function: function.clone(),
            specification: specification.clone(),
        },
        Proposition::CFunctionPartiallySatisfiesSpecification {
            function,
            specification,
        } => Proposition::CFunctionPartiallySatisfiesSpecification {
            function: function.clone(),
            specification: specification.clone(),
        },
        Proposition::CMemoryLoads {
            memory,
            pointer,
            outcome,
        } => Proposition::CMemoryLoads {
            memory: memory.clone(),
            pointer: pointer.clone(),
            outcome: outcome.clone(),
        },
        Proposition::CMemoryCanStore {
            memory,
            pointer,
            byte_width,
        } => Proposition::CMemoryCanStore {
            memory: memory.clone(),
            pointer: pointer.clone(),
            byte_width: *byte_width,
        },
        Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
            wide,
        } => Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: base.clone(),
            bytes: bytes.clone(),
            wide: *wide,
        },
        Proposition::CValidPlace {
            range,
            memory,
            pointer,
            place_type,
            access_policy,
        } => Proposition::CValidPlace {
            range: range.clone(),
            memory: memory.clone(),
            pointer: pointer.clone(),
            place_type: place_type.clone(),
            access_policy: *access_policy,
        },
        Proposition::CMemoryInitialized {
            memory,
            base,
            bytes,
        } => Proposition::CMemoryInitialized {
            memory: memory.clone(),
            base: base.clone(),
            bytes: *bytes,
        },
        Proposition::CMemoryReadDefined {
            memory,
            pointer,
            value_type,
        } => Proposition::CMemoryReadDefined {
            memory: memory.clone(),
            pointer: pointer.clone(),
            value_type: *value_type,
        },
        Proposition::CResourceSeparate { left, right } => Proposition::CResourceSeparate {
            left: left.clone(),
            right: right.clone(),
        },
        Proposition::CResourceComposition(resources) => {
            Proposition::CResourceComposition(resources.clone())
        }
        Proposition::CResourceContains { parent, child } => Proposition::CResourceContains {
            parent: parent.clone(),
            child: child.clone(),
        },
        Proposition::CMemoryMutatesOnly {
            before,
            after,
            writes,
        } => Proposition::CMemoryMutatesOnly {
            before: before.clone(),
            after: after.clone(),
            writes: writes.clone(),
        },
        Proposition::CMemoryEffectSummary {
            before,
            after,
            mutable_ranges,
        } => Proposition::CMemoryEffectSummary {
            before: before.clone(),
            after: after.clone(),
            mutable_ranges: mutable_ranges.clone(),
        },
        Proposition::CHeapAllocationFreed {
            before,
            after,
            allocation_base,
            bytes,
        } => Proposition::CHeapAllocationFreed {
            before: before.clone(),
            after: after.clone(),
            allocation_base: allocation_base.clone(),
            bytes: bytes.clone(),
        },
        Proposition::And(..)
        | Proposition::Or(..)
        | Proposition::Not(..)
        | Proposition::Implies(..)
        | Proposition::ForAll { .. }
        | Proposition::Exists { .. } => unreachable!("connectives are cloned by the work stack"),
    }
}

/// Compares a proposition tree without consuming stack per logical connective.
/// Atomic terms retain their ordinary equality implementation; the unbounded
/// surface shape is the proposition connective spine handled here.
pub(crate) fn propositions_equal_iteratively(left: &Proposition, right: &Proposition) -> bool {
    let mut pending = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        match (left, right) {
            (Proposition::And(left, right), Proposition::And(other_left, other_right))
            | (Proposition::Or(left, right), Proposition::Or(other_left, other_right))
            | (Proposition::Implies(left, right), Proposition::Implies(other_left, other_right)) => {
                pending.push((right, other_right));
                pending.push((left, other_left));
            }
            (Proposition::Not(body), Proposition::Not(other_body)) => {
                pending.push((body, other_body));
            }
            (
                Proposition::ForAll { var, sort, body },
                Proposition::ForAll {
                    var: other_var,
                    sort: other_sort,
                    body: other_body,
                },
            ) => {
                if var != other_var || sort != other_sort {
                    return false;
                }
                pending.push((body, other_body));
            }
            (
                Proposition::Exists {
                    name,
                    var,
                    sort,
                    body,
                },
                Proposition::Exists {
                    name: other_name,
                    var: other_var,
                    sort: other_sort,
                    body: other_body,
                },
            ) => {
                if name != other_name || var != other_var || sort != other_sort {
                    return false;
                }
                pending.push((body, other_body));
            }
            (left, right) if std::mem::discriminant(left) == std::mem::discriminant(right) => {
                if left != right {
                    return false;
                }
            }
            _ => return false,
        }
    }
    true
}

/// An abstract proven proposition produced by kernel axioms.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Theorem {
    pub(super) proposition: std::sync::Arc<Proposition>,
}

/// Kernel-issued authority for a closed pure theorem that may be used during
/// whole-contract certification. The private field prevents the Click layer
/// from promoting an arbitrary proposition or unrelated theorem object.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CVerifiedPureTheorem {
    pub(super) theorem: Theorem,
}

/// A local, symbolic contract-refinement problem opened by a pure theorem.
///
/// Construction is kernel-owned. The refining interface is either a verified
/// or explicitly external concrete function, or another exact named contract
/// fact for the same symbolic pointer. Both interfaces are instantiated with
/// the same fresh arguments. The surface proof may inspect the argument
/// bindings and entry state only to lower explicit logical case splits; it
/// cannot manufacture a refinement authority.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CFunctionContractRefinementContext {
    pub(super) contract: CFunctionContract,
    /// The implementation side of refinement is an interface judgment too;
    /// concrete body evidence is checked before this context is opened and is
    /// not needed to lower the symbolic relation.
    pub(super) function_interface: CFunctionContractInterface,
    pub(super) function_name: String,
    pub(super) pointer: CPointerValue,
    pub(super) source_contract: Option<CFunctionContract>,
    pub(super) argument_values: Vec<CValue>,
    pub(super) result_variable: Variable,
    /// The mark the budget that invented `argument_values` reached,
    /// execution-relative: the refinement obligations continue from it
    /// rather than restarting the counter over arguments already issued.
    pub(super) next_kernel_variable: u64,
}

/// Kernel-generated sufficient logical obligations for one contract relation.
/// The states and proposition cannot be supplied by the language layer.
pub struct CFunctionContractRefinementObligations {
    pub(super) entry: CState,
    pub(super) post: CState,
    pub(super) proposition: Proposition,
}

/// A proof tree produced by contextual proposition reasoning.
///
/// Smart reasoning may search for this tree. Check only checks the selected
/// rule and its explicit children; it never searches for an alternative proof.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PropositionDerivation {
    pub(super) conclusion: Proposition,
    pub(super) rule: PropositionDerivationRule,
}

/// One exact signed-order edge retained by an atomic derivation.
///
/// The edge is oriented from `lower` to `upper`; `strict` distinguishes `<`
/// from `<=`. Certificate consumers can write this ordered path directly
/// instead of rediscovering it from an unordered premise set.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SignedOrderDerivationStep {
    pub(super) lower: Bitvector32Term,
    pub(super) upper: Bitvector32Term,
    pub(super) strict: bool,
    pub(super) premise: Proposition,
}

/// The base-alignment fact an atomic pointer-alignment decision rested on.
/// `None` means the base is a heap allocation, whose alignment is intrinsic
/// to the LP64 allocator profile and needs no context fact.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct PointerAlignmentEvidence {
    pub(super) premise: Option<Proposition>,
}

/// The exact facts a pointer-word equality decision rested on: recorded
/// address forms of words, base alignments, tag bounds, and pointer
/// equalities. Checking the decision from exactly these facts re-derives
/// the same value.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct PointerWordEvidence {
    pub(super) premises: Vec<Proposition>,
}

/// One exact ground-int32 equality edge retained in the orientation selected
/// by an atomic derivation. `premise` is the exact context proposition; the
/// source/target orientation may be the reverse of its written equality.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BitvectorEqualityDerivationStep {
    pub(super) source: Bitvector32Term,
    pub(super) target: Bitvector32Term,
    pub(super) premise: Proposition,
}

/// Target-directed evidence that two pointer offsets are equal by structural
/// congruence, exact integer equality premises, and bounded full-width
/// constant arithmetic.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum PointerOffsetCongruenceEvidence {
    Exact,
    WideScaledConstant {
        value: i64,
    },
    ExactPremise(Box<Proposition>),
    Add {
        first: Box<PointerOffsetCongruenceEvidence>,
        second: Box<PointerOffsetCongruenceEvidence>,
        swapped: bool,
    },
    /// Equal full-pointer observations, projected to the same numeric stride.
    /// This is offset equality only and never transports a designation.
    PointerReadSnapshot {
        byte_width: i64,
        equality: Box<crate::kernel::memory_provenance::CheckedLoadEquality>,
    },
    /// A numeric full-pointer read is unchanged between two checked
    /// snapshots, followed by an exact offset premise at its newer spelling.
    PointerReadSnapshotAlias {
        byte_width: i64,
        intermediate: Box<PointerOffsetTerm>,
        equality: Box<crate::kernel::memory_provenance::CheckedLoadEquality>,
        premise: Box<Proposition>,
        reversed: bool,
    },
    Int32Scaled {
        byte_width: i64,
        path: Vec<BitvectorEqualityDerivationStep>,
    },
    Int32ScaledDerived {
        byte_width: i64,
        equality: DirectBitvectorEqualityEvidence,
    },
    Int64Scaled {
        byte_width: i64,
        unsigned: bool,
        path: Vec<BitvectorEqualityDerivationStep>,
    },
    ElementIndex {
        byte_width: u32,
        path: Vec<BitvectorEqualityDerivationStep>,
    },
    ElementIndexDerived {
        byte_width: u32,
        equality: DirectBitvectorEqualityEvidence,
    },
}

/// A finite, target-directed equality path used inside retained pointer
/// congruence. Each variant names exact equality or order evidence; the
/// checker follows that path without proposition search.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum DirectBitvectorEqualityEvidence {
    AdditiveCancellation {
        left: Bitvector32Term,
        right: Bitvector32Term,
        equality: Box<DirectBitvectorEqualityEvidence>,
    },
    EqualSignedConstants {
        value: i64,
        left: SignedConstantEvidence,
        right: SignedConstantEvidence,
    },
    LeAndNotLt(Box<Int32LeAndNotLtEqualityEvidence>),
    GeAndNotGt(Box<Int32GeAndNotGtEqualityEvidence>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum SignedConstantEvidence {
    Constant,
    ExactEquality(Box<Proposition>),
    SingletonBounds {
        variable: Variable,
        lower: IndexedSignedOrderBoundEvidence,
        upper: IndexedSignedOrderBoundEvidence,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct IndexedSignedOrderBoundEvidence {
    pub(in crate::kernel) other_equality: Option<Box<Proposition>>,
    pub(in crate::kernel) endpoint: Bitvector32Term,
    pub(in crate::kernel) other: Bitvector32Term,
    pub(in crate::kernel) strict: bool,
    pub(in crate::kernel) forward: bool,
    pub(in crate::kernel) source: Box<Proposition>,
}

/// Evidence that two load variables name one cell because their
/// registered origins have the same memory epoch and block and congruent
/// offsets. The original variables remain distinct context-free names.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LoadAddressCongruenceEvidence {
    pub(super) left_pointer: Pointer,
    pub(super) right_pointer: Pointer,
    pub(super) offset: PointerOffsetCongruenceEvidence,
}

/// The premises a retained evidence leaf names.
///
/// Evidence records propositions, never a context. A `PureFactContext`
/// carries every derived index and grows with the ambient proof state, so
/// embedding one makes a leaf's size a function of the whole proof rather
/// than of what it actually cited, and `context_premises` had to
/// materialize that index to answer at all. See the "Retained evidence
/// names premises, never a context" rule in `docs/internals/proof-objects.md`.
///
/// Checking a leaf rebuilds a context from exactly these propositions, so
/// the check can never consult more than the evidence names.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RetainedPremises {
    propositions: std::sync::Arc<Vec<Proposition>>,
}

impl RetainedPremises {
    pub(crate) fn from_context(context: &PureFactContext) -> Self {
        Self {
            propositions: std::sync::Arc::new(context.pure_facts()),
        }
    }

    /// The propositions this leaf cites, in a deterministic order.
    pub(crate) fn named(&self) -> &[Proposition] {
        &self.propositions
    }

    /// A context holding exactly the cited propositions and nothing else.
    pub(crate) fn context(&self) -> PureFactContext {
        self.propositions
            .iter()
            .fold(PureFactContext::new(), |context, premise| {
                context.assume_proposition(premise.clone())
            })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum PropositionDerivationRule {
    ContextFree,
    ContextualAtomic {
        premises: RetainedPremises,
        premises_id: u64,
        for_simp: bool,
        evidence: AtomicPropositionDerivationEvidence,
    },
    Explosion {
        premises: RetainedPremises,
    },
    And {
        left: Box<PropositionDerivation>,
        right: Box<PropositionDerivation>,
    },
    /// Constructor congruence: equal corresponding fields make two
    /// applications of the same constructor equal.
    AlgebraicConstructorCongruence {
        fields: Vec<PropositionDerivation>,
    },
    /// Constructor injectivity: an exact equality between two applications
    /// of one constructor entails equality of the selected fields.
    AlgebraicConstructorInjectivity {
        source: Box<Proposition>,
        field_index: usize,
    },
    OrLeft(Box<PropositionDerivation>),
    OrRight(Box<PropositionDerivation>),
    DoubleNegation(Box<PropositionDerivation>),
    Implies {
        antecedent: Box<Proposition>,
        body: Box<PropositionDerivation>,
    },
    ImpliesFalseAntecedent(Box<PropositionDerivation>),
    ForAllBody(Box<PropositionDerivation>),
    /// Prove an existential by selecting the bound variable from an exact
    /// existential fact and checking the target body under that witness's
    /// conjuncts.
    ExistsFromFact {
        source: Box<Proposition>,
        body: Box<PropositionDerivation>,
    },
    /// Prove an existential by selecting a free witness term and checking the
    /// substituted body against the current context.
    ExistsFromWitness {
        witness: Bitvector32Term,
        body: Box<PropositionDerivation>,
    },
    /// Prove an in-range one-byte loadability universal from one exact wider
    /// loadability range and the universal body's guard premises.
    ForAllLoadableRange {
        source: Box<Proposition>,
    },
    /// Prove an existential one-byte loadability fact by selecting the
    /// constant zero index from one exact wider range.
    ExistsLoadableRange {
        source: Box<Proposition>,
        witness: Bitvector32Term,
    },
    FiniteForAll {
        instances: Vec<PropositionDerivation>,
    },
    /// Substitute a variable pinned to one signed value by two exact order
    /// bounds, then check the proof of the resulting proposition.
    SingletonSubstitution {
        variable: Variable,
        value: i64,
        equality: DirectBitvectorEqualityEvidence,
        body: Box<PropositionDerivation>,
    },
    DisjunctionCases {
        disjunction: Box<Proposition>,
        cases: Vec<PropositionDerivation>,
    },
    /// An exact disjunction is impossible when every arm's negation is exact.
    /// No branch context is rebuilt, so opposite condition facts cannot be
    /// overwritten while establishing the contradiction.
    RefutedDisjunction {
        disjunction: Box<Proposition>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Int32IncrementBoundsEvidence {
    pub(super) lower_bound: SignedOrderDerivationStep,
    pub(super) upper_bound: SignedOrderDerivationStep,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Int32PredecessorUpperBoundEvidence {
    pub(super) nonnegative: SignedOrderDerivationStep,
    pub(super) upper_bound: SignedOrderDerivationStep,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Int32OneLeEvidence {
    Direct(Box<SignedOrderDerivationStep>),
    EqualOne(Vec<BitvectorEqualityDerivationStep>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Int32NonnegativeAddWithinMaxEvidence {
    pub(super) amount_nonnegative: SignedOrderDerivationStep,
    pub(super) within_headroom: SignedOrderDerivationStep,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Int32NonnegativeSubtractWithinValueEvidence {
    pub(super) amount_nonnegative: SignedOrderDerivationStep,
    pub(super) within_value: SignedOrderDerivationStep,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Int32LeAndNotLtEqualityEvidence {
    pub(super) less_equal: Proposition,
    pub(super) not_less_than: Proposition,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Int32GeAndNotGtEqualityEvidence {
    pub(super) greater_equal: Proposition,
    pub(super) not_greater_than: Proposition,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Int32LeAndNeqStrictEvidence {
    pub(super) less_equal: Proposition,
    pub(super) not_equal: Proposition,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ForallInt32InstantiationEvidence {
    pub(crate) quantified: Proposition,
    pub(crate) argument: Bitvector32Term,
    pub(crate) guard_premises: Vec<Proposition>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct UInt32PackingEvidence {
    pub(super) memory: SharedCMemory,
    pub(super) object: Pointer,
    pub(super) profile: UInt32RepresentationProfile,
    pub(super) word: Bitvector32Term,
    pub(super) bytes: [u8; 4],
    pub(super) byte_equalities: [Proposition; 4],
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum AtomicPropositionDerivationEvidence {
    WidenedUnsignedSumBound,
    UInt32Representation(Box<UInt32PackingEvidence>),
    MemoryDag(Box<AtomicMemoryLoadEqualityEvidence>),
    LoadAddressCongruence(Box<LoadAddressCongruenceEvidence>),
    PointerOffsetMemoryDag(Box<PointerOffsetEqualityEvidence>),
    BitvectorEqualityPath(Vec<BitvectorEqualityDerivationStep>),
    Int32PinnedConstantEquality(Box<DirectBitvectorEqualityEvidence>),
    ForallInt32Instantiation(Box<ForallInt32InstantiationEvidence>),
    SignedOrderPath(Vec<SignedOrderDerivationStep>),
    /// A chain of exact 64-bit order facts, `uint64` when `unsigned` and
    /// `int64` otherwise, each step's premise in the context as written.
    WideOrderPath {
        unsigned: bool,
        path: Vec<SignedOrderDerivationStep>,
    },
    Int32IncrementUpperBound(Box<SignedOrderDerivationStep>),
    Int32IncrementConstantUpperBound(Box<SignedOrderDerivationStep>),
    Int32IncrementStrictlyIncreases(Box<SignedOrderDerivationStep>),
    Int32IncrementBelowMaxIsDefined(Box<SignedOrderDerivationStep>),
    Int32OnePlusBelowMaxIsDefined(Box<SignedOrderDerivationStep>),
    Int32OnePlusStrictlyIncreases(Box<SignedOrderDerivationStep>),
    Int32NonnegativeAddWithinMaxIsDefined(Box<Int32NonnegativeAddWithinMaxEvidence>),
    Int32NonnegativeSubtractWithinValueIsDefined(Box<Int32NonnegativeSubtractWithinValueEvidence>),
    Int32IncrementLowerBound(Box<Int32IncrementBoundsEvidence>),
    Int32IncrementGreaterEqualLowerBound(Box<Int32IncrementBoundsEvidence>),
    Int32IncrementStrictGreaterLowerBound(Box<Int32IncrementBoundsEvidence>),
    Int32IncrementStrictGreaterFromStrictLower(Box<Int32IncrementBoundsEvidence>),
    Int32IncrementPreservesOrder(Box<Int32IncrementBoundsEvidence>),
    Int32PositiveIsNonnegative(Box<SignedOrderDerivationStep>),
    Int32SuccessorLeImpliesLt(Box<SignedOrderDerivationStep>),
    Int32ConstantLowerBoundWeakening(Box<SignedOrderDerivationStep>),
    Int32NegatedStrictSuccessorBound(Box<SignedOrderDerivationStep>),
    Int32PositivePredecessorIsNonnegative(Box<SignedOrderDerivationStep>),
    Int32PositivePredecessorStrictlyDecreases(Box<SignedOrderDerivationStep>),
    Int32NonnegativePredecessorUpperBound(Box<Int32PredecessorUpperBoundEvidence>),
    Int32OneLePredecessorIsNonnegative(Int32OneLeEvidence),
    Int32OneLePredecessorStrictlyDecreases(Int32OneLeEvidence),
    Int32EqualOnePredecessorIsZero(Vec<BitvectorEqualityDerivationStep>),
    Int32LeAndNeqImpliesStrict(Box<Int32LeAndNeqStrictEvidence>),
    Int32LeAndNotLtImpliesEquality(Box<Int32LeAndNotLtEqualityEvidence>),
    Int32GeAndNotGtImpliesEquality(Box<Int32GeAndNotGtEqualityEvidence>),
    PointerAlignment(Box<PointerAlignmentEvidence>),
    PointerWord(Box<PointerWordEvidence>),
    /// Constructor disjointness: an exact equality that identifies a
    /// symbolic value with one constructor makes it unequal to a different
    /// constructor of the same algebraic type.
    AlgebraicConstructorNoConfusion(Box<Proposition>),
    Legacy,
}

/// What one premise says about which variant a symbolic model value has.
///
/// `Excluded` comes from a disequality against a field-free constructor, the
/// only disequality that rules a whole variant out: `model != Some(3)` leaves
/// `Some` possible. `Witnessed` comes from an existential equality such as
/// `exists (v) { model == Some(v) }`, which names the variant without naming
/// its fields.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum AlgebraicVariantEvidenceKind {
    Excluded,
    Witnessed,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct AlgebraicVariantEvidence {
    pub kind: AlgebraicVariantEvidenceKind,
    pub variant: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) enum AtomicConnectionKey {
    Variable(Variable),
    Block(PointerBlock),
}

/// One immutable fact shared by every dependency bucket that names it.
#[derive(Clone, Debug)]
pub(crate) struct SharedIndexFact<T>(std::sync::Arc<T>);

impl<T> SharedIndexFact<T> {
    pub(crate) fn new(value: T) -> Self {
        Self(std::sync::Arc::new(value))
    }
}
impl<T> AsRef<T> for SharedIndexFact<T> {
    fn as_ref(&self) -> &T {
        &self.0
    }
}
impl<T> std::borrow::Borrow<T> for SharedIndexFact<T> {
    fn borrow(&self) -> &T {
        self.as_ref()
    }
}
impl<T: Ord> PartialEq for SharedIndexFact<T> {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}
impl<T: Ord> Eq for SharedIndexFact<T> {}
impl<T: Ord> PartialOrd for SharedIndexFact<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl<T: Ord> Ord for SharedIndexFact<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if std::sync::Arc::ptr_eq(&self.0, &other.0) {
            std::cmp::Ordering::Equal
        } else {
            self.as_ref().cmp(other.as_ref())
        }
    }
}

/// Borrowed adjacency entries let selection deduplicate before cloning syntax.
pub(crate) enum AtomicConnectedFact<'a> {
    Condition(&'a ConditionTerm, bool),
    Proposition(&'a Proposition),
}
impl AtomicConnectedFact<'_> {
    pub(crate) fn identity(&self) -> (u8, usize) {
        match self {
            Self::Condition(condition, _) => (0, *condition as *const ConditionTerm as usize),
            Self::Proposition(proposition) => (1, *proposition as *const Proposition as usize),
        }
    }
    pub(crate) fn is_condition(&self) -> bool {
        matches!(
            self,
            Self::Condition(..) | Self::Proposition(Proposition::ConditionIs(..))
        )
    }
    pub(crate) fn matches(&self, goal: &Proposition) -> bool {
        match self {
            Self::Condition(condition, value) => {
                matches!(goal, Proposition::ConditionIs(c,v) if c == *condition && v == value)
            }
            Self::Proposition(proposition) => *proposition == goal,
        }
    }
    pub(crate) fn to_proposition(&self) -> Proposition {
        match self {
            Self::Condition(condition, value) => {
                Proposition::ConditionIs((*condition).clone(), *value)
            }
            Self::Proposition(proposition) => (*proposition).clone(),
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(super) struct AtomicConnectionFacts {
    pub conditions: crate::persistent::PersistentSet<SharedIndexFact<Proposition>>,
    pub propositions: crate::persistent::PersistentSet<SharedIndexFact<Proposition>>,
}

/// The representation and deferral choices a context reasons under, one bit
/// each. The bits occupy the top nine bits of the content fingerprint.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub(super) struct ReasoningPolicy(u16);

impl ReasoningPolicy {
    pub(super) const DEFER_NON_EXACT_LOADABILITY_OBLIGATIONS: Self = Self(1 << 0);
    pub(super) const DEFER_NON_EXACT_CONDITION_REASONING: Self = Self(1 << 1);
    pub(super) const PREFER_SYMBOLIC_EXTERNAL_LOADS: Self = Self(1 << 2);
    pub(super) const FORCE_SYMBOLIC_EXTERNAL_LOADS: Self = Self(1 << 3);
    pub(super) const ALLOW_SYMBOLIC_CONTRACT_LOADS: Self = Self(1 << 4);
    pub(super) const TRANSPORT_MEMORY_LOAD_CONDITION_FACTS: Self = Self(1 << 5);
    /// Select alias normalization for loads captured by pure functions.
    /// This affects representation only, never validity obligations.
    pub(super) const KEEP_SPEC_LOADS_SYMBOLIC: Self = Self(1 << 6);
    pub(super) const REQUIRE_OWNED_EXPRESSION_LOADS: Self = Self(1 << 7);

    pub(super) const OBSERVE_POINTER_ADDRESSES: Self = Self(1 << 8);

    pub(super) fn contains(self, choice: Self) -> bool {
        self.0 & choice.0 != 0
    }

    pub(super) fn fingerprint(self) -> u64 {
        (u64::from(self.0 & 0xff) << 56) | (u64::from(self.0 >> 8) << 55)
    }

    pub(super) fn toggle(&mut self, choice: Self) {
        self.0 ^= choice.0;
    }
}

#[derive(Clone, Debug, Default)]
pub struct PureFactContext {
    /// Shared ordered projection used when checked paths publish this context.
    pub(super) execution_fact_projection: super::execution_facts::ContextFacts,
    /// Persistent syntax adjacency for atomic certificate planning. Unlike
    /// free-variable indexes, this never scans snapshot contents.
    pub(super) atomic_connection_facts:
        crate::persistent::PersistentMap<AtomicConnectionKey, AtomicConnectionFacts>,
    pub(super) atomic_ground_facts: crate::persistent::PersistentSet<SharedIndexFact<Proposition>>,
    pub(super) atomic_quantified_facts:
        crate::persistent::PersistentSet<SharedIndexFact<Proposition>>,
    /// True 64-bit equalities as an undirected adjacency map, derived
    /// incrementally from `condition_facts`. Unchanged branches share it;
    /// inserting an equality updates only its two endpoints.
    pub(super) bitvector64_equality_facts: crate::persistent::PersistentMap<
        Bitvector32Term,
        crate::persistent::PersistentMap<Bitvector32Term, ConditionTerm>,
    >,
    pub(super) condition_facts: crate::persistent::PersistentMap<ConditionTerm, bool>,
    pub(super) signed_variable_chains: super::assumptions::variable_chains::VariableChains,
    /// Incremental adjacency for conditions whose variables can be read
    /// without inspecting a snapshot.
    pub(super) condition_facts_by_variable: crate::persistent::PersistentMap<
        Variable,
        crate::persistent::PersistentMap<SharedIndexFact<ConditionTerm>, bool>,
    >,
    /// Snapshot-dependent conditions use the complete collector only when
    /// smart premise selection asks for them. Scalar updates share the cache.
    pub(super) snapshot_condition_variable_base: crate::persistent::PersistentMap<
        Variable,
        crate::persistent::PersistentMap<SharedIndexFact<ConditionTerm>, bool>,
    >,
    pub(super) snapshot_condition_variable_changes:
        crate::persistent::PersistentMap<ConditionTerm, Option<bool>>,
    pub(super) snapshot_condition_variables: std::sync::Arc<
        std::sync::OnceLock<
            crate::persistent::PersistentMap<
                Variable,
                crate::persistent::PersistentMap<SharedIndexFact<ConditionTerm>, bool>,
            >,
        >,
    >,
    /// The condition facts `condition_matches` can relate to a query spelled
    /// differently, keyed by their kind and the canonical forms of their two
    /// sides (`condition_match_key`): an equality under its unordered pair of
    /// sides, a signed order under its strictness and its lower and upper
    /// side, whichever way it was written. Any other fact matches a query
    /// only when it is that query, which is the exact lookup. A query then
    /// reads the keys its own sides and their recorded-equality classes
    /// spell, so `has_condition_fact` never visits an unrelated fact.
    /// Derived incrementally from `condition_facts`.
    pub(super) condition_facts_by_sides: crate::persistent::PersistentMap<
        ConditionMatchKey,
        crate::persistent::PersistentMap<ConditionTerm, bool>,
    >,
    /// The facts of `condition_facts_by_sides` with a side that is not an
    /// atom (a constant, or a variable that no load names): a load, a sum,
    /// a conditional. `condition_matches` can prove such a side equal to a
    /// query side by reasoning its key does not spell (a load's stored
    /// value, additive rearrangement), so a query that misses every key
    /// still asks these. A fact of two atoms is matched only through its
    /// key.
    /// Keyed by the family of kinds that can match one another
    /// (`condition_match_family`).
    pub(super) open_condition_facts:
        crate::persistent::PersistentMap<u8, crate::persistent::PersistentMap<ConditionTerm, bool>>,
    /// The signed-order condition facts (`<`, `<=`, `>`, `>=`, either
    /// value) of `condition_facts`, in its order: what
    /// `condition_order_facts` collects, so collecting reads only order
    /// facts instead of every condition fact. Derived incrementally with
    /// the condition-match indexes.
    pub(super) order_condition_facts: crate::persistent::PersistentMap<ConditionTerm, bool>,
    /// True `Bitvector32Equal` and `Bitvector64Equal` facts that pin a term
    /// to a constant, keyed by that term and carrying, per fact, the constant
    /// it names. Derived incrementally from `condition_facts`; ordered by
    /// fact so the first entry is the one a scan of `condition_facts` in its
    /// own order would find (`exact_signed_constant`).
    /// The equality classes of the true `Bitvector32Equal` facts, each with
    /// the constant its members are proved to denote. Derived incrementally
    /// from `condition_facts`, so a term's constant after equality
    /// normalization is a class lookup rather than a walk over every fact
    /// the term is connected to.
    pub(super) constant_classes: super::assumptions::ConstantClasses,
    /// True int32 equalities filed under their exact written endpoints.
    /// Fact order preserves the direct constant walk's deterministic choice;
    /// no memory canonicalization, pointer-offset edges, or arithmetic folding.
    pub(super) direct_bitvector_equalities: crate::persistent::PersistentMap<
        Bitvector32Term,
        crate::persistent::PersistentMap<ConditionTerm, Bitvector32Term>,
    >,
    pub(super) exact_constant_equalities: crate::persistent::PersistentMap<
        Bitvector32Term,
        crate::persistent::PersistentMap<ConditionTerm, i64>,
    >,
    /// What an exact fact says about the null-ness of a pointer, keyed by
    /// that pointer's offset term and carrying the block the fact named
    /// together with the fact itself. Derived incrementally from
    /// `condition_facts`: every equality against the null pointer files its
    /// other side here. A comparison of two pointers in one block is a
    /// `PointerOffsetEqual` that no longer names the block, so this index is
    /// what lets "one of these is null and the other is not" be two keyed
    /// lookups instead of a scan. The conclusion is about the offset terms
    /// alone: if `B + left` is null and `B + right` is not, then `left` and
    /// `right` are different offsets whatever block the query came from.
    pub(super) null_pointer_offsets: crate::persistent::PersistentMap<
        PointerOffsetTerm,
        crate::persistent::PersistentMap<(PointerBlock, bool), ConditionTerm>,
    >,
    /// Exact equalities between two pointers of *different* blocks, indexed
    /// under each side and carrying the fact that states them. An equality
    /// inside one block is a `PointerOffsetEqual` that never reaches this
    /// index (`ConditionTerm::pointer_equal`), so an entry here always says
    /// that two block spellings name one address. Derived incrementally from
    /// `condition_facts`, like every other index above, so asking what one
    /// pointer is proved equal to is a keyed lookup rather than a scan of
    /// every pointer comparison the path happens to hold.
    /// Original alignment premises, retained for graph reconstruction only.
    pub(super) pointer_alignment_facts: crate::persistent::PersistentMap<(Pointer, u64), ()>,
    pub(super) pointer_block_aliases: crate::persistent::PersistentMap<
        Pointer,
        crate::persistent::PersistentMap<Pointer, ConditionTerm>,
    >,
    /// The keys of `pointer_block_aliases` again, filed under each
    /// pointer's offset term. A same-block comparison names only its two
    /// offsets, so this is what recovers, by one keyed lookup, the block
    /// spellings an offset was proved equal to across blocks.
    pub(super) pointer_block_aliases_by_offset: crate::persistent::PersistentMap<
        PointerOffsetTerm,
        crate::persistent::PersistentSet<Pointer>,
    >,
    /// Trusted persistent equality closure for pointers, offsets, and int32
    /// terms. Appended on insertion; withdrawal rebuilds from exact equality
    /// indexes, preserving the remaining support in every fragment.
    pub(super) equality_graph: super::equality_graph::EqualityGraph,
    pub(super) congruence_conditions: crate::persistent::PersistentMap<ConditionTerm, bool>,
    /// Exact defining equations for pointer-typed reads issued on this path,
    /// indexed by their load variable. Producer metadata certifies the C
    /// value's type; the equation supplies its snapshot and address. Both
    /// are required before a graph query may use the read as a bridge.
    pub(super) typed_pointer_read_definitions: crate::persistent::PersistentMap<
        Variable,
        crate::persistent::PersistentMap<((u32, u32), Pointer), (Pointer, SharedCMemory)>,
    >,
    pub(super) uint64_graph_equalities: crate::persistent::PersistentMap<
        (
            super::equality_graph::MachineAtom,
            super::equality_graph::MachineAtom,
        ),
        usize,
    >,
    /// Counts exact int32 premises supporting each canonical oriented edge.
    /// Several spellings can support one edge; withdrawal removes one support.
    pub(super) int32_graph_equalities: crate::persistent::PersistentMap<
        (
            super::equality_graph::MachineAtom,
            super::equality_graph::MachineAtom,
        ),
        usize,
    >,
    /// Normalized same-block pointer equalities, indexed under each offset.
    pub(super) pointer_offset_aliases: crate::persistent::PersistentMap<
        PointerOffsetTerm,
        crate::persistent::PersistentSet<PointerOffsetTerm>,
    >,
    /// `pointer_offset_aliases` again, keyed by the alias offset's root atom
    /// (`resource_algebra::offset_root_atom`).
    pub(super) pointer_offset_aliases_by_root: crate::persistent::PersistentMap<
        Option<PointerOffsetTerm>,
        crate::persistent::PersistentSet<(PointerOffsetTerm, PointerOffsetTerm)>,
    >,
    /// Addresses of the first elements of two separated memory ranges of
    /// one block, keyed by the unordered pair and carrying the separation
    /// facts that state it. Mirrors `memory_separation_facts` under a key a
    /// pointer comparison can build. Each range holds the element at its own
    /// anchor, so two separated ranges cannot share one anchor -- again a
    /// statement about the offset terms alone, whatever block the comparison
    /// came from. Two owned members of a held composition are asked the same
    /// question of the composition's own anchor index
    /// (`ResourceContext::separates_owned_anchors`).
    pub(super) separated_anchor_offsets: crate::persistent::PersistentMap<
        (PointerOffsetTerm, PointerOffsetTerm),
        crate::persistent::PersistentSet<Proposition>,
    >,
    /// Exact signed-order bounds keyed by either endpoint — under the term
    /// the fact wrote and, when different, its canonical form as an alias.
    /// Each entry carries the fact's own endpoint term first, so evidence
    /// found through the alias can still cite the exact fact. Counts
    /// preserve equivalent condition terms when one source fact is replaced.
    pub(super) signed_order_bounds: crate::persistent::PersistentMap<
        Bitvector32Term,
        crate::persistent::PersistentMap<(Bitvector32Term, Bitvector32Term, bool, bool), usize>,
    >,
    /// The `int64` counterpart of `signed_order_bounds`, maintained by the
    /// same insert and remove path over `Bitvector64Signed*` order facts. It
    /// is kept separate so an `int64` bound is never read as an int32 one.
    pub(super) int64_signed_order_bounds: crate::persistent::PersistentMap<
        Bitvector32Term,
        crate::persistent::PersistentMap<(Bitvector32Term, Bitvector32Term, bool, bool), usize>,
    >,
    /// Unsigned 64-bit order facts indexed by either endpoint. This keeps
    /// slice-index range transport proportional to the queried order chain.
    pub(super) uint64_order_bounds: crate::persistent::PersistentMap<
        Bitvector32Term,
        crate::persistent::PersistentMap<(Bitvector32Term, Bitvector32Term, bool, bool), usize>,
    >,
    /// The 64-bit order facts again, split by direction for the chain walk:
    /// for each kind (`[unsigned, signed]`) and each direction (`[upward,
    /// downward]`), the canonical far ends of the facts leaving a canonical
    /// term in that direction, with whether the fact is strict. A walk reads
    /// only the edges it can follow, so a bound many indices share, `n` under
    /// `c0 < n`, `c1 < n`, ..., costs an upward walk through it nothing for
    /// the facts below it. Derived from the two indexes above by the same
    /// insert and remove path.
    pub(super) wide_order_edges: [[crate::persistent::PersistentMap<
        Bitvector32Term,
        crate::persistent::PersistentMap<(Bitvector32Term, bool), usize>,
    >; 2]; 2],
    /// Condition facts containing a memory-load atom, indexed by the loaded
    /// pointer's snapshot-blind structural fingerprint. This is derived from
    /// `condition_facts`; it narrows snapshot-aware load-form checks
    /// without deciding them.
    pub(super) memory_load_condition_facts:
        std::sync::Arc<std::sync::OnceLock<BTreeMap<(PointerBlock, u64), BTreeSet<ConditionTerm>>>>,
    /// True bitvector and int32-scaled pointer-offset equalities, indexed as
    /// an undirected adjacency graph whose edges retain one exact source
    /// proposition. Memory-load vertices use their
    /// assumption-free canonical memory-load term. Derived lazily from
    /// `condition_facts` and shared by unchanged clones.
    pub(super) bitvector_equality_facts: std::sync::Arc<
        std::sync::OnceLock<BTreeMap<Bitvector32Term, BTreeMap<Bitvector32Term, Proposition>>>,
    >,
    /// A persistent set: a context is cloned and extended by one fact at
    /// each lowering path and planning probe, so an extension must copy
    /// only a search path, not the whole set.
    pub(super) prop_facts: imbl::OrdSet<Proposition>,
    /// Alpha/load identity index for propositions that may be stated as a
    /// call requirement.  The key retains memory epochs and canonicalizes
    /// only binders; the persistent buckets keep updates local to one key.
    /// A context built in bulk from a fact list defers the keys until the
    /// index is first asked for (see `StatedPropositionIndex`).
    pub(super) stated_proposition_index: super::assumptions::StatedPropositionIndex,
    /// Nominal function-contract witnesses keyed by the exact pointer value.
    /// This keeps indirect-call lookup proportional to contracts explicitly
    /// known for that pointer, never to project-wide declarations.
    pub(super) function_contract_facts:
        std::sync::Arc<BTreeMap<Pointer, BTreeMap<String, Proposition>>>,
    /// Derived candidates for checked function-read transport, selected by
    /// the immutable complete read's exact cell address.
    pub(super) function_contract_read_cells:
        crate::persistent::PersistentMap<Pointer, crate::persistent::PersistentMap<Pointer, ()>>,
    /// Exact equalities between two applications of one algebraic
    /// constructor, indexed by each field equality they entail. Both levels
    /// are persistent so adding one proof fact changes logarithmically many
    /// nodes instead of cloning an ambient fact table.
    pub(super) algebraic_constructor_field_equalities: crate::persistent::PersistentMap<
        Proposition,
        crate::persistent::PersistentMap<(Proposition, usize), ()>,
    >,
    /// Exact equalities between distinct checked constructors. Any such fact
    /// makes the context inconsistent by constructor disjointness.
    pub(super) algebraic_constructor_conflicts: crate::persistent::PersistentMap<Proposition, ()>,
    /// Direct constructor evidence indexed by the symbolic value it describes.
    pub(super) algebraic_variable_constructors: crate::persistent::PersistentMap<
        Variable,
        crate::persistent::PersistentMap<Proposition, AlgebraicTerm>,
    >,
    /// Weaker constructor evidence indexed by the symbolic value it describes:
    /// a premise that rules one variant out, or one that witnesses a variant
    /// without naming its fields. Arm selection reads only the entries for the
    /// value it decides, so a section with many unrelated premises costs what
    /// a section with none costs.
    pub(super) algebraic_variable_variant_evidence: crate::persistent::PersistentMap<
        Variable,
        crate::persistent::PersistentMap<Proposition, AlgebraicVariantEvidence>,
    >,
    /// Premises that fix the value of a pure function applied to a symbolic
    /// algebraic value, indexed by that value. Arm refutation reads only the
    /// entries for the model it decides, so a section with many unrelated
    /// predicate facts costs what a section with none costs.
    pub(super) algebraic_variable_predicate_facts:
        crate::persistent::PersistentMap<Variable, crate::persistent::PersistentSet<Proposition>>,
    /// Exact disjunctive proposition facts. This derived index keeps bounded
    /// case search proportional to possible case splits rather than every
    /// unrelated proposition in the context.
    pub(super) disjunction_facts: std::sync::Arc<BTreeSet<Proposition>>,
    pub(super) resource_compositions: std::sync::Arc<BTreeSet<ResourceContext>>,
    /// Derived provenance-only footprints published with each explicitly
    /// admitted composition. This is not consumable resource authority.
    pub(super) composition_object_resources: memory_equality_index::ObjectEvidenceSources,
    pub(super) memory_read_defined_facts: crate::persistent::PersistentMap<
        (Pointer, CType),
        crate::persistent::PersistentSet<Proposition>,
    >,
    pub(super) memory_loadable_facts: std::sync::Arc<BTreeMap<PointerBlock, BTreeSet<Proposition>>>,
    /// Loadability facts keyed by the C object identity carried by their
    /// base. Pointer provenance queries use this persistent index instead of
    /// scanning every external-argument fact, whose physical block is shared
    /// by all pointer parameters.
    pub(super) memory_loadable_object_facts:
        crate::persistent::PersistentMap<Pointer, crate::persistent::PersistentSet<Proposition>>,
    pub(super) memory_loadable_shape_facts:
        std::sync::Arc<std::sync::OnceLock<BTreeMap<(PointerBlock, u64), BTreeSet<Proposition>>>>,
    pub(super) memory_separation_facts: std::sync::Arc<
        BTreeMap<(PointerBlock, PointerBlock), Vec<(Proposition, CMemoryRange, CMemoryRange)>>,
    >,
    /// Separation facts the block-pair index cannot serve: at least one
    /// side is a non-memory resource whose containment may still entail a
    /// memory separation through its body. Kept small and scanned
    /// linearly; memory-memory facts live in the index above instead.
    pub(super) nonmemory_separation_facts: std::sync::Arc<Vec<Proposition>>,
    pub(super) content_fingerprint: u64,
    pub(super) reasoning_policy: ReasoningPolicy,
}

impl PartialEq for PureFactContext {
    fn eq(&self, other: &Self) -> bool {
        self.content_fingerprint == other.content_fingerprint
            && self.condition_facts == other.condition_facts
            && self.typed_pointer_read_definitions == other.typed_pointer_read_definitions
            && self.prop_facts == other.prop_facts
            && self.resource_compositions == other.resource_compositions
            && self.reasoning_policy == other.reasoning_policy
    }
}

impl Eq for PureFactContext {}

impl std::hash::Hash for PureFactContext {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.content_fingerprint);
    }
}

#[derive(Clone, Debug)]
pub struct ProofObligation {
    pub(super) proposition: Proposition,
    pub(super) context: Option<String>,
    pub(super) assumable: bool,
    /// Source identity for a required call precondition, when this
    /// obligation was emitted while applying a selected callee contract.
    /// This is planning metadata only and is excluded from obligation
    /// equality, hashing, and ordering just like lowering introductions.
    pub(super) call_requirement_site: Option<std::sync::Arc<CallRequirementSource>>,
    /// The head chain the lowering that built `proposition` recorded for it,
    /// outermost first, when the kernel built this obligation from a lowered
    /// specification proposition.
    ///
    /// Lowering wraps an obligation in `Implies` nodes that no Surface
    /// connective wrote. A consumer that introduces the head of this
    /// obligation reads the chain instead of guessing from the shape the
    /// written syntax happens to share. `None` is the unrecorded state: an
    /// obligation the kernel built with no lowering of its own.
    pub(super) introductions: Option<Arc<super::LoweringIntroductions>>,
}

/// Provenance describes the proposition; it never distinguishes two
/// obligations. Comparison, ordering, and hashing therefore read the
/// checked fields only, so an obligation carrying a recorded chain still
/// deduplicates against the same obligation built without one.
impl PartialEq for ProofObligation {
    fn eq(&self, other: &Self) -> bool {
        self.proposition == other.proposition
            && self.context == other.context
            && self.assumable == other.assumable
    }
}

impl Eq for ProofObligation {}

impl Hash for ProofObligation {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.proposition.hash(state);
        self.context.hash(state);
        self.assumable.hash(state);
    }
}

impl Ord for ProofObligation {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.proposition
            .cmp(&other.proposition)
            .then_with(|| self.context.cmp(&other.context))
            .then_with(|| self.assumable.cmp(&other.assumable))
    }
}

impl PartialOrd for ProofObligation {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ExecutionPureFact {
    pub(super) proposition: Proposition,
    pub(super) public: bool,
    pub(super) certified: bool,
    /// A value equation derived by a logical read, not a condition selecting
    /// an evaluation path. It travels with the result's existing premises.
    pub(super) logical_read_equation: bool,
    /// Set on the memory summary a checked interface join produced from its
    /// arms' own checked effects. See
    /// [`ExecutionPureFact::certified_join_summary`].
    pub(super) join_summary: bool,
    pub(super) certified_store: Option<Box<CertifiedMemoryStore>>,
    pub(super) transport: Option<Box<CertifiedExecutionFactTransport>>,
    /// Exact producer metadata for a kernel-minted load variable.  This is
    /// carried with the certified fact rather than recovered from the current
    /// state, since the producer's snapshot and pointer are the authority.
    pub(super) generated_load_binding: Option<Box<GeneratedLoadBinding>>,
    pub(super) generated_load_source_events: GeneratedLoadSourceEvents,
}

/// Source events are execution provenance, not part of the proposition's
/// semantic identity. Keep them beside the fact while making fact equality
/// and hashing remain proposition-oriented.
#[derive(Clone, Debug, Default)]
pub(crate) struct GeneratedLoadSourceEvents(Vec<GeneratedLoadSourceEvent>);

impl GeneratedLoadSourceEvents {
    pub(crate) fn as_slice(&self) -> &[GeneratedLoadSourceEvent] {
        &self.0
    }

    pub(crate) fn push(&mut self, event: GeneratedLoadSourceEvent) {
        self.0.push(event);
    }
}

impl PartialEq for GeneratedLoadSourceEvents {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl Eq for GeneratedLoadSourceEvents {}

impl std::hash::Hash for GeneratedLoadSourceEvents {
    fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {}
}

impl Ord for GeneratedLoadSourceEvents {
    fn cmp(&self, _other: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

impl PartialOrd for GeneratedLoadSourceEvents {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// The source-independent identity of one kernel-generated load equation.
/// Consumers must use the complete `(variable, snapshot, pointer)` key; the
/// source expression is retained only as the exact equation operand produced
/// by the kernel.  A variable-level tombstone is represented by
/// [`GeneratedLoadBinding::Ambiguous`] when one path observes incompatible
/// bindings for the same variable.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) enum GeneratedLoadBinding {
    Exact {
        variable: Variable,
        snapshot: CMemorySnapshotIdentity,
        pointer: Pointer,
        load: Bitvector32Term,
        /// The C value produced by a completed, nonvolatile pointer read.
        /// Scalar and volatile reads have no pointer bridge.
        typed_pointer_value: Option<Pointer>,
        /// The current cell read by a checked resource-index expression.
        /// Its cached value can retain an older defining load.
        observed_pointer_read: Option<(SharedCMemory, Pointer)>,
    },
    Ambiguous {
        variable: Variable,
    },
}

/// The source-side identity of one generated load occurrence.  This is kept
/// kernel-private and deliberately carries no parser or surface types: a
/// frontend lowering may assign an owner and an occurrence number, while proof
/// presentation only compares the opaque identity it receives.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct LoadSourceId {
    pub(crate) owner: LoadSourceOwnerId,
    pub(crate) occurrence: u32,
}

/// Stable owner identity for source load occurrences.  The source unit and
/// function names are diagnostic/source-plan data, not part of any kernel
/// proposition or semantic expression identity.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct LoadSourceOwnerId {
    pub(crate) source_unit: Arc<str>,
    pub(crate) function: Arc<str>,
}

/// One producer observation pairing a source occurrence with the exact
/// source-neutral binding minted by the kernel.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct GeneratedLoadSourceEvent {
    source: LoadSourceId,
    binding: GeneratedLoadBinding,
}

impl GeneratedLoadSourceEvent {
    /// Construct an event from one exact producer observation. Ambiguity is a
    /// property of the persistent resolution store, never an operation that
    /// execution can claim to have observed at one source occurrence.
    pub(crate) fn new(source: LoadSourceId, binding: GeneratedLoadBinding) -> Option<Self> {
        matches!(binding, GeneratedLoadBinding::Exact { .. }).then_some(Self { source, binding })
    }
    #[cfg(test)]
    pub(crate) fn source(&self) -> &LoadSourceId {
        &self.source
    }

    pub(crate) fn binding(&self) -> &GeneratedLoadBinding {
        &self.binding
    }

    pub(crate) fn variable(&self) -> Variable {
        match &self.binding {
            GeneratedLoadBinding::Exact { variable, .. } => *variable,
            GeneratedLoadBinding::Ambiguous { .. } => {
                unreachable!("generated-load source events are constructed only for exact mints")
            }
        }
    }
}

/// Persistent proof-presentation resolution for one generated load variable.
/// A conflicting observation is a permanent tombstone: later consumers must
/// not guess which source occurrence was intended.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) enum GeneratedLoadSourceResolution {
    Unique(GeneratedLoadSourceEvent),
    Ambiguous { variable: Variable },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CertifiedExecutionFactTransport {
    pub(super) source: Proposition,
    pub(super) theorem: Theorem,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) struct CertifiedMemoryStore {
    pub(super) before: CMemory,
    pub(super) after: CMemory,
    pub(super) pointer: Pointer,
    pub(super) value: CValue,
    pub(super) authorized_range: Option<CMemoryRange>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicCExecution {
    pub(super) paths: Vec<SymbolicCExecutionPath>,
    pub(super) limit: Option<ExecutionLimit>,
}

/// One complete path set contract certification may judge a claim over: a
/// checked execution reused at the contract's entry, or the kernel's own
/// execution when no artifact was supplied. Its paths jointly cover the function from the
/// entry they name, so a claim that holds on every one of them holds.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CContractPathSet {
    /// Parallel to `paths`: provenance minted by the exhaustive kernel
    /// resource-case checker, never supplied by a source proof.
    pub(super) checked_resource_guard_cases: Vec<Arc<super::api::CCheckedResourceGuardCase>>,
    pub(super) paths: Vec<SymbolicCExecutionPath>,
    /// Exact resource claims checked for each path.  The vector is parallel
    /// to `paths`; an entry names only claims whose surface proof crossed the
    /// kernel resource/lifetime checker for that path.
    pub(super) checked_resource_claims: Vec<Vec<CFunctionContractClaimKey>>,
    pub(super) checked_resource_transitions: Vec<bool>,
    /// Paths whose contract exit resource transition was deferred because a
    /// conditional produced effect was not decided by the proof entry facts.
    /// Contract certification must resolve these paths under an exhaustive
    /// guard case before using their post-state.
    pub(super) deferred_contract_exits: Vec<bool>,
    /// Exact boundary error retained for each deferred path. A deferred marker
    /// is valid only when this records the conditional-effect selection error
    /// that caused the deferral.
    pub(super) deferred_contract_exit_errors: Vec<Option<CRuntimeError>>,
    /// Resource facts independently checked by the surface proof for each
    /// path. Deferred exit resolution composes these facts into the body
    /// outcome before applying the remaining conditional boundary effect.
    pub(super) checked_returned_resources: Vec<ResourceContext>,
    /// The caller state the reused artifact's proof ran at, when its paths
    /// were rebased onto this contract's caller state. A claim the proof
    /// completed at that state certifies the rebased path: the rebase
    /// checked the two entry representations definitionally equal.
    pub(super) completion_origin_state: Option<CState>,
    /// Authenticated entry custody for each path, including partitioned proofs.
    pub(super) boundary_transfers:
        Vec<Option<Arc<super::functions::CheckedBoundaryResourceTransfer>>>,
}

/// A complete function frontier produced from only the exact function's
/// contract entry state and requirements.
///
/// Unlike [`SymbolicCExecution`], this type is accepted as evidence when
/// certifying an opaque function rule. Its fields are kernel-private so callers
/// cannot turn an execution performed under arbitrary assumptions into
/// contract evidence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CFunctionContractExecution {
    /// One entry per resource-guard case of the contract, each listing every
    /// path set available for that case. A claim holds when, in every case,
    /// one path set certifies it on all of its paths: each set is a complete
    /// execution of the function under the case, so any one is authority for
    /// it. The sets differ only in how the proofs that produced them
    /// structured the paths (a proof that joins two arms publishes the
    /// joined path; another publishes each arm), and a claim completed on
    /// one proof's outcome is matched against that proof's paths.
    pub(super) cases: Vec<Vec<CContractPathSet>>,
    /// Why certification produced no paths: either no supplied checked
    /// artifact could be reused, or the contract entry context itself could
    /// not be built. Callers report it; it carries no authority.
    pub(super) reuse_diagnostic: Option<String>,
    /// The entry premise the contract context could not authorize, when that
    /// is why reuse was refused. The kernel names its *kind* in
    /// `reuse_diagnostic`; a reader needs the premise itself to know which
    /// fact is missing, and only the caller can spell it in the user's names.
    /// It carries no authority either — it is the refused premise, not a
    /// granted one.
    pub(super) reuse_unauthorized_premise: Option<Proposition>,
    /// The resources the contract entry held where that premise was refused.
    /// A refused loadability premise is a claim about these, so a reader
    /// needs them beside it to see which range the premise fell outside.
    pub(super) reuse_entry_resources: Vec<CResourceFact>,
    /// The pure facts of the contract context that premise was refused in:
    /// what it was checked against.
    pub(super) reuse_context_facts: Vec<Proposition>,
    pub(super) checked_call_events: super::proof::CheckedCallEvents,
    /// How this certification ran the function's loops. Under
    /// `ApplyVerifiedRules` a loop is either run concretely to its exit or
    /// replaced by a verified loop rule, and one with neither yields no
    /// paths; under `Verify` an annotated loop may be summarized without
    /// ever exiting. The termination check reads this to know which.
    pub(super) loop_semantics: CLoopSemantics,
    /// The user-defined tactics the certified proofs applied.
    pub(super) applied_tactics: std::collections::BTreeSet<String>,
    /// Complete conservative call dependencies from kernel-checked execution.
    /// None retains source-call analysis; a present empty set proves no calls.
    /// Shared across claims and certificate reuse, never copied per step.
    pub(super) checked_callees: Option<Arc<BTreeSet<String>>>,
}

/// A kernel-created record of one exact whole-function execution judgment.
///
/// Callers may retain and present this artifact, but cannot manufacture or
/// alter its execution metadata. Before reusing its checked frontier,
/// contract certification checks that the contract entry states each of this
/// artifact's assumptions: the proof started from that entry, so the check
/// is a lookup, and what it can refuse is an entry case the proof assumed
/// without covering the others.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CCheckedFunctionExecution {
    pub(super) state: CState,
    pub(super) function: CFunction,
    pub(super) arguments: Vec<CExpression>,
    pub(super) assumptions: PureFactContext,
    pub(super) environment: CExecutionEnvironment,
    pub(super) execution_semantics: CExecutionSemantics,
    pub(super) mode: CFunctionContractExecutionMode,
    pub(super) execution: SymbolicCExecution,
    /// Exact resource claims checked for each execution path.  This is proof
    /// evidence, not a request to re-evaluate a resource transition during
    /// later contract certification.
    pub(super) checked_resource_claims: Vec<Vec<CFunctionContractClaimKey>>,
    pub(super) checked_resource_transitions: Vec<bool>,
    /// Paths whose contract exit resource transition was deferred because a
    /// conditional produced effect was not decided by the proof entry facts.
    /// Contract certification must resolve these paths under an exhaustive
    /// guard case before using their post-state.
    pub(super) deferred_contract_exits: Vec<bool>,
    /// Exact boundary error retained for each deferred path. A deferred marker
    /// is valid only when this records the conditional-effect selection error
    /// that caused the deferral.
    pub(super) deferred_contract_exit_errors: Vec<Option<CRuntimeError>>,
    /// Resource facts independently checked by the surface proof for each
    /// path. Deferred exit resolution composes these facts into the body
    /// outcome before applying the remaining conditional boundary effect.
    pub(super) checked_returned_resources: Vec<ResourceContext>,
    /// Original contract caller state when a kernel-checked proof entered C
    /// execution through a definitionally equal resource representation.
    pub(super) entry_representation_origin: Option<CState>,
    /// The user-defined tactics this execution's proof applied.
    pub(super) applied_tactics: std::collections::BTreeSet<String>,
    /// Complete conservative call dependencies from kernel-checked execution.
    /// None retains source-call analysis; a present empty set proves no calls.
    /// Shared across claims and certificate reuse, never copied per step.
    pub(super) checked_callees: Option<Arc<BTreeSet<String>>>,
    /// Original checked input selection; later certification must not rebuild it.
    pub(super) boundary_transfer: Option<Arc<super::functions::CheckedBoundaryResourceTransfer>>,
    pub(super) checked_call_events: super::proof::CheckedCallEvents,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CFunctionContractExecutionMode {
    VerifyLoops,
    ExecuteLoops,
}

impl CFunctionContractExecution {
    /// An empty certification that carries why it produced no paths. A
    /// diagnostic is not authority: the result is still empty and certifies
    /// nothing.
    pub(crate) fn failed(diagnostic: String) -> Self {
        Self {
            cases: Vec::new(),
            reuse_diagnostic: Some(diagnostic),
            reuse_unauthorized_premise: None,
            reuse_entry_resources: Vec::new(),
            reuse_context_facts: Vec::new(),
            checked_call_events: Default::default(),
            loop_semantics: CLoopSemantics::Verify,
            checked_callees: None,
            applied_tactics: Default::default(),
        }
    }

    /// Every path across every case and path set.
    pub fn path_count(&self) -> usize {
        self.cases.iter().flatten().map(|set| set.paths.len()).sum()
    }

    /// Whether every resource-guard case has a path set to judge claims
    /// over.
    pub(crate) fn is_complete(&self) -> bool {
        !self.cases.is_empty()
            && self
                .cases
                .iter()
                .all(|alternatives| !alternatives.is_empty())
    }

    pub(crate) fn cases(&self) -> &[Vec<CContractPathSet>] {
        &self.cases
    }

    /// Why certification produced no paths although checked artifacts were
    /// supplied: the premise kind or entry-state component that blocked
    /// reuse.
    pub fn reuse_diagnostic(&self) -> Option<&str> {
        self.reuse_diagnostic.as_deref()
    }

    /// The entry premise behind [`Self::reuse_diagnostic`], for a caller that
    /// can print it in the names the user wrote.
    pub fn reuse_unauthorized_premise(&self) -> Option<&Proposition> {
        self.reuse_unauthorized_premise.as_ref()
    }

    /// The contract entry resources [`Self::reuse_unauthorized_premise`] was
    /// refused against.
    pub fn reuse_entry_resources(&self) -> &[CResourceFact] {
        &self.reuse_entry_resources
    }

    /// The contract context's pure facts [`Self::reuse_unauthorized_premise`]
    /// was refused against.
    pub fn reuse_context_facts(&self) -> &[Proposition] {
        &self.reuse_context_facts
    }
}

impl CCheckedFunctionExecution {
    pub(crate) fn with_checked_resource_claims(
        &self,
        checked_resource_claims: Vec<Vec<CFunctionContractClaimKey>>,
    ) -> Self {
        let mut checked = self.clone();
        checked.checked_resource_claims = checked_resource_claims;
        checked
    }

    pub(crate) fn with_checked_resource_transitions(
        &self,
        checked_resource_transitions: Vec<bool>,
    ) -> Self {
        let mut checked = self.clone();
        checked.checked_resource_transitions = checked_resource_transitions;
        checked
    }

    pub(crate) fn with_checked_returned_resources(
        &self,
        checked_returned_resources: Vec<ResourceContext>,
    ) -> Self {
        let mut checked = self.clone();
        checked.checked_returned_resources = checked_returned_resources;
        checked
    }

    pub fn paths(&self) -> &[SymbolicCExecutionPath] {
        self.execution.paths()
    }

    pub(crate) fn function(&self) -> &CFunction {
        self.boundary_transfer
            .as_deref()
            .map_or(&self.function, |transfer| transfer.checked_function())
    }

    pub(crate) fn boundary_transfer(
        &self,
    ) -> Option<&Arc<super::functions::CheckedBoundaryResourceTransfer>> {
        self.boundary_transfer.as_ref()
    }

    pub(crate) fn function_arguments(&self) -> &[CExpression] {
        &self.arguments
    }

    /// A complete proof checked its returned resource units jointly on every path.
    pub(crate) fn has_checked_resource_transitions(&self) -> bool {
        !self.execution.paths.is_empty()
            && self.checked_resource_transitions.len() == self.execution.paths.len()
            && self
                .checked_resource_transitions
                .iter()
                .all(|checked| *checked)
    }

    /// The exact caller state used to enter this checked execution, when the
    /// proof recorded a checked function-entry boundary.  Surface
    /// certification reuses this identity instead of reconstructing a second
    /// resource occurrence/loan root.
    pub(crate) fn caller_state(&self) -> Option<&CState> {
        self.entry_representation_origin.as_ref()
    }

    /// Allocation return accounting reads borrowed inputs in the immutable
    /// checked entry snapshot, before C may mutate a pointer naming them.
    pub(crate) fn allocation_entry_state(&self) -> &CState {
        self.entry_representation_origin
            .as_ref()
            .unwrap_or(&self.state)
    }

    /// Whether two checked executions are the same, naming the first
    /// difference otherwise. Path theorems are compared premise by premise
    /// rather than through the derived equality, whose recursion over a long
    /// implication chain can exhaust a verification thread's stack.
    pub fn agrees_with(&self, other: &Self) -> Result<(), String> {
        fn same_proposition(left: &Proposition, right: &Proposition) -> Result<(), String> {
            let (mut left, mut right) = (left, right);
            let mut index = 0;
            loop {
                match (left, right) {
                    (
                        Proposition::Implies(left_premise, left_body),
                        Proposition::Implies(right_premise, right_body),
                    ) => {
                        if left_premise != right_premise {
                            return Err(format!("premise {index} differs"));
                        }
                        index += 1;
                        left = left_body;
                        right = right_body;
                    }
                    (Proposition::Implies(..), _) | (_, Proposition::Implies(..)) => {
                        return Err(format!(
                            "the theorems have different premise counts at {index}"
                        ));
                    }
                    (left, right) => {
                        return (left == right)
                            .then_some(())
                            .ok_or_else(|| "the theorem bodies differ".to_string());
                    }
                }
            }
        }
        if self.state != other.state {
            return Err("the caller states differ".to_string());
        }
        if self.function != other.function {
            return Err("the functions differ".to_string());
        }
        if self.arguments != other.arguments {
            return Err("the arguments differ".to_string());
        }
        if self.assumptions != other.assumptions {
            return Err("the assumptions differ".to_string());
        }
        if self.environment != other.environment {
            return Err("the environments differ".to_string());
        }
        if self.execution_semantics != other.execution_semantics || self.mode != other.mode {
            return Err("the execution semantics or modes differ".to_string());
        }
        if self.execution.limit != other.execution.limit {
            return Err("the limits differ".to_string());
        }
        if self.entry_representation_origin != other.entry_representation_origin {
            return Err(format!(
                "the entry representation origins differ: {} versus {}",
                self.entry_representation_origin.is_some(),
                other.entry_representation_origin.is_some()
            ));
        }
        // Entry capabilities carry custody authorization, rather than an
        // observable outcome. Independent checks may capture distinct receipts.
        if self.execution.paths.len() != other.execution.paths.len() {
            return Err(format!(
                "path counts differ: {} versus {}",
                self.execution.paths.len(),
                other.execution.paths.len()
            ));
        }
        for (index, (left, right)) in self
            .execution
            .paths
            .iter()
            .zip(&other.execution.paths)
            .enumerate()
        {
            if left.assumptions != right.assumptions {
                return Err(format!("path {index}: the assumptions differ"));
            }
            if left.facts != right.facts {
                // Counted, not dumped: the kernel has no source spelling of
                // a path fact, and a caller that needs the facts has both
                // executions in hand.
                let missing = right
                    .facts
                    .iter()
                    .filter(|fact| !left.facts.contains(fact))
                    .count();
                let extra = left
                    .facts
                    .iter()
                    .filter(|fact| !right.facts.contains(fact))
                    .count();
                return Err(format!(
                    "path {index}: the facts differ; {missing} of the other's facts are missing and {extra} are extra"
                ));
            }
            if left.effect_facts != right.effect_facts {
                return Err(format!("path {index}: the effect facts differ"));
            }
            if left.obligations != right.obligations {
                return Err(format!("path {index}: the obligations differ"));
            }
            if left.loan_evidence != right.loan_evidence {
                return Err(format!("path {index}: the loan evidence differs"));
            }
            same_proposition(left.theorem.proposition(), right.theorem.proposition())
                .map_err(|difference| format!("path {index}: {difference}"))?;
        }
        Ok(())
    }

    pub fn limit(&self) -> Option<ExecutionLimit> {
        self.execution.limit()
    }
}

#[derive(Clone, Debug)]
pub struct SymbolicCExecutionPath {
    /// The body outcome checked against a retained Proof trace before the
    /// same producer applies the contract exit rule. Ordinary symbolic paths
    /// have no separate proof-completion origin.
    pub(super) completion_origin: Option<CFunctionOutcome>,
    pub(super) assumptions: PureFactContext,
    /// The checked body context, retained by the Proof completion producer.
    /// It is available only after certification has checked the entry under
    /// `assumptions`. Legacy execution producers use the flat-fact fallback.
    pub(super) post_assumptions: Option<PureFactContext>,
    pub(super) facts: ExecutionFacts,
    pub(super) effect_facts: ExecutionFacts,
    pub(super) obligations: Vec<ProofObligation>,
    pub(super) theorem: Theorem,
    pub(super) loan_evidence: super::loans::CheckedLoanCallEvidenceSequence,
}

// Retaining a context changes neither a path's evidence nor its identity.
// Avoid comparing its complete persistent indexes just to compare paths.
impl PartialEq for SymbolicCExecutionPath {
    fn eq(&self, other: &Self) -> bool {
        self.completion_origin == other.completion_origin
            && self.assumptions == other.assumptions
            && self.facts == other.facts
            && self.effect_facts == other.effect_facts
            && self.obligations == other.obligations
            && self.theorem == other.theorem
            && self.loan_evidence == other.loan_evidence
    }
}

impl Eq for SymbolicCExecutionPath {}

/// An untrusted collection of checked function outcomes.
///
/// Candidates deliberately carry no [`Theorem`]. They become useful as proof
/// evidence only after a checked kernel execution independently reproduces the
/// same complete path frontier.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CFunctionExecutionCandidates {
    pub(super) data: std::sync::Arc<CFunctionExecutionCandidatesData>,
}

/// Immutable publication of one complete outcome frontier. Proof forks retain
/// this collection, rather than copying every sibling path and the source body.
#[derive(Debug)]
pub(super) struct CFunctionExecutionCandidatesData {
    pub(super) state: CState,
    pub(super) function: Arc<CFunction>,
    pub(super) arguments: Arc<Vec<CExpression>>,
    pub(super) paths: super::proof::PersistentVector<CFunctionExecutionCandidate>,
    pub(super) common_facts: Option<ExecutionFacts>,
}
impl PartialEq for CFunctionExecutionCandidatesData {
    fn eq(&self, other: &Self) -> bool {
        self.state == other.state
            && self.function == other.function
            && self.arguments == other.arguments
            && self.paths == other.paths
    }
}
impl Eq for CFunctionExecutionCandidatesData {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CFunctionExecutionCandidate {
    pub(super) data: Arc<CFunctionExecutionCandidateData>,
}

/// An immutable candidate record retained across distinct terminal frontiers.
/// Adding facts shares the original outcome and obligations as well as the
/// unchanged fact streams. This is untrusted publication, never a theorem.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CFunctionExecutionCandidateData {
    pub(super) outcome: Arc<CFunctionOutcome>,
    pub(super) facts: ExecutionFacts,
    pub(super) effect_facts: ExecutionFacts,
    /// Whether re-publication's public-then-private effect order is already
    /// retained. Derived only from the stored facts; carries no authority.
    pub(super) effects_public_first: bool,
    pub(super) obligations: Arc<Vec<ProofObligation>>,
    pub(super) loan_evidence: super::loans::CheckedLoanCallEvidenceSequence,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicCConditionEvaluation {
    pub(super) paths: Vec<SymbolicCConditionEvaluationPath>,
    pub(super) limit: Option<ExecutionLimit>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicCConditionEvaluationPath {
    pub(super) facts: ExecutionFacts,
    pub(super) obligations: Vec<ProofObligation>,
    pub(super) theorem: Theorem,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CExpressionPath {
    pub(super) outcome: CExpressionOutcome,
    pub(super) facts: ExecutionFacts,
    pub(super) obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CLValuePath {
    pub(super) outcome: CLValueOutcome,
    pub(super) facts: ExecutionFacts,
    pub(super) obligations: Vec<ProofObligation>,
}

/// Source correspondence describes a checked path without distinguishing
/// semantically identical paths. The empty form allocates nothing, and cloning
/// a loop path shares its output-sized mapping.
#[derive(Clone, Debug, Default)]
pub(super) struct LoopInvariantCorrespondence(
    pub(super) Option<std::sync::Arc<[(usize, Proposition)]>>,
);

impl PartialEq for LoopInvariantCorrespondence {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl Eq for LoopInvariantCorrespondence {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CStatementExecutionPath {
    /// Declaration-indexed source correspondence for this loop's checked exit.
    /// This is presentation metadata, never an additional assumption.
    pub(super) loop_invariant_correspondence: LoopInvariantCorrespondence,
    pub(super) outcome: CStatementOutcome,
    pub(super) facts: ExecutionFacts,
    pub(super) obligations: Vec<ProofObligation>,
    pub(super) loan_evidence: super::loans::CheckedLoanCallEvidenceSequence,
}

impl CStatementExecutionPath {
    /// A path with no loop-invariant correspondence and no loan evidence,
    /// which is every path not leaving a checked loop or a borrowing call.
    pub(super) fn new(
        outcome: CStatementOutcome,
        facts: ExecutionFacts,
        obligations: Vec<ProofObligation>,
    ) -> Self {
        Self {
            loop_invariant_correspondence: Default::default(),
            outcome,
            facts,
            obligations,
            loan_evidence: super::loans::empty_checked_loan_evidence_sequence(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CFunctionPath {
    pub(super) outcome: CFunctionOutcome,
    pub(super) facts: ExecutionFacts,
    pub(super) obligations: Vec<ProofObligation>,
    pub(super) loan_evidence: super::loans::CheckedLoanCallEvidenceSequence,
}

impl CFunctionPath {
    /// A path with no loan evidence: every path not ending in a borrowing
    /// call.
    pub(super) fn new(
        outcome: CFunctionOutcome,
        facts: ExecutionFacts,
        obligations: Vec<ProofObligation>,
    ) -> Self {
        Self {
            outcome,
            facts,
            obligations,
            loan_evidence: super::loans::empty_checked_loan_evidence_sequence(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CArgumentsPath {
    pub(super) values: Vec<CValue>,
    pub(super) outcome: Option<CFunctionOutcome>,
    pub(super) facts: ExecutionFacts,
    pub(super) obligations: Vec<ProofObligation>,
}

/// Where a fresh-identity stream takes the counter it hands out from.
///
/// A proof state has exactly one such counter. `Local` is a stream over
/// terms the caller already holds — a substitution, an instantiation, a case
/// partition — where the reserved set is everything those terms mention and
/// no other allocator runs against the same state while it lives.
///
/// `Execution` is the stream of one symbolic C execution, and its counter is
/// that execution's [`ExecutionBudget`]. The loop rule's havoc of modified
/// locals, resource-model field havoc, heap allocation, opaque call results
/// and load minting all allocate from it, so no two of them can hand the
/// same identity to two different things: a re-bound loop binder's model
/// field cannot collide with the local the loop havocs. It also keeps the
/// proof core's freshness probe honest, which assumes everything the kernel
/// has issued lies below `next_kernel_variable` rather than rescanning.
#[derive(Clone, Debug, Eq, PartialEq)]
enum KernelVariableCounter {
    Local(u64),
    Execution,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct KernelVariableGenerator {
    counter: KernelVariableCounter,
    reserved: BTreeSet<Variable>,
    shared_reserved: Option<Arc<BTreeSet<Variable>>>,
}

impl KernelVariableGenerator {
    /// Build the deterministic term-local fresh-name stream used by both
    /// planning and certificate validation. Given the same lower bound and
    /// reserved set, the first available identifier and every successor are
    /// identical, so a check never relies on accidental equality with an
    /// independently chosen symbolic name.
    pub(super) fn fresh_for(lower_bound: u64, existing: BTreeSet<Variable>) -> Self {
        Self {
            counter: KernelVariableCounter::Local(lower_bound),
            reserved: existing,
            shared_reserved: None,
        }
    }

    /// The fresh-name stream of one symbolic C execution. It reserves
    /// `existing` on top of the execution's own counter, and every identity
    /// it issues advances that counter, so it is the same allocator as every
    /// other kernel allocation made under the same budget.
    pub(super) fn fresh_for_execution(existing: BTreeSet<Variable>) -> Self {
        Self {
            counter: KernelVariableCounter::Execution,
            reserved: existing,
            shared_reserved: None,
        }
    }

    pub(super) fn fresh_for_execution_with_shared_reservations(
        existing: BTreeSet<Variable>,
        shared_reserved: Arc<BTreeSet<Variable>>,
    ) -> Self {
        Self {
            counter: KernelVariableCounter::Execution,
            reserved: existing,
            shared_reserved: Some(shared_reserved),
        }
    }

    /// One identity from `counter` that neither this stream nor its shared
    /// reservations have handed out, advancing `counter` past it. Cost is one
    /// reserved-set probe per candidate; the counter itself is O(1).
    fn allocate_from(&mut self, counter: &mut u64) -> Variable {
        let start = *counter;
        loop {
            let variable = Variable(*counter);
            *counter = counter.wrapping_add(1);
            let shared_contains = self
                .shared_reserved
                .as_ref()
                .is_some_and(|reserved| reserved.contains(&variable));
            if !shared_contains && self.reserved.insert(variable) {
                return variable;
            }
            assert!(
                *counter != start,
                "all symbolic variable identifiers are already reserved"
            );
        }
    }

    pub(super) fn next(&mut self) -> Variable {
        let KernelVariableCounter::Local(start) = self.counter else {
            panic!("an execution's fresh-variable stream must allocate through its budget");
        };
        let mut counter = start;
        let variable = self.allocate_from(&mut counter);
        self.counter = KernelVariableCounter::Local(counter);
        variable
    }

    /// One identity from the execution's single counter. Using the budget is
    /// what makes this stream and every other allocation under the same
    /// budget one allocator rather than two overlapping ones. A stream that
    /// has walked its whole range refuses through the budget's ceiling
    /// rather than wrapping back onto identities it already issued.
    pub(super) fn next_in(&mut self, budget: &mut ExecutionBudget) -> ExecutionResult<Variable> {
        assert!(
            matches!(self.counter, KernelVariableCounter::Execution),
            "a term-local fresh-variable stream must not allocate from an execution budget"
        );
        loop {
            let variable = budget.allocate_kernel_variable()?;
            let shared_contains = self
                .shared_reserved
                .as_ref()
                .is_some_and(|reserved| reserved.contains(&variable));
            if !shared_contains && self.reserved.insert(variable) {
                return Ok(variable);
            }
        }
    }
}

#[cfg(test)]
mod representation_size_tests {
    use super::*;

    /// A connective boxes each side, and a fact list stores each fact, at the
    /// size of the widest variant. C states, functions, statements, and
    /// resources therefore stay behind a pointer, so a pure fact such as
    /// `a == b` does not pay for a C payload it does not carry.
    #[test]
    fn pure_facts_do_not_pay_for_c_payloads() {
        assert!(std::mem::size_of::<Term>() <= 144);
        assert!(std::mem::size_of::<Proposition>() <= 2 * std::mem::size_of::<Term>());
        assert!(std::mem::size_of::<ExecutionPureFact>() <= 352);
        assert!(std::mem::size_of::<CStatementOutcome>() <= 144);
        assert!(std::mem::size_of::<CFunctionOutcome>() <= 144);
    }
}
