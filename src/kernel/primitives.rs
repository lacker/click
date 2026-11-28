use super::api::{
    int8, int16, int32, normalize_exact_memory_loads_in_pointer_offset, uint8, uint16, uint32,
};
use super::memory_history::{AddressOffsetEqualityEvidence, AtomicMemoryLoadEqualityEvidence};
use super::reasoning::{
    collect_or_cases, instantiate_range_fold_step, memory_states_proven_equal_at_pointer,
    pointers_proven_equal_for_memory_resolution, resource_context_has_read,
    signed_bitvector_constant, signed_i64_bitvector_constant,
};
use super::{ExecutionFacts, ExecutionValue, StoredExecutionValue, StoredMemoryValue};
use crate::persistent::{PersistentMap, PersistentSet};
use std::collections::{BTreeMap, BTreeSet};
use std::hash::{Hash, Hasher};
use std::sync::{Arc, OnceLock};

mod bindings;
pub(crate) use bindings::GeneratedBinderSpellingScope;
pub use bindings::{
    BindingDeclaration, BindingName, GeneratedBinderId, LocalBindingId, LocalFunctionId,
    LocalStorageInstance, SliceLengthBinding, StaticBindingId, StaticBindingMetadata,
    StaticBindingOwner,
};

/// Opaque creation identity carried by a modeled `pthread_t` word. Its ID is
/// not the numeric C representation and carries no completion authority.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ThreadHandleId(pub(crate) u64);

pub(crate) const LITTLE_ENDIAN_PREDICATE_NAME: &str = "__click_little_endian";

pub(crate) const SAME_ALLOCATION_PREDICATE_NAME: &str = "__click_same_allocation";
/// The prefix of the fact that opaque subobject bounds cover a range of
/// `element_width`-byte elements: `{prefix}{element_width}(start, from, to)`
/// (`design/pointer-subobject-bounds.md`, Phase C).
pub(crate) const SUBOBJECT_COVERS_PREDICATE_PREFIX: &str = "__click_subobject_covers_";

/// The Click spelling of the kernel predicate `name`: `same_allocation`
/// for the built-in, the declared name for a contract or a
/// user predicate. `None` marks verifier bookkeeping under the reserved
/// `__click_` prefix, which no Click proposition lowers to.
pub(crate) fn predicate_source_name(name: &str) -> Option<&str> {
    match name {
        SAME_ALLOCATION_PREDICATE_NAME => Some("same_allocation"),
        LITTLE_ENDIAN_PREDICATE_NAME => Some("little_endian"),
        _ => FunctionContract::surface_name_from_predicate(name)
            .or_else(|| (!name.starts_with("__click_")).then_some(name)),
    }
}

impl KernelProposition {
    /// Whether this is kernel authority rather than a proof-state fact: a
    /// resource composition, a completed volatile access record, or a
    /// predicate with no Click spelling. The
    /// kernel holds and checks it like any fact; no surface view presents or
    /// cites it (`docs/internals/raise-lower-principle.md`).
    pub(crate) fn is_kernel_authority(&self) -> bool {
        match self {
            Self::ResourceComposition(_) | Self::VolatileAccess(_) => true,
            Self::Predicate { name, .. } => predicate_source_name(name).is_none(),
            _ => false,
        }
    }
}

#[cfg(test)]
mod allocation_size_tests;
mod bool_sort;
mod contracts;
mod symbolic_layout;
pub use symbolic_layout::{
    AccessExtent, LayoutOffset, LayoutSize, SymbolicField, SymbolicLayoutName, layout_term_spelling,
};
pub(in crate::kernel) mod float_conversion;
mod load;
#[cfg(test)]
mod memory_construction_tests;
#[cfg(test)]
pub(crate) use load::allow_cross_arena_loads;
#[cfg(test)]
pub(crate) use load::interned_load_count;
pub use load::{Load, LoadCell, ReadPoint};
pub(crate) use load::{
    LoadInternerState, capture_load_interner, clear_load_interner, restore_load_interner,
};
pub(crate) use load::{legacy_pointer_word_read, read_operands};
pub(crate) mod program_point;
pub use program_point::ProgramPoint;
mod statement_clone;
#[cfg(test)]
pub(crate) use contracts::memory_range_byte_count_guards;
pub(crate) use contracts::{
    MemoryRangeSpan, admitted_memory_range_span_facts, is_unnamed_footprint_base,
    memory_range_byte_count, memory_range_byte_count_span, memory_range_element_count,
    memory_range_element_count_guards, memory_range_element_count_limit,
    memory_range_span_guard_spellings, memory_range_span_guards, narrow_range_constant,
    scaled_span_element_width, stated_loadable_span_guard_spellings, stated_loadable_span_guards,
    wide_loadable_element_count, wide_range_bounds,
};
mod integer;
pub(crate) use integer::clear_machine_observation_memo;
mod kernel_term;
pub(in crate::kernel) use kernel_term::wrap_exact_machine_value;
pub(crate) use kernel_term::{
    BooleanOperandView, FloatOperandView, KernelConstructor, KernelFold, KernelFoldIndex,
    KernelMatch, KernelTermExport, KernelTermImport,
};
// Prepared rewrite interface for the following scoped consumers.
pub(in crate::kernel) use kernel_term::ArrayObject;
pub use kernel_term::{
    Address, AddressOffset, AddressParts, KernelCallArgument, KernelFloatType,
    KernelImportedScalar, KernelIntegerOperator, KernelMachineLiteral, KernelNativeDescriptor,
    KernelObservedArgument, KernelObservedPointer, KernelTerm, KernelTermNode, KernelType,
    KernelWrittenMachine, Pointer, SubobjectBounds,
};
#[allow(unused_imports)]
pub(crate) use kernel_term::{
    AddressBlock, KernelMemoryRead, PointerRewrite, PointerRewriteError, SharedAddressBase,
};
pub(crate) use kernel_term::{
    KernelAddressOffset, KernelArrayObject, KernelMatchArm, OffsetTree, OffsetView,
    PointerMetadataKey, SharedAddress, SharedAddressOffset, SharedPointer,
};
mod machine_integer;
pub use machine_integer::{
    MachineIntegerConstant, MachineIntegerDivisionError, MachineIntegerFormat, MachineIntegerWidth,
};
pub(crate) use machine_integer::{is_narrow_widening32, is_sign_cast32};
mod remainder_rules;
mod wide_order_guards;
pub use integer::{
    AlgebraicIntegerMatchArm, IntegerComparisonOperator, IntegerRangeFoldIndex, IntegerTerm,
    SharedIntegerApplication, SharedIntegerRangeEndpoint, SharedIntegerTerm, SharedPureApplication,
};
pub use integer::{MachineIntegerType, SharedMachineIntegerTerm, SignedDefinedWidth};
pub(crate) use integer::{
    MachineOperandView, PureApplicationIdentity, clear_shared_machine_variable_cache,
    machine_operand_syntax_cmp, shared_condition_operand_leaf_pairs,
    shared_machine_conversion_leaves, shared_machine_read_leaves, shared_machine_read_uses,
    shared_machine_syntax_equal, shared_machine_syntax_variables, shared_operand_leaf_pairs,
    shared_state_read_pairs,
};
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
mod cell_version_intervals;
mod derivations;
mod heap_effective_types;
mod initialized_bytes;
mod observed_population_families;
pub(crate) use heap_effective_types::HeapEffectiveTypes;
pub(crate) use initialized_bytes::InitializedBytes;
mod memory_blocks;
pub(crate) use memory_blocks::MemoryBlocks;
mod memory_state;
pub(crate) use observed_population_families::ObservedPopulationFamilies;
mod persistent_map;
pub(crate) use memory_state::BlockMembership;
pub(crate) use memory_state::held_term_fingerprint;
mod statement_sequence;
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
pub(crate) use persistent_map::{HashedOrdMap, HashedOrdMapChange, HashedOrdSet};
pub use statement_sequence::ProgramStatementSequence;
mod iterated;
pub use iterated::{IteratedGuard, IteratedMemory};
pub(in crate::kernel) mod canonical_fact_set;
mod composition_member_index;
mod memory_equality_index;
mod sequence_values;
pub use sequence_values::{SequenceValues, SequenceValuesIter};
mod descriptor_values;
pub use descriptor_values::{
    StoredAlgebraicTerm, StoredConditionTerm, StoredIntegerTerm, StoredMachineTerm,
    StoredPointerOffset, StoredProgramValue,
};
mod resource_fields;
pub(crate) use resource_fields::StoredResourceField;
pub use resource_fields::{ResourceFieldValue, ResourceFieldValues};
mod resource_algebra;
pub(crate) use resource_algebra::coalesce_written_resource_descriptions;
#[cfg(test)]
pub(crate) use resource_algebra::take_whole_normalization_facts;
mod arithmetic_domains;
mod term_operations;
mod term_shape;
mod term_width;
pub(super) use derivations::*;
pub(crate) use memory_state::resource_context_has_symbolic_range_read;
pub use memory_state::value_independent_click_memory;
pub(super) use resource_algebra::*;
pub(crate) use term_operations::{
    first_unavailable_connective_side, listed_premise_holds, mirrored_equality,
    proposition_holds_without_facts, single_variable_of_program_value,
};
pub(in crate::kernel) use term_operations::{float_binary_bits_at, round_right_to_even};
pub(in crate::kernel) use term_operations::{
    int64_add_interval_fits, int64_signed_order_by_width_views, int64_subtract_interval_fits,
};
pub(crate) use term_shape::{BitvectorBinaryOp, BitvectorComparisonOp, BitvectorUnaryOp};
pub(crate) use term_width::*;

pub(super) const C_POINTER_BYTE_WIDTH: u32 = 8;
/// The bytes a value of an abstract type parameter takes in memory, as a
/// generic struct's field: a model width, since no program reads its bytes.
pub(crate) const ABSTRACT_VALUE_WIDTH: u32 = 8;

/// The allocator alignment guaranteed by the LP64 heap model.  Keep this
/// beside the pointer primitives so all proof routes use the same profile
/// contract rather than copying a second limit into a checker.
pub(crate) const HEAP_ALLOCATION_ALIGNMENT: u64 = 16;

/// A symbolic identity. Source and execution producers still use the numeric
/// constructor below; a kernel-allocated fresh variable carries a private
/// origin as well, so even a caller-constructed variable with the same number
/// cannot capture it. Names in source text are separate from this identity.
#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub struct Variable {
    // Whether this is the element count of the slice its base variable names
    // ([`Variable::element_count`]). It comes first, so every count orders
    // after every other variable and ordinary variables stay ahead of
    // `Variable::FIRST_NON_ORDINARY`.
    element_count: bool,
    // The origin comes next, so variables order by producer: ordinary
    // variables keep their numeric order ahead of every other origin, and
    // each other origin is one contiguous run after them. A query for the
    // greatest ordinary variable must bound itself by
    // `Variable::FIRST_NON_ORDINARY` rather than read a set's last element.
    origin: VariableOrigin,
    number: (u64,),
}

/// A quantifier's bound variable. Only closing a body over a free variable
/// makes one, so a bound occurrence is never a free variable.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct QuantifierBinder(Variable);

impl QuantifierBinder {
    /// The binder of a quantifier of height `height`. Only closing calls this.
    pub(in crate::kernel) const fn of_height(height: u64) -> Self {
        Self(Variable::bound(height))
    }

    pub(crate) fn height(&self) -> u64 {
        self.0.number.0
    }
}

impl std::ops::Deref for QuantifierBinder {
    type Target = Variable;

    fn deref(&self) -> &Variable {
        &self.0
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
enum VariableOrigin {
    Ordinary,
    KernelFresh,
    /// A quantifier's bound variable, numbered by the quantifier's height:
    /// one more than the tallest quantifier in its body. Only closing a body
    /// makes one; no producer of free variables can.
    Bound,
    /// A free variable a quantifier was opened at where no proof state
    /// reserves identities, numbered per verification session.
    Opening,
    /// A match arm's binder, numbered by the lowering budget that built the
    /// arm. No other producer mints one, so an occurrence in an arm body is a
    /// bound occurrence of that arm's binder.
    MatchBinder,
    /// A specification fold's accumulator or item, one per written binder
    /// name and role, numbered in allocation order.
    SpecFoldBinder,
    /// A free variable `intro` or a logical choice introduced, standing for
    /// an arbitrary value. Numbered from the witnesses its proof state
    /// already reserves.
    Witness,
    /// A variable a named producer mints, numbered by that producer.
    Produced(Producer),
}

/// A producer of free variables that numbers its own variables. Two
/// producers never share a variable, whatever their numbers, so a producer
/// numbers from zero by whatever rule suits it.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) enum Producer {
    /// A parameter of the function whose recursive call a termination check
    /// compares, by parameter index.
    TerminationParameter,
    /// A `let` witness of a structural measure's definition, by index.
    TerminationWitness,
    /// A pointer argument of a pure theorem, by parameter index.
    PointerArgument,
    /// An Integer binder of a resource `match` arm, numbered once for a
    /// function's whole resource environment.
    ResourceIntegerBinding,
    /// A variable Surface lowering binds while it lowers a quantifier, fold
    /// or `match` in a fixed-state proof proposition, numbered per lowering.
    ProofQuantifier,
    /// The same while lowering a function's annotations.
    FunctionQuantifier,
    /// The same while lowering a requirement or contract summary.
    RequirementQuantifier,
    /// The same while lowering a resource body, condition or fold-read
    /// definition.
    ResourceQuantifier,
    /// A Surface algebraic binder, by its binder index: a written algebraic
    /// quantifier or `let`, or a constructor field a proof `match` splits on.
    /// The index is how the binder raises back to Surface.
    AlgebraicBinder,
    /// The arbitrary value stored in a linked, const C library object.
    CLibraryValue,
}

// Hash the number before the origin, as before the fields were reordered for
// `Ord`: hashing does not need the order, and keeping it leaves every hashed
// collection of variables laid out as it was.
impl std::hash::Hash for Variable {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.number.hash(state);
        self.origin.hash(state);
        // A count hashes one more word; every other variable hashes as before.
        if self.element_count {
            true.hash(state);
        }
    }
}

impl std::fmt::Debug for Variable {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(slice) = self.counted_slice() {
            return formatter.debug_tuple("ElementCount").field(&slice).finish();
        }
        match self.origin {
            VariableOrigin::Ordinary => formatter.debug_tuple("Variable").field(&self.0).finish(),
            VariableOrigin::KernelFresh => formatter
                .debug_tuple("FreshVariable")
                .field(&self.0)
                .finish(),
            VariableOrigin::Bound => formatter.debug_tuple("Bound").field(&self.0).finish(),
            VariableOrigin::Opening => formatter.debug_tuple("Opening").field(&self.0).finish(),
            VariableOrigin::MatchBinder => {
                formatter.debug_tuple("MatchBinder").field(&self.0).finish()
            }
            VariableOrigin::Witness => formatter.debug_tuple("Witness").field(&self.0).finish(),
            VariableOrigin::Produced(producer) => formatter
                .debug_tuple(&format!("{producer:?}"))
                .field(&self.0)
                .finish(),
            VariableOrigin::SpecFoldBinder => formatter
                .debug_tuple("SpecFoldBinder")
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
        element_count: false,
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
    /// The bound variable of a quantifier of height `height`.
    pub(in crate::kernel) const fn bound(height: u64) -> Self {
        Self {
            element_count: false,
            number: (height,),
            origin: VariableOrigin::Bound,
        }
    }

    /// The `number`th variable a session opened a quantifier at.
    pub(in crate::kernel) const fn opening(number: u64) -> Self {
        Self {
            element_count: false,
            number: (number,),
            origin: VariableOrigin::Opening,
        }
    }

    /// The least variable of any origin other than `Ordinary`: every
    /// ordinary variable orders before it and every other variable at or
    /// after it.
    pub(crate) const FIRST_NON_ORDINARY: Self = Self {
        element_count: false,
        number: (0,),
        origin: VariableOrigin::KernelFresh,
    };

    /// Whether this is an ordinary numbered variable, `Variable(n)`.
    pub(crate) fn is_ordinary(&self) -> bool {
        !self.element_count && self.origin == VariableOrigin::Ordinary
    }

    /// Whether this is a quantifier's bound variable.
    pub(crate) fn is_bound(&self) -> bool {
        !self.element_count && self.origin == VariableOrigin::Bound
    }

    /// The `number`th match-arm binder a lowering budget allocated.
    pub(in crate::kernel) const fn match_binder(number: u64) -> Self {
        Self {
            element_count: false,
            number: (number,),
            origin: VariableOrigin::MatchBinder,
        }
    }

    /// The `number`th specification fold binder.
    pub(in crate::kernel) const fn spec_fold_binder(number: u64) -> Self {
        Self {
            element_count: false,
            number: (number,),
            origin: VariableOrigin::SpecFoldBinder,
        }
    }

    /// Whether this is a specification fold's binder.
    #[cfg(test)]
    pub(in crate::kernel) fn is_spec_fold_binder(&self) -> bool {
        !self.element_count && self.origin == VariableOrigin::SpecFoldBinder
    }

    /// The `number`th variable `producer` minted.
    pub(crate) const fn produced(producer: Producer, number: u64) -> Self {
        Self {
            element_count: false,
            number: (number,),
            origin: VariableOrigin::Produced(producer),
        }
    }

    /// The producer that minted this variable, if a named one did.
    pub(crate) fn producer(&self) -> Option<Producer> {
        match self.origin {
            VariableOrigin::Produced(producer) if !self.element_count => Some(producer),
            _ => None,
        }
    }

    /// The Surface binder index of an algebraic binder variable.
    pub(crate) fn algebraic_binder_index(&self) -> Option<u64> {
        (!self.element_count && self.origin == VariableOrigin::Produced(Producer::AlgebraicBinder))
            .then_some(self.number.0)
    }

    /// The `number`th universal-introduction or choice witness.
    pub(in crate::kernel) const fn witness(number: u64) -> Self {
        Self {
            element_count: false,
            number: (number,),
            origin: VariableOrigin::Witness,
        }
    }

    /// Whether this is a universal-introduction or choice witness.
    pub(in crate::kernel) fn is_witness(&self) -> bool {
        !self.element_count && self.origin == VariableOrigin::Witness
    }

    /// Whether this is a match arm's binder.
    pub(in crate::kernel) fn is_match_binder(&self) -> bool {
        !self.element_count && self.origin == VariableOrigin::MatchBinder
    }

    /// The element count of the slice this variable names
    /// (`design/rust-slice-values.md`, step 2b-iii-a): a `UInt64` variable
    /// whose identity is this variable's plus the component, so a value named
    /// by one variable, such as a slice-returning call's result, names its
    /// count with no second allocation, and the count raises from the name of
    /// the slice. It is no binder, witness or producer's variable of its own,
    /// and orders after every variable that is not a count. A count has no
    /// count of its own.
    pub(crate) const fn element_count(self) -> Self {
        assert!(
            !self.element_count,
            "internal error: an element count names no slice"
        );
        Self {
            element_count: true,
            ..self
        }
    }

    /// The variable whose slice this is the element count of, or `None` for
    /// a variable that is not a count.
    pub(crate) fn counted_slice(&self) -> Option<Self> {
        self.element_count.then_some(Self {
            element_count: false,
            ..*self
        })
    }

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
            element_count: false,
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
pub(super) struct ExecutionEnvironmentVariableIndex {
    values: Arc<OnceLock<Arc<BTreeSet<Variable>>>>,
    /// At least the greatest execution-range variable `values` holds or
    /// would hold, when an owner bounds its variables without collecting
    /// them (`LazyReservedVariables`).
    execution_bound: Arc<OnceLock<Option<Variable>>>,
    #[cfg(test)]
    builds: Arc<std::sync::atomic::AtomicUsize>,
}

impl ExecutionEnvironmentVariableIndex {
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

    pub(super) fn execution_bound(
        &self,
        initialize: impl FnOnce() -> Option<Variable>,
    ) -> Option<Variable> {
        *self.execution_bound.get_or_init(initialize)
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

/// A derived index, so two rules or environments that agree on their
/// semantic content are equal whatever their indexes hold.
impl PartialEq for ExecutionEnvironmentVariableIndex {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl Eq for ExecutionEnvironmentVariableIndex {}

impl std::fmt::Debug for ExecutionEnvironmentVariableIndex {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("ExecutionEnvironmentVariableIndex")
    }
}

/// The symbolic variables an execution environment reserves, held as the
/// sets of its parts: one for its functions, contracts, function rules and
/// recursion anchor, and one for each verified loop rule. Each set is
/// collected once and shared by every clone holding its part, so an
/// environment that gains a loop rule collects that rule alone.
///
/// A part whose set is costly to collect, a loop rule whose prerequisite
/// context is the whole path at its loop or the context a loop head is
/// prepared under, is held as a [`LazyReservedVariables`]: an upper bound
/// on the execution-range variables it holds, kept beside its facts, and
/// the set itself, collected only when a query the bound cannot answer
/// needs it.
#[derive(Clone, Debug, Default)]
pub(crate) struct ReservedVariableSets {
    sets: Vec<Arc<BTreeSet<Variable>>>,
    lazy: Vec<LazyReservedVariables>,
}

impl ReservedVariableSets {
    pub(crate) fn contains(&self, variable: &Variable) -> bool {
        self.sets.iter().any(|set| set.contains(variable))
            || self.lazy.iter().any(|set| set.contains(variable))
    }

    /// Every reserved variable; this collects every lazy part.
    #[cfg(test)]
    pub(crate) fn iter(&self) -> impl Iterator<Item = &Variable> {
        self.sets
            .iter()
            .flat_map(|set| set.iter())
            .chain(self.lazy.iter().flat_map(|set| set.collected().iter()))
    }

    pub(super) fn push_lazy(&mut self, set: LazyReservedVariables) {
        self.lazy.push(set);
    }
}

impl From<Arc<BTreeSet<Variable>>> for ReservedVariableSets {
    fn from(set: Arc<BTreeSet<Variable>>) -> Self {
        Self {
            sets: vec![set],
            lazy: Vec::new(),
        }
    }
}

impl From<LazyReservedVariables> for ReservedVariableSets {
    fn from(set: LazyReservedVariables) -> Self {
        Self {
            sets: Vec::new(),
            lazy: vec![set],
        }
    }
}

/// A reserved variable set collected only when a query needs it.
///
/// An execution's fresh identities come from the execution range
/// (`ExecutionBudget::KERNEL_VARIABLE_BASE` up to its ceiling), so the
/// question a fresh-identity stream asks of a reservation is almost always
/// whether it holds some execution-range variable above everything the
/// stream has already skipped. `execution_bound` is at least the greatest
/// execution-range variable the set holds (a fact context keeps exactly
/// such a bound as it files facts, `PureFactContext::execution_variable_ceiling`),
/// so an execution-range query above it is answered "no" without collecting.
/// Any other query collects the set once, shared by every clone, and
/// answers from it: the answer is always the collected set's.
#[derive(Clone)]
pub(crate) struct LazyReservedVariables {
    execution_bound: Option<Variable>,
    collect: Arc<dyn Fn() -> Arc<BTreeSet<Variable>> + Send + Sync>,
    collected: Arc<OnceLock<Arc<BTreeSet<Variable>>>>,
}

impl std::fmt::Debug for LazyReservedVariables {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("LazyReservedVariables")
            .field("execution_bound", &self.execution_bound)
            .field("collected", &self.collected.get().is_some())
            .finish()
    }
}

#[cfg(test)]
thread_local! {
    /// Lazy reservation sets collected on this thread, for scaling tests.
    static LAZY_RESERVATION_COLLECTIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn lazy_reservation_collections() -> usize {
    LAZY_RESERVATION_COLLECTIONS.with(std::cell::Cell::get)
}

impl LazyReservedVariables {
    /// `collect` must return a set none of whose execution-range variables
    /// lies above `execution_bound`.
    pub(super) fn new(
        execution_bound: Option<Variable>,
        collect: impl Fn() -> Arc<BTreeSet<Variable>> + Send + Sync + 'static,
    ) -> Self {
        Self {
            execution_bound,
            collect: Arc::new(collect),
            collected: Arc::new(OnceLock::new()),
        }
    }

    fn collected(&self) -> &BTreeSet<Variable> {
        self.collected.get_or_init(|| {
            #[cfg(test)]
            LAZY_RESERVATION_COLLECTIONS.with(|count| count.set(count.get() + 1));
            (self.collect)()
        })
    }

    fn contains(&self, variable: &Variable) -> bool {
        let execution_range = variable.is_ordinary()
            && (crate::kernel::ExecutionBudget::KERNEL_VARIABLE_BASE
                ..crate::kernel::ExecutionBudget::KERNEL_VARIABLE_CEILING)
                .contains(&variable.0);
        if execution_range && self.execution_bound.is_none_or(|bound| *variable > bound) {
            #[cfg(debug_assertions)]
            if crate::instrumentation::lazy_reservation_cross_checks_enabled() {
                crate::instrumentation::uncharged_debug_check(|| {
                    assert!(
                        !self.collected().contains(variable),
                        "a lazy reservation's execution bound {:?} is below its variable {variable:?}",
                        self.execution_bound,
                    );
                });
            }
            return false;
        }
        self.collected().contains(variable)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Sort {
    Condition,
    Bitvector32,
    Integer,
    ProgramInt32,
    ProgramInt64,
    ProgramInteger(MachineIntegerType),
    ProgramPointer(ProgramType),
    ProgramObjectPointer(ProgramType, crate::kernel::effective_type::CAccessClass),
    Algebraic(AlgebraicType),
}

impl Sort {
    pub(crate) fn pointer_type(&self) -> Option<ProgramType> {
        match self {
            Self::ProgramPointer(ty) | Self::ProgramObjectPointer(ty, _) => Some(*ty),
            _ => None,
        }
    }

    pub(crate) fn pointer_object_class(
        &self,
    ) -> Option<crate::kernel::effective_type::CAccessClass> {
        match self {
            Self::ProgramObjectPointer(_, class) => Some(class.clone()),
            _ => None,
        }
    }

    pub(crate) fn symbolic_pointer_value(&self, variable: Variable) -> Option<ProgramValue> {
        let ty = self.pointer_type()?;
        // A slice sort's binder names a wide pointer, thin part and count
        // (`design/rust-slice-values.md`, step 2b-iii-b-i).
        if !ty.is_pointer() && !ty.is_slice_pointer() {
            return None;
        }
        Some(
            crate::kernel::symbolic_call_result(ty, variable)
                .with_pointer_object_class(self.pointer_object_class()),
        )
    }

    pub fn machine_integer(integer_type: MachineIntegerType) -> Self {
        match integer_type {
            MachineIntegerType::Int32 => Self::ProgramInt32,
            MachineIntegerType::Int64 => Self::ProgramInt64,
            other => Self::ProgramInteger(other),
        }
    }

    pub fn machine_integer_type(&self) -> Option<MachineIntegerType> {
        match self {
            Self::ProgramInt32 => Some(MachineIntegerType::Int32),
            Self::ProgramInt64 => Some(MachineIntegerType::Int64),
            Self::ProgramInteger(integer_type) => Some(*integer_type),
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
/// in the term. A four-byte read keeps the reader's signedness (`Int32`,
/// `UInt32`) and is its own load; the two reads of one cell are related by
/// σ (R-mem), and a typed read of a cell stored at the other signedness is
/// the sign cast σ of the stored word (rule K5,
/// `design/machine-integers.md`). Eight-byte reads are one kind (`Bits64`)
/// and let the `ProgramValue` wrapper choose the interpretation. Narrower reads
/// store the extended value, which signedness changes, so they keep it. Wide 128-bit reads also keep signedness: their
/// checked constant payloads retain the exact machine format. This profile
/// supports exact typed cells, not signed/unsigned memory reinterpretation.
/// Floating-point reads are kinds of their own.
///
/// A pointer read is an `Int32` read: Click names a pointer value by the
/// four-byte word at its address (`Address::loaded` scales that word), which
/// is also how a materialized pointer field's cells hold it. The access is
/// still eight bytes wide; framing takes the width recorded at the address,
/// which a pointer read records, and never less than the kind's own.
///
/// A value of an algebraic type held in memory is read at its own type,
/// [`Self::Algebraic`]: the decoding of the cell's bytes at that type
/// (`design/loads.md`, step 3b PR 2), never an integer read.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum LoadKind {
    Int8,
    UInt8,
    Int16,
    UInt16,
    Int32,
    UInt32,
    Bits64,
    /// A read of a whole value of algebraic type `T`, the stand-in an
    /// algebraic read of a `T` ([`AlgebraicTermNode::MemoryLoad`]) takes in
    /// memory reasoning: the cell's bytes decoded at `T`. It reaches the
    /// model's width for a type Click lays out itself (an enum, a library
    /// instance), and `sizeof(T)` bytes for one it knows only by name
    /// ([`Self::extent`]). Two stand-ins of one cell at two types are two
    /// decodings of one load, and neither is an integer read of the cell.
    Algebraic(TypeParameterName),
    /// Wide loads retain signedness because their constant payloads are typed.
    Int128,
    UInt128,
    Float32,
    Float64,
    /// The element count of the slice a read of a slice cell decodes to
    /// (`design/rust-slice-values.md`, step 2b-ii-b): the cell's metadata,
    /// a `u64`, read from the whole 16-byte cell. The kernel states no
    /// layout for the cell's words, so this is no integer read of either
    /// word, and no integer read of the cell is this read.
    SliceCount,
}

impl LoadKind {
    /// The kind of a C read of `value_type`, for every scalar or pointer type
    /// a load can have. `_Bool` reads its byte unsigned and normalizes it.
    pub fn of_type(value_type: ProgramType) -> Option<Self> {
        Some(match value_type {
            ProgramType::Bool | ProgramType::UInt8 => Self::UInt8,
            ProgramType::Int8 => Self::Int8,
            ProgramType::Int16 => Self::Int16,
            ProgramType::UInt16 => Self::UInt16,
            ProgramType::Int32 => Self::Int32,
            ProgramType::UInt32 => Self::UInt32,
            ProgramType::Int64 | ProgramType::UInt64 => Self::Bits64,
            ProgramType::Int128 => Self::Int128,
            ProgramType::UInt128 => Self::UInt128,
            ProgramType::Float32 => Self::Float32,
            ProgramType::Float64 => Self::Float64,
            ProgramType::Void
            | ProgramType::Int8Array(_)
            | ProgramType::Int16Array(_)
            | ProgramType::Int32Array(_)
            | ProgramType::UInt8Array(_)
            | ProgramType::UInt16Array(_)
            | ProgramType::UInt32Array(_)
            | ProgramType::Int128Array(_)
            | ProgramType::Int64Array(_)
            | ProgramType::UInt128Array(_)
            | ProgramType::UInt64Array(_)
            | ProgramType::Float32Array(_)
            | ProgramType::Float64Array(_)
            | ProgramType::PointerArray(_, _) => return None,
            _ if value_type.is_pointer() => Self::Int32,
            _ => return None,
        })
    }

    /// The kind of read that returns exactly `value`, a cell's stored value:
    /// a read of any other kind at the cell's address does not.
    pub fn of_value(value: &ProgramValue) -> Option<Self> {
        Some(match value.numeric_value() {
            ProgramValue::PointerInteger(_) => unreachable!("numeric projection"),
            ProgramValue::Void | ProgramValue::Parameter(_) => return None,
            ProgramValue::Bool(_) | ProgramValue::UInt8(_) => Self::UInt8,
            ProgramValue::Int8(_) => Self::Int8,
            ProgramValue::Int16(_) => Self::Int16,
            ProgramValue::UInt16(_) => Self::UInt16,
            ProgramValue::Int32(_) => Self::Int32,
            ProgramValue::UInt32(_) => Self::UInt32,
            ProgramValue::Int64(_) | ProgramValue::UInt64(_) => Self::Bits64,
            ProgramValue::Int128(_) => Self::Int128,
            ProgramValue::UInt128(_) => Self::UInt128,
            ProgramValue::Float32(_) => Self::Float32,
            ProgramValue::Float64(_) => Self::Float64,
            // A slice's two-word cell is no scalar or pointer-word read: no
            // kind reads it, so no scalar read is answered by a stored slice
            // (`design/rust-slice-values.md`, step 2b-ii-a).
            ProgramValue::Pointer(pointer) if pointer.is_wide() => return None,
            ProgramValue::Pointer(_) => Self::Int32,
        })
    }

    /// Whether a read of this kind returns `value`'s term, where `value` is
    /// what a cell holds: the read is exactly the stored value's kind. A
    /// 32-bit read of the other signedness returns σ of the stored word
    /// (R-mem, rule K5), which is another term; [`Self::read_cell`] builds
    /// it. This is the one test every route that answers a load term from a
    /// cell or a store with the stored term itself applies.
    pub fn reads_value(self, value: &ProgramValue) -> bool {
        Self::of_value(value) == Some(self)
    }

    /// Whether a read of this kind reads the same bytes as a read of
    /// `other`: the same kind, or either 32-bit signedness. The two 32-bit
    /// reads are two loads related by σ (R-mem); this names the cell a read
    /// observes, never a term.
    pub fn reads_word_of(self, other: Self) -> bool {
        self == other || (self.is_word32() && other.is_word32())
    }

    /// The value a read of this kind returns from a cell holding `value`:
    /// the value itself when the read is of its kind, or, for a read of a
    /// cell of the same width and the other signedness, the same bits
    /// reinterpreted ([`ProgramType::read_cell`]): the modular conversion at one
    /// or two bytes, and σ of the stored word at 32 bits (R-mem, rule K5).
    /// The 64-bit kind reads a cell of either signedness, whose typed
    /// carrier gives the reader its signedness.
    pub(crate) fn read_cell(self, value: &ProgramValue) -> Option<ProgramValue> {
        if self.reads_value(value) {
            return Some(value.clone());
        }
        match self {
            // A slice read's count is the stored slice's count.
            Self::SliceCount => match value {
                ProgramValue::Pointer(stored) => stored.len().cloned().map(ProgramValue::UInt64),
                _ => None,
            },
            Self::Int8 => ProgramType::Int8.read_cell(value),
            Self::UInt8 => ProgramType::UInt8.read_cell(value),
            Self::Int16 => ProgramType::Int16.read_cell(value),
            Self::UInt16 => ProgramType::UInt16.read_cell(value),
            Self::Int32 => ProgramType::Int32.read_cell(value),
            Self::UInt32 => ProgramType::UInt32.read_cell(value),
            _ => None,
        }
    }

    /// Whether this is a 32-bit integer read of either signedness: the two
    /// read the same four bytes, related by σ (R-mem).
    pub fn is_word32(self) -> bool {
        matches!(self, Self::Int32 | Self::UInt32)
    }

    /// Width when the kind is known but no typed producer recorded an access.
    /// A 32-bit read can also name an LP64 pointer word, so keep its eight-byte ABI
    /// footprint. A fully unknown access uses MAX_SCALAR_ACCESS_BYTES instead.
    pub(crate) fn unrecorded_access_byte_width(self) -> u32 {
        if self.is_word32() {
            crate::kernel::C_POINTER_BYTE_WIDTH
        } else if self == Self::SliceCount {
            crate::kernel::WIDE_POINTER_BYTE_WIDTH
        } else {
            self.byte_width()
        }
    }

    /// How many bytes a read of this kind returns.
    pub fn byte_width(self) -> u32 {
        match self {
            Self::Int8 | Self::UInt8 => 1,
            Self::Int16 | Self::UInt16 => 2,
            Self::Int32 | Self::UInt32 | Self::Float32 => 4,
            Self::Bits64 | Self::Float64 | Self::SliceCount => 8,
            Self::Int128 | Self::UInt128 => 16,
            // A cell holding a value of algebraic type keeps the model width;
            // the bytes the read reaches are its extent.
            Self::Algebraic(_) => ABSTRACT_VALUE_WIDTH,
        }
    }

    /// The bytes a read of this kind reaches: its width, or the whole
    /// object of an abstract type, `sizeof(T)`.
    pub(crate) fn extent(self) -> crate::kernel::AccessExtent {
        match self {
            // `AccessExtent::of_algebraic` of the read's type.
            Self::Algebraic(parameter) => {
                crate::kernel::AccessExtent::of_type(ProgramType::Parameter(parameter))
            }
            // A count reads the slice's whole cell, never one word of it.
            Self::SliceCount => {
                crate::kernel::AccessExtent::Bytes(crate::kernel::WIDE_POINTER_BYTE_WIDTH)
            }
            other => crate::kernel::AccessExtent::Bytes(other.byte_width()),
        }
    }

    /// The kind of the stand-in load an algebraic read of `algebraic_type`
    /// takes: the decoding at that type, [`Self::Algebraic`].
    pub(crate) fn of_algebraic(algebraic_type: &AlgebraicType) -> Self {
        Self::Algebraic(TypeParameterName::of(algebraic_type))
    }

    /// The algebraic type a read of this kind decodes at, for the stand-in
    /// of an algebraic read; `None` for a C scalar read.
    pub(crate) fn algebraic_type(self) -> Option<TypeParameterName> {
        match self {
            Self::Algebraic(parameter) => Some(parameter),
            _ => None,
        }
    }
}

/// The object class an address term retains from the pointer it was formed
/// from (`design/effective-types.md`). Like a pointer value's class, it is
/// not part of the value's identity: it compares equal to every other
/// annotation, hashes to nothing, and orders as equal, so equality, fact
/// lookup, rewriting and premise matching see one address however it is
/// annotated. Only an integer-to-pointer cast reads it, and the destination
/// type of that cast never supplies it.
#[derive(Clone, Debug, Default)]
pub struct AddressObjectClass(Option<crate::kernel::effective_type::CAccessClass>);

impl AddressObjectClass {
    pub const NONE: Self = Self(None);

    pub(crate) fn new(class: Option<crate::kernel::effective_type::CAccessClass>) -> Self {
        Self(class)
    }

    pub(crate) fn class(&self) -> Option<crate::kernel::effective_type::CAccessClass> {
        self.0.clone()
    }
}

impl PartialEq for AddressObjectClass {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl Eq for AddressObjectClass {}

impl std::hash::Hash for AddressObjectClass {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}

impl PartialOrd for AddressObjectClass {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AddressObjectClass {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

#[derive(Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum OldMachineTerm {
    /// A constant of `format`, its two's-complement bits in the low
    /// `format` bits of `bits` (`bits <= format`'s mask; every builder masks
    /// or checks). One node for every format (decision G9,
    /// `design/machine-integers.md`): `int32` is the format of every
    /// kernel-internal constant (indices, counts, masks), and a C, C++ or
    /// Rust value keeps its own. A `uint32` constant's word is the `int32`
    /// constant of the same bits inside a 32-bit operator or comparison
    /// ([`OldMachineTerm::into_word32`]). Build it with
    /// [`OldMachineTerm::constant`], [`OldMachineTerm::uint32_constant`],
    /// [`OldMachineTerm::int64_constant`],
    /// [`OldMachineTerm::uint64_constant`] or
    /// [`OldMachineTerm::machine_constant`]; match it with
    /// `int32_constant!`, `uint32_constant!`, `bits32_constant!`,
    /// `int64_constant!`, `uint64_constant!` or `constant_node!`. The derived
    /// order sorts constants by format, then bits.
    Constant {
        format: MachineIntegerType,
        bits: u128,
    },
    Variable(Variable),
    /// `left op right`, both operands read at `format`. Signed and unsigned
    /// division, remainder and right shift are told apart by the format, not
    /// the operator; a shift count is its own operand of any width. The
    /// formats are the 32- and 64-bit ones. A 32-bit operator reads words
    /// (rule K1), so the sign-free operators (`+ - * << & | ^`) are filed at
    /// `int32`, the signed format of their width, as equality is, and only
    /// `Divide`, `Remainder` and `ShiftRight` are built at `uint32`; the width
    /// audit (`term_width`) refuses any other format. `op` precedes `format`
    /// so that the derived order of the 32-bit nodes is the order their
    /// per-operator variants had (`design/machine-integers.md`, "Stage 3").
    Binary {
        op: MachineBinaryOp,
        format: MachineIntegerType,
        left: Box<OldMachineTerm>,
        right: Box<OldMachineTerm>,
    },
    /// `op operand`, the operand read at `format`, under the same format
    /// restriction as [`Self::Binary`]: the 32-bit complement is at `int32`.
    Unary {
        format: MachineIntegerType,
        op: MachineUnaryOp,
        operand: Box<OldMachineTerm>,
    },
    If {
        condition: Box<OldConditionTerm>,
        then_term: Box<OldMachineTerm>,
        else_term: Box<OldMachineTerm>,
    },
    RangeFold {
        start: Box<OldMachineTerm>,
        end: Box<OldMachineTerm>,
        initial: Box<OldMachineTerm>,
        accumulator: Variable,
        item: Variable,
        body: Box<OldMachineTerm>,
    },
    /// An opaque application retained across one-step unfolding of a total
    /// pure Click function at symbolic arguments.
    PureFunctionApplication {
        name: String,
        arguments: Vec<OldMachineTerm>,
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
    /// The value a read of `LoadKind` at the pointer returns in the state.
    /// Its identity is the interned [`Load`] its [`LoadCell`] holds, the
    /// point's read key and the cell, and its kind (`design/loads.md`, step
    /// 3a): the [`ReadPoint`] is the producer's selection, which consumers
    /// branch on, and compares equal to every other. The kind is part of the
    /// identity: two reads of one address that differ in width or, below
    /// four bytes, in signedness return different values, so they are
    /// different terms. See [`LoadKind`]. Built only by
    /// [`OldMachineTerm::read_named`].
    MemoryLoad(ReadPoint, LoadCell, LoadKind),
    /// The physical LP64 address bits of an object pointer. This numeric
    /// observation carries no provenance or selected bounds. Complete C
    /// integer copies retain that information separately in PointerInteger.
    /// Checked tag identities can recover address bits, never pointer bounds.
    /// The annotation retains the source object class for a later cast and
    /// does not participate in equality, ordering, or hashing.
    IntegerAddress(Box<Address>, AddressObjectClass),
    IntegerToMachine {
        value: SharedIntegerTerm,
        destination: MachineIntegerType,
    },
    /// Integral conversion of `value`, read at `from`, to `to`, modulo the
    /// destination width. One node for every conversion; `spelling` keeps
    /// the constructor that wrote it, so a conversion spelled by a legacy
    /// per-pair constructor stays a different term from the
    /// [`MachineCastSpelling::Generic`] one of the same formats. A legacy
    /// spelling fixes its formats ([`MachineCastSpelling::legacy_formats`]):
    /// the low word ([`MachineCastSpelling::UInt32From64`]) reads its operand
    /// as the 64 bits of a `uint64`, whatever the operand's signedness.
    /// Build it with [`OldMachineTerm::cast_node`] or the smart
    /// constructors (`machine_integer_cast`, `int64_from_32`,
    /// `uint32_from_64`, ...); match it with `cast_term!`. `spelling`
    /// precedes the formats so the derived order of the conversions is the
    /// order their per-pair variants had (`design/machine-integers.md`,
    /// "Stage 3").
    Cast {
        spelling: MachineCastSpelling,
        value: Box<OldMachineTerm>,
        from: MachineIntegerType,
        to: MachineIntegerType,
    },
    Float32Negate(Box<OldMachineTerm>),
    Float32Binary {
        operator: FloatBinaryOperator,
        left: Box<OldMachineTerm>,
        right: Box<OldMachineTerm>,
    },
    Float64Negate(Box<OldMachineTerm>),
    Float64Binary {
        operator: FloatBinaryOperator,
        left: Box<OldMachineTerm>,
        right: Box<OldMachineTerm>,
    },
    /// Rule C1 (`design/machine-integers.md`, Stage 5): the integer value of
    /// the `Bool` `value` at the format `to`, `value as to`. It is 1 when
    /// `value` holds and 0 otherwise, which lie in every format, so it owes
    /// nothing and its word is 1 or 0 at every width. A specification `Bool`
    /// travels in a `ProgramValue::Bool` as its cast to `uint8`, the byte a `bool`
    /// cell holds; its truth is `value`. Built by
    /// [`OldMachineTerm::bool_cast`], which folds a constant. It follows
    /// the preexisting variants, so the derived order of the terms before it is
    /// unchanged.
    BoolCast {
        to: MachineIntegerType,
        value: Box<OldConditionTerm>,
    },
    /// An opaque pthread word; never a symbolic variable or numeric literal.
    ThreadHandle(ThreadHandleId),
    /// The element count, a `UInt64`, of the slice a slice-valued pure
    /// application returns (`design/rust-slice-values.md`, step 2b-iii-b-ii):
    /// `f(x).len()`. The slice's thin part is based on
    /// `AddressBase::PureFunctionApplication` of the same application, so one
    /// application names both components. It is keyed by the application's
    /// identity and is never an integer application of the function's name,
    /// which would be another function of that name. It follows the
    /// preexisting variants, so their derived order is unchanged.
    PureApplicationCount(SharedPureApplication),
}

/// The derived `Debug` spelling of every variant, except that a constant
/// keeps the spelling of the per-format variant it had before decision G9
/// (`Constant(7)`, `UInt32Constant(7)`, `Int64Constant(-1)`,
/// `UInt64Constant(7)`, `MachineIntegerConstant(..)`): a diagnostic that
/// prints a term with `{:?}` prints what it printed.
impl std::fmt::Debug for OldMachineTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ThreadHandle(id) => f.debug_tuple("ThreadHandle").field(id).finish(),
            Self::PureApplicationCount(application) => f
                .debug_tuple("PureApplicationCount")
                .field(application)
                .finish(),
            int32_constant!(bits) => f
                .debug_tuple("Constant")
                .field(&constant_u32(*bits))
                .finish(),
            uint32_constant!(bits) => f
                .debug_tuple("UInt32Constant")
                .field(&constant_u32(*bits))
                .finish(),
            int64_constant!(bits) => f
                .debug_tuple("Int64Constant")
                .field(&constant_i64(*bits))
                .finish(),
            uint64_constant!(bits) => f
                .debug_tuple("UInt64Constant")
                .field(&constant_u64(*bits))
                .finish(),
            Self::Constant { format, bits } => f
                .debug_tuple("MachineIntegerConstant")
                .field(&MachineIntegerConstant::from_term_bits(
                    format.format(),
                    *bits,
                ))
                .finish(),
            Self::Variable(variable) => f.debug_tuple("Variable").field(variable).finish(),
            Self::Binary {
                op,
                format,
                left,
                right,
            } => f
                .debug_struct("Binary")
                .field("op", op)
                .field("format", format)
                .field("left", left)
                .field("right", right)
                .finish(),
            Self::Unary {
                format,
                op,
                operand,
            } => f
                .debug_struct("Unary")
                .field("format", format)
                .field("op", op)
                .field("operand", operand)
                .finish(),
            Self::If {
                condition,
                then_term,
                else_term,
            } => f
                .debug_struct("If")
                .field("condition", condition)
                .field("then_term", then_term)
                .field("else_term", else_term)
                .finish(),
            Self::RangeFold {
                start,
                end,
                initial,
                accumulator,
                item,
                body,
            } => f
                .debug_struct("RangeFold")
                .field("start", start)
                .field("end", end)
                .field("initial", initial)
                .field("accumulator", accumulator)
                .field("item", item)
                .field("body", body)
                .finish(),
            Self::PureFunctionApplication { name, arguments } => f
                .debug_struct("PureFunctionApplication")
                .field("name", name)
                .field("arguments", arguments)
                .finish(),
            Self::ClickFunctionApplication { name, arguments } => f
                .debug_struct("ClickFunctionApplication")
                .field("name", name)
                .field("arguments", arguments)
                .finish(),
            Self::AlgebraicMatch { scrutinee, arms } => f
                .debug_struct("AlgebraicMatch")
                .field("scrutinee", scrutinee)
                .field("arms", arms)
                .finish(),
            Self::MemoryLoad(memory, pointer, kind) => f
                .debug_tuple("MemoryLoad")
                .field(memory)
                .field(pointer)
                .field(kind)
                .finish(),
            Self::IntegerAddress(pointer, class) => f
                .debug_tuple("IntegerAddress")
                .field(pointer)
                .field(class)
                .finish(),
            Self::IntegerToMachine { value, destination } => f
                .debug_struct("IntegerToMachine")
                .field("value", value)
                .field("destination", destination)
                .finish(),
            // A conversion prints as the variant its spelling replaced.
            Self::Cast {
                spelling: MachineCastSpelling::Generic,
                value,
                from,
                to,
            } => f
                .debug_struct("MachineIntegerCast")
                .field("value", value)
                .field("source", from)
                .field("destination", to)
                .finish(),
            Self::Cast {
                spelling, value, ..
            } => f.debug_tuple(spelling.name()).field(value).finish(),
            Self::Float32Negate(value) => f.debug_tuple("Float32Negate").field(value).finish(),
            Self::Float32Binary {
                operator,
                left,
                right,
            } => f
                .debug_struct("Float32Binary")
                .field("operator", operator)
                .field("left", left)
                .field("right", right)
                .finish(),
            Self::Float64Negate(value) => f.debug_tuple("Float64Negate").field(value).finish(),
            Self::Float64Binary {
                operator,
                left,
                right,
            } => f
                .debug_struct("Float64Binary")
                .field("operator", operator)
                .field("left", left)
                .field("right", right)
                .finish(),
            Self::BoolCast { to, value } => f
                .debug_struct("BoolCast")
                .field("to", to)
                .field("value", value)
                .finish(),
        }
    }
}

/// The operator of a machine binary term ([`OldMachineTerm::Binary`]).
/// Signedness comes from the term's format: `Divide`, `Remainder` and
/// `ShiftRight` are signed (arithmetic) at a signed format and unsigned
/// (logical) at an unsigned one.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum MachineBinaryOp {
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

/// The operator of a machine unary term ([`OldMachineTerm::Unary`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum MachineUnaryOp {
    BitwiseNot,
}

/// The relation of a machine comparison ([`OldConditionTerm::Compare`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CompareRelation {
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
    Equal,
}

/// The operation a machine overflow test ([`OldConditionTerm::Overflows`])
/// guards.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum OverflowOperation {
    Add,
    Subtract,
    Multiply,
    Divide,
    ShiftLeft,
}

/// Equality, hashing and order compare a condition's identity
/// ([`ConditionIdentity`]): a 32-bit equality is one fact whichever
/// signedness it is filed at (rule K6), so `Compare { UInt32, Equal }` and
/// `Compare { Int32, Equal }` over the same words are equal, hash alike and
/// order as equal. The `uint32` format is kept for presentation.
#[derive(Clone, Debug)]
pub enum OldConditionTerm {
    Constant(bool),
    Variable(Variable),
    /// Logical equality of immutable algebraic values, not a C comparison.
    AlgebraicEqual(Box<AlgebraicTerm>, Box<AlgebraicTerm>),
    /// `left REL right`, both operands read at `format`. A format of 8 to 32
    /// bits compares 32-bit words, 64 bits 64-bit words and 128 bits 128-bit
    /// words. Equality reads no sign, so an equality is filed at the signed
    /// format of its width, except that an equality of `uint32` values is
    /// filed at `uint32` for presentation; it is the same fact as at `int32`
    /// (rule K6, [`OldConditionTerm::fact_format`]). A narrow value's word is its canonical extension,
    /// which the `int32` order compares exactly, so a narrow comparison is
    /// filed at `int32` (`design/machine-integers.md`, "One condition
    /// family").
    Compare {
        format: MachineIntegerType,
        relation: CompareRelation,
        left: Box<OldMachineTerm>,
        right: Box<OldMachineTerm>,
    },
    /// Whether the exact result of `left op right`, the operands read at
    /// `format`, lies outside `format`: a signed overflow test is C's
    /// undefined behavior and Rust's panic, an unsigned one is wrapping, which
    /// is defined in C (`design/machine-integers.md`, "Decisions").
    Overflows {
        format: MachineIntegerType,
        op: OverflowOperation,
        left: Box<OldMachineTerm>,
        right: Box<OldMachineTerm>,
    },
    Float32(FloatCondition),
    Float64(FloatCondition),
    AddressOffsetEqual(Box<AddressOffset>, Box<AddressOffset>),
    AddressEqual(Box<Address>, Box<Address>),
    /// Specification pointer equality includes the designated object and bounds.
    PointerEqual(Box<Pointer>, Box<Pointer>),
    IntegerLessThan(SharedIntegerTerm, SharedIntegerTerm),
    IntegerLessEqual(SharedIntegerTerm, SharedIntegerTerm),
    IntegerGreaterThan(SharedIntegerTerm, SharedIntegerTerm),
    IntegerGreaterEqual(SharedIntegerTerm, SharedIntegerTerm),
    IntegerEqual(SharedIntegerTerm, SharedIntegerTerm),
    IntegerNotEqual(SharedIntegerTerm, SharedIntegerTerm),
    /// Click `Bool`, the logical sort (`design/machine-integers.md`, Stage
    /// 5): conditions are its terms, `Constant` and `Variable` above its
    /// literals and binders. The four forms below are its values that are
    /// not comparisons. They follow every other variant, so the derived
    /// order of the conditions before them is unchanged.
    ///
    /// The application of a `-> Bool` pure function. Rule L-Unfold relates
    /// it to the function's body ([`OldConditionTerm::bool_unfold_equation`]).
    BoolApplication(SharedPureApplication),
    /// `if condition { then } else { else }` over `Bool`. Rule L-If reads
    /// it as the case split ([`OldConditionTerm::open_bool_if`]), opened only
    /// on demand: by a decision of the conditional itself or by a proof
    /// step that asks for the split, never when it is assumed.
    BoolIf {
        condition: Box<OldConditionTerm>,
        then_condition: Box<OldConditionTerm>,
        else_condition: Box<OldConditionTerm>,
    },
    /// Logical equality of two `Bool` values, `a == b` (iff). Rule L-Eq: a
    /// true one merges the two values' classes in the e-graph, where their
    /// truth is shared; a false one contradicts that merge.
    BoolEqual(Box<OldConditionTerm>, Box<OldConditionTerm>),
}

/// A condition's identity: the condition itself, with a 32-bit equality's
/// format read as `int32` (rule K6). Borrowed, so building it is one match
/// on the root: no scan, no clone. The variants follow [`OldConditionTerm`]'s
/// order, so hashes and the derived order are unchanged elsewhere.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord)]
enum ConditionIdentity<'a> {
    Constant(bool),
    Variable(&'a Variable),
    AlgebraicEqual(&'a AlgebraicTerm, &'a AlgebraicTerm),
    Compare {
        format: MachineIntegerType,
        relation: CompareRelation,
        left: ComparisonSide<'a>,
        right: ComparisonSide<'a>,
    },
    Overflows {
        format: MachineIntegerType,
        op: OverflowOperation,
        left: &'a OldMachineTerm,
        right: &'a OldMachineTerm,
    },
    Float32(&'a FloatCondition),
    Float64(&'a FloatCondition),
    AddressOffsetEqual(&'a AddressOffset, &'a AddressOffset),
    AddressEqual(&'a Address, &'a Address),
    PointerEqual(&'a Pointer, &'a Pointer),
    IntegerLessThan(&'a SharedIntegerTerm, &'a SharedIntegerTerm),
    IntegerLessEqual(&'a SharedIntegerTerm, &'a SharedIntegerTerm),
    IntegerGreaterThan(&'a SharedIntegerTerm, &'a SharedIntegerTerm),
    IntegerGreaterEqual(&'a SharedIntegerTerm, &'a SharedIntegerTerm),
    IntegerEqual(&'a SharedIntegerTerm, &'a SharedIntegerTerm),
    IntegerNotEqual(&'a SharedIntegerTerm, &'a SharedIntegerTerm),
    BoolApplication(&'a SharedPureApplication),
    BoolIf {
        condition: &'a OldConditionTerm,
        then_condition: &'a OldConditionTerm,
        else_condition: &'a OldConditionTerm,
    },
    BoolEqual(&'a OldConditionTerm, &'a OldConditionTerm),
}

/// A comparison side as its fact identity reads it
/// ([`OldConditionTerm::comparison_fact`]): a term, or the value of a
/// constant of the comparison's identity format (an 8- or 16-bit format, or
/// `int32` for a 32-bit equality's constant of either spelling).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum ComparisonSide<'a> {
    Term(&'a OldMachineTerm),
    Value(i128),
}

impl<'a> ComparisonSide<'a> {
    /// The side as a term of its comparison's identity `format`: a term as
    /// itself, a value as that format's native constant.
    pub(crate) fn term(self, format: MachineIntegerType) -> std::borrow::Cow<'a, OldMachineTerm> {
        match self {
            Self::Term(term) => std::borrow::Cow::Borrowed(term),
            Self::Value(value) if format.format().bits() == 32 => {
                std::borrow::Cow::Owned(OldMachineTerm::constant_at32(format, value as u32))
            }
            Self::Value(value) => std::borrow::Cow::Owned(OldMachineTerm::machine_constant(
                MachineIntegerConstant::from_signed(format.format(), value)
                    .expect("an identity value lies in its narrow format's range"),
            )),
        }
    }
}

#[cfg(test)]
thread_local! {
    /// Calls of [`comparison_identity`], for its scaling test.
    static COMPARISON_IDENTITY_VISITS: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
}

/// The identity of the comparison `left REL right` at `format`. A native
/// 8- or 16-bit comparison and the signed `int32` comparison of its
/// operands' widenings are one fact (rule K8 at the fact level, as K6
/// makes a 32-bit equality one fact at either signedness): the promoted
/// comparison whose sides are widenings from one narrow format `S`, or
/// constants of `S`'s range, is identified at `S` over the widenings'
/// operands. Terms keep their written spelling; only identity, hashing,
/// order and the fact keys read this form. One match on each side; no
/// clone.
///
/// A 32-bit equality compares bits, which σ keeps (rule K6, a lookup-level
/// equivalence since σ is a node of its own): it is identified at `int32`
/// whichever signedness it is written at, each side read through one σ and
/// a constant of either spelling read as its bits. So `u == v` at `uint32`,
/// `u as int32 == v as int32` and `u == x as uint32` with `v == x as
/// uint32` are one fact. The terms keep their format and their σ.
fn comparison_identity<'a>(
    format: MachineIntegerType,
    relation: CompareRelation,
    left: &'a OldMachineTerm,
    right: &'a OldMachineTerm,
) -> (MachineIntegerType, ComparisonSide<'a>, ComparisonSide<'a>) {
    #[cfg(test)]
    COMPARISON_IDENTITY_VISITS.with(|visits| visits.set(visits.get() + 1));
    let format = OldConditionTerm::fact_format(format, relation);
    let bits = format.format().bits();
    let (left, right) = if relation == CompareRelation::Equal && bits == 32 {
        (left.sign_cast32_bits(), right.sign_cast32_bits())
    } else {
        (left, right)
    };
    // A 32-bit equality's constant side, of either spelling, as its bits.
    let side = |term: &'a OldMachineTerm| match term.constant32() {
        Some(bits) if relation == CompareRelation::Equal && format == MachineIntegerType::Int32 => {
            ComparisonSide::Value(i128::from(bits as i32))
        }
        _ => ComparisonSide::Term(term),
    };
    if bits < 32 {
        let side = |term: &'a OldMachineTerm| match term {
            native_constant!(constant_format, bits) if *constant_format == format => {
                MachineIntegerConstant::from_term_bits(format.format(), *bits)
                    .to_i128()
                    .map_or(ComparisonSide::Term(term), ComparisonSide::Value)
            }
            _ => ComparisonSide::Term(term),
        };
        return (format, side(left), side(right));
    }
    if format == MachineIntegerType::Int32 {
        let source = left
            .narrow_widening32_operand()
            .or_else(|| right.narrow_widening32_operand())
            .map(|(source, _)| source);
        if let Some(source) = source {
            let (low, high) = {
                let narrow = source.format();
                let bits = narrow.bits();
                if narrow.is_signed() {
                    (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)
                } else {
                    (0, (1i128 << bits) - 1)
                }
            };
            let side = |term: &'a OldMachineTerm| match term {
                bits32_constant!(value) if relation == CompareRelation::Equal => {
                    let value = i128::from(constant_u32(*value) as i32);
                    (low <= value && value <= high).then_some(ComparisonSide::Value(value))
                }
                int32_constant!(value) => {
                    let value = i128::from(constant_u32(*value) as i32);
                    (low <= value && value <= high).then_some(ComparisonSide::Value(value))
                }
                term => match term.narrow_widening32_operand() {
                    Some((operand_source, operand)) if operand_source == source => {
                        Some(ComparisonSide::Term(operand))
                    }
                    _ => None,
                },
            };
            if let (Some(left), Some(right)) = (side(left), side(right)) {
                return (source, left, right);
            }
        }
    }
    (format, side(left), side(right))
}

impl OldConditionTerm {
    /// The format a comparison is identified at as a fact: a 32-bit
    /// equality at `int32` whichever signedness it is written at (rule K6,
    /// a lookup-level equivalence; [`comparison_identity`] also reads its
    /// sides through σ); every other comparison at its own format. The
    /// term keeps the format it is written at.
    pub(crate) fn fact_format(
        format: MachineIntegerType,
        relation: CompareRelation,
    ) -> MachineIntegerType {
        if relation == CompareRelation::Equal && format == MachineIntegerType::UInt32 {
            MachineIntegerType::Int32
        } else {
            format
        }
    }

    fn identity(&self) -> ConditionIdentity<'_> {
        use ConditionIdentity as I;
        match self {
            Self::Constant(value) => I::Constant(*value),
            Self::Variable(variable) => I::Variable(variable),
            Self::AlgebraicEqual(left, right) => I::AlgebraicEqual(left, right),
            Self::Compare {
                format,
                relation,
                left,
                right,
            } => {
                let (format, left, right) = comparison_identity(*format, *relation, left, right);
                I::Compare {
                    format,
                    relation: *relation,
                    left,
                    right,
                }
            }
            Self::Overflows {
                format,
                op,
                left,
                right,
            } => I::Overflows {
                format: *format,
                op: *op,
                left,
                right,
            },
            Self::Float32(condition) => I::Float32(condition),
            Self::Float64(condition) => I::Float64(condition),
            Self::AddressOffsetEqual(left, right) => I::AddressOffsetEqual(left, right),
            Self::AddressEqual(left, right) => I::AddressEqual(left, right),
            Self::PointerEqual(left, right) => I::PointerEqual(left, right),
            // An Integer comparison is one fact with the comparison of its
            // sides read through their observations' value relations
            // (rule W): `to_integer(x as int32) <= 7` and
            // `to_integer(x) <= 7` share identity, hashing and order. The
            // reading is cached on each side, O(1) after its first use.
            Self::IntegerLessThan(left, right) => {
                I::IntegerLessThan(left.read_through_ref(), right.read_through_ref())
            }
            Self::IntegerLessEqual(left, right) => {
                I::IntegerLessEqual(left.read_through_ref(), right.read_through_ref())
            }
            Self::IntegerGreaterThan(left, right) => {
                I::IntegerGreaterThan(left.read_through_ref(), right.read_through_ref())
            }
            Self::IntegerGreaterEqual(left, right) => {
                I::IntegerGreaterEqual(left.read_through_ref(), right.read_through_ref())
            }
            Self::IntegerEqual(left, right) => {
                I::IntegerEqual(left.read_through_ref(), right.read_through_ref())
            }
            Self::IntegerNotEqual(left, right) => {
                I::IntegerNotEqual(left.read_through_ref(), right.read_through_ref())
            }
            Self::BoolApplication(application) => I::BoolApplication(application),
            Self::BoolIf {
                condition,
                then_condition,
                else_condition,
            } => I::BoolIf {
                condition,
                then_condition,
                else_condition,
            },
            Self::BoolEqual(left, right) => I::BoolEqual(left, right),
        }
    }
}

impl OldConditionTerm {
    /// A machine comparison as its fact identity reads it: its identity
    /// format, relation and sides ([`comparison_identity`]). A native 8- or
    /// 16-bit comparison and the `int32` comparison of its operands'
    /// widenings give the same reading. `None` for every other condition.
    /// One match on the root and each side; no clone.
    pub(crate) fn comparison_fact(
        &self,
    ) -> Option<(
        MachineIntegerType,
        CompareRelation,
        ComparisonSide<'_>,
        ComparisonSide<'_>,
    )> {
        let Self::Compare {
            format,
            relation,
            left,
            right,
        } = self
        else {
            return None;
        };
        let (format, left, right) = comparison_identity(*format, *relation, left, right);
        Some((format, *relation, left, right))
    }

    /// [`OldConditionTerm::as_bitvector_comparison`] at the condition's fact
    /// identity: the comparison a structural fact key files. A promoted
    /// comparison of widenings from one narrow format reads as the native
    /// comparison of their operands (a constant as that format's native
    /// constant), so both spellings of one fact share a key. The only
    /// allocation is a narrow constant side.
    pub(crate) fn as_fact_comparison(
        &self,
    ) -> Option<(
        crate::kernel::primitives::BitvectorComparisonOp,
        std::borrow::Cow<'_, OldMachineTerm>,
        std::borrow::Cow<'_, OldMachineTerm>,
    )> {
        if let Some((format, relation, left, right)) = self.comparison_fact() {
            return Some((
                crate::kernel::primitives::BitvectorComparisonOp::Compare(format, relation),
                left.term(format),
                right.term(format),
            ));
        }
        self.as_bitvector_comparison()
            .map(|(operator, left, right)| {
                (
                    operator,
                    std::borrow::Cow::Borrowed(left),
                    std::borrow::Cow::Borrowed(right),
                )
            })
    }
}

impl PartialEq for OldConditionTerm {
    fn eq(&self, other: &Self) -> bool {
        self.identity() == other.identity()
    }
}

impl Eq for OldConditionTerm {}

impl std::hash::Hash for OldConditionTerm {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.identity().hash(state)
    }
}

impl PartialOrd for OldConditionTerm {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OldConditionTerm {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.identity().cmp(&other.identity())
    }
}

/// Matches every machine comparison and overflow test, at any format.
macro_rules! binary_bitvector_condition {
    ($left:pat, $right:pat) => {
        $crate::kernel::OldConditionTerm::Compare {
            left: $left,
            right: $right,
            ..
        } | $crate::kernel::OldConditionTerm::Overflows {
            left: $left,
            right: $right,
            ..
        }
    };
}
pub(crate) use binary_bitvector_condition;

/// Matches the machine operation `$left op $right` at one format, as
/// `binary_term!(Int32, Add, left, right)`, or with `..` in place of the
/// operands. The 32-bit sign-free operators are at `Int32`; see
/// [`OldMachineTerm::Binary`].
///
/// `Bits32` in place of the format matches the operation at either 32-bit
/// format, for a rule that reads only the operation's bits; `Bits32 @ f`
/// also binds the matched format to `f`, so a rule that rebuilds the node
/// keeps it (`design/machine-integers.md`, "Every format its own nodes").
/// A rule that reads a signed result, an order or an interval names its
/// format.
macro_rules! binary_term {
    (Bits32, $op:ident, ..) => {
        $crate::kernel::OldMachineTerm::Binary {
            op: $crate::kernel::MachineBinaryOp::$op,
            format: $crate::kernel::MachineIntegerType::Int32
                | $crate::kernel::MachineIntegerType::UInt32,
            ..
        }
    };
    (Bits32, $op:ident, $left:pat, $right:pat) => {
        $crate::kernel::OldMachineTerm::Binary {
            op: $crate::kernel::MachineBinaryOp::$op,
            format: $crate::kernel::MachineIntegerType::Int32
                | $crate::kernel::MachineIntegerType::UInt32,
            left: $left,
            right: $right,
        }
    };
    (Bits32 @ $bound:ident, $op:ident, $left:pat, $right:pat) => {
        $crate::kernel::OldMachineTerm::Binary {
            op: $crate::kernel::MachineBinaryOp::$op,
            format:
                $bound @ ($crate::kernel::MachineIntegerType::Int32
                | $crate::kernel::MachineIntegerType::UInt32),
            left: $left,
            right: $right,
        }
    };
    ($format:ident, $op:ident, ..) => {
        $crate::kernel::OldMachineTerm::Binary {
            op: $crate::kernel::MachineBinaryOp::$op,
            format: $crate::kernel::MachineIntegerType::$format,
            ..
        }
    };
    ($format:ident, $op:ident, $left:pat, $right:pat) => {
        $crate::kernel::OldMachineTerm::Binary {
            op: $crate::kernel::MachineBinaryOp::$op,
            format: $crate::kernel::MachineIntegerType::$format,
            left: $left,
            right: $right,
        }
    };
}
pub(crate) use binary_term;

/// Builds the bare machine node `$left op $right` at one format, unfolded,
/// from boxed operands: `binary_node!(Int32, Add, left, right)`, or at a
/// format value, `binary_node!(@ format, Add, left, right)`. The folding
/// constructors (`OldMachineTerm::add`, `machine_binary`, ...) simplify.
macro_rules! binary_node {
    (@ $format:expr, $op:ident, $left:expr, $right:expr $(,)?) => {
        $crate::kernel::OldMachineTerm::Binary {
            op: $crate::kernel::MachineBinaryOp::$op,
            format: $format,
            left: $left,
            right: $right,
        }
    };
    ($format:ident, $op:ident, $left:expr, $right:expr $(,)?) => {
        $crate::kernel::OldMachineTerm::Binary {
            op: $crate::kernel::MachineBinaryOp::$op,
            format: $crate::kernel::MachineIntegerType::$format,
            left: $left,
            right: $right,
        }
    };
}
pub(crate) use binary_node;

/// Matches the machine operation `op $operand` at one format, as
/// `unary_term!(Int32, BitwiseNot, operand)`; `Bits32` (and `Bits32 @ f`)
/// as for [`binary_term`].
macro_rules! unary_term {
    (Bits32, $op:ident, ..) => {
        $crate::kernel::OldMachineTerm::Unary {
            format: $crate::kernel::MachineIntegerType::Int32
                | $crate::kernel::MachineIntegerType::UInt32,
            op: $crate::kernel::MachineUnaryOp::$op,
            ..
        }
    };
    (Bits32, $op:ident, $operand:pat) => {
        $crate::kernel::OldMachineTerm::Unary {
            format: $crate::kernel::MachineIntegerType::Int32
                | $crate::kernel::MachineIntegerType::UInt32,
            op: $crate::kernel::MachineUnaryOp::$op,
            operand: $operand,
        }
    };
    (Bits32 @ $bound:ident, $op:ident, $operand:pat) => {
        $crate::kernel::OldMachineTerm::Unary {
            format:
                $bound @ ($crate::kernel::MachineIntegerType::Int32
                | $crate::kernel::MachineIntegerType::UInt32),
            op: $crate::kernel::MachineUnaryOp::$op,
            operand: $operand,
        }
    };
    ($format:ident, $op:ident, ..) => {
        $crate::kernel::OldMachineTerm::Unary {
            format: $crate::kernel::MachineIntegerType::$format,
            op: $crate::kernel::MachineUnaryOp::$op,
            ..
        }
    };
    ($format:ident, $op:ident, $operand:pat) => {
        $crate::kernel::OldMachineTerm::Unary {
            format: $crate::kernel::MachineIntegerType::$format,
            op: $crate::kernel::MachineUnaryOp::$op,
            operand: $operand,
        }
    };
}
pub(crate) use unary_term;

/// Builds the bare machine node `op $operand` at one format from a boxed
/// operand: `unary_node!(Int32, BitwiseNot, operand)`.
macro_rules! unary_node {
    ($format:ident, $op:ident, $operand:expr $(,)?) => {
        $crate::kernel::OldMachineTerm::Unary {
            format: $crate::kernel::MachineIntegerType::$format,
            op: $crate::kernel::MachineUnaryOp::$op,
            operand: $operand,
        }
    };
}
pub(crate) use unary_node;

/// The bits a 32-bit constant pattern (`int32_constant!`,
/// `uint32_constant!`, `bits32_constant!`) bound, as the 32-bit word.
pub(crate) const fn constant_u32(bits: u128) -> u32 {
    bits as u32
}

/// The bits an `int64_constant!` pattern bound, as the `int64` value.
pub(crate) const fn constant_i64(bits: u128) -> i64 {
    bits as u64 as i64
}

/// The bits a `uint64_constant!` pattern bound, as the `uint64` value.
pub(crate) const fn constant_u64(bits: u128) -> u64 {
    bits as u64
}

/// Matches the `int32` constant whose bits match `$bits` (a `u128`
/// pattern), as `int32_constant!(0)` or `int32_constant!(bits)`; see
/// [`OldMachineTerm::Constant`].
macro_rules! int32_constant {
    ($bits:pat $(,)?) => {
        $crate::kernel::OldMachineTerm::Constant {
            format: $crate::kernel::MachineIntegerType::Int32,
            bits: $bits,
        }
    };
}
pub(crate) use int32_constant;

/// Matches the `uint32` constant whose bits match `$bits`.
macro_rules! uint32_constant {
    ($bits:pat $(,)?) => {
        $crate::kernel::OldMachineTerm::Constant {
            format: $crate::kernel::MachineIntegerType::UInt32,
            bits: $bits,
        }
    };
}
pub(crate) use uint32_constant;

/// Matches a 32-bit constant of either format whose bits match `$bits`;
/// `bits32_constant!(f @ bits)` also binds the format to `f`.
macro_rules! bits32_constant {
    ($format:ident @ $bits:pat $(,)?) => {
        $crate::kernel::OldMachineTerm::Constant {
            format:
                $format @ ($crate::kernel::MachineIntegerType::Int32
                | $crate::kernel::MachineIntegerType::UInt32),
            bits: $bits,
        }
    };
    ($bits:pat $(,)?) => {
        $crate::kernel::OldMachineTerm::Constant {
            format: $crate::kernel::MachineIntegerType::Int32
                | $crate::kernel::MachineIntegerType::UInt32,
            bits: $bits,
        }
    };
}
pub(crate) use bits32_constant;

/// Matches the `int64` constant whose bits match `$bits`. The bits are the
/// value's two's complement in 64 bits; read the value with `as u64 as i64`.
macro_rules! int64_constant {
    ($bits:pat $(,)?) => {
        $crate::kernel::OldMachineTerm::Constant {
            format: $crate::kernel::MachineIntegerType::Int64,
            bits: $bits,
        }
    };
}
pub(crate) use int64_constant;

/// Matches the `uint64` constant whose bits match `$bits`.
macro_rules! uint64_constant {
    ($bits:pat $(,)?) => {
        $crate::kernel::OldMachineTerm::Constant {
            format: $crate::kernel::MachineIntegerType::UInt64,
            bits: $bits,
        }
    };
}
pub(crate) use uint64_constant;

/// Matches a constant of the 8-, 16- or 128-bit formats, the constants that
/// are not words (a native narrow value or a 128-bit value), binding its
/// format and bits.
macro_rules! native_constant {
    (_, $bits:pat $(,)?) => {
        $crate::kernel::OldMachineTerm::Constant {
            format: $crate::kernel::MachineIntegerType::Int8
                | $crate::kernel::MachineIntegerType::UInt8
                | $crate::kernel::MachineIntegerType::Int16
                | $crate::kernel::MachineIntegerType::UInt16
                | $crate::kernel::MachineIntegerType::Int128
                | $crate::kernel::MachineIntegerType::UInt128,
            bits: $bits,
        }
    };
    ($format:ident, $bits:pat $(,)?) => {
        $crate::kernel::OldMachineTerm::Constant {
            format:
                $format @ ($crate::kernel::MachineIntegerType::Int8
                | $crate::kernel::MachineIntegerType::UInt8
                | $crate::kernel::MachineIntegerType::Int16
                | $crate::kernel::MachineIntegerType::UInt16
                | $crate::kernel::MachineIntegerType::Int128
                | $crate::kernel::MachineIntegerType::UInt128),
            bits: $bits,
        }
    };
}
pub(crate) use native_constant;

/// Matches every two-operand 32-bit [`OldMachineTerm`] operation, binding the operands to `$left`
/// and `$right`.
macro_rules! binary_bitvector32_term {
    ($left:pat, $right:pat) => {
        $crate::kernel::OldMachineTerm::Binary {
            format: $crate::kernel::MachineIntegerType::Int32
                | $crate::kernel::MachineIntegerType::UInt32,
            left: $left,
            right: $right,
            ..
        }
    };
}
pub(crate) use binary_bitvector32_term;

/// Matches every two-operand [`OldMachineTerm`] operation that is not at a 32-bit format, binding
/// the operands to `$left` and `$right`. Only the 64-bit formats, signed or unsigned, are built
/// there (see [`OldMachineTerm::Binary`]); the others are listed so that this and
/// [`binary_bitvector32_term`] together match every `Binary` node.
macro_rules! binary_wide_term {
    (..) => {
        $crate::kernel::OldMachineTerm::Binary {
            format: $crate::kernel::MachineIntegerType::Int64
                | $crate::kernel::MachineIntegerType::UInt64
                | $crate::kernel::MachineIntegerType::Int8
                | $crate::kernel::MachineIntegerType::Int16
                | $crate::kernel::MachineIntegerType::UInt8
                | $crate::kernel::MachineIntegerType::UInt16
                | $crate::kernel::MachineIntegerType::Int128
                | $crate::kernel::MachineIntegerType::UInt128,
            ..
        }
    };
    ($left:pat, $right:pat) => {
        $crate::kernel::OldMachineTerm::Binary {
            format: $crate::kernel::MachineIntegerType::Int64
                | $crate::kernel::MachineIntegerType::UInt64
                | $crate::kernel::MachineIntegerType::Int8
                | $crate::kernel::MachineIntegerType::Int16
                | $crate::kernel::MachineIntegerType::UInt8
                | $crate::kernel::MachineIntegerType::UInt16
                | $crate::kernel::MachineIntegerType::Int128
                | $crate::kernel::MachineIntegerType::UInt128,
            left: $left,
            right: $right,
            ..
        }
    };
}
pub(crate) use binary_wide_term;

/// Matches every one-operand machine operator node ([`OldMachineTerm::Unary`]) that is not at a
/// 32-bit format, binding its operand to `$operand`. Only the 64-bit complements are built there;
/// with `unary_term!(Bits32, BitwiseNot, ..)` it matches every `Unary` node.
macro_rules! unary_wide_term {
    (..) => {
        $crate::kernel::OldMachineTerm::Unary {
            format: $crate::kernel::MachineIntegerType::Int64
                | $crate::kernel::MachineIntegerType::UInt64
                | $crate::kernel::MachineIntegerType::Int8
                | $crate::kernel::MachineIntegerType::Int16
                | $crate::kernel::MachineIntegerType::UInt8
                | $crate::kernel::MachineIntegerType::UInt16
                | $crate::kernel::MachineIntegerType::Int128
                | $crate::kernel::MachineIntegerType::UInt128,
            ..
        }
    };
    ($operand:pat) => {
        $crate::kernel::OldMachineTerm::Unary {
            format: $crate::kernel::MachineIntegerType::Int64
                | $crate::kernel::MachineIntegerType::UInt64
                | $crate::kernel::MachineIntegerType::Int8
                | $crate::kernel::MachineIntegerType::Int16
                | $crate::kernel::MachineIntegerType::UInt8
                | $crate::kernel::MachineIntegerType::UInt16
                | $crate::kernel::MachineIntegerType::Int128
                | $crate::kernel::MachineIntegerType::UInt128,
            operand: $operand,
            ..
        }
    };
}
pub(crate) use unary_wide_term;

/// Matches every two-operand [`OldMachineTerm`] operation of any width, binding the operands to
/// `$left` and `$right`.
macro_rules! binary_machine_term {
    (..) => {
        $crate::kernel::OldMachineTerm::Binary { .. }
    };
    ($left:pat, $right:pat) => {
        $crate::kernel::OldMachineTerm::Binary {
            left: $left,
            right: $right,
            ..
        }
    };
}
pub(crate) use binary_machine_term;

/// Matches every [`OldConditionTerm`] comparison of two mathematical integers, binding the operands to
/// `$left` and `$right`.
macro_rules! integer_comparison_condition {
    ($left:pat, $right:pat) => {
        $crate::kernel::OldConditionTerm::IntegerLessThan($left, $right)
            | $crate::kernel::OldConditionTerm::IntegerLessEqual($left, $right)
            | $crate::kernel::OldConditionTerm::IntegerGreaterThan($left, $right)
            | $crate::kernel::OldConditionTerm::IntegerGreaterEqual($left, $right)
            | $crate::kernel::OldConditionTerm::IntegerEqual($left, $right)
            | $crate::kernel::OldConditionTerm::IntegerNotEqual($left, $right)
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

/// Matches every binary operator [`ProgramExpression`]: arithmetic, bitwise, comparison and logical,
/// binding the operands to `$left` and `$right`.
macro_rules! binary_c_operation {
    ($left:pat, $right:pat) => {
        $crate::kernel::ProgramExpression::Add($left, $right)
            | $crate::kernel::ProgramExpression::Subtract($left, $right)
            | $crate::kernel::ProgramExpression::Multiply($left, $right)
            | $crate::kernel::ProgramExpression::Divide($left, $right)
            | $crate::kernel::ProgramExpression::Remainder($left, $right)
            | $crate::kernel::ProgramExpression::BitwiseAnd($left, $right)
            | $crate::kernel::ProgramExpression::BitwiseOr($left, $right)
            | $crate::kernel::ProgramExpression::BitwiseXor($left, $right)
            | $crate::kernel::ProgramExpression::ShiftLeft($left, $right)
            | $crate::kernel::ProgramExpression::RustShiftLeft($left, $right)
            | $crate::kernel::ProgramExpression::ShiftRight($left, $right)
            | $crate::kernel::ProgramExpression::RustShiftRight($left, $right)
            | $crate::kernel::ProgramExpression::Equal($left, $right)
            | $crate::kernel::ProgramExpression::NotEqual($left, $right)
            | $crate::kernel::ProgramExpression::LessThan($left, $right)
            | $crate::kernel::ProgramExpression::LessEqual($left, $right)
            | $crate::kernel::ProgramExpression::GreaterThan($left, $right)
            | $crate::kernel::ProgramExpression::GreaterEqual($left, $right)
            | $crate::kernel::ProgramExpression::And($left, $right)
            | $crate::kernel::ProgramExpression::Or($left, $right)
    };
}
pub(crate) use binary_c_operation;

/// Matches every two-operand [`ProgramExpression`]: the binary operators and indexing, binding the
/// operands to `$left` and `$right`.
macro_rules! binary_c_expression {
    ($left:pat, $right:pat) => {
        $crate::kernel::binary_c_operation!($left, $right)
            | $crate::kernel::ProgramExpression::Index($left, $right)
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
            | $crate::kernel::SpecExpression::RustShiftLeft($left, $right)
            | $crate::kernel::SpecExpression::ShiftRight($left, $right)
            | $crate::kernel::SpecExpression::RustShiftRight($left, $right)
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

/// Matches every integer [`ProgramValue`] that promotes to `int`, binding its operand to `$term`.
macro_rules! int_promoted_c_value {
    ($term:pat) => {
        $crate::kernel::ProgramValue::Int8($term)
            | $crate::kernel::ProgramValue::Int16($term)
            | $crate::kernel::ProgramValue::Int32($term)
            | $crate::kernel::ProgramValue::UInt8($term)
            | $crate::kernel::ProgramValue::UInt16($term)
    };
}
pub(crate) use int_promoted_c_value;

/// Matches every integer [`ProgramValue`] of at most 32 bits, binding its operand to `$term`.
macro_rules! integer32_c_value {
    ($term:pat) => {
        $crate::kernel::ProgramValue::Int8($term)
            | $crate::kernel::ProgramValue::Int16($term)
            | $crate::kernel::ProgramValue::Int32($term)
            | $crate::kernel::ProgramValue::UInt8($term)
            | $crate::kernel::ProgramValue::UInt16($term)
            | $crate::kernel::ProgramValue::UInt32($term)
    };
}
pub(crate) use integer32_c_value;

/// Matches every integer [`ProgramValue`] of at most 64 bits, binding its operand to `$term`.
macro_rules! integer64_c_value {
    ($term:pat) => {
        $crate::kernel::ProgramValue::Int8($term)
            | $crate::kernel::ProgramValue::Int16($term)
            | $crate::kernel::ProgramValue::Int32($term)
            | $crate::kernel::ProgramValue::UInt8($term)
            | $crate::kernel::ProgramValue::UInt16($term)
            | $crate::kernel::ProgramValue::UInt32($term)
            | $crate::kernel::ProgramValue::Int64($term)
            | $crate::kernel::ProgramValue::UInt64($term)
    };
}
pub(crate) use integer64_c_value;

/// Matches every integer [`ProgramValue`], binding its operand to `$term`.
macro_rules! integer_c_value {
    ($term:pat) => {
        $crate::kernel::ProgramValue::Int8($term)
            | $crate::kernel::ProgramValue::Int16($term)
            | $crate::kernel::ProgramValue::Int32($term)
            | $crate::kernel::ProgramValue::UInt8($term)
            | $crate::kernel::ProgramValue::UInt16($term)
            | $crate::kernel::ProgramValue::UInt32($term)
            | $crate::kernel::ProgramValue::Int64($term)
            | $crate::kernel::ProgramValue::UInt64($term)
            | $crate::kernel::ProgramValue::Int128($term)
            | $crate::kernel::ProgramValue::UInt128($term)
    };
}
pub(crate) use integer_c_value;

/// Matches every arithmetic [`ProgramValue`]: `_Bool`, the integers and the floating types, binding its
/// operand to `$term`.
macro_rules! arithmetic_c_value {
    ($term:pat) => {
        $crate::kernel::ProgramValue::Bool($term)
            | $crate::kernel::ProgramValue::Int8($term)
            | $crate::kernel::ProgramValue::Int16($term)
            | $crate::kernel::ProgramValue::Int32($term)
            | $crate::kernel::ProgramValue::UInt8($term)
            | $crate::kernel::ProgramValue::UInt16($term)
            | $crate::kernel::ProgramValue::UInt32($term)
            | $crate::kernel::ProgramValue::Int64($term)
            | $crate::kernel::ProgramValue::UInt64($term)
            | $crate::kernel::ProgramValue::Int128($term)
            | $crate::kernel::ProgramValue::UInt128($term)
            | $crate::kernel::ProgramValue::Float32($term)
            | $crate::kernel::ProgramValue::Float64($term)
    };
}
pub(crate) use arithmetic_c_value;

/// The constructor that spelled a [`OldMachineTerm::Cast`] (and a kernel
/// `MachineCast`): the generic conversion, or one of the six legacy
/// per-pair conversions, each with fixed formats. Part of a conversion's
/// identity, so the legacy and generic spellings of one pair of formats stay
/// different terms, as they were different variants.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum MachineCastSpelling {
    Generic,
    Int64From32,
    UInt64From32,
    /// The low word of a 64-bit operand, read as the bits of a `uint64`.
    UInt32From64,
    Int64FromUInt32,
    UInt64FromInt32,
    UInt64FromInt64,
}

impl MachineCastSpelling {
    /// The source and destination formats a legacy spelling fixes, `None`
    /// for [`Self::Generic`].
    pub(crate) const fn legacy_formats(self) -> Option<(MachineIntegerType, MachineIntegerType)> {
        use MachineIntegerType as T;
        Some(match self {
            Self::Generic => return None,
            Self::Int64From32 => (T::Int32, T::Int64),
            Self::UInt64From32 => (T::UInt32, T::UInt64),
            Self::UInt32From64 => (T::UInt64, T::UInt32),
            Self::Int64FromUInt32 => (T::UInt32, T::Int64),
            Self::UInt64FromInt32 => (T::Int32, T::UInt64),
            Self::UInt64FromInt64 => (T::Int64, T::UInt64),
        })
    }

    /// The name of the variant this spelling replaced, for `Debug`.
    pub(crate) const fn name(self) -> &'static str {
        match self {
            Self::Generic => "MachineIntegerCast",
            Self::Int64From32 => "Int64From32",
            Self::UInt64From32 => "UInt64From32",
            Self::UInt32From64 => "UInt32From64",
            Self::Int64FromUInt32 => "Int64FromUInt32",
            Self::UInt64FromInt32 => "UInt64FromInt32",
            Self::UInt64FromInt64 => "UInt64FromInt64",
        }
    }
}

/// Matches a legacy-spelled [`OldMachineTerm::Cast`], binding its boxed
/// operand: `cast_term!(Int64From32, value)`. A legacy spelling fixes its
/// formats ([`MachineCastSpelling::legacy_formats`]); build one with
/// [`OldMachineTerm::legacy_cast`]. A generic conversion is the struct
/// `Cast { spelling: Generic, .. }`.
macro_rules! cast_term {
    ($spelling:ident, _ $(,)?) => {
        $crate::kernel::OldMachineTerm::Cast {
            spelling: $crate::kernel::MachineCastSpelling::$spelling,
            ..
        }
    };
    ($spelling:ident, $value:pat $(,)?) => {
        $crate::kernel::OldMachineTerm::Cast {
            spelling: $crate::kernel::MachineCastSpelling::$spelling,
            value: $value,
            ..
        }
    };
}
pub(crate) use cast_term;

/// Matches the [`BitvectorUnaryOp`] of a legacy-spelled conversion:
/// `cast_op!(UInt64FromInt64)`; build one with
/// [`BitvectorUnaryOp::legacy_cast`].
macro_rules! cast_op {
    ($spelling:ident) => {
        $crate::kernel::BitvectorUnaryOp::Cast {
            spelling: $crate::kernel::MachineCastSpelling::$spelling,
            ..
        }
    };
}
pub(crate) use cast_op;

/// Matches every one-operand [`OldMachineTerm`] operation and conversion, binding its operand to
/// `$term`.
macro_rules! unary_machine_term {
    ($term:pat) => {
        $crate::kernel::OldMachineTerm::Unary { operand: $term, .. }
            | $crate::kernel::OldMachineTerm::Cast { value: $term, .. }
            | $crate::kernel::OldMachineTerm::Float32Negate($term)
            | $crate::kernel::OldMachineTerm::Float64Negate($term)
    };
}
pub(crate) use unary_machine_term;

/// Which decodings of one pointer cell's bytes are one pointer value
/// (`design/loads.md`, "Pointers"). Every object-pointer type decodes the
/// same bytes to the same pointer, so the pointee type is no part of a
/// pointer load's identity. A function pointer is a different value: its
/// load has no object domain, and a store of one answers no object-pointer
/// load, nor the reverse.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) enum PointerLoadCategory {
    Object,
    Function,
}

impl PointerLoadCategory {
    /// The category of an eight-byte pointer decoded at `value_type`, or
    /// `None` for a type that is no single pointer cell.
    pub(crate) fn of_type(value_type: ProgramType) -> Option<Self> {
        match value_type {
            ProgramType::FunctionPointer(_) => Some(Self::Function),
            // An array of pointers is an aggregate, not one pointer cell.
            ProgramType::PointerArray(_, _) => None,
            value_type if value_type.is_pointer() => Some(Self::Object),
            _ => None,
        }
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
    /// The load itself. It has no category or pointee type: both belong
    /// to the `Pointer` term that decodes it (`design/loads.md`).
    pub(crate) identity: Load,
    pub(crate) defining_memory: SharedMemory,
    pub(crate) point: ProgramPoint,
    pub(crate) defining_address: Address,
    pub(crate) displacement: AddressOffset,
}

pub(crate) type ObjectTypeRequirements =
    imbl::OrdMap<usize, crate::kernel::effective_type::CAccessClass>;

/// Positive object-type evidence, with the entry assumptions its use consumes.
/// The assumptions are proof metadata; they do not change a numeric address.
#[derive(Clone, Debug)]
pub struct ObjectTypeEvidence {
    pub(super) class: crate::kernel::effective_type::CAccessClass,
    pub(super) checked: bool,
    pub(super) premise_fingerprint: u64,
    pub(super) premises: imbl::OrdMap<(u64, usize), Arc<ObjectTypePremise>>,
}

#[derive(Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) struct ObjectTypePremise {
    pub(super) parameter: usize,
    pub(super) class: crate::kernel::effective_type::CAccessClass,
    pub(super) scope: u64,
}

/// Exact non-address metadata shared by native and retained certification.
/// Optional default qualifier storage is not itself part of this reading.
#[derive(PartialEq, Eq)]
pub(in crate::kernel) struct RetainedPointerMetadata<'a> {
    program_type: ProgramType,
    bounds_known: bool,
    declared_class: Option<&'a crate::kernel::effective_type::CAccessClass>,
    evidence: Option<&'a ObjectTypeEvidence>,
}

impl SubobjectBounds {
    /// The fact that these opaque bounds cover `range`.
    pub(crate) fn coverage_fact(&self, range: &MemoryRange) -> Proposition {
        let pointer = |pointer: Address| {
            Term::ProgramValue(
                ProgramValue::Pointer(Pointer::new(pointer, ProgramType::VoidPointer)).into(),
            )
        };
        let width = range.element_width();
        if let Some((start, end)) = range.wide_bounds() {
            return Proposition::Predicate {
                name: format!("{SUBOBJECT_COVERS_PREDICATE_PREFIX}{width}"),
                arguments: vec![
                    pointer(self.start().clone()),
                    pointer(range.base().clone()),
                    Term::ProgramValue((ProgramValue::UInt64(start.clone())).into()),
                    Term::ProgramValue((ProgramValue::UInt64(end.clone())).into()),
                ],
            };
        }
        Proposition::Predicate {
            name: format!("{SUBOBJECT_COVERS_PREDICATE_PREFIX}{width}"),
            arguments: vec![
                pointer(self.start().clone()),
                pointer(
                    range
                        .base()
                        .offset_by_elements(range.start().clone(), width),
                ),
                pointer(range.base().offset_by_elements(range.end().clone(), width)),
            ],
        }
    }

    /// The range a coverage fact names: its first element's address, its
    /// element count and its element width.
    pub(crate) fn covered_range(
        proposition: &Proposition,
    ) -> Option<(Address, OldMachineTerm, u32)> {
        let Proposition::Predicate { name, arguments } = proposition else {
            return None;
        };
        let width = name
            .strip_prefix(SUBOBJECT_COVERS_PREDICATE_PREFIX)?
            .parse::<u32>()
            .ok()?;
        let [
            _,
            term_source_0 @ Term::ProgramValue(_),
            term_source_1 @ Term::ProgramValue(_),
        ] = arguments.as_slice()
        else {
            return None;
        };
        let (Some(ProgramValue::Pointer(from)), Some(ProgramValue::Pointer(to))) = (
            term_source_0.program_value_native(),
            term_source_1.program_value_native(),
        ) else {
            return None;
        };
        let count = to
            .address()
            .element_index_from_base_with_width(from.address(), width)?;
        Some((from.address().clone(), count, width))
    }

    /// A native range retains both full-width endpoints in its coverage fact.
    pub(crate) fn covered_wide_range(proposition: &Proposition) -> Option<MemoryRange> {
        let Proposition::Predicate { name, arguments } = proposition else {
            return None;
        };
        let width = name
            .strip_prefix(SUBOBJECT_COVERS_PREDICATE_PREFIX)?
            .parse::<u32>()
            .ok()
            .filter(|width| *width > 0)?;
        let [
            _,
            term_source_0 @ Term::ProgramValue(_),
            term_source_1 @ Term::ProgramValue(_),
            term_source_2 @ Term::ProgramValue(_),
        ] = arguments.as_slice()
        else {
            return None;
        };
        let (
            Some(ProgramValue::Pointer(base)),
            Some(ProgramValue::UInt64(start)),
            Some(ProgramValue::UInt64(end)),
        ) = (
            term_source_0.program_value_native(),
            term_source_1.program_value_native(),
            term_source_2.program_value_native(),
        )
        else {
            return None;
        };
        Some(MemoryRange::new_wide(
            base.address().clone(),
            start.clone(),
            end.clone(),
            width,
        ))
    }

    /// The `width` bytes at `start`: a member's bounds.
    pub(crate) fn constant(start: Address, width: u32) -> Self {
        Self::new(start, OldMachineTerm::constant(width))
    }

    /// The width in bytes when it is a constant.
    pub(crate) fn constant_width(&self) -> Option<u32> {
        self.width().as_const()
    }
}

impl Pointer {
    pub(crate) fn new(pointer: Address, program_type: ProgramType) -> Self {
        assert!(
            !program_type.is_slice_pointer(),
            "internal error: a slice pointer is built with its element count \
             (`Pointer::with_element_count`), not as a thin pointer"
        );
        assert!(
            program_type.is_pointer(),
            "C pointer values require a pointer type"
        );
        let is_function =
            matches!(program_type, ProgramType::FunctionPointer(_)) || pointer.base.is_function();
        let known_root = is_function
            || matches!(
                pointer.base,
                AddressBase::AggregateReturn { .. }
                    | AddressBase::ContractResult
                    | AddressBase::ContractException
                    | AddressBase::StaticObject { .. }
                    | AddressBase::AutomaticLocal { .. }
                    | AddressBase::SliceLength { .. }
                    | AddressBase::ReferenceCarrier { .. }
                    | AddressBase::Concrete(_)
                    | AddressBase::Heap(_)
                    | AddressBase::Temporary(_)
            );
        let root = if is_function {
            Address::null()
        } else {
            pointer.object_identity()
        };
        let array = if known_root {
            ArrayObject::allocation()
        } else {
            ArrayObject::opaque(Some(root.clone()))
        };
        Self::from_parts(pointer, root, array, program_type)
    }

    /// A complete pointer read owns an opaque domain independently of its
    /// numeric address. Both bounds and origin cover all eight bytes.
    pub(in crate::kernel) fn from_read(
        pointer: Address,
        program_type: ProgramType,
        memory: &SharedMemory,
        cell: &Address,
    ) -> Self {
        Self::from_read_at(pointer, program_type, memory, None, cell)
    }

    /// The slice a read of the slice cell `cell` at `point` decodes to
    /// (`design/rust-slice-values.md`, step 2b-ii-b): a wide pointer of
    /// `slice_type` whose data pointer ([`AddressBase::SliceData`]) and count
    /// ([`LoadKind::SliceCount`]) are both named by the one load of the cell.
    /// Neither is a read of one of the cell's words, which the kernel relates
    /// to them only by a layout fact it does not state. Two reads of one
    /// load are one slice.
    pub(in crate::kernel) fn slice_read(
        point: ProgramPoint,
        cell: &Address,
        slice_type: ProgramType,
    ) -> Self {
        let ProgramType::SlicePointer(element) = slice_type else {
            panic!("internal error: a slice read at the thin type `{slice_type:?}`");
        };
        let count = OldMachineTerm::read_named(point, cell.clone(), LoadKind::SliceCount);
        let OldMachineTerm::MemoryLoad(_, read, _) = &count else {
            unreachable!("a named read is a memory load");
        };
        let data = Address::new(read.load().slice_data_base(), AddressOffset::constant(0));
        Self::new(data, element.thin_pointer_type())
            .with_element_count(count)
            .with_type(slice_type)
    }

    /// The load a slice read names ([`Self::slice_read`]), when this is one:
    /// the whole read, its data pointer undisplaced and its count the same
    /// load's. A slice built from parts of reads is not one.
    pub(in crate::kernel) fn slice_read_load(&self) -> Option<&Load> {
        let AddressBase::SliceData(load) = &self.address().base else {
            return None;
        };
        if !matches!(self.address().offset.view(), OffsetView::Constant(0)) {
            return None;
        }
        let OldMachineTerm::MemoryLoad(_, read, LoadKind::SliceCount) = self.len()? else {
            return None;
        };
        (read.load() == load
            && *self == Self::slice_read(load.point().clone(), load.cell(), self.program_type()))
        .then_some(load)
    }

    /// [`Self::from_read`] of a read made at `site`, when the caller has one:
    /// the domain's origin records it as its read site
    /// (`Address::loaded_value_read_at`). The value is the same.
    pub(in crate::kernel) fn from_read_at(
        pointer: Address,
        program_type: ProgramType,
        memory: &SharedMemory,
        site: Option<&ProgramPoint>,
        cell: &Address,
    ) -> Self {
        let value = Self::new(pointer, program_type);
        if matches!(program_type, ProgramType::FunctionPointer(_))
            || value.address().base.is_function()
        {
            return value;
        }
        // Cache observations retain their unchanged-byte source directly.
        // This lookup crosses no writes: preservation across program states
        // needs explicit evidence, not a search for an older cell version.
        crate::instrumentation::record_deterministic_work(1);
        let source = memory.unchanged_bytes_source();
        let origin = Address::loaded_value_read_at(&source, site, cell);
        value
            .with_array_object(ArrayObject::opaque(Some(origin.clone())))
            .with_provenance(origin)
    }

    /// A point-named complete read uses the same identity for its address,
    /// provenance, and bounds owner. Function pointers have no object domain.
    pub(in crate::kernel) fn from_point_read(
        point: ProgramPoint,
        program_type: ProgramType,
        cell: &Address,
    ) -> Self {
        if point.read_version_id().is_none() {
            let address = Address::loaded_source_value_at(&point, cell);
            return Self::from_read_at(
                address,
                program_type,
                point.shared_memory(),
                Some(&point),
                cell,
            );
        }
        // One load per cell at one version point, whatever type decodes
        // it: the category and pointee type are the term's.
        let address = Load::at(point, cell).address();
        let value = Self::new(address.clone(), program_type);
        if matches!(program_type, ProgramType::FunctionPointer(_)) {
            return value;
        }
        value
            .with_provenance(address.clone())
            .with_array_object(ArrayObject::opaque(Some(address)))
    }

    /// The read that introduced this complete pointer's opaque domain when
    /// its numeric address alone names a different read version. This is
    /// the producing read, not an address-alias or preservation query.
    pub(crate) fn complete_read_source(&self) -> Option<(SharedMemory, Address)> {
        if self.bounds_owner() != Some(self.provenance())
            || self.address().object_identity() == *self.provenance()
        {
            return None;
        }
        let address_read = self.address().as_loaded_value()?;
        let origin = self.provenance().as_loaded_value()?;
        if address_read.displacement != AddressOffset::constant(0)
            || origin.displacement != AddressOffset::constant(0)
            || address_read.defining_address != origin.defining_address
        {
            return None;
        }
        Some((origin.defining_memory, origin.defining_address))
    }

    pub(in crate::kernel) fn bounds_owner(&self) -> Option<&Address> {
        self.array_object().owner()
    }

    pub(in crate::kernel) fn with_bounds_owner(self, owner: Option<Address>) -> Self {
        let array = self.array_object().with_owner(owner);
        self.with_array_object(array)
    }

    /// Entry member selection establishes bounds for its parent's opaque domain.
    pub(in crate::kernel) fn opaque_coverage_fact(
        &self,
        range: &MemoryRange,
    ) -> Option<Proposition> {
        if self.bounds_are_known() {
            return None;
        }
        let origin = self.bounds_owner()?;
        Some(SubobjectBounds::new(origin.clone(), OldMachineTerm::constant(0)).coverage_fact(range))
    }

    pub(in crate::kernel) fn access_provenance(&self) -> (&Address, Option<&Address>) {
        (
            self.provenance(),
            if self.bounds_are_known() {
                None
            } else {
                self.bounds_owner()
            },
        )
    }

    /// Exact retained qualifiers for syntax certification. Address-bearing
    /// metadata is compared separately through its written term structure.
    pub(in crate::kernel) fn retained_nonaddress_metadata(&self) -> RetainedPointerMetadata<'_> {
        self.shared().retained_nonaddress_metadata()
    }

    pub(crate) fn bounds(&self) -> Option<&SubobjectBounds> {
        self.array_object().bounds()
    }

    pub(crate) fn bounds_are_known(&self) -> bool {
        self.array_object().is_known()
    }

    /// The complete allocation as the array object: a byte view's.
    pub(in crate::kernel) fn with_root_bounds(self) -> Self {
        self.with_array_object(ArrayObject::allocation())
    }

    pub(crate) fn object_class(&self) -> Option<crate::kernel::effective_type::CAccessClass> {
        self.object_type_evidence()
            .map(|evidence| evidence.class.clone())
            .or_else(|| self.qualifiers()?.object_class.clone())
    }

    pub(crate) fn object_origin_evidence(&self) -> Option<&ObjectTypeEvidence> {
        self.qualifiers()?.object_type_evidence.as_ref()
    }
    pub(crate) fn object_type_evidence(&self) -> Option<&ObjectTypeEvidence> {
        self.object_origin_evidence()
            .filter(|evidence| evidence.checked)
    }

    pub(crate) fn supports_object_class(
        &self,
        class: &crate::kernel::effective_type::CAccessClass,
    ) -> bool {
        self.is_null()
            || self
                .object_type_evidence()
                .is_some_and(|evidence| evidence.has_class(class))
    }

    /// A cast never replaces evidence for the object originally designated.
    pub(crate) fn with_object_class(
        self,
        class: Option<crate::kernel::effective_type::CAccessClass>,
    ) -> Self {
        self.with_object_type_evidence(class.map(ObjectTypeEvidence::from))
    }

    pub(crate) fn with_object_type_evidence(
        mut self,
        evidence: Option<ObjectTypeEvidence>,
    ) -> Self {
        if let Some(evidence) = evidence
            && (self.object_origin_evidence().is_none()
                || (evidence.checked && self.object_type_evidence().is_none()))
        {
            self = self.with_declared_object_class(Some(evidence.class.clone()));
            self.qualifiers_mut().object_type_evidence = Some(evidence);
        }
        self
    }

    pub(crate) fn with_declared_object_class(
        mut self,
        class: Option<crate::kernel::effective_type::CAccessClass>,
    ) -> Self {
        if class.is_some() && self.object_class().is_none() {
            self.qualifiers_mut().object_class = class;
        }
        self
    }

    pub(crate) fn with_bounds(self, bounds: Option<SubobjectBounds>) -> Self {
        if bounds.is_none() && self.bounds().is_none() {
            return self;
        }
        let array = self.array_object().with_bounds(bounds);
        self.with_array_object(array)
    }

    /// Applies a substitution to every address the value mentions: its own
    /// address and its bounds' start. Use it where the rewrite maps
    /// variables, not where it only respells the address. A wide pointer's
    /// element count is a numeric component and is mapped by `count`, the
    /// same substitution on machine terms; a thin pointer never calls it.
    pub(crate) fn map_pointers(
        &self,
        mut map: impl FnMut(&Address) -> Address,
        count: impl FnOnce(&OldMachineTerm) -> OldMachineTerm,
    ) -> Self {
        let address = map(self.address());
        let provenance = map(self.provenance());
        let array = self.array_object().map(map);
        let mut result = self.clone().with_address(address);
        if provenance != *self.provenance() {
            result = result.with_provenance(provenance);
        }
        result.with_array_object(array).map_element_count(count)
    }

    pub(in crate::kernel) fn try_map_pointers(
        &self,
        mut map: impl FnMut(&Address) -> Option<Address>,
        count: impl FnOnce(&OldMachineTerm) -> Option<OldMachineTerm>,
    ) -> Option<Self> {
        let pointer = map(self.address())?;
        let provenance = map(self.provenance())?;
        let array = self.array_object().try_map(map)?;
        let count = match self.len() {
            Some(source) => Some(count(source)?),
            None => None,
        };
        let result = self
            .clone()
            .with_address(pointer)
            .with_provenance(provenance)
            .with_array_object(array);
        Some(match count {
            Some(count) => result.with_replaced_element_count(count),
            None => result,
        })
    }

    /// The same value with its element count mapped; a thin pointer is
    /// returned unchanged without calling `count`.
    fn map_element_count(self, count: impl FnOnce(&OldMachineTerm) -> OldMachineTerm) -> Self {
        let Some(source) = self.len() else {
            return self;
        };
        let mapped = count(source);
        if &mapped == source {
            return self;
        }
        self.with_replaced_element_count(mapped)
    }

    /// Every numeric term a wide pointer's metadata holds, for variable
    /// collection beside [`Self::pointers`]: empty for a thin pointer.
    pub(crate) fn metadata_terms(&self) -> impl Iterator<Item = &OldMachineTerm> {
        self.len().into_iter()
    }

    /// Re-spell physical addresses without changing the value's origin.
    /// A wide pointer's element count is a numeric component, not an origin:
    /// `count` respells it as the caller respells the machine terms beside
    /// the value (canonicalizing its embedded reads, or rewriting them by an
    /// address equality), so a count that reads memory is respelled with the
    /// scalars stored or compared with it. A thin pointer never calls it.
    pub(in crate::kernel) fn map_addresses(
        &self,
        map: impl FnMut(&Address) -> Address,
        count: impl FnOnce(&OldMachineTerm) -> OldMachineTerm,
    ) -> Self {
        let mapped = self.map_pointers(map, count);
        let array = mapped
            .array_object()
            .with_owner(self.array_object().owner().cloned());
        mapped
            .with_provenance(self.provenance().clone())
            .with_array_object(array)
    }

    /// Every address the value mentions, for variable collection.
    pub(crate) fn pointers(&self) -> impl Iterator<Item = &Address> {
        std::iter::once(self.address())
            .chain(std::iter::once(self.provenance()))
            .chain(self.bounds_owner())
            .chain(self.bounds().map(SubobjectBounds::start))
    }

    pub(crate) fn is_null(&self) -> bool {
        self.address().base == AddressBase::Concrete("null".to_string())
            && self.address().offset == AddressOffset::constant(0)
    }
}

/// A source occurrence of a string literal, independent of C variable names.
/// Shared so pointer and expression nodes stay small and cloning does not copy names.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct StringLiteralId(Arc<StringLiteralOccurrence>);

#[derive(Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
struct StringLiteralOccurrence {
    source: Option<String>,
    function: String,
    ordinal: u32,
}

impl StringLiteralId {
    pub fn new(function: impl Into<String>, ordinal: u32) -> Self {
        Self(Arc::new(StringLiteralOccurrence {
            source: None,
            function: function.into(),
            ordinal,
        }))
    }

    pub fn with_source(self, source: impl Into<String>) -> Self {
        Self(Arc::new(StringLiteralOccurrence {
            source: Some(source.into()),
            function: self.0.function.clone(),
            ordinal: self.0.ordinal,
        }))
    }

    pub fn source(&self) -> Option<&str> {
        self.0.source.as_deref()
    }
    pub fn function(&self) -> &str {
        &self.0.function
    }
    pub fn ordinal(&self) -> u32 {
        self.0.ordinal
    }

    pub(crate) fn payload_bytes(&self) -> usize {
        self.0.function.len() + self.0.source.as_ref().map_or(0, String::len) + 4
    }
}

impl std::fmt::Display for StringLiteralId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(source) = &self.0.source {
            write!(f, "{source:?}::")?;
        }
        write!(f, "{}.string_literal({})", self.0.function, self.0.ordinal)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum AddressBase {
    Concrete(String),
    /// A string literal occurrence. Distinct occurrences with identical
    /// bytes are intentionally not proven distinct: C permits an
    /// implementation to merge them. The occurrence identity still keeps
    /// one literal's pointer stable, and differing bytes prove that two
    /// occurrences cannot be the same object.
    StringLiteral {
        identity: StringLiteralId,
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
    /// The value a pointer-typed load decodes to, independent of the
    /// storage block that held it and of the type that decodes it
    /// (`design/loads.md`). Built only by [`Load::base`].
    Load(Load),
    /// The data pointer of the slice a slice-typed load decodes to
    /// (`design/rust-slice-values.md`, step 2b-ii-b): the thin part of a
    /// read of a 16-byte slice cell. It is its own read, never the pointer
    /// read of the cell's first word ([`Self::Load`]), which the kernel would
    /// equate with it only by a layout fact it does not state. Built only by
    /// [`Load::slice_data_base`].
    SliceData(Load),
    /// An opaque pointer-valued pure call. This is not an allocation identity
    /// and grants neither distinctness nor memory access.
    PureFunctionApplication(SharedPureApplication),

    /// A trusted allocation identity. Unlike a symbolic/opaque block, this is
    /// fresh and distinct from every other block identity.
    Heap(u64),
    /// Storage the verifier introduced for an object the C abstract machine
    /// creates but the program never names: an aggregate call or conditional
    /// expression result.
    ///
    /// Soundness of treating this as fresh and distinct from every other
    /// block: the object does not exist before the call that produces it, so
    /// no pointer the program already holds can point into it. Later pointers
    /// derived from the result retain this identity and its lifetime. A by-value
    /// return is a copy: the callee's own storage, whatever it was, is a
    /// different object from this temporary, and the copy is what the caller
    /// reads. Every later use spells the temporary through this identity or
    /// copies out of it; a program that stores the aggregate into a local and
    /// then takes `&local.field` is addressing the local's block, not this
    /// one. Identities come from the single kernel variable allocator, so two
    /// temporaries are never confused, and a fresh identity is never the
    /// identity of storage that already existed.
    Temporary(u64),
    AutomaticLocal {
        binding: LocalBindingId,
        instance: LocalStorageInstance,
    },
    /// Internal storage of the pointer carrying a reference, distinct from
    /// the referent object and from an ordinary address-looking source name.
    ReferenceCarrier {
        referent: Arc<BindingName>,
        instance: LocalStorageInstance,
    },
    /// Internal storage of the length component of a slice.
    SliceLength {
        slice: SliceLengthBinding,
        instance: LocalStorageInstance,
    },
    StaticObject {
        binding: StaticBindingId,
    },
    /// Value-only bookkeeping slot for the contract result, never C storage.
    ContractResult,
    /// Caller-owned copy materialized at the aggregate return boundary.
    /// Uses the frame allocator, independently of every source local name.
    AggregateReturn {
        frame: u64,
    },
    /// Value-only bookkeeping slot for a thrown payload, never C storage.
    ContractException,
}

impl std::hash::Hash for AddressBase {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Keep the hash domain of the pre-string-literal variants stable.
        // Pointer hashes feed deterministic load-variable identities, so
        // inserting a new enum variant must not renumber existing blocks.
        match self {
            Self::AggregateReturn { frame } => {
                14u64.hash(state);
                frame.hash(state);
            }
            Self::ContractResult => 13u64.hash(state),
            Self::ContractException => 15u64.hash(state),
            Self::SliceLength { slice, instance } => {
                17u64.hash(state);
                slice.hash(state);
                instance.hash(state);
            }
            Self::StaticObject { binding } => {
                12u64.hash(state);
                binding.hash(state);
            }
            Self::ReferenceCarrier { referent, instance } => {
                16u64.hash(state);
                referent.hash(state);
                instance.hash(state);
            }
            Self::AutomaticLocal { binding, instance } => {
                11u64.hash(state);
                binding.hash(state);
                instance.hash(state);
            }
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
            Self::Load(load) => {
                9u64.hash(state);
                load.hash(state);
            }
            Self::SliceData(load) => {
                18u64.hash(state);
                load.hash(state);
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

/// The storage class a concrete block's name records, as its prefix: an
/// automatic object of the current frames, a file-scope object with external
/// or internal linkage, or storage a havoc introduced. Test a block with the
/// `is_*_block` methods below, never by spelling a prefix at the use site.
pub(crate) const LOCAL_BLOCK_PREFIX: &str = "local:";
pub(crate) const GLOBAL_BLOCK_PREFIX: &str = "global:";
pub(crate) const STATIC_BLOCK_PREFIX: &str = "static:";
pub(crate) const HAVOC_BLOCK_PREFIX: &str = "havoc:";
pub(crate) const CALL_HAVOC_BLOCK_PREFIX: &str = "call-havoc:";

impl AddressBase {
    /// Whether a concrete block name records automatic storage.
    pub(crate) fn is_local_name(name: &str) -> bool {
        name.starts_with(LOCAL_BLOCK_PREFIX)
    }

    /// Whether a concrete block name records a file-scope object with
    /// external linkage.
    pub(crate) fn is_global_name(name: &str) -> bool {
        name.starts_with(GLOBAL_BLOCK_PREFIX)
    }

    /// Whether a concrete block name records a `static` object.
    pub(crate) fn is_static_name(name: &str) -> bool {
        name.starts_with(STATIC_BLOCK_PREFIX)
    }

    /// A frontend-created C++ parameter object, allocated in its caller.
    pub(crate) fn prepared_argument_binding(&self) -> Option<&LocalBindingId> {
        match self {
            Self::AutomaticLocal { binding, .. } if binding.is_prepared_argument() => Some(binding),
            _ => None,
        }
    }

    /// Automatic storage: a local, parameter, frame or lifetime object.
    pub(crate) fn is_local_block(&self) -> bool {
        self.starts_with(LOCAL_BLOCK_PREFIX)
    }

    /// A file-scope object with external linkage.
    pub(crate) fn is_global_block(&self) -> bool {
        matches!(self, Self::StaticObject { binding } if binding.function().is_none())
            || self.starts_with(GLOBAL_BLOCK_PREFIX)
    }

    /// A file-scope or function-scope `static` object.
    pub(crate) fn is_static_block(&self) -> bool {
        matches!(self, Self::StaticObject { binding } if binding.function().is_some())
            || self.starts_with(STATIC_BLOCK_PREFIX)
    }

    /// Static storage of either linkage.
    pub(crate) fn is_static_storage_block(&self) -> bool {
        self.is_global_block() || self.is_static_block()
    }

    /// Storage a loop or statement havoc introduced.
    pub(crate) fn is_havoc_block(&self) -> bool {
        self.starts_with(HAVOC_BLOCK_PREFIX)
    }

    /// Storage a havoc at a call introduced.
    pub(crate) fn is_call_havoc_block(&self) -> bool {
        self.starts_with(CALL_HAVOC_BLOCK_PREFIX)
    }

    pub(crate) fn is_function(&self) -> bool {
        matches!(self, Self::Function(_) | Self::FunctionSymbolic(_))
    }

    pub(crate) fn starts_with(&self, prefix: &str) -> bool {
        match self {
            Self::AutomaticLocal { instance, .. }
            | Self::ReferenceCarrier { instance, .. }
            | Self::SliceLength { instance, .. } => {
                prefix == "local:"
                    || match instance {
                        LocalStorageInstance::ValueParameter => prefix == "local:value-parameter:",
                        LocalStorageInstance::Lifetime(_) => prefix == "local:lifetime:",
                        LocalStorageInstance::Frame(_) => prefix == "local:frame:",
                        LocalStorageInstance::Implicit => false,
                    }
            }
            Self::AggregateReturn { .. } => prefix == "local:" || prefix == "local:frame:",
            Self::ContractResult | Self::ContractException => prefix == "local:",
            Self::Concrete(name) => name.starts_with(prefix),
            Self::StringLiteral { .. } => prefix == "string:",
            _ => false,
        }
    }

    pub(crate) fn strip_prefix<'a>(&'a self, prefix: &str) -> Option<&'a str> {
        match self {
            Self::Concrete(name) => name.strip_prefix(prefix),
            Self::AggregateReturn { .. }
            | Self::ContractResult
            | Self::ContractException
            | Self::StaticObject { .. }
            | Self::AutomaticLocal { .. }
            | Self::SliceLength { .. }
            | Self::ReferenceCarrier { .. }
            | Self::StringLiteral { .. }
            | Self::Function(_)
            | Self::FunctionSymbolic(_)
            | Self::ExternalArgument
            | Self::ExternalObject(_)
            | Self::Symbolic(_)
            | Self::Load(_)
            | Self::SliceData(_)
            | Self::PureFunctionApplication(_)
            | Self::Heap(_)
            | Self::Temporary(_) => None,
        }
    }

    /// Whether no execution can make these two block identities name one
    /// object. This is the kernel's only structural separation rule for
    /// blocks, and `Address::blocks_proven_distinct` is its pointer-level
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
                    | Self::Load(_)
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
        // A loaded pointer is a value obtained at the state it was read
        // in, and cannot point into an object that did not exist then.
        let loaded_before = |value: &Self, object: &Self| match value {
            Self::Symbolic(variable) => {
                crate::kernel::is_load_variable(variable)
                    && crate::kernel::eval::loaded_pointer_predates_block(variable, object)
            }
            Self::Load(load) => {
                crate::kernel::eval::loaded_pointer_read_predates_block(load, object)
            }
            _ => false,
        };
        if loaded_before(self, other) || loaded_before(other, self) {
            return true;
        }
        // A pointer read holds the pointer its state stores at the read's
        // address (the read-over-write authority), so it lies in that
        // pointer's block. This reads memory, never facts.
        let stored_block = |block: &Self| match block {
            Self::Load(load) => crate::kernel::eval::loaded_pointer_stored_block(load),
            _ => None,
        };
        if stored_block(self).is_some_and(|stored| stored.proven_distinct(other))
            || stored_block(other).is_some_and(|stored| self.proven_distinct(&stored))
        {
            return true;
        }
        // A symbolic block is a logic variable that later facts may constrain
        // to any address, including a heap block named below (a contract
        // postcondition such as `result == destination` does exactly that).
        // It is therefore never proven distinct by structure alone; only an
        // explicit disequality in the assumptions can separate it.
        if matches!(
            self,
            Self::Symbolic(_) | Self::Load(_) | Self::PureFunctionApplication(_)
        ) || matches!(
            other,
            Self::Symbolic(_) | Self::Load(_) | Self::PureFunctionApplication(_)
        ) {
            return false;
        }
        // A function's own scalar locals (`local:` blocks) are storage the
        // function declared; memory reached through a parameter
        // (`ExternalArgument`) existed before the call and cannot be one of
        // them.
        let local_versus_argument = |left: &Self, right: &Self| {
            left.is_local_block()
                && matches!(right, Self::ExternalArgument | Self::ExternalObject(_))
        };
        // A string literal is an object of its own (C11 6.4.5p6). Only
        // another literal with the same bytes may share its storage, so it
        // is never a declared object or a function.
        let literal_versus_declared = |left: &Self, right: &Self| {
            matches!(left, Self::StringLiteral { .. })
                && matches!(
                    right,
                    Self::AggregateReturn { .. }
                        | Self::ContractResult
                        | Self::ContractException
                        | Self::StaticObject { .. }
                        | Self::AutomaticLocal { .. }
                        | Self::SliceLength { .. }
                        | Self::ReferenceCarrier { .. }
                        | Self::Concrete(_)
                        | Self::Function(_)
                )
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
                || (matches!(
                    self,
                    Self::AggregateReturn { .. }
                        | Self::ContractResult
                        | Self::ContractException
                        | Self::AutomaticLocal { .. }
                        | Self::SliceLength { .. }
                        | Self::ReferenceCarrier { .. }
                        | Self::StaticObject { .. }
                ) && matches!(
                    other,
                    Self::AggregateReturn { .. }
                        | Self::ContractResult
                        | Self::ContractException
                        | Self::AutomaticLocal { .. }
                        | Self::SliceLength { .. }
                        | Self::ReferenceCarrier { .. }
                        | Self::StaticObject { .. }
                        | Self::Concrete(_)
                ))
                || (matches!(
                    other,
                    Self::AggregateReturn { .. }
                        | Self::ContractResult
                        | Self::ContractException
                        | Self::AutomaticLocal { .. }
                        | Self::SliceLength { .. }
                        | Self::ReferenceCarrier { .. }
                        | Self::StaticObject { .. }
                ) && matches!(self, Self::Concrete(_)))
                || literal_versus_declared(self, other)
                || literal_versus_declared(other, self)
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

impl From<String> for AddressBase {
    fn from(name: String) -> Self {
        Self::Concrete(name)
    }
}

impl From<&str> for AddressBase {
    fn from(name: &str) -> Self {
        Self::Concrete(name.to_string())
    }
}

impl std::fmt::Display for AddressBase {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AggregateReturn { frame } => write!(formatter, "result.storage(frame, {frame})"),
            Self::ContractResult => formatter.write_str("result.storage()"),
            Self::ContractException => formatter.write_str("exception.storage()"),
            Self::SliceLength { slice, instance } => {
                write!(formatter, "{slice}.storage({instance})")
            }
            Self::StaticObject { binding } => write!(formatter, "{binding}.storage()"),
            Self::ReferenceCarrier { referent, instance } => {
                write!(
                    formatter,
                    "reference-carrier({referent}).storage({instance})"
                )
            }
            Self::AutomaticLocal { binding, instance } => {
                write!(formatter, "{}.storage({instance})", binding.canonical())
            }
            Self::PureFunctionApplication(application) => write!(
                formatter,
                "pure-pointer:{}:{}",
                application.name(),
                application.id()
            ),
            Self::Concrete(name) => formatter.write_str(name),
            Self::StringLiteral { identity, .. } => write!(formatter, "{identity}"),
            Self::Function(name) => write!(formatter, "function:{name}"),
            Self::FunctionSymbolic(variable) => {
                write!(formatter, "symbolic-function-pointer:{}", variable.0)
            }
            Self::ExternalArgument => formatter.write_str("arg-memory"),
            Self::ExternalObject(variable) => write!(formatter, "arg-object:{}", variable.0),
            Self::Symbolic(variable) => write!(formatter, "symbolic-pointer:{}", variable.0),
            Self::Load(load) => write!(formatter, "loaded-pointer:{}", load.id()),
            Self::SliceData(load) => write!(formatter, "loaded-slice-data:{}", load.id()),
            Self::Heap(identity) => write!(formatter, "heap-allocation:{identity}"),
            Self::Temporary(identity) => write!(formatter, "temporary:{identity}"),
        }
    }
}

/// Complete LP64 integer produced from a pointer. Numeric projections discard
/// this record; complete C-value transport keeps it. Fields are kernel-owned.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(in crate::kernel) enum PointerIntegerKind {
    Exact,
    Tagged,
    /// An incoming or loaded complete word. Its identity is independent of
    /// its numeric value; only an explicit full-pointer contract gives bounds.
    Word {
        changed_bits: u64,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct PointerIntegerValue {
    pub(in crate::kernel) numeric: Box<ProgramValue>,
    pub(in crate::kernel) pointer: Box<Pointer>,
    pub(in crate::kernel) kind: PointerIntegerKind,
}

impl PointerIntegerValue {
    /// Whether this is a complete word that was passed in or loaded, whose
    /// identity is independent of its numeric value, rather than an address
    /// (`address(p)`) or a tag on one (`address(p) + 1`) computed from it.
    pub(crate) fn is_opaque_word(&self) -> bool {
        matches!(self.kind, PointerIntegerKind::Word { .. })
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ProgramValue {
    PointerInteger(PointerIntegerValue),
    Void,
    /// C `_Bool` values are represented by a 32-bit term whose value is
    /// always normalized to zero or one.  The storage width remains the
    /// ABI-defined one byte width exposed by `ProgramType::Bool`.
    Bool(OldMachineTerm),
    Int8(OldMachineTerm),
    Int16(OldMachineTerm),
    Int32(OldMachineTerm),
    UInt8(OldMachineTerm),
    UInt16(OldMachineTerm),
    UInt32(OldMachineTerm),
    Int64(OldMachineTerm),
    UInt64(OldMachineTerm),
    Int128(OldMachineTerm),
    UInt128(OldMachineTerm),
    /// IEEE-754 binary32 payload represented in the shared checked term arena.
    Float32(OldMachineTerm),
    /// IEEE-754 binary64 payload represented in the shared checked term arena.
    Float64(OldMachineTerm),
    Pointer(Pointer),
    /// A value of an abstract type parameter: the spec value of that rigid
    /// type it is.
    Parameter(Box<AlgebraicTerm>),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ProgramType {
    /// A value of the abstract type parameter with this interned name.
    Parameter(TypeParameterName),
    /// A pointer to a value of the abstract type parameter with this name,
    /// a Rust `&T`.
    ParameterPointer(TypeParameterName),
    Void,
    Bool,
    /// An opaque object pointer with provenance but no modeled pointee type.
    /// It is valid for identity-preserving casts and comparisons, but not for
    /// dereference, indexing, or pointer arithmetic.
    VoidPointer,
    /// Pointer to an opaque object-pointer slot, needed to retain the exact
    /// `pthread_join` result parameter type even in null-only calls.
    VoidPointerPointer,
    /// Click's untyped pointer, spelled `Pointer`: an address and a
    /// provenance with no pointee type, like LLVM's opaque `ptr`. An access,
    /// cast or call through it states its own type (`load<T>(p)`, `p as
    /// (T *)`), so it cannot be dereferenced, indexed or scaled. It is not a
    /// C type: C's `void *` rules (implicit conversions, GNU byte
    /// arithmetic, the character view a conversion forms) do not apply to
    /// it, and a cast to or from it keeps the value. For now it designates
    /// objects only; function pointers keep their own signature type.
    Pointer,
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
    PointerArray(PointerArrayElement, u32),
    /// A wide pointer to `[T]` or `str` (`design/rust-slice-values.md`): a
    /// thin pointer of [`SliceElement::thin_pointer_type`] plus its element
    /// count. Every value of this type carries the count
    /// ([`Pointer::len`]) and no thin pointer has it. Rust's `&[T]`, `&mut
    /// [T]`, `*const [T]`, `*mut [T]` and `Box<[T]>` are this one type, told
    /// apart, as thin `&T`, `&mut T` and `*const T` are, by the declaration's
    /// qualifiers and contract. It has no pointee type, so no thin pointer
    /// operation (arithmetic, ordering, dereference, integer casts) takes
    /// it: those read [`Pointer::as_ptr`].
    SlicePointer(SliceElement),
}

/// The bytes a wide pointer's cell holds: its data word and its metadata
/// word.
pub(crate) const WIDE_POINTER_BYTE_WIDTH: u32 = 2 * C_POINTER_BYTE_WIDTH;

/// The element type of a [`ProgramType::SlicePointer`]: `[T]` for a scalar
/// or abstract `T`, or `str`, whose elements are UTF-8 bytes. `str` is its
/// own element so the UTF-8 invariant attaches to strings and never to
/// arbitrary bytes (`design/rust-slice-values.md`, "String slices").
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SliceElement {
    Int8,
    Int16,
    Int32,
    Int64,
    Int128,
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    UInt128,
    Float32,
    Float64,
    /// `str`: a byte sequence whose thin part is a `u8` pointer.
    Str,
    /// An abstract element type, a generic `[T]`.
    Parameter(TypeParameterName),
}

impl SliceElement {
    /// The `[T]` whose thin part has this type, `T *`; `None` for a type
    /// that is no slice's thin part. A `u8` pointer gives `[u8]`, never
    /// `str`, which is reached only by retyping a wide pointer.
    pub fn of_thin_pointer_type(program_type: ProgramType) -> Option<Self> {
        Some(match program_type {
            ProgramType::Int8Pointer => Self::Int8,
            ProgramType::Int16Pointer => Self::Int16,
            ProgramType::Int32Pointer => Self::Int32,
            ProgramType::Int64Pointer => Self::Int64,
            ProgramType::Int128Pointer => Self::Int128,
            ProgramType::UInt8Pointer => Self::UInt8,
            ProgramType::UInt16Pointer => Self::UInt16,
            ProgramType::UInt32Pointer => Self::UInt32,
            ProgramType::UInt64Pointer => Self::UInt64,
            ProgramType::UInt128Pointer => Self::UInt128,
            ProgramType::Float32Pointer => Self::Float32,
            ProgramType::Float64Pointer => Self::Float64,
            ProgramType::ParameterPointer(parameter) => Self::Parameter(parameter),
            _ => return None,
        })
    }

    /// The Click specification spelling of the slice pointer type:
    /// `Slice<T>` for `&[T]`, `Str` for `&str`.
    pub fn slice_type_spelling(self) -> &'static str {
        let element = match self {
            Self::Str => return "Str",
            Self::Parameter(parameter) => parameter.name(),
            Self::Int8 => "int8",
            Self::Int16 => "int16",
            Self::Int32 => "int32",
            Self::Int64 => "int64",
            Self::Int128 => "int128",
            Self::UInt8 => "uint8",
            Self::UInt16 => "uint16",
            Self::UInt32 => "uint32",
            Self::UInt64 => "uint64",
            Self::UInt128 => "uint128",
            Self::Float32 => "float32",
            Self::Float64 => "float64",
        };
        TypeParameterName::intern(&format!("Slice<{element}>")).name()
    }

    /// The type of the thin part, `s.as_ptr()`.
    pub fn thin_pointer_type(self) -> ProgramType {
        match self {
            Self::Int8 => ProgramType::Int8Pointer,
            Self::Int16 => ProgramType::Int16Pointer,
            Self::Int32 => ProgramType::Int32Pointer,
            Self::Int64 => ProgramType::Int64Pointer,
            Self::Int128 => ProgramType::Int128Pointer,
            Self::UInt8 | Self::Str => ProgramType::UInt8Pointer,
            Self::UInt16 => ProgramType::UInt16Pointer,
            Self::UInt32 => ProgramType::UInt32Pointer,
            Self::UInt64 => ProgramType::UInt64Pointer,
            Self::UInt128 => ProgramType::UInt128Pointer,
            Self::Float32 => ProgramType::Float32Pointer,
            Self::Float64 => ProgramType::Float64Pointer,
            Self::Parameter(parameter) => ProgramType::ParameterPointer(parameter),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum PointerArrayElement {
    Void,
    /// Plain `char` under a target where it is unsigned. Kept apart from
    /// `UInt8` only so the C frontend recovers `char *` from the element;
    /// its cells are `uint8*` pointers.
    UnsignedPlainChar,
    /// Plain `char` under a target where it is signed; its cells are
    /// `int8*` pointers.
    SignedPlainChar,
    /// Pointer to plain `char` (unsigned on the target): an array of `char
    /// **` cells, such as a table of string tables. Its cells are `uint8**`.
    UnsignedPlainCharPointer,
    /// Pointer to plain `char` (signed on the target); its cells are
    /// `int8**`.
    SignedPlainCharPointer,
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

impl PointerArrayElement {
    pub fn from_pointer_type(program_type: ProgramType) -> Option<Self> {
        Some(match program_type {
            ProgramType::VoidPointer => Self::Void,
            ProgramType::Int8Pointer => Self::Int8,
            ProgramType::Int16Pointer => Self::Int16,
            ProgramType::Int32Pointer => Self::Int32,
            ProgramType::UInt8Pointer => Self::UInt8,
            ProgramType::UInt16Pointer => Self::UInt16,
            ProgramType::UInt32Pointer => Self::UInt32,
            ProgramType::Int64Pointer => Self::Int64,
            ProgramType::Int128Pointer => Self::Int128,
            ProgramType::UInt64Pointer => Self::UInt64,
            ProgramType::UInt128Pointer => Self::UInt128,
            ProgramType::Float32Pointer => Self::Float32,
            ProgramType::Float64Pointer => Self::Float64,
            _ => return None,
        })
    }

    pub fn pointer_type(self) -> ProgramType {
        match self {
            Self::Void => ProgramType::VoidPointer,
            Self::UnsignedPlainChar => ProgramType::UInt8Pointer,
            Self::SignedPlainChar => ProgramType::Int8Pointer,
            Self::UnsignedPlainCharPointer => ProgramType::UInt8PointerPointer,
            Self::SignedPlainCharPointer => ProgramType::Int8PointerPointer,
            Self::Int8 => ProgramType::Int8Pointer,
            Self::Int16 => ProgramType::Int16Pointer,
            Self::Int32 => ProgramType::Int32Pointer,
            Self::UInt8 => ProgramType::UInt8Pointer,
            Self::UInt16 => ProgramType::UInt16Pointer,
            Self::UInt32 => ProgramType::UInt32Pointer,
            Self::Int64 => ProgramType::Int64Pointer,
            Self::Int128 => ProgramType::Int128Pointer,
            Self::UInt64 => ProgramType::UInt64Pointer,
            Self::UInt128 => ProgramType::UInt128Pointer,
            Self::Float32 => ProgramType::Float32Pointer,
            Self::Float64 => ProgramType::Float64Pointer,
        }
    }

    pub fn decayed_type_spelling(self) -> &'static str {
        match self {
            Self::Void => "void**",
            Self::UnsignedPlainChar | Self::UInt8 => "uint8**",
            Self::SignedPlainChar | Self::Int8 => "int8**",
            Self::UnsignedPlainCharPointer => "uint8***",
            Self::SignedPlainCharPointer => "int8***",
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
/// The declared, exact exceptional channel. Surface contracts currently spell
/// the scalar channel and the pinned opaque standard exception class; source
/// execution cannot silently invent another payload type.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) enum ExceptionalSignature {
    #[default]
    None,
    Int32,
    Opaque(TypeParameterName),
}

impl ExceptionalSignature {
    pub(crate) fn is_empty(self) -> bool {
        self == Self::None
    }

    pub(crate) fn permits(self, value: &ProgramValue) -> bool {
        self.payload_type() == Some(value.program_type())
    }

    pub(crate) fn payload_type(self) -> Option<ProgramType> {
        match self {
            Self::None => None,
            Self::Int32 => Some(ProgramType::Int32),
            Self::Opaque(name) => Some(ProgramType::Parameter(name)),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct LValue {
    pub(super) storage: LValueStorage,
    pub(super) value_type: ProgramType,
    pub(super) volatile: bool,
    pub(super) pointee_volatile: bool,
    pub(super) constant: bool,
    pub(super) pointee_constant: bool,
    /// The provenance of the pointer this memory lvalue was reached through:
    /// its allocation and array object. The access is checked against it,
    /// and `&lvalue` keeps it.
    pub(super) provenance: Option<Address>,
    pub(super) array: Option<ArrayObject>,
    /// The class of the lvalue's type, which the access uses, when the
    /// frontend supplied one.
    pub(super) access_class: Option<crate::kernel::effective_type::CAccessClass>,
    /// The class of the object the pointer this lvalue was reached through
    /// designates.
    pub(super) object_class: Option<crate::kernel::effective_type::CAccessClass>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) enum LValueStorage {
    Local { name: BindingName },
    Memory { pointer: Address },
}

/// The language-specific integer rule at an explicit kernel cast boundary.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum IntegerCastMode {
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
    /// An inserted byte/void view changes the carrier while retaining the
    /// source pointer's provenance and bounds. Authored pointer casts use
    /// the separate explicit conversion rule.
    PointerCoercion,
    /// Legacy exact uint64-to-int64 boundary.
    UInt64BitsToInt64,
    /// The `Bool` value of a Rust comparison, `!` or connective (Stage 5,
    /// decision D5): its operand's condition is the value, built with no
    /// path split. Only the Rust front end writes it, at target `bool`.
    BoolValue,
    /// A Rust operator `+ - * & | ^ <<` or `!` on an 8- or 16-bit value
    /// (decision G4): its operand is the operator over operands of the
    /// target's type as written, and its value is that operator's native
    /// node at the target's format, `(a op b) mod 2^N`, with no promotion
    /// and no conversion. Only the Rust front end writes it; Rust's
    /// overflow panics for these operators are separate checked assertions.
    /// Signed narrow `/ %` retain the promoted operation's converted term
    /// and emit their own narrow overflow prerequisite.
    NarrowArithmetic,
    /// The conversion lowering inserts from a pure function's body to its
    /// declared result type: C's conversion, as `CConversion`, at whose
    /// type the body's arithmetic is (decision G2), so a body `a + b` of a
    /// `-> uint8` function is the `uint8` operator.
    ResultConversion,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ProgramExpression {
    /// A literal object installed for this function, never a program local.
    StringLiteral(StringLiteralId),
    Value(ProgramValue),
    Variable(BindingName),
    FunctionAddress(String),
    Cast {
        expression: Box<ProgramExpression>,
        target_type: ProgramType,
        integer_mode: IntegerCastMode,
        /// The struct tag of a pointer cast target, as the source spelled it.
        /// Evaluation ignores it: a struct pointer is a kernel `Int32Pointer`
        /// and the layout lives with the field accesses. It is kept so a
        /// contract cast prints back as `(struct name *)` and so the parser
        /// resolves `->field` through the cast result.
        pointee_struct: Option<String>,
        /// `sizeof` the struct `pointee_struct` names, when the cast's
        /// producer has its layout. A pointer to a struct's initial member,
        /// converted to the struct's type, points to the struct (C11
        /// 6.7.2.1p15), so the result's array object is that struct's bytes.
        pointee_struct_size: Option<u32>,
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
    Ternary {
        condition: Box<ProgramExpression>,
        then_branch: Box<ProgramExpression>,
        else_branch: Box<ProgramExpression>,
    },
    /// Click unary minus: float sign negation, otherwise existing zero subtraction.
    Negate(Box<ProgramExpression>),
    FloatNegate(Box<ProgramExpression>),
    FloatClassification {
        expression: Box<ProgramExpression>,
        classification: FloatClassification,
    },
    AddressOf(Box<ProgramExpression>),
    /// Form an address only after checking that the complete lvalue denotes
    /// live storage. Unlike C's &* cancellation, this excludes one-past and
    /// expired addresses. It performs no load and grants no access authority.
    CheckedObjectAddress(Box<ProgramExpression>),
    /// The address `bytes` into the object `pointer` designates: a member's
    /// offset, a number or a symbolic layout's `offsetof` term.
    PointerOffsetBytes {
        pointer: Box<ProgramExpression>,
        bytes: LayoutOffset,
    },
    /// The pointer narrowed to the `width`-byte subobject that starts at its
    /// address: a member access selects the member's own bounds
    /// (`design/pointer-subobject-bounds.md`). It performs no load, grants
    /// no access authority and does not move the address.
    Subobject {
        pointer: Box<ProgramExpression>,
        width: u32,
    },
    LessThan(Box<ProgramExpression>, Box<ProgramExpression>),
    LessEqual(Box<ProgramExpression>, Box<ProgramExpression>),
    GreaterThan(Box<ProgramExpression>, Box<ProgramExpression>),
    GreaterEqual(Box<ProgramExpression>, Box<ProgramExpression>),
    Equal(Box<ProgramExpression>, Box<ProgramExpression>),
    NotEqual(Box<ProgramExpression>, Box<ProgramExpression>),
    Not(Box<ProgramExpression>),
    And(Box<ProgramExpression>, Box<ProgramExpression>),
    Or(Box<ProgramExpression>, Box<ProgramExpression>),
    Add(Box<ProgramExpression>, Box<ProgramExpression>),
    Subtract(Box<ProgramExpression>, Box<ProgramExpression>),
    Multiply(Box<ProgramExpression>, Box<ProgramExpression>),
    Divide(Box<ProgramExpression>, Box<ProgramExpression>),
    Remainder(Box<ProgramExpression>, Box<ProgramExpression>),
    ShiftLeft(Box<ProgramExpression>, Box<ProgramExpression>),
    /// Rust-width shifts retained in resource argument expressions.
    RustShiftLeft(Box<ProgramExpression>, Box<ProgramExpression>),
    RustShiftRight(Box<ProgramExpression>, Box<ProgramExpression>),
    ShiftRight(Box<ProgramExpression>, Box<ProgramExpression>),
    BitwiseAnd(Box<ProgramExpression>, Box<ProgramExpression>),
    BitwiseOr(Box<ProgramExpression>, Box<ProgramExpression>),
    BitwiseXor(Box<ProgramExpression>, Box<ProgramExpression>),
    BitwiseNot(Box<ProgramExpression>),
    Load(Box<ProgramExpression>),
    TypedLoad {
        pointer: Box<ProgramExpression>,
        value_type: ProgramType,
        /// A sequential kernel access primitive forces one observable access
        /// even when the source lvalue itself was not declared volatile.
        volatile: bool,
        /// Qualification of a loaded pointer's pointee, not of this cell.
        pointee_constant: bool,
        /// The class of the lvalue's C type, which the access uses, when the
        /// frontend supplied one (`design/effective-types.md`).
        access_class: Option<crate::kernel::effective_type::CAccessClass>,
        /// Source origin is presentation metadata only. Its comparison
        /// traits intentionally ignore the value.
        source: ExpressionLoadSource,
    },
    Index(Box<ProgramExpression>, Box<ProgramExpression>),
    /// A Rust enum value built from its variant's fields, in declaration
    /// order: `Shape::Circle(r)`. Its type is `ProgramType::Parameter(enum_type)`.
    EnumConstruct {
        enum_type: TypeParameterName,
        variant: String,
        fields: Vec<ProgramExpression>,
    },
    /// Field `index` of an enum value of variant `variant`, which a `match`
    /// arm has established: `(s as Shape::Circle).0`.
    EnumField {
        value: Box<ProgramExpression>,
        variant: String,
        index: usize,
    },
    /// The result of step `step` of this statement: the term a call step
    /// (`ProgramStatement::CallResult`) returned, or the value an assignment step
    /// (`ProgramStatement::Assign` with `prior_result`) replaced.
    StepResult {
        step: u32,
        origin: StepOrigin,
        /// Whether this read ends the result. A read that keeps it, as a
        /// Rust `for` loop's `match` test of the `Option` `next()` returned,
        /// leaves it for a later read in the same pass, which ends it.
        ends: bool,
    },
    /// Whether an enum value is of variant `variant`, as a `bool`: the test
    /// a Rust `match` arm makes. An undecided test splits on the variant.
    EnumIs {
        value: Box<ProgramExpression>,
        variant: String,
    },
    /// `s.len()`: the element count of the slice `s` evaluates to, read in
    /// place as [`SpecExpression::SliceLength`] reads it, Rust MIR's
    /// `PtrMetadata` (`design/rust-slice-values.md`, step 3). A thin operand
    /// is refused with [`RuntimeError::SliceTypeMismatch`].
    SliceLength(Box<ProgramExpression>),
    /// `s.as_ptr()`: the thin data pointer of the slice `s` evaluates to,
    /// as [`SpecExpression::SliceData`] reads it.
    SliceData(Box<ProgramExpression>),
    /// `slice::from_raw_parts(data, count)`: the slice whose thin part is
    /// `data` and whose element count is the `u64` `count`, built directly
    /// as [`SpecExpression::SliceFromRawParts`] builds it. A wide `data` is
    /// refused with [`RuntimeError::ThinPointerRequired`].
    SliceFromRawParts {
        data: Box<ProgramExpression>,
        count: Box<ProgramExpression>,
    },
}

/// Optional source origin attached to a typed load. Two expressions that
/// differ only in this metadata remain equal in kernel collections and caches.
#[derive(Clone, Debug)]
pub struct ExpressionLoadSource(Option<Arc<LoadSourceId>>);

impl ExpressionLoadSource {
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

impl Default for ExpressionLoadSource {
    fn default() -> Self {
        Self::none()
    }
}

impl PartialEq for ExpressionLoadSource {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl Eq for ExpressionLoadSource {}

impl std::hash::Hash for ExpressionLoadSource {
    fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {}
}

impl Ord for ExpressionLoadSource {
    fn cmp(&self, _other: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

impl PartialOrd for ExpressionLoadSource {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ComparisonOperator {
    Equal,
    NotEqual,
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum FloatBinaryOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum FloatClassification {
    Finite,
    Infinite,
    Zero,
    Subnormal,
    Nan,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum FloatCondition {
    Comparison {
        operator: ComparisonOperator,
        left: Box<OldMachineTerm>,
        right: Box<OldMachineTerm>,
    },
    Classification {
        classification: FloatClassification,
        value: Box<OldMachineTerm>,
    },
}

impl FloatCondition {
    pub(crate) fn for_each_bitvector_term(&self, mut visit: impl FnMut(&OldMachineTerm)) {
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
        mut map: impl FnMut(&OldMachineTerm) -> OldMachineTerm,
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
        mut map: impl FnMut(&OldMachineTerm) -> Option<OldMachineTerm>,
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
pub enum UpdateOperator {
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

/// The point a specification read reads at. A specification is lowered once
/// and checked later, against different states, so most reads name a point
/// relative to the state they are checked in.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecPoint {
    /// The state being checked.
    Current,
    /// Its function's entry: `old(...)` in a contract.
    FunctionEntry,
    /// The enclosing loop's entry.
    LoopEntry,
    /// One fixed point: `old(...)` in a proof, `at(label, ...)`.
    At(ProgramPoint),
}

/// Body-derived origins of a pure function's pointer result. Null branches
/// contribute no origin. Argument origins are instantiated from the actual
/// value, never from the parameter's declared type or a destination cast.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct PurePointerResult {
    pub(crate) classes: BTreeSet<crate::kernel::effective_type::CAccessClass>,
    pub(crate) arguments: BTreeSet<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecExpression {
    Value(ProgramValue),
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
        program_type: ProgramType,
    },
    AlgebraicMatch {
        scrutinee: Box<SpecAlgebraicExpression>,
        arms: Vec<SpecAlgebraicMatchArm>,
    },
    ProgramExpression(ProgramExpression),
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
    /// Rust shifts preserve the operand width and owe only count bounds.
    RustShiftLeft(Box<SpecExpression>, Box<SpecExpression>),
    RustShiftRight(Box<SpecExpression>, Box<SpecExpression>),
    ShiftRight(Box<SpecExpression>, Box<SpecExpression>),
    BitwiseAnd(Box<SpecExpression>, Box<SpecExpression>),
    BitwiseOr(Box<SpecExpression>, Box<SpecExpression>),
    BitwiseXor(Box<SpecExpression>, Box<SpecExpression>),
    /// Unary minus retains float sign semantics until the operand is evaluated.
    Negate(Box<SpecExpression>),
    BitwiseNot(Box<SpecExpression>),
    Cast(Box<SpecExpression>, ProgramType),
    /// The operator at the root of the expression, one of `+ - * & | ^ ~`,
    /// at the 8- or 16-bit format its position expects (decision G2): over
    /// two operands of that format (an `int32` literal it holds takes the
    /// format), the operator's native node, `(a op b) mod 2^N`. Over operands
    /// of another type the operator keeps its promoted reading.
    NarrowArithmetic(Box<SpecExpression>, MachineIntegerType),
    /// An implicit pointer conversion retains the complete provenance.
    PointerCoercion(Box<SpecExpression>, ProgramType),
    /// `s.len()`: the element count of the slice `s` evaluates to, its
    /// metadata component, read in place with no unfold
    /// (`design/rust-slice-values.md`, step 2b-iii-c-i). A thin operand is
    /// a type mismatch.
    SliceLength(Box<SpecExpression>),
    /// `s.as_ptr()`: the thin data pointer of the slice `s` evaluates to,
    /// the same address, provenance and array object with no metadata.
    SliceData(Box<SpecExpression>),
    /// `slice::from_raw_parts(data, count)`: the slice whose thin part is
    /// `data` and whose element count is `count`, a `u64`. A wide `data` is
    /// refused with [`RuntimeError::ThinPointerRequired`]. Construction owes
    /// nothing; what a slice lets a program read is the resource it holds.
    SliceFromRawParts {
        data: Box<SpecExpression>,
        count: Box<SpecExpression>,
    },
    If {
        condition: Box<SpecProposition>,
        then_branch: Box<SpecExpression>,
        else_branch: Box<SpecExpression>,
    },
    RangeFold {
        start: Box<SpecExpression>,
        end: Box<SpecExpression>,
        initial: Box<SpecExpression>,
        accumulator: BindingName,
        item: BindingName,
        body: Box<SpecExpression>,
    },
    Let {
        name: BindingName,
        value: Box<SpecExpression>,
        body: Box<SpecExpression>,
    },
    PureFunctionApplication {
        name: String,
        arguments: Vec<SpecPureFunctionArgument>,
        result_type: ProgramType,
        pointer_result: Option<Arc<PurePointerResult>>,
        /// The class of the object a pointer result designates, from the
        /// function's declared return type (`design/effective-types.md`).
        result_object_class: Option<crate::kernel::effective_type::CAccessClass>,
    },
    LoopEntryState(Box<SpecExpression>),
    Subobject {
        pointer: Box<SpecExpression>,
        width: u32,
    },
    PointerOffset {
        pointer: Box<SpecExpression>,
        elements: Box<SpecExpression>,
        byte_width: u32,
    },
    MemoryLoad {
        point: SpecPoint,
        pointer: Box<SpecExpression>,
        value_type: ProgramType,
        /// Surface `exact(place)`: the read named by the selected state's own
        /// memory, with no version walk (`design/exact-reads.md`). An ordinary
        /// read (`false`) names the cell's version point.
        exact: bool,
    },
    /// A field of a by-value parameter, not a dereference of a C pointer.
    /// Its logical value remains available after the parameter storage ends.
    AggregateFieldValue {
        parameter: BindingName,
        pointer: Box<SpecExpression>,
        value_type: ProgramType,
    },
    /// `value`, defined only where `requirement` holds: its evaluation owes
    /// `requirement`, guarded as every evaluation obligation is, and adds no
    /// fact. A Rust subslice's length `b - a` requires `a <= b <= len`, where
    /// Rust panics otherwise.
    Requires {
        requirement: Box<SpecProposition>,
        value: Box<SpecExpression>,
    },
    /// Address a C place whose base is evaluated by the specification's state.
    /// No lexical binding or execution local is introduced.
    ObjectAddress(Box<SpecObjectAddress>),
}

/// The C place operations around a specification-evaluated address base.
/// Steps are stored outside-in, preserving C subobject provenance formation.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecAddressStep {
    Subobject { width: u32 },
    OffsetBytes { bytes: LayoutOffset },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct SpecObjectAddress {
    pub base: Box<SpecExpression>,
    pub steps: Vec<SpecAddressStep>,
    pub value_type: ProgramType,
    pub volatile: bool,
    pub pointee_constant: bool,
    pub access_class: Option<crate::kernel::effective_type::CAccessClass>,
    pub source: ExpressionLoadSource,
    pub checked: bool,
}

impl SpecObjectAddress {
    /// Rebuild only this node's metadata while a spec traversal maps its base.
    pub(crate) fn with_base(&self, base: SpecExpression) -> Self {
        Self {
            base: Box::new(base),
            steps: self.steps.clone(),
            value_type: self.value_type,
            volatile: self.volatile,
            pointee_constant: self.pointee_constant,
            access_class: self.access_class.clone(),
            source: self.source.clone(),
            checked: self.checked,
        }
    }

    /// Feed the selected base value to the ordinary C address operation.
    /// All place steps remain syntax, so member provenance is formed by the
    /// same checked transition as a program address, without a fake variable.
    pub(crate) fn program_expression(&self, base: ProgramValue) -> ProgramExpression {
        let mut pointer = ProgramExpression::Value(base);
        for step in self.steps.iter().rev() {
            pointer = match step {
                SpecAddressStep::Subobject { width } => ProgramExpression::Subobject {
                    pointer: Box::new(pointer),
                    width: *width,
                },
                SpecAddressStep::OffsetBytes { bytes } => ProgramExpression::PointerOffsetBytes {
                    pointer: Box::new(pointer),
                    bytes: *bytes,
                },
            };
        }
        let target = Box::new(ProgramExpression::TypedLoad {
            pointer: Box::new(pointer),
            value_type: self.value_type,
            volatile: self.volatile,
            pointee_constant: self.pointee_constant,
            access_class: self.access_class.clone(),
            source: self.source.clone(),
        });
        if self.checked {
            ProgramExpression::CheckedObjectAddress(target)
        } else {
            ProgramExpression::AddressOf(target)
        }
    }
}

impl SpecExpression {
    /// `self` at the position of a value of machine type `target`
    /// (decision G2, the type-directed arithmetic rule): at an 8- or 16-bit
    /// `target`, each `+ - * & | ^ ~` of its arithmetic spine, through the
    /// branches of a conditional and the body of a `let`, is that type's
    /// operator ([`Self::NarrowArithmetic`]). Every other expression, and
    /// every expression at another type, is unchanged. One visit per spine
    /// node.
    pub fn at_machine_type(self, target: ProgramType) -> Self {
        let Some(format) = MachineIntegerType::from_program_type(target).filter(|format| {
            matches!(
                format,
                MachineIntegerType::Int8
                    | MachineIntegerType::UInt8
                    | MachineIntegerType::Int16
                    | MachineIntegerType::UInt16
            )
        }) else {
            return self;
        };
        self.at_narrow_format(format)
    }

    fn at_narrow_format(self, format: MachineIntegerType) -> Self {
        let at = |expression: Box<Self>| Box::new(expression.at_narrow_format(format));
        let operation = match self {
            Self::Add(left, right) => Self::Add(at(left), at(right)),
            Self::Subtract(left, right) => Self::Subtract(at(left), at(right)),
            Self::Multiply(left, right) => Self::Multiply(at(left), at(right)),
            Self::BitwiseAnd(left, right) => Self::BitwiseAnd(at(left), at(right)),
            Self::BitwiseOr(left, right) => Self::BitwiseOr(at(left), at(right)),
            Self::BitwiseXor(left, right) => Self::BitwiseXor(at(left), at(right)),
            Self::BitwiseNot(operand) => Self::BitwiseNot(at(operand)),
            Self::If {
                condition,
                then_branch,
                else_branch,
            } => {
                return Self::If {
                    condition,
                    then_branch: at(then_branch),
                    else_branch: at(else_branch),
                };
            }
            Self::Let { name, value, body } => {
                return Self::Let {
                    name,
                    value,
                    body: at(body),
                };
            }
            other => return other,
        };
        Self::NarrowArithmetic(Box::new(operation), format)
    }
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
/// no lookup in `ExecutionState.locals` and no C representation.
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
    /// `if condition { then_branch } else { else_branch }` with Integer
    /// branches, evaluated as a scalar `if` is: a literally constant
    /// condition selects its branch, any other lowers both into one
    /// [`IntegerTerm::If`].
    If {
        condition: Box<SpecProposition>,
        then_branch: Box<Self>,
        else_branch: Box<Self>,
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
    Binding(BindingName),
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
    If {
        condition: Box<SpecProposition>,
        then_branch: Box<SpecAlgebraicExpression>,
        else_branch: Box<SpecAlgebraicExpression>,
    },
    /// The algebraic value a C value of this type holds: a Rust enum
    /// parameter, local or result, `ProgramValue::Parameter`.
    ProgramValue(Box<SpecExpression>),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ResourceFieldProjection {
    pub identity: InstanceRef,
    pub children: Vec<String>,
    /// Written member for a path whose final schema can differ from the
    /// parent's retained record. A witness uses its name, with no field index.
    pub field_name: Option<String>,
    pub field_index: usize,
    /// Select the explicit entry state supplied to spec evaluation. There is
    /// no fallback to the current state when that state is unavailable.
    pub at_entry: bool,
}

impl ResourceFieldProjection {
    pub(crate) const WITNESS: usize = usize::MAX;
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecPureFunctionArgument {
    /// Enforce a nominal pointer parameter without changing the argument's
    /// value or the memory state carried by an array reference.
    ObjectPointer {
        argument: Box<SpecPureFunctionArgument>,
        object_class: crate::kernel::effective_type::CAccessClass,
    },
    Value(SpecExpression),
    Integer(SpecIntegerExpression),
    Algebraic(SpecAlgebraicExpression),
    ArrayRef {
        point: SpecPoint,
        pointer: SpecExpression,
        element_type: ProgramType,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecAlgebraicValue {
    Program(SpecExpression),
    Integer(SpecIntegerExpression),
    Algebraic(SpecAlgebraicExpression),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct SpecAlgebraicMatchArm {
    pub variant: String,
    pub bindings: Vec<BindingName>,
    pub binding_types: Vec<AlgebraicValueType>,
    pub body: SpecExpression,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct SpecAlgebraicResultMatchArm {
    pub variant: String,
    pub bindings: Vec<BindingName>,
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
    pub bindings: Vec<BindingName>,
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
    Program(ProgramType),
    /// A pointer payload with a checked original object-class guarantee.
    /// Null is allowed; a destination cast alone does not establish the class.
    ObjectPointer(ProgramType, crate::kernel::effective_type::CAccessClass),
    Integer,
    Algebraic {
        name: String,
        arguments: Vec<AlgebraicValueType>,
    },
}

impl AlgebraicValueType {
    pub(crate) fn object_class(&self) -> Option<crate::kernel::effective_type::CAccessClass> {
        match self {
            Self::ObjectPointer(_, class) => Some(class.clone()),
            _ => None,
        }
    }

    pub(crate) fn accepts_program_value(&self, value: &ProgramValue) -> bool {
        match self {
            Self::Program(ty) => *ty == value.program_type(),
            Self::ObjectPointer(ty, class) => {
                matches!(value, ProgramValue::Pointer(pointer) if pointer.program_type() == *ty
                    && pointer.supports_object_class(class))
            }
            _ => false,
        }
    }

    pub(crate) fn symbolic_program_value(&self, variable: Variable) -> Option<ProgramValue> {
        let ty = match self {
            Self::Program(ty) | Self::ObjectPointer(ty, _) => *ty,
            _ => return None,
        };
        Some(
            crate::kernel::symbolic_call_result(ty, variable)
                .with_pointer_object_class(self.object_class()),
        )
    }
}

/// A resource field has a logical type, never a C storage location.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ResourceFieldType {
    Integer,
    Program(ProgramType),
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
                ResourceFieldType::Program(ty) => !matches!(
                    ty,
                    ProgramType::Void
                        | ProgramType::FunctionPointer(_)
                        | ProgramType::Int8Array(_)
                        | ProgramType::Int16Array(_)
                        | ProgramType::Int32Array(_)
                        | ProgramType::UInt8Array(_)
                        | ProgramType::UInt16Array(_)
                        | ProgramType::UInt32Array(_)
                        | ProgramType::Int128Array(_)
                        | ProgramType::Int64Array(_)
                        | ProgramType::UInt128Array(_)
                        | ProgramType::UInt64Array(_)
                        | ProgramType::Float32Array(_)
                        | ProgramType::Float64Array(_)
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
///
/// The schemas also record, beside the field types, the object class a
/// pointer field's declaration gives the object it designates
/// (`design/effective-types.md`). A field's kernel type spells every struct
/// pointer as an `int32` pointer, so this is where a symbolic value of the
/// field gets the class a parameter of the declared type would have. Like a
/// pointer value's class it is not part of the type's identity: two types
/// that differ only in it are equal, and only fresh symbolic field values
/// read it.
#[derive(Debug)]
pub struct AlgebraicSchemas {
    variants:
        std::collections::BTreeMap<AlgebraicValueType, std::sync::Arc<[AlgebraicVariantType]>>,
    grounded: std::collections::BTreeSet<AlgebraicValueType>,
    object_classes: std::collections::BTreeMap<AlgebraicValueType, AlgebraicFieldObjectClasses>,
}

/// The declared object class of each field of each constructor of one
/// algebraic type, by constructor name; a field without one is `None`.
pub(crate) type AlgebraicFieldObjectClasses = std::collections::BTreeMap<
    String,
    std::sync::Arc<[Option<crate::kernel::effective_type::CAccessClass>]>,
>;

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
                        AlgebraicValueType::Program(_)
                        | AlgebraicValueType::ObjectPointer(_, _)
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
        Self {
            variants,
            grounded,
            object_classes: std::collections::BTreeMap::new(),
        }
    }

    /// These schemas with the declared object classes of pointer fields.
    /// Entries for types or constructors without a classed field may be
    /// omitted.
    pub(crate) fn with_object_classes(
        mut self,
        object_classes: std::collections::BTreeMap<AlgebraicValueType, AlgebraicFieldObjectClasses>,
    ) -> Self {
        self.object_classes = object_classes;
        self
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
    /// A conditional algebraic value, built by [`AlgebraicTerm::if_then_else`]
    /// so that a constant condition or equal branches never stand.
    If {
        condition: Box<OldConditionTerm>,
        then_term: Box<AlgebraicTerm>,
        else_term: Box<AlgebraicTerm>,
    },
    /// The value of an abstract type parameter that memory `memory` holds at
    /// `pointer`, a generic struct's field: the algebraic counterpart of a
    /// [`OldMachineTerm::MemoryLoad`].
    MemoryLoad {
        point: ProgramPoint,
        pointer: Box<Address>,
    },
}

impl AlgebraicTermNode {
    /// The load term at the same memory and address as a
    /// [`AlgebraicTermNode::MemoryLoad`], decoded at its algebraic type
    /// ([`LoadKind::Algebraic`]): a walker reaches its memory and address as
    /// it reaches a scalar load's, and a load-atom comparison compares it as
    /// it compares one. It is no integer read of the cell: it equals no C
    /// scalar read, and no fact about one names it.
    pub(crate) fn memory_load_carrier(
        point: &ProgramPoint,
        pointer: &Address,
        algebraic_type: &AlgebraicType,
    ) -> OldMachineTerm {
        crate::kernel::OldMachineTerm::read_named(
            point.clone(),
            pointer.clone(),
            LoadKind::of_algebraic(algebraic_type),
        )
    }

    /// The [`AlgebraicTermNode::MemoryLoad`] whose carrier a rewrite of
    /// [`Self::memory_load_carrier_value`] left: a load at a memory and an
    /// address, still decoded at an algebraic type. `None` when the rewrite
    /// replaced the load.
    pub(crate) fn memory_load_from_carrier(carrier: &ProgramValue) -> Option<Self> {
        match carrier {
            ProgramValue::UInt64(OldMachineTerm::MemoryLoad(
                point,
                pointer,
                LoadKind::Algebraic(_),
            )) => Some(Self::MemoryLoad {
                point: point.point().clone(),
                pointer: pointer.boxed(),
            }),
            _ => None,
        }
    }

    /// [`Self::parameter_load`] read at `memory` itself, for tests.
    #[cfg(test)]
    pub(crate) fn parameter_load_unsited(
        memory: SharedMemory,
        pointer: Address,
        parameter: TypeParameterName,
    ) -> ProgramValue {
        let site = ProgramPoint::at(&memory);
        Self::parameter_load(memory, &site, pointer, parameter)
    }

    /// The value of abstract type `parameter` that `memory` holds at
    /// `pointer`, read at `site`.
    pub(crate) fn parameter_load(
        memory: SharedMemory,
        site: &ProgramPoint,
        pointer: Address,
        parameter: TypeParameterName,
    ) -> ProgramValue {
        // A value is named by the point its cell was last written, so a
        // read after unrelated stores is the read before them.
        let memory = crate::kernel::memory_history::canonical_value_load_memory(
            &memory,
            &pointer,
            AccessExtent::of_algebraic(&parameter.algebraic_type()),
        );
        Self::parameter_load_at(ProgramPoint::walked(&memory, site), pointer, parameter)
    }

    /// A checked cell observation uses the same typed version as a logical read.
    pub(crate) fn parameter_cell_load(
        source: &ProgramPoint,
        pointer: Address,
        parameter: TypeParameterName,
    ) -> ProgramValue {
        if let Some(version) =
            source.ordinary_typed_version(&pointer, ProgramType::Parameter(parameter))
        {
            return Self::parameter_load_at(version, pointer, parameter);
        }
        Self::parameter_load(source.shared_memory().clone(), source, pointer, parameter)
    }

    pub(crate) fn parameter_load_at(
        point: ProgramPoint,
        pointer: Address,
        parameter: TypeParameterName,
    ) -> ProgramValue {
        ProgramValue::Parameter(Box::new(AlgebraicTerm {
            algebraic_type: parameter.algebraic_type(),
            node: Self::MemoryLoad {
                point,
                pointer: Box::new(pointer),
            },
        }))
    }

    /// [`Self::memory_load_carrier`] as an algebraic field value, for the
    /// value-level walkers (substitution, rewriting, variable collection),
    /// which reach a 64-bit term through a `ProgramValue`. The `UInt64` tag
    /// only routes such a walker to its machine-term arm, which reads no
    /// format from it; the term inside is the decoding at the algebraic
    /// type. The walkers count work per level, so passing the term to them
    /// bare would change their work accounting.
    pub(crate) fn memory_load_carrier_value(
        point: &ProgramPoint,
        pointer: &Address,
        algebraic_type: &AlgebraicType,
    ) -> AlgebraicValue {
        AlgebraicValue::Program(ProgramValue::UInt64(Self::memory_load_carrier(
            point,
            pointer,
            algebraic_type,
        )))
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum PureFunctionArgument {
    Value(ProgramValue),
    /// A typed word argument whose expression remains in the common DAG.
    /// Its signedness is the argument's declared value sort, not an inferred
    /// mathematical observation. Readers borrow its operand view.
    SharedMachine(SharedMachineIntegerTerm),
    Integer(SharedIntegerTerm),
    Algebraic(AlgebraicTerm),
    ArrayRef {
        point: ProgramPoint,
        pointer: ProgramValue,
        element_type: ProgramType,
    },
}

/// A condition rewritten by a rewrite of scalar terms: as the condition of
/// `if condition { 1 } else { 0 }`, so a rewrite that decides it leaves the
/// constant it decided.
pub(crate) fn rewrite_condition_through_bits(
    condition: &OldConditionTerm,
    rewrite: impl FnOnce(&OldMachineTerm) -> OldMachineTerm,
) -> OldConditionTerm {
    let carrier = OldMachineTerm::If {
        condition: Box::new(condition.clone()),
        then_term: Box::new(OldMachineTerm::constant(1)),
        else_term: Box::new(OldMachineTerm::constant(0)),
    };
    match rewrite(&carrier) {
        OldMachineTerm::If {
            condition,
            then_term,
            else_term,
        } if *then_term == OldMachineTerm::constant(1)
            && *else_term == OldMachineTerm::constant(0) =>
        {
            *condition
        }
        bits32_constant!(1) => OldConditionTerm::Constant(true),
        bits32_constant!(0) => OldConditionTerm::Constant(false),
        _ => condition.clone(),
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum AlgebraicValue {
    Program(ProgramValue),
    Integer(IntegerTerm),
    Algebraic(AlgebraicTerm),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct AlgebraicBitvectorMatchArm {
    pub variant: String,
    pub bindings: Vec<AlgebraicValue>,
    pub body: OldMachineTerm,
    /// The written names of `bindings`, for printing only.
    pub binding_names: BindingNames,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct AlgebraicResultMatchArm {
    pub variant: String,
    pub bindings: Vec<AlgebraicValue>,
    pub body: AlgebraicTerm,
    /// The written names of `bindings`, for printing only.
    pub binding_names: BindingNames,
}

impl AlgebraicTerm {
    /// Visit scalar payload roots without expanding datatype schemas or copying
    /// terms. Callers decide how far to traverse each scalar expression.
    pub(crate) fn for_each_machine_operand(&self, mut visit: impl FnMut(MachineOperandView<'_>)) {
        enum Node<'a> {
            Algebraic(&'a AlgebraicTerm),
            Value(&'a ProgramValue),
            Offset(&'a AddressOffset),
        }
        let mut pending = vec![Node::Algebraic(self)];
        while let Some(node) = pending.pop() {
            match node {
                Node::Algebraic(term) => match &term.node {
                    AlgebraicTermNode::Variable(_) => {}
                    AlgebraicTermNode::Constructor { fields, .. } => {
                        for field in fields {
                            match field {
                                AlgebraicValue::Program(v) => pending.push(Node::Value(v)),
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
                                    AlgebraicValue::Program(v) => pending.push(Node::Value(v)),
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
                                PureFunctionArgument::SharedMachine(v) => {
                                    visit(v.operand_view());
                                    continue;
                                }
                                PureFunctionArgument::Algebraic(v) => Node::Algebraic(v),
                                PureFunctionArgument::Integer(_) => continue,
                            });
                        }
                    }
                    AlgebraicTermNode::MemoryLoad {
                        point: memory,
                        pointer,
                    } => {
                        visit(MachineOperandView::Old(
                            &AlgebraicTermNode::memory_load_carrier(
                                memory,
                                pointer,
                                &term.algebraic_type,
                            ),
                        ));
                    }
                    AlgebraicTermNode::If {
                        condition,
                        then_term,
                        else_term,
                    } => {
                        // The condition's terms are visited as the scalar
                        // conditional that carries them, so a caller walks
                        // them as it walks any condition.
                        visit(MachineOperandView::Old(&OldMachineTerm::If {
                            condition: condition.clone(),
                            then_term: Box::new(OldMachineTerm::constant(0)),
                            else_term: Box::new(OldMachineTerm::constant(0)),
                        }));
                        pending.push(Node::Algebraic(then_term));
                        pending.push(Node::Algebraic(else_term));
                    }
                },
                Node::Value(value) => match value.numeric_value() {
                    ProgramValue::PointerInteger(_) => unreachable!("numeric projection"),
                    ProgramValue::Parameter(term) => pending.push(Node::Algebraic(term)),
                    ProgramValue::Void => {}
                    ProgramValue::Bool(v) => visit(MachineOperandView::Old(v)),
                    ProgramValue::Pointer(v) => pending.push(Node::Offset(&v.address().offset)),
                    ProgramValue::Int8(v) => visit(MachineOperandView::Old(v)),
                    ProgramValue::Int16(v)
                    | ProgramValue::UInt16(v)
                    | ProgramValue::UInt8(v)
                    | ProgramValue::Int32(v)
                    | ProgramValue::UInt32(v)
                    | ProgramValue::Int64(v)
                    | ProgramValue::UInt64(v)
                    | ProgramValue::Int128(v)
                    | ProgramValue::UInt128(v)
                    | ProgramValue::Float32(v)
                    | ProgramValue::Float64(v) => visit(MachineOperandView::Old(v)),
                },
                Node::Offset(offset) => match offset.view() {
                    OffsetView::Constant(_) | OffsetView::Variable(_) => {}
                    OffsetView::Add(a, b) => {
                        pending.push(Node::Offset(a));
                        pending.push(Node::Offset(b));
                    }
                    OffsetView::Int32Scaled { .. } | OffsetView::Int64Scaled { .. } => {
                        for value in offset.scaled_operands() {
                            visit(value.operand_view());
                        }
                    }
                },
            }
        }
    }

    /// `if condition { then_term } else { else_term }`: one branch when the
    /// condition is a constant or both branches are the same term.
    pub(crate) fn if_then_else(
        condition: OldConditionTerm,
        then_term: AlgebraicTerm,
        else_term: AlgebraicTerm,
    ) -> AlgebraicTerm {
        match condition {
            OldConditionTerm::Constant(true) => then_term,
            OldConditionTerm::Constant(false) => else_term,
            _ if then_term == else_term => then_term,
            condition => AlgebraicTerm {
                algebraic_type: then_term.algebraic_type.clone(),
                node: AlgebraicTermNode::If {
                    condition: Box::new(condition),
                    then_term: Box::new(then_term),
                    else_term: Box::new(else_term),
                },
            },
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
            // Only a value whose C carrier is a type's, an abstract type
            // parameter's or a Rust enum's, is loaded.
            AlgebraicTermNode::MemoryLoad { .. } => {
                self.algebraic_type.rigid || TypeParameterName::carries(&self.algebraic_type)
            }
            AlgebraicTermNode::Constructor { .. } => self.checked_constructor_fields().is_some(),
            AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
                arguments.iter().all(PureFunctionArgument::is_well_formed)
            }
            AlgebraicTermNode::If {
                then_term,
                else_term,
                ..
            } => {
                then_term.algebraic_type == self.algebraic_type
                    && else_term.algebraic_type == self.algebraic_type
                    && then_term.is_well_formed()
                    && else_term.is_well_formed()
            }
            AlgebraicTermNode::Match { scrutinee, arms } => {
                if scrutinee.algebraic_type.rigid
                    || arms.len() != scrutinee.algebraic_type.variants.len()
                    || !scrutinee.is_well_formed()
                {
                    return false;
                }
                crate::instrumentation::record_deterministic_work(arms.len());
                let arms_by_variant: std::collections::HashMap<_, _> =
                    arms.iter().map(|arm| (arm.variant.as_str(), arm)).collect();
                arms_by_variant.len() == arms.len()
                    && scrutinee.algebraic_type.variants.iter().all(|variant| {
                        arms_by_variant
                            .get(variant.name.as_str())
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

    /// The object class the declaration of field `index` of constructor
    /// `variant` gives the object a pointer stored there designates. A type
    /// without classed fields answers without building its lookup key.
    pub(crate) fn field_object_class(
        &self,
        variant: &str,
        index: usize,
    ) -> Option<crate::kernel::effective_type::CAccessClass> {
        if self.rigid || self.schemas.object_classes.is_empty() {
            return None;
        }
        self.schemas
            .object_classes
            .get(&self.value_type())?
            .get(variant)?
            .get(index)?
            .clone()
    }

    /// A fresh symbolic value for field `index` of constructor `variant`,
    /// of kernel type `program_type`, carrying the class its declaration gives a
    /// pointer field's object.
    pub(crate) fn symbolic_program_field_value(
        &self,
        variant: &str,
        index: usize,
        program_type: ProgramType,
        variable: Variable,
    ) -> ProgramValue {
        let value = crate::kernel::symbolic_call_result(program_type, variable);
        match program_type
            .is_pointer()
            .then(|| self.field_object_class(variant, index))
            .flatten()
        {
            Some(class) => value.with_pointer_object_class(Some(class)),
            None => value,
        }
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

impl From<ProgramValue> for AlgebraicValue {
    fn from(value: ProgramValue) -> Self {
        Self::Program(value)
    }
}

impl AlgebraicValue {
    pub fn as_program_value(&self) -> Option<&ProgramValue> {
        match self {
            Self::Program(value) => Some(value),
            Self::Integer(_) => None,
            Self::Algebraic(_) => None,
        }
    }

    pub(in crate::kernel) fn value_type(&self) -> AlgebraicValueType {
        match self {
            Self::Program(value) => AlgebraicValueType::Program(value.program_type()),
            Self::Integer(_) => AlgebraicValueType::Integer,
            Self::Algebraic(value) => value.algebraic_type.value_type(),
        }
    }

    pub(crate) fn has_type(&self, expected: &AlgebraicValueType) -> bool {
        match self {
            Self::Program(value) => expected.accepts_program_value(value),
            _ => self.value_type() == *expected,
        }
    }

    fn is_well_formed_for(
        &self,
        expected: &AlgebraicValueType,
        schemas: &AlgebraicSchemas,
    ) -> bool {
        if let Self::Program(value) = self {
            return expected.accepts_program_value(value);
        }
        if &self.value_type() != expected {
            return false;
        }
        match self {
            Self::Program(_) => true,
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
    /// Numeric identity for typed argument matching. The stored argument keeps
    /// its exact producer payload; only checking asks for this observation.
    pub(crate) fn machine_identity(&self) -> Option<SharedMachineIntegerTerm> {
        match self {
            Self::SharedMachine(value) => Some(match value.shared_operand() {
                Some(root) => SharedMachineIntegerTerm::observe_shared(value.ty(), root.clone())
                    .expect("typed shared machine argument"),
                None => value.clone(),
            }),
            Self::Value(value) => {
                let (integer_c_value!(bits)) = value else {
                    return None;
                };
                Some(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::from_program_type(value.program_type()).unwrap(),
                    bits.clone(),
                ))
            }
            _ => None,
        }
    }

    fn is_well_formed(&self) -> bool {
        match self {
            Self::Value(_) | Self::SharedMachine(_) => true,
            Self::Integer(_) => true,
            Self::Algebraic(term) => term.is_well_formed(),
            Self::ArrayRef {
                pointer,
                element_type,
                ..
            } => pointer.program_type().is_pointer() && *element_type != ProgramType::Void,
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
        point: SpecPoint,
        pointer: SpecExpression,
    },
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
        operator: ComparisonOperator,
        right: SpecExpression,
    },
    FloatClassification {
        expression: SpecExpression,
        classification: FloatClassification,
    },
    /// A written `true` or `false`: lowers to that constant condition
    /// directly, not through a comparison.
    Truth(bool),
    And(Box<SpecProposition>, Box<SpecProposition>),
    Or(Box<SpecProposition>, Box<SpecProposition>),
    Not(Box<SpecProposition>),
    Implies(Box<SpecProposition>, Box<SpecProposition>),
    ForAllInt32 {
        name: BindingName,
        variable: Variable,
        body: Box<SpecProposition>,
    },
    ForAllMachineInteger {
        name: BindingName,
        variable: Variable,
        integer_type: MachineIntegerType,
        body: Box<SpecProposition>,
    },
    ForAllInteger {
        name: BindingName,
        variable: Variable,
        body: Box<SpecProposition>,
    },
    ForAllAlgebraic {
        name: BindingName,
        variable: Variable,
        algebraic_type: AlgebraicType,
        body: Box<SpecProposition>,
    },
    ForAllPointer {
        name: BindingName,
        variable: Variable,
        program_type: ProgramType,
        body: Box<SpecProposition>,
    },
    ExistsInt32 {
        name: BindingName,
        variable: Variable,
        body: Box<SpecProposition>,
    },
    ExistsMachineInteger {
        name: BindingName,
        variable: Variable,
        integer_type: MachineIntegerType,
        body: Box<SpecProposition>,
    },
    ExistsInteger {
        name: BindingName,
        variable: Variable,
        body: Box<SpecProposition>,
    },
    ExistsAlgebraic {
        name: BindingName,
        variable: Variable,
        algebraic_type: AlgebraicType,
        body: Box<SpecProposition>,
    },
    ExistsPointer {
        name: BindingName,
        variable: Variable,
        program_type: ProgramType,
        body: Box<SpecProposition>,
    },
    /// Observe this state's mutex protocol without conferring ownership.
    MutexHeld(Box<SpecExpression>),
    Predicate {
        name: String,
        arguments: Vec<SpecPredicateArgument>,
        /// Whether the definition observes the resource model. SymbolicMemory states
        /// remain explicit predicate arguments independently of this flag.
        resource_state_dependent: bool,
    },
    ResourceSeparate {
        left: SpecResource,
        right: SpecResource,
    },
    ResourceViewable {
        point: SpecPoint,
        resource: SpecResource,
    },
    ResourceContains {
        parent: SpecResource,
        child: SpecResource,
    },
    MemoryLoadable {
        point: SpecPoint,
        base: SpecExpression,
        start: SpecExpression,
        end: SpecExpression,
        element_width: u32,
    },
    /// The whole evaluation domain of an expression: every operation in it
    /// is defined. Kernel producers state this for a term they evaluate;
    /// it lowers to the conjunction of each operation's domain.
    Defined(SpecExpression),
    /// Lowered from the `defined(...)` special form: the domain of the
    /// expression's root operation, with its operands taken as values. An
    /// operand's own domain is an ordinary obligation of the term, not part
    /// of the claim (`kernel::spec::operation_defined`).
    OperationDefined(SpecExpression),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct SequenceTerm {
    pub element_type: Option<ProgramType>,
    pub node: std::sync::Arc<SequenceTermNode>,
}

impl SequenceTerm {
    pub(crate) fn map_program_values(
        &self,
        map: &mut impl FnMut(&ExecutionValue) -> ExecutionValue,
    ) -> Self {
        let node = match self.node.as_ref() {
            SequenceTermNode::Literal(values) => {
                SequenceTermNode::Literal(SequenceValues::from_values((0..values.len()).map(
                    |index| match values.retained_value_ref(index) {
                        Some(value) => map(value),
                        None => map(&ExecutionValue::Native(
                            values.get(index).expect("sequence element").clone(),
                        )),
                    },
                )))
            }
            SequenceTermNode::Concat(left, right) => SequenceTermNode::Concat(
                left.map_program_values(map),
                right.map_program_values(map),
            ),
        };
        Self {
            element_type: self.element_type,
            node: std::sync::Arc::new(node),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SequenceTermNode {
    Literal(SequenceValues),
    Concat(SequenceTerm, SequenceTerm),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecResource {
    Star(Box<SpecResource>, Box<SpecResource>),
    Instance {
        identity: InstanceId,
        at_entry: bool,
    },
    Value(Resource),
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
pub struct SwitchCase {
    /// `None` is the default case; integer values are represented in the
    /// promoted int32 or uint32 bit pattern used by C.
    pub value: Option<u32>,
    pub body: Box<ProgramStatement>,
}

/// Stable identity of one source control-flow target inside a function.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ControlTargetId(pub(crate) u32);

/// The exact executable frontier named by a control-flow target.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct ControlTarget {
    pub(crate) statement_index: usize,
    pub(crate) remaining: std::sync::Arc<ProgramStatement>,
}

/// Allocation and initialization policy for an automatic aggregate object.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum AggregateDeclarationKind {
    /// Ordinary local storage, with no explicit constructor ownership grant.
    Local,
    /// Existing frontend protocol: seed placeholders and require the frontend
    /// to prove that constructors overwrite them before observation.
    Constructor,
    /// Fresh owned storage. Only actual writes initialize its fields.
    ConstructionDestination,
}

/// Storage type of an aggregate expression result. It has no program-local name.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct AggregateResultLayout {
    pub layout: AggregateLayout,
    pub declared_class: Option<crate::kernel::effective_type::CAccessClass>,
}

/// How a named call selects its contract.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CallDispatch {
    #[default]
    Direct,
    CppVirtual,
}

#[derive(Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ProgramStatement {
    Skip,
    Break,
    Continue,
    /// A source-directed edge whose target is resolved in the containing
    /// function's checked control-flow table.
    Goto {
        target: ControlTargetId,
        /// Automatic objects in the lexical scopes the edge leaves.
        exited_locals: std::sync::Arc<[BindingName]>,
    },

    Declare {
        /// A scalar construction initializer, evaluated after fresh allocation.
        /// This is the only declaration transition permitted to initialize const storage.
        initializer: Option<ProgramExpression>,
        name: BindingDeclaration,
        program_type: ProgramType,
        volatile: bool,
        pointee_volatile: bool,
        constant: bool,
        pointee_constant: bool,
        /// Present for an automatic array declared with an initializer: the
        /// declaration zero-fills the object, and the initializer's written
        /// elements follow as ordinary stores. Absent, the object is
        /// uninitialized.
        zero_fill: Option<ZeroFill>,
        /// The class of the object, or of its elements, when the kernel type
        /// cannot give it (`design/effective-types.md`).
        declared_class: Option<crate::kernel::effective_type::CAccessClass>,
    },
    /// Declare an address-backed scalar-only aggregate. Aggregate values are
    /// not runtime `ProgramValue`s; their local binding exposes the block base so
    /// field lowering can continue to use typed memory accesses.
    DeclareAggregate {
        name: BindingDeclaration,
        layout: AggregateLayout,
        kind: AggregateDeclarationKind,
        /// The object's class for the strict-aliasing check, a struct's
        /// (`design/effective-types.md`).
        declared_class: Option<crate::kernel::effective_type::CAccessClass>,
    },
    /// Copy an address-backed aggregate, preserving typed views for any
    /// overlapping union members in its layout.
    CopyAggregate {
        target: ProgramExpression,
        source: ProgramExpression,
        layout: AggregateLayout,
    },
    /// Write a scalar-array region with one evaluated repeated value or a
    /// uniform initialized local source. `fresh` additionally requires complete
    /// fresh local storage. Authority is checked; count never expands into nodes.
    InitializeScalarArray {
        target: ProgramExpression,
        source: ProgramExpression,
        element_type: ProgramType,
        count: u32,
        copy: bool,
        fresh: bool,
    },
    Assign {
        name: BindingName,
        expression: ProgramExpression,
        source: super::source_access::StatementAssignSource,
        /// Leaves the target's value from before this assignment as the
        /// result of step N, which the rest of the statement reads: the
        /// value of a postfix `p++`.
        prior_result: Option<u32>,
    },
    /// Invoke a construction-return function in an already allocated destination.
    /// The call constructs the object; there is no result assignment or copy.
    CallConstruct {
        target: BindingName,
        function_name: String,
        arguments: Vec<ProgramExpression>,
    },
    /// Record the GNU builtin's unknown integer result, either 0 or 1.
    BuiltinConstantP {
        step: u32,
    },
    /// Form a callable with the written closure's captured values.
    CreateClosure {
        step: u32,
        closure: String,
        captures: Vec<ProgramExpression>,
        source: Option<ClosureSite>,
    },
    /// A call inside an expression of the statement that follows it: its
    /// result is that statement's `ProgramExpression::StepResult { step, .. }`,
    /// never a variable of the program.
    CallResult {
        aggregate_layout: Option<AggregateResultLayout>,
        call: u32,
        function_name: String,
        arguments: Vec<ProgramExpression>,
        /// The callee's declared result type, which the result takes as an
        /// assignment to a local of that type would; `None` keeps the
        /// contract's own.
        result_type: Option<ProgramType>,
        result_aggregate_layout: Option<AggregateLayout>,
        result_pointee_constant: bool,
        dispatch: CallDispatch,
        /// The function pointer the call goes through, when it is not a
        /// call of a named function; `function_name` then only describes it.
        callee: Option<Callee>,
    },
    Call {
        function_name: String,
        arguments: Vec<ProgramExpression>,
        dispatch: CallDispatch,
        /// The function pointer the call goes through, when it is not a
        /// call of a named function; `function_name` then only describes it.
        callee: Option<Callee>,
        /// The typed reference transfer, with its source provenance when available.
        reference_binding: Option<Arc<ReferenceBindingOperation>>,
    },
    /// A value the rest of its statement reads: the value an operator that
    /// decides between its operands (`&&`, `||`, the ternary operator) takes
    /// at the end of the arm that computed it, a statement expression's
    /// value, or a value read before a call. It is the result of each of
    /// `steps`, one per expression that reads it; with none, the value is
    /// evaluated and discarded, as an expression statement's is. It has
    /// `value_type` when one is given, as an assignment to a local of that
    /// type would give it.
    StepValue {
        aggregate_layout: Option<AggregateResultLayout>,
        steps: Vec<u32>,
        expression: ProgramExpression,
        value_type: Option<ProgramType>,
        pointee_constant: bool,
    },
    /// Allocate a runtime-sized heap block and assign either null or its fresh
    /// base pointer to `target`.
    HeapAllocate {
        target: BindingName,
        bytes: ProgramExpression,
        zeroed: bool,
        /// A directly bound struct object: class, complete size, and alignment.
        object_type: Option<(crate::kernel::effective_type::CAccessClass, u32, u32)>,
        /// The allocation's failure ends the program instead of yielding
        /// null, as a C++ `new` does in a `noexcept` function: no execution
        /// continues past a failure, so only the success outcome follows.
        ends_program_on_failure: bool,
    },
    /// End the heap allocation named by `pointer`. Null is a no-op.
    HeapFree {
        pointer: ProgramExpression,
    },
    Assert {
        condition: ProgramExpression,
        label: Option<String>,
    },
    /// Statements run in order: a source block, or a statement region an
    /// execution frontier still has to run. Its statements are a persistent
    /// sequence shared by the frontiers that advance through it, and it
    /// stands for the pair tree `Seq(first, Seq(second, ...))` it replaced
    /// (see [`ProgramStatementSequence`]).
    Seq(ProgramStatementSequence),
    Return(ProgramExpression),
    /// Produce a checked exceptional outcome. The first internal slice carries
    /// one int32 payload; source-language handler matching lands separately.
    Throw(ProgramExpression),
    /// Throw a fresh opaque value of a nominal type. The frontend has checked
    /// construction and trivial destruction; the outcome names it `exception`.
    ThrowOpaque(TypeParameterName),
    /// Catch an int32 exceptional outcome from `try_body` and bind its payload
    /// for the handler. Other outcomes retain their original path and state.
    TryCatchInt32 {
        try_body: Box<ProgramStatement>,
        binding: BindingName,
        handler: Box<ProgramStatement>,
    },
    /// `body`, which may exit by throwing while destructible objects are
    /// live, as a C++ call made in their scope can. On an int32 exceptional
    /// exit, `cleanup` (their destructors) runs and the same exception
    /// continues to propagate; every other outcome is `body`'s own. It is
    /// not a source handler: nothing is caught, and no binding is introduced.
    UnwindCleanup {
        body: Box<ProgramStatement>,
        cleanup: Box<ProgramStatement>,
    },
    Store {
        pointer: ProgramExpression,
        value: ProgramExpression,
    },
    TypedStore {
        pointer: ProgramExpression,
        value: ProgramExpression,
        value_type: ProgramType,
        /// The class of the stored lvalue when `value_type` erases it; see
        /// [`ProgramExpression::TypedLoad::access_class`].
        access_class: Option<crate::kernel::effective_type::CAccessClass>,
        /// See [`ProgramExpression::TypedLoad::volatile`].
        volatile: bool,
        /// The destination pointer cell's declared pointee qualification.
        pointee_constant: bool,
        /// Source origin only; checked memory authority is still required.
        source: super::StatementStoreSource,
    },
    /// Evaluate a compound-assignment or increment target as one lvalue,
    /// read it, apply the operator with the operand, and write the result back.
    Update {
        target: ProgramExpression,
        operator: UpdateOperator,
        operand: ProgramExpression,
    },
    If {
        condition: ProgramExpression,
        then_branch: Box<ProgramStatement>,
        else_branch: Box<ProgramStatement>,
    },
    /// A loop's own test, inside a pass, after the statements the loop runs
    /// between its entry and its test: true continues the pass, false leaves
    /// the loop. It is a position of the loop as written, `loop(i).test`, never
    /// a statement of the source program.
    LoopTest {
        aggregate_steps: Vec<u32>,
        condition: ProgramExpression,
    },
    /// Shared loop form for structured loops and checked natural cycles.
    Loop {
        /// The loop's one test region, outside the body scope.
        test: LoopTestRegion,
        /// Shared update region, entered after leaving the body scope.
        update: Option<std::sync::Arc<ProgramStatement>>,
        invariant: Vec<Proposition>,
        invariant_checks: Vec<LoopInvariantCheck>,
        effect_checks: Vec<LoopEffectCheck>,
        /// Resources the loop declares for itself. An empty list means the
        /// body executes with the enclosing resource context; a declaration
        /// narrows that context to exactly these resources, with everything
        /// else the enclosing frame owns viewed rather than owned.
        resource_specs: Vec<ResourceSpec>,
        /// The loop's declared `decreases` components, in source order. An
        /// empty list means the loop is unranked. Each component is one
        /// int32-valued expression evaluated at the iteration entry and again
        /// at the back edge; the back-edge invariant bundle carries one
        /// nonnegativity obligation per component and one lexicographic
        /// decrease obligation over them.
        ranking_measures: Vec<RankingComponent>,
        /// The loop's declared structural `decreases` binder, when the clause
        /// named a loop resource binder instead of int32 components (D6).
        /// The back edge checks that the instance the binder ends holding is
        /// a direct contained child, in the exact resource definition, of the
        /// instance it held at the loop head.
        structural_measure: Option<String>,
        /// When present, this is a proof-only natural cycle whose source body
        /// retains a checked `goto` to the target. The matching jump is the
        /// back edge; ordinary completion of the body is the cycle exit.
        backedge_target: Option<ControlTargetId>,
        /// When present, a proof-only natural cycle has one checked forward
        /// `goto` that leaves the cycle at this target.
        natural_exit_target: Option<ControlTargetId>,
        body: Box<ProgramStatement>,
    },
    Switch {
        expression: ProgramExpression,
        cases: Vec<SwitchCase>,
    },
    /// End selected automatic objects at a frontend-recorded lifetime boundary,
    /// including a full expression's materialized temporaries. This retires
    /// their storage and ownership, never the allocations their fields name.
    EndAutomaticLifetimes {
        names: Vec<BindingName>,
        steps: Vec<u32>,
    },
}

/// Where an effectful loop test runs relative to its body.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum LoopTestPosition {
    BeforeBody,
    AfterBody,
}

/// The phase selected at an iteration entry or a checked preservation point.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum LoopEntryPhase {
    Test,
    Body,
}

/// Every loop has one test region: optional preparation, a decision and cleanup.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct LoopTestRegion {
    pub statement: std::sync::Arc<ProgramStatement>,
    pub position: LoopTestPosition,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct LoopInvariantCheck {
    pub(super) proposition: SpecProposition,
    pub(super) entry_context: Option<String>,
    pub(super) preservation_context: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct LoopEffectCheck {
    pub(super) effect: LoopEffect,
    pub(super) span: LoopEffectSpan,
    pub(super) context: Option<String>,
    /// The semantic origin is typed so diagnostics cannot be mistaken for
    /// authority.  Inherited resource frames are replaced by
    /// `validated_ranges` at the function entry before loop proof starts.
    pub(super) origin: LoopEffectOrigin,
    pub(super) validated_ranges: Option<Vec<MemoryRange>>,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum LoopEffectOrigin {
    #[default]
    Unspecified,
    Explicit,
    DeclaredResource,
    InheritedResourceDerived,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum LoopEffect {
    Mutable(Vec<MemorySegment>),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum LoopEffectSpan {
    Whole,
    Step,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct MemorySegment {
    pub(super) base: ProgramExpression,
    pub(super) start: ProgramExpression,
    pub(super) end: ProgramExpression,
    /// The ABI width of one logical range element. The compatibility
    /// constructor defaults to the historical int32 width; typed surface
    /// lowering preserves wider struct-array strides here.
    pub(super) element_width: u32,
    /// An optional entry-state condition guarding a contract footprint.
    /// Resource and loop segments are normally unconditional.
    pub(super) guard: Option<SpecProposition>,
    /// `uninitialized(p[a..b])` in a contract: the bytes are held with no
    /// claim that they are initialized. The callee's proof starts with them
    /// unwritten, and a produced range reaches the caller unwritten. The
    /// resource itself is ordinary ownership of the range.
    pub(super) uninitialized: bool,
    /// The byte runs, from the start of the range, that hold values: a
    /// scalar field's leading bytes, or an object's fields. The rest is
    /// padding, which holds nothing to initialize. `None` is every byte.
    pub(super) value_runs: SegmentValueRuns,
}

/// Where a segment's values lie, read only by a call's initialization check.
/// It describes the layout under the range, not what the contract says, so
/// two segments that differ only here are the same clause: an override's
/// `views *this` is its interface's.
#[derive(Clone, Debug, Default)]
pub struct SegmentValueRuns(pub(super) Option<std::sync::Arc<[(u32, u32)]>>);

impl PartialEq for SegmentValueRuns {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl Eq for SegmentValueRuns {}

impl std::hash::Hash for SegmentValueRuns {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}

impl PartialOrd for SegmentValueRuns {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SegmentValueRuns {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

#[derive(Clone, Debug)]
pub struct MemoryRange {
    pub(super) base: Address,
    /// Origin of the value naming the range, independent of address aliases.
    pub(super) provenance: Address,
    /// A typed clause also demands this carrier's provenance. Raw kernel
    /// intervals ask only about physical authority; both retain supplier
    /// provenances through resource algebra and subsequent C access checks.
    pub(super) typed_carrier: bool,
    /// The array object of the pointer that named the range. It has no
    /// bounds of its own: the range's bytes are its bounds.
    pub(super) carrier: ArrayObject,
    /// The bounds, in elements. Read them through [`MemoryRange::start`]
    /// and [`MemoryRange::end`], which hold only for an `Int32` range, or
    /// through [`MemoryRange::wide_bounds`]: a term carries no width, so a
    /// wide bound read as a signed 32-bit index is a different number.
    start_bound: StoredMachineTerm,
    end_bound: StoredMachineTerm,
    /// The size in bytes of one logical element in `start..end`.
    ///
    /// Resource ranges remain expressed in logical element coordinates, but
    /// retaining this width lets kernel consumers derive their physical byte
    /// footprint without recovering the source C type.
    pub(super) element_width: u32,
    /// How the bounds are read. Last, so ranges order by base first and
    /// `Int32` ranges keep the order they had among themselves.
    kind: RangeIndexKind,
    /// Parent-member bounds established while evaluating this footprint.
    /// Evidence only: it never changes the identity or authority of the range.
    pub(super) formation_coverage: Arc<[Proposition]>,
    /// For the whole object of a symbolic layout, `[p, p + sizeof(L))`, the
    /// fields of `L` taken out of it, sorted: the range holds the object's
    /// bytes but theirs. Empty for every other range. Only the field rules
    /// read a range with holes; every other route refuses it.
    pub(super) holes: Arc<[u32]>,
}

impl MemoryRange {
    // The mode changes what a requested clause must establish, not the
    // identity of the physical authority and retained carrier it names.
    fn identity(
        &self,
    ) -> (
        &Address,
        &Address,
        Option<&Address>,
        &StoredMachineTerm,
        &StoredMachineTerm,
        u32,
        RangeIndexKind,
        &[u32],
    ) {
        (
            &self.base,
            &self.provenance,
            self.carrier.owner(),
            &self.start_bound,
            &self.end_bound,
            self.element_width,
            self.kind,
            &self.holes,
        )
    }
}
impl PartialEq for MemoryRange {
    fn eq(&self, other: &Self) -> bool {
        self.identity() == other.identity()
    }
}
impl Eq for MemoryRange {}
impl std::hash::Hash for MemoryRange {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.identity().hash(state);
    }
}
impl PartialOrd for MemoryRange {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for MemoryRange {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.identity().cmp(&other.identity())
    }
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

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ProgramParameter {
    pub(super) name: BindingDeclaration,
    pub(super) program_type: ProgramType,
    pub(super) aggregate_layout: Option<AggregateLayout>,
    pub(super) volatile: bool,
    pub(super) pointee_volatile: bool,
    pub(super) constant: bool,
    pub(super) pointee_constant: bool,
    /// The class of the object a pointer parameter's declaration says it
    /// designates, when the frontend supplied one.
    pub(super) pointee_class: Option<crate::kernel::effective_type::CAccessClass>,
    /// Relative index of a Rust slice's adjacent length argument. Its valid
    /// length grants formation bounds across argument/value-parameter splits,
    /// independently of byte access authority. C pointers have none.
    pub(super) slice_length_parameter: Option<usize>,
    /// Byte width of the bounds of a valid fixed-size Rust array reference. This grants
    /// pointer formation bounds, independently of byte access authority.
    /// The bytes a Rust array or struct reference designates: a number,
    /// or a symbolic struct's `sizeof`.
    pub(super) fixed_reference_bounds: Option<LayoutSize>,
}

/// A linked file-scope scalar. Globals use one stable memory block across all
/// function frames; the initial value is installed when the first function
/// entry state is created.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Global {
    pub(super) source_name: String,
    pub(super) kernel_name: BindingDeclaration,
    pub(super) program_type: ProgramType,
    pub(super) initial_value: ProgramValue,
    /// The value is supplied by a linked declaration of a const library
    /// object and is available independently of a function's memory frame.
    pub(super) linked_library_value: bool,
    pub(super) volatile: bool,
    pub(super) pointee_volatile: bool,
    pub(super) constant: bool,
    pub(super) pointee_constant: bool,
    /// The object's strict-aliasing class (`design/effective-types.md`),
    /// when the frontend knows more than the kernel type says.
    pub(super) declared_class: Option<crate::kernel::effective_type::CAccessClass>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct GlobalArray {
    pub(super) source_name: String,
    pub(super) kernel_name: BindingDeclaration,
    pub(super) element_type: ProgramType,
    pub(super) length: u32,
    pub(super) initial_values: ArrayContents,
    pub(super) constant: bool,
    /// The object's strict-aliasing class (`design/effective-types.md`),
    /// when the frontend knows more than the kernel type says.
    pub(super) declared_class: Option<crate::kernel::effective_type::CAccessClass>,
}

/// A linked file-scope aggregate. The layout describes the typed leaf cells
/// that occupy the stable global block; aggregate values themselves have no
/// scalar `ProgramValue` representation.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct GlobalAggregate {
    pub(super) source_name: String,
    pub(super) kernel_name: BindingDeclaration,
    pub(super) layout: AggregateLayout,
    pub(super) initializers: Vec<AggregateInitializer>,
    pub(super) constant: bool,
    /// The object's strict-aliasing class (`design/effective-types.md`),
    /// when the frontend knows more than the kernel type says.
    pub(super) declared_class: Option<crate::kernel::effective_type::CAccessClass>,
}

/// A linked file-scope array of supported struct aggregates. Initializer
/// offsets are relative to the complete array block; omitted cells are
/// zero-filled when the block is first materialized.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct GlobalAggregateArray {
    pub(super) source_name: String,
    pub(super) kernel_name: BindingDeclaration,
    pub(super) layout: AggregateLayout,
    pub(super) length: u32,
    pub(super) initializers: Vec<AggregateInitializer>,
    pub(super) constant: bool,
    /// The object's strict-aliasing class (`design/effective-types.md`),
    /// when the frontend knows more than the kernel type says.
    pub(super) declared_class: Option<crate::kernel::effective_type::CAccessClass>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct StaticLocal {
    pub(super) source_name: String,
    pub(super) kernel_name: BindingDeclaration,
    pub(super) program_type: ProgramType,
    pub(super) initial_value: ProgramValue,
    pub(super) volatile: bool,
    pub(super) pointee_volatile: bool,
    pub(super) constant: bool,
    pub(super) pointee_constant: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct StaticArray {
    pub(super) source_name: String,
    pub(super) kernel_name: BindingDeclaration,
    pub(super) element_type: ProgramType,
    pub(super) length: u32,
    pub(super) initial_values: ArrayContents,
    pub(super) constant: bool,
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
pub struct ArrayContents {
    length: u32,
    default: ProgramValue,
    elements: std::sync::Arc<[(u32, ProgramValue)]>,
}

impl ArrayContents {
    /// `length` elements holding `default`, except each listed `(index,
    /// value)`. The indices must be ascending, distinct and below `length`;
    /// a listed value equal to `default` is dropped.
    pub fn new(
        length: u32,
        default: ProgramValue,
        elements: impl IntoIterator<Item = (u32, ProgramValue)>,
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
    pub fn default_value(&self) -> &ProgramValue {
        &self.default
    }

    /// The elements holding something other than the default, ascending.
    pub fn explicit_elements(&self) -> &[(u32, ProgramValue)] {
        &self.elements
    }

    /// Whether some element holds the default.
    pub fn has_default_elements(&self) -> bool {
        self.elements.len() < self.length as usize
    }

    /// The value element `index` holds.
    pub fn value_at(&self, index: u32) -> &ProgramValue {
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
    pub fn values(&self) -> impl Iterator<Item = &ProgramValue> + '_ {
        self.has_default_elements()
            .then_some(&self.default)
            .into_iter()
            .chain(self.elements.iter().map(|(_, value)| value))
    }

    /// Every element's value in index order, one per element.
    #[cfg(test)]
    pub fn dense_values(&self) -> Vec<ProgramValue> {
        (0..self.length)
            .map(|index| self.value_at(index).clone())
            .collect()
    }
}

impl From<Vec<ProgramValue>> for ArrayContents {
    /// One value per element, index order. The last value is the default,
    /// so a trailing stretch of equal values is not listed.
    fn from(values: Vec<ProgramValue>) -> Self {
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
/// ([`SymbolicMemory::with_constant_runs`]).
///
/// [`CellRun`]: crate::kernel::primitives::CellRun
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ConstantRun {
    pub(crate) offset: u32,
    pub(crate) stride: u32,
    pub(crate) count: u32,
    pub(crate) value: ProgramValue,
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
pub struct ZeroFill {
    pub(super) stride: u32,
    pub(super) count: u32,
    pub(super) cells: std::sync::Arc<[ZeroCell]>,
    /// Explicit values constructed inside a const scalar-array declaration.
    pub(crate) written_elements: std::sync::Arc<[(u32, ProgramExpression)]>,
}

/// One zero store of every element of a [`ZeroFill`]: `zero`, the zero
/// initializer's value, stored as a `value_type` cell `offset` bytes into
/// the element, with the store's pointee qualification.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ZeroCell {
    pub(super) offset: u32,
    pub(super) value_type: ProgramType,
    pub(super) pointee_constant: bool,
    pub(super) zero: ProgramValue,
}

impl ZeroFill {
    pub fn new(stride: u32, count: u32, cells: Vec<ZeroCell>) -> Self {
        Self {
            stride,
            count,
            cells: cells.into(),
            written_elements: Default::default(),
        }
    }

    pub(crate) fn expressions(&self) -> impl Iterator<Item = &ProgramExpression> {
        self.written_elements
            .iter()
            .map(|(_, expression)| expression)
    }

    pub(crate) fn with_written_elements(mut self, written: Vec<(u32, ProgramExpression)>) -> Self {
        self.written_elements = written.into();
        self
    }
}

impl ZeroCell {
    pub fn new(
        offset: u32,
        value_type: ProgramType,
        pointee_constant: bool,
        zero: ProgramValue,
    ) -> Self {
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
pub struct StaticAggregate {
    pub(super) source_name: String,
    pub(super) kernel_name: BindingDeclaration,
    pub(super) layout: AggregateLayout,
    pub(super) initializers: Vec<AggregateInitializer>,
    pub(super) constant: bool,
}

/// A function-local static array of supported struct aggregates.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct StaticAggregateArray {
    pub(super) source_name: String,
    pub(super) kernel_name: BindingDeclaration,
    pub(super) layout: AggregateLayout,
    pub(super) length: u32,
    pub(super) initializers: Vec<AggregateInitializer>,
    pub(super) constant: bool,
}

/// Static-storage metadata shared by all copies of a function descriptor.
/// Keeping the collections behind the existing static-storage pointer avoids
/// increasing the size of the recursive `Proposition` enum's
/// function-execution variants.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) struct FunctionStaticStorage {
    pub(super) static_arrays: Vec<StaticArray>,
    pub(super) global_aggregates: Vec<GlobalAggregate>,
    pub(super) global_aggregate_arrays: Vec<GlobalAggregateArray>,
    pub(super) static_aggregates: Vec<StaticAggregate>,
    pub(super) static_aggregate_arrays: Vec<StaticAggregateArray>,
}

/// A function's embedded C string constant. The bytes include the trailing
/// NUL and are installed in a stable read-only memory block at function entry.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct StringLiteral {
    pub(super) identity: StringLiteralId,
    pub(super) bytes: Vec<u8>,
    /// The character type of the literal's elements: `UInt8` where plain
    /// `char` is unsigned and `Int8` where it is signed. Each byte is stored
    /// as a cell of this type, holding the byte's value under it.
    pub(super) element_type: ProgramType,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct AggregateField {
    pub(super) name: String,
    /// A number, or in a symbolic layout the field's `offsetof` term.
    pub(super) offset: LayoutOffset,
    pub(super) program_type: ProgramType,
    /// The source dimensions of an array field with more than one, outermost
    /// first. `program_type` holds such a field as one flat array; nothing reasons
    /// from the shape, which only lets a proof term about an element be
    /// spelled with the subscripts the source declares.
    pub(super) array_shape: Option<Vec<u32>>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct AggregateUnionField {
    pub(super) name: String,
    pub(super) offset_bytes: u32,
    pub(super) program_type: ProgramType,
}

impl AggregateUnionField {
    pub fn new(name: impl Into<String>, offset_bytes: u32, program_type: ProgramType) -> Self {
        Self {
            name: name.into(),
            offset_bytes,
            program_type,
        }
    }

    /// The member's offset, a number: unions have concrete layouts.
    pub fn offset(&self) -> LayoutOffset {
        LayoutOffset::Bytes(self.offset_bytes)
    }

    pub fn offset_bytes(&self) -> u32 {
        self.offset_bytes
    }

    pub fn program_type(&self) -> ProgramType {
        self.program_type
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct AggregateUnion {
    pub(super) name: String,
    pub(super) offset_bytes: u32,
    pub(super) size_bytes: u32,
    pub(super) fields: Vec<AggregateUnionField>,
}

impl AggregateUnion {
    pub fn new(
        name: impl Into<String>,
        offset_bytes: u32,
        size_bytes: u32,
        fields: Vec<AggregateUnionField>,
    ) -> Self {
        Self {
            name: name.into(),
            offset_bytes,
            size_bytes,
            fields,
        }
    }

    pub fn offset_bytes(&self) -> u32 {
        self.offset_bytes
    }

    pub fn size_bytes(&self) -> u32 {
        self.size_bytes
    }

    pub fn fields(&self) -> &[AggregateUnionField] {
        &self.fields
    }
}

impl AggregateField {
    pub fn new(
        name: impl Into<String>,
        offset: impl Into<LayoutOffset>,
        program_type: ProgramType,
    ) -> Self {
        Self {
            name: name.into(),
            offset: offset.into(),
            program_type,
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

    /// The field's byte offset in a concrete layout. A symbolic layout's
    /// field has [`Self::offset`] only.
    pub fn offset_bytes(&self) -> u32 {
        self.offset.concrete()
    }

    pub fn offset(&self) -> LayoutOffset {
        self.offset
    }

    pub fn program_type(&self) -> ProgramType {
        self.program_type
    }
}

/// One explicitly initialized scalar cell in a static-storage aggregate.
/// The aggregate materializer zero-fills the complete layout first, then
/// applies these entries at their ABI-relative offsets.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct AggregateInitializer {
    pub(super) offset_bytes: u32,
    pub(super) value: ProgramValue,
}

impl AggregateInitializer {
    pub fn new(offset_bytes: u32, value: ProgramValue) -> Self {
        Self {
            offset_bytes,
            value,
        }
    }

    pub fn offset_bytes(&self) -> u32 {
        self.offset_bytes
    }

    pub fn value(&self) -> &ProgramValue {
        &self.value
    }
}

/// Sorted record-relative offsets and masks of the bytes occupied by named
/// C bit-fields. A padding-only byte has no entry.
pub(crate) type BitFieldBytes = Arc<[(u32, std::num::NonZeroU8)]>;

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct AggregateLayout {
    /// The declared bits copied by an assignment of a local C bit-field
    /// record. Padding is outside the assigned value.
    pub(super) bit_field_bytes: Option<BitFieldBytes>,
    /// A number, or a symbolic layout's `sizeof` term.
    pub(super) size: LayoutSize,
    pub(super) alignment_bytes: u32,
    pub(super) fields: Vec<AggregateField>,
    pub(super) unions: Vec<AggregateUnion>,
    /// The one value the object holds, for a local that keeps a value of a
    /// type with no fields in memory: a borrowed Rust enum local. The
    /// local's name reads that value.
    pub(super) value_type: Option<ProgramType>,
}

impl AggregateLayout {
    pub fn new(
        size: impl Into<LayoutSize>,
        alignment_bytes: u32,
        fields: Vec<AggregateField>,
    ) -> Self {
        assert!(alignment_bytes.is_power_of_two());
        Self {
            size: size.into(),
            alignment_bytes,
            fields,
            unions: Vec::new(),
            value_type: None,
            bit_field_bytes: None,
        }
    }

    pub(crate) fn with_bit_field_bytes(mut self, field_bytes: Option<BitFieldBytes>) -> Self {
        self.bit_field_bytes = field_bytes;
        self
    }

    /// The layout of an object that holds one value of `value_type`, a type
    /// with no fields such as a Rust enum's: its size and alignment are the
    /// value's width.
    pub fn holding_value(value_type: ProgramType) -> Self {
        let width = value_type.byte_width();
        Self {
            value_type: Some(value_type),
            ..Self::new(width, width, Vec::new())
        }
    }

    /// The type of the one value the object holds, when it holds one.
    pub fn value_type(&self) -> Option<ProgramType> {
        self.value_type
    }

    pub fn with_unions(
        size: impl Into<LayoutSize>,
        alignment_bytes: u32,
        fields: Vec<AggregateField>,
        unions: Vec<AggregateUnion>,
    ) -> Self {
        assert!(alignment_bytes.is_power_of_two());
        Self {
            size: size.into(),
            alignment_bytes,
            fields,
            unions,
            value_type: None,
            bit_field_bytes: None,
        }
    }

    /// The size of a concrete layout. A symbolic layout has [`Self::size`]
    /// only.
    pub fn size_bytes(&self) -> u32 {
        self.size.concrete()
    }

    pub fn size(&self) -> LayoutSize {
        self.size
    }

    pub fn alignment_bytes(&self) -> u32 {
        self.alignment_bytes
    }

    pub fn fields(&self) -> &[AggregateField] {
        &self.fields
    }

    pub fn unions(&self) -> &[AggregateUnion] {
        &self.unions
    }
}

/// The body-independent interface shared by every way Click can apply a
/// function contract.
///
/// A [`ProgramFunction`] keeps the implementation body and storage alongside this
/// value, but all typed call parameters/result metadata, proof binders,
/// logical clauses, normalized resource terms, effect information, and source
/// origins live here.  Keeping this carrier separate from the body is
/// important for opaque calls: applying a checked summary must not implicitly
/// execute (or even inspect) the concrete body.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct FunctionContractInterface {
    pub(crate) object_type_requirements: ObjectTypeRequirements,
    pub(crate) return_object_type_guarantee: Option<crate::kernel::effective_type::CAccessClass>,
    pub(crate) return_type: ProgramType,
    pub(crate) return_pointee_constant: bool,
    /// The class of the object a returned pointer designates, from the
    /// declared return type (`design/effective-types.md`).
    pub(crate) return_pointee_class: Option<crate::kernel::effective_type::CAccessClass>,
    pub(crate) return_aggregate_layout: Option<AggregateLayout>,
    /// The contract states `allocates(result, n)`: a call's result is a
    /// fresh heap block, distinct from every block that existed before.
    pub(crate) fresh_result_allocation: bool,
    pub(crate) aggregate_return_mode: AggregateReturnMode,
    pub(crate) construction_parameter: Option<(usize, AggregateLayout)>,
    pub(crate) exceptional_signature: ExceptionalSignature,
    pub(crate) parameters: Vec<ProgramParameter>,
    /// Explicit resource-instance binders introduced by a named contract.
    /// These are part of the application interface, not a body assumption.
    pub(crate) proof_parameters: std::sync::Arc<[ResourceSpec]>,
    /// A named contract's value parameters, `let amount: int32;`. A fact
    /// attaching the contract to a function value fixes them; a call binds
    /// them beside the call's arguments. They are not part of the function
    /// type the contract applies to.
    pub(crate) value_parameters: Vec<ProgramParameter>,
    pub(crate) resource_requires: Vec<ResourceSpec>,
    pub(crate) resource_ensures: Vec<ResourceSpec>,
    pub(super) resource_transfer_rule: Arc<super::functions::SummaryResourceTransferRule>,
    pub(crate) resource_constructors: Vec<ResourceSpec>,
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
    pub(crate) contract_mutable: Vec<MemorySegment>,
    /// mixtures with startup or explicit effect segments.
    pub(crate) contract_effect_claim_required: bool,
    pub(crate) resource_derived_mutable_frame: bool,
    pub(crate) resource_derived_frame_mixed: bool,
    pub(crate) contract_claims: Vec<FunctionContractClaim>,
    pub(crate) opaque_contract_supported: bool,
    pub(crate) composite_resource_definitions: Arc<[CompositeResourceDefinition]>,
    /// Shape summary built with the registered definitions. Substitution
    /// changes operands without changing guard presence or recursion.
    pub(crate) composite_definitions_need_entry_cases: bool,
    /// Sorted names of the abstract families that are not `authorized`.
    /// Abstract families have no definition here, so only a name on this list
    /// is known to take no part in population accounting.
    pub(crate) ordinary_abstract_families: Vec<String>,
    /// Contract-local definitions for opaque Click predicate requirements.
    /// Both sides are instantiated at the exact function entry state.
    pub(crate) predicate_unfoldings: Vec<PredicateUnfolding>,
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
    pub(crate) recursion_measure: Vec<RankingComponent>,
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
    pub(crate) recursion_resource: Option<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ProgramFunction {
    pub(super) program_entry: bool,
    pub(super) name: String,
    /// Header-provided `static inline` or `static __always_inline` functions
    /// have a checked body but no
    /// Click contract. Calls to them execute that body at the call site
    /// instead of requiring an opaque verified-function rule.
    pub(super) inline_body: bool,
    pub(super) body: ProgramStatement,
    pub(super) source_body: ProgramStatement,
    pub(super) control_targets: std::sync::Arc<BTreeMap<ControlTargetId, ControlTarget>>,
    /// Shared: every claim and theorem a proof issues carries the function,
    /// and the contract spans every parameter.
    pub(super) contract_interface: Arc<FunctionContractInterface>,
    pub(super) global_variables: Vec<Global>,
    pub(super) global_arrays: Vec<GlobalArray>,
    pub(super) static_variables: Vec<StaticLocal>,
    pub(super) static_storage: std::sync::Arc<FunctionStaticStorage>,
    pub(super) string_literals: Vec<StringLiteral>,
    pub(super) address_taken_locals: AddressTakenLocals,
    pub(super) loop_source_index: LoopSourceIndexCache,
    pub(super) callee_static_storage: CalleeStaticStorage,
    /// A frontend-identified whole-body cycle. Its source identity exists
    /// before a frontier clause adds the executable proof wrapper.
    pub(super) natural_loop_source: Option<(ControlTargetId, Option<ControlTargetId>)>,
}

/// The locals whose address a function's body takes, found once per body
/// rather than by walking the body at every call or path that binds the
/// function's arguments. It is derived from `body`, so equality, hashing and
/// ordering ignore it.
#[derive(Clone, Debug, Default)]
pub(super) struct AddressTakenLocals(Arc<std::sync::OnceLock<BTreeSet<BindingName>>>);

/// The static storage of the functions a function's body calls directly
/// that its own storage does not declare, each as a storage-only function
/// ([`ProgramFunction::static_storage_only`]). The function's entry installs
/// its memory with the function's own storage, so a call finds its callee's
/// storage in place. The frontend derives it from the body and the program,
/// so equality, hashing and ordering ignore it.
#[derive(Clone, Debug, Default)]
pub(super) struct CalleeStaticStorage(pub(super) Arc<[ProgramFunction]>);
impl PartialEq for CalleeStaticStorage {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl Eq for CalleeStaticStorage {}
impl std::hash::Hash for CalleeStaticStorage {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}
impl PartialOrd for CalleeStaticStorage {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for CalleeStaticStorage {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

/// Derived source-loop shapes and eligibility data, shared by function clones.
#[derive(Clone, Debug, Default)]
pub(super) struct LoopSourceIndexCache(
    pub(super) Arc<std::sync::OnceLock<crate::kernel::termination::loop_evidence::LoopSourceIndex>>,
);
impl PartialEq for LoopSourceIndexCache {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl Eq for LoopSourceIndexCache {}
impl std::hash::Hash for LoopSourceIndexCache {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}
impl PartialOrd for LoopSourceIndexCache {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for LoopSourceIndexCache {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

impl PartialEq for AddressTakenLocals {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl Eq for AddressTakenLocals {}
impl std::hash::Hash for AddressTakenLocals {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}
impl PartialOrd for AddressTakenLocals {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for AddressTakenLocals {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

impl ProgramFunction {
    /// The locals whose address the body takes.
    pub(crate) fn address_taken_locals(&self) -> &BTreeSet<BindingName> {
        self.address_taken_locals.0.get_or_init(|| {
            let mut names = BTreeSet::new();
            crate::kernel::loops::collect_address_taken_locals(&self.body, &mut names);
            names
        })
    }
}

/// Source origin is planning metadata, not part of a function's checked
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

// Declaration origin is retained through instantiation but does not alter
// a definition's semantic identity, just like ContractRequirementSources.
#[derive(Clone, Debug, Default)]
pub(super) struct PredicateRequirementSource(Option<usize>);
impl PartialEq for PredicateRequirementSource {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl Eq for PredicateRequirementSource {}
impl std::hash::Hash for PredicateRequirementSource {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}
impl PartialOrd for PredicateRequirementSource {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for PredicateRequirementSource {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct PredicateUnfolding {
    pub(super) predicate: SpecProposition,
    pub(super) body: SpecProposition,
    pub(super) requirement_source: PredicateRequirementSource,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CompositeResourceDefinition {
    /// Typed resource-reference parameters. These describe arguments, not
    /// owned ingredients; custody requires an explicit body clause.
    pub(super) resource_parameters: Vec<ResourceSpec>,
    pub(super) instance_schema: Option<ResourceFieldSchema>,
    pub(super) matched: Option<ResourceMatchBody>,
    pub(super) name: String,
    pub(super) parameters: Vec<ProgramParameter>,
    /// Existential witnesses bound inside the body (`let next: T where P`).
    /// Each is bound like a parameter when the body is instantiated: to the
    /// recorded origin of the word its `where` fact relates it to, or to a
    /// fresh symbolic pointer when no origin is recorded yet.
    pub(super) witnesses: Vec<ProgramParameter>,
    pub(super) condition: Option<SpecProposition>,
    pub(super) recursive: bool,
    /// A same-family child declared inside a matched arm rather than in the
    /// unmatched memory body. `recursive` describes that body, which instance
    /// fold/unfold rewrites; [`CompositeResourceDefinition::is_recursive`]
    /// answers for the definition as a whole.
    pub(super) matched_recursive: bool,
    /// Whether a body fact reads a population count. Such a fact can change
    /// while the head is lent, so a stable borrow cannot carry it.
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
    /// (`loadable(...)`, directly or through a predicate). A borrow of the
    /// composite stabilizes its memory and tokens, not the liveness of
    /// storage the fact names, so such facts are not restored by recovery.
    pub(super) facts_claim_liveness: bool,
    pub(super) contains: Vec<ResourceSpec>,
    /// Named child instances of the unmatched body. A matched definition
    /// keeps its children in its arms instead. Each is of another family: an
    /// unmatched body has no submodel to descend to.
    pub(super) children: Vec<ResourceChildSpec>,
    pub(super) facts: Vec<SpecProposition>,
    /// Compiled fact index to original resource-body fact index. Predicate
    /// unfolding can produce two compiled facts for one source fact.
    pub(super) fact_source_indices: Vec<usize>,
    /// Source spellings are diagnostic metadata. They never justify a fact.
    pub(super) fact_source_spellings: Vec<String>,
    /// A field-bearing abstract family: its instances carry fields, but its
    /// body is empty and no proof step folds, unfolds, or observes one. Only
    /// a trusted contract produces or consumes an instance.
    pub(super) sealed: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ResourceMatchBody {
    pub field_index: usize,
    pub algebraic_type: AlgebraicType,
    pub arms: Vec<ResourceMatchArm>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ResourceMatchArm {
    pub variant: String,
    pub bindings: Vec<String>,
    pub binding_types: Vec<AlgebraicValueType>,
    /// Kernel identities for mathematical Integer constructor bindings.
    /// C and algebraic bindings carry `None`; the identities are fresh
    /// lowering atoms that the selected constructor fields replace after the
    /// kernel has checked the arm schema.
    pub binding_variables: Vec<Option<Variable>>,
    pub contains: Vec<ResourceSpec>,
    pub facts: Vec<SpecProposition>,
    pub children: Vec<ResourceChildSpec>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ResourceChildSpec {
    pub name: String,
    /// The child's own composite resource definition. It may be the parent's
    /// definition or another declared resource; the rewrite resolves it and
    /// checks the child's arguments and fields against that definition.
    pub resource: String,
    pub binding: InstanceId,
    pub arguments: Vec<SpecExpression>,
    /// Where each of the child's fields comes from, in the child schema's
    /// order. A same-family child's matched model field must be a proper
    /// submodel: an immediate constructor binding of the same algebraic type.
    pub field_bindings: Vec<ResourceChildField>,
}

/// The source of one field of a child instance a resource body declares.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ResourceChildField {
    /// The selected constructor's binding at this index.
    Constructor(usize),
    /// The parent instance's own field at this index. The child's field then
    /// equals the parent's, as a scalar model value does; it never makes a
    /// same-family child a submodel.
    Parent(usize),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum FunctionContractClaimKey {
    BodySafety,
    Effect(usize),
    Ensure(usize),
    ExceptionalEnsure(usize),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct FunctionContractClaim {
    pub(super) key: FunctionContractClaimKey,
    pub(super) target: FunctionContractClaimTarget,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum FunctionContractClaimTarget {
    BodySafety,
    Effect,
    EnsureProposition(usize),
    EnsureResource(usize),
    ExceptionalEnsureProposition(usize),
}

/// The contract return value is independent of every program/proof identifier.
pub(crate) const CONTRACT_RESULT: BindingName = BindingName::ContractResult;

/// Preserve typed identities when raising a program binding to Surface.
pub(crate) fn program_local_source_name(name: impl Into<BindingName>) -> BindingName {
    name.into()
}

/// The thrown payload is independent of every program/proof identifier.
pub(crate) const CONTRACT_EXCEPTION: BindingName = BindingName::ContractException;

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct FunctionSpecification {
    pub(super) state: ExecutionState,
    /// Shared: every theorem a proof issues carries the specification, and
    /// both lists span every parameter.
    pub(super) arguments: Arc<[ProgramExpression]>,
    pub(super) requires: Arc<[Proposition]>,
    pub(super) outcome: FunctionOutcome,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum CallBinderTarget {
    Function(Arc<str>),
    ReferenceBinding(ReferenceBindingContract),
}

impl std::fmt::Display for CallBinderTarget {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Function(name) => f.write_str(name),
            Self::ReferenceBinding(binding) => binding.fmt(f),
        }
    }
}

/// One checked binder transport selected at a call or reference binding.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallBinderTransport {
    pub(crate) target: CallBinderTarget,
    /// How many arguments the step wrote, checked against the call it selects.
    pub(crate) arity: usize,
    /// Every instance binder of that callee, mapped to the caller instance
    /// that supplies it. A `produces` binder maps to the fresh identity the
    /// caller's `let` introduced.
    pub(crate) bindings: std::sync::Arc<ResourceBindings>,
    /// Runtime binders that name a resource type, evaluated at the call.
    pub(crate) type_arguments: std::sync::Arc<BTreeMap<Variable, super::ResourceDescription>>,
}

impl CallBinderTransport {
    /// The surface has already resolved the written callee against the
    /// call at the frontier. Transport is valid only for that exact target.
    pub(crate) fn names_call_to(&self, function_name: &str) -> bool {
        matches!(&self.target, CallBinderTarget::Function(name)
            if function_name == name.as_ref())
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

/// An environment's verified loop rules, in the order they were added, with
/// the indexes stepping a loop reads: the rules filed under a fingerprint
/// of their loop statement, so finding the rule for a loop compares only
/// rules for that statement, and the reservation of every rule's variables
/// behind one execution bound (`LazyReservedVariables`). All of it is
/// persistent: an environment that gains a rule shares every earlier rule
/// and index entry with the one it was built from.
#[derive(Clone, Default)]
pub(super) struct VerifiedLoopRules {
    /// Behind an `Arc` so a copy of an environment shares this storage by
    /// identity even while the vector is small enough to be held inline.
    rules: Arc<imbl::Vector<Arc<VerifiedLoopRule>>>,
    by_statement: imbl::OrdMap<u64, imbl::Vector<usize>>,
    execution_bound: Option<Variable>,
    reservation: Arc<OnceLock<LazyReservedVariables>>,
}

impl PartialEq for VerifiedLoopRules {
    fn eq(&self, other: &Self) -> bool {
        self.rules == other.rules
    }
}

impl Eq for VerifiedLoopRules {}

impl std::fmt::Debug for VerifiedLoopRules {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.debug_list().entries(self.rules.iter()).finish()
    }
}

impl VerifiedLoopRules {
    fn statement_key(statement: &ProgramStatement) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        statement.hash(&mut hasher);
        hasher.finish()
    }

    pub(super) fn push(&mut self, rule: VerifiedLoopRule) {
        let bound =
            crate::kernel::reasoning::variable_collection::verified_loop_rule_execution_bound(
                &rule,
            );
        self.execution_bound = self.execution_bound.max(bound);
        self.by_statement
            .entry(Self::statement_key(&rule.loop_statement))
            .or_default()
            .push_back(self.rules.len());
        Arc::make_mut(&mut self.rules).push_back(Arc::new(rule));
        self.reservation = Arc::new(OnceLock::new());
    }

    pub(super) fn iter(&self) -> impl Iterator<Item = &VerifiedLoopRule> {
        self.rules.iter().map(Arc::as_ref)
    }

    /// The rules for `statement`, in order: every rule whose loop statement
    /// is `statement` is among them.
    pub(super) fn for_statement(
        &self,
        statement: &ProgramStatement,
    ) -> impl Iterator<Item = &VerifiedLoopRule> {
        self.by_statement
            .get(&Self::statement_key(statement))
            .into_iter()
            .flat_map(|positions| positions.iter())
            .map(|position| self.rules[*position].as_ref())
    }

    /// Every rule's reserved variables, collected only when a query the
    /// rules' common execution bound cannot answer needs them.
    pub(super) fn reserved_variables(&self) -> Option<LazyReservedVariables> {
        if self.rules.is_empty() {
            return None;
        }
        Some(
            self.reservation
                .get_or_init(|| {
                    let rules = self.rules.clone();
                    LazyReservedVariables::new(self.execution_bound, move || {
                        let mut variables = BTreeSet::new();
                        for rule in rules.iter() {
                            variables.extend(
                                crate::kernel::reasoning::variable_collection::verified_loop_rule_variables(
                                    rule,
                                )
                                .iter()
                                .copied(),
                            );
                        }
                        Arc::new(variables)
                    })
                })
                .clone(),
        )
    }

    #[cfg(test)]
    pub(super) fn shares_storage_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.rules, &other.rules)
    }
}

#[derive(Clone, Default)]
pub struct ExecutionEnvironment {
    // A proof-local rule choice. This is not installed in the project environment.
    pub(crate) selected_call_contract: Option<std::sync::Arc<str>>,
    pub(crate) selected_call_resource_arguments: Option<std::sync::Arc<[InstanceId]>>,
    /// A proof-local binder map for one ordinary C call: the callee named by
    /// the step, and one caller instance per instance binder the callee
    /// declares. Binding is a lookup per entry; nothing is searched for.
    pub(crate) selected_call_binders: Option<std::sync::Arc<CallBinderTransport>>,
    /// A proof-local choice of values for one ordinary C call's contract
    /// value parameters: the callee, and the values the proof's call map
    /// gives, each with the parameter it names. A parameter the map leaves
    /// out is taken from the one held instance its clause selects.
    pub(crate) selected_call_value_arguments:
        Option<std::sync::Arc<(String, Vec<(String, ProgramValue)>)>>,
    pub(super) functions: std::sync::Arc<BTreeMap<String, ProgramFunction>>,
    pub(super) function_contracts: std::sync::Arc<BTreeMap<String, FunctionContract>>,
    pub(super) reference_binding_rules:
        Arc<BTreeMap<ReferenceBindingContract, ExternalFunctionRule>>,
    pub(super) cpp_virtual_rules: std::sync::Arc<BTreeMap<String, ExternalFunctionRule>>,
    pub(super) external_function_rules: std::sync::Arc<BTreeMap<String, ExternalFunctionRule>>,
    pub(super) verified_function_rules: std::sync::Arc<BTreeMap<String, VerifiedFunctionRule>>,
    pub(super) verified_function_termination_rules:
        std::sync::Arc<BTreeMap<String, VerifiedFunctionTerminationRule>>,
    /// Installed only after the surface checks the exact built-in header and
    /// selected runtime. A pthread call must use its checked transition; an
    /// ordinary external function contract is never a substitute.
    pub(super) modeled_pthread_binding:
        Option<crate::languages::c::thread_runtime::ModeledPthreadBinding>,
    /// Resource-definition metadata for selected modeled mutex calls. Named
    /// lookup avoids scanning unrelated project definitions at each call.
    pub(super) modeled_mutex_definitions:
        std::sync::Arc<BTreeMap<String, CompositeResourceDefinition>>,
    /// The same definitions as one name-sorted slice, for deriving the
    /// footprint of a protected resource whose body reaches other families.
    pub(super) modeled_mutex_definition_list: std::sync::Arc<[CompositeResourceDefinition]>,
    /// The selected target's byte order. It decides whether a one-byte C
    /// access inside a wider integer cell reads or updates that cell's
    /// representation; see `crate::kernel::eval::byte_view`.
    pub(super) byte_order: ByteOrder,
    pub(super) verified_loop_rules: VerifiedLoopRules,
    /// The function currently being certified, when it declares an expression
    /// `decreases` measure. It is part of this environment's identity below,
    /// so a checked execution recorded without it is not reused to certify a
    /// contract whose function declares one: an artifact stepped with no
    /// anchor emitted no descent obligation, and certification must not take
    /// it for one that did.
    pub(super) recursion_anchor: Option<std::sync::Arc<RecursionAnchor>>,
    /// Exact contract certification may split an undecided conditional
    /// resource effect at a verified call boundary. Ordinary proof execution
    /// leaves this off, so an undecided guard remains an actionable call
    /// failure there.
    pub(super) allow_conditional_resource_cases: bool,
    pub(super) variable_index: ExecutionEnvironmentVariableIndex,
}

impl std::fmt::Debug for ExecutionEnvironment {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ExecutionEnvironment")
            .field("selected_call_contract", &self.selected_call_contract)
            .field(
                "selected_call_resource_arguments",
                &self.selected_call_resource_arguments,
            )
            .field("selected_call_binders", &self.selected_call_binders)
            .field(
                "selected_call_value_arguments",
                &self.selected_call_value_arguments,
            )
            .field("functions", &self.functions)
            .field("function_contracts", &self.function_contracts)
            .field("reference_binding_rules", &self.reference_binding_rules)
            .field("cpp_virtual_rules", &self.cpp_virtual_rules)
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

impl PartialEq for ExecutionEnvironment {
    fn eq(&self, other: &Self) -> bool {
        self.selected_call_contract == other.selected_call_contract
            && self.selected_call_resource_arguments == other.selected_call_resource_arguments
            && self.selected_call_binders == other.selected_call_binders
            && self.selected_call_value_arguments == other.selected_call_value_arguments
            && self.functions == other.functions
            && self.function_contracts == other.function_contracts
            && self.reference_binding_rules == other.reference_binding_rules
            && self.cpp_virtual_rules == other.cpp_virtual_rules
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

impl Eq for ExecutionEnvironment {}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LoopSemantics {
    Verify,
    ApplyVerifiedRules,
}

/// How an execution treats loops. Calls have one semantics: a callee with a
/// verified rule is applied through it, and only a contract-less inline
/// helper runs its body, at the call site.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ExecutionSemantics {
    pub loops: LoopSemantics,
}

impl ExecutionSemantics {
    pub const APPLY_VERIFIED_RULES: Self = Self {
        loops: LoopSemantics::ApplyVerifiedRules,
    };

    pub const APPLY_CALL_RULES_AND_VERIFY_LOOPS: Self = Self {
        loops: LoopSemantics::Verify,
    };
}

/// The environment a C execution runs in and the semantics it runs under,
/// which kernel execution threads through every statement and call
/// together.
#[derive(Clone, Copy)]
pub(crate) struct ExecutionContext<'a> {
    pub(crate) environment: &'a ExecutionEnvironment,
    pub(crate) semantics: ExecutionSemantics,
}

impl<'a> ExecutionContext<'a> {
    pub(crate) fn new(
        environment: &'a ExecutionEnvironment,
        semantics: ExecutionSemantics,
    ) -> Self {
        Self {
            environment,
            semantics,
        }
    }

    /// Applies verified call rules and verifies loops directly.
    #[cfg(test)]
    pub(crate) fn verify_loops(environment: &'a ExecutionEnvironment) -> Self {
        Self::new(
            environment,
            ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        )
    }

    /// Applies verified call and loop rules.
    pub(crate) fn apply_verified_rules(environment: &'a ExecutionEnvironment) -> Self {
        Self::new(environment, ExecutionSemantics::APPLY_VERIFIED_RULES)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedFunctionRule {
    /// Producer-owned concrete/avoided loop coverage. Independent legacy
    /// inputs have no ordinary body owner and use their separate adapter.
    pub(super) descent_completion:
        Option<Arc<crate::kernel::termination::descent_completion::DescentCompletion>>,
    pub(super) concrete_loop_exits:
        Option<Arc<crate::kernel::termination::loop_evidence::ConcreteLoopExits>>,
    /// Only the positive object-type premises consumed by the checked proof.
    /// Checked result origins, instantiated with the caller's actual types.
    pub(super) pointer_result: Option<Arc<PurePointerResult>>,

    pub(super) function: ProgramFunction,
    /// Compatibility mode for independent execution/certification APIs.
    /// Ordinary body proofs publish concrete loop coverage separately;
    /// this mode alone is not source-bound exit evidence.
    pub(super) loop_semantics: LoopSemantics,
    /// The user-defined tactics this rule's certified proofs applied, by
    /// name. A tactic's procedure runs no code, so its body has no calls;
    /// these applications are its call edges, written by the kernel from the
    /// checked traces, so the termination check may trust them.
    pub(super) applied_tactics: std::collections::BTreeSet<String>,
    /// Complete conservative call dependencies from kernel-checked execution.
    /// None retains source-call analysis; a present empty set proves no calls.
    /// Shared across claims and certificate reuse, never copied per step.
    pub(super) checked_callees: Option<Arc<BTreeSet<crate::kernel::termination::CallDependency>>>,
}

impl VerifiedFunctionRule {}

/// A nominal, body-independent behavioral interface for an indirect call.
///
/// Named contracts retain only their nominal name and this checked interface.
/// A source function may be used to build the interface, but its body, globals,
/// and static storage are not part of a callback contract and are discarded at
/// construction. This keeps indirect application independent of an arbitrary
/// source/template representation.
#[derive(Clone, Debug)]
pub struct FunctionContract {
    pub(super) closure: bool,
    pub(super) name: String,
    /// Source-name origin retained only for diagnostics. It is not part
    /// of the contract identity and cannot alter callback behavior.
    pub(super) callee_name: String,
    pub(super) interface: FunctionContractInterface,
    /// The values a fact fixed for the interface's value parameters, when
    /// this contract was found through one; empty for the declaration.
    pub(super) value_arguments: Vec<ProgramValue>,
}

impl PartialEq for FunctionContract {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && self.interface == other.interface
            && self.value_arguments == other.value_arguments
    }
}

impl Eq for FunctionContract {}

impl std::hash::Hash for FunctionContract {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.interface.hash(state);
        self.value_arguments.hash(state);
    }
}

impl PartialOrd for FunctionContract {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for FunctionContract {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.name
            .cmp(&other.name)
            .then_with(|| self.interface.cmp(&other.interface))
            .then_with(|| self.value_arguments.cmp(&other.value_arguments))
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

/// An exact byte span of a checked representation copy whose source may
/// contain unwritten bytes.
pub(super) struct RepresentationCopyRange {
    pub(super) destination: Address,
    pub(super) source: Address,
    pub(super) bytes: u32,
}

/// A contract supplied for a C function whose implementation is outside the
/// verified source set. External rules are intentionally distinct from
/// [`VerifiedFunctionRule`]: they are knowns accepted at call sites,
/// not evidence that Click checked a function body.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExternalFunctionRule {
    pub(super) function: ProgramFunction,
    /// This assumption names a concrete, well-formed function whose proof is
    /// outside the current partial-verification selection. It never escapes
    /// that selection's environment.
    pub(super) scoped_unselected: bool,
    /// Set only for a recognized byte-copy declaration whose checked effect
    /// the kernel applies after the external contract.
    pub(super) representation_copy: Option<RepresentationCopyEffect>,
}

impl ExternalFunctionRule {
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
/// Construction is deliberately separate from [`VerifiedFunctionRule`], so
/// ordinary opaque calls never acquire a total-correctness assumption.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedFunctionTerminationRule {
    pub(super) function: ProgramFunction,
}

/// An untrusted surface-language proposal for ranking the cycles in one C
/// function. The kernel checks every supplied index and expression against the
/// exact body before producing termination evidence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionTerminationPlan {
    pub(super) function_name: String,
    pub(super) recursive_measure: Option<FunctionTerminationMeasure>,
    pub(super) loop_measures: BTreeMap<usize, LoopTerminationMeasure>,
}

/// One loop's declared `decreases` measure (D6).
///
/// The clause is one expression at the surface; what it names decides which
/// of these the loop carries, and the loop head carries the same choice, so
/// the back-edge check and this plan cannot describe different measures.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LoopTerminationMeasure {
    /// Scalar int32 components, in source order, ranked lexicographically by
    /// the back-edge invariant bundle.
    Ranking(Vec<RankingMeasureKey>),
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
pub enum RankingComponent {
    /// Today's measure: a scalar int32 C expression over locals and reads.
    ProgramExpression(ProgramExpression),
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

impl RankingComponent {
    /// How the whole-function termination plan names this component.
    pub(super) fn key(&self) -> RankingMeasureKey {
        match self {
            Self::ProgramExpression(expression) => {
                RankingMeasureKey::ProgramExpression(expression.clone())
            }
            Self::Pure { source, .. } | Self::PureInteger { source, .. } => {
                RankingMeasureKey::Pure(source.clone())
            }
        }
    }
}

/// The value of one `decreases` component at one state, in the carrier its
/// declaration chose.
///
/// The carrier is a function of the component, not of the state: a
/// [`RankingComponent::PureInteger`] reads as an `Integer` at every state and
/// the other two read as the machine type C's usual arithmetic conversions
/// give the expression -- int32, uint32, or uint64 -- which is a function of
/// the declared types it names, so it is the same at every state. A reading
/// whose carrier differs from the other reading's is refused rather than
/// coerced. That is what lets the
/// two obligations be built from the two readings of one component without
/// asking which carrier each reading happened to land in.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RankingMeasureValue {
    /// A machine int32 quantity, ranked by signed comparison.
    Machine(OldMachineTerm),
    /// A machine uint32 quantity, ranked by unsigned comparison of the value
    /// C computes, wraparound included. Every such value is a natural number
    /// below 2^32, so it is nonnegative by construction.
    Unsigned32(OldMachineTerm),
    /// A machine uint64 quantity, ranked by unsigned 64-bit comparison of the
    /// value C computes, wraparound included; nonnegative by construction.
    Unsigned64(OldMachineTerm),
    /// A machine int64 quantity, ranked by signed 64-bit comparison. Like an
    /// int32 it owes `0 <= m`.
    Signed64(OldMachineTerm),
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
/// equality `ProgramExpression` gets: two different lowered expressions declared
/// with the same spelling compare equal here. That is deliberate, and it does
/// not widen what can be proved, because this comparison is not the
/// termination evidence.
///
/// The evidence is the certified loop's own back-edge invariant bundle. That
/// bundle carries one `0 <= m` member and one lexicographic `m_post < m_pre`
/// member per declared component, built by the kernel from the
/// `RankingComponent` the rule's loop head carries and evaluated by the
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
pub enum RankingMeasureKey {
    ProgramExpression(ProgramExpression),
    Pure(String),
}

impl FunctionTerminationPlan {
    pub fn extend_loop_measures(
        &mut self,
        measures: impl IntoIterator<Item = (usize, LoopTerminationMeasure)>,
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
/// obligations were emitted. See [`RecursionAnchor`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FunctionTerminationMeasure {
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
/// [`crate::kernel::program_execution_environment_with_recursion_anchor`] reads the
/// measure off the function's own contract interface and evaluates it itself.
///
/// `entry_obligations` are what reading the measure at the entry owes: the
/// loadability of its reads. They travel with the anchor and are emitted at
/// the self-call, where the path context can discharge them, rather than
/// being dropped.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecursionAnchor {
    pub(super) function: String,
    pub(super) components: Vec<RankingComponent>,
    /// The other functions whose calls owe descent against `measure`, read
    /// off the same interface as `components`.
    pub(super) peers: Vec<String>,
    pub(super) measure: Vec<RankingMeasureValue>,
    /// For a structural measure, the instance the measured binder held at
    /// the function's own entry; `components` and `measure` are then empty.
    pub(super) structural_entry: Option<ResourceInstance>,
    pub(super) structural_resource:
        Option<crate::kernel::termination::resource_descent::ResourceDescent>,
    pub(super) entry_obligations: Vec<ProofObligation>,
}

impl RecursionAnchor {
    pub(super) fn function(&self) -> &str {
        &self.function
    }

    pub(super) fn measure(&self) -> &[RankingMeasureValue] {
        &self.measure
    }

    pub(super) fn components(&self) -> &[RankingComponent] {
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
    /// The certified [`ProgramFunction`] is what a judgment has in hand, and its
    /// interface is where the anchor's component was read from, so comparing
    /// both is what binds an anchor to one declared measure of one function.
    pub(super) fn ranks(&self, function: &str, interface: &FunctionContractInterface) -> bool {
        self.function == function
            && interface.recursion_measure().unwrap_or_default() == self.components.as_slice()
            && interface.recursion_binder().is_some() == self.structural_entry.is_some()
            && interface.recursion_resource()
                == self
                    .structural_resource
                    .as_ref()
                    .map(|resource| resource.requirement)
            && self
                .structural_resource
                .as_ref()
                .is_none_or(|resource| resource.matches_declaration(interface))
            && interface.recursion_peers() == self.peers.as_slice()
    }

    pub(super) fn structural_entry(&self) -> Option<&ResourceInstance> {
        self.structural_entry.as_ref()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum TerminationErrorKind {
    InvalidMeasure,
    Internal,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TerminationError {
    pub(super) message: String,
    /// The function whose termination was being decided when the check
    /// failed, for a diagnostic to locate. It is not part of the verdict.
    pub(super) function: Option<String>,
    pub(super) kind: TerminationErrorKind,
}

impl VerifiedFunctionTerminationRule {}

/// Kernel-checked evidence that a checked proof discharged one proposition at
/// one exact function outcome. Contract finalization finds this evidence by
/// the claim it closed and matches it to the path it was completed on.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CheckedFunctionProposition {
    /// Exact checked execution path that produced this completion.
    pub(super) path_origin: Option<Theorem>,
    pub(super) function: ProgramFunction,
    pub(super) specification: FunctionSpecification,
    pub(super) proposition: Proposition,
    /// The contract claim this proposition closed: the proof was opened
    /// from the kernel's goal for that claim, which carries the claim's
    /// identity through to here. `None` for any other proposition.
    pub(super) claim: Option<FunctionContractClaimTarget>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedLoopRule {
    pub(super) symbolic_entry_state: ExecutionState,
    pub(super) loop_statement: ProgramStatement,
    /// Source identity retained by the loop-opening operation.
    pub(super) loop_evidence: Option<crate::kernel::termination::loop_evidence::LoopEvidence>,
    pub(super) required_assumptions: PureFactContext,
    pub(super) paths: Vec<StatementExecutionPath>,
    pub(super) composite_resource_definitions: Vec<CompositeResourceDefinition>,
    /// The recursion anchor the loop's body was stepped under, when the
    /// function this loop belongs to declares an expression `decreases`
    /// measure.
    ///
    /// The kernel writes this from the environment the paths above were
    /// produced in; there is no other way to set it, so it is a record of what
    /// the body actually owed rather than a claim about it. A self-call inside
    /// the body raised its descent obligations exactly when this is `Some`,
    /// and the rule's paths retain any outstanding statement-entry
    /// conditions for application. Applying the rule and the termination
    /// judgment both read it; see
    /// [`ExecutionEnvironment::applicable_verified_loop_rule`].
    pub(super) recursion_anchor: Option<std::sync::Arc<RecursionAnchor>>,
    /// The variables this rule reserves in an environment holding it,
    /// collected the first time one asks and shared by the rule's clones.
    pub(super) variable_index: ExecutionEnvironmentVariableIndex,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum UndefinedBehavior {
    SignedOverflow,
    /// The signed overflow of a division or remainder, which happens
    /// when the minimum value of the format is divided by -1. Kept apart from
    /// [`Self::SignedOverflow`] so the refusal names the pair the facts
    /// leave open instead of a bare `signed overflow`.
    SignedDivisionOverflow(MachineIntegerType),
    PointerArithmetic,
    DivisionByZero,
    FloatToIntegerOutOfRange,
    InvalidShift,
    InvalidMemory,
    UninitializedRead,
    /// An operation on a pointer value whose pointee's lifetime has ended
    /// (C11 6.2.4p2, Annex J.2): comparing, subtracting, offsetting, testing
    /// or converting a pointer into a freed allocation. A refusal names the
    /// operation through `crate::kernel::locate_undefined_behavior`; the
    /// kernel's name for the allocation is not something the reader wrote.
    FreedPointerUse,
    /// An equality comparison whose answer C11 6.5.9p6 leaves to the
    /// implementation's object layout: one operand may be one past the end
    /// of its object and the other the start of a different object, and the
    /// two are equal exactly when the objects are adjacent. The result is
    /// unspecified rather than undefined, and refused because the kernel does
    /// not model object placement. A refusal names the comparison through
    /// `crate::kernel::locate_undefined_behavior`.
    OnePastEndComparison,
    /// A read or write through a pointer outside the subobject it
    /// designates (C11 6.5.6p8, C++ [expr.add]): `*(&pair.first + 1)` is
    /// one past `first`, not `second`, though both name the same address.
    SubobjectAccess {
        /// The access requirement retained at the refusal site, for diagnostics
        /// only. No successful execution constructs this payload.
        required: Box<Proposition>,
    },
    /// A read or write through an lvalue whose type may not access the
    /// object (C11 6.5p7): a `long` read through a `long long *`, or an
    /// `int **` cell read as `long *`. GCC at `-O2` assumes it never happens
    /// (`design/effective-types.md`).
    IncompatibleAccess {
        access: crate::kernel::effective_type::CAccessClass,
        object: crate::kernel::effective_type::CAccessClass,
    },
}

impl UndefinedBehavior {
    /// The requirement lost by a refused access. This is diagnostic evidence,
    /// not a new execution obligation or a license to continue the path.
    pub(crate) fn required_goal(&self) -> Option<&Proposition> {
        match self {
            Self::SubobjectAccess { required } => Some(required),
            _ => None,
        }
    }

    pub fn description(&self) -> String {
        match self {
            Self::SignedOverflow => "signed overflow".to_string(),
            Self::SignedDivisionOverflow(MachineIntegerType::Int32) => {
                "signed overflow (INT_MIN / -1 is the one int32 division or remainder that overflows)"
                    .to_string()
            }
            Self::SignedDivisionOverflow(format) => format!(
                "signed overflow (the minimum signed {}-bit value divided by -1 overflows division and remainder)",
                format.format().bits(),
            ),
            Self::PointerArithmetic => "pointer arithmetic left the pointed-to object".to_string(),
            Self::SubobjectAccess { .. } => {
                "access outside the subobject the pointer designates".to_string()
            }
            Self::DivisionByZero => "division by zero".to_string(),
            Self::FloatToIntegerOutOfRange => {
                "float-to-integer conversion is out of range after truncation or the value is non-finite".to_string()
            }
            Self::InvalidShift => "invalid shift".to_string(),
            Self::InvalidMemory => "invalid memory access".to_string(),
            Self::UninitializedRead => "read of uninitialized storage".to_string(),
            Self::FreedPointerUse => "use of a pointer into a freed allocation: its value is \
                 indeterminate after the free"
                .to_string(),
            Self::OnePastEndComparison => "comparison of a one-past-the-end pointer with the start \
                 of another object: whether the two objects are adjacent is unspecified"
                .to_string(),
            Self::IncompatibleAccess { access, object } => format!(
                "an object of type `{}` accessed through an lvalue of type `{}`: an object may \
                 be accessed only through its own type, up to signedness and qualifiers, or a \
                 character type (C11 6.5p7), and GCC at -O2 assumes nothing else happens",
                object.spelling(),
                access.spelling()
            ),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum InvalidFree {
    InteriorPointer,
    NonHeapPointer,
    DoubleFree,
}

/// How a [`RuntimeError::FunctionContract`] message ends when a function
/// returned a value its declared return type does not admit; the message
/// starts with the function's name.
pub const RETURN_TYPE_MISMATCH: &str = "returned a value that does not match its declared type";

/// The undecided no-wrap condition of a wide range re-spelled in another
/// element width: `range`'s endpoint `count`, multiplied by `factor`, must
/// stay at most `UINT64_MAX` for the two spellings to name the same bytes.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct WideRangeNoWrap {
    pub range: ResourceFact,
    pub count: OldMachineTerm,
    pub factor: u64,
}

/// Source-level evidence for a refused returned borrow. These are the
/// resources the checker already selected, retained only on refusal.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ReturnedBorrowRefusal {
    pub output: ResourceFact,
    pub reason: ReturnedBorrowReason,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ReturnedBorrowReason {
    ExplicitSourceRequired,
    UnevaluableSource,
    InactiveSource,
    UnrecoverableSource(ResourceFact),
    UncoveredView {
        source: ResourceFact,
        viewed: ResourceFact,
    },
    MissingOutput,
    MissingHold(ResourceFact),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum RuntimeError {
    UnboundVariable(String),
    UnknownFunction(String),
    TypeMismatch,
    /// A 64-bit `malloc`, `calloc` or `realloc` size Click cannot use as a
    /// heap block's size: a symbolic `malloc` size the facts do not prove
    /// exact and within `1..=PTRDIFF_MAX` bytes, or a symbolic `calloc` or
    /// `realloc` size (`design/heap-allocation-sizes.md`). Diagnostic only.
    HeapAllocationSize,
    /// A `uint32` heap allocation size, or element count, the facts do not
    /// bound to the checked signed 32-bit allocation size. Diagnostic only.
    HeapAllocationSizeAboveInt32,
    /// A typed memory load whose type does not fit the value the cell
    /// holds: a 4-byte load of an 8-byte cell, or a pointer cell read as an
    /// integer. `stored` is the cell's value when the state knows it.
    LoadTypeMismatch {
        pointer: Address,
        value_type: ProgramType,
        stored: Option<Box<ProgramValue>>,
    },
    /// A pointer/integer cast outside the modeled LP64 conversions: the
    /// message names the rejected direction and what evidence it needed.
    PointerConversion(String),
    /// A Rust enum operation outside the values it is defined on: a field
    /// read of a variant the value is not known to have, or a constructor
    /// whose fields do not fit its variant. The message says which.
    EnumVariant(String),
    /// A thin-pointer operation (arithmetic, ordering, comparison, a cast,
    /// a truth test) given a wide pointer, or a cast that would add or remove
    /// a slice's element count. `operation` names it; the operation reads a
    /// slice's thin part, `s.as_ptr()` (`design/rust-slice-values.md`).
    ThinPointerRequired {
        operation: &'static str,
    },
    /// A slice operation (`s.len()`, `s.as_ptr()`) given an operand that
    /// is not a slice: a thin pointer or a scalar. `operation` names it.
    SliceTypeMismatch {
        operation: &'static str,
    },
    IndeterminatePointeeType,
    UnsupportedPointerSubtractionOffsets,
    UnsupportedPointerComparisonOffsets,
    UnsupportedFunctionPointerOffset,
    WrongArity {
        expected: usize,
        actual: usize,
    },
    MissingReturn,
    MissingResource {
        resource: Box<ResourceFact>,
    },
    /// A required wide memory range is held in another element width, and
    /// the two name the same bytes only when `count * factor` does not wrap,
    /// which the facts do not decide. `range` is the range whose endpoint
    /// `count` is, or becomes, that product. Diagnostic only.
    WideRangeRespellingMayWrap(Box<WideRangeNoWrap>),
    /// An operation requires the current initialization's lifecycle owner.
    MissingMutexLive {
        mutex: Address,
    },
    /// An operation requires a use borrow for this mutex initialization.
    MissingMutexUse {
        mutex: Address,
    },
    /// An operation requires an acquisition that is not available as owned authority.
    MissingMutexGuard {
        mutex: Address,
    },
    /// Unlock requires owned folded authority satisfying its protected assertion.
    /// The diagnostic witness's cached fields do not require historical values.
    MissingMutexInvariant {
        resource: Box<ResourceFact>,
        /// The resource the call map selected instead, when it is owned but
        /// of another protected type.
        supplied: Option<Box<ResourceFact>>,
    },
    /// A stable-view call returned a view that no checked input child,
    /// preserved outer binding, owner projection, or read-only block backs.
    UnbackedReturnedView {
        view: Box<ResourceFact>,
    },
    ReturnedBorrow(Box<ReturnedBorrowRefusal>),
    MissingVerifiedFunctionRule(String),
    UnsupportedOpaqueFunctionContract(String),
    AbstractFunctionPointerCall(String),
    FunctionContract(String),
    /// A resource clause violates a contract rule.
    InvalidContractResource(String),
    /// An argument or state produced for opening a contract had the wrong representation.
    ContractEntryInvariant(String),
    UnsupportedContractEntry(String),
    OverlappingContractInputView {
        owned: Box<ResourceFact>,
        viewed: Box<ResourceFact>,
    },
    /// A verified call may write memory for which it has no checked byte bound.
    UnboundedWriteWithLiveView {
        callee: String,
        effect_source: Option<Box<ResourceFact>>,
        protected: Option<Box<MemoryRange>>,
    },
    /// A resource clause's value could not be evaluated for want of a value
    /// it reads: a cell, field or argument the state does not yet hold.
    /// Another clause's authority may supply it, so a contract's resource
    /// evaluator retries the clause after the others. Otherwise it is a
    /// [`Self::FunctionContract`] refusal and is reported as one.
    UnsuppliedResourceValue(String),
    /// Candidate borrow recovery refused while these exact checked path
    /// obligations remain. Retained for diagnostics, never admitted as facts.
    PendingCallObligations(Arc<[ProofObligation]>),
    /// Exact operands retained at a rejected contract boundary. Diagnostic
    /// only: these values never establish a fact or grant access.
    ContractResourceDiagnostic {
        reason: String,
        held: Option<Box<ResourceFact>>,
        required: Box<ResourceFact>,
        memory: Option<Box<SymbolicMemory>>,
    },
    /// Lock or destroy encountered no successful modeled initialization for
    /// this mutex on the current path.
    UninitializedMutex {
        mutex: Address,
    },
    /// The modeled runtime has no sound shared-mutex transition for workers.
    /// This is a verifier limitation, not a missing client proof premise.
    UnsupportedConcurrentMutex,
    MutexStorageInUse {
        mutex: Address,
        allocation: Address,
    },
    MutexStorageSeparationRequired {
        allocation: Box<MemoryRange>,
        storage: Box<MemoryRange>,
    },
    MutexStorageWrite {
        write: Box<MemoryRange>,
        storage: Box<MemoryRange>,
    },
    MissingMutexStorageAlignment {
        mutex: Address,
        alignment: u32,
    },
    UnsupportedMutexStorageRetirement,
    /// The automatic object cannot expire while initialized mutex storage
    /// is known (or may be constrained) to lie in it.
    MutexStorageScopeEnd {
        local: String,
        mutex: Address,
        may_alias: bool,
    },
    InvalidFree(InvalidFree),
    UnresolvedAllocationOutcome,
    LiveAllocationLeak {
        allocation: Box<ResourceFact>,
        /// The declared resource obligation whose body keeps `allocation`
        /// live, when the kernel can identify one.  Keeping this alongside
        /// the allocation lets surface diagnostics name the obligation that
        /// was lost instead of reverse-engineering resource definitions from
        /// a lowered allocation fact.
        resource: Option<Box<ResourceFact>>,
    },
    StaleResourceAfterFree {
        resource: Box<ResourceFact>,
    },
    DuplicateResource {
        resource: Box<ResourceFact>,
    },
    OverlappingOwnedMemoryResources {
        left: Box<MemoryRange>,
        right: Box<MemoryRange>,
    },
    /// A callee's produced or ensured composite carries a body that overlaps
    /// a resource the destination context already holds. Composing the head
    /// would leave two owners over the same bytes, so the context would stop
    /// denoting a partition.
    ProducedCompositeOverlapsHeldResource {
        produced: Box<ResourceFact>,
        piece: Box<ResourceFact>,
        held: Box<ResourceFact>,
    },
    BorrowRefusal(Box<crate::kernel::BorrowRefusalDiagnostic>),
    /// A call needs `assembled`, a viewed composite the caller holds the
    /// pieces of but not the instance, and assembling it is a fold: `fact`
    /// is the first body fact, lowered at the caller's memory, the caller
    /// has not established. Diagnostic only.
    UnestablishedAssemblyFact {
        assembled: Box<ResourceFact>,
        fact: Box<Proposition>,
        source: Option<Box<ResourceBodyFactSource>>,
    },
}

impl From<crate::kernel::BorrowRefusalDiagnostic> for RuntimeError {
    fn from(diagnostic: crate::kernel::BorrowRefusalDiagnostic) -> Self {
        Self::BorrowRefusal(Box::new(diagnostic))
    }
}

/// The written clause of a refused composite assembly, with the parameter
/// values at that call. Diagnostic metadata only; it supplies no evidence.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ResourceBodyFactSource {
    pub spelling: String,
    pub bindings: Vec<(String, ProgramValue)>,
}

/// The most earlier conjuncts a conjunction's right side may be read under
/// while it owes evaluation domains: [`ExecutionLimit::GuardedConjunctionTooLong`].
pub const GUARDED_CONJUNCTION_LIMIT: usize = 64;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ExecutionLimit {
    Deadline,
    ExpressionSteps,
    StatementSteps,
    FunctionCalls,
    LoopUnrolls,
    Paths,
    /// A loop invariant's pass count, `iterations`, read where no loop
    /// phase binds it.
    LoopIterationsUnbound,
    UnsupportedPureFunctionResult(ProgramType),
    /// Stage 5 (`design/machine-integers.md`, decision D2): a `Bool`
    /// compared with an integer. `Bool` has no integer value.
    BoolComparedWithInteger,
    /// An order (`<`, `<=`, `>`, `>=`) on `Bool`.
    BoolOrdered,
    /// Arithmetic on a `Bool`, an implicit promotion included.
    BoolArithmetic,
    /// A conditional with an `int32` arm and a `Bool` arm.
    MixedBoolArms,
    /// A symbolic specification conditional whose pointer arms cannot share a value.
    SymbolicPointerConditional,
    /// A conjunction whose right side owes evaluation domains read under
    /// more than [`GUARDED_CONJUNCTION_LIMIT`] earlier conjuncts. Each such
    /// domain carries its whole guard, so a longer chain is refused rather
    /// than lowered slowly.
    GuardedConjunctionTooLong,
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
    /// A count names one concrete population anchor.
    AuthorityCountNeedsExactPointer,
    AuthorityCountNeedsResolvedMember,
    /// Both the visible authority fact and checked ledger custody are needed.
    AuthorityCountNeedsOwnership,
    /// The population's authority is lent to an outstanding worker.
    AuthorityCountLentToWorker,
    /// An outstanding locked worker changes the population before its join.
    AuthorityCountPendingLockedWorker,
    /// The right side of an `or` has no value wherever its left side is
    /// false, the only case in which it is read.
    DisjunctionRightUndefined,
    /// Renaming a quantifier's variable to its bound form ran out of work.
    QuantifierDoesNotClose,
}

/// The stopping point as [`ExecutionLimit::describe`] names it.
impl std::fmt::Display for ExecutionLimit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&(*self).describe())
    }
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
            Self::LoopIterationsUnbound => {
                "`iterations` outside a loop phase that binds its pass count".to_string()
            }
            Self::UnsupportedPureFunctionResult(result_type) => {
                format!("unsupported pure-function result type {result_type:?}")
            }
            Self::BoolComparedWithInteger => "a `Bool` compared with an integer".to_string(),
            Self::BoolOrdered => "an order on `Bool`".to_string(),
            Self::BoolArithmetic => "arithmetic on a `Bool`".to_string(),
            Self::MixedBoolArms => "a conditional with an integer and a `Bool` arm".to_string(),
            Self::SymbolicPointerConditional => {
                "a symbolic choice between distinct pointer values".to_string()
            }
            Self::GuardedConjunctionTooLong => format!(
                "a conjunction guarding evaluation domains by more than {GUARDED_CONJUNCTION_LIMIT} conjuncts"
            ),
            Self::KernelVariables { ceiling } => {
                format!("the execution's fresh-identity range, which ends below {ceiling}")
            }
            Self::MatchBinderVariables { ceiling } => {
                format!("the match-binder identity range, which ends below {ceiling}")
            }
            Self::ExecutionIdentityBesideLiveState => {
                "an internal request for an execution identity beside a live state".to_string()
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
            Self::DisjunctionRightUndefined => {
                "an `or` whose right side is undefined wherever its left side is false".to_string()
            }
            Self::QuantifierDoesNotClose => {
                "a quantifier whose body could not be renamed to its bound variable".to_string()
            }
            Self::ResourceFieldInstanceUnavailable => {
                "a model field of a resource instance this state does not hold".to_string()
            }
        }
    }
}

/// The kernel-side one-line rendering, [`RuntimeError::kernel_summary`].
impl std::fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.kernel_summary())
    }
}

impl RuntimeError {
    /// The exact view requested by a load while evaluating a resource clause.
    /// A comparison between held and required resources carries both operands.
    pub(crate) fn missing_contract_read(&self) -> Option<&MemoryRange> {
        match self {
            Self::ContractResourceDiagnostic {
                held: None,
                required,
                ..
            } if required.is_view() => required.memory_range(),
            _ => None,
        }
    }

    /// Whether evaluating or admitting the declared entry resources identified a
    /// violation of a contract rule.
    pub(crate) fn is_contract_entry_resource_error(&self) -> bool {
        self.missing_contract_read().is_some()
            || matches!(
                self,
                Self::InvalidContractResource(_)
                    | Self::OverlappingOwnedMemoryResources { .. }
                    | Self::OverlappingContractInputView { .. }
            )
    }

    /// The sentence for [`RuntimeError::UnbackedReturnedView`], which the
    /// surface completes with the view in source terms.
    pub const UNBACKED_RETURNED_VIEW: &'static str =
        "stable-view call returned a view without a checked input child or preserved outer binding";

    /// A kernel-side one-line rendering, for messages built where no C
    /// parameter names are at hand, so it names no pointer: the kernel's
    /// spelling of an address is lowering state, not anything the reader
    /// wrote. The surface describers spell pointers through the parameters.
    /// The message of a function-contract refusal, including one whose
    /// resource value another clause may still supply.
    pub fn function_contract_message(&self) -> Option<&str> {
        match self {
            Self::FunctionContract(message)
            | Self::InvalidContractResource(message)
            | Self::UnsuppliedResourceValue(message) => Some(message),
            _ => None,
        }
    }

    /// Why a heap allocation's size was refused, and which sizes are
    /// accepted ([`Self::HeapAllocationSize`]).
    pub const HEAP_ALLOCATION_SIZE_MESSAGE: &'static str = "heap allocation size must be proved to fit a heap block: a symbolic 64-bit (`size_t`) `malloc` or `realloc` size is accepted where the facts prove it at least 1 and at most PTRDIFF_MAX (9223372036854775807) bytes, `malloc(n * w)`, `realloc(p, n * w)` and `calloc(n, w)` where they prove `1 <= n <= PTRDIFF_MAX / w`, and a product of two symbolic sizes not at all";

    /// Why an unsigned 32-bit heap allocation size was refused
    /// ([`Self::HeapAllocationSizeAboveInt32`]).
    pub const HEAP_ALLOCATION_SIZE_ABOVE_INT32_MESSAGE: &'static str = "heap allocation size must be known to fit the signed 32-bit allocation size: Click models a heap block with a checked 32-bit size of at most 2147483647 bytes, and accepts a `uint32` size, or element count, only where the facts bound it to that size";

    /// The sentence a [`Self::ThinPointerRequired`] refusal says.
    pub fn thin_pointer_required_message(operation: &str) -> String {
        format!(
            "{operation} takes a thin pointer, not a slice: use the slice's data pointer \
             `.as_ptr()`, or its length `.len()`"
        )
    }

    /// The sentence a [`Self::SliceTypeMismatch`] refusal says.
    pub fn slice_type_mismatch_message(operation: &str) -> String {
        format!("type mismatch: {operation} takes a slice, not a thin pointer or a scalar")
    }

    pub fn kernel_summary(&self) -> String {
        match self {
            RuntimeError::LoadTypeMismatch {
                value_type, stored, ..
            } => {
                let found = match stored.as_deref() {
                    Some(ProgramValue::Pointer(_)) => "found a pointer in the cell".to_string(),
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
    /// This lowering's own counter for match-arm binders. Binders have
    /// their own origin, so no execution, quantifier, fold, load or pointer
    /// producer can mint one.
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
    pub(super) dropped_runtime_error: Option<RuntimeError>,
    /// The first undefined behavior a specification evaluation dropped while
    /// every path of some sub-evaluation ended in it and none in a runtime
    /// error: a C operand whose operation is undefined wherever it is read,
    /// such as `y / x` read where `x == 0`. Diagnostic only, as
    /// [`Self::dropped_runtime_error`] is.
    pub(super) dropped_undefined_behavior: Option<UndefinedBehavior>,
    /// The first constant element range a specification lowering dropped
    /// because it is not a valid 32-bit byte span: reversed, or wider than
    /// `u32::MAX` bytes once scaled. Such a range prunes its own evaluation
    /// path, and the surviving path count says nothing about why. Diagnostic
    /// only: no evaluation reads it back.
    pub(super) dropped_range_span: Option<DroppedRangeSpan>,
    /// The first range fold a specification lowering dropped because its body
    /// did not evaluate to one symbolic iteration under the fold's binders.
    /// Such a fold prunes its own evaluation path, and the surviving path
    /// count says nothing about why. Diagnostic only: no evaluation reads it
    /// back.
    pub(super) dropped_fold_body: Option<DroppedFoldBody>,
    /// A comparison the requested operator could not build for its operands.
    /// Diagnostic only; it never changes which paths or terms are produced.
    pub(super) dropped_symbolic_pointer_conditional: bool,
    pub(super) dropped_comparison: Option<(ProgramType, ComparisonOperator, ProgramType)>,
    /// Set when a stated resource relation was dropped because this context
    /// already proves one of its memory ranges is not a valid byte span.
    /// Unlike [`Self::dropped_range_span`] the endpoints here need not be
    /// constants — the surrounding facts are what decide it — so there is no
    /// element count to report, only the reason. Diagnostic only: no
    /// evaluation reads it back.
    /// Set when a stated memory range was dropped because this context
    /// refutes one of its span guards: `Some(true)` when the refuted guard
    /// orders its endpoints (the range runs backwards), `Some(false)` when
    /// it bounds the byte count (the range is too wide). Diagnostic only.
    pub(super) dropped_refuted_range_span: Option<bool>,
    /// The byte order of the environment whose statements this budget is
    /// executing, installed from `ExecutionEnvironment` at each statement.
    /// `None` until a statement installs it: an expression evaluated with no
    /// environment in hand has no byte view of integer cells at all.
    pub(super) program_byte_order: Option<ByteOrder>,
}

/// A constant element range a lowering refused as a byte span, for the
/// message a caller writes when the lowering produced no path.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DroppedRangeSpan {
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
pub enum ExpressionOutcome<V = ProgramValue> {
    Value(V),
    UndefinedBehavior(UndefinedBehavior),
    RuntimeError(RuntimeError),
}

impl<V> ExpressionOutcome<V> {
    /// Change only the value carrier; refusals keep their original identity.
    pub fn map_value<W>(self, map: impl FnOnce(V) -> W) -> ExpressionOutcome<W> {
        match self {
            Self::Value(value) => ExpressionOutcome::Value(map(value)),
            Self::UndefinedBehavior(error) => ExpressionOutcome::UndefinedBehavior(error),
            Self::RuntimeError(error) => ExpressionOutcome::RuntimeError(error),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ConditionOutcome {
    Value(bool),
    UndefinedBehavior(UndefinedBehavior),
    RuntimeError(RuntimeError),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) enum LValueOutcome {
    LValue(LValue),
    UndefinedBehavior(UndefinedBehavior),
    RuntimeError(RuntimeError),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum StatementOutcome {
    Normal(Box<ExecutionState>),
    Break(Box<ExecutionState>),
    /// The loop's own test was false; distinct from a written `break`.
    LoopTestFalse(Box<ExecutionState>),
    Continue(Box<ExecutionState>),
    /// A checked source edge awaiting resumption at its function-owned target.
    Jump {
        target: ControlTargetId,
        state: Box<ExecutionState>,
    },
    Return {
        value: StoredExecutionValue,
        state: Box<ExecutionState>,
    },
    /// An exceptional transfer that has not yet been handled in this function.
    Throw {
        value: StoredExecutionValue,
        state: Box<ExecutionState>,
    },
    /// Internal to `ProgramStatementVerifies`: the statement has no finite
    /// successor, but all of its finite prefixes have been checked.
    VerificationDiverges,
    UndefinedBehavior(UndefinedBehavior),
    RuntimeError(RuntimeError),
}

impl StatementOutcome {
    /// The state this outcome continues from, when it has one.
    pub(crate) fn state_mut(&mut self) -> Option<&mut ExecutionState> {
        match self {
            Self::Normal(state)
            | Self::Break(state)
            | Self::LoopTestFalse(state)
            | Self::Continue(state)
            | Self::Jump { state, .. }
            | Self::Return { state, .. }
            | Self::Throw { state, .. } => Some(state),
            Self::VerificationDiverges | Self::UndefinedBehavior(_) | Self::RuntimeError(_) => None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum FunctionOutcome {
    Return {
        value: StoredExecutionValue,
        state: Box<ExecutionState>,
    },
    /// An exceptional outcome crossing this function boundary.
    Throw {
        value: StoredExecutionValue,
        state: Box<ExecutionState>,
    },
    /// Internal to `ProgramFunctionVerifies`: no return frontier exists, but the
    /// function's finite prefixes satisfy its safety proof.
    VerificationDiverges,
    UndefinedBehavior(UndefinedBehavior),
    RuntimeError(RuntimeError),
}

impl FunctionOutcome {
    /// Equality that identifies end states differing only in creation
    /// ledgers that record nothing (`ExecutionState::equal_up_to_unused_creation_ledgers`).
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
pub struct LocalEnvironment {
    /// Persistent, so binding one name copies one search path rather than
    /// every binding: a frame of N locals bound one at a time costs N log N.
    pub(super) bindings: crate::persistent::PersistentMap<BindingName, LocalBinding>,
    pub(super) slots: crate::persistent::PersistentMap<Address, BindingName>,
    /// The slots that can designate automatic storage. Value-only parameter
    /// pseudo-slots never have a block and do not participate in lifetime ends.
    automatic_slots: crate::persistent::PersistentMap<Address, ()>,
    /// Each scalar object's name under a fingerprint of the integer term it
    /// holds, kept with `bindings`: naming a value looks up the objects that
    /// may hold it instead of comparing it with every binding.
    pub(super) held_terms: crate::persistent::PersistentMap<(u64, BindingName), ()>,
    /// Pointer-valued objects by their held pointer's block, then name.
    /// Source synthesis visits only possible bases of the selected pointer.
    pub(super) pointer_objects_by_block: crate::persistent::PersistentMap<
        AddressBase,
        crate::persistent::PersistentMap<BindingName, ()>,
    >,
    pub(super) visible_names: PersistentMap<String, PersistentMap<(u32, bool, u32), BindingName>>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) enum LocalBinding {
    Object {
        /// True only for an allocated scalar binding, not a logical parameter
        /// whose compatibility pseudo-slot happens to have the same name.
        storage_declared: bool,
        value: StoredExecutionValue,
        program_type: ProgramType,
        slot: Address,
        volatile: bool,
        pointee_volatile: bool,
        constant: bool,
        pointee_constant: bool,
    },
    UninitializedObject {
        program_type: ProgramType,
        slot: Address,
        volatile: bool,
        pointee_volatile: bool,
        constant: bool,
        pointee_constant: bool,
    },
    GlobalObject {
        program_type: ProgramType,
        slot: Address,
        library_value: Option<StoredExecutionValue>,
        volatile: bool,
        pointee_volatile: bool,
        constant: bool,
        pointee_constant: bool,
    },
    ArrayObject {
        element_type: ProgramType,
        length: u32,
        slot: Address,
        constant: bool,
    },
    AggregateObject {
        layout: AggregateLayout,
        slot: Address,
        constant: bool,
        /// Set only on the parameter object materialized for a standalone proof.
        proof_input_for: Option<std::sync::Arc<str>>,
    },
}

/// The state a state forgot knowledge from.
///
/// A state is interned by content, so two states with the same known
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
/// state would put a chain of `Arc<SymbolicMemory>` inside every state that
/// ever forgot anything, and equality, ordering and dropping would all
/// recurse down it — one stack frame per forget, on a hot path, in a
/// structure the arena already keeps alive. Every field here is O(1) to
/// compare and to hash.
///
/// It is held behind an `Arc` rather than inline for the same reason the
/// cell map is: `SymbolicMemory` travels by value through deeply recursive
/// evaluation, so a state pays one pointer for the mark and the states
/// that inherit it share the one allocation.
///
/// `content_hash` comes first so that the derived ordering is the one a
/// verification can reproduce: it is a function of the base's content, while
/// arena tokens count process-wide and would order states differently from
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

/// What a state no longer knows, beside its cells.
///
/// Two facts of the same kind, behind one pointer. `SymbolicMemory` travels by value
/// inside `Term`, whose clone recurses once per nested operator, so a state
/// pays one word for both rather than one each.
#[derive(Clone, Debug, Default, Eq, PartialEq, Ord, PartialOrd)]
pub struct ForgottenKnowledge {
    /// Automatic-storage blocks whose lifetimes have ended. Unlike removing
    /// the block alone, retaining this tombstone makes stale aliases invalid
    /// even when a later proof step forgets or rejoins ordinary cells.
    pub(super) ended_local_blocks: HashedOrdSet<AddressBase>,
    /// The entries of `ended_local_blocks` whose address some pointer value
    /// may hold (`block_is_never_address_taken_local` is false). Only these
    /// can make a load through a pointer observe a retired object, so only
    /// these belong in a read's projection. Maintained wherever
    /// `ended_local_blocks` changes, so naming never scans the whole set.
    pub(super) ended_addressable_local_blocks: HashedOrdSet<AddressBase>,
    /// Set where cached values were dropped without the memory itself being
    /// known unchanged; see [`ForgottenFrom`]. Carried by later stores and by
    /// the projections used for load naming, so a state that has forgotten
    /// something can never re-intern as the state it forgot it from.
    pub(super) forgotten_from: Option<ForgottenFrom>,
    /// Inputs of the most recent branch abstraction. Their exact arena
    /// identities prevent first-wins read naming from mixing different joins;
    /// their content hashes keep read names reproducible across sessions.
    /// The persistent set caches its hash and does not retain recursive
    /// state contents. Read projections must retain this identity.
    pub(super) join_inputs: HashedOrdSet<ForgottenFrom>,
}

/// What the verifier knows about memory at one program point: symbolic
/// values for the cells it has tracked, plus the blocks, heap state, and
/// forgotten knowledge that bound them. It is partial: a cell with no entry
/// is unknown, not empty or zero. Each value belongs to a
/// [`ProgramPoint`](crate::kernel::ProgramPoint); pass the point rather than
/// this value where the point is what is meant.
#[derive(Clone, Debug, Default)]
pub struct SymbolicMemory {
    pub(super) construction: Option<Arc<MemoryConstruction>>,
    /// The steps taken on this value's path since its state last reached a
    /// point ([`program_point::StepLog`]). Not part of equality, hashing or
    /// the interning key, and never kept in the arena: it follows the value
    /// a path executes, not the content.
    pub(super) pending_steps: Option<Arc<program_point::StepLog>>,
    pub(super) blocks: std::sync::Arc<MemoryBlocks>,
    pub(super) cells: std::sync::Arc<CellStore>,
    /// Typed views of address-overlapping union storage. A union member is
    /// keyed by its address and type rather than placed in `cells`, because
    /// two members at one address must remain independently readable after a
    /// by-value aggregate copy.
    pub(super) union_cells: std::sync::Arc<HashedOrdMap<(Address, ProgramType), StoredMemoryValue>>,
    pub(super) forgotten: std::sync::Arc<ForgottenKnowledge>,
    pub(super) heap: std::sync::Arc<HeapMemory>,
}

/// A retained explanation, deliberately excluded from memory equality, hashing,
/// interning keys, and every proof rule. It travels with the state, including
/// across threads. Roots guard against accidentally inheriting a stale origin
/// when a constructor edits a cloned state without recording its operation.
#[derive(Clone)]
pub(crate) struct MemoryConstruction {
    roots: SymbolicMemory,
    pub(crate) kind: MemoryConstructionKind,
}

// Avoid recursively dumping the entire construction history in an assertion.
impl std::fmt::Debug for MemoryConstruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let operation = match &self.kind {
            MemoryConstructionKind::Transition(edge) => edge.kind_name(),
            MemoryConstructionKind::Transform { operation, .. } => operation,
        };
        f.debug_tuple("MemoryConstruction")
            .field(&operation)
            .finish()
    }
}

#[derive(Clone, Debug)]
pub(crate) enum MemoryConstructionKind {
    Transition(Arc<MemoryDerivation>),
    Transform {
        operation: &'static str,
        sources: Vec<SymbolicMemory>,
        arguments: Vec<ProgramValue>,
    },
}

impl SymbolicMemory {
    // Pin the described roots so an in-place Arc mutation or allocator address
    // reuse cannot make a stale construction appear to describe new contents.
    // Dropping the origin here avoids a self-reference through this pin.
    fn diagnostic_roots(&self) -> Self {
        let mut roots = self.clone();
        roots.construction = None;
        roots
    }

    pub(crate) fn diagnostic_construction(&self) -> Option<&MemoryConstructionKind> {
        self.construction
            .as_ref()
            .filter(|origin| origin.roots.same_storage_roots(self))
            .map(|origin| &origin.kind)
    }

    pub(crate) fn is_initial_diagnostic_memory(&self) -> bool {
        self.blocks.is_empty()
            && self.cells.len() == 0
            && self.union_cells.is_empty()
            && *self.forgotten == ForgottenKnowledge::default()
            && *self.heap == HeapMemory::default()
    }

    pub(in crate::kernel) fn record_diagnostic_transform(
        &mut self,
        operation: &'static str,
        sources: Vec<SymbolicMemory>,
        arguments: Vec<ProgramValue>,
    ) {
        crate::instrumentation::record_deterministic_work(1 + sources.len());
        if sources.len() == 1 && self.same_storage_roots(&sources[0]) {
            return;
        }
        self.construction = Some(Arc::new(MemoryConstruction {
            roots: self.diagnostic_roots(),
            kind: MemoryConstructionKind::Transform {
                operation,
                sources,
                arguments,
            },
        }));
    }

    /// O(1) diagnostic identity for a state without interning or walking
    /// its contents. This is intentionally only an identity label; equal
    /// labels imply shared storage roots, not semantic inequality otherwise.
    pub(crate) fn diagnostic_identity(&self) -> (usize, usize, usize, usize, usize) {
        self.storage_root_identity()
    }

    /// Exact O(1) lookup key for shared storage, never semantic inequality.
    /// Users of this key retain the memory roots for the lookup lifetime.
    pub(in crate::kernel) fn storage_root_identity(&self) -> (usize, usize, usize, usize, usize) {
        (
            std::sync::Arc::as_ptr(&self.blocks) as usize,
            std::sync::Arc::as_ptr(&self.cells) as usize,
            std::sync::Arc::as_ptr(&self.union_cells) as usize,
            std::sync::Arc::as_ptr(&self.forgotten) as usize,
            std::sync::Arc::as_ptr(&self.heap) as usize,
        )
    }

    /// Records that this state dropped cached values that `base` knew,
    /// without the memory the two describe having changed.
    ///
    /// Overwriting an older mark keeps the whole history: `base` carries its
    /// own mark, and `base`'s content hash — which is what is stored here —
    /// already depends on it.
    pub(in crate::kernel) fn mark_forgotten_from(&mut self, base: &SharedMemory) {
        std::sync::Arc::make_mut(&mut self.forgotten).forgotten_from = Some(ForgottenFrom {
            content_hash: base.content_hash,
            arena_id: base.arena_id(),
        });
    }

    /// Whether the two states describe one memory: the same blocks, heap
    /// lifetimes, union views and forgotten-knowledge marks, and the same
    /// cells whatever representation each cell store keeps them in
    /// ([`CellStore::same_cells_as`]). Everything but the cell cache's layout
    /// is compared exactly as `==` compares it.
    #[cfg(test)]
    pub(in crate::kernel) fn same_contents_as(&self, other: &Self) -> bool {
        self == other
            || (self.blocks == other.blocks
                && self.union_cells == other.union_cells
                && self.forgotten == other.forgotten
                && self.heap == other.heap
                && self.cells.same_cells_as(&other.cells))
    }

    /// Whether `self == other`, for two states each derived from `base`'s
    /// storage, comparing only what each changed from `base` (see
    /// [`HashedOrdMap::eq_relative_to`]). Exact whatever the states share;
    /// the cost is the changed paths when both were derived from `base`.
    pub(super) fn eq_relative_to(&self, other: &Self, base: &Self) -> bool {
        memory_content_hash(self) == memory_content_hash(other)
            && self.non_cell_contents_eq_relative_to(other, base)
            && (std::sync::Arc::ptr_eq(&self.cells, &other.cells)
                || self.cells.eq_relative_to(&other.cells, &base.cells))
    }

    /// Like `same_contents_as`, with an exact changed-path comparison when
    /// the states share a base. Logical cells can still agree across layouts.
    pub(super) fn same_contents_relative_to(&self, other: &Self, base: &Self) -> bool {
        if self.same_storage_roots(other)
            || matches!(
                (interned_storage_of(self), interned_storage_of(other)),
                (Some(left), Some(right)) if left.arena_id() == right.arena_id()
            )
        {
            return true;
        }
        self.non_cell_contents_eq_relative_to(other, base)
            && (std::sync::Arc::ptr_eq(&self.cells, &other.cells)
                || self.cells.eq_relative_to(&other.cells, &base.cells)
                || self.cells.same_logical_cells_by_difference(&other.cells))
    }

    fn non_cell_contents_eq_relative_to(&self, other: &Self, base: &Self) -> bool {
        (std::sync::Arc::ptr_eq(&self.blocks, &other.blocks)
            || self.blocks.eq_relative_to(&other.blocks, &base.blocks))
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
    /// the stored state by [`Self::same_storage_roots`]. Tests use it to
    /// stand for an equal state reached without going through a
    /// derivation, which would hand back the arena's canonical instance.
    #[cfg(test)]
    pub(crate) fn with_fresh_storage_roots(&self) -> Self {
        let mut result = Self {
            construction: None,
            pending_steps: None,
            blocks: std::sync::Arc::new((*self.blocks).clone()),
            cells: std::sync::Arc::new((*self.cells).clone()),
            union_cells: std::sync::Arc::new((*self.union_cells).clone()),
            forgotten: std::sync::Arc::new((*self.forgotten).clone()),
            heap: std::sync::Arc::new((*self.heap).clone()),
        };
        result.record_diagnostic_transform("copy state storage", vec![self.clone()], Vec::new());
        result
    }

    /// Whether two states are the same stored state, by the storage
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
/// state where its block is still live.
#[derive(Clone)]
pub(in crate::kernel) struct ReadRegionIdentity {
    block_size: Option<AllocationSize>,
    local_lifetime_ended: bool,
    heap: Arc<HeapMemory>,
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

impl SymbolicMemory {
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

impl PartialEq for SymbolicMemory {
    /// Rejects on the O(1) content hash before any elementwise comparison.
    /// Without that, a candidate that differs only in a later component
    /// would pay for comparing the equal earlier ones, and which candidates a
    /// randomly seeded hash table happens to probe would change the charged
    /// work from run to run.
    fn eq(&self, other: &Self) -> bool {
        if memory_content_hash(self) != memory_content_hash(other) {
            return false;
        }
        self.blocks == other.blocks
            && self.cells == other.cells
            && self.union_cells == other.union_cells
            && self.forgotten == other.forgotten
            && self.heap == other.heap
    }
}

impl Eq for SymbolicMemory {}

impl std::hash::Hash for SymbolicMemory {
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

impl Ord for SymbolicMemory {
    /// By a content hash first, then structurally. The structural order walks
    /// the entries two states share, and states along one path share
    /// almost all of them, so ordered collections keyed by memories (fact
    /// sets, premise sets) paid for the whole memory on every comparison
    /// (`roadmap/scaling.md`). The cached content hash is O(1) and, being a
    /// function of the entries under fixed hash keys, as deterministic as
    /// the structural order; equal states have equal hashes, so the
    /// structural walk runs only for equal states in unshared storage
    /// and on hash collisions, and the order stays consistent with `Eq`.
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if std::sync::Arc::ptr_eq(&self.blocks, &other.blocks)
            && std::sync::Arc::ptr_eq(&self.cells, &other.cells)
            && std::sync::Arc::ptr_eq(&self.union_cells, &other.union_cells)
            && std::sync::Arc::ptr_eq(&self.forgotten, &other.forgotten)
            && std::sync::Arc::ptr_eq(&self.heap, &other.heap)
        {
            return std::cmp::Ordering::Equal;
        }
        memory_ordering_key(self)
            .cmp(&memory_ordering_key(other))
            .then_with(|| self.structural_cmp(other))
    }
}

#[cfg(test)]
thread_local! {
    /// Structural memory and resource-context comparisons run on this
    /// thread, for the regressions that ordering does not walk states.
    static STRUCTURAL_COMPARISONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// The structural memory and resource-context comparisons `run` performed.
#[cfg(test)]
pub(crate) fn count_structural_comparisons<T>(run: impl FnOnce() -> T) -> (T, usize) {
    let before = STRUCTURAL_COMPARISONS.with(std::cell::Cell::get);
    let result = run();
    (
        result,
        STRUCTURAL_COMPARISONS.with(std::cell::Cell::get) - before,
    )
}

fn count_structural_comparison() {
    #[cfg(test)]
    STRUCTURAL_COMPARISONS.with(|count| count.set(count.get() + 1));
}

impl SymbolicMemory {
    fn structural_cmp(&self, other: &Self) -> std::cmp::Ordering {
        count_structural_comparison();
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

impl PartialOrd for SymbolicMemory {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// The machine format of a memory block's byte count
/// (`design/heap-allocation-sizes.md`, decision D1).
///
/// `Int32` is a 32-bit byte count in `0..=INT32_MAX`, on which its signed
/// and unsigned readings agree: every block but a heap block with a symbolic
/// 64-bit (`size_t`) size. `UInt64` is an unsigned 64-bit byte count, at
/// most `PTRDIFF_MAX` when admitted; its `allocation` token holds a `uint64`
/// and its owned range is wide ([`RangeIndexKind::UInt64`]). `malloc` of a
/// symbolic 64-bit size proved to fit makes one.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum AllocationSizeKind {
    Int32,
    UInt64,
}

/// A memory block's byte count together with its format.
///
/// Equality and ordering compare the kind after the bytes. Hashing and
/// `Debug` of an `Int32` size are exactly those of its byte term, so
/// state hashes (which name symbolic loads and order forgotten states)
/// and traces of every 32-bit block are those of the untagged term; a
/// `UInt64` size hashes and prints its kind as well.
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct AllocationSize {
    bytes: StoredMachineTerm,
    kind: AllocationSizeKind,
}

impl std::hash::Hash for AllocationSize {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.bytes.hash(state);
        if self.kind != AllocationSizeKind::Int32 {
            self.kind.hash(state);
        }
    }
}

impl std::fmt::Debug for AllocationSize {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind {
            AllocationSizeKind::Int32 => self.bytes.fmt(formatter),
            AllocationSizeKind::UInt64 => {
                formatter.debug_tuple("UInt64").field(&self.bytes).finish()
            }
        }
    }
}

impl AllocationSize {
    pub(crate) fn from_value(value: crate::kernel::ExecutionValue) -> Option<Self> {
        let kind = match value.program_type() {
            ProgramType::Int32 => AllocationSizeKind::Int32,
            ProgramType::UInt64 => AllocationSizeKind::UInt64,
            _ => return None,
        };
        Some(Self {
            bytes: StoredMachineTerm::from_value(value)?,
            kind,
        })
    }

    pub fn new(bytes: OldMachineTerm, kind: AllocationSizeKind) -> Self {
        Self {
            bytes: StoredMachineTerm::new(
                match kind {
                    AllocationSizeKind::Int32 => MachineIntegerType::Int32,
                    AllocationSizeKind::UInt64 => MachineIntegerType::UInt64,
                },
                bytes,
            ),
            kind,
        }
    }

    /// A 32-bit byte count in `0..=INT32_MAX`.
    pub fn int32(bytes: impl Into<OldMachineTerm>) -> Self {
        Self::new(bytes.into(), AllocationSizeKind::Int32)
    }

    pub fn bytes(&self) -> &OldMachineTerm {
        self.bytes.old_form()
    }

    pub(crate) fn byte_operand(&self) -> MachineOperandView<'_> {
        self.bytes.operand_view()
    }

    pub fn kind(&self) -> AllocationSizeKind {
        self.kind
    }

    pub(crate) fn map_stored_bytes(
        &self,
        rewrite: impl FnOnce(&StoredMachineTerm) -> StoredMachineTerm,
    ) -> Self {
        Self {
            bytes: rewrite(&self.bytes),
            kind: self.kind,
        }
    }

    /// The `allocation` token's byte-count argument: an `int32` or a `uint64`.
    pub(crate) fn token_value(&self) -> ProgramValue {
        match self.kind {
            AllocationSizeKind::Int32 => ProgramValue::Int32(self.bytes.old_form().clone()),
            AllocationSizeKind::UInt64 => ProgramValue::UInt64(self.bytes.old_form().clone()),
        }
    }

    /// The byte count as an unsigned 64-bit value: a 32-bit size zero
    /// extended (it is nonnegative), a 64-bit one as it is.
    pub(crate) fn uint64_bytes(&self) -> OldMachineTerm {
        match self.kind {
            AllocationSizeKind::Int32 => {
                OldMachineTerm::uint64_from_32(self.bytes.old_form().clone())
            }
            AllocationSizeKind::UInt64 => self.bytes.old_form().clone(),
        }
    }

    /// The byte count as a signed 64-bit value: a 32-bit size zero
    /// extended, a 64-bit one reinterpreted (it is at most `PTRDIFF_MAX`).
    pub(crate) fn int64_bytes(&self) -> OldMachineTerm {
        match self.kind {
            AllocationSizeKind::Int32 => {
                OldMachineTerm::int64_from_uint32(self.bytes.old_form().clone())
            }
            AllocationSizeKind::UInt64 => {
                OldMachineTerm::int64_from_uint64_bits(self.bytes.old_form().clone())
            }
        }
    }

    /// The byte count as a 32-bit word, for a 32-bit size only. A 32-bit
    /// comparison against a 64-bit size has no meaning.
    pub(crate) fn int32_bytes(&self) -> Option<&OldMachineTerm> {
        (self.kind == AllocationSizeKind::Int32).then(|| self.bytes.old_form())
    }

    /// A constant byte count in this size's format.
    pub(crate) fn constant(&self, bytes: u32) -> OldMachineTerm {
        match self.kind {
            AllocationSizeKind::Int32 => OldMachineTerm::constant(bytes),
            AllocationSizeKind::UInt64 => OldMachineTerm::uint64_constant(u64::from(bytes)),
        }
    }

    /// `left <= right` over unsigned values of this size's format.
    pub(crate) fn unsigned_less_equal(
        &self,
        left: OldMachineTerm,
        right: OldMachineTerm,
    ) -> OldConditionTerm {
        match self.kind {
            AllocationSizeKind::Int32 => OldConditionTerm::unsigned_less_equal(left, right),
            AllocationSizeKind::UInt64 => OldConditionTerm::uint64_less_equal(left, right),
        }
    }

    /// The range `base[0..count]` of `element_width`-byte elements in this
    /// size's index kind; `count` is in the size's format.
    pub(crate) fn range(
        &self,
        base: Address,
        count: OldMachineTerm,
        element_width: u32,
    ) -> MemoryRange {
        match self.kind {
            AllocationSizeKind::Int32 => MemoryRange::new_with_element_width(
                base,
                OldMachineTerm::constant(0),
                count,
                element_width,
            ),
            AllocationSizeKind::UInt64 => MemoryRange::new_wide(
                base,
                OldMachineTerm::uint64_constant(0),
                count,
                element_width,
            ),
        }
    }

    /// The number of `element_width`-byte elements this size holds, in its
    /// format, when its byte count spells it: an `int32` count through
    /// [`crate::kernel::reasoning::element_count_from_bytes`], a `uint64` one
    /// through [`crate::kernel::reasoning::uint64_element_count_from_bytes`].
    pub(crate) fn element_count(&self, element_width: u32) -> Option<OldMachineTerm> {
        match self.kind {
            AllocationSizeKind::Int32 => crate::kernel::reasoning::element_count_from_bytes(
                self.bytes.old_form(),
                element_width,
            ),
            AllocationSizeKind::UInt64 => {
                crate::kernel::reasoning::uint64_element_count_from_bytes(
                    self.bytes.old_form(),
                    element_width,
                )
            }
        }
    }

    /// The block's complete byte range, `base[0..bytes]`.
    pub(crate) fn byte_range(&self, base: Address) -> MemoryRange {
        self.range(base, self.bytes.old_form().clone(), 1)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) struct PendingReallocation {
    pub(super) old_pointer: Address,
    pub(super) old_bytes: AllocationSize,
    /// Full old byte range separated from the active borrows at the call.
    pub(super) retirement_separation: Option<std::sync::Arc<Proposition>>,
    /// Bytes at the start of the new block that retain calloc's guaranteed
    /// zero value. A prefix equal to the new allocation size means the whole
    /// block is zeroed; a shorter prefix leaves the grown tail uninitialized.
    pub(super) zeroed_prefix: Option<OldMachineTerm>,
    pub(super) copied_cells: Vec<(AddressOffset, ProgramValue)>,
    /// The runs of constant byte offsets of the old block that were
    /// initialized and lie in the new allocation, cut at its size: a
    /// successful resize preserves them whether or not a cached cell still
    /// names their value, and the bytes the new block grows by stay
    /// uninitialized.
    pub(super) initialized_prefix: Vec<(i64, u32)>,
}

/// Every field is a state collection, so hashing is O(1).
#[derive(Clone, Debug, Default, Eq, PartialEq, Ord, PartialOrd)]
pub(super) struct HeapMemory {
    /// Live heap blocks are also present in `blocks`; this set distinguishes
    /// them from automatic storage and memory-havoc markers.
    pub(super) live_allocations: HashedOrdMap<Address, AllocationSize>,
    /// Heap identities are never reused within a proof. These are semantic
    /// tombstones for double-free and stale-pointer diagnostics, not
    /// resources or surviving allocation authority.
    pub(super) deallocated_allocations: HashedOrdMap<Address, AllocationSize>,
    /// A malloc result whose null/success outcome has not yet been refined by
    /// control flow or direct return. Pending allocations carry no authority
    /// until resolved.
    pub(super) pending_allocations: HashedOrdMap<Address, AllocationSize>,
    /// Object classes established by a fresh allocation's checked typed binding.
    pub(super) pending_object_classes:
        HashedOrdMap<Address, crate::kernel::effective_type::CAccessClass>,
    /// Successful malloc storage remains uninitialized until individual
    /// cells are written. Contract-imported allocations are not placed here.
    pub(super) uninitialized_allocations: HashedOrdSet<Address>,
    /// Explicit proof-entry objects whose bytes start unwritten. Unlike heap
    /// allocations these carry neither freshness nor deallocation authority.
    pub(super) uninitialized_objects: HashedOrdMap<Address, u32>,
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
    pub(super) zeroed_allocations: HashedOrdSet<Address>,
    /// Successful reallocations of zeroed storage may preserve only a prefix
    /// of the old block. The remainder of a grown block is uninitialized.
    pub(super) zeroed_prefix_allocations: HashedOrdMap<Address, OldMachineTerm>,
    /// Pending calloc results whose null/success outcome has not yet been
    /// refined.
    pub(super) zeroed_pending_allocations: HashedOrdSet<Address>,
    /// Pending reallocations retain the old live block until their result is
    /// refined. Success then retires it and installs the copied prefix;
    /// failure simply resolves the new result to null.
    pub(super) pending_reallocations: HashedOrdMap<Address, PendingReallocation>,
    /// The effective types C stores gave heap cells
    /// (`design/effective-types.md`); see [`HeapEffectiveTypes`].
    pub(super) effective_types: HeapEffectiveTypes,
}

impl std::hash::Hash for HeapMemory {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // SymbolicMemory state hashes name symbolic loads and order forgotten states.
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
        if !self.pending_object_classes.is_empty() {
            "pending_object_classes".hash(state);
            self.pending_object_classes.hash(state);
        }
        if self.effective_types != HeapEffectiveTypes::default() {
            "effective_types".hash(state);
            self.effective_types.hash(state);
        }
        if !self.uninitialized_objects.is_empty() {
            "uninitialized_objects".hash(state);
            self.uninitialized_objects.hash(state);
        }
    }
}

impl HeapMemory {
    /// Equality of two heap states derived from `base`; see
    /// [`HashedOrdMap::eq_relative_to`].
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
            && self
                .pending_object_classes
                .eq_relative_to(&other.pending_object_classes, &base.pending_object_classes)
            && self.uninitialized_allocations.eq_relative_to(
                &other.uninitialized_allocations,
                &base.uninitialized_allocations,
            )
            && self
                .uninitialized_objects
                .eq_relative_to(&other.uninitialized_objects, &base.uninitialized_objects)
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
            && self
                .effective_types
                .eq_relative_to(&other.effective_types, &base.effective_types)
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
            && self.zeroed_allocations == other.zeroed_allocations
            && self.zeroed_prefix_allocations == other.zeroed_prefix_allocations
            && self.zeroed_pending_allocations == other.zeroed_pending_allocations
            && self.pending_reallocations == other.pending_reallocations
    }

    /// Whether `next` has this heap's allocation lifetimes except for
    /// tombstones of allocations that ended after this state, none of which
    /// was live, pending, or being reallocated here.
    ///
    /// A loop body that frees storage it reached through a resource it
    /// unfolded ends an allocation the loop head never held as live: the
    /// head state knows it only folded inside a resource. Its tombstone is a
    /// double-free and stale-pointer diagnostic, not authority. Every access
    /// and every `free` needs ownership of the allocation, which the body
    /// consumed, and heap identities are never reused within a proof, so a
    /// head that does not record the tombstone admits no operation the back
    /// edge refuses. Any other difference is refused as before. Work is the
    /// changed entries, found by the maps' structural diff.
    pub(super) fn has_same_allocation_lifetimes_up_to_ended(&self, next: &Self) -> bool {
        self.live_allocations == next.live_allocations
            && self.pending_allocations == next.pending_allocations
            && self.uninitialized_allocations == next.uninitialized_allocations
            && self.uninitialized_objects == next.uninitialized_objects
            && self.zeroed_allocations == next.zeroed_allocations
            && self.zeroed_prefix_allocations == next.zeroed_prefix_allocations
            && self.zeroed_pending_allocations == next.zeroed_pending_allocations
            && self.pending_reallocations == next.pending_reallocations
            && self
                .deallocated_allocations
                .diff(&next.deallocated_allocations)
                .all(|change| match change {
                    HashedOrdMapChange::Added(pointer) => {
                        !self.live_allocations.contains_key(pointer)
                            && !self.pending_allocations.contains_key(pointer)
                            && !self.pending_reallocations.contains_key(pointer)
                    }
                    _ => false,
                })
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct MemoryBlock {
    pub(super) size: AllocationSize,
    pub(super) read_only: bool,
    /// A complete automatic scalar's declared type, independent of whether
    /// its representation has been initialized. Untyped blocks and arrays
    /// carry no scalar declaration.
    pub(super) declared_scalar_type: Option<ProgramType>,
    /// The declared class of every element of the block's object, for a
    /// declared scalar or an array of one scalar type. An access through any
    /// pointer is checked against it (`design/effective-types.md`).
    pub(super) declared_class: Option<crate::kernel::effective_type::CAccessClass>,
}

/// An interned, immutable memory state for embedding inside terms.
///
/// Equality and hashing are O(1) via the arena identity and a precomputed
/// content hash. Ordering keeps a same-identity fast path, then orders by
/// the content hash and only then structurally, as `SymbolicMemory` does: proof
/// search is sensitive to iteration order, and the content hash is as
/// deterministic as the structure, where arena-insertion order would be
/// nondeterministic across checks.
#[derive(Clone)]
pub struct SharedMemory {
    arena: u32,
    id: u32,
    content_hash: u64,
    memory: std::sync::Arc<SymbolicMemory>,
}

/// Record that `memory` is the state at `node`'s point, unless an earlier
/// point already holds it. O(1); identity is unchanged.
pub(in crate::kernel::primitives) fn record_memory_occurrence(
    memory: &SharedMemory,
    node: &std::sync::Arc<program_point::PointNode>,
) {
    C_MEMORY_ARENA.with(|arena| {
        let mut arena = arena.borrow_mut();
        let (token, arena) = &mut *arena;
        if *token != memory.arena {
            return;
        }
        if let Some(slot) = arena.occurrences.get_mut(memory.id as usize)
            && slot.as_ref().is_none_or(|weak| weak.strong_count() == 0)
        {
            *slot = Some(std::sync::Arc::downgrade(node));
        }
    });
}

impl SharedMemory {
    /// The first program point whose state this memory is, or of which it
    /// is a view: a projection for one read stands for its one source's
    /// state. `None` for a memory no point has held.
    pub(in crate::kernel::primitives) fn occurrence(
        &self,
    ) -> Option<std::sync::Arc<program_point::PointNode>> {
        let mut memory = self.clone();
        for _ in 0..4 {
            let found = C_MEMORY_ARENA.with(|arena| {
                let arena = arena.borrow();
                if arena.0 != memory.arena {
                    return None;
                }
                arena
                    .1
                    .occurrences
                    .get(memory.id as usize)
                    .cloned()
                    .flatten()
                    .and_then(|weak| weak.upgrade())
            });
            if found.is_some() {
                return found;
            }
            let Some(MemoryConstructionKind::Transform {
                operation: "project memory for pointer read" | "canonicalize embedded reads",
                sources,
                ..
            }) = memory.diagnostic_construction()
            else {
                return None;
            };
            let [source] = sources.as_slice() else {
                return None;
            };
            memory = intern_memory_ref(source);
        }
        None
    }

    /// How this state was produced, when the arena that named it is this
    /// thread's and an edge producer recorded one.
    ///
    /// `None` is always a legitimate answer — for entry states, for
    /// states built by paths that record no edge, and for handles that
    /// crossed a thread. Consumers fall back rather than conclude anything
    /// from the absence.
    pub(crate) fn derivation(&self) -> Option<std::sync::Arc<MemoryDerivation>> {
        C_MEMORY_ARENA.with(|arena| {
            let arena = arena.borrow();
            if arena.0 != self.arena {
                return None;
            }
            arena.1.derivations.get(self.id as usize).cloned().flatten()
        })
    }

    /// The arena id naming this state, valid only against ids from the
    /// same arena. Strictly decreasing along `derivation().base()`, which is
    /// what makes DAG walks terminate.
    pub(crate) fn arena_id(&self) -> (u32, u32) {
        (self.arena, self.id)
    }

    /// Producer-recorded identity of unchanged program bytes, for graph load
    /// congruence only. This is trusted-kernel metadata, not state equality
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

    /// Choose the old block walk's endpoint for static storage, or the
    /// first edge that the index leaves to that walk.
    pub(in crate::kernel) fn indexed_static_block_version(
        &self,
        block: &AddressBase,
    ) -> (SharedMemory, bool) {
        debug_assert!(block.is_static_storage_block());
        crate::instrumentation::record_deterministic_work(1);
        C_MEMORY_ARENA.with(|arena| {
            let arena = arena.borrow();
            if arena.0 != self.arena {
                return (self.clone(), true);
            }
            let mut start = self;
            while let Some(index) = &arena.1.static_block_versions[start.id as usize] {
                if let Some(version) = index.changed.get(block) {
                    return (version.clone(), true);
                }
                start = match &index.anchor {
                    StaticBlockVersionAnchor::Barrier(memory) => return (memory.clone(), true),
                    StaticBlockVersionAnchor::Unclassified(memory) => {
                        return (memory.clone(), false);
                    }
                    // A state interned before its derivation may acquire an
                    // edge later. Reuse the prefix index now installed there.
                    StaticBlockVersionAnchor::Root(memory) => memory,
                };
                if arena.1.static_block_versions[start.id as usize].is_some() {
                    crate::instrumentation::record_deterministic_work(1);
                }
            }
            (start.clone(), true)
        })
    }

    /// Skip the recorded store and checked call suffix for a static cell.
    /// An intersecting call is selected for the ordinary edge check.
    pub(in crate::kernel) fn indexed_static_cell_version(
        &self,
        pointer: &Address,
        bytes: u32,
    ) -> Option<StaticCellVersion> {
        let span = static_cell_byte_span(pointer, bytes)?;
        C_MEMORY_ARENA.with(|arena| {
            let arena = arena.borrow();
            if arena.0 != self.arena {
                return None;
            }
            let index = arena.1.static_cell_versions[self.id as usize].as_ref()?;
            crate::instrumentation::record_deterministic_work(1);
            // All these IDs are on this chain, where each derivation
            // points back to a strictly older arena state.
            let writes = index.changed.get(&pointer.base);
            let store = writes.and_then(|block| {
                span.clone()
                    .filter_map(|byte| block.stores.get(&byte).copied())
                    .max()
            });
            let call = writes.and_then(|block| block.calls.latest_candidate(&span));
            if let Some(store) = store.filter(|&store| Some(store) > call) {
                return Some(StaticCellVersion::Written(
                    arena.1.memory_handle(self.arena, store),
                ));
            }
            let boundary = call.unwrap_or(index.boundary);
            // At the selected call itself the legacy walk checks this edge,
            // including any ownership the caller kept across it.
            (boundary != self.id)
                .then(|| StaticCellVersion::Boundary(arena.1.memory_handle(self.arena, boundary)))
        })
    }

    /// SymbolicMemory state identity for definedness of a direct automatic object.
    /// A producer updates only the local it stores; every other transition
    /// starts a fresh identity unless it merely forgets cached values.
    pub(crate) fn local_read_definedness_identity(&self, pointer: &Address) -> (u32, u32) {
        if !pointer.base.is_local_block() {
            return self.arena_id();
        }
        crate::instrumentation::record_deterministic_work(1);
        C_MEMORY_ARENA.with(|arena| {
            let arena = arena.borrow();
            if arena.0 != self.arena {
                return self.arena_id();
            }
            let versions = &arena.1.local_definedness_versions[self.id as usize];
            (
                self.arena,
                versions
                    .changed
                    .get(&pointer.base)
                    .copied()
                    .unwrap_or(versions.base),
            )
        })
    }

    /// The producer-retained source of unchanged physical bytes. This is
    /// read congruence only: callers must retain the current state for
    /// initialization, lifetime and permission checks.
    pub(crate) fn unchanged_bytes_source(&self) -> Self {
        C_MEMORY_ARENA.with(|arena| {
            let arena = arena.borrow();
            if arena.0 != self.arena {
                return self.clone();
            }
            let source = arena.1.read_identities[self.id as usize];
            if source == self.id {
                return self.clone();
            }
            arena.1.memory_handle(self.arena, source)
        })
    }

    pub(crate) fn memory(&self) -> &SymbolicMemory {
        &self.memory
    }
}

impl PartialEq for SharedMemory {
    fn eq(&self, other: &Self) -> bool {
        if self.arena == other.arena {
            return self.id == other.id;
        }
        self.content_hash == other.content_hash && self.memory == other.memory
    }
}

impl Eq for SharedMemory {}

impl std::hash::Hash for SharedMemory {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.content_hash);
    }
}

impl Ord for SharedMemory {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.arena == other.arena && self.id == other.id {
            return std::cmp::Ordering::Equal;
        }
        self.content_hash
            .cmp(&other.content_hash)
            .then_with(|| self.memory.structural_cmp(&other.memory))
    }
}

impl PartialOrd for SharedMemory {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl std::fmt::Debug for SharedMemory {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.memory.fmt(formatter)
    }
}

/// The compact identity of a memory state at a retained proof frontier.
/// This only records the persistent-node pointers already held by `SymbolicMemory`;
/// it does not intern, clone, or scan the state.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct MemoryStateIdentity {
    shallow: MemoryShallowIdentity,
}

#[cfg(test)]
thread_local! {
    static CALL_REQUIREMENT_SITE_CONSTRUCTION_COUNT: std::cell::Cell<u64> =
        const { std::cell::Cell::new(0) };
}

impl MemoryStateIdentity {
    pub(crate) fn of(memory: &SymbolicMemory) -> Self {
        Self {
            shallow: MemoryShallowIdentity::of(memory),
        }
    }
}

/// The exact source-side identity needed to retry one unresolved call
/// requirement.  This is deliberately limited to the selected callee, its
/// source argument expressions, and the call's source state identity; it
/// does not retain a C state or an ambient fact set.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CallRequirementSite {
    pub(crate) callee: String,
    pub(crate) reference_binding: Option<ReferenceBindingContract>,
    /// Original indirect invocation, distinct from the selected concrete target.
    pub(crate) source_callee: Option<std::sync::Arc<str>>,
    pub(crate) value_arguments: std::sync::Arc<[(String, ProgramValue)]>,
    pub(crate) resource_arguments: std::sync::Arc<[(String, ResourceBinder, ResourceBinder)]>,
    pub(crate) interface: std::sync::Arc<str>,
    pub(crate) candidate_ordinal: usize,
    pub(crate) source_arguments: std::sync::Arc<Vec<ProgramExpression>>,
    /// Enclosing runtime invocation when this requirement belongs to its
    /// worker. `source_arguments` still names the worker's actual arguments.
    pub(crate) source_invocation_arguments: Option<std::sync::Arc<Vec<ProgramExpression>>>,
    pub(crate) source_memory_state: MemoryStateIdentity,
}

impl CallRequirementSite {
    pub(crate) fn for_requirement(
        callee: impl Into<String>,
        interface: &str,
        candidate_ordinal: usize,
        source_arguments: &[ProgramExpression],
        source_memory: &SymbolicMemory,
    ) -> Self {
        #[cfg(test)]
        CALL_REQUIREMENT_SITE_CONSTRUCTION_COUNT.with(|count| {
            count.set(count.get().saturating_add(1));
        });
        Self {
            callee: callee.into(),
            reference_binding: None,
            source_callee: None,
            value_arguments: std::sync::Arc::from([]),
            resource_arguments: std::sync::Arc::from([]),
            interface: std::sync::Arc::from(interface),
            candidate_ordinal,
            source_arguments: std::sync::Arc::new(source_arguments.to_vec()),
            source_invocation_arguments: None,
            source_memory_state: MemoryStateIdentity::of(source_memory),
        }
    }

    pub(crate) fn with_reference_binding(
        mut self,
        binding: Option<&ReferenceBindingContract>,
    ) -> Self {
        self.reference_binding = binding.cloned();
        self
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
    /// The checked resource clause that requires a symbolic range's bytes
    /// to be initialized at the call.
    pub(crate) initialization_clause: Option<usize>,
    /// Exact state identity of the source-side load carrier, when this
    /// requirement is stateful and its lowering registered one.  This is
    /// separate from `site.source_memory_state`, which identifies the caller's
    /// frontier and must remain stable for source lookup.
    pub(crate) source_load_state: Option<MemoryStateIdentity>,
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
        source_load_state: Option<MemoryStateIdentity>,
    ) -> Self {
        Self {
            site,
            requirement_ordinal,
            source_requirement_ordinal,
            initialization_clause: None,
            source_load_state,
            // Generated requirements and contracts without a source registry
            // must never advertise source-side capabilities.
            source_requirement_is_state_independent: source_requirement_ordinal.is_some()
                && source_requirement_is_state_independent,
        }
    }

    pub(crate) fn with_initialization_clause(mut self, index: usize) -> Self {
        self.initialization_clause = Some(index);
        self
    }
}

impl std::ops::Deref for CallRequirementSource {
    type Target = CallRequirementSite;

    fn deref(&self) -> &Self::Target {
        &self.site
    }
}

impl std::ops::Deref for SharedMemory {
    type Target = SymbolicMemory;

    fn deref(&self) -> &SymbolicMemory {
        &self.memory
    }
}

impl AsRef<SymbolicMemory> for SharedMemory {
    fn as_ref(&self) -> &SymbolicMemory {
        &self.memory
    }
}

impl From<SymbolicMemory> for SharedMemory {
    fn from(memory: SymbolicMemory) -> Self {
        intern_memory(memory)
    }
}

impl From<&SymbolicMemory> for SharedMemory {
    fn from(memory: &SymbolicMemory) -> Self {
        intern_memory_ref(memory)
    }
}

/// How a memory state was produced from an earlier one: the edges of the
/// named-memory-state DAG (`docs/internals/memory-dag.md`). Each
/// variant names its base state, so following `base` walks backwards
/// through the write history that execution already knew when it built the
/// state — instead of reconstructing that history at proof time from
/// recorded effect facts.
///
/// A derivation is **advisory**. It only ever states a true fact about how a
/// state arose, so every consumer must fall back to its previous
/// reasoning when none is present; nothing may depend on one existing. That
/// is why a state interned on another thread (the arena is thread-local)
/// is merely slower to reason about rather than wrong.
///
/// `LoopHavoc` is deliberately its own edge kind rather than a bulk store.
/// Interface havoc has no checked write set, so no load-preservation walk may
/// cross that form. Verified whole-loop effects may carry a checked write set;
/// those edges are crossed only with range-disjointness evidence. Enforcing
/// that at the edge is how havoc identity survives this arc by construction,
/// upstream of any state comparison (see conventions.md's soundness trap).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MemoryDerivation {
    /// `base` with one cell written. Aliasing between the written cell and
    /// a later load is decided in the querying proof context, never from
    /// facts captured on the edge: interning is first-wins on equal
    /// states, so an edge can be shared by paths with different
    /// assumptions.
    Store {
        base: SharedMemory,
        pointer: Address,
        value: StoredMemoryValue,
    },
    /// A write to the physical bytes of a bit-field representation. The
    /// successor may know only some bits, so this is no evidence for a
    /// load of the entire written byte.
    RepresentationWrite {
        base: SharedMemory,
        pointer: Address,
        bytes: u32,
    },
    /// `base` with one block declared; no cell changes, so every load reads
    /// exactly what it read in `base`. This fourth edge kind was added after
    /// the initial DAG arc; without it, block declaration split the DAG into
    /// disjoint components ("arena identity is connected, arena derivations
    /// are not"). The havoc producers insert their marker
    /// blocks directly rather than through [`SymbolicMemory::with_block`], so this
    /// edge can never alias a havoc hop.
    BlockDeclared {
        base: SharedMemory,
        block: AddressBase,
    },
    /// `base` with one fresh, uninitialized heap block made live.
    HeapAllocated {
        base: SharedMemory,
        block: AddressBase,
        bytes: OldMachineTerm,
    },
    /// `base` with one unresolved allocation result registered. Pending
    /// metadata changes no program-observable memory, so every existing load
    /// is preserved across this edge.
    HeapAllocationPending {
        base: SharedMemory,
        allocation_base: Address,
        bytes: OldMachineTerm,
    },
    /// `base` with a failed pending allocation removed. No storage was
    /// allocated or written; existing reads retain their validity and value.
    HeapAllocationFailed { base: SharedMemory },
    /// `base` with only the allocation claims imported from contracts
    /// changed. Consuming an input claim and installing an output claim do
    /// not write bytes, allocate storage, or free storage, so every load is
    /// preserved across this edge.
    ContractAllocationClaimsChanged { base: SharedMemory },
    /// `base` after an input allocation claim was consumed by a contract
    /// that does not decide continuity. The callee may have freed the object,
    /// so cached contents and status for that allocation cannot cross this
    /// edge even though no definite C `free` is asserted.
    ContractAllocationRetired {
        base: SharedMemory,
        allocation_base: Address,
        bytes: OldMachineTerm,
    },
    /// `base` with one complete heap allocation lifetime ended.
    ///
    /// `allocation_base` is kept rather than only its broad address base:
    /// allocations imported from contracts can be subranges of external
    /// memory, where retiring the whole `ExternalArgument` block would also
    /// deallocate unrelated objects.
    HeapFreed {
        base: SharedMemory,
        allocation_base: Address,
        bytes: OldMachineTerm,
    },
    /// `base` with only the initialized-byte record extended. The writes
    /// establishing those bytes have their own earlier edges; recording this
    /// metadata changes no stored value and must not disconnect that history.
    ObjectInitializationRecorded {
        base: SharedMemory,
        pointer: Address,
        bytes: u32,
        /// The kind of complete integer cell initialized by a checked
        /// call output whose value is unknown.
        call_output: Option<LoadKind>,
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
    CellsForgotten { base: SharedMemory },
    /// Cache a value observed in `base`; no bytes or lifetime facts change.
    CellObserved { base: SharedMemory },
    /// `base` after a loop body that may write anything it can reach.
    ///
    /// `mutable_ranges` is present only when the loop's whole-effect summary
    /// supplied a checked footprint. `None` remains an unconditional barrier;
    /// `Some(empty)` is a checked no-write footprint.
    LoopHavoc {
        base: SharedMemory,
        variable: Variable,
        mutable_ranges: Option<Vec<MemoryRange>>,
        /// Flat ownership withheld from the body by its checked resource
        /// partition, even where an iterated footprint over-approximates writes.
        kept_by_function: Option<CallKeptRanges>,
    },
    /// `base` after an automatic-storage object's lifetime ended. The block
    /// is named so the memory-DAG can preserve unrelated loads while stopping
    /// every load through an alias to this retired object.
    LocalLifetimeEnded {
        base: SharedMemory,
        block: AddressBase,
    },
    /// A memory abstraction of all incoming branch states. A read crosses
    /// only with typed evidence that every incoming memory agrees with `base`
    /// on the complete access. The constructor retains all inputs in the
    /// state identity; this edge carries no branch-local assumptions.
    BranchJoin {
        base: SharedMemory,
        incoming: Vec<SharedMemory>,
    },
    /// `base` after a call that may write only within `mutable_ranges`.
    ///
    /// Preservation of a load outside those ranges must be justified in the
    /// querying proof context. Two paths with different assumptions (for
    /// example `length == 0` and `length == 1`) can produce this exact
    /// state, so no path's assumptions may be attached to the edge.
    ///
    /// `kept_by_caller` is the owned memory the caller kept outside the
    /// transfer, when it held any: the one-layer bodies of its residual owned
    /// instances and composites, and every flat owned residual member in a
    /// block the write set may alias, whether or not its cell was cached.
    /// The callee cannot write a byte of it, since owned memory is a
    /// partition at the call; the write-set marker spells these ranges, so
    /// the edge is shared only by paths that kept the same memory.
    CallHavoc {
        base: SharedMemory,
        variable: Variable,
        mutable_ranges: Vec<MemoryRange>,
        kept_by_caller: Option<CallKeptRanges>,
        /// The resource every write of the call lies inside, when its
        /// contract bounds its writes by the inputs it consumes and borrows
        /// rather than by ranges alone: `list(child)` for a call that
        /// consumes `list(child)`. The call's write footprint is its
        /// `mutable_ranges`, inside this resource.
        resource_bound: Option<std::sync::Arc<Resource>>,
    },
    /// `base` with a run of seeded cells added: exactly the stores, in
    /// element order, of each slot the run held live when it was seeded
    /// ([`CellRun`]). One edge stands for the whole run so that seeding a
    /// constant range costs the same whatever its length; every consumer
    /// reads it as that sequence of stores (`Self::seeded_stores`).
    CellsSeeded {
        base: SharedMemory,
        run: std::sync::Arc<CellRun>,
    },
}

impl MemoryDerivation {
    /// The physical destination of a single checked write. A representation
    /// write names a footprint without supplying a whole-byte value.
    pub(in crate::kernel) fn single_write(&self) -> Option<(&Address, u32)> {
        match self {
            Self::Store { pointer, value, .. } => Some((pointer, value.byte_width())),
            Self::RepresentationWrite { pointer, bytes, .. } => Some((pointer, *bytes)),
            _ => None,
        }
    }

    /// [`Self::single_write`] with the write's extent: a stored value of an
    /// abstract type reaches its whole object, `sizeof(T)` bytes.
    pub(in crate::kernel) fn single_write_extent(&self) -> Option<(&Address, AccessExtent)> {
        match self {
            Self::Store { pointer, value, .. }
                if let ProgramValue::Parameter(term) = value.native() =>
            {
                Some((pointer, AccessExtent::of_algebraic(&term.algebraic_type)))
            }
            _ => self
                .single_write()
                .map(|(pointer, bytes)| (pointer, AccessExtent::Bytes(bytes))),
        }
    }

    /// The stores a `CellsSeeded` edge stands for, newest first: the order a
    /// walk from the produced state meets them in. `None` for every other
    /// edge kind.
    pub(crate) fn seeded_stores(&self) -> Option<Vec<(Address, ProgramValue)>> {
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
    /// without carrying a state.
    pub(crate) fn kind_name(&self) -> &'static str {
        match self {
            Self::CellsSeeded { .. } => "CellsSeeded",
            Self::Store { .. } => "Store",
            Self::RepresentationWrite { .. } => "RepresentationWrite",
            Self::BlockDeclared { .. } => "BlockDeclared",
            Self::HeapAllocated { .. } => "HeapAllocated",
            Self::HeapAllocationPending { .. } => "HeapAllocationPending",
            Self::HeapAllocationFailed { .. } => "HeapAllocationFailed",
            Self::ContractAllocationClaimsChanged { .. } => "ContractAllocationClaimsChanged",
            Self::ContractAllocationRetired { .. } => "ContractAllocationRetired",
            Self::HeapFreed { .. } => "HeapFreed",
            Self::ObjectInitializationRecorded { .. } => "ObjectInitializationRecorded",
            Self::CellsForgotten { .. } => "CellsForgotten",
            Self::CellObserved { .. } => "CellObserved",
            Self::LocalLifetimeEnded { .. } => "LocalLifetimeEnded",
            Self::LoopHavoc { .. } => "LoopHavoc",
            Self::CallHavoc { .. } => "CallHavoc",
            Self::BranchJoin { .. } => "BranchJoin",
        }
    }

    /// The state this one was derived from.
    pub fn base(&self) -> &SharedMemory {
        match self {
            Self::Store { base, .. }
            | Self::RepresentationWrite { base, .. }
            | Self::BlockDeclared { base, .. }
            | Self::HeapAllocated { base, .. }
            | Self::HeapAllocationPending { base, .. }
            | Self::HeapAllocationFailed { base }
            | Self::ContractAllocationClaimsChanged { base }
            | Self::ContractAllocationRetired { base, .. }
            | Self::HeapFreed { base, .. }
            | Self::ObjectInitializationRecorded { base, .. }
            | Self::CellsForgotten { base }
            | Self::CellObserved { base }
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
struct MemoryArena {
    /// Arena ID and content hash. The table looks up candidates by hash and
    /// checks their exact contents, using a common base when the caller has one.
    identities: hashbrown::HashTable<(u32, u64)>,
    shallow_identities: std::collections::HashMap<MemoryShallowIdentity, (u32, u64)>,
    /// SymbolicMemory states whose storage roots were registered in `shallow_identities`
    /// on a structural hit. Holding them keeps those roots allocated, so a
    /// registered address cannot be reused by a different map. Each pin is
    /// an O(1) handle clone.
    shallow_pins: Vec<SymbolicMemory>,
    memories: Vec<std::sync::Arc<SymbolicMemory>>,
    /// The recorded children of each base, by the child's content hash: a
    /// derivation re-run from the same base (planning and then checking one
    /// statement, say) is recognized here by comparing its changes from the
    /// base, instead of its whole content, before the structural lookup.
    derived_children: std::collections::HashMap<(u32, u64), Vec<u32>>,
    /// Indexed by arena id; `None` for entry states and for any state
    /// whose first interning did not come from a recorded edge.
    derivations: Vec<Option<std::sync::Arc<MemoryDerivation>>>,
    /// Indexed by arena id: the first program point whose state this memory
    /// was, set when the point is made. Weak, because a point holds its
    /// memory. Only metadata: it changes no identity.
    occurrences: Vec<Option<std::sync::Weak<program_point::PointNode>>>,
    /// Immutable load-congruence keys. Producers reuse the base's key only
    /// for an unconditional byte-preserving transition. No history is queried.
    read_identities: Vec<u32>,
    /// Producer-maintained local-object versions; queries never walk history.
    local_definedness_versions: Vec<LocalDefinednessVersions>,
    /// Block versions follow the same first-recorded edges as derivations.
    static_block_versions: Vec<Option<StaticBlockVersions>>,
    /// Fixed-offset stores and checked call ranges on the cell walk's byte sources.
    static_cell_versions: Vec<Option<StaticCellVersions>>,
}

impl MemoryArena {
    fn memory_handle(&self, arena: u32, id: u32) -> SharedMemory {
        let memory = self.memories[id as usize].clone();
        let (_, content_hash) = self.shallow_identities[&MemoryShallowIdentity::of(&memory)];
        SharedMemory {
            arena,
            id,
            content_hash,
            memory,
        }
    }

    fn record_static_cell_versions(&mut self, step: &MemoryDerivation, id: u32) {
        // The cell walk normalizes the base to the retained bytes source
        // after each hop. Index exactly that chain.
        let before = self.read_identities[step.base().id as usize];
        let previous = &self.static_cell_versions[before as usize];
        let mut index = previous.clone().unwrap_or_else(|| StaticCellVersions {
            boundary: before,
            changed: Default::default(),
        });
        if let Some((pointer, bytes)) = step.single_write() {
            // A recorded local block is distinct from every static block.
            if pointer.base.is_local_block() {
                self.static_cell_versions[id as usize] = previous.clone();
                return;
            }
            let Some(span) = static_cell_byte_span(pointer, bytes) else {
                return;
            };
            index.update_block(&pointer.base, |block| {
                for byte in span {
                    block.stores.insert(byte, id);
                }
            });
        } else if let MemoryDerivation::CallHavoc { mutable_ranges, .. } = step {
            for range in mutable_ranges {
                crate::instrumentation::record_deterministic_work(1);
                let (start, end) = range.bound_terms();
                if start == end {
                    continue;
                }
                let Some((span, alignment)) = static_call_range(range) else {
                    return;
                };
                index.update_block(&range.base().base, |block| {
                    block.calls.ranges.write(span, id);
                    block.calls.by_alignment[alignment] = Some(id);
                });
            }
        } else {
            return;
        }
        self.static_cell_versions[id as usize] = Some(index);
    }
}

#[derive(Clone)]
struct StaticCellVersions {
    boundary: u32,
    changed: PersistentMap<AddressBase, StaticCellWrites>,
}

impl StaticCellVersions {
    fn update_block(&mut self, base: &AddressBase, update: impl FnOnce(&mut StaticCellWrites)) {
        let mut block = self.changed.get(base).cloned().unwrap_or_default();
        update(&mut block);
        self.changed.insert(base.clone(), block);
    }
}

#[derive(Clone, Default)]
struct StaticCellWrites {
    // A scalar touches at most MAX_SCALAR_ACCESS_BYTES keys. Each key keeps
    // the most recent store to that byte, even after a partial overwrite.
    stores: PersistentMap<i64, u32>,
    calls: StaticCallWrites,
}

#[derive(Clone, Default)]
struct StaticCallWrites {
    ranges: cell_version_intervals::CellVersionIntervals,
    // Latest call requiring each alignment (1, 2, 4, 8 or 16 bytes). The
    // existing constant separation rule requires an exact element index.
    by_alignment: [Option<u32>; 5],
}

impl StaticCallWrites {
    fn latest_candidate(&self, span: &std::ops::Range<i64>) -> Option<u32> {
        if span.end > i64::from(i32::MAX) {
            return self.by_alignment.iter().copied().max().flatten();
        }
        let start = span.start as u32;
        let alignments = start.trailing_zeros().min(4) as usize;
        let unaligned = self.by_alignment[alignments + 1..]
            .iter()
            .copied()
            .max()
            .flatten();
        unaligned.max(self.ranges.latest(start..span.end as u32))
    }
}

pub(in crate::kernel) enum StaticCellVersion {
    Written(SharedMemory),
    Boundary(SharedMemory),
}

/// Keep the constant element geometry that the legacy call separator uses.
/// Unknown blocks, offsets, bounds, or shapes leave an ordinary walk boundary.
fn static_call_range(range: &MemoryRange) -> Option<(std::ops::Range<u32>, usize)> {
    let OffsetView::Constant(base) = range.base().offset.view() else {
        return None;
    };
    let width = range.element_width();
    if !range.base().base.is_static_storage_block()
        || range.wide_bounds().is_some()
        || !width.is_power_of_two()
        || i64::from(width) > MAX_SCALAR_ACCESS_BYTES
        || i32::try_from(base).ok()? < 0
        || base % i64::from(width) != 0
    {
        return None;
    }
    let (start, end) = resource_algebra::concrete_memory_range_bounds(range)?;
    Some((
        u32::try_from(start).ok()?..u32::try_from(end).ok()?,
        width.trailing_zeros() as usize,
    ))
}

fn static_cell_byte_span(pointer: &Address, bytes: u32) -> Option<std::ops::Range<i64>> {
    let OffsetView::Constant(start) = pointer.offset.view() else {
        return None;
    };
    let bytes = i64::from(bytes);
    if !pointer.base.is_static_storage_block()
        || start < 0
        || !(1..=MAX_SCALAR_ACCESS_BYTES).contains(&bytes)
    {
        return None;
    }
    Some(start..start.checked_add(bytes)?)
}

#[derive(Clone)]
struct LocalDefinednessVersions {
    base: u32,
    changed: crate::persistent::PersistentMap<AddressBase, u32>,
}

impl LocalDefinednessVersions {
    fn fresh(base: u32) -> Self {
        Self {
            base,
            changed: Default::default(),
        }
    }
}

#[derive(Clone)]
enum StaticBlockVersionAnchor {
    Root(SharedMemory),
    Barrier(SharedMemory),
    /// Loaded pointers can be structurally separate via their stored value.
    Unclassified(SharedMemory),
}

#[derive(Clone)]
struct StaticBlockVersions {
    anchor: StaticBlockVersionAnchor,
    changed: crate::persistent::PersistentMap<AddressBase, SharedMemory>,
}

impl StaticBlockVersions {
    fn after(previous: Option<&Self>, step: &MemoryDerivation, produced: &SharedMemory) -> Self {
        use crate::kernel::resource_tracker::step_effect::{
            BlockVersionEffect, block_version_effect,
        };
        let mut versions = previous.cloned().unwrap_or_else(|| Self {
            anchor: StaticBlockVersionAnchor::Root(step.base().clone()),
            changed: Default::default(),
        });
        match block_version_effect(step) {
            BlockVersionEffect::Object(block, _) => versions.record_object(block, produced),
            BlockVersionEffect::WriteSet(ranges) => {
                for range in ranges {
                    crate::instrumentation::record_deterministic_work(1);
                    versions.record_object(&range.base().base, produced);
                    if matches!(versions.anchor, StaticBlockVersionAnchor::Barrier(ref memory)
                        if memory.arena_id() == produced.arena_id())
                    {
                        break;
                    }
                }
            }
            BlockVersionEffect::Unchanged => {}
            BlockVersionEffect::Barrier => versions.end_at(produced, true),
        }
        versions
    }

    fn record_object(&mut self, block: &AddressBase, produced: &SharedMemory) {
        match block {
            block if block.is_static_storage_block() => {
                self.changed.insert(block.clone(), produced.clone());
            }
            // These variants are proven distinct from both forms of static
            // storage (StaticObject and the legacy Concrete names).
            AddressBase::Concrete(_)
            | AddressBase::StringLiteral { .. }
            | AddressBase::Heap(_)
            | AddressBase::Temporary(_)
            | AddressBase::AutomaticLocal { .. }
            | AddressBase::ReferenceCarrier { .. }
            | AddressBase::SliceLength { .. }
            | AddressBase::AggregateReturn { .. }
            | AddressBase::ContractResult
            | AddressBase::ContractException => {}
            AddressBase::Load(_) => self.end_at(produced, false),
            _ => self.end_at(produced, true),
        }
    }

    fn end_at(&mut self, produced: &SharedMemory, definite: bool) {
        self.anchor = if definite {
            StaticBlockVersionAnchor::Barrier(produced.clone())
        } else {
            StaticBlockVersionAnchor::Unclassified(produced.clone())
        };
        self.changed = Default::default();
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct MemoryShallowIdentity {
    blocks: usize,
    cells: usize,
    union_cells: usize,
    forgotten: usize,
    heap: usize,
}

impl MemoryShallowIdentity {
    fn of(memory: &SymbolicMemory) -> Self {
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
    static C_MEMORY_ARENA: std::cell::RefCell<(u32, MemoryArena)> = std::cell::RefCell::new((
        NEXT_MEMORY_ARENA_TOKEN.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
        MemoryArena::default(),
    ));
    static C_MEMORY_DERIVATION_GENERATION: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Replaces this thread's memory arena with an empty one under a fresh
/// token. SymbolicMemory states interned before keep comparing by content but lose
/// their derivations, so nothing recorded for an earlier verification can
/// answer a DAG walk in a later one. Called by [`super::VerificationSession`]
/// at the outermost verification entry; see its documentation.
/// This thread's memory arena as one value: its token, every interned
/// state with its derivation, and the derivation generation. Clones share
/// the states' storage, so a capture costs one handle per arena entry.
#[derive(Clone)]
pub(super) struct MemoryArenaState {
    arena: (u32, MemoryArena),
    derivation_generation: u64,
}

/// How many entries the arena holds: interned states and pinned roots.
#[cfg(test)]
pub(super) fn memory_arena_entry_count() -> usize {
    C_MEMORY_ARENA.with(|arena| {
        let arena = arena.borrow();
        arena.1.memories.len() + arena.1.shallow_pins.len()
    })
}

pub(super) fn capture_memory_arena() -> MemoryArenaState {
    MemoryArenaState {
        arena: C_MEMORY_ARENA.with(|arena| arena.borrow().clone()),
        derivation_generation: C_MEMORY_DERIVATION_GENERATION.with(std::cell::Cell::get),
    }
}

/// Reinstalls a captured arena under its own token, so every state id the
/// capture's holder kept still names the same state and derivation, and
/// nothing interned since remains.
pub(super) fn restore_memory_arena(state: &MemoryArenaState) {
    C_MEMORY_ARENA.with(|arena| *arena.borrow_mut() = state.arena.clone());
    C_MEMORY_DERIVATION_GENERATION.with(|generation| generation.set(state.derivation_generation));
}

/// Scope native import memo keys to the active state arena. Global shared
/// syntax identities remain independent; a cache lookup must not compare the
/// contents of states owned by different verification sessions.
fn memory_arena_token() -> u32 {
    C_MEMORY_ARENA.with(|arena| arena.borrow().0)
}

pub(super) fn start_fresh_memory_arena() {
    C_MEMORY_ARENA.with(|arena| {
        *arena.borrow_mut() = (
            NEXT_MEMORY_ARENA_TOKEN.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
            MemoryArena::default(),
        );
    });
}

/// Bumped every time a derivation slot is filled on a state that was
/// interned before the edge was recorded. Memo tables over DAG walks key on
/// this so an edge recorded later invalidates earlier "no path" answers
/// instead of leaving them stale.
///
/// A recording that interns the state it derives does not bump it: no
/// earlier question could name that state, and an existing state's
/// history never changes, so no earlier answer can. Bumping on those too
/// emptied every negative memo at every program step, and a call step re-ran
/// each failed alias question its walks had already answered.
pub(super) fn memory_derivation_generation() -> u64 {
    C_MEMORY_DERIVATION_GENERATION.with(std::cell::Cell::get)
}

/// Interns `memory` as the base of a derivation about to be applied to it,
/// and replaces it with the arena's canonical storage for that content (an
/// O(1) handle clone). Every recorded result is therefore derived from its
/// base's canonical storage and shares every unchanged subtree with it, which
/// is what lets [`record_memory_derivation`] compare a re-derived result
/// against an earlier child of the same base along the changed paths only.
pub(crate) fn intern_derivation_base(memory: &mut SymbolicMemory) -> SharedMemory {
    let base = intern_memory_ref(memory);
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
/// canonical instance forward means every later state derived from this
/// one shares storage roots with whatever the arena already holds, so facts
/// and terms that embed equal states compare by root identity.
pub(crate) fn record_memory_derivation(result: &mut SymbolicMemory, derivation: MemoryDerivation) {
    let variable_base = derivation.base().clone();
    let derivation = Arc::new(derivation);
    let names_existing_cells = match derivation.as_ref() {
        MemoryDerivation::CellObserved { .. } => true,
        MemoryDerivation::CellsSeeded { base, run } => {
            matches!(run.value_mode(), cell_store::RunValueMode::Load)
                && (run.element_width() == run.value_width()
                    || (run.element_width() > run.value_width()
                        && run.element_type() != ProgramType::Bool))
                && base.read_identity() == run.source().read_identity()
        }
        _ => false,
    };
    // The log this value carries from the path that made it; the step is
    // added once the result's arena identity is known.
    let inherited = result.pending_steps.take();
    result.construction = Some(Arc::new(MemoryConstruction {
        roots: result.diagnostic_roots(),
        kind: MemoryConstructionKind::Transition(derivation.clone()),
    }));
    if let Some(child) = recorded_child_matching(result, derivation.base()) {
        // Already this base's recorded child: its derivation slot is filled,
        // so recording would change nothing but the storage handed back.
        *result = child;
        let produced = intern_memory_ref(result);
        result.pending_steps = Some(program_point::StepLog::push(
            inherited,
            derivation.clone(),
            produced,
            names_existing_cells,
        ));
        return;
    }
    // Interning borrows the arena, so it has to finish before the write.
    let read_identity = match derivation.as_ref() {
        MemoryDerivation::CellsForgotten { base }
        | MemoryDerivation::BlockDeclared { base, .. }
        | MemoryDerivation::ObjectInitializationRecorded { base, .. } => {
            // Declaration/initialization metadata writes no values. Keep the
            // bytes' identity; type, lifetime and access use this state.
            Some(base.read_identity())
        }
        // Naming the same bytes includes runs copied from an equivalent
        // earlier source, even if their cache entries differ.
        _ if names_existing_cells => Some(variable_base.read_identity()),
        _ => None,
    };
    // A state this call interns is one no query has seen yet, so filling
    // its derivation cannot change an earlier answer.
    let next_id = C_MEMORY_ARENA.with(|arena| arena.borrow().1.memories.len());
    let derived = intern_memory_ref_with_read_identity(result, read_identity);
    let interned_here = derived.id as usize >= next_id;
    if !result.same_storage_roots(derived.memory()) {
        *result = derived.memory().clone();
    }
    result.pending_steps = Some(program_point::StepLog::push(
        inherited,
        derivation.clone(),
        derived.clone(),
        names_existing_cells,
    ));
    C_MEMORY_ARENA.with(|arena| {
        let mut arena = arena.borrow_mut();
        if arena.0 != derived.arena || arena.0 != derivation.base().arena {
            return;
        }
        let arena = &mut arena.1;
        // Set once, before a newly interned state can escape this producer.
        // A concrete local store cannot affect another automatic object.
        // Forgetting cached values changes knowledge, not initialized bytes
        // or lifetimes. All other effects conservatively retain a fresh key.
        if interned_here {
            let versions = match derivation.as_ref() {
                MemoryDerivation::Store { base, pointer, .. }
                | MemoryDerivation::RepresentationWrite { base, pointer, .. }
                    if pointer.base.is_local_block() =>
                {
                    let mut versions = arena.local_definedness_versions[base.id as usize].clone();
                    versions.changed = versions
                        .changed
                        .with_inserted(pointer.base.clone(), derived.id);
                    Some(versions)
                }
                MemoryDerivation::CellsForgotten { base } => {
                    Some(arena.local_definedness_versions[base.id as usize].clone())
                }
                _ => None,
            };
            if let Some(versions) = versions {
                arena.local_definedness_versions[derived.id as usize] = versions;
            }
        }
        if arena.derivations[derived.id as usize].is_some() {
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
        arena.static_block_versions[derived.id as usize] = Some(StaticBlockVersions::after(
            arena.static_block_versions[base_id as usize].as_ref(),
            &derivation,
            &derived,
        ));
        arena.record_static_cell_versions(&derivation, derived.id);
        arena.derivations[derived.id as usize] = Some(derivation);
        arena
            .derived_children
            .entry((base_id, derived.content_hash))
            .or_default()
            .push(derived.id);
        if !interned_here {
            C_MEMORY_DERIVATION_GENERATION.with(|generation| generation.set(generation.get() + 1));
        }
    });
    crate::kernel::reasoning::advance_memory_variable_index(&variable_base, &derived);
}

/// The canonical storage of a recorded child of `base` equal to `result`,
/// when there is one.
///
/// `result` was derived from `base`'s canonical storage
/// ([`intern_derivation_base`]) and so was every recorded child, so both share
/// all of `base` that their updates did not touch and the comparison walks
/// only the changed paths. The answer is exact either way.
fn recorded_child_matching(result: &SymbolicMemory, base: &SharedMemory) -> Option<SymbolicMemory> {
    let content_hash = memory_content_hash(result);
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

/// A content hash of `memory` for ordering: the components' cached hashes
/// combined by a multiply-rotate mix rather than SipHash, which costs more
/// than the rest of a comparison and runs twice per comparison. Like the
/// content hash it depends only on the entries, so it is deterministic and
/// equal for equal states; a collision costs only the structural walk.
fn memory_ordering_key(memory: &SymbolicMemory) -> u64 {
    use std::hash::{Hash, Hasher};
    #[derive(Default)]
    struct OrderingHasher(u64);
    impl Hasher for OrderingHasher {
        fn finish(&self) -> u64 {
            self.0
        }
        fn write(&mut self, bytes: &[u8]) {
            for chunk in bytes.chunks(8) {
                let mut word = [0u8; 8];
                word[..chunk.len()].copy_from_slice(chunk);
                self.write_u64(u64::from_le_bytes(word));
            }
        }
        fn write_u64(&mut self, word: u64) {
            self.0 = (self.0.rotate_left(5) ^ word).wrapping_mul(0x517c_c1b7_2722_0a95);
        }
        fn write_usize(&mut self, word: usize) {
            self.write_u64(word as u64);
        }
    }
    let mut hasher = OrderingHasher::default();
    memory.hash(&mut hasher);
    hasher.finish()
}

fn memory_content_hash(memory: &SymbolicMemory) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    memory.hash(&mut hasher);
    hasher.finish()
}

/// The component collections a state hashes: three memory maps, the
/// ended-lifetime set, the nine heap collections, and the forget mark.
const C_MEMORY_HASHED_COMPONENTS: usize = 14;

/// Charges a structural arena lookup. Hashing is O(1) per component because
/// each collection caches its content hash; the comparison a bucket hit
/// performs is charged by the collections' own `eq`, per element actually
/// compared, and is O(1) for states sharing their persistent roots.
fn record_memory_structural_lookup_work() {
    crate::instrumentation::record_deterministic_work(C_MEMORY_HASHED_COMPONENTS);
}

/// Interns a memory state in the thread-local arena. Structurally equal
/// states interned on the same thread share one allocation and identity;
/// states that cross threads still compare correctly through the content
/// hash and structural fallback.
pub fn intern_memory(memory: SymbolicMemory) -> SharedMemory {
    intern_memory_with(std::borrow::Cow::Owned(memory), None, None)
}

/// The interned state `memory` is the canonical storage of, found by its
/// storage roots alone, or `None`. Interns nothing and compares no content:
/// a state a derivation produced carries its interned storage forward
/// ([`record_memory_derivation`]), so a live state's memory is found here
/// in O(1), and any other memory is left to the caller.
pub(crate) fn interned_storage_of(memory: &SymbolicMemory) -> Option<SharedMemory> {
    C_MEMORY_ARENA.with(|arena| {
        let arena = arena.borrow();
        let (token, arena) = &*arena;
        let (id, content_hash) = arena
            .shallow_identities
            .get(&MemoryShallowIdentity::of(memory))
            .copied()?;
        Some(SharedMemory {
            arena: *token,
            id,
            content_hash,
            memory: arena.memories[id as usize].clone(),
        })
    })
}

/// Interns by reference: an already-interned state is found without
/// cloning it, so hot memoization lookups keyed by interned identity pay a
/// hash and comparison but no allocation.
pub fn intern_memory_ref(memory: &SymbolicMemory) -> SharedMemory {
    intern_memory_ref_with_read_identity(memory, None)
}

/// First interning wins, including its read identity. Existing states never
/// change keys underneath registered applications; an earlier unannotated hit
/// conservatively loses this equality rather than requiring graph rescans.
fn intern_memory_ref_with_read_identity(
    memory: &SymbolicMemory,
    read_identity: Option<(u32, u32)>,
) -> SharedMemory {
    intern_memory_with(std::borrow::Cow::Borrowed(memory), None, read_identity)
}

fn intern_memory_with(
    memory: std::borrow::Cow<'_, SymbolicMemory>,
    base: Option<&SymbolicMemory>,
    read_identity: Option<(u32, u32)>,
) -> SharedMemory {
    C_MEMORY_ARENA.with(|arena| {
        let mut arena = arena.borrow_mut();
        let (token, arena) = &mut *arena;
        let shallow_identity = MemoryShallowIdentity::of(&memory);
        if let Some((id, content_hash)) = arena.shallow_identities.get(&shallow_identity).copied() {
            return SharedMemory {
                arena: *token,
                id,
                content_hash,
                memory: arena.memories[id as usize].clone(),
            };
        }
        record_memory_structural_lookup_work();
        let content_hash = memory_content_hash(&memory);
        if let Some(&(id, _)) = arena
            .identities
            .find(content_hash, |&(id, candidate_hash)| {
                if candidate_hash != content_hash {
                    return false;
                }
                let stored = &arena.memories[id as usize];
                match base {
                    Some(base) => memory.eq_relative_to(stored, base),
                    None => *memory == **stored,
                }
            })
        {
            // Remember the caller's storage roots, so the next lookup of this
            // same state is an O(1) shallow hit instead of another
            // comparison. The pin keeps those roots alive: a registered
            // address must never be freed and reused by different content.
            arena
                .shallow_identities
                .insert(shallow_identity, (id, content_hash));
            arena.shallow_pins.push(memory.into_owned());
            return SharedMemory {
                arena: *token,
                id,
                content_hash,
                memory: arena.memories[id as usize].clone(),
            };
        }
        let id = u32::try_from(arena.memories.len()).expect("memory arena exhausted");
        let mut stored = memory.into_owned();
        stored.pending_steps = None;
        let stored = std::sync::Arc::new(stored);
        arena
            .identities
            .insert_unique(content_hash, (id, content_hash), |&(_, hash)| hash);
        arena
            .shallow_identities
            .insert(shallow_identity, (id, content_hash));
        arena.memories.push(stored.clone());
        arena.derivations.push(None);
        arena.occurrences.push(None);
        arena.static_block_versions.push(None);
        arena.static_cell_versions.push(None);
        arena
            .local_definedness_versions
            .push(LocalDefinednessVersions::fresh(id));
        arena.read_identities.push(
            read_identity
                .filter(|(source_arena, source)| *source_arena == *token && *source < id)
                .map_or(id, |(_, source)| source),
        );
        SharedMemory {
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
    /// state. The creation root supplies its logical identity; this witness
    /// cannot supply resources to an execution or resource rewrite.
    pub(super) predicate_count_permissions: Option<PredicateCountPermissions>,

    /// Creation history is shared out-of-line to keep ExecutionState's recursive
    /// checker stack footprint unchanged. Legacy states use None.
    pub(super) creation: Option<super::population_authority::storage_creation::CreationEvents>,
}

/// Whether an aggregate return copies a value or completes caller storage.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum AggregateReturnMode {
    #[default]
    Copy,
    Construction,
}

/// Call metadata only. Selecting it grants neither storage nor ownership.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) struct AggregateDestination {
    pub(super) pointer: Address,
    pub(super) layout: AggregateLayout,
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ExecutionState {
    pub(super) aggregate_destination: Option<Arc<AggregateDestination>>,
    /// Lexical field values for scratch resource-body evaluation only.
    /// This is not ownership and is never populated by unfolding a resource.
    pub(super) instance_field_scope: ResourceContext,
    /// Call-local formal identities; the ledger retains actual caller identities.
    pub(super) resource_bindings: Option<std::sync::Arc<ResourceBindings>>,
    /// The fields of a resource definition evaluated without an instance,
    /// which [`InstanceRef::Body`] reads when no opened instance is bound.
    /// Scratch resource-body evaluation only, like `instance_field_scope`.
    pub(super) body_field_view: Option<Arc<ResourceInstance>>,
    pub(super) locals: LocalEnvironment,
    pub(super) memory: SymbolicMemory,
    /// The point this state's path has reached; not part of equality
    /// ([`program_point::PathLink`]).
    pub(super) point: program_point::PathLink,
    pub(super) resources: ResourceContext,
    /// Active stable-view authority. `None` is the canonical empty ledger so
    /// independently constructed states retain ordinary structural equality.
    pub(super) borrow_ledger: Option<super::borrows::BorrowLedger>,
    /// Holder identity for the authority carried by this state. Keeping it
    /// beside the immutable ledger lets nested candidate calls reuse the
    /// caller's participant when lending a view.
    pub(super) borrow_participant: Option<super::borrows::BorrowParticipantId>,
    /// Exact resource-occurrence bindings for live borrowed views. This map
    /// is carried with checked state so nested calls can reborrow by identity.
    pub(super) borrow_bindings: super::borrows::BorrowBindings,
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
    /// Resource families the proof has observed, for authority borrow
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
    /// The results of the calls a statement makes inside its expressions,
    /// by the call's number in its function, while that statement runs: the
    /// call step sets one, the rest of the statement reads it, and the
    /// statement's end drops what it read. `None` is the canonical state at
    /// every statement boundary.
    pub(crate) step_results: Option<Arc<PersistentMap<u32, StoredExecutionValue>>>,
    /// Anonymous aggregate storage created by expression steps, keyed by producer.
    pub(crate) aggregate_step_objects: crate::persistent::PersistentMap<u32, Address>,
    /// Literal values of this frame. Objects themselves have static storage duration.
    pub(crate) literal_values: Arc<PersistentMap<StringLiteralId, StoredExecutionValue>>,
}

/// A reference at a written call.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ReferenceBindingSlot {
    Receiver,
    Argument(usize),
}

/// One conversion between checked C++ record layouts.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CppObjectConversion {
    pub derived: Arc<str>,
    pub base: Arc<str>,
}

impl CppObjectConversion {
    pub(crate) fn new(derived: &str, base: &str) -> Self {
        Self {
            derived: derived.into(),
            base: base.into(),
        }
    }

    /// The private composite family used by the shared resource checker.
    /// This spelling cannot be a declared source identifier.
    pub(crate) fn loan_family(&self) -> String {
        format!("C++ reference loan ({:?}, {:?})", self.derived, self.base)
    }
}

#[derive(
    Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, serde::Serialize, serde::Deserialize,
)]
pub enum ReferenceBindingKind {
    AcquireMutable,
    ReleaseMutable,
    AcquireShared,
    ReleaseShared,
}

impl ReferenceBindingKind {
    pub(crate) const ALL: [Self; 4] = [
        Self::AcquireMutable,
        Self::ReleaseMutable,
        Self::AcquireShared,
        Self::ReleaseShared,
    ];

    pub(crate) fn acquire(shared: bool) -> Self {
        if shared {
            Self::AcquireShared
        } else {
            Self::AcquireMutable
        }
    }

    pub(crate) fn release(self) -> Self {
        match self {
            Self::AcquireMutable | Self::ReleaseMutable => Self::ReleaseMutable,
            Self::AcquireShared | Self::ReleaseShared => Self::ReleaseShared,
        }
    }

    fn description(self) -> &'static str {
        match self {
            Self::AcquireMutable => "mutable reference binding",
            Self::ReleaseMutable => "mutable reference release",
            Self::AcquireShared => "shared reference binding",
            Self::ReleaseShared => "shared reference release",
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CppBindingContract {
    pub conversion: CppObjectConversion,
    pub kind: ReferenceBindingKind,
}

impl CppBindingContract {
    pub(crate) fn release(&self) -> Self {
        Self {
            conversion: self.conversion.clone(),
            kind: self.kind.release(),
        }
    }
}

impl std::fmt::Display for CppBindingContract {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} from {} to {}",
            self.kind.description(),
            self.conversion.derived,
            self.conversion.base
        )
    }
}

#[derive(
    Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, serde::Serialize, serde::Deserialize,
)]
pub struct RustObjectConversion {
    pub record: String,
    pub trait_name: String,
}

impl RustObjectConversion {
    // A private composite family for the memory lent by a shared binding.
    // A source declaration cannot spell this key.
    pub(crate) fn loan_family(&self) -> String {
        format!(
            "Rust shared reference loan ({:?}, {:?})",
            self.record, self.trait_name
        )
    }
}

#[derive(
    Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, serde::Serialize, serde::Deserialize,
)]
pub struct RustBindingContract {
    pub conversion: RustObjectConversion,
    pub kind: ReferenceBindingKind,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ReferenceBindingContract {
    Cpp(CppBindingContract),
    Rust(RustBindingContract),
}

impl ReferenceBindingContract {
    pub(crate) fn release(&self) -> Self {
        match self {
            Self::Cpp(contract) => Self::Cpp(contract.release()),
            Self::Rust(contract) => Self::Rust(RustBindingContract {
                conversion: contract.conversion.clone(),
                kind: contract.kind.release(),
            }),
        }
    }
}

impl std::fmt::Display for ReferenceBindingContract {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Cpp(contract) => contract.fmt(f),
            Self::Rust(contract) => write!(
                f,
                "{} of <{} as {}>",
                contract.kind.description(),
                contract.conversion.record,
                contract.conversion.trait_name,
            ),
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ReferenceBindingOperation {
    pub contract: ReferenceBindingContract,
    pub source: Option<ReferenceBindingSource>,
}

/// The regions of a checked reference binding, relative to its acquisition.
/// Its lowering places all acquisitions before the call and releases after it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ReferenceBindingSource {
    pub slot: ReferenceBindingSlot,
    pub call_offset: usize,
    pub release_offset: usize,
}

/// The function pointer a call goes through, with its type.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Callee {
    pub pointer: ProgramExpression,
    pub pointer_type: ProgramType,
}

/// The expression that supplies a written closure.
#[derive(
    Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, serde::Serialize, serde::Deserialize,
)]
pub struct ClosureSite {
    pub(crate) statements: Vec<u32>,
    pub(crate) expression: ClosureExpression,
}

#[derive(
    Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, serde::Serialize, serde::Deserialize,
)]
pub enum ClosureExpression {
    Argument { call: u32, argument: u32 },
    Initializer,
}

/// What made a statement's step result.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum StepOrigin {
    /// The value of the GNU builtin `__builtin_constant_p`.
    BuiltinConstantP,
    /// A call of this function returned it.
    Call(String),
    /// It is this local's value before an assignment step replaced it, the
    /// value of a postfix `x++` or `x--`.
    Prior(String),
    /// An operator that decides between its operands took it.
    Operator(OperatorKind),
    /// A value step recorded it: what this describes, such as a statement
    /// expression's value.
    Value(&'static str),
}

/// An operator that decides which of its operands run.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum OperatorKind {
    /// `&&`
    And,
    /// `||`
    Or,
    /// The ternary operator, `c ? a : b`.
    Ternary,
}

impl ProgramExpression {
    /// The steps whose results evaluating this expression reads and ends.
    pub(crate) fn collect_step_results_read(&self, steps: &mut Vec<u32>) {
        match self {
            ProgramExpression::StepResult {
                step, ends: true, ..
            } => steps.push(*step),
            ProgramExpression::StepResult { ends: false, .. } => {}
            ProgramExpression::StringLiteral(_)
            | ProgramExpression::Value(_)
            | ProgramExpression::Variable(_)
            | ProgramExpression::FunctionAddress(_) => {}
            ProgramExpression::EnumConstruct { fields, .. } => {
                for field in fields {
                    field.collect_step_results_read(steps);
                }
            }
            ProgramExpression::Ternary {
                condition,
                then_branch,
                else_branch,
            } => {
                condition.collect_step_results_read(steps);
                then_branch.collect_step_results_read(steps);
                else_branch.collect_step_results_read(steps);
            }
            ProgramExpression::Cast { expression, .. }
            | ProgramExpression::Negate(expression)
            | ProgramExpression::FloatNegate(expression)
            | ProgramExpression::FloatClassification { expression, .. }
            | ProgramExpression::EnumField {
                value: expression, ..
            }
            | ProgramExpression::EnumIs {
                value: expression, ..
            }
            | ProgramExpression::SliceLength(expression)
            | ProgramExpression::SliceData(expression)
            | ProgramExpression::BitwiseNot(expression)
            | ProgramExpression::AddressOf(expression)
            | ProgramExpression::CheckedObjectAddress(expression)
            | ProgramExpression::Not(expression)
            | ProgramExpression::Load(expression)
            | ProgramExpression::PointerOffsetBytes {
                pointer: expression,
                ..
            }
            | ProgramExpression::Subobject {
                pointer: expression,
                ..
            }
            | ProgramExpression::TypedLoad {
                pointer: expression,
                ..
            } => expression.collect_step_results_read(steps),
            crate::kernel::binary_c_expression!(left, right)
            | ProgramExpression::SliceFromRawParts {
                data: left,
                count: right,
            } => {
                left.collect_step_results_read(steps);
                right.collect_step_results_read(steps);
            }
        }
    }
}

impl ExecutionState {
    /// Records the term call `call` of the running statement returned.
    pub(super) fn set_step_result(&mut self, call: u32, value: ProgramValue) {
        self.set_retained_step_result(call, value.into());
    }

    /// Keep the executed value through its statement-local handoff. Results
    /// are values, like locals and returns, not native memory cells; recording
    /// one must not export a retained arithmetic expression tree.
    pub(super) fn set_retained_step_result(
        &mut self,
        call: u32,
        value: crate::kernel::ExecutionValue,
    ) {
        let mut results = self.step_results.as_deref().cloned().unwrap_or_default();
        results.insert(call, value.into());
        self.step_results = Some(Arc::new(results));
    }

    /// The term call `call` of the running statement returned, once its call
    /// step has run.
    pub(crate) fn step_result(&self, call: u32) -> Option<&StoredExecutionValue> {
        self.step_results.as_ref()?.get(&call)
    }

    /// Ends the results of `steps`: their reader has read them.
    pub(super) fn end_step_results(&mut self, steps: &[u32]) {
        let Some(results) = &self.step_results else {
            return;
        };
        if !steps.iter().any(|step| results.contains_key(step)) {
            return;
        }
        let mut results = (**results).clone();
        for step in steps {
            results.remove(step);
        }
        self.step_results = (!results.is_empty()).then(|| Arc::new(results));
    }
}

#[derive(Clone)]
pub(super) struct PredicateCountPermissions(pub(super) std::sync::Arc<ResourceContext>);

// Permissions justify observing the count but do not change its value. The
// enclosing ExecutionState compares the captured creation root independently.
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

/// Call-local origins of residual memory owners, constructed by splitting.
/// Values name the original occurrence directly, never a predecessor chain.
#[derive(Clone, Default)]
pub(crate) struct MemorySplitOrigins {
    origins: PersistentMap<ResourceOccurrenceId, ResourceOccurrenceId>,
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

/// An immutable resource composition state.
///
/// One pointer-sized storage root keeps recursive execution frames shallow.
/// Forks share that root; a local insertion or removal replaces only the
/// logarithmic paths in the fact store and affected indexes.
#[derive(Default)]
pub struct ResourceContext {
    /// Path metadata for diagnostics and refold witness selection, omitted
    /// from semantic equality, hashing and ordering.
    /// A shared persistent root keeps clones constant-work and never copies facts.
    instance_consumptions: Option<std::sync::Arc<PersistentMap<InstanceId, InstanceConsumption>>>,
    /// Derived trusted-kernel index. It never supplies ownership evidence.
    memory_equalities: std::sync::Mutex<memory_equality_index::MemoryPairings>,
    pub(super) storage: std::sync::Arc<ResourceContextStorage>,
    /// Selected unfold custody, keyed by emitted occurrence. This is producer
    /// evidence for framing a body's exchange, never a geometric match.
    pub(super) framed_origins: PersistentMap<ResourceOccurrenceId, ResourceOccurrenceId>,
    /// Disposable projection, never ownership evidence or semantic identity.
    /// Immutable forks share even the cold cache; producers detach it before
    /// advancing only their own delta.
    pub(super) observable_projection:
        std::sync::Arc<std::sync::Mutex<Option<ObservableResourceProjection>>>,
    /// Checked dependency bundles for resource occurrences that are views of
    /// an active stable borrow.  This is deliberately separate from the
    /// resource algebra's support graph: equal resource terms can have
    /// different borrow origins, and a rewrite must preserve the opaque
    /// occurrence identity rather than rediscovering it from the term.
    pub(super) borrow_dependencies: std::sync::Arc<crate::kernel::borrows::BorrowBindingsState>,
    pub(super) structural_witnesses:
        Option<std::sync::Arc<crate::kernel::termination::resource_descent::ResourceWitnesses>>,
}

impl Clone for ResourceContext {
    fn clone(&self) -> Self {
        Self {
            instance_consumptions: self.instance_consumptions.clone(),
            storage: self.storage.clone(),
            framed_origins: self.framed_origins.clone(),
            observable_projection: self.observable_projection.clone(),
            borrow_dependencies: self.borrow_dependencies.clone(),
            structural_witnesses: self.structural_witnesses.clone(),
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
    /// This metadata never grants ownership or supplies a fact.
    pub(crate) fn instance_consumption(
        &self,
        identity: InstanceId,
    ) -> Option<&InstanceConsumption> {
        self.instance_consumptions.as_ref()?.get(&identity)
    }

    pub(super) fn record_instance_consumption(
        &mut self,
        identity: InstanceId,
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
            && self.borrow_dependencies.map.is_empty()
    }

    /// Return a live dependency for an exact occurrence.  The occurrence
    /// lookup is checked against this context so stale sidecar entries can
    /// never authorize a rewritten or removed resource.
    pub(crate) fn borrow_dependency(
        &self,
        occurrence: ResourceOccurrenceId,
    ) -> Option<&crate::kernel::borrows::BorrowBinding> {
        self.storage
            .entry_by_occurrence
            .contains_key(&occurrence)
            .then(|| self.borrow_dependencies.map.get(&occurrence))
            .flatten()
    }

    /// Attach one checked dependency to a freshly inserted occurrence.
    /// Callers must identify the destination occurrence returned by the
    /// resource insertion operation; value equality is intentionally not a
    /// valid substitute for that identity.
    pub(crate) fn with_borrow_dependency(
        mut self,
        occurrence: ResourceOccurrenceId,
        dependency: crate::kernel::borrows::BorrowBinding,
    ) -> Self {
        if self.storage.entry_by_occurrence.contains_key(&occurrence) {
            if let Some(existing) = self.borrow_dependencies.map.get(&occurrence) {
                if existing != &dependency {
                    return self;
                }
                return self;
            }
            self.borrow_dependencies = self.borrow_dependencies.updated(
                self.borrow_dependencies
                    .map
                    .with_inserted(occurrence, dependency),
                [occurrence],
            );
        }
        self
    }

    pub(crate) fn borrow_dependency_state(
        &self,
    ) -> std::sync::Arc<crate::kernel::borrows::BorrowBindingsState> {
        self.borrow_dependencies.clone()
    }

    pub(crate) fn with_borrow_dependency_state(
        mut self,
        state: std::sync::Arc<crate::kernel::borrows::BorrowBindingsState>,
    ) -> Self {
        self.borrow_dependencies = state;
        self
    }

    pub(crate) fn live_borrow_dependencies(
        &self,
    ) -> impl Iterator<Item = (ResourceOccurrenceId, &crate::kernel::borrows::BorrowBinding)> {
        // A filtered observation shares the current borrow state, which may
        // also contain excluded occurrences. Query the smaller side of the
        // intersection; never walk all excluded borrows for a small frame.
        let by_entries = self.storage.facts.len() < self.borrow_dependencies.map.len();
        let mut selected = Vec::new();
        if by_entries {
            for (_, occurrence) in self.storage.occurrence_by_entry.iter() {
                crate::instrumentation::record_deterministic_work(1);
                if let Some(binding) = self.borrow_dependencies.map.get(occurrence) {
                    selected.push((*occurrence, binding));
                }
            }
            // Preserve the original occurrence ordering for every caller.
            selected.sort_unstable_by_key(|(occurrence, _)| *occurrence);
        }
        self.borrow_dependencies
            .map
            .iter()
            .take(if by_entries {
                0
            } else {
                self.borrow_dependencies.map.len()
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
/// occurrence identifies the owner; this record pins the memory state and
/// the exact footprint(s) read while the projection was made.  Unknown
/// dependencies are deliberately conservative and are invalidated by any
/// opaque memory transition.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) enum ResourceMemoryFootprint {
    None,
    Exact(std::sync::Arc<[MemoryRange]>),
    Unknown,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ResourceSupportMetadata {
    pub(super) memory_state_identity: MemoryStateIdentity,
    pub(super) footprint: ResourceMemoryFootprint,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct ResourceMemoryIntervalNode {
    pub(super) block: AddressBase,
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
    pub(super) facts: PersistentMap<ResourceEntryId, ResourceFact>,
    pub(super) next_entry_id: ResourceEntryId,
    pub(super) occurrence_by_entry: PersistentMap<ResourceEntryId, ResourceOccurrenceId>,
    pub(super) entry_by_occurrence: PersistentMap<ResourceOccurrenceId, ResourceEntryId>,
    pub(super) index: ResourceContextIndex,
    /// Derived view entries name the exact owned resource that supports them.
    /// Ordinary entries are explicit and therefore absent from this map.
    pub(super) supported_by: PersistentMap<ResourceEntryId, ResourceFact>,
    /// Exact non-memory observations with live owned support. Separating this
    /// from ordinary views avoids searching equal descriptions for an owner.
    pub(super) nonmemory_projections_by_fact: PersistentMap<ResourceFact, ResourceEntryIds>,
    /// Explicit views are indexed separately from derived observations.
    pub(super) principal_views_by_fact: PersistentMap<ResourceFact, ResourceEntryIds>,
    /// Exact owned-entry identity for each supported projection. The fact
    /// cache above is useful for diagnostics, but this occurrence index is
    /// authoritative when one of several equal owned entries is consumed.
    pub(super) support_occurrence_by_projection:
        PersistentMap<ResourceEntryId, ResourceOccurrenceId>,
    /// Value-keyed reverse support index retained for compatibility with
    /// normalization and diagnostics. Removal and evidence use the
    /// occurrence-keyed index below, so equal authorities cannot alias.
    pub(super) projections_by_support: PersistentMap<ResourceFact, ResourceEntryIds>,
    /// Occurrence-keyed reverse index; unlike the fact-keyed compatibility
    /// index above, this cannot conflate equal support occurrences.
    pub(super) projections_by_support_occurrence:
        PersistentMap<ResourceOccurrenceId, ResourceEntryIds>,
    /// SymbolicMemory-dependent projections, indexed by their exact entry.  The
    /// companion block index lets a store/call/loop invalidation visit only
    /// projections whose recorded footprint can be affected.
    pub(super) support_metadata_by_projection:
        PersistentMap<ResourceOccurrenceId, ResourceSupportMetadata>,
    pub(super) projections_by_memory_block: PersistentMap<AddressBase, ResourceOccurrenceIds>,
    /// Dyadic interval indexes provide logarithmic affected-support lookup.
    pub(super) projections_by_memory_interval:
        PersistentMap<ResourceMemoryIntervalNode, ResourceOccurrenceIds>,
    pub(super) projections_by_memory_interval_subtree:
        PersistentMap<ResourceMemoryIntervalNode, ResourceOccurrenceIds>,
    pub(super) symbolic_memory_support: ResourceOccurrenceIds,
    pub(super) unknown_memory_support: ResourceOccurrenceIds,
    /// Certified, state-stable owned expansions for folded resource
    /// generations. Reusing these avoids re-lowering the same body into
    /// fresh symbolic load identities at each later transition.
    pub(super) expansions_by_support_occurrence:
        PersistentMap<ResourceOccurrenceId, std::sync::Arc<Vec<ResourceFact>>>,
    /// Canonical cache buckets keyed by support fact and rank among equal
    /// owned authorities. Independently built equivalent states can
    /// compare their support graph without exposing opaque occurrence
    /// allocation order, while invalidation remains occurrence-keyed above.
    /// Nesting by fact lets rekeying touch only the affected bucket.
    pub(super) expansions_by_support_entry:
        PersistentMap<ResourceFact, PersistentMap<usize, std::sync::Arc<Vec<ResourceFact>>>>,
    /// Persistent mutation ancestry used by checked Proof joins. The origin
    /// distinguishes unrelated states; the history names only exact facts
    /// whose multiplicity or representation changed.
    pub(super) origin: std::sync::Arc<()>,
    pub(super) history: Option<std::sync::Arc<ResourceContextChange>>,
    /// A scratch observable projection's unfiltered input and addressability
    /// registry. Used only to compare admissions; the projection's live exact
    /// index still decides which changed facts it actually supplies.
    pub(super) observable_projection_source:
        Option<(std::sync::Arc<()>, std::sync::Arc<ResourceContextStorage>)>,
    /// Legacy callers that explicitly enumerate every fact pay the
    /// output-sized materialization once per immutable state.
    pub(super) materialized: std::sync::OnceLock<Vec<ResourceFact>>,
}

#[derive(Clone)]
pub(crate) enum InstanceConsumption {
    Opened {
        instance: std::sync::Arc<ResourceInstance>,
        children: std::sync::Arc<std::collections::BTreeMap<String, InstanceId>>,
        values: std::sync::Arc<std::collections::BTreeMap<String, ProgramValue>>,
    },
    FoldChild {
        parent: InstanceId,
        slot: std::sync::Arc<str>,
    },
}

#[derive(Clone)]
pub(super) struct ResourceContextChange {
    pub(super) depth: usize,
    /// Exact occurrence delta for derived indexes; metadata changes use None.
    pub(super) entry_delta: Option<(ResourceEntryId, bool)>,
    pub(super) fact: ResourceFact,
    pub(super) parent: Option<std::sync::Arc<ResourceContextChange>>,
}

#[derive(Clone, Debug, Default)]
pub(super) struct ResourceContextIndex {
    /// The sum of the held facts' hashes, a content hash of the fact
    /// multiset kept as facts are inserted and removed, so ordering two
    /// contexts need not walk their facts (`ResourceContext::cmp`).
    pub(super) fact_hash: u64,
    /// The held facts as a canonical multiset: contexts holding the same
    /// facts share its root, so equality never walks them.
    pub(super) canonical: canonical_fact_set::CanonicalFactSet,
    pub(super) boundary_memory: canonical_fact_set::CanonicalFactSet,
    pub(super) boundary_memory_count: usize,
    pub(super) boundary_frame_revision: std::sync::Arc<()>,
    pub(super) boundary_non_nominal_count: usize,
    pub(super) boundary_non_argument_or_nominal_count: usize,
    pub(super) boundary_may_alias_argument_count: usize,
    pub(super) boundary_private_entries: ResourceEntryIds,
    pub(super) boundary_private_registry: Option<std::sync::Arc<()>>,
    pub(super) memory_facts: HashedOrdMap<ResourceFact, ()>,
    /// The owned facts of resources other than memory, each once: the
    /// non-memory members a composition is listed under
    /// (`CompositionMemberIndex`).
    pub(super) owned_non_memory_facts: HashedOrdMap<ResourceFact, ()>,
    /// Exact occurrences of owning allocation tokens, in resource order.
    pub(super) owned_allocation_tokens: ResourceEntryIds,
    pub(super) owned_memory_ranges: HashedOrdMap<MemoryRange, ()>,
    pub(super) owned_memory_range_counts: PersistentMap<MemoryRange, usize>,
    owned_count: usize,
    owned_composite_count: usize,
    /// Exclusive occurrence identities: named instances and conditional loop
    /// guard custody. Shape/pointer indexes below contain only named instances.
    pub(super) instances: PersistentMap<InstanceId, ResourceEntryIds>,
    /// Only duplicated or malformed mutex authority atoms need a validity check.
    pub(super) suspect_mutex_authorities: PersistentMap<Resource, ()>,
    pub(super) invalid_mutex_authority_access: PersistentMap<Resource, usize>,
    /// Instance identities with an entry whose access is not one owned unit.
    /// With `instances`, these select the identities that can fail a
    /// validity check without visiting every instance.
    pub(super) invalid_instance_access: PersistentMap<InstanceId, usize>,
    /// The identities held more than once or held with invalid access: the
    /// only ones whose entries can fail `exclusive_validity_error`.
    pub(super) suspect_instances: PersistentMap<InstanceId, ()>,
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
    pub(super) owned_instances_by_pointer_argument: PersistentMap<Address, ResourceEntryIds>,
    /// Logical resource occurrences whose pointer arguments name a C++
    /// prepared argument object. Its lifetime end queries only this block.
    pub(super) prepared_argument_resources: PersistentMap<AddressBase, ResourceEntryIds>,
    /// Owned folded composites keyed by each C pointer argument they name,
    /// and by the block of each. A call's kept memory answers a question
    /// about one address from the composites whose arguments can spell it,
    /// never the context's other composites
    /// (`memory_state::CallKeptRanges::range_holding`).
    pub(super) owned_composites_by_pointer_argument: PersistentMap<Address, ResourceEntryIds>,
    pub(super) owned_composites_by_argument_block: PersistentMap<AddressBase, ResourceEntryIds>,
    pub(super) viewed_composites_by_argument_block: PersistentMap<AddressBase, ResourceEntryIds>,
    /// Owned unit heads with exactly one argument, a nominal heap pointer.
    /// The count for a typed family can cover its whole shape without
    /// enumerating the occurrences the caller kept.
    heap_anchored_composite_counts: PersistentMap<(String, ProgramType), usize>,
    /// The owned folded composites with their multiplicity, content-hashed,
    /// so a kept set's identity can name them in constant work.
    pub(super) owned_composite_facts: HashedOrdMap<ResourceFact, usize>,
    pub(super) exact: PersistentMap<ResourceFact, ResourceEntryIds>,
    written_normalization: resource_algebra::WrittenNormalizationIndex,
    /// Exact physical ranges with their access modes, only for observing
    /// partition separation. Entries still carry their original authority.
    pub(super) spatial_memory: PersistentMap<ResourceFact, ResourceEntryIds>,
    pub(super) by_resource: PersistentMap<Resource, ResourceEntryIds>,
    /// Constant owned units of quantity-bearing families. A quantity query
    /// reads one exact key rather than enumerating separately retained units.
    /// u128 covers every u64 entry ID times a positive signed-32 quantity.
    pub(super) numeric_owned_units: PersistentMap<Resource, (u128, usize)>,
    pub(super) mutex_authorities: PersistentMap<(ResourceFamily, Address), ResourceEntryIds>,
    /// Subscriber rights an acquire load has read through, awaiting the C
    /// branch that tests the value (`publication::resolve_observed_publications`).
    pub(super) observed_publications: PersistentMap<(), ResourceEntryIds>,
    pub(super) exact_shapes: PersistentMap<(ResourceFamily, String, usize), ResourceEntryIds>,
    /// Tokens and composites keyed by shape and by the root of their first
    /// argument when it is a pointer (`None` otherwise). Every pointer
    /// parameter shares one block, so a lookup by shape alone would compare
    /// a parameter's fact with every other parameter's.
    pub(super) exact_shapes_by_root: PersistentMap<ShapeRootKey, ResourceEntryIds>,
    pub(super) memory_by_block: PersistentMap<AddressBase, ResourceEntryIds>,
    /// SymbolicMemory facts whose allocation identity is not a concrete block. An
    /// implicit local borrow must not rediscover whether these alias its storage.
    pub(super) nonconcrete_memory_count: usize,
    /// Iterated guarded-ownership facts keyed by both blocks their
    /// denotation depends on: the element base and the guard cells. A store,
    /// havoc, or free visits only the facts filed under its own block.
    pub(super) iterated_by_block: PersistentMap<AddressBase, ResourceEntryIds>,
    /// Owned iterated facts keyed by their instantiated clause without holes.
    /// Membership changes at individual indices do not change this key.
    pub(super) owned_iterated_by_clause: PersistentMap<IteratedMemory, ResourceEntryIds>,
    /// SymbolicMemory facts keyed by their exact base spelling. Direct pointer
    /// equalities can then find only the facts whose bases they identify,
    /// without scanning every resource in an aliased block.
    pub(super) memory_by_base: PersistentMap<Address, ResourceEntryIds>,
    /// Ownership-only exact-base buckets. Validity checks must not filter
    /// read observations out of the general memory bucket.
    pub(super) owned_memory_by_base: PersistentMap<Address, ResourceEntryIds>,
    /// Raw address anchors maintained during resource publication, for queries
    /// before a proof boundary has paired the input with an equality graph.
    /// Structural candidates maintained at resource publication, independent
    /// of proof-graph registration. Keys never establish access authority.
    structural_memory: memory_equality_index::structural::StructuralMemory,
    /// Raw persistent roots for pairing with an equality graph, maintained
    /// alongside the spelling index so pairing never scans the resource store.
    memory_addresses: memory_equality_index::MemoryAddresses,
    memory_objects: memory_equality_index::symbolic::ObjectSuppliers,
    pub(super) owned_memory_by_block: PersistentMap<AddressBase, ResourceEntryIds>,
    /// Automatic memory owners, indexed independently of external and global
    /// holdings. Addressability is checked when projecting observable facts.
    pub(super) owned_hidden_memory_generation: Option<u64>,
    pub(super) owned_physical_memory_by_block: PersistentMap<AddressBase, ResourceEntryIds>,
    pub(super) owned_hidden_memory_by_block: PersistentMap<AddressBase, ResourceEntryIds>,
    pub(super) owned_automatic_memory_by_block: PersistentMap<AddressBase, ResourceEntryIds>,
    /// The blocks holding two or more owned memory ranges. Only those can
    /// contribute same-block separation candidates, so projecting a
    /// composition's pairs visits these blocks and not one per allocation.
    pub(super) shared_owned_memory_blocks: PersistentMap<AddressBase, ()>,
    /// Nonempty constant byte ranges, keyed by symbolic origin, mode,
    /// and the **signed** values of those endpoints. The key's order is what
    /// the partition check's predecessor and successor probes stand in for a
    /// pairwise scan with, so it is an ordering question wearing a key's
    /// clothes: read as `u32`, a range starting below its base sorted past
    /// every range there is and its overlapping neighbour was never probed.
    pub(super) concrete_memory: PersistentMap<(Address, bool, i128, i128), ResourceEntryIds>,
    constant_owned_intervals: memory_equality_index::ConstantOwnershipIntervals,
    /// All constant ranges, including known-empty ones, represented at this origin.
    pub(super) concrete_memory_by_base: PersistentMap<(Address, bool), usize>,
    /// Owned memory ranges keyed by their base's root: the block and the
    /// first symbolic atom of the base offset, in canonical form (absent for
    /// a wholly constant offset). Two owned ranges whose bases share no
    /// root, no recorded-equality class of a root, and no exact alias have
    /// no fact the overlap decision could relate them by, so validity
    /// compares a range only with the ranges these keys select
    /// (`owned_validity_candidates`).
    pub(super) owned_memory_by_root: PersistentMap<MemoryBaseRoot, ResourceEntryIds>,
    /// Fixed footprints at one unregistered scalar base, indexed by that
    /// variable independently of its scale. Other footprints remain in the
    /// open bucket: they may resolve through memory or symbolic endpoints.
    pub(super) owned_memory_by_base_variable:
        PersistentMap<(AddressBase, Variable), ResourceEntryIds>,
    pub(super) owned_memory_open_bases: PersistentMap<AddressBase, ResourceEntryIds>,
    pub(super) owned_non_memory_entries: ResourceEntryIds,
    /// Owned memory ranges with a first element, keyed by that element's
    /// offset (the range's anchor). Two distinct owned members of one block
    /// have different anchors, which a pointer comparison asks by key
    /// rather than through every pair of members.
    pub(super) owned_memory_by_anchor: PersistentMap<AddressOffset, ResourceEntryIds>,
}

/// A condition fact's kind and canonical sides; see
/// `PureFactContext::condition_facts_by_sides`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum ConditionMatchKey {
    /// A 32-bit equality, sides in ascending order.
    Equal(OldMachineTerm, OldMachineTerm),
    /// An offset equality, sides in ascending order.
    OffsetEqual(AddressOffset, AddressOffset),
    /// A signed order: strict, then its lower and its upper side.
    Order(bool, OldMachineTerm, OldMachineTerm),
    /// An unsigned 32-bit order, separate from signed order facts.
    UnsignedOrder(bool, OldMachineTerm, OldMachineTerm),
    /// Signed addition overflow, with commutative operands ordered.
    OverflowAdd(OldMachineTerm, OldMachineTerm),
}

impl ConditionMatchKey {
    /// The family of kinds a fact under this key can match: equalities,
    /// offset equalities, or orders of the same signedness.
    pub(super) fn family(&self) -> u8 {
        match self {
            Self::Equal(_, _) => 0,
            Self::OffsetEqual(_, _) => 1,
            Self::Order(_, _, _) => 2,
            Self::UnsignedOrder(_, _, _) => 4,
            Self::OverflowAdd(_, _) => 3,
        }
    }
}

/// The block and first symbolic atom (canonical) of a memory base; see
/// `ResourceContextIndex::owned_memory_by_root`.
pub(super) type MemoryBaseRoot = (AddressBase, Option<AddressOffset>);

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
            && std::sync::Arc::ptr_eq(&self.borrow_dependencies, &other.borrow_dependencies)
        {
            return true;
        }
        self.storage
            .index
            .canonical
            .same_contents(&other.storage.index.canonical)
            && self.storage.supported_by == other.storage.supported_by
            && compare_support_graph(self, other) == std::cmp::Ordering::Equal
            && self.storage.expansions_by_support_entry == other.storage.expansions_by_support_entry
            && compare_borrow_dependencies(self, other) == std::cmp::Ordering::Equal
    }
}

impl Eq for ResourceContext {}

impl std::hash::Hash for ResourceContext {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // The fact multiset's content hash: equal contexts hold equal facts,
        // in whatever order they were filed.
        self.storage.index.fact_hash.hash(state);
        self.storage.index.exact.len().hash(state);
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
        // Hash the same structure-derived keys `compare_borrow_dependencies`
        // orders by, so two contexts that compare equal never hash apart.
        for dependency in stable_borrow_dependencies(self) {
            dependency.hash(state);
        }
    }
}

impl Ord for ResourceContext {
    /// By the fact multiset's cached content hash first, then structurally.
    /// The structural order walks the facts two contexts share, and the
    /// states a path states share almost all of them, so a set of stated
    /// compositions paid for a whole context per comparison
    /// (`roadmap/scaling.md`). Equal contexts hold equal facts and so equal
    /// hashes, and the hash depends only on the facts, so the order is
    /// consistent with `Eq` and deterministic.
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if std::sync::Arc::ptr_eq(&self.storage, &other.storage)
            && std::sync::Arc::ptr_eq(&self.borrow_dependencies, &other.borrow_dependencies)
        {
            return std::cmp::Ordering::Equal;
        }
        let key = |context: &Self| {
            let index = &context.storage.index;
            (index.fact_hash, index.exact.len())
        };
        key(self)
            .cmp(&key(other))
            .then_with(|| self.structural_cmp(other))
    }
}

impl ResourceContext {
    fn structural_cmp(&self, other: &Self) -> std::cmp::Ordering {
        count_structural_comparison();
        self.storage
            .index
            .canonical
            .cmp_contents(&other.storage.index.canonical)
            .then_with(|| {
                self.storage
                    .supported_by
                    .iter()
                    .cmp(other.storage.supported_by.iter())
            })
            .then_with(|| compare_support_graph(self, other))
            .then_with(|| compare_cached_expansions(self, other))
            .then_with(|| compare_borrow_dependencies(self, other))
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

/// One live borrow dependency, reduced to keys that do not name a process-local
/// counter.
///
/// `ResourceOccurrenceId`, `BorrowId`, `BorrowScopeId`, and `BorrowShareId` are all
/// fresh arena/ordinal pairs. Comparing them directly makes two structurally
/// identical contexts unequal whenever their bindings came from different
/// ledgers or were allocated in a different order, which silently costs loop
/// fixpoints, interning, and cross-run artifact reuse. The occurrence and the
/// dependency's support become the stable entry ordinals `compare_support_graph`
/// already uses; the borrow, scope, and share become the position of their first
/// appearance in that stable order, which preserves exactly which dependencies
/// share a borrow, scope, or share without naming any of them.
///
/// This changes only how dependencies compare. Their meaning, and every
/// authority check that reads `borrow_dependency`, still uses the exact
/// identities.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
struct StableBorrowDependency<'a> {
    entry: ResourceEntryId,
    viewed: &'a ResourceFact,
    support: StableBorrowSupport,
    borrow: usize,
    scope: usize,
    share: usize,
    hold: Option<usize>,
}

/// Where a dependency's supporting occurrence lives, without naming its arena.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum StableBorrowSupport {
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

/// The context's live borrow dependencies in a canonical, structure-derived
/// order. Ordering by the stable entry ordinal is a total order because
/// `entry_by_occurrence` maps distinct occurrences to distinct entries.
fn stable_borrow_dependencies(context: &ResourceContext) -> Vec<StableBorrowDependency<'_>> {
    let mut ordered = context
        .live_borrow_dependencies()
        .filter_map(|(occurrence, binding)| {
            context
                .storage
                .entry_by_occurrence
                .get(&occurrence)
                .map(|entry| (*entry, binding))
        })
        .collect::<Vec<_>>();
    ordered.sort_unstable_by_key(|(entry, _)| *entry);
    let mut borrows = std::collections::BTreeMap::new();
    let mut scopes = std::collections::BTreeMap::new();
    let mut shares = std::collections::BTreeMap::new();
    let mut supports = std::collections::BTreeMap::new();
    let mut holds = std::collections::BTreeMap::new();
    ordered
        .into_iter()
        .map(|(entry, binding)| {
            let borrow = first_appearance(&mut borrows, binding.borrow);
            let scope = first_appearance(&mut scopes, binding.scope);
            let share = first_appearance(&mut shares, binding.share);
            let hold = binding.hold.map(|hold| first_appearance(&mut holds, hold));
            let support = match context.storage.entry_by_occurrence.get(&binding.support) {
                Some(entry) => StableBorrowSupport::Entry(*entry),
                None => {
                    StableBorrowSupport::Position(first_appearance(&mut supports, binding.support))
                }
            };
            StableBorrowDependency {
                entry,
                viewed: &binding.viewed,
                support,
                borrow,
                scope,
                share,
                hold,
            }
        })
        .collect()
}

fn compare_borrow_dependencies(
    left: &ResourceContext,
    right: &ResourceContext,
) -> std::cmp::Ordering {
    stable_borrow_dependencies(left).cmp(&stable_borrow_dependencies(right))
}

impl PartialOrd for ResourceContext {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Compare only the support graph, using each state's stable entry
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
pub enum ResourceFact {
    Own(Resource, Box<StoredMachineTerm>),
    View(Resource),
}

/// Immutable logical indices shared by resource states and population keys.
/// Cloning a resource must not clone a recursive model stored in its indices.
/// Explicit native argument input/output DTO.
pub type NativeResourceArguments = std::sync::Arc<[AlgebraicValue]>;
/// Immutable resource arguments retain the same typed carriers as fields.
pub type ResourceArguments = ResourceFieldValues;

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Resource {
    /// Separating conjunction; repeated components retain their multiplicity.
    Star(std::sync::Arc<super::ResourceConjunction>),
    /// Empty resource descriptor.
    Emp,
    Footprint(Arc<super::RegionFootprint>),
    /// Rigid descriptor for a resource-valued theorem parameter.
    Parameter(Variable),
    Memory(MemoryRange),
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
    /// Exclusive custody of a loop guard, conditional on its frozen head condition.
    ConditionalMutexGuard(Arc<ConditionalMutexGuard>),
    /// Exclusive lifecycle authority for one initialized mutex.
    MutexLive(MutexIdentity),
    /// Owned permission to use one checked borrow share of an initialized mutex.
    MutexUse(MutexUseIdentity),
    /// Iterated guarded ownership: one fact for every element of a bounded
    /// index range whose guard cell holds (`iterated.rs`).
    Iterated(Arc<IteratedMemory>),
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
    pub(in crate::kernel) flag: Address,
    pub(in crate::kernel) payload: super::ResourceDescription,
    /// A subscriber right an acquire load has read `observed` through, until
    /// a C branch decides whether that value is zero.
    pub(in crate::kernel) observed: Option<StoredProgramValue>,
}

impl PublicationRight {
    pub(crate) fn new(
        side: PublicationSide,
        flag: Address,
        payload: super::ResourceDescription,
    ) -> Self {
        Self {
            side,
            flag,
            payload,
            observed: None,
        }
    }
    pub(crate) fn observed(&self) -> Option<&ProgramValue> {
        self.observed.as_ref().map(StoredProgramValue::old_form)
    }
    pub(crate) fn side(&self) -> PublicationSide {
        self.side
    }
    pub(crate) fn flag(&self) -> &Address {
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
    /// Bound addresses are immutable diagnostic metadata; only an
    /// unbound description's address participates in substitution.
    pub(in crate::kernel) mutex: Address,
}

/// A loop-owned occurrence. Protocol metadata and the condition never create
/// this resource: only checked entry/backedge ownership exchanges do.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ConditionalMutexGuard {
    pub(in crate::kernel) identity: InstanceId,
    pub(in crate::kernel) guard: MutexIdentity,
    pub(in crate::kernel) initialization: MutexIdentity,
    pub(in crate::kernel) held: StoredConditionTerm,
}

impl ConditionalMutexGuard {
    pub(crate) fn mutex(&self) -> &Address {
        self.guard.mutex()
    }
    pub(crate) fn condition(&self) -> &OldConditionTerm {
        self.held.old_form()
    }
}

/// Opaque identity of one use-share resource occurrence. The pointer is
/// diagnostic metadata, not a constructor for borrow authority. Substitution
/// must preserve this identity just as it preserves a concrete acquisition.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct MutexUseIdentity {
    pub(in crate::kernel) protected: Option<super::ResourceDescription>,
    pub(in crate::kernel) binding: Option<super::borrows::MutexUseBinding>,
    pub(in crate::kernel) initialization: Option<u64>,
    pub(in crate::kernel) mutex: Address,
}

impl MutexUseIdentity {
    pub(crate) fn protected_type(&self) -> Option<&super::ResourceDescription> {
        self.protected.as_ref()
    }
    pub(crate) fn mutex(&self) -> &Address {
        &self.mutex
    }
}

impl MutexIdentity {
    pub(crate) fn mutex(&self) -> &Address {
        &self.mutex
    }
}

impl Resource {
    pub(crate) fn star(left: Self, right: Self) -> Self {
        Self::Star(super::resource_conjunction::intern(left, right))
    }

    /// The resource's name in a diagnostic, with no argument or address
    /// spelling: the kernel has no source names for those.
    pub(crate) fn diagnostic_name(&self) -> &str {
        match self {
            Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_) => {
                "resource parameter"
            }
            Resource::Composite { name, .. } | Resource::Token { name, .. } => name,
            Resource::Memory(_) => "memory",
            Resource::PopulationAuthority(_) => "population authority",
            Resource::MutexGuard(_) => "mutex guard",
            Resource::ConditionalMutexGuard(_) => "conditional mutex guard",
            Resource::MutexLive(_) => "mutex lifetime",
            Resource::MutexUse(_) => "mutex use",
            Resource::Publication(_) => "publication right",
            Resource::Instance(instance) => instance.name(),
            Resource::Iterated(iterated) => iterated.owner(),
        }
    }

    /// One iterated guarded-ownership fact. The fact is shared, so cloning a
    /// resource context never copies its terms.
    pub(crate) fn iterated(iterated: IteratedMemory) -> Self {
        Self::Iterated(Arc::new(iterated))
    }
}

/// The identity of one resource instance: a held atom's own name, never a
/// value. It is not interchangeable with a value [`Variable`].
#[derive(Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct InstanceId(Variable);

/// Prints as the number it is carried as, so diagnostics and debug output
/// that spelled an instance identity before this type existed are unchanged.
impl std::fmt::Debug for InstanceId {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(formatter)
    }
}

impl InstanceId {
    /// An instance identity from the number it is carried as. Migration
    /// constructor: later work will require an origin here.
    pub const fn from_variable(variable: Variable) -> Self {
        Self(variable)
    }

    /// The number this identity is carried as, for registries still keyed by it.
    pub const fn variable(self) -> Variable {
        self.0
    }

    /// Whether an execution created this instance
    /// ([`ExecutionBudget::allocate_instance_identity`]) rather than a
    /// binder the surface named.
    pub fn created_by_execution(self) -> bool {
        (ExecutionBudget::KERNEL_VARIABLE_BASE..ExecutionBudget::KERNEL_VARIABLE_CEILING)
            .contains(&self.0.0)
    }
}

/// The instance a resource field read names: the instance a resource
/// definition's body describes (its `self`), or a particular instance.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum InstanceRef {
    /// The instance whose body is being read. It is bound where an instance
    /// is opened ([`ResourceBindings::bind_body`]), or read from the field
    /// view of a definition evaluated without one.
    Body,
    Instance(InstanceId),
}

impl From<InstanceId> for InstanceRef {
    fn from(identity: InstanceId) -> Self {
        InstanceRef::Instance(identity)
    }
}

impl InstanceRef {
    /// The particular instance this names, if it is not the body's own.
    pub const fn instance(self) -> Option<InstanceId> {
        match self {
            InstanceRef::Body => None,
            InstanceRef::Instance(identity) => Some(identity),
        }
    }
}

/// The proof name of one exact mutex authority occurrence (a live, use or
/// guard authority bound by a named resource clause). It is an alias in a
/// state's named-authority table, never a resource instance or a value.
#[derive(Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct MutexAuthorityId(Variable);

/// Prints as the number it is carried as, like [`InstanceId`].
impl std::fmt::Debug for MutexAuthorityId {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(formatter)
    }
}

impl MutexAuthorityId {
    /// A mutex authority name from the binder number it is carried as.
    pub const fn from_variable(variable: Variable) -> Self {
        Self(variable)
    }

    /// The binder number, for call binding maps still keyed by it.
    pub const fn variable(self) -> Variable {
        self.0
    }
}

/// A callee's resource binder: an exclusive instance binder or a named
/// mutex authority binder. Which one a binder is comes from the clause that
/// declares it ([`ResourceSpec::binding_identity`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ResourceBinder {
    Instance(InstanceId),
    MutexAuthority(MutexAuthorityId),
}

impl ResourceBinder {
    /// The instance this binder names, if it is an instance binder.
    pub const fn instance(self) -> Option<InstanceId> {
        match self {
            ResourceBinder::Instance(identity) => Some(identity),
            ResourceBinder::MutexAuthority(_) => None,
        }
    }

    /// The mutex authority this binder names, if it is an authority binder.
    pub const fn mutex_authority(self) -> Option<MutexAuthorityId> {
        match self {
            ResourceBinder::Instance(_) => None,
            ResourceBinder::MutexAuthority(identity) => Some(identity),
        }
    }

    /// The number this binder is carried as, for hidden binder spellings
    /// and runtime binder descriptors.
    pub const fn variable(self) -> Variable {
        match self {
            ResourceBinder::Instance(identity) => identity.variable(),
            ResourceBinder::MutexAuthority(identity) => identity.variable(),
        }
    }
}

/// The checked binding of a callee's resource binders to the caller's
/// resources at one call or rewrite. Each binder maps to a caller resource
/// of its own sort.
#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ResourceBindings {
    instances: BTreeMap<InstanceId, InstanceId>,
    mutex_authorities: BTreeMap<MutexAuthorityId, MutexAuthorityId>,
    /// The instance [`InstanceRef::Body`] names while its body is opened.
    body: Option<InstanceId>,
}

impl ResourceBindings {
    pub fn new() -> Self {
        Self::default()
    }

    /// The caller instance an instance binder names.
    pub fn instance(&self, binder: InstanceId) -> Option<InstanceId> {
        self.instances.get(&binder).copied()
    }

    /// Binds [`InstanceRef::Body`] to the instance whose body is opened.
    pub fn bind_body(&mut self, instance: InstanceId) {
        self.body = Some(instance);
    }

    /// The instance [`InstanceRef::Body`] names, if a body is opened.
    pub fn body(&self) -> Option<InstanceId> {
        self.body
    }

    /// The caller authority a mutex authority binder names.
    pub fn mutex_authority(&self, binder: MutexAuthorityId) -> Option<MutexAuthorityId> {
        self.mutex_authorities.get(&binder).copied()
    }

    /// The caller resource a binder names, of the binder's sort.
    pub fn get(&self, binder: ResourceBinder) -> Option<ResourceBinder> {
        match binder {
            ResourceBinder::Instance(binder) => self.instance(binder).map(ResourceBinder::Instance),
            ResourceBinder::MutexAuthority(binder) => self
                .mutex_authority(binder)
                .map(ResourceBinder::MutexAuthority),
        }
    }

    pub fn contains(&self, binder: ResourceBinder) -> bool {
        self.get(binder).is_some()
    }

    /// Binds an instance binder; returns the caller instance it already named.
    pub fn insert_instance(
        &mut self,
        binder: InstanceId,
        actual: InstanceId,
    ) -> Option<InstanceId> {
        self.instances.insert(binder, actual)
    }

    /// Binds a mutex authority binder; returns the authority it already named.
    pub fn insert_mutex_authority(
        &mut self,
        binder: MutexAuthorityId,
        actual: MutexAuthorityId,
    ) -> Option<MutexAuthorityId> {
        self.mutex_authorities.insert(binder, actual)
    }

    /// Binds `binder` to `actual`, a caller resource of the same sort.
    /// Returns `Err` when the sorts differ, and otherwise whether the binder
    /// was already bound.
    #[expect(
        clippy::result_unit_err,
        reason = "callers report the mismatched resource sorts"
    )]
    pub fn insert(&mut self, binder: ResourceBinder, actual: ResourceBinder) -> Result<bool, ()> {
        match (binder, actual) {
            (ResourceBinder::Instance(binder), ResourceBinder::Instance(actual)) => {
                Ok(self.insert_instance(binder, actual).is_some())
            }
            (ResourceBinder::MutexAuthority(binder), ResourceBinder::MutexAuthority(actual)) => {
                Ok(self.insert_mutex_authority(binder, actual).is_some())
            }
            _ => Err(()),
        }
    }

    /// Every binding, instances first, each in binder order.
    pub fn iter(&self) -> impl Iterator<Item = (ResourceBinder, ResourceBinder)> + '_ {
        self.instances
            .iter()
            .map(|(binder, actual)| {
                (
                    ResourceBinder::Instance(*binder),
                    ResourceBinder::Instance(*actual),
                )
            })
            .chain(self.mutex_authorities.iter().map(|(binder, actual)| {
                (
                    ResourceBinder::MutexAuthority(*binder),
                    ResourceBinder::MutexAuthority(*actual),
                )
            }))
    }

    /// Adds every binding of `other`, replacing this map's binding of the
    /// same binder.
    pub fn extend(&mut self, other: &Self) {
        self.instances.extend(&other.instances);
        self.mutex_authorities.extend(&other.mutex_authorities);
    }

    /// The caller instances bound, in binder order.
    pub fn instances(&self) -> impl Iterator<Item = (InstanceId, InstanceId)> + '_ {
        self.instances
            .iter()
            .map(|(binder, actual)| (*binder, *actual))
    }

    pub fn len(&self) -> usize {
        self.instances.len() + self.mutex_authorities.len() + usize::from(self.body.is_some())
    }

    pub fn is_empty(&self) -> bool {
        self.instances.is_empty() && self.mutex_authorities.is_empty() && self.body.is_none()
    }
}

/// A proof-only, exclusive resource instance. Identity is independent of its
/// field state; equal fields do not identify distinct instances. This is an
/// opaque ownership atom: its arguments and fields grant no memory authority.
/// Constructing an atom is not a proof that it is owned or that a resource
/// definition's body holds.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ResourceInstance {
    pub(super) identity: InstanceId,
    pub(super) name: String,
    pub(super) arguments: ResourceArguments,
    pub(super) schema: ResourceFieldSchema,
    pub(super) fields: ResourceFieldValues,
    pub(super) resource_arguments: Arc<[super::ResourceReference]>,
}

impl ResourceInstance {
    /// The identity a field view carries. A field view is a definition's
    /// fields and arguments read without an instance; it is reached only
    /// through [`InstanceRef::Body`] and never looked up by identity, so this
    /// value names nothing.
    const FIELD_VIEW_IDENTITY: InstanceId = InstanceId(Variable(u64::MAX));

    /// A definition's fields and arguments, to read as its body's own
    /// instance when there is no instance: it grants no ownership and is
    /// never held in a resource context.
    pub(crate) fn field_view(
        name: String,
        arguments: ResourceArguments,
        schema: ResourceFieldSchema,
        fields: ResourceFieldValues,
    ) -> Option<Self> {
        Self::new(Self::FIELD_VIEW_IDENTITY, name, arguments, schema, fields)
    }

    pub fn new(
        identity: InstanceId,
        name: String,
        arguments: ResourceArguments,
        schema: ResourceFieldSchema,
        fields: ResourceFieldValues,
    ) -> Option<Self> {
        Self::new_with_resource_arguments(identity, name, arguments, schema, fields, Vec::new())
    }

    /// Construct an exclusive atom with proof-only arguments. As for `new`, a
    /// countable schema is rejected; references do not change countability.
    pub fn new_with_resource_arguments(
        identity: InstanceId,
        name: String,
        arguments: ResourceArguments,
        schema: ResourceFieldSchema,
        fields: ResourceFieldValues,
        resource_arguments: Vec<super::ResourceReference>,
    ) -> Option<Self> {
        if schema.is_fieldless() || schema.fields().len() != fields.len() {
            return None;
        }
        if !fields.matches_schema(&schema) {
            return None;
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

    pub fn identity(&self) -> InstanceId {
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
    pub fn arguments(&self) -> &ResourceArguments {
        &self.arguments
    }
    pub fn fields(&self) -> &ResourceFieldValues {
        &self.fields
    }
    pub fn schema(&self) -> &ResourceFieldSchema {
        &self.schema
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResourceContextValidityError {
    /// A raw symbolic boundary needs this explicit separation premise.
    UnestablishedOwnedBoundary(Box<Proposition>),
    /// Opaque ownership lacks a finite indexed frontier.
    UnsupportedOwnershipBoundary,
    InvalidExclusiveAccess(ResourceFact),
    DuplicateOwnedResourceFact(ResourceFact),
    OverlappingOwnedMemoryResources {
        left: MemoryRange,
        right: MemoryRange,
    },
}

impl std::fmt::Display for ResourceContextValidityError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::UnsupportedOwnershipBoundary => "ownership separation lacks an indexed finite frontier",
            Self::UnestablishedOwnedBoundary(_) => "symbolic ownership boundary requires an explicit separation proof",
            Self::InvalidExclusiveAccess(_) => {
                "field-bearing resource instances and mutex guards require exclusive ownership with quantity one"
            }
            Self::DuplicateOwnedResourceFact(_) => "the same resource is owned twice",
            Self::OverlappingOwnedMemoryResources { .. } => "two owned memory resources overlap",
        })
    }
}

/// The result of consuming one available resource fact to satisfy a required
/// fact. Viewed facts are normally preserved; owned facts may be removed or
/// replaced by residual ownership.
pub(super) enum ResourceFactConsumption {
    Preserve,
    Replace(Vec<ResourceFact>),
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
    fn validate_spec(&self, spec: &ResourceSpec) -> Result<(), ResourceSpecError> {
        if spec.term.family() != self.family() {
            return Err(ResourceSpecError::InvalidNestedTerm(
                "resource term and family algebra disagree".into(),
            ));
        }
        if let ResourceTerm::PopulationAuthority { protected, .. } = &spec.term
            && (!matches!(
                protected.resource.term(),
                ResourceTerm::Composite { .. } | ResourceTerm::Token { .. }
            ) || (matches!(protected.resource.term(), ResourceTerm::Token { .. })
                && !protected.schema.fields().is_empty())
                || protected.resource.access() != ResourceAccessMode::Own
                || protected.resource.quantity() != &ResourceQuantity::One)
        {
            return Err(ResourceSpecError::InvalidNestedTerm(
                "population authority requires an owned unit composite or token resource type"
                    .into(),
            ));
        }
        match self.family() {
            ResourceFamily::Parameter => {
                return Err(ResourceSpecError::InvalidNestedTerm(
                    "a Resource parameter carries no ownership".into(),
                ));
            }
            ResourceFamily::PopulationAuthority
            | ResourceFamily::MutexGuard
            | ResourceFamily::MutexLive
            | ResourceFamily::MutexUse
            | ResourceFamily::Publication => {
                if spec.access != ResourceAccessMode::Own {
                    return Err(ResourceSpecError::InvalidAccess {
                        family: self.family(),
                        access: spec.access,
                    });
                }
                if spec.quantity != ResourceQuantity::One {
                    return Err(ResourceSpecError::InvalidQuantity {
                        family: self.family(),
                        reason: "authority has unit quantity".into(),
                    });
                }
            }
            ResourceFamily::Memory => {
                if !matches!(spec.quantity, ResourceQuantity::One) {
                    return Err(ResourceSpecError::InvalidQuantity {
                        family: ResourceFamily::Memory,
                        reason: "memory ranges have unit quantity".into(),
                    });
                }
            }
            ResourceFamily::Instance => {
                if spec.access != ResourceAccessMode::Own {
                    return Err(ResourceSpecError::InvalidAccess {
                        family: ResourceFamily::Instance,
                        access: spec.access,
                    });
                }
                if !matches!(spec.quantity, ResourceQuantity::One) {
                    return Err(ResourceSpecError::InvalidQuantity {
                        family: ResourceFamily::Instance,
                        reason: "field-bearing instances have unit quantity".into(),
                    });
                }
                if !matches!(spec.term, ResourceTerm::Instance { ref resource, .. } if matches!(resource.as_ref(), ResourceTerm::Composite { .. }))
                {
                    return Err(ResourceSpecError::InvalidNestedTerm(
                        "field-bearing instances require a declared composite term".into(),
                    ));
                }
            }
            ResourceFamily::Iterated => {
                if !matches!(spec.quantity, ResourceQuantity::One) {
                    return Err(ResourceSpecError::InvalidQuantity {
                        family: ResourceFamily::Iterated,
                        reason: "iterated ownership has unit quantity".into(),
                    });
                }
            }
            ResourceFamily::Composite | ResourceFamily::Token => {
                if matches!(spec.quantity, ResourceQuantity::Count(_))
                    && spec.access != ResourceAccessMode::Own
                {
                    return Err(ResourceSpecError::InvalidAccess {
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
        left: &ResourceFact,
        right: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceContextValidityError>;

    fn entails(
        &self,
        available: &ResourceFact,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> bool;

    fn consume(
        &self,
        available: &ResourceFact,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceFactConsumption>;

    /// Returns one fact equivalent to composing this pair when the pair can be
    /// losslessly normalized. `None` leaves both facts in the resource state.
    fn normalize_pair(
        &self,
        left: &ResourceFact,
        right: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceFact>;

    fn core(&self, fact: &ResourceFact) -> Option<ResourceFact>;
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
    Parameter,
    Memory,
    PopulationAuthority,
    Composite,
    Token,
    Instance,
    MutexGuard,
    MutexLive,
    MutexUse,
    /// Iterated guarded ownership (`Resource::Iterated`).
    Iterated,
    /// One half of a one-shot publication channel (`Resource::Publication`).
    Publication,
}

impl ResourceFamily {
    /// The family's name in a diagnostic.
    pub(crate) fn describe(self) -> &'static str {
        match self {
            Self::Parameter => "resource parameter",
            Self::Memory => "memory",
            Self::PopulationAuthority => "population authority",
            Self::Composite => "composite",
            Self::Token => "token",
            Self::Instance => "resource instance",
            Self::MutexGuard => "mutex_guard",
            Self::MutexLive => "mutex_live",
            Self::MutexUse => "mutex_use",
            Self::Iterated => "iterated ownership",
            Self::Publication => "publication",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ResourceAccessMode {
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
pub struct ResourceTypeSpec {
    pub resource: Box<ResourceSpec>,
    pub schema: ResourceFieldSchema,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ResourceTerm {
    Memory(MemorySegment),
    PopulationAuthority {
        protected: Box<ResourceTypeSpec>,
        population_arity: Option<usize>,
        state_source: ResourceStateSource,
    },
    MutexGuard {
        mutex: Box<ProgramExpression>,
        state_source: ResourceStateSource,
    },
    MutexLive {
        mutex: Box<ProgramExpression>,
        state_source: ResourceStateSource,
    },
    MutexUse {
        protected: Option<Box<ResourceTypeSpec>>,
        mutex: Box<ProgramExpression>,
        state_source: ResourceStateSource,
    },
    /// `publisher(flag, P)` or `subscriber(flag, P)`.
    Publication {
        side: PublicationSide,
        payload: Box<ResourceTypeSpec>,
        flag: Box<ProgramExpression>,
        state_source: ResourceStateSource,
    },
    Composite {
        name: String,
        arguments: Vec<ProgramExpression>,
        argument_state_sources: Vec<ResourceStateSource>,
        parameter_types: Vec<ProgramType>,
    },
    Token {
        name: String,
        arguments: Vec<ProgramExpression>,
        argument_state_sources: Vec<ResourceStateSource>,
        parameter_types: Vec<ProgramType>,
    },
    Instance {
        identity: InstanceId,
        /// The spelling the declaration gave this binder. The identity is the
        /// semantic key; this is the name a binder or proof-parameter map is
        /// written with, retained the same way [`ResourceChildSpec::name`]
        /// retains a child slot's spelling, so diagnostics can print the map
        /// the user has to write.
        ///
        /// The surface binding the clause carries is the single source for
        /// this spelling: lowering copies it here, and the parser copies the
        /// same name into its own per-callee binder index for the call maps it
        /// checks before lowering runs.
        binder: String,
        schema: ResourceFieldSchema,
        resource: Box<ResourceTerm>,
    },
    /// An iterated guarded-ownership clause of a resource body. It evaluates
    /// to one `Resource::Iterated` fact; see `primitives/iterated.rs`.
    Iterated(Box<IteratedSpec>),
}

/// The unevaluated form of an iterated guarded-ownership clause: C
/// expressions over the body's parameters, with the element and guard shape
/// fixed by validation.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct IteratedSpec {
    pub(crate) owner: String,
    /// `element.base[element.start..element.end]` is the index range
    /// `lo..hi` read against the element base; the element width is the
    /// base's.
    pub(crate) element: MemorySegment,
    pub(crate) stride: u32,
    pub(crate) start_offset: i32,
    pub(crate) end_offset: i32,
    pub(crate) guard_base: ProgramExpression,
    pub(crate) guard_cell_type: ProgramType,
    pub(crate) guard_cell_width: u32,
    pub(crate) holds_when_equal: bool,
    pub(crate) guard_value: ProgramExpression,
}

/// Quantity is explicit in the normalized form.  `One` is the ordinary unit
/// quantity; `Count` is reserved for the existing counted composite/token
/// resources.  In particular, memory and exclusive instances cannot acquire a
/// quantity merely because a wrapper could represent one.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ResourceQuantity {
    One,
    Count(ProgramExpression),
}

/// The transfer operation associated with a normalized specification.
/// Resource vectors remain grouped by their source-level section for stable
/// ordering, but the semantic operation is carried on each element.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ResourceTransferRole {
    Borrow,
    Consume,
    Produce,
}

/// Which state supplies the resource term's address, arguments, or quantity.
/// Callers may still pass an explicitly selected state to the evaluator; this
/// metadata records the selection made by lowering and prevents entry/post
/// meaning from being inferred from a vector's position.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ResourceStateSource {
    Entry,
    Current,
    Post,
}

#[derive(Clone, Debug)]
pub struct ResourceSpec {
    /// Actual resource-reference binders, separate from C-valued arguments.
    /// Naming a binder here grants no ownership of its occurrence.
    resource_arguments: Arc<[InstanceId]>,
    term: ResourceTerm,
    /// A proof binder for one raw mutex authority. This does not change the
    /// resource family or turn the authority into a composite instance.
    mutex_authority_binding: Option<Arc<(MutexAuthorityId, String)>>,
    access: ResourceAccessMode,
    quantity: ResourceQuantity,
    quantity_state_source: ResourceStateSource,
    role: ResourceTransferRole,
    state_source: ResourceStateSource,
    /// A pre-state proposition controlling a conditional resource effect.
    /// `None` is the ordinary unconditional clause.
    guard: Option<SpecProposition>,
    /// The normalized input requirement that backs this produced memory view.
    view_source: Option<usize>,
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
pub enum ResourceSpecError {
    InvalidAccess {
        family: ResourceFamily,
        access: ResourceAccessMode,
    },
    InvalidQuantity {
        family: ResourceFamily,
        reason: String,
    },
    InvalidNestedTerm(String),
}

impl std::fmt::Display for ResourceSpecError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidAccess { family, access } => {
                let access = match access {
                    ResourceAccessMode::Own => "owns",
                    ResourceAccessMode::View => "views",
                };
                write!(
                    formatter,
                    "{} resources do not permit `{access}` access",
                    family.describe()
                )
            }
            Self::InvalidQuantity { family, reason } => {
                write!(
                    formatter,
                    "{} resource has invalid quantity: {reason}",
                    family.describe()
                )
            }
            Self::InvalidNestedTerm(reason) => formatter.write_str(reason),
        }
    }
}

impl std::error::Error for ResourceSpecError {}

impl ResourceTerm {
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

    pub fn memory_segment(&self) -> Option<&MemorySegment> {
        match self {
            Self::Memory(segment) => Some(segment),
            _ => None,
        }
    }

    pub fn instance_identity(&self) -> Option<InstanceId> {
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

    pub fn instance_resource(&self) -> Option<&ResourceTerm> {
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

    pub fn declared_arguments(&self) -> Option<&[ProgramExpression]> {
        match self {
            Self::Composite { arguments, .. } | Self::Token { arguments, .. } => Some(arguments),
            _ => None,
        }
    }

    pub fn declared_argument_states(&self) -> Option<&[ResourceStateSource]> {
        match self {
            Self::Composite {
                argument_state_sources,
                ..
            }
            | Self::Token {
                argument_state_sources,
                ..
            } => Some(argument_state_sources),
            _ => None,
        }
    }
}

impl ResourceSpec {
    pub fn new(
        term: ResourceTerm,
        access: ResourceAccessMode,
        quantity: ResourceQuantity,
        role: ResourceTransferRole,
        state_source: ResourceStateSource,
    ) -> Result<Self, ResourceSpecError> {
        let spec = Self {
            term,
            mutex_authority_binding: None,
            resource_arguments: Arc::from([]),
            access,
            quantity,
            quantity_state_source: ResourceStateSource::Current,
            role,
            state_source,
            guard: None,
            view_source: None,
            clause_position: None,
            source_arguments: None,
        };
        spec.validate()?;
        Ok(spec)
    }

    pub fn memory(
        segment: MemorySegment,
        access: ResourceAccessMode,
        role: ResourceTransferRole,
        state_source: ResourceStateSource,
    ) -> Self {
        Self::new(
            ResourceTerm::Memory(segment),
            access,
            ResourceQuantity::One,
            role,
            state_source,
        )
        .expect("unit memory terms are valid by construction")
    }

    /// Constructors for kernel callers that do not have a surrounding
    /// transfer section.  Surface lowering uses the fully annotated
    /// constructor below; these defaults describe the caller-selected
    /// current state, with the transfer role made explicit as `Consume`.
    pub fn viewed_memory(segment: MemorySegment) -> Self {
        Self::memory(
            segment,
            ResourceAccessMode::View,
            ResourceTransferRole::Borrow,
            ResourceStateSource::Current,
        )
    }

    pub fn owned_memory(segment: MemorySegment) -> Self {
        Self::memory(
            segment,
            ResourceAccessMode::Own,
            ResourceTransferRole::Consume,
            ResourceStateSource::Current,
        )
    }

    pub fn declared(
        family: ResourceFamily,
        access: ResourceAccessMode,
        name: String,
        arguments: Vec<ProgramExpression>,
        parameter_types: Vec<ProgramType>,
        role: ResourceTransferRole,
        state_source: ResourceStateSource,
    ) -> Result<Self, ResourceSpecError> {
        Self::declared_with_argument_states(
            family,
            access,
            name,
            arguments,
            Vec::new(),
            parameter_types,
            role,
            state_source,
        )
    }

    pub fn declared_with_argument_states(
        family: ResourceFamily,
        access: ResourceAccessMode,
        name: String,
        arguments: Vec<ProgramExpression>,
        mut argument_state_sources: Vec<ResourceStateSource>,
        parameter_types: Vec<ProgramType>,
        role: ResourceTransferRole,
        state_source: ResourceStateSource,
    ) -> Result<Self, ResourceSpecError> {
        if argument_state_sources.is_empty() {
            argument_state_sources = vec![ResourceStateSource::Current; arguments.len()];
        }
        if arguments.len() != argument_state_sources.len()
            || arguments.len() != parameter_types.len()
        {
            return Err(ResourceSpecError::InvalidNestedTerm(
                "resource argument metadata has the wrong length".into(),
            ));
        }
        let term = match family {
            ResourceFamily::Parameter => {
                return Err(ResourceSpecError::InvalidNestedTerm(
                    "a Resource parameter carries no ownership".into(),
                ));
            }
            ResourceFamily::Composite => ResourceTerm::Composite {
                name,
                arguments,
                argument_state_sources,
                parameter_types,
            },
            ResourceFamily::Token => ResourceTerm::Token {
                name,
                arguments,
                argument_state_sources,
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
                return Err(ResourceSpecError::InvalidNestedTerm(
                    "only composite and token families have declared resource terms".into(),
                ));
            }
        };
        Self::new(term, access, ResourceQuantity::One, role, state_source)
    }

    pub fn instance(
        identity: InstanceId,
        binder: String,
        schema: ResourceFieldSchema,
        resource: ResourceSpec,
        role: ResourceTransferRole,
        state_source: ResourceStateSource,
    ) -> Result<Self, ResourceSpecError> {
        if resource.access != ResourceAccessMode::Own
            || resource.quantity != ResourceQuantity::One
            || !matches!(resource.term, ResourceTerm::Composite { .. })
        {
            return Err(ResourceSpecError::InvalidNestedTerm(
                "named resource instances require an owned unit composite term".into(),
            ));
        }
        let references = resource.resource_arguments.clone();
        Self::new(
            ResourceTerm::Instance {
                identity,
                binder,
                schema,
                resource: Box::new(resource.term),
            },
            ResourceAccessMode::Own,
            ResourceQuantity::One,
            role,
            state_source,
        )
        .map(|spec| spec.with_resource_arguments(references.to_vec()))
    }

    pub fn quantified(
        quantity: ProgramExpression,
        resource: ResourceSpec,
        role: ResourceTransferRole,
        state_source: ResourceStateSource,
    ) -> Result<Self, ResourceSpecError> {
        if !resource.resource_arguments.is_empty() {
            return Err(ResourceSpecError::InvalidNestedTerm(
                "resource arguments require an exclusive instance, not a counted clause".into(),
            ));
        }
        if resource.access != ResourceAccessMode::Own {
            return Err(ResourceSpecError::InvalidAccess {
                family: resource.family(),
                access: resource.access,
            });
        }
        if resource.quantity != ResourceQuantity::One {
            return Err(ResourceSpecError::InvalidQuantity {
                family: resource.family(),
                reason: "a counted resource must wrap a unit term".into(),
            });
        }
        if matches!(
            resource.family(),
            ResourceFamily::Memory | ResourceFamily::Instance
        ) {
            return Err(ResourceSpecError::InvalidQuantity {
                family: resource.family(),
                reason: "this resource family does not support quantities".into(),
            });
        }
        if !matches!(
            resource.term,
            ResourceTerm::Composite { .. } | ResourceTerm::Token { .. }
        ) {
            return Err(ResourceSpecError::InvalidNestedTerm(
                "quantities require an owned unit composite or token term".into(),
            ));
        }
        Self::new(
            resource.term,
            ResourceAccessMode::Own,
            ResourceQuantity::Count(quantity),
            role,
            state_source,
        )
    }

    pub fn quantified_with_quantity_state(
        quantity: ProgramExpression,
        resource: ResourceSpec,
        role: ResourceTransferRole,
        state_source: ResourceStateSource,
        quantity_state_source: ResourceStateSource,
    ) -> Result<Self, ResourceSpecError> {
        let mut spec = Self::quantified(quantity, resource, role, state_source)?;
        spec.quantity_state_source = quantity_state_source;
        Ok(spec)
    }

    pub fn term(&self) -> &ResourceTerm {
        &self.term
    }

    pub(in crate::kernel) fn with_captured_memory_segment(&self, segment: MemorySegment) -> Self {
        debug_assert!(matches!(self.term, ResourceTerm::Memory(_)));
        let mut captured = self.clone();
        captured.term = ResourceTerm::Memory(segment);
        captured
    }

    pub fn with_mutex_authority_binding(
        mut self,
        identity: MutexAuthorityId,
        binder: String,
    ) -> Result<Self, ResourceSpecError> {
        if !matches!(
            self.term,
            ResourceTerm::MutexGuard { .. }
                | ResourceTerm::MutexLive { .. }
                | ResourceTerm::MutexUse { .. }
        ) || self.access != ResourceAccessMode::Own
            || self.quantity != ResourceQuantity::One
            || self.mutex_authority_binding.is_some()
        {
            return Err(ResourceSpecError::InvalidNestedTerm(
                "named mutex authority requires one owned, unbound mutex resource".into(),
            ));
        }
        self.mutex_authority_binding = Some(Arc::new((identity, binder)));
        Ok(self)
    }

    pub fn mutex_authority_binding(&self) -> Option<(MutexAuthorityId, &str)> {
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

    pub fn binding_identity(&self) -> Option<ResourceBinder> {
        self.instance_identity()
            .map(ResourceBinder::Instance)
            .or_else(|| {
                self.mutex_authority_binding()
                    .map(|(identity, _)| ResourceBinder::MutexAuthority(identity))
            })
    }

    pub fn access(&self) -> ResourceAccessMode {
        self.access
    }

    pub fn quantity(&self) -> &ResourceQuantity {
        &self.quantity
    }

    pub fn quantity_state_source(&self) -> ResourceStateSource {
        self.quantity_state_source
    }

    pub fn role(&self) -> ResourceTransferRole {
        self.role
    }

    pub fn state_source(&self) -> ResourceStateSource {
        self.state_source
    }

    pub fn guard(&self) -> Option<&SpecProposition> {
        self.guard.as_ref()
    }

    pub(crate) fn with_view_source(mut self, source: usize) -> Self {
        self.view_source = Some(source);
        self
    }

    pub(crate) fn view_source(&self) -> Option<usize> {
        self.view_source
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

    pub fn with_resource_arguments(mut self, arguments: Vec<InstanceId>) -> Self {
        self.resource_arguments = arguments.into();
        self
    }

    pub fn resource_arguments(&self) -> &[InstanceId] {
        &self.resource_arguments
    }

    /// Capture entry-bound scalar parameters before loop cursor havoc or rebinding.
    /// Current arguments remain state-dependent; source spellings remain intact.
    pub(crate) fn with_captured_entry_parameters(
        mut self,
        entry_values: &impl NamedBindingMap<ProgramValue>,
    ) -> Self {
        fn capture(term: &mut ResourceTerm, entry_values: &impl NamedBindingMap<ProgramValue>) {
            match term {
                ResourceTerm::Instance { resource, .. } => capture(resource, entry_values),
                ResourceTerm::Composite {
                    arguments,
                    argument_state_sources,
                    ..
                }
                | ResourceTerm::Token {
                    arguments,
                    argument_state_sources,
                    ..
                } => {
                    for (argument, state_source) in arguments.iter_mut().zip(argument_state_sources)
                    {
                        if *state_source == ResourceStateSource::Entry
                            && let ProgramExpression::Variable(name) = argument
                            && let Some(value) = name.metadata_in(entry_values)
                        {
                            *argument = ProgramExpression::Value(value.clone());
                        }
                    }
                }
                _ => {}
            }
        }
        capture(&mut self.term, entry_values);
        self
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
        self.access == ResourceAccessMode::View
    }

    pub fn is_instance(&self) -> bool {
        matches!(self.term, ResourceTerm::Instance { .. })
    }

    pub fn instance_identity(&self) -> Option<InstanceId> {
        self.term.instance_identity()
    }

    pub fn instance_binder(&self) -> Option<&str> {
        self.term.instance_binder()
    }

    pub fn instance_schema(&self) -> Option<&ResourceFieldSchema> {
        self.term.instance_schema()
    }

    pub fn instance_resource(&self) -> Option<ResourceTerm> {
        self.term.instance_resource().cloned()
    }

    pub fn instance_resource_spec(&self) -> Option<Self> {
        let resource = self.instance_resource()?;
        Some(
            Self::new(
                resource,
                ResourceAccessMode::Own,
                ResourceQuantity::One,
                self.role,
                self.state_source,
            )
            .expect("validated instance terms have valid owned unit bodies")
            .with_resource_arguments(self.resource_arguments().to_vec()),
        )
    }

    pub fn memory_segment(&self) -> Option<&MemorySegment> {
        self.term.memory_segment()
    }

    pub fn memory_segment_mut(&mut self) -> Option<&mut MemorySegment> {
        match &mut self.term {
            ResourceTerm::Memory(segment) => Some(segment),
            _ => None,
        }
    }

    pub fn declared_name(&self) -> Option<&str> {
        self.term.declared_name()
    }

    pub(crate) fn contained_definition_name(&self) -> Option<&str> {
        let mut term = &self.term;
        while let ResourceTerm::Instance { resource, .. } = term {
            term = resource;
        }
        term.declared_name()
    }

    pub fn declared_arguments(&self) -> Option<&[ProgramExpression]> {
        self.term.declared_arguments()
    }

    pub fn declared_argument_states(&self) -> Option<&[ResourceStateSource]> {
        self.term.declared_argument_states()
    }

    pub fn composite(
        access: ResourceAccessMode,
        name: String,
        arguments: Vec<ProgramExpression>,
        parameter_types: Vec<ProgramType>,
    ) -> Self {
        Self::declared(
            ResourceFamily::Composite,
            access,
            name,
            arguments,
            parameter_types,
            ResourceTransferRole::Consume,
            ResourceStateSource::Current,
        )
        .expect("composite resource terms are valid by construction")
    }

    pub fn token(
        access: ResourceAccessMode,
        name: String,
        arguments: Vec<ProgramExpression>,
        parameter_types: Vec<ProgramType>,
    ) -> Self {
        Self::declared(
            ResourceFamily::Token,
            access,
            name,
            arguments,
            parameter_types,
            ResourceTransferRole::Consume,
            ResourceStateSource::Current,
        )
        .expect("token resource terms are valid by construction")
    }

    pub fn with_role(mut self, role: ResourceTransferRole) -> Self {
        self.role = role;
        self
    }

    pub fn with_state_source(mut self, state_source: ResourceStateSource) -> Self {
        self.state_source = state_source;
        self
    }

    fn validate(&self) -> Result<(), ResourceSpecError> {
        crate::kernel::primitives::resource_algebra::validate_resource_spec(self)
    }
}

// Clause positions are diagnostic metadata, not part of a resource's
// identity.  In particular, the same normalized term may occur in a
// precondition and a postcondition (or in two separately expanded source
// clauses); changing its source position must not change contract identity,
// resource indexing, or equality used by the algebra.
impl PartialEq for ResourceSpec {
    fn eq(&self, other: &Self) -> bool {
        self.term == other.term
            && self.resource_arguments == other.resource_arguments
            && self.mutex_authority_binding == other.mutex_authority_binding
            && self.access == other.access
            && self.quantity == other.quantity
            && self.quantity_state_source == other.quantity_state_source
            && self.role == other.role
            && self.state_source == other.state_source
            && self.guard == other.guard
            && self.view_source == other.view_source
    }
}

impl Eq for ResourceSpec {}

impl Hash for ResourceSpec {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.term.hash(state);
        self.resource_arguments.hash(state);
        self.mutex_authority_binding.hash(state);
        self.access.hash(state);
        self.quantity.hash(state);
        self.quantity_state_source.hash(state);
        self.role.hash(state);
        self.state_source.hash(state);
        self.guard.hash(state);
        self.view_source.hash(state);
    }
}

impl Ord for ResourceSpec {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (
            &self.term,
            &self.resource_arguments,
            &self.mutex_authority_binding,
            self.access,
            &self.quantity,
            self.quantity_state_source,
            self.role,
            self.state_source,
            &self.guard,
            self.view_source,
        )
            .cmp(&(
                &other.term,
                &other.resource_arguments,
                &other.mutex_authority_binding,
                other.access,
                &other.quantity,
                other.quantity_state_source,
                other.role,
                other.state_source,
                &other.guard,
                other.view_source,
            ))
    }
}

impl PartialOrd for ResourceSpec {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod named_mutex_authority_spec_tests {
    use super::*;

    fn authority(term: ResourceTerm) -> ResourceSpec {
        ResourceSpec::new(
            term,
            ResourceAccessMode::Own,
            ResourceQuantity::One,
            ResourceTransferRole::Borrow,
            ResourceStateSource::Current,
        )
        .unwrap()
    }

    #[test]
    fn raw_mutex_authority_bindings_are_typed_and_retained() {
        let mutex = Box::new(ProgramExpression::Value(ProgramValue::pointer(
            Address::symbolic(Variable(700)),
        )));
        for term in [
            ResourceTerm::MutexLive {
                mutex: mutex.clone(),
                state_source: ResourceStateSource::Current,
            },
            ResourceTerm::MutexUse {
                protected: None,
                mutex: mutex.clone(),
                state_source: ResourceStateSource::Current,
            },
            ResourceTerm::MutexGuard {
                mutex: mutex.clone(),
                state_source: ResourceStateSource::Current,
            },
        ] {
            let unnamed = authority(term);
            let named = unnamed
                .clone()
                .with_mutex_authority_binding(
                    MutexAuthorityId::from_variable(Variable(9)),
                    "guard".into(),
                )
                .unwrap();
            assert_eq!(named.term(), unnamed.term());
            assert_eq!(named.family(), unnamed.family());
            assert_eq!(
                named.binding_identity(),
                Some(ResourceBinder::MutexAuthority(
                    MutexAuthorityId::from_variable(Variable(9))
                ))
            );
            assert_eq!(named.instance_identity(), None);
            assert_eq!(
                named.mutex_authority_binding(),
                Some((MutexAuthorityId::from_variable(Variable(9)), "guard"))
            );
            assert_ne!(named, unnamed);
            assert_ne!(named.cmp(&unnamed), std::cmp::Ordering::Equal);
            assert_eq!(
                named
                    .clone()
                    .with_role(ResourceTransferRole::Consume)
                    .with_state_source(ResourceStateSource::Entry)
                    .mutex_authority_binding(),
                Some((MutexAuthorityId::from_variable(Variable(9)), "guard"))
            );
            assert!(
                named
                    .with_mutex_authority_binding(
                        MutexAuthorityId::from_variable(Variable(10)),
                        "another".into()
                    )
                    .is_err()
            );
        }
    }

    #[test]
    fn non_mutex_and_non_exclusive_specs_cannot_be_named_authority() {
        let token = ResourceSpec::token(ResourceAccessMode::Own, "token".into(), vec![], vec![]);
        assert!(
            token
                .with_mutex_authority_binding(
                    MutexAuthorityId::from_variable(Variable(1)),
                    "token".into()
                )
                .is_err()
        );
        let composite =
            ResourceSpec::composite(ResourceAccessMode::Own, "state".into(), vec![], vec![]);
        assert!(
            composite
                .with_mutex_authority_binding(
                    MutexAuthorityId::from_variable(Variable(1)),
                    "state".into()
                )
                .is_err()
        );
        let mutex = Box::new(ProgramExpression::Value(ProgramValue::pointer(
            Address::symbolic(Variable(701)),
        )));
        let viewed = ResourceSpec::new(
            ResourceTerm::MutexGuard {
                mutex: mutex.clone(),
                state_source: ResourceStateSource::Current,
            },
            ResourceAccessMode::View,
            ResourceQuantity::One,
            ResourceTransferRole::Borrow,
            ResourceStateSource::Current,
        );
        assert!(viewed.is_err());
        let counted = ResourceSpec::new(
            ResourceTerm::MutexGuard {
                mutex,
                state_source: ResourceStateSource::Current,
            },
            ResourceAccessMode::Own,
            ResourceQuantity::Count(ProgramExpression::Value(int32(2))),
            ResourceTransferRole::Borrow,
            ResourceStateSource::Current,
        );
        assert!(counted.is_err());
    }
}

#[cfg(test)]
mod population_authority_spec_tests {
    use super::*;

    fn authority_type(resource: ResourceSpec) -> ResourceTerm {
        ResourceTerm::PopulationAuthority {
            population_arity: None,
            protected: Box::new(ResourceTypeSpec {
                resource: Box::new(resource),
                schema: ResourceFieldSchema::new(vec![]).unwrap(),
            }),
            state_source: ResourceStateSource::Current,
        }
    }

    #[test]
    fn authority_requires_exclusive_unit_declared_type() {
        for resource in [
            ResourceSpec::composite(ResourceAccessMode::Own, "node".into(), vec![], vec![]),
            ResourceSpec::token(ResourceAccessMode::Own, "node".into(), vec![], vec![]),
        ] {
            let term = authority_type(resource);
            assert!(
                ResourceSpec::new(
                    term.clone(),
                    ResourceAccessMode::Own,
                    ResourceQuantity::One,
                    ResourceTransferRole::Borrow,
                    ResourceStateSource::Current,
                )
                .is_ok()
            );
            assert!(
                ResourceSpec::new(
                    term.clone(),
                    ResourceAccessMode::View,
                    ResourceQuantity::One,
                    ResourceTransferRole::Borrow,
                    ResourceStateSource::Current,
                )
                .is_err()
            );
            assert!(
                ResourceSpec::new(
                    term,
                    ResourceAccessMode::Own,
                    ResourceQuantity::Count(ProgramExpression::Value(int32(2))),
                    ResourceTransferRole::Borrow,
                    ResourceStateSource::Current,
                )
                .is_err()
            );
        }
    }

    #[test]
    fn authority_cannot_be_composed_twice_or_split() {
        let description = super::super::ResourceDescription::new(
            "node".into(),
            Vec::<AlgebraicValue>::new().into(),
            ResourceFieldSchema::new(vec![]).unwrap(),
        );
        let fact = ResourceFact::own(Resource::PopulationAuthority(description.clone()));
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
                    ResourceFact::View(Resource::PopulationAuthority(description.clone())),
                    &assumptions,
                )
                .is_err()
        );
        assert!(
            ResourceContext::new()
                .try_compose_with_fact(
                    ResourceFact::Own(
                        Resource::PopulationAuthority(description.clone()),
                        Box::new(OldMachineTerm::constant(2).into()),
                    ),
                    &assumptions,
                )
                .is_err()
        );
        assert!(
            ResourceFact::View(Resource::PopulationAuthority(description))
                .core()
                .is_none()
        );
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Term {
    Condition(StoredConditionTerm),
    Bitvector32(StoredMachineTerm),
    Integer(StoredIntegerTerm),
    PointerOffset(StoredPointerOffset),
    ProgramValue(StoredProgramValue),
    Sequence(SequenceTerm),
    Algebraic(StoredAlgebraicTerm),
    // Outcomes carry ExecutionState. Keep them out of Term's inline size so cloning
    // a deep pure proposition does not spend stack on unused C variants.
    /// The source point of the following pointer in a predicate array argument.
    ArrayReadPoint(ProgramPoint),
    ExecutionState(Box<ExecutionState>),
}

impl Term {
    /// Consume an owned payload without cloning its native expression prefix.
    pub(crate) fn into_program_value_native(self) -> Option<ProgramValue> {
        match self {
            Self::ProgramValue(value) => Some(value.into()),
            _ => None,
        }
    }

    /// Selected native payload views. Storage and producers retain their own
    /// carriers; structural consumers name the compatibility reading explicitly.
    pub(crate) fn old_condition(&self) -> Option<&OldConditionTerm> {
        match self {
            Self::Condition(value) => Some(value.old_form()),
            _ => None,
        }
    }
    #[cfg(test)]
    pub(crate) fn bitvector_native(&self) -> Option<&OldMachineTerm> {
        match self {
            Self::Bitvector32(value) => Some(value.old_form()),
            _ => None,
        }
    }
    #[cfg(test)]
    pub(crate) fn integer_native(&self) -> Option<&IntegerTerm> {
        match self {
            Self::Integer(value) => Some(value.old_form()),
            _ => None,
        }
    }
    pub(crate) fn program_value_native(&self) -> Option<&ProgramValue> {
        match self {
            Self::ProgramValue(value) => Some(value.old_form()),
            _ => None,
        }
    }
    pub(crate) fn algebraic_native(&self) -> Option<&AlgebraicTerm> {
        match self {
            Self::Algebraic(value) => Some(value.old_form()),
            _ => None,
        }
    }
}

#[cfg(test)]
mod term_payload_view_tests {
    use super::*;

    #[test]
    fn owned_program_value_extraction_moves_native_address_prefixes() {
        for size in [16, 64, 256] {
            let mut offset = AddressOffset::constant(0);
            for index in 0..size {
                offset = AddressOffset::raw_add(
                    offset,
                    AddressOffset::variable(Variable(991300 + index)),
                );
            }
            let value = ProgramValue::pointer(Address::new(
                AddressBase::PureFunctionApplication(SharedPureApplication::intern(
                    "owned_native_pointer_result".into(),
                    Vec::new(),
                )),
                offset,
            ));
            let ProgramValue::Pointer(pointer) = &value else {
                unreachable!()
            };
            let OffsetView::Add(left, right) = pointer.address().offset.view() else {
                unreachable!()
            };
            let allocations = [std::ptr::from_ref(left), std::ptr::from_ref(right)];
            let Some(ProgramValue::Pointer(pointer)) =
                Term::ProgramValue(value.into()).into_program_value_native()
            else {
                unreachable!()
            };
            let address = pointer.into_pointer();
            let OffsetView::Add(left, right) = address.offset.view() else {
                unreachable!()
            };
            assert_eq!(
                [std::ptr::from_ref(left), std::ptr::from_ref(right)],
                allocations,
                "the owned result's address nodes must move, size={size}",
            );
        }
    }
}

/// The source name of a universal's binder, carried for diagnostics only.
///
/// It never distinguishes two propositions: equality, ordering, and hashing
/// ignore it, so `forall (a: int32) { P }` and `forall (b: int32) { P }` over
/// the same variable are one fact. A binder built by Click carries none.
#[derive(Clone, Default)]
pub struct BinderName(Option<std::sync::Arc<str>>);

impl BinderName {
    pub fn binding(name: &BindingName) -> Self {
        name.named().map(Self::written).unwrap_or_default()
    }
    pub fn written(name: &str) -> Self {
        Self((!name.is_empty()).then(|| name.into()))
    }

    pub fn as_str(&self) -> Option<&str> {
        self.0.as_deref()
    }
}

/// The written names of a match arm's bindings, in order, carried for
/// diagnostics only. Like [`BinderName`], it never distinguishes two terms.
#[derive(Clone, Default)]
pub struct BindingNames(Option<std::sync::Arc<[BinderName]>>);

impl BindingNames {
    pub fn bindings(names: &[BindingName]) -> Self {
        Self((!names.is_empty()).then(|| names.iter().map(BinderName::binding).collect()))
    }
    pub fn written(names: &[String]) -> Self {
        Self(
            (!names.is_empty())
                .then(|| names.iter().map(|name| BinderName::written(name)).collect()),
        )
    }

    pub fn get(&self, index: usize) -> Option<&str> {
        self.0.as_deref()?.get(index)?.as_str()
    }
}

impl std::fmt::Debug for BindingNames {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("_")
    }
}

impl PartialEq for BindingNames {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl Eq for BindingNames {}

impl PartialOrd for BindingNames {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BindingNames {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

impl Hash for BindingNames {
    fn hash<H: Hasher>(&self, _: &mut H) {}
}

impl std::fmt::Debug for BinderName {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("_")
    }
}

impl PartialEq for BinderName {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl Eq for BinderName {}

impl PartialOrd for BinderName {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BinderName {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

impl Hash for BinderName {
    fn hash<H: Hasher>(&self, _: &mut H) {}
}

/// The nominal identity of one completed sequential volatile access.
/// This is not a binder, a C value, or permission to access memory.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct VolatileEventId(pub(crate) u64);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum VolatileAccessKind {
    Read,
    Write,
}

/// Kernel-produced evidence of one access. Equal addresses and values do
/// not identify distinct events. Read results are exposed by source region
/// through `read_event(i).result`, independently of this nominal identity.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct VolatileAccess {
    pub(crate) id: VolatileEventId,
    pub(crate) kind: VolatileAccessKind,
    pub(crate) pointer: Address,
    pub(crate) value_type: ProgramType,
    pub(crate) value: StoredProgramValue,
}

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum KernelProposition {
    VolatileAccess(Arc<VolatileAccess>),
    Equal(Term, Term),
    SequenceMembership {
        element: StoredProgramValue,
        sequence: SequenceTerm,
    },
    ConditionIs(StoredConditionTerm, bool),
    Predicate {
        name: String,
        arguments: Vec<Term>,
    },
    ProgramExpressionEvaluates {
        state: Box<ExecutionState>,
        expression: ProgramExpression,
        outcome: ExpressionOutcome<StoredProgramValue>,
    },
    ProgramConditionEvaluates {
        state: Box<ExecutionState>,
        condition: ProgramExpression,
        outcome: ConditionOutcome,
    },
    /// An abstract verification transition: the outcome is one a checked
    /// run admits, not a claim that it is concretely reachable.
    ProgramStatementVerifies {
        state: Box<ExecutionState>,
        statement: Box<ProgramStatement>,
        outcome: StatementOutcome,
    },
    /// A return branch admitted by modular verification. This is conditional
    /// on the function returning and is not a termination or reachability
    /// theorem.
    ProgramFunctionVerifies {
        state: Box<ExecutionState>,
        function: Box<ProgramFunction>,
        arguments: Vec<ProgramExpression>,
        outcome: FunctionOutcome,
    },
    /// The specification describes one allowed return branch and makes no
    /// claim that the branch is reachable or that the function terminates.
    ProgramFunctionPartiallySatisfiesSpecification {
        function: Box<ProgramFunction>,
        // Large C payloads stay out of every pure proposition clone frame.
        specification: Box<FunctionSpecification>,
    },
    MemoryLoads {
        memory: SymbolicMemory,
        /// The point `memory` is the state at; not part of the fact's
        /// equality ([`program_point::PathLink`]).
        point: program_point::PathLink,
        pointer: Address,
        outcome: ExpressionOutcome<StoredProgramValue>,
    },
    MemoryCanStore {
        memory: SymbolicMemory,
        /// The point `memory` is the state at; not part of the fact's
        /// equality ([`program_point::PathLink`]).
        point: program_point::PathLink,
        pointer: Address,
        byte_width: u32,
    },
    /// `bytes` bytes at `base` are live in `memory`. The count is a 32-bit
    /// term, or, when `wide`, an unsigned 64-bit one: a term carries no
    /// width, so a reader that takes a wide count as 32 bits misreads it.
    MemoryLoadable {
        memory: SymbolicMemory,
        /// The point `memory` is the state at; not part of the fact's
        /// equality ([`program_point::PathLink`]).
        point: program_point::PathLink,
        base: Address,
        bytes: StoredMachineTerm,
        wide: bool,
    },
    /// A typed read is valid in this state, including initialization.
    /// The point records where the observation was made. Memory provides
    /// its initialization and lifetime information. Synthetic memory
    /// queries can have no recorded point.
    MemoryReadDefined {
        at: Option<program_point::ProgramPointId>,
        memory: SymbolicMemory,
        /// The point `memory` is the state at; not part of the fact's
        /// equality ([`program_point::PathLink`]), unlike `at`.
        point: program_point::PathLink,
        pointer: Address,
        value_type: ProgramType,
    },
    ResourceSeparate {
        left: Box<Resource>,
        right: Box<Resource>,
    },
    /// Internal carrier for an already-validated resource composition.
    /// PureFactContext store this as indexed kernel authority rather than as an
    /// ambient proposition visible to proof search.
    ResourceComposition(ResourceContext),
    ResourceViewable {
        memory: SymbolicMemory,
        /// The point `memory` is the state at; not part of the fact's
        /// equality ([`program_point::PathLink`]).
        point: program_point::PathLink,
        resource: Box<Resource>,
    },
    ResourceContains {
        parent: Box<Resource>,
        child: Box<Resource>,
    },
    /// Internal write bound for a recorded transition, using constant byte
    /// counts. Listed ranges may conservatively include bytes that were not
    /// written. Preservation proofs use recorded region footprints; allocation
    /// lifetime effects are recorded separately.
    MemoryMutatesOnly {
        before: SymbolicMemory,
        /// The point `before` is the state at; not part of the fact's
        /// equality ([`program_point::PathLink`]).
        before_point: program_point::PathLink,
        after: SymbolicMemory,
        /// The point `after` is the state at.
        after_point: program_point::PathLink,
        writes: Vec<(Address, AccessExtent)>,
    },
    /// Internal write bound expressed as [`MemoryRange`] descriptors, including
    /// symbolic spans. Like [`Self::MemoryMutatesOnly`], this bounds possible
    /// writes rather than claiming that every listed cell changed.
    MemoryEffectSummary {
        before: SymbolicMemory,
        /// The point `before` is the state at. Not part of the fact's
        /// equality, hashing or order ([`program_point::PathLink`]).
        before_point: program_point::PathLink,
        after: SymbolicMemory,
        /// The point `after` is the state at.
        after_point: program_point::PathLink,
        mutable_ranges: Vec<MemoryRange>,
    },
    /// Frees of the heap blocks in `blocks`, each at its base with its size,
    /// which keeps its format, so a 64-bit block's free reinstates a 64-bit
    /// claim. Between `before` and `after` only these blocks and
    /// `mutable_ranges` change: a `free` statement frees one block and
    /// changes nothing else; a call's exit frees every block its allocation
    /// effects retire, and its other effects (the claims it retires or
    /// makes and the memory it produces) are its mutable ranges.
    HeapAllocationFreed {
        before: SymbolicMemory,
        /// The point `before` is the state at; not part of the fact's
        /// equality ([`program_point::PathLink`]).
        before_point: program_point::PathLink,
        after: SymbolicMemory,
        /// The point `after` is the state at.
        after_point: program_point::PathLink,
        blocks: Vec<(Address, AllocationSize)>,
        mutable_ranges: Vec<MemoryRange>,
    },
    And(Box<KernelProposition>, Box<KernelProposition>),
    Or(Box<KernelProposition>, Box<KernelProposition>),
    Not(Box<KernelProposition>),
    Implies(Box<KernelProposition>, Box<KernelProposition>),
    ForAll {
        var: QuantifierBinder,
        sort: Sort,
        body: Box<KernelProposition>,
        /// The binder's written name, for printing only.
        name: BinderName,
    },
    Exists {
        name: String,
        var: QuantifierBinder,
        sort: Sort,
        body: Box<KernelProposition>,
    },
}

/// Compatibility name for [`KernelProposition`].
pub use self::KernelProposition as Proposition;

impl KernelProposition {
    /// Store an exact native input or an already-retained logical condition.
    pub fn condition_is(condition: impl Into<StoredConditionTerm>, truth: bool) -> Self {
        Self::ConditionIs(condition.into(), truth)
    }

    /// The written Boolean literal and its asserted polarity. Compound
    /// conditions keep their spelling even when their value is known.
    pub(crate) fn literal_condition(&self) -> Option<(bool, bool)> {
        let Self::ConditionIs(condition, polarity) = self else {
            return None;
        };
        Some((condition.operand_view().constant()?, *polarity))
    }

    /// Selected native condition-payload inspection. This view borrows the
    /// original payload and truth marker without rebuilding a proposition.
    pub(crate) fn old_condition(&self) -> Option<(&OldConditionTerm, &bool)> {
        match self {
            Self::ConditionIs(condition, truth) => Some((condition.old_form(), truth)),
            _ => None,
        }
    }

    /// The two ranges of a separation between two memory resources.
    pub(crate) fn memory_separation(&self) -> Option<(&MemoryRange, &MemoryRange)> {
        match self {
            Self::ResourceSeparate { left, right } => match (&**left, &**right) {
                (Resource::Memory(left), Resource::Memory(right)) => Some((left, right)),
                _ => None,
            },
            _ => None,
        }
    }

    /// The parent and the child range of a containment of a memory resource.
    #[cfg(test)]
    pub(crate) fn memory_containment(&self) -> Option<(&Resource, &MemoryRange)> {
        match self {
            Self::ResourceContains { parent, child } => match &**child {
                Resource::Memory(range) => Some((parent, range)),
                _ => None,
            },
            _ => None,
        }
    }
}

impl Clone for KernelProposition {
    fn clone(&self) -> Self {
        clone_proposition_iteratively(self)
    }
}

impl Hash for KernelProposition {
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
                Proposition::ForAll {
                    var, sort, body, ..
                } => {
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
/// equality. Every field hashes structurally; a memory state hashes by its
/// cached content hash in O(1). Hashing an atom's debug text instead printed
/// every state it names, so inserting or looking up a call's effect summary
/// cost the size of the whole memory, and each later call in a long function
/// paid more than the last.
fn hash_atomic_proposition<H: Hasher>(atomic: &Proposition, state: &mut H) {
    std::mem::discriminant(atomic).hash(state);
    match atomic {
        Proposition::VolatileAccess(event) => event.hash(state),
        Proposition::Equal(left, right) => {
            left.hash(state);
            right.hash(state);
        }
        Proposition::SequenceMembership { element, sequence } => {
            element.hash(state);
            sequence.hash(state);
        }
        Proposition::ConditionIs(condition, value) => {
            condition.hash(state);
            value.hash(state);
        }
        Proposition::Predicate { name, arguments } => {
            name.hash(state);
            arguments.hash(state);
        }
        Proposition::ProgramExpressionEvaluates {
            state: c_state,
            expression,
            outcome,
        } => {
            c_state.hash(state);
            expression.hash(state);
            outcome.hash(state);
        }
        Proposition::ProgramConditionEvaluates {
            state: c_state,
            condition,
            outcome,
        } => {
            c_state.hash(state);
            condition.hash(state);
            outcome.hash(state);
        }
        Proposition::ProgramStatementVerifies {
            state: c_state,
            statement,
            outcome,
        } => {
            c_state.hash(state);
            statement.hash(state);
            outcome.hash(state);
        }
        Proposition::ProgramFunctionVerifies {
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
        Proposition::ProgramFunctionPartiallySatisfiesSpecification {
            function,
            specification,
        } => {
            function.hash(state);
            specification.hash(state);
        }
        Proposition::MemoryLoads {
            memory,
            pointer,
            outcome,
            ..
        } => {
            memory.hash(state);
            pointer.hash(state);
            outcome.hash(state);
        }
        Proposition::MemoryCanStore {
            memory,
            pointer,
            byte_width,
            ..
        } => {
            memory.hash(state);
            pointer.hash(state);
            byte_width.hash(state);
        }
        Proposition::MemoryLoadable {
            memory,
            base,
            bytes,
            wide,
            ..
        } => {
            memory.hash(state);
            base.hash(state);
            bytes.hash(state);
            wide.hash(state);
        }
        Proposition::MemoryReadDefined {
            at,
            memory,
            pointer,
            value_type,
            ..
        } => {
            at.hash(state);
            memory.hash(state);
            pointer.hash(state);
            value_type.hash(state);
        }
        Proposition::ResourceSeparate { left, right } => {
            left.hash(state);
            right.hash(state);
        }
        Proposition::ResourceComposition(resources) => resources.hash(state),
        Proposition::ResourceViewable {
            memory, resource, ..
        } => {
            memory.hash(state);
            resource.hash(state);
        }
        Proposition::ResourceContains { parent, child } => {
            parent.hash(state);
            child.hash(state);
        }
        Proposition::MemoryMutatesOnly {
            before,
            after,
            writes,
            ..
        } => {
            before.hash(state);
            after.hash(state);
            writes.hash(state);
        }
        Proposition::MemoryEffectSummary {
            before,
            after,
            mutable_ranges,
            ..
        } => {
            before.hash(state);
            after.hash(state);
            mutable_ranges.hash(state);
        }
        Proposition::HeapAllocationFreed {
            before,
            after,
            blocks,
            mutable_ranges,
            ..
        } => {
            before.hash(state);
            after.hash(state);
            blocks.hash(state);
            mutable_ranges.hash(state);
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
            var: QuantifierBinder,
            sort: Sort,
            name: BinderName,
        },
        BuildExists {
            name: String,
            var: QuantifierBinder,
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
                Proposition::ForAll {
                    var,
                    sort,
                    body,
                    name,
                } => {
                    frames.push(Frame::BuildForAll {
                        var: *var,
                        sort: sort.clone(),
                        name: name.clone(),
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
            Frame::BuildForAll { var, sort, name } => {
                let body = values.pop().expect("the forall body is cloned");
                values.push(Proposition::ForAll {
                    var,
                    sort,
                    name,
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
        Proposition::VolatileAccess(event) => Proposition::VolatileAccess(event.clone()),
        Proposition::Equal(left, right) => Proposition::Equal(left.clone(), right.clone()),
        Proposition::SequenceMembership { element, sequence } => Proposition::SequenceMembership {
            element: element.clone(),
            sequence: sequence.clone(),
        },
        Proposition::ConditionIs(condition, value) => {
            Proposition::condition_is(condition.clone(), *value)
        }
        Proposition::Predicate { name, arguments } => Proposition::Predicate {
            name: name.clone(),
            arguments: arguments.clone(),
        },
        Proposition::ProgramExpressionEvaluates {
            state,
            expression,
            outcome,
        } => Proposition::ProgramExpressionEvaluates {
            state: state.clone(),
            expression: expression.clone(),
            outcome: outcome.clone(),
        },
        Proposition::ProgramConditionEvaluates {
            state,
            condition,
            outcome,
        } => Proposition::ProgramConditionEvaluates {
            state: state.clone(),
            condition: condition.clone(),
            outcome: outcome.clone(),
        },
        Proposition::ProgramStatementVerifies {
            state,
            statement,
            outcome,
        } => Proposition::ProgramStatementVerifies {
            state: state.clone(),
            statement: statement.clone(),
            outcome: outcome.clone(),
        },
        Proposition::ProgramFunctionVerifies {
            state,
            function,
            arguments,
            outcome,
        } => Proposition::ProgramFunctionVerifies {
            state: state.clone(),
            function: function.clone(),
            arguments: arguments.clone(),
            outcome: outcome.clone(),
        },
        Proposition::ProgramFunctionPartiallySatisfiesSpecification {
            function,
            specification,
        } => Proposition::ProgramFunctionPartiallySatisfiesSpecification {
            function: function.clone(),
            specification: specification.clone(),
        },
        Proposition::MemoryLoads {
            memory,
            pointer,
            outcome,
            point,
        } => Proposition::MemoryLoads {
            point: point.clone(),
            memory: memory.clone(),
            pointer: pointer.clone(),
            outcome: outcome.clone(),
        },
        Proposition::MemoryCanStore {
            memory,
            pointer,
            byte_width,
            point,
        } => Proposition::MemoryCanStore {
            point: point.clone(),
            memory: memory.clone(),
            pointer: pointer.clone(),
            byte_width: *byte_width,
        },
        Proposition::MemoryLoadable {
            memory,
            base,
            bytes,
            wide,
            point,
        } => Proposition::MemoryLoadable {
            point: point.clone(),
            memory: memory.clone(),
            base: base.clone(),
            bytes: bytes.clone(),
            wide: *wide,
        },
        Proposition::MemoryReadDefined {
            at,
            memory,
            pointer,
            value_type,
            point,
        } => Proposition::MemoryReadDefined {
            point: point.clone(),
            at: *at,
            memory: memory.clone(),
            pointer: pointer.clone(),
            value_type: *value_type,
        },
        Proposition::ResourceSeparate { left, right } => Proposition::ResourceSeparate {
            left: left.clone(),
            right: right.clone(),
        },
        Proposition::ResourceComposition(resources) => {
            Proposition::ResourceComposition(resources.clone())
        }
        Proposition::ResourceViewable {
            memory,
            point,
            resource,
        } => Proposition::ResourceViewable {
            memory: memory.clone(),
            point: point.clone(),
            resource: resource.clone(),
        },
        Proposition::ResourceContains { parent, child } => Proposition::ResourceContains {
            parent: parent.clone(),
            child: child.clone(),
        },
        Proposition::MemoryMutatesOnly {
            before,
            after,
            writes,
            before_point,
            after_point,
        } => Proposition::MemoryMutatesOnly {
            before_point: before_point.clone(),
            after_point: after_point.clone(),
            before: before.clone(),
            after: after.clone(),
            writes: writes.clone(),
        },
        Proposition::MemoryEffectSummary {
            before,
            after,
            mutable_ranges,
            before_point,
            after_point,
        } => Proposition::MemoryEffectSummary {
            before: before.clone(),
            before_point: before_point.clone(),
            after: after.clone(),
            after_point: after_point.clone(),
            mutable_ranges: mutable_ranges.clone(),
        },
        Proposition::HeapAllocationFreed {
            before,
            after,
            blocks,
            mutable_ranges,
            before_point,
            after_point,
        } => Proposition::HeapAllocationFreed {
            before_point: before_point.clone(),
            after_point: after_point.clone(),
            before: before.clone(),
            after: after.clone(),
            blocks: blocks.clone(),
            mutable_ranges: mutable_ranges.clone(),
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
                Proposition::ForAll {
                    var, sort, body, ..
                },
                Proposition::ForAll {
                    var: other_var,
                    sort: other_sort,
                    body: other_body,
                    ..
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
#[derive(Clone)]
pub struct Theorem {
    pub(super) proposition: std::sync::Arc<Proposition>,
    // Condition evaluation shares its ambient premises until a consumer
    // asks for the standalone proposition. The syntax above already holds
    // the path-local premises and obligations in their original order.
    deferred_premises: Option<std::sync::Arc<DeferredTheoremPremises>>,
}

struct DeferredTheoremPremises {
    propositions: super::fact_collections::FactSet<Proposition>,
    conditions: super::fact_collections::FactMap<OldConditionTerm, bool>,
    standalone: OnceLock<Proposition>,
}

/// Kernel-issued authority for a closed pure theorem that may be used during
/// whole-contract certification. The private field prevents the Click layer
/// from promoting an arbitrary proposition or unrelated theorem object.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedPureTheorem {
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
pub struct FunctionContractRefinementContext {
    pub(super) object_type_requirements: ObjectTypeRequirements,
    pub(super) contract: FunctionContract,
    /// The implementation side of refinement is an interface judgment too;
    /// concrete body evidence is checked before this context is opened and is
    /// not needed to lower the symbolic relation.
    pub(super) function_interface: FunctionContractInterface,
    pub(super) function_name: String,
    pub(super) pointer: Pointer,
    pub(super) source_contract: Option<FunctionContract>,
    /// The values a fact fixed for the implementation side's own value
    /// parameters, when that side is a named contract found through one.
    pub(super) function_value_arguments: Vec<ProgramValue>,
    pub(super) argument_values: Vec<ProgramValue>,
    pub(super) result_variable: Variable,
    /// The mark the budget that invented `argument_values` reached,
    /// execution-relative: the refinement obligations continue from it
    /// rather than restarting the counter over arguments already issued.
    pub(super) next_kernel_variable: u64,
}

/// Kernel-generated sufficient logical obligations for one contract relation.
/// The states and proposition cannot be supplied by the language layer.
pub struct FunctionContractRefinementObligations {
    pub(super) context: FunctionContractRefinementContext,
    pub(super) entry: ExecutionState,
    pub(super) post: ExecutionState,
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
    pub(super) lower: super::assumptions::checked_scalar_facts::ScalarOperandKey,
    pub(super) upper: super::assumptions::checked_scalar_facts::ScalarOperandKey,
    pub(super) strict: bool,
    pub(super) premise: Proposition,
}

/// One exact order edge, retained in its original orientation and
/// polarity. Checking reads its endpoints from the premise's operand views.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OrderDerivationStep {
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
    pub(super) source: SharedMachineIntegerTerm,
    pub(super) target: SharedMachineIntegerTerm,
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
        left: SharedMachineIntegerTerm,
        right: SharedMachineIntegerTerm,
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

/// One selected source and its optional exact constant equality. Endpoints
/// and strictness are read from the source, rather than copied into trees.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct IndexedSignedOrderBoundEvidence {
    pub(in crate::kernel) other_equality: Option<Box<Proposition>>,
    pub(in crate::kernel) forward: bool,
    pub(in crate::kernel) source: Box<Proposition>,
}

/// Evidence that two load variables name one cell because their
/// registered origins have the same memory version and block and congruent
/// offsets. The original variables remain distinct context-free names.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LoadAddressCongruenceEvidence {
    pub(super) left_pointer: Address,
    pub(super) right_pointer: Address,
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
    pub(crate) fn context(&self) -> crate::kernel::SelectedFacts<'static> {
        crate::kernel::SelectedFacts::from_propositions(&self.propositions)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum PropositionDerivationRule {
    ContextFree,
    ContextualAtomic {
        premises: RetainedPremises,
        premises_id: u64,
        extended_rules: bool,
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
    /// A universal from its body opened at `witness`, a free variable that
    /// no premise the proof cites mentions.
    ForAllBody {
        witness: Variable,
        proof: Box<PropositionDerivation>,
    },
    /// Open an exact existential fact and the goal at a fresh witness. The
    /// opened fact supplies local assumptions to the proof of the goal body.
    ExistsFromFact {
        source: Box<Proposition>,
        witness: Variable,
        body: Box<PropositionDerivation>,
    },
    /// Prove an existential by selecting a free witness term and checking the
    /// substituted body against the current context.
    ExistsFromWitness {
        witness: OldMachineTerm,
        body: Box<PropositionDerivation>,
    },
    /// Prove an in-range one-byte loadability universal from one exact wider
    /// loadability range and the universal body's guard premises.
    ForAllLoadableRange {
        source: Box<Proposition>,
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
    pub(crate) argument: OldMachineTerm,
    pub(crate) guard_premises: Vec<Proposition>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum AtomicPropositionDerivationEvidence {
    WidenedUnsignedSumBound,
    MemoryDag(Box<AtomicMemoryLoadEqualityEvidence>),
    LoadAddressCongruence(Box<LoadAddressCongruenceEvidence>),
    PointerOffsetMemoryDag(Box<AddressOffsetEqualityEvidence>),
    BitvectorEqualityPath(Vec<BitvectorEqualityDerivationStep>),
    Int32PinnedConstantEquality(Box<DirectBitvectorEqualityEvidence>),
    ForallInt32Instantiation(Box<ForallInt32InstantiationEvidence>),
    SignedOrderPath(Vec<OrderDerivationStep>),
    /// A chain of exact order facts at `format`, a 64-bit format or
    /// `uint32`, each step's premise in the context as written.
    WideOrderPath {
        format: MachineIntegerType,
        path: Vec<OrderDerivationStep>,
    },
    Int32IncrementUpperBound(Box<SignedOrderDerivationStep>),
    Int32IncrementConstantUpperBound(Box<SignedOrderDerivationStep>),
    Int32IncrementStrictlyIncreases(Box<SignedOrderDerivationStep>),
    Int32IncrementBelowMaxIsDefined(Box<Proposition>),
    Int32OnePlusBelowMaxIsDefined(Box<Proposition>),
    Int32OnePlusStrictlyIncreases(Box<SignedOrderDerivationStep>),
    Int32NonnegativeAddWithinMaxIsDefined(Box<[Proposition; 2]>),
    Int32NonnegativeSubtractWithinValueIsDefined(Box<[Proposition; 2]>),
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
    Block(AddressBase),
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
    Condition(&'a OldConditionTerm, bool),
    Proposition(&'a Proposition),
}
impl AtomicConnectedFact<'_> {
    pub(crate) fn identity(&self) -> (u8, usize) {
        match self {
            Self::Condition(condition, _) => (0, *condition as *const OldConditionTerm as usize),
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
                matches!(goal, Proposition::ConditionIs(c,v) if c.old_form() == *condition && v == value)
            }
            Self::Proposition(proposition) => *proposition == goal,
        }
    }
    pub(crate) fn to_proposition(&self) -> Proposition {
        match self {
            Self::Condition(condition, value) => {
                Proposition::condition_is((*condition).clone(), *value)
            }
            Self::Proposition(proposition) => (*proposition).clone(),
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(super) struct AtomicConnectionFacts {
    pub conditions: crate::persistent::PersistentSet<SharedIndexFact<Proposition>>,
    pub propositions: crate::persistent::PersistentSet<SharedIndexFact<Proposition>>,
    pub disjunctions: crate::persistent::PersistentSet<SharedIndexFact<Proposition>>,
}

/// The representation and deferral choices a context reasons under, one bit
/// each. The bits occupy the top byte of the context's content fingerprint.
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
    /// Evaluate a contract entry's own clauses: a clause through a pointer
    /// with opaque bounds states what the bounds cover, so it is not
    /// checked against it (`design/pointer-subobject-bounds.md`, Phase C).
    pub(super) const ASSUME_ENTRY_CLAUSE_SPANS: Self = Self(1 << 8);
    /// A held resource carries the arithmetic domains established by its fold.
    pub(super) const ASSUME_HELD_RESOURCE_DOMAINS: Self = Self(1 << 9);
    pub(super) const RETAIN_REQUIRED_OBLIGATIONS: Self = Self(1 << 10);
    pub(super) const RETAIN_ARGUMENT_DOMAINS: Self = Self(1 << 11);

    pub(super) fn contains(self, choice: Self) -> bool {
        self.0 & choice.0 != 0
    }

    pub(super) fn fingerprint(self) -> u64 {
        u64::from(self.0) << 48
    }

    pub(super) fn toggle(&mut self, choice: Self) {
        self.0 ^= choice.0;
    }
}

#[derive(Clone, Debug, Default)]
pub struct PureFactContext {
    /// Debug builds only: the width each variable of this context's facts is
    /// used at (`term_width.rs`). Two facts combine only within one context,
    /// so a variable must keep one width within it. Not part of equality.
    pub(super) variable_widths: imbl::OrdMap<Variable, CarrierWidth>,
    /// Shared ordered projection used when checked paths publish this context.
    pub(super) execution_fact_projection: super::execution_facts::ContextFacts,
    /// Persistent syntax adjacency for atomic certificate planning. Unlike
    /// free-variable indexes, this never scans state contents.
    pub(super) atomic_connection_facts:
        crate::persistent::PersistentMap<AtomicConnectionKey, AtomicConnectionFacts>,
    pub(super) atomic_ground_facts:
        crate::kernel::fact_collections::ScanSet<SharedIndexFact<Proposition>>,
    pub(super) atomic_quantified_facts:
        crate::kernel::fact_collections::ScanSet<SharedIndexFact<Proposition>>,
    /// The universal facts filed under each shape their conclusion takes
    /// (`UniversalConclusionKey`), so an instantiation reads the universals
    /// that can conclude its goal, not every universal.
    pub(super) universals_by_conclusion: crate::persistent::PersistentMap<
        super::assumptions::UniversalConclusionKey,
        crate::persistent::PersistentSet<SharedIndexFact<Proposition>>,
    >,
    /// One retained source per alpha/load identity of an explicit universal
    /// equality or its selected operand. Range-guard checking never enumerates
    /// the context's equality universals.
    pub(super) universal_equality_sources: crate::persistent::PersistentMap<
        crate::kernel::proof::PropositionIdentityKey,
        (std::sync::Arc<Proposition>, bool),
    >,
    pub(super) condition_facts: super::fact_collections::FactMap<OldConditionTerm, bool>,
    pub(super) signed_variable_chains: super::assumptions::variable_chains::VariableChains,
    /// Incremental adjacency for conditions whose variables can be read
    /// without inspecting a state.
    pub(super) shared_condition_variables: super::assumptions::shared_condition_variables::Index,
    pub(super) condition_facts_by_variable: crate::persistent::PersistentMap<
        Variable,
        crate::persistent::PersistentMap<SharedIndexFact<OldConditionTerm>, bool>,
    >,
    /// MemoryState-dependent conditions use the complete collector only when
    /// smart premise selection asks for them. Scalar updates share the cache.
    pub(super) state_condition_variable_base: crate::persistent::PersistentMap<
        Variable,
        crate::persistent::PersistentMap<SharedIndexFact<OldConditionTerm>, bool>,
    >,
    pub(super) state_condition_variable_changes:
        crate::persistent::PersistentMap<OldConditionTerm, bool>,
    pub(super) state_condition_variables: std::sync::Arc<
        std::sync::OnceLock<
            crate::persistent::PersistentMap<
                Variable,
                crate::persistent::PersistentMap<SharedIndexFact<OldConditionTerm>, bool>,
            >,
        >,
    >,
    /// The condition facts `condition_matches` can relate to a query spelled
    /// differently, keyed by their kind and the canonical forms of their two
    /// sides (`condition_match_key`): an equality under its unordered pair of
    /// sides, a 32-bit order under its signedness, strictness and lower and
    /// upper side, whichever way it was written. Any other fact matches a query
    /// only when it is that query, which is the exact lookup. A query then
    /// reads the keys its own sides and their recorded-equality classes
    /// spell, so `has_condition_fact` never visits an unrelated fact.
    /// Derived incrementally from `condition_facts`.
    pub(super) condition_facts_by_sides: crate::persistent::PersistentMap<
        ConditionMatchKey,
        crate::persistent::PersistentMap<OldConditionTerm, bool>,
    >,
    /// Stage 5, rule L-Eq: each `Bool` equality fact `a == b` filed under
    /// both operands, with the fact's truth, so a decision of one operand
    /// reads its partners without visiting any other fact.
    pub(super) bool_equation_partners: crate::persistent::PersistentMap<
        OldConditionTerm,
        crate::persistent::PersistentMap<OldConditionTerm, bool>,
    >,
    /// The facts of `condition_facts_by_sides` with a side that is not an
    /// atom (a constant, or a variable that no load names): a load, a sum,
    /// a conditional. `condition_matches` can prove such a side equal to a
    /// query side by reasoning its key does not spell (a load's stored
    /// value, additive rearrangement), so a query that misses every key
    /// still asks these. A fact of two atoms is matched only through its
    /// key.
    /// Keyed by the family of kinds that can match one another
    /// ([`ConditionMatchKey::family`]).
    pub(super) open_condition_facts: crate::persistent::PersistentMap<
        u8,
        crate::persistent::PersistentMap<OldConditionTerm, bool>,
    >,
    /// The signed-order condition facts (`<`, `<=`, `>`, `>=`, either
    /// value) of `condition_facts`, in its order: what
    /// `condition_order_facts` collects, so collecting reads only order
    /// facts instead of every condition fact. Derived incrementally with
    /// the condition-match indexes.
    pub(super) order_condition_facts: super::fact_collections::FactMap<OldConditionTerm, bool>,
    /// Difference logic over `condition_facts`
    /// (`docs/internals/verification-efficiency.md`), the fast path condition evaluation
    /// asks before the general decision.
    pub(super) difference_graph: super::difference_graph::ContextDifferenceGraph,
    /// The contradictions among `condition_facts`, indexed as each fact is
    /// assumed (`assumptions/contradictions.rs`).
    pub(super) contradictions: super::assumptions::contradictions::ContextContradictions,
    /// What an exact fact says about the null-ness of a pointer, keyed by
    /// that pointer's offset term and carrying the block the fact named
    /// together with the fact itself. Derived incrementally from
    /// `condition_facts`: every equality against the null pointer files its
    /// other side here. A comparison of two pointers in one block is a
    /// `AddressOffsetEqual` that no longer names the block, so this index is
    /// what lets "one of these is null and the other is not" be two keyed
    /// lookups instead of a scan. The conclusion is about the offset terms
    /// alone: if `B + left` is null and `B + right` is not, then `left` and
    /// `right` are different offsets whatever block the query came from.
    pub(super) null_pointer_offsets: crate::persistent::PersistentMap<
        AddressOffset,
        crate::persistent::PersistentMap<(AddressBase, bool), OldConditionTerm>,
    >,
    /// Trusted persistent equality closure for pointers, offsets, and int32
    /// terms. Appended on insertion; restriction rebuilds from exact equality
    /// indexes.
    pub(super) equality_graph: super::equality_graph::EqualityGraph,
    /// Addresses of the first elements of two separated memory ranges of
    /// one block, keyed by the unordered pair and carrying the separation
    /// facts that state it. Mirrors `memory_separation_facts` under a key a
    /// pointer comparison can build. Each range holds the element at its own
    /// anchor, so two separated ranges cannot share one anchor -- again a
    /// statement about the offset terms alone, whatever block the comparison
    /// came from. Ownership alone does not trigger composition discovery.
    pub(super) separated_anchor_offsets: crate::persistent::PersistentMap<
        (AddressOffset, AddressOffset),
        crate::persistent::PersistentSet<Proposition>,
    >,
    /// The same stated nonempty separation evidence for anchors whose
    /// blocks differ. Such a separation distinguishes complete pointers,
    /// but says nothing about their offsets alone.
    pub(super) separated_anchor_pointers: crate::persistent::PersistentMap<
        (Address, Address),
        crate::persistent::PersistentSet<Proposition>,
    >,
    /// Scoped separation authority selected through checked address classes.
    pub(super) separated_address_classes: super::assumptions::SeparatedAddressIndex,
    /// Exact signed-order bounds keyed by either endpoint — under the term
    /// the fact wrote and, when different, its canonical form as an alias.
    /// Each entry carries the fact's own endpoint term first, so evidence
    /// found through the alias can still cite the exact fact. Counts
    /// preserve equivalent condition terms when one source fact is replaced.
    /// The written order facts by the lower end an order walk follows them
    /// from, each filed as its own condition so a walk can cite it exactly:
    /// [`super::assumptions::OrderFactsByLower`].
    pub(super) order_facts_by_lower: super::assumptions::OrderFactsByLower,
    /// True `AddressOffsetEqual` facts by each side's state shape
    /// (`offset_state_shape`), the candidates
    /// `has_pointer_offset_state_fact` checks.
    pub(super) address_offset_equalities_by_shape:
        crate::persistent::PersistentMap<u64, crate::persistent::PersistentSet<OldConditionTerm>>,
    pub(super) observation_comparisons:
        super::assumptions::observation_comparisons::ObservationComparisons,
    pub(super) checked_scalar_facts: super::assumptions::checked_scalar_facts::CheckedScalarFacts,
    pub(super) checked_order_bounds: super::assumptions::checked_order_bounds::CheckedOrderBounds,
    pub(super) signed_order_bounds: super::assumptions::retained_order_bounds::OrderBoundIndex,
    /// The `int64` counterpart of `signed_order_bounds`, maintained by the
    /// same insert and remove path over `int64` order facts. It
    /// is kept separate so an `int64` bound is never read as an int32 one.
    pub(super) int64_signed_order_bounds:
        super::assumptions::retained_order_bounds::OrderBoundIndex,
    /// Unsigned 32-bit order facts indexed by either endpoint, as
    /// `signed_order_bounds` files signed ones; kept separate so a `uint32`
    /// bound is never read as an `int32` one.
    pub(super) uint32_order_bounds: super::assumptions::retained_order_bounds::OrderBoundIndex,
    /// Unsigned 64-bit order facts indexed by either endpoint. This keeps
    /// slice-index range transport proportional to the queried order chain.
    pub(super) uint64_order_bounds: super::assumptions::retained_order_bounds::OrderBoundIndex,
    /// The 64-bit order facts again, split by direction for the chain walk:
    /// for each kind (`[unsigned, signed]`) and each direction (`[upward,
    /// downward]`), the canonical far ends of the facts leaving a canonical
    /// term in that direction, with whether the fact is strict. A walk reads
    /// only the edges it can follow, so a bound many indices share, `n` under
    /// `c0 < n`, `c1 < n`, ..., costs an upward walk through it nothing for
    /// the facts below it. Derived from the two indexes above by the same
    /// insert and remove path.
    pub(super) wide_order_edges:
        [[super::assumptions::retained_order_bounds::OrderEdgeIndex; 2]; 2],
    /// Condition facts containing a memory-load atom, indexed by the loaded
    /// pointer's state-blind structural fingerprint. This is derived from
    /// `condition_facts`; it narrows state-aware load-form checks
    /// without deciding them. It is maintained at each condition insert, so a
    /// fork copies only the path to the keys it changes.
    pub(super) memory_load_condition_facts: crate::persistent::PersistentMap<
        (AddressBase, u64),
        crate::persistent::PersistentSet<OldConditionTerm>,
    >,
    /// A persistent set: a context is cloned and extended by one fact at
    /// each lowering path and planning probe, so an extension must copy
    /// only a search path, not the whole set.
    pub(super) prop_facts: super::fact_collections::FactSet<Proposition>,
    /// Persistent exact Boolean propagation, maintained only at fact admission.
    pub(super) exact_propagation: super::assumptions::exact_propagation::Index,
    pub(super) comparison_views: PersistentMap<
        super::assumptions::observation_comparisons::PropositionKey,
        crate::persistent::PersistentSet<Proposition>,
    >,
    /// Alpha/load identity index for propositions that may be stated as a
    /// call requirement.  The key retains memory versions and canonicalizes
    /// only binders; the persistent buckets keep updates local to one key.
    /// A context built in bulk from a fact list defers the keys until the
    /// index is first asked for (see `StatedPropositionIndex`).
    pub(super) stated_proposition_index: super::assumptions::StatedPropositionIndex,
    /// Exact equalities between distinct checked constructors. Any such fact
    /// makes the context inconsistent by constructor disjointness.
    pub(super) algebraic_constructor_conflicts: crate::persistent::PersistentMap<Proposition, ()>,
    /// Whether an equality between an algebraic `if` and a constructor has
    /// decided a condition here, so a later fact's conditionals are read
    /// against the decided conditions. Facts of no such context pay nothing.
    pub(super) decided_algebraic_ifs: bool,
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
    /// Exact disjunctive proposition facts. This derived index keeps bounded
    /// case search proportional to possible case splits rather than every
    /// unrelated proposition in the context.
    pub(super) disjunction_facts: crate::kernel::fact_collections::ScanSet<Proposition>,
    pub(super) resource_compositions: super::fact_collections::ScanSet<ResourceContext>,
    /// The ownership a store in this context writes under, when the writer
    /// stated it: the current state's observable composition and any
    /// composition the store opened from held folded instances, all also
    /// among `resource_compositions` (empty when the state holds none). Store
    /// separation then reads these alone rather than every composition the
    /// path stated before (`roadmap/scaling.md`). `None` (the default) leaves
    /// store separation reading them all.
    pub(super) store_owners: Option<std::sync::Arc<Vec<ResourceContext>>>,
    /// Derived provenance-only footprints published with each explicitly
    /// admitted composition. This is not consumable resource authority.
    pub(super) composition_object_resources: memory_equality_index::ObjectEvidenceSources,
    /// Candidate lookup over `resource_compositions` by owned member, so
    /// separation by ownership reads the compositions that can answer rather
    /// than every one the path stated.
    pub(super) composition_members: composition_member_index::CompositionMemberIndex,
    /// Memory-view keys for validity checking, with the original point-bound
    /// propositions retained as sources for explicit proof construction.
    pub(super) memory_read_defined_facts: crate::persistent::PersistentMap<
        (Address, ProgramType),
        crate::persistent::PersistentMap<
            Proposition,
            crate::persistent::PersistentSet<Proposition>,
        >,
    >,
    pub(super) memory_loadable_facts: crate::persistent::PersistentMap<
        AddressBase,
        crate::persistent::PersistentSet<Proposition>,
    >,
    /// Loadability facts keyed by the C object identity carried by their
    /// base. Pointer provenance queries use this persistent index instead of
    /// scanning every external-argument fact, whose physical block is shared
    /// by all pointer parameters.
    pub(super) memory_loadable_object_facts:
        crate::persistent::PersistentMap<Address, crate::persistent::PersistentSet<Proposition>>,
    /// Loadability facts by base block, then by the base's state-blind
    /// fingerprint. Updated with `memory_loadable_facts`, so a fork copies
    /// only the path to the shape it changes.
    pub(super) memory_loadable_shape_facts: crate::persistent::PersistentMap<
        AddressBase,
        crate::persistent::PersistentMap<u64, crate::persistent::PersistentSet<Proposition>>,
    >,
    /// The memory effect facts (`MemoryEffectSummary`, `MemoryMutatesOnly`,
    /// `HeapAllocationFreed`), filed under both of their memories, so a load
    /// comparison between two states reads the effects naming one of
    /// them, not every proposition fact.
    pub(super) memory_effect_facts: crate::persistent::PersistentMap<
        SymbolicMemory,
        crate::persistent::PersistentSet<Proposition>,
    >,
    /// The `ResourceContains` facts, filed by their parent: a memory
    /// range under its base block, any other resource under itself. A
    /// containment walk reads the facts under the resource it has reached,
    /// not every proposition fact.
    pub(super) resource_contains_facts: crate::persistent::PersistentMap<
        super::assumptions::ResourceContainsKey,
        crate::persistent::PersistentSet<Proposition>,
    >,
    /// Explicit separation from a complete retained raw-memory partition.
    /// The canonical set in the value keeps the identity key alive.
    pub(super) explicit_memory_boundaries: crate::persistent::PersistentMap<
        (MemoryRange, usize),
        (
            canonical_fact_set::CanonicalFactSet,
            std::sync::Arc<Proposition>,
        ),
    >,
    pub(super) memory_separation_facts: crate::persistent::PersistentMap<
        (AddressBase, AddressBase),
        std::sync::Arc<Vec<(Proposition, MemoryRange, MemoryRange)>>,
    >,
    /// Separation facts the block-pair index cannot serve: at least one
    /// side is a non-memory resource whose containment may still entail a
    /// memory separation through its body. Kept small and scanned
    /// linearly; memory-memory facts live in the index above instead.
    pub(super) nonmemory_separation_facts: std::sync::Arc<Vec<Proposition>>,
    /// The separation facts filed under each non-memory side they name.
    pub(super) nonmemory_separations_by_side:
        crate::persistent::PersistentMap<Resource, crate::persistent::PersistentSet<Proposition>>,
    /// The containment facts filed under their child when it is not memory,
    /// so the containers of a non-memory resource are walked upward from it.
    pub(super) resource_containers:
        crate::persistent::PersistentMap<Resource, crate::persistent::PersistentSet<Proposition>>,
    /// The containment facts with a memory child, filed under the child's
    /// block, so the containers of a range are walked upward from it.
    pub(super) memory_containers: crate::persistent::PersistentMap<
        AddressBase,
        crate::persistent::PersistentSet<Proposition>,
    >,
    /// Every separation proposition fact, memory or not, in the
    /// proposition order of `prop_facts`. The provers that cannot key a
    /// separation query by block pair scan these instead of every
    /// proposition fact, and a `find` here chooses the same fact.
    pub(super) separation_facts: crate::kernel::fact_collections::ScanSet<Proposition>,
    /// Narrow memory separations, filed under each endpoint's block.
    pub(super) separation_facts_by_block: crate::persistent::PersistentMap<
        AddressBase,
        crate::persistent::PersistentSet<Proposition>,
    >,
    /// Separations with a wide side, also filed under their endpoint blocks.
    /// Wide containment can follow a base equality even for a narrow query,
    /// so shallow callers select these under the queried pointers' related
    /// blocks in addition to their ordinary narrow-containment keys.
    pub(super) wide_separation_facts_by_block: crate::persistent::PersistentMap<
        AddressBase,
        crate::persistent::PersistentSet<Proposition>,
    >,
    pub(super) content_fingerprint: u64,
    pub(super) reasoning_policy: ReasoningPolicy,
    /// At least the greatest execution-range variable any fact filed here
    /// mentions; see `ExecutionVariableCeiling`. Not part of the context's
    /// equality or hash.
    pub(super) execution_variable_ceiling: super::assumptions::ExecutionVariableCeiling,
}

impl PartialEq for PureFactContext {
    fn eq(&self, other: &Self) -> bool {
        self.content_fingerprint == other.content_fingerprint
            && self.condition_facts == other.condition_facts
            && self.equality_graph.admitted.typed_pointer_read_definitions
                == other.equality_graph.admitted.typed_pointer_read_definitions
            && self.prop_facts == other.prop_facts
            && self.resource_compositions == other.resource_compositions
            && self.store_owners == other.store_owners
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
    /// An expression domain is mandatory at a use site, but travels with
    /// a contract precondition assumed at function entry. Its caller must
    /// establish this same obligation before applying the contract.
    pub(super) evaluation_domain: bool,
    /// Producer metadata: emitted on the false arm of a C assertion.
    /// This tags the existing truthiness obligation, not a new proposition.
    pub(super) assertion_failure: bool,
    /// A `held` observation could not be made in this state.
    pub(super) invalid_mutex_held_observation: bool,
    /// Refuting this nonzero-divisor obligation is division by zero.
    pub(super) unsigned_divisor: bool,
    /// An ordered range bound for an executed float-to-integer conversion.
    pub(super) float_to_integer_bound: bool,
    /// A representability bound for an executed signed operation.
    pub(super) signed_arithmetic_bound: bool,
    /// This condition must be established before applying the statement.
    pub(super) statement_entry_required: bool,
    /// Diagnostic metadata only. The proposition itself carries both ranges.
    pub(super) live_view_write: bool,
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

/// This metadata describes the proposition; it never distinguishes two
/// obligations. Comparison, ordering, and hashing therefore read the
/// checked fields only, so an obligation carrying a recorded chain still
/// deduplicates against the same obligation built without one.
impl PartialEq for ProofObligation {
    fn eq(&self, other: &Self) -> bool {
        self.proposition == other.proposition
            && self.context == other.context
            && self.assumable == other.assumable
            && self.evaluation_domain == other.evaluation_domain
            && self.statement_entry_required == other.statement_entry_required
    }
}

impl Eq for ProofObligation {}

impl Hash for ProofObligation {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.proposition.hash(state);
        self.context.hash(state);
        self.assumable.hash(state);
        self.evaluation_domain.hash(state);
        self.statement_entry_required.hash(state);
    }
}

impl Ord for ProofObligation {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.proposition
            .cmp(&other.proposition)
            .then_with(|| self.context.cmp(&other.context))
            .then_with(|| self.assumable.cmp(&other.assumable))
            .then_with(|| self.evaluation_domain.cmp(&other.evaluation_domain))
            .then_with(|| {
                self.statement_entry_required
                    .cmp(&other.statement_entry_required)
            })
    }
}

impl PartialOrd for ProofObligation {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ExecutionPureFact {
    pub(super) proposition: Arc<Proposition>,
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
    /// state, since the producer's state and pointer are the authority.
    pub(super) generated_load_binding: Option<Box<GeneratedLoadBinding>>,
    /// Checked callback-read evidence, independent of scalar-variable naming.
    pub(super) checked_pointer_read: Option<Box<(Address, SharedMemory, Address)>>,
    pub(super) generated_load_source_events: GeneratedLoadSourceEvents,
    pub(super) reference_observation: super::source_access::ReferenceObservationSource,
}

/// Source events are execution derivation, not part of the proposition's
/// semantic identity. Keep them beside the fact while making fact equality
/// and hashing remain proposition-oriented. Allocate the event list only for
/// facts carrying source events; ordinary pure facts keep one optional pointer.
#[derive(Clone, Debug, Default)]
#[allow(clippy::box_collection)] // Pure facts retain only one optional source-event pointer.
pub(crate) struct GeneratedLoadSourceEvents(Option<Box<Vec<GeneratedLoadSourceEvent>>>);

impl GeneratedLoadSourceEvents {
    pub(crate) fn as_slice(&self) -> &[GeneratedLoadSourceEvent] {
        self.0.as_deref().map_or(&[], Vec::as_slice)
    }

    pub(crate) fn push(&mut self, event: GeneratedLoadSourceEvent) {
        self.0.get_or_insert_with(Default::default).push(event);
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
/// Consumers must use the complete `(variable, retained_state, pointer)` key; the
/// source expression is retained only as the exact equation operand produced
/// by the kernel.  A variable-level tombstone is represented by
/// [`GeneratedLoadBinding::Ambiguous`] when one path observes incompatible
/// bindings for the same variable.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) enum GeneratedLoadBinding {
    Exact {
        variable: Variable,
        retained_state: MemoryStateIdentity,
        pointer: Address,
        load: OldMachineTerm,
        /// The C value produced by a completed, nonvolatile pointer read.
        /// Scalar and volatile reads have no pointer bridge.
        typed_pointer_value: Option<Address>,
        /// The current cell read by a checked resource-index expression.
        /// Its cached value can retain an older defining load.
        observed_pointer_read: Option<(SharedMemory, Address)>,
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
    pub(crate) reference_access: Option<Arc<super::ReferenceAccessSourceId>>,
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
    pub(super) before: SymbolicMemory,
    pub(super) after: SymbolicMemory,
    /// `after`, named by its memory and placed at the store's point.
    pub(super) after_point: ProgramPoint,
    pub(super) pointer: Address,
    pub(super) value: ProgramValue,
    pub(super) authorized_range: Option<MemoryRange>,
    pub(super) source: super::StatementStoreSource,
    pub(super) value_equation: Option<Arc<Proposition>>,
    /// Evaluated lvalue coordinates, before ownership may rebase the write.
    pub(super) source_address: Option<Address>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicExecution {
    pub(super) paths: Vec<SymbolicExecutionPath>,
    pub(super) limit: Option<ExecutionLimit>,
}

/// A kernel-created record of one exact whole-function execution judgment.
/// Opened-contract executions retain their producer's entry authority;
/// whole-contract admission consumes it without rechecking premises or entry
/// representations. Independent conditional executions have no such authority
/// and retain their separate validation route.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CheckedFunctionExecution {
    pub(super) retained_descent: bool,
    pub(super) published_outcomes:
        super::proof::PersistentVector<Arc<super::PublishedFunctionOutcome>>,
    /// Obligations retired directly by ordinary proof operations for this strategy.
    pub(super) contract_completion: Option<Arc<super::ContractProofProgress>>,
    /// Issued by the opened entry's execution producer, never by an
    /// independent conditional execution or a caller-supplied premise list.
    pub(super) entry_authority: Option<super::proof::ContractEntryAuthority>,
    pub(super) closed_exit_obligations: Vec<Option<super::ClosedContractExit>>,
    /// The immutable outcome publication this proof completed. Return-path
    /// completion uses this same input and preserves its checked path object.
    pub(super) proof_candidates: Option<FunctionExecutionCandidates>,
    pub(super) state: ExecutionState,
    pub(super) function: ProgramFunction,
    pub(super) arguments: Vec<ProgramExpression>,
    pub(super) assumptions: PureFactContext,
    pub(super) environment: ExecutionEnvironment,
    pub(super) execution_semantics: ExecutionSemantics,
    pub(super) mode: FunctionContractExecutionMode,
    pub(super) execution: SymbolicExecution,
    /// Exact resource claims checked for each execution path.  This is proof
    /// evidence, not a request to re-evaluate a resource transition during
    /// later contract certification.
    pub(super) checked_resource_claims: Vec<Vec<FunctionContractClaimKey>>,
    pub(super) checked_resource_transitions: Vec<bool>,
    /// Paths whose contract exit resource transition was deferred because a
    /// conditional produced effect was not decided by the proof entry facts.
    /// Contract certification must resolve these paths under an exhaustive
    /// guard case before using their post-state.
    pub(super) deferred_contract_exits: Vec<bool>,
    /// Exact boundary error retained for each deferred path. A deferred marker
    /// is valid only when this records the conditional-effect selection error
    /// that caused the deferral.
    pub(super) deferred_contract_exit_errors: Vec<Option<RuntimeError>>,
    /// Original contract caller state when a kernel-checked proof entered C
    /// execution through a definitionally equal resource representation.
    pub(super) entry_representation_origin: Option<ExecutionState>,
    /// The user-defined tactics this execution's proof applied.
    pub(super) applied_tactics: std::collections::BTreeSet<String>,
    /// Complete conservative call dependencies from kernel-checked execution.
    /// None retains source-call analysis; a present empty set proves no calls.
    /// Shared across claims and certificate reuse, never copied per step.
    pub(super) checked_callees: Option<Arc<BTreeSet<crate::kernel::termination::CallDependency>>>,
    /// Original checked input selection; later certification must not rebuild it.
    pub(super) boundary_transfer: Option<Arc<super::functions::CheckedBoundaryResourceTransfer>>,
    pub(super) checked_call_events: super::proof::CheckedCallEvents,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FunctionContractExecutionMode {
    VerifyLoops,
    ExecuteLoops,
}

impl CheckedFunctionExecution {
    pub fn paths(&self) -> &[SymbolicExecutionPath] {
        self.execution.paths()
    }

    pub(crate) fn function(&self) -> &ProgramFunction {
        self.boundary_transfer
            .as_deref()
            .map_or(&self.function, |transfer| transfer.checked_function())
    }

    pub(crate) fn function_arguments(&self) -> &[ProgramExpression] {
        &self.arguments
    }

    /// Allocation return accounting reads borrowed inputs in the immutable
    /// checked entry state, before C may mutate a pointer naming them.
    pub(crate) fn allocation_entry_state(&self) -> &ExecutionState {
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
            if left.borrow_evidence != right.borrow_evidence {
                return Err(format!("path {index}: the borrow evidence differs"));
            }
            same_proposition(left.theorem.proposition(), right.theorem.proposition())
                .map_err(|difference| format!("path {index}: {difference}"))?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct SymbolicExecutionPath {
    /// The body outcome checked against a retained Proof trace before the
    /// same producer applies the contract exit rule. Ordinary symbolic paths
    /// have no separate proof-completion origin.
    pub(super) descent_step: Option<crate::kernel::DescentStep>,
    pub(super) completion_origin: Option<FunctionOutcome>,
    pub(super) call_result: Option<StoredExecutionValue>,
    pub(super) assumptions: PureFactContext,
    /// The checked body context, retained by the Proof completion producer.
    /// It is available only after certification has checked the entry under
    /// `assumptions`. Legacy execution producers use the flat-fact fallback.
    pub(super) post_assumptions: Option<PureFactContext>,
    pub(super) facts: ExecutionFacts,
    pub(super) effect_facts: ExecutionFacts,
    pub(super) obligations: Vec<ProofObligation>,
    pub(super) theorem: Theorem,
    pub(super) borrow_evidence: super::borrows::CheckedBorrowCallEvidenceSequence,
}

// Retaining a context changes neither a path's evidence nor its identity.
// Avoid comparing its complete persistent indexes just to compare paths.
impl PartialEq for SymbolicExecutionPath {
    fn eq(&self, other: &Self) -> bool {
        self.completion_origin == other.completion_origin
            && self.call_result == other.call_result
            && self.assumptions == other.assumptions
            && self.facts == other.facts
            && self.effect_facts == other.effect_facts
            && self.obligations == other.obligations
            && self.theorem == other.theorem
            && self.borrow_evidence == other.borrow_evidence
    }
}

impl Eq for SymbolicExecutionPath {}

/// An untrusted collection of checked function outcomes.
///
/// Candidates deliberately carry no [`Theorem`]. They become useful as proof
/// evidence only after a checked kernel execution independently reproduces the
/// same complete path frontier.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionExecutionCandidates {
    pub(super) data: std::sync::Arc<FunctionExecutionCandidatesData>,
}

/// Immutable publication of one complete outcome frontier. Proof forks retain
/// this collection, rather than copying every sibling path and the source body.
#[derive(Debug)]
pub(super) struct FunctionExecutionCandidatesData {
    pub(super) state: ExecutionState,
    pub(super) function: Arc<ProgramFunction>,
    pub(super) arguments: Arc<Vec<ProgramExpression>>,
    pub(super) paths: super::proof::PersistentVector<FunctionExecutionCandidate>,
    pub(super) common_facts: Option<ExecutionFacts>,
}
impl PartialEq for FunctionExecutionCandidatesData {
    fn eq(&self, other: &Self) -> bool {
        self.state == other.state
            && self.function == other.function
            && self.arguments == other.arguments
            && self.paths == other.paths
    }
}
impl Eq for FunctionExecutionCandidatesData {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionExecutionCandidate {
    pub(super) data: Arc<FunctionExecutionCandidateData>,
}

/// An immutable candidate record retained across distinct terminal frontiers.
/// Adding facts shares the original outcome and obligations as well as the
/// unchanged fact streams. This is untrusted publication, never a theorem.
#[derive(Clone, Debug)]
pub(super) struct FunctionExecutionCandidateData {
    /// Selected producer delta for a retained completion context. It changes
    /// neither the candidate's facts nor its untrusted publication semantics.
    pub(super) completion_delta: Option<ExecutionFacts>,
    pub(super) outcome: Arc<FunctionOutcome>,
    pub(super) facts: ExecutionFacts,
    pub(super) effect_facts: ExecutionFacts,
    /// Whether re-publication's public-then-private effect order is already
    /// retained. Derived only from the stored facts; carries no authority.
    pub(super) effects_public_first: bool,
    pub(super) obligations: Arc<Vec<ProofObligation>>,
    pub(super) borrow_evidence: super::borrows::CheckedBorrowCallEvidenceSequence,
}

impl PartialEq for FunctionExecutionCandidateData {
    fn eq(&self, other: &Self) -> bool {
        self.outcome == other.outcome
            && self.facts == other.facts
            && self.effect_facts == other.effect_facts
            && self.effects_public_first == other.effects_public_first
            && self.obligations == other.obligations
            && self.borrow_evidence == other.borrow_evidence
    }
}
impl Eq for FunctionExecutionCandidateData {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicConditionEvaluation {
    pub(super) paths: Vec<SymbolicConditionEvaluationPath>,
    pub(super) limit: Option<ExecutionLimit>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicConditionEvaluationPath {
    pub(super) outcome: ConditionOutcome,
    pub(super) facts: ExecutionFacts,
    pub(super) obligations: Vec<ProofObligation>,
    pub(super) theorem: Theorem,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ExpressionPath<V = ProgramValue> {
    pub(super) outcome: ExpressionOutcome<V>,
    pub(super) facts: ExecutionFacts,
    pub(super) obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct LValuePath {
    pub(super) outcome: LValueOutcome,
    pub(super) facts: ExecutionFacts,
    pub(super) obligations: Vec<ProofObligation>,
}

/// Source correspondence describes a checked path without distinguishing
/// semantically identical paths. The empty form allocates nothing, and cloning
/// a loop path shares its output-sized mapping.
#[derive(Clone, Debug, Default)]
pub(super) struct LoopInvariantCorrespondence {
    pub(super) invariants: Option<std::sync::Arc<[(usize, Proposition)]>>,
    /// The loop head's pass count, `iterations`, which the path's facts
    /// state over: spelled `loop(i).iterations` past the loop.
    pub(super) iterations: Option<IntegerTerm>,
}

impl PartialEq for LoopInvariantCorrespondence {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl Eq for LoopInvariantCorrespondence {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct StatementExecutionPath {
    /// Declaration-indexed source correspondence for this loop's checked exit.
    /// This is presentation metadata, never an additional assumption.
    pub(super) loop_invariant_correspondence: LoopInvariantCorrespondence,
    /// Exact non-void result retained by the call producer, even when discarded.
    pub(super) call_result: Option<StoredExecutionValue>,
    pub(super) outcome: StatementOutcome,
    pub(super) facts: ExecutionFacts,
    pub(super) obligations: Vec<ProofObligation>,
    pub(super) borrow_evidence: super::borrows::CheckedBorrowCallEvidenceSequence,
}

impl StatementExecutionPath {
    pub(super) fn with_call_result(
        mut self,
        result: Option<impl Into<StoredExecutionValue>>,
    ) -> Self {
        if matches!(self.outcome, StatementOutcome::Normal(_)) {
            self.call_result = result
                .map(Into::into)
                .filter(|value| value.program_type() != ProgramType::Void);
        }
        self
    }

    /// A path with no loop-invariant correspondence and no borrow evidence,
    /// which is every path not leaving a checked loop or a borrowing call.
    pub(super) fn new(
        outcome: StatementOutcome,
        facts: ExecutionFacts,
        obligations: Vec<ProofObligation>,
    ) -> Self {
        Self {
            loop_invariant_correspondence: Default::default(),
            call_result: None,
            outcome,
            facts,
            obligations,
            borrow_evidence: super::borrows::empty_checked_borrow_evidence_sequence(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct FunctionPath {
    pub(super) outcome: FunctionOutcome,
    pub(super) facts: ExecutionFacts,
    pub(super) obligations: Vec<ProofObligation>,
    pub(super) borrow_evidence: super::borrows::CheckedBorrowCallEvidenceSequence,
}

impl FunctionPath {
    /// A path with no borrow evidence: every path not ending in a borrowing
    /// call.
    pub(super) fn new(
        outcome: FunctionOutcome,
        facts: ExecutionFacts,
        obligations: Vec<ProofObligation>,
    ) -> Self {
        Self {
            outcome,
            facts,
            obligations,
            borrow_evidence: super::borrows::empty_checked_borrow_evidence_sequence(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ArgumentsPath<V = ProgramValue> {
    pub(super) values: Vec<V>,
    pub(super) outcome: Option<FunctionOutcome>,
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

pub(super) struct KernelVariableGenerator<'scope> {
    counter: KernelVariableCounter,
    reserved: BTreeSet<Variable>,
    shared_reserved: Option<ReservedVariableSets>,
    deferred_reserved: Option<Box<dyn FnOnce() -> BTreeSet<Variable> + 'scope>>,
    /// An execution stream allocates only above this: every identity up to
    /// it is reserved without being listed (a fact context's
    /// `execution_variable_ceiling`).
    reserved_through: Option<Variable>,
}

impl<'scope> KernelVariableGenerator<'scope> {
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
            deferred_reserved: None,
            reserved_through: None,
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
            deferred_reserved: None,
            reserved_through: None,
        }
    }

    pub(super) fn fresh_for_execution_with_shared_reservations(
        existing: BTreeSet<Variable>,
        shared_reserved: impl Into<ReservedVariableSets>,
    ) -> Self {
        Self {
            counter: KernelVariableCounter::Execution,
            reserved: existing,
            shared_reserved: Some(shared_reserved.into()),
            deferred_reserved: None,
            reserved_through: None,
        }
    }

    /// Borrow the statement inputs without walking them until execution
    /// actually needs a fresh identity. A plain store requests none.
    pub(super) fn fresh_for_execution_with_deferred_reservations(
        collect: impl FnOnce() -> BTreeSet<Variable> + 'scope,
        shared_reserved: impl Into<ReservedVariableSets>,
    ) -> Self {
        let mut generator =
            Self::fresh_for_execution_with_shared_reservations(BTreeSet::new(), shared_reserved);
        generator.deferred_reserved = Some(Box::new(collect));
        generator
    }

    /// Reserves every identity up to `ceiling` for the execution stream.
    pub(super) fn reserving_through(mut self, ceiling: Option<Variable>) -> Self {
        self.reserved_through = self.reserved_through.max(ceiling);
        self
    }

    fn prepare_reservations(&mut self) {
        if let Some(collect) = self.deferred_reserved.take() {
            self.reserved.extend(collect());
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
        self.prepare_reservations();
        if let Some(ceiling) = self.reserved_through {
            budget.skip_kernel_variables_through(ceiling);
        }
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
    fn pure_facts_do_not_pay_for_program_payloads() {
        assert!(std::mem::size_of::<Term>() <= 144);
        // Keep this budget independent of Term's current layout. Shrinking
        // an operand does not increase the space used by other fact variants.
        assert!(std::mem::size_of::<Proposition>() <= 2 * 144);
        assert!(std::mem::size_of::<ExecutionPureFact>() <= 352);
        assert!(std::mem::size_of::<StatementOutcome>() <= 144);
        assert!(std::mem::size_of::<FunctionOutcome>() <= 144);
    }
}

/// The algebraic type of a value a C local holds, interned so that `ProgramType`
/// stays `Copy`: an abstract type parameter, a rigid type known only by its
/// name, or a Rust enum, a `spec enum` whose values the program constructs and
/// matches. Types are few and live for the process, so each is leaked once.
/// Two enums of one name with different variants are different types.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct TypeParameterName(u32);

struct TypeParameterNames {
    types: Vec<&'static AlgebraicType>,
    // Rigid values use only their name, never the unrelated enum definitions.
    rigid: std::collections::BTreeMap<String, TypeParameterName>,
    // Rigid names of library instances, `Vec<uint32>`: opaque values of a
    // fixed width, not of a size Click does not know.
    library_instances: std::collections::BTreeSet<String>,
    // Every other type, by name: the few interned types of one name are the
    // only candidates a lookup compares, so finding a type does not scan
    // every type the process has interned.
    structural: std::collections::BTreeMap<String, Vec<TypeParameterName>>,
}

impl TypeParameterNames {
    /// The interned type equal to `algebraic_type`, which is not rigid.
    fn structural(&self, algebraic_type: &AlgebraicType) -> Option<TypeParameterName> {
        self.structural
            .get(&algebraic_type.name)?
            .iter()
            .copied()
            .find(|known| {
                crate::instrumentation::record_deterministic_work(1);
                *self.types[known.0 as usize] == *algebraic_type
            })
    }
}

static TYPE_PARAMETER_NAMES: std::sync::Mutex<TypeParameterNames> =
    std::sync::Mutex::new(TypeParameterNames {
        types: Vec::new(),
        rigid: std::collections::BTreeMap::new(),
        library_instances: std::collections::BTreeSet::new(),
        structural: std::collections::BTreeMap::new(),
    });

impl TypeParameterName {
    /// The abstract type parameter of this name.
    pub fn intern(name: &str) -> Self {
        Self::of(&AlgebraicType::parameter(name.to_string()))
    }

    /// The type a value of `algebraic_type` has.
    pub fn of(algebraic_type: &AlgebraicType) -> Self {
        let mut names = TYPE_PARAMETER_NAMES.lock().expect("type parameter names");
        let rigid = algebraic_type.rigid
            && algebraic_type.arguments.is_empty()
            && algebraic_type.variants.is_empty();
        if rigid {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(known) = names.rigid.get(&algebraic_type.name) {
                return *known;
            }
        } else if let Some(known) = names.structural(algebraic_type) {
            return known;
        }
        let id = Self(names.types.len() as u32);
        names
            .types
            .push(Box::leak(Box::new(algebraic_type.clone())));
        if rigid {
            names.rigid.insert(algebraic_type.name.clone(), id);
        } else {
            names
                .structural
                .entry(algebraic_type.name.clone())
                .or_default()
                .push(id);
        }
        id
    }

    /// Whether Click knows nothing of this type but its name, as of a type
    /// parameter: its values are opaque and its size is `sizeof(T)`. An
    /// enum, with its variants, or an instance such as `Vec<u32>` is not.
    pub fn has_abstract_size(self) -> bool {
        let names = TYPE_PARAMETER_NAMES.lock().expect("type parameter names");
        let algebraic_type = names.types[self.0 as usize];
        algebraic_type.rigid
            && algebraic_type.arguments.is_empty()
            && algebraic_type.variants.is_empty()
            && !names.library_instances.contains(&algebraic_type.name)
    }

    /// Records that the rigid type `name` is an instance of a library type,
    /// such as `Vec<uint32>`, whose values are opaque but of a fixed width.
    pub fn declare_library_instance(name: &str) {
        let mut names = TYPE_PARAMETER_NAMES.lock().expect("type parameter names");
        if !names.library_instances.contains(name) {
            names.library_instances.insert(name.to_string());
        }
    }

    /// The bytes a value of this type takes in memory, `sizeof(T)`: a
    /// number the type fixes and Click does not know. Two uses of one type
    /// name the same term; a proof learns of it only the facts the program's
    /// language states for every type, and an instance reads it as its own
    /// type's size.
    /// The type whose `sizeof(T)` `term` is, for a type of abstract size.
    pub fn of_size_term(term: &OldMachineTerm) -> Option<Self> {
        let OldMachineTerm::PureFunctionApplication { name, arguments } = term else {
            return None;
        };
        let type_name = name.strip_prefix("sizeof<")?.strip_suffix('>')?;
        if !arguments.is_empty() {
            return None;
        }
        let parameter = Self::intern(type_name);
        (parameter.has_abstract_size() && parameter.size_term() == *term).then_some(parameter)
    }

    pub fn size_term(self) -> OldMachineTerm {
        OldMachineTerm::PureFunctionApplication {
            name: format!("sizeof<{}>", self.name()),
            arguments: Vec::new(),
        }
    }

    pub fn name(self) -> &'static str {
        &TYPE_PARAMETER_NAMES
            .lock()
            .expect("type parameter names")
            .types[self.0 as usize]
            .name
    }

    /// The algebraic type a value of this type is: rigid for a type
    /// parameter, with its variants for an enum.
    pub fn algebraic_type(self) -> AlgebraicType {
        TYPE_PARAMETER_NAMES
            .lock()
            .expect("type parameter names")
            .types[self.0 as usize]
            .clone()
    }

    /// Whether `algebraic_type` is the type of a C carrier already named,
    /// so a memory cell can hold its values. Nothing is registered.
    pub(crate) fn carries(algebraic_type: &AlgebraicType) -> bool {
        let names = TYPE_PARAMETER_NAMES.lock().expect("type parameter names");
        if algebraic_type.rigid
            && algebraic_type.arguments.is_empty()
            && algebraic_type.variants.is_empty()
        {
            crate::instrumentation::record_deterministic_work(1);
            names.rigid.contains_key(&algebraic_type.name)
        } else {
            names.structural(algebraic_type).is_some()
        }
    }

    /// Whether values of this type are an enum's, which the program
    /// constructs and matches, rather than an abstract type parameter's.
    pub fn is_enum(self) -> bool {
        !TYPE_PARAMETER_NAMES
            .lock()
            .expect("type parameter names")
            .types[self.0 as usize]
            .rigid
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../scaling_tests/kernel/primitives.rs");
}

pub(crate) use bindings::NamedBindingMap;
