use super::borrows::{
    BorrowBinding, BorrowBindings, BorrowLedger, BorrowRefusal, BorrowRefusalOperation,
    BorrowRefusalSubject, BorrowedContractInputBacking,
};
pub(crate) use super::functions::admit_declared_entry_resources;
use super::functions::{
    apply_verified_contract_resource_transition,
    checked_expand_composite_resource_fact_with_children,
    construct_program_function_resource as construct_c_function_resource_checked,
    evaluate_function_resource_context_with_metadata,
    function_return_resources_definitionally_established,
};
pub(super) use super::memory_history::*;
use super::prelude::*;
pub(super) use super::resource_tracker::cell_source::*;
use crate::kernel::ResourceDescription;
use crate::kernel::binary_node;
use crate::kernel::binary_term;
use crate::kernel::proof::PropositionSource;
use crate::kernel::{CompareRelation, OverflowOperation};
use crate::kernel::{MachineCastSpelling, cast_term};
use crate::kernel::{OffsetTree, OffsetView};
use crate::kernel::{
    bits32_constant, constant_u32, int64_constant, native_constant, uint64_constant,
};
use std::sync::Arc;

#[cfg(test)]
thread_local! {
    static CHECKED_FUNCTION_BODY_EXECUTIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

thread_local! {
    /// The borrowed-input roots and abstract mutex reservations installed for each function in this
    /// verification session, keyed by function name and holding the exact
    /// entry state they were installed on. Every proof unit of one function
    /// (each claim proof, loop proof, and certification) must share one
    /// entry authority: a borrow ledger's identity is opaque and fresh, so two
    /// installs would be two different authorities and no completion from
    /// one could certify a claim at the other. The pre-install state is
    /// compared exactly, once per proof unit; a function whose entry state
    /// changed simply gets a new root.
    static BORROWED_INPUT_ROOTS: std::cell::RefCell<BTreeMap<String, (ExecutionState, ExecutionState)>> =
        const { std::cell::RefCell::new(BTreeMap::new()) };
}

/// The element question a memory access in a named object asks, for a
/// refusal to state: the access lands in element `index` of an object of
/// `count` elements, each `stride` bytes wide.
///
/// This reads the address the way the element rules do (the widest scaled
/// summand of the offset, at least as wide as the access, is the element
/// index; the object's size divided by its stride is the count). It decides
/// nothing; a refusal uses it to say which bound it could not show.
#[derive(Clone, Debug)]
pub(crate) struct MemoryAccessElementBound {
    pub(crate) index: OldMachineTerm,
    pub(crate) count: OldMachineTerm,
    pub(crate) stride: u32,
}

pub(crate) fn memory_access_element_bound(
    memory: &SymbolicMemory,
    pointer: &Address,
    byte_width: u32,
) -> Option<MemoryAccessElementBound> {
    let size = memory.block_size(&pointer.base)?;
    let mut pending = vec![&pointer.offset];
    let mut widest: Option<(SharedMachineIntegerTerm, u32)> = None;
    while let Some(term) = pending.pop() {
        match term.view() {
            OffsetView::Add(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            OffsetView::Int32Scaled { index, byte_width }
            | OffsetView::Int64Scaled {
                index, byte_width, ..
            } => {
                let stride = u32::try_from(byte_width).ok()?;
                if widest.as_ref().is_none_or(|(_, widest)| stride > *widest) {
                    widest = Some((index, stride));
                }
            }
            OffsetView::Constant(_) => {}
            OffsetView::Variable(_) => return None,
        }
    }
    let (index, stride) = widest?;
    if stride < byte_width {
        return None;
    }
    // A widened index is spelled as the C index it widens: a `uint32` index
    // zero-extends to the 64-bit offset.
    let index = match index.structural_value() {
        cast_term!(UInt64From32, index) => OldMachineTerm::clone(index),
        value => value.clone(),
    };
    Some(MemoryAccessElementBound {
        index,
        count: crate::kernel::reasoning::element_count_from_bytes(size, stride)?,
        stride,
    })
}

pub(crate) fn clear_borrowed_input_root_memo() {
    BORROWED_INPUT_ROOTS.with(|roots| roots.borrow_mut().clear());
}

#[cfg(test)]
fn record_checked_function_body_execution() {
    CHECKED_FUNCTION_BODY_EXECUTIONS.with(|count| count.set(count.get() + 1));
}

#[cfg(not(test))]
#[cfg(test)]
fn record_checked_function_body_execution() {}

#[cfg(test)]
pub(crate) fn take_checked_function_body_execution_count() -> usize {
    CHECKED_FUNCTION_BODY_EXECUTIONS.with(|count| count.replace(0))
}

pub(in crate::kernel) mod contract_certification;
pub use contract_certification::*;
mod algebraic_cases;
pub(in crate::kernel) use algebraic_cases::algebraic_constructor_case_equations;
pub use algebraic_cases::algebraic_constructor_cases;
use contract_certification::contract_resource_condition_cases;
#[cfg(test)]
use contract_certification::prove_symbolic_program_function_verification_paths;

pub fn int32(bits: impl Into<OldMachineTerm>) -> ProgramValue {
    ProgramValue::Int32(bits.into())
}

/// The C `bool` value of a `bool` cell whose byte is the `uint8` term
/// `byte`: the byte rule (Stage 5), the `Bool` `byte != 0` at `uint8`,
/// carried as its cast (rule C1).
pub fn bool_value(byte: impl Into<OldMachineTerm>) -> ProgramValue {
    ProgramValue::of_bool(OldConditionTerm::truth_of_bool_word(
        &byte.into().in_narrow_format(MachineIntegerType::UInt8),
    ))
}

/// Rule C1b: the range of a `Bool`'s integer cast, `0 <= c`, `c <= 1` and
/// `c == 0 or c == 1`, filed where a C value is introduced (an entry value, a
/// read), beside a narrow integer's range.
///
/// The cast of a `Bool` is 1 when it holds and 0 otherwise, so each fact is
/// true by C1 alone. The disjunction is stated beside the bounds because
/// neither disjunct is provable alone, and the closers do not derive it from
/// the bounds. A `Bool` value states the range of its cast to `int32`, the
/// format C's promotion and an `int` result read it at; an integer value
/// that is a cast states its own. `None` for a constant, which has nothing
/// left to state, and for every other value.
pub(crate) fn program_bool_cast_range_facts(value: &ProgramValue) -> Option<Vec<Proposition>> {
    let cast = match value.numeric_value() {
        ProgramValue::Bool(word) => {
            OldMachineTerm::bool_cast(MachineIntegerType::Int32, word.bool_cast_operand()?.clone())
        }
        crate::kernel::integer64_c_value!(term) if term.bool_cast_operand().is_some() => {
            term.clone()
        }
        _ => return None,
    };
    let OldMachineTerm::BoolCast { to, .. } = &cast else {
        return None;
    };
    // An 8- or 16-bit cast states its range in its own format.
    if to.format().bits() < 32 {
        let constant = |value| {
            to.constant_term(crate::kernel::MachineIntegerConstant::from_unsigned(
                to.format(),
                value,
            )?)
        };
        let (zero, one) = (constant(0)?, constant(1)?);
        let compare = |relation, constant: &OldMachineTerm| {
            Proposition::condition_is(
                OldConditionTerm::machine_compare(*to, relation, cast.clone(), constant.clone()),
                true,
            )
        };
        use crate::kernel::CompareRelation as R;
        return Some(vec![
            compare(R::GreaterEqual, &zero),
            compare(R::LessEqual, &one),
            Proposition::Or(
                Box::new(compare(R::Equal, &zero)),
                Box::new(compare(R::Equal, &one)),
            ),
        ]);
    }
    let wide = to.format().bits() == 64;
    let (zero, one) = if wide {
        if to.format().is_signed() {
            (
                OldMachineTerm::int64_constant(0),
                OldMachineTerm::int64_constant(1),
            )
        } else {
            (
                OldMachineTerm::uint64_constant(0),
                OldMachineTerm::uint64_constant(1),
            )
        }
    } else {
        (OldMachineTerm::constant(0), OldMachineTerm::constant(1))
    };
    let equals = |constant: &OldMachineTerm| {
        Proposition::condition_is(
            if wide {
                if to.format().is_signed() {
                    OldConditionTerm::int64_equal(cast.clone(), constant.clone())
                } else {
                    OldConditionTerm::uint64_equal(cast.clone(), constant.clone())
                }
            } else {
                OldConditionTerm::equal(cast.clone(), constant.clone())
            },
            true,
        )
    };
    let disjunction = Proposition::Or(Box::new(equals(&zero)), Box::new(equals(&one)));
    if wide {
        return Some(vec![disjunction]);
    }
    Some(vec![
        Proposition::condition_is(
            OldConditionTerm::signed_greater_equal(cast.clone(), zero),
            true,
        ),
        Proposition::condition_is(OldConditionTerm::signed_less_equal(cast.clone(), one), true),
        disjunction,
    ])
}

/// The range `[lower, upper]` every value of a narrow C integer type lies
/// in, with the term holding it: a `uint8` is in `[0, 255]`, an `int16` in
/// `[-32768, 32767]`. `None` for every other type, whose range is its word.
pub(crate) fn program_narrow_integer_range(
    value: &ProgramValue,
) -> Option<(&OldMachineTerm, i32, i32)> {
    match value {
        ProgramValue::Int8(term) => Some((term, i32::from(i8::MIN), i32::from(i8::MAX))),
        ProgramValue::Int16(term) => Some((term, i32::from(i16::MIN), i32::from(i16::MAX))),
        ProgramValue::UInt8(term) => Some((term, 0, i32::from(u8::MAX))),
        ProgramValue::UInt16(term) => Some((term, 0, i32::from(u16::MAX))),
        _ => None,
    }
}

/// An `int8` value. A 32-bit constant given for it is read as its value's
/// word (`OldMachineTerm::in_narrow_format`).
pub fn int8(bits: impl Into<OldMachineTerm>) -> ProgramValue {
    ProgramValue::Int8(bits.into().in_narrow_format(MachineIntegerType::Int8))
}

/// An `int16` value; see [`int8`].
pub fn int16(bits: impl Into<OldMachineTerm>) -> ProgramValue {
    ProgramValue::Int16(bits.into().in_narrow_format(MachineIntegerType::Int16))
}

/// A `uint8` value; see [`int8`].
pub fn uint8(bits: impl Into<OldMachineTerm>) -> ProgramValue {
    ProgramValue::UInt8(bits.into().in_narrow_format(MachineIntegerType::UInt8))
}

/// A `uint16` value; see [`int8`].
pub fn uint16(bits: impl Into<OldMachineTerm>) -> ProgramValue {
    ProgramValue::UInt16(bits.into().in_narrow_format(MachineIntegerType::UInt16))
}

/// A `uint32` value. A root 32-bit constant takes the `uint32` format
/// (`OldMachineTerm::in_format32`), so it prints as itself.
#[track_caller]
pub fn uint32(bits: impl Into<OldMachineTerm>) -> ProgramValue {
    let bits = bits.into();
    if crate::kernel::machine_integer::format_audit::is_sign_free_word_operator(&bits) {
        crate::kernel::machine_integer::format_audit::record(
            crate::kernel::machine_integer::format_audit::WordIdentity::UInt32OperatorAtInt32,
            std::panic::Location::caller(),
        );
    }
    ProgramValue::UInt32(bits.in_format32(crate::kernel::MachineIntegerType::UInt32))
}

/// A 64-bit value. A plain 32-bit constant, as `int64(-1)` writes, is widened
/// to the 64-bit constant it denotes, sign-extended for `int64` and
/// zero-extended for `uint64`, so the value's term has the value's width.
pub fn int64(bits: impl Into<OldMachineTerm>) -> ProgramValue {
    ProgramValue::Int64(match bits.into() {
        bits32_constant!(bits) => {
            OldMachineTerm::int64_constant(i64::from(constant_u32(bits) as i32))
        }
        term => term,
    })
}

pub fn uint64(bits: impl Into<OldMachineTerm>) -> ProgramValue {
    ProgramValue::UInt64(match bits.into() {
        bits32_constant!(bits) => OldMachineTerm::uint64_constant(u64::from(constant_u32(bits))),
        term => term,
    })
}

pub fn float32(bits: impl Into<OldMachineTerm>) -> ProgramValue {
    ProgramValue::Float32(bits.into())
}

pub fn float64(bits: impl Into<OldMachineTerm>) -> ProgramValue {
    ProgramValue::Float64(bits.into())
}

/// True when `pointer` addresses within a live heap allocation of `memory`,
/// matching allocation keys through the path's pointer equalities or exact
/// materialization of loads embedded in the key and pointer forms.
pub(crate) fn memory_holds_live_heap_allocation_at(
    memory: &super::SymbolicMemory,
    pointer: &Address,
    assumptions: &PureFactContext,
) -> bool {
    memory.is_live_heap_address(pointer, assumptions)
        || memory.heap_live_allocation_bases().any(|base| {
            base.base == pointer.base
                && super::assumptions::pointer_offsets_equal_after_exact_materialization(
                    &base.offset,
                    &pointer.offset,
                )
        })
}

/// Recognizes two condition-fact forms as the same fact under the given
/// assumptions, with the exact matching rule the atomic prover applies when
/// it consumes a context fact: memory-resolution load equality and
/// decide-driven term equality. This is a bounded check, not a search.
pub fn program_condition_facts_match_for_transport(
    source: &Proposition,
    target: &Proposition,
    assumptions: &PureFactContext,
) -> bool {
    let (
        Proposition::ConditionIs(source_condition, source_value),
        Proposition::ConditionIs(target_condition, target_value),
    ) = (source, target)
    else {
        return false;
    };
    source_value == target_value
        && assumptions.condition_matches(source_condition.old_form(), target_condition.old_form())
}

/// The `transport` rule for one bare condition: `context` states it, it
/// holds by memory resolution from the facts in `context`, or a quantified
/// fact instantiated at its terms states it.
fn condition_target_reaches(context: &PureFactContext, target: &Proposition) -> bool {
    let Proposition::ConditionIs(condition, value) = target else {
        return false;
    };
    context.proves_exact(target)
        || contract_certification::condition_holds_by_memory_resolution(context, condition.old_form(), *value)
        || contract_certification::condition_holds_by_instantiated_fact(
            context,
            condition.old_form(),
            *value,
            &|premise| transport_premise_holds(context, premise),
        )
        // A native 8- or 16-bit comparison reaches as the signed `int32`
        // comparison of its operands' widenings, which has its truth
        // (`narrow_comparison_as_int32`).
        || crate::kernel::machine_integer::comparison::narrow_proposition_as_int32(target)
            .is_some_and(|widened| condition_target_reaches(context, &widened))
}

/// A premise of a quantified fact `transport` instantiates: each conjunct
/// is settled by an exact route or reaches like a target.
fn transport_premise_holds(context: &PureFactContext, premise: &Proposition) -> bool {
    match premise {
        Proposition::And(left, right) => {
            transport_premise_holds(context, left) && transport_premise_holds(context, right)
        }
        _ => context.settles_exactly(premise) || condition_target_reaches(context, premise),
    }
}

/// Certifies a stated condition target from one explicit condition source and
/// deterministic memory-resolution evidence. Unlike whole-fact transport,
/// this permits a target to retain an old load on one side while transporting
/// the other side to a newer state.
pub(crate) fn program_condition_fact_target_reaches_in_context(
    source: &Proposition,
    target: &Proposition,
    assumptions: &PureFactContext,
) -> bool {
    if !matches!(source, Proposition::ConditionIs(_, _))
        || !matches!(target, Proposition::ConditionIs(_, _))
    {
        return false;
    }
    let with_source = if super::proposition_holds_without_facts(source) {
        assumptions.clone()
    } else {
        assumptions.clone().assume_proposition(source.clone())
    };
    // The source is fully represented by this context (or is a tautology).
    // Different reflexive source spellings must not repeat the same failed
    // target question. Successes still run and record their own consulted premises.
    super::closure_memoized_fact_check(
        super::ClosureFactCheck::ConditionTarget,
        &[target],
        None,
        &with_source,
        &[],
        || condition_target_reaches(&with_source, target),
    )
}

/// Exports target-directed transport only when every contextual dependency
/// can be retained as an explicit theorem premise. Callers that merely need
/// to check a fact inside one live context use the context-bound predicate
/// above instead of turning that context into reusable authority.
pub fn prove_program_condition_fact_target_transport(
    source: &Proposition,
    target: &Proposition,
    assumptions: &PureFactContext,
) -> Option<Theorem> {
    let (proved, premises) = crate::kernel::collect_consulted_premises(|| {
        crate::kernel::capture_implicit_consulted_premises(|| {
            program_condition_fact_target_reaches_in_context(source, target, assumptions)
        })
    });
    if !proved {
        return None;
    }
    // Consulted-premise collection proposes an output-sized premise set; it is not
    // itself authority. Recheck against only that set plus the explicit
    // source, so an unrecorded ambient dependency can only make construction
    // fail, never disappear into the exported theorem.
    let restricted = premises
        .iter()
        .cloned()
        .fold(PureFactContext::new(), |context, premise| {
            context.assume_proposition(premise)
        })
        .assume_proposition(source.clone());
    condition_target_reaches(&restricted, target)
        .then(|| program_condition_fact_transport_theorem(source, target.clone(), premises))
}

#[derive(Clone, Debug)]
pub struct LoopPreservationContext {
    state: ExecutionState,
    /// Guard facts for this entry path, retained before publishing the entry join.
    entry_guard: Vec<Proposition>,
    /// Retain the exact frame paired with this persistent body checkpoint.
    /// Rebuilding an equal loop head gives a different mutation history.
    exit_frame: Option<ResourceContext>,
    loop_entry_state: ExecutionState,
    pure_facts: Vec<Proposition>,
    /// One selected semantic proposition per declared invariant, including
    /// clauses already present in the ambient fact context.
    invariant_propositions: Vec<Proposition>,
    /// The binders this loop's `owns name: resource(...)` clauses declare.
    /// The back edge binds those names again on whatever the body ends
    /// holding, so the join needs them beside the head state.
    binders: Vec<crate::kernel::LoopBinder>,
    /// The head's pass count `K`: the invariants this head assumes read
    /// `iterations` as `K`, and the back edge owes them at `K + 1`
    /// ([`loop_invariant_obligations_at_back_edge`]).
    iterations: IntegerTerm,
    /// The execution's fresh-variable counter after building this head.
    ///
    /// Preparing the head invents identities -- the havoc of every local and
    /// every mutable cell the body writes, a re-bound binder's model fields,
    /// an arbitrary algebraic binding -- from the execution's one counter,
    /// which this context is built with. Carrying the mark back is what makes
    /// it impossible to take the head state and keep the old counter: the
    /// iteration that continues past the loop, and the body proof that runs
    /// inside it, both continue from here.
    next_kernel_variable: u64,
    /// The head this context's body runs from. The loop rule's exits use
    /// it too, so its back edges and exits share one head.
    head: std::sync::Arc<super::loops::LoopHead>,
}

/// Facts retained by a checked loop exit. Explicit constructor inputs have
/// their own scope; existing proof scopes retain their store and its context.
#[derive(Clone)]
pub(crate) enum LoopExitFacts {
    Explicit(std::sync::Arc<[Proposition]>),
    Retained(std::sync::Arc<crate::kernel::proof::PureFactStore>),
}
impl std::fmt::Debug for LoopExitFacts {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}
impl PartialEq for LoopExitFacts {
    fn eq(&self, other: &Self) -> bool {
        self.iter().eq(other.iter())
    }
}
impl Eq for LoopExitFacts {}
impl From<Vec<Proposition>> for LoopExitFacts {
    fn from(facts: Vec<Proposition>) -> Self {
        Self::Explicit(facts.into())
    }
}
impl LoopExitFacts {
    pub(crate) fn iter(&self) -> Box<dyn Iterator<Item = &Proposition> + '_> {
        match self {
            Self::Explicit(facts) => Box::new(facts.iter()),
            Self::Retained(facts) => Box::new(facts.propositions()),
        }
    }
    /// Add only this retained scope's delta to the incoming context. An
    /// opposite truth is still admitted and records the original contradiction.
    pub(crate) fn context_with(&self, ambient: &PureFactContext) -> PureFactContext {
        let facts = match self {
            Self::Retained(facts) => facts,
            Self::Explicit(facts) => {
                return super::reasoning::path_facts::assumptions_with_propositions(ambient, facts);
            }
        };
        let mut context = ambient.clone();
        for change in ambient
            .execution_fact_projection
            .diff(&facts.assumptions().execution_fact_projection)
        {
            match change {
                imbl::ordmap::DiffItem::Add(_, fact)
                | imbl::ordmap::DiffItem::Update { new: (_, fact), .. } => {
                    context = context.assume_execution_pure_fact(fact);
                }
                imbl::ordmap::DiffItem::Remove(..) => {}
            }
        }
        for (composition, in_ambient) in ambient
            .resource_compositions
            .diff(&facts.assumptions().resource_compositions)
        {
            if !in_ambient {
                context = context
                    .assume_proposition(Proposition::ResourceComposition(composition.clone()));
            }
        }
        context
    }
    pub(crate) fn certified_facts(&self) -> ExecutionFacts {
        match self {
            Self::Explicit(facts) => facts
                .iter()
                .cloned()
                .map(ExecutionPureFact::certified)
                .collect(),
            Self::Retained(facts) => facts
                .shared_presented_propositions()
                .map(|fact| ExecutionPureFact::from_shared(fact).into_certified())
                .collect(),
        }
    }
}
impl crate::kernel::proof::PropositionSource for LoopExitFacts {
    fn exact_available(&self, required: &Proposition) -> bool {
        match self {
            Self::Explicit(facts) => facts.as_ref().exact_available(required),
            Self::Retained(facts) => facts.exact_available(required),
        }
    }
    fn ordered_fact_store(&self) -> crate::kernel::proof::PureFactStore {
        match self {
            Self::Explicit(facts) => facts.as_ref().ordered_fact_store(),
            Self::Retained(facts) => facts.ordered_fact_store(),
        }
    }
    fn propositions(&self) -> impl Iterator<Item = &Proposition> {
        self.iter()
    }
    fn pure_context(&self) -> PureFactContext {
        match self {
            Self::Explicit(facts) => facts.as_ref().pure_context(),
            Self::Retained(facts) => facts.assumptions().clone(),
        }
    }
    fn fact_store(&self) -> crate::kernel::proof::PureFactStore {
        match self {
            Self::Explicit(facts) => facts.as_ref().fact_store(),
            Self::Retained(facts) => (**facts).clone(),
        }
    }
}

/// A body state produced by a checked preservation proof that may be the
/// final loop iteration. A guard-exit candidate requires an independently
/// checked false post-body condition. A natural cycle's checked forward jump
/// instead carries its target and is exported at its own state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LoopFinalExitCandidate {
    state: ExecutionState,
    jump_target: Option<ControlTargetId>,
    guard_points_index: Option<usize>,
    /// A checked exit is copied into the loop rule; its facts stay shared.
    pure_facts: LoopExitFacts,
    borrow_evidence: crate::kernel::borrows::CheckedBorrowCallEvidenceSequence,
}

impl LoopFinalExitCandidate {
    pub(crate) fn from_store(
        state: ExecutionState,
        facts: &crate::kernel::proof::PureFactStore,
    ) -> Self {
        Self {
            state,
            jump_target: None,
            guard_points_index: None,
            pure_facts: LoopExitFacts::Retained(Arc::new(facts.clone())),
            borrow_evidence: crate::kernel::borrows::empty_checked_borrow_evidence_sequence(),
        }
    }

    #[cfg(test)]
    pub(crate) fn new(state: ExecutionState, pure_facts: Vec<Proposition>) -> Self {
        crate::instrumentation::record_deterministic_work(pure_facts.len());
        Self {
            state,
            jump_target: None,
            guard_points_index: None,
            pure_facts: pure_facts.into(),
            borrow_evidence: crate::kernel::borrows::empty_checked_borrow_evidence_sequence(),
        }
    }

    pub(crate) fn with_jump_target(mut self, target: ControlTargetId) -> Self {
        self.jump_target = Some(target);
        self
    }

    pub(crate) fn jump_target(&self) -> Option<ControlTargetId> {
        self.jump_target
    }

    pub(crate) fn with_guard_points_index(mut self, index: Option<usize>) -> Self {
        self.guard_points_index = index;
        self
    }

    pub(crate) fn guard_points_index(&self) -> Option<usize> {
        self.guard_points_index
    }

    pub(crate) fn with_borrow_evidence(
        mut self,
        borrow_evidence: crate::kernel::borrows::CheckedBorrowCallEvidenceSequence,
    ) -> Self {
        self.borrow_evidence = borrow_evidence;
        self
    }

    pub(crate) fn state(&self) -> &ExecutionState {
        &self.state
    }

    pub(crate) fn pure_facts(&self) -> &LoopExitFacts {
        &self.pure_facts
    }

    pub(crate) fn borrow_evidence(
        &self,
    ) -> &crate::kernel::borrows::CheckedBorrowCallEvidenceSequence {
        &self.borrow_evidence
    }
}

/// One certified iteration path that exits instead of reaching the back edge.
///
/// Written breaks, false tests and checked natural exits carry the state and
/// facts they reached. They owe no back-edge invariant closure or decrease.
/// One loop head of a proof-driven loop and the states its checked body
/// reached when it returned there: the iterations no exit's path holds. The
/// loop rule reads their writes from the memory history and records them on
/// the loop's exits.
#[derive(Clone, Debug)]
pub(crate) struct LoopBackEdges {
    pub(super) head: std::sync::Arc<super::loops::LoopHead>,
    pub(super) states: Vec<ExecutionState>,
    /// The fresh-variable counter after the head was built: identities
    /// below it may belong to the head.
    pub(super) next_kernel_variable: u64,
}

/// The loop rule joins these paths with its direct guard-false exit into the
/// single successor the enclosing frontier continues from.
#[derive(Clone, Debug)]
pub(crate) struct LoopEarlyExit {
    state: ExecutionState,
    guard_false: bool,
    guard_points_index: Option<usize>,
    /// A checked exit is copied into the loop rule; its facts stay shared.
    pure_facts: LoopExitFacts,
    borrow_evidence: crate::kernel::borrows::CheckedBorrowCallEvidenceSequence,
}

impl PartialEq for LoopEarlyExit {
    fn eq(&self, other: &Self) -> bool {
        self.state == other.state
            && self.guard_false == other.guard_false
            && self.guard_points_index == other.guard_points_index
            && self.pure_facts == other.pure_facts
            && self.borrow_evidence == other.borrow_evidence
    }
}
impl Eq for LoopEarlyExit {}

impl LoopEarlyExit {
    pub(crate) fn new(state: ExecutionState, pure_facts: Vec<Proposition>) -> Self {
        crate::instrumentation::record_deterministic_work(pure_facts.len());
        Self {
            state,
            guard_false: false,
            guard_points_index: None,
            pure_facts: pure_facts.into(),
            borrow_evidence: crate::kernel::borrows::empty_checked_borrow_evidence_sequence(),
        }
    }

    /// Retain the checked context alongside the exact facts it indexed.
    pub(crate) fn from_store(
        state: ExecutionState,
        facts: &crate::kernel::proof::PureFactStore,
    ) -> Self {
        Self {
            state,
            guard_false: false,
            guard_points_index: None,
            pure_facts: LoopExitFacts::Retained(Arc::new(facts.clone())),
            borrow_evidence: crate::kernel::borrows::empty_checked_borrow_evidence_sequence(),
        }
    }

    pub(crate) fn with_guard_false(mut self, guard_false: bool) -> Self {
        self.guard_false = guard_false;
        self
    }

    pub(crate) fn guard_false(&self) -> bool {
        self.guard_false
    }

    pub(crate) fn fact_context(&self) -> Option<&PureFactContext> {
        match &self.pure_facts {
            LoopExitFacts::Retained(facts) => Some(facts.assumptions()),
            LoopExitFacts::Explicit(_) => None,
        }
    }

    pub(crate) fn with_guard_points_index(mut self, index: Option<usize>) -> Self {
        self.guard_points_index = index;
        self
    }

    pub(crate) fn guard_points_index(&self) -> Option<usize> {
        self.guard_points_index
    }

    pub(crate) fn with_borrow_evidence(
        mut self,
        borrow_evidence: crate::kernel::borrows::CheckedBorrowCallEvidenceSequence,
    ) -> Self {
        self.borrow_evidence = borrow_evidence;
        self
    }

    pub(crate) fn state(&self) -> &ExecutionState {
        &self.state
    }

    pub(crate) fn pure_facts(&self) -> &LoopExitFacts {
        &self.pure_facts
    }

    pub(crate) fn borrow_evidence(
        &self,
    ) -> &crate::kernel::borrows::CheckedBorrowCallEvidenceSequence {
        &self.borrow_evidence
    }
}

/// One certified body path that left the loop, and its function, through
/// `return`.
///
/// A `return` inside a summarized body is a function exit, not a back edge:
/// the invariants are not closed on it and no measure is required to
/// decrease. The proof layer supplies the returned value, the state the path
/// reached and the facts retained there; the loop rule exports the path as a
/// `Return` outcome of the loop statement, so the enclosing execution
/// certifies the postcondition and the resource obligations on exactly that
/// value and state instead of dropping the path. It is never offered to the
/// loop guard: a guard that is never false, a natural cycle's `while (1)`,
/// would otherwise swallow it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LoopReturnExit {
    value: StoredExecutionValue,
    state: ExecutionState,
    /// A checked exit is copied into the loop rule; its facts stay shared.
    pure_facts: LoopExitFacts,
    borrow_evidence: crate::kernel::borrows::CheckedBorrowCallEvidenceSequence,
}

impl LoopReturnExit {
    pub(crate) fn from_store(
        value: impl Into<StoredExecutionValue>,
        state: ExecutionState,
        facts: &crate::kernel::proof::PureFactStore,
    ) -> Self {
        Self {
            value: value.into(),
            state,
            pure_facts: LoopExitFacts::Retained(Arc::new(facts.clone())),
            borrow_evidence: crate::kernel::borrows::empty_checked_borrow_evidence_sequence(),
        }
    }

    pub(crate) fn with_borrow_evidence(
        mut self,
        borrow_evidence: crate::kernel::borrows::CheckedBorrowCallEvidenceSequence,
    ) -> Self {
        self.borrow_evidence = borrow_evidence;
        self
    }

    pub(crate) fn value(&self) -> &StoredExecutionValue {
        &self.value
    }

    pub(crate) fn state(&self) -> &ExecutionState {
        &self.state
    }

    pub(crate) fn pure_facts(&self) -> &LoopExitFacts {
        &self.pure_facts
    }

    pub(crate) fn borrow_evidence(
        &self,
    ) -> &crate::kernel::borrows::CheckedBorrowCallEvidenceSequence {
        &self.borrow_evidence
    }
}

#[cfg(test)]
pub(super) fn path_function_outcome(path: &SymbolicExecutionPath) -> Option<&FunctionOutcome> {
    let mut proposition = path.theorem.proposition();
    while let Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    match proposition {
        Proposition::ProgramFunctionVerifies { outcome, .. } => Some(outcome),
        _ => None,
    }
}

#[cfg(test)]
mod loop_exit_sharing_tests {
    use super::*;

    #[test]
    fn retained_exit_context_records_opposite_truth_without_changing_parent() {
        use crate::kernel::proof::PureFactStore;
        let condition = OldConditionTerm::equal(
            OldMachineTerm::Variable(Variable(9_901_100)),
            OldMachineTerm::constant(0),
        );
        let before = Proposition::condition_is(condition.clone(), true);
        let after = Proposition::condition_is(condition, false);
        let ambient = PureFactStore::from_ordered(std::slice::from_ref(&before));
        let path = PureFactStore::from_ordered(std::slice::from_ref(&after));
        let exit = LoopFinalExitCandidate::from_store(ExecutionState::new(), &path);
        let joined = exit.pure_facts().context_with(ambient.assumptions());
        assert!(joined.is_inconsistent());
        assert!(!ambient.assumptions().is_inconsistent());
        assert!(!path.assumptions().is_inconsistent());
        assert!(ambient.contains(&before));
        assert!(!ambient.contains(&after));
    }

    #[test]
    fn natural_forward_exit_is_a_jump_and_only_absent_exits_diverge() {
        let backedge = ControlTargetId(1);
        let exit_target = ControlTargetId(2);
        let statement = program_while(
            crate::kernel::program_expression::int32_literal(1),
            Vec::new(),
            program_goto(backedge),
        )
        .with_backedge_target(backedge)
        .with_natural_exit_target(exit_target);
        let check = |candidates| {
            prove_symbolic_loop_exit_with_proven_phases(
                ExecutionState::new(),
                statement.clone(),
                PureFactContext::new(),
                ExecutionEnvironment::new(),
                true,
                true,
                candidates,
                Vec::new(),
                Vec::new(),
            )
        };
        let (_, returned) = check(vec![
            LoopFinalExitCandidate::new(ExecutionState::new(), Vec::new())
                .with_jump_target(exit_target),
        ]);
        let returned = returned.expect("a checked forward jump must form a loop rule");
        assert_eq!(returned.paths.len(), 1);
        assert!(matches!(
            returned.paths[0].outcome,
            StatementOutcome::Jump { target, .. } if target == exit_target
        ));
        let (_, divergent) = check(Vec::new());
        let divergent = divergent.expect("a loop with no reachable exits can diverge");
        assert_eq!(divergent.paths.len(), 1);
        assert!(matches!(
            divergent.paths[0].outcome,
            StatementOutcome::VerificationDiverges
        ));
        let (_, invalid) = check(vec![
            LoopFinalExitCandidate::new(ExecutionState::new(), Vec::new())
                .with_jump_target(ControlTargetId(3)),
        ]);
        assert!(
            invalid.is_none(),
            "a different target cannot certify this loop"
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../scaling_tests/kernel/api/loop_exit_sharing_tests.rs");
    }
}

impl LoopPreservationContext {
    /// The states this context's checked body reached when it returned to
    /// the head, for the loop rule.
    pub(crate) fn back_edges(&self, states: Vec<ExecutionState>) -> LoopBackEdges {
        LoopBackEdges {
            head: self.head.clone(),
            states,
            next_kernel_variable: self.next_kernel_variable,
        }
    }

    pub(crate) fn restored_exit(
        &self,
        state: &ExecutionState,
        facts: &crate::kernel::proof::PureFactStore,
        assumptions: &PureFactContext,
    ) -> (ExecutionState, crate::kernel::proof::PureFactStore) {
        (self.restored_exit_state(state, assumptions), facts.clone())
    }

    pub(crate) fn restored_exit_state(
        &self,
        state: &ExecutionState,
        assumptions: &PureFactContext,
    ) -> ExecutionState {
        let rebound = crate::kernel::loop_state_with_loop_binders_rebound(
            &self.state,
            state,
            &self.binders,
            assumptions,
        )
        .unwrap_or_else(|_| state.clone());
        self.exit_frame.as_ref().map_or_else(
            || rebound.clone(),
            |frame| {
                crate::kernel::loops::restore_loop_exit_state(
                    &rebound,
                    self.state.resources(),
                    frame,
                    assumptions,
                )
            },
        )
    }

    // A return has no post-loop scope. Preserve the body's output bindings;
    // rebinding them to loop names would invalidate named `produces` results.
    pub(crate) fn restored_return(
        &self,
        state: &ExecutionState,
        facts: &crate::kernel::proof::PureFactStore,
        assumptions: &PureFactContext,
    ) -> (ExecutionState, crate::kernel::proof::PureFactStore) {
        let restored = self.exit_frame.as_ref().map_or_else(
            || state.clone(),
            |frame| {
                crate::kernel::loops::restore_loop_exit_state(
                    state,
                    self.state.resources(),
                    frame,
                    assumptions,
                )
            },
        );
        let facts = facts.clone();
        (restored, facts)
    }

    pub fn state(&self) -> &ExecutionState {
        &self.state
    }

    pub fn loop_entry_state(&self) -> &ExecutionState {
        &self.loop_entry_state
    }

    pub(crate) fn entry_guard(&self) -> &[Proposition] {
        &self.entry_guard
    }

    pub fn pure_facts(&self) -> &[Proposition] {
        &self.pure_facts
    }

    pub fn invariant_propositions(&self) -> &[Proposition] {
        &self.invariant_propositions
    }

    /// The binders this loop's header declares.
    pub fn binders(&self) -> &[crate::kernel::LoopBinder] {
        &self.binders
    }

    /// The execution's fresh-variable counter after this head was built. It
    /// is never below the counter the head was built from, so an execution
    /// that continues from it only moves forward.
    /// The head's pass count `K`, which a preserve proof reads as
    /// `iterations`.
    pub fn iterations(&self) -> &IntegerTerm {
        &self.iterations
    }

    pub fn next_kernel_variable(&self) -> u64 {
        self.next_kernel_variable
    }
}

/// Why a loop head could not be built.
///
/// A premise the head owes is returned as the proposition itself, beside the
/// head state whose locals name its variables, so the surface spells it in
/// the source's names instead of the kernel printing its internal form.
#[derive(Clone, Debug)]
pub enum LoopHeadRefusal {
    /// A refusal the kernel spells on its own.
    Message(String),
    Contract(String),
    Tactic(String),
    /// A declared loop resource could not be read at the loop entry.
    ResourceEvaluation(String),
    /// The loop test did not produce a value on a reachable path.
    GuardEvaluation(String),
    /// A premise the head's guard owes that the entry context does not
    /// discharge. The invariants owe none here: their side conditions are
    /// invariant content, assumed at the head and owed at entry and at every
    /// back edge.
    MissingPrerequisite {
        proposition: Proposition,
        context: Option<String>,
        /// The loop-top state the premise is stated over.
        state: ExecutionState,
    },
    /// A resource the loop declares that the enclosing context does not
    /// hold, evaluated over `state`.
    UnheldResource {
        fact: ResourceFact,
        state: ExecutionState,
    },
}

impl From<String> for LoopHeadRefusal {
    fn from(message: String) -> Self {
        Self::Message(message)
    }
}

#[allow(clippy::too_many_arguments)]
pub fn loop_preservation_contexts(
    loop_entry_state: &ExecutionState,
    condition: &ProgramExpression,
    invariant_checks: &[LoopInvariantCheck],
    effect_checks: &[LoopEffectCheck],
    resource_specs: &[ResourceSpec],
    definitions: &[CompositeResourceDefinition],
    body: &ProgramStatement,
    assumptions: &PureFactContext,
    next_kernel_variable: u64,
) -> Result<Vec<LoopPreservationContext>, LoopHeadRefusal> {
    loop_phase_preservation_contexts(
        loop_entry_state,
        Some(condition),
        invariant_checks,
        effect_checks,
        resource_specs,
        definitions,
        body,
        assumptions,
        next_kernel_variable,
    )
}

/// Computes loop-body preservation contexts for a C `do ... while` loop.
/// Unlike a pre-tested `while`, the first body entry cannot assume that the
/// post-test condition is true; the condition only guards later iterations.
pub fn program_do_while_preservation_contexts(
    loop_entry_state: &ExecutionState,
    condition: &ProgramExpression,
    invariant_checks: &[LoopInvariantCheck],
    effect_checks: &[LoopEffectCheck],
    resource_specs: &[ResourceSpec],
    definitions: &[CompositeResourceDefinition],
    body: &ProgramStatement,
    assumptions: &PureFactContext,
    next_kernel_variable: u64,
) -> Result<Vec<LoopPreservationContext>, LoopHeadRefusal> {
    let test = LoopTestRegion::expression(condition.clone(), LoopTestPosition::AfterBody);
    let pass = program_loop_pass(body, None, Some(&test));
    loop_phase_preservation_contexts(
        loop_entry_state,
        None,
        invariant_checks,
        effect_checks,
        resource_specs,
        definitions,
        &pass,
        assumptions,
        next_kernel_variable,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn loop_phase_preservation_contexts(
    loop_entry_state: &ExecutionState,
    condition: Option<&ProgramExpression>,
    invariant_checks: &[LoopInvariantCheck],
    effect_checks: &[LoopEffectCheck],
    resource_specs: &[ResourceSpec],
    definitions: &[CompositeResourceDefinition],
    body: &ProgramStatement,
    assumptions: &PureFactContext,
    next_kernel_variable: u64,
) -> Result<Vec<LoopPreservationContext>, LoopHeadRefusal> {
    // The head inherits the execution's counter instead of restarting at the
    // base of the identity range. Restarting it in the middle of an execution
    // is how a havocked local, a re-bound binder's model field or an
    // arbitrary algebraic binding comes to carry an identity the execution
    // has already handed to something live.
    let mut budget = ExecutionBudget::continuing_from(next_kernel_variable);
    let mut existing_variables = BTreeSet::new();
    crate::instrumentation::measure_operation("", "", "loop entry state reservation", || {
        collect_execution_state_reservations(
            loop_entry_state,
            budget.next_kernel_variable,
            None,
            &mut existing_variables,
        );
    });
    if let Some(condition) = condition {
        collect_program_expression_bitvector_variables(condition, &mut existing_variables);
    }
    for check in invariant_checks {
        collect_spec_proposition_bitvector_variables(check.proposition(), &mut existing_variables);
    }
    for check in effect_checks {
        collect_loop_effect_bitvector_variables(check.effect(), &mut existing_variables);
    }
    collect_execution_statement_bitvector_variables(body, &mut existing_variables);
    // The context's variables are the whole path's before the loop. The
    // head's identities come from the execution counter, which normally
    // already lies above every one of them, so they are reserved through the
    // ceiling the context keeps and collected only for a query below it.
    let path_assumptions = assumptions.clone();
    let mut variables = KernelVariableGenerator::fresh_for_execution_with_shared_reservations(
        existing_variables,
        crate::kernel::LazyReservedVariables::new(
            assumptions.execution_variable_ceiling(),
            move || {
                let mut variables = BTreeSet::new();
                collect_assumption_variables(&path_assumptions, &mut variables);
                std::sync::Arc::new(variables)
            },
        ),
    );
    let head = prepare_loop_top_state(
        loop_entry_state,
        effect_checks,
        invariant_checks,
        resource_specs,
        definitions,
        body,
        assumptions,
        &mut budget,
        &mut variables,
    )
    .map_err(|error| {
        format!(
            "could not prepare the loop head: it stopped at {}",
            error.describe()
        )
    })?;
    if let Some(failure) = head.resource_failures.first() {
        return Err(match failure {
            super::loops::LoopResourceFailure::Message(message) => {
                LoopHeadRefusal::Message(message.clone())
            }
            super::loops::LoopResourceFailure::Contract(message) => {
                LoopHeadRefusal::Contract(message.clone())
            }
            super::loops::LoopResourceFailure::Tactic(message) => {
                LoopHeadRefusal::Tactic(message.clone())
            }
            super::loops::LoopResourceFailure::Evaluation(message) => {
                LoopHeadRefusal::ResourceEvaluation(message.clone())
            }
            super::loops::LoopResourceFailure::Unheld { fact, state } => {
                LoopHeadRefusal::UnheldResource {
                    fact: fact.clone(),
                    state: state.clone(),
                }
            }
        });
    }
    let shared_head = std::sync::Arc::new(head.clone());
    // Preservation runs the body with the loop's declared resources.
    let exit_frame = head
        .narrows_resources()
        .then(|| head.top.resources().clone());
    let top_state = head.body;
    let iterations = head.iterations;
    let whole_loop_effect_summaries = head.summaries;
    let whole_loop_effect_facts = whole_loop_effect_summaries
        .iter()
        .cloned()
        .map(ExecutionPureFact::new)
        .collect::<Vec<_>>();
    let mut contexts = Vec::new();
    for (invariant_facts, invariant_obligations, invariant_propositions) in assume_invariant_checks(
        &top_state,
        loop_entry_state,
        invariant_checks,
        &iterations,
        assumptions,
        &whole_loop_effect_facts,
        &[],
        &mut budget,
    )
    .map_err(|error| {
        loop_head_invariant_failure(
            &top_state,
            loop_entry_state,
            invariant_checks,
            &iterations,
            assumptions,
            error,
        )
    })? {
        let condition_contexts = crate::kernel::loops::assume_loop_entry_truthiness(
            &top_state,
            condition,
            definitions,
            assumptions,
            &invariant_facts,
            &invariant_obligations,
            true,
            &mut budget,
        )
        .map_err(|error| format!("could not assume the loop test: {}", error.describe()))?;
        // A disjunctive guard such as `while (a || b)` has one way *in* per
        // disjunct, and the body runs on each of them with only that path's
        // own guard facts. The mirror of the exit join: export the
        // disjunction of what each entry path states alone, so one written
        // proof can reason by cases over the ways the guard was true instead
        // of needing a different certificate per entry path.
        let entry_guards = condition_contexts
            .iter()
            .map(|assumption| {
                assumption
                    .facts
                    .iter()
                    .map(|fact| fact.proposition().clone())
                    .filter(|proposition| {
                        !invariant_facts
                            .iter()
                            .any(|fact| fact.proposition() == proposition)
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let entry_disjunction = crate::kernel::loops::guard_path_disjunction(&entry_guards);
        for (assumption, guard) in condition_contexts.into_iter().zip(entry_guards) {
            let entry_guard = guard;
            // A guard operand this function may not read leaves the head's
            // premises undefined; there is no iteration to describe here.
            if let Some(outcome) = assumption.undecided_outcome() {
                return Err(LoopHeadRefusal::GuardEvaluation(
                    undecided_loop_guard_context(outcome),
                ));
            }
            let ConditionAssumption {
                facts, obligations, ..
            } = assumption;
            let context_assumptions = assumptions_with_path_context(assumptions, &facts, &[]);
            if let Some(obligation) = obligations.iter().find(|obligation| {
                !required_obligation_is_exactly_discharged(
                    &context_assumptions,
                    obligation.proposition(),
                )
            }) {
                return Err(LoopHeadRefusal::MissingPrerequisite {
                    proposition: obligation.proposition().clone(),
                    context: obligation.context().map(str::to_string),
                    state: top_state.clone(),
                });
            }
            let mut pure_facts = facts
                .into_iter()
                .map(|fact| fact.proposition().clone())
                .collect::<Vec<_>>();
            // D7 applied to refutation at the loop head. The invariants and
            // the loop condition together may refute an arm of a binder's
            // model, and the body needs that conclusion as a premise: an
            // ascending loop learns `ctx.model != Context::Top` from
            // `parent != 0` against the `Top` arm's `fact parent == 0`, which
            // is what lets its proof `match` close that arm by contradiction
            // instead of unfolding a frame it does not hold.
            pure_facts.extend(
                crate::kernel::publish_instance_arms(
                    top_state.resources(),
                    definitions,
                    &top_state,
                    &context_assumptions,
                )
                .model_facts,
            );
            if let Some(disjunction) = &entry_disjunction {
                pure_facts.push(disjunction.clone());
            }
            pure_facts.sort();
            pure_facts.dedup();
            contexts.push(LoopPreservationContext {
                entry_guard,
                state: top_state.clone(),
                exit_frame: exit_frame.clone(),
                loop_entry_state: loop_entry_state.clone(),
                pure_facts,
                invariant_propositions: invariant_propositions.iter().cloned().collect(),
                binders: crate::kernel::loop_binders(resource_specs),
                iterations: iterations.clone(),
                // Filled in below from the one budget every context here was
                // built with, so each reports the same high-water mark rather
                // than the mark at the moment it happened to be pushed.
                next_kernel_variable,
                head: shared_head.clone(),
            });
        }
    }
    // One budget served every context above, so its final mark bounds every
    // identity any of them carries. An execution continuing from any of them
    // continues from here.
    let reached = budget.next_kernel_variable();
    for context in &mut contexts {
        context.next_kernel_variable = reached;
    }
    Ok(contexts)
}

/// Names the loop invariant that could not be read at the abstract loop head.
///
/// The usual cause is an invariant that reads a resource instance the loop did
/// not declare: the body holds exactly the loop's own resources, so a binder
/// the header does not name has no model to read there. Retrying the checks
/// one at a time costs one lowering per invariant and only on the failing
/// path.
fn loop_head_invariant_failure(
    top_state: &ExecutionState,
    loop_entry_state: &ExecutionState,
    invariant_checks: &[LoopInvariantCheck],
    iterations: &IntegerTerm,
    assumptions: &PureFactContext,
    error: ExecutionLimit,
) -> LoopHeadRefusal {
    let mut budget = ExecutionBudget::beside_live_state();
    for check in invariant_checks {
        if matches!(
            assume_invariant_checks(
                top_state,
                loop_entry_state,
                std::slice::from_ref(check),
                iterations,
                assumptions,
                &[],
                &[],
                &mut budget,
            ),
            Err(ExecutionLimit::ResourceFieldInstanceUnavailable)
        ) {
            let context = invariant_context(check, InvariantPhase::Preservation)
                .unwrap_or("a loop invariant");
            return LoopHeadRefusal::Contract(format!(
                "{context}: could not be read at the loop head; a loop invariant may only read the resource instances the loop declares"
            ));
        }
    }
    LoopHeadRefusal::Message(format!(
        "could not assume loop invariants: they stopped at {}",
        error.describe()
    ))
}

pub fn loop_invariant_obligations_at_back_edge(
    state: &ExecutionState,
    iteration_entry_state: &ExecutionState,
    invariant_checks: &[LoopInvariantCheck],
    head_iterations: &IntegerTerm,
    assumptions: &PureFactContext,
) -> Result<Vec<ProofObligation>, String> {
    collect_invariant_check_obligations_without_search(
        state,
        iteration_entry_state,
        invariant_checks,
        InvariantPhase::Preservation,
        Some(head_iterations),
        assumptions,
        &mut ExecutionBudget::beside_live_state(),
    )
    .map_err(|error| {
        format!(
            "could not lower back-edge invariants: they stopped at {}",
            error.describe()
        )
    })
}

/// The source form of one declared `decreases` component, for diagnostics.
pub fn ranking_measure_source(measure: &RankingComponent) -> String {
    crate::kernel::termination::ranking_measure_display(measure)
}

/// The identity spelling of one declared `decreases` component: the form a
/// pure component's written source is keyed by, which must keep telling
/// different measures apart even where it has no source spelling.
pub fn ranking_measure_identity(measure: &RankingComponent) -> String {
    crate::kernel::termination::ranking_measure_key(measure)
}

/// The other members of each function's recursive component, for the
/// functions in a component of two or more, from a call graph keyed by
/// function name. Callees that are not keys are ignored.
///
/// This is untrusted input to the contract interface: a function's peers
/// decide which of its calls owe descent, and the termination check refuses
/// a component whose certified interfaces leave a member out. Work is linear
/// in the graph.
pub fn recursive_component_peers(
    calls: &BTreeMap<String, BTreeSet<String>>,
) -> BTreeMap<String, Vec<String>> {
    let names = calls.keys().collect::<Vec<_>>();
    let index = names
        .iter()
        .enumerate()
        .map(|(position, name)| (name.as_str(), position))
        .collect::<BTreeMap<_, _>>();
    let edges = calls
        .values()
        .map(|callees| {
            callees
                .iter()
                .filter_map(|callee| index.get(callee.as_str()).copied())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mut peers = BTreeMap::new();
    for component in super::owned_footprint_reach::strongly_connected_components(&edges) {
        if component.len() < 2 {
            continue;
        }
        for &member in &component {
            peers.insert(
                names[member].clone(),
                component
                    .iter()
                    .filter(|&&other| other != member)
                    .map(|&other| names[other].clone())
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect(),
            );
        }
    }
    peers
}

/// The environment one C function is certified under, carrying its recursion
/// anchor when it declares an expression `decreases` measure.
///
/// The caller says which function is being certified and at which entry; the
/// kernel reads the measure off that function's own contract interface and
/// evaluates it, so nothing about what the recursion is ranked by comes from
/// the caller. A function with no declared measure gets the environment back
/// unchanged, and today that is every function, so no existing certification
/// changes shape.
///
/// Both sides of contract certification derive the anchor here, from the same
/// function and the same arguments, which is why an artifact stepped without
/// an anchor does not satisfy `checked.environment == environment`: the
/// anchor is part of the environment's identity.
pub fn program_execution_environment_with_recursion_anchor(
    environment: ExecutionEnvironment,
    function: &ProgramFunction,
    caller_state: &ExecutionState,
    arguments: &[ProgramExpression],
) -> Result<ExecutionEnvironment, String> {
    program_execution_environment_with_recursion_anchor_reporting(
        environment,
        function,
        caller_state,
        arguments,
    )
    .map_err(|error| error.to_string())
}

pub(crate) fn program_execution_environment_with_recursion_anchor_reporting(
    environment: ExecutionEnvironment,
    function: &ProgramFunction,
    caller_state: &ExecutionState,
    arguments: &[ProgramExpression],
) -> Result<ExecutionEnvironment, TerminationError> {
    if !function.contract_interface().has_call_ranked_recursion() {
        return Ok(environment);
    }
    let entry_state =
        program_function_entry_state(caller_state, function, arguments).ok_or_else(|| {
            TerminationError {
                message: format!(
                    "could not bind `{}`'s arguments to read its `decreases` measure at entry",
                    function.name()
                ),
                function: Some(function.name().to_owned()),
                kind: TerminationErrorKind::Internal,
            }
        })?;
    let anchor = crate::kernel::termination::program_function_recursion_anchor(
        function,
        &entry_state,
        &PureFactContext::new(),
        &mut ExecutionBudget::beside_live_state(),
    )?;
    Ok(match anchor {
        Some(anchor) => environment.with_recursion_anchor(anchor),
        None => environment,
    })
}

/// The ranked loop's back-edge bundle members, after its invariants.
///
/// `iteration_entry_state` reads each declared component at preserve entry
/// and `state` at the back edge. The member order is fixed by
/// `collect_loop_ranking_obligations`; see that function for the shape.
pub fn loop_ranking_obligations_at_back_edge(
    state: &ExecutionState,
    iteration_entry_state: &ExecutionState,
    head_iterations: &IntegerTerm,
    ranking_measures: &[RankingComponent],
    assumptions: &PureFactContext,
) -> Result<Vec<ProofObligation>, String> {
    collect_loop_ranking_obligations(
        state,
        iteration_entry_state,
        Some(head_iterations),
        ranking_measures,
        assumptions,
        &mut ExecutionBudget::beside_live_state(),
    )
}

/// Exact entry judgments grouped by invariant declaration. Lowering's path
/// facts and loadability conditions remain guards on each judgment, with their
/// introduction metadata. A declaration can have several path judgments; an
/// empty group means no reachable lowering path. These are goals, not evidence
/// that initialization has proved them.
#[derive(Clone, Debug)]
pub struct LoopEntryGoals {
    declarations: Vec<Vec<ProofObligation>>,
}

impl LoopEntryGoals {
    pub fn declarations(&self) -> &[Vec<ProofObligation>] {
        &self.declarations
    }
}

pub fn loop_entry_goals(
    state: &ExecutionState,
    invariant_checks: &[LoopInvariantCheck],
    assumptions: &PureFactContext,
) -> Result<LoopEntryGoals, String> {
    let mut declarations = vec![Vec::new(); invariant_checks.len()];
    super::loops::collect_loop_entry_goals(
        state,
        invariant_checks,
        assumptions,
        &mut ExecutionBudget::beside_live_state(),
        &mut declarations,
    )
    .map_err(|error| {
        format!(
            "could not lower entry invariants: they stopped at {}",
            error.describe()
        )
    })?;
    Ok(LoopEntryGoals { declarations })
}

#[cfg(test)]
pub fn loop_invariant_obligations_at_entry(
    state: &ExecutionState,
    invariant_checks: &[LoopInvariantCheck],
    assumptions: &PureFactContext,
) -> Result<Vec<ProofObligation>, String> {
    collect_invariant_check_obligations_without_search(
        state,
        state,
        invariant_checks,
        InvariantPhase::Entry,
        None,
        assumptions,
        &mut ExecutionBudget::beside_live_state(),
    )
    .map_err(|error| {
        format!(
            "could not lower entry invariants: they stopped at {}",
            error.describe()
        )
    })
}

pub fn loop_invariants_hold_at_entry(
    state: &ExecutionState,
    invariant_checks: &[LoopInvariantCheck],
    assumptions: &PureFactContext,
) -> Result<(), String> {
    let obligations = collect_invariant_check_obligations(
        state,
        state,
        invariant_checks,
        InvariantPhase::Entry,
        None,
        assumptions,
        &mut ExecutionBudget::beside_live_state(),
    )
    .map_err(|error| {
        format!(
            "could not lower entry invariants: they stopped at {}",
            error.describe()
        )
    })?;
    if let Some(obligation) = obligations.first() {
        return Err(format!(
            "missing invariant fact{}",
            obligation
                .context()
                .map(|context| format!(" ({context})"))
                .unwrap_or_default()
        ));
    }
    Ok(())
}

/// One arm's join abstraction and the execution counter the joined execution
/// continues from.
///
/// A join invents identities, exactly as a loop head or an opaque call does,
/// and it draws them from the same counter those do. This pair is what makes
/// the counter impossible to drop: a caller cannot take the abstract state
/// without taking the counter that goes with it, so a later loop-head havoc,
/// opaque call result, heap allocation or resource model field cannot be
/// handed an identity a live join-abstracted value already carries.
/// `next_kernel_variable` is the execution-relative counter the arms carry,
/// and every identity this abstraction issued lies below it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StateJoinAbstraction {
    pub state: ExecutionState,
    pub next_kernel_variable: u64,
    memory_requirements: Vec<Proposition>,
}

impl StateJoinAbstraction {
    /// The abstraction may be published only if every changed span separates
    /// from the live borrow footprint at the split, before any arm runs.
    pub(crate) fn unproved_memory_separation(
        &self,
        entry_facts: &crate::kernel::proof::PureFactStore,
    ) -> Option<&Proposition> {
        self.memory_requirements
            .iter()
            .find(|goal| !crate::kernel::proof::checked_branch_fact_is_available(entry_facts, goal))
    }
}

/// Builds a branch-independent symbolic state for a proof join.
///
/// Locals that still equal a stable function-entry value retain that identity.
/// Other scalar and pointer locals become fresh symbolic values, and non-stack
/// memory is forgotten. Exported facts and resources constrain those values at
/// the abstract frontier.
pub fn abstract_execution_state_for_join(
    state: &ExecutionState,
    stable_entry_locals: &BTreeMap<BindingName, ProgramValue>,
    next_kernel_variable: u64,
) -> Result<StateJoinAbstraction, String> {
    abstract_execution_state_for_join_across(
        state,
        std::slice::from_ref(&state),
        stable_entry_locals,
        next_kernel_variable,
    )
}

/// Builds one arm's abstract join state using a variable reservation shared
/// by every sibling arm. Nested joins may already contain abstract variables;
/// reserving the union makes the next abstraction fresh and deterministic
/// across all siblings rather than dependent on which arm was abstracted
/// earlier.
///
/// `next_kernel_variable` must be the same for every sibling -- the maximum
/// of the arms' counters -- because each arm's abstraction is computed
/// separately and then compared for equality. Counting from the maximum is
/// what makes the result independent of which arm allocated more, and what
/// keeps the join off identities an arm has already spent.
pub fn abstract_execution_state_for_join_across(
    state: &ExecutionState,
    sibling_states: &[&ExecutionState],
    stable_entry_locals: &BTreeMap<BindingName, ProgramValue>,
    next_kernel_variable: u64,
) -> Result<StateJoinAbstraction, String> {
    abstract_execution_state_for_join_across_with_policy(
        state,
        sibling_states,
        JoinLocals::Stable(stable_entry_locals),
        next_kernel_variable,
    )
}

/// Builds a branch-interface abstraction while retaining non-scalar memory
/// when every checked arm has the exact same such memory. This avoids
/// forgetting an already-established immutable frame merely because scalar
/// locals differ across the branch. Any disagreement uses the ordinary
/// conservative memory havoc.
///
/// A local keeps its value exactly when every arm holds it alike. Only the
/// locals on which the arms differ are visited, found from the structure the
/// arms' frames share, so a join costs the arms' changes rather than every
/// local and parameter in scope.
pub fn abstract_execution_state_for_interface_join_across(
    state: &ExecutionState,
    sibling_states: &[&ExecutionState],
    next_kernel_variable: u64,
) -> Result<StateJoinAbstraction, String> {
    abstract_execution_state_for_join_across_with_policy(
        state,
        sibling_states,
        JoinLocals::ArmsAgree,
        next_kernel_variable,
    )
}

/// Which locals a join abstraction keeps: those still holding a given stable
/// value, or, at an interface join, those every arm holds alike.
#[derive(Clone, Copy)]
enum JoinLocals<'a> {
    Stable(&'a BTreeMap<BindingName, ProgramValue>),
    ArmsAgree,
}

/// The blocks an interface join keeps: the slots of the locals it visited
/// and kept, and the slot of any object local the arms hold alike, which it
/// keeps without visiting. The second is read from the slot index.
struct InterfacePreservedBlocks<'a> {
    locals: &'a LocalEnvironment,
    differing: &'a BTreeSet<&'a BindingName>,
    visited: &'a BTreeSet<AddressBase>,
}

impl crate::kernel::primitives::BlockMembership for InterfacePreservedBlocks<'_> {
    fn contains_block(&self, block: &AddressBase) -> bool {
        self.visited.contains(block)
            || self
                .locals
                .names_with_slot_in(block)
                .into_iter()
                .any(|name| {
                    !self.differing.contains(name)
                        && matches!(
                            self.locals.bindings.get(name),
                            Some(LocalBinding::Object { .. })
                        )
                })
    }
}

fn abstract_execution_state_for_join_across_with_policy(
    state: &ExecutionState,
    sibling_states: &[&ExecutionState],
    join_locals: JoinLocals<'_>,
    next_kernel_variable: u64,
) -> Result<StateJoinAbstraction, String> {
    let preserve_exact_common_memory = matches!(join_locals, JoinLocals::ArmsAgree);
    // A join may retain one exact persistent ledger root, but it cannot pick
    // one arm's borrow history when siblings have advanced independently. The
    // ledger equality is an opaque state-identity comparison; no borrow map or
    // history is traversed here.
    if sibling_states
        .iter()
        .any(|sibling| sibling.aggregate_destination != state.aggregate_destination)
    {
        return Err("construction destination differs across branch join".to_string());
    }
    if sibling_states
        .iter()
        .any(|sibling| sibling.borrow_ledger != state.borrow_ledger)
    {
        return Err("stable-view borrow state differs across branch join".to_string());
    }
    if sibling_states
        .iter()
        .any(|sibling| sibling.borrow_participant != state.borrow_participant)
    {
        return Err("stable-view borrow participant differs across branch join".to_string());
    }
    if sibling_states
        .iter()
        .any(|sibling| sibling.borrow_bindings != state.borrow_bindings)
    {
        return Err("stable-view occurrence bindings differ across branch join".to_string());
    }
    // An interface join takes its fresh identities from the execution's one
    // counter, continued from the highest mark any arm reached. That counter
    // only moves forward and nothing else issues identities in its range,
    // so every identity an arm holds from it lies below the mark and the
    // join cannot re-issue one. The join therefore reads no arm state to
    // find the names in use. The loop-head abstraction below is left as it
    // was: whether its callers' marks cover the states it abstracts was not
    // examined when the join stopped scanning.
    let mut existing_variables = BTreeSet::new();
    if !preserve_exact_common_memory {
        for sibling in sibling_states {
            crate::instrumentation::record_deterministic_work(
                sibling.locals.bindings.len()
                    + sibling.memory.blocks.len()
                    + sibling.memory.cells.len()
                    + sibling.memory.union_cells.len()
                    + sibling.memory.forgotten.ended_local_blocks.len()
                    + sibling.resources().facts().len(),
            );
            // The state scan reserves the `havoc:N` and `call-havoc:N` marker
            // blocks' identities itself; the join no longer harvests block names.
            collect_execution_state_bitvector_variables(sibling, &mut existing_variables);
        }
        if let JoinLocals::Stable(stable_entry_locals) = join_locals {
            for value in stable_entry_locals.values() {
                crate::instrumentation::record_deterministic_work(1);
                collect_program_value_bitvector_variables(value, &mut existing_variables);
            }
        }
    }
    // The interface join takes that rule on trust. Debug builds, which
    // the gate runs, check it: no identity an arm holds from the execution's
    // range may lie at or above the mark the join counts from. A stale mark
    // is how a join hands a fresh local an identity already in use; a loop
    // tactic that did not move its proof's counter past its rule's
    // identities did exactly that.
    #[cfg(debug_assertions)]
    if preserve_exact_common_memory {
        crate::instrumentation::uncharged_debug_check(|| {
            let mut held = BTreeSet::new();
            for sibling in sibling_states {
                collect_execution_state_bitvector_variables(sibling, &mut held);
            }
            if let JoinLocals::Stable(stable_entry_locals) = join_locals {
                for value in stable_entry_locals.values() {
                    collect_program_value_bitvector_variables(value, &mut held);
                }
            }
            let mark = ExecutionBudget::KERNEL_VARIABLE_BASE + next_kernel_variable;
            let stale = held
                .iter()
                .filter(|variable| {
                    variable.0 >= mark && variable.0 < ExecutionBudget::KERNEL_VARIABLE_CEILING
                })
                .collect::<Vec<_>>();
            assert!(
                stale.is_empty(),
                "an interface join counts fresh identities from {mark}, but its arms already hold {stale:?}"
            );
        });
    }
    // The abstraction allocates through an execution budget, which is the one
    // counter every kernel allocation under this execution uses. Starting it
    // at the arms' counter rather than at the range's base keeps a join off
    // identities an arm already spent; returning the mark below keeps the
    // continuation off the identities this join spends.
    let mut budget = ExecutionBudget::continuing_from(next_kernel_variable);
    let mut variables = KernelVariableGenerator::fresh_for_execution(existing_variables);
    let mut abstract_state = state.clone();
    // A nested arm may already carry a memory-havoc marker from an inner
    // join. Retain the union on every sibling so the enclosing abstraction is
    // deterministic without discarding any memory-distinction history.
    // Only a block on which a sibling differs from this state can be one
    // this state lacks, so the siblings' blocks are not walked.
    for sibling in sibling_states {
        let differing = abstract_state
            .memory
            .blocks
            .diff(&sibling.memory.blocks)
            .filter_map(|change| match change {
                crate::kernel::primitives::HashedOrdMapChange::Removed(_) => None,
                crate::kernel::primitives::HashedOrdMapChange::Added(block)
                | crate::kernel::primitives::HashedOrdMapChange::Changed(block) => {
                    block.is_havoc_block().then(|| block.clone())
                }
            })
            .collect::<Vec<_>>();
        for block in differing {
            let contents = sibling
                .memory
                .blocks
                .get(&block)
                .expect("a differing block is held");
            std::sync::Arc::make_mut(&mut abstract_state.memory.blocks)
                .insert(block, contents.clone());
        }
    }
    abstract_state.memory.record_diagnostic_transform(
        "retain sibling havoc markers",
        std::iter::once(state.memory.clone())
            .chain(sibling_states.iter().map(|state| state.memory.clone()))
            .collect(),
        Vec::new(),
    );
    abstract_state.next_local_lifetime = sibling_states
        .iter()
        .map(|sibling| sibling.next_local_lifetime)
        .max()
        .unwrap_or(state.next_local_lifetime);
    let mut abstract_objects = Vec::new();
    let mut preserved_blocks = BTreeSet::new();

    // A local that some arm of an interface join left uninitialized is
    // uninitialized after the join: the path through that arm never gave it
    // a value, so reading it afterwards is as undefined as it was there. An
    // arm that did initialize it must not keep a value for it, or the two
    // arms' abstractions differ and the arms cannot be joined at all.
    //
    // At an interface join the locals visited are those some arm binds
    // differently. A local every arm binds alike keeps its binding and its
    // slot unvisited: it is stable, and no arm left it uninitialized unless
    // this one did too.
    let differing = match join_locals {
        JoinLocals::Stable(_) => BTreeSet::new(),
        JoinLocals::ArmsAgree => {
            let mut differing = BTreeSet::new();
            if let Some(first) = sibling_states.first() {
                differing.extend(state.locals.differing_names(&first.locals));
                for sibling in &sibling_states[1..] {
                    differing.extend(first.locals.differing_names(&sibling.locals));
                }
            }
            differing
        }
    };
    let mut uninitialized_in_an_arm = BTreeSet::new();
    if preserve_exact_common_memory {
        for name in &differing {
            crate::instrumentation::record_deterministic_work(1);
            if sibling_states.iter().any(|sibling| {
                matches!(
                    sibling.locals.bindings.get(*name),
                    Some(LocalBinding::UninitializedObject { .. })
                )
            }) {
                uninitialized_in_an_arm.insert(*name);
            }
        }
    }
    let mut left_uninitialized = Vec::new();

    let visited: Box<dyn Iterator<Item = (&BindingName, &LocalBinding)>> = match join_locals {
        JoinLocals::Stable(_) => Box::new(state.locals.bindings.iter()),
        JoinLocals::ArmsAgree => Box::new(
            differing
                .iter()
                .filter_map(|name| state.locals.bindings.get_key_value(*name)),
        ),
    };
    for (name, binding) in visited {
        crate::instrumentation::record_deterministic_work(1);
        if let LocalBinding::Object {
            program_type,
            slot,
            volatile,
            pointee_volatile,
            constant,
            pointee_constant,
            ..
        } = binding
            && uninitialized_in_an_arm.contains(name)
        {
            // Its block is not preserved, so the memory join below drops
            // the value this arm stored and its initialization record.
            left_uninitialized.push((
                name.clone(),
                *program_type,
                slot.clone(),
                *volatile,
                *pointee_volatile,
                *constant,
                *pointee_constant,
            ));
            continue;
        }
        let LocalBinding::Object {
            value,
            program_type,
            slot,
            ..
        } = binding
        else {
            continue;
        };
        let stable = match join_locals {
            JoinLocals::Stable(stable_entry_locals) => stable_entry_locals
                .get(name)
                .is_some_and(|held| value.matches_native(held)),
            JoinLocals::ArmsAgree => sibling_states
                .iter()
                .all(|sibling| sibling.locals.get(name) == Some(value)),
        };
        let abstract_value = if stable {
            value.clone()
        } else {
            match program_type {
                ProgramType::Void => continue,
                // A `Bool` the arms disagree on is a fresh `Bool` binder.
                ProgramType::Bool => ProgramValue::of_bool(OldConditionTerm::Variable(
                    join_variable(&mut variables, &mut budget)?,
                )),
                ProgramType::Int8 => int8(OldMachineTerm::Variable(join_variable(
                    &mut variables,
                    &mut budget,
                )?)),
                ProgramType::Int16 => int16(OldMachineTerm::Variable(join_variable(
                    &mut variables,
                    &mut budget,
                )?)),
                ProgramType::Int32 => int32(OldMachineTerm::Variable(join_variable(
                    &mut variables,
                    &mut budget,
                )?)),
                ProgramType::Int64 => ProgramValue::Int64(OldMachineTerm::Variable(join_variable(
                    &mut variables,
                    &mut budget,
                )?)),
                ProgramType::UInt32 => uint32(OldMachineTerm::Variable(join_variable(
                    &mut variables,
                    &mut budget,
                )?)),
                ProgramType::UInt8 => uint8(OldMachineTerm::Variable(join_variable(
                    &mut variables,
                    &mut budget,
                )?)),
                ProgramType::UInt16 => uint16(OldMachineTerm::Variable(join_variable(
                    &mut variables,
                    &mut budget,
                )?)),
                ProgramType::UInt64 => ProgramValue::UInt64(OldMachineTerm::Variable(
                    join_variable(&mut variables, &mut budget)?,
                )),
                ProgramType::Float32 => ProgramValue::Float32(OldMachineTerm::Variable(
                    join_variable(&mut variables, &mut budget)?,
                )),
                ProgramType::Float64 => ProgramValue::Float64(OldMachineTerm::Variable(
                    join_variable(&mut variables, &mut budget)?,
                )),
                ProgramType::FunctionPointer(_) => ProgramValue::typed_pointer(
                    Address::symbolic_function(join_variable(&mut variables, &mut budget)?),
                    *program_type,
                ),
                ProgramType::Int8Array(_) => {
                    unreachable!("array objects use LocalBinding::ArrayObject")
                }
                ProgramType::Int32Array(_)
                | ProgramType::UInt8Array(_)
                | ProgramType::Int16Array(_)
                | ProgramType::UInt16Array(_)
                | ProgramType::UInt32Array(_)
                | ProgramType::Int128Array(_)
                | ProgramType::Int64Array(_)
                | ProgramType::UInt128Array(_)
                | ProgramType::UInt64Array(_)
                | ProgramType::Float32Array(_)
                | ProgramType::Float64Array(_) => {
                    unreachable!("array objects use LocalBinding::ArrayObject")
                }
                // A slice the arms disagree on is a fresh slice binder, its
                // data pointer and count named by one variable.
                ProgramType::SlicePointer(_) => crate::kernel::symbolic_call_result(
                    *program_type,
                    join_variable(&mut variables, &mut budget)?,
                ),
                _ => ProgramValue::typed_pointer(
                    Address::symbolic(join_variable(&mut variables, &mut budget)?),
                    *program_type,
                ),
            }
            .into()
        };
        preserved_blocks.insert(slot.base.clone());
        abstract_objects.push((name.clone(), abstract_value, *program_type));
    }

    let interface_preserved = InterfacePreservedBlocks {
        locals: &state.locals,
        differing: &differing,
        visited: &preserved_blocks,
    };
    let preserved: &dyn crate::kernel::primitives::BlockMembership = match join_locals {
        JoinLocals::Stable(_) => &preserved_blocks,
        JoinLocals::ArmsAgree => &interface_preserved,
    };

    // The arms' memories are one memory when they differ only inside the
    // blocks the join preserves anyway. The differences are read off the
    // structure the states share, so equal memories cost nothing and
    // unequal ones cost what differs.
    let common_memory = preserve_exact_common_memory
        && sibling_states
            .iter()
            .all(|sibling| state.memory.differs_only_within(&sibling.memory, preserved));
    let mut memory_requirements = BTreeSet::new();
    if !common_memory {
        if let Some(ledger) = abstract_state.borrow_ledger() {
            for sibling in sibling_states {
                branch_memory_delta_requirements(
                    &abstract_state.memory,
                    &sibling.memory,
                    ledger,
                    &mut memory_requirements,
                )?;
            }
        }
        if preserve_exact_common_memory {
            let sibling_memories = sibling_states
                .iter()
                .map(|sibling| &sibling.memory)
                .collect::<Vec<_>>();
            // Record the checked arm, not the scratch memory whose marker
            // union above differs depending on which arm is being abstracted.
            // The join itself already unions every incoming arm's blocks.
            let memory = state
                .memory
                .clone()
                .with_interface_memory_havoc_preserving_borrows(
                    join_variable(&mut variables, &mut budget)?,
                    preserved,
                    &sibling_memories,
                    abstract_state.borrow_ledger(),
                )?;
            abstract_state.set_memory(memory);
        } else {
            let memory = abstract_state
                .memory
                .clone()
                .with_loop_memory_havoc_preserving_borrows(
                    join_variable(&mut variables, &mut budget)?,
                    preserved,
                    None,
                    abstract_state.borrow_ledger(),
                );
            abstract_state.set_memory(memory);
        }
    }
    for (name, value, program_type) in abstract_objects {
        sync_retained_stack_local(&mut abstract_state, &name, &value);
        abstract_state
            .locals
            .set_retained_typed_with_all_qualifiers(
                name,
                value,
                program_type,
                false,
                false,
                false,
                false,
            );
    }
    for (name, program_type, slot, volatile, pointee_volatile, constant, pointee_constant) in
        left_uninitialized
    {
        abstract_state.locals.set_uninitialized_with_all_qualifiers(
            name,
            program_type,
            slot,
            volatile,
            pointee_volatile,
            constant,
            pointee_constant,
        );
    }
    // Drop the resource context through the rebasing setter, not by writing
    // the field. The occurrence-to-borrow sidecar is keyed by the occurrences of
    // the context being discarded, so a direct assignment would leave the
    // abstraction advertising borrow dependencies for occurrences it no longer
    // has -- and would disagree with every other path that reaches an empty
    // context through `with_resource_context`. The ledger and participant are
    // untouched: the arms' authority survives the abstraction, only the
    // per-occurrence bookkeeping of the discarded context goes away.
    // Arms whose creation ledgers diverged hold separately minted names for
    // the same records, such as the anchors of a local both declare. Every
    // arm then takes the first sibling's ledger, so the join compares one
    // ledger, and a ledger that records a different state is kept.
    if let (Some(own), Some(first)) = (
        abstract_state.population_effects.creation.as_ref(),
        sibling_states
            .first()
            .and_then(|sibling| sibling.population_effects.creation.as_ref()),
    ) && own != first
        && (own.records_same_state_as(first) || own.records_same_state_up_to_fresh_anchors(first))
    {
        std::sync::Arc::make_mut(&mut abstract_state.population_effects).creation =
            Some(first.clone());
    }
    Ok(StateJoinAbstraction {
        // Structural empty join shape; live successor resources are supplied
        // separately by the checked interface, not inserted into this placeholder.
        state: abstract_state.with_resource_context(ResourceContext::new()),
        next_kernel_variable: budget.next_kernel_variable(),
        memory_requirements: memory_requirements.into_iter().collect(),
    })
}

/// One identity for a join abstraction, from the execution's single counter.
fn join_variable(
    variables: &mut KernelVariableGenerator,
    budget: &mut ExecutionBudget,
) -> Result<Variable, String> {
    variables.next_in(budget).map_err(|limit| {
        format!(
            "the branch join has no fresh identity left: it stopped at {}",
            limit.describe()
        )
    })
}

fn branch_memory_delta_requirements(
    base: &SymbolicMemory,
    sibling: &SymbolicMemory,
    ledger: &crate::kernel::borrows::BorrowLedger,
    requirements: &mut BTreeSet<Proposition>,
) -> Result<(), String> {
    if !ledger.has_active_memory_borrows() {
        return Ok(());
    }
    if base.blocks != sibling.blocks
        || base.heap != sibling.heap
        || base.forgotten.ended_local_blocks != sibling.forgotten.ended_local_blocks
    {
        return Err("branch memory join has an unsupported allocation or block delta while a stable-view borrow is active".to_string());
    }
    for pointer in base.differing_cell_pointers(sibling) {
        crate::instrumentation::record_deterministic_work(1);
        let byte_width = base
            .join_cell_width(&pointer)
            .max(sibling.join_cell_width(&pointer));
        if byte_width == 0 {
            return Err(
                "branch memory join has an unknown changed cell width while a stable-view borrow is active".to_string(),
            );
        }
        let range = MemoryRange::new_with_element_width(
            pointer,
            OldMachineTerm::constant(0),
            OldMachineTerm::constant(byte_width),
            1,
        );
        requirements.extend(ledger.memory_access_requirement(&range));
    }
    Ok(())
}

/// Read only the expression's existing C type metadata; no load or access
/// check is performed. Surface branch spelling uses this to keep native
/// address comparisons separate from contract pointer-value equalities.
pub(crate) fn program_expression_has_pointer_type(
    state: &ExecutionState,
    expression: &ProgramExpression,
) -> bool {
    super::eval::program_expression_pointee_type(state, expression).is_some()
}

/// Whether `expression` is a C `bool` value this state can type: a `bool`
/// constant, or a read of a `bool` object. A branch on it is the `Bool`
/// claim on the value itself (Stage 5), not its comparison with an integer.
pub(crate) fn program_expression_has_bool_type(
    state: &ExecutionState,
    expression: &ProgramExpression,
) -> bool {
    match expression {
        ProgramExpression::Value(value) => value.program_type() == ProgramType::Bool,
        // A variant test is a claim on the enum value, never a number.
        ProgramExpression::EnumIs { .. } => true,
        ProgramExpression::StepResult { step, .. } => state
            .step_result(*step)
            .is_some_and(|value| value.program_type() == ProgramType::Bool),
        expression => {
            super::eval::program_expression_lvalue_type(state, expression)
                == Some(ProgramType::Bool)
        }
    }
}

/// The values a composite definition binds its existential witnesses to for
/// `composite` under `memory` and `assumptions`, in declaration order. This
/// is the same deterministic choice body instantiation makes, so a surface
/// substitution of witness names agrees with the kernel's own expansion.
pub fn composite_resource_witness_values(
    composite: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    memory: &SymbolicMemory,
    resources: &ResourceContext,
    assumptions: &PureFactContext,
) -> Option<Vec<ProgramValue>> {
    let Resource::Composite { name, arguments } = composite.resource() else {
        return None;
    };
    let definition = definitions
        .iter()
        .find(|definition| definition.name() == name)?;
    if definition.parameters().len() != arguments.len() {
        return None;
    }
    let mut state = ExecutionState::new().with_memory(memory.clone());
    for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
        let argument = argument.as_program_value()?;
        state.locals.set_typed(
            parameter.binding_name().clone(),
            argument.clone(),
            parameter.program_type(),
        );
    }
    let assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    super::functions::bind_composite_witnesses_with_held(
        definition,
        &(arguments).native_values(),
        &mut state,
        resources,
        &assumptions,
    )
}

pub fn program_assign(
    name: impl Into<BindingName>,
    expression: ProgramExpression,
) -> ProgramStatement {
    ProgramStatement::Assign {
        name: name.into(),
        expression,
        source: Default::default(),
        prior_result: None,
    }
}

/// Build a value-producing call and the expression naming its result.
/// The caller allocates `call` uniquely within the function's source layout.
pub fn program_call_value(
    call: u32,
    function_name: impl Into<String>,
    arguments: Vec<ProgramExpression>,
) -> (ProgramStatement, ProgramExpression) {
    let function_name = function_name.into();
    let result = ProgramExpression::StepResult {
        step: call,
        origin: StepOrigin::Call(function_name.clone()),
        ends: true,
    };
    (
        ProgramStatement::CallResult {
            aggregate_layout: None,
            call,
            function_name,
            arguments,
            result_type: None,
            result_aggregate_layout: None,
            result_pointee_constant: false,
            dispatch: CallDispatch::Direct,
            callee: None,
        },
        result,
    )
}

pub(crate) fn program_create_closure(
    step: u32,
    closure: String,
    captures: Vec<ProgramExpression>,
    source: Option<ClosureSite>,
) -> (ProgramStatement, ProgramExpression) {
    (
        ProgramStatement::CreateClosure {
            step,
            closure,
            captures,
            source,
        },
        ProgramExpression::StepResult {
            step,
            origin: StepOrigin::Value("closure creation"),
            ends: true,
        },
    )
}

/// Two explicit operations: a call retaining its value, then a scalar assignment.
#[cfg(test)]
pub fn program_call_then_assign(
    call: u32,
    target: impl Into<BindingName>,
    function_name: impl Into<String>,
    arguments: Vec<ProgramExpression>,
) -> ProgramStatement {
    let (call, value) = program_call_value(call, function_name, arguments);
    program_seq(call, program_assign(target, value))
}

/// A reallocation result followed by its destination assignment.
#[cfg(test)]
pub fn program_reallocate_then_assign(
    call: u32,
    target: impl Into<BindingName>,
    result_type: ProgramType,
    arguments: Vec<ProgramExpression>,
) -> ProgramStatement {
    let (mut operation, value) = program_call_value(call, "realloc", arguments);
    if let ProgramStatement::CallResult {
        result_type: expected,
        ..
    } = &mut operation
    {
        *expected = Some(result_type);
    }
    program_seq(operation, program_assign(target, value))
}

pub fn program_call_construct(
    target: impl Into<BindingName>,
    function_name: impl Into<String>,
    arguments: Vec<ProgramExpression>,
) -> ProgramStatement {
    ProgramStatement::CallConstruct {
        target: target.into(),
        function_name: function_name.into(),
        arguments,
    }
}

pub fn program_call(
    function_name: impl Into<String>,
    arguments: Vec<ProgramExpression>,
) -> ProgramStatement {
    ProgramStatement::Call {
        function_name: function_name.into(),
        arguments,
        callee: None,
        dispatch: crate::kernel::CallDispatch::Direct,
        reference_binding: None,
    }
}

#[cfg(test)]
pub fn program_heap_allocate(target: impl Into<BindingName>, bytes: u32) -> ProgramStatement {
    program_heap_allocate_sized(
        target,
        crate::kernel::program_expression::int32_literal(bytes),
    )
}

#[cfg(test)]
pub fn program_heap_allocate_sized(
    target: impl Into<BindingName>,
    bytes: ProgramExpression,
) -> ProgramStatement {
    program_heap_allocate_sized_with_zeroed(target, bytes, false)
}

#[cfg(test)]
pub fn program_heap_allocate_sized_with_zeroed(
    target: impl Into<BindingName>,
    bytes: ProgramExpression,
    zeroed: bool,
) -> ProgramStatement {
    ProgramStatement::HeapAllocate {
        target: target.into(),
        bytes,
        zeroed,
        object_type: None,
        ends_program_on_failure: false,
    }
}

pub fn program_heap_free(pointer: ProgramExpression) -> ProgramStatement {
    ProgramStatement::HeapFree { pointer }
}

pub fn program_declare(
    name: impl Into<BindingName>,
    program_type: ProgramType,
) -> ProgramStatement {
    program_declare_volatile(name, program_type, false)
}

pub fn program_declare_volatile(
    name: impl Into<BindingName>,
    program_type: ProgramType,
    volatile: bool,
) -> ProgramStatement {
    program_declare_qualified(name, program_type, volatile, false)
}

pub fn program_declare_qualified(
    name: impl Into<BindingName>,
    program_type: ProgramType,
    volatile: bool,
    pointee_volatile: bool,
) -> ProgramStatement {
    program_declare_with_all_qualifiers(
        name,
        program_type,
        volatile,
        pointee_volatile,
        false,
        false,
    )
}

pub fn program_declare_with_all_qualifiers(
    name: impl Into<BindingName>,
    program_type: ProgramType,
    volatile: bool,
    pointee_volatile: bool,
    constant: bool,
    pointee_constant: bool,
) -> ProgramStatement {
    ProgramStatement::Declare {
        name: Into::<BindingName>::into(name).into(),
        program_type,
        volatile,
        pointee_volatile,
        constant,
        pointee_constant,
        initializer: None,
        zero_fill: None,
        declared_class: None,
    }
}

/// [`program_declare_with_all_qualifiers`], zero-filling the object first when
/// `zero_fill` says how: an automatic array declared with an initializer,
/// whose written elements follow as ordinary stores ([`ZeroFill`]).
pub fn program_declare_with_zero_fill(
    name: impl Into<BindingName>,
    program_type: ProgramType,
    volatile: bool,
    pointee_volatile: bool,
    constant: bool,
    pointee_constant: bool,
    zero_fill: Option<ZeroFill>,
) -> ProgramStatement {
    ProgramStatement::Declare {
        name: Into::<BindingName>::into(name).into(),
        program_type,
        volatile,
        pointee_volatile,
        constant,
        pointee_constant,
        initializer: None,
        zero_fill,
        declared_class: None,
    }
}

/// Allocate a fresh scalar and initialize it once. Ordinary stores remain
/// subject to the object's const qualification after this transition.
pub fn program_declare_initialized(
    name: impl Into<BindingName>,
    program_type: ProgramType,
    expression: ProgramExpression,
    volatile: bool,
    pointee_volatile: bool,
    constant: bool,
    pointee_constant: bool,
) -> ProgramStatement {
    ProgramStatement::Declare {
        name: Into::<BindingName>::into(name).into(),
        program_type,
        volatile,
        pointee_volatile,
        constant,
        pointee_constant,
        zero_fill: None,
        declared_class: None,
        initializer: Some(expression),
    }
}

pub fn program_declare_aggregate(
    name: impl Into<BindingName>,
    layout: AggregateLayout,
) -> ProgramStatement {
    ProgramStatement::DeclareAggregate {
        name: Into::<BindingName>::into(name).into(),
        layout,
        kind: AggregateDeclarationKind::Local,
        declared_class: None,
    }
}

/// [`program_declare_aggregate`] of an object whose class is `declared_class`.
pub(crate) fn program_declare_classed_aggregate(
    name: impl Into<BindingName>,
    layout: AggregateLayout,
    declared_class: Option<crate::kernel::effective_type::CAccessClass>,
) -> ProgramStatement {
    ProgramStatement::DeclareAggregate {
        name: Into::<BindingName>::into(name).into(),
        layout,
        kind: AggregateDeclarationKind::Local,
        declared_class,
    }
}

pub fn program_begin_aggregate_construction(
    name: impl Into<BindingName>,
    layout: AggregateLayout,
) -> ProgramStatement {
    ProgramStatement::DeclareAggregate {
        name: Into::<BindingName>::into(name).into(),
        layout,
        kind: AggregateDeclarationKind::Constructor,
        declared_class: None,
    }
}

/// Allocates fresh owned aggregate storage without initializing its fields.
/// This grants authority over the allocation, not over any future pointees.
pub fn program_allocate_aggregate_destination(
    name: impl Into<BindingName>,
    layout: AggregateLayout,
) -> ProgramStatement {
    ProgramStatement::DeclareAggregate {
        name: Into::<BindingName>::into(name).into(),
        layout,
        kind: AggregateDeclarationKind::ConstructionDestination,
        declared_class: None,
    }
}

pub fn program_copy_aggregate(
    target: ProgramExpression,
    source: ProgramExpression,
    layout: AggregateLayout,
) -> ProgramStatement {
    ProgramStatement::CopyAggregate {
        target,
        source,
        layout,
    }
}

/// Retire automatic storage at a source-language lifetime boundary. Frontends
/// supply the objects whose lifetimes end; this grants no cleanup authority.
pub fn program_end_automatic_lifetimes(names: Vec<BindingName>) -> ProgramStatement {
    ProgramStatement::EndAutomaticLifetimes {
        names,
        steps: Vec::new(),
    }
}

pub fn program_initialize_scalar_array(
    target: ProgramExpression,
    source: ProgramExpression,
    element_type: ProgramType,
    count: u32,
    copy: bool,
) -> ProgramStatement {
    ProgramStatement::InitializeScalarArray {
        target,
        source,
        element_type,
        count,
        copy,
        fresh: true,
    }
}

/// Write an embedded scalar-array region without changing adjacent bytes.
/// This does not grant storage, initialization or memory authority.
pub fn program_write_scalar_array_region(
    target: ProgramExpression,
    source: ProgramExpression,
    element_type: ProgramType,
    count: u32,
    copy: bool,
) -> ProgramStatement {
    ProgramStatement::InitializeScalarArray {
        target,
        source,
        element_type,
        count,
        copy,
        fresh: false,
    }
}

pub fn program_assert(condition: ProgramExpression) -> ProgramStatement {
    ProgramStatement::Assert {
        condition,
        label: None,
    }
}

pub fn program_labeled_assert(
    condition: ProgramExpression,
    label: impl Into<String>,
) -> ProgramStatement {
    ProgramStatement::Assert {
        condition,
        label: Some(label.into()),
    }
}

pub fn program_seq(first: ProgramStatement, second: ProgramStatement) -> ProgramStatement {
    ProgramStatement::seq(Arc::new(first), Arc::new(second))
}

pub fn program_skip() -> ProgramStatement {
    ProgramStatement::Skip
}

pub fn program_break() -> ProgramStatement {
    ProgramStatement::Break
}

pub fn program_continue() -> ProgramStatement {
    ProgramStatement::Continue
}

#[cfg(test)]
pub(crate) fn program_goto(target: ControlTargetId) -> ProgramStatement {
    ProgramStatement::Goto {
        target,
        exited_locals: Default::default(),
    }
}

pub fn program_switch(expression: ProgramExpression, cases: Vec<SwitchCase>) -> ProgramStatement {
    ProgramStatement::Switch { expression, cases }
}

pub fn program_return(expression: ProgramExpression) -> ProgramStatement {
    ProgramStatement::Return(expression)
}

pub fn program_void_value() -> ProgramExpression {
    ProgramExpression::Value(ProgramValue::Void)
}

pub fn program_store(pointer: ProgramExpression, value: ProgramExpression) -> ProgramStatement {
    ProgramStatement::Store { pointer, value }
}

pub fn program_typed_store(
    pointer: ProgramExpression,
    value: ProgramExpression,
    value_type: ProgramType,
) -> ProgramStatement {
    program_qualified_typed_store(pointer, value, value_type, None, false, false)
}

/// A typed store whose lvalue has `access_class` when `value_type` erases
/// it, as [`crate::kernel::program_expression::classed_load`] does for a load.
pub(crate) fn program_qualified_typed_store(
    pointer: ProgramExpression,
    value: ProgramExpression,
    value_type: ProgramType,
    access_class: Option<crate::kernel::effective_type::CAccessClass>,
    pointee_constant: bool,
    volatile: bool,
) -> ProgramStatement {
    ProgramStatement::TypedStore {
        pointer,
        value,
        value_type,
        access_class,
        pointee_constant,
        volatile,
        source: Default::default(),
    }
}

pub fn program_update(
    target: ProgramExpression,
    operator: UpdateOperator,
    operand: ProgramExpression,
) -> ProgramStatement {
    ProgramStatement::Update {
        target,
        operator,
        operand,
    }
}

pub fn program_if(
    condition: ProgramExpression,
    then_branch: ProgramStatement,
    else_branch: ProgramStatement,
) -> ProgramStatement {
    ProgramStatement::If {
        condition,
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
    }
}

/// Handle a checked int32 exceptional outcome, binding its payload only on
/// the caught path. Normal and other terminal outcomes bypass the handler.
pub fn program_try_catch_int32(
    try_body: ProgramStatement,
    binding: impl Into<BindingName>,
    handler: ProgramStatement,
) -> ProgramStatement {
    ProgramStatement::TryCatchInt32 {
        try_body: Box::new(try_body),
        binding: binding.into(),
        handler: Box::new(handler),
    }
}

/// The statements an int32 exceptional exit from an
/// [`ProgramStatement::UnwindCleanup`] runs: its cleanup, then the same
/// exception continuing with `payload`. Execution, the proof cursor, and
/// the source layout all step this one shape, so the point where the
/// exception continues is a statement of its own.
pub fn program_unwind_continuation(
    cleanup: &ProgramStatement,
    payload: ProgramExpression,
) -> ProgramStatement {
    program_seq(cleanup.clone(), ProgramStatement::Throw(payload))
}

/// `body` with the cleanup an int32 exceptional exit from it runs before
/// propagating ([`ProgramStatement::UnwindCleanup`]).
pub fn program_unwind_cleanup(
    body: ProgramStatement,
    cleanup: ProgramStatement,
) -> ProgramStatement {
    ProgramStatement::UnwindCleanup {
        body: Box::new(body),
        cleanup: Box::new(cleanup),
    }
}

pub fn program_while(
    condition: ProgramExpression,
    invariant: Vec<Proposition>,
    body: ProgramStatement,
) -> ProgramStatement {
    program_while_with_invariant_and_effect_checks(
        condition,
        invariant,
        Vec::new(),
        Vec::new(),
        body,
    )
}

#[cfg(test)]
pub fn program_while_with_invariant_checks(
    condition: ProgramExpression,
    invariant: Vec<Proposition>,
    invariant_checks: Vec<LoopInvariantCheck>,
    body: ProgramStatement,
) -> ProgramStatement {
    program_while_with_invariant_and_effect_checks(
        condition,
        invariant,
        invariant_checks,
        Vec::new(),
        body,
    )
}

pub fn program_while_with_invariant_and_effect_checks(
    condition: ProgramExpression,
    invariant: Vec<Proposition>,
    invariant_checks: Vec<LoopInvariantCheck>,
    effect_checks: Vec<LoopEffectCheck>,
    body: ProgramStatement,
) -> ProgramStatement {
    ProgramStatement::Loop {
        test: crate::kernel::LoopTestRegion::expression(
            condition,
            crate::kernel::LoopTestPosition::BeforeBody,
        ),
        update: None,
        invariant,
        invariant_checks,
        effect_checks,
        resource_specs: Vec::new(),
        ranking_measures: Vec::new(),
        structural_measure: None,
        backedge_target: None,
        natural_exit_target: None,
        body: Box::new(body),
    }
}

impl LoopTestRegion {
    /// A test with no preparation or temporary cleanup.
    pub fn expression(condition: ProgramExpression, position: LoopTestPosition) -> Self {
        Self {
            statement: std::sync::Arc::new(ProgramStatement::LoopTest {
                condition,
                aggregate_steps: Vec::new(),
            }),
            position,
        }
    }

    pub(crate) fn entry_phase(&self) -> crate::kernel::LoopEntryPhase {
        match self.position {
            LoopTestPosition::BeforeBody => crate::kernel::LoopEntryPhase::Test,
            LoopTestPosition::AfterBody => crate::kernel::LoopEntryPhase::Body,
        }
    }

    /// The checked entry guard has already selected a pure pre-test's body.
    pub(crate) fn preservation_phase(&self) -> crate::kernel::LoopEntryPhase {
        if self.entry_condition().is_some() {
            crate::kernel::LoopEntryPhase::Body
        } else {
            self.entry_phase()
        }
    }

    /// A decision with no source preparation or temporary cleanup. This is
    /// source-layout metadata, not a different executable loop form.
    pub(crate) fn source_condition(&self) -> Option<&ProgramExpression> {
        match self.statement.as_ref() {
            ProgramStatement::LoopTest {
                condition,
                aggregate_steps,
            } if aggregate_steps.is_empty() => Some(condition),
            _ => None,
        }
    }

    /// Code that owns source statement numbers. A pure decision is named by
    /// its loop's test position and never renumbers the body.
    pub(crate) fn source_region(&self) -> Option<&Self> {
        self.source_condition().is_none().then_some(self)
    }

    /// A preparation-free pre-test can seed a preservation proof with its
    /// checked entry guard. Every executable pass still owns its test region.
    pub(crate) fn entry_condition(&self) -> Option<&ProgramExpression> {
        (self.position == LoopTestPosition::BeforeBody)
            .then(|| self.source_condition())
            .flatten()
    }
}

/// Child source regions in executable order, without copying their statements.
pub(crate) fn program_loop_regions<'a>(
    body: &'a ProgramStatement,
    update: Option<&'a ProgramStatement>,
    test: Option<&'a LoopTestRegion>,
) -> impl Iterator<Item = &'a ProgramStatement> {
    [
        test.filter(|test| test.position == LoopTestPosition::BeforeBody)
            .map(|test| test.statement.as_ref()),
        Some(body),
        update,
        test.filter(|test| test.position == LoopTestPosition::AfterBody)
            .map(|test| test.statement.as_ref()),
    ]
    .into_iter()
    .flatten()
}

/// The source body including a loop's shared pre-test, if it has one.
pub(crate) fn program_loop_body_region(
    body: &ProgramStatement,
    test: Option<&LoopTestRegion>,
) -> ProgramStatement {
    match test {
        Some(test) if test.position == LoopTestPosition::BeforeBody => {
            ProgramStatement::seq(test.statement.clone(), std::sync::Arc::new(body.clone()))
        }
        _ => body.clone(),
    }
}

/// The destination of every continuing edge, shared independently of its
/// incoming proof state: update, then the post-test when this loop has one.
pub(crate) fn program_loop_continuation(
    update: Option<&ProgramStatement>,
    test: Option<&LoopTestRegion>,
) -> Option<std::sync::Arc<ProgramStatement>> {
    let post_test = test.filter(|test| test.position == LoopTestPosition::AfterBody);
    match (update, post_test) {
        (Some(update), Some(test)) => Some(std::sync::Arc::new(ProgramStatement::seq(
            std::sync::Arc::new(update.clone()),
            test.statement.clone(),
        ))),
        (Some(update), None) => Some(std::sync::Arc::new(update.clone())),
        (None, Some(test)) => Some(test.statement.clone()),
        (None, None) => None,
    }
}

pub(crate) fn program_loop_preservation_pass(
    body: &ProgramStatement,
    update: Option<&ProgramStatement>,
    test: &LoopTestRegion,
) -> ProgramStatement {
    let body = match test.preservation_phase() {
        crate::kernel::LoopEntryPhase::Test => program_loop_body_region(body, Some(test)),
        crate::kernel::LoopEntryPhase::Body => body.clone(),
    };
    match program_loop_continuation(update, Some(test)) {
        Some(tail) => ProgramStatement::seq(std::sync::Arc::new(body), tail),
        None => body,
    }
}

pub(crate) fn program_loop_pass(
    body: &ProgramStatement,
    update: Option<&ProgramStatement>,
    test: Option<&LoopTestRegion>,
) -> ProgramStatement {
    program_loop_pass_and_continuation(body, update, test).0
}

/// Assemble a pass and retain its shared continuation from the same source.
/// A checked entry can use this code directly as its continue destination.
pub(crate) fn program_loop_pass_and_continuation(
    body: &ProgramStatement,
    update: Option<&ProgramStatement>,
    test: Option<&LoopTestRegion>,
) -> (ProgramStatement, Option<std::sync::Arc<ProgramStatement>>) {
    let body = program_loop_body_region(body, test);
    let continuation = program_loop_continuation(update, test);
    let pass = match &continuation {
        Some(tail) => ProgramStatement::seq(std::sync::Arc::new(body), tail.clone()),
        None => body,
    };
    (pass, continuation)
}

impl ProgramStatement {
    /// Set the loop's one test region, outside the body and its scopes.
    pub fn with_loop_test(
        mut self,
        statement: ProgramStatement,
        position: LoopTestPosition,
    ) -> Self {
        if let Self::Loop { test, .. } = &mut self {
            *test = LoopTestRegion {
                statement: std::sync::Arc::new(statement),
                position,
            };
        }
        self
    }

    pub(crate) fn with_optional_loop_test(
        self,
        test: Option<ProgramStatement>,
        position: LoopTestPosition,
    ) -> Self {
        match test {
            Some(test) => self.with_loop_test(test, position),
            None => self,
        }
    }

    /// The single update region reached by fallthrough and `continue`.
    pub fn with_loop_update(mut self, step: ProgramStatement) -> Self {
        if let Self::Loop { update, .. } = &mut self {
            *update = Some(std::sync::Arc::new(step));
        }
        self
    }

    /// The pair `Seq(first, second)`: `first`, then `second`.
    pub fn seq(first: Arc<ProgramStatement>, second: Arc<ProgramStatement>) -> Self {
        Self::Seq(ProgramStatementSequence::pair(first, second))
    }

    /// Declares the resources a loop holds for itself.
    ///
    /// An empty declaration leaves the loop inheriting the enclosing resource
    /// context, which is what every loop without `owns` or `views` clauses
    /// does. A statement that is not a loop head keeps its shape: only a loop
    /// carries resource declarations.
    pub fn with_loop_resource_specs(mut self, specs: Vec<ResourceSpec>) -> Self {
        if specs.is_empty() {
            return self;
        }
        if let Self::Loop { resource_specs, .. } = &mut self {
            *resource_specs = specs;
        }
        self
    }

    /// Declares the loop's `decreases` components in source order.
    ///
    /// An empty declaration leaves the loop unranked, which is what every
    /// loop without a `decreases` clause is. The components travel with the
    /// loop head so the back-edge invariant bundle and the whole-function
    /// termination pass agree on exactly which measure was checked.
    pub fn with_loop_ranking_measures(mut self, measures: Vec<RankingComponent>) -> Self {
        if measures.is_empty() {
            return self;
        }
        if let Self::Loop {
            ranking_measures, ..
        } = &mut self
        {
            *ranking_measures = measures;
        }
        self
    }

    /// Declares the loop's structural `decreases` binder (D6).
    ///
    /// `None` leaves the loop with whatever numeric components it declared.
    /// The binder name travels with the loop head for the same reason the
    /// ranking components do: the back edge, the verified loop rule, and the
    /// whole-function termination pass read one declared clause.
    pub fn with_loop_structural_measure(mut self, measure: Option<String>) -> Self {
        if measure.is_none() {
            return self;
        }
        if let Self::Loop {
            structural_measure, ..
        } = &mut self
        {
            *structural_measure = measure;
        }
        self
    }

    /// Retains the source target of a proof-only natural cycle. The cycle
    /// wrapper is an internal loop region; its body still contains the
    /// original checked `goto` statement.
    pub fn with_backedge_target(mut self, target: ControlTargetId) -> Self {
        if let Self::Loop {
            backedge_target, ..
        } = &mut self
        {
            *backedge_target = Some(target);
        }
        self
    }

    /// Retains the explicit forward exit target of a proof-only natural cycle.
    pub fn with_natural_exit_target(mut self, target: ControlTargetId) -> Self {
        if let Self::Loop {
            natural_exit_target,
            ..
        } = &mut self
        {
            *natural_exit_target = Some(target);
        }
        self
    }
}

pub fn program_do_while(condition: ProgramExpression, body: ProgramStatement) -> ProgramStatement {
    program_do_while_with_invariant_and_effect_checks(condition, Vec::new(), Vec::new(), body)
}

pub fn program_do_while_with_invariant_and_effect_checks(
    condition: ProgramExpression,
    invariant_checks: Vec<LoopInvariantCheck>,
    effect_checks: Vec<LoopEffectCheck>,
    body: ProgramStatement,
) -> ProgramStatement {
    ProgramStatement::Loop {
        test: crate::kernel::LoopTestRegion::expression(
            condition,
            crate::kernel::LoopTestPosition::AfterBody,
        ),
        update: None,
        invariant: Vec::new(),
        invariant_checks,
        effect_checks,
        resource_specs: Vec::new(),
        ranking_measures: Vec::new(),
        structural_measure: None,
        backedge_target: None,
        natural_exit_target: None,
        body: Box::new(body),
    }
}

pub fn program_parameter(
    name: impl Into<BindingName>,
    program_type: ProgramType,
) -> ProgramParameter {
    ProgramParameter::new(name, program_type)
}

pub fn program_parameter_with_aggregate_layout(
    name: impl Into<BindingName>,
    program_type: ProgramType,
    layout: AggregateLayout,
) -> ProgramParameter {
    ProgramParameter::new(name, program_type).with_aggregate_layout(layout)
}

pub fn program_function(
    return_type: ProgramType,
    name: impl Into<String>,
    parameters: Vec<ProgramParameter>,
    body: ProgramStatement,
) -> ProgramFunction {
    ProgramFunction::new(return_type, name, parameters, body)
}

/// Lowers each contract clause of `function` once: its `requires` at
/// `entry_state`, its `ensures` at that state with the result a fresh
/// symbolic value of the return type. A clause that does not lower, as one
/// using arithmetic on a value of an abstract type, is refused with the
/// lowering's reason. Nothing is proved: a declaration no body answers for,
/// a generic trait's interface, is checked this way once for every type.
pub fn program_check_contract_clauses_lower(
    function: &ProgramFunction,
    state: &ExecutionState,
    arguments: &[ProgramValue],
    assumptions: &PureFactContext,
) -> Result<(), String> {
    // The parameters are bound to the arguments as model values, as a call
    // binds them; no storage is declared for them.
    let mut entry_state = state.clone();
    for (parameter, argument) in function.parameters().iter().zip(arguments) {
        entry_state.locals.bind_logical_typed(
            parameter.binding_name(),
            argument.clone(),
            parameter.program_type(),
        );
    }
    let entry_state = &entry_state;
    for clause in function.contract_requires() {
        program_lower_spec_proposition_at_state(
            entry_state,
            clause,
            Some(entry_state),
            assumptions,
        )?;
    }
    let mut exit_state = entry_state.clone();
    if function.return_type() != ProgramType::Void {
        // A variable no argument uses: arguments are numbered from zero.
        let result = crate::kernel::symbolic_call_result(
            function.return_type(),
            Variable(u64::from(u32::MAX)),
        );
        exit_state
            .locals
            .set_typed(CONTRACT_RESULT, result, function.return_type());
    }
    for clause in function.contract_ensures() {
        program_lower_spec_proposition_at_state(
            &exit_state,
            clause,
            Some(entry_state),
            assumptions,
        )?;
    }
    Ok(())
}

/// Lowers a spec proposition at `state`, the one lowering every proof-side
/// proposition and every contract clause share. `entry_state` is what
/// `old(...)` refers to. The result is the proposition on the lowering's
/// single path with the facts its loads introduced and the obligations
/// they left open (a load the state does not show loadable); `None` when
/// the lowering fails or splits into several paths.
pub fn program_lower_spec_proposition_at_state(
    state: &ExecutionState,
    proposition: &SpecProposition,
    entry_state: Option<&ExecutionState>,
    assumptions: &PureFactContext,
) -> Result<(Proposition, Vec<Proposition>, Vec<Proposition>), String> {
    let (proposition, facts, obligations, _) =
        program_lower_spec_proposition_at_state_with_head_origins(
            state,
            proposition,
            entry_state,
            assumptions,
        )?;
    Ok((proposition, facts, obligations))
}

/// [`program_lower_spec_proposition_at_state`], also reporting the origin of
/// each node in the lowered proposition's head chain: which of its outermost
/// nodes this lowering inserted as a guard, which were written, and the exact kernel variable
/// each written universal bound its written name to. A proof that
/// introduces the head of this goal reads the record instead of inferring
/// the correspondence from the shape the written syntax happens to share.
pub fn program_lower_spec_proposition_at_state_with_head_origins(
    state: &ExecutionState,
    proposition: &SpecProposition,
    entry_state: Option<&ExecutionState>,
    assumptions: &PureFactContext,
) -> Result<
    (
        Proposition,
        Vec<Proposition>,
        Vec<Proposition>,
        LoweringIntroductions,
    ),
    String,
> {
    let (goal, facts, obligations, introductions) =
        program_lower_spec_proposition_with_checked_obligations(
            state,
            proposition,
            entry_state,
            assumptions,
        )
        .map_err(|refusal| refusal.message)?;
    Ok((
        goal,
        facts,
        obligations
            .into_iter()
            .map(|obligation| obligation.proposition().clone())
            .collect(),
        introductions,
    ))
}

/// Why one proof-side lowering refused, as its message plus whatever the
/// lowering recorded about the path it pruned.
///
/// The message is the whole answer for a caller that only reports it. A
/// caller that can spell the user's names -- the surface -- reads the
/// structured record instead and writes the refusal in those names, which is
/// the difference between "produced 0 paths" and naming the cell whose read
/// split.
#[derive(Clone, Debug)]
pub struct LoweringRefusal {
    pub message: String,
    pub limit: Option<ExecutionLimit>,
    /// Present when the lowering pruned a range fold because its body did not
    /// lower to one symbolic iteration under the fold's binders.
    pub dropped_fold_body: Option<DroppedFoldBody>,
    /// Operand types and operator of a comparison that could not be built.
    pub dropped_comparison: Option<(ProgramType, ComparisonOperator, ProgramType)>,
}

impl From<LoweringRefusal> for String {
    fn from(refusal: LoweringRefusal) -> Self {
        refusal.message
    }
}

/// Why a specification lowering or evaluation stopped, in the reader's terms.
///
/// The kernel's own stopping points are budgets and internal defects, and a
/// `{:?}` of one is a leak: `the kernel evaluation hit Paths` told a reader
/// holding a `fold` with an unowned model field nothing they could act on.
/// The classified variants say what happened; everything else names its
/// budget through the one table, [`ExecutionLimit::describe`].
/// The refusal of decision D2 (Stage 5, `design/machine-integers.md`): a
/// `Bool` is not a number.
pub(crate) const BOOL_HAS_NO_INTEGER_VALUE: &str =
    "a `Bool` has no integer value; write `b as int32`, or compare it with `true` or `false`";

pub(in crate::kernel) fn describe_spec_lowering_limit(what: &str, limit: ExecutionLimit) -> String {
    match limit {
        // The lowering runs beside a live execution whose identity mark it
        // does not carry, so an identity from the base of that range would
        // name a havocked local or a join abstraction. Everything this
        // lowering invents is a bound variable drawn from the match-binder
        // range instead; a request for an execution identity is a defect in
        // the kernel, and it is reported as one rather than satisfied.
        ExecutionLimit::ExecutionIdentityBesideLiveState => {
            "internal: execution identity requested beside a live state".to_string()
        }
        ExecutionLimit::AuthorityCountNeedsExactPointer => {
            "count(...) needs one exact base pointer".to_string()
        }
        ExecutionLimit::AuthorityCountNeedsResolvedMember => {
            "count(...) requires resolved member indices or the helper's selected member"
                .to_string()
        }
        ExecutionLimit::AuthorityCountNeedsOwnership => {
            "count(...) requires owning authority for that population".to_string()
        }
        ExecutionLimit::AuthorityCountPendingLockedWorker => {
            "count(...) is unknown until pthread_join returns the workers that change this population under its mutex".to_string()
        }
        ExecutionLimit::AuthorityCountLentToWorker => {
            "count(...) requires owning authority for that population, which an outstanding worker holds until its pthread_join".to_string()
        }
        ExecutionLimit::GuardedConjunctionTooLong => format!(
            "unsupported: a conjunction reads a side that owes evaluation domains under more \
             than {} earlier conjuncts; split it into separate clauses or `have` steps",
            crate::kernel::GUARDED_CONJUNCTION_LIMIT
        ),
        ExecutionLimit::BoolComparedWithInteger => BOOL_HAS_NO_INTEGER_VALUE.to_string(),
        ExecutionLimit::BoolArithmetic => BOOL_HAS_NO_INTEGER_VALUE.to_string(),
        ExecutionLimit::BoolOrdered => {
            "`Bool` has no order; compare `Bool` values with `==` or `!=`, or write `b as int32`"
                .to_string()
        }
        ExecutionLimit::MixedBoolArms => {
            "a conditional's arms have one type: one is an integer and the other a `Bool`; write `b as int32`, or use `true` and `false` arms".to_string()
        }
        ExecutionLimit::SymbolicPointerConditional => {
            "Click cannot yet represent a symbolic choice between distinct pointers. Put the comparison inside both cases, using `or`".to_string()
        }
        ExecutionLimit::DisjunctionRightUndefined => {
            "the right side of `or` is undefined wherever its left side is false, the only case in which it is read".to_string()
        }
        // The kernel knows the identity is absent; it does not know the name
        // the reader wrote for it. A caller that has the source expression
        // says which field and which repair instead of printing this.
        ExecutionLimit::ResourceFieldInstanceUnavailable => {
            "this expression reads a model field of a resource instance the state does not hold"
                .to_string()
        }
        limit => format!("the kernel {what} stopped at {}", limit.describe()),
    }
}

fn retained_lowering_limit(budget: &ExecutionBudget, limit: ExecutionLimit) -> ExecutionLimit {
    if budget.dropped_symbolic_pointer_conditional
        && matches!(
            limit,
            ExecutionLimit::Paths | ExecutionLimit::DisjunctionRightUndefined
        )
    {
        ExecutionLimit::SymbolicPointerConditional
    } else {
        limit
    }
}

/// Why a specification evaluation did not produce exactly one path. No path
/// at all is almost always every path ending in a runtime error, and the
/// first such error is the message; the count alone hid a 4-byte load of an
/// 8-byte cell behind "0 paths" for three proof attempts.
fn no_single_path_message<T>(what: &str, paths: &[T], budget: &ExecutionBudget) -> String {
    if paths.is_empty()
        && let Some(span) = budget.dropped_range_span()
    {
        let width = span.element_width;
        let limit = span.byte_limit;
        return if span.element_count < 0 {
            let count = -span.element_count;
            let elements = if count == 1 { "element" } else { "elements" };
            format!(
                "the kernel {what} produced no path: a memory range runs backwards, so it is not a byte span: its end is {count} {elements} before its start"
            )
        } else {
            format!(
                "the kernel {what} produced no path: a memory range is too wide to be a 32-bit byte span: {} elements of {width} bytes is {} bytes, past the {limit}-byte limit",
                span.element_count,
                span.element_count.saturating_mul(i64::from(width))
            )
        };
    }
    if paths.is_empty()
        && let Some(reversed) = budget.dropped_refuted_range_span()
    {
        return if reversed {
            format!(
                "the kernel {what} produced no path: a memory range runs backwards, so it is not a byte span: this context proves its end is before its start"
            )
        } else {
            format!(
                "the kernel {what} produced no path: a memory range is too wide to be a 32-bit byte span: this context bounds its element count past the byte limit"
            )
        };
    }
    match (paths.len(), budget.dropped_runtime_error()) {
        (0, Some(error)) => format!(
            "the kernel {what} produced no path: every evaluation path ended in a runtime error: {}",
            error.kernel_summary()
        ),
        (0, None) if budget.dropped_fold_body().is_some() => {
            let dropped = budget
                .dropped_fold_body()
                .expect("the guard above checked this");
            match dropped.body_paths {
                1 => format!(
                    "the kernel {what} produced no path: a range fold's body raised a condition \
                     that is about one item of the fold's range rather than about this state, so \
                     the fold could not be lowered as one symbolic iteration"
                ),
                count => format!(
                    "the kernel {what} produced no path: a range fold's body evaluated to {count} \
                     paths, not one, so it does not denote one value for every item of the fold's \
                     range"
                ),
            }
        }
        (0, None) if let Some(behavior) = budget.dropped_undefined_behavior() => format!(
            "the kernel {what} produced no path: every evaluation path ended in undefined \
             behavior: {}",
            behavior.description()
        ),
        (0, None) if budget.dropped_comparison.is_some() => {
            "the comparison could not be constructed for its operand values".to_string()
        }
        (count, _) => format!("the kernel {what} produced {count} paths, not one"),
    }
}

/// Selects the one lowering candidate justified by facts already stated in
/// this exact proof context. A single candidate needs no routing evidence;
/// several candidates do. In the latter case every fact that routed the
/// selected candidate must already be an exactly stated fact, and exactly one
/// candidate may satisfy that rule.
///
/// This deliberately walks only the produced candidates and their own facts.
/// It neither scans the ambient context nor treats the absence or conflict of
/// sibling candidates as evidence for a survivor.
pub(in crate::kernel) fn exactly_selected_spec_proposition_path<'a>(
    paths: &'a [crate::kernel::spec::SpecPropositionPath],
    assumptions: &PureFactContext,
) -> Option<&'a crate::kernel::spec::SpecPropositionPath> {
    if let [path] = paths {
        return Some(path);
    }
    let mut selected = None;
    for path in paths {
        crate::instrumentation::record_deterministic_work(1);
        if !path.facts.has_path_conditions()
            || !path
                .facts
                .iter()
                .filter(|fact| !fact.is_logical_read_equation())
                .all(|fact| assumptions.states_required_goal(fact.proposition()))
        {
            continue;
        }
        if selected.is_some() {
            return None;
        }
        selected = Some(path);
    }
    selected
}

/// Proof-side lowering keeps mandatory verification conditions distinct from
/// assumable evaluation obligations until the caller checks their evidence.
pub(crate) fn program_lower_spec_proposition_with_checked_obligations(
    state: &ExecutionState,
    proposition: &SpecProposition,
    entry_state: Option<&ExecutionState>,
    assumptions: &PureFactContext,
) -> Result<
    (
        Proposition,
        Vec<Proposition>,
        Vec<ProofObligation>,
        LoweringIntroductions,
    ),
    LoweringRefusal,
> {
    lower_checked_proof_proposition(state, proposition, entry_state, assumptions, false)
}

/// [`program_lower_spec_proposition_with_checked_obligations`] for a `branch
/// ensuring` fact at its join. Every arm lowered the fact with ordinary
/// lowering, so the join may introduce its typed calls' argument domains for
/// the joined values (see `spec::lower_assumed_interface_proposition`).
pub(crate) fn program_lower_assumed_interface_proposition_with_checked_obligations(
    state: &ExecutionState,
    proposition: &SpecProposition,
    entry_state: Option<&ExecutionState>,
    assumptions: &PureFactContext,
) -> Result<
    (
        Proposition,
        Vec<Proposition>,
        Vec<ProofObligation>,
        LoweringIntroductions,
    ),
    LoweringRefusal,
> {
    lower_checked_proof_proposition(state, proposition, entry_state, assumptions, true)
}

/// The reasoning policy a proposition a proof states is lowered under: a
/// `have`, and a `branch ensuring` fact checked in each arm, lower the same
/// text the same way. A proposition that applies a pure function keeps its
/// memory reads symbolic, so a read through the application's value reaches
/// the cell by the equality graph rather than by evaluating the read.
pub(crate) fn proof_lowering_assumptions(
    assumptions: &PureFactContext,
    proposition: &SpecProposition,
) -> PureFactContext {
    let assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads()
        .defer_non_exact_loadability_obligations();
    if applies_pure_function(proposition) {
        assumptions.keep_spec_loads_symbolic()
    } else {
        assumptions
    }
}

/// Whether `proposition` applies a pure function anywhere in its written
/// body. One visit per spec node.
fn applies_pure_function(proposition: &SpecProposition) -> bool {
    use crate::kernel::spec::walk::{SpecNode, Visit, WalkBudget, Walked, walk_spec};
    let walked = walk_spec(
        SpecNode::Proposition(proposition),
        WalkBudget::Unmetered,
        |node| match node {
            SpecNode::Expression(SpecExpression::PureFunctionApplication { .. })
            | SpecNode::Integer(SpecIntegerExpression::PureFunctionApplication { .. }) => {
                Visit::Stop(())
            }
            SpecNode::Algebraic(algebraic)
                if matches!(
                    algebraic.node,
                    SpecAlgebraicExpressionNode::PureFunctionApplication { .. }
                ) =>
            {
                Visit::Stop(())
            }
            _ => Visit::Descend,
        },
    );
    matches!(walked, Walked::Stopped(()))
}

fn lower_checked_proof_proposition(
    state: &ExecutionState,
    proposition: &SpecProposition,
    entry_state: Option<&ExecutionState>,
    assumptions: &PureFactContext,
    assumed_interface: bool,
) -> Result<
    (
        Proposition,
        Vec<Proposition>,
        Vec<ProofObligation>,
        LoweringIntroductions,
    ),
    LoweringRefusal,
> {
    let lowering_assumptions = proof_lowering_assumptions(assumptions, proposition);
    let mut budget = ExecutionBudget::beside_live_state();
    let lower = if assumed_interface {
        crate::kernel::spec::lower_assumed_interface_proposition
    } else {
        lower_spec_proposition_at_state_with_loop_entry
    };
    let paths = lower(
        state,
        proposition,
        entry_state,
        &lowering_assumptions,
        &mut budget,
    )
    .map_err(|limit| {
        let limit = retained_lowering_limit(&budget, limit);
        LoweringRefusal {
            message: describe_spec_lowering_limit("lowering", limit),
            limit: Some(limit),
            dropped_fold_body: None,
            dropped_comparison: None,
        }
    })?;
    let Some(path) = exactly_selected_spec_proposition_path(&paths, assumptions) else {
        let limit = (paths.is_empty()
            && budget.dropped_symbolic_pointer_conditional
            && budget.dropped_runtime_error().is_none())
        .then_some(ExecutionLimit::SymbolicPointerConditional);
        return Err(LoweringRefusal {
            message: if let Some(limit) = limit {
                describe_spec_lowering_limit("lowering", limit)
            } else {
                no_single_path_message("lowering", &paths, &budget)
            },
            limit,
            // Only a lowering that produced nothing at all is explained by a
            // pruned fold: with a path in hand the count, not the prune, is
            // what the caller must read. A dropped runtime error is more
            // concrete still, and its own message keeps precedence.
            dropped_fold_body: (paths.is_empty() && budget.dropped_runtime_error().is_none())
                .then(|| budget.dropped_fold_body().cloned())
                .flatten(),
            dropped_comparison: (paths.is_empty() && budget.dropped_runtime_error().is_none())
                .then_some(budget.dropped_comparison)
                .flatten(),
        });
    };
    let lowered_proposition = crate::kernel::clone_proposition_iteratively(&path.proposition);
    if crate::kernel::fact_stability::enabled() {
        let fact_free = crate::kernel::fact_stability::shadow(|| {
            let empty = lowering_assumptions.without_facts();
            let mut budget = ExecutionBudget::beside_live_state();
            match lower(state, proposition, entry_state, &empty, &mut budget) {
                Ok(paths) => match exactly_selected_spec_proposition_path(&paths, &empty) {
                    Some(path) => crate::kernel::fact_stability::FactFree::Term(
                        crate::kernel::clone_proposition_iteratively(&path.proposition),
                    ),
                    None if paths.is_empty() => crate::kernel::fact_stability::FactFree::Refused,
                    None => crate::kernel::fact_stability::FactFree::Paths(paths.len()),
                },
                Err(_) => crate::kernel::fact_stability::FactFree::Refused,
            }
        });
        crate::kernel::fact_stability::compare(
            if assumed_interface {
                "assumed interface proposition"
            } else {
                "checked proof proposition"
            },
            &lowered_proposition,
            &fact_free,
        );
    }
    let facts = path
        .facts
        .iter()
        .map(|fact| crate::kernel::clone_proposition_iteratively(fact.proposition()))
        .collect();
    let obligations = path.obligations.clone();
    let introductions = path.introductions.clone();
    Ok((lowered_proposition, facts, obligations, introductions))
}

/// Evaluates a spec expression at `state`: the one evaluation every
/// proof-side expression and every contract expression share. `entry_state`
/// is what `old(...)` refers to. The result is the value on the evaluation's
/// single path with the load obligations the path left open.
pub fn program_evaluate_speprogram_expression_at_state(
    state: &ExecutionState,
    expression: &SpecExpression,
    entry_state: Option<&ExecutionState>,
    assumptions: &PureFactContext,
) -> Result<(ProgramValue, Vec<Proposition>), String> {
    let path = evaluate_speprogram_expression_path(state, expression, entry_state, assumptions)?;
    Ok((
        path.value.into_native(),
        path.obligations
            .into_iter()
            .map(|obligation| obligation.proposition().clone())
            .collect(),
    ))
}

/// Capture a typed common root without materializing its native expression tree.
/// Path facts and required constructions remain attached to this result; capture
/// alone grants no authority to use them as established premises.
pub(crate) fn program_evaluate_retained_spec_expression(
    state: &ExecutionState,
    expression: &SpecExpression,
    entry_state: Option<&ExecutionState>,
    assumptions: &PureFactContext,
) -> Result<crate::kernel::LoweredTermPath, String> {
    evaluate_speprogram_expression_path(state, expression, entry_state, assumptions)
        .map(|path| path.map_value(|value| value.common_operand()))
}

fn evaluate_speprogram_expression_path(
    state: &ExecutionState,
    expression: &SpecExpression,
    entry_state: Option<&ExecutionState>,
    assumptions: &PureFactContext,
) -> Result<super::spec::SpecExpressionPath, String> {
    let lowering_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads()
        .defer_non_exact_loadability_obligations();
    let mut budget = ExecutionBudget::beside_live_state();
    let paths = evaluate_spec_expression_paths_with_loop_entry(
        state,
        expression,
        entry_state,
        &lowering_assumptions,
        &mut budget,
    )
    .map_err(|limit| describe_spec_lowering_limit("evaluation", limit))?;
    if paths.len() != 1 {
        return Err(no_single_path_message("evaluation", &paths, &budget));
    }
    Ok(paths.into_iter().next().expect("one evaluation path"))
}

pub(crate) fn program_evaluate_speresource_expression_with_checked_obligations(
    state: &ExecutionState,
    expression: &SpecExpression,
    entry_state: Option<&ExecutionState>,
    assumptions: &PureFactContext,
) -> Result<(ProgramValue, Vec<ProofObligation>), String> {
    let lowering_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads()
        .defer_non_exact_loadability_obligations();
    let mut budget = ExecutionBudget::beside_live_state();
    let paths = crate::kernel::spec::evaluate_spec_expression_checked_paths_with_loop_entry(
        state,
        expression,
        entry_state,
        &lowering_assumptions,
        &mut budget,
    )
    .map_err(|limit| describe_spec_lowering_limit("evaluation", limit))?;
    let [path] = paths.as_slice() else {
        return Err(no_single_path_message("evaluation", &paths, &budget));
    };
    Ok((path.value.clone().into_native(), path.obligations.clone()))
}

/// Freeze protocols before evaluating an independent contract's assumed guard
/// inputs. This grants no resources and is not a call-site transfer operation.
pub(crate) fn execution_state_with_assumed_mutex_inputs(
    mut state: ExecutionState,
) -> ExecutionState {
    if state.resources.facts().iter().any(|fact| {
        matches!(
            fact.resource(),
            Resource::MutexGuard(_) | Resource::MutexLive(_) | Resource::MutexUse(_)
        )
    }) {
        state.preserves_mutex_protocols = true;
    }
    state
}

pub(crate) fn program_mutex_guard_resource(
    state: &ExecutionState,
    mutex: &Address,
    abstract_entry: bool,
) -> Option<ResourceFact> {
    crate::kernel::mutexes::guard_resource(state, mutex, abstract_entry)
}

pub(crate) fn program_mutex_live_resource(
    state: &ExecutionState,
    mutex: &Address,
    abstract_entry: bool,
) -> Option<ResourceFact> {
    crate::kernel::mutexes::live_resource(state, mutex, abstract_entry)
}

/// Construct a contract requirement; this does not establish ownership.
pub(crate) fn program_mutex_use_resource_with_type(
    state: &ExecutionState,
    mutex: &Address,
    protected: ResourceDescription,
) -> ResourceFact {
    let fact = program_mutex_use_resource(state, mutex);
    let Resource::MutexUse(mut identity) = fact.resource().clone() else {
        unreachable!()
    };
    identity.protected = Some(protected);
    ResourceFact::own(Resource::MutexUse(identity))
}

pub(crate) fn program_mutex_use_resource(state: &ExecutionState, mutex: &Address) -> ResourceFact {
    crate::kernel::mutexes::use_resource(state, mutex)
}

/// Binds a contract's value parameters in an entry state, as a call binds
/// them beside its arguments.
pub(crate) fn bind_contract_value_parameters(
    entry: &mut ExecutionState,
    parameters: &[ProgramParameter],
    values: &[ProgramValue],
) {
    for (parameter, value) in parameters.iter().zip(values) {
        entry.locals.set_typed_qualified_with_all_qualifiers(
            parameter.binding_name().clone(),
            value.clone(),
            parameter.program_type(),
            SymbolicMemory::value_parameter_pointer(parameter.binding_name()),
            false,
            false,
            false,
            false,
        );
    }
}

pub fn program_function_entry_state(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
) -> Option<ExecutionState> {
    program_function_entry_state_with(caller_state, function, arguments, false)
}

/// The state that declares a function proof's by-value aggregate inputs:
/// [`program_function_entry_state`], except that each such parameter's object is
/// declared and not copied into. It is the argument the proof is about, so
/// the caller names its cells as their own entry values.
pub fn program_function_input_objects_state(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
) -> Option<ExecutionState> {
    program_function_entry_state_with(caller_state, function, arguments, true)
}

/// Keeps the identity of each aggregate proof input explicitly named by a
/// logical resource. Select by the materialized slot's exact pointer key.
pub(crate) fn with_resource_keyed_aggregate_proof_inputs(
    mut state: ExecutionState,
    function: &ProgramFunction,
) -> ExecutionState {
    let mut owner = None;
    for parameter in function.parameters() {
        crate::instrumentation::record_deterministic_work(1);
        if parameter.aggregate_layout().is_none() {
            continue;
        }
        let name = parameter.binding_name();
        let Some(LocalBinding::AggregateObject {
            layout,
            slot,
            constant,
            ..
        }) = state.locals.binding(name)
        else {
            continue;
        };
        if state
            .resources
            .owned_instances_with_pointer_argument(slot)
            .next()
            .is_none()
        {
            continue;
        }
        let owner = owner.get_or_insert_with(|| Arc::<str>::from(function.name()));
        state.locals.insert_binding(
            name.clone(),
            LocalBinding::AggregateObject {
                layout: layout.clone(),
                slot: slot.clone(),
                constant: *constant,
                proof_input_for: Some(owner.clone()),
            },
        );
    }
    state
}

fn program_function_entry_state_with(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    input_aggregates: bool,
) -> Option<ExecutionState> {
    let values = arguments
        .iter()
        .map(|argument| match argument {
            ProgramExpression::Value(value) => Some(value.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    let mut entry = crate::kernel::functions::bind_program_function_arguments_with(
        caller_state,
        function,
        &values,
        input_aggregates,
    )?;
    if let Some(events) = caller_state
        .population_effects
        .creation
        .as_ref()
        .filter(|events| events.has_opaque_import())
    {
        Arc::make_mut(&mut entry.population_effects).creation = Some(events.enter_proof_entry());
    }
    // This API rebinds a proof frontier, including an explicitly unfolded
    // entry representation. It is not the modular call ownership transfer.
    entry.instance_field_scope = caller_state.instance_field_scope.clone();
    Some(entry)
}

/// Install the caller-supplied shared borrows assumed by one modular contract
/// proof. Only principal resource occurrences selected by checked input-view
/// clauses may receive authority here. Ordinary and nested calls must use the
/// checked lending/reborrow planner instead.
pub(crate) fn execution_state_with_borrowed_contract_inputs(
    state: ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
) -> Result<ExecutionState, RuntimeError> {
    let mut state = state;
    state.preserves_mutex_protocols |=
        crate::kernel::functions::preserves_mutex_protocols(function.contract_interface());
    let has_views = function
        .resource_requires()
        .iter()
        .any(ResourceSpec::is_view);
    if !has_views && !state.preserves_mutex_protocols {
        return Ok(state);
    }
    if state.borrow_ledger().is_some()
        || state.borrow_participant().is_some()
        || state.borrow_bindings().iter().next().is_some()
        || !state.borrow_bindings_are_consistent()
    {
        return Err(BorrowRefusal::InvalidEvidence
            .diagnostic(BorrowRefusalOperation::Entry)
            .into());
    }
    if let Some(rooted) = BORROWED_INPUT_ROOTS.with(|roots| {
        roots
            .borrow()
            .get(function.name())
            .filter(|(installed_on, _)| installed_on == &state)
            .map(|(_, rooted)| rooted.clone())
    }) {
        // Borrow identities are reused across separately checked claims, but
        // their pure contexts have independent graph lineages. This is the
        // selected contract-input producer boundary, not a permission query.
        rooted
            .resources()
            .synchronize_memory_equalities(assumptions);
        return Ok(rooted);
    }
    let mut rooted = if has_views {
        // The function's own entry clauses (`assume_entry_clause_spans`).
        install_borrowed_contract_inputs(
            state.clone(),
            function,
            arguments,
            &assumptions.clone().assume_entry_clause_spans(),
        )?
    } else {
        state.clone()
    };
    // Root only actual primitive input occurrences. A description alone is
    // never authority at an executing call site.
    let use_inputs = rooted.resources().facts().iter().filter(|fact|
        matches!(fact.resource(), Resource::MutexUse(identity) if identity.binding.is_none()))
        .cloned().collect::<Vec<_>>();
    if !use_inputs.is_empty() {
        let mut ledger = rooted
            .borrow_ledger()
            .cloned()
            .unwrap_or_else(BorrowLedger::new);
        let holder = match rooted.borrow_participant() {
            Some(holder) => holder,
            None => ledger
                .fresh_participant()
                .map_err(|e| e.diagnostic(BorrowRefusalOperation::Entry))?,
        };
        for fact in use_inputs {
            let Resource::MutexUse(identity) = fact.resource() else {
                unreachable!()
            };
            let (support, _) = rooted
                .resources()
                .unique_owned_occurrence_for_fact(&fact)
                .ok_or_else(|| {
                    BorrowRefusal::MissingBacking.diagnostic(BorrowRefusalOperation::Entry)
                })?;
            let (next, input) = ledger
                .borrowed_mutex_use_input_with_protected(
                    holder,
                    support,
                    identity.mutex.clone(),
                    identity.protected.clone(),
                )
                .map_err(|e| e.diagnostic(BorrowRefusalOperation::Entry))?;
            let bound = next
                .mutex_use_resource(input.usage, holder)
                .map_err(|e| e.diagnostic(BorrowRefusalOperation::Entry))?;
            rooted.resources = rooted
                .resources
                .clone()
                .without_fact_delaying_normalization(&fact, assumptions)
                .ok_or_else(|| {
                    BorrowRefusal::MissingBacking.diagnostic(BorrowRefusalOperation::Entry)
                })?
                .try_compose_with_facts_delaying_normalization([bound], assumptions)
                .map_err(|_| {
                    BorrowRefusal::MissingBacking.diagnostic(BorrowRefusalOperation::Entry)
                })?;
            ledger = next;
        }
        rooted.borrow_ledger = Some(ledger);
        rooted.borrow_participant = Some(holder);
    }
    if state.preserves_mutex_protocols && state.mutex_ledger.is_none() {
        rooted.mutex_input_reservations =
            crate::kernel::functions::assumed_mutex_input_reservations(
                &state,
                function,
                assumptions,
            );
    }
    rooted = crate::kernel::mutexes::bind_assumed_guard_inputs(rooted, assumptions)
        .map_err(|e| e.diagnostic(BorrowRefusalOperation::Entry))?;
    rooted = crate::kernel::mutexes::bind_assumed_lifetime_inputs(rooted, assumptions)
        .map_err(|e| e.diagnostic(BorrowRefusalOperation::Entry))?;
    // Bind names only after primitive inputs have generative initialization
    // and acquisition identities. A name cannot manufacture its authority.
    if function
        .resource_requires()
        .iter()
        .any(|spec| spec.mutex_authority_binding().is_some())
    {
        let entry =
            program_function_entry_state(&rooted, function, arguments).ok_or_else(|| {
                BorrowRefusal::MissingBacking.diagnostic(BorrowRefusalOperation::Entry)
            })?;
        let mut budget = ExecutionBudget::beside_live_state();
        for spec in function.resource_requires() {
            let Some((identity, _)) = spec.mutex_authority_binding() else {
                continue;
            };
            let fact = super::functions::evaluate_function_resource_spec_with_entry(
                &entry,
                &entry,
                &spec.without_mutex_authority_binding(),
                assumptions,
                &mut budget,
            )
            .map_err(|limit| {
                ContractEntryRefusal::from_limit("could not evaluate a mutex input", limit)
                    .into_runtime_error()
            })??;
            rooted = rooted
                .bind_named_mutex_authority(identity, &fact)
                .map_err(|_| {
                    BorrowRefusal::MissingBacking.diagnostic(BorrowRefusalOperation::Entry)
                })?;
        }
    }
    if let Some(contract) =
        crate::kernel::mutexes::helper_contracts::classify(function.contract_interface())
            .map_err(|reason| RuntimeError::InvalidContractResource(reason.into()))?
    {
        let entry =
            program_function_entry_state(&rooted, function, arguments).ok_or_else(|| {
                BorrowRefusal::MissingBacking.diagnostic(BorrowRefusalOperation::Entry)
            })?;
        let mut budget = ExecutionBudget::beside_live_state();
        let mut evaluate = |spec: &ResourceSpec| {
            super::functions::evaluate_function_resource_spec_with_entry(
                &entry,
                &entry,
                spec,
                assumptions,
                &mut budget,
            )
            .map_err(|limit| {
                ContractEntryRefusal::from_limit("could not evaluate a mutex input", limit)
                    .into_runtime_error()
            })?
        };
        let access = evaluate(&contract.access)?;
        let (guard, payload) =
            if contract.effect == crate::kernel::mutexes::helper_contracts::HelperEffect::Release {
                let guard = evaluate(&contract.guard)?;
                let payload = contract
                    .payload
                    .as_ref()
                    .map(&mut evaluate)
                    .transpose()?
                    .map(|fact| {
                        let Resource::Instance(instance) = fact.resource() else {
                            unreachable!("named protected state")
                        };
                        instance.clone()
                    });
                (Some(guard), payload)
            } else {
                (None, None)
            };
        rooted = crate::kernel::mutexes::helper_contracts::install_entry(
            rooted,
            &contract,
            &access,
            guard.as_ref(),
            payload,
        )
        .map_err(|_| BorrowRefusal::InvalidEvidence.diagnostic(BorrowRefusalOperation::Entry))?;
    }
    BORROWED_INPUT_ROOTS.with(|roots| {
        roots
            .borrow_mut()
            .insert(function.name().to_string(), (state, rooted.clone()));
    });
    Ok(rooted)
}

fn install_borrowed_contract_inputs(
    state: ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
) -> Result<ExecutionState, RuntimeError> {
    let entry = program_function_entry_state(&state, function, arguments)
        .ok_or_else(|| BorrowRefusal::MissingBacking.diagnostic(BorrowRefusalOperation::Entry))?;
    let mut budget = ExecutionBudget::beside_live_state();
    let (_, checked_inputs) = evaluate_function_resource_context_with_metadata(
        &entry,
        function.resource_requires(),
        function.composite_resource_definitions(),
        &assumptions.clone().assume_entry_clause_spans(),
        &mut budget,
    )
    .map_err(|limit| {
        ContractEntryRefusal::from_limit("could not evaluate the input view clauses", limit)
            .into_runtime_error()
    })??;

    // The contract's partition is the precondition: an owned clause that
    // provably overlaps a viewed clause, or a viewed composite's direct
    // frontier, is a contract no caller can satisfy. Refuse it here rather
    // than proving a vacuous body under it.
    let owned_input_ranges = checked_inputs
        .iter()
        .filter(|input| input.fact.is_own())
        .filter_map(|input| input.fact.memory_range().cloned())
        .collect::<Vec<_>>();
    // This check decides the partition, so it may not read a claim *of* the
    // partition. `memory_ranges_proven_overlapping` answers "not
    // overlapping" as soon as the context holds an explicit separation of
    // the two ranges, and the entry partition
    // (`functions::contract_entry_partition_facts`) is exactly such a
    // separation over exactly these two clauses: reading one here would let
    // the claim license itself, and `requires q == p; views p[0..1]; owns
    // q[0..1];` would stop being refused
    // (`root_view_refuses_an_owned_alias_of_the_viewed_range`). Every memory
    // separation is ignored by this query, regardless of spelling. A stated
    // `separate(..)` over the same two clauses is a second spelling of the
    // same claim, not evidence about where the ranges are.
    let refuse_owned_overlap = |viewed_range: &MemoryRange| {
        owned_input_ranges
            .iter()
            .find(|owned| {
                crate::kernel::primitives::contract_entry_memory_overlap(
                    owned,
                    viewed_range,
                    assumptions,
                )
            })
            .map(|owned| {
                BorrowRefusal::ActiveDependency.proven_overlap_diagnostic(
                    BorrowRefusalOperation::Entry,
                    BorrowRefusalSubject::for_conflicting_resources(
                        ResourceFact::view_memory(viewed_range.clone()),
                        ResourceFact::own_memory(owned.clone()),
                    ),
                )
            })
    };
    // Normalization can represent a folded input view as a projection of an
    // owner. Such a view has no independent occurrence to borrow. Check the
    // written owners before asking the state for a principal view occurrence.
    let owned_composites = std::cell::LazyCell::new(|| {
        ResourceContext::new_with_equalities(assumptions).unchecked_with_facts(
            checked_inputs
                .iter()
                .map(|input| &input.fact)
                .filter(|fact| {
                    fact.is_own() && matches!(fact.resource(), Resource::Composite { .. })
                })
                .cloned(),
        )
    });
    let mut selected = BTreeMap::new();
    for input in checked_inputs.iter().filter(|input| input.fact.is_view()) {
        if matches!(input.fact.resource(), Resource::Composite { .. })
            && let Some((_, owner)) = owned_composites
                .directly_supporting_owned_entry_ignoring_separation(&input.fact, assumptions)
        {
            return Err(BorrowRefusal::ActiveDependency
                .proven_overlap_diagnostic(
                    BorrowRefusalOperation::Entry,
                    BorrowRefusalSubject::for_conflicting_resources(
                        input.fact.clone(),
                        owner.clone(),
                    ),
                )
                .into());
        }
        if let Some(range) = input.fact.memory_range()
            && let Some(diagnostic) = refuse_owned_overlap(range)
        {
            return Err(diagnostic.into());
        }
        if matches!(
            input.fact.resource(),
            Resource::Memory(range)
                if range.base().base.is_local_block()
                    || state.memory().is_read_only_block(&range.base().base)
        ) {
            continue;
        }
        let Some(occurrence) = state
            .resources()
            .principal_input_view_occurrence(&input.fact, assumptions)
        else {
            return Err(BorrowRefusal::MissingBorrowBinding
                .diagnostic_with_subject(
                    BorrowRefusalOperation::Entry,
                    BorrowRefusalSubject::for_resource(input.fact.clone()),
                )
                .into());
        };
        let viewed = state
            .resources()
            .view_fact_at_occurrence(occurrence)
            .cloned()
            .ok_or_else(|| {
                BorrowRefusal::MissingBorrowBinding.diagnostic_with_subject(
                    BorrowRefusalOperation::Entry,
                    BorrowRefusalSubject::with_support_id(occurrence),
                )
            })?;
        // Address-backed aggregate parameters and compiler-created local
        // arrays are storage owned by this activation. Their bounded views
        // use the existing local-storage check at each call; they are not
        // caller-supplied shared borrows and therefore need no external root.
        if matches!(
            viewed.resource(),
            Resource::Memory(range)
                if range.base().base.is_local_block()
                    || state.memory().is_read_only_block(&range.base().base)
        ) {
            continue;
        }
        // A view the same contract already owns is not authority a caller
        // lends: the two clauses describe one right twice. Name both so the
        // reader can see which `views` and which `owns` overlap.
        //
        // Asked without the memory separations, for the reason above:
        // `memory_range_covers` answers "does not cover" as soon as the
        // context separates the two ranges, and the entry partition is
        // exactly a separation of an owned clause from a viewed one. This is
        // the decision that licenses that fact, so it cannot consume it.
        if let Some((_, owner)) = state
            .resources()
            .directly_supporting_owned_entry_ignoring_separation(&viewed, assumptions)
        {
            let owner = owner.clone();
            return Err(BorrowRefusal::ActiveDependency
                .diagnostic_with_subject(
                    BorrowRefusalOperation::Entry,
                    BorrowRefusalSubject::for_supported_view(viewed, owner, occurrence),
                )
                .into());
        }
        selected.entry(occurrence).or_insert(viewed);
    }

    if selected.is_empty() {
        return Ok(state);
    }

    let mut ledger = BorrowLedger::new();
    let participant = ledger
        .fresh_participant()
        .map_err(|error| error.diagnostic(BorrowRefusalOperation::Entry))?;
    let mut bindings = BorrowBindings::default();
    for (occurrence, viewed) in selected {
        let (backing, backing_pieces) = if matches!(viewed.resource(), Resource::Composite { .. }) {
            let singleton = ResourceContext::new_with_equalities(assumptions)
                .unchecked_with_fact(viewed.clone());
            let (_, mut pieces, raw_children) =
                checked_expand_composite_resource_fact_with_children(
                    &singleton,
                    &viewed,
                    function.composite_resource_definitions(),
                    &state.program_point(),
                    assumptions,
                )
                .map_err(ContractEntryRefusal::into_runtime_error)?;
            for raw_child in raw_children {
                let candidates = state
                    .resources()
                    .view_occurrences_for_fact(&raw_child, assumptions);
                if let [occurrence] = candidates.as_slice()
                    && let Some(actual) = state
                        .resources()
                        .view_fact_at_occurrence(*occurrence)
                        .cloned()
                    && !pieces.contains(&actual)
                {
                    pieces.push(actual);
                }
            }
            if pieces
                .iter()
                .any(|piece| matches!(piece.resource(), Resource::Instance(_)))
            {
                return Err(RuntimeError::InvalidContractResource(
                    "a composite input view cannot include an exclusive resource instance".into(),
                ));
            }
            let backing = BorrowedContractInputBacking::from_checked_expansion(
                occurrence,
                viewed.clone(),
                pieces.clone(),
            )
            .ok_or_else(|| {
                RuntimeError::ContractEntryInvariant(
                    "the checked composite input did not produce a stable view".into(),
                )
            })?;
            (Some(backing), pieces)
        } else {
            (None, Vec::new())
        };
        let opening = ledger
            .borrowed_contract_input(participant, occurrence, viewed.clone(), backing)
            .map_err(|error| {
                error.diagnostic_with_subject(
                    BorrowRefusalOperation::Entry,
                    BorrowRefusalSubject::with_support_id(occurrence),
                )
            })?;
        ledger = ledger.apply(&opening.transition).map_err(|error| {
            error.diagnostic_with_subject(
                BorrowRefusalOperation::Entry,
                BorrowRefusalSubject::with_support_id(occurrence),
            )
        })?;
        bindings = bindings.with_inserted(
            occurrence,
            BorrowBinding {
                borrow: opening.borrow,
                scope: opening.scope,
                share: opening.root_share,
                support: occurrence,
                viewed,
                hold: None,
            },
        );
        for piece in backing_pieces {
            if let Some(range) = piece.memory_range()
                && let Some(diagnostic) = refuse_owned_overlap(range)
            {
                return Err(diagnostic.into());
            }
            let occurrences = state
                .resources()
                .view_occurrences_for_fact(&piece, assumptions);
            match occurrences.as_slice() {
                [] => {}
                [piece_occurrence] => {
                    bindings = bindings.with_inserted(
                        *piece_occurrence,
                        BorrowBinding {
                            borrow: opening.borrow,
                            scope: opening.scope,
                            share: opening.root_share,
                            support: occurrence,
                            viewed: piece,
                            hold: None,
                        },
                    );
                }
                _ => {
                    return Err(BorrowRefusal::MissingBorrowBinding
                        .diagnostic_with_subject(
                            BorrowRefusalOperation::Entry,
                            BorrowRefusalSubject::for_resource(piece),
                        )
                        .into());
                }
            }
        }
    }
    Ok(state
        .with_borrow_ledger(Some(ledger))
        .with_borrow_participant(Some(participant))
        .with_borrow_bindings(bindings))
}

/// Produces the exact callee entry state used by contract verification.
///
/// Composite requirements normally use their canonical contained resources.
/// When proof execution has explicitly observed or unfolded part of a recursive
/// resource, independent certification preserves that equivalent form so
/// both executions use the same boundary state.
pub fn program_function_contract_entry_state(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
) -> Result<ExecutionState, String> {
    program_function_contract_entry_state_with_refusal(
        caller_state,
        function,
        arguments,
        assumptions,
    )
    .map_err(ContractEntryRefusal::into_message)
}

pub(crate) fn program_function_contract_entry_state_with_refusal(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
) -> Result<ExecutionState, ContractEntryRefusal> {
    let values = arguments
        .iter()
        .map(|argument| match argument {
            ProgramExpression::Value(value) => Some(value.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()
        .ok_or_else(|| {
            ContractEntryRefusal::Internal(
                "contract entry arguments must be concrete symbolic values".into(),
            )
        })?;
    let mut budget = ExecutionBudget::beside_live_state();
    match prepare_function_contract_entry_state_with_values(
        caller_state,
        function,
        &values,
        assumptions,
        &mut budget,
    ) {
        Ok(Ok(state)) => Ok(state),
        Ok(Err(error)) => Err(ContractEntryRefusal::from_resource_error(
            "could not prepare contract resources",
            &error,
        )),
        Err(limit) => Err(ContractEntryRefusal::from_limit(
            "could not prepare contract resources",
            limit,
        )),
    }
}

/// Whether a body outcome establishes every resource the contract returns,
/// by the rule contract certification applies to a `produces` claim. A proof
/// consults this before reading the outcome through the contract's resource
/// transition, so the surface accepts exactly the exits certification does.
pub fn program_function_return_resources_definitionally_established(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    outcome: &FunctionOutcome,
    assumptions: &PureFactContext,
) -> bool {
    crate::instrumentation::measure_operation(
        "kernel",
        "return resources",
        "return resources: definitional check",
        || {
            function_return_resources_definitionally_established(
                caller_state,
                function,
                arguments,
                outcome,
                assumptions,
                None,
            )
        },
    )
}

/// Applies a function's already-checked resource effect to a concrete body
/// outcome. This changes only the contract-level resource/population state;
/// the C value and memory come from the supplied body execution.
pub fn apply_program_function_contract_resource_transition(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    outcome: FunctionOutcome,
    assumptions: &PureFactContext,
) -> Result<(FunctionOutcome, Vec<ProofObligation>), String> {
    match apply_verified_contract_resource_transition(
        caller_state,
        function,
        arguments,
        outcome,
        assumptions,
        &mut ExecutionBudget::beside_live_state(),
    ) {
        Ok(Ok(result)) => Ok(result),
        Ok(Err(error)) => Err(format!(
            "contract resource transition failed: {}",
            super::api::contract_certification::describe_certification_runtime_error(&error)
        )),
        Err(limit) => Err(format!(
            "contract resource transition stopped at {}",
            limit.describe()
        )),
    }
}

/// Commits a proposed return-resource exchange only after its verification
/// conditions have been established in the supplied checked context. The
/// proposal API above also serves callers that retain explicit obligations.
/// Prepares the count interpretation used to prove a function's return
/// resource invariants, without transferring the body's ownership. This
/// creates no theorem or invariant facts: the eventual specification must
/// still be certified against the checked exit outcome. In particular callers
/// must not project resource invariant facts from this provisional state.
pub(crate) fn function_body_with_return_counts(
    body: &FunctionOutcome,
    checked_exit: &FunctionOutcome,
) -> FunctionOutcome {
    match (body, checked_exit) {
        (
            FunctionOutcome::Return { value, state },
            FunctionOutcome::Return {
                state: exit_state, ..
            },
        ) => {
            let mut state = state.clone();
            state.observed_population_families = exit_state.observed_population_families.clone();
            FunctionOutcome::Return {
                value: value.clone(),
                state,
            }
        }
        _ => body.clone(),
    }
}

/// Applies a kernel-checked, zero-source construction of one abstract token
/// to a function outcome state.
pub fn construct_program_function_resource(
    state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    result: &ProgramValue,
    constructed: &ResourceFact,
    assumptions: &PureFactContext,
) -> Result<ExecutionState, String> {
    match construct_c_function_resource_checked(
        state,
        function,
        arguments,
        result,
        constructed,
        assumptions,
    ) {
        Ok(Ok(state)) => Ok(state),
        Ok(Err(error)) => Err(format!(
            "resource construction failed: {}",
            super::api::contract_certification::describe_certification_runtime_error(&error)
        )),
        Err(limit) => Err(format!(
            "resource construction stopped at {}",
            limit.describe()
        )),
    }
}

pub fn program_function_outcome_from_statement_outcome(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    outcome: StatementOutcome,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> (FunctionOutcome, Vec<ProofObligation>) {
    let (outcome, obligations) = function_outcome_from_body(
        caller_state,
        function,
        outcome,
        obligations,
        assumptions,
        None,
    );
    (
        crate::kernel::functions::exit_with_unheld_produced_binders_adopted(
            function,
            outcome,
            assumptions,
        ),
        obligations,
    )
}

/// Applies the ordinary function-exit transition, splitting only the
/// transition boundary when a conditional resource effect is undecided. The
/// C body is not executed again: each returned case reuses the supplied statement
/// outcome and carries the guard facts that authorized its boundary check.
pub(crate) fn program_function_outcomes_from_statement_outcome_with_resource_cases(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    outcome: StatementOutcome,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<(FunctionOutcome, Vec<ProofObligation>, Vec<Proposition>)> {
    let original_outcome = outcome.clone();
    let original_obligations = obligations.clone();
    let (outcome, obligations) = program_function_outcome_from_statement_outcome(
        caller_state,
        function,
        outcome,
        obligations,
        assumptions,
    );
    let FunctionOutcome::RuntimeError(error) = &outcome else {
        return vec![(outcome, obligations, Vec::new())];
    };
    if !crate::kernel::functions::is_deferred_conditional_resource_effect_error(error) {
        return vec![(outcome, obligations, Vec::new())];
    }
    let Some(cases) =
        contract_resource_condition_cases(caller_state, function, arguments, assumptions)
    else {
        return vec![(outcome, obligations, Vec::new())];
    };
    let mut resolved = Vec::new();
    for case in cases {
        let case_assumptions = assumptions_with_propositions(assumptions, &case);
        let (case_outcome, case_obligations) = program_function_outcome_from_statement_outcome(
            caller_state,
            function,
            original_outcome.clone(),
            original_obligations.clone(),
            &case_assumptions,
        );
        if !matches!(
            case_outcome,
            FunctionOutcome::RuntimeError(
                ref error
            ) if crate::kernel::functions::is_deferred_conditional_resource_effect_error(error)
        ) {
            resolved.push((case_outcome, case_obligations, case));
        }
    }
    if resolved.is_empty() {
        vec![(outcome, obligations, Vec::new())]
    } else {
        resolved
    }
}

#[cfg(test)]
pub fn program_function_specification(
    state: ExecutionState,
    arguments: Vec<ProgramExpression>,
    requires: Vec<Proposition>,
    outcome: FunctionOutcome,
) -> FunctionSpecification {
    FunctionSpecification::new(state, arguments, requires, outcome)
}

pub fn proposition_and(left: Proposition, right: Proposition) -> Proposition {
    Proposition::And(Box::new(left), Box::new(right))
}

pub fn proposition_and_all(mut propositions: Vec<Proposition>) -> Proposition {
    if propositions.is_empty() {
        return Proposition::condition_is(OldConditionTerm::Constant(true), true);
    }
    while propositions.len() > 1 {
        let mut next = Vec::with_capacity(propositions.len().div_ceil(2));
        let mut pairs = propositions.into_iter();
        while let Some(left) = pairs.next() {
            next.push(match pairs.next() {
                Some(right) => proposition_and(left, right),
                None => left,
            });
        }
        propositions = next;
    }
    propositions.pop().expect("nonempty conjunction level")
}

pub fn substitute_int32_variable_in_proposition(
    proposition: &Proposition,
    variable: Variable,
    value: OldMachineTerm,
) -> Proposition {
    substitute_bitvector_variable_in_proposition(proposition, variable, &value)
}

/// Planning evidence for certificate lowering: the guided instantiation
/// values the atomic prover would try for one universally quantified int32
/// fact against a target condition fact, plus every value of a
/// constant-bounded binder range. Simple check never calls this; the
/// selected value is recorded explicitly in the emitted certificate.
pub fn forall_instantiation_candidate_values(
    quantified: &Proposition,
    target: &Proposition,
) -> Vec<OldMachineTerm> {
    let Proposition::ForAll { var, body, .. } = quantified else {
        return Vec::new();
    };
    let mut candidates = match target {
        Proposition::ConditionIs(condition, _) => {
            PureFactContext::guided_forall_condition_candidates(**var, body, condition.old_form())
        }
        _ => BTreeSet::new(),
    };
    let variables = vec![**var];
    if let Some(ranges) = crate::kernel::reasoning::finite_forall_ranges(&variables, body)
        && let [range] = ranges.as_slice()
        && let Ok(width) = usize::try_from(range.upper - range.lower + 1)
    {
        crate::instrumentation::record_deterministic_work(width);
        for value in range.lower..=range.upper {
            candidates.insert(range.constant(value));
        }
    }
    candidates.into_iter().collect()
}

/// Returns only target-guided universal-instantiation values.
///
/// Unlike [`forall_instantiation_candidate_values`], this query does not
/// enumerate or solve the quantified body's finite range. Proof-object smart
/// search uses it while probing indexed universals so an irrelevant retained
/// range cannot trigger project-scale reasoning before a candidate is known
/// to match the focused atomic goal.
pub fn forall_guided_instantiation_candidate_values(
    quantified: &Proposition,
    target: &Proposition,
) -> Vec<OldMachineTerm> {
    let Proposition::ForAll {
        var, sort, body, ..
    } = quantified
    else {
        return Vec::new();
    };
    match target {
        Proposition::ConditionIs(condition, _) => {
            PureFactContext::guided_forall_condition_candidates(**var, body, condition.old_form())
                .into_iter()
                .collect()
        }
        Proposition::MemoryReadDefined {
            pointer,
            value_type: ProgramType::UInt8,
            ..
        } if *sort == Sort::ProgramInteger(MachineIntegerType::UInt64) => {
            let mut conclusion = body.as_ref();
            while let Proposition::Implies(_, next) = conclusion {
                crate::instrumentation::record_deterministic_work(1);
                conclusion = next;
            }
            if let Proposition::MemoryReadDefined {
                pointer: pattern,
                value_type: ProgramType::UInt8,
                ..
            } = conclusion
                && let Some(index) = guided_byte_read_index(**var, pattern, pointer)
            {
                return vec![index];
            }
            Vec::new()
        }
        _ => Vec::new(),
    }
}

/// Select the index already named by a byte-read goal. The ordinary
/// instantiation and closing tactic still check the guards and read point.
fn guided_byte_read_index(
    binder: Variable,
    pattern: &Address,
    pointer: &Address,
) -> Option<OldMachineTerm> {
    crate::instrumentation::record_deterministic_work(1);
    let (base_offset, index_offset) = match pattern.offset.view() {
        OffsetView::Add(base, index) => (base.clone(), index),
        _ => (AddressOffset::constant(0), &pattern.offset),
    };
    let OffsetView::Int64Scaled {
        index: value,
        byte_width: 1,
        unsigned: true,
    } = index_offset.view()
    else {
        return None;
    };
    if value.operand_view().variable() != Some(&binder) {
        return None;
    }
    let base = pattern.with_offset(base_offset);
    let index = pointer.shared_wide_element_index_from_base(&base, 1)?;
    let index = index.operand_view();
    index
        .variable()
        .copied()
        .map(OldMachineTerm::Variable)
        .or_else(|| index.uint64_constant().map(OldMachineTerm::uint64_constant))
}

/// Chooses a variable identity absent from both the free variables and logical
/// binders of the supplied propositions, and from `also_reserved`.
pub fn fresh_int32_variable_for_propositions(
    propositions: &[Proposition],
    also_reserved: &[Variable],
) -> Variable {
    let mut reserved = also_reserved.iter().copied().collect::<BTreeSet<_>>();
    for proposition in propositions {
        reserved.extend(proposition_variables(proposition));
    }
    KernelVariableGenerator::fresh_for(0, reserved).next()
}

/// Collects every free variable and logical binder identity in one
/// proposition. Proof facts retain this set incrementally so freshness checks
/// do not rebuild the entire ambient fact list for each universal intro.
pub(crate) fn proposition_variables(proposition: &Proposition) -> BTreeSet<Variable> {
    let mut variables = BTreeSet::new();
    collect_proposition_bitvector_variables(proposition, &mut variables);
    collect_proposition_bound_variables(proposition, &mut variables);
    variables
}

#[cfg(test)]
pub fn program_max_body() -> ProgramStatement {
    program_if(
        crate::kernel::program_expression::less_than(
            crate::kernel::program_expression::variable("a"),
            crate::kernel::program_expression::variable("b"),
        ),
        program_return(crate::kernel::program_expression::variable("b")),
        program_return(crate::kernel::program_expression::variable("a")),
    )
}

#[cfg(test)]
pub fn program_max_function() -> ProgramFunction {
    program_function(
        ProgramType::Int32,
        "max",
        vec![
            program_parameter("a", ProgramType::Int32),
            program_parameter("b", ProgramType::Int32),
        ],
        program_max_body(),
    )
}

#[cfg(test)]
pub fn program_max_state(a: ProgramValue, b: ProgramValue) -> ExecutionState {
    ExecutionState::new().with_local("a", a).with_local("b", b)
}

#[cfg(test)]
pub fn program_max_lt_condition(a: OldMachineTerm, b: OldMachineTerm) -> OldConditionTerm {
    OldConditionTerm::signed_less_than(a, b)
}

#[cfg(test)]
pub fn prove_program_expression_evaluation(
    state: ExecutionState,
    expression: ProgramExpression,
) -> Option<Theorem> {
    let mut budget = ExecutionBudget::for_new_execution().with_program_expression_cost(&expression);
    let mut paths = super::eval::evaluate_expression_value_paths(
        &state,
        &expression,
        &PureFactContext::new(),
        &mut budget,
    )
    .ok()?
    .into_iter();
    let path = paths.next()?;
    if paths.next().is_some() || !path.obligations.is_empty() {
        return None;
    }
    let outcome = path.outcome;
    Some(Theorem::new(Proposition::ProgramExpressionEvaluates {
        state: Box::new(state),
        expression,
        outcome: outcome.map_value(Into::into),
    }))
}

pub fn prove_symbolic_program_condition_evaluation(
    state: ExecutionState,
    condition: ProgramExpression,
    assumptions: PureFactContext,
) -> SymbolicConditionEvaluation {
    let mut budget = ExecutionBudget::beside_live_state().with_program_expression_cost(&condition);
    let expression_paths =
        match evaluate_program_condition_paths(&state, &condition, &assumptions, &mut budget) {
            Ok(paths) => paths,
            Err(limit) => {
                return SymbolicConditionEvaluation {
                    paths: Vec::new(),
                    limit: Some(limit),
                };
            }
        };
    let mut outcomes = Vec::new();
    for path in expression_paths {
        match path.outcome {
            ExpressionOutcome::Value(value) => {
                outcomes.extend(
                    program_truthiness_paths(value, path.facts, path.obligations, &assumptions)
                        .into_iter()
                        .map(|path| {
                            (
                                ConditionOutcome::Value(path.is_true),
                                path.facts,
                                path.obligations,
                            )
                        }),
                );
            }
            ExpressionOutcome::UndefinedBehavior(kind) => outcomes.push((
                ConditionOutcome::UndefinedBehavior(kind),
                path.facts,
                path.obligations,
            )),
            ExpressionOutcome::RuntimeError(error) => outcomes.push((
                ConditionOutcome::RuntimeError(error),
                path.facts,
                path.obligations,
            )),
        }
    }
    let _timing =
        crate::instrumentation::OperationTiming::new("", "", "C condition theorem construction");
    let paths = outcomes
        .into_iter()
        .map(|(outcome, facts, obligations)| {
            crate::instrumentation::record_deterministic_work(1);
            let facts = public_execution_pure_facts(&facts);
            let proposition = Proposition::ProgramConditionEvaluates {
                state: Box::new(state.clone()),
                condition: condition.clone(),
                outcome: outcome.clone(),
            };
            let theorem = Theorem::with_ambient_premises(
                crate::kernel::reasoning::path_facts::wrap_local_proof_facts(
                    proposition,
                    &facts,
                    &obligations,
                ),
                &assumptions,
            );
            SymbolicConditionEvaluationPath {
                outcome,
                facts,
                obligations,
                theorem,
            }
        })
        .collect();

    SymbolicConditionEvaluation { paths, limit: None }
}

#[cfg(test)]
pub fn prove_execution_statement_execution(
    state: ExecutionState,
    statement: ProgramStatement,
) -> Option<Theorem> {
    prove_symbolic_program_execution(state, statement, PureFactContext::new())
}

#[cfg(test)]
pub fn prove_symbolic_program_execution(
    state: ExecutionState,
    statement: ProgramStatement,
    assumptions: PureFactContext,
) -> Option<Theorem> {
    let budget = ExecutionBudget::for_new_execution().with_execution_statement_cost(&statement);
    prove_symbolic_program_execution_with_budget(state, statement, assumptions, budget)
}

#[cfg(test)]
pub fn prove_symbolic_program_execution_with_budget(
    state: ExecutionState,
    statement: ProgramStatement,
    assumptions: PureFactContext,
    budget: ExecutionBudget,
) -> Option<Theorem> {
    prove_symbolic_program_execution_with_environment_and_budget(
        state,
        statement,
        assumptions,
        ExecutionEnvironment::new(),
        ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        budget,
    )
}

#[cfg(test)]
pub fn prove_symbolic_program_execution_with_environment(
    state: ExecutionState,
    statement: ProgramStatement,
    assumptions: PureFactContext,
    environment: ExecutionEnvironment,
    execution_semantics: ExecutionSemantics,
) -> Option<Theorem> {
    let budget = ExecutionBudget::for_new_execution().with_execution_statement_cost(&statement);
    prove_symbolic_program_execution_with_environment_and_budget(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
        budget,
    )
}

#[cfg(test)]
pub fn prove_symbolic_program_execution_with_environment_and_budget(
    state: ExecutionState,
    statement: ProgramStatement,
    assumptions: PureFactContext,
    environment: ExecutionEnvironment,
    execution_semantics: ExecutionSemantics,
    budget: ExecutionBudget,
) -> Option<Theorem> {
    let execution = prove_symbolic_program_execution_paths_with_environment_and_budget(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
        budget,
    );
    if execution.limit().is_some() {
        return None;
    }
    let mut paths = execution.paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() {
        return None;
    }
    Some(path.theorem)
}

#[cfg(test)]
pub fn prove_symbolic_program_execution_paths(
    state: ExecutionState,
    statement: ProgramStatement,
    assumptions: PureFactContext,
) -> SymbolicExecution {
    let budget = ExecutionBudget::for_new_execution().with_execution_statement_cost(&statement);
    prove_symbolic_program_execution_paths_with_budget(state, statement, assumptions, budget)
}

#[cfg(test)]
pub fn prove_symbolic_program_execution_paths_with_budget(
    state: ExecutionState,
    statement: ProgramStatement,
    assumptions: PureFactContext,
    budget: ExecutionBudget,
) -> SymbolicExecution {
    prove_symbolic_program_execution_paths_with_environment_and_budget(
        state,
        statement,
        assumptions,
        ExecutionEnvironment::new(),
        ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        budget,
    )
}

#[cfg(test)]
pub fn prove_symbolic_program_execution_paths_with_environment(
    state: ExecutionState,
    statement: ProgramStatement,
    assumptions: PureFactContext,
    environment: ExecutionEnvironment,
    execution_semantics: ExecutionSemantics,
) -> SymbolicExecution {
    let budget = ExecutionBudget::for_new_execution().with_execution_statement_cost(&statement);
    prove_symbolic_program_execution_paths_with_environment_and_budget(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
        budget,
    )
}

#[cfg(test)]
pub fn prove_symbolic_program_execution_paths_with_environment_and_budget(
    state: ExecutionState,
    statement: ProgramStatement,
    assumptions: PureFactContext,
    environment: ExecutionEnvironment,
    execution_semantics: ExecutionSemantics,
    mut budget: ExecutionBudget,
) -> SymbolicExecution {
    let paths = match execute_execution_statement_paths(
        &state,
        &statement,
        &assumptions,
        ExecutionContext::new(&environment, execution_semantics),
        &mut budget,
    ) {
        Ok(paths) => paths,
        Err(limit) => {
            return SymbolicExecution {
                paths: Vec::new(),
                limit: Some(limit),
            };
        }
    };
    let paths = paths
        .into_iter()
        .map(|path| {
            let effect_facts = memory_effect_execution_facts(&path.facts);
            let facts = public_execution_pure_facts(&path.facts);
            // Calls apply their callees' verified rules, which describe a
            // returning callee only, so the outcome is a verification
            // transition rather than a concretely reachable execution.
            let proposition = Proposition::ProgramStatementVerifies {
                state: Box::new(state.clone()),
                statement: Box::new(statement.clone()),
                outcome: path.outcome,
            };
            let theorem = Theorem::new(wrap_proof_facts(
                proposition,
                &assumptions,
                &facts,
                &path.obligations,
            ));
            SymbolicExecutionPath {
                descent_step: None,
                completion_origin: None,
                call_result: path.call_result,
                assumptions: assumptions.clone(),
                post_assumptions: None,
                facts,
                effect_facts,
                obligations: path.obligations,
                theorem,
                borrow_evidence: path.borrow_evidence,
            }
        })
        .collect();

    SymbolicExecution { paths, limit: None }
}

#[cfg(test)]
pub fn prove_symbolic_execution_statement_verification_paths_with_environment(
    state: ExecutionState,
    statement: ProgramStatement,
    assumptions: PureFactContext,
    environment: ExecutionEnvironment,
    execution_semantics: ExecutionSemantics,
) -> SymbolicExecution {
    prove_symbolic_execution_statement_verification_paths_with_environment_and_loop_rule(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
    )
    .0
}

#[cfg(test)]
pub fn prove_symbolic_execution_statement_verification_paths_with_environment_and_loop_rule(
    state: ExecutionState,
    statement: ProgramStatement,
    assumptions: PureFactContext,
    environment: ExecutionEnvironment,
    execution_semantics: ExecutionSemantics,
) -> (SymbolicExecution, Option<VerifiedLoopRule>) {
    let mut budget = ExecutionBudget::for_new_execution().with_execution_statement_cost(&statement);
    prove_symbolic_execution_statement_verification_paths_with_environment_and_loop_rule_using_budget(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
        &mut budget,
    )
}

fn statement_kernel_variables<'scope>(
    state: &'scope ExecutionState,
    statement: &'scope ProgramStatement,
    assumptions: &PureFactContext,
    environment: &ExecutionEnvironment,
    next_candidate: u64,
) -> KernelVariableGenerator<'scope> {
    let fact_bound = assumptions.execution_variable_ceiling();
    KernelVariableGenerator::fresh_for_execution_with_deferred_reservations(
        move || {
            let mut existing = BTreeSet::new();
            crate::instrumentation::measure_operation(
                "",
                "",
                "statement state reservation",
                || {
                    collect_execution_state_reservations(
                        state,
                        next_candidate,
                        fact_bound,
                        &mut existing,
                    );
                },
            );
            collect_execution_statement_bitvector_variables(statement, &mut existing);
            existing
        },
        execution_environment_variable_index(environment),
    )
    .reserving_through(fact_bound)
}

pub(crate) fn prove_symbolic_execution_statement_verification_paths_with_environment_and_loop_rule_using_budget(
    state: ExecutionState,
    statement: impl Into<crate::kernel::StatementProofInput>,
    assumptions: PureFactContext,
    environment: ExecutionEnvironment,
    execution_semantics: ExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> (SymbolicExecution, Option<VerifiedLoopRule>) {
    let crate::kernel::StatementProofInput {
        statement,
        loop_evidence,
    } = statement.into();
    let loop_evidence =
        loop_evidence.map(|evidence| evidence.executed_under(execution_semantics.loops));
    let mut variables = statement_kernel_variables(
        &state,
        &statement,
        &assumptions,
        &environment,
        budget.next_kernel_variable,
    );
    let execution = execute_execution_statement_verification_paths(
        &state,
        &statement,
        &assumptions,
        ExecutionContext::new(&environment, execution_semantics),
        budget,
        &mut variables,
    );
    drop(variables);
    let paths = match execution {
        Ok(paths) => paths,
        Err(limit) => {
            return (
                SymbolicExecution {
                    paths: Vec::new(),
                    limit: Some(limit),
                },
                None,
            );
        }
    };
    symbolic_execution_statement_execution_with_loop_rule(
        state,
        statement,
        assumptions,
        paths,
        &environment,
        loop_evidence,
    )
}

#[cfg(test)]
pub(crate) fn prove_symbolic_loop_exit_with_proven_phases(
    state: ExecutionState,
    statement: ProgramStatement,
    assumptions: PureFactContext,
    environment: ExecutionEnvironment,
    initialization_proven: bool,
    preservation_proven: bool,
    final_exit_candidates: Vec<LoopFinalExitCandidate>,
    early_exits: Vec<LoopEarlyExit>,
    return_exits: Vec<LoopReturnExit>,
) -> (SymbolicExecution, Option<VerifiedLoopRule>) {
    let mut budget = ExecutionBudget::for_new_execution().with_execution_statement_cost(&statement);
    prove_symbolic_loop_exit_with_proven_phases_using_budget(
        state,
        statement,
        assumptions,
        environment,
        initialization_proven,
        preservation_proven,
        final_exit_candidates,
        early_exits,
        return_exits,
        &[],
        None,
        None,
        &mut budget,
    )
}

/// Checks an explicit proof at the false-guard frontier. The caller gets
/// that frontier's checked facts and the caller's record index for a unique
/// checked false-guard path, if available. It returns the facts its proof added.
pub(crate) type LoopOtherwiseProof<'a> = dyn FnMut(
        &ExecutionState,
        &ExecutionState,
        &ExecutionFacts,
        Option<usize>,
    ) -> Option<ExecutionFacts>
    + 'a;

/// Checks the source interface for a loop join. The mask selects checked
/// common facts in producer order. Written exports are checked in every
/// concrete predecessor and returned in terms of the abstract successor.
pub(crate) type LoopExitFactScope<'a> = dyn Fn(
        &ExecutionState,
        &IntegerTerm,
        &[(ExecutionState, ExecutionFacts)],
        &ExecutionFacts,
    ) -> (Vec<bool>, Vec<Proposition>)
    + 'a;

pub(crate) fn prove_symbolic_loop_exit_with_proven_phases_using_budget(
    state: ExecutionState,
    statement: impl Into<crate::kernel::StatementProofInput>,
    assumptions: PureFactContext,
    environment: ExecutionEnvironment,
    initialization_proven: bool,
    preservation_proven: bool,
    final_exit_candidates: Vec<LoopFinalExitCandidate>,
    early_exits: Vec<LoopEarlyExit>,
    return_exits: Vec<LoopReturnExit>,
    back_edges: &[LoopBackEdges],
    otherwise: Option<&mut LoopOtherwiseProof<'_>>,
    exit_fact_scope: Option<&LoopExitFactScope<'_>>,
    budget: &mut ExecutionBudget,
) -> (SymbolicExecution, Option<VerifiedLoopRule>) {
    let crate::kernel::StatementProofInput {
        statement,
        loop_evidence,
    } = statement.into();
    let loop_evidence =
        loop_evidence.map(|evidence| evidence.executed_under(LoopSemantics::ApplyVerifiedRules));
    let Some(program_loop) = crate::kernel::loops::LoopExecutionView::of(&statement) else {
        return (
            SymbolicExecution {
                paths: Vec::new(),
                limit: None,
            },
            None,
        );
    };
    let mut variables = statement_kernel_variables(
        &state,
        &statement,
        &assumptions,
        &environment,
        budget.next_kernel_variable,
    );
    let execution = execute_program_loop_exit_paths_with_proven_phases(
        &state,
        program_loop,
        &assumptions,
        ExecutionContext::apply_verified_rules(&environment),
        initialization_proven,
        preservation_proven,
        &final_exit_candidates,
        &early_exits,
        &return_exits,
        back_edges,
        otherwise,
        exit_fact_scope,
        budget,
        &mut variables,
    );
    drop(variables);
    let paths = match execution {
        Ok(paths) => paths,
        Err(limit) => {
            return (
                SymbolicExecution {
                    paths: Vec::new(),
                    limit: Some(limit),
                },
                None,
            );
        }
    };
    symbolic_execution_statement_execution_with_loop_rule(
        state,
        statement,
        assumptions,
        paths,
        &environment,
        loop_evidence,
    )
}

fn symbolic_execution_statement_execution_with_loop_rule(
    state: ExecutionState,
    statement: ProgramStatement,
    assumptions: PureFactContext,
    paths: Vec<StatementExecutionPath>,
    environment: &ExecutionEnvironment,
    loop_evidence: Option<crate::kernel::termination::loop_evidence::LoopEvidence>,
) -> (SymbolicExecution, Option<VerifiedLoopRule>) {
    // A rule's paths are the loop statement's successors: the joined exit,
    // a proven-divergent loop, each checked forward jump, and each
    // `return` the body reaches. A returned
    // path leaves the function from inside the loop; the rule carries it so
    // the enclosing execution continues with it as a returned path instead of
    // certifying the function on the exit path alone.
    let loop_rule = (matches!(statement, ProgramStatement::Loop { .. })
        && paths.iter().all(|path| {
            (matches!(
                path.outcome,
                StatementOutcome::Normal(_)
                    | StatementOutcome::Return { .. }
                    | StatementOutcome::VerificationDiverges
            ) || matches!(
                (&statement, &path.outcome),
                (
                    ProgramStatement::Loop {
                        backedge_target: None,
                        ..
                    },
                    StatementOutcome::Jump { .. }
                )
            ) || matches!(
                (&statement, &path.outcome),
                (ProgramStatement::Loop {
                    backedge_target: Some(_),
                    natural_exit_target: Some(exit_target),
                    ..
                }, StatementOutcome::Jump { target, .. }) if target == exit_target
            )) && path
                .obligations
                .iter()
                .all(|obligation| obligation.is_assumable() || obligation.statement_entry_required)
        }))
    .then(|| VerifiedLoopRule {
        symbolic_entry_state: state.clone(),
        loop_statement: statement.clone(),
        loop_evidence,
        required_assumptions: assumptions.clone(),
        paths: paths.clone(),
        composite_resource_definitions: Default::default(),
        // The rule records the anchor its own body was stepped under. A
        // self-call in that body raised the descent obligations exactly when
        // this is set. Every body obligation has already been discharged
        // or was assumable. The application still owes any retained
        // statement-entry conditions.
        recursion_anchor: environment.recursion_anchor_handle(),
        variable_index: Default::default(),
    });
    let paths = paths
        .into_iter()
        .map(|path| {
            let effect_facts = memory_effect_execution_facts(&path.facts);
            let facts = public_execution_pure_facts(&path.facts);
            let proposition = Proposition::ProgramStatementVerifies {
                state: Box::new(state.clone()),
                statement: Box::new(statement.clone()),
                outcome: path.outcome,
            };
            // The theorem carries the path's own facts and obligations. The
            // context it executed under travels beside it as `assumptions`
            // and is recorded with it; copying every context fact into the
            // theorem as a premise cost a clone of the whole context per
            // step, and the premises were then only looked up again in the
            // same context (`roadmap/scaling.md` cause 4).
            let theorem = Theorem::new(wrap_proof_facts(
                proposition,
                &PureFactContext::new(),
                &facts,
                &path.obligations,
            ));
            SymbolicExecutionPath {
                descent_step: crate::kernel::DescentStep::under_state(environment, &state),
                completion_origin: None,
                call_result: path.call_result,
                assumptions: assumptions.clone(),
                post_assumptions: None,
                facts,
                effect_facts,
                obligations: path.obligations,
                theorem,
                borrow_evidence: path.borrow_evidence,
            }
        })
        .collect();

    (SymbolicExecution { paths, limit: None }, loop_rule)
}

pub fn prove_symbolic_program_function_execution(
    state: ExecutionState,
    function: ProgramFunction,
    arguments: Vec<ProgramExpression>,
    assumptions: PureFactContext,
) -> Option<Theorem> {
    let budget =
        ExecutionBudget::for_new_execution().with_program_function_cost(&function, &arguments);
    prove_symbolic_program_function_execution_with_budget(
        state,
        function,
        arguments,
        assumptions,
        budget,
    )
}

pub fn prove_symbolic_program_function_execution_with_budget(
    state: ExecutionState,
    function: ProgramFunction,
    arguments: Vec<ProgramExpression>,
    assumptions: PureFactContext,
    budget: ExecutionBudget,
) -> Option<Theorem> {
    prove_symbolic_program_function_execution_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        ExecutionEnvironment::new(),
        ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        budget,
    )
}

#[cfg(test)]
pub fn prove_symbolic_program_function_execution_with_environment(
    state: ExecutionState,
    function: ProgramFunction,
    arguments: Vec<ProgramExpression>,
    assumptions: PureFactContext,
    environment: ExecutionEnvironment,
    execution_semantics: ExecutionSemantics,
) -> Option<Theorem> {
    let budget =
        ExecutionBudget::for_new_execution().with_program_function_cost(&function, &arguments);
    prove_symbolic_program_function_execution_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
    )
}

pub fn prove_symbolic_program_function_execution_with_environment_and_budget(
    state: ExecutionState,
    function: ProgramFunction,
    arguments: Vec<ProgramExpression>,
    assumptions: PureFactContext,
    environment: ExecutionEnvironment,
    execution_semantics: ExecutionSemantics,
    budget: ExecutionBudget,
) -> Option<Theorem> {
    let execution = prove_symbolic_program_function_execution_paths_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
    );
    if execution.limit().is_some() {
        return None;
    }
    let mut paths = execution.paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() {
        return None;
    }
    Some(path.theorem)
}

#[cfg(test)]
pub fn prove_symbolic_program_function_execution_paths(
    state: ExecutionState,
    function: ProgramFunction,
    arguments: Vec<ProgramExpression>,
    assumptions: PureFactContext,
) -> SymbolicExecution {
    let budget =
        ExecutionBudget::for_new_execution().with_program_function_cost(&function, &arguments);
    prove_symbolic_program_function_execution_paths_with_budget(
        state,
        function,
        arguments,
        assumptions,
        budget,
    )
}

#[cfg(test)]
pub fn prove_symbolic_program_function_execution_paths_with_budget(
    state: ExecutionState,
    function: ProgramFunction,
    arguments: Vec<ProgramExpression>,
    assumptions: PureFactContext,
    budget: ExecutionBudget,
) -> SymbolicExecution {
    prove_symbolic_program_function_execution_paths_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        ExecutionEnvironment::new(),
        ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        budget,
    )
}

#[cfg(test)]
pub fn prove_symbolic_program_function_execution_paths_with_environment(
    state: ExecutionState,
    function: ProgramFunction,
    arguments: Vec<ProgramExpression>,
    assumptions: PureFactContext,
    environment: ExecutionEnvironment,
    execution_semantics: ExecutionSemantics,
) -> SymbolicExecution {
    let budget =
        ExecutionBudget::for_new_execution().with_program_function_cost(&function, &arguments);
    prove_symbolic_program_function_execution_paths_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
    )
}

pub fn prove_symbolic_program_function_execution_paths_with_environment_and_budget(
    state: ExecutionState,
    function: ProgramFunction,
    arguments: Vec<ProgramExpression>,
    assumptions: PureFactContext,
    environment: ExecutionEnvironment,
    execution_semantics: ExecutionSemantics,
    budget: ExecutionBudget,
) -> SymbolicExecution {
    prove_symbolic_program_function_execution_paths_with_contract_resources(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
        false,
    )
}

fn function_has_conditional_resource_effect(function: &ProgramFunction) -> bool {
    function
        .resource_ensures()
        .iter()
        .any(|resource| resource.guard().is_some())
}

#[allow(clippy::too_many_arguments)]
fn prove_symbolic_program_function_execution_paths_with_contract_resources(
    state: ExecutionState,
    function: ProgramFunction,
    arguments: Vec<ProgramExpression>,
    assumptions: PureFactContext,
    environment: ExecutionEnvironment,
    execution_semantics: ExecutionSemantics,
    mut budget: ExecutionBudget,
    prepare_contract_resources: bool,
) -> SymbolicExecution {
    let defer_conditional_resource_effect = function_has_conditional_resource_effect(&function);
    let (state, arguments) =
        super::functions::prepare_external_aggregate_arguments(&state, &function, arguments);
    let paths = match execute_program_function_paths_with_contract_resources(
        &state,
        &function,
        &arguments,
        &assumptions,
        ExecutionContext::new(&environment, execution_semantics),
        &mut budget,
        prepare_contract_resources,
        defer_conditional_resource_effect,
    ) {
        Ok(paths) => paths,
        Err(limit) => {
            return SymbolicExecution {
                paths: Vec::new(),
                limit: Some(limit),
            };
        }
    };
    let paths = paths
        .into_iter()
        .map(|path| {
            let effect_facts = memory_effect_execution_facts(&path.facts);
            let facts = public_execution_pure_facts(&path.facts);
            // As for statements: applied callee rules make this a
            // verification transition.
            let proposition = Proposition::ProgramFunctionVerifies {
                state: Box::new(state.clone()),
                function: Box::new(function.clone()),
                arguments: arguments.clone(),
                outcome: path.outcome,
            };
            let theorem = Theorem::new(wrap_proof_facts(
                proposition,
                &assumptions,
                &facts,
                &path.obligations,
            ));
            SymbolicExecutionPath {
                descent_step: None,
                completion_origin: None,
                call_result: None,
                assumptions: assumptions.clone(),
                post_assumptions: None,
                facts,
                effect_facts,
                obligations: path.obligations,
                theorem,
                borrow_evidence: path.borrow_evidence,
            }
        })
        .collect();

    SymbolicExecution { paths, limit: None }
}

#[cfg(test)]
pub fn prove_symbolic_program_function_verification_paths_with_environment(
    state: ExecutionState,
    function: ProgramFunction,
    arguments: Vec<ProgramExpression>,
    assumptions: PureFactContext,
    environment: ExecutionEnvironment,
    execution_semantics: ExecutionSemantics,
) -> SymbolicExecution {
    let budget =
        ExecutionBudget::for_new_execution().with_program_function_cost(&function, &arguments);
    prove_symbolic_program_function_verification_paths_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
    )
}

#[cfg(test)]
pub fn prove_symbolic_program_function_verification_paths_with_environment_and_budget(
    state: ExecutionState,
    function: ProgramFunction,
    arguments: Vec<ProgramExpression>,
    assumptions: PureFactContext,
    environment: ExecutionEnvironment,
    execution_semantics: ExecutionSemantics,
    budget: ExecutionBudget,
) -> SymbolicExecution {
    prove_symbolic_program_function_verification_paths(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
        false,
        false,
    )
}

/// Executes one whole-function judgment and retains its exact authority inputs
/// together with the resulting frontier for later contract certification.
#[cfg(test)]
pub fn prove_checked_program_function_execution_with_environment(
    state: ExecutionState,
    function: ProgramFunction,
    arguments: Vec<ProgramExpression>,
    assumptions: PureFactContext,
    environment: ExecutionEnvironment,
    execution_semantics: ExecutionSemantics,
    mode: FunctionContractExecutionMode,
) -> CheckedFunctionExecution {
    record_checked_function_body_execution();
    let environment = if environment.has_conditional_resource_effects()
        || function_has_conditional_resource_effect(&function)
    {
        environment.with_conditional_resource_cases()
    } else {
        environment
    };
    let defer_conditional_resource_effect = function_has_conditional_resource_effect(&function);
    let execution = match mode {
        FunctionContractExecutionMode::VerifyLoops => {
            prove_symbolic_program_function_verification_paths(
                state.clone(),
                function.clone(),
                arguments.clone(),
                assumptions.clone(),
                environment.clone(),
                execution_semantics,
                ExecutionBudget::for_new_execution()
                    .with_program_function_cost(&function, &arguments),
                true,
                defer_conditional_resource_effect,
            )
        }
        FunctionContractExecutionMode::ExecuteLoops => {
            prove_symbolic_program_function_execution_paths_with_contract_resources(
                state.clone(),
                function.clone(),
                arguments.clone(),
                assumptions.clone(),
                environment.clone(),
                execution_semantics,
                ExecutionBudget::for_new_execution()
                    .with_program_function_cost(&function, &arguments),
                true,
            )
        }
    };
    let path_count = execution.paths().len();
    CheckedFunctionExecution {
        retained_descent: false,
        published_outcomes: Default::default(),
        contract_completion: None,
        entry_authority: None,
        closed_exit_obligations: vec![None; path_count],
        proof_candidates: None,
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        mode,
        execution,
        checked_resource_claims: vec![Vec::new(); path_count],
        checked_resource_transitions: vec![false; path_count],
        deferred_contract_exits: vec![false; path_count],
        deferred_contract_exit_errors: vec![None; path_count],
        // Empty certificate placeholders, replaced by checked clause contexts;
        // they never receive unchecked memory deltas or answer permission queries.
        entry_representation_origin: None,
        boundary_transfer: None,
        checked_call_events: Default::default(),
        checked_callees: None,
        applied_tactics: Default::default(),
    }
}

pub(in crate::kernel) fn proof_evidence_conclusion(theorem: &Theorem) -> &Proposition {
    theorem.execution_conclusion()
}

pub(in crate::kernel) fn proof_evidence_assumptions(
    theorem: &Theorem,
    base: &PureFactContext,
) -> PureFactContext {
    let mut assumptions = base.clone();
    let mut proposition = theorem.proposition();
    let mut premises = 0;
    while let Proposition::Implies(premise, body) = proposition {
        assumptions = assumptions.assume_proposition(premise.as_ref().clone());
        premises += 1;
        proposition = body;
    }
    crate::kernel::reasoning::path_facts::count_context_rebuild_entries(premises);
    assumptions
}

pub(crate) fn execution_evidence_states_match(
    function: &ProgramFunction,
    left: &ExecutionState,
    right: &ExecutionState,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    // Stable-view authority is semantic state, even though ordinary entry
    // rebasing is allowed to change the ghost resource representation.  Do
    // not let a checked execution cross a borrow root, holder, or occurrence
    // binding boundary while comparing the remaining representation.
    if !borrow_authority_states_match(left, right) {
        return false;
    }
    let mut left_without_ghost_difference = left.clone();
    left_without_ghost_difference.resources = right.resources.clone();
    left_without_ghost_difference.observed_population_families =
        right.observed_population_families.clone();
    left_without_ghost_difference == *right
        && contract_certification::resource_contexts_definitionally_equal_with_definitions(
            function.composite_resource_definitions(),
            &left.program_point(),
            left.resources(),
            &right.program_point(),
            right.resources(),
            assumptions,
        )
        && population_observations_equal(left, right)
}

/// Checks the representation-only state change permitted before the first C
/// operation. Resource scopes may materialize otherwise unchanged symbolic
/// loads, but cannot alter locals, local-object cells, heap lifetime state,
/// resource meaning, or population counts.
pub(crate) fn function_entry_representation_states_match(
    function: &ProgramFunction,
    left: &ExecutionState,
    right: &ExecutionState,
    assumptions: &PureFactContext,
) -> bool {
    borrow_authority_states_match(left, right)
        && left.locals == right.locals
        && left.memory.heap == right.memory.heap
        && left.local_cell_values().eq(right.local_cell_values())
        && memories_definitionally_equal(left.memory(), right.memory(), assumptions)
        && contract_certification::resource_contexts_definitionally_equal_with_definitions(
            function.composite_resource_definitions(),
            &left.program_point(),
            left.resources(),
            &right.program_point(),
            right.resources(),
            assumptions,
        )
        && population_observations_equal(left, right)
}

/// Compare the stable-view authority that cannot be reconstructed from a
/// resource representation.  Resource occurrences are opaque identities, so
/// equal-looking resource facts are insufficient when a checked artifact is
/// rebased onto another proof entry.
fn borrow_authority_states_match(left: &ExecutionState, right: &ExecutionState) -> bool {
    left.borrow_ledger() == right.borrow_ledger()
        && left.borrow_participant() == right.borrow_participant()
        && left.borrow_bindings() == right.borrow_bindings()
        && left.borrow_bindings_are_consistent()
        && right.borrow_bindings_are_consistent()
}

pub(in crate::kernel) fn proof_evidence_initial_state<'e>(
    events: impl IntoIterator<Item = &'e crate::kernel::proof::CheckedExecutionEvent>,
) -> Option<&'e ExecutionState> {
    use crate::kernel::proof::CheckedExecutionEvent;

    events.into_iter().find_map(|event| match event {
        CheckedExecutionEvent::ProofCase(_)
        | CheckedExecutionEvent::ReturnProposition(_)
        | CheckedExecutionEvent::Context(_)
        | CheckedExecutionEvent::CompletedContext(_)
        | CheckedExecutionEvent::StatementEffects(_)
        | CheckedExecutionEvent::Call(_)
        | CheckedExecutionEvent::LoopEntry { .. } => None,
        CheckedExecutionEvent::AutomaticLifetimeEnd(end) => Some(end.before_state()),
        CheckedExecutionEvent::ViewRelease(release) => Some(release.before_state()),
        CheckedExecutionEvent::ResourceObservation(observation) => Some(observation.before_state()),
        CheckedExecutionEvent::ResourceRewrite(rewrite) => Some(rewrite.before_state()),
        CheckedExecutionEvent::PopulationAuthorityRewrite(rewrite) => Some(rewrite.before_state()),
        CheckedExecutionEvent::PopulationMemberRewrite(rewrite) => Some(rewrite.before_state()),
        CheckedExecutionEvent::IteratedStep(step) => Some(step.before_state()),
        CheckedExecutionEvent::TacticApplication(application) => Some(application.before_state()),
        CheckedExecutionEvent::Statement(theorem) | CheckedExecutionEvent::Condition(theorem) => {
            match proof_evidence_conclusion(theorem) {
                Proposition::ProgramStatementVerifies { state, .. }
                | Proposition::ProgramConditionEvaluates { state, .. } => Some(state),
                _ => None,
            }
        }
        CheckedExecutionEvent::Branch(branch) => Some(branch.start_state()),
        CheckedExecutionEvent::ProofCaseJoin(join) => Some(join.start_state()),
    })
}

/// Every proof-case arm in the traces must be valid, a path may pass
/// through one partition once, and every constructor must be represented
/// by a retained trace or a kernel-checked contradiction in its partition.
/// The arms' own facts are what the
/// proof object assumes on each path; no restatement of the cases from outside
/// the traces is consulted.
pub(in crate::kernel) fn proof_case_partitions_are_exhaustive(
    evidence: &[crate::kernel::proof::ExecutionEvidence],
) -> bool {
    use crate::kernel::proof::CheckedExecutionEvent;

    fn collect<'e>(
        events: impl IntoIterator<Item = &'e CheckedExecutionEvent>,
        covered: &mut std::collections::BTreeMap<usize, Vec<bool>>,
        path_partitions: &mut std::collections::BTreeSet<usize>,
    ) -> bool {
        for event in events {
            match event {
                CheckedExecutionEvent::ProofCase(arm) => {
                    if !arm.is_valid() || !path_partitions.insert(arm.identity()) {
                        return false;
                    }
                    covered
                        .entry(arm.identity())
                        .or_insert_with(|| arm.excluded_cases())[arm.arm_index()] = true;
                }
                CheckedExecutionEvent::Branch(branch) => {
                    for arm_index in 0..2 {
                        let mut nested_partitions = std::collections::BTreeSet::new();
                        if !collect(
                            branch.arm_events(arm_index),
                            covered,
                            &mut nested_partitions,
                        ) {
                            return false;
                        }
                    }
                }
                // Each live arm begins with its own `ProofCase` event, so
                // walking the arms records the joined partition's coverage
                // like any other; the arms are sibling paths.
                CheckedExecutionEvent::ProofCaseJoin(join) => {
                    for events in join.live_arm_events() {
                        let mut nested_partitions = std::collections::BTreeSet::new();
                        if !collect(events, covered, &mut nested_partitions) {
                            return false;
                        }
                    }
                }
                CheckedExecutionEvent::Statement(_)
                | CheckedExecutionEvent::LoopEntry { .. }
                | CheckedExecutionEvent::Call(_)
                | CheckedExecutionEvent::Condition(_)
                | CheckedExecutionEvent::ReturnProposition(_)
                | CheckedExecutionEvent::Context(_)
                | CheckedExecutionEvent::CompletedContext(_)
                | CheckedExecutionEvent::StatementEffects(_)
                | CheckedExecutionEvent::AutomaticLifetimeEnd(_)
                | CheckedExecutionEvent::ViewRelease(_)
                | CheckedExecutionEvent::ResourceObservation(_)
                | CheckedExecutionEvent::ResourceRewrite(_)
                | CheckedExecutionEvent::PopulationAuthorityRewrite(_)
                | CheckedExecutionEvent::PopulationMemberRewrite(_)
                | CheckedExecutionEvent::IteratedStep(_)
                | CheckedExecutionEvent::TacticApplication(_) => {}
            }
        }
        true
    }

    let mut covered = std::collections::BTreeMap::new();
    for trace in evidence {
        let mut path_partitions = std::collections::BTreeSet::new();
        if !collect(trace.iter(), &mut covered, &mut path_partitions) {
            return false;
        }
    }
    covered
        .values()
        .all(|arms| !arms.is_empty() && arms.iter().all(|covered| *covered))
}

#[cfg(test)]
mod proof_case_evidence_tests {
    use super::*;
    use crate::kernel::proof::{
        CheckedProofCasePartition, ExecutionFrontier, ExecutionProofCore, OutcomeEvidenceFork,
        OutcomeForkArm, PureFactStore,
    };

    fn case_partition(
        root: &PureFactStore,
    ) -> (Arc<CheckedProofCasePartition>, Proposition, Proposition) {
        let then_fact = Proposition::Predicate {
            name: "case".to_string(),
            arguments: Vec::new(),
        };
        let else_fact = Proposition::Not(Box::new(then_fact.clone()));
        let partition =
            CheckedProofCasePartition::check(root, then_fact.clone(), else_fact.clone())
                .expect("complementary facts should create a checked partition");
        (partition, then_fact, else_fact)
    }

    #[test]
    fn branch_memory_delta_uses_the_full_changed_cell_width() {
        let pointer = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
        let escrow = ResourceFact::own_memory(MemoryRange::new(
            pointer.clone(),
            OldMachineTerm::constant(0),
            OldMachineTerm::constant(1),
        ));
        let support = ResourceContext::new()
            .unchecked_with_fact(escrow.clone())
            .unique_owned_occurrence_for_fact(&escrow)
            .expect("the test escrow has one backing occurrence")
            .0;
        let ledger = crate::kernel::borrows::BorrowLedger::new();
        let owner = ledger.fresh_participant().unwrap();
        let opening = ledger.lend(owner, owner, support, escrow).unwrap();
        let ledger = ledger.apply(&opening.transition).unwrap();
        let base = SymbolicMemory::new()
            .with_block("arg", 8)
            .store(pointer.clone(), int32(0));
        let later_byte = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(1));
        let changed = base.clone().store(later_byte, int32(1));
        let mut requirements = BTreeSet::new();
        branch_memory_delta_requirements(&base, &changed, &ledger, &mut requirements).unwrap();
        let changed_range = MemoryRange::new_with_element_width(
            Address::new(AddressBase::ExternalArgument, AddressOffset::constant(1)),
            0u32.into(),
            4u32.into(),
            1,
        );
        assert!(requirements.contains(&ledger.memory_access_requirement(&changed_range).unwrap()));
    }

    #[test]
    fn entry_representation_rebase_rejects_changed_borrow_authority() {
        let function = program_function(
            ProgramType::Void,
            "borrow_entry_rebase",
            Vec::new(),
            ProgramStatement::Return(ProgramExpression::Value(ProgramValue::Void)),
        );
        let ledger = crate::kernel::borrows::BorrowLedger::new();
        let first_holder = ledger.fresh_participant().unwrap();
        let second_holder = ledger.fresh_participant().unwrap();
        let first = ExecutionState::new()
            .with_borrow_ledger(Some(ledger.clone()))
            .with_borrow_participant(Some(first_holder));
        let second = ExecutionState::new()
            .with_borrow_ledger(Some(ledger))
            .with_borrow_participant(Some(second_holder));
        let assumptions = PureFactContext::new();

        assert!(!function_entry_representation_states_match(
            &function,
            &first,
            &second,
            &assumptions,
        ));
        assert!(!execution_evidence_states_match(
            &function,
            &first,
            &second,
            &assumptions,
        ));
    }

    #[test]
    fn proof_case_family_requires_both_arms_once_per_path() {
        let root = PureFactStore::default();
        let (partition, then_fact, else_fact) = case_partition(&root);
        let mut then_core =
            ExecutionProofCore::at_entry(ExecutionState::new(), ExecutionFrontier::default());
        assert!(then_core.record_proof_case_arm(
            partition.clone(),
            0,
            root.with_fact(then_fact.clone())
        ));
        let mut else_core =
            ExecutionProofCore::at_entry(ExecutionState::new(), ExecutionFrontier::default());
        assert!(else_core.record_proof_case_arm(partition.clone(), 1, root.with_fact(else_fact)));
        let evidence = vec![
            then_core.execution_evidence[0].clone(),
            else_core.execution_evidence[0].clone(),
        ];

        assert!(proof_case_partitions_are_exhaustive(&evidence));
        // One arm alone does not exhaust the partition.
        assert!(!proof_case_partitions_are_exhaustive(&evidence[..1]));
        // A path may pass through a partition once.
        let mut duplicate_then_core = then_core.clone();
        assert!(
            duplicate_then_core.record_proof_case_arm(partition, 0, root.with_fact(then_fact),)
        );
        assert!(!proof_case_partitions_are_exhaustive(&[
            duplicate_then_core.execution_evidence[0].clone(),
            else_core.execution_evidence[0].clone(),
        ]));
    }

    /// A core at function entry and its two arms, each having entered its
    /// case of `partition` and then established `shared` and its own fact.
    fn joinable_arms(
        root: &PureFactStore,
        partition: &Arc<CheckedProofCasePartition>,
        case_facts: [&Proposition; 2],
        shared: &Proposition,
    ) -> (ExecutionProofCore, [(ExecutionProofCore, PureFactStore); 2]) {
        let parent =
            ExecutionProofCore::at_entry(ExecutionState::new(), ExecutionFrontier::default());
        let arms = [0, 1].map(|index| {
            let entered = root.with_fact(case_facts[index].clone());
            let mut core = parent.clone();
            assert!(core.record_proof_case_arm(partition.clone(), index, entered.clone()));
            let own = Proposition::Predicate {
                name: format!("only_in_arm_{index}"),
                arguments: Vec::new(),
            };
            (core, entered.with_fact(shared.clone()).with_fact(own))
        });
        (parent, arms)
    }

    fn join_test_function() -> ProgramFunction {
        program_function(
            ProgramType::Int32,
            "joined",
            Vec::new(),
            program_return(crate::kernel::program_expression::int32_literal(0)),
        )
    }

    #[test]
    fn case_join_rejoins_the_arms_with_only_the_facts_they_share() {
        let root = PureFactStore::default();
        let (partition, then_fact, else_fact) = case_partition(&root);
        let shared = Proposition::Predicate {
            name: "shared".to_string(),
            arguments: Vec::new(),
        };
        let (parent, [(then_core, then_facts), (else_core, else_facts)]) =
            joinable_arms(&root, &partition, [&then_fact, &else_fact], &shared);
        let function = join_test_function();
        let arms = [(&then_core, &then_facts), (&else_core, &else_facts)];

        let mut joined = parent.clone();
        let changed_execution = joined
            .record_proof_case_join(
                &parent,
                &arms,
                &function,
                &[],
                &root.with_fact(shared.clone()),
            )
            .expect("two arms at one state rejoin");
        assert!(!changed_execution);
        // The proof is one path again, and that path covers the partition.
        assert_eq!(joined.execution_evidence.len(), 1);
        assert!(proof_case_partitions_are_exhaustive(&[joined
            .execution_evidence[0]
            .clone()]));

        // A successor may keep only what every arm established: not a case
        // fact, and not one arm's own fact.
        let refused = |successor: PureFactStore| {
            parent
                .clone()
                .record_proof_case_join(&parent, &arms, &function, &[], &successor)
                .is_err()
        };
        assert!(refused(root.with_fact(then_fact.clone())));
        assert!(refused(root.with_fact(else_fact.clone())));
        assert!(refused(root.with_fact(Proposition::Predicate {
            name: "only_in_arm_0".to_string(),
            arguments: Vec::new(),
        })));
        assert!(refused(root.with_fact(shared).with_fact(then_fact)));
    }

    #[test]
    fn case_join_refuses_arms_that_do_not_belong_together() {
        let root = PureFactStore::default();
        let (partition, then_fact, else_fact) = case_partition(&root);
        let shared = Proposition::Predicate {
            name: "shared".to_string(),
            arguments: Vec::new(),
        };
        let (parent, [(then_core, then_facts), (else_core, else_facts)]) =
            joinable_arms(&root, &partition, [&then_fact, &else_fact], &shared);
        let function = join_test_function();
        let refused = |arms: &[(&ExecutionProofCore, &PureFactStore)]| {
            parent
                .clone()
                .record_proof_case_join(&parent, arms, &function, &[], &root)
                .is_err()
        };

        // One arm is nothing to join.
        assert!(refused(&[(&then_core, &then_facts)]));
        // The same case twice.
        assert!(refused(&[
            (&then_core, &then_facts),
            (&then_core, &then_facts)
        ]));
        // An arm entered a different partition over the same facts.
        let (other, other_then, _) = case_partition(&root);
        let mut foreign = parent.clone();
        let foreign_facts = root.with_fact(other_then);
        assert!(foreign.record_proof_case_arm(other, 0, foreign_facts.clone()));
        assert!(refused(&[
            (&foreign, &foreign_facts),
            (&else_core, &else_facts)
        ]));
        // Facts that are not this arm's: they never entered its case.
        let unrelated = root.with_fact(shared);
        assert!(refused(&[
            (&then_core, &unrelated),
            (&else_core, &else_facts)
        ]));
        // An arm that entered no case at all.
        assert!(refused(&[(&parent, &root), (&else_core, &else_facts)]));
    }

    /// One path that joined only some cases does not cover the partition:
    /// the cases it left out still need paths of their own.
    #[test]
    fn a_join_of_some_cases_leaves_the_others_owed() {
        let root = PureFactStore::default();
        let (partition, then_fact, else_fact) = case_partition(&root);
        let mut then_core =
            ExecutionProofCore::at_entry(ExecutionState::new(), ExecutionFrontier::default());
        assert!(then_core.record_proof_case_arm(partition.clone(), 0, root.with_fact(then_fact)));
        // Only the `then` case has a path.
        assert!(!proof_case_partitions_are_exhaustive(&[then_core
            .execution_evidence[0]
            .clone()]));
        let mut else_core =
            ExecutionProofCore::at_entry(ExecutionState::new(), ExecutionFrontier::default());
        assert!(else_core.record_proof_case_arm(partition, 1, root.with_fact(else_fact)));
        assert!(proof_case_partitions_are_exhaustive(&[
            then_core.execution_evidence[0].clone(),
            else_core.execution_evidence[0].clone(),
        ]));
    }

    #[test]
    fn outcome_evidence_fork_splits_traces_in_candidate_order() {
        let root = PureFactStore::default();
        let (partition, then_fact, else_fact) = case_partition(&root);
        let mut core =
            ExecutionProofCore::at_entry(ExecutionState::new(), ExecutionFrontier::default());
        // Two candidate paths with one trace each; the second is forked.
        let function = program_function(
            ProgramType::Int32,
            "fork",
            Vec::new(),
            program_return(crate::kernel::program_expression::int32_literal(0)),
        );
        let entry_state = program_function_entry_state(&ExecutionState::new(), &function, &[])
            .expect("entry state");
        let skip_return = |value: u32| {
            Theorem::new(Proposition::ProgramStatementVerifies {
                state: Box::new(entry_state.clone()),
                statement: Box::new(ProgramStatement::Skip),
                outcome: StatementOutcome::Return {
                    value: int32(value).into(),
                    state: Box::new(entry_state.clone()),
                },
            })
        };
        core.record_statement_outcomes(
            &function,
            &[],
            &[
                (skip_return(0), &[][..], &[][..]),
                (skip_return(1), &[][..], &[][..]),
            ],
            PureFactContext::new(),
        )
        .expect("skip outcomes advance the entry frontier");
        assert_eq!(core.execution_evidence.len(), 2);

        // A plan must cover every trace.
        assert!(
            core.fork_outcome_evidence(&[OutcomeEvidenceFork::Keep])
                .is_err()
        );
        // Arm facts must extend the root by exactly the arm's case fact.
        assert!(
            core.fork_outcome_evidence(&[
                OutcomeEvidenceFork::Keep,
                OutcomeEvidenceFork::binary(
                    partition.clone(),
                    [
                        root.with_fact(else_fact.clone()),
                        root.with_fact(then_fact.clone())
                    ],
                    [OutcomeEvidenceFork::Keep, OutcomeEvidenceFork::Keep],
                ),
            ])
            .is_err()
        );
        // A split takes each live case once, in order.
        let arm = |case, fact: &Proposition| OutcomeForkArm {
            case,
            facts: root.with_fact(fact.clone()),
            then: OutcomeEvidenceFork::Keep,
        };
        for arms in [
            vec![arm(0, &then_fact)],
            vec![arm(1, &else_fact), arm(0, &then_fact)],
            vec![arm(0, &then_fact), arm(0, &then_fact), arm(1, &else_fact)],
        ] {
            assert!(
                core.fork_outcome_evidence(&[
                    OutcomeEvidenceFork::Keep,
                    OutcomeEvidenceFork::Split {
                        partition: partition.clone(),
                        arms,
                    },
                ])
                .is_err()
            );
        }
        core.fork_outcome_evidence(&[
            OutcomeEvidenceFork::Keep,
            OutcomeEvidenceFork::binary(
                partition.clone(),
                [root.with_fact(then_fact), root.with_fact(else_fact)],
                [OutcomeEvidenceFork::Keep, OutcomeEvidenceFork::Keep],
            ),
        ])
        .expect("a well-formed plan forks the second trace");
        assert_eq!(core.execution_evidence.len(), 3);
        assert_eq!(core.execution_evidence[0].len(), 2);
        assert_eq!(core.execution_evidence[1].len(), 3);
        assert_eq!(core.execution_evidence[2].len(), 3);
        assert!(proof_case_partitions_are_exhaustive(
            core.execution_evidence.as_slice()
        ));
        // The forked traces share the original's prefix.
        assert!(
            core.execution_evidence[1]
                .suffix_since(&core.execution_evidence[0])
                .is_none()
        );
    }

    #[test]
    fn nested_outcome_evidence_is_exhaustive_and_rejects_corrupt_inner_arms() {
        let root = PureFactStore::default();
        let (outer, positive, negative) = case_partition(&root);
        let outer_facts = [root.with_fact(positive), root.with_fact(negative)];
        let inner_positive = Proposition::Predicate {
            name: "inner".into(),
            arguments: Vec::new(),
        };
        let inner_negative = Proposition::Not(Box::new(inner_positive.clone()));
        let inner = CheckedProofCasePartition::check(
            &outer_facts[0],
            inner_positive.clone(),
            inner_negative.clone(),
        )
        .unwrap();
        let inner_facts = [
            outer_facts[0].with_fact(inner_positive),
            outer_facts[0].with_fact(inner_negative),
        ];
        let plan = |corrupt| {
            OutcomeEvidenceFork::binary(
                outer.clone(),
                outer_facts.clone(),
                [
                    OutcomeEvidenceFork::binary(
                        inner.clone(),
                        if corrupt {
                            [inner_facts[1].clone(), inner_facts[0].clone()]
                        } else {
                            inner_facts.clone()
                        },
                        [OutcomeEvidenceFork::Keep, OutcomeEvidenceFork::Keep],
                    ),
                    OutcomeEvidenceFork::Keep,
                ],
            )
        };
        let mut core =
            ExecutionProofCore::at_entry(ExecutionState::new(), ExecutionFrontier::default());
        assert!(core.fork_outcome_evidence(&[plan(true)]).is_err());
        assert_eq!(
            core.execution_evidence.len(),
            1,
            "a rejected tree changes nothing"
        );
        core.fork_outcome_evidence(&[plan(false)]).unwrap();
        assert_eq!(core.execution_evidence.len(), 3);
        assert_eq!(
            core.execution_evidence
                .iter()
                .map(|trace| trace.len())
                .collect::<Vec<_>>(),
            [2, 2, 1]
        );
        let traces = core.execution_evidence.to_vec();
        assert!(proof_case_partitions_are_exhaustive(&traces));
        assert!(
            !proof_case_partitions_are_exhaustive(&traces[1..]),
            "losing an inner arm is not exhaustive"
        );
    }
}

/// Reports whether an exact pure-fact context is contradictory.
///
/// Proof orchestration uses this before treating a derived contradiction as
/// path-exclusion evidence: explosion in an already-inconsistent context is
/// not proof that a sibling branch owns the path.
pub fn pure_fact_context_is_inconsistent(assumptions: &PureFactContext) -> bool {
    assumptions.is_inconsistent()
}

/// Reifies one exact context fact as the explicit identity implication
/// `fact -> fact`. This is intentionally not a general proposition prover:
/// callers that want a derived resource invariant must plan and record that
/// derivation before asking the kernel to issue theorem authority.
fn theorem_from_exact_context_fact(
    assumptions: &PureFactContext,
    conclusion: Proposition,
) -> Option<Theorem> {
    if !proposition_holds_without_facts(&conclusion) && !assumptions.proves_exact(&conclusion) {
        return None;
    }
    let proposition = Proposition::Implies(Box::new(conclusion.clone()), Box::new(conclusion));
    Some(Theorem::new(proposition))
}

/// Check the domain of a + (b + c) from the three explicit domains of
/// a + b, (a + b) + c, and b + c. The first two put the mathematical total
/// in signed range; the third makes the regrouped inner sum denote that total.
/// This reads only the named guards through the indexed atomic checker.
pub(in crate::kernel) fn checked_int32_reassociated_add_domain(
    assumptions: &PureFactContext,
    goal: &Proposition,
) -> bool {
    // The rule reads the goal's shape, so it also reads its comparison form:
    // a read of a cell holding a sum is that sum.
    checked_int32_reassociated_add_domain_as_written(assumptions, goal)
        || crate::kernel::comparison_form(goal).is_some_and(|comparison| {
            checked_int32_reassociated_add_domain_as_written(assumptions, &comparison)
        })
}

fn checked_int32_reassociated_add_domain_as_written(
    assumptions: &PureFactContext,
    goal: &Proposition,
) -> bool {
    use crate::kernel::machine_integer::{
        Operation,
        definedness::{OverflowQueryView, ordinary_arithmetic_guard_view},
    };
    use crate::kernel::{MachineBinaryOp, MachineOperandView as View};
    let query = ordinary_arithmetic_guard_view(goal);
    let operands = if let Some(query) = &query {
        if query.format != MachineIntegerType::Int32 || query.operation != Operation::Add {
            return false;
        }
        query
            .operands
            .each_ref()
            .map(|operand| operand.operand_view())
    } else if let Some((
        OldConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Add,
            left,
            right,
        },
        false,
    )) = (goal).old_condition()
    {
        [View::Old(left), View::Old(right)]
    } else {
        return false;
    };
    fn nested(value: View<'_>) -> Option<[View<'_>; 2]> {
        match value.binary() {
            Some((MachineIntegerType::Int32, MachineBinaryOp::Add, pair)) => Some(pair),
            _ => None,
        }
    }
    let checks = |a: View<'_>, [b, c]: [View<'_>; 2]| {
        let sum = match [a, b] {
            [View::Old(a), View::Old(b)] => crate::kernel::SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                OldMachineTerm::add(a.clone(), b.clone()),
            ),
            operands => {
                let roots = operands.map(|operand| match operand {
                    View::Shared(root) => root.clone(),
                    View::Old(value) => crate::kernel::KernelTermImport::default()
                        .machine(MachineIntegerType::Int32, value),
                });
                crate::kernel::SharedMachineIntegerTerm::from_shared(
                    MachineIntegerType::Int32,
                    crate::kernel::KernelTerm::machine_binary_shared(
                        MachineIntegerType::Int32,
                        MachineBinaryOp::Add,
                        roots,
                    ),
                )
                .unwrap_or_else(|| {
                    // Opaque legacy families still use their existing producer
                    // boundary until they acquire shared operand identities.
                    crate::kernel::SharedMachineIntegerTerm::intern(
                        MachineIntegerType::Int32,
                        OldMachineTerm::add(
                            a.retain(MachineIntegerType::Int32).value().clone(),
                            b.retain(MachineIntegerType::Int32).value().clone(),
                        ),
                    )
                })
            }
        };
        [[a, b], [sum.operand_view(), c], [b, c]]
            .into_iter()
            .all(|pair| {
                [pair, [pair[1], pair[0]]].into_iter().any(|pair| {
                    let query = OverflowQueryView::from_operands(
                        MachineIntegerType::Int32,
                        Operation::Add,
                        pair,
                    )
                    .expect("signed addition query");
                    query
                        .bounds()
                        .iter()
                        .all(|bound| assumptions.settles_exactly(bound))
                })
            })
    };
    nested(operands[1]).is_some_and(|pair| checks(operands[0], pair))
        || nested(operands[0]).is_some_and(|pair| checks(operands[1], pair))
}

/// Reconstruct a count bound checked against this state's immutable ledger and
/// exact custody. Retained observations must bind the result to this state;
/// this does not return an unconditional arithmetic theorem.
pub fn checked_owned_resource_count_lower_bound(
    state: &ExecutionState,
    owned: &ResourceFact,
    assumptions: &PureFactContext,
) -> Option<Proposition> {
    if !state.resources().satisfies_fact(owned, assumptions) {
        return None;
    }
    let quantity = owned.owned_quantity_term()?;
    let (name, arguments) = match owned.resource() {
        Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_) => {
            return None;
        }
        Resource::Composite { name, arguments } | Resource::Token { name, arguments } => {
            (name, arguments)
        }
        Resource::Memory(_)
        | Resource::PopulationAuthority(_)
        | Resource::Instance(_)
        | Resource::ConditionalMutexGuard(_)
        | Resource::MutexGuard(_)
        | Resource::MutexLive(_)
        | Resource::MutexUse(_)
        | Resource::Publication(_)
        | Resource::Iterated(_) => return None,
    };
    let mut checked_facts = assumptions.clone();
    let count = {
        let arguments = arguments
            .iter()
            .map(|argument| match argument {
                crate::kernel::ResourceFieldValue::Program(value) => {
                    Some(Some(SpecExpression::Value(value.clone())))
                }
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?;
        let expression = SpecExpression::CountedResourceCount {
            name: name.clone(),
            arguments,
        };
        let paths = crate::kernel::spec::evaluate_spec_expression_paths_with_bindings(
            state,
            &expression,
            assumptions,
            &BTreeMap::new(),
            &mut ExecutionBudget::beside_live_state(),
        )
        .ok()?;
        let [path] = paths.as_slice() else {
            return None;
        };
        if !path.obligations.iter().all(|obligation| {
            PureFactContext::settles_exactly(assumptions, obligation.proposition())
        }) {
            return None;
        }
        for fact in &path.facts {
            checked_facts = checked_facts.assume_proposition(fact.proposition().clone());
        }
        let native = path.value.native();
        let ProgramValue::Int32(value) = native.as_ref() else {
            return None;
        };
        value.clone()
    };
    let conclusion = Proposition::condition_is(
        crate::kernel::machine_integer::comparison::stored_logical_comparison(
            MachineIntegerType::Int32,
            CompareRelation::LessEqual,
            [
                MachineOperandView::Old(quantity),
                MachineOperandView::Old(&count),
            ],
            false,
        ),
        true,
    );
    if !proposition_holds_without_facts(&conclusion)
        && !PureFactContext::settles_exactly(&checked_facts, &conclusion)
    {
        let reversed = Proposition::condition_is(
            StoredConditionTerm::signed_int32_at_least(&count, quantity),
            true,
        );
        if !checked_facts.proves_exact(&reversed) {
            return None;
        }
    }
    Some(conclusion)
}

pub(super) fn owned_quantity_nonnegative_claim(owned: &ResourceFact) -> Option<Proposition> {
    let quantity = owned.owned_quantity_term()?;
    let condition = crate::kernel::machine_integer::comparison::stored_logical_comparison(
        MachineIntegerType::Int32,
        CompareRelation::LessEqual,
        [
            MachineOperandView::Old(&OldMachineTerm::constant(0)),
            MachineOperandView::Old(quantity),
        ],
        false,
    );
    Some(Proposition::condition_is(condition, true))
}

/// Certifies the nonnegativity invariant carried by an owned declared-resource
/// coefficient in a concrete ghost state.
pub fn prove_owned_resource_quantity_nonnegative(
    state: &ExecutionState,
    owned: &ResourceFact,
    claimed: &Proposition,
    assumptions: &PureFactContext,
) -> Option<Theorem> {
    if !state.resources().satisfies_fact(owned, assumptions) {
        return None;
    }
    let conclusion = owned_quantity_nonnegative_claim(owned)?;
    if claimed != &conclusion {
        return None;
    }
    theorem_from_exact_context_fact(assumptions, conclusion)
}

/// Whether two states agree on population body access and on the families
/// they have observed.
pub(crate) fn population_observations_equal(left: &ExecutionState, right: &ExecutionState) -> bool {
    left.population_access == right.population_access
        && left.observed_population_families == right.observed_population_families
}

#[cfg(test)]
pub fn prove_program_max_lt_returns_right(a: Variable, b: Variable) -> Option<Theorem> {
    let a_bits = OldMachineTerm::Variable(a);
    let b_bits = OldMachineTerm::Variable(b);
    let a_value = int32(a_bits.clone());
    let b_value = int32(b_bits.clone());
    let condition = program_max_lt_condition(a_bits.clone(), b_bits.clone());
    let state = program_max_state(a_value, b_value.clone());
    let assumptions = PureFactContext::new().assume_condition(condition.clone(), true);
    let outcome = execute_execution_statement(&state, &program_max_body(), &assumptions)?;

    if outcome
        != (StatementOutcome::Return {
            value: b_value.into(),
            state: Box::new(state.clone()),
        })
    {
        return None;
    }

    Some(Theorem::new(forall_int32(
        a,
        forall_int32(
            b,
            Proposition::Implies(
                Box::new(Proposition::condition_is(condition, true)),
                Box::new(Proposition::ProgramStatementVerifies {
                    state: Box::new(state),
                    statement: Box::new(program_max_body()),
                    outcome,
                }),
            ),
        ),
    )))
}

#[cfg(test)]
pub fn prove_program_max_not_lt_returns_left(a: Variable, b: Variable) -> Option<Theorem> {
    let a_bits = OldMachineTerm::Variable(a);
    let b_bits = OldMachineTerm::Variable(b);
    let a_value = int32(a_bits.clone());
    let b_value = int32(b_bits.clone());
    let condition = program_max_lt_condition(a_bits, b_bits);
    let state = program_max_state(a_value.clone(), b_value);
    let assumptions = PureFactContext::new().assume_condition(condition.clone(), false);
    let outcome = execute_execution_statement(&state, &program_max_body(), &assumptions)?;

    if outcome
        != (StatementOutcome::Return {
            value: a_value.into(),
            state: Box::new(state.clone()),
        })
    {
        return None;
    }

    Some(Theorem::new(forall_int32(
        a,
        forall_int32(
            b,
            Proposition::Implies(
                Box::new(Proposition::condition_is(condition, false)),
                Box::new(Proposition::ProgramStatementVerifies {
                    state: Box::new(state),
                    statement: Box::new(program_max_body()),
                    outcome,
                }),
            ),
        ),
    )))
}

/// Two signed int32 values are equal when the first is no greater than the
/// second and is not strictly less than it.
pub fn prove_int32_le_antisymmetric(left: OldMachineTerm, right: OldMachineTerm) -> Theorem {
    let le_premise = Proposition::condition_is(
        OldConditionTerm::signed_less_equal(left.clone(), right.clone()),
        true,
    );
    let reverse_le_premise = Proposition::condition_is(
        OldConditionTerm::signed_less_equal(right.clone(), left.clone()),
        true,
    );
    let conclusion = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(left),
            right: Box::new(right),
        },
        true,
    );
    implication([le_premise, reverse_le_premise], conclusion)
}

/// An empty population has no members. For the exact member `name(arguments)`
/// of the population `name(arguments[0], _, ...)`, its count is zero when the
/// population's is. Both counts are evaluated here exactly as `count(...)`
/// lowers at `state`, so the theorem states the terms a proof writes, and the
/// law holds of them by the meaning of a count; it is never a fact-dependent
/// fold. `None` when either count does not lower to one defined `int32`.
pub fn prove_population_member_count_zero(
    state: &ExecutionState,
    name: &str,
    arguments: &[ProgramValue],
    assumptions: &PureFactContext,
) -> Option<Theorem> {
    if arguments.len() < 2 {
        return None;
    }
    let count = |arguments: Vec<Option<SpecExpression>>| {
        let paths = crate::kernel::spec::evaluate_spec_expression_paths_with_bindings(
            state,
            &SpecExpression::CountedResourceCount {
                name: name.to_owned(),
                arguments,
            },
            assumptions,
            &BTreeMap::new(),
            &mut ExecutionBudget::beside_live_state(),
        )
        .ok()?;
        let [path] = paths.as_slice() else {
            return None;
        };
        if !path.obligations.iter().all(|obligation| {
            PureFactContext::settles_exactly(assumptions, obligation.proposition())
        }) {
            return None;
        }
        let native = path.value.native();
        let ProgramValue::Int32(value) = native.as_ref() else {
            return None;
        };
        Some(value.clone())
    };
    let member = count(
        arguments
            .iter()
            .map(|argument| Some(SpecExpression::Value(argument.clone())))
            .collect(),
    )?;
    let total = count(
        std::iter::once(Some(SpecExpression::Value(arguments[0].clone())))
            .chain(arguments[1..].iter().map(|_| None))
            .collect(),
    )?;
    Some(implication(
        [Proposition::condition_is(
            OldConditionTerm::equal(total, OldMachineTerm::constant(0)),
            true,
        )],
        Proposition::condition_is(
            OldConditionTerm::equal(member, OldMachineTerm::constant(0)),
            true,
        ),
    ))
}

/// A fold law shifts its endpoint by one in the endpoint's word ring. Keep
/// the existing native constructor reading without expanding retained input.
fn shifted_fold_endpoint(
    endpoint: &SharedIntegerRangeEndpoint,
    format: MachineIntegerType,
    operation: MachineBinaryOp,
) -> SharedIntegerRangeEndpoint {
    use crate::kernel::{KernelTermImport, MachineOperandView as V};
    let one = match format {
        MachineIntegerType::Int32 => OldMachineTerm::constant(1),
        MachineIntegerType::UInt64 => OldMachineTerm::uint64_constant(1),
        _ => unreachable!("machine fold endpoint format"),
    };
    let operand = endpoint.machine_operand().operand_view();
    let root = match operand {
        V::Old(term) => {
            return SharedIntegerRangeEndpoint::intern(OldMachineTerm::machine_binary(
                format,
                operation,
                term.clone(),
                one,
            ));
        }
        V::Shared(root) => root.with_machine_observation_type(format),
    };
    // The native uint64 constructor reads constant arithmetic and casts;
    // int32 constructors read only literal roots. The shared constant reading
    // is cached with the syntax node, including unsuccessful readings.
    let root = if format == MachineIntegerType::UInt64 {
        operand
            .uint64_constant()
            .map(|bits| {
                KernelTermImport::default().machine(format, &OldMachineTerm::uint64_constant(bits))
            })
            .unwrap_or(root)
    } else {
        root
    };
    let one = KernelTermImport::default().machine(format, &one);
    let shifted = crate::kernel::proof::term_rewrite::TermRewrite::machine_binary_reading(
        format, operation, root, one,
    )
    .with_machine_observation_type(MachineIntegerType::Int32);
    endpoint
        .with_shared_operand(shifted)
        .expect("retained fold endpoint")
}

fn fold_endpoint_order(
    format: MachineIntegerType,
    relation: CompareRelation,
    left: &SharedIntegerRangeEndpoint,
    right: &SharedIntegerRangeEndpoint,
) -> OldConditionTerm {
    crate::kernel::machine_integer::comparison::condition_for_operand_views(
        format,
        relation,
        [
            left.machine_operand().operand_view(),
            right.machine_operand().operand_view(),
        ],
    )
}

/// The empty Integer fold law, guarded by the endpoint ordering.
pub fn prove_integer_range_fold_empty(
    index: IntegerRangeFoldIndex,
    initial: IntegerTerm,
    accumulator: Variable,
    item: Variable,
    body: IntegerTerm,
) -> Theorem {
    let guard = match &index {
        IntegerRangeFoldIndex::Int32 { start, end } => fold_endpoint_order(
            MachineIntegerType::Int32,
            CompareRelation::LessEqual,
            end,
            start,
        ),
        IntegerRangeFoldIndex::UInt64 { start, end } => fold_endpoint_order(
            MachineIntegerType::UInt64,
            CompareRelation::LessEqual,
            end,
            start,
        ),
        IntegerRangeFoldIndex::Integer { start, end } => {
            OldConditionTerm::integer_less_equal(end.as_ref().clone(), start.as_ref().clone())
        }
    };
    let fold = IntegerTerm::range_fold(index, initial.clone(), accumulator, item, body);
    implication(
        [Proposition::condition_is(guard, true)],
        Proposition::condition_is(
            OldConditionTerm::IntegerEqual(fold.into(), initial.into()),
            true,
        ),
    )
}

/// The append-one Integer fold law.  The Int32 carrier includes the checked
/// increment premise; neither carrier is expanded over the range.
pub fn prove_integer_range_fold_append(
    index: IntegerRangeFoldIndex,
    initial: IntegerTerm,
    accumulator: Variable,
    item: Variable,
    body: IntegerTerm,
) -> Option<Theorem> {
    if matches!(&index, IntegerRangeFoldIndex::Integer { .. }) && accumulator == item {
        return None;
    }
    let (extended, guard, item_value) = match &index {
        IntegerRangeFoldIndex::Int32 { start, end } => {
            let item_value = end
                .machine_operand()
                .operand_view()
                .observe(MachineIntegerType::Int32)?;
            let increment =
                shifted_fold_endpoint(end, MachineIntegerType::Int32, MachineBinaryOp::Add);
            let guard = fold_endpoint_order(
                MachineIntegerType::Int32,
                CompareRelation::LessEqual,
                start,
                end,
            );
            let safe = crate::kernel::machine_integer::comparison::condition_for_operand_views(
                MachineIntegerType::Int32,
                CompareRelation::LessThan,
                [
                    end.machine_operand().operand_view(),
                    crate::kernel::MachineOperandView::Old(&OldMachineTerm::constant(
                        i32::MAX as u32,
                    )),
                ],
            );
            let extended = IntegerRangeFoldIndex::Int32 {
                start: start.clone(),
                end: increment,
            };
            (
                extended,
                Proposition::And(
                    Box::new(Proposition::condition_is(guard, true)),
                    Box::new(Proposition::condition_is(safe, true)),
                ),
                item_value,
            )
        }
        // The unsigned 64-bit carrier, like the signed one, extends the
        // range only below the type's largest value, where `end + 1` does
        // not wrap.
        IntegerRangeFoldIndex::UInt64 { start, end } => {
            let item_value = end
                .machine_operand()
                .operand_view()
                .observe(MachineIntegerType::UInt64)?;
            let increment =
                shifted_fold_endpoint(end, MachineIntegerType::UInt64, MachineBinaryOp::Add);
            let guard = fold_endpoint_order(
                MachineIntegerType::UInt64,
                CompareRelation::LessEqual,
                start,
                end,
            );
            let safe = crate::kernel::machine_integer::comparison::condition_for_operand_views(
                MachineIntegerType::UInt64,
                CompareRelation::LessThan,
                [
                    end.machine_operand().operand_view(),
                    crate::kernel::MachineOperandView::Old(&OldMachineTerm::uint64_constant(
                        u64::MAX,
                    )),
                ],
            );
            let extended = IntegerRangeFoldIndex::UInt64 {
                start: start.clone(),
                end: increment,
            };
            (
                extended,
                Proposition::And(
                    Box::new(Proposition::condition_is(guard, true)),
                    Box::new(Proposition::condition_is(safe, true)),
                ),
                item_value,
            )
        }
        IntegerRangeFoldIndex::Integer { start, end } => {
            let increment = IntegerTerm::add(end.as_ref().clone(), IntegerTerm::constant_i64(1));
            let guard =
                OldConditionTerm::integer_less_equal(start.as_ref().clone(), end.as_ref().clone());
            let extended = IntegerRangeFoldIndex::Integer {
                start: start.clone(),
                end: increment.into(),
            };
            (
                extended,
                Proposition::condition_is(guard, true),
                end.as_ref().clone(),
            )
        }
    };
    let original_initial = initial.clone();
    let program_item = index.machine_item_type();
    let prior = IntegerTerm::range_fold(index, initial, accumulator, item, body.clone());
    let stepped = crate::kernel::reasoning::instantiate_integer_range_fold_step(
        &body,
        accumulator,
        &prior,
        item,
        &item_value,
        program_item,
    )
    .ok()?;
    let extended_fold =
        IntegerTerm::range_fold(extended, original_initial, accumulator, item, body);
    Some(implication(
        [guard],
        Proposition::condition_is(
            OldConditionTerm::IntegerEqual(extended_fold.into(), stepped.into()),
            true,
        ),
    ))
}

/// The predecessor of a range fold's end endpoint, in the endpoint's own
/// carrier. The Int32 carrier subtracts in wrapping bitvector arithmetic, so
/// the predecessor endpoint always exists as a term; whether the *written*
/// `hi - 1` denotes it is the surface's separate definedness question, and
/// the append law's own `start <= end - 1` guard is what makes the range
/// nonempty.
fn integer_range_fold_predecessor_index(
    index: &IntegerRangeFoldIndex,
) -> Option<(IntegerRangeFoldIndex, IntegerTerm)> {
    match index {
        IntegerRangeFoldIndex::Int32 { start, end } => {
            let predecessor =
                shifted_fold_endpoint(end, MachineIntegerType::Int32, MachineBinaryOp::Subtract);
            let item_value = predecessor
                .machine_operand()
                .operand_view()
                .observe(MachineIntegerType::Int32)?;
            Some((
                IntegerRangeFoldIndex::Int32 {
                    start: start.clone(),
                    end: predecessor,
                },
                item_value,
            ))
        }
        IntegerRangeFoldIndex::UInt64 { start, end } => {
            let predecessor =
                shifted_fold_endpoint(end, MachineIntegerType::UInt64, MachineBinaryOp::Subtract);
            let item_value = predecessor
                .machine_operand()
                .operand_view()
                .observe(MachineIntegerType::UInt64)?;
            Some((
                IntegerRangeFoldIndex::UInt64 {
                    start: start.clone(),
                    end: predecessor,
                },
                item_value,
            ))
        }
        IntegerRangeFoldIndex::Integer { start, end } => {
            let predecessor =
                IntegerTerm::subtract(end.as_ref().clone(), IntegerTerm::constant_i64(1));
            Some((
                IntegerRangeFoldIndex::Integer {
                    start: start.clone(),
                    end: predecessor.clone().into(),
                },
                predecessor,
            ))
        }
    }
}

/// Replaces one Integer term by another inside a proposition's Integer
/// comparisons, returning `None` when nothing changed.
///
/// This is Leibniz for a proof step that already holds the two terms' proved
/// equality: rewriting *some* occurrences is sound, so the walk is
/// deliberately shallow. It descends only the arithmetic spine -- negation,
/// addition, subtraction, multiplication, truncating quotient/remainder -- and
/// compares interned identity
/// everywhere else, so it never enters a range fold's binders and its work is
/// linear in the distinct arithmetic DAG nodes and proposition it rebuilds.
pub fn substitute_integer_term_in_proposition(
    proposition: &Proposition,
    from: &SharedIntegerTerm,
    to: &SharedIntegerTerm,
) -> Option<Proposition> {
    fn walk_term(
        term: &SharedIntegerTerm,
        from: &SharedIntegerTerm,
        to: &SharedIntegerTerm,
        changed: &mut bool,
        memo: &mut std::collections::HashMap<u64, SharedIntegerTerm>,
    ) -> SharedIntegerTerm {
        if let Some(result) = memo.get(&term.id()) {
            return result.clone();
        }
        crate::instrumentation::record_deterministic_work(1);
        if term == from {
            *changed = true;
            memo.insert(term.id(), to.clone());
            return to.clone();
        }
        let rebuilt = match term.as_ref() {
            IntegerTerm::Negate(inner) => {
                IntegerTerm::Negate(walk_term(inner, from, to, changed, memo))
            }
            IntegerTerm::Add(left, right) => IntegerTerm::Add(
                walk_term(left, from, to, changed, memo),
                walk_term(right, from, to, changed, memo),
            ),
            IntegerTerm::Subtract(left, right) => IntegerTerm::Subtract(
                walk_term(left, from, to, changed, memo),
                walk_term(right, from, to, changed, memo),
            ),
            IntegerTerm::Multiply(left, right) => IntegerTerm::Multiply(
                walk_term(left, from, to, changed, memo),
                walk_term(right, from, to, changed, memo),
            ),
            IntegerTerm::TruncatingQuotient(left, right)
            | IntegerTerm::TruncatingRemainder(left, right) => {
                let left = walk_term(left, from, to, changed, memo);
                let right = walk_term(right, from, to, changed, memo);
                let remainder = matches!(term.as_ref(), IntegerTerm::TruncatingRemainder(..));
                IntegerTerm::truncating_division_shared(left, right, remainder)
            }
            _ => term.as_ref().clone(),
        };
        let result = SharedIntegerTerm::intern(rebuilt);
        memo.insert(term.id(), result.clone());
        result
    }

    fn walk_condition(
        condition: &OldConditionTerm,
        from: &SharedIntegerTerm,
        to: &SharedIntegerTerm,
        changed: &mut bool,
        memo: &mut std::collections::HashMap<u64, SharedIntegerTerm>,
    ) -> OldConditionTerm {
        let mut rebuild =
            |constructor: fn(SharedIntegerTerm, SharedIntegerTerm) -> OldConditionTerm,
             left: &SharedIntegerTerm,
             right: &SharedIntegerTerm,
             changed: &mut bool| {
                constructor(
                    walk_term(left, from, to, changed, memo),
                    walk_term(right, from, to, changed, memo),
                )
            };
        match condition {
            OldConditionTerm::IntegerLessThan(left, right) => {
                rebuild(OldConditionTerm::IntegerLessThan, left, right, changed)
            }
            OldConditionTerm::IntegerLessEqual(left, right) => {
                rebuild(OldConditionTerm::IntegerLessEqual, left, right, changed)
            }
            OldConditionTerm::IntegerGreaterThan(left, right) => {
                rebuild(OldConditionTerm::IntegerGreaterThan, left, right, changed)
            }
            OldConditionTerm::IntegerGreaterEqual(left, right) => {
                rebuild(OldConditionTerm::IntegerGreaterEqual, left, right, changed)
            }
            OldConditionTerm::IntegerEqual(left, right) => {
                rebuild(OldConditionTerm::IntegerEqual, left, right, changed)
            }
            OldConditionTerm::IntegerNotEqual(left, right) => {
                rebuild(OldConditionTerm::IntegerNotEqual, left, right, changed)
            }
            condition => condition.clone(),
        }
    }

    fn walk(
        proposition: &Proposition,
        from: &SharedIntegerTerm,
        to: &SharedIntegerTerm,
        changed: &mut bool,
        memo: &mut std::collections::HashMap<u64, SharedIntegerTerm>,
    ) -> Proposition {
        match proposition {
            Proposition::ConditionIs(condition, expected) => Proposition::condition_is(
                walk_condition(condition.old_form(), from, to, changed, memo),
                *expected,
            ),
            Proposition::And(left, right) => Proposition::And(
                Box::new(walk(left, from, to, changed, memo)),
                Box::new(walk(right, from, to, changed, memo)),
            ),
            Proposition::Or(left, right) => Proposition::Or(
                Box::new(walk(left, from, to, changed, memo)),
                Box::new(walk(right, from, to, changed, memo)),
            ),
            Proposition::Not(body) => {
                Proposition::Not(Box::new(walk(body, from, to, changed, memo)))
            }
            Proposition::Implies(antecedent, consequent) => Proposition::Implies(
                Box::new(walk(antecedent, from, to, changed, memo)),
                Box::new(walk(consequent, from, to, changed, memo)),
            ),
            proposition => proposition.clone(),
        }
    }

    let mut changed = false;
    let rewritten = walk(
        proposition,
        from,
        to,
        &mut changed,
        &mut std::collections::HashMap::new(),
    );
    changed.then_some(rewritten)
}

/// The append law's predecessor-range guard, constructed without touching
/// its body. Ordinary unfold can select a written guard before instantiating
/// that law; all of its guards still become ordinary checked obligations.
pub(crate) fn integer_range_fold_predecessor_guard(
    index: &IntegerRangeFoldIndex,
) -> Option<OldConditionTerm> {
    let (prior, _) = integer_range_fold_predecessor_index(index)?;
    Some(match prior {
        IntegerRangeFoldIndex::Int32 { start, end } => fold_endpoint_order(
            MachineIntegerType::Int32,
            CompareRelation::LessEqual,
            &start,
            &end,
        ),
        IntegerRangeFoldIndex::UInt64 { start, end } => fold_endpoint_order(
            MachineIntegerType::UInt64,
            CompareRelation::LessEqual,
            &start,
            &end,
        ),
        IntegerRangeFoldIndex::Integer { start, end } => {
            OldConditionTerm::integer_less_equal(start.as_ref().clone(), end.as_ref().clone())
        }
    })
}

/// The opaque application `f(args)` with the int32 or uint64 argument at `position`
/// replaced by its predecessor, or an already specialized fold with its end
/// replaced by its predecessor, for restating a range fold one endpoint
/// lower. The subtraction is wrapping bitvector arithmetic, matching the
/// endpoint `integer_range_fold_predecessor_index` builds, so the two agree
/// by construction.
pub fn integer_range_fold_predecessor_application(
    whole: &IntegerTerm,
    position: usize,
) -> Option<IntegerTerm> {
    if let IntegerTerm::RangeFold {
        index,
        initial,
        accumulator,
        item,
        body,
    } = whole
    {
        let (index, _) = integer_range_fold_predecessor_index(index)?;
        return Some(IntegerTerm::range_fold(
            index,
            initial.as_ref().clone(),
            *accumulator,
            *item,
            body.as_ref().clone(),
        ));
    }
    let IntegerTerm::PureFunctionApplication(applied) = whole else {
        return None;
    };
    let mut arguments = applied.arguments().to_vec();
    arguments[position] = match arguments.get(position)? {
        PureFunctionArgument::SharedMachine(endpoint)
            if matches!(
                endpoint.ty(),
                MachineIntegerType::Int32 | MachineIntegerType::UInt64
            ) =>
        {
            let format = endpoint.ty();
            let root = KernelTerm::retained_machine_operand(format, endpoint.operand_view());
            let one = KernelTerm::retained_native_machine_operand(
                format,
                &crate::kernel::machine_integer::range::constant_word(format, &1.into()).unwrap(),
            );
            let operands = [root, one];
            let node = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Subtract,
                operands.clone(),
            );
            let node = crate::kernel::proof::equality_rewrite::rebuild_normalized_machine_node(
                &node, &operands,
            )?;
            PureFunctionArgument::SharedMachine(SharedMachineIntegerTerm::from_shared(
                format, node,
            )?)
        }
        PureFunctionArgument::Value(ProgramValue::Int32(endpoint)) => {
            PureFunctionArgument::Value(ProgramValue::Int32(OldMachineTerm::subtract(
                endpoint.clone(),
                OldMachineTerm::constant(1),
            )))
        }
        PureFunctionArgument::Value(ProgramValue::UInt64(endpoint)) => {
            PureFunctionArgument::Value(ProgramValue::UInt64(OldMachineTerm::uint64_subtract(
                endpoint.clone(),
                OldMachineTerm::uint64_constant(1),
            )))
        }
        _ => return None,
    };
    Some(IntegerTerm::PureFunctionApplication(
        SharedPureApplication::intern(applied.name().to_string(), arguments),
    ))
}

/// A range-fold law restated over the terms a pure function's defining
/// equation gives its folds, so a proof can reason about the whole range
/// through the function application instead of retyping the fold.
///
/// `whole` is a term the caller must prove equal to `fold(start..end)`: in
/// practice the opaque application `f(args)` whose declared body is that
/// fold. `prior`, when present, selects the append form and is a term the
/// caller must prove equal to `fold(start..end - 1)` -- the same application
/// at the predecessor endpoint. Those equalities are *premises* of the
/// produced theorem, beside the underlying law's own guards, so the surface
/// discharges each of them exactly and this entry point assumes nothing the
/// existing laws do not already prove.
///
/// Empty form: from `whole == fold` and `end <= start`, conclude
/// `whole == initial`, by `prove_integer_range_fold_empty`.
///
/// Append form: instantiate `prove_integer_range_fold_append` at the
/// predecessor index `start..end - 1`, whose conclusion is stated over
/// `fold(start..(end - 1) + 1)`. That fold and `fold(start..end)` are the
/// same Integer by endpoint affine normalization, checked here against an
/// empty fact context so no ambient fact can be borrowed. Substituting
/// `prior` for the equal `fold(start..end - 1)` inside the law's next-element
/// step is congruence under the second premise.
pub fn prove_integer_range_fold_over_equal_terms(
    index: IntegerRangeFoldIndex,
    initial: IntegerTerm,
    accumulator: Variable,
    item: Variable,
    body: IntegerTerm,
    whole: IntegerTerm,
    prior: Option<IntegerTerm>,
) -> Result<Theorem, &'static str> {
    let fold = IntegerTerm::range_fold(
        index.clone(),
        initial.clone(),
        accumulator,
        item,
        body.clone(),
    );
    let whole_is_fold = Proposition::condition_is(
        OldConditionTerm::IntegerEqual(whole.clone().into(), fold.clone().into()),
        true,
    );
    let Some(prior) = prior else {
        let empty = prove_integer_range_fold_empty(index, initial.clone(), accumulator, item, body);
        let Proposition::Implies(guard, _) = empty.proposition() else {
            return Err("the Integer fold empty law is not a guarded theorem");
        };
        return Ok(implication(
            [Proposition::And(
                Box::new(whole_is_fold),
                Box::new(guard.as_ref().clone()),
            )],
            Proposition::condition_is(
                OldConditionTerm::IntegerEqual(whole.into(), initial.into()),
                true,
            ),
        ));
    };

    let (predecessor_index, item_value) = integer_range_fold_predecessor_index(&index)
        .ok_or("the fold end endpoint has no Integer predecessor in its own carrier")?;
    let program_item = predecessor_index.machine_item_type();
    let append = prove_integer_range_fold_append(
        predecessor_index.clone(),
        initial.clone(),
        accumulator,
        item,
        body.clone(),
    )
    .ok_or("the Integer fold append law could not instantiate its next-element step")?;
    let Proposition::Implies(guard, conclusion) = append.proposition() else {
        return Err("the Integer fold append law is not a guarded theorem");
    };
    let Some((OldConditionTerm::IntegerEqual(extended, _), true)) =
        conclusion.as_ref().old_condition()
    else {
        return Err("the Integer fold append law did not conclude an equation");
    };
    // The law is stated at `start..(end - 1) + 1`; the caller's `whole` is
    // proved equal to `start..end`. Refuse unless those are the same fold.
    if !crate::kernel::reasoning::integer_range_fold_terms_alpha_equivalent(
        extended,
        &SharedIntegerTerm::from(fold.clone()),
        &PureFactContext::new(),
    ) {
        return Err("the fold at the successor of the predecessor endpoint is not the fold itself");
    }
    let prior_fold =
        IntegerTerm::range_fold(predecessor_index, initial, accumulator, item, body.clone());
    let prior_is_fold = Proposition::condition_is(
        OldConditionTerm::IntegerEqual(prior.clone().into(), prior_fold.into()),
        true,
    );
    let stepped = crate::kernel::reasoning::instantiate_integer_range_fold_step(
        &body,
        accumulator,
        &prior,
        item,
        &item_value,
        program_item,
    )
    .map_err(|_| {
        "the fold body could not take the previous accumulator and the last item; a fold whose item indexes a pure call is not yet supported"
    })?;
    Ok(implication(
        [Proposition::And(
            Box::new(Proposition::And(
                Box::new(whole_is_fold),
                Box::new(prior_is_fold),
            )),
            Box::new(guard.as_ref().clone()),
        )],
        Proposition::condition_is(
            OldConditionTerm::IntegerEqual(whole.into(), stepped.into()),
            true,
        ),
    ))
}

/// Universally closes a pure int32 implication that a checked proof already
/// established.
///
/// The kernel does not re-prove the conclusion. `completion` is the durable
/// record a completed [`ProofObject`](crate::kernel::proof::ProofObject)
/// issues for its root judgment, and this constructor checks only that the
/// record is the one the claimed implication describes: the proof's goal is
/// exactly `conclusion`, the facts its root branch assumed are exactly
/// `requirements`, and every free bitvector variable of both is listed exactly
/// once in `variables`. This is the sole constructor for authority that lets
/// a Click pure theorem participate in whole-contract certification.
pub(crate) fn prove_universally_quantified_pure_implication(
    requirements: Vec<Proposition>,
    conclusion: Proposition,
    variables: Vec<Variable>,
    completion: &crate::kernel::proof::CheckedProposition,
) -> Option<VerifiedPureTheorem> {
    checked_pure_implication_matches(&requirements, &conclusion, completion)
        .then(|| universally_close_pure_implication(requirements, conclusion, variables))?
}

/// Whether one completed proof is exactly a proof of `conclusion` from
/// `requirements`.
///
/// Both checks are exact: proposition identity, and set identity between the
/// root branch's assumed facts and the explicit requirements. The fact store
/// deduplicates equal top-level facts at construction, so a repeated
/// requirement is not a mismatch.
fn checked_pure_implication_matches(
    requirements: &[Proposition],
    conclusion: &Proposition,
    completion: &crate::kernel::proof::CheckedProposition,
) -> bool {
    let root_assumptions = completion.root_assumptions().to_vec();
    root_assumptions.len() == requirements.len()
        && crate::kernel::propositions_equal_iteratively(completion.proposition(), conclusion)
        && root_assumptions.iter().all(|assumption| {
            requirements.iter().any(|requirement| {
                crate::kernel::propositions_equal_iteratively(assumption, requirement)
            })
        })
}

/// Folds the explicit requirements and binders around an established
/// conclusion. Every caller must already have checked the completion.
fn universally_close_pure_implication(
    requirements: Vec<Proposition>,
    conclusion: Proposition,
    variables: Vec<Variable>,
) -> Option<VerifiedPureTheorem> {
    let declared = variables.iter().copied().collect::<BTreeSet<_>>();
    if declared.len() != variables.len() {
        return None;
    }
    let mut occurring = BTreeSet::new();
    for proposition in requirements.iter().chain(std::iter::once(&conclusion)) {
        collect_proposition_bitvector_variables(proposition, &mut occurring);
    }
    if occurring != declared {
        return None;
    }
    let implication = requirements
        .into_iter()
        .rev()
        .fold(conclusion, |body, requirement| {
            Proposition::Implies(Box::new(requirement), Box::new(body))
        });
    let binders = variables
        .into_iter()
        .map(|var| (Default::default(), var, Sort::ProgramInt32))
        .collect::<Vec<_>>();
    let proposition = crate::kernel::quantifiers::close_foralls(&binders, &implication)?;
    Some(VerifiedPureTheorem {
        theorem: Theorem::new(proposition),
    })
}

/// Opens one verified concrete target as a local named-contract refinement
/// problem for a pure theorem proof, with the contract's value parameters
/// fixed to `values`.
///
/// No project search occurs: both names are exact map lookups, and a concrete
/// target must already carry a verified or explicitly external rule.
pub fn program_function_contract_refinement_context(
    environment: &ExecutionEnvironment,
    contract_name: &str,
    target_name: &str,
    values: &[ProgramValue],
) -> Option<FunctionContractRefinementContext> {
    program_function_contract_refinement_context_reporting(
        environment,
        contract_name,
        target_name,
        values,
    )
    .ok()
}

pub(crate) enum ConcreteRefinementRefusal {
    MissingContract,
    InvalidContractArguments,
    MissingTarget,
    ThrowingTarget,
    DifferentExceptionType,
    IncompatibleInterface,
    ContextUnavailable,
}

pub(crate) fn program_function_contract_refinement_context_reporting(
    environment: &ExecutionEnvironment,
    contract_name: &str,
    target_name: &str,
    values: &[ProgramValue],
) -> Result<FunctionContractRefinementContext, ConcreteRefinementRefusal> {
    use ConcreteRefinementRefusal::*;
    let contract = environment
        .get_function_contract(contract_name)
        .ok_or(MissingContract)?
        .instantiated(values)
        .ok_or(InvalidContractArguments)?;
    let checked = environment
        .get_verified_function_rule(target_name)
        .map(|rule| &rule.function)
        .or_else(|| {
            environment
                .get_external_function_rule(target_name)
                .map(|rule| &rule.function)
        });
    let declaration = checked
        .or_else(|| environment.get_function(target_name))
        .ok_or(MissingTarget)?;
    let required = contract.interface().exceptional_signature();
    let actual = declaration.contract_interface().exceptional_signature();
    if !actual.is_empty() && actual != required {
        return Err(if required.is_empty() {
            ThrowingTarget
        } else {
            DifferentExceptionType
        });
    }
    let function = checked.ok_or(MissingTarget)?;
    if !contract.has_compatible_signature_and_resource_vocabulary(function) {
        return Err(IncompatibleInterface);
    }
    let mut context = prepare_function_contract_refinement_context(
        &contract,
        function,
        &mut ExecutionBudget::for_new_execution(),
    )
    .ok_or(ContextUnavailable)?;
    context.object_type_requirements = function
        .contract_interface()
        .object_type_requirements()
        .clone();
    Ok(context)
}

/// Whether `function`'s contract refines the named contract `contract_name`,
/// by the judgment that forms `Contract(&function)` at a call: a trait
/// method implementation is checked once against the trait's interface,
/// which calls through the trait then assume. `function` must itself be
/// verified against its contract; this compares the two contracts only.
pub fn program_function_refines_named_contract(
    environment: &ExecutionEnvironment,
    contract_name: &str,
    function: &ProgramFunction,
) -> Result<bool, String> {
    let Some(contract) = environment.get_function_contract(contract_name) else {
        return Ok(false);
    };
    super::functions::function_refines_named_contract(
        contract,
        function,
        function.contract_interface().object_type_requirements(),
        &mut ExecutionBudget::for_new_execution(),
    )
    .map_err(ExecutionLimit::describe)
}

/// Whether `function`'s contract refines the contract `interface` is
/// verified against, as an override's must refine the virtual method's it
/// overrides: the same judgment as a named contract's.
pub fn program_function_refines_function_contract(
    _environment: &ExecutionEnvironment,
    interface: &ProgramFunction,
    function: &ProgramFunction,
) -> Result<bool, String> {
    let Some(contract) = FunctionContract::new(interface.name(), interface.clone()) else {
        return Ok(false);
    };
    super::functions::function_refines_named_contract(
        &contract,
        function,
        function.contract_interface().object_type_requirements(),
        &mut ExecutionBudget::for_new_execution(),
    )
    .map_err(ExecutionLimit::describe)
}

pub(crate) enum OverrideInterface<'a> {
    Named(&'a str),
    OnImplementation(&'a FunctionContract),
    Verified(&'a ProgramFunction),
}

pub(crate) enum OverrideRefusal {
    InterfaceUnavailable,
    UnprovedRequirement(usize),
    Incompatible,
}

pub(crate) fn program_override_refinement_failure(
    environment: &ExecutionEnvironment,
    interface: OverrideInterface<'_>,
    function: &ProgramFunction,
) -> ExecutionResult<Option<OverrideRefusal>> {
    let verified_contract;
    let contract = match interface {
        OverrideInterface::Named(name) => environment.get_function_contract(name),
        OverrideInterface::OnImplementation(contract) => Some(contract),
        OverrideInterface::Verified(interface) => {
            verified_contract = FunctionContract::new(interface.name(), interface.clone());
            verified_contract.as_ref()
        }
    };
    let Some(contract) = contract else {
        return Ok(Some(OverrideRefusal::InterfaceUnavailable));
    };
    let mut unproved = None;
    let refines = super::functions::function_refines_named_contract_reporting(
        contract,
        function,
        function.contract_interface().object_type_requirements(),
        &mut ExecutionBudget::for_new_execution(),
        Some(&mut unproved),
    )?;
    Ok(if refines {
        None
    } else {
        Some(unproved.map_or(
            OverrideRefusal::Incompatible,
            OverrideRefusal::UnprovedRequirement,
        ))
    })
}

/// The explicit refinement theorem a refused concrete formation needs.
///
/// Both names are exact map lookups into the same tables the formation check
/// reads, so the printed skeleton states the obligation that was refused.
///
/// `declared_parameter_spellings` lets the caller spell parameter types this
/// interface cannot: a struct pointer is kept as a layout, so the struct tag
/// comes from the contract's source declaration. A position left empty keeps
/// the spelling this interface derives from the modeled type.
pub fn program_named_contract_refinement_theorem_skeleton(
    environment: &ExecutionEnvironment,
    contract_name: &str,
    target_name: &str,
    declared_parameter_spellings: &[Option<String>],
) -> Option<String> {
    let contract = environment.get_function_contract(contract_name)?;
    let function = if let Some(rule) = environment.get_verified_function_rule(target_name) {
        &rule.function
    } else {
        &environment
            .get_external_function_rule(target_name)?
            .function
    };
    Some(named_contract_refinement_theorem_skeleton(
        contract,
        function,
        declared_parameter_spellings,
    ))
}

/// Opens one named contract as an implementation of another for the same
/// exact symbolic function-pointer value, each with its value parameters
/// fixed to its facts' values.
///
/// Both contract names are exact environment lookups. The source fact remains
/// an explicit premise of the theorem authority issued after refinement; this
/// operation does not infer contracts from a signature or inspect project
/// functions.
pub fn contract_refinement_context(
    environment: &ExecutionEnvironment,
    target_contract_name: &str,
    target_values: &[ProgramValue],
    source_contract_name: &str,
    source_values: &[ProgramValue],
    pointer: &ProgramValue,
) -> Option<FunctionContractRefinementContext> {
    let target = environment
        .get_function_contract(target_contract_name)?
        .instantiated(target_values)?;
    let source = environment
        .get_function_contract(source_contract_name)?
        .instantiated(source_values)?;
    let ProgramValue::Pointer(pointer) = pointer else {
        return None;
    };
    if pointer.program_type() != target.function_pointer_type()
        || pointer.program_type() != source.function_pointer_type()
        || !matches!(pointer.address().base, AddressBase::FunctionSymbolic(_))
        || !matches!(pointer.address().offset.view(), OffsetView::Constant(0))
    {
        return None;
    }
    let mut context = super::functions::contract_refinement_context_for_interface(
        &target,
        source.name(),
        source.interface(),
        &mut ExecutionBudget::for_new_execution(),
    )?;
    context.pointer = pointer.clone();
    context.function_value_arguments = source.value_arguments().to_vec();
    context.source_contract = Some(source);
    Some(context)
}

/// Returns the shared arbitrary argument values introduced by a refinement
/// theorem's `unfold(Contract)` step.
pub fn program_function_contract_refinement_arguments(
    context: &FunctionContractRefinementContext,
) -> &[ProgramValue] {
    &context.argument_values
}

pub fn program_function_contract_refinement_obligations(
    context: &FunctionContractRefinementContext,
) -> Option<FunctionContractRefinementObligations> {
    check_program_function_contract_refinement_obligations(context).ok()
}

pub(crate) use super::functions::ContractRefinementPreparationError;

pub(crate) fn check_program_function_contract_refinement_obligations(
    context: &FunctionContractRefinementContext,
) -> Result<FunctionContractRefinementObligations, ContractRefinementPreparationError> {
    prepare_contract_refinement_obligations(context)
}

impl FunctionContractRefinementObligations {
    pub fn entry(&self) -> &ExecutionState {
        &self.entry
    }
    pub fn post(&self) -> &ExecutionState {
        &self.post
    }
    pub fn proposition(&self) -> &Proposition {
        &self.proposition
    }
}

/// Issues contract authority only from the exact closed ordinary proof obligation.
pub(crate) fn prove_program_function_contract_refinement(
    obligations: &FunctionContractRefinementObligations,
    conclusion: Proposition,
    proof: &crate::kernel::proof::CheckedProposition,
) -> Option<VerifiedPureTheorem> {
    let context = &obligations.context;
    let Proposition::Predicate { name, arguments } = &conclusion else {
        return None;
    };
    // The fact names the pointer and then the values the contract's value
    // parameters were fixed to.
    let [
        state @ Term::ExecutionState(_),
        term_source_0 @ Term::ProgramValue(_),
        values @ ..,
    ] = arguments.as_slice()
    else {
        return None;
    };
    let (Some(ProgramValue::Pointer(pointer)),) = (term_source_0.program_value_native(),) else {
        return None;
    };
    if name != &context.contract.predicate_name()
        || pointer != &context.pointer
        || pointer.program_type() != context.contract.function_pointer_type()
        || values.len() != context.contract.value_arguments().len()
        || !values.iter().zip(context.contract.value_arguments()).all(
            |(term, value)| matches!(term, Term::ProgramValue(term) if term.old_form() == value),
        )
    {
        return None;
    }

    // Keep the original post-state point when checking the closed proof.
    if !proof.is_closed() || proof.proposition() != obligations.proposition() {
        return None;
    }
    let theorem = match &context.source_contract {
        None => {
            if context.pointer.address().base
                != AddressBase::Function(context.function_name.clone())
            {
                return None;
            }
            conclusion
        }
        Some(source) => {
            let AddressBase::FunctionSymbolic(variable) = &context.pointer.address().base else {
                return None;
            };
            let premise = Proposition::Predicate {
                name: source.predicate_name(),
                arguments: [
                    state.clone(),
                    Term::ProgramValue(ProgramValue::Pointer(context.pointer.clone()).into()),
                ]
                .into_iter()
                .chain(
                    source
                        .value_arguments()
                        .iter()
                        .cloned()
                        .map(|value| Term::ProgramValue(value.into())),
                )
                .collect(),
            };
            crate::kernel::quantifiers::close_forall(
                Default::default(),
                *variable,
                Sort::ProgramPointer(context.pointer.program_type()),
                &Proposition::Implies(Box::new(premise), Box::new(conclusion)),
            )?
        }
    };
    Some(VerifiedPureTheorem {
        theorem: Theorem::new(theorem),
    })
}

mod contract_interface_identity;

/// A checked one-call wrapper proves a contract implication. The wrapper's
/// only extra inputs are source contracts for its last, arbitrary callback
/// parameter. Its body must call precisely that parameter with every other
/// parameter in order. No target-contract assumption authorizes this call.
pub(crate) fn prove_executed_contract_refinement(
    environment: &ExecutionEnvironment,
    sources: &[(&str, Vec<ProgramValue>)],
    target_name: &str,
    conclusion: Proposition,
    rule: &VerifiedFunctionRule,
) -> Option<VerifiedPureTheorem> {
    if sources.is_empty() {
        return None;
    }
    let target = environment.get_function_contract(target_name)?;
    let target_values = executed_conclusion_values(&conclusion, target)?;
    let mut function = rule.function.clone();
    let callback = function.pop_parameter()?;
    if callback.program_type() != target.function_pointer_type() {
        return None;
    }
    pop_executed_value_pins(&mut function, &target_values)?;
    let arguments = executed_call_arguments(&function, target_values.len())?;
    let call = if function.return_type() == ProgramType::Void {
        ProgramStatement::Call {
            function_name: callback.name().to_string(),
            arguments,
            callee: None,
            dispatch: crate::kernel::CallDispatch::Direct,
            reference_binding: None,
        }
    } else {
        let (call, result) = program_call_value(0, callback.name(), arguments);
        program_seq(call, program_return(result))
    };
    if function.body() != &call || function.source_body() != &call {
        return None;
    }
    for (source_name, source_values) in sources.iter().rev() {
        let source = environment.get_function_contract(source_name)?;
        if callback.program_type() != source.function_pointer_type()
            || source_values.len() != source.interface().value_parameters().len()
        {
            return None;
        }
        let source_requirement =
            SpecProposition::Predicate {
                // A function-contract predicate denotes its closed interface,
                // independently of the caller's current population model.
                resource_state_dependent: false,
                name: source.predicate_name(),
                arguments: std::iter::once(SpecPredicateArgument::Value(
                    SpecExpression::ProgramExpression(ProgramExpression::Variable(
                        (callback.name().to_string()).into(),
                    )),
                ))
                .chain(source_values.iter().map(|value| {
                    SpecPredicateArgument::Value(SpecExpression::Value(value.clone()))
                }))
                .collect(),
            };
        if function.pop_contract_requirement()? != source_requirement {
            return None;
        }
    }
    let function = function.with_trailing_value_parameters(target_values.len())?;
    if !contract_interface_identity::same_interface(target, &function) {
        return None;
    }
    let Proposition::Predicate { name, arguments } = &conclusion else {
        return None;
    };
    let [
        state @ Term::ExecutionState(_),
        term_source_0 @ Term::ProgramValue(_),
        ..,
    ] = arguments.as_slice()
    else {
        return None;
    };
    let (Some(ProgramValue::Pointer(pointer)),) = (term_source_0.program_value_native(),) else {
        return None;
    };
    let AddressBase::FunctionSymbolic(variable) = pointer.address().base else {
        return None;
    };
    if name != &target.predicate_name()
        || pointer.program_type() != target.function_pointer_type()
        || !matches!(pointer.address().offset.view(), OffsetView::Constant(0))
    {
        return None;
    }
    let mut implication = conclusion.clone();
    for (source_name, source_values) in sources.iter().rev() {
        let premise = Proposition::Predicate {
            name: environment
                .get_function_contract(source_name)?
                .predicate_name(),
            arguments: [
                state.clone(),
                Term::ProgramValue(ProgramValue::Pointer(pointer.clone()).into()),
            ]
            .into_iter()
            .chain(
                source_values
                    .iter()
                    .cloned()
                    .map(|value| Term::ProgramValue(value.into())),
            )
            .collect(),
        };
        implication = Proposition::Implies(Box::new(premise), Box::new(implication));
    }
    Some(VerifiedPureTheorem {
        theorem: Theorem::new(crate::kernel::quantifiers::close_forall(
            Default::default(),
            variable,
            Sort::ProgramPointer(pointer.program_type()),
            &implication,
        )?),
    })
}

/// The values an execution theorem's conclusion fixes the target contract's
/// value parameters to, after its function pointer: one per parameter.
fn executed_conclusion_values(
    conclusion: &Proposition,
    target: &FunctionContract,
) -> Option<Vec<ProgramValue>> {
    let Proposition::Predicate { arguments, .. } = conclusion else {
        return None;
    };
    let values = arguments
        .get(2..)?
        .iter()
        .map(|argument| match argument {
            Term::ProgramValue(value) => Some(value.old_form().clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    (values.len() == target.interface().value_parameters().len()).then_some(values)
}

/// An execution theorem's one-call wrapper carries the target contract's
/// value parameters as its trailing parameters, each pinned to the
/// conclusion's value by a trailing requirement `parameter == value`: the
/// wrapper is verified for every value that equals it, which is the target
/// contract at those values. Pops and checks the pins.
fn pop_executed_value_pins(function: &mut ProgramFunction, values: &[ProgramValue]) -> Option<()> {
    let call_count = function.parameters().len().checked_sub(values.len())?;
    let parameters = function.parameters()[call_count..].to_vec();
    for (parameter, value) in parameters.iter().zip(values).rev() {
        let pin = SpecProposition::Comparison {
            left: SpecExpression::ProgramExpression(ProgramExpression::Variable(
                parameter.binding_name().clone(),
            )),
            operator: ComparisonOperator::Equal,
            right: SpecExpression::Value(value.clone()),
        };
        if function.pop_contract_requirement()? != pin {
            return None;
        }
    }
    Some(())
}

/// The arguments of the one call an execution wrapper makes: its call
/// parameters, in order, without the value parameters that trail them.
fn executed_call_arguments(
    function: &ProgramFunction,
    value_count: usize,
) -> Option<Vec<ProgramExpression>> {
    let call_count = function.parameters().len().checked_sub(value_count)?;
    Some(
        function.parameters()[..call_count]
            .iter()
            .map(|parameter| ProgramExpression::Variable(parameter.binding_name().clone()))
            .collect(),
    )
}

/// The declared interface of a verified or explicitly external project
/// function: its parameter types in order, then its return type. Two exact map
/// lookups, so a concrete `executes` clause is checked against the same C
/// signature the call rule will use.
pub fn program_project_function_signature(
    environment: &ExecutionEnvironment,
    name: &str,
) -> Option<(Vec<ProgramType>, ProgramType)> {
    let function = project_function_interface(environment, name)?;
    Some((
        function
            .parameters()
            .iter()
            .map(|parameter| parameter.program_type())
            .collect(),
        function.return_type(),
    ))
}

fn project_function_interface<'a>(
    environment: &'a ExecutionEnvironment,
    name: &str,
) -> Option<&'a ProgramFunction> {
    if let Some(rule) = environment.get_verified_function_rule(name) {
        return Some(&rule.function);
    }
    Some(&environment.get_external_function_rule(name)?.function)
}

/// A checked one-call wrapper proves that a named project function satisfies a
/// named contract. The wrapper takes the contract's own interface and no extra
/// inputs; its body must be precisely one call to `callee_name` with every
/// parameter in order, so what the wrapper was verified to do is what that one
/// call does. No target-contract assumption authorizes this call, and no
/// source contract is quantified over: the source is the callee's own verified
/// or explicitly external contract, already used by the checked call.
pub(crate) fn prove_executed_concrete_contract_refinement(
    environment: &ExecutionEnvironment,
    callee_name: &str,
    target_name: &str,
    conclusion: Proposition,
    rule: &VerifiedFunctionRule,
) -> Option<VerifiedPureTheorem> {
    let target = environment.get_function_contract(target_name)?;
    // The callee has to be a function this project has a rule for. An
    // unverified name would make the checked call vacuous.
    project_function_interface(environment, callee_name)?;
    let target_values = executed_conclusion_values(&conclusion, target)?;
    let mut function = rule.function.clone();
    pop_executed_value_pins(&mut function, &target_values)?;
    let arguments = executed_call_arguments(&function, target_values.len())?;
    let call = if function.return_type() == ProgramType::Void {
        ProgramStatement::Call {
            function_name: callee_name.to_string(),
            arguments,
            callee: None,
            dispatch: crate::kernel::CallDispatch::Direct,
            reference_binding: None,
        }
    } else {
        let (call, result) = program_call_value(0, callee_name, arguments);
        program_seq(call, program_return(result))
    };
    if function.body() != &call || function.source_body() != &call {
        return None;
    }
    let function = function.with_trailing_value_parameters(target_values.len())?;
    if !contract_interface_identity::same_interface(target, &function) {
        return None;
    }
    let Proposition::Predicate { name, arguments } = &conclusion else {
        return None;
    };
    let [
        Term::ExecutionState(_),
        term_source_0 @ Term::ProgramValue(_),
        ..,
    ] = arguments.as_slice()
    else {
        return None;
    };
    let (Some(ProgramValue::Pointer(pointer)),) = (term_source_0.program_value_native(),) else {
        return None;
    };
    if pointer.address().base != AddressBase::Function(callee_name.to_string()) {
        return None;
    }
    if name != &target.predicate_name()
        || pointer.program_type() != target.function_pointer_type()
        || !matches!(pointer.address().offset.view(), OffsetView::Constant(0))
    {
        return None;
    }
    Some(VerifiedPureTheorem {
        theorem: Theorem::new(conclusion),
    })
}

fn rewrite_int32_term_by_exact_equality(
    term: &OldMachineTerm,
    from: &OldMachineTerm,
    to: &OldMachineTerm,
) -> OldMachineTerm {
    if term == from {
        return to.clone();
    }
    let binary = |left: &OldMachineTerm, right: &OldMachineTerm| {
        (
            rewrite_int32_term_by_exact_equality(left, from, to),
            rewrite_int32_term_by_exact_equality(right, from, to),
        )
    };
    match term {
        OldMachineTerm::ThreadHandle(_) => term.clone(),
        OldMachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            ..
        } => term.clone(),

        binary_term!(Int32, Add, left, right) => {
            let (left, right) = binary(left, right);
            OldMachineTerm::add(left, right)
        }
        binary_term!(Int32, Subtract, left, right) => {
            let (left, right) = binary(left, right);
            OldMachineTerm::subtract(left, right)
        }
        OldMachineTerm::If {
            condition,
            then_term,
            else_term,
        } => OldMachineTerm::If {
            condition: condition.clone(),
            then_term: Box::new(rewrite_int32_term_by_exact_equality(then_term, from, to)),
            else_term: Box::new(rewrite_int32_term_by_exact_equality(else_term, from, to)),
        },
        OldMachineTerm::PureFunctionApplication { name, arguments } => {
            OldMachineTerm::rebuild_pure_application(
                name.clone(),
                arguments
                    .iter()
                    .map(|argument| rewrite_int32_term_by_exact_equality(argument, from, to))
                    .collect(),
            )
        }
        OldMachineTerm::ClickFunctionApplication { .. }
        | OldMachineTerm::PureApplicationCount(_)
        | OldMachineTerm::AlgebraicMatch { .. } => term.clone(),
        bits32_constant!(_)
        | OldMachineTerm::Variable(_)
        | OldMachineTerm::MemoryLoad(_, _, _)
        | OldMachineTerm::IntegerAddress(_, _)
        | int64_constant!(_)
        | uint64_constant!(_)
        | native_constant!(_, _)
        | cast_term!(Int64From32, _)
        | cast_term!(Int64FromUInt32, _)
        | cast_term!(UInt64From32, _)
        | cast_term!(UInt32From64, _)
        | cast_term!(UInt64FromInt32, _)
        | cast_term!(UInt64FromInt64, _)
        | crate::kernel::binary_wide_term!(..)
        | crate::kernel::unary_wide_term!(..)
        | OldMachineTerm::RangeFold { .. }
        | OldMachineTerm::BoolCast { .. }
        | OldMachineTerm::IntegerToMachine { .. } => term.clone(),
        term => match (term.as_binary(), term.as_unary()) {
            (Some((op, left, right)), _) => op.build_raw(
                rewrite_int32_term_by_exact_equality(left, from, to),
                rewrite_int32_term_by_exact_equality(right, from, to),
            ),
            (_, Some((op, value))) => {
                op.build_raw(rewrite_int32_term_by_exact_equality(value, from, to))
            }
            _ => unreachable!("every other variant has its own arm"),
        },
    }
}

/// Universally closes a pure int32 implication whose checked proof rewrote the
/// conclusion by an explicit ordered list of int32 equalities.
///
/// This is deliberately a certificate validator, and it neither proves the
/// conclusion nor proves a rewrite. `completion` carries the closed judgment,
/// exactly as in [`prove_universally_quantified_pure_implication`]. Each
/// supplied equality is *cited*: it must be exactly available among the
/// requirements (a requirement, or a conjunct of one), must actually rewrite
/// the equality goal reached so far, and is applied in the supplied
/// orientation. Reordering the list, dropping one, or naming an equality the
/// requirements do not contain is therefore rejected.
pub(crate) fn prove_universally_quantified_pure_implication_by_int32_rewrites(
    requirements: Vec<Proposition>,
    conclusion: Proposition,
    variables: Vec<Variable>,
    rewrites: Vec<Proposition>,
    completion: &crate::kernel::proof::CheckedProposition,
) -> Option<VerifiedPureTheorem> {
    if !checked_pure_implication_matches(&requirements, &conclusion, completion) {
        return None;
    }
    let mut goal = conclusion.clone();
    for rewrite in rewrites {
        crate::kernel::proof::fact_reasoning::exactly_available_fact(&rewrite, &requirements)?;
        let Some((
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left: from,
                right: to,
            },
            true,
        )) = rewrite.old_condition()
        else {
            return None;
        };
        let Some((
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            },
            true,
        )) = goal.old_condition()
        else {
            return None;
        };
        let rewritten_left = rewrite_int32_term_by_exact_equality(left, from, to);
        let rewritten_right = rewrite_int32_term_by_exact_equality(right, from, to);
        if &rewritten_left == left.as_ref() && &rewritten_right == right.as_ref() {
            return None;
        }
        goal = Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(rewritten_left),
                right: Box::new(rewritten_right),
            },
            true,
        );
    }
    universally_close_pure_implication(requirements, conclusion, variables)
}

/// Observe unsigned machine division in Integer arithmetic. Both domains
/// explicitly exclude a zero divisor; no no-wrap premise is needed.
pub fn prove_uint32_divide_to_integer(left: OldMachineTerm, right: OldMachineTerm) -> Theorem {
    prove_uint32_integer_division_bridge(left, right, false)
}

/// Observe unsigned machine remainder in nonnegative Integer arithmetic.
pub fn prove_uint32_remainder_to_integer(left: OldMachineTerm, right: OldMachineTerm) -> Theorem {
    prove_uint32_integer_division_bridge(left, right, true)
}

fn prove_uint32_integer_division_bridge(
    left: OldMachineTerm,
    right: OldMachineTerm,
    remainder: bool,
) -> Theorem {
    let observe = |value| {
        IntegerTerm::from_machine(MachineIntegerType::UInt32, value)
            .expect("every uint32 bit pattern has an unsigned Integer interpretation")
    };
    let dividend = observe(left.clone());
    let divisor = observe(right.clone());
    let native_nonzero = Proposition::condition_is(
        OldConditionTerm::equal(right.clone(), OldMachineTerm::constant(0)),
        false,
    );
    let integer_nonzero = Proposition::condition_is(
        OldConditionTerm::integer_not_equal(divisor.clone(), IntegerTerm::constant_i64(0)),
        true,
    );
    let (machine, exact) = if remainder {
        (
            OldMachineTerm::unsigned_remainder(left, right),
            IntegerTerm::TruncatingRemainder(dividend.into(), divisor.into()),
        )
    } else {
        (
            OldMachineTerm::unsigned_divide(left, right),
            IntegerTerm::TruncatingQuotient(dividend.into(), divisor.into()),
        )
    };
    let conclusion = Proposition::condition_is(
        OldConditionTerm::IntegerEqual(observe(machine).into(), exact.into()),
        true,
    );
    implication([native_nonzero, integer_nonzero], conclusion)
}

/// Exact mathematical observation of two unsigned 16-bit fields packed
/// into a 32- or 64-bit word. Both bounds are necessary: the fields must be
/// disjoint, and the high shift must preserve all bits.
pub fn prove_unsigned_pack_u16_to_integer(
    ty: MachineIntegerType,
    low: OldMachineTerm,
    high: OldMachineTerm,
) -> Option<Theorem> {
    prove_unsigned_pack_u16_in_order_to_integer(ty, low, high, false)
}

/// The same disjoint-field packing law for `(high << 16) | low`.
pub fn prove_unsigned_pack_u16_high_first_to_integer(
    ty: MachineIntegerType,
    low: OldMachineTerm,
    high: OldMachineTerm,
) -> Option<Theorem> {
    prove_unsigned_pack_u16_in_order_to_integer(ty, low, high, true)
}

fn prove_unsigned_pack_u16_in_order_to_integer(
    ty: MachineIntegerType,
    low: OldMachineTerm,
    high: OldMachineTerm,
    high_first: bool,
) -> Option<Theorem> {
    let (packed, low_bound, high_bound) = match ty {
        MachineIntegerType::UInt32 => (
            binary_node!(
                UInt32,
                BitwiseOr,
                low.clone().into(),
                binary_node!(
                    UInt32,
                    ShiftLeft,
                    high.clone().into(),
                    OldMachineTerm::uint32_constant(16).into(),
                )
                .into(),
            ),
            OldConditionTerm::unsigned_less_equal(low.clone(), OldMachineTerm::constant(65535)),
            OldConditionTerm::unsigned_less_equal(high.clone(), OldMachineTerm::constant(65535)),
        ),
        MachineIntegerType::UInt64 => (
            OldMachineTerm::uint64_bitwise_or(
                low.clone(),
                OldMachineTerm::uint64_shift_left(high.clone(), OldMachineTerm::int64_constant(16)),
            ),
            OldConditionTerm::uint64_less_equal(
                low.clone(),
                OldMachineTerm::uint64_constant(65535),
            ),
            OldConditionTerm::uint64_less_equal(
                high.clone(),
                OldMachineTerm::uint64_constant(65535),
            ),
        ),
        _ => return None,
    };
    let packed = if high_first {
        match ty {
            MachineIntegerType::UInt32 => binary_node!(
                UInt32,
                BitwiseOr,
                binary_node!(
                    UInt32,
                    ShiftLeft,
                    high.clone().into(),
                    OldMachineTerm::uint32_constant(16).into(),
                )
                .into(),
                low.clone().into(),
            ),
            MachineIntegerType::UInt64 => OldMachineTerm::uint64_bitwise_or(
                OldMachineTerm::uint64_shift_left(high.clone(), OldMachineTerm::int64_constant(16)),
                low.clone(),
            ),
            _ => unreachable!("packing accepts unsigned word types"),
        }
    } else {
        packed
    };
    let observe = |value| IntegerTerm::from_machine(ty, value);
    let exact = IntegerTerm::Add(
        observe(low)?.into(),
        IntegerTerm::Multiply(
            IntegerTerm::constant_i64(65536).into(),
            observe(high)?.into(),
        )
        .into(),
    );
    Some(implication(
        [
            Proposition::condition_is(low_bound, true),
            Proposition::condition_is(high_bound, true),
        ],
        Proposition::condition_is(
            OldConditionTerm::integer_equal(observe(packed)?, exact),
            true,
        ),
    ))
}

/// Recover the low word of `(high << 16) | low` for two bounded uint16 fields.
/// The bounds are part of the issued theorem, never inferred from its operands.
pub fn prove_uint32_unpack_uint16_low(low: OldMachineTerm, high: OldMachineTerm) -> Theorem {
    prove_uint32_unpack_uint16_word(low, high, false)
}

/// Recover the high word using an unsigned (logical) right shift and mask.
pub fn prove_uint32_unpack_uint16_high(low: OldMachineTerm, high: OldMachineTerm) -> Theorem {
    prove_uint32_unpack_uint16_word(low, high, true)
}

fn prove_uint32_unpack_uint16_word(
    low: OldMachineTerm,
    high: OldMachineTerm,
    high_word: bool,
) -> Theorem {
    // Each bound confines the field to 16 bits. Shifting high left 16 then
    // ORing low puts the fields in disjoint halves without discarding high
    // bits. Masking selects the low half; logically shifting right first
    // selects the high half, including when the packed word's sign bit is set.
    let packed = binary_node!(
        UInt32,
        BitwiseOr,
        binary_node!(
            UInt32,
            ShiftLeft,
            high.clone().into(),
            OldMachineTerm::uint32_constant(16).into()
        )
        .into(),
        low.clone().into(),
    );
    let selected = if high_word {
        binary_node!(
            UInt32,
            ShiftRight,
            packed.into(),
            OldMachineTerm::uint32_constant(16).into()
        )
    } else {
        packed
    };
    let extracted = binary_node!(
        UInt32,
        BitwiseAnd,
        selected.into(),
        OldMachineTerm::uint32_constant(65535).into()
    );
    let exact = if high_word { high.clone() } else { low.clone() };
    implication(
        [
            Proposition::condition_is(
                OldConditionTerm::unsigned_less_equal(low, OldMachineTerm::constant(65535)),
                true,
            ),
            Proposition::condition_is(
                OldConditionTerm::unsigned_less_equal(high, OldMachineTerm::constant(65535)),
                true,
            ),
        ],
        Proposition::condition_is(OldConditionTerm::uint32_equal(extracted, exact), true),
    )
}

/// Recover a bounded uint16 field from the LP64 C packing expression.
/// Both bounds are necessary: no operand may overlap the other field.
fn prove_uint64_unpack_uint16_word(
    low: OldMachineTerm,
    high: OldMachineTerm,
    high_word: bool,
) -> Theorem {
    let packed = OldMachineTerm::uint64_bitwise_or(
        low.clone(),
        OldMachineTerm::uint64_shift_left(high.clone(), OldMachineTerm::int64_constant(16)),
    );
    let selected = if high_word {
        OldMachineTerm::uint64_logical_shift_right(packed, OldMachineTerm::int64_constant(16))
    } else {
        packed
    };
    let extracted =
        OldMachineTerm::uint64_bitwise_and(selected, OldMachineTerm::uint64_constant(65535));
    let exact = if high_word { high.clone() } else { low.clone() };
    implication(
        [
            Proposition::condition_is(
                OldConditionTerm::uint64_less_equal(low, OldMachineTerm::uint64_constant(65535)),
                true,
            ),
            Proposition::condition_is(
                OldConditionTerm::uint64_less_equal(high, OldMachineTerm::uint64_constant(65535)),
                true,
            ),
        ],
        Proposition::condition_is(OldConditionTerm::uint64_equal(extracted, exact), true),
    )
}

/// The `uint64` kernel laws: 16-bit packing and unpacking, and exact
/// division and remainder observations. Division and remainder exclude zero
/// in both evaluation domains, but impose no bound on the dividend.
pub fn prove_uint64_integer_bridge(
    name: &str,
    left: OldMachineTerm,
    right: OldMachineTerm,
) -> Option<Theorem> {
    if name == "click::integer::uint64_pack_uint16_to_integer" {
        return prove_unsigned_pack_u16_to_integer(MachineIntegerType::UInt64, left, right);
    }
    if matches!(
        name,
        "click::integer::uint64_unpack_uint16_low" | "click::integer::uint64_unpack_uint16_high"
    ) {
        return Some(prove_uint64_unpack_uint16_word(
            left,
            right,
            name == "click::integer::uint64_unpack_uint16_high",
        ));
    }
    if !matches!(
        name,
        "click::integer::uint64_divide_to_integer" | "click::integer::uint64_remainder_to_integer"
    ) {
        return None;
    }
    let observe = |value| {
        IntegerTerm::from_machine(MachineIntegerType::UInt64, value)
            .expect("every uint64 bit pattern has an unsigned Integer interpretation")
    };
    let a = observe(left.clone());
    let b = observe(right.clone());
    let native_nonzero = Proposition::condition_is(
        OldConditionTerm::uint64_equal(right.clone(), OldMachineTerm::uint64_constant(0)),
        false,
    );
    let integer_nonzero = Proposition::condition_is(
        OldConditionTerm::integer_not_equal(b.clone(), IntegerTerm::constant_i64(0)),
        true,
    );
    let (machine, exact) = if name == "click::integer::uint64_divide_to_integer" {
        (
            OldMachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Divide,
                left: left.into(),
                right: right.into(),
            },
            IntegerTerm::TruncatingQuotient(a.into(), b.into()),
        )
    } else {
        (
            OldMachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Remainder,
                left: left.into(),
                right: right.into(),
            },
            IntegerTerm::TruncatingRemainder(a.into(), b.into()),
        )
    };
    let conclusion = Proposition::condition_is(
        OldConditionTerm::IntegerEqual(observe(machine).into(), exact.into()),
        true,
    );
    Some(implication([native_nonzero, integer_nonzero], conclusion))
}

/// Exact mathematical remainder of a defined signed 32-bit operation.
/// Both zero division and MIN / -1 are excluded by the native definedness
/// premise, even though mathematical remainder itself has no overflow.
pub fn prove_int32_remainder_to_integer(left: OldMachineTerm, right: OldMachineTerm) -> Theorem {
    let observe = |value| {
        IntegerTerm::from_machine(MachineIntegerType::Int32, value)
            .expect("typed operands have exact Integer interpretations")
    };
    let native_defined =
        Proposition::signed_division_defined(MachineIntegerType::Int32, &left, &right);
    let integer_nonzero = Proposition::condition_is(
        OldConditionTerm::integer_not_equal(observe(right.clone()), IntegerTerm::constant_i64(0)),
        true,
    );
    let exact = IntegerTerm::truncating_remainder(observe(left.clone()), observe(right.clone()));
    let machine = binary_node!(Int32, Remainder, left.into(), right.into());
    implication(
        [native_defined, integer_nonzero],
        Proposition::condition_is(
            OldConditionTerm::IntegerEqual(observe(machine).into(), exact.into()),
            true,
        ),
    )
}

/// The theorem `premises[0] implies (premises[1] implies (... conclusion))`.
fn implication<const N: usize>(premises: [Proposition; N], conclusion: Proposition) -> Theorem {
    Theorem::new(
        premises
            .into_iter()
            .rev()
            .fold(conclusion, |body, premise| {
                Proposition::Implies(Box::new(premise), Box::new(body))
            }),
    )
}

#[cfg(test)]
fn uint32_implication(premise: OldConditionTerm, conclusion: OldConditionTerm) -> Theorem {
    implication(
        [Proposition::condition_is(premise, true)],
        Proposition::condition_is(conclusion, true),
    )
}

#[cfg(test)]
fn uint32_transitivity(
    first: OldConditionTerm,
    second: OldConditionTerm,
    conclusion: OldConditionTerm,
) -> Theorem {
    implication(
        [
            Proposition::condition_is(first, true),
            Proposition::condition_is(second, true),
        ],
        Proposition::condition_is(conclusion, true),
    )
}

/// Unsigned non-strict order followed by strict order is strict order.
#[cfg(test)]
pub fn prove_uint32_le_lt_transitive(
    first: OldMachineTerm,
    middle: OldMachineTerm,
    last: OldMachineTerm,
) -> Theorem {
    uint32_transitivity(
        OldConditionTerm::unsigned_less_equal(first.clone(), middle.clone()),
        OldConditionTerm::unsigned_less_than(middle, last.clone()),
        OldConditionTerm::unsigned_less_than(first, last),
    )
}

/// `lower < greater` and `greater > lower` are one uint32 order.
#[cfg(test)]
pub fn prove_uint32_lt_implies_reversed_gt(
    lower: OldMachineTerm,
    greater: OldMachineTerm,
) -> Theorem {
    uint32_implication(
        OldConditionTerm::unsigned_less_than(lower.clone(), greater.clone()),
        OldConditionTerm::unsigned_greater_than(greater, lower),
    )
}

/// `greater >= lower` and `lower <= greater` are one uint32 order.
#[cfg(test)]
pub fn prove_uint32_ge_implies_reversed_le(
    greater: OldMachineTerm,
    lower: OldMachineTerm,
) -> Theorem {
    uint32_implication(
        OldConditionTerm::unsigned_greater_equal(greater.clone(), lower.clone()),
        OldConditionTerm::unsigned_less_equal(lower, greater),
    )
}

#[cfg(test)]
mod retained_fold_law_tests {
    use super::*;
    use crate::kernel::{
        KernelTerm, KernelTermExport, KernelTermImport, KernelType, VerificationSession,
    };

    fn endpoint(native: &OldMachineTerm) -> SharedIntegerRangeEndpoint {
        let root = KernelTermImport::default()
            .machine_arithmetic(MachineIntegerType::Int32, native)
            .unwrap();
        SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(0))
            .with_shared_operand(root)
            .unwrap()
    }

    #[test]
    fn retained_endpoint_shifts_match_the_existing_word_constructors() {
        let _session = VerificationSession::enter();
        for format in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
            let constant = |n| {
                if format == MachineIntegerType::Int32 {
                    OldMachineTerm::constant(n as u32)
                } else {
                    OldMachineTerm::uint64_constant(n)
                }
            };
            let x = OldMachineTerm::Variable(Variable(1005000));
            let raw = |op, a, b| OldMachineTerm::Binary {
                format,
                op,
                left: Box::new(a),
                right: Box::new(b),
            };
            let mut cases = vec![
                x.clone(),
                constant(0),
                constant(1),
                constant(u64::MAX),
                raw(MachineBinaryOp::Add, x.clone(), constant(1)),
                raw(MachineBinaryOp::Add, constant(1), x.clone()),
                raw(MachineBinaryOp::Subtract, x, constant(1)),
                raw(MachineBinaryOp::Add, constant(2), constant(3)),
            ];
            if format == MachineIntegerType::UInt64 {
                cases.push(OldMachineTerm::Cast {
                    spelling: MachineCastSpelling::Generic,
                    from: MachineIntegerType::Int32,
                    to: format,
                    value: Box::new(OldMachineTerm::constant(7)),
                });
            }
            for native in cases {
                for operation in [MachineBinaryOp::Add, MachineBinaryOp::Subtract] {
                    let end = endpoint(&native);
                    let exports = KernelTermExport::machine_export_count();
                    let shifted = shifted_fold_endpoint(&end, format, operation);
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                    let expected = OldMachineTerm::machine_binary(
                        format,
                        operation,
                        native.clone(),
                        constant(1),
                    );
                    assert_eq!(
                        shifted.value(),
                        &expected,
                        "{format:?} {operation:?}: {native:?}"
                    );
                }
            }
        }
    }

    mod scaling_tests {
        use super::*;
        include!("../scaling_tests/kernel/api/retained_fold_law_tests.rs");
    }
}

#[cfg(test)]
mod retained_lowering_result_tests {
    use super::*;
    use crate::kernel::{ExecutionValue, KernelTermExport, KernelType, VerificationSession};

    #[test]
    fn common_lowering_result_keeps_typed_root_and_scoped_obligations() {
        let _session = VerificationSession::enter();
        let state = ExecutionState::new();
        let assumptions = PureFactContext::new();
        let expressions = [
            SpecExpression::Add(
                Box::new(SpecExpression::Value(ProgramValue::Int32(
                    OldMachineTerm::Variable(Variable(999992)),
                ))),
                Box::new(SpecExpression::Value(ProgramValue::Int32(
                    OldMachineTerm::constant(1),
                ))),
            ),
            SpecExpression::IntegerToMachine {
                value: Box::new(SpecIntegerExpression::Term(IntegerTerm::Variable(
                    Variable(999993),
                ))),
                destination: MachineIntegerType::Int32,
            },
        ];
        for (index, expression) in expressions.iter().enumerate() {
            let native =
                evaluate_speprogram_expression_path(&state, expression, None, &assumptions)
                    .unwrap();
            let expected = native.value.clone().into_native();
            let exports = KernelTermExport::machine_export_count();
            let retained =
                program_evaluate_retained_spec_expression(&state, expression, None, &assumptions)
                    .unwrap();
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert_eq!(
                retained.value.ty(),
                &KernelType::Program(ProgramType::Int32)
            );
            assert_eq!(retained.facts, native.facts);
            assert_eq!(retained.obligations, native.obligations);
            if index == 1 {
                assert!(
                    !retained.obligations.is_empty(),
                    "conversion bounds remain obligations"
                );
            }
            assert_eq!(
                ExecutionValue::Shared(retained.value).into_native(),
                expected
            );
        }
    }

    mod scaling_tests {
        use super::*;
        include!("../scaling_tests/kernel/api/retained_lowering_result_tests.rs");
    }
}
