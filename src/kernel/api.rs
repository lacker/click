use super::functions::{
    apply_verified_contract_resource_transition,
    construct_c_function_resource as construct_c_function_resource_checked,
    evaluate_function_resource_context_with_metadata, expand_composite_resource_fact_with_children,
    function_return_resources_definitionally_established,
};
use super::loans::{
    BorrowedContractInputBacking, LoanLedger, LoanRefusal, LoanRefusalDiagnostic,
    LoanRefusalOperation, LoanRefusalSubject, LoanViewBinding, LoanViewBindings,
};
pub(super) use super::memory_provenance::*;
use super::prelude::*;
pub(super) use super::resource_tracker::cell_source::*;
use crate::instrumentation::ArtifactReuseRejection;
use crate::kernel::ResourceDescription;
use std::sync::Arc;

mod uint32_representation;
pub use uint32_representation::prove_declared_uint32_from_bytes;

#[cfg(test)]
thread_local! {
    static CHECKED_FUNCTION_BODY_EXECUTIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

thread_local! {
    /// The borrowed-input roots and abstract mutex reservations installed for each function in this
    /// verification session, keyed by function name and holding the exact
    /// entry state they were installed on. Every proof unit of one function
    /// (each claim proof, loop proof, and certification) must share one
    /// entry authority: a loan ledger's identity is opaque and fresh, so two
    /// installs would be two different authorities and no completion from
    /// one could certify a claim at the other. The pre-install state is
    /// compared exactly, once per proof unit; a function whose entry state
    /// changed simply gets a new root.
    static BORROWED_INPUT_ROOTS: std::cell::RefCell<BTreeMap<String, (CState, CState)>> =
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
    pub(crate) index: Bitvector32Term,
    pub(crate) count: Bitvector32Term,
    pub(crate) stride: u32,
}

pub(crate) fn memory_access_element_bound(
    memory: &CMemory,
    pointer: &Pointer,
    byte_width: u32,
) -> Option<MemoryAccessElementBound> {
    let size = memory.block_size(&pointer.block)?;
    let mut pending = vec![&pointer.offset];
    let mut widest: Option<(&Bitvector32Term, u32)> = None;
    while let Some(term) = pending.pop() {
        match term {
            PointerOffsetTerm::Add(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            // A widened index is spelled as the C index it widens: a
            // `uint32` index zero-extends to the 64-bit offset.
            PointerOffsetTerm::Int32Scaled { value, byte_width }
            | PointerOffsetTerm::Int64Scaled {
                value, byte_width, ..
            } => {
                let value = match value.as_ref() {
                    Bitvector32Term::UInt64From32(index) => index,
                    value => value,
                };
                let stride = u32::try_from(*byte_width).ok()?;
                if widest.is_none_or(|(_, widest)| stride > widest) {
                    widest = Some((value, stride));
                }
            }
            PointerOffsetTerm::Constant(_) => {}
            PointerOffsetTerm::Variable(_) => return None,
        }
    }
    let (index, stride) = widest?;
    if stride < byte_width {
        return None;
    }
    Some(MemoryAccessElementBound {
        index: index.clone(),
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
use contract_certification::{
    certification_proves_condition_from_verified_pure_implication,
    contract_resource_condition_cases, prove_symbolic_c_function_verification_paths,
    resources_certify_loadability,
};

pub fn int32(bits: impl Into<Bitvector32Term>) -> CValue {
    CValue::Int32(bits.into())
}

pub fn bool_value(bits: impl Into<Bitvector32Term>) -> CValue {
    let bits = bits.into();
    CValue::Bool(Bitvector32Term::if_then_else(
        ConditionTerm::equal(bits, Bitvector32Term::Constant(0)),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    ))
}

/// The range fact `value == 0 or value == 1` of a `_Bool` rvalue, when its
/// term is structurally normalized.
///
/// A C `_Bool` object holds only `0` or `1`, and a `_Bool` value built by
/// [`bool_value`] or by a symbolic `_Bool` load is a conditional whose arms
/// are exactly those constants. Neither disjunct is provable alone, so without
/// this fact a proof would need an explicit case split to state the type's
/// own range. The fact is returned only when every leaf of the term is the
/// constant `0` or `1`, so it is context-free true by construction and never
/// trusts the `CValue::Bool` invariant. A constant has nothing left to state
/// and yields `None`. The walk is bounded by the term's conditional spine.
pub(crate) fn c_bool_range_fact(value: &CValue) -> Option<Proposition> {
    fn leaves_are_zero_or_one(term: &Bitvector32Term) -> bool {
        match term {
            Bitvector32Term::Constant(0 | 1) => true,
            Bitvector32Term::If {
                then_term,
                else_term,
                ..
            } => leaves_are_zero_or_one(then_term) && leaves_are_zero_or_one(else_term),
            _ => false,
        }
    }
    let CValue::Bool(term) = value else {
        return None;
    };
    if !matches!(term, Bitvector32Term::If { .. }) || !leaves_are_zero_or_one(term) {
        return None;
    }
    let equals = |constant| {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(term.clone()),
                Box::new(Bitvector32Term::Constant(constant)),
            ),
            true,
        )
    };
    Some(Proposition::Or(Box::new(equals(0)), Box::new(equals(1))))
}

/// The range `[lower, upper]` every value of a narrow C integer type lies
/// in, with the term holding it: a `uint8` is in `[0, 255]`, an `int16` in
/// `[-32768, 32767]`. `None` for every other type, whose range is its word.
pub(crate) fn c_narrow_integer_range(value: &CValue) -> Option<(&Bitvector32Term, i32, i32)> {
    match value {
        CValue::Int8(term) => Some((term, i32::from(i8::MIN), i32::from(i8::MAX))),
        CValue::Int16(term) => Some((term, i32::from(i16::MIN), i32::from(i16::MAX))),
        CValue::UInt8(term) => Some((term, 0, i32::from(u8::MAX))),
        CValue::UInt16(term) => Some((term, 0, i32::from(u16::MAX))),
        _ => None,
    }
}

/// The type range `lower <= value` and `value <= upper` of a narrow integer
/// value that is not a constant, as the facts every reader of the value may
/// use.
///
/// Click never truncates: each conversion into a narrow type owes the
/// obligation that its operand is in the type's range, so a narrow value is
/// in range wherever one exists. A parameter's entry value is one such value
/// (the caller's argument was converted to the parameter's type), so its
/// range is an entry fact of the function, stated once where the value is
/// introduced instead of at each use.
pub(crate) fn c_narrow_integer_range_facts(value: &CValue) -> Option<Vec<Proposition>> {
    let (term, lower, upper) = c_narrow_integer_range(value)?;
    if term.as_const().is_some() {
        return None;
    }
    let mut facts = vec![
        Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(
                term.clone(),
                Bitvector32Term::Constant(lower as u32),
            ),
            true,
        ),
        Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(term.clone(), Bitvector32Term::Constant(upper as u32)),
            true,
        ),
    ];
    // An unsigned type's range is also an unsigned bound. The closers do
    // not yet bridge the signed pair to it, and a widening to `uint32` is
    // read in that order, so it is stated beside them.
    if lower == 0 {
        facts.push(Proposition::ConditionIs(
            ConditionTerm::unsigned_less_equal(
                term.clone(),
                Bitvector32Term::Constant(upper as u32),
            ),
            true,
        ));
    }
    Some(facts)
}

pub fn int8(bits: impl Into<Bitvector32Term>) -> CValue {
    CValue::Int8(bits.into())
}

pub fn int16(bits: impl Into<Bitvector32Term>) -> CValue {
    CValue::Int16(bits.into())
}

pub fn uint8(bits: impl Into<Bitvector32Term>) -> CValue {
    CValue::UInt8(bits.into())
}

pub fn uint16(bits: impl Into<Bitvector32Term>) -> CValue {
    CValue::UInt16(bits.into())
}

pub fn uint32(bits: impl Into<Bitvector32Term>) -> CValue {
    CValue::UInt32(bits.into())
}

pub fn int64(bits: impl Into<Bitvector32Term>) -> CValue {
    CValue::Int64(bits.into())
}

pub fn uint64(bits: impl Into<Bitvector32Term>) -> CValue {
    CValue::UInt64(bits.into())
}

pub fn float32(bits: impl Into<Bitvector32Term>) -> CValue {
    CValue::Float32(bits.into())
}

pub fn float64(bits: impl Into<Bitvector32Term>) -> CValue {
    CValue::Float64(bits.into())
}

/// True when `pointer` addresses within a live heap allocation of `memory`,
/// matching allocation keys through the path's pointer equalities or exact
/// materialization of loads embedded in the key and pointer forms.
pub(crate) fn c_memory_holds_live_heap_allocation_at(
    memory: &super::CMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    memory.is_live_heap_address(pointer, assumptions)
        || memory.heap_live_allocation_bases().any(|base| {
            base.block == pointer.block
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
pub fn c_condition_facts_match_for_transport(
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
        && assumptions.condition_matches(source_condition, target_condition)
}

/// The `transport` rule for one bare condition: `context` states it, it
/// holds by memory resolution from the facts in `context`, or a quantified
/// fact instantiated at its terms states it.
fn condition_target_reaches(context: &PureFactContext, target: &Proposition) -> bool {
    let Proposition::ConditionIs(condition, value) = target else {
        return false;
    };
    context.proves_exact(target)
        || contract_certification::condition_holds_by_memory_resolution(context, condition, *value)
        || contract_certification::condition_holds_by_instantiated_fact(
            context,
            condition,
            *value,
            &|premise| transport_premise_holds(context, premise),
        )
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
/// the other side to a newer snapshot.
pub(crate) fn c_condition_fact_target_reaches_in_context(
    source: &Proposition,
    target: &Proposition,
    assumptions: &PureFactContext,
) -> bool {
    if !matches!(source, Proposition::ConditionIs(_, _))
        || !matches!(target, Proposition::ConditionIs(_, _))
    {
        return false;
    }
    let with_source = assumptions.clone().assume_proposition(source.clone());
    condition_target_reaches(&with_source, target)
}

/// Exports target-directed transport only when every contextual dependency
/// can be retained as an explicit theorem premise. Callers that merely need
/// to check a fact inside one live context use the context-bound predicate
/// above instead of turning that context into reusable authority.
pub fn prove_c_condition_fact_target_transport(
    source: &Proposition,
    target: &Proposition,
    assumptions: &PureFactContext,
) -> Option<Theorem> {
    let (proved, premises) = crate::kernel::collect_reasoning_provenance(|| {
        crate::kernel::capture_implicit_reasoning_provenance(|| {
            c_condition_fact_target_reaches_in_context(source, target, assumptions)
        })
    });
    if !proved {
        return None;
    }
    // Provenance collection proposes an output-sized premise set; it is not
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
        .then(|| c_condition_fact_transport_theorem(source, target.clone(), premises))
}

#[derive(Clone, Debug)]
pub struct CLoopPreservationContext {
    state: CState,
    /// Retain the exact frame paired with this persistent body checkpoint.
    /// Rebuilding an equal loop head gives a different mutation history.
    exit_frame: Option<ResourceContext>,
    loop_entry_state: CState,
    pure_facts: Vec<Proposition>,
    /// One selected semantic proposition per declared invariant, including
    /// clauses already present in the ambient fact context.
    invariant_propositions: Vec<Proposition>,
    whole_loop_effect_facts: Vec<Proposition>,
    /// The binders this loop's `owns name: resource(...)` clauses declare.
    /// The back edge binds those names again on whatever the body ends
    /// holding, so the join needs them beside the head state.
    binders: Vec<crate::kernel::CLoopBinder>,
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
    pointer_carriers: std::collections::BTreeMap<String, CPointerValue>,
}

/// A body state produced by a checked preservation proof that may be the
/// final loop iteration. A guard-exit candidate requires an independently
/// checked false post-body condition. A natural cycle's checked forward jump
/// instead carries its target and is exported at its own state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CLoopFinalExitCandidate {
    state: CState,
    jump_target: Option<CControlTargetId>,
    /// A checked exit is copied into the loop rule; its facts stay shared.
    pure_facts: std::sync::Arc<[Proposition]>,
    loan_evidence: crate::kernel::loans::CheckedLoanCallEvidenceSequence,
}

impl CLoopFinalExitCandidate {
    pub(crate) fn new(state: CState, pure_facts: Vec<Proposition>) -> Self {
        crate::instrumentation::record_deterministic_work(pure_facts.len());
        Self {
            state,
            jump_target: None,
            pure_facts: pure_facts.into(),
            loan_evidence: crate::kernel::loans::empty_checked_loan_evidence_sequence(),
        }
    }

    pub(crate) fn with_jump_target(mut self, target: CControlTargetId) -> Self {
        self.jump_target = Some(target);
        self
    }

    pub(crate) fn jump_target(&self) -> Option<CControlTargetId> {
        self.jump_target
    }

    pub(crate) fn with_loan_evidence(
        mut self,
        loan_evidence: crate::kernel::loans::CheckedLoanCallEvidenceSequence,
    ) -> Self {
        self.loan_evidence = loan_evidence;
        self
    }

    pub(crate) fn state(&self) -> &CState {
        &self.state
    }

    pub(crate) fn pure_facts(&self) -> &[Proposition] {
        &self.pure_facts
    }

    pub(crate) fn loan_evidence(&self) -> &crate::kernel::loans::CheckedLoanCallEvidenceSequence {
        &self.loan_evidence
    }
}

/// One certified body path that left the loop through `break`.
///
/// A `break` is an exit, not a back edge: the invariants are not closed on
/// it and no measure is required to decrease. The proof layer supplies the
/// state the path reached and the facts retained there; the loop rule joins
/// every break exit with the guard-false exit into the single successor the
/// enclosing frontier continues from, so no way out of the loop is dropped.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CLoopBreakExit {
    state: CState,
    /// A checked exit is copied into the loop rule; its facts stay shared.
    pure_facts: std::sync::Arc<[Proposition]>,
    loan_evidence: crate::kernel::loans::CheckedLoanCallEvidenceSequence,
}

impl CLoopBreakExit {
    pub(crate) fn new(state: CState, pure_facts: Vec<Proposition>) -> Self {
        crate::instrumentation::record_deterministic_work(pure_facts.len());
        Self {
            state,
            pure_facts: pure_facts.into(),
            loan_evidence: crate::kernel::loans::empty_checked_loan_evidence_sequence(),
        }
    }

    pub(crate) fn with_loan_evidence(
        mut self,
        loan_evidence: crate::kernel::loans::CheckedLoanCallEvidenceSequence,
    ) -> Self {
        self.loan_evidence = loan_evidence;
        self
    }

    pub(crate) fn state(&self) -> &CState {
        &self.state
    }

    pub(crate) fn pure_facts(&self) -> &[Proposition] {
        &self.pure_facts
    }

    pub(crate) fn loan_evidence(&self) -> &crate::kernel::loans::CheckedLoanCallEvidenceSequence {
        &self.loan_evidence
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
pub(crate) struct CLoopReturnExit {
    value: CValue,
    state: CState,
    /// A checked exit is copied into the loop rule; its facts stay shared.
    pure_facts: std::sync::Arc<[Proposition]>,
    loan_evidence: crate::kernel::loans::CheckedLoanCallEvidenceSequence,
}

impl CLoopReturnExit {
    pub(crate) fn new(value: CValue, state: CState, pure_facts: Vec<Proposition>) -> Self {
        crate::instrumentation::record_deterministic_work(pure_facts.len());
        Self {
            value,
            state,
            pure_facts: pure_facts.into(),
            loan_evidence: crate::kernel::loans::empty_checked_loan_evidence_sequence(),
        }
    }

    pub(crate) fn with_loan_evidence(
        mut self,
        loan_evidence: crate::kernel::loans::CheckedLoanCallEvidenceSequence,
    ) -> Self {
        self.loan_evidence = loan_evidence;
        self
    }

    pub(crate) fn value(&self) -> &CValue {
        &self.value
    }

    pub(crate) fn state(&self) -> &CState {
        &self.state
    }

    pub(crate) fn pure_facts(&self) -> &[Proposition] {
        &self.pure_facts
    }

    pub(crate) fn loan_evidence(&self) -> &crate::kernel::loans::CheckedLoanCallEvidenceSequence {
        &self.loan_evidence
    }
}

#[cfg(test)]
mod loop_exit_sharing_tests {
    use super::*;

    #[test]
    fn natural_forward_exit_is_a_jump_and_only_absent_exits_diverge() {
        let backedge = CControlTargetId(1);
        let exit_target = CControlTargetId(2);
        let statement = c_while(c_int32_literal(1), Vec::new(), c_goto(backedge))
            .with_backedge_target(backedge)
            .with_natural_exit_target(exit_target);
        let check = |candidates| {
            prove_symbolic_c_loop_exit_with_proven_phases(
                CState::new(),
                statement.clone(),
                PureFactContext::new(),
                CExecutionEnvironment::new(),
                true,
                true,
                candidates,
                Vec::new(),
                Vec::new(),
            )
        };
        let (_, returned) = check(vec![
            CLoopFinalExitCandidate::new(CState::new(), Vec::new()).with_jump_target(exit_target),
        ]);
        let returned = returned.expect("a checked forward jump must form a loop rule");
        assert_eq!(returned.paths.len(), 1);
        assert!(matches!(
            returned.paths[0].outcome,
            CStatementOutcome::Jump { target, .. } if target == exit_target
        ));
        let (_, divergent) = check(Vec::new());
        let divergent = divergent.expect("a loop with no reachable exits can diverge");
        assert_eq!(divergent.paths.len(), 1);
        assert!(matches!(
            divergent.paths[0].outcome,
            CStatementOutcome::VerificationDiverges
        ));
        let (_, invalid) = check(vec![
            CLoopFinalExitCandidate::new(CState::new(), Vec::new())
                .with_jump_target(CControlTargetId(3)),
        ]);
        assert!(
            invalid.is_none(),
            "a different target cannot certify this loop"
        );
    }

    #[test]
    fn checked_loop_exit_copies_share_their_fact_storage() {
        for count in [4usize, 64, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let facts = vec![Proposition::ConditionIs(ConditionTerm::Constant(true), true); count];
            let state = CState::new();
            let (break_exit, break_work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    CLoopBreakExit::new(state.clone(), facts.clone())
                });
            let (final_exit, final_work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    CLoopFinalExitCandidate::new(state.clone(), facts.clone())
                });
            assert!(break_work >= count && break_work <= count * 4 + 32);
            assert!(final_work >= count && final_work <= count * 4 + 32);
            let jump_exit = final_exit.clone().with_jump_target(CControlTargetId(2));
            for _ in 0..16 {
                let copied_break = break_exit.clone();
                let copied_final = final_exit.clone();
                assert!(std::ptr::eq(
                    break_exit.pure_facts(),
                    copied_break.pure_facts()
                ));
                assert!(std::ptr::eq(
                    final_exit.pure_facts(),
                    copied_final.pure_facts()
                ));
                assert_eq!(copied_break.pure_facts(), facts);
                assert_eq!(copied_final.pure_facts(), facts);
                let copied_jump = jump_exit.clone();
                assert_eq!(copied_jump.jump_target(), Some(CControlTargetId(2)));
                assert!(std::ptr::eq(
                    jump_exit.pure_facts(),
                    copied_jump.pure_facts()
                ));
            }
        }
    }
}

impl CLoopPreservationContext {
    pub(crate) fn check_pointer_carriers(&self, state: &CState) -> Result<(), String> {
        super::loops::check_loop_pointer_carriers(&self.pointer_carriers, state)
    }

    pub(crate) fn restored_exit(
        &self,
        state: &CState,
        facts: &crate::kernel::proof::ProofFacts,
        assumptions: &PureFactContext,
    ) -> (CState, Vec<Proposition>) {
        let rebound = crate::kernel::c_loop_state_with_loop_binders_rebound(
            &self.state,
            state,
            &self.binders,
            assumptions,
        )
        .unwrap_or_else(|_| state.clone());
        self.restored_return(&rebound, facts, assumptions)
    }

    // A return has no post-loop scope. Preserve the body's output bindings;
    // rebinding them to loop names would invalidate named `produces` results.
    pub(crate) fn restored_return(
        &self,
        state: &CState,
        facts: &crate::kernel::proof::ProofFacts,
        assumptions: &PureFactContext,
    ) -> (CState, Vec<Proposition>) {
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
        let facts = facts.to_vec();
        (restored, facts)
    }

    pub fn state(&self) -> &CState {
        &self.state
    }

    pub fn loop_entry_state(&self) -> &CState {
        &self.loop_entry_state
    }

    pub fn pure_facts(&self) -> &[Proposition] {
        &self.pure_facts
    }

    pub fn invariant_propositions(&self) -> &[Proposition] {
        &self.invariant_propositions
    }

    /// Effect summaries generated by this loop's whole-span checks. A
    /// step-span structural effect must not use one of these summaries as if
    /// it were the effect of a single iteration; nested execution effects
    /// remain available separately on the checked path.
    pub fn whole_loop_effect_facts(&self) -> &[Proposition] {
        &self.whole_loop_effect_facts
    }

    /// The binders this loop's header declares.
    pub fn binders(&self) -> &[crate::kernel::CLoopBinder] {
        &self.binders
    }

    /// The execution's fresh-variable counter after this head was built. It
    /// is never below the counter the head was built from, so an execution
    /// that continues from it only moves forward.
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
pub enum CLoopHeadRefusal {
    /// A refusal the kernel spells on its own.
    Message(String),
    /// A premise the head's guard owes that the entry context does not
    /// discharge. The invariants owe none here: their side conditions are
    /// invariant content, assumed at the head and owed at entry and at every
    /// back edge.
    MissingPrerequisite {
        proposition: Proposition,
        context: Option<String>,
        /// The loop-top state the premise is stated over.
        state: CState,
    },
    /// A resource the loop declares that the enclosing context does not
    /// hold, evaluated over `state`.
    UnheldResource { fact: CResourceFact, state: CState },
}

impl From<String> for CLoopHeadRefusal {
    fn from(message: String) -> Self {
        Self::Message(message)
    }
}

#[allow(clippy::too_many_arguments)]
pub fn c_loop_preservation_contexts(
    loop_entry_state: &CState,
    condition: &CExpression,
    invariant_checks: &[CLoopInvariantCheck],
    effect_checks: &[CLoopEffectCheck],
    resource_specs: &[CResourceSpec],
    definitions: &[CCompositeResourceDefinition],
    body: &CStatement,
    assumptions: &PureFactContext,
    next_kernel_variable: u64,
) -> Result<Vec<CLoopPreservationContext>, CLoopHeadRefusal> {
    c_loop_preservation_contexts_with_mode(
        loop_entry_state,
        condition,
        invariant_checks,
        effect_checks,
        resource_specs,
        definitions,
        body,
        assumptions,
        next_kernel_variable,
        false,
    )
}

/// Computes loop-body preservation contexts for a C `do ... while` loop.
/// Unlike a pre-tested `while`, the first body entry cannot assume that the
/// post-test condition is true; the condition only guards later iterations.
pub fn c_do_while_preservation_contexts(
    loop_entry_state: &CState,
    condition: &CExpression,
    invariant_checks: &[CLoopInvariantCheck],
    effect_checks: &[CLoopEffectCheck],
    resource_specs: &[CResourceSpec],
    definitions: &[CCompositeResourceDefinition],
    body: &CStatement,
    assumptions: &PureFactContext,
    next_kernel_variable: u64,
) -> Result<Vec<CLoopPreservationContext>, CLoopHeadRefusal> {
    c_loop_preservation_contexts_with_mode(
        loop_entry_state,
        condition,
        invariant_checks,
        effect_checks,
        resource_specs,
        definitions,
        body,
        assumptions,
        next_kernel_variable,
        true,
    )
}

#[allow(clippy::too_many_arguments)]
fn c_loop_preservation_contexts_with_mode(
    loop_entry_state: &CState,
    condition: &CExpression,
    invariant_checks: &[CLoopInvariantCheck],
    effect_checks: &[CLoopEffectCheck],
    resource_specs: &[CResourceSpec],
    definitions: &[CCompositeResourceDefinition],
    body: &CStatement,
    assumptions: &PureFactContext,
    next_kernel_variable: u64,
    do_while: bool,
) -> Result<Vec<CLoopPreservationContext>, CLoopHeadRefusal> {
    // The head inherits the execution's counter instead of restarting at the
    // base of the identity range. Restarting it in the middle of an execution
    // is how a havocked local, a re-bound binder's model field or an
    // arbitrary algebraic binding comes to carry an identity the execution
    // has already handed to something live.
    let mut budget = ExecutionBudget::continuing_from(next_kernel_variable);
    let mut existing_variables = BTreeSet::new();
    collect_c_state_bitvector_variables(loop_entry_state, &mut existing_variables);
    collect_c_expression_bitvector_variables(condition, &mut existing_variables);
    for check in invariant_checks {
        collect_spec_proposition_bitvector_variables(check.proposition(), &mut existing_variables);
    }
    for check in effect_checks {
        collect_loop_effect_bitvector_variables(check.effect(), &mut existing_variables);
    }
    collect_c_statement_bitvector_variables(body, &mut existing_variables);
    collect_assumption_variables(assumptions, &mut existing_variables);
    let mut variables = KernelVariableGenerator::fresh_for_execution(existing_variables);
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
            super::loops::CLoopResourceFailure::Message(message) => {
                CLoopHeadRefusal::Message(message.clone())
            }
            super::loops::CLoopResourceFailure::Unheld { fact, state } => {
                CLoopHeadRefusal::UnheldResource {
                    fact: fact.clone(),
                    state: state.clone(),
                }
            }
        });
    }
    // Preservation runs the body with the loop's declared resources.
    let exit_frame = head
        .narrows_resources()
        .then(|| head.top.resources().clone());
    let top_state = head.body;
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
            assumptions,
            error,
        )
    })? {
        let condition_contexts = if do_while {
            vec![CConditionAssumption {
                branch: CConditionBranch::Decided(true),
                facts: invariant_facts.clone(),
                obligations: invariant_obligations.clone(),
            }]
        } else {
            assume_condition_truthiness(
                &top_state,
                condition,
                definitions,
                assumptions,
                &invariant_facts,
                &invariant_obligations,
                true,
                &mut budget,
            )
            .map_err(|error| {
                format!(
                    "could not assume the loop condition: it stopped at {}",
                    error.describe()
                )
            })?
        };
        // A disjunctive guard such as `while (a || b)` has one way *in* per
        // disjunct, and the body runs on each of them with only that path's
        // own guard facts. The mirror of the exit join: export the
        // disjunction of what each entry path states alone, so one written
        // proof can reason by cases over the ways the guard was true instead
        // of needing a different certificate per entry path.
        let entry_disjunction = crate::kernel::loops::guard_path_disjunction(
            &condition_contexts
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
                .collect::<Vec<_>>(),
        );
        for assumption in condition_contexts {
            // A guard operand this function may not read leaves the head's
            // premises undefined; there is no iteration to describe here.
            if let Some(outcome) = assumption.undecided_outcome() {
                return Err(undecided_loop_guard_context(outcome).into());
            }
            let CConditionAssumption {
                facts, obligations, ..
            } = assumption;
            let context_assumptions = assumptions_with_path_context(assumptions, &facts, &[]);
            if let Some(obligation) = obligations.iter().find(|obligation| {
                !required_obligation_is_exactly_discharged(
                    &context_assumptions,
                    obligation.proposition(),
                )
            }) {
                return Err(CLoopHeadRefusal::MissingPrerequisite {
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
            contexts.push(CLoopPreservationContext {
                state: top_state.clone(),
                exit_frame: exit_frame.clone(),
                loop_entry_state: loop_entry_state.clone(),
                pure_facts,
                invariant_propositions: invariant_propositions.iter().cloned().collect(),
                whole_loop_effect_facts: whole_loop_effect_summaries.clone(),
                binders: crate::kernel::c_loop_binders(resource_specs),
                // Filled in below from the one budget every context here was
                // built with, so each reports the same high-water mark rather
                // than the mark at the moment it happened to be pushed.
                next_kernel_variable,
                pointer_carriers: head.pointer_carriers.clone(),
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
    top_state: &CState,
    loop_entry_state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    assumptions: &PureFactContext,
    error: ExecutionLimit,
) -> String {
    let mut budget = ExecutionBudget::beside_live_state();
    for check in invariant_checks {
        if assume_invariant_checks(
            top_state,
            loop_entry_state,
            std::slice::from_ref(check),
            assumptions,
            &[],
            &[],
            &mut budget,
        )
        .is_err()
        {
            let context = invariant_context(check, InvariantPhase::Preservation)
                .unwrap_or("a loop invariant");
            return format!(
                "{context}: could not be read at the loop head; a loop invariant may only read the resource instances the loop declares"
            );
        }
    }
    format!(
        "could not assume loop invariants: they stopped at {}",
        error.describe()
    )
}

pub fn c_loop_invariant_obligations_at_back_edge(
    state: &CState,
    iteration_entry_state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    assumptions: &PureFactContext,
) -> Result<Vec<ProofObligation>, String> {
    collect_invariant_check_obligations_without_search(
        state,
        iteration_entry_state,
        invariant_checks,
        InvariantPhase::Preservation,
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

/// Refuses a loop `decreases` component whose variables can be written
/// through an escaped address. See the termination module for the rule.
pub fn c_reject_address_escaped_loop_measures(
    function_name: &str,
    measures: &[CRankingComponent],
    body: &CStatement,
) -> Result<(), String> {
    crate::kernel::termination::c_reject_address_escaped_loop_measures(
        function_name,
        measures,
        body,
    )
}

/// The source form of one declared `decreases` component, for diagnostics.
pub fn c_ranking_measure_source(measure: &CRankingComponent) -> String {
    crate::kernel::termination::c_ranking_measure_display(measure)
}

/// The identity spelling of one declared `decreases` component: the form a
/// pure component's written source is keyed by, which must keep telling
/// different measures apart even where it has no source spelling.
pub fn c_ranking_measure_identity(measure: &CRankingComponent) -> String {
    crate::kernel::termination::c_ranking_measure_key(measure)
}

/// The source form of a whole declared `decreases` clause, for diagnostics.
pub fn c_ranking_measures_source(measures: &[CRankingComponent]) -> String {
    crate::kernel::termination::c_ranking_measures_display(measures)
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
pub fn c_execution_environment_with_recursion_anchor(
    environment: CExecutionEnvironment,
    function: &CFunction,
    caller_state: &CState,
    arguments: &[CExpression],
) -> Result<CExecutionEnvironment, String> {
    if function.contract_interface().recursion_measure().is_none() {
        return Ok(environment);
    }
    let entry_state =
        c_function_entry_state(caller_state, function, arguments).ok_or_else(|| {
            format!(
                "could not bind `{}`'s arguments to read its `decreases` measure at entry",
                function.name()
            )
        })?;
    let anchor = crate::kernel::termination::c_function_recursion_anchor(
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
pub fn c_loop_ranking_obligations_at_back_edge(
    state: &CState,
    iteration_entry_state: &CState,
    ranking_measures: &[CRankingComponent],
    assumptions: &PureFactContext,
) -> Result<Vec<ProofObligation>, String> {
    collect_loop_ranking_obligations(
        state,
        iteration_entry_state,
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
pub struct CLoopEntryGoals {
    declarations: Vec<Vec<ProofObligation>>,
}

impl CLoopEntryGoals {
    pub fn declarations(&self) -> &[Vec<ProofObligation>] {
        &self.declarations
    }
}

pub fn c_loop_entry_goals(
    state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    assumptions: &PureFactContext,
) -> Result<CLoopEntryGoals, String> {
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
    Ok(CLoopEntryGoals { declarations })
}

pub fn c_loop_invariant_obligations_at_entry(
    state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    assumptions: &PureFactContext,
) -> Result<Vec<ProofObligation>, String> {
    collect_invariant_check_obligations_without_search(
        state,
        state,
        invariant_checks,
        InvariantPhase::Entry,
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

pub fn c_loop_invariants_hold_at_entry(
    state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    assumptions: &PureFactContext,
) -> Result<(), String> {
    let obligations = collect_invariant_check_obligations(
        state,
        state,
        invariant_checks,
        InvariantPhase::Entry,
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
pub struct CStateJoinAbstraction {
    pub state: CState,
    pub next_kernel_variable: u64,
}

/// Builds a branch-independent symbolic state for a proof join.
///
/// Locals that still equal a stable function-entry value retain that identity.
/// Other scalar and pointer locals become fresh symbolic values, and non-stack
/// memory is forgotten. Exported facts and resources constrain those values at
/// the abstract frontier.
pub fn abstract_c_state_for_join(
    state: &CState,
    stable_entry_locals: &BTreeMap<String, CValue>,
    next_kernel_variable: u64,
) -> Result<CStateJoinAbstraction, String> {
    abstract_c_state_for_join_across(
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
pub fn abstract_c_state_for_join_across(
    state: &CState,
    sibling_states: &[&CState],
    stable_entry_locals: &BTreeMap<String, CValue>,
    next_kernel_variable: u64,
) -> Result<CStateJoinAbstraction, String> {
    abstract_c_state_for_join_across_with_policy(
        state,
        sibling_states,
        stable_entry_locals,
        next_kernel_variable,
        false,
    )
}

/// Builds a branch-interface abstraction while retaining non-scalar memory
/// when every checked arm has the exact same such memory. This avoids
/// forgetting an already-established immutable frame merely because scalar
/// locals differ across the branch. Any disagreement uses the ordinary
/// conservative memory havoc.
pub fn abstract_c_state_for_interface_join_across(
    state: &CState,
    sibling_states: &[&CState],
    stable_entry_locals: &BTreeMap<String, CValue>,
    next_kernel_variable: u64,
) -> Result<CStateJoinAbstraction, String> {
    abstract_c_state_for_join_across_with_policy(
        state,
        sibling_states,
        stable_entry_locals,
        next_kernel_variable,
        true,
    )
}

fn abstract_c_state_for_join_across_with_policy(
    state: &CState,
    sibling_states: &[&CState],
    stable_entry_locals: &BTreeMap<String, CValue>,
    next_kernel_variable: u64,
    preserve_exact_common_memory: bool,
) -> Result<CStateJoinAbstraction, String> {
    // A join may retain one exact persistent ledger root, but it cannot pick
    // one arm's loan history when siblings have advanced independently. The
    // ledger equality is an opaque state-identity comparison; no loan map or
    // history is traversed here.
    if sibling_states
        .iter()
        .any(|sibling| sibling.aggregate_destination != state.aggregate_destination)
    {
        return Err("construction destination differs across branch join".to_string());
    }
    if sibling_states
        .iter()
        .any(|sibling| sibling.loan_ledger != state.loan_ledger)
    {
        return Err("stable-view loan state differs across branch join".to_string());
    }
    if sibling_states
        .iter()
        .any(|sibling| sibling.loan_participant != state.loan_participant)
    {
        return Err("stable-view loan participant differs across branch join".to_string());
    }
    if sibling_states
        .iter()
        .any(|sibling| sibling.loan_view_bindings != state.loan_view_bindings)
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
            collect_c_state_bitvector_variables(sibling, &mut existing_variables);
        }
        for value in stable_entry_locals.values() {
            crate::instrumentation::record_deterministic_work(1);
            collect_c_value_bitvector_variables(value, &mut existing_variables);
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
                collect_c_state_bitvector_variables(sibling, &mut held);
            }
            for value in stable_entry_locals.values() {
                collect_c_value_bitvector_variables(value, &mut held);
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
                crate::kernel::primitives::SnapshotMapChange::Removed(_) => None,
                crate::kernel::primitives::SnapshotMapChange::Added(block)
                | crate::kernel::primitives::SnapshotMapChange::Changed(block) => {
                    block.starts_with("havoc:").then(|| block.clone())
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
    let mut uninitialized_in_an_arm = BTreeSet::new();
    if preserve_exact_common_memory {
        for sibling in sibling_states {
            for (name, binding) in sibling.locals.bindings.iter() {
                crate::instrumentation::record_deterministic_work(1);
                if matches!(binding, CLocalBinding::UninitializedObject { .. }) {
                    uninitialized_in_an_arm.insert(name.as_str());
                }
            }
        }
    }
    let mut left_uninitialized = Vec::new();

    for (name, binding) in state.locals.bindings.iter() {
        crate::instrumentation::record_deterministic_work(1);
        if let CLocalBinding::Object {
            c_type,
            slot,
            volatile,
            pointee_volatile,
            constant,
            pointee_constant,
            ..
        } = binding
            && uninitialized_in_an_arm.contains(name.as_str())
        {
            // Its block is not preserved, so the memory join below drops
            // the value this arm stored and its initialization record.
            left_uninitialized.push((
                name.clone(),
                *c_type,
                slot.clone(),
                *volatile,
                *pointee_volatile,
                *constant,
                *pointee_constant,
            ));
            continue;
        }
        let CLocalBinding::Object {
            value,
            c_type,
            slot,
            ..
        } = binding
        else {
            continue;
        };
        let abstract_value = if stable_entry_locals.get(name) == Some(value) {
            value.clone()
        } else {
            match c_type {
                CType::Void => continue,
                CType::Bool => CValue::Bool(Bitvector32Term::if_then_else(
                    ConditionTerm::Variable(join_variable(&mut variables, &mut budget)?),
                    Bitvector32Term::Constant(1),
                    Bitvector32Term::Constant(0),
                )),
                CType::Int8 => int8(Bitvector32Term::Variable(join_variable(
                    &mut variables,
                    &mut budget,
                )?)),
                CType::Int16 => int16(Bitvector32Term::Variable(join_variable(
                    &mut variables,
                    &mut budget,
                )?)),
                CType::Int32 => int32(Bitvector32Term::Variable(join_variable(
                    &mut variables,
                    &mut budget,
                )?)),
                CType::Int64 => CValue::Int64(Bitvector32Term::Variable(join_variable(
                    &mut variables,
                    &mut budget,
                )?)),
                CType::UInt32 => uint32(Bitvector32Term::Variable(join_variable(
                    &mut variables,
                    &mut budget,
                )?)),
                CType::UInt8 => uint8(Bitvector32Term::Variable(join_variable(
                    &mut variables,
                    &mut budget,
                )?)),
                CType::UInt16 => uint16(Bitvector32Term::Variable(join_variable(
                    &mut variables,
                    &mut budget,
                )?)),
                CType::UInt64 => CValue::UInt64(Bitvector32Term::Variable(join_variable(
                    &mut variables,
                    &mut budget,
                )?)),
                CType::Float32 => CValue::Float32(Bitvector32Term::Variable(join_variable(
                    &mut variables,
                    &mut budget,
                )?)),
                CType::Float64 => CValue::Float64(Bitvector32Term::Variable(join_variable(
                    &mut variables,
                    &mut budget,
                )?)),
                CType::FunctionPointer(_) => CValue::typed_pointer(
                    Pointer::symbolic_function(join_variable(&mut variables, &mut budget)?),
                    *c_type,
                ),
                CType::Int8Array(_) => {
                    unreachable!("array objects use CLocalBinding::ArrayObject")
                }
                CType::Int32Array(_)
                | CType::UInt8Array(_)
                | CType::Int16Array(_)
                | CType::UInt16Array(_)
                | CType::UInt32Array(_)
                | CType::Int128Array(_)
                | CType::Int64Array(_)
                | CType::UInt128Array(_)
                | CType::UInt64Array(_)
                | CType::Float32Array(_)
                | CType::Float64Array(_) => {
                    unreachable!("array objects use CLocalBinding::ArrayObject")
                }
                _ => {
                    let variable = join_variable(&mut variables, &mut budget)?;
                    let pointer = CPointerValue::new(Pointer::symbolic(variable), *c_type);
                    // An unknown joined address cannot erase an enrolled
                    // carrier, even when another arm held a legacy pointer
                    // with the same numeric address.
                    let designated = std::iter::once(state)
                        .chain(sibling_states.iter().copied())
                        .any(|arm| {
                            matches!(arm.locals.get(name),
                            Some(CValue::Pointer(value)) if value.designation().is_some())
                        });
                    CValue::Pointer(if designated {
                        pointer.with_designation(PointerDesignation::Unresolved(variable))
                    } else {
                        pointer
                    })
                }
            }
        };
        preserved_blocks.insert(slot.block.clone());
        abstract_objects.push((name.clone(), abstract_value, *c_type));
    }

    // The arms' memories are one memory when they differ only inside the
    // blocks the join preserves anyway. The differences are read off the
    // structure the snapshots share, so equal memories cost nothing and
    // unequal ones cost what differs.
    let common_memory = preserve_exact_common_memory
        && sibling_states.iter().all(|sibling| {
            state
                .memory
                .differs_only_within(&sibling.memory, &preserved_blocks)
        });
    if !common_memory {
        if let Some(ledger) = abstract_state.loan_ledger() {
            for sibling in sibling_states {
                validate_branch_memory_delta_against_loans(
                    &abstract_state.memory,
                    &sibling.memory,
                    ledger,
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
                .with_interface_memory_havoc_preserving_loans(
                    join_variable(&mut variables, &mut budget)?,
                    &preserved_blocks,
                    &sibling_memories,
                    abstract_state.loan_ledger(),
                )?;
            abstract_state.set_memory(memory);
        } else {
            let memory = abstract_state
                .memory
                .clone()
                .with_loop_memory_havoc_preserving_loans(
                    join_variable(&mut variables, &mut budget)?,
                    &preserved_blocks,
                    None,
                    abstract_state.loan_ledger(),
                );
            abstract_state.set_memory(memory);
        }
    }
    for (name, value, c_type) in abstract_objects {
        sync_stack_local(&mut abstract_state, &name, &value);
        abstract_state.locals.set_typed(name, value, c_type);
    }
    for (name, c_type, slot, volatile, pointee_volatile, constant, pointee_constant) in
        left_uninitialized
    {
        abstract_state.locals.set_uninitialized_with_all_qualifiers(
            name,
            c_type,
            slot,
            volatile,
            pointee_volatile,
            constant,
            pointee_constant,
        );
    }
    // Drop the resource context through the rebasing setter, not by writing
    // the field. The occurrence-to-loan sidecar is keyed by the occurrences of
    // the context being discarded, so a direct assignment would leave the
    // abstraction advertising loan dependencies for occurrences it no longer
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
    Ok(CStateJoinAbstraction {
        // Structural empty join shape; live successor resources are supplied
        // separately by the checked interface, not inserted into this placeholder.
        state: abstract_state.with_resource_context(ResourceContext::new()),
        next_kernel_variable: budget.next_kernel_variable(),
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

fn validate_branch_memory_delta_against_loans(
    base: &CMemory,
    sibling: &CMemory,
    ledger: &crate::kernel::loans::LoanLedger,
) -> Result<(), String> {
    if !ledger.has_active_memory_loans() {
        return Ok(());
    }
    if base.blocks != sibling.blocks
        || base.heap != sibling.heap
        || base.forgotten.ended_local_blocks != sibling.forgotten.ended_local_blocks
    {
        return Err("branch memory join has an unsupported allocation or block delta while a stable-view loan is active".to_string());
    }
    for pointer in base.differing_cell_pointers(sibling) {
        let mut byte_width = base
            .cells
            .get(&pointer)
            .map(|value| value.byte_width())
            .unwrap_or(0)
            .max(
                sibling
                    .cells
                    .get(&pointer)
                    .map(|value| value.byte_width())
                    .unwrap_or(0),
            );
        for (union_pointer, c_type) in base.union_cells.keys() {
            if union_pointer == &pointer {
                byte_width = byte_width.max(c_type.byte_width());
            }
        }
        for (union_pointer, c_type) in sibling.union_cells.keys() {
            if union_pointer == &pointer {
                byte_width = byte_width.max(c_type.byte_width());
            }
        }
        if byte_width == 0 {
            return Err(
                "branch memory join has an unknown changed cell width while a stable-view loan is active".to_string(),
            );
        }
        let range = CMemoryRange::new_with_element_width(
            pointer,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(byte_width),
            1,
        );
        if let Err(error) = ledger.permits_memory_access(&range) {
            return Err(format!(
                "branch memory join changes an active stable-view footprint: {error}"
            ));
        }
    }
    Ok(())
}

pub fn c_variable(name: impl Into<String>) -> CExpression {
    CExpression::Variable(name.into())
}

pub fn c_function_address(name: impl Into<String>) -> CExpression {
    CExpression::FunctionAddress(name.into())
}

/// The values a composite definition binds its existential witnesses to for
/// `composite` under `memory` and `assumptions`, in declaration order. This
/// is the same deterministic choice body instantiation makes, so a surface
/// substitution of witness names agrees with the kernel's own expansion.
pub fn composite_resource_witness_values(
    composite: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    resources: &ResourceContext,
    assumptions: &PureFactContext,
) -> Option<Vec<CValue>> {
    let CResource::Composite { name, arguments } = composite.resource() else {
        return None;
    };
    let definition = definitions
        .iter()
        .find(|definition| definition.name() == name)?;
    if definition.parameters().len() != arguments.len() {
        return None;
    }
    let mut state = CState::new().with_memory(memory.clone());
    for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
        let argument = argument.as_c_value()?;
        state.locals.set_typed(
            parameter.name().to_string(),
            argument.clone(),
            parameter.c_type(),
        );
    }
    let assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    super::functions::bind_composite_witnesses_with_held(
        definition,
        arguments,
        &mut state,
        resources,
        &assumptions,
    )
}

pub fn c_cast(expression: CExpression, target_type: CType) -> CExpression {
    c_cast_with_pointee_volatile(expression, target_type, false)
}

pub fn c_cast_with_pointee_volatile(
    expression: CExpression,
    target_type: CType,
    pointee_volatile: bool,
) -> CExpression {
    c_cast_with_pointee_qualifiers(expression, target_type, pointee_volatile, false)
}

pub fn c_cast_with_pointee_qualifiers(
    expression: CExpression,
    target_type: CType,
    pointee_volatile: bool,
    pointee_constant: bool,
) -> CExpression {
    c_cast_with_pointee_qualifiers_and_struct(
        expression,
        target_type,
        pointee_volatile,
        pointee_constant,
        None,
    )
}

pub fn c_cast_with_pointee_qualifiers_and_struct(
    expression: CExpression,
    target_type: CType,
    pointee_volatile: bool,
    pointee_constant: bool,
    pointee_struct: Option<String>,
) -> CExpression {
    CExpression::Cast {
        expression: Box::new(expression),
        target_type,
        integer_mode: crate::kernel::CIntegerCastMode::Standard,
        pointee_struct,
        pointee_volatile,
        pointee_constant,
        explicit_qualification: false,
    }
}

/// A cast the C source wrote. Its result has exactly the destination's
/// pointee `const` qualification, so unlike the lowering-inserted casts
/// above it can drop the source pointer's `const`.
pub fn c_source_cast_with_pointee_qualifiers_and_struct(
    expression: CExpression,
    target_type: CType,
    pointee_volatile: bool,
    pointee_constant: bool,
    pointee_struct: Option<String>,
) -> CExpression {
    CExpression::Cast {
        expression: Box::new(expression),
        target_type,
        integer_mode: crate::kernel::CIntegerCastMode::Standard,
        pointee_struct,
        pointee_volatile,
        pointee_constant,
        explicit_qualification: true,
    }
}

/// Explicit modulo conversion between admitted machine integer types.
/// The evaluator checks both runtime types. This policy is shared by Rust and
/// C++20; ordinary C casts continue to use `c_cast` and its checked policy.
pub fn c_integer_cast_modulo(expression: CExpression, target_type: CType) -> CExpression {
    let mut result = c_cast(expression, target_type);
    if let CExpression::Cast { integer_mode, .. } = &mut result {
        *integer_mode = CIntegerCastMode::Modulo;
    }
    result
}

/// The C++20 uint64-to-int64 rule, distinct from an ordinary C cast.
pub fn c_uint64_bits_to_int64(expression: CExpression) -> CExpression {
    let mut result = c_cast(expression, CType::Int64);
    if let CExpression::Cast { integer_mode, .. } = &mut result {
        *integer_mode = CIntegerCastMode::UInt64BitsToInt64;
    }
    result
}

pub fn c_conditional(
    condition: CExpression,
    then_branch: CExpression,
    else_branch: CExpression,
) -> CExpression {
    CExpression::Conditional {
        condition: Box::new(condition),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
    }
}

pub fn c_float_classification(
    expression: CExpression,
    classification: CFloatClassification,
) -> CExpression {
    CExpression::FloatClassification {
        expression: Box::new(expression),
        classification,
    }
}

pub fn c_float_negate(expression: CExpression) -> CExpression {
    CExpression::FloatNegate(Box::new(expression))
}

pub fn c_addr_of(name: impl Into<String>) -> CExpression {
    CExpression::AddressOf(Box::new(c_variable(name)))
}

/// A non-reading check of the storage denoted by an lvalue.
pub fn c_checked_object_address(lvalue: CExpression) -> CExpression {
    CExpression::CheckedObjectAddress(Box::new(lvalue))
}

pub fn c_pointer_offset_bytes(pointer: CExpression, bytes: u32) -> CExpression {
    if bytes == 0 {
        pointer
    } else {
        CExpression::PointerOffsetBytes {
            pointer: Box::new(pointer),
            bytes,
        }
    }
}

pub fn c_int32_literal(value: u32) -> CExpression {
    CExpression::Value(int32(Bitvector32Term::Constant(value)))
}

pub fn c_uint8_literal(value: u8) -> CExpression {
    CExpression::Value(uint8(Bitvector32Term::Constant(u32::from(value))))
}

pub fn c_uint32_literal(value: u32) -> CExpression {
    CExpression::Value(uint32(Bitvector32Term::Constant(value)))
}

/// Signed wide literal in the common checked machine arena.
pub fn c_int128_literal(value: i128) -> CExpression {
    let ty = MachineIntegerType::Int128;
    CExpression::Value(
        ty.constant_value(
            MachineIntegerConstant::from_signed(ty.format(), value)
                .expect("i128 fits the signed 128-bit format"),
        )
        .expect("exact wide format"),
    )
}

/// Unsigned wide literal; the high 64 bits are retained.
pub fn c_uint128_literal(value: u128) -> CExpression {
    let ty = MachineIntegerType::UInt128;
    CExpression::Value(
        ty.constant_value(
            MachineIntegerConstant::from_unsigned(ty.format(), value)
                .expect("u128 fits the unsigned 128-bit format"),
        )
        .expect("exact wide format"),
    )
}

pub fn c_int64_literal(value: i64) -> CExpression {
    CExpression::Value(int64(Bitvector32Term::Int64Constant(value)))
}

pub fn c_uint64_literal(value: u64) -> CExpression {
    CExpression::Value(uint64(Bitvector32Term::UInt64Constant(value)))
}

pub fn c_float32_literal(bits: u32) -> CExpression {
    CExpression::Value(float32(Bitvector32Term::Constant(bits)))
}

pub fn c_float64_literal(bits: u64) -> CExpression {
    CExpression::Value(float64(Bitvector32Term::UInt64Constant(bits)))
}

pub fn c_pointer_value(pointer: Pointer) -> CExpression {
    CExpression::Value(CValue::pointer(pointer))
}

pub fn c_typed_pointer_value(pointer: Pointer, c_type: CType) -> CExpression {
    CExpression::Value(CValue::typed_pointer(pointer, c_type))
}

pub fn c_less_than(left: CExpression, right: CExpression) -> CExpression {
    CExpression::LessThan(Box::new(left), Box::new(right))
}

pub fn c_less_equal(left: CExpression, right: CExpression) -> CExpression {
    CExpression::LessEqual(Box::new(left), Box::new(right))
}

pub fn c_greater_than(left: CExpression, right: CExpression) -> CExpression {
    CExpression::GreaterThan(Box::new(left), Box::new(right))
}

pub fn c_greater_equal(left: CExpression, right: CExpression) -> CExpression {
    CExpression::GreaterEqual(Box::new(left), Box::new(right))
}

pub fn c_equal(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Equal(Box::new(left), Box::new(right))
}

pub fn c_not_equal(left: CExpression, right: CExpression) -> CExpression {
    CExpression::NotEqual(Box::new(left), Box::new(right))
}

pub fn c_not(expression: CExpression) -> CExpression {
    CExpression::Not(Box::new(expression))
}

pub fn c_and(left: CExpression, right: CExpression) -> CExpression {
    CExpression::And(Box::new(left), Box::new(right))
}

pub fn c_or(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Or(Box::new(left), Box::new(right))
}

pub fn c_add(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Add(Box::new(left), Box::new(right))
}

pub fn c_subtract(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Subtract(Box::new(left), Box::new(right))
}

pub fn c_multiply(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Multiply(Box::new(left), Box::new(right))
}

pub fn c_divide(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Divide(Box::new(left), Box::new(right))
}

pub fn c_remainder(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Remainder(Box::new(left), Box::new(right))
}

pub fn c_shift_left(left: CExpression, right: CExpression) -> CExpression {
    CExpression::ShiftLeft(Box::new(left), Box::new(right))
}

pub fn c_shift_right(left: CExpression, right: CExpression) -> CExpression {
    CExpression::ShiftRight(Box::new(left), Box::new(right))
}

pub fn c_bitwise_and(left: CExpression, right: CExpression) -> CExpression {
    CExpression::BitwiseAnd(Box::new(left), Box::new(right))
}

pub fn c_bitwise_or(left: CExpression, right: CExpression) -> CExpression {
    CExpression::BitwiseOr(Box::new(left), Box::new(right))
}

pub fn c_bitwise_xor(left: CExpression, right: CExpression) -> CExpression {
    CExpression::BitwiseXor(Box::new(left), Box::new(right))
}

pub fn c_bitwise_not(expression: CExpression) -> CExpression {
    CExpression::BitwiseNot(Box::new(expression))
}

pub fn c_load(pointer: CExpression) -> CExpression {
    CExpression::Load(Box::new(pointer))
}

pub fn c_typed_load(pointer: CExpression, value_type: CType) -> CExpression {
    c_typed_load_with_source(pointer, value_type, None)
}

pub(crate) fn c_typed_load_with_source(
    pointer: CExpression,
    value_type: CType,
    source: Option<crate::kernel::LoadSourceId>,
) -> CExpression {
    c_qualified_typed_load_with_source(pointer, value_type, false, source)
}

pub(crate) fn c_qualified_typed_load_with_source(
    pointer: CExpression,
    value_type: CType,
    pointee_constant: bool,
    source: Option<crate::kernel::LoadSourceId>,
) -> CExpression {
    CExpression::TypedLoad {
        pointer: Box::new(pointer),
        value_type,
        volatile: false,
        pointee_constant,
        source: source
            .map(crate::kernel::CExpressionLoadSource::new)
            .unwrap_or_default(),
    }
}

/// Construct one checked sequential access to the typed cell reached by
/// `pointer`.  This is the kernel projection used by `READ_ONCE` and the
/// lvalue side of `WRITE_ONCE`/`rcu_assign_pointer`; it is deliberately an
/// observable sequential access, not an atomic or release/acquire operation.
pub fn c_volatile_typed_load(pointer: CExpression, value_type: CType) -> CExpression {
    c_qualified_volatile_typed_load(pointer, value_type, false)
}

pub(crate) fn c_qualified_volatile_typed_load(
    pointer: CExpression,
    value_type: CType,
    pointee_constant: bool,
) -> CExpression {
    CExpression::TypedLoad {
        pointer: Box::new(pointer),
        value_type,
        volatile: true,
        pointee_constant,
        source: crate::kernel::CExpressionLoadSource::none(),
    }
}

pub fn c_index(base: CExpression, index: CExpression) -> CExpression {
    CExpression::Index(Box::new(base), Box::new(index))
}

pub fn c_assign(name: impl Into<String>, expression: CExpression) -> CStatement {
    CStatement::Assign {
        name: name.into(),
        expression,
    }
}

pub fn c_call_assign(
    target: impl Into<String>,
    function_name: impl Into<String>,
    arguments: Vec<CExpression>,
) -> CStatement {
    CStatement::CallAssign {
        target: target.into(),
        function_name: function_name.into(),
        arguments,
    }
}

pub fn c_call(function_name: impl Into<String>, arguments: Vec<CExpression>) -> CStatement {
    CStatement::Call {
        function_name: function_name.into(),
        arguments,
    }
}

pub fn c_heap_allocate(target: impl Into<String>, bytes: u32) -> CStatement {
    c_heap_allocate_sized(target, c_int32_literal(bytes))
}

pub fn c_heap_allocate_sized(target: impl Into<String>, bytes: CExpression) -> CStatement {
    c_heap_allocate_sized_with_zeroed(target, bytes, false)
}

pub fn c_heap_allocate_sized_with_zeroed(
    target: impl Into<String>,
    bytes: CExpression,
    zeroed: bool,
) -> CStatement {
    CStatement::HeapAllocate {
        target: target.into(),
        bytes,
        zeroed,
        allocated_scalar_type: None,
    }
}

pub fn c_heap_free(pointer: CExpression) -> CStatement {
    CStatement::HeapFree { pointer }
}

pub fn c_declare(name: impl Into<String>, c_type: CType) -> CStatement {
    c_declare_volatile(name, c_type, false)
}

pub fn c_declare_volatile(name: impl Into<String>, c_type: CType, volatile: bool) -> CStatement {
    c_declare_qualified(name, c_type, volatile, false)
}

pub fn c_declare_qualified(
    name: impl Into<String>,
    c_type: CType,
    volatile: bool,
    pointee_volatile: bool,
) -> CStatement {
    c_declare_with_all_qualifiers(name, c_type, volatile, pointee_volatile, false, false)
}

pub fn c_declare_with_all_qualifiers(
    name: impl Into<String>,
    c_type: CType,
    volatile: bool,
    pointee_volatile: bool,
    constant: bool,
    pointee_constant: bool,
) -> CStatement {
    CStatement::Declare {
        name: name.into(),
        c_type,
        array_object_kind: CArrayObjectKind::Scalar,
        volatile,
        pointee_volatile,
        constant,
        pointee_constant,
        initializer: None,
        zero_fill: None,
    }
}

/// [`c_declare_with_all_qualifiers`], zero-filling the object first when
/// `zero_fill` says how: an automatic array declared with an initializer,
/// whose written elements follow as ordinary stores ([`CZeroFill`]).
pub fn c_declare_with_zero_fill(
    name: impl Into<String>,
    c_type: CType,
    volatile: bool,
    pointee_volatile: bool,
    constant: bool,
    pointee_constant: bool,
    zero_fill: Option<CZeroFill>,
) -> CStatement {
    CStatement::Declare {
        name: name.into(),
        c_type,
        array_object_kind: CArrayObjectKind::Scalar,
        volatile,
        pointee_volatile,
        constant,
        pointee_constant,
        initializer: None,
        zero_fill,
    }
}

/// Declare the lowered byte backing of an array of source aggregate objects.
/// This storage has no scalar-byte array domain; explicit aggregate-element
/// metadata is required before checked aggregate-array domains can be issued.
pub fn c_declare_aggregate_array(name: impl Into<String>, bytes: u32) -> CStatement {
    c_declare_aggregate_array_with_zero_fill(name, bytes, false, false, false, false, None)
}

pub fn c_declare_aggregate_array_with_zero_fill(
    name: impl Into<String>,
    bytes: u32,
    volatile: bool,
    pointee_volatile: bool,
    constant: bool,
    pointee_constant: bool,
    zero_fill: Option<CZeroFill>,
) -> CStatement {
    CStatement::Declare {
        name: name.into(),
        c_type: CType::UInt8Array(bytes),
        array_object_kind: CArrayObjectKind::AggregateBacking,
        volatile,
        pointee_volatile,
        constant,
        pointee_constant,
        initializer: None,
        zero_fill,
    }
}

/// Allocate a fresh scalar and initialize it once. Ordinary stores remain
/// subject to the object's const qualification after this transition.
pub fn c_declare_initialized(
    name: impl Into<String>,
    c_type: CType,
    expression: CExpression,
    volatile: bool,
    pointee_volatile: bool,
    constant: bool,
    pointee_constant: bool,
) -> CStatement {
    CStatement::Declare {
        name: name.into(),
        c_type,
        array_object_kind: CArrayObjectKind::Scalar,
        volatile,
        pointee_volatile,
        constant,
        pointee_constant,
        zero_fill: None,
        initializer: Some(expression),
    }
}

pub fn c_declare_aggregate(name: impl Into<String>, layout: CAggregateLayout) -> CStatement {
    CStatement::DeclareAggregate {
        name: name.into(),
        layout,
        kind: CAggregateDeclarationKind::Local,
    }
}

pub fn c_begin_aggregate_construction(
    name: impl Into<String>,
    layout: CAggregateLayout,
) -> CStatement {
    CStatement::DeclareAggregate {
        name: name.into(),
        layout,
        kind: CAggregateDeclarationKind::Constructor,
    }
}

/// Allocates fresh owned aggregate storage without initializing its fields.
/// This grants authority over the allocation, not over any future pointees.
pub fn c_allocate_aggregate_destination(
    name: impl Into<String>,
    layout: CAggregateLayout,
) -> CStatement {
    CStatement::DeclareAggregate {
        name: name.into(),
        layout,
        kind: CAggregateDeclarationKind::ConstructionDestination,
    }
}

pub fn c_copy_aggregate(
    target: CExpression,
    source: CExpression,
    layout: CAggregateLayout,
) -> CStatement {
    CStatement::CopyAggregate {
        target,
        source,
        layout,
    }
}

/// Retire automatic storage at a source-language lifetime boundary. Frontends
/// supply the objects whose lifetimes end; this grants no cleanup authority.
pub fn c_end_automatic_lifetimes(names: Vec<String>) -> CStatement {
    CStatement::EndAutomaticLifetimes { names }
}

pub fn c_initialize_scalar_array(
    target: CExpression,
    source: CExpression,
    element_type: CType,
    count: u32,
    copy: bool,
) -> CStatement {
    CStatement::InitializeScalarArray {
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
pub fn c_write_scalar_array_region(
    target: CExpression,
    source: CExpression,
    element_type: CType,
    count: u32,
    copy: bool,
) -> CStatement {
    CStatement::InitializeScalarArray {
        target,
        source,
        element_type,
        count,
        copy,
        fresh: false,
    }
}

pub fn c_assert(condition: CExpression) -> CStatement {
    CStatement::Assert {
        condition,
        label: None,
    }
}

pub fn c_labeled_assert(condition: CExpression, label: impl Into<String>) -> CStatement {
    CStatement::Assert {
        condition,
        label: Some(label.into()),
    }
}

pub fn c_seq(first: CStatement, second: CStatement) -> CStatement {
    CStatement::Seq(Arc::new(first), Arc::new(second))
}

pub fn c_skip() -> CStatement {
    CStatement::Skip
}

pub fn c_break() -> CStatement {
    CStatement::Break
}

pub fn c_continue() -> CStatement {
    CStatement::Continue
}

pub(crate) fn c_goto(target: CControlTargetId) -> CStatement {
    CStatement::Goto { target }
}

pub fn c_switch(expression: CExpression, cases: Vec<CSwitchCase>) -> CStatement {
    CStatement::Switch { expression, cases }
}

pub fn c_return(expression: CExpression) -> CStatement {
    CStatement::Return(expression)
}

pub fn c_void_value() -> CExpression {
    CExpression::Value(CValue::Void)
}

pub fn c_store(pointer: CExpression, value: CExpression) -> CStatement {
    CStatement::Store { pointer, value }
}

pub fn c_typed_store(pointer: CExpression, value: CExpression, value_type: CType) -> CStatement {
    c_qualified_typed_store(pointer, value, value_type, false, false)
}

pub(crate) fn c_qualified_typed_store(
    pointer: CExpression,
    value: CExpression,
    value_type: CType,
    pointee_constant: bool,
    volatile: bool,
) -> CStatement {
    CStatement::TypedStore {
        pointer,
        value,
        value_type,
        pointee_constant,
        volatile,
    }
}

/// Construct the checked sequential store used by the kernel pointer
/// publication primitives.  It has ordinary C memory effects plus one
/// ordered access fact; it does not provide a concurrent-reader or
/// release/acquire theorem.
pub fn c_volatile_typed_store(
    pointer: CExpression,
    value: CExpression,
    value_type: CType,
) -> CStatement {
    CStatement::TypedStore {
        pointer,
        value,
        value_type,
        volatile: true,
        pointee_constant: false,
    }
}

pub fn c_update(
    target: CExpression,
    operator: CUpdateOperator,
    operand: CExpression,
) -> CStatement {
    CStatement::Update {
        target,
        operator,
        operand,
    }
}

pub fn c_if(
    condition: CExpression,
    then_branch: CStatement,
    else_branch: CStatement,
) -> CStatement {
    CStatement::If {
        condition,
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
    }
}

/// Handle a checked int32 exceptional outcome, binding its payload only on
/// the caught path. Normal and other terminal outcomes bypass the handler.
pub fn c_try_catch_int32(
    try_body: CStatement,
    binding: impl Into<String>,
    handler: CStatement,
) -> CStatement {
    c_try_catch_int32_with_cleanup(try_body, binding, handler, false)
}

pub fn c_try_catch_int32_with_cleanup(
    try_body: CStatement,
    binding: impl Into<String>,
    handler: CStatement,
    cleanup_unwind: bool,
) -> CStatement {
    CStatement::TryCatchInt32 {
        try_body: Box::new(try_body),
        binding: binding.into(),
        handler: Box::new(handler),
        cleanup_unwind,
    }
}

pub fn c_while(
    condition: CExpression,
    invariant: Vec<Proposition>,
    body: CStatement,
) -> CStatement {
    c_while_with_invariant_and_effect_checks(condition, invariant, Vec::new(), Vec::new(), body)
}

pub fn c_while_with_invariant_checks(
    condition: CExpression,
    invariant: Vec<Proposition>,
    invariant_checks: Vec<CLoopInvariantCheck>,
    body: CStatement,
) -> CStatement {
    c_while_with_invariant_and_effect_checks(
        condition,
        invariant,
        invariant_checks,
        Vec::new(),
        body,
    )
}

pub fn c_while_with_invariant_and_effect_checks(
    condition: CExpression,
    invariant: Vec<Proposition>,
    invariant_checks: Vec<CLoopInvariantCheck>,
    effect_checks: Vec<CLoopEffectCheck>,
    body: CStatement,
) -> CStatement {
    CStatement::While {
        condition,
        invariant,
        invariant_checks,
        effect_checks,
        resource_specs: Vec::new(),
        ranking_measures: Vec::new(),
        structural_measure: None,
        do_while: false,
        backedge_target: None,
        natural_exit_target: None,
        body: Box::new(body),
    }
}

impl CStatement {
    /// Declares the resources a loop holds for itself.
    ///
    /// An empty declaration leaves the loop inheriting the enclosing resource
    /// context, which is what every loop without `owns` or `views` clauses
    /// does. A statement that is not a loop head keeps its shape: only a loop
    /// carries resource declarations.
    pub fn with_loop_resource_specs(mut self, specs: Vec<CResourceSpec>) -> Self {
        if specs.is_empty() {
            return self;
        }
        if let Self::While { resource_specs, .. } = &mut self {
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
    pub fn with_loop_ranking_measures(mut self, measures: Vec<CRankingComponent>) -> Self {
        if measures.is_empty() {
            return self;
        }
        if let Self::While {
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
        if let Self::While {
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
    pub fn with_backedge_target(mut self, target: CControlTargetId) -> Self {
        if let Self::While {
            backedge_target, ..
        } = &mut self
        {
            *backedge_target = Some(target);
        }
        self
    }

    /// Retains the explicit forward exit target of a proof-only natural cycle.
    pub fn with_natural_exit_target(mut self, target: CControlTargetId) -> Self {
        if let Self::While {
            natural_exit_target,
            ..
        } = &mut self
        {
            *natural_exit_target = Some(target);
        }
        self
    }
}

pub fn c_do_while(condition: CExpression, body: CStatement) -> CStatement {
    c_do_while_with_invariant_and_effect_checks(condition, Vec::new(), Vec::new(), body)
}

pub fn c_do_while_with_invariant_and_effect_checks(
    condition: CExpression,
    invariant_checks: Vec<CLoopInvariantCheck>,
    effect_checks: Vec<CLoopEffectCheck>,
    body: CStatement,
) -> CStatement {
    CStatement::While {
        condition,
        invariant: Vec::new(),
        invariant_checks,
        effect_checks,
        resource_specs: Vec::new(),
        ranking_measures: Vec::new(),
        structural_measure: None,
        do_while: true,
        backedge_target: None,
        natural_exit_target: None,
        body: Box::new(body),
    }
}

pub fn c_continue_with_step(step: CStatement) -> CStatement {
    CStatement::ForStep {
        step: Box::new(step),
        exited_locals: Vec::new(),
        continue_after: true,
    }
}

/// Lowers the body of a C `for` loop to the existing `while` representation.
/// A normal body completion reaches the appended step through the sequence;
/// a `continue` must execute that same step before returning to the loop head.
/// Nested loops are opaque here because their `continue` statements target
/// those inner loops instead.
pub fn c_for_body_with_step(body: CStatement, step: CStatement) -> CStatement {
    fn rewrite(statement: CStatement, step: &CStatement, scopes: &mut Vec<String>) -> CStatement {
        match statement {
            CStatement::Continue => CStatement::ForStep {
                step: Box::new(step.clone()),
                exited_locals: scopes.clone(),
                continue_after: true,
            },
            CStatement::Seq(first, second) => c_seq(
                rewrite((*first).clone(), step, scopes),
                rewrite((*second).clone(), step, scopes),
            ),
            CStatement::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let mut arm = |body: CStatement| {
                    let parent_len = scopes.len();
                    scopes.extend(crate::kernel::eval::scope_declared_names(&body));
                    let body = rewrite(body, step, scopes);
                    scopes.truncate(parent_len);
                    body
                };
                c_if(condition, arm(*then_branch), arm(*else_branch))
            }
            CStatement::Switch { expression, cases } => {
                let parent_len = scopes.len();
                for case in &cases {
                    scopes.extend(crate::kernel::eval::scope_declared_names(&case.body));
                }
                let cases = cases
                    .into_iter()
                    .map(|case| CSwitchCase {
                        value: case.value,
                        body: Box::new(rewrite(*case.body, step, scopes)),
                    })
                    .collect();
                scopes.truncate(parent_len);
                c_switch(expression, cases)
            }
            statement => statement,
        }
    }
    fn first_step(step: CStatement, names: Vec<String>) -> CStatement {
        match step {
            CStatement::Seq(first, rest) => {
                c_seq(first_step((*first).clone(), names), (*rest).clone())
            }
            step => CStatement::ForStep {
                step: Box::new(step),
                exited_locals: names,
                continue_after: false,
            },
        }
    }
    let names = crate::kernel::eval::scope_declared_names(&body);
    let rewritten = rewrite(body, &step, &mut names.clone());
    // No wrapper is needed when the body declares nothing. This preserves
    // the ordinary scalar update and its direct producer facts.
    let step = if names.is_empty() {
        step
    } else {
        first_step(step, names)
    };
    c_seq(rewritten, step)
}

pub fn c_parameter(name: impl Into<String>, c_type: CType) -> CParameter {
    CParameter::new(name, c_type)
}

pub fn c_parameter_with_aggregate_layout(
    name: impl Into<String>,
    c_type: CType,
    layout: CAggregateLayout,
) -> CParameter {
    CParameter::new(name, c_type).with_aggregate_layout(layout)
}

pub fn c_function(
    return_type: CType,
    name: impl Into<String>,
    parameters: Vec<CParameter>,
    body: CStatement,
) -> CFunction {
    CFunction::new(return_type, name, parameters, body)
}

/// Lowers a spec proposition at `state`, the one lowering every proof-side
/// proposition and every contract clause share. `entry_state` is what
/// `old(...)` refers to. The result is the proposition on the lowering's
/// single path with the facts its loads introduced and the obligations
/// they left open (a load the state does not show loadable); `None` when
/// the lowering fails or splits into several paths.
pub fn c_lower_spec_proposition_at_state(
    state: &CState,
    proposition: &SpecProposition,
    entry_state: Option<&CState>,
    assumptions: &PureFactContext,
) -> Result<(Proposition, Vec<Proposition>, Vec<Proposition>), String> {
    let (proposition, facts, obligations, _) = c_lower_spec_proposition_at_state_with_provenance(
        state,
        proposition,
        entry_state,
        assumptions,
    )?;
    Ok((proposition, facts, obligations))
}

/// [`c_lower_spec_proposition_at_state`], also reporting the head chain of
/// the lowered proposition: which of its outermost nodes this lowering
/// inserted as a guard, which were written, and the exact kernel variable
/// each written universal bound its written name to. A proof that
/// introduces the head of this goal reads the record instead of inferring
/// the correspondence from the shape the written syntax happens to share.
pub fn c_lower_spec_proposition_at_state_with_provenance(
    state: &CState,
    proposition: &SpecProposition,
    entry_state: Option<&CState>,
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
        c_lower_spec_proposition_with_checked_obligations(
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
    /// Present when the lowering pruned a range fold because its body did not
    /// lower to one symbolic iteration under the fold's binders.
    pub dropped_fold_body: Option<DroppedFoldBody>,
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
fn describe_spec_lowering_limit(what: &str, limit: ExecutionLimit) -> String {
    match limit {
        ExecutionLimit::UnsupportedIntegerExistentialBody => {
            "Integer existential bodies must currently be pure and total".to_string()
        }
        // The lowering runs beside a live execution whose identity mark it
        // does not carry, so an identity from the base of that range would
        // name a havocked local or a join abstraction. Everything this
        // lowering invents is a bound variable drawn from the match-binder
        // range instead; a request for an execution identity is a defect in
        // the kernel, and it is reported as one rather than satisfied.
        ExecutionLimit::ExecutionIdentityBesideLiveState => {
            "internal: execution identity requested beside a live state".to_string()
        }
        ExecutionLimit::ResourceCountPendingWorker => {
            "count(...) requires joining its outstanding worker".to_string()
        }
        ExecutionLimit::ResourceCountPossiblyAliased => {
            "count(...) of a population that may alias another tracked population of its family; state whether their arguments are equal or different".to_string()
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
        ExecutionLimit::AuthorityCountOverflows => "the population count exceeds int32".to_string(),
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

/// Why a specification evaluation did not produce exactly one path. No path
/// at all is almost always every path ending in a runtime error, and the
/// first such error is the message; the count alone hid a 4-byte load of an
/// 8-byte cell behind "0 paths" for three proof attempts.
fn no_single_path_message<T>(what: &str, paths: &[T], budget: &ExecutionBudget) -> String {
    if paths.is_empty()
        && let Some(extent) = budget.dropped_range_extent()
    {
        let width = extent.element_width;
        let limit = extent.byte_limit;
        return if extent.element_count < 0 {
            let count = -extent.element_count;
            let elements = if count == 1 { "element" } else { "elements" };
            format!(
                "the kernel {what} produced no path: a memory range runs backwards, so it is not a byte extent: its end is {count} {elements} before its start"
            )
        } else {
            format!(
                "the kernel {what} produced no path: a memory range is too wide to be a 32-bit byte extent: {} elements of {width} bytes is {} bytes, past the {limit}-byte limit",
                extent.element_count,
                extent.element_count.saturating_mul(i64::from(width))
            )
        };
    }
    if paths.is_empty() && budget.dropped_relation_range_extent() {
        return format!(
            "the kernel {what} produced no path: it relates a memory range this context already \
             proves is not a byte extent, because its end is before its start"
        );
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
pub(crate) fn c_lower_spec_proposition_with_checked_obligations(
    state: &CState,
    proposition: &SpecProposition,
    entry_state: Option<&CState>,
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
    let lowering_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads()
        .defer_non_exact_loadability_obligations();
    let mut budget = ExecutionBudget::beside_live_state();
    let paths = lower_spec_proposition_at_state_with_loop_entry(
        state,
        proposition,
        entry_state,
        &lowering_assumptions,
        &mut budget,
    )
    .map_err(|limit| describe_spec_lowering_limit("lowering", limit))
    .map_err(|message| LoweringRefusal {
        message,
        dropped_fold_body: None,
    })?;
    let Some(path) = exactly_selected_spec_proposition_path(&paths, assumptions) else {
        return Err(LoweringRefusal {
            message: no_single_path_message("lowering", &paths, &budget),
            // Only a lowering that produced nothing at all is explained by a
            // pruned fold: with a path in hand the count, not the prune, is
            // what the caller must read. A dropped runtime error is more
            // concrete still, and its own message keeps precedence.
            dropped_fold_body: (paths.is_empty() && budget.dropped_runtime_error().is_none())
                .then(|| budget.dropped_fold_body().cloned())
                .flatten(),
        });
    };
    let lowered_proposition = crate::kernel::clone_proposition_iteratively(&path.proposition);
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
pub fn c_evaluate_spec_expression_at_state(
    state: &CState,
    expression: &SpecExpression,
    entry_state: Option<&CState>,
    assumptions: &PureFactContext,
) -> Result<(CValue, Vec<Proposition>), String> {
    let (value, obligations) = c_evaluate_spec_expression_with_checked_obligations(
        state,
        expression,
        entry_state,
        assumptions,
    )?;
    Ok((
        value,
        obligations
            .into_iter()
            .map(|obligation| obligation.proposition().clone())
            .collect(),
    ))
}

/// Retains mandatory conversion conditions for proof-side expression capture.
pub(crate) fn c_evaluate_spec_expression_with_checked_obligations(
    state: &CState,
    expression: &SpecExpression,
    entry_state: Option<&CState>,
    assumptions: &PureFactContext,
) -> Result<(CValue, Vec<ProofObligation>), String> {
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
    let [path] = paths.as_slice() else {
        return Err(no_single_path_message("evaluation", &paths, &budget));
    };
    Ok((path.value.clone(), path.obligations.clone()))
}

pub(crate) fn c_evaluate_spec_resource_expression_with_checked_obligations(
    state: &CState,
    expression: &SpecExpression,
    entry_state: Option<&CState>,
    assumptions: &PureFactContext,
) -> Result<(CValue, Vec<ProofObligation>), String> {
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
    Ok((path.value.clone(), path.obligations.clone()))
}

/// Freeze protocols before evaluating an independent contract's assumed guard
/// inputs. This grants no resources and is not a call-site transfer operation.
pub(crate) fn c_state_with_assumed_mutex_inputs(mut state: CState) -> CState {
    if state.resources.facts().iter().any(|fact| {
        matches!(
            fact.resource(),
            CResource::MutexGuard(_) | CResource::MutexLive(_) | CResource::MutexUse(_)
        )
    }) {
        state.preserves_mutex_protocols = true;
    }
    state
}

pub(crate) fn c_mutex_guard_resource(
    state: &CState,
    mutex: &Pointer,
    abstract_entry: bool,
) -> Option<CResourceFact> {
    crate::kernel::mutexes::guard_resource(state, mutex, abstract_entry)
}

pub(crate) fn c_mutex_live_resource(
    state: &CState,
    mutex: &Pointer,
    abstract_entry: bool,
) -> Option<CResourceFact> {
    crate::kernel::mutexes::live_resource(state, mutex, abstract_entry)
}

/// Construct a contract requirement; this does not establish ownership.
pub(crate) fn c_mutex_use_resource_with_type(
    state: &CState,
    mutex: &Pointer,
    protected: ResourceDescription,
) -> CResourceFact {
    let fact = c_mutex_use_resource(state, mutex);
    let CResource::MutexUse(mut identity) = fact.resource().clone() else {
        unreachable!()
    };
    identity.protected = Some(protected);
    CResourceFact::own(CResource::MutexUse(identity))
}

pub(crate) fn c_mutex_use_resource(state: &CState, mutex: &Pointer) -> CResourceFact {
    crate::kernel::mutexes::use_resource(state, mutex)
}

/// Represent the structural destination requirement of one native construction
/// contract at symbolic proof entry. This is part of source obligation setup,
/// not a call rule: actual calls must establish the same requirement through
/// the constructor binder. The input may be a subobject of an unknown enclosing
/// allocation. No storage, initialized value, separation or permission is added.
/// Source-obligation producer for an independently bound constructor receiver.
/// Actual calls validate their retained destination; this issues no permission
/// or initialized bytes and is not a caller pointer conversion.
pub(crate) fn c_construction_contract_input_pointer(
    function: &CFunction,
    address: Pointer,
) -> Option<CPointerValue> {
    let interface = function.contract_interface();
    let (index, layout) = interface.construction_parameter()?;
    if interface.aggregate_return_mode() != CAggregateReturnMode::Copy
        || interface.return_type() != CType::Void
        || interface.return_aggregate_layout().is_some()
    {
        return None;
    }
    let parameter = interface.parameters().get(index)?;
    if !parameter.c_type().is_pointer() || parameter.aggregate_layout().is_some() {
        return None;
    }
    Some(
        CMemory::aggregate_input_pointer(address, layout, parameter.c_type())
            .with_pointee_constant(parameter.pointee_is_constant())
            .with_pointee_volatile(parameter.pointee_is_volatile()),
    )
}

pub(crate) fn c_state_with_construction_contract_input(
    state: CState,
    function: &CFunction,
    arguments: &[CExpression],
) -> Result<CState, String> {
    let interface = function.contract_interface();
    let (pointer, layout) = if let Some((index, layout)) = interface.construction_parameter() {
        if interface.aggregate_return_mode() != CAggregateReturnMode::Copy
            || interface.return_type() != CType::Void
            || interface.return_aggregate_layout().is_some()
        {
            return Err("invalid constructor input interface".into());
        }
        let Some(parameter) = interface.parameters().get(index) else {
            return Err("constructor input parameter is missing".into());
        };
        if !parameter.c_type().is_pointer() || parameter.aggregate_layout().is_some() {
            return Err("constructor input parameter is not a destination pointer".into());
        }
        let Some(CExpression::Value(CValue::Pointer(pointer))) = arguments.get(index) else {
            return Err("constructor input is not an entry pointer value".into());
        };
        (pointer.pointer().clone(), layout)
    } else if interface.aggregate_return_mode() == CAggregateReturnMode::Construction {
        let layout = interface
            .return_aggregate_layout()
            .ok_or("construction result has no layout")?;
        let selected = state
            .aggregate_destination
            .as_deref()
            .ok_or("construction result has no selected destination")?;
        if &selected.layout != layout {
            return Err("construction result destination has a different layout".into());
        }
        (selected.pointer.clone(), layout)
    } else {
        return Ok(state);
    };
    let memory = state
        .memory()
        .clone()
        .with_object_input_domain(pointer, layout)?;
    Ok(state.with_memory(memory))
}

pub fn c_function_entry_state(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
) -> Option<CState> {
    c_function_entry_state_with_assumptions(
        caller_state,
        function,
        arguments,
        &PureFactContext::new(),
    )
}

/// Rebind a checked frontier using its actual caller facts for native object
/// arguments whose containing-array position is symbolic.
pub fn c_function_entry_state_with_assumptions(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
) -> Option<CState> {
    let values = arguments
        .iter()
        .map(|argument| match argument {
            CExpression::Value(value) => Some(value.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    let mut entry =
        bind_c_function_arguments_with_assumptions(caller_state, function, &values, assumptions)?;
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
pub(crate) fn c_state_with_borrowed_contract_inputs(
    state: CState,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
) -> Result<CState, LoanRefusalDiagnostic> {
    let mut state = state;
    state.preserves_mutex_protocols |=
        crate::kernel::functions::preserves_mutex_protocols(function.contract_interface());
    let has_views = function
        .resource_requires()
        .iter()
        .any(CResourceSpec::is_view);
    if !has_views && !state.preserves_mutex_protocols {
        return Ok(state);
    }
    if state.loan_ledger().is_some()
        || state.loan_participant().is_some()
        || state.loan_view_bindings().iter().next().is_some()
        || !state.loan_bindings_are_consistent()
    {
        return Err(LoanRefusal::InvalidEvidence.diagnostic(LoanRefusalOperation::Entry));
    }
    if let Some(rooted) = BORROWED_INPUT_ROOTS.with(|roots| {
        roots
            .borrow()
            .get(function.name())
            .filter(|(installed_on, _)| installed_on == &state)
            .map(|(_, rooted)| rooted.clone())
    }) {
        // Loan identities are reused across separately checked claims, but
        // their pure contexts have independent graph lineages. This is the
        // selected contract-input producer boundary, not a permission query.
        rooted
            .resources()
            .synchronize_memory_equalities(assumptions);
        return Ok(rooted);
    }
    let mut rooted = if has_views {
        install_borrowed_contract_inputs(state.clone(), function, arguments, assumptions)?
    } else {
        state.clone()
    };
    // Root only actual primitive input occurrences. A description alone is
    // never authority at an executing call site.
    let use_inputs = rooted.resources().facts().iter().filter(|fact|
        matches!(fact.resource(), CResource::MutexUse(identity) if identity.binding.is_none()))
        .cloned().collect::<Vec<_>>();
    if !use_inputs.is_empty() {
        let mut ledger = rooted
            .loan_ledger()
            .cloned()
            .unwrap_or_else(LoanLedger::new);
        let holder = match rooted.loan_participant() {
            Some(holder) => holder,
            None => ledger
                .fresh_participant()
                .map_err(|e| e.diagnostic(LoanRefusalOperation::Entry))?,
        };
        for fact in use_inputs {
            let CResource::MutexUse(identity) = fact.resource() else {
                unreachable!()
            };
            let (support, _) = rooted
                .resources()
                .unique_owned_occurrence_for_fact(&fact)
                .ok_or_else(|| {
                    LoanRefusal::MissingBacking.diagnostic(LoanRefusalOperation::Entry)
                })?;
            let (next, input) = ledger
                .borrowed_mutex_use_input_with_protected(
                    holder,
                    support,
                    identity.mutex.clone(),
                    identity.protected.clone(),
                )
                .map_err(|e| e.diagnostic(LoanRefusalOperation::Entry))?;
            let bound = next
                .mutex_use_resource(input.usage, holder)
                .map_err(|e| e.diagnostic(LoanRefusalOperation::Entry))?;
            rooted.resources = rooted
                .resources
                .clone()
                .without_fact_delaying_normalization(&fact, assumptions)
                .ok_or_else(|| LoanRefusal::MissingBacking.diagnostic(LoanRefusalOperation::Entry))?
                .try_compose_with_facts_delaying_normalization([bound], assumptions)
                .map_err(|_| LoanRefusal::MissingBacking.diagnostic(LoanRefusalOperation::Entry))?;
            ledger = next;
        }
        rooted.loan_ledger = Some(ledger);
        rooted.loan_participant = Some(holder);
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
        .map_err(|e| e.diagnostic(LoanRefusalOperation::Entry))?;
    rooted = crate::kernel::mutexes::bind_assumed_lifetime_inputs(rooted, assumptions)
        .map_err(|e| e.diagnostic(LoanRefusalOperation::Entry))?;
    // Bind names only after primitive inputs have generative initialization
    // and acquisition identities. A name cannot manufacture its authority.
    if function
        .resource_requires()
        .iter()
        .any(|spec| spec.mutex_authority_binding().is_some())
    {
        let entry =
            c_function_entry_state_with_assumptions(&rooted, function, arguments, assumptions)
                .ok_or_else(|| {
                    LoanRefusal::MissingBacking.diagnostic(LoanRefusalOperation::Entry)
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
            .map_err(|_| LoanRefusal::InvalidEvidence.diagnostic(LoanRefusalOperation::Entry))?
            .map_err(|_| LoanRefusal::MissingBacking.diagnostic(LoanRefusalOperation::Entry))?;
            rooted = rooted
                .bind_named_mutex_authority(identity, &fact)
                .map_err(|_| LoanRefusal::MissingBacking.diagnostic(LoanRefusalOperation::Entry))?;
        }
    }
    if let Some(contract) =
        crate::kernel::mutexes::helper_contracts::classify(function.contract_interface())
            .map_err(|_| LoanRefusal::InvalidEvidence.diagnostic(LoanRefusalOperation::Entry))?
    {
        let entry =
            c_function_entry_state_with_assumptions(&rooted, function, arguments, assumptions)
                .ok_or_else(|| {
                    LoanRefusal::MissingBacking.diagnostic(LoanRefusalOperation::Entry)
                })?;
        let mut budget = ExecutionBudget::beside_live_state();
        let mut evaluate = |spec: &CResourceSpec| {
            super::functions::evaluate_function_resource_spec_with_entry(
                &entry,
                &entry,
                spec,
                assumptions,
                &mut budget,
            )
            .map_err(|_| LoanRefusal::InvalidEvidence.diagnostic(LoanRefusalOperation::Entry))?
            .map_err(|_| LoanRefusal::MissingBacking.diagnostic(LoanRefusalOperation::Entry))
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
                        let CResource::Instance(instance) = fact.resource() else {
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
        .map_err(|_| LoanRefusal::InvalidEvidence.diagnostic(LoanRefusalOperation::Entry))?;
    }
    BORROWED_INPUT_ROOTS.with(|roots| {
        roots
            .borrow_mut()
            .insert(function.name().to_string(), (state, rooted.clone()));
    });
    Ok(rooted)
}

fn install_borrowed_contract_inputs(
    state: CState,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
) -> Result<CState, LoanRefusalDiagnostic> {
    let entry =
        c_function_entry_state_with_assumptions(&state, function, arguments, assumptions)
            .ok_or_else(|| LoanRefusal::MissingBacking.diagnostic(LoanRefusalOperation::Entry))?;
    let mut budget = ExecutionBudget::beside_live_state();
    let (_, checked_inputs) = evaluate_function_resource_context_with_metadata(
        &entry,
        function.resource_requires(),
        function.composite_resource_definitions(),
        assumptions,
        &mut budget,
    )
    .map_err(|_| LoanRefusal::InvalidEvidence.diagnostic(LoanRefusalOperation::Entry))?
    .map_err(|_| LoanRefusal::MissingBacking.diagnostic(LoanRefusalOperation::Entry))?;

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
    let refuse_owned_overlap = |viewed_range: &CMemoryRange| {
        owned_input_ranges
            .iter()
            .find(|owned| {
                crate::kernel::loans::protected_range_proven_overlapping_ignoring_separation(
                    owned,
                    viewed_range,
                    assumptions,
                )
            })
            .map(|owned| {
                LoanRefusal::ActiveDependency.proven_overlap_diagnostic(
                    LoanRefusalOperation::Entry,
                    LoanRefusalSubject::for_conflicting_resources(
                        CResourceFact::view_memory(viewed_range.clone()),
                        CResourceFact::own_memory(owned.clone()),
                    ),
                )
            })
    };
    let mut selected = BTreeMap::new();
    for input in checked_inputs
        .into_iter()
        .filter(|input| input.fact.is_view())
    {
        if let Some(range) = input.fact.memory_range()
            && let Some(diagnostic) = refuse_owned_overlap(range)
        {
            return Err(diagnostic);
        }
        if matches!(
            input.fact.resource(),
            CResource::Memory(range)
                if range.base().block.starts_with("local:")
                    || state.memory().is_read_only_block(&range.base().block)
        ) {
            continue;
        }
        let candidates = state
            .resources()
            .view_occurrences_for_fact(&input.fact, assumptions)
            .into_iter()
            .filter(|occurrence| state.resources().view_occurrence_is_principal(*occurrence))
            .collect::<Vec<_>>();
        let [occurrence] = candidates.as_slice() else {
            return Err(LoanRefusal::MissingLoanBinding.diagnostic_with_subject(
                LoanRefusalOperation::Entry,
                LoanRefusalSubject::for_resource(input.fact),
            ));
        };
        let viewed = state
            .resources()
            .view_fact_at_occurrence(*occurrence)
            .cloned()
            .ok_or_else(|| {
                LoanRefusal::MissingLoanBinding.diagnostic_with_subject(
                    LoanRefusalOperation::Entry,
                    LoanRefusalSubject::with_support_id(*occurrence),
                )
            })?;
        // Address-backed aggregate parameters and compiler-created local
        // arrays are storage owned by this activation. Their bounded views
        // use the existing local-storage check at each call; they are not
        // caller-supplied shared borrows and therefore need no external root.
        if matches!(
            viewed.resource(),
            CResource::Memory(range)
                if range.base().block.starts_with("local:")
                    || state.memory().is_read_only_block(&range.base().block)
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
            return Err(LoanRefusal::ActiveDependency.diagnostic_with_subject(
                LoanRefusalOperation::Entry,
                LoanRefusalSubject::for_supported_view(viewed, owner, *occurrence),
            ));
        }
        selected.entry(*occurrence).or_insert(viewed);
    }

    if selected.is_empty() {
        return Ok(state);
    }

    let mut ledger = LoanLedger::new();
    let participant = ledger
        .fresh_participant()
        .map_err(|error| error.diagnostic(LoanRefusalOperation::Entry))?;
    let mut bindings = LoanViewBindings::default();
    for (occurrence, viewed) in selected {
        let (backing, backing_pieces) = if matches!(viewed.resource(), CResource::Composite { .. })
        {
            let singleton = ResourceContext::new_with_equalities(assumptions)
                .unchecked_with_fact(viewed.clone());
            let pieces = expand_composite_resource_fact_with_children(
                &singleton,
                &viewed,
                function.composite_resource_definitions(),
                state.memory(),
                assumptions,
            )
            .map(|(_, mut children, raw_children)| {
                for raw_child in raw_children {
                    let candidates = state
                        .resources()
                        .view_occurrences_for_fact(&raw_child, assumptions);
                    if let [occurrence] = candidates.as_slice()
                        && let Some(actual) = state
                            .resources()
                            .view_fact_at_occurrence(*occurrence)
                            .cloned()
                        && !children.contains(&actual)
                    {
                        children.push(actual);
                    }
                }
                children
            })
            .and_then(|pieces| {
                BorrowedContractInputBacking::from_checked_expansion(
                    occurrence,
                    viewed.clone(),
                    pieces.clone(),
                )
                .map(|backing| (backing, pieces))
            })
            .ok_or_else(|| {
                LoanRefusal::UnsupportedResource.diagnostic_with_subject(
                    LoanRefusalOperation::Entry,
                    LoanRefusalSubject::with_support_id(occurrence),
                )
            })?;
            (Some(pieces.0), pieces.1)
        } else {
            (None, Vec::new())
        };
        let opening = ledger
            .borrowed_contract_input(participant, occurrence, viewed.clone(), backing)
            .map_err(|error| {
                error.diagnostic_with_subject(
                    LoanRefusalOperation::Entry,
                    LoanRefusalSubject::with_support_id(occurrence),
                )
            })?;
        ledger = ledger.apply(&opening.transition).map_err(|error| {
            error.diagnostic_with_subject(
                LoanRefusalOperation::Entry,
                LoanRefusalSubject::with_support_id(occurrence),
            )
        })?;
        bindings = bindings.with_inserted(
            occurrence,
            LoanViewBinding {
                loan: opening.loan,
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
                return Err(diagnostic);
            }
            let occurrences = state
                .resources()
                .view_occurrences_for_fact(&piece, assumptions);
            match occurrences.as_slice() {
                [] => {}
                [piece_occurrence] => {
                    bindings = bindings.with_inserted(
                        *piece_occurrence,
                        LoanViewBinding {
                            loan: opening.loan,
                            scope: opening.scope,
                            share: opening.root_share,
                            support: occurrence,
                            viewed: piece,
                            hold: None,
                        },
                    );
                }
                _ => {
                    return Err(LoanRefusal::MissingLoanBinding.diagnostic_with_subject(
                        LoanRefusalOperation::Entry,
                        LoanRefusalSubject::for_resource(piece),
                    ));
                }
            }
        }
    }
    Ok(state
        .with_loan_ledger(Some(ledger))
        .with_loan_participant(Some(participant))
        .with_loan_view_bindings(bindings))
}

/// Produces the exact callee entry state used by contract verification.
///
/// Composite requirements normally use their canonical contained resources.
/// When proof execution has explicitly observed or unfolded part of a recursive
/// resource, independent certification preserves that equivalent form so
/// both executions use the same boundary state.
pub fn c_function_contract_entry_state(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
) -> Result<CState, String> {
    let values = arguments
        .iter()
        .map(|argument| match argument {
            CExpression::Value(value) => Some(value.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()
        .ok_or_else(|| "contract entry arguments must be concrete symbolic values".to_string())?;
    let mut budget = ExecutionBudget::beside_live_state();
    match prepare_function_contract_entry_state_with_values(
        caller_state,
        function,
        &values,
        assumptions,
        &mut budget,
    ) {
        Ok(Ok(state)) => Ok(state),
        Ok(Err(error)) => Err(format!(
            "could not prepare contract resources: {}",
            contract_certification::describe_certification_runtime_error(&error)
        )),
        Err(limit) => Err(format!(
            "contract resource preparation stopped at {}",
            limit.describe()
        )),
    }
}

/// Whether a body outcome establishes every resource the contract returns,
/// by the rule contract certification applies to a `produces` claim. A proof
/// consults this before reading the outcome through the contract's resource
/// transition, so the surface accepts exactly the exits certification does.
pub fn c_function_return_resources_definitionally_established(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    outcome: &CFunctionOutcome,
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
            )
        },
    )
}

/// Applies a function's already-checked resource effect to a concrete body
/// outcome. This changes only the contract-level resource/population state;
/// the C value and memory come from the supplied body execution.
pub fn apply_c_function_contract_resource_transition(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    outcome: CFunctionOutcome,
    assumptions: &PureFactContext,
) -> Result<(CFunctionOutcome, Vec<ProofObligation>), String> {
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
pub(crate) fn checked_c_function_contract_resource_transition(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    outcome: CFunctionOutcome,
    assumptions: &PureFactContext,
) -> Result<CFunctionOutcome, String> {
    let (outcome, obligations) = apply_c_function_contract_resource_transition(
        caller_state,
        function,
        arguments,
        outcome,
        assumptions,
    )?;
    if let Some(obligation) = obligations.iter().find(|obligation| {
        !crate::kernel::PureFactContext::settles_exactly(assumptions, obligation.proposition())
    }) {
        return Err(format!(
            "unproved contract resource obligation: {}",
            obligation.context().unwrap_or("resource transition"),
        ));
    }
    Ok(outcome)
}

/// Prepares the count interpretation used to prove a function's return
/// resource invariants, without transferring the body's ownership. This
/// creates no theorem or invariant facts: the eventual specification must
/// still be certified against the checked exit outcome. In particular callers
/// must not project resource invariant facts from this provisional state.
pub(crate) fn function_body_with_return_counts(
    body: &CFunctionOutcome,
    checked_exit: &CFunctionOutcome,
) -> CFunctionOutcome {
    match (body, checked_exit) {
        (
            CFunctionOutcome::Return { value, state },
            CFunctionOutcome::Return {
                state: exit_state, ..
            },
        ) => {
            let mut state = state.clone();
            state.observed_population_families = exit_state.observed_population_families.clone();
            CFunctionOutcome::Return {
                value: value.clone(),
                state,
            }
        }
        _ => body.clone(),
    }
}

/// Applies a kernel-checked, zero-source construction of one abstract token
/// to a function outcome state.
pub fn construct_c_function_resource(
    state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    result: &CValue,
    constructed: &CResourceFact,
    assumptions: &PureFactContext,
) -> Result<CState, String> {
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

pub fn c_function_outcome_from_statement_outcome(
    caller_state: &CState,
    function: &CFunction,
    outcome: CStatementOutcome,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> (CFunctionOutcome, Vec<ProofObligation>) {
    function_outcome_from_body(
        caller_state,
        function,
        outcome,
        obligations,
        assumptions,
        None,
    )
}

/// Applies the ordinary function-exit transition, splitting only the
/// transition boundary when a conditional resource effect is undecided. The
/// C body is not executed again: each returned case reuses the supplied statement
/// outcome and carries the guard facts that authorized its boundary check.
pub(crate) fn c_function_outcomes_from_statement_outcome_with_resource_cases(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    outcome: CStatementOutcome,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<(CFunctionOutcome, Vec<ProofObligation>, Vec<Proposition>)> {
    let original_outcome = outcome.clone();
    let original_obligations = obligations.clone();
    let (outcome, obligations) = c_function_outcome_from_statement_outcome(
        caller_state,
        function,
        outcome,
        obligations,
        assumptions,
    );
    let CFunctionOutcome::RuntimeError(error) = &outcome else {
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
        let (case_outcome, case_obligations) = c_function_outcome_from_statement_outcome(
            caller_state,
            function,
            original_outcome.clone(),
            original_obligations.clone(),
            &case_assumptions,
        );
        if !matches!(
            case_outcome,
            CFunctionOutcome::RuntimeError(
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

pub fn c_function_specification(
    state: CState,
    arguments: Vec<CExpression>,
    requires: Vec<Proposition>,
    outcome: CFunctionOutcome,
) -> CFunctionSpecification {
    CFunctionSpecification::new(state, arguments, requires, outcome)
}

pub fn proposition_and(left: Proposition, right: Proposition) -> Proposition {
    Proposition::And(Box::new(left), Box::new(right))
}

pub fn proposition_and_all(mut propositions: Vec<Proposition>) -> Proposition {
    if propositions.is_empty() {
        return Proposition::ConditionIs(ConditionTerm::Constant(true), true);
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

/// Expands C expression definedness into the exact pure proposition under
/// which evaluation reaches a value rather than undefined behavior.
pub fn c_expression_definedness_proposition(
    state: &CState,
    expression: &CExpression,
) -> Result<Proposition, ExecutionLimit> {
    let mut budget = ExecutionBudget::for_new_execution().with_c_expression_cost(expression);
    let paths =
        evaluate_c_expression_paths(state, expression, &PureFactContext::new(), &mut budget)?;
    let mut normal_paths = paths.into_iter().filter_map(|path| {
        if !matches!(path.outcome, CExpressionOutcome::Value(_)) {
            return None;
        }
        Some(proposition_and_all(
            path.facts
                .into_iter()
                .map(|fact| fact.proposition().clone())
                .chain(
                    path.obligations
                        .into_iter()
                        .map(|obligation| obligation.proposition().clone()),
                )
                .collect(),
        ))
    });
    let Some(first) = normal_paths.next() else {
        return Ok(Proposition::ConditionIs(
            ConditionTerm::Constant(false),
            true,
        ));
    };
    Ok(normal_paths.fold(first, |left, right| {
        Proposition::Or(Box::new(left), Box::new(right))
    }))
}

pub fn substitute_int32_variable_in_proposition(
    proposition: &Proposition,
    variable: Variable,
    value: Bitvector32Term,
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
) -> Vec<Bitvector32Term> {
    let Proposition::ForAll { var, body, .. } = quantified else {
        return Vec::new();
    };
    let mut candidates = match target {
        Proposition::ConditionIs(condition, _) => {
            PureFactContext::guided_forall_condition_candidates(*var, body, condition)
        }
        _ => BTreeSet::new(),
    };
    let variables = vec![*var];
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
) -> Vec<Bitvector32Term> {
    let Proposition::ForAll { var, body, .. } = quantified else {
        return Vec::new();
    };
    match target {
        Proposition::ConditionIs(condition, _) => {
            PureFactContext::guided_forall_condition_candidates(*var, body, condition)
                .into_iter()
                .collect()
        }
        _ => Vec::new(),
    }
}

/// Chooses a variable identity absent from both the free variables and logical
/// binders of the supplied propositions.
pub fn fresh_int32_variable_for_propositions(propositions: &[Proposition]) -> Variable {
    let mut reserved = BTreeSet::new();
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

pub fn c_max_body() -> CStatement {
    c_if(
        c_less_than(c_variable("a"), c_variable("b")),
        c_return(c_variable("b")),
        c_return(c_variable("a")),
    )
}

pub fn c_max_function() -> CFunction {
    c_function(
        CType::Int32,
        "max",
        vec![
            c_parameter("a", CType::Int32),
            c_parameter("b", CType::Int32),
        ],
        c_max_body(),
    )
}

pub fn c_max_environment(a: CValue, b: CValue) -> CLocalEnvironment {
    CLocalEnvironment::new().with("a", a).with("b", b)
}

pub fn c_max_state(a: CValue, b: CValue) -> CState {
    CState::new().with_local("a", a).with_local("b", b)
}

pub fn c_max_lt_condition(a: Bitvector32Term, b: Bitvector32Term) -> ConditionTerm {
    ConditionTerm::signed_less_than(a, b)
}

pub fn prove_c_expression_evaluation(state: CState, expression: CExpression) -> Option<Theorem> {
    let mut budget = ExecutionBudget::for_new_execution().with_c_expression_cost(&expression);
    let outcome = evaluate_c_expression(&state, &expression, &PureFactContext::new(), &mut budget)?;
    Some(Theorem::new(Proposition::CExpressionEvaluates {
        state: Box::new(state),
        expression,
        outcome,
    }))
}

pub fn prove_symbolic_c_condition_evaluation(
    state: CState,
    condition: CExpression,
    assumptions: PureFactContext,
) -> SymbolicCConditionEvaluation {
    let mut budget = ExecutionBudget::beside_live_state().with_c_expression_cost(&condition);
    let expression_paths =
        match evaluate_c_condition_paths(&state, &condition, &assumptions, &mut budget) {
            Ok(paths) => paths,
            Err(limit) => {
                return SymbolicCConditionEvaluation {
                    paths: Vec::new(),
                    limit: Some(limit),
                };
            }
        };
    let mut outcomes = Vec::new();
    for path in expression_paths {
        match path.outcome {
            CExpressionOutcome::Value(value) => {
                outcomes.extend(
                    c_truthiness_paths(value, path.facts, path.obligations, &assumptions)
                        .into_iter()
                        .map(|path| {
                            (
                                CConditionOutcome::Value(path.is_true),
                                path.facts,
                                path.obligations,
                            )
                        }),
                );
            }
            CExpressionOutcome::UndefinedBehavior(kind) => outcomes.push((
                CConditionOutcome::UndefinedBehavior(kind),
                path.facts,
                path.obligations,
            )),
            CExpressionOutcome::RuntimeError(error) => outcomes.push((
                CConditionOutcome::RuntimeError(error),
                path.facts,
                path.obligations,
            )),
        }
    }
    let paths = outcomes
        .into_iter()
        .map(|(outcome, facts, obligations)| {
            let facts = public_execution_pure_facts(&facts);
            let proposition = Proposition::CConditionEvaluates {
                state: Box::new(state.clone()),
                condition: condition.clone(),
                outcome,
            };
            let theorem = Theorem::new(wrap_proof_facts(
                proposition,
                &assumptions,
                &facts,
                &obligations,
            ));
            SymbolicCConditionEvaluationPath {
                facts,
                obligations,
                theorem,
            }
        })
        .collect();

    SymbolicCConditionEvaluation { paths, limit: None }
}

pub fn prove_c_statement_execution(state: CState, statement: CStatement) -> Option<Theorem> {
    prove_symbolic_c_execution(state, statement, PureFactContext::new())
}

pub fn prove_c_statement_execution_under_assumptions(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
) -> Option<Theorem> {
    prove_symbolic_c_execution(state, statement, assumptions)
}

pub fn prove_symbolic_c_execution(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
) -> Option<Theorem> {
    let budget = ExecutionBudget::for_new_execution().with_c_statement_cost(&statement);
    prove_symbolic_c_execution_with_budget(state, statement, assumptions, budget)
}

pub fn prove_symbolic_c_execution_with_budget(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    budget: ExecutionBudget,
) -> Option<Theorem> {
    prove_symbolic_c_execution_with_environment_and_budget(
        state,
        statement,
        assumptions,
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        budget,
    )
}

pub fn prove_symbolic_c_execution_with_environment(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> Option<Theorem> {
    let budget = ExecutionBudget::for_new_execution().with_c_statement_cost(&statement);
    prove_symbolic_c_execution_with_environment_and_budget(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
        budget,
    )
}

pub fn prove_symbolic_c_execution_with_environment_and_budget(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: ExecutionBudget,
) -> Option<Theorem> {
    let execution = prove_symbolic_c_execution_paths_with_environment_and_budget(
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

pub fn prove_symbolic_c_execution_paths(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
) -> SymbolicCExecution {
    let budget = ExecutionBudget::for_new_execution().with_c_statement_cost(&statement);
    prove_symbolic_c_execution_paths_with_budget(state, statement, assumptions, budget)
}

pub fn prove_symbolic_c_execution_paths_with_budget(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    budget: ExecutionBudget,
) -> SymbolicCExecution {
    prove_symbolic_c_execution_paths_with_environment_and_budget(
        state,
        statement,
        assumptions,
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        budget,
    )
}

pub fn prove_symbolic_c_execution_paths_with_environment(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> SymbolicCExecution {
    let budget = ExecutionBudget::for_new_execution().with_c_statement_cost(&statement);
    prove_symbolic_c_execution_paths_with_environment_and_budget(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
        budget,
    )
}

pub fn prove_symbolic_c_execution_paths_with_environment_and_budget(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    mut budget: ExecutionBudget,
) -> SymbolicCExecution {
    let paths = match execute_c_statement_paths(
        &state,
        &statement,
        &assumptions,
        &environment,
        execution_semantics,
        &mut budget,
    ) {
        Ok(paths) => paths,
        Err(limit) => {
            return SymbolicCExecution {
                paths: Vec::new(),
                limit: Some(limit),
            };
        }
    };
    let paths = paths
        .into_iter()
        .map(|mut path| {
            if let Some(memory) = statement_outcome_memory(&path.outcome) {
                path.facts.extend(
                    memory
                        .string_literal_loadable_facts()
                        .into_iter()
                        .map(ExecutionPureFact::certified),
                );
            }
            let effect_facts = memory_effect_execution_facts(&path.facts);
            let facts = public_execution_pure_facts(&path.facts);
            let proposition = if execution_semantics == CExecutionSemantics::EXECUTE_BODIES {
                Proposition::CStatementExecutes {
                    state: Box::new(state.clone()),
                    statement: Box::new(statement.clone()),
                    outcome: path.outcome,
                }
            } else {
                Proposition::CStatementVerifies {
                    state: Box::new(state.clone()),
                    statement: Box::new(statement.clone()),
                    outcome: path.outcome,
                }
            };
            let theorem = Theorem::new(wrap_proof_facts(
                proposition,
                &assumptions,
                &facts,
                &path.obligations,
            ));
            SymbolicCExecutionPath {
                completion_origin: None,
                assumptions: assumptions.clone(),
                post_assumptions: None,
                facts,
                effect_facts,
                obligations: path.obligations,
                theorem,
                loan_evidence: path.loan_evidence,
            }
        })
        .collect();

    SymbolicCExecution { paths, limit: None }
}

pub fn prove_symbolic_c_statement_verification_paths_with_environment(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> SymbolicCExecution {
    prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
    )
    .0
}

pub fn prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> (SymbolicCExecution, Option<CVerifiedLoopRule>) {
    let mut budget =
        ExecutionBudget::for_new_execution().with_c_statement_verification_cost(&statement);
    prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule_using_budget(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
        &mut budget,
    )
}

fn statement_kernel_variables(
    state: &CState,
    statement: &CStatement,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
) -> KernelVariableGenerator {
    let mut existing = BTreeSet::new();
    collect_c_state_bitvector_variables(state, &mut existing);
    collect_c_statement_bitvector_variables(statement, &mut existing);
    collect_assumption_variables(assumptions, &mut existing);
    KernelVariableGenerator::fresh_for_execution_with_shared_reservations(
        existing,
        execution_environment_variable_index(environment),
    )
}

pub(crate) fn prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule_using_budget(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> (SymbolicCExecution, Option<CVerifiedLoopRule>) {
    let mut variables = statement_kernel_variables(&state, &statement, &assumptions, &environment);
    let execution = execute_c_statement_verification_paths(
        &state,
        &statement,
        &assumptions,
        &environment,
        execution_semantics,
        budget,
        &mut variables,
    );
    let paths = match execution {
        Ok(paths) => paths,
        Err(limit) => {
            return (
                SymbolicCExecution {
                    paths: Vec::new(),
                    limit: Some(limit),
                },
                None,
            );
        }
    };
    let paths = paths
        .into_iter()
        .map(|mut path| {
            if let Some(memory) = statement_outcome_memory(&path.outcome) {
                path.facts.extend(
                    memory
                        .string_literal_loadable_facts()
                        .into_iter()
                        .map(ExecutionPureFact::certified),
                );
            }
            path
        })
        .collect();
    symbolic_c_statement_execution_with_loop_rule(
        state,
        statement,
        assumptions,
        paths,
        &environment,
    )
}

fn statement_outcome_memory(outcome: &CStatementOutcome) -> Option<&CMemory> {
    match outcome {
        CStatementOutcome::Normal(state)
        | CStatementOutcome::Break(state)
        | CStatementOutcome::Continue(state)
        | CStatementOutcome::Jump { state, .. } => Some(state.memory()),
        CStatementOutcome::Return { state, .. } | CStatementOutcome::Throw { state, .. } => {
            Some(state.memory())
        }
        CStatementOutcome::VerificationDiverges
        | CStatementOutcome::UndefinedBehavior(_)
        | CStatementOutcome::RuntimeError(_) => None,
    }
}

#[cfg(test)]
pub(crate) fn prove_symbolic_c_loop_exit_with_proven_phases(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    initialization_proven: bool,
    preservation_proven: bool,
    final_exit_candidates: Vec<CLoopFinalExitCandidate>,
    break_exits: Vec<CLoopBreakExit>,
    return_exits: Vec<CLoopReturnExit>,
) -> (SymbolicCExecution, Option<CVerifiedLoopRule>) {
    let mut budget =
        ExecutionBudget::for_new_execution().with_c_statement_verification_cost(&statement);
    prove_symbolic_c_loop_exit_with_proven_phases_using_budget(
        state,
        statement,
        assumptions,
        environment,
        initialization_proven,
        preservation_proven,
        final_exit_candidates,
        break_exits,
        return_exits,
        &mut budget,
    )
}

pub(crate) fn prove_symbolic_c_loop_exit_with_proven_phases_using_budget(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    initialization_proven: bool,
    preservation_proven: bool,
    final_exit_candidates: Vec<CLoopFinalExitCandidate>,
    break_exits: Vec<CLoopBreakExit>,
    return_exits: Vec<CLoopReturnExit>,
    budget: &mut ExecutionBudget,
) -> (SymbolicCExecution, Option<CVerifiedLoopRule>) {
    let CStatement::While {
        condition,
        invariant,
        invariant_checks,
        effect_checks,
        resource_specs,
        ranking_measures,
        structural_measure,
        body,
        do_while,
        backedge_target,
        natural_exit_target,
        ..
    } = &statement
    else {
        return (
            SymbolicCExecution {
                paths: Vec::new(),
                limit: None,
            },
            None,
        );
    };
    let mut variables = statement_kernel_variables(&state, &statement, &assumptions, &environment);
    let execution = execute_c_while_exit_paths_with_proven_phases(
        &state,
        condition,
        invariant,
        invariant_checks,
        effect_checks,
        resource_specs,
        ranking_measures,
        structural_measure.as_deref(),
        body,
        &assumptions,
        &environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        initialization_proven,
        preservation_proven,
        &final_exit_candidates,
        &break_exits,
        &return_exits,
        budget,
        &mut variables,
        *do_while,
        *backedge_target,
        *natural_exit_target,
    );
    let paths = match execution {
        Ok(paths) => paths,
        Err(limit) => {
            return (
                SymbolicCExecution {
                    paths: Vec::new(),
                    limit: Some(limit),
                },
                None,
            );
        }
    };
    symbolic_c_statement_execution_with_loop_rule(
        state,
        statement,
        assumptions,
        paths,
        &environment,
    )
}

fn symbolic_c_statement_execution_with_loop_rule(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    paths: Vec<CStatementExecutionPath>,
    environment: &CExecutionEnvironment,
) -> (SymbolicCExecution, Option<CVerifiedLoopRule>) {
    // A rule's paths are the loop statement's successors: the joined exit,
    // a proven-divergent loop, each checked natural forward jump, and each
    // `return` the body reaches. A returned
    // path leaves the function from inside the loop; the rule carries it so
    // the enclosing execution continues with it as a returned path instead of
    // certifying the function on the exit path alone.
    let loop_rule = (matches!(statement, CStatement::While { .. })
        && paths.iter().all(|path| {
            (matches!(
                path.outcome,
                CStatementOutcome::Normal(_)
                    | CStatementOutcome::Return { .. }
                    | CStatementOutcome::VerificationDiverges
            ) || matches!(
                (&statement, &path.outcome),
                (CStatement::While {
                    backedge_target: Some(_),
                    natural_exit_target: Some(exit_target),
                    ..
                }, CStatementOutcome::Jump { target, .. }) if target == exit_target
            )) && path.obligations.iter().all(ProofObligation::is_assumable)
        }))
    .then(|| CVerifiedLoopRule {
        symbolic_entry_state: state.clone(),
        loop_statement: statement.clone(),
        loop_index: None,
        required_assumptions: assumptions.clone(),
        paths: paths.clone(),
        composite_resource_definitions: Vec::new(),
        // The rule records the anchor its own body was stepped under. A
        // self-call in that body raised the descent obligations exactly when
        // this is set, and the rule was only formed because every obligation
        // on its paths was discharged or assumable, so this is the kernel's
        // own note of what the summary already paid for.
        recursion_anchor: environment.recursion_anchor_handle(),
    });
    let paths = paths
        .into_iter()
        .map(|path| {
            let effect_facts = memory_effect_execution_facts(&path.facts);
            let facts = public_execution_pure_facts(&path.facts);
            let proposition = Proposition::CStatementVerifies {
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
            SymbolicCExecutionPath {
                completion_origin: None,
                assumptions: assumptions.clone(),
                post_assumptions: None,
                facts,
                effect_facts,
                obligations: path.obligations,
                theorem,
                loan_evidence: path.loan_evidence,
            }
        })
        .collect();

    (SymbolicCExecution { paths, limit: None }, loop_rule)
}

pub fn prove_symbolic_c_function_execution(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
) -> Option<Theorem> {
    let budget = ExecutionBudget::for_new_execution().with_c_function_cost(&function, &arguments);
    prove_symbolic_c_function_execution_with_budget(state, function, arguments, assumptions, budget)
}

pub fn prove_symbolic_c_function_execution_with_budget(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
    budget: ExecutionBudget,
) -> Option<Theorem> {
    prove_symbolic_c_function_execution_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        budget,
    )
}

pub fn prove_symbolic_c_function_execution_with_environment(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> Option<Theorem> {
    let budget = ExecutionBudget::for_new_execution().with_c_function_cost(&function, &arguments);
    prove_symbolic_c_function_execution_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
    )
}

pub fn prove_symbolic_c_function_execution_with_environment_and_budget(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: ExecutionBudget,
) -> Option<Theorem> {
    let execution = prove_symbolic_c_function_execution_paths_with_environment_and_budget(
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

pub fn prove_symbolic_c_function_execution_paths(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
) -> SymbolicCExecution {
    let budget = ExecutionBudget::for_new_execution().with_c_function_cost(&function, &arguments);
    prove_symbolic_c_function_execution_paths_with_budget(
        state,
        function,
        arguments,
        assumptions,
        budget,
    )
}

pub fn prove_symbolic_c_function_execution_paths_with_budget(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
    budget: ExecutionBudget,
) -> SymbolicCExecution {
    prove_symbolic_c_function_execution_paths_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        budget,
    )
}

pub fn prove_symbolic_c_function_execution_paths_with_environment(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> SymbolicCExecution {
    let budget = ExecutionBudget::for_new_execution().with_c_function_cost(&function, &arguments);
    prove_symbolic_c_function_execution_paths_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
    )
}

pub fn prove_symbolic_c_function_execution_paths_with_environment_and_budget(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: ExecutionBudget,
) -> SymbolicCExecution {
    prove_symbolic_c_function_execution_paths_with_contract_resources(
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

fn function_has_conditional_resource_effect(function: &CFunction) -> bool {
    function
        .resource_ensures()
        .iter()
        .any(|resource| resource.guard().is_some())
}

#[allow(clippy::too_many_arguments)]
fn prove_symbolic_c_function_execution_paths_with_contract_resources(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    mut budget: ExecutionBudget,
    prepare_contract_resources: bool,
) -> SymbolicCExecution {
    let defer_conditional_resource_effect = function_has_conditional_resource_effect(&function);
    let paths = match execute_c_function_paths_with_contract_resources(
        &state,
        &function,
        &arguments,
        &assumptions,
        &environment,
        execution_semantics,
        &mut budget,
        prepare_contract_resources,
        defer_conditional_resource_effect,
    ) {
        Ok(paths) => paths,
        Err(limit) => {
            return SymbolicCExecution {
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
            let proposition = if execution_semantics == CExecutionSemantics::EXECUTE_BODIES {
                Proposition::CFunctionExecutes {
                    state: Box::new(state.clone()),
                    function: Box::new(function.clone()),
                    arguments: arguments.clone(),
                    outcome: path.outcome,
                }
            } else {
                Proposition::CFunctionVerifies {
                    state: Box::new(state.clone()),
                    function: Box::new(function.clone()),
                    arguments: arguments.clone(),
                    outcome: path.outcome,
                }
            };
            let theorem = Theorem::new(wrap_proof_facts(
                proposition,
                &assumptions,
                &facts,
                &path.obligations,
            ));
            SymbolicCExecutionPath {
                completion_origin: None,
                assumptions: assumptions.clone(),
                post_assumptions: None,
                facts,
                effect_facts,
                obligations: path.obligations,
                theorem,
                loan_evidence: path.loan_evidence,
            }
        })
        .collect();

    SymbolicCExecution { paths, limit: None }
}

pub fn prove_symbolic_c_function_verification_paths_with_environment(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> SymbolicCExecution {
    let budget = ExecutionBudget::for_new_execution()
        .with_c_function_verification_cost(&function, &arguments);
    prove_symbolic_c_function_verification_paths_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
    )
}

pub fn prove_symbolic_c_function_verification_paths_with_environment_and_budget(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: ExecutionBudget,
) -> SymbolicCExecution {
    prove_symbolic_c_function_verification_paths(
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

/// Verifies an exact function body from its declared contract-entry resources.
///
/// Unlike ordinary proof execution, this canonicalizes composite requirements
/// before body execution. It is the independent execution used to certify
/// opaque contract claims.
pub fn prove_symbolic_c_function_contract_verification_paths_with_environment(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> SymbolicCExecution {
    let environment = if environment.has_conditional_resource_effects()
        || function_has_conditional_resource_effect(&function)
    {
        environment.with_conditional_resource_cases()
    } else {
        environment
    };
    let defer_conditional_resource_effect = function_has_conditional_resource_effect(&function);
    let budget = ExecutionBudget::for_new_execution()
        .with_c_function_verification_cost(&function, &arguments);
    prove_symbolic_c_function_verification_paths(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
        true,
        defer_conditional_resource_effect,
    )
}

/// Executes one whole-function judgment and retains its exact authority inputs
/// together with the resulting frontier for later contract certification.
#[allow(clippy::too_many_arguments)]
pub fn prove_checked_c_function_execution_with_environment(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    mode: CFunctionContractExecutionMode,
) -> CCheckedFunctionExecution {
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
        CFunctionContractExecutionMode::VerifyLoops => {
            prove_symbolic_c_function_verification_paths(
                state.clone(),
                function.clone(),
                arguments.clone(),
                assumptions.clone(),
                environment.clone(),
                execution_semantics,
                ExecutionBudget::for_new_execution()
                    .with_c_function_verification_cost(&function, &arguments),
                true,
                defer_conditional_resource_effect,
            )
        }
        CFunctionContractExecutionMode::ExecuteLoops => {
            prove_symbolic_c_function_execution_paths_with_contract_resources(
                state.clone(),
                function.clone(),
                arguments.clone(),
                assumptions.clone(),
                environment.clone(),
                execution_semantics,
                ExecutionBudget::for_new_execution().with_c_function_cost(&function, &arguments),
                true,
            )
        }
    };
    let path_count = execution.paths().len();
    CCheckedFunctionExecution {
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
        checked_returned_resources: vec![ResourceContext::new(); path_count],
        entry_representation_origin: None,
        boundary_transfer: None,
        checked_call_events: Default::default(),
        checked_callees: None,
        applied_tactics: Default::default(),
    }
}

pub(in crate::kernel) fn proof_evidence_conclusion(theorem: &Theorem) -> &Proposition {
    let mut conclusion = theorem.proposition();
    while let Proposition::Implies(_, body) = conclusion {
        conclusion = body;
    }
    conclusion
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

/// The first premise of a retained transition theorem that is not retained,
/// if any. A premise is retained when it is an
/// exact fact of the entry context, of the context the theorem was proved
/// under (`CheckedExecutionEvent::Context`), of the candidate path, an
/// obligation, or a resource-certified loadability. A loadability premise
/// may also be covered by a loadability fact of the retained context over a
/// wider range of the same block (a callee's requirement inside the caller's
/// `loadable(p[0..n])`), which is the one range rule the executor
/// discharged it with. Nothing else is derived.
pub(in crate::kernel) fn proof_evidence_unretained_premise(
    theorem: &Theorem,
    assumptions: &PureFactContext,
    executed_under: Option<&PureFactContext>,
    execution_facts: &(impl ExecutionFactSource + ?Sized),
    obligations: &[ProofObligation],
    state: &CState,
    function_entry_resource_facts: Option<&PureFactContext>,
) -> Option<Proposition> {
    // The path's retained facts (with their conjuncts) and obligations, as
    // one set built the first time a premise misses both contexts: a
    // theorem lists a premise per context fact, and scanning the path's
    // facts once per premise was quadratic in the path. A retained fact
    // contributes its conjuncts: conjunction elimination is the one
    // structural rule the proof object applies to retained facts (a kernel
    // theorem lists the context it executed under as atomic condition facts,
    // while a loop step retains the lowered invariant it assumed as one
    // conjunction, so `And(a, b)` retained is `a` retained).
    let mut retained: Option<BTreeSet<&Proposition>> = None;
    let mut retained_contains = |premise: &Proposition| {
        retained
            .get_or_insert_with(|| {
                let mut set = BTreeSet::new();
                let mut pending = execution_facts
                    .fact_iter()
                    .map(ExecutionPureFact::proposition)
                    .collect::<Vec<_>>();
                // Uncharged, as the scan it replaces was. The set is still
                // linear in the path's facts at each checked step, a
                // per-step cost the contract does not allow: charging it
                // makes `expanded_roundtrip_extra_copy_is_logarithmic_beside_unrelated_allocations`
                // grow a unit per unrelated allocation (see
                // docs/internals/verification-efficiency.md).
                while let Some(fact) = pending.pop() {
                    if set.insert(fact)
                        && let Proposition::And(left, right) = fact
                    {
                        pending.push(left);
                        pending.push(right);
                    }
                }
                set.extend(obligations.iter().map(ProofObligation::proposition));
                crate::kernel::reasoning::path_facts::count_uncharged_context_entries(set.len());
                set
            })
            .contains(premise)
    };
    let mut proposition = theorem.proposition();
    while let Proposition::Implies(premise, body) = proposition {
        if !(assumptions.proves_exact(premise)
            || executed_under.is_some_and(|context| context.proves_exact(premise))
            || retained_contains(premise)
            || resources_certify_loadability(state, state.resources(), premise, assumptions)
            || (matches!(premise.as_ref(), Proposition::CMemoryLoadable { .. })
                && executed_under
                    .is_some_and(|context| loadable_covered_by_fact(context, premise)))
            || (matches!(
                premise.as_ref(),
                Proposition::CResourceContains { .. } | Proposition::CResourceSeparate { .. }
            ) && function_entry_resource_facts
                .is_some_and(|facts| facts.proves_exact(premise))))
        {
            return Some(premise.as_ref().clone());
        }
        proposition = body;
    }
    None
}

pub(crate) fn execution_evidence_states_match(
    function: &CFunction,
    left: &CState,
    right: &CState,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    // Stable-view authority is semantic state, even though ordinary entry
    // rebasing is allowed to change the ghost resource representation.  Do
    // not let a checked execution cross a loan root, holder, or occurrence
    // binding boundary while comparing the remaining representation.
    if !loan_authority_states_match(left, right) {
        return false;
    }
    let mut left_without_ghost_difference = left.clone();
    left_without_ghost_difference.resources = right.resources.clone();
    left_without_ghost_difference.observed_population_families =
        right.observed_population_families.clone();
    left_without_ghost_difference == *right
        && contract_certification::resource_contexts_definitionally_equal_with_definitions(
            function.composite_resource_definitions(),
            left.memory(),
            left.resources(),
            right.memory(),
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
    function: &CFunction,
    left: &CState,
    right: &CState,
    assumptions: &PureFactContext,
) -> bool {
    loan_authority_states_match(left, right)
        && left.locals == right.locals
        && left.memory.heap == right.memory.heap
        && left.local_cell_values().eq(right.local_cell_values())
        && c_memories_definitionally_equal(left.memory(), right.memory(), assumptions)
        && contract_certification::resource_contexts_definitionally_equal_with_definitions(
            function.composite_resource_definitions(),
            left.memory(),
            left.resources(),
            right.memory(),
            right.resources(),
            assumptions,
        )
        && population_observations_equal(left, right)
}

/// Compare the stable-view authority that cannot be reconstructed from a
/// resource representation.  Resource occurrences are opaque identities, so
/// equal-looking resource facts are insufficient when a checked artifact is
/// rebased onto another proof entry.
fn loan_authority_states_match(left: &CState, right: &CState) -> bool {
    left.loan_ledger() == right.loan_ledger()
        && left.loan_participant() == right.loan_participant()
        && left.loan_view_bindings() == right.loan_view_bindings()
        && left.loan_bindings_are_consistent()
        && right.loan_bindings_are_consistent()
}

pub(in crate::kernel) fn proof_evidence_function_refines_same_source(
    original: &CFunction,
    checked: &CFunction,
) -> bool {
    original.return_type() == checked.return_type()
        && original.name() == checked.name()
        && original.parameters() == checked.parameters()
        && original.exceptional_signature() == checked.exceptional_signature()
        && original.source_body() == checked.source_body()
        && original.resource_requires() == checked.resource_requires()
        && original.resource_ensures() == checked.resource_ensures()
        && original.resource_constructors() == checked.resource_constructors()
        && original.contract_requires() == checked.contract_requires()
        && original.contract_ensures() == checked.contract_ensures()
        && original.exceptional_ensures() == checked.exceptional_ensures()
        && original.contract_mutable() == checked.contract_mutable()
        && original.resource_derived_mutable_frame() == checked.resource_derived_mutable_frame()
        && original.contract_interface().resource_derived_frame_mixed
            == checked.contract_interface().resource_derived_frame_mixed
        && original.contract_effect_claim_required() == checked.contract_effect_claim_required()
        && original.contract_claims() == checked.contract_claims()
        && original.opaque_contract_supported() == checked.opaque_contract_supported()
        && original.composite_resource_definitions() == checked.composite_resource_definitions()
        && original.predicate_unfoldings() == checked.predicate_unfoldings()
}

pub(in crate::kernel) fn proof_evidence_initial_state(
    events: &[crate::kernel::proof::CheckedExecutionEvent],
) -> Option<&CState> {
    use crate::kernel::proof::CheckedExecutionEvent;

    events.iter().find_map(|event| match event {
        CheckedExecutionEvent::ProofCase(_)
        | CheckedExecutionEvent::ReturnProposition(_)
        | CheckedExecutionEvent::Context(_)
        | CheckedExecutionEvent::StatementEffects(_)
        | CheckedExecutionEvent::Call(_) => None,
        CheckedExecutionEvent::AutomaticLifetimeEnd(end) => Some(end.before_state()),
        CheckedExecutionEvent::ResourceObservation(observation) => Some(observation.before_state()),
        CheckedExecutionEvent::ResourceRewrite(rewrite) => Some(rewrite.before_state()),
        CheckedExecutionEvent::PopulationAuthorityRewrite(rewrite) => Some(rewrite.before_state()),
        CheckedExecutionEvent::PopulationMemberRewrite(rewrite) => Some(rewrite.before_state()),
        CheckedExecutionEvent::IteratedStep(step) => Some(step.before_state()),
        CheckedExecutionEvent::TacticApplication(application) => Some(application.before_state()),
        CheckedExecutionEvent::Statement(theorem) | CheckedExecutionEvent::Condition(theorem) => {
            match proof_evidence_conclusion(theorem) {
                Proposition::CStatementVerifies { state, .. }
                | Proposition::CConditionEvaluates { state, .. } => Some(state),
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
    evidence: &[crate::kernel::proof::PersistentSequence<
        crate::kernel::proof::CheckedExecutionEvent,
    >],
) -> bool {
    use crate::kernel::proof::CheckedExecutionEvent;

    fn collect(
        events: &[CheckedExecutionEvent],
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
                | CheckedExecutionEvent::Call(_)
                | CheckedExecutionEvent::Condition(_)
                | CheckedExecutionEvent::ReturnProposition(_)
                | CheckedExecutionEvent::Context(_)
                | CheckedExecutionEvent::StatementEffects(_)
                | CheckedExecutionEvent::AutomaticLifetimeEnd(_)
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
        if !collect(&trace.to_vec(), &mut covered, &mut path_partitions) {
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
        ProofFacts,
    };

    fn case_partition(
        root: &ProofFacts,
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
        let pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let escrow = CResourceFact::own_memory(CMemoryRange::new(
            pointer.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        ));
        let support = ResourceContext::new()
            .unchecked_with_fact(escrow.clone())
            .unique_owned_occurrence_for_fact(&escrow)
            .expect("the test escrow has one backing occurrence")
            .0;
        let ledger = crate::kernel::loans::LoanLedger::new();
        let owner = ledger.fresh_participant().unwrap();
        let opening = ledger.lend(owner, owner, support, escrow).unwrap();
        let ledger = ledger.apply(&opening.transition).unwrap();
        let base = CMemory::new()
            .with_block("arg", 8)
            .store(pointer.clone(), int32(0));
        let later_byte = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(1),
        };
        let changed = base.clone().store(later_byte, int32(1));
        assert!(validate_branch_memory_delta_against_loans(&base, &changed, &ledger).is_err());
        let disjoint = base.clone().store(
            Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Constant(4),
            },
            int32(1),
        );
        assert!(validate_branch_memory_delta_against_loans(&base, &disjoint, &ledger).is_ok());
    }

    #[test]
    fn entry_representation_rebase_rejects_changed_loan_authority() {
        let function = c_function(
            CType::Void,
            "loan_entry_rebase",
            Vec::new(),
            CStatement::Return(CExpression::Value(CValue::Void)),
        );
        let ledger = crate::kernel::loans::LoanLedger::new();
        let first_holder = ledger.fresh_participant().unwrap();
        let second_holder = ledger.fresh_participant().unwrap();
        let first = CState::new()
            .with_loan_ledger(Some(ledger.clone()))
            .with_loan_participant(Some(first_holder));
        let second = CState::new()
            .with_loan_ledger(Some(ledger))
            .with_loan_participant(Some(second_holder));
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
        let root = ProofFacts::default();
        let (partition, then_fact, else_fact) = case_partition(&root);
        let mut then_core =
            ExecutionProofCore::at_entry(CState::new(), ExecutionFrontier::default());
        assert!(then_core.record_proof_case_arm(
            partition.clone(),
            0,
            root.with_fact(then_fact.clone())
        ));
        let mut else_core =
            ExecutionProofCore::at_entry(CState::new(), ExecutionFrontier::default());
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
        root: &ProofFacts,
        partition: &Arc<CheckedProofCasePartition>,
        case_facts: [&Proposition; 2],
        shared: &Proposition,
    ) -> (ExecutionProofCore, [(ExecutionProofCore, ProofFacts); 2]) {
        let parent = ExecutionProofCore::at_entry(CState::new(), ExecutionFrontier::default());
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

    fn join_test_function() -> CFunction {
        c_function(
            CType::Int32,
            "joined",
            Vec::new(),
            c_return(c_int32_literal(0)),
        )
    }

    #[test]
    fn case_join_rejoins_the_arms_with_only_the_facts_they_share() {
        let root = ProofFacts::default();
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
        let refused = |successor: ProofFacts| {
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
        let root = ProofFacts::default();
        let (partition, then_fact, else_fact) = case_partition(&root);
        let shared = Proposition::Predicate {
            name: "shared".to_string(),
            arguments: Vec::new(),
        };
        let (parent, [(then_core, then_facts), (else_core, else_facts)]) =
            joinable_arms(&root, &partition, [&then_fact, &else_fact], &shared);
        let function = join_test_function();
        let refused = |arms: &[(&ExecutionProofCore, &ProofFacts)]| {
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
        let root = ProofFacts::default();
        let (partition, then_fact, else_fact) = case_partition(&root);
        let mut then_core =
            ExecutionProofCore::at_entry(CState::new(), ExecutionFrontier::default());
        assert!(then_core.record_proof_case_arm(partition.clone(), 0, root.with_fact(then_fact)));
        // Only the `then` case has a path.
        assert!(!proof_case_partitions_are_exhaustive(&[then_core
            .execution_evidence[0]
            .clone()]));
        let mut else_core =
            ExecutionProofCore::at_entry(CState::new(), ExecutionFrontier::default());
        assert!(else_core.record_proof_case_arm(partition, 1, root.with_fact(else_fact)));
        assert!(proof_case_partitions_are_exhaustive(&[
            then_core.execution_evidence[0].clone(),
            else_core.execution_evidence[0].clone(),
        ]));
    }

    #[test]
    fn outcome_evidence_fork_splits_traces_in_candidate_order() {
        let root = ProofFacts::default();
        let (partition, then_fact, else_fact) = case_partition(&root);
        let mut core = ExecutionProofCore::at_entry(CState::new(), ExecutionFrontier::default());
        // Two candidate paths with one trace each; the second is forked.
        let function = c_function(
            CType::Int32,
            "fork",
            Vec::new(),
            c_return(c_int32_literal(0)),
        );
        let entry_state =
            c_function_entry_state(&CState::new(), &function, &[]).expect("entry state");
        let skip_return = |value: u32| {
            Theorem::new(Proposition::CStatementVerifies {
                state: Box::new(entry_state.clone()),
                statement: Box::new(CStatement::Skip),
                outcome: CStatementOutcome::Return {
                    value: int32(value),
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
                OutcomeEvidenceFork::Split {
                    partition: partition.clone(),
                    arm_facts: [
                        root.with_fact(else_fact.clone()),
                        root.with_fact(then_fact.clone())
                    ],
                },
            ])
            .is_err()
        );
        core.fork_outcome_evidence(&[
            OutcomeEvidenceFork::Keep,
            OutcomeEvidenceFork::Split {
                partition: partition.clone(),
                arm_facts: [root.with_fact(then_fact), root.with_fact(else_fact)],
            },
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
        let root = ProofFacts::default();
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
        let plan = |corrupt| OutcomeEvidenceFork::NestedSplit {
            partition: outer.clone(),
            arm_facts: outer_facts.clone(),
            arms: [
                Box::new(OutcomeEvidenceFork::Split {
                    partition: inner.clone(),
                    arm_facts: if corrupt {
                        [inner_facts[1].clone(), inner_facts[0].clone()]
                    } else {
                        inner_facts.clone()
                    },
                }),
                Box::new(OutcomeEvidenceFork::Keep),
            ],
        };
        let mut core = ExecutionProofCore::at_entry(CState::new(), ExecutionFrontier::default());
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
    if !assumptions.proves_exact(&conclusion) {
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
    let Proposition::ConditionIs(ConditionTerm::Bitvector32SignedAddOverflows(left, right), false) =
        goal
    else {
        return false;
    };
    let (a, b, c) = match (left.as_ref(), right.as_ref()) {
        (a, Bitvector32Term::Add(b, c)) | (Bitvector32Term::Add(b, c), a) => {
            (a, b.as_ref(), c.as_ref())
        }
        _ => return false,
    };
    [
        ConditionTerm::signed_add_overflows(a.clone(), b.clone()),
        ConditionTerm::signed_add_overflows(Bitvector32Term::add(a.clone(), b.clone()), c.clone()),
        ConditionTerm::signed_add_overflows(b.clone(), c.clone()),
    ]
    .iter()
    .all(|condition| {
        PureFactContext::settles_exactly(
            assumptions,
            &Proposition::ConditionIs(condition.clone(), false),
        ) || PureFactContext::settles_exactly(
            assumptions,
            &Proposition::ConditionIs(
                match condition {
                    ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
                        ConditionTerm::signed_add_overflows(
                            right.as_ref().clone(),
                            left.as_ref().clone(),
                        )
                    }
                    _ => unreachable!(),
                },
                false,
            ),
        )
    })
}

/// Reconstruct a count bound checked against this state's immutable ledger and
/// exact custody. Retained observations must bind the result to this state;
/// this does not return an unconditional arithmetic theorem.
pub fn checked_owned_resource_count_lower_bound(
    state: &CState,
    owned: &CResourceFact,
    assumptions: &PureFactContext,
) -> Option<Proposition> {
    if !state.resources().satisfies_fact(owned, assumptions) {
        return None;
    }
    let quantity = owned.owned_quantity_term()?.clone();
    let (name, arguments) = match owned.resource() {
        CResource::Composite { name, arguments } | CResource::Token { name, arguments } => {
            (name, arguments)
        }
        CResource::Memory(_)
        | CResource::PopulationAuthority(_)
        | CResource::Instance(_)
        | CResource::MutexGuard(_)
        | CResource::MutexLive(_)
        | CResource::MutexUse(_)
        | CResource::Publication(_)
        | CResource::Iterated(_) => return None,
    };
    let mut checked_facts = assumptions.clone();
    let count = {
        let arguments = arguments
            .iter()
            .map(|argument| match argument {
                AlgebraicValue::C(value) => Some(Some(SpecExpression::Value(value.clone()))),
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
        let CValue::Int32(value) = &path.value else {
            return None;
        };
        value.clone()
    };
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(quantity.clone(), count.clone()),
        true,
    );
    {
        let reversed =
            Proposition::ConditionIs(ConditionTerm::signed_greater_equal(count, quantity), true);
        if !PureFactContext::settles_exactly(&checked_facts, &conclusion)
            && !checked_facts.proves_exact(&reversed)
        {
            return None;
        }
    }
    Some(conclusion)
}

/// Certifies the nonnegativity invariant carried by an owned declared-resource
/// coefficient in a concrete ghost state.
pub fn prove_owned_resource_quantity_nonnegative(
    state: &CState,
    owned: &CResourceFact,
    claimed: &Proposition,
    assumptions: &PureFactContext,
) -> Option<Theorem> {
    if !state.resources().satisfies_fact(owned, assumptions) {
        return None;
    }
    let quantity = owned.owned_quantity_term()?.clone();
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), quantity),
        true,
    );
    if claimed != &conclusion {
        return None;
    }
    theorem_from_exact_context_fact(assumptions, conclusion)
}

/// Re-expresses a checked execution from a definitionally equal ghost-resource
/// representation of the same concrete entry state.
///
/// Resource folds, unfolds, and observations can leave the proof state with a
/// different `ResourceContext` than independently reconstructed contract
/// entry. The program locals, memory, and counted populations must still be
/// exactly identical, and the kernel's bounded resource equality relation
/// must prove the two ghost representations equivalent before any execution
/// theorem is rebuilt at the contract entry state.
/// A short, dump-free description of an artifact premise for a certification
/// diagnostic.
fn describe_contract_reuse_premise(premise: &Proposition) -> String {
    fn resource_name(resource: &CResource) -> &str {
        match resource {
            CResource::Composite { name, .. } | CResource::Token { name, .. } => name,
            CResource::Memory(_) => "memory",
            CResource::PopulationAuthority(_) => "population authority",
            CResource::MutexGuard(_) => "mutex guard",
            CResource::MutexLive(_) => "mutex lifetime",
            CResource::MutexUse(_) => "mutex use",
            CResource::Publication(_) => "publication right",
            CResource::Instance(instance) => instance.name(),
            CResource::Iterated(iterated) => iterated.owner(),
        }
    }
    match premise {
        Proposition::Predicate { name, .. } => format!("the predicate identity `{name}`"),
        Proposition::CResourceContains { parent, .. } => {
            format!(
                "a containment fact under resource `{}`",
                resource_name(parent)
            )
        }
        Proposition::CResourceSeparate { left, right } => format!(
            "a separation fact between `{}` and `{}`",
            resource_name(left),
            resource_name(right)
        ),
        Proposition::ConditionIs(..) | Proposition::Not(_) => "a condition fact".to_string(),
        _ => "a pure fact".to_string(),
    }
}

fn checked_execution_at_definitionally_equal_entry_state(
    checked: &CCheckedFunctionExecution,
    state: &CState,
    function: &CFunction,
    assumptions: &PureFactContext,
) -> Option<SymbolicCExecution> {
    // An artifact completed through a kernel-issued `CheckedFunctionEntry`
    // records the contract caller state it was tied to, and the proof object
    // already checked that its entry representation is definitionally equal
    // to the entry derived from that state. No second equivalence search is
    // needed for it.
    let entry_origin_matches = checked.entry_representation_origin.as_ref() == Some(state);
    if !entry_origin_matches {
        if !loan_authority_states_match(&checked.state, state) {
            return None;
        }
        // Recursive composites can expose an unbounded proof relation between
        // folded and projected entry contexts. Certification must not turn a
        // cache probe into that search: without a kernel-issued entry tying
        // the artifact to this state, decline.
        if function
            .composite_resource_definitions()
            .iter()
            .any(CCompositeResourceDefinition::is_recursive)
        {
            return None;
        }
        let mut checked_without_ghost_difference = checked.state.clone();
        checked_without_ghost_difference.resources = state.resources.clone();
        checked_without_ghost_difference.observed_population_families =
            state.observed_population_families.clone();
        if !checked_without_ghost_difference.equal_up_to_unused_creation_ledgers(state) {
            return None;
        }
        let resources_match = crate::kernel::api::contract_certification::resource_contexts_definitionally_equal_with_definitions(
            function.composite_resource_definitions(),
            checked.state.memory(),
            checked.state.resources(),
            state.memory(),
            state.resources(),
            assumptions,
        );
        let populations_match = population_observations_equal(&checked.state, state);
        if !resources_match || !populations_match {
            return None;
        }
    }

    let mut paths = Vec::with_capacity(checked.execution.paths.len());
    for path in &checked.execution.paths {
        let mut conclusion = path.theorem.proposition();
        while let Proposition::Implies(_, body) = conclusion {
            conclusion = body;
        }
        let proposition = match conclusion {
            Proposition::CFunctionExecutes {
                state: proved_state,
                function: proved_function,
                arguments,
                outcome,
            } if **proved_state == checked.state
                && **proved_function == *function
                && arguments == &checked.arguments =>
            {
                Proposition::CFunctionExecutes {
                    state: Box::new(state.clone()),
                    function: Box::new(function.clone()),
                    arguments: arguments.clone(),
                    outcome: outcome.clone(),
                }
            }
            Proposition::CFunctionVerifies {
                state: proved_state,
                function: proved_function,
                arguments,
                outcome,
            } if **proved_state == checked.state
                && **proved_function == *function
                && arguments == &checked.arguments =>
            {
                Proposition::CFunctionVerifies {
                    state: Box::new(state.clone()),
                    function: Box::new(function.clone()),
                    arguments: arguments.clone(),
                    outcome: outcome.clone(),
                }
            }
            _ => return None,
        };
        paths.push(SymbolicCExecutionPath {
            completion_origin: None,
            assumptions: path.assumptions.clone(),
            post_assumptions: path.post_assumptions.clone(),
            facts: path.facts.clone(),
            effect_facts: path.effect_facts.clone(),
            obligations: path.obligations.clone(),
            theorem: Theorem::new(wrap_proof_facts(
                proposition,
                &path.assumptions,
                &path.facts,
                &path.obligations,
            )),
            loan_evidence: path.loan_evidence.clone(),
        });
    }
    Some(SymbolicCExecution { paths, limit: None })
}

/// Whether every stable-view binding a state publishes is authorized by the
/// authority that same state carries.
///
/// A state holding a ledger must have each binding authorized by it under the
/// state's own holder. A state holding no ledger carries no authority to root
/// a binding in, so the only authorized population there is the empty one --
/// which is exactly what a modular proof that never lent anything reaches.
/// Treating that pristine case as unauthorized, or treating a ledger-less
/// state as vacuously authorized, are the two ways to get this wrong.
fn state_loan_bindings_are_authorized(state: &CState, assumptions: &PureFactContext) -> bool {
    match (state.loan_ledger(), state.loan_participant()) {
        (Some(ledger), Some(participant)) => {
            ledger.authorizes_bindings(participant, state.loan_view_bindings(), assumptions)
        }
        (None, None) => state.loan_view_bindings().iter().next().is_none(),
        _ => false,
    }
}

fn checked_loan_evidence_is_valid(
    checked: &CCheckedFunctionExecution,
    function: &CFunction,
) -> bool {
    if !function
        .resource_requires()
        .iter()
        .any(CResourceSpec::is_view)
    {
        return true;
    }
    let (caller_ledger, caller_participant, pristine_start) = match (
        checked.state.loan_ledger(),
        checked.state.loan_participant(),
    ) {
        (Some(ledger), Some(participant)) => (Some(ledger), Some(participant), false),
        (None, None) => (None, None, true),
        _ => return false,
    };
    let thread_recovered = |return_state: &CState| match (
        checked.state.loan_ledger(),
        checked.state.loan_participant(),
        return_state.loan_ledger(),
        return_state.thread_ledger.as_ref(),
    ) {
        (Some(origin), Some(participant), Some(current), Some(threads)) => {
            threads.witnesses_loan_recovery(origin, current, participant)
        }
        _ => false,
    };
    checked.execution.paths.iter().all(|path| {
        let Some(outcome) = path_function_outcome(path) else {
            return false;
        };
        let publishes_exit_state = matches!(
            outcome,
            CFunctionOutcome::Return { .. } | CFunctionOutcome::Throw { .. }
        );
        if path.loan_evidence.is_empty() {
            return match outcome {
                CFunctionOutcome::Return {
                    state: return_state,
                    ..
                }
                | CFunctionOutcome::Throw {
                    state: return_state,
                    ..
                } => {
                    (checked.state.loan_ledger() == return_state.loan_ledger()
                        || thread_recovered(return_state))
                        && checked.state.loan_participant() == return_state.loan_participant()
                        && return_state.loan_bindings_are_consistent()
                        && checked.state.loan_bindings_are_consistent()
                        && state_loan_bindings_are_authorized(return_state, &checked.assumptions)
                }
                _ => !publishes_exit_state,
            };
        }
        if !path.loan_evidence.is_valid() {
            return false;
        }
        let (outer_recovered_ledger, outer_recovered_participant) =
            match (caller_ledger, caller_participant) {
                (Some(caller_ledger), Some(caller_participant)) => (
                    path.loan_evidence.recovered_ledger_for(
                        caller_ledger,
                        caller_participant,
                        false,
                    ),
                    Some(caller_participant),
                ),
                (None, None) if pristine_start => {
                    // The pristine root has no state identity to use as an
                    // index key.  The sequence keeps the last pristine-root
                    // recovery as a bounded summary instead.
                    let (participant, recovered) = path.loan_evidence.pristine_recovery();
                    (recovered, participant)
                }
                _ => (None, None),
            };
        let return_state = match outcome {
            CFunctionOutcome::Return { state, .. } | CFunctionOutcome::Throw { state, .. } => state,
            _ => return true,
        };
        (return_state.loan_ledger() == outer_recovered_ledger.as_ref()
            || thread_recovered(return_state))
            && return_state.loan_participant() == outer_recovered_participant
            && return_state.loan_bindings_are_consistent()
            && checked.state.loan_bindings_are_consistent()
            && state_loan_bindings_are_authorized(return_state, &checked.assumptions)
    })
}

#[cfg(test)]
mod loan_authorization_tests {
    use super::*;

    #[test]
    fn a_pristine_return_state_is_authorized_and_a_rootless_binding_is_not() {
        let assumptions = PureFactContext::new();
        // A modular proof that never lent anything returns with no ledger and
        // no binding. That is authorized: there is nothing to authorize.
        assert!(state_loan_bindings_are_authorized(
            &CState::new(),
            &assumptions
        ));

        let support_fact = CResourceFact::own_token("authorization_support".into(), Vec::new());
        // The binding's viewed fact must be a view the loan actually permits,
        // which is the view form of the escrowed resource.
        let viewed = CResourceFact::view_token("authorization_support".into(), Vec::new());
        let resources =
            ResourceContext::new().unchecked_with_facts([support_fact.clone(), viewed.clone()]);
        let support = resources.owned_occurrences_for_fact(&support_fact)[0];
        let occurrence = resources.occurrences_for_fact(&viewed)[0];
        let ledger = crate::kernel::loans::LoanLedger::new();
        let owner = ledger.fresh_participant().expect("owner identity");
        let reader = ledger.fresh_participant().expect("reader identity");
        let opening = ledger
            .lend(owner, reader, support, support_fact)
            .expect("the view is backed by a fresh loan");
        let binding = crate::kernel::loans::LoanViewBinding {
            loan: opening.loan,
            scope: opening.scope,
            share: opening.root_share,
            support,
            viewed,
            hold: None,
        };
        let lent = ledger
            .apply(&opening.transition)
            .expect("the opening applies to its own predecessor");

        let authorized = CState::new()
            .with_loan_ledger(Some(lent))
            .with_loan_participant(Some(reader))
            .with_resource_context_and_loan_dependencies(
                resources.clone(),
                [(occurrence, binding.clone())],
            );
        assert!(state_loan_bindings_are_authorized(
            &authorized,
            &assumptions
        ));

        // The same binding with the ledger taken away has no authority behind
        // it, and a ledger-less state must not be vacuously authorized.
        let rootless = CState::new()
            .with_resource_context_and_loan_dependencies(resources, [(occurrence, binding)]);
        assert!(!state_loan_bindings_are_authorized(&rootless, &assumptions));

        // A holder the ledger does not know is not an authority either.
        let unheld = authorized.clone().with_loan_participant(None);
        assert!(!state_loan_bindings_are_authorized(&unheld, &assumptions));
    }
}

fn path_function_outcome(path: &SymbolicCExecutionPath) -> Option<&CFunctionOutcome> {
    let mut proposition = path.theorem.proposition();
    while let Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    match proposition {
        Proposition::CFunctionExecutes { outcome, .. }
        | Proposition::CFunctionVerifies { outcome, .. } => Some(outcome),
        _ => None,
    }
}

/// Whether two states agree on population body access and on the families
/// they have observed.
pub(crate) fn population_observations_equal(left: &CState, right: &CState) -> bool {
    left.population_access == right.population_access
        && left.observed_population_families == right.observed_population_families
}

/// Certifies an opaque contract from kernel-checked whole-function
/// executions: an artifact is reused when its retained authority is implied
/// by the exact contract entry. Certification never executes the body
/// itself; with no reusable artifact it produces no paths and the reason.
///
/// `state` and `arguments` specify the entry being checked. This operation
/// does not generate generic inputs from the source signature. Callers that
/// intend to package reusable function rules must supply an entry representing
/// the declared input domain, as Surface's `initial_call_state` does. See
/// `docs/internals/kernel.md`, "Source obligations and checked evidence".
#[allow(clippy::too_many_arguments)]
pub fn prove_c_function_contract_execution_paths_with_checked_artifacts(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    mode: CFunctionContractExecutionMode,
    checked_artifacts: &[CCheckedFunctionExecution],
) -> CFunctionContractExecution {
    prove_c_function_contract_execution_paths_with_checked_artifacts_and_pure_theorems(
        state,
        function,
        arguments,
        environment,
        execution_semantics,
        mode,
        checked_artifacts,
        &[],
    )
}

/// Certifies an opaque contract with kernel-issued pure theorem authorities.
/// The entry-construction responsibility is the same as for
/// [`prove_c_function_contract_execution_paths_with_checked_artifacts`].
#[allow(clippy::too_many_arguments)]
pub fn prove_c_function_contract_execution_paths_with_checked_artifacts_and_pure_theorems(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    mode: CFunctionContractExecutionMode,
    checked_artifacts: &[CCheckedFunctionExecution],
    pure_theorems: &[CVerifiedPureTheorem],
) -> CFunctionContractExecution {
    let environment = if environment.has_conditional_resource_effects()
        || function_has_conditional_resource_effect(&function)
    {
        environment.with_conditional_resource_cases()
    } else {
        environment
    };
    // Certification computes the anchor a second time here; the proof
    // stepped with its own. An artifact whose environment carries no
    // anchor, or a different one, then fails `matches_execution_metadata`
    // below and is not reused: a body stepped without the anchor emitted no
    // descent obligation at its self-calls, and certifying a contract from it
    // would grant a recursive function everything but the descent.
    let environment = match c_execution_environment_with_recursion_anchor(
        environment,
        &function,
        &state,
        &arguments,
    ) {
        Ok(environment) => environment,
        Err(reason) => return CFunctionContractExecution::failed(reason),
    };
    let pure_theorem_facts = pure_theorems
        .iter()
        .map(|verified| verified.theorem.proposition().clone())
        .collect::<Vec<_>>();
    let base_assumptions = match crate::instrumentation::measure_operation(
        function.name(),
        "contract certification",
        "contract assumptions",
        || {
            c_function_contract_entry(&state, &function, &arguments)
                .map(CContractEntry::into_assumptions)
        },
    ) {
        Ok(assumptions) => assumptions,
        Err(reason) => {
            if crate::instrumentation::enabled() {
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::Diagnostic(format!(
                        "exact certification could not construct contract assumptions for {}: {reason}",
                        function.name()
                    )),
                );
            }
            return CFunctionContractExecution::failed(reason);
        }
    };
    let Some(resource_condition_cases) = crate::instrumentation::measure_operation(
        function.name(),
        "contract certification",
        "contract resource guard cases",
        || contract_resource_condition_cases(&state, &function, &arguments, &base_assumptions),
    ) else {
        if crate::instrumentation::enabled() {
            crate::instrumentation::emit(crate::instrumentation::VerificationEvent::Diagnostic(
                format!(
                    "exact certification could not enumerate resource guards for {}",
                    function.name()
                ),
            ));
        }
        return CFunctionContractExecution::failed(
            "could not enumerate the undecided resource guards of the contract entry".to_string(),
        );
    };
    let mut cases = Vec::new();
    let mut reuse_diagnostic = None;
    let mut reuse_unauthorized_premise = None;
    let mut reuse_entry_resources = Vec::new();
    let mut reuse_context_facts = Vec::new();
    for case_facts in resource_condition_cases {
        // A resource-guard case assumes its guards beside the contract entry.
        let assumptions = assumptions_with_propositions(&base_assumptions, &case_facts);
        let Some(mut entry_state) = c_function_entry_state(&state, &function, &arguments) else {
            return CFunctionContractExecution::failed(
                "could not build the contract entry state from the call arguments".to_string(),
            );
        };
        let has_recursive_resources = function
            .composite_resource_definitions()
            .iter()
            .any(CCompositeResourceDefinition::is_recursive);
        // With recursive definitions the caller state already holds the
        // proof-directed projections. Expanding it globally would erase child
        // composites and expose unrelated recursive branches, so it is kept.
        if !has_recursive_resources {
            let Some(entry_resources) = crate::instrumentation::measure_operation(
                function.name(),
                "contract certification",
                "contract entry resource expansion",
                || {
                    {
                        super::functions::expand_all_composite_resource_facts_at_state(
                            entry_state.resources(),
                            function.composite_resource_definitions(),
                            &entry_state,
                            &assumptions,
                        )
                    }
                },
            ) else {
                return CFunctionContractExecution::failed(
                    "could not expand the composite resources of the contract entry state"
                        .to_string(),
                );
            };
            entry_state = entry_state.with_resource_context(entry_resources);
        }
        let matches_execution_metadata_except_state = |checked: &CCheckedFunctionExecution| {
            checked.function == function
                && checked.arguments == arguments
                && checked.environment == environment
                && checked.execution_semantics == execution_semantics
                && checked.mode == mode
                && checked.assumptions.has_same_reasoning_policy(&assumptions)
                && checked.execution.limit().is_none()
                && !checked.execution.paths().is_empty()
                && checked_loan_evidence_is_valid(checked, &function)
        };
        let raw_entry_state = c_function_entry_state(&state, &function, &arguments);
        let mut reuse_assumptions = assumptions.clone();
        // A claim proof opens entry composites and assumes the containment
        // and separation facts of their children. Derive those facts from the
        // kernel definitions at the contract entry state, expanding only the
        // composites some artifact premise names, so the work is bounded by
        // the premises rather than by the resource depth.
        {
            let definitions = function.composite_resource_definitions();
            let mut composites = Vec::new();
            for fact in raw_entry_state
                .iter()
                .flat_map(|raw| raw.resources().facts().iter())
                .chain(entry_state.resources().facts().iter())
            {
                // Containment is definitional: it depends on the composite's
                // body at the entry memory, not on whether the contract owns
                // or views it, so evaluate every composite as owned.
                if matches!(fact.resource(), CResource::Composite { .. }) {
                    let owned = CResourceFact::own(fact.resource().clone());
                    if !composites.contains(&owned) {
                        composites.push(owned);
                    }
                }
            }
            let mut expanded = std::collections::BTreeSet::new();
            loop {
                let named = checked_artifacts
                    .iter()
                    .filter(|checked| matches_execution_metadata_except_state(checked))
                    .flat_map(|checked| checked.assumptions.pure_facts())
                    .filter(|premise| {
                        matches!(
                            premise,
                            Proposition::CResourceContains { .. }
                                | Proposition::CResourceSeparate { .. }
                        ) && !(reuse_assumptions.proves_exact(premise)
                            || reuse_assumptions.states_required_goal(premise))
                    })
                    .flat_map(|premise| match premise {
                        Proposition::CResourceContains { parent, .. } => vec![*parent],
                        Proposition::CResourceSeparate { left, right } => vec![*left, *right],
                        _ => Vec::new(),
                    })
                    .filter(|resource| {
                        matches!(resource, CResource::Composite { .. })
                            && !expanded.contains(resource)
                    })
                    .collect::<std::collections::BTreeSet<_>>();
                let wanted = named
                    .into_iter()
                    .filter_map(|resource| {
                        composites
                            .iter()
                            .find(|fact| fact.resource() == &resource)
                            .cloned()
                    })
                    .collect::<Vec<_>>();
                if wanted.is_empty() {
                    break;
                }
                for composite in wanted {
                    expanded.insert(composite.resource().clone());
                    let Some(propositions) =
                        crate::kernel::functions::evaluate_composite_resource_relation_propositions(
                            &composite,
                            definitions,
                            entry_state.memory(),
                            &reuse_assumptions,
                        )
                    else {
                        continue;
                    };
                    for proposition in propositions {
                        if let Proposition::CResourceContains { child, .. } = &proposition
                            && matches!(&**child, CResource::Composite { .. })
                        {
                            composites.push(CResourceFact::own(*child.clone()));
                        }
                        reuse_assumptions = reuse_assumptions.assume_proposition(proposition);
                    }
                }
            }
        }
        // A proof that observes a viewed child of an entry composite loads
        // that child's cells. The entry holds them through the folded child,
        // so a loadability premise the entry as given does not certify is
        // retried against the entry's composites opened level by level, as
        // deep as the entry facts decide. The levels are built only when such
        // a premise appears, once per certification.
        let opened_entry_levels = std::cell::OnceCell::<Vec<ResourceContext>>::new();
        let opened_entry_levels = || {
            opened_entry_levels.get_or_init(|| {
                let mut levels = Vec::new();
                let mut current = entry_state.resources().clone();
                while let Some(next) =
                    super::functions::expand_all_composite_resource_facts_at_state(
                        &current,
                        function.composite_resource_definitions(),
                        &entry_state,
                        &reuse_assumptions,
                    )
                {
                    if next == current {
                        break;
                    }
                    levels.push(next.clone());
                    current = next;
                }
                levels
            })
        };
        let checked_premise_is_authorized =
            |_checked: &CCheckedFunctionExecution, premise: &Proposition| {
                reuse_assumptions.proves_exact(premise)
                    || reuse_assumptions.states_required_goal(premise)
                    || matches!(premise, Proposition::CMemoryLoadable { .. })
                        && (resources_certify_loadability(
                            &entry_state,
                            entry_state.resources(),
                            premise,
                            &reuse_assumptions,
                        ) || opened_entry_levels().iter().any(|resources| {
                            resources_certify_loadability(
                                &entry_state,
                                resources,
                                premise,
                                &reuse_assumptions,
                            )
                        }))
            };
        let authorized = |checked: &CCheckedFunctionExecution| {
            checked
                .assumptions
                .pure_facts()
                .into_iter()
                .all(|premise| checked_premise_is_authorized(checked, &premise))
        };
        let candidates = checked_artifacts
            .iter()
            .filter(|checked| matches_execution_metadata_except_state(checked))
            .collect::<Vec<_>>();
        // Every checked execution reusable at this entry is one path set the
        // claims may be judged over. Proofs of one function structure their
        // paths differently (a proof that joins two arms publishes the
        // joined path; another publishes each arm) and may run at different
        // representations of the entry (one observed a resource first), and
        // a claim completed on one proof's outcome is matched against that
        // proof's paths. An artifact at the contract's exact entry state is
        // taken as is; one at another representation is rebased onto this
        // entry, which pays the definitional equivalence check only for it.
        let mut alternatives: Vec<CContractPathSet> = crate::instrumentation::measure_operation(
            function.name(),
            "contract certification",
            "contract checked body reuse",
            || {
                candidates
                    .iter()
                    .filter(|checked| checked.state == state && authorized(checked))
                    .map(|checked| CContractPathSet {
                        boundary_transfers: vec![
                            checked.boundary_transfer().cloned();
                            checked.execution.paths.len()
                        ],
                        paths: checked.execution.paths.clone(),
                        checked_resource_claims: checked.checked_resource_claims.clone(),
                        checked_resource_transitions: checked.checked_resource_transitions.clone(),
                        deferred_contract_exits: checked.deferred_contract_exits.clone(),
                        deferred_contract_exit_errors: checked
                            .deferred_contract_exit_errors
                            .clone(),
                        checked_returned_resources: checked.checked_returned_resources.clone(),
                        completion_origin_state: Some(checked.state.clone()),
                    })
                    .collect()
            },
        );
        alternatives.extend(crate::instrumentation::measure_operation(
            function.name(),
            "contract certification",
            "contract checked body resource-rebased reuse",
            || {
                candidates
                    .iter()
                    .filter(|checked| checked.state != state && authorized(checked))
                    .filter_map(|checked| {
                        crate::instrumentation::measure_operation(
                            function.name(),
                            "contract certification",
                            "contract checked entry resource equivalence",
                            || {
                                checked_execution_at_definitionally_equal_entry_state(
                                    checked,
                                    &state,
                                    &function,
                                    &assumptions,
                                )
                            },
                        )
                        .map(|execution| CContractPathSet {
                            boundary_transfers: vec![
                                checked.boundary_transfer().cloned();
                                execution.paths.len()
                            ],
                            paths: execution.paths,
                            checked_resource_claims: checked.checked_resource_claims.clone(),
                            checked_resource_transitions: checked
                                .checked_resource_transitions
                                .clone(),
                            deferred_contract_exits: checked.deferred_contract_exits.clone(),
                            deferred_contract_exit_errors: checked
                                .deferred_contract_exit_errors
                                .clone(),
                            checked_returned_resources: checked.checked_returned_resources.clone(),
                            completion_origin_state: Some(checked.state.clone()),
                        })
                    })
                    .collect::<Vec<_>>()
            },
        ));
        if alternatives.is_empty() {
            // Two artifacts whose single unauthorized entry premises are one
            // condition and its negation together cover the entry: their
            // paths form one path set.
            let partition_reuse = || -> Option<CContractPathSet> {
                let partitioned = candidates
                    .iter()
                    .filter_map(|checked| {
                        let mut unproved = checked
                            .assumptions
                            .pure_facts()
                            .into_iter()
                            .filter(|premise| !checked_premise_is_authorized(checked, premise));
                        let premise = unproved.next()?;
                        if unproved.next().is_some() {
                            return None;
                        }
                        let Proposition::ConditionIs(condition, value) = premise else {
                            return None;
                        };
                        Some((*checked, condition, value))
                    })
                    .collect::<Vec<_>>();
                for (left_index, (left, left_condition, left_value)) in
                    partitioned.iter().enumerate()
                {
                    let Some((right, _, _)) = partitioned[left_index + 1..].iter().find(
                        |(_, right_condition, right_value)| {
                            right_condition == left_condition && right_value != left_value
                        },
                    ) else {
                        continue;
                    };
                    let origin = (left.state == right.state).then(|| left.state.clone());
                    let mut boundary_transfers =
                        vec![left.boundary_transfer().cloned(); left.execution.paths.len()];
                    boundary_transfers.extend(vec![
                        right.boundary_transfer().cloned();
                        right.execution.paths.len()
                    ]);
                    let left_claims = left.checked_resource_claims.clone();
                    let right_claims = right.checked_resource_claims.clone();
                    let left_transitions = left.checked_resource_transitions.clone();
                    let right_transitions = right.checked_resource_transitions.clone();
                    let left_deferred_contract_exits = left.deferred_contract_exits.clone();
                    let right_deferred_contract_exits = right.deferred_contract_exits.clone();
                    let left_deferred_contract_exit_errors =
                        left.deferred_contract_exit_errors.clone();
                    let right_deferred_contract_exit_errors =
                        right.deferred_contract_exit_errors.clone();
                    let left_checked_returned_resources = left.checked_returned_resources.clone();
                    let right_checked_returned_resources = right.checked_returned_resources.clone();
                    let left = checked_execution_at_definitionally_equal_entry_state(
                        left,
                        &state,
                        &function,
                        &assumptions,
                    )?;
                    let right = checked_execution_at_definitionally_equal_entry_state(
                        right,
                        &state,
                        &function,
                        &assumptions,
                    )?;
                    let mut paths = left.paths;
                    paths.extend(right.paths);
                    let mut checked_resource_claims = left_claims;
                    checked_resource_claims.extend(right_claims);
                    let mut checked_resource_transitions = left_transitions;
                    checked_resource_transitions.extend(right_transitions);
                    let mut deferred_contract_exits = left_deferred_contract_exits;
                    deferred_contract_exits.extend(right_deferred_contract_exits);
                    let mut deferred_contract_exit_errors = left_deferred_contract_exit_errors;
                    deferred_contract_exit_errors.extend(right_deferred_contract_exit_errors);
                    let mut checked_returned_resources = left_checked_returned_resources;
                    checked_returned_resources.extend(right_checked_returned_resources);
                    return Some(CContractPathSet {
                        paths,
                        checked_resource_claims,
                        checked_resource_transitions,
                        deferred_contract_exits,
                        deferred_contract_exit_errors,
                        checked_returned_resources,
                        boundary_transfers,
                        completion_origin_state: origin,
                    });
                }
                None
            };
            alternatives.extend(crate::instrumentation::measure_operation(
                function.name(),
                "contract certification",
                "contract checked body partition reuse",
                partition_reuse,
            ));
        }
        let reused = !alternatives.is_empty();
        if !reused {
            // Certification never executes the body: reuse either applies
            // or the caller gets no paths and the reason.
            let mut cause = ArtifactReuseRejection::NoMatchingArtifact;
            let mut detail = format!(
                "no checked execution of `{}` matched the contract's execution mode",
                function.name()
            );
            for checked in &candidates {
                if checked.state != state {
                    if cause == ArtifactReuseRejection::NoMatchingArtifact {
                        cause = ArtifactReuseRejection::EntryStateDelta;
                        detail = format!(
                            "the checked execution of `{}` started at a different entry state than the contract and could not be rebased onto it",
                            function.name()
                        );
                    }
                    continue;
                }
                let unauthorized = checked
                    .assumptions
                    .pure_facts()
                    .into_iter()
                    .find(|premise| !checked_premise_is_authorized(checked, premise));
                cause = match &unauthorized {
                    Some(Proposition::Predicate { .. }) => {
                        ArtifactReuseRejection::UnauthorizedPredicatePremise
                    }
                    Some(
                        Proposition::CResourceContains { .. }
                        | Proposition::CResourceSeparate { .. },
                    ) => ArtifactReuseRejection::UnauthorizedResourcePremise,
                    Some(_) | None => ArtifactReuseRejection::UnauthorizedPremise,
                };
                detail = match &unauthorized {
                    Some(premise) => format!(
                        "the checked execution of `{}` assumed {} at entry, which the contract context cannot derive",
                        function.name(),
                        describe_contract_reuse_premise(premise)
                    ),
                    None => format!(
                        "the checked execution of `{}` could not be reused at the contract entry",
                        function.name()
                    ),
                };
                if unauthorized.is_some() {
                    reuse_entry_resources = entry_state.resources().facts().to_vec();
                    reuse_context_facts = reuse_assumptions.pure_facts();
                }
                reuse_unauthorized_premise = unauthorized;
                break;
            }
            crate::instrumentation::record_artifact_reuse_rejection(cause);
            crate::instrumentation::measure_operation(
                function.name(),
                "contract certification",
                "contract artifact reuse rejected",
                || (),
            );
            reuse_diagnostic = Some(detail);
        }
        for set in &mut alternatives {
            // A reused path carries the proof's own entry premises. Every one
            // of them was just authorized from the reconstructed contract
            // context, so the context itself, with the predicate identities
            // and relation facts derived above, is a sound entry context for
            // the path and is what claim certification needs to see:
            // requirement bodies and derived entry facts the proof never
            // spelled out.
            if reused {
                for path in &mut set.paths {
                    let entry_premises = path.assumptions.pure_facts();
                    path.facts
                        .retain(|fact| !entry_premises.contains(fact.proposition()));
                    path.assumptions = reuse_assumptions.clone();
                }
            }
            for path in &mut set.paths {
                let mut certification_assumptions = path.assumptions.clone();
                for obligation in &path.obligations {
                    let Proposition::ConditionIs(condition, value) = obligation.proposition()
                    else {
                        continue;
                    };
                    if certification_assumptions.proves_exact(obligation.proposition())
                        || pure_theorem_facts.iter().any(|fact| {
                            certification_proves_condition_from_verified_pure_implication(
                                &certification_assumptions,
                                fact,
                                condition,
                                *value,
                            )
                        })
                    {
                        certification_assumptions = certification_assumptions
                            .assume_proposition(obligation.proposition().clone());
                    }
                }
                path.assumptions = certification_assumptions;
            }
        }
        cases.push(alternatives);
    }
    let mut checked_call_events = crate::kernel::proof::CheckedCallEvents::default();
    let mut applied_tactics = std::collections::BTreeSet::new();
    for artifact in checked_artifacts {
        checked_call_events.extend(&artifact.checked_call_events);
        applied_tactics.extend(artifact.applied_tactics.iter().cloned());
    }
    CFunctionContractExecution {
        cases,
        reuse_diagnostic,
        reuse_unauthorized_premise,
        reuse_entry_resources,
        reuse_context_facts,
        checked_call_events,
        loop_semantics: execution_semantics.loops,
        applied_tactics,
        checked_callees: super::termination::merge_checked_callees(
            checked_artifacts
                .iter()
                .map(|artifact| artifact.checked_callees.as_ref()),
        ),
    }
}

pub fn prove_c_function_satisfies_specification(
    function: CFunction,
    specification: CFunctionSpecification,
    assumptions: PureFactContext,
) -> Option<Theorem> {
    prove_c_function_satisfies_specification_with_environment(
        function,
        specification,
        assumptions,
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
    )
}

pub fn prove_c_function_satisfies_specification_with_environment(
    function: CFunction,
    specification: CFunctionSpecification,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> Option<Theorem> {
    let specification_assumptions =
        assumptions_with_propositions(&assumptions, specification.requires());
    let paths = execute_c_function_paths(
        specification.state(),
        &function,
        specification.arguments(),
        &specification_assumptions,
        &environment,
        execution_semantics,
        &mut ExecutionBudget::for_new_execution(),
    )
    .ok()?;
    let mut paths = paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some()
        || path.facts.iter().any(ExecutionPureFact::is_public)
        || !path.obligations.is_empty()
        || &path.outcome != specification.outcome()
    {
        return None;
    }

    let requires = specification.requires().to_vec();
    let proposition = requires.iter().rev().fold(
        Proposition::CFunctionSatisfiesSpecification {
            function: Box::new(function),
            specification: Box::new(specification),
        },
        |body, requirement| Proposition::Implies(Box::new(requirement.clone()), Box::new(body)),
    );
    Some(Theorem::new(wrap_proof_facts(
        proposition,
        &assumptions,
        &[],
        &[],
    )))
}

pub fn prove_c_max_lt_returns_right(a: Variable, b: Variable) -> Option<Theorem> {
    let a_bits = Bitvector32Term::Variable(a);
    let b_bits = Bitvector32Term::Variable(b);
    let a_value = int32(a_bits.clone());
    let b_value = int32(b_bits.clone());
    let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());
    let state = c_max_state(a_value, b_value.clone());
    let assumptions = PureFactContext::new().assume_condition(condition.clone(), true);
    let outcome = execute_c_statement(&state, &c_max_body(), &assumptions)?;

    if outcome
        != (CStatementOutcome::Return {
            value: b_value,
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
                Box::new(Proposition::ConditionIs(condition, true)),
                Box::new(Proposition::CStatementExecutes {
                    state: Box::new(state),
                    statement: Box::new(c_max_body()),
                    outcome,
                }),
            ),
        ),
    )))
}

pub fn prove_c_max_not_lt_returns_left(a: Variable, b: Variable) -> Option<Theorem> {
    let a_bits = Bitvector32Term::Variable(a);
    let b_bits = Bitvector32Term::Variable(b);
    let a_value = int32(a_bits.clone());
    let b_value = int32(b_bits.clone());
    let condition = c_max_lt_condition(a_bits, b_bits);
    let state = c_max_state(a_value.clone(), b_value);
    let assumptions = PureFactContext::new().assume_condition(condition.clone(), false);
    let outcome = execute_c_statement(&state, &c_max_body(), &assumptions)?;

    if outcome
        != (CStatementOutcome::Return {
            value: a_value,
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
                Box::new(Proposition::ConditionIs(condition, false)),
                Box::new(Proposition::CStatementExecutes {
                    state: Box::new(state),
                    statement: Box::new(c_max_body()),
                    outcome,
                }),
            ),
        ),
    )))
}

/// Signed int32 increment preserves a strict upper bound as a non-strict
/// bound. The strict premise also rules out signed overflow: if `value` were
/// `INT_MAX`, no int32 `upper` could be greater than it.
pub fn prove_int32_increment_upper_bound(
    value: Bitvector32Term,
    upper: Bitvector32Term,
) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(value.clone(), upper.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            Bitvector32Term::add(value, Bitvector32Term::Constant(1)),
            upper,
        ),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// A signed int32 increment is strictly greater than its input when a strict
/// upper bound rules out overflow.
pub fn prove_int32_increment_strictly_increases(
    value: Bitvector32Term,
    upper: Bitvector32Term,
) -> Theorem {
    let premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(value.clone(), upper), true);
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(
            value.clone(),
            Bitvector32Term::add(value, Bitvector32Term::Constant(1)),
        ),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// Signed int32 increment preserves a non-strict lower bound when a strict
/// upper bound rules out signed overflow.
pub fn prove_int32_increment_lower_bound(
    value: Bitvector32Term,
    lower: Bitvector32Term,
    upper: Bitvector32Term,
) -> Theorem {
    let lower_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(lower.clone(), value.clone()),
        true,
    );
    let upper_premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(value.clone(), upper), true);
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            lower,
            Bitvector32Term::add(value, Bitvector32Term::Constant(1)),
        ),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(lower_premise),
        Box::new(Proposition::Implies(
            Box::new(upper_premise),
            Box::new(conclusion),
        )),
    ))
}

/// Increment preserves a signed lower bound, in greater-equal surface order.
pub fn prove_int32_increment_greater_equal_lower_bound(
    value: Bitvector32Term,
    lower: Bitvector32Term,
    upper: Bitvector32Term,
) -> Theorem {
    let lower_premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(value.clone(), lower.clone()),
        true,
    );
    let upper_premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(value.clone(), upper), true);
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(
            Bitvector32Term::add(value, Bitvector32Term::Constant(1)),
            lower,
        ),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(lower_premise),
        Box::new(Proposition::Implies(
            Box::new(upper_premise),
            Box::new(conclusion),
        )),
    ))
}

/// Increment makes a nonnegative signed gap strictly positive.
pub fn prove_int32_increment_strict_greater_lower_bound(
    value: Bitvector32Term,
    lower: Bitvector32Term,
    upper: Bitvector32Term,
) -> Theorem {
    let lower_premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(value.clone(), lower.clone()),
        true,
    );
    let upper_premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(value.clone(), upper), true);
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(
            Bitvector32Term::add(value, Bitvector32Term::Constant(1)),
            lower,
        ),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(lower_premise),
        Box::new(Proposition::Implies(
            Box::new(upper_premise),
            Box::new(conclusion),
        )),
    ))
}

/// Signed int32 increment preserves non-strict order when a strict upper
/// bound rules out overflow. Since `lower <= value < upper`, neither increment
/// can wrap past `INT_MAX`.
pub fn prove_int32_increment_preserves_order(
    value: Bitvector32Term,
    lower: Bitvector32Term,
    upper: Bitvector32Term,
) -> Theorem {
    let order_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(lower.clone(), value.clone()),
        true,
    );
    let upper_premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(value.clone(), upper), true);
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            Bitvector32Term::add(lower, Bitvector32Term::Constant(1)),
            Bitvector32Term::add(value, Bitvector32Term::Constant(1)),
        ),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(order_premise),
        Box::new(Proposition::Implies(
            Box::new(upper_premise),
            Box::new(conclusion),
        )),
    ))
}

/// A value at least one greater than `lower` is strictly greater than
/// `lower`. The first premise explicitly proves that forming the successor did
/// not wrap in signed int32 arithmetic.
pub fn prove_int32_successor_le_implies_lt(
    lower: Bitvector32Term,
    value: Bitvector32Term,
) -> Theorem {
    let successor = Bitvector32Term::add(lower.clone(), Bitvector32Term::Constant(1));
    let no_overflow_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(lower.clone(), successor.clone()),
        true,
    );
    let bound_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(successor, value.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(ConditionTerm::signed_less_than(lower, value), true);
    Theorem::new(Proposition::Implies(
        Box::new(no_overflow_premise),
        Box::new(Proposition::Implies(
            Box::new(bound_premise),
            Box::new(conclusion),
        )),
    ))
}

/// A signed int32 value strictly below another value's successor is no
/// greater than that value. This remains valid when the successor wraps:
/// then the strict premise is unsatisfiable.
pub fn prove_int32_lt_successor_implies_le(
    value: Bitvector32Term,
    upper: Bitvector32Term,
) -> Theorem {
    let successor = Bitvector32Term::add(upper.clone(), Bitvector32Term::Constant(1));
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(value.clone(), successor),
        true,
    );
    let conclusion = Proposition::ConditionIs(ConditionTerm::signed_less_equal(value, upper), true);
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// Two signed int32 values are equal when the first is no greater than the
/// second and is not strictly less than it.
pub fn prove_int32_le_antisymmetric(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    let le_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
        true,
    );
    let reverse_le_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(right.clone(), left.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(le_premise),
        Box::new(Proposition::Implies(
            Box::new(reverse_le_premise),
            Box::new(conclusion),
        )),
    ))
}

/// A signed int32 value at most another is equal to it when it is not
/// strictly smaller.
pub fn prove_int32_le_and_not_lt_implies_eq(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Theorem {
    let le_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
        true,
    );
    let not_lt_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(left.clone(), right.clone()),
        false,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(le_premise),
        Box::new(Proposition::Implies(
            Box::new(not_lt_premise),
            Box::new(conclusion),
        )),
    ))
}

/// A signed int32 value no greater than another and unequal to it is strictly
/// smaller. The explicit inequality premise keeps this deterministic rule on
/// the simple-certificate surface instead of relying on arithmetic search.
pub fn prove_int32_le_and_neq_implies_lt(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    let le_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
        true,
    );
    let neq_premise = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(left.clone()), Box::new(right.clone())),
        false,
    );
    let conclusion = Proposition::ConditionIs(ConditionTerm::signed_less_than(left, right), true);
    Theorem::new(Proposition::Implies(
        Box::new(le_premise),
        Box::new(Proposition::Implies(
            Box::new(neq_premise),
            Box::new(conclusion),
        )),
    ))
}

/// A signed int32 value at least another is equal to it when it is not
/// strictly greater.
pub fn prove_int32_ge_and_not_gt_implies_eq(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Theorem {
    let ge_premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(left.clone(), right.clone()),
        true,
    );
    let not_gt_premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(left.clone(), right.clone()),
        false,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(ge_premise),
        Box::new(Proposition::Implies(
            Box::new(not_gt_premise),
            Box::new(conclusion),
        )),
    ))
}

/// Any positive signed int32 value is nonnegative.
pub fn prove_int32_positive_is_nonnegative(value: Bitvector32Term) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(0), value.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), value),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// Signed strict order implies signed non-strict order.
pub fn prove_int32_lt_implies_le(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(left.clone(), right.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(ConditionTerm::signed_less_equal(left, right), true);
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// Strict signed int32 order implies disequality.
pub fn prove_int32_lt_implies_neq(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(left.clone(), right.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
        false,
    );
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// The negation of signed strict order implies the reverse non-strict order.
pub fn prove_int32_not_lt_implies_ge(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(left.clone(), right.clone()),
        false,
    );
    let conclusion =
        Proposition::ConditionIs(ConditionTerm::signed_greater_equal(left, right), true);
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
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
        IntegerRangeFoldIndex::Int32 { start, end } => {
            ConditionTerm::signed_less_equal(end.value().clone(), start.value().clone())
        }
        IntegerRangeFoldIndex::UInt64 { start, end } => {
            ConditionTerm::uint64_less_equal(end.value().clone(), start.value().clone())
        }
        IntegerRangeFoldIndex::Integer { start, end } => {
            ConditionTerm::integer_less_equal(end.as_ref().clone(), start.as_ref().clone())
        }
    };
    let fold = IntegerTerm::range_fold(index, initial.clone(), accumulator, item, body);
    Theorem::new(Proposition::Implies(
        Box::new(Proposition::ConditionIs(guard, true)),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(fold.into(), initial.into()),
            true,
        )),
    ))
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
            let original_end = end.value().clone();
            let increment =
                Bitvector32Term::add(original_end.clone(), Bitvector32Term::Constant(1));
            let guard =
                ConditionTerm::signed_less_equal(start.value().clone(), end.value().clone());
            let safe = ConditionTerm::signed_less_than(
                end.value().clone(),
                Bitvector32Term::Constant(i32::MAX as u32),
            );
            let extended = IntegerRangeFoldIndex::Int32 {
                start: start.clone(),
                end: SharedIntegerRangeEndpoint::intern(increment),
            };
            let item_value = IntegerTerm::from_machine(MachineIntegerType::Int32, original_end)?;
            (
                extended,
                Proposition::And(
                    Box::new(Proposition::ConditionIs(guard, true)),
                    Box::new(Proposition::ConditionIs(safe, true)),
                ),
                item_value,
            )
        }
        // The unsigned 64-bit carrier, like the signed one, extends the
        // range only below the type's largest value, where `end + 1` does
        // not wrap.
        IntegerRangeFoldIndex::UInt64 { start, end } => {
            let original_end = end.value().clone();
            let increment = Bitvector32Term::uint64_add(
                original_end.clone(),
                Bitvector32Term::UInt64Constant(1),
            );
            let guard =
                ConditionTerm::uint64_less_equal(start.value().clone(), end.value().clone());
            let safe = ConditionTerm::uint64_less_than(
                end.value().clone(),
                Bitvector32Term::UInt64Constant(u64::MAX),
            );
            let extended = IntegerRangeFoldIndex::UInt64 {
                start: start.clone(),
                end: SharedIntegerRangeEndpoint::intern(increment),
            };
            let item_value = IntegerTerm::from_machine(MachineIntegerType::UInt64, original_end)?;
            (
                extended,
                Proposition::And(
                    Box::new(Proposition::ConditionIs(guard, true)),
                    Box::new(Proposition::ConditionIs(safe, true)),
                ),
                item_value,
            )
        }
        IntegerRangeFoldIndex::Integer { start, end } => {
            let increment = IntegerTerm::add(end.as_ref().clone(), IntegerTerm::constant_i64(1));
            let guard =
                ConditionTerm::integer_less_equal(start.as_ref().clone(), end.as_ref().clone());
            let extended = IntegerRangeFoldIndex::Integer {
                start: start.clone(),
                end: increment.into(),
            };
            (
                extended,
                Proposition::ConditionIs(guard, true),
                end.as_ref().clone(),
            )
        }
    };
    let original_initial = initial.clone();
    let c_item = index.machine_item_type();
    let prior = IntegerTerm::range_fold(index, initial, accumulator, item, body.clone());
    let stepped = crate::kernel::reasoning::instantiate_integer_range_fold_step(
        &body,
        accumulator,
        &prior,
        item,
        &item_value,
        c_item,
    )
    .ok()?;
    let extended_fold =
        IntegerTerm::range_fold(extended, original_initial, accumulator, item, body);
    Some(Theorem::new(Proposition::Implies(
        Box::new(guard),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(extended_fold.into(), stepped.into()),
            true,
        )),
    )))
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
                Bitvector32Term::subtract(end.value().clone(), Bitvector32Term::Constant(1));
            Some((
                IntegerRangeFoldIndex::Int32 {
                    start: start.clone(),
                    end: SharedIntegerRangeEndpoint::intern(predecessor.clone()),
                },
                IntegerTerm::from_machine(MachineIntegerType::Int32, predecessor)?,
            ))
        }
        IntegerRangeFoldIndex::UInt64 { start, end } => {
            let predecessor = Bitvector32Term::uint64_subtract(
                end.value().clone(),
                Bitvector32Term::UInt64Constant(1),
            );
            Some((
                IntegerRangeFoldIndex::UInt64 {
                    start: start.clone(),
                    end: SharedIntegerRangeEndpoint::intern(predecessor.clone()),
                },
                IntegerTerm::from_machine(MachineIntegerType::UInt64, predecessor)?,
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
            IntegerTerm::TruncatingQuotient(left, right) => IntegerTerm::truncating_quotient(
                walk_term(left, from, to, changed, memo).as_ref().clone(),
                walk_term(right, from, to, changed, memo).as_ref().clone(),
            ),
            IntegerTerm::TruncatingRemainder(left, right) => IntegerTerm::truncating_remainder(
                walk_term(left, from, to, changed, memo).as_ref().clone(),
                walk_term(right, from, to, changed, memo).as_ref().clone(),
            ),
            _ => term.as_ref().clone(),
        };
        let result = SharedIntegerTerm::intern(rebuilt);
        memo.insert(term.id(), result.clone());
        result
    }

    fn walk_condition(
        condition: &ConditionTerm,
        from: &SharedIntegerTerm,
        to: &SharedIntegerTerm,
        changed: &mut bool,
        memo: &mut std::collections::HashMap<u64, SharedIntegerTerm>,
    ) -> ConditionTerm {
        let mut rebuild =
            |constructor: fn(SharedIntegerTerm, SharedIntegerTerm) -> ConditionTerm,
             left: &SharedIntegerTerm,
             right: &SharedIntegerTerm,
             changed: &mut bool| {
                constructor(
                    walk_term(left, from, to, changed, memo),
                    walk_term(right, from, to, changed, memo),
                )
            };
        match condition {
            ConditionTerm::IntegerLessThan(left, right) => {
                rebuild(ConditionTerm::IntegerLessThan, left, right, changed)
            }
            ConditionTerm::IntegerLessEqual(left, right) => {
                rebuild(ConditionTerm::IntegerLessEqual, left, right, changed)
            }
            ConditionTerm::IntegerGreaterThan(left, right) => {
                rebuild(ConditionTerm::IntegerGreaterThan, left, right, changed)
            }
            ConditionTerm::IntegerGreaterEqual(left, right) => {
                rebuild(ConditionTerm::IntegerGreaterEqual, left, right, changed)
            }
            ConditionTerm::IntegerEqual(left, right) => {
                rebuild(ConditionTerm::IntegerEqual, left, right, changed)
            }
            ConditionTerm::IntegerNotEqual(left, right) => {
                rebuild(ConditionTerm::IntegerNotEqual, left, right, changed)
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
            Proposition::ConditionIs(condition, expected) => Proposition::ConditionIs(
                walk_condition(condition, from, to, changed, memo),
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

/// The opaque application `f(args)` with the int32 or uint64 argument at `position`
/// replaced by its predecessor, for restating a range fold one endpoint
/// lower. The subtraction is wrapping bitvector arithmetic, matching the
/// endpoint `integer_range_fold_predecessor_index` builds, so the two agree
/// by construction.
pub fn integer_range_fold_predecessor_application(
    whole: &IntegerTerm,
    position: usize,
) -> Option<IntegerTerm> {
    let IntegerTerm::PureFunctionApplication(applied) = whole else {
        return None;
    };
    let mut arguments = applied.arguments().to_vec();
    arguments[position] = match arguments.get(position)? {
        PureFunctionArgument::Value(CValue::Int32(endpoint)) => {
            PureFunctionArgument::Value(CValue::Int32(Bitvector32Term::subtract(
                endpoint.clone(),
                Bitvector32Term::Constant(1),
            )))
        }
        PureFunctionArgument::Value(CValue::UInt64(endpoint)) => {
            PureFunctionArgument::Value(CValue::UInt64(Bitvector32Term::uint64_subtract(
                endpoint.clone(),
                Bitvector32Term::UInt64Constant(1),
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
    let whole_is_fold = Proposition::ConditionIs(
        ConditionTerm::IntegerEqual(whole.clone().into(), fold.clone().into()),
        true,
    );
    let Some(prior) = prior else {
        let empty = prove_integer_range_fold_empty(index, initial.clone(), accumulator, item, body);
        let Proposition::Implies(guard, _) = empty.proposition() else {
            return Err("the Integer fold empty law is not a guarded theorem");
        };
        return Ok(Theorem::new(Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(whole_is_fold),
                Box::new(guard.as_ref().clone()),
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::IntegerEqual(whole.into(), initial.into()),
                true,
            )),
        )));
    };

    let (predecessor_index, item_value) = integer_range_fold_predecessor_index(&index)
        .ok_or("the fold end endpoint has no Integer predecessor in its own carrier")?;
    let c_item = predecessor_index.machine_item_type();
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
    let Proposition::ConditionIs(ConditionTerm::IntegerEqual(extended, _), true) =
        conclusion.as_ref()
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
    let prior_is_fold = Proposition::ConditionIs(
        ConditionTerm::IntegerEqual(prior.clone().into(), prior_fold.into()),
        true,
    );
    let stepped = crate::kernel::reasoning::instantiate_integer_range_fold_step(
        &body,
        accumulator,
        &prior,
        item,
        &item_value,
        c_item,
    )
    .map_err(|_| {
        "the fold body could not take the previous accumulator and the last item; a fold whose item indexes a pure call is not yet supported"
    })?;
    Ok(Theorem::new(Proposition::Implies(
        Box::new(Proposition::And(
            Box::new(Proposition::And(
                Box::new(whole_is_fold),
                Box::new(prior_is_fold),
            )),
            Box::new(guard.as_ref().clone()),
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(whole.into(), stepped.into()),
            true,
        )),
    )))
}

/// Incrementing a signed int32 value below `INT_MAX` is defined.
pub fn prove_int32_increment_below_max_is_defined(value: Bitvector32Term) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(value.clone(), Bitvector32Term::Constant(i32::MAX as u32)),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedAddOverflows(
            Box::new(value),
            Box::new(Bitvector32Term::Constant(1)),
        ),
        false,
    );
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
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
) -> Option<CVerifiedPureTheorem> {
    checked_pure_implication_matches(&requirements, &conclusion, completion)
        .then(|| universally_close_pure_implication(requirements, conclusion, variables))?
}

/// Creates conditional authority for a theorem declaration supplied by an
/// imported module. This is deliberately crate-private: it records an input
/// assumption for contract certification and is never returned as a proved
/// theorem artifact.
pub(crate) fn assume_universally_quantified_pure_implication(
    requirements: Vec<Proposition>,
    conclusion: Proposition,
    variables: Vec<Variable>,
) -> Option<CVerifiedPureTheorem> {
    universally_close_pure_implication(requirements, conclusion, variables)
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
) -> Option<CVerifiedPureTheorem> {
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
    let proposition =
        variables
            .into_iter()
            .rev()
            .fold(implication, |body, var| Proposition::ForAll {
                var,
                sort: Sort::CInt32,
                body: Box::new(body),
            });
    Some(CVerifiedPureTheorem {
        theorem: Theorem::new(proposition),
    })
}

/// Opens one verified concrete target as a local named-contract refinement
/// problem for a pure theorem proof.
///
/// No project search occurs: both names are exact map lookups, and a concrete
/// target must already carry a verified or explicitly external rule.
pub fn c_function_contract_refinement_context(
    environment: &CExecutionEnvironment,
    contract_name: &str,
    target_name: &str,
) -> Option<CFunctionContractRefinementContext> {
    let contract = environment.get_function_contract(contract_name)?;
    let function = if let Some(rule) = environment.get_verified_function_rule(target_name) {
        &rule.function
    } else {
        &environment
            .get_external_function_rule(target_name)?
            .function
    };
    prepare_function_contract_refinement_context(
        contract,
        function,
        &mut ExecutionBudget::for_new_execution(),
    )
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
pub fn c_named_contract_refinement_theorem_skeleton(
    environment: &CExecutionEnvironment,
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
/// exact symbolic function-pointer value.
///
/// Both contract names are exact environment lookups. The source fact remains
/// an explicit premise of the theorem authority issued after refinement; this
/// operation does not infer contracts from a signature or inspect project
/// functions.
pub fn c_contract_refinement_context(
    environment: &CExecutionEnvironment,
    target_contract_name: &str,
    source_contract_name: &str,
    pointer: &CValue,
) -> Option<CFunctionContractRefinementContext> {
    let target = environment.get_function_contract(target_contract_name)?;
    let source = environment.get_function_contract(source_contract_name)?;
    let CValue::Pointer(pointer) = pointer else {
        return None;
    };
    if pointer.c_type() != target.function_pointer_type()
        || pointer.c_type() != source.function_pointer_type()
        || !matches!(pointer.pointer().block, PointerBlock::FunctionSymbolic(_))
        || pointer.pointer().offset != PointerOffsetTerm::Constant(0)
    {
        return None;
    }
    let mut context = super::functions::contract_refinement_context_for_interface(
        target,
        source.name(),
        source.interface(),
        &mut ExecutionBudget::for_new_execution(),
    )?;
    context.pointer = pointer.clone();
    context.source_contract = Some(source.clone());
    Some(context)
}

/// Returns the shared arbitrary argument values introduced by a refinement
/// theorem's `unfold(Contract)` step.
pub fn c_function_contract_refinement_arguments(
    context: &CFunctionContractRefinementContext,
) -> &[CValue] {
    &context.argument_values
}

/// Returns the symbolic entry state used to lower explicit proof conditions.
pub fn c_function_contract_refinement_entry_state(
    context: &CFunctionContractRefinementContext,
) -> CState {
    function_contract_refinement_entry_state(context)
}

pub fn c_function_contract_refinement_obligations(
    context: &CFunctionContractRefinementContext,
) -> Option<CFunctionContractRefinementObligations> {
    prepare_contract_refinement_obligations(context)
}

impl CFunctionContractRefinementObligations {
    pub fn entry(&self) -> &CState {
        &self.entry
    }
    pub fn post(&self) -> &CState {
        &self.post
    }
    pub fn proposition(&self) -> &Proposition {
        &self.proposition
    }
}

/// Issues contract authority only from the exact closed ordinary proof obligation.
pub(crate) fn prove_c_function_contract_refinement(
    context: &CFunctionContractRefinementContext,
    conclusion: Proposition,
    proof: &crate::kernel::proof::CheckedProposition,
) -> Option<CVerifiedPureTheorem> {
    let Proposition::Predicate { name, arguments } = &conclusion else {
        return None;
    };
    let [
        state @ Term::CState(_),
        Term::CValue(CValue::Pointer(pointer)),
    ] = arguments.as_slice()
    else {
        return None;
    };
    if name != &context.contract.predicate_name()
        || pointer != &context.pointer
        || pointer.c_type() != context.contract.function_pointer_type()
    {
        return None;
    }

    let obligations = prepare_contract_refinement_obligations(context)?;
    if !proof.is_closed() || proof.proposition() != &obligations.proposition {
        return None;
    }
    let theorem = match &context.source_contract {
        None => {
            if context.pointer.pointer().block
                != PointerBlock::Function(context.function_name.clone())
            {
                return None;
            }
            conclusion
        }
        Some(source) => {
            let PointerBlock::FunctionSymbolic(variable) = &context.pointer.pointer().block else {
                return None;
            };
            let premise = Proposition::Predicate {
                name: source.predicate_name(),
                arguments: vec![
                    state.clone(),
                    Term::CValue(CValue::Pointer(context.pointer.clone())),
                ],
            };
            Proposition::ForAll {
                var: *variable,
                sort: Sort::CPointer(context.pointer.c_type()),
                body: Box::new(Proposition::Implies(
                    Box::new(premise),
                    Box::new(conclusion),
                )),
            }
        }
    };
    Some(CVerifiedPureTheorem {
        theorem: Theorem::new(theorem),
    })
}

mod contract_interface_identity;

pub(in crate::kernel) fn native_record_refinement_obligations_match(
    left: &CFunctionContractInterface,
    right: &CFunctionContractInterface,
) -> bool {
    contract_interface_identity::same_native_record_obligations(left, right)
}

/// A checked one-call wrapper proves a contract implication. The wrapper's
/// only extra inputs are source contracts for its last, arbitrary callback
/// parameter. Its body must call precisely that parameter with every other
/// parameter in order. No target-contract assumption authorizes this call.
pub(crate) fn prove_executed_contract_refinement(
    environment: &CExecutionEnvironment,
    source_names: &[&str],
    target_name: &str,
    conclusion: Proposition,
    rule: &CVerifiedFunctionRule,
) -> Option<CVerifiedPureTheorem> {
    if source_names.is_empty() {
        return None;
    }
    let target = environment.get_function_contract(target_name)?;
    let mut function = rule.function.clone();
    let callback = function.pop_parameter()?;
    if callback.c_type() != target.function_pointer_type() {
        return None;
    }
    let arguments = function
        .parameters()
        .iter()
        .map(|parameter| CExpression::Variable(parameter.name().to_string()))
        .collect();
    let call = if function.return_type() == CType::Void {
        CStatement::Call {
            function_name: callback.name().to_string(),
            arguments,
        }
    } else {
        CStatement::Seq(
            Arc::new(CStatement::CallAssign {
                target: "result".into(),
                function_name: callback.name().to_string(),
                arguments,
            }),
            Arc::new(CStatement::Return(CExpression::Variable("result".into()))),
        )
    };
    if function.body() != &call || function.source_body() != &call {
        return None;
    }
    for source_name in source_names.iter().rev() {
        let source = environment.get_function_contract(source_name)?;
        if callback.c_type() != source.function_pointer_type() {
            return None;
        }
        let source_requirement = SpecProposition::Predicate {
            // A function-contract predicate denotes its closed interface,
            // independently of the caller's current population model.
            resource_state_dependent: false,
            name: source.predicate_name(),
            arguments: vec![SpecPredicateArgument::Value(SpecExpression::CExpression(
                CExpression::Variable(callback.name().to_string()),
            ))],
        };
        if function.pop_contract_requirement()? != source_requirement {
            return None;
        }
    }
    if !contract_interface_identity::same_interface(target, &function) {
        return None;
    }
    let Proposition::Predicate { name, arguments } = &conclusion else {
        return None;
    };
    let [
        state @ Term::CState(_),
        Term::CValue(CValue::Pointer(pointer)),
    ] = arguments.as_slice()
    else {
        return None;
    };
    let PointerBlock::FunctionSymbolic(variable) = pointer.pointer().block else {
        return None;
    };
    if name != &target.predicate_name()
        || pointer.c_type() != target.function_pointer_type()
        || pointer.pointer().offset != PointerOffsetTerm::Constant(0)
    {
        return None;
    }
    let mut implication = conclusion.clone();
    for source_name in source_names.iter().rev() {
        let premise = Proposition::Predicate {
            name: environment
                .get_function_contract(source_name)?
                .predicate_name(),
            arguments: vec![
                state.clone(),
                Term::CValue(CValue::Pointer(pointer.clone())),
            ],
        };
        implication = Proposition::Implies(Box::new(premise), Box::new(implication));
    }
    Some(CVerifiedPureTheorem {
        theorem: Theorem::new(Proposition::ForAll {
            var: variable,
            sort: Sort::CPointer(pointer.c_type()),
            body: Box::new(implication),
        }),
    })
}

/// The declared interface of a verified or explicitly external project
/// function: its parameter types in order, then its return type. Two exact map
/// lookups, so a concrete `executes` clause is checked against the same C
/// signature the call rule will use.
pub fn c_project_function_signature(
    environment: &CExecutionEnvironment,
    name: &str,
) -> Option<(Vec<CType>, CType)> {
    let function = project_function_interface(environment, name)?;
    Some((
        function
            .parameters()
            .iter()
            .map(|parameter| parameter.c_type())
            .collect(),
        function.return_type(),
    ))
}

fn project_function_interface<'a>(
    environment: &'a CExecutionEnvironment,
    name: &str,
) -> Option<&'a CFunction> {
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
    environment: &CExecutionEnvironment,
    callee_name: &str,
    target_name: &str,
    conclusion: Proposition,
    rule: &CVerifiedFunctionRule,
) -> Option<CVerifiedPureTheorem> {
    let target = environment.get_function_contract(target_name)?;
    // The callee has to be a function this project has a rule for. An
    // unverified name would make the checked call vacuous.
    project_function_interface(environment, callee_name)?;
    let function = rule.function.clone();
    let arguments = function
        .parameters()
        .iter()
        .map(|parameter| CExpression::Variable(parameter.name().to_string()))
        .collect();
    let call = if function.return_type() == CType::Void {
        CStatement::Call {
            function_name: callee_name.to_string(),
            arguments,
        }
    } else {
        CStatement::Seq(
            Arc::new(CStatement::CallAssign {
                target: "result".into(),
                function_name: callee_name.to_string(),
                arguments,
            }),
            Arc::new(CStatement::Return(CExpression::Variable("result".into()))),
        )
    };
    if function.body() != &call || function.source_body() != &call {
        return None;
    }
    if !contract_interface_identity::same_interface(target, &function) {
        return None;
    }
    let Proposition::Predicate { name, arguments } = &conclusion else {
        return None;
    };
    let [Term::CState(_), Term::CValue(CValue::Pointer(pointer))] = arguments.as_slice() else {
        return None;
    };
    if pointer.pointer().block != PointerBlock::Function(callee_name.to_string()) {
        return None;
    }
    if name != &target.predicate_name()
        || pointer.c_type() != target.function_pointer_type()
        || pointer.pointer().offset != PointerOffsetTerm::Constant(0)
    {
        return None;
    }
    Some(CVerifiedPureTheorem {
        theorem: Theorem::new(conclusion),
    })
}

fn rewrite_int32_term_by_exact_equality(
    term: &Bitvector32Term,
    from: &Bitvector32Term,
    to: &Bitvector32Term,
) -> Bitvector32Term {
    if term == from {
        return to.clone();
    }
    let binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
        (
            rewrite_int32_term_by_exact_equality(left, from, to),
            rewrite_int32_term_by_exact_equality(right, from, to),
        )
    };
    match term {
        Bitvector32Term::MachineIntegerCast { .. } => term.clone(),

        Bitvector32Term::Add(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::add(left, right)
        }
        Bitvector32Term::Subtract(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::subtract(left, right)
        }
        Bitvector32Term::Multiply(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::Multiply(Box::new(left), Box::new(right))
        }
        Bitvector32Term::Divide(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::Divide(Box::new(left), Box::new(right))
        }
        Bitvector32Term::UnsignedDivide(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::UnsignedDivide(Box::new(left), Box::new(right))
        }
        Bitvector32Term::Remainder(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::Remainder(Box::new(left), Box::new(right))
        }
        Bitvector32Term::UnsignedRemainder(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::UnsignedRemainder(Box::new(left), Box::new(right))
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::ShiftLeft(Box::new(left), Box::new(right))
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::ArithmeticShiftRight(Box::new(left), Box::new(right))
        }
        Bitvector32Term::LogicalShiftRight(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::LogicalShiftRight(Box::new(left), Box::new(right))
        }
        Bitvector32Term::BitwiseAnd(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::BitwiseAnd(Box::new(left), Box::new(right))
        }
        Bitvector32Term::BitwiseOr(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::BitwiseOr(Box::new(left), Box::new(right))
        }
        Bitvector32Term::BitwiseXor(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::BitwiseXor(Box::new(left), Box::new(right))
        }
        Bitvector32Term::BitwiseNot(value) => Bitvector32Term::BitwiseNot(Box::new(
            rewrite_int32_term_by_exact_equality(value, from, to),
        )),
        Bitvector32Term::Float32Negate(value) => Bitvector32Term::Float32Negate(Box::new(
            rewrite_int32_term_by_exact_equality(value, from, to),
        )),
        Bitvector32Term::Float32Binary {
            operator,
            left,
            right,
        } => Bitvector32Term::Float32Binary {
            operator: *operator,
            left: Box::new(rewrite_int32_term_by_exact_equality(left, from, to)),
            right: Box::new(rewrite_int32_term_by_exact_equality(right, from, to)),
        },
        Bitvector32Term::Float64Negate(value) => Bitvector32Term::Float64Negate(Box::new(
            rewrite_int32_term_by_exact_equality(value, from, to),
        )),
        Bitvector32Term::Float64Binary {
            operator,
            left,
            right,
        } => Bitvector32Term::Float64Binary {
            operator: *operator,
            left: Box::new(rewrite_int32_term_by_exact_equality(left, from, to)),
            right: Box::new(rewrite_int32_term_by_exact_equality(right, from, to)),
        },
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => Bitvector32Term::If {
            condition: condition.clone(),
            then_term: Box::new(rewrite_int32_term_by_exact_equality(then_term, from, to)),
            else_term: Box::new(rewrite_int32_term_by_exact_equality(else_term, from, to)),
        },
        Bitvector32Term::PureFunctionApplication { name, arguments } => {
            Bitvector32Term::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| rewrite_int32_term_by_exact_equality(argument, from, to))
                    .collect(),
            }
        }
        Bitvector32Term::ClickFunctionApplication { .. }
        | Bitvector32Term::AlgebraicMatch { .. } => term.clone(),
        Bitvector32Term::Constant(_)
        | Bitvector32Term::Variable(_)
        | Bitvector32Term::MemoryLoad(_, _, _)
        | Bitvector32Term::PointerAddress(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::MachineIntegerConstant(_)
        | Bitvector32Term::Int64From32(_)
        | Bitvector32Term::Int64FromUInt32(_)
        | Bitvector32Term::UInt64From32(_)
        | Bitvector32Term::UInt32From64(_)
        | Bitvector32Term::UInt64FromInt32(_)
        | Bitvector32Term::UInt64FromInt64(_)
        | crate::kernel::binary_int64_term!(_, _)
        | Bitvector32Term::Int64BitwiseNot(_)
        | crate::kernel::binary_uint64_term!(_, _)
        | Bitvector32Term::UInt64BitwiseNot(_)
        | Bitvector32Term::RangeFold { .. }
        | Bitvector32Term::IntegerToMachine { .. } => term.clone(),
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
) -> Option<CVerifiedPureTheorem> {
    if !checked_pure_implication_matches(&requirements, &conclusion, completion) {
        return None;
    }
    let mut goal = conclusion.clone();
    for rewrite in rewrites {
        crate::kernel::proof::fact_reasoning::exactly_available_fact(&rewrite, &requirements)?;
        let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(from, to), true) = rewrite
        else {
            return None;
        };
        let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) = goal
        else {
            return None;
        };
        let rewritten_left = rewrite_int32_term_by_exact_equality(&left, &from, &to);
        let rewritten_right = rewrite_int32_term_by_exact_equality(&right, &from, &to);
        if rewritten_left == *left && rewritten_right == *right {
            return None;
        }
        goal = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(Box::new(rewritten_left), Box::new(rewritten_right)),
            true,
        );
    }
    universally_close_pure_implication(requirements, conclusion, variables)
}

/// Adding one on the left of a signed int32 value below the maximum is
/// defined.
pub fn prove_int32_one_plus_below_max_is_defined(value: Bitvector32Term) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(value.clone(), Bitvector32Term::Constant(i32::MAX as u32)),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_add_overflows(Bitvector32Term::Constant(1), value),
        false,
    );
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// Adding one on the left strictly increases a signed int32 value below the
/// maximum.
pub fn prove_int32_one_plus_strictly_increases(value: Bitvector32Term) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(value.clone(), Bitvector32Term::Constant(i32::MAX as u32)),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(
            value.clone(),
            Bitvector32Term::Add(Box::new(Bitvector32Term::Constant(1)), Box::new(value)),
        ),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// Adding a nonnegative signed int32 amount within the remaining positive
/// headroom is defined.
pub fn prove_int32_nonnegative_add_within_max_is_defined(
    value: Bitvector32Term,
    amount: Bitvector32Term,
) -> Theorem {
    let amount_is_nonnegative = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), amount.clone()),
        true,
    );
    let within_headroom = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            value.clone(),
            Bitvector32Term::Subtract(
                Box::new(Bitvector32Term::Constant(i32::MAX as u32)),
                Box::new(amount.clone()),
            ),
        ),
        true,
    );
    let conclusion =
        Proposition::ConditionIs(ConditionTerm::signed_add_overflows(value, amount), false);
    Theorem::new(Proposition::Implies(
        Box::new(amount_is_nonnegative),
        Box::new(Proposition::Implies(
            Box::new(within_headroom),
            Box::new(conclusion),
        )),
    ))
}

/// Subtracting a nonnegative signed int32 amount no larger than the value is
/// defined.
pub fn prove_int32_nonnegative_subtract_within_value_is_defined(
    value: Bitvector32Term,
    amount: Bitvector32Term,
) -> Theorem {
    let amount_is_nonnegative = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), amount.clone()),
        true,
    );
    let amount_within_value = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(amount.clone(), value.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_subtract_overflows(value, amount),
        false,
    );
    Theorem::new(Proposition::Implies(
        Box::new(amount_is_nonnegative),
        Box::new(Proposition::Implies(
            Box::new(amount_within_value),
            Box::new(conclusion),
        )),
    ))
}

/// Moving one unit between nonnegative summands preserves their signed int32
/// sum. A positive right summand leaves both adjusted operands nonnegative,
/// while definedness of the original sum supplies the shared upper bound that
/// rules out overflow in the increment and recomposed sum.
pub fn prove_int32_move_one_from_right_to_left_preserves_sum(
    total: Bitvector32Term,
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Theorem {
    let left_is_nonnegative = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), left.clone()),
        true,
    );
    let right_is_positive = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(1), right.clone()),
        true,
    );
    let original_sum = Bitvector32Term::add(left.clone(), right.clone());
    let total_is_original_sum = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(total.clone()), Box::new(original_sum)),
        true,
    );
    let incremented = Bitvector32Term::add(left.clone(), Bitvector32Term::Constant(1));
    let decremented = Bitvector32Term::Subtract(
        Box::new(right.clone()),
        Box::new(Bitvector32Term::Constant(1)),
    );
    let adjusted_sum = Bitvector32Term::add(incremented, decremented);
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(total), Box::new(adjusted_sum)),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(left_is_nonnegative),
        Box::new(Proposition::Implies(
            Box::new(right_is_positive),
            Box::new(Proposition::Implies(
                Box::new(total_is_original_sum),
                Box::new(conclusion),
            )),
        )),
    ))
}

/// Kernel-issued universally quantified authority for the unit-transfer sum rule.
pub fn certify_int32_move_one_from_right_to_left_preserves_sum() -> CVerifiedPureTheorem {
    let total = Variable(0);
    let left = Variable(1);
    let right = Variable(2);
    let implication = prove_int32_move_one_from_right_to_left_preserves_sum(
        Bitvector32Term::Variable(total),
        Bitvector32Term::Variable(left),
        Bitvector32Term::Variable(right),
    );
    CVerifiedPureTheorem {
        theorem: Theorem::new(forall_int32(
            total,
            forall_int32(left, forall_int32(right, implication.proposition().clone())),
        )),
    }
}

/// Mathematical bounds on the exact sum establish signed C addition safety.
pub fn prove_int32_add_defined_by_integer_bounds(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Theorem {
    prove_int32_operation_defined_by_integer_bounds(left, right, false)
}

/// Mathematical bounds on the exact difference establish signed C
/// subtraction safety.
pub fn prove_int32_subtract_defined_by_integer_bounds(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Theorem {
    prove_int32_operation_defined_by_integer_bounds(left, right, true)
}

fn prove_int32_operation_defined_by_integer_bounds(
    left: Bitvector32Term,
    right: Bitvector32Term,
    subtract: bool,
) -> Theorem {
    prove_signed_operation_defined_by_integer_bounds(
        MachineIntegerType::Int32,
        left,
        right,
        subtract,
    )
}

/// Mathematical bounds on the exact sum establish signed 64-bit C addition
/// safety.
pub fn prove_int64_add_defined_by_integer_bounds(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Theorem {
    prove_signed_operation_defined_by_integer_bounds(MachineIntegerType::Int64, left, right, false)
}

/// Mathematical bounds on the exact difference establish signed 64-bit C
/// subtraction safety.
pub fn prove_int64_subtract_defined_by_integer_bounds(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Theorem {
    prove_signed_operation_defined_by_integer_bounds(MachineIntegerType::Int64, left, right, true)
}

/// A signed sum or difference is defined when its exact mathematical value
/// lies in the type's range: overflow is exactly leaving that range.
fn prove_signed_operation_defined_by_integer_bounds(
    ty: MachineIntegerType,
    left: Bitvector32Term,
    right: Bitvector32Term,
    subtract: bool,
) -> Theorem {
    let observe = |value| {
        IntegerTerm::from_machine(ty, value)
            .expect("every signed bit pattern has a mathematical interpretation")
    };
    let (observed_left, observed_right) =
        (observe(left.clone()).into(), observe(right.clone()).into());
    let exact: SharedIntegerTerm = if subtract {
        IntegerTerm::Subtract(observed_left, observed_right).into()
    } else {
        IntegerTerm::Add(observed_left, observed_right).into()
    };
    let (overflows, minimum, maximum) = match (ty, subtract) {
        (MachineIntegerType::Int32, false) => (
            ConditionTerm::signed_add_overflows(left, right),
            i64::from(i32::MIN),
            i64::from(i32::MAX),
        ),
        (MachineIntegerType::Int32, true) => (
            ConditionTerm::signed_subtract_overflows(left, right),
            i64::from(i32::MIN),
            i64::from(i32::MAX),
        ),
        (MachineIntegerType::Int64, false) => (
            ConditionTerm::int64_signed_add_overflows(left, right),
            i64::MIN,
            i64::MAX,
        ),
        (MachineIntegerType::Int64, true) => (
            ConditionTerm::int64_signed_subtract_overflows(left, right),
            i64::MIN,
            i64::MAX,
        ),
        _ => unreachable!("definedness by Integer bounds admits only int32 and int64"),
    };
    Theorem::new(Proposition::Implies(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::IntegerGreaterEqual(
                exact.clone(),
                IntegerTerm::constant_i64(minimum).into(),
            ),
            true,
        )),
        Box::new(Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::IntegerLessEqual(exact, IntegerTerm::constant_i64(maximum).into()),
                true,
            )),
            Box::new(Proposition::ConditionIs(overflows, false)),
        )),
    ))
}

/// Strict order of the exact Integer observations implies strict native
/// signed int64 order: the observation is injective and monotone.
pub fn prove_int64_less_than_of_to_integer(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Theorem {
    let integer = ConditionTerm::IntegerLessThan(
        IntegerTerm::from_machine(MachineIntegerType::Int64, left.clone())
            .unwrap()
            .into(),
        IntegerTerm::from_machine(MachineIntegerType::Int64, right.clone())
            .unwrap()
            .into(),
    );
    Theorem::new(Proposition::Implies(
        Box::new(Proposition::ConditionIs(integer, true)),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::int64_signed_less_than(left, right),
            true,
        )),
    ))
}

/// A checked round trip through a machine carrier preserves an Integer
/// precisely within that carrier's representable range.
pub fn prove_integer_machine_round_trip(
    value: IntegerTerm,
    destination: MachineIntegerType,
) -> Theorem {
    let (lower, upper) = super::spec::integer_machine_bounds(destination);
    let converted = Bitvector32Term::IntegerToMachine {
        value: value.clone().into(),
        destination,
    };
    let observed = IntegerTerm::from_machine(destination, converted)
        .expect("machine observation has an integral carrier");
    Theorem::new(Proposition::Implies(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::IntegerGreaterEqual(value.clone().into(), lower.into()),
            true,
        )),
        Box::new(Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::IntegerLessEqual(value.clone().into(), upper.into()),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::IntegerEqual(observed.into(), value.into()),
                true,
            )),
        )),
    ))
}

/// Exact unsigned observations of both summands must fit the u32 range.
/// Widening each u32 operand to i64 is value-preserving, and their sum is at
/// most 2*(2^32-1), so evaluating the widened guard cannot overflow i64.
pub fn prove_uint32_widened_add_guard_by_integer_bound(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Theorem {
    let premise = uint32_exact_sum_bound(left.clone(), right.clone());
    let sum = Bitvector32Term::int64_add(
        Bitvector32Term::int64_from_uint32(left),
        Bitvector32Term::int64_from_uint32(right),
    );
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::int64_signed_less_equal(
                sum,
                Bitvector32Term::Int64Constant(i64::from(u32::MAX)),
            ),
            true,
        )),
    ))
}

fn uint32_exact_sum_bound(left: Bitvector32Term, right: Bitvector32Term) -> Proposition {
    let observe = |value| {
        IntegerTerm::from_machine(MachineIntegerType::UInt32, value)
            .expect("every uint32 bit pattern has an unsigned Integer interpretation")
    };
    Proposition::ConditionIs(
        ConditionTerm::IntegerLessEqual(
            IntegerTerm::Add(observe(left).into(), observe(right).into()).into(),
            IntegerTerm::constant_i64(i64::from(u32::MAX)).into(),
        ),
        true,
    )
}

/// Unsigned machine addition agrees with mathematical addition precisely
/// under the explicit no-wrap bound. Definedness alone permits wrapping.
pub fn prove_uint32_add_to_integer(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    let premise = uint32_exact_sum_bound(left.clone(), right.clone());
    let observe = |value| {
        IntegerTerm::from_machine(MachineIntegerType::UInt32, value)
            .expect("every uint32 bit pattern has an unsigned Integer interpretation")
    };
    let observed_sum = observe(Bitvector32Term::add(left.clone(), right.clone()));
    let exact = IntegerTerm::Add(observe(left).into(), observe(right).into());
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(observed_sum.into(), exact.into()),
            true,
        )),
    ))
}

/// Exact mathematical observation of unsigned subtraction without underflow.
/// Native definedness alone permits wrapping, including 0u32 - 1u32.
pub fn prove_uint32_subtract_to_integer(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    let observe = |value| {
        IntegerTerm::from_machine(MachineIntegerType::UInt32, value)
            .expect("every uint32 bit pattern has an unsigned Integer interpretation")
    };
    let difference = observe(Bitvector32Term::subtract(left.clone(), right.clone()));
    let exact = IntegerTerm::Subtract(observe(left.clone()).into(), observe(right.clone()).into());
    Theorem::new(Proposition::Implies(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::unsigned_less_equal(right, left),
            true,
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(difference.into(), exact.into()),
            true,
        )),
    ))
}

/// Unsigned multiplication has its exact mathematical value under the native
/// checked-multiplication guard. The zero factor branch does not divide by zero.
/// Definedness of a wrapping u32 product alone is insufficient.
pub fn prove_uint32_mul_to_integer(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    let premise = uint32_mul_guard(left.clone(), right.clone());
    let observe = |value| {
        IntegerTerm::from_machine(MachineIntegerType::UInt32, value)
            .expect("every uint32 bit pattern has an unsigned Integer interpretation")
    };
    let product = observe(Bitvector32Term::multiply(left.clone(), right.clone()));
    let exact = IntegerTerm::Multiply(observe(left).into(), observe(right).into());
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(product.into(), exact.into()),
            true,
        )),
    ))
}

fn uint32_mul_guard(left: Bitvector32Term, right: Bitvector32Term) -> Proposition {
    Proposition::Or(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(right.clone(), Bitvector32Term::Constant(0)),
            true,
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::unsigned_less_equal(
                left,
                Bitvector32Term::unsigned_divide(Bitvector32Term::Constant(u32::MAX), right),
            ),
            true,
        )),
    )
}

/// A mathematical product that fits u32 establishes Rust's checked native
/// multiplication guard. Unsigned observations are nonnegative, so the
/// nonzero branch is exactly left <= floor(u32::MAX / right).
pub fn prove_uint32_mul_guard_by_integer_bound(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Theorem {
    let observe = |value| {
        IntegerTerm::from_machine(MachineIntegerType::UInt32, value)
            .expect("every uint32 bit pattern has an unsigned Integer interpretation")
    };
    let product =
        IntegerTerm::Multiply(observe(left.clone()).into(), observe(right.clone()).into());
    let premise = Proposition::ConditionIs(
        ConditionTerm::IntegerLessEqual(
            product.into(),
            IntegerTerm::constant_i64(i64::from(u32::MAX)).into(),
        ),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(uint32_mul_guard(left, right)),
    ))
}

/// Observe unsigned machine division in Integer arithmetic. Both domains
/// explicitly exclude a zero divisor; no no-wrap premise is needed.
pub fn prove_uint32_divide_to_integer(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    prove_uint32_integer_division_bridge(left, right, false)
}

/// Observe unsigned machine remainder in nonnegative Integer arithmetic.
pub fn prove_uint32_remainder_to_integer(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    prove_uint32_integer_division_bridge(left, right, true)
}

fn prove_uint32_integer_division_bridge(
    left: Bitvector32Term,
    right: Bitvector32Term,
    remainder: bool,
) -> Theorem {
    let observe = |value| {
        IntegerTerm::from_machine(MachineIntegerType::UInt32, value)
            .expect("every uint32 bit pattern has an unsigned Integer interpretation")
    };
    let dividend = observe(left.clone());
    let divisor = observe(right.clone());
    let native_nonzero = Proposition::ConditionIs(
        ConditionTerm::equal(right.clone(), Bitvector32Term::Constant(0)),
        false,
    );
    let integer_nonzero = Proposition::ConditionIs(
        ConditionTerm::integer_not_equal(divisor.clone(), IntegerTerm::constant_i64(0)),
        true,
    );
    let (machine, exact) = if remainder {
        (
            Bitvector32Term::unsigned_remainder(left, right),
            IntegerTerm::TruncatingRemainder(dividend.into(), divisor.into()),
        )
    } else {
        (
            Bitvector32Term::unsigned_divide(left, right),
            IntegerTerm::TruncatingQuotient(dividend.into(), divisor.into()),
        )
    };
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::IntegerEqual(observe(machine).into(), exact.into()),
        true,
    );
    Theorem::new(Proposition::Implies(
        native_nonzero.into(),
        Proposition::Implies(integer_nonzero.into(), conclusion.into()).into(),
    ))
}

/// An unsigned remainder is strictly below its nonzero divisor.
/// No upper bound on the dividend is needed; zero division is excluded.
pub fn prove_uint32_remainder_less_than_divisor(
    value: Bitvector32Term,
    divisor: Bitvector32Term,
) -> Theorem {
    Theorem::new(Proposition::Implies(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(divisor.clone(), Bitvector32Term::Constant(0)),
            false,
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::unsigned_less_than(
                Bitvector32Term::unsigned_remainder(value, divisor.clone()),
                divisor,
            ),
            true,
        )),
    ))
}

/// A dividend strictly below an unsigned divisor is already its remainder.
/// The strict unsigned premise also excludes division by zero.
pub fn prove_uint32_remainder_of_lt(value: Bitvector32Term, divisor: Bitvector32Term) -> Theorem {
    Theorem::new(Proposition::Implies(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::unsigned_less_than(value.clone(), divisor.clone()),
            true,
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::unsigned_remainder(value.clone(), divisor),
                value,
            ),
            true,
        )),
    ))
}

/// Preserve native unsigned u32 order in exact mathematical observations.
/// The unsigned interpretation includes values above the signed sign bit.
pub fn prove_uint32_less_equal_to_integer(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Theorem {
    prove_machine_integer_order_bridge(MachineIntegerType::UInt32, left, right, false)
}

/// Reflect mathematical order into native unsigned u32 order.
pub fn prove_uint32_less_equal_of_to_integer(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Theorem {
    prove_machine_integer_order_bridge(MachineIntegerType::UInt32, left, right, true)
}

/// Exact mathematical observation of a defined signed 32-bit addition.
/// The overflow premise is essential: the machine term alone is modular.
pub fn prove_int32_add_to_integer(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    prove_signed_operation_to_integer(MachineIntegerType::Int32, left, right, false)
}

/// Exact unsigned 64-bit observations. Addition and multiplication require
/// explicit no-wrap bounds; subtraction requires no underflow. Division and
/// remainder exclude zero in both evaluation domains, but impose no bound on
/// the dividend. These laws
/// describe unsigned machine arithmetic, not signed overflow definedness.
/// Exact mathematical observation of two unsigned 16-bit fields packed
/// into a 32- or 64-bit word. Both bounds are necessary: the fields must be
/// disjoint, and the high shift must preserve all bits.
pub fn prove_unsigned_pack_u16_to_integer(
    ty: MachineIntegerType,
    low: Bitvector32Term,
    high: Bitvector32Term,
) -> Option<Theorem> {
    prove_unsigned_pack_u16_in_order_to_integer(ty, low, high, false)
}

/// The same disjoint-field packing law for `(high << 16) | low`.
pub fn prove_unsigned_pack_u16_high_first_to_integer(
    ty: MachineIntegerType,
    low: Bitvector32Term,
    high: Bitvector32Term,
) -> Option<Theorem> {
    prove_unsigned_pack_u16_in_order_to_integer(ty, low, high, true)
}

fn prove_unsigned_pack_u16_in_order_to_integer(
    ty: MachineIntegerType,
    low: Bitvector32Term,
    high: Bitvector32Term,
    high_first: bool,
) -> Option<Theorem> {
    let (packed, low_bound, high_bound) = match ty {
        MachineIntegerType::UInt32 => (
            Bitvector32Term::BitwiseOr(
                low.clone().into(),
                Bitvector32Term::ShiftLeft(
                    high.clone().into(),
                    Bitvector32Term::Constant(16).into(),
                )
                .into(),
            ),
            ConditionTerm::unsigned_less_equal(low.clone(), Bitvector32Term::Constant(65535)),
            ConditionTerm::unsigned_less_equal(high.clone(), Bitvector32Term::Constant(65535)),
        ),
        MachineIntegerType::UInt64 => (
            Bitvector32Term::uint64_bitwise_or(
                low.clone(),
                Bitvector32Term::uint64_shift_left(
                    high.clone(),
                    Bitvector32Term::Int64Constant(16),
                ),
            ),
            ConditionTerm::uint64_less_equal(low.clone(), Bitvector32Term::UInt64Constant(65535)),
            ConditionTerm::uint64_less_equal(high.clone(), Bitvector32Term::UInt64Constant(65535)),
        ),
        _ => return None,
    };
    let packed = if high_first {
        match ty {
            MachineIntegerType::UInt32 => Bitvector32Term::BitwiseOr(
                Bitvector32Term::ShiftLeft(
                    high.clone().into(),
                    Bitvector32Term::Constant(16).into(),
                )
                .into(),
                low.clone().into(),
            ),
            MachineIntegerType::UInt64 => Bitvector32Term::uint64_bitwise_or(
                Bitvector32Term::uint64_shift_left(
                    high.clone(),
                    Bitvector32Term::Int64Constant(16),
                ),
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
    Some(Theorem::new(Proposition::Implies(
        Box::new(Proposition::ConditionIs(low_bound, true)),
        Box::new(Proposition::Implies(
            Box::new(Proposition::ConditionIs(high_bound, true)),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::integer_equal(observe(packed)?, exact),
                true,
            )),
        )),
    )))
}

pub fn prove_uint64_integer_bridge(
    name: &str,
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Option<Theorem> {
    if matches!(
        name,
        "uint64_less_equal_to_integer" | "uint64_to_integer_less_equal_implies_less_equal"
    ) {
        return Some(prove_machine_integer_order_bridge(
            MachineIntegerType::UInt64,
            left,
            right,
            name == "uint64_to_integer_less_equal_implies_less_equal",
        ));
    }
    // The unsigned observation is injective: equal observations are the
    // same 64-bit pattern.
    if name == "uint64_to_integer_equal_implies_equal" {
        return Some(prove_integer_equality_bridge(
            MachineIntegerType::UInt64,
            left,
            right,
        ));
    }
    if name == "uint64_pack_uint16_to_integer" {
        return prove_unsigned_pack_u16_to_integer(MachineIntegerType::UInt64, left, right);
    }
    let observe = |value| {
        IntegerTerm::from_machine(MachineIntegerType::UInt64, value)
            .expect("every uint64 bit pattern has an unsigned Integer interpretation")
    };
    let a = observe(left.clone());
    let b = observe(right.clone());
    // Strict order, in both directions: the unsigned observation is
    // injective and monotone over every 64-bit pattern.
    if matches!(
        name,
        "uint64_less_than_to_integer" | "uint64_to_integer_less_than_implies_less_than"
    ) {
        let native = Proposition::ConditionIs(ConditionTerm::uint64_less_than(left, right), true);
        let integer =
            Proposition::ConditionIs(ConditionTerm::IntegerLessThan(a.into(), b.into()), true);
        let (premise, conclusion) = if name == "uint64_to_integer_less_than_implies_less_than" {
            (integer, native)
        } else {
            (native, integer)
        };
        return Some(Theorem::new(Proposition::Implies(
            Box::new(premise),
            Box::new(conclusion),
        )));
    }
    // Unsigned total order: strict less and greater-or-equal are
    // complementary evaluations of the same two 64-bit patterns.
    if name == "uint64_less_than_implies_not_greater_equal" {
        return Some(Theorem::new(Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::uint64_less_than(left.clone(), right.clone()),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::Bitvector64UnsignedGreaterEqual(left.into(), right.into()),
                false,
            )),
        )));
    }
    let maximum = IntegerTerm::constant(num_bigint::BigInt::from(u64::MAX));
    let (machine, exact, guard) = match name {
        "uint64_add_to_integer" => {
            let exact = IntegerTerm::Add(a.into(), b.into());
            let guard = Proposition::ConditionIs(
                ConditionTerm::IntegerLessEqual(exact.clone().into(), maximum.into()),
                true,
            );
            (
                Bitvector32Term::UInt64Add(left.into(), right.into()),
                exact,
                guard,
            )
        }
        "uint64_multiply_to_integer" => {
            let exact = IntegerTerm::Multiply(a.into(), b.into());
            let guard = Proposition::ConditionIs(
                ConditionTerm::IntegerLessEqual(exact.clone().into(), maximum.into()),
                true,
            );
            (
                Bitvector32Term::UInt64Multiply(left.into(), right.into()),
                exact,
                guard,
            )
        }
        "uint64_subtract_to_integer" => {
            let guard = Proposition::ConditionIs(
                ConditionTerm::IntegerLessEqual(b.clone().into(), a.clone().into()),
                true,
            );
            (
                Bitvector32Term::UInt64Subtract(left.into(), right.into()),
                IntegerTerm::Subtract(a.into(), b.into()),
                guard,
            )
        }
        "uint64_divide_to_integer" | "uint64_remainder_to_integer" => {
            let native_nonzero = Proposition::ConditionIs(
                ConditionTerm::uint64_equal(right.clone(), Bitvector32Term::UInt64Constant(0)),
                false,
            );
            let integer_nonzero = Proposition::ConditionIs(
                ConditionTerm::integer_not_equal(b.clone(), IntegerTerm::constant_i64(0)),
                true,
            );
            let (machine, exact) = if name == "uint64_divide_to_integer" {
                (
                    Bitvector32Term::UInt64Divide(left.into(), right.into()),
                    IntegerTerm::TruncatingQuotient(a.into(), b.into()),
                )
            } else {
                (
                    Bitvector32Term::UInt64Remainder(left.into(), right.into()),
                    IntegerTerm::TruncatingRemainder(a.into(), b.into()),
                )
            };
            let conclusion = Proposition::ConditionIs(
                ConditionTerm::IntegerEqual(observe(machine).into(), exact.into()),
                true,
            );
            return Some(Theorem::new(Proposition::Implies(
                native_nonzero.into(),
                Proposition::Implies(integer_nonzero.into(), conclusion.into()).into(),
            )));
        }
        _ => return None,
    };
    Some(Theorem::new(Proposition::Implies(
        guard.into(),
        Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(observe(machine).into(), exact.into()),
            true,
        )
        .into(),
    )))
}

/// Signed int32 order is preserved by its exact mathematical observation.
/// Every int32 bit pattern has an Integer interpretation, so this law needs
/// only the corresponding C order premise and no definedness side condition.
pub fn prove_int32_less_equal_to_integer(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    prove_machine_integer_order_bridge(MachineIntegerType::Int32, left, right, false)
}

/// Reflect mathematical order into native signed int32 order.
pub fn prove_int32_less_equal_of_to_integer(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Theorem {
    prove_machine_integer_order_bridge(MachineIntegerType::Int32, left, right, true)
}

/// Preserve native signed int64 order in its mathematical observation.
pub fn prove_int64_less_equal_to_integer(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    prove_machine_integer_order_bridge(MachineIntegerType::Int64, left, right, false)
}

/// Preserve a strict native signed int64 comparison in Integer arithmetic.
pub fn prove_int64_less_than_to_integer(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    let integer = ConditionTerm::IntegerLessThan(
        IntegerTerm::from_machine(MachineIntegerType::Int64, left.clone())
            .unwrap()
            .into(),
        IntegerTerm::from_machine(MachineIntegerType::Int64, right.clone())
            .unwrap()
            .into(),
    );
    Theorem::new(Proposition::Implies(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::int64_signed_less_than(left, right),
            true,
        )),
        Box::new(Proposition::ConditionIs(integer, true)),
    ))
}

/// Preserve the source's signed greater-or-equal comparison without changing its operands.
pub fn prove_int64_greater_equal_to_integer(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Theorem {
    let integer = ConditionTerm::IntegerGreaterEqual(
        IntegerTerm::from_machine(MachineIntegerType::Int64, left.clone())
            .unwrap()
            .into(),
        IntegerTerm::from_machine(MachineIntegerType::Int64, right.clone())
            .unwrap()
            .into(),
    );
    Theorem::new(Proposition::Implies(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::int64_signed_greater_equal(left, right),
            true,
        )),
        Box::new(Proposition::ConditionIs(integer, true)),
    ))
}

/// Reflect mathematical order into native signed int64 order.
pub fn prove_int64_less_equal_of_to_integer(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Theorem {
    prove_machine_integer_order_bridge(MachineIntegerType::Int64, left, right, true)
}

fn prove_machine_integer_order_bridge(
    ty: MachineIntegerType,
    left: Bitvector32Term,
    right: Bitvector32Term,
    reverse: bool,
) -> Theorem {
    let observe = |value| {
        IntegerTerm::from_machine(ty, value)
            .expect("typed machine operands have exact Integer interpretations")
    };
    let native = match ty {
        MachineIntegerType::UInt32 => {
            ConditionTerm::unsigned_less_equal(left.clone(), right.clone())
        }
        MachineIntegerType::Int32 => ConditionTerm::signed_less_equal(left.clone(), right.clone()),
        MachineIntegerType::Int64 => {
            ConditionTerm::int64_signed_less_equal(left.clone(), right.clone())
        }
        MachineIntegerType::UInt64 => ConditionTerm::uint64_less_equal(left.clone(), right.clone()),
        _ => unreachable!("order bridges admit only uint32/uint64/int32/int64"),
    };
    let native = Proposition::ConditionIs(native, true);
    let integer = Proposition::ConditionIs(
        ConditionTerm::IntegerLessEqual(observe(left).into(), observe(right).into()),
        true,
    );
    let (premise, conclusion) = if reverse {
        (integer, native)
    } else {
        (native, integer)
    };
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// Signed int32 observation is injective: two equal mathematical values
/// have the same 32-bit pattern. No overflow premise or conversion back is
/// needed, since every signed int32 pattern has one exact Integer value.
pub fn prove_int32_equal_of_to_integer(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    prove_integer_equality_bridge(MachineIntegerType::Int32, left, right)
}

/// Signed int64 observation is injective, including the full 64-bit extrema.
pub fn prove_int64_equal_of_to_integer(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    prove_integer_equality_bridge(MachineIntegerType::Int64, left, right)
}

/// Unsigned uint32 observation is injective: every 32-bit pattern has one
/// exact Integer value in `0..=4294967295`, including the patterns above the
/// signed sign bit, so equal observations have the same pattern.
pub fn prove_uint32_equal_of_to_integer(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    prove_integer_equality_bridge(MachineIntegerType::UInt32, left, right)
}

fn prove_integer_equality_bridge(
    ty: MachineIntegerType,
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Theorem {
    let observe = |value| {
        IntegerTerm::from_machine(ty, value)
            .expect("typed operands have exact Integer interpretations")
    };
    let integer = Proposition::ConditionIs(
        ConditionTerm::IntegerEqual(observe(left.clone()).into(), observe(right.clone()).into()),
        true,
    );
    let native = match ty {
        MachineIntegerType::Int32 => ConditionTerm::equal(left, right),
        MachineIntegerType::Int64 => ConditionTerm::int64_equal(left, right),
        // Equality of the 32-bit pattern does not depend on its signedness.
        MachineIntegerType::UInt32 => ConditionTerm::equal(left, right),
        MachineIntegerType::UInt64 => ConditionTerm::uint64_equal(left, right),
        _ => unreachable!("integer equality bridges admit only int32/int64/uint32/uint64"),
    };
    Theorem::new(Proposition::Implies(
        Box::new(integer),
        Box::new(Proposition::ConditionIs(native, true)),
    ))
}

/// Exact mathematical observation of a defined signed 32-bit subtraction.
pub fn prove_int32_subtract_to_integer(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    prove_signed_operation_to_integer(MachineIntegerType::Int32, left, right, true)
}

/// Exact mathematical remainder of a defined signed 32-bit operation.
/// Both zero division and MIN / -1 are excluded by the native definedness
/// premise, even though mathematical remainder itself has no overflow.
pub fn prove_int32_remainder_to_integer(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    let observe = |value| {
        IntegerTerm::from_machine(MachineIntegerType::Int32, value)
            .expect("typed operands have exact Integer interpretations")
    };
    let native_defined = Proposition::And(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(right.clone(), Bitvector32Term::Constant(0)),
            false,
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::signed_divide_overflows(left.clone(), right.clone()),
            false,
        )),
    );
    let integer_nonzero = Proposition::ConditionIs(
        ConditionTerm::integer_not_equal(observe(right.clone()), IntegerTerm::constant_i64(0)),
        true,
    );
    let exact = IntegerTerm::truncating_remainder(observe(left.clone()), observe(right.clone()));
    let machine = Bitvector32Term::Remainder(left.into(), right.into());
    Theorem::new(Proposition::Implies(
        native_defined.into(),
        Proposition::Implies(
            integer_nonzero.into(),
            Proposition::ConditionIs(
                ConditionTerm::IntegerEqual(observe(machine).into(), exact.into()),
                true,
            )
            .into(),
        )
        .into(),
    ))
}

/// Exact mathematical observation of a defined signed 64-bit addition.
pub fn prove_int64_add_to_integer(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    prove_signed_operation_to_integer(MachineIntegerType::Int64, left, right, false)
}

/// Exact mathematical observation of a defined signed 64-bit subtraction.
pub fn prove_int64_subtract_to_integer(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    prove_signed_operation_to_integer(MachineIntegerType::Int64, left, right, true)
}

fn prove_signed_operation_to_integer(
    ty: MachineIntegerType,
    left: Bitvector32Term,
    right: Bitvector32Term,
    subtract: bool,
) -> Theorem {
    let observe = |value| {
        IntegerTerm::from_machine(ty, value)
            .expect("typed operands have exact Integer interpretations")
    };
    let (overflow, machine) = match (ty, subtract) {
        (MachineIntegerType::Int32, false) => (
            ConditionTerm::signed_add_overflows(left.clone(), right.clone()),
            Bitvector32Term::Add(Box::new(left.clone()), Box::new(right.clone())),
        ),
        (MachineIntegerType::Int32, true) => (
            ConditionTerm::signed_subtract_overflows(left.clone(), right.clone()),
            Bitvector32Term::Subtract(Box::new(left.clone()), Box::new(right.clone())),
        ),
        (MachineIntegerType::Int64, false) => (
            ConditionTerm::int64_signed_add_overflows(left.clone(), right.clone()),
            Bitvector32Term::Int64Add(Box::new(left.clone()), Box::new(right.clone())),
        ),
        (MachineIntegerType::Int64, true) => (
            ConditionTerm::int64_signed_subtract_overflows(left.clone(), right.clone()),
            Bitvector32Term::Int64Subtract(Box::new(left.clone()), Box::new(right.clone())),
        ),
        _ => unreachable!("signed operation bridges admit only int32/int64"),
    };
    let mathematical = if subtract {
        IntegerTerm::Subtract(observe(left).into(), observe(right).into())
    } else {
        IntegerTerm::Add(observe(left).into(), observe(right).into())
    };
    Theorem::new(Proposition::Implies(
        Box::new(Proposition::ConditionIs(overflow, false)),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(observe(machine).into(), mathematical.into()),
            true,
        )),
    ))
}

/// A defined signed addition with a nonnegative right operand is at least its
/// left operand.
pub fn prove_int32_add_nonnegative_right_is_at_least_left(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Theorem {
    let right_is_nonnegative = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), right.clone()),
        true,
    );
    let addition_is_defined = Proposition::ConditionIs(
        ConditionTerm::signed_add_overflows(left.clone(), right.clone()),
        false,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(left.clone(), Bitvector32Term::add(left, right)),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(right_is_nonnegative),
        Box::new(Proposition::Implies(
            Box::new(addition_is_defined),
            Box::new(conclusion),
        )),
    ))
}

/// A defined signed addition with a nonnegative left operand is at least its
/// right operand.
pub fn prove_int32_add_nonnegative_left_is_at_least_right(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Theorem {
    let left_is_nonnegative = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), left.clone()),
        true,
    );
    let addition_is_defined = Proposition::ConditionIs(
        ConditionTerm::signed_add_overflows(left.clone(), right.clone()),
        false,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(right.clone(), Bitvector32Term::add(left, right)),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(left_is_nonnegative),
        Box::new(Proposition::Implies(
            Box::new(addition_is_defined),
            Box::new(conclusion),
        )),
    ))
}

/// Decrementing a positive signed int32 value produces a nonnegative value.
pub fn prove_int32_positive_predecessor_is_nonnegative(value: Bitvector32Term) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(0), value.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            Bitvector32Term::Constant(0),
            Bitvector32Term::Subtract(Box::new(value), Box::new(Bitvector32Term::Constant(1))),
        ),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// Decrementing a signed int32 value strictly above one leaves at least one.
pub fn prove_int32_above_one_predecessor_is_at_least_one(value: Bitvector32Term) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(1), value.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedGreaterEqual(
            Box::new(Bitvector32Term::Subtract(
                Box::new(value),
                Box::new(Bitvector32Term::Constant(1)),
            )),
            Box::new(Bitvector32Term::Constant(1)),
        ),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// Kernel-issued authority for the fixed predecessor bound used by independent
/// contract certification. Unlike a bare [`Theorem`], callers cannot build
/// this evidence from an untrusted proposition.
pub fn certify_int32_above_one_predecessor_is_at_least_one() -> CVerifiedPureTheorem {
    let variable = Variable(0);
    let implication =
        prove_int32_above_one_predecessor_is_at_least_one(Bitvector32Term::Variable(variable));
    CVerifiedPureTheorem {
        theorem: Theorem::new(Proposition::ForAll {
            var: variable,
            sort: Sort::CInt32,
            body: Box::new(implication.proposition().clone()),
        }),
    }
}

/// Decrementing a nonnegative signed int32 value preserves a non-strict
/// upper bound: nonnegativity rules out the `INT_MIN` wraparound, so the
/// predecessor stays strictly below the value and hence at most the bound.
pub fn prove_int32_nonnegative_predecessor_upper_bound(
    value: Bitvector32Term,
    bound: Bitvector32Term,
) -> Theorem {
    let nonnegative_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), value.clone()),
        true,
    );
    let bound_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(value.clone(), bound.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            Bitvector32Term::Subtract(Box::new(value), Box::new(Bitvector32Term::Constant(1))),
            bound,
        ),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(nonnegative_premise),
        Box::new(Proposition::Implies(
            Box::new(bound_premise),
            Box::new(conclusion),
        )),
    ))
}

/// Decrementing a positive signed int32 value strictly decreases it.
pub fn prove_int32_positive_predecessor_strictly_decreases(value: Bitvector32Term) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(0), value.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(
            Bitvector32Term::Subtract(
                Box::new(value.clone()),
                Box::new(Bitvector32Term::Constant(1)),
            ),
            value,
        ),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

fn uint32_implication(premise: ConditionTerm, conclusion: ConditionTerm) -> Theorem {
    Theorem::new(Proposition::Implies(
        Box::new(Proposition::ConditionIs(premise, true)),
        Box::new(Proposition::ConditionIs(conclusion, true)),
    ))
}

/// Decrementing a nonzero uint32 value strictly decreases it. A nonzero
/// value has a predecessor that does not wrap; at zero the predecessor is
/// `UINT_MAX`, which the premise excludes.
pub fn prove_uint32_positive_predecessor_strictly_decreases(value: Bitvector32Term) -> Theorem {
    uint32_implication(
        ConditionTerm::unsigned_less_than(Bitvector32Term::Constant(0), value.clone()),
        ConditionTerm::unsigned_less_than(
            Bitvector32Term::Subtract(
                Box::new(value.clone()),
                Box::new(Bitvector32Term::Constant(1)),
            ),
            value,
        ),
    )
}

/// A uint32 increment preserves a strict upper bound as a non-strict bound.
/// The strict premise rules out wraparound: if `value` were `UINT_MAX`, no
/// uint32 `upper` could be greater than it.
pub fn prove_uint32_increment_upper_bound(
    value: Bitvector32Term,
    upper: Bitvector32Term,
) -> Theorem {
    uint32_implication(
        ConditionTerm::unsigned_less_than(value.clone(), upper.clone()),
        ConditionTerm::unsigned_less_equal(
            Bitvector32Term::add(value, Bitvector32Term::Constant(1)),
            upper,
        ),
    )
}

/// A uint32 increment is strictly greater than its input when a strict
/// upper bound rules out wraparound.
pub fn prove_uint32_increment_strictly_increases(
    value: Bitvector32Term,
    upper: Bitvector32Term,
) -> Theorem {
    uint32_implication(
        ConditionTerm::unsigned_less_than(value.clone(), upper),
        ConditionTerm::unsigned_less_than(
            value.clone(),
            Bitvector32Term::add(value, Bitvector32Term::Constant(1)),
        ),
    )
}

/// The uint32 difference `upper - value` is nonzero when `value` is strictly
/// below `upper`. The subtraction does not wrap, because `value <= upper`.
pub fn prove_uint32_lt_implies_positive_difference(
    value: Bitvector32Term,
    upper: Bitvector32Term,
) -> Theorem {
    uint32_implication(
        ConditionTerm::unsigned_less_than(value.clone(), upper.clone()),
        ConditionTerm::unsigned_less_than(
            Bitvector32Term::Constant(0),
            Bitvector32Term::Subtract(Box::new(upper), Box::new(value)),
        ),
    )
}

/// Incrementing a uint32 `value` below `bound` decreases the difference
/// `bound - value`, stated over the affine forms a loop measure `bound -
/// value` evaluates to: `(0 - value) + (bound - 1)` after the increment and
/// `(0 - value) + bound` before it. Neither wraps: `value <= bound - 1`, so
/// the first is `bound - 1 - value` in `[0, bound - 1]` and the second is
/// one more.
pub fn prove_uint32_difference_decreases_after_increment(
    value: Bitvector32Term,
    bound: Bitvector32Term,
) -> Theorem {
    let negated = Bitvector32Term::Subtract(
        Box::new(Bitvector32Term::Constant(0)),
        Box::new(value.clone()),
    );
    uint32_implication(
        ConditionTerm::unsigned_less_than(value, bound.clone()),
        ConditionTerm::unsigned_less_than(
            Bitvector32Term::Add(
                Box::new(negated.clone()),
                Box::new(Bitvector32Term::Subtract(
                    Box::new(bound.clone()),
                    Box::new(Bitvector32Term::Constant(1)),
                )),
            ),
            Bitvector32Term::Add(Box::new(negated), Box::new(bound)),
        ),
    )
}

fn uint32_transitivity(
    first: ConditionTerm,
    second: ConditionTerm,
    conclusion: ConditionTerm,
) -> Theorem {
    Theorem::new(Proposition::Implies(
        Box::new(Proposition::ConditionIs(first, true)),
        Box::new(Proposition::Implies(
            Box::new(Proposition::ConditionIs(second, true)),
            Box::new(Proposition::ConditionIs(conclusion, true)),
        )),
    ))
}

/// Unsigned strict order followed by non-strict order is strict order.
pub fn prove_uint32_lt_le_transitive(
    first: Bitvector32Term,
    middle: Bitvector32Term,
    last: Bitvector32Term,
) -> Theorem {
    uint32_transitivity(
        ConditionTerm::unsigned_less_than(first.clone(), middle.clone()),
        ConditionTerm::unsigned_less_equal(middle, last.clone()),
        ConditionTerm::unsigned_less_than(first, last),
    )
}

/// Unsigned non-strict order followed by strict order is strict order.
pub fn prove_uint32_le_lt_transitive(
    first: Bitvector32Term,
    middle: Bitvector32Term,
    last: Bitvector32Term,
) -> Theorem {
    uint32_transitivity(
        ConditionTerm::unsigned_less_equal(first.clone(), middle.clone()),
        ConditionTerm::unsigned_less_than(middle, last.clone()),
        ConditionTerm::unsigned_less_than(first, last),
    )
}

/// Unsigned strict order is transitive.
pub fn prove_uint32_lt_transitive(
    first: Bitvector32Term,
    middle: Bitvector32Term,
    last: Bitvector32Term,
) -> Theorem {
    uint32_transitivity(
        ConditionTerm::unsigned_less_than(first.clone(), middle.clone()),
        ConditionTerm::unsigned_less_than(middle, last.clone()),
        ConditionTerm::unsigned_less_than(first, last),
    )
}

/// Unsigned non-strict order is transitive.
pub fn prove_uint32_le_transitive(
    first: Bitvector32Term,
    middle: Bitvector32Term,
    last: Bitvector32Term,
) -> Theorem {
    uint32_transitivity(
        ConditionTerm::unsigned_less_equal(first.clone(), middle.clone()),
        ConditionTerm::unsigned_less_equal(middle, last.clone()),
        ConditionTerm::unsigned_less_equal(first, last),
    )
}

/// `greater > lower` and `lower < greater` are one uint32 order.
pub fn prove_uint32_gt_implies_reversed_lt(
    greater: Bitvector32Term,
    lower: Bitvector32Term,
) -> Theorem {
    uint32_implication(
        ConditionTerm::unsigned_greater_than(greater.clone(), lower.clone()),
        ConditionTerm::unsigned_less_than(lower, greater),
    )
}

/// `lower < greater` and `greater > lower` are one uint32 order.
pub fn prove_uint32_lt_implies_reversed_gt(
    lower: Bitvector32Term,
    greater: Bitvector32Term,
) -> Theorem {
    uint32_implication(
        ConditionTerm::unsigned_less_than(lower.clone(), greater.clone()),
        ConditionTerm::unsigned_greater_than(greater, lower),
    )
}

/// `greater >= lower` and `lower <= greater` are one uint32 order.
pub fn prove_uint32_ge_implies_reversed_le(
    greater: Bitvector32Term,
    lower: Bitvector32Term,
) -> Theorem {
    uint32_implication(
        ConditionTerm::unsigned_greater_equal(greater.clone(), lower.clone()),
        ConditionTerm::unsigned_less_equal(lower, greater),
    )
}

/// `lower <= greater` and `greater >= lower` are one uint32 order.
pub fn prove_uint32_le_implies_reversed_ge(
    lower: Bitvector32Term,
    greater: Bitvector32Term,
) -> Theorem {
    uint32_implication(
        ConditionTerm::unsigned_less_equal(lower.clone(), greater.clone()),
        ConditionTerm::unsigned_greater_equal(greater, lower),
    )
}

/// Whether `name` is one of the 64-bit order transitivity theorems.
pub fn is_wide_order_transitivity_name(name: &str) -> bool {
    matches!(
        name.split_once('_'),
        Some((
            "uint64" | "int64",
            "less_than_less_equal_transitive"
                | "less_equal_less_than_transitive"
                | "less_than_transitive"
                | "less_equal_transitive"
        ))
    )
}

/// Transitivity of 64-bit order, by the name of its standard theorem:
/// `{uint64,int64}_{less_than_less_equal,less_equal_less_than,less_than,less_equal}_transitive`. The first premise orders
/// `first` and `middle`, the second `middle` and `last`, and the conclusion
/// is strict when either premise is.
pub fn prove_wide_order_transitive(
    name: &str,
    first: Bitvector32Term,
    middle: Bitvector32Term,
    last: Bitvector32Term,
) -> Option<Theorem> {
    let (unsigned, shape) = match name.split_once('_')? {
        ("uint64", shape) => (true, shape),
        ("int64", shape) => (false, shape),
        _ => return None,
    };
    let (first_strict, second_strict) = match shape {
        "less_than_less_equal_transitive" => (true, false),
        "less_equal_less_than_transitive" => (false, true),
        "less_than_transitive" => (true, true),
        "less_equal_transitive" => (false, false),
        _ => return None,
    };
    let order = |lower: Bitvector32Term, upper: Bitvector32Term, strict: bool| {
        Proposition::ConditionIs(
            match (unsigned, strict) {
                (true, true) => ConditionTerm::uint64_less_than(lower, upper),
                (true, false) => ConditionTerm::uint64_less_equal(lower, upper),
                (false, true) => ConditionTerm::int64_signed_less_than(lower, upper),
                (false, false) => ConditionTerm::int64_signed_less_equal(lower, upper),
            },
            true,
        )
    };
    Some(Theorem::new(Proposition::Implies(
        Box::new(order(first.clone(), middle.clone(), first_strict)),
        Box::new(Proposition::Implies(
            Box::new(order(middle, last.clone(), second_strict)),
            Box::new(order(first, last, first_strict || second_strict)),
        )),
    )))
}

/// An unsigned 64-bit value at most another is equal to it when it is not
/// strictly smaller.
pub fn prove_uint64_le_and_not_lt_implies_eq(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Theorem {
    Theorem::new(Proposition::Implies(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::uint64_less_equal(left.clone(), right.clone()),
            true,
        )),
        Box::new(Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::uint64_less_than(left.clone(), right.clone()),
                false,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::Bitvector64Equal(Box::new(left), Box::new(right)),
                true,
            )),
        )),
    ))
}

/// Signed non-strict order followed by strict order is strict order.
pub fn prove_int32_le_lt_transitive(
    first: Bitvector32Term,
    middle: Bitvector32Term,
    last: Bitvector32Term,
) -> Theorem {
    let first_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(first.clone(), middle.clone()),
        true,
    );
    let second_premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(middle, last.clone()), true);
    let conclusion = Proposition::ConditionIs(ConditionTerm::signed_less_than(first, last), true);
    Theorem::new(Proposition::Implies(
        Box::new(first_premise),
        Box::new(Proposition::Implies(
            Box::new(second_premise),
            Box::new(conclusion),
        )),
    ))
}

/// Signed strict order absorbs a non-strict upper extension.
pub fn prove_int32_lt_le_transitive(
    first: Bitvector32Term,
    middle: Bitvector32Term,
    last: Bitvector32Term,
) -> Theorem {
    let first_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(first.clone(), middle.clone()),
        true,
    );
    let second_premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_equal(middle, last.clone()), true);
    let conclusion = Proposition::ConditionIs(ConditionTerm::signed_less_than(first, last), true);
    Theorem::new(Proposition::Implies(
        Box::new(first_premise),
        Box::new(Proposition::Implies(
            Box::new(second_premise),
            Box::new(conclusion),
        )),
    ))
}

/// Signed strict order is transitive.
pub fn prove_int32_lt_transitive(
    first: Bitvector32Term,
    middle: Bitvector32Term,
    last: Bitvector32Term,
) -> Theorem {
    let first_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(first.clone(), middle.clone()),
        true,
    );
    let second_premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(middle, last.clone()), true);
    let conclusion = Proposition::ConditionIs(ConditionTerm::signed_less_than(first, last), true);
    Theorem::new(Proposition::Implies(
        Box::new(first_premise),
        Box::new(Proposition::Implies(
            Box::new(second_premise),
            Box::new(conclusion),
        )),
    ))
}

/// Signed non-strict order is transitive.
pub fn prove_int32_le_transitive(
    first: Bitvector32Term,
    middle: Bitvector32Term,
    last: Bitvector32Term,
) -> Theorem {
    let first_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(first.clone(), middle.clone()),
        true,
    );
    let second_premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_equal(middle, last.clone()), true);
    let conclusion = Proposition::ConditionIs(ConditionTerm::signed_less_equal(first, last), true);
    Theorem::new(Proposition::Implies(
        Box::new(first_premise),
        Box::new(Proposition::Implies(
            Box::new(second_premise),
            Box::new(conclusion),
        )),
    ))
}

/// Signed non-strict greater-than order is transitive.
pub fn prove_int32_ge_transitive(
    last: Bitvector32Term,
    middle: Bitvector32Term,
    first: Bitvector32Term,
) -> Theorem {
    let first_premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(last.clone(), middle.clone()),
        true,
    );
    let second_premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(middle, first.clone()),
        true,
    );
    let conclusion =
        Proposition::ConditionIs(ConditionTerm::signed_greater_equal(last, first), true);
    Theorem::new(Proposition::Implies(
        Box::new(first_premise),
        Box::new(Proposition::Implies(
            Box::new(second_premise),
            Box::new(conclusion),
        )),
    ))
}

/// Signed greater-equal is the reversed form of signed less-equal.
pub fn prove_int32_ge_implies_reversed_le(
    greater: Bitvector32Term,
    lower: Bitvector32Term,
) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(greater.clone(), lower.clone()),
        true,
    );
    let conclusion =
        Proposition::ConditionIs(ConditionTerm::signed_less_equal(lower, greater), true);
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// Signed non-strict order is preserved when written in reversed greater-or-equal form.
pub fn prove_int32_le_implies_reversed_ge(
    lower: Bitvector32Term,
    greater: Bitvector32Term,
) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(lower.clone(), greater.clone()),
        true,
    );
    let conclusion =
        Proposition::ConditionIs(ConditionTerm::signed_greater_equal(greater, lower), true);
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

pub fn prove_memory_load(memory: CMemory, pointer: Pointer) -> Theorem {
    let outcome = memory.load(&pointer);
    Theorem::new(Proposition::CMemoryLoads {
        memory,
        pointer,
        outcome,
    })
}

pub fn prove_memory_load_after_store_same(
    memory: CMemory,
    pointer: Pointer,
    value: CValue,
) -> Theorem {
    let stored = memory.store(pointer.clone(), value.clone());
    Theorem::new(Proposition::CMemoryLoads {
        memory: stored,
        pointer,
        outcome: CExpressionOutcome::Value(value),
    })
}

pub fn prove_memory_load_after_store_other(
    memory: CMemory,
    stored_pointer: Pointer,
    stored_value: CValue,
    loaded_pointer: Pointer,
) -> Option<Theorem> {
    if stored_pointer == loaded_pointer {
        return None;
    }

    let outcome = memory.load(&loaded_pointer);
    let stored = memory.store(stored_pointer, stored_value);
    if stored.load(&loaded_pointer) != outcome {
        return None;
    }

    Some(Theorem::new(Proposition::CMemoryLoads {
        memory: stored,
        pointer: loaded_pointer,
        outcome,
    }))
}

#[cfg(test)]
mod construction_contract_input_tests {
    use super::*;

    fn layout() -> CAggregateLayout {
        CAggregateLayout::new(8, 4, vec![CAggregateField::new("value", 0, CType::Int32)])
    }

    #[test]
    fn construction_input_setup_is_interface_selected_and_does_not_initialize_storage() {
        let _session = crate::kernel::VerificationSession::enter();
        let at = Pointer::symbolic(Variable(981_501));
        let other = Pointer::symbolic(Variable(981_502));
        let function = c_function(
            CType::Void,
            "construct",
            vec![
                c_parameter("input", CType::Int32Pointer),
                c_parameter("this", CType::Int32Pointer),
            ],
            c_skip(),
        )
        .with_construction_parameter(1, layout());
        let memory = CMemory::new().with_uninitialized_object(at.clone(), 8);
        let state = CState::new().with_memory(memory);
        let arguments = vec![c_pointer_value(other.clone()), c_pointer_value(at.clone())];
        let selected =
            c_state_with_construction_contract_input(state.clone(), &function, &arguments).unwrap();
        assert_eq!(selected.resources(), state.resources());
        assert_eq!(selected.locals(), state.locals());
        assert!(selected.memory().block_size(&at.block).is_none());
        assert!(selected.memory().known_value(&at).is_none());
        assert!(!selected.memory().has_initialized_bytes_at(&at, 8));
        assert!(selected.memory().may_read_uninitialized_object(&at, 8));
        assert_eq!(
            selected.memory(),
            &state
                .memory()
                .clone()
                .with_object_input_domain(at, &layout())
                .unwrap()
        );
        assert_ne!(
            selected.memory(),
            &state
                .memory()
                .clone()
                .with_object_input_domain(other, &layout())
                .unwrap()
        );
        assert!(
            c_state_with_construction_contract_input(state, &function, &arguments[..1]).is_err()
        );
    }

    #[test]
    fn ordinary_pointer_contract_and_raw_destination_do_not_supply_object_inputs() {
        let _session = crate::kernel::VerificationSession::enter();
        let at = Pointer::symbolic(Variable(981_503));
        let state = CState::new()
            .with_memory(CMemory::new().with_uninitialized_object(at.clone(), 8))
            .with_aggregate_return_destination(at.clone(), layout());
        let function = c_function(
            CType::Void,
            "ordinary",
            vec![c_parameter("p", CType::Int32Pointer)],
            c_skip(),
        );
        let after = c_state_with_construction_contract_input(
            state.clone(),
            &function,
            &[c_pointer_value(at)],
        )
        .unwrap();
        assert_eq!(after, state);
    }

    #[test]
    fn construction_result_setup_requires_its_exact_selected_layout() {
        let _session = crate::kernel::VerificationSession::enter();
        let at = Pointer::symbolic(Variable(981_504));
        let function = c_function(CType::Int32Pointer, "factory", vec![], c_skip())
            .with_construction_return(layout());
        let state =
            CState::new().with_memory(CMemory::new().with_uninitialized_block(at.block.clone(), 8));
        assert!(c_state_with_construction_contract_input(state.clone(), &function, &[]).is_err());
        let wrong =
            CAggregateLayout::new(8, 4, vec![CAggregateField::new("value", 0, CType::UInt32)]);
        assert!(
            c_state_with_construction_contract_input(
                state
                    .clone()
                    .with_aggregate_return_destination(at.clone(), wrong),
                &function,
                &[]
            )
            .is_err()
        );
        let selected = c_state_with_construction_contract_input(
            state.with_aggregate_return_destination(at.clone(), layout()),
            &function,
            &[],
        )
        .unwrap();
        assert_eq!(selected.memory().block_size(&at.block), Some(&8u32.into()));
        assert!(!selected.memory().has_initialized_bytes_at(&at, 8));
        assert_eq!(selected.resources(), CState::new().resources());
    }
}
